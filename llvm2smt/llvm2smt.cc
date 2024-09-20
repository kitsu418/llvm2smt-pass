#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <string>

#include <z3++.h>

using namespace llvm;

namespace {

class InstructionException : public std::runtime_error {
public:
  InstructionException(const char *msg, const Value *v = nullptr, int line = 0)
      : std::runtime_error(msg) {
    raw_string_ostream os(_msg);

    os << msg << " at line " << line << ": ";
    if (v) {
      v->getType()->print(os);
      os << " ";
      v->print(os);
    } else {
      os << "Unknown instruction";
    }
    os << "\n";
  }

  virtual const char *what() const noexcept override { return _msg.c_str(); }

private:
  std::string _msg;
};

#define ERROR(msg, v)                                                          \
  do {                                                                         \
    throw InstructionException(msg, v, __LINE__);                              \
  } while (0)

class LiveVariableAnalysis {
public:
  void analyze_function(Function &fun) noexcept {
    for (auto &bb : fun) {
      in[&bb] = {};
      out[&bb] = {};
    }

    bool changed = true;
    while (changed) {
      changed = false;

      for (auto &bb : llvm::reverse(fun)) {
        std::set<Value *> new_out = {};

        // out[B] = \bigcup_\text{S a successor of B} in[S]
        for (auto succ : successors(&bb)) {
          for (auto v : in[succ]) {
            new_out.insert(v);
          }
        }

        // in[B] = use(B) \cup (out[B] - def(B))
        std::set<Value *> new_in = new_out;
        for (auto &inst : llvm::reverse(bb)) {
          new_in.erase(&inst);
          for (auto &use : inst.operands()) {
            if (isa<Instruction>(use) || isa<Argument>(use)) {
              new_in.insert(use);
            }
          }
        }

        if (new_in != in[&bb] || new_out != out[&bb]) {
          std::swap(in[&bb], new_in);
          std::swap(out[&bb], new_out);
          changed = true;
        }
      }
    }
  }

  const std::set<Value *> &get_in(BasicBlock *bb) const { return in.at(bb); }

  LiveVariableAnalysis(Function &fun) { analyze_function(fun); }
  ~LiveVariableAnalysis() = default;

private:
  std::map<BasicBlock *, std::set<Value *>> in{};
  std::map<BasicBlock *, std::set<Value *>> out{};
};

class Context {
public:
  Context(Module *m)
      : fp(z3::fixedpoint(ctx)), byte_sort(ctx.bv_sort(8)),
        address_sort(ctx.bv_sort(64)),
        memory_sort(ctx.array_sort(address_sort, byte_sort)),
        slot_tracker(ModuleSlotTracker(m)), memory_state_num(0) {

    for (auto &f : *m) {
      if (f.isDeclaration()) {
        continue;
      }

      live_vars_map.insert({&f, LiveVariableAnalysis(f)});
      const auto &lva = live_vars_map.at(&f);

      for (auto &bb : f) {
        if (f.isDeclaration()) {
          continue;
        }
        slot_tracker.incorporateFunction(f);

        z3::sort_vector domain(ctx);

        for (auto var : lva.get_in(&bb)) {
          if (var->getType()->isIntegerTy()) {
            if (var->getType()->getIntegerBitWidth() == 1) {
              domain.push_back(ctx.bool_sort());
            } else {
              domain.push_back(
                  ctx.bv_sort(var->getType()->getIntegerBitWidth()));
            }
          } else if (var->getType()->isIntOrPtrTy()) {
            domain.push_back(ctx.bv_sort(64));
          } else {
            ERROR("Unsupported type", var);
          }
        }
        // the id of the basic block transitioning to current basic block state
        domain.push_back(ctx.string_sort());
        // current memory state
        domain.push_back(memory_sort);
        // stack pointer
        domain.push_back(address_sort);

        relation_map.insert(
            {&bb, ctx.function(get_value_name(&bb, bb.getParent()).c_str(),
                               domain, ctx.bool_sort())});
        fp.register_relation(relation_map.at(&bb));
      }
    }
  }

  z3::expr to_z3_expr(Value *v, Function *f, bool is_signed = true) {
    if (isa<Constant>(v)) {
      if (auto constant_int = dyn_cast<ConstantInt>(v)) {
        auto width = constant_int->getType()->getIntegerBitWidth();
        if (width == 1) {
          return ctx.bool_val(is_signed ? constant_int->getSExtValue() != 0
                                        : constant_int->getZExtValue() != 0);
        } else {
          return ctx.bv_val(is_signed ? constant_int->getSExtValue()
                                      : constant_int->getZExtValue(),
                            width);
        }
      } else if (auto global_variable = dyn_cast<GlobalVariable>(v)) {
        if (global_variable->isExternalLinkage(global_variable->getLinkage())) {
          if (global_variable->getValueType()->isIntegerTy()) {
            auto width = global_variable->getValueType()->getIntegerBitWidth();
            if (width == 1) {
              return ctx.bool_const(get_value_name(global_variable, f).c_str());
            } else {
              return ctx.bv_const(get_value_name(global_variable, f).c_str(),
                                  width);
            }
          } else if (global_variable->getValueType()->isPointerTy()) {
            return ctx.bv_const(get_value_name(global_variable, f).c_str(), 64);
          } else {
            ERROR("Unsupported type", v);
          }
        } else {
          ERROR("Unsupported type", v);
        }
      } else {
        ERROR("Unsupported type", v);
      }
    } else if (isa<Instruction>(v) || isa<Argument>(v)) {
      if (v->getType()->isIntegerTy()) {
        auto width = v->getType()->getIntegerBitWidth();
        if (width == 1) {
          return ctx.bool_const(get_value_name(v, f).c_str());
        } else {
          return ctx.bv_const(get_value_name(v, f).c_str(), width);
        }
      } else {
        ERROR("Unsupported type", v);
      }
    } else if (v->getType()->isLabelTy()) {
      return ctx.string_val(get_value_name(v, f));
    } else {
      ERROR("Unsupported type", v);
    }
  }

  z3::expr query_value_map(Value *v) { return value_map.at(v); }

  void update_value_map(Value *v, z3::expr &&e) {
    value_map.insert({v, std::move(e)});
  }

  bool has_value(Value *v) const noexcept { return value_map.count(v) > 0; }

  z3::context &get_context() noexcept { return ctx; }

  std::string get_value_name(Value *v, Function *f) noexcept {
    if (auto *bb = dyn_cast<BasicBlock>(v)) {
      return f->getName().str() + "#" +
             std::to_string((slot_tracker.getLocalSlot(bb)));
    } else {
      return f->getName().str() + "%" +
             std::to_string((slot_tracker.getLocalSlot(v)));
    }
  }

  void incorporate_function(const Function &f) {
    slot_tracker.incorporateFunction(f);
  }

  z3::expr_vector get_horn_clause(BasicBlock &bb) {
    z3::expr_vector clauses(ctx);
    z3::expr_vector body(ctx);
    const auto &lva = live_vars_map.at(bb.getParent());

    z3::expr_vector domain(ctx);
    for (auto lv : lva.get_in(&bb)) {
      if (lv->getType()->isIntegerTy()) {
        auto width = lv->getType()->getIntegerBitWidth();
        if (width == 1) {
          domain.push_back(
              ctx.bool_const(get_value_name(lv, bb.getParent()).c_str()));
        } else {
          domain.push_back(
              ctx.bv_const(get_value_name(lv, bb.getParent()).c_str(), width));
        }
      } else if (lv->getType()->isIntOrPtrTy()) {
        domain.push_back(
            ctx.bv_const(get_value_name(lv, bb.getParent()).c_str(), 64));
      } else {
        ERROR("Unsupported type", lv);
      }
    }
    domain.push_back(ctx.string_const("predecessor"));
    domain.push_back(ctx.constant("memory_0", memory_sort));
    domain.push_back(ctx.constant("sp_0", address_sort));
    body.push_back(relation_map.at(&bb)(std::move(domain)));

    int memory_state_num = 0;
    for (auto &inst : bb) {
      try {
        if (has_value(&inst)) {
          auto type = inst.getType();
          if (isa<AllocaInst>(inst)) {
            body.push_back(query_value_map(&inst));
          } else if (type->isIntegerTy()) {
            auto rhs = query_value_map(&inst);
            auto width = type->getIntegerBitWidth();
            auto lhs =
                width == 1
                    ? ctx.bool_const(
                          get_value_name(&inst, bb.getParent()).c_str())
                    : ctx.bv_const(
                          get_value_name(&inst, bb.getParent()).c_str(), width);
            body.push_back(lhs == rhs);
          } else if (type->isVoidTy()) {
            continue;
          } else {
            ERROR("Unsupported type", &inst);
          }
        }
      } catch (z3::exception &e) {
        errs() << e.msg() << "\n";
        ERROR("Z3 Exception", &inst);
      }
    }

    auto terminatior = bb.getTerminator();

    for (auto succ : successors(&bb)) {
      z3::expr_vector head_args(ctx);
      for (auto var : lva.get_in(succ)) {
        if (var->getType()->isIntegerTy()) {
          auto width = var->getType()->getIntegerBitWidth();
          if (width == 1) {
            head_args.push_back(
                ctx.bool_const(get_value_name(var, bb.getParent()).c_str()));
          } else {
            head_args.push_back(ctx.bv_const(
                get_value_name(var, bb.getParent()).c_str(), width));
          }
        } else if (var->getType()->isIntOrPtrTy()) {
          head_args.push_back(
              ctx.bv_const(get_value_name(var, bb.getParent()).c_str(), 64));
        } else {
          ERROR("Unsupported type", var);
        }
      }
      head_args.push_back(
          ctx.string_const(get_value_name(&bb, bb.getParent()).c_str()));
      head_args.push_back(ctx.constant(
          ("memory_" + std::to_string(memory_state_num)).c_str(), memory_sort));
      head_args.push_back(ctx.constant(
          ("sp_" + std::to_string(memory_state_num)).c_str(), address_sort));

      if (auto branch = dyn_cast<BranchInst>(terminatior)) {
        if (branch->isConditional()) {
          auto cond = branch->getCondition();
          auto expr = to_z3_expr(cond, bb.getParent());
          if (branch->getSuccessor(0) == succ) {
            body.push_back(expr);
          } else {
            body.push_back(!expr);
          }
        }
      }

      clauses.push_back(
          z3::implies(std::move(z3::mk_and(body)),
                      relation_map.at(succ)(std::move(head_args))));
      body.pop_back();
    }
    // bb.print(errs());

    return clauses;
  }

  void reset_memory_state() noexcept { memory_state_num = 0; }

  z3::sort get_byte_sort() const noexcept { return byte_sort; }
  z3::sort get_address_sort() const noexcept { return address_sort; }
  z3::sort get_memory_sort() const noexcept { return memory_sort; }
  int get_memory_state_num() const noexcept { return memory_state_num; }
  void inc_memory_state_num() noexcept { ++memory_state_num; }

private:
  z3::context ctx{};
  z3::fixedpoint fp;
  z3::sort byte_sort;
  z3::sort address_sort;
  z3::sort memory_sort;

  std::map<Value *, z3::expr> value_map{};
  ModuleSlotTracker slot_tracker;
  std::map<BasicBlock *, z3::func_decl> relation_map{};
  std::map<Function *, LiveVariableAnalysis> live_vars_map{};
  int memory_state_num{};
  int call_num{};
};

class llvm2smtVisitor : public InstVisitor<llvm2smtVisitor> {
public:
  llvm2smtVisitor(Context &c) : ctx(c) {}

  void visitBinaryOperator(BinaryOperator &inst) {
    assert(inst.getNumOperands() == 2);
    auto op1 = inst.getOperand(0);
    auto op2 = inst.getOperand(1);
    assert(op1->getType() == op2->getType());

    auto expr1 =
        ctx.to_z3_expr(op1, inst.getFunction(), !inst.hasNoSignedWrap());
    auto expr2 =
        ctx.to_z3_expr(op2, inst.getFunction(), !inst.hasNoSignedWrap());

    try {
      switch (inst.getOpcode()) {
      case Instruction::Add:
        ctx.update_value_map(&inst, expr1 + expr2);
        break;
      case Instruction::Sub:
        ctx.update_value_map(&inst, expr1 - expr2);
        break;
      case Instruction::Mul:
        ctx.update_value_map(
            &inst, (expr1 * expr2)
                       .extract(op1->getType()->getIntegerBitWidth() - 1, 0));
        break;
      case Instruction::UDiv:
        ctx.update_value_map(&inst, z3::udiv(expr1, expr2));
        break;
      case Instruction::SDiv:
        ctx.update_value_map(&inst, expr1 / expr2);
        break;
      case Instruction::URem:
        ctx.update_value_map(&inst, z3::urem(expr1, expr2));
        break;
      case Instruction::SRem:
        ctx.update_value_map(&inst, z3::srem(expr1, expr2));
        break;
      case Instruction::Shl:
        ctx.update_value_map(&inst, z3::shl(expr1, expr2));
        break;
      case Instruction::LShr:
        ctx.update_value_map(&inst, z3::lshr(expr1, expr2));
        break;
      case Instruction::AShr:
        ctx.update_value_map(&inst, z3::ashr(expr1, expr2));
        break;
      case Instruction::And:
        ctx.update_value_map(&inst, expr1 & expr2);
        break;
      case Instruction::Or:
        ctx.update_value_map(&inst, expr1 | expr2);
        break;
      case Instruction::Xor:
        ctx.update_value_map(&inst, expr1 ^ expr2);
        break;
      case Instruction::FAdd:
      case Instruction::FSub:
      case Instruction::FMul:
      case Instruction::FDiv:
      case Instruction::FRem:
        ERROR("Unsupported instruction", &inst);
        break;
      default:
        ERROR("Unknown instruction", &inst);
        break;
      }
    } catch (z3::exception &e) {
      errs() << e.msg() << "\n";
      ERROR("Z3 Exception", &inst);
    }
  }

  void visitICmp(ICmpInst &inst) {
    assert(inst.getNumOperands() == 2);
    auto op1 = inst.getOperand(0);
    auto op2 = inst.getOperand(1);
    assert(op1->getType() == op2->getType());

    auto expr1 =
        ctx.to_z3_expr(op1, inst.getFunction(), !inst.hasNoSignedWrap());
    auto expr2 =
        ctx.to_z3_expr(op2, inst.getFunction(), !inst.hasNoSignedWrap());

    try {
      switch (inst.getPredicate()) {
      case CmpInst::ICMP_EQ:
        ctx.update_value_map(&inst, expr1 == expr2);
        break;
      case CmpInst::ICMP_NE:
        ctx.update_value_map(&inst, expr1 != expr2);
        break;
      case CmpInst::ICMP_UGT:
        ctx.update_value_map(&inst, z3::ugt(expr1, expr2));
        break;
      case CmpInst::ICMP_UGE:
        ctx.update_value_map(&inst, z3::uge(expr1, expr2));
        break;
      case CmpInst::ICMP_ULT:
        ctx.update_value_map(&inst, z3::ult(expr1, expr2));
        break;
      case CmpInst::ICMP_ULE:
        ctx.update_value_map(&inst, z3::ule(expr1, expr2));
        break;
      case CmpInst::ICMP_SGT:
        ctx.update_value_map(&inst, z3::sgt(expr1, expr2));
        break;
      case CmpInst::ICMP_SGE:
        ctx.update_value_map(&inst, z3::sge(expr1, expr2));
        break;
      case CmpInst::ICMP_SLT:
        ctx.update_value_map(&inst, z3::slt(expr1, expr2));
        break;
      case CmpInst::ICMP_SLE:
        ctx.update_value_map(&inst, z3::sle(expr1, expr2));
        break;
      case CmpInst::FCMP_FALSE:
      case CmpInst::FCMP_OEQ:
      case CmpInst::FCMP_OGT:
      case CmpInst::FCMP_OGE:
      case CmpInst::FCMP_OLT:
      case CmpInst::FCMP_OLE:
      case CmpInst::FCMP_ONE:
      case CmpInst::FCMP_ORD:
      case CmpInst::FCMP_UNO:
      case CmpInst::FCMP_UEQ:
      case CmpInst::FCMP_UGT:
      case CmpInst::FCMP_UGE:
      case CmpInst::FCMP_ULT:
      case CmpInst::FCMP_ULE:
      case CmpInst::FCMP_UNE:
      case CmpInst::FCMP_TRUE:
        ERROR("Unsupported predicate", &inst);
        break;
      default:
        ERROR("Unknown predicate", &inst);
        break;
      }
    } catch (z3::exception &e) {
      errs() << e.msg() << "\n";
      ERROR("Z3 Exception", &inst);
    }
  }

  void visitBranchInst(BranchInst &inst) {
    // do nothing here
  }

  void visitCastInst(CastInst &inst) {
    auto src = inst.getSrcTy();
    auto dst = inst.getDestTy();
    auto v = inst.getOperand(0);
    if (v == nullptr) {
      ERROR("Operand is null", &inst);
    }
    auto e = ctx.to_z3_expr(v, inst.getFunction(), !inst.hasNoSignedWrap());

    switch (inst.getOpcode()) {
    case Instruction::ZExt:
      if (!v->getType()->isIntegerTy()) {
        ERROR("Value is not Integer", v);
      }
      if (dst->getIntegerBitWidth() <= src->getIntegerBitWidth()) {
        ERROR("Invalid cast", &inst);
      }

      ctx.update_value_map(&inst, z3::zext(e, (dst->getIntegerBitWidth() -
                                               src->getIntegerBitWidth())));
      break;
    case Instruction::SExt:
      if (!v->getType()->isIntegerTy()) {
        ERROR("Value is not Integer", v);
      }
      if (dst->getIntegerBitWidth() <= src->getIntegerBitWidth()) {
        ERROR("Invalid cast", &inst);
      }

      ctx.update_value_map(&inst, z3::sext(e, (dst->getIntegerBitWidth() -
                                               src->getIntegerBitWidth())));
      break;
    case Instruction::Trunc:
      if (dst->getIntegerBitWidth() >= src->getIntegerBitWidth()) {
        ERROR("Invalid cast", &inst);
      }
      ctx.update_value_map(&inst, e.extract(dst->getIntegerBitWidth() - 1, 0));
      break;
    case Instruction::BitCast:
    case Instruction::FPToUI:
    case Instruction::FPToSI:
    case Instruction::UIToFP:
    case Instruction::SIToFP:
    case Instruction::FPTrunc:
    case Instruction::FPExt:
    case Instruction::PtrToInt:
    case Instruction::IntToPtr:
    case Instruction::AddrSpaceCast:
      ERROR("Unsupported Opcode", &inst);
      break;
    default:
      ERROR("Unknown Opcode", &inst);
      break;
    }
  }

  void visitPHINode(PHINode &inst) {
    z3::expr pred = ctx.get_context().string_const("predecessor");
    if (inst.getNumIncomingValues() == 0) {
      ERROR("PHINode has no incoming values", &inst);
    }

    // z3::expr e = z3::ite(
    //     pred == ctx.get_z3_expr(inst.getIncomingBlock(0),
    //     inst.getFunction()), ctx.get_z3_expr(inst.getIncomingValue(0),
    //     inst.getFunction()), e);
    // for (unsigned int i = 1; i < inst.getNumIncomingValues(); ++i) {
    //   auto incoming_expr =
    //       ctx.get_z3_expr(inst.getIncomingValue(i), inst.getFunction());
    //   e = z3::ite(
    //       pred == ctx.get_z3_expr(inst.getIncomingBlock(i),
    //       inst.getFunction()), std::move(incoming_expr), std::move(e));
    // }

    // ctx.update_value_map(&inst, std::move(e));
  }

  void visitReturnInst(ReturnInst &inst) {}

  void visitAllocaInst(AllocaInst &inst) {
    auto name = ctx.get_value_name(&inst, inst.getFunction());
    auto memory = ctx.get_context().constant(
        ("memory_" + std::to_string(ctx.get_memory_state_num())).c_str(),
        ctx.get_memory_sort());
    auto new_memory = ctx.get_context().constant(
        ("memory_" + std::to_string(ctx.get_memory_state_num() + 1)).c_str(),
        ctx.get_memory_sort());
    auto sp = ctx.get_context().constant(
        ("sp_" + std::to_string(ctx.get_memory_state_num())).c_str(),
        ctx.get_address_sort());
    auto new_sp = ctx.get_context().constant(
        ("sp_" + std::to_string(ctx.get_memory_state_num() + 1)).c_str(),
        ctx.get_memory_sort());

    z3::expr_vector states(ctx.get_context());
    states.push_back(new_memory = memory);
    if (inst.getAllocatedType()->isIntegerTy()) {
      states.push_back(
          new_sp =
              sp -
              ctx.get_context().bv_val(
                  (inst.getAllocatedType()->getIntegerBitWidth() + 7) / 8, 64));
    } else {
      ERROR("Unsupported type", &inst);
    }
    states.push_back(ctx.get_context().bv_const(
                         ctx.get_value_name(&inst, inst.getFunction()).c_str(),
                         64) = new_sp);

    ctx.update_value_map(&inst, z3::mk_and(states));
    ctx.inc_memory_state_num();
  }

  void visitLoadInst(LoadInst &inst) {
    auto ptr = inst.getPointerOperand();
    auto ptr_expr = ctx.to_z3_expr(ptr, inst.getFunction());
    auto memory = ctx.get_context().constant(
        ("memory_" + std::to_string(ctx.get_memory_state_num())).c_str(),
        ctx.get_memory_sort());
    auto sp = ctx.get_context().constant(
        ("sp_" + std::to_string(ctx.get_memory_state_num())).c_str(),
        ctx.get_address_sort());

    if (inst.getType()->isIntegerTy()) {
      auto width = inst.getType()->getIntegerBitWidth();
      z3::expr_vector bytes(ctx.get_context());

      // little endian
      for (unsigned int i = (width - 1) / 8; i >= 0; --i) {
        auto byte = z3::select(memory, sp + ctx.get_context().bv_val(i, 64));
        bytes.push_back(std::move(byte));
      }

      ctx.update_value_map(&inst, z3::concat(bytes).extract(width - 1, 0));
    } else {
      ERROR("Unsupported type", &inst);
    }
  }

  void visitStoreInst(StoreInst &inst) {
    auto ptr = inst.getPointerOperand();
    auto val = inst.getValueOperand();

    auto ptr_expr = ctx.to_z3_expr(ptr, inst.getFunction());
    auto val_expr = ctx.to_z3_expr(val, inst.getFunction());

    auto memory = ctx.get_context().constant(
        ("memory_" + std::to_string(ctx.get_memory_state_num())).c_str(),
        ctx.get_memory_sort());
    auto sp = ctx.get_context().constant(
        ("sp_" + std::to_string(ctx.get_memory_state_num())).c_str(),
        ctx.get_address_sort());

    auto byte_sort = ctx.get_byte_sort();
    auto address_sort = ctx.get_address_sort();
    auto memory_sort = ctx.get_memory_sort();

    if (val->getType()->isIntegerTy()) {
      auto width = val->getType()->getIntegerBitWidth();
      z3::expr_vector new_memory(ctx.get_context());

      // little endian
      for (unsigned int i = 0; i < (width + 7) / 8; ++i) {
        auto byte = val_expr.extract(i * 8 + 7, i * 8);
        ctx.inc_memory_state_num();
        new_memory.push_back(
            ctx.get_context().constant(
                ("memory_" + std::to_string(ctx.get_memory_state_num()))
                    .c_str(),
                ctx.get_memory_sort()) =
                z3::store(memory, ptr_expr + ctx.get_context().bv_val(i, 64),
                          std::move(byte)));
      }

      ctx.update_value_map(&inst, z3::mk_and(new_memory));
    } else {
      ERROR("Unsupported type", &inst);
    }
  }

  void visitInstruction(Instruction &inst) {
    ERROR("Unsupported instruction", &inst);
  }

private:
  Context &ctx;
};

class llvm2SmtPass : public PassInfoMixin<llvm2SmtPass> {
public:
  PreservedAnalyses run(Module &m, ModuleAnalysisManager &mam) {
    Context ctx(&m);

    for (Function &f : m) {
      errs() << "Processing function: " << f.getName() << "\n";
      ctx.incorporate_function(f);

      std::string filename = (f.getName() + ".smt2").str();
      std::error_code ec;
      raw_fd_ostream out(filename, ec, sys::fs::OF_Text);

      llvm2smtVisitor visitor(ctx);

      for (auto &bb : f) {
        ctx.reset_memory_state();

        try {
          visitor.visit(bb);
        } catch (InstructionException &e) {
          errs() << e.what();
        }

        auto clauses = ctx.get_horn_clause(bb);
        errs() << clauses.to_string() << "\n";
      }
    }

    return PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

} // namespace

PassPluginLibraryInfo getPassPluginInfo() {
  const auto callback = [](PassBuilder &PB) {
    PB.registerPipelineParsingCallback(
        [&](StringRef name, ModulePassManager &mpm, auto) {
          if (name == "llvm2smt") {
            mpm.addPass(llvm2SmtPass());
            return true;
          } else {
            return false;
          }
        });
  };

  return {LLVM_PLUGIN_API_VERSION, "LLVM to SMT-LIB Pass", "0.0.1", callback};
};

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getPassPluginInfo();
}
