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
          } else if (var->getType()->isPointerTy()) {
            domain.push_back(ctx.bv_sort(64));
          } else if (var->getType()->isFloatTy()) {
            domain.push_back(ctx.fpa_sort<32>());
          } else if (var->getType()->isDoubleTy()) {
            domain.push_back(ctx.fpa_sort<64>());
          } else {
            ERROR("Unsupported type", var);
          }
        }

        // work with PHI nodes: we extract them to the arguments of the head
        for (auto &phi : bb.phis()) {
          if (phi.getType()->isIntegerTy()) {
            if (phi.getType()->getIntegerBitWidth() == 1) {
              domain.push_back(ctx.bool_sort());
            } else {
              domain.push_back(
                  ctx.bv_sort(phi.getType()->getIntegerBitWidth()));
            }
          } else if (phi.getType()->isPointerTy()) {
            domain.push_back(ctx.bv_sort(64));
          } else if (phi.getType()->isFloatTy()) {
            domain.push_back(ctx.fpa_sort<32>());
          } else if (phi.getType()->isDoubleTy()) {
            domain.push_back(ctx.fpa_sort<64>());
          } else {
            ERROR("Unsupported type", &phi);
          }
        }

        // current memory state
        domain.push_back(memory_sort);
        // stack pointer
        domain.push_back(address_sort);

        relation_map.insert(
            {&bb, ctx.function(
                      (get_value_name(&bb, bb.getParent()) + "_rel").c_str(),
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
      } else if (isa<ConstantFP>(v)) {
        if (v->getType()->isFloatTy()) {
          return ctx.fpa_val(
              cast<ConstantFP>(v)->getValueAPF().convertToFloat());
        } else if (v->getType()->isDoubleTy()) {
          return ctx.fpa_val(
              cast<ConstantFP>(v)->getValueAPF().convertToDouble());
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
      } else if (v->getType()->isPointerTy()) {
        return ctx.constant(get_value_name(v, f).c_str(), address_sort);
      } else if (v->getType()->isFloatTy()) {
        return ctx.fpa_const<32>(get_value_name(v, f).c_str());
      } else if (v->getType()->isDoubleTy()) {
        return ctx.fpa_const<64>(get_value_name(v, f).c_str());
      } else {
        ERROR("Unsupported type", v);
      }
    } else if (v->getType()->isLabelTy()) {
      return ctx.string_val(get_value_name(v, f));
    } else if (isa<CallBase>(v)) {
      auto name = "call_" + std::to_string(call_num++);

      if (v->getType()->isIntegerTy()) {
        auto width = v->getType()->getIntegerBitWidth();
        if (width == 1) {
          return ctx.bool_const(name.c_str());
        } else {
          return ctx.bv_const(name.c_str(), width);
        }
      } else if (v->getType()->isPointerTy()) {
        return ctx.bv_const(name.c_str(), 64);
      } else if (v->getType()->isFloatTy()) {
        return ctx.fpa_const<32>(name.c_str());
      } else if (v->getType()->isDoubleTy()) {
        return ctx.fpa_const<64>(name.c_str());
      } else {
        ERROR("Unsupported type", v);
      }
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

  void add_rules(BasicBlock &bb) {
    z3::expr_vector body(ctx);
    const auto &lva = live_vars_map.at(bb.getParent());

    z3::expr_vector domain(ctx);
    for (auto lv : lva.get_in(&bb)) {
      domain.push_back(to_z3_expr(lv, bb.getParent()));
    }

    for (auto &phi : bb.phis()) {
      domain.push_back(to_z3_expr(&phi, bb.getParent()));
    }

    domain.push_back(ctx.constant("memory_0", memory_sort));
    domain.push_back(ctx.constant("sp_0", address_sort));
    body.push_back(relation_map.at(&bb)(std::move(domain)));

    for (auto &inst : bb) {
      try {
        if (isa<PHINode>(inst)) {
          continue;
        } else if (has_value(&inst)) {
          auto type = inst.getType();
          if (isa<AllocaInst>(inst) || isa<StoreInst>(inst)) {
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
          } else if (type->isPointerTy()) {
            auto rhs = query_value_map(&inst);
            auto lhs =
                ctx.bv_const(get_value_name(&inst, bb.getParent()).c_str(), 64);
            body.push_back(lhs == rhs);
          } else if (type->isFloatTy()) {
            auto rhs = query_value_map(&inst);
            auto lhs = ctx.fpa_const<32>(
                get_value_name(&inst, bb.getParent()).c_str());
            body.push_back(lhs == rhs);
          } else if (type->isDoubleTy()) {
            auto rhs = query_value_map(&inst);
            auto lhs = ctx.fpa_const<64>(
                get_value_name(&inst, bb.getParent()).c_str());
            body.push_back(lhs == rhs);
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
        head_args.push_back(to_z3_expr(var, bb.getParent()));
      }

      for (auto &phi : succ->phis()) {
        auto incoming = phi.getIncomingValueForBlock(&bb);
        head_args.push_back(to_z3_expr(incoming, bb.getParent()));
      }

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
        } else {
          body.push_back(ctx.bool_val(true));
        }
      }

      auto clause = z3::implies(std::move(z3::mk_and(body)),
                                relation_map.at(succ)(std::move(head_args)));
      fp.add_rule(clause,
                  ctx.str_symbol((get_value_name(&bb, bb.getParent()) + "->" +
                                  get_value_name(succ, bb.getParent()))
                                     .c_str()));
      body.pop_back();
    }
  }

  void reset_memory_state() noexcept { memory_state_num = 0; }

  z3::sort get_byte_sort() const noexcept { return byte_sort; }
  z3::sort get_address_sort() const noexcept { return address_sort; }
  z3::sort get_memory_sort() const noexcept { return memory_sort; }
  int get_memory_state_num() const noexcept { return memory_state_num; }
  void inc_memory_state_num() noexcept { ++memory_state_num; }
  int get_call_num() const noexcept { return call_num; }
  void inc_call_num() noexcept { ++call_num; }

  void dump(raw_fd_ostream &out) noexcept { out << fp.to_string(); }

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
      case Instruction::FAdd:
        ctx.update_value_map(&inst, expr1 + expr2);
        break;
      case Instruction::Sub:
      case Instruction::FSub:
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
      case Instruction::FMul:
        ctx.update_value_map(&inst, expr1 * expr2);
        break;
      case Instruction::FDiv:
        ctx.update_value_map(&inst, expr1 / expr2);
        break;
      case Instruction::FRem:
        ctx.update_value_map(&inst, z3::rem(expr1, expr2));
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

  void visitFCmp(FCmpInst &inst) {
    assert(inst.getNumOperands() == 2);
    auto op1 = inst.getOperand(0);
    auto op2 = inst.getOperand(1);
    assert(op1->getType() == op2->getType());

    if (!op1->getType()->isFloatTy() && !op1->getType()->isDoubleTy()) {
      ERROR("Unsupported type", &inst);
    }

    auto expr1 = ctx.to_z3_expr(op1, inst.getFunction());
    auto expr2 = ctx.to_z3_expr(op2, inst.getFunction());

    switch (inst.getPredicate()) {
    case CmpInst::FCMP_FALSE:
      ctx.update_value_map(&inst, ctx.get_context().bool_val(false));
      break;
    case CmpInst::FCMP_OEQ:
      ctx.update_value_map(&inst, z3::fp_eq(expr1, expr2) &&
                                      !expr1.mk_is_nan() && !expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_OGT:
      ctx.update_value_map(&inst, expr1 > expr2 && !expr1.mk_is_nan() &&
                                      !expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_OGE:
      ctx.update_value_map(&inst, expr1 >= expr2 && !expr1.mk_is_nan() &&
                                      !expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_OLT:
      ctx.update_value_map(&inst, expr1 < expr2 && !expr1.mk_is_nan() &&
                                      !expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_OLE:
      ctx.update_value_map(&inst, expr1 <= expr2 && !expr1.mk_is_nan() &&
                                      !expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_ONE:
      ctx.update_value_map(&inst, !z3::fp_eq(expr1, expr2) &&
                                      !expr1.mk_is_nan() && !expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_ORD:
      ctx.update_value_map(&inst, !expr1.mk_is_nan() && !expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_UNO:
      ctx.update_value_map(&inst, expr1.mk_is_nan() || expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_UEQ:
      ctx.update_value_map(&inst, z3::fp_eq(expr1, expr2) ||
                                      expr1.mk_is_nan() || expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_UGT:
      ctx.update_value_map(&inst, expr1 > expr2 || expr1.mk_is_nan() ||
                                      expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_UGE:
      ctx.update_value_map(&inst, expr1 >= expr2 || expr1.mk_is_nan() ||
                                      expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_ULT:
      ctx.update_value_map(&inst, expr1 < expr2 || expr1.mk_is_nan() ||
                                      expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_ULE:
      ctx.update_value_map(&inst, expr1 <= expr2 || expr1.mk_is_nan() ||
                                      expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_UNE:
      ctx.update_value_map(&inst, !z3::fp_eq(expr1, expr2) ||
                                      expr1.mk_is_nan() || expr2.mk_is_nan());
      break;
    case CmpInst::FCMP_TRUE:
      ctx.update_value_map(&inst, ctx.get_context().bool_val(true));
      break;
    case CmpInst::ICMP_EQ:
    case CmpInst::ICMP_NE:
    case CmpInst::ICMP_UGT:
    case CmpInst::ICMP_UGE:
    case CmpInst::ICMP_ULT:
    case CmpInst::ICMP_ULE:
    case CmpInst::ICMP_SGT:
    case CmpInst::ICMP_SGE:
    case CmpInst::ICMP_SLT:
    case CmpInst::ICMP_SLE:
      ERROR("Unsupported predicate", &inst);
      break;
    default:
      ERROR("Unknown predicate", &inst);
      break;
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
    case Instruction::SIToFP:
      if (!v->getType()->isIntegerTy()) {
        ERROR("Value is not Integer", v);
      }
      if (!dst->isFloatTy() && !dst->isDoubleTy()) {
        ERROR("Invalid cast", &inst);
      }
      ctx.update_value_map(
          &inst, z3::sbv_to_fpa(e, dst->isFloatTy()
                                       ? ctx.get_context().fpa_sort<32>()
                                       : ctx.get_context().fpa_sort<64>()));
      break;
    case Instruction::BitCast:
    case Instruction::FPToUI:
    case Instruction::FPToSI:
    case Instruction::UIToFP:
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
    // we work with PHI nodes in the add_rules method
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
        ctx.get_address_sort());

    z3::expr_vector states(ctx.get_context());
    states.push_back(new_memory == memory);
    if (inst.getAllocatedType()->isIntegerTy()) {
      states.push_back(
          new_sp ==
          sp -
              ctx.get_context().bv_val(
                  (inst.getAllocatedType()->getIntegerBitWidth() + 7) / 8, 64));
    } else if (inst.getAllocatedType()->isFloatTy()) {
      states.push_back(new_sp == sp - ctx.get_context().bv_val(4, 64));
    } else if (inst.getAllocatedType()->isDoubleTy() ||
               inst.getAllocatedType()->isPointerTy()) {
      states.push_back(new_sp == sp - ctx.get_context().bv_val(8, 64));
    } else {
      ERROR("Unsupported type", &inst);
    }
    states.push_back(ctx.to_z3_expr(&inst, inst.getFunction()) == new_sp);

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
      for (int i = (width - 1) / 8; i >= 0; --i) {
        auto byte =
            z3::select(memory, ptr_expr + ctx.get_context().bv_val(i, 64));
        bytes.push_back(std::move(byte));
      }

      ctx.update_value_map(
          &inst, width % 8 == 0 ? z3::concat(bytes)
                                : z3::concat(bytes).extract(width - 1, 0));
    } else if (inst.getType()->isPointerTy()) {
      z3::expr_vector bytes(ctx.get_context());
      for (int i = 7; i >= 0; --i) {
        auto byte =
            z3::select(memory, ptr_expr + ctx.get_context().bv_val(i, 64));
        bytes.push_back(std::move(byte));
      }
      ctx.update_value_map(&inst, z3::concat(bytes));
    } else if (inst.getType()->isFloatTy() || inst.getType()->isDoubleTy()) {
      z3::expr_vector bytes(ctx.get_context());
      for (int i = inst.getType()->isFloatTy() ? 3 : 7; i >= 0; --i) {
        auto byte =
            z3::select(memory, ptr_expr + ctx.get_context().bv_val(i, 64));
        bytes.push_back(std::move(byte));
      }
      ctx.update_value_map(
          &inst, z3::sbv_to_fpa(z3::concat(bytes),
                                inst.getType()->isFloatTy()
                                    ? ctx.get_context().fpa_sort<32>()
                                    : ctx.get_context().fpa_sort<64>()));
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

    if (val->getType()->isIntegerTy() || val->getType()->isPointerTy()) {
      auto width = val->getType()->isIntegerTy()
                       ? val->getType()->getIntegerBitWidth()
                       : 64;
      z3::expr_vector new_memory(ctx.get_context());

      // little endian
      for (unsigned int i = 0; i < (width + 7) / 8; ++i) {
        auto byte =
            width >= i * 8 + 8
                ? val_expr.extract(i * 8 + 7, i * 8)
                : (width == 1
                       ? z3::ite(val_expr, ctx.get_context().bv_val(1, 8),
                                 ctx.get_context().bv_val(0, 8))
                       : z3::zext(val_expr.extract(width - 1, i * 8),
                                  8 - (width - i * 8)));
        ctx.inc_memory_state_num();
        new_memory.push_back(
            ctx.get_context().constant(
                ("memory_" + std::to_string(ctx.get_memory_state_num()))
                    .c_str(),
                ctx.get_memory_sort()) ==
            z3::store(memory, ptr_expr + ctx.get_context().bv_val(i, 64),
                      std::move(byte)));
      }

      ctx.update_value_map(&inst, z3::mk_and(new_memory));
    } else if (val->getType()->isFloatTy() || val->getType()->isDoubleTy()) {
      z3::expr_vector new_memory(ctx.get_context());
      auto bv = val_expr.mk_to_ieee_bv();
      for (unsigned int i = 0; i < (val->getType()->isFloatTy() ? 4 : 8); ++i) {
        ctx.inc_memory_state_num();
        new_memory.push_back(
            ctx.get_context().constant(
                ("memory_" + std::to_string(ctx.get_memory_state_num()))
                    .c_str(),
                ctx.get_memory_sort()) ==
            z3::store(memory, ptr_expr + ctx.get_context().bv_val(i, 64),
                      bv.extract(i * 8 + 7, i * 8)));
      }
      ctx.update_value_map(&inst, z3::mk_and(new_memory));
    } else {
      ERROR("Unsupported type", &inst);
    }
  }

  void visitCallBase(CallBase &inst) {
    if (!inst.getType()->isVoidTy()) {
      auto name = ("call_" + std::to_string(ctx.get_call_num()));
      if (inst.getType()->isIntegerTy()) {
        auto width = inst.getType()->getIntegerBitWidth();
        if (width == 1) {
          ctx.update_value_map(&inst,
                               ctx.get_context().bool_const(name.c_str()));
        } else {
          ctx.update_value_map(&inst,
                               ctx.get_context().bv_const(name.c_str(), width));
        }
      } else if (inst.getType()->isPointerTy()) {
        ctx.update_value_map(&inst,
                             ctx.get_context().bv_const(name.c_str(), 64));
      } else {
        ERROR("Unsupported type", &inst);
      }
    }
  }

  void visitUnreachableInst(UnreachableInst &inst) {
    // do nothing here, waku waku
  }

  void visitUnaryOperator(UnaryOperator &inst) {
    switch (inst.getOpcode()) {
    case Instruction::FNeg:
      ctx.update_value_map(
          &inst, -ctx.to_z3_expr(inst.getOperand(0), inst.getFunction()));
      break;
    default:
      ERROR("Unsupported instruction", &inst);
      break;
    }
  }

  void visitIntrinsicInst(IntrinsicInst &inst) {
    // just ignore them
  }

  void visitGetElementPtrInst(GetElementPtrInst &inst) {
    auto base = inst.getPointerOperand();
    auto index = inst.getOperand(1);

    if (!index->getType()->isIntegerTy()) {
      ERROR("Index is not Integer", &inst);
    }

    if (index->getType()->getIntegerBitWidth() != 64) {
      ERROR("Index width is not 64", &inst);
    }

    auto base_expr = ctx.to_z3_expr(base, inst.getFunction());
    auto type = inst.getType();

    if (type->isIntegerTy()) {
      auto size = (type->getIntegerBitWidth() + 7) / 8;
      ctx.update_value_map(
          &inst,
          base_expr + z3::shl(ctx.to_z3_expr(index, inst.getFunction()), size));
    } else if (type->isFloatTy()) {
      ctx.update_value_map(
          &inst,
          base_expr + z3::shl(ctx.to_z3_expr(index, inst.getFunction()), 2));
    } else if (type->isDoubleTy()) {
      ctx.update_value_map(
          &inst,
          base_expr + z3::shl(ctx.to_z3_expr(index, inst.getFunction()), 4));
    } else if (type->isPointerTy()) {
      ctx.update_value_map(
          &inst,
          base_expr + z3::shl(ctx.to_z3_expr(index, inst.getFunction()), 4));
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
    std::string filename = (m.getName() + ".smt2").str();
    std::error_code ec;
    raw_fd_ostream out(filename, ec, sys::fs::OF_Text);

    for (Function &f : m) {
      errs() << "Processing function: " << f.getName() << "\n";
      ctx.incorporate_function(f);

      llvm2smtVisitor visitor(ctx);

      for (auto &bb : f) {
        ctx.reset_memory_state();

        try {
          visitor.visit(bb);
        } catch (InstructionException &e) {
          errs() << e.what();
        }

        ctx.add_rules(bb);
      }
    }

    ctx.dump(out);

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
