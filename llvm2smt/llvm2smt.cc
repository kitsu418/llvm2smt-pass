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
      : fp(z3::fixedpoint(ctx)), slot_tracker(ModuleSlotTracker(m)) {
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
          } else {
            // ERROR("Unsupported type", var);
          }
        }

        relation_map.insert(
            {&bb, ctx.function(get_value_name(&bb, bb.getParent()).c_str(),
                               domain, ctx.bool_sort())});
        fp.register_relation(relation_map.at(&bb));
      }
    }
  }

  z3::expr get_z3_expr(Value *v, Function *f, bool is_signed = true) {
    auto it = value_map.find(v);
    if (it != value_map.end()) {
      return it->second;
    }
    if (isa<Constant>(v)) {
      if (auto constant_int = dyn_cast<ConstantInt>(v)) {
        auto width = constant_int->getType()->getIntegerBitWidth();
        if (width == 1) {
          value_map.insert(
              {v, ctx.bool_val(constant_int->getZExtValue() != 0)});
        } else {
          value_map.insert(
              {v, ctx.bv_val(is_signed ? constant_int->getSExtValue()
                                       : constant_int->getZExtValue(),
                             width)});
        }
        return value_map.at(v);
      } else {
        ERROR("Unsupported type", v);
      }
    } else if (isa<Instruction>(v) || isa<Argument>(v)) {
      if (v->getType()->isIntegerTy()) {
        auto width = v->getType()->getIntegerBitWidth();
        if (width == 1) {
          value_map.insert({v, ctx.bool_const(get_value_name(v, f).c_str())});
        } else {
          value_map.insert(
              {v, ctx.bv_const(get_value_name(v, f).c_str(), width)});
        }
        return value_map.at(v);
      } else {
        ERROR("Unsupported type", v);
      }
    } else {
      ERROR("Unsupported type", v);
    }
  }

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
      } else {
        ERROR("Unsupported type", lv);
      }
    }
    body.push_back(relation_map.at(&bb)(std::move(domain)));

    for (auto &inst : bb) {
      if (has_value(&inst)) {
        auto type = inst.getType();
        if (type->isIntegerTy()) {
          auto rhs = get_z3_expr(&inst, bb.getParent());
          auto width = type->getIntegerBitWidth();
          auto lhs =
              width == 1
                  ? ctx.bool_const(
                        get_value_name(&inst, bb.getParent()).c_str())
                  : ctx.bv_const(get_value_name(&inst, bb.getParent()).c_str(),
                                 width);
          body.push_back(lhs == rhs);
        } else if (type->isVoidTy()) {
          continue;
        } else {
          ERROR("Unsupported type", &inst);
        }
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
        } else {
          ERROR("Unsupported type", var);
        }
      }

      if (auto branch = dyn_cast<BranchInst>(terminatior)) {
        if (branch->isConditional()) {
          auto cond = branch->getCondition();
          auto expr = get_z3_expr(cond, bb.getParent());
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
    bb.print(errs());

    return clauses;
  }

private:
  z3::context ctx{};
  z3::fixedpoint fp;
  std::map<Value *, z3::expr> value_map{};
  ModuleSlotTracker slot_tracker;
  std::map<BasicBlock *, z3::func_decl> relation_map{};
  std::map<Function *, LiveVariableAnalysis> live_vars_map{};
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
        ctx.get_z3_expr(op1, inst.getFunction(), !inst.hasNoSignedWrap());
    auto expr2 =
        ctx.get_z3_expr(op2, inst.getFunction(), !inst.hasNoSignedWrap());

    switch (inst.getOpcode()) {
    case Instruction::Add:
      ctx.update_value_map(&inst, expr1 + expr2);
      break;
    case Instruction::Sub:
      ctx.update_value_map(&inst, expr1 - expr2);
      break;
    case Instruction::Mul:
      ctx.update_value_map(&inst, expr1 * expr2);
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
    default:
      ERROR("Unsupported instruction", &inst);
      break;
    }
  }

  void visitICmp(ICmpInst &inst) {
    assert(inst.getNumOperands() == 2);
    auto op1 = inst.getOperand(0);
    auto op2 = inst.getOperand(1);
    assert(op1->getType() == op2->getType());

    auto expr1 =
        ctx.get_z3_expr(op1, inst.getFunction(), !inst.hasNoSignedWrap());
    auto expr2 =
        ctx.get_z3_expr(op2, inst.getFunction(), !inst.hasNoSignedWrap());

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
    case CmpInst::BAD_FCMP_PREDICATE:
    case CmpInst::BAD_ICMP_PREDICATE:
      ERROR("Bad predicate", &inst);
      break;
    }
  }

  void visitBranchInst(BranchInst &inst) {
    ctx.update_value_map(&inst, ctx.get_context().bool_val(true));
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

      try {
        visitor.visit(f);
      } catch (InstructionException &e) {
        errs() << e.what();
      }

      for (auto &bb : f) {
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
