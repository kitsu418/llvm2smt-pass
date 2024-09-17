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
  InstructionException(const char *msg, const Value *v = nullptr)
      : std::runtime_error(msg) {
    raw_string_ostream os(_msg);
    os << msg << ": ";
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
            domain.push_back(ctx.bv_sort(var->getType()->getIntegerBitWidth()));
          } else {
            throw InstructionException("Unsupported type", var);
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
    if (auto *constant = dyn_cast<Constant>(v)) {
      if (auto constant_int = dyn_cast<ConstantInt>(constant)) {
        auto width = constant_int->getType()->getIntegerBitWidth();
        z3::expr e = ctx.bv_val(is_signed ? constant_int->getSExtValue()
                                          : constant_int->getZExtValue(),
                                width);
        value_map.insert({v, std::move(e)});
        return value_map.at(v);
      } else {
        throw InstructionException("Unsupported type", v);
      }
    } else if (auto *inst = dyn_cast<Instruction>(v)) {
      if (v->getType()->isIntegerTy()) {
        auto width = v->getType()->getIntegerBitWidth();
        z3::expr e = ctx.bv_const(get_value_name(v, f).c_str(), width);
        value_map.insert({v, std::move(e)});
        return value_map.at(v);
      } else {
        throw InstructionException("Unsupported type", v);
      }
    } else if (auto *arg = dyn_cast<Argument>(v)) {
      if (v->getType()->isIntegerTy()) {
        auto width = v->getType()->getIntegerBitWidth();
        z3::expr e = ctx.bv_const(get_value_name(v, f).c_str(), width);
        value_map.insert({v, std::move(e)});
        return value_map.at(v);
      } else {
        throw InstructionException("Unsupported type", v);
      }
    } else {
      throw InstructionException("Unsupported type", v);
    }
  }

  void update_value_map(Value *v, z3::expr &&e) {
    value_map.insert({v, std::move(e)});
  }

  bool has_value(Value *v) const noexcept {
    return value_map.count(v) > 0;
  }

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
        domain.push_back(
            ctx.bv_const(get_value_name(lv, bb.getParent()).c_str(), width));
      } else {
        throw InstructionException("Unsupported type", lv);
      }
    }
    body.push_back(relation_map.at(&bb)(std::move(domain)));

    for (auto &inst : bb) {
      if (has_value(&inst)) {
        inst.print(errs());
        auto type = inst.getType();
        if (type->isIntegerTy()) {
          auto rhs = get_z3_expr(&inst, bb.getParent());
          auto width = type->getIntegerBitWidth();
          auto lhs = ctx.bv_const(get_value_name(&inst, bb.getParent()).c_str(),
                                  width);
          body.push_back(lhs == rhs);
        } else {
          throw InstructionException("Unsupported type", &inst);
        }
      }
    }

    auto body_and = z3::mk_and(body);

    for (auto succ : successors(&bb)) {
      z3::expr_vector head_args(ctx);
      for (auto var : lva.get_in(succ)) {
        if (var->getType()->isIntegerTy()) {
          auto width = var->getType()->getIntegerBitWidth();
          head_args.push_back(
              ctx.bv_const(get_value_name(var, bb.getParent()).c_str(), width));
        } else {
          throw InstructionException("Unsupported type", var);
        }
      }

      clauses.push_back(z3::implies(
          std::move(body_and), relation_map.at(succ)(std::move(head_args))));
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

  void visitBinaryOperator(BinaryOperator &I) {
    assert(I.getNumOperands() == 2);
    auto op1 = I.getOperand(0);
    auto op2 = I.getOperand(1);
    assert(op1->getType() == op2->getType());

    auto expr1 = ctx.get_z3_expr(op1, I.getFunction(), !I.hasNoSignedWrap());
    auto expr2 = ctx.get_z3_expr(op2, I.getFunction(), !I.hasNoSignedWrap());

    switch (I.getOpcode()) {
    case Instruction::Add:
      ctx.update_value_map(&I, expr1 + expr2);
      break;
    case Instruction::Sub:
      ctx.update_value_map(&I, expr1 - expr2);
      break;
    case Instruction::Mul:
      ctx.update_value_map(&I, expr1 * expr2);
      break;
    case Instruction::UDiv:
      ctx.update_value_map(&I, z3::udiv(expr1, expr2));
      break;
    case Instruction::SDiv:
      ctx.update_value_map(&I, expr1 / expr2);
      break;
    case Instruction::URem:
      ctx.update_value_map(&I, z3::urem(expr1, expr2));
      break;
    case Instruction::SRem:
      ctx.update_value_map(&I, z3::srem(expr1, expr2));
      break;
    case Instruction::Shl:
      ctx.update_value_map(&I, z3::shl(expr1, expr2));
      break;
    case Instruction::LShr:
      ctx.update_value_map(&I, z3::lshr(expr1, expr2));
      break;
    case Instruction::AShr:
      ctx.update_value_map(&I, z3::ashr(expr1, expr2));
      break;
    case Instruction::And:
      ctx.update_value_map(&I, expr1 & expr2);
      break;
    case Instruction::Or:
      ctx.update_value_map(&I, expr1 | expr2);
      break;
    case Instruction::Xor:
      ctx.update_value_map(&I, expr1 ^ expr2);
      break;
    case Instruction::FAdd:
    case Instruction::FSub:
    case Instruction::FMul:
    case Instruction::FDiv:
    case Instruction::FRem:
    default:
      throw InstructionException("Unsupported instruction", &I);
      break;
    }
  }

  void visitInstruction(Instruction &I) {
    if (I.isBinaryOp()) {
      visitBinaryOperator(cast<BinaryOperator>(I));
    } else {
      throw InstructionException("Unsupported instruction", &I);
    }
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
