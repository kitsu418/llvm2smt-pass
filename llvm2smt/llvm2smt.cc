#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <cstdint>
#include <string>
#include <system_error>

using namespace llvm;

namespace {

std::string toSmtType(Type *type) {
  if (type->isIntegerTy()) {
    return "(_ BitVec " + std::to_string(type->getIntegerBitWidth()) + ")";
  } else {
    throw std::runtime_error("Unsupported type");
  }
}

std::string toSmtExpr(ConstantData *constant) {
  if (constant->getType()->isIntegerTy()) {
    auto width = constant->getType()->getIntegerBitWidth();
    return "(_ bv" +
           std::to_string(
               constant->getUniqueInteger().getLimitedValue(1 << width)) +
           " " + std::to_string(width) + ")";
  } else {
    throw std::runtime_error("Unsupported constant type");
  }
}

class llvm2smtVisitor : public InstVisitor<llvm2smtVisitor> {
public:
  llvm2smtVisitor(raw_ostream &o, ModuleSlotTracker &tracker)
      : out(o), slot_tracker(tracker) {}

  void visitBinaryOperator(BinaryOperator &I) {
    assert(I.getNumOperands() == 2);
    std::array<Value *, 2> operands = {I.getOperand(0), I.getOperand(1)};
    assert(operands[0]->getType() == operands[1]->getType());

    out << ";;";
    I.print(out);

    out << "\n(define-fun |%" << slot_tracker.getLocalSlot(&I) << "| () "
        << toSmtType(operands[0]->getType()) << " (";

    switch (I.getOpcode()) {
    case Instruction::Add:
      out << "bvadd ";
      break;
    case Instruction::Sub:
      out << "bvsub ";
      break;
    case Instruction::Mul:
      out << "bvmul ";
      break;
    case Instruction::UDiv:
      out << "bvudiv ";
      break;
    case Instruction::SDiv:
      out << "bvsdiv ";
      break;
    case Instruction::URem:
      out << "bvurem ";
      break;
    case Instruction::SRem:
      out << "bvsrem ";
      break;
    case Instruction::Shl:
      out << "bvshl ";
      break;
    case Instruction::LShr:
      out << "bvlshr ";
      break;
    case Instruction::AShr:
      out << "bvashr ";
      break;
    case Instruction::And:
      out << "bvand ";
      break;
    case Instruction::Or:
      out << "bvor ";
      break;
    case Instruction::Xor:
      out << "bvxor ";
      break;
    case Instruction::FAdd:
    case Instruction::FSub:
    case Instruction::FMul:
    case Instruction::FDiv:
    case Instruction::FRem:
    default:
      break;
    }

    for (uint32_t i = 0; i < 2; ++i) {
      if (auto *constant = dyn_cast<ConstantData>(operands[i])) {
        out << toSmtExpr(constant) << (i ? "))\n" : " ");
      } else if (auto *inst = dyn_cast<Instruction>(operands[i])) {
        out << "|%" << slot_tracker.getLocalSlot(inst) << "|"
            << (i ? "))\n" : " ");
      } else {
        throw std::runtime_error("Unsupported operand type");
      }
    }
  }

private:
  raw_ostream &out;
  ModuleSlotTracker &slot_tracker;
};

class llvm2SmtPass : public PassInfoMixin<llvm2SmtPass> {
public:
  PreservedAnalyses run(Module &m, ModuleAnalysisManager &mam) {
    ModuleSlotTracker mst(&m);

    for (Function &f : m) {
      errs() << "Processing function: " << f.getName() << "\n";
      mst.incorporateFunction(f);

      std::string filename = (f.getName() + ".smt2").str();
      std::error_code ec;
      raw_fd_ostream out(filename, ec, sys::fs::OF_Text);

      llvm2smtVisitor visitor(out, mst);
      visitor.visit(f);
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
