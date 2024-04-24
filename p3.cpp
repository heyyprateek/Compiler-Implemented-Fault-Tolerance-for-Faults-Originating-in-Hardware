#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <set>
#include <vector>
#include <utility>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/IR/PassManager.h"
// #include "llvm/Analysis/CGSCCAnalysisManager.h"
// #include "llvm/Analysis/ModuleAnalysisManager.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"

using namespace llvm;

// Define a macro to enable/disable debugging output
#define DEBUG_PRINT_EN false

#if DEBUG_PRINT_EN
#define DEBUG_PRINT(msg) llvm::errs() << msg;
#else
#define DEBUG_PRINT(msg)
#endif

void debugPrintLLVMInstr(Instruction &I)
{
  // convert to string
  std::string InstStr;
  raw_string_ostream OS(InstStr);
  I.print(OS);
  // Use the debug print macro
  DEBUG_PRINT("Instruction:" << InstStr);
}

static LLVMContext Context;

LLVMContext &getGlobalContext()
{
  return Context;
}

static void SoftwareFaultTolerance(Module *);

static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
    InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
    OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
    NoSWFT("no-swft",
           cl::desc("Do not perform SWFT."),
           cl::init(false));

static cl::opt<bool>
    Verbose("verbose",
            cl::desc("Verbose stats."),
            cl::init(false));

static cl::opt<bool>
    NoCheck("no",
            cl::desc("Do not check for valid IR."),
            cl::init(false));

// Use this to enable your bonus code
static cl::opt<bool>
    Bonus("bonus",
          cl::desc("Run the bonus code."),
          cl::init(false));

// Use these to control whether or not parts of your pass run
static cl::opt<bool>
    NoReplicate("no-replicate",
                cl::desc("Do not perform code replication."),
                cl::init(false));

static cl::opt<bool>
    NoControlProtection("no-control-protection",
                        cl::desc("Do not perform control flow protection."),
                        cl::init(false));

void RunO2(Module *M);
void BuildHelperFunctions(Module *);
void summarize(Module *M);
static void ReplicateCode(Function *f);
FunctionCallee AssertFT;
FunctionCallee AssertCFG;

int main(int argc, char **argv)
{
  // Parse command line arguments
  cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

  // Handle creating output files and shutting down properly
  llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

  // LLVM idiom for constructing output file.
  std::unique_ptr<ToolOutputFile> Out;
  std::string ErrorInfo;
  std::error_code EC;
  Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                               sys::fs::OF_None));

  EnableStatistics();

  // Read in module
  SMDiagnostic Err;
  std::unique_ptr<Module> M;
  M = parseIRFile(InputFilename, Err, Context);

  // If errors, fail
  if (M.get() == 0)
  {
    Err.print(argv[0], errs());
    return 1;
  }

  // Run O2 optimizations
  RunO2(M.get());

  BuildHelperFunctions(M.get());

  if (!NoSWFT)
  {
    SoftwareFaultTolerance(M.get());
  }

  // Collect statistics on Module
  summarize(M.get());
  print_csv_file(OutputFilename);

  // if (Verbose)
    PrintStatistics(errs());

  // Verify integrity of Module, do this by default
  if (!NoCheck)
  {
    legacy::PassManager Passes;
    Passes.add(createVerifierPass());
    Passes.run(*M.get());
  }

  // Write final bitcode
  WriteBitcodeToFile(*M.get(), Out->os());
  Out->keep();

  return 0;
}

static void print_csv_file(std::string outputfile)
{
  std::ofstream stats(outputfile + ".stats");
  auto a = GetStatistics();
  for (auto p : a)
  {
    stats << p.first.str() << "," << p.second << std::endl;
  }
  stats.close();
}

// Collect this statistic; increment for each instruction you add.
static llvm::Statistic SWFTAdded = {"", "SWFTadd", "SWFT added instructions"};

/*---------------------------------------------------------
  * Control Flow Protection
---------------------------------------------------------*/
// Global map to store unique IDs for basic blocks
std::unordered_map<BasicBlock *, uint32_t> UniqueIDMap;

// Function to calculate unique ID for a basic block
uint32_t calculateUniqueID(BasicBlock *BB)
{
  // Check if unique ID for BB is already calculated and stored
  auto it = UniqueIDMap.find(BB);
  if (it != UniqueIDMap.end())
  {
    // Return the stored unique ID
    return it->second;
  }

  // If not calculated yet, calculate it
  // uint32_t NumFunc = 0;
  uint32_t NumBB = 0;
  uint32_t SizeBB = 0;

  // Calculate SizeBB: Number of instructions in the block
  for (auto &Inst : *BB)
  {
    if (!isa<Instruction>(&Inst))
      continue;
    ++SizeBB;
  }

  // Calculate NumBB: Unique number identifying the block
  for (auto &FuncBB : *BB->getParent())
  {
    if (&FuncBB == BB)
      break;
    ++NumBB;
  }

  // Calculate NumFunc: Unique number identifying the function
  // for (auto &Func : BB->getParent()->getParent()->getModule()) {
  //     if (&Func == BB->getParent()) break;
  //     ++NumFunc;
  // }

  // Calculate the unique ID based on the provided algorithm
  uint32_t ID = (NumBB << 20) | (SizeBB << 8) | ((NumBB * SizeBB) % 37);
  // uint32_t ID = (NumBB << 20) | (SizeFunc << 16) | (SizeBB << 8) | ((NumBB * SizeBB) % 37);

  // Store the unique ID for future use
  UniqueIDMap[BB] = ID;
  return ID;
}

static void VerifyControlFlow(Function *F, Module *M)
{
  std::unordered_map<BasicBlock *, PHINode *> destPhiMap;
  std::unordered_map<BasicBlock *, PHINode *> diffPhiMap;

  std::unordered_map<BasicBlock *, Value *> newDestMap;
  std::unordered_map<BasicBlock *, Value *> newDiffMap;

  uint32_t assertCFGUniqueID = 0;

  // Traverse over all basic blocks
  for (BasicBlock &BB : *F)
  {
    // Set insert point to the first non-PHI instruction in the basic block
    IRBuilder<> Builder(&*(BB.getFirstNonPHI()));
    Value *currentBBID = ConstantInt::get(Type::getInt32Ty(getGlobalContext()), calculateUniqueID(&BB));

    // Create PHINodes for Dest and Diff
    // Note: Do not specify the number of incoming values yet for both Dest and Diff PHINodes
    if (&BB != &F->getEntryBlock())
    {
      unsigned NumPreds = BB.getSinglePredecessor() ? 1 : std::distance(pred_begin(&BB), pred_end(&BB));
      PHINode *DiffPhi = Builder.CreatePHI(Type::getInt32Ty(getGlobalContext()),
                                           NumPreds,
                                           std::string("Diff") + std::to_string(calculateUniqueID(&BB)));
      // Successful addition of DiffPhi, increment counter
      SWFTAdded++;

      PHINode *DestPhi = Builder.CreatePHI(Type::getInt32Ty(getGlobalContext()),
                                           NumPreds,
                                           std::string("Dest") + std::to_string(calculateUniqueID(&BB)));
      // Successful addition of DestPhi, increment counter
      SWFTAdded++;

      // Insert code to compute newDest
      Value *newDest = Builder.CreateXor(DiffPhi,
                                         DestPhi,
                                         std::string("Dest") + std::to_string(calculateUniqueID(&BB)) + "_new");
      // Successful addition of newDest, increment counter
      SWFTAdded++;

      // Insert comparison and call to assert_cfg_ft
      Instruction *cfg_cmp = dyn_cast<Instruction>(Builder.CreateICmpEQ(newDest, currentBBID, std::string("cfg_cmp") + std::to_string(assertCFGUniqueID)));
      // Successful addition of icmp instruction, increment counter
      SWFTAdded++;
      Value *ft = Builder.CreateZExt(cfg_cmp, IntegerType::getInt32Ty(getGlobalContext()), "ft" + std::to_string(assertCFGUniqueID));
      if (!ft)
      {
        DEBUG_PRINT("Verify Control Flow: %%ft is null\n");
        return;
      }
      else
      {
        // Successful addition of zext instruction, increment counter
        SWFTAdded++;
      }
      if (!newDest)
      {
        DEBUG_PRINT("Verify Control Flow: newDest is null\n");
        return;
      }
      if (!Builder.getInt32(assertCFGUniqueID))
      {
        DEBUG_PRINT("Verify Control Flow: assertCFGUniqueID is null\n");
        return;
      }
      // Call the AssertCFG function if the newDest is not equal to the current BB's unique ID
      std::vector<Value *> args;
      args.push_back(ft);
      args.push_back(newDest);
      args.push_back(Builder.getInt32(assertCFGUniqueID));
      std::vector<llvm::Type *> argTypes = {Builder.getInt32Ty(), Builder.getInt32Ty(), Builder.getInt32Ty()};
      llvm::Type *returnType = llvm::Type::getVoidTy(getGlobalContext());
      FunctionType *FT = FunctionType::get(returnType, argTypes, false);
      Function *F = M->getFunction("assert_cfg_ft");
      Builder.CreateCall(FT, F, args);
      // Successful addition of assert_cfg_ft, increment counter
      SWFTAdded++;

      // Store the PHINodes in maps
      destPhiMap[&BB] = DestPhi;
      diffPhiMap[&BB] = DiffPhi;

      // Store new Dest in map
      newDestMap[&BB] = newDest;
    }

    // Create new Diff register
    Instruction *TermInst = BB.getTerminator();
    Builder.SetInsertPoint(TermInst);
    Value *newDiff;
    if (BranchInst *BI = dyn_cast<BranchInst>(TermInst))
    {
      if (BI->isConditional())
      { // conditional branch
        Value *cmp = BI->getCondition();
        Value *selectInstr = Builder.CreateSelect(cmp,
                                                  Builder.getInt32(calculateUniqueID(BI->getSuccessor(0))),
                                                  Builder.getInt32(calculateUniqueID(BI->getSuccessor(1))),
                                                  "Select" + std::to_string(calculateUniqueID(&BB)));
        // Successful addition of select instruction, increment counter
        SWFTAdded++;
        newDiff = Builder.CreateXor(currentBBID,
                                    selectInstr,
                                    "Diff" + std::to_string(calculateUniqueID(&BB)) + "_value");
        // Successful addition of newDiff, increment counter
        SWFTAdded++;
      }
      else
      { // unconditional branch
        assert(BI->isUnconditional());
        newDiff = Builder.CreateXor(currentBBID,
                                    Builder.getInt32(calculateUniqueID(BI->getSuccessor(0))),
                                    "Diff" + std::to_string(calculateUniqueID(&BB)) + "_value");
        // Successful addition of newDiff, increment counter
        SWFTAdded++;
      }
    }
    else if (SwitchInst *SI = dyn_cast<SwitchInst>(TermInst))
    {
      // Value *newDiff = Builder.CreateSelect(cfg_cmp, ConstantInt::get(Type::getInt32Ty(F->getContext()), calculateUniqueID(SI->getDefaultDest())), DiffPhi);
      // DEBUG_PRINT("switch instruction not supported for control flow yet\n");
      // continue;
      Value *switchCondn = SI->getCondition();
      BasicBlock *defaultDest = SI->getDefaultDest();
      uint32_t switchCmpCount = 0;
      Value *prevSelectInstr = nullptr;
      for (auto &Case : SI->cases())
      {
        BasicBlock *caseDest = Case.getCaseSuccessor();
        Value *caseValue = Case.getCaseValue();
        Value *caseID = Builder.getInt32(calculateUniqueID(caseDest));

        // Create icmp instruction to compare switch condition with case value
        Value *switchCmp = Builder.CreateICmpEQ(switchCondn, caseValue, "switch_cmp" + std::to_string(calculateUniqueID(&BB)) + std::to_string(switchCmpCount));
        // Successful addition of icmp instruction, increment counter
        SWFTAdded++;
        switchCmpCount++;

        // Create select instruction to select case ID if switch condition matches case value
        if (prevSelectInstr == nullptr)
        {
          Value *selectInstr = Builder.CreateSelect(switchCmp, caseID, Builder.getInt32(calculateUniqueID(defaultDest)), "select" + std::to_string(calculateUniqueID(&BB)));
          prevSelectInstr = selectInstr;
          // Successful addition of select instruction, increment counter
          SWFTAdded++;
        }
        else
        {
          Value *selectInstr = Builder.CreateSelect(switchCmp, caseID, prevSelectInstr, "select" + std::to_string(calculateUniqueID(&BB)));
          // prevSelectInstr->replaceAllUsesWith(selectInstr);
          // prevSelectInstr->eraseFromParent();
          prevSelectInstr = selectInstr;
          // Successful addition of select instruction, increment counter
          SWFTAdded++;
        }
      }
      newDiff = Builder.CreateXor(currentBBID, prevSelectInstr, "Diff" + std::to_string(calculateUniqueID(&BB)) + "_value");
      // Successful addition of newDiff, increment counter
      SWFTAdded++;
    }
    else
    {
      DEBUG_PRINT("Error: Unsupported terminator instruction: ");
      debugPrintLLVMInstr(*TermInst);
      DEBUG_PRINT("\n");
      continue;
    }

    // Store new Dest and new Diff in maps
    newDiffMap[&BB] = newDiff;
  }

  // Traverse over the basic blocks again to update PHINode operands
  for (auto &BB : *F)
  {
    if (&BB != &F->getEntryBlock())
    {
      PHINode *DestPhi = destPhiMap[&BB];
      PHINode *DiffPhi = diffPhiMap[&BB];

      // Update operands for DestPhi and DiffPhi
      for (auto pred : llvm::predecessors(&BB))
      {
        DiffPhi->addIncoming(newDiffMap[pred], pred);
        // Check if the predecessor is the entry block
        if (pred == &F->getEntryBlock())
        {
          // If the predecessor is the entry block, add the unique ID of the entry block as the incoming value for DestPhi
          DestPhi->addIncoming(ConstantInt::get(Type::getInt32Ty(getGlobalContext()), calculateUniqueID(pred)), pred);
        }
        else
        {
          // Otherwise, add the newDest value of the predecessor as the incoming value for DestPhi
          DestPhi->addIncoming(newDestMap[pred], pred);
        }
      }
    }
  }
}

/*---------------------------------------------------------
  * Code replication
---------------------------------------------------------*/

static bool doNotReplicate(Instruction *Inst)
{
  switch (Inst->getOpcode())
  {
  case Instruction::Ret:
  case Instruction::Br:
  case Instruction::Switch:
  case Instruction::IndirectBr:
  case Instruction::Invoke:
  case Instruction::Resume:
  case Instruction::Unreachable:
  case Instruction::Store:
  case Instruction::Call:
  case Instruction::Alloca:
    return true;
  default:
    return false;
  }
}

static void ReplicateCode(Function *f, Module *M)
{
  std::map<Instruction *, Instruction *> cloneMap;

  // Iterate over all the basic blocks in the function
  for (auto &BB : *f)
  {
    for (auto it = BB.begin(), end = BB.end(); it != end; ++it)
    {
      Instruction *original = &*it;
      // Skip the instruction if it should not be replicated
      if (doNotReplicate(original))
      {
        DEBUG_PRINT("Skipping instruction: ");
        debugPrintLLVMInstr(*original);
        DEBUG_PRINT("\n");
        continue;
      }
      // Clone the instruction and insert it after the original
      Instruction *clone = original->clone();
      clone->insertBefore(original);
      // // Map the original instructions to its clone
      cloneMap[original] = clone;
      SWFTAdded++;
    }
  }

  // Update the operands of the cloned instructions so that they receive the cloned
  for (auto &origClonePair : cloneMap)
  {
    Instruction *original = origClonePair.first;
    Instruction *clone = origClonePair.second;
    DEBUG_PRINT("Original Instruction: ");
    debugPrintLLVMInstr(*original);
    DEBUG_PRINT("\n");
    // Iterate over all the operands of the cloned instruction
    unsigned operandIter = 0; // type should be unsigned because of comparison with getNumOperands which returns unsigned
    while (operandIter < clone->getNumOperands())
    {
      // If the operand is an instruction that has a clone, update the operand
      Value *operand = clone->getOperand(operandIter);
      Instruction *operandInst = dyn_cast<Instruction>(operand);
      if (operandInst != nullptr)
      {
        if (cloneMap.count(operandInst) != 0)
        { // Check if the operand has a clone in the clone map
          clone->setOperand(operandIter, cloneMap[operandInst]);
        }
        operandIter++; // Increment operandIter after updating operand
      }
      else
      {
        operandIter++; // Increment operandIter for non-instruction operands
      }
    }
    DEBUG_PRINT("Replicated instr with operand: ");
    debugPrintLLVMInstr(*clone);
    DEBUG_PRINT("\n");
  }

  // Insert comparison and call to assert_ft
  uint32_t assertUniqueID = 0;
  for (auto &BB : *f)
  {
    for (auto it = BB.begin(), end = BB.end(); it != end; ++it)
    {
      Instruction *instr = &*it;
      if (cloneMap.count(instr) != 0)
      {
        Instruction *original = instr;
        Instruction *clone = cloneMap[instr];
        IRBuilder<> Builder(&BB);
        // Set the insert point to the next instruction after the original
        if (original->getOpcode() == Instruction::PHI)
        {
          // If the original instruction is a PHI node, set the insert point to the first non-PHI instruction in the basic block
          Builder.SetInsertPoint(original->getParent()->getFirstNonPHI());
        }
        else
        {
          // Otherwise, set the insert point to the next instruction after the original
          Builder.SetInsertPoint(original->getNextNode());
        }
        // Compare the original and the clone
        if (
            original->getType()->isIntegerTy() ||
            original->getType()->isPointerTy() ||
            clone->getType()->isIntegerTy() ||
            clone->getType()->isPointerTy())
        {
          Instruction *cmp = dyn_cast<Instruction>(Builder.CreateICmpEQ(original, clone, "ftcmp" + std::to_string(assertUniqueID)));
          if (cmp != nullptr)
          {
            // For successful insertion of the comparison instruction, increment counter
            SWFTAdded++;
            // Zero extend the result of the comparison
            Value *zextResult = Builder.CreateZExt(cmp, IntegerType::getInt32Ty(getGlobalContext()), "ftcmp_zext" + std::to_string(assertUniqueID));
            // Call the AssertFT function if the original and the clone are not equal
            if (!zextResult)
            {
              DEBUG_PRINT("Replicate Code: zextResult is null\n");
              return;
            }
            else
            {
              // For successful insertion of the zext instruction, increment counter
              SWFTAdded++;
            }
            if (!Builder.getInt32(assertUniqueID))
            {
              DEBUG_PRINT("Replicate Code: assertUniqueID is null\n");
              return;
            }
            // Insert assert_ft call
            std::vector<Value *> args;
            args.push_back(zextResult);
            args.push_back(Builder.getInt32(assertUniqueID));
            std::vector<llvm::Type *> argTypes = {Builder.getInt32Ty(), Builder.getInt32Ty()};
            llvm::Type *returnType = llvm::Type::getVoidTy(getGlobalContext());
            FunctionType *FT = FunctionType::get(returnType, argTypes, false);
            Function *F = M->getFunction("assert_ft");
            Builder.CreateCall(FT, F, args);
            // For successful insertion of the assert_ft instruction, increment counter
            SWFTAdded++;
            // Increment unique ID for the next comparison
            assertUniqueID++;
          }
          else
          {
            DEBUG_PRINT("CreateICmpEQ for ftcmp_zext");
            DEBUG_PRINT(std::to_string(assertUniqueID));
            DEBUG_PRINT(" is null\n");
            return;
          }
        }
      }
    }
  }
}


static void SoftwareFaultTolerance(Module *M)
{
  Module::FunctionListType &list = M->getFunctionList();

  std::vector<Function *> flist;
  // FIND THE ASSERT FUNCTIONS AND DO NOT INSTRUMENT THEM
  for (Module::FunctionListType::iterator it = list.begin(); it != list.end(); it++)
  {
    Function *fptr = &*it;
    if (fptr->size() > 0 && fptr != AssertFT.getCallee() && fptr != AssertCFG.getCallee())
      flist.push_back(fptr);
  }

  // PROTECT CODE IN EACH FUNCTION
  for (std::vector<Function *>::iterator it = flist.begin(); it != flist.end(); it++)
  {
    // CALL A FUNCTION TO REPLICATE CODE in *it
    ReplicateCode(*it, M);
    // CALL A FUNCTION TO PROTECT CONTROL FLOW in *it
    VerifyControlFlow(*it, M);
  }
  if (DEBUG_PRINT_EN)
  {
    M->dump();
  }
}