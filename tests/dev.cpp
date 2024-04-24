static void VerifyControlFlow(Function *F) {
    std::unordered_map<BasicBlock*, PHINode*> destPhiMap;
    std::unordered_map<BasicBlock*, PHINode*> diffPhiMap;

    std::unordered_map<BasicBlock*, Value*> newDestMap;
    std::unordered_map<BasicBlock*, Value*> newDiffMap;

    uint32_t assertCFGUniqueID = 0;

    // Traverse over all basic blocks
    for (auto &BB : *F) {
        // Create PHINodes for Dest and Diff
        IRBuilder<> Builder(&*(BB.getFirstInsertionPt()));
        PHINode *DiffPhi = Builder.CreatePHI(Type::getInt32Ty(F->getContext()), 0, "Diff"+std::to_string(calculateUniqueID(&BB)));
        PHINode *DestPhi = Builder.CreatePHI(Type::getInt32Ty(F->getContext()), 0, "Dest"+std::to_string(calculateUniqueID(&BB)));

        // Insert code to compute new Dest
        Value *newDest = Builder.CreateXor(DiffPhi, DestPhi, "Dest"+std::to_string(calculateUniqueID(&BB))+"_value");
        Value *uniqueIDValue = ConstantInt::get(Type::getInt32Ty(BB->getContext()), uniqueID);
        // Instruction *termInst = BB.getTerminator();
        // Value *incomingValue = termInst->getOperand(0);
        // Value *XORResult = Builder.CreateXor(DiffPhi, DestPhi, "XORResult");

        // Insert comparison and call to assert_ft_cfg
        Value *cfg_cmp = Builder.CreateICmpEQ(newDest, uniqueIDValue, "cfg_cmp");
        Instruction *cfg_cmp_inst = dyn_cast<Instruction>(cfg_cmp);
        Value *ft = Builder.CreateZExt(cfg_cmp, Type::getInt32Ty(F->getContext()), "ft");
        // Call the AssertCFG function if the newDest is not equal to the current BB's unique ID
        std::vector<Value*> args;
        args.push_back(Builder.getInt32(ft));
        args.push_back(Builder.getInt32(assertCFGUniqueID));
        Function *F = M->getFunction("AssertCFG");
        Builder.CreateCall(F->getFunctionType(), F, args);

        // Update Diff
        Instruction *TermInst = BB.getTerminator();
        Builder.setInsertPoint(TermInst);
        if (BranchInst *BI = dyn_cast<BranchInst>(TermInst)) {
          if (BI->isConditional()) { // conditional branch
            Value *cmp = BI->getCondition();
            Value *selectInstr = Builder.CreateSelect(cmp,
                                                      Builder.getInt32(calculateUniqueID(BI->getSuccessor(0))), 
                                                      Builder.getInt32(calculateUniqueID(BI->getSuccessor(1))), 
                                                      "Select"+std::to_string(calculateUniqueID(&BB)));
            // DiffPhi->addIncoming(newDiff, &BB);

            Value *newDiff = Builder.CreateXor(Builder.getInt32(calculateUniqueID(&BB)),
                                               selectInstr, 
                                               "Diff"+std::to_string(calculateUniqueID(&BB))+"_value");
          }
          else{ // unconditional branch
          assert(BI->isUnconditional());
          Value *newDiff = Builder.CreateXor(Builder.getInt32(calculateUniqueID(&BB)),
                                             Builder.getInt32(calculateUniqueID(BI->getSuccessor(0))), 
                                             "Diff"+std::to_string(calculateUniqueID(&BB))+"_value");
          }
        }
        else if (SwitchInst *SI = dyn_cast<SwitchInst>(TermInst)) {
          // Value *newDiff = Builder.CreateSelect(cfg_cmp, ConstantInt::get(Type::getInt32Ty(F->getContext()), calculateUniqueID(SI->getDefaultDest())), DiffPhi);
        }
        else {
          // do something
          errs() << "Error: Unsupported terminator instruction!\n";
        }
        Value *newDiff;
        if (/* conditional branch */) {
            newDiff = Builder.CreateSelect(cfg_cmp, ConstantInt::get(Type::getInt32Ty(F->getContext()), /* destination block ID */), DiffPhi);
        } else {
            newDiff = ConstantInt::get(Type::getInt32Ty(F->getContext()), /* destination block ID */);
        }

        // Insert code at the end of the block to compute the new Diff
        IRBuilder<> endBuilder(BB.getTerminator()->getNextNode());
        DiffPhi->addIncoming(newDiff, &BB);

        // Store Dest and Diff in maps
        destPhiMap[&BB] = DestPhi;
        diffPhiMap[&BB] = DiffPhi;
        
        // Store new Dest and new Diff in maps
        newDestMap[&BB] = newDest;
        newDiffMap[&BB] = newDiff;
    }

    // Traverse over the basic blocks again to update PHINode operands
    for (auto &BB : *F) {
        PHINode *DestPhi = destPhiMap[&BB];
        PHINode *DiffPhi = diffPhiMap[&BB];

        // Update operands for DestPhi and DiffPhi
        for (auto pred : predecessors(&BB)) {
            BasicBlock *predBB = pred;
            DestPhi->addIncoming(newDestMap[predBB], predBB);
            DiffPhi->addIncoming(newDiffMap[predBB], predBB);
        }
    }
}