#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/Obfuscation/DopLoop.h"
#include "llvm/Transforms/Obfuscation/Utils.h"

using namespace llvm;

namespace {
    struct DopLoop : public FunctionPass {
        static char ID;
        bool flag;
        DopLoop() : FunctionPass(ID) {}
        DopLoop(bool flag) : FunctionPass(ID) {this->flag = flag; DopLoop();}

        bool runOnFunction(Function &F) override {
            if(toObfuscate(flag,&F,"doploop")) {
                StringRef *sr = new StringRef("fun");
                if (F.getName().equals(*sr)) {
                    addDopLoop(F);
                    return true;
                }
            }
            return false;
        }
        void addDopLoop(Function &F) {
            BasicBlock *loopBB, *preBB;
            for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                if (isloop(bb)) {
                    loopBB = bb;
                    errs() << "find a loop in BB" << "\n";
                } else {
                    errs() << "not a loop" << "\n";
                }
            }

            // search for the BB before the loopBB
            for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                Instruction *bbend = bb->getTerminator();
                BranchInst *br = dyn_cast<BranchInst>(bbend);

                if (br && br->isUnconditional() && br->getSuccessor(0) == loopBB) {
                    preBB = bb;
                    break;
                }
                
            }

            // find the local variable for dop
            // the first store instruction (Can be improved!)
            BasicBlock::iterator insertAlloca;
            for (BasicBlock::iterator i = preBB->begin(), e = preBB->end(); i != e; ++i) {
                unsigned opcode = i->getOpcode();
                if (opcode == Instruction::Store) {
                    insertAlloca = i;
                    break;
                }
            }

            // insert allca for the dop pointers
            BasicBlock::iterator ii = std::next(insertAlloca);
            AllocaInst* dop1 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop1");
            AllocaInst* dop2 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop2");
            AllocaInst* dop1br1 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop1br1");
            AllocaInst* dop2br1 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop2br1");

            preBB->getInstList().insert(ii, dop1);
            preBB->getInstList().insert(ii, dop2);
            preBB->getInstList().insert(ii, dop1br1);
            preBB->getInstList().insert(ii, dop2br1);

            // store the variable's address to the dop pointers
            StoreInst* dop1st = new StoreInst(insertAlloca->getOperand(1), dop1, false, ii);
            StoreInst* dop2st = new StoreInst(insertAlloca->getOperand(1), dop2, false, ii);
            StoreInst* dop1br1st = new StoreInst(insertAlloca->getOperand(1), dop1br1, false, ii);
            StoreInst* dop2br1st = new StoreInst(insertAlloca->getOperand(1), dop2br1, false, ii);

            int num = 6;
            BasicBlock::iterator splitpt1, splitpt2;
            for (BasicBlock::iterator i = loopBB->begin(), e = loopBB->end(); num != 0; --num) {
                ++i;--e;
                if (num == 1) {
                    splitpt1 = i;
                    splitpt2 = e;
                }
            }
            splitpt2--;

            BasicBlock *obfBB1, *normalBB, *obfBB2, *loopend;
            Twine *var1 = new Twine("obfBB1");
            obfBB1 = loopBB->splitBasicBlock(loopBB->begin(), *var1);
	    errs() << "split obfBB1." << '\n';
            Twine *var2 = new Twine("normalBB");
            normalBB = obfBB1->splitBasicBlock(splitpt1, *var2);
	    errs() << "split normalBB." << '\n';

            BasicBlock *newhead, *newtail;
            std::map<Instruction*, Instruction*> fixssa1;
            insertDOP(obfBB1, normalBB, 2, dop1, dop2, &newhead, &newtail, &fixssa1, F);
            loopBB->getTerminator()->eraseFromParent();
            BranchInst::Create(newhead, loopBB);
	    errs() << "DOP1 inserted." << '\n';

            Twine *var3 = new Twine("obfBB2");
            obfBB2 = normalBB->splitBasicBlock(splitpt2, *var3);
            loopend = obfBB2->splitBasicBlock(obfBB2->getTerminator(), "");

            BasicBlock *newhead2, *newtail2;
            std::map<Instruction*, Instruction*> fixssa2;
            insertDOP(obfBB2, loopend, 2, dop1br1, dop2br1, &newhead2, &newtail2, &fixssa2, F);
            normalBB->getTerminator()->eraseFromParent();
            BranchInst::Create(newhead2, normalBB);
	    errs() << "DOP2 inserted." << '\n';
        }

        bool isloop(BasicBlock *bb);
        void insertDOP(BasicBlock *obfBB, BasicBlock *postBB, int offset,
                              AllocaInst *dop1, AllocaInst *dop2,
                              BasicBlock **head, BasicBlock **tail,
                              std::map<Instruction*, Instruction*> *fixssa,
                              Function &F);
    };
}

// check wether a basic block is a loop body
bool DopLoop::isloop(BasicBlock *bb)
{
    Instruction *bbend = bb->getTerminator();
    BranchInst *br = dyn_cast<BranchInst>(bbend);

    // skip the unconditional jumps
    while (br && br->isUnconditional()) {
        Instruction *next = br->getSuccessor(0)->getTerminator();
        BranchInst *nextbr = dyn_cast<BranchInst>(next);
        br = nextbr ? nextbr : NULL;
    }

    if (br) {
        int succnum = br->getNumSuccessors();
        for (int i = 0; i < succnum; ++i) {
            if (br->getSuccessor(i) == bb)
                return true;
        }
        return false;
    } else
        return false;
}

// Insert dynamic opaque predicate into obfBB
void DopLoop::insertDOP(BasicBlock *obfBB, BasicBlock *postBB, int offset,
                      AllocaInst *dop1, AllocaInst *dop2,
                      BasicBlock **head, BasicBlock **tail,
                      std::map<Instruction*, Instruction*> *fixssa,
                      Function &F)
{
    // create the first dop basic block
    BasicBlock *dop1BB = BasicBlock::Create(F.getContext(), "dop1BB", &F, obfBB);
    LoadInst *dop1p = new LoadInst(dop1, "", false, 4, dop1BB);
    LoadInst *dop1deref = new LoadInst(dop1p, "", false, 4, dop1BB);
    *head = dop1BB;

    // create alter BB from cloneing the obfBB
    const Twine & name = "alter";
    ValueToValueMapTy VMap;
    BasicBlock* alterBB = llvm::CloneBasicBlock(obfBB, VMap, name, &F);

    for (BasicBlock::iterator i = alterBB->begin(), e = alterBB->end() ; i != e; ++i) {
        // Loop over the operands of the instruction
        for(User::op_iterator opi = i->op_begin (), ope = i->op_end(); opi != ope; ++opi) {
            // get the value for the operand
            Value *v = MapValue(*opi, VMap,  RF_None, 0);
            if (v != 0){
                *opi = v;
            }
        }
    }

    // Map instructions in obfBB and alterBB
    for (BasicBlock::iterator i = obfBB->begin(), j = alterBB->begin(),
             e = obfBB->end(), f = alterBB->end(); i != e && j != f; ++i, ++j) {
        // errs() << "install fix ssa:" << "\n";
        (*fixssa)[i] = j;
    }
    // Fix use values in alterBB
    for (BasicBlock::iterator i = alterBB->begin(), e = alterBB->end() ; i != e; ++i) {
        for (User::op_iterator opi = i->op_begin(), ope = i->op_end(); opi != ope; ++opi) {
            Instruction *vi = dyn_cast<Instruction>(*opi);
            if (fixssa->find(vi) != fixssa->end()) {
                *opi = (Value*)(*fixssa)[vi];
            }
        }
    }

    // create the first dop at the end of dop1BB
    Twine *var3 = new Twine("dopbranch1");
    Value *rvalue = ConstantInt::get(Type::getInt32Ty(F.getContext()), 0);
    // preBB->getTerminator()->eraseFromParent();
    ICmpInst *dopbranch1 = new ICmpInst(*dop1BB, CmpInst::ICMP_SGT , dop1deref, rvalue, *var3);
    BranchInst::Create(obfBB, alterBB, dopbranch1, dop1BB);

    // split the obfBB and alterBB with an offset
    BasicBlock::iterator splitpt1 = obfBB->begin(),
                         splitpt2 = alterBB->begin();
    BasicBlock *obfBB2, *alterBB2;
    // int num = 2;
    int n = offset;
    for (BasicBlock::iterator e = obfBB->end(); splitpt1 != e && n > 0; ++splitpt1, --n) ;
    n = offset+1;
    for (BasicBlock::iterator e = alterBB->end(); splitpt2 != e && n > 0; ++splitpt2, --n) ;
    Twine *var4 = new Twine("obfBB2");
    obfBB2 = obfBB->splitBasicBlock(splitpt1, *var4);
    Twine *var5 = new Twine("obfBBalter2");
    alterBB2 = alterBB->splitBasicBlock(splitpt2, *var5);

    // create the second dop as a separate BB
    BasicBlock *dop2BB = BasicBlock::Create(F.getContext(), "dop2BB", &F, obfBB2);
    LoadInst *dop2p = new LoadInst(dop2, "", false, 4, dop2BB);
    LoadInst *dop2deref = new LoadInst(dop2p, "", false, 4, dop2BB);
    Twine *var6 = new Twine("dopbranch2");
    Value *rvalue2 = ConstantInt::get(Type::getInt32Ty(F.getContext()), 0);
    ICmpInst *dopbranch2 = new ICmpInst(*dop2BB, CmpInst::ICMP_SGT , dop2deref, rvalue2, *var6);
    BranchInst::Create(obfBB2, alterBB2, dopbranch2, dop2BB);

    // connect obfBB and alterBB to the second dop
    obfBB->getTerminator()->eraseFromParent();
    BranchInst::Create(dop2BB, obfBB);
    alterBB->getTerminator()->eraseFromParent();
    BranchInst::Create(dop2BB, alterBB);

    // insert phi node and update uses in postBB
    BasicBlock::iterator ii = postBB->begin();
    std::map<Instruction*, PHINode*> insertedPHI;
    for (BasicBlock::iterator i = postBB->begin(), e = postBB->end() ; i != e; ++i) {
        for(User::op_iterator opi = i->op_begin(), ope = i->op_end(); opi != ope; ++opi) {
            Instruction *p;
            Instruction *vi = dyn_cast<Instruction>(*opi);
            PHINode *q;
            if (fixssa->find(vi) != fixssa->end()) {
                PHINode *fixnode;
                p = (*fixssa)[vi];
                if (insertedPHI.find(vi) == insertedPHI.end()) {
                    q = insertedPHI[vi];
                    fixnode = PHINode::Create(vi->getType(), 2, "", ii);
                    fixnode->addIncoming(vi, vi->getParent());
                    fixnode->addIncoming(p, p->getParent());
                    insertedPHI[vi] = fixnode;
                } else {
                    fixnode = q;
                }
                *opi = (Value*)fixnode;
            }
        }
    }
}

char DopLoop::ID = 0;
static RegisterPass<DopLoop> X("DopLoop", "Dynamic opaque predicate obfuscation Pass for straight line code");

Pass *llvm::createDopLoop() {
    return new DopLoop();
}

Pass *llvm::createDopLoop(bool flag) {
    return new DopLoop(flag);
}
