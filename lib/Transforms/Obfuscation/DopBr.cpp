#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/Obfuscation/DopBr.h"
#include "llvm/Transforms/Obfuscation/Utils.h"

using namespace llvm;

namespace {
    struct DopBr : public FunctionPass {
        static char ID;
        bool flag;
        DopBr() : FunctionPass(ID) {}
        DopBr(bool flag) : FunctionPass(ID) {this->flag = flag; DopBr();}

        bool runOnFunction(Function &F) override {
            if(toObfuscate(flag,&F,"dopbr")) {
                StringRef *sr = new StringRef("fun");
                if (F.getName().equals(*sr)) {
                    addDopBranch(F);
                    return true;
                }
            }
            return false;
        }

        // build dependence
        void builddep(Instruction *iuse, std::set<Instruction*> &idep);

        // insert DOP into obfBB
        void insertDOP(BasicBlock *obfBB, BasicBlock *postBB, int offset,
                              AllocaInst *dop1, AllocaInst *dop2,
                              BasicBlock **head, BasicBlock **tail,
                              std::map<Instruction*, Instruction*> *fixssa,
                              Function &F);

        // add dynamic opaque predicates to 
        void addDopBranch(Function &F) {
            BranchInst *ibr;
            BasicBlock *preBB, *postBB, *obfBB;
            std::set<Instruction *> dep;
            for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                ibr = dyn_cast<BranchInst>(bb->getTerminator());
                if (ibr && ibr->isConditional()) {
                    errs() << "find a branch in BB" << "\n";
		    break;
                }
            }
            builddep(ibr, dep);
            
	    errs() << "dep is built." << '\n';
            for (std::set<Instruction *>::iterator i = dep.begin(); i != dep.end(); ++i) {
                errs() << **i << "\n";
            }

            // find the last inst before ibr but not affect it
            preBB = ibr->getParent();
            BasicBlock::iterator keyinst = ibr;
            for (BasicBlock::iterator j = preBB->begin(); keyinst != j; --keyinst) {
	      if (dep.find(keyinst) == dep.end()) {
                    break;
                }
            }
            Instruction *kinst = dyn_cast<Instruction>(keyinst);
            errs() << "keyinst is: " << *kinst << '\n';

            // find the local variable for dop
            // the first store instruction (Can be improved!)
            BasicBlock::iterator insertAlloca;
            for (BasicBlock::iterator i = ibr->getParent()->begin(), e = ibr->getParent()->end(); i != e; ++i) {
                unsigned opcode = i->getOpcode();
                if (opcode == Instruction::Store) {
                    insertAlloca = i;
                    break;
                }
            }

            // split the snippet between the first store and the branch
            // as the obfBB
            BasicBlock::iterator preBBend = std::next(insertAlloca);
            Twine *var1 = new Twine("obfBB");
            obfBB = preBB->splitBasicBlock(preBBend, *var1);
            Twine *var2 = new Twine("postBB");
            postBB = obfBB->splitBasicBlock(ibr, *var2);


            // insert allca for the dop pointers
            BasicBlock::iterator ii = std::next(insertAlloca);
            AllocaInst* dop1 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop1");
            AllocaInst* dop2 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop2");
            AllocaInst* dop1br1 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop1br1");
            AllocaInst* dop2br1 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop2br1");
            AllocaInst* dop1br2 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop1br2");
            AllocaInst* dop2br2 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop2br2");

            preBB->getInstList().insert(ii, dop1);
            preBB->getInstList().insert(ii, dop2);
            preBB->getInstList().insert(ii, dop1br1);
            preBB->getInstList().insert(ii, dop2br1);
            preBB->getInstList().insert(ii, dop1br2);
            preBB->getInstList().insert(ii, dop2br2);

            // store the variable's address to the dop pointers
            StoreInst* dop1st = new StoreInst(insertAlloca->getOperand(1), dop1, false, ii);
            StoreInst* dop2st = new StoreInst(insertAlloca->getOperand(1), dop2, false, ii);
            StoreInst* dop1br1st = new StoreInst(insertAlloca->getOperand(1), dop1br1, false, ii);
            StoreInst* dop2br1st = new StoreInst(insertAlloca->getOperand(1), dop2br1, false, ii);
            StoreInst* dop1br2st = new StoreInst(insertAlloca->getOperand(1), dop1br2, false, ii);
            StoreInst* dop2br2st = new StoreInst(insertAlloca->getOperand(1), dop2br2, false, ii);

            // load dop1's value
            // LoadInst* dop1p = new LoadInst(dop1, "", false, 4, ii);
            // LoadInst* dop1deref = new LoadInst(dop1p, "", false, 4, ii);

            std::map<Instruction*, Instruction*> fixssa;
            BasicBlock *newhead, *newtail;
            insertDOP(obfBB, postBB, 2, dop1, dop2, &newhead, &newtail, &fixssa, F);
	    errs() << "DOP inserted." << '\n';

            // connect preBB to the new head
            preBB->getTerminator()->eraseFromParent();
            BranchInst::Create(newhead, preBB);

            // insert dop1br1 and dop2br1 to the true branch
            BasicBlock *br1BB = ibr->getSuccessor(0);
            BasicBlock *obfBBbr1 = br1BB->splitBasicBlock(br1BB->begin(), "");
            BasicBlock *br1succ = br1BB->getTerminator()->getSuccessor(0);
            BasicBlock *newheadbr1, *newtailbr1;
            std::map<Instruction*, Instruction*> fixssabr1;
            insertDOP(obfBBbr1, br1succ, 2, dop1br1, dop2br1, &newheadbr1, &newtailbr1, &fixssabr1, F);
            br1BB->getTerminator()->eraseFromParent();
            BranchInst::Create(newheadbr1, br1BB);

            // insert keyinst into the true branch of dop1br1
            // kinst->eraseFromParent();
	    // errs() << "remove keyinst" << '\n';
            // BasicBlock *iBB = newheadbr1->getTerminator()->getSuccessor(0);
	    // errs() << "get new head" << '\n';
            // ii = iBB->begin();
	    // errs() << "set ii" << '\n';
            // Instruction *kinstclone = kinst->clone();
            // iBB->getInstList().insert(ii, kinstclone);
	    // errs() << "insert key inst" << '\n';

            // insert dop1br2 and dop2br2 to the false branch
            BasicBlock *br2BB = ibr->getSuccessor(1);
            BasicBlock *obfBBbr2 = br2BB->splitBasicBlock(br2BB->begin(), "");
            BasicBlock *br2succ = br2BB->getTerminator()->getSuccessor(0);
            BasicBlock *newheadbr2, *newtailbr2;
            std::map<Instruction*, Instruction*> fixssabr2;
            insertDOP(obfBBbr2, br2succ, 2, dop1br2, dop2br2, &newheadbr2, &newtailbr2, &fixssabr2, F);
            br2BB->getTerminator()->eraseFromParent();
            BranchInst::Create(newheadbr2, br2BB);
        }
    };
}

// Insert dynamic opaque predicate into obfBB
void DopBr::insertDOP(BasicBlock *obfBB, BasicBlock *postBB, int offset,
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

// build a set idep, which contains all instructions that iuse depends on
void DopBr::builddep(Instruction *iuse, std::set<Instruction*> &idep)
{
    // errs() << "Enter builddep" << '\n';

    Instruction *vi = iuse;
    Instruction *op0, *op1;
    if (vi == NULL) {
        errs() << "No instruction" << '\n';
        return;
    } else {
        switch (vi->getOpcode()) {
        case Instruction::Add:
            errs() << "Add" << '\n';
            idep.insert(vi);
            op0 = dyn_cast<Instruction>(vi->getOperand(0));
            op1 = dyn_cast<Instruction>(vi->getOperand(1));
            builddep(op0, idep);
            builddep(op1, idep);
            return;
        case Instruction::Sub:
            errs() << "Sub" << '\n';
            idep.insert(vi);
            op0 = dyn_cast<Instruction>(vi->getOperand(0));
            op1 = dyn_cast<Instruction>(vi->getOperand(1));
            builddep(op0, idep);
            builddep(op1, idep);
            return;
        case Instruction::Mul:
            errs() << "Mul" << '\n';
            idep.insert(vi);
            op0 = dyn_cast<Instruction>(vi->getOperand(0));
            op1 = dyn_cast<Instruction>(vi->getOperand(1));
            builddep(op0, idep);
            builddep(op1, idep);
            return;
        case Instruction::Br:
            errs() << "Br" << '\n';
            idep.insert(vi);
            op0 = dyn_cast<Instruction>(vi->getOperand(0));
            builddep(op0, idep);
            return;
        case Instruction::Load:
        {
            errs() << "Load" << '\n';
            idep.insert(vi);
            BasicBlock::iterator i = vi;
            for (BasicBlock::iterator j = vi->getParent()->end(); i != j; --i) {
                if (i->getOpcode() == Instruction::Store && i->getOperand(1) == vi->getOperand(0)) {
                    break;
                }
            }
            op0 = dyn_cast<Instruction>(i);
            builddep(op0, idep);
            return;
        }
        case Instruction::Store:
            errs() << "Store" << '\n';
            idep.insert(vi);
            op0 = dyn_cast<Instruction>(vi->getOperand(0));
            builddep(op0, idep);
            return;
        case Instruction::Alloca:
            errs() << "Alloca" << '\n';
            idep.insert(vi);
            return;
        case Instruction::ICmp:
            errs() << "ICmp" << '\n';
            idep.insert(vi);
            op0 = dyn_cast<Instruction>(vi->getOperand(0));
            builddep(op0, idep);
            return;
        default:
	    errs() << "Unknown" << '\n';
            return;
        }
    }
}

char DopBr::ID = 0;
static RegisterPass<DopBr> X("DopBr", "Dynamic opaque predicate obfuscation Pass for straight line code");

Pass *llvm::createDopBr() {
    return new DopBr();
}

Pass *llvm::createDopBr(bool flag) {
    return new DopBr(flag);
}
