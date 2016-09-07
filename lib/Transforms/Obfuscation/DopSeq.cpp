#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/Obfuscation/DopSeq.h"
#include "llvm/Transforms/Obfuscation/Utils.h"

using namespace llvm;

namespace {
    struct DopSeq : public FunctionPass {
        static char ID;
        bool flag;
        DopSeq() : FunctionPass(ID) {}
        DopSeq(bool flag) : FunctionPass(ID) {this->flag = flag; DopSeq();}

        bool runOnFunction(Function &F) override {
            if(toObfuscate(flag,&F,"dopseq")) {
                StringRef *sr = new StringRef("fun");
                if (F.getName().equals(*sr)) {
                    errs() << "Hello: ";
                    errs().write_escaped(F.getName()) << '\n';
                    
                    addDopSeq(F);
                        
                    return true;

                // for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                //     for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
                //         errs().write_escaped(i->getOpcodeName()) << '\n';
                //     }
                // }
                }
            }
            return false;
        }

        // add dynamic opaque predicate to sequential code
        void addDopSeq(Function &F) {
            bool firstStore = true;
            Value *covar;
            BasicBlock *preBB, *postBB, *obfBB;
            BasicBlock::iterator preBBend, obfBBend, insertAlloca;

            // split the snippet between two store instructions of a variable
            // the snippet is obfBB
            for (Function::iterator bb = F.begin(), e = F.end(); bb != e; ++bb) {
                for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i != e; ++i) {
                    unsigned opcode = i->getOpcode();
                    if (opcode == Instruction::Store) {
                        if (firstStore == true) {
                            errs() << "The first store: " << *i << "\n";
                            errs() << *i->getOperand(1)  << "\n";
                            covar = i->getOperand(1);
                            insertAlloca = i;
                            preBBend = std::next(i);
                            // for(Value::use_iterator ui = i->use_begin(), ie = i->use_end(); ui != ie; ++ui){
                            //   Value *v = *ui;
                            //   Instruction *vi = dyn_cast<Instruction>(*ui);
                            //   errs() << "\t\t" << *vi << "\n";
                            // }
                            // errs().write_escaped(i->getOpcodeName()) << '\n';
                            // errs().write_escaped(i->getOperand(0)->getName()) << '\n';
                            firstStore = false;
                            continue;
                        } else {
                            if (i->getOperand(1) == covar) {
                                obfBBend = i;
                                errs() << "    " << *i << "\n";
                            }
                        }
                    }
                }
            }
	    Function::iterator bb = F.begin();
            preBB = bb;
            Twine *var1 = new Twine("obfBB");
            obfBB = bb->splitBasicBlock(preBBend, *var1);
            Twine *var2 = new Twine("postBB");
            postBB = obfBB->splitBasicBlock(obfBBend, *var2);

            // insert allca for the dop pointers
            BasicBlock::iterator ii = std::next(insertAlloca);
            AllocaInst* dop1 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop1");
            AllocaInst* dop2 = new AllocaInst(Type::getInt32PtrTy(F.getContext()), 0, 4, "dop2");
            preBB->getInstList().insert(ii, dop1);
            preBB->getInstList().insert(ii, dop2);

            // store the variable's address to the dop pointers
            StoreInst* dop1st = new StoreInst(insertAlloca->getOperand(1), dop1, false, ii);
            StoreInst* dop2st = new StoreInst(insertAlloca->getOperand(1), dop2, false, ii);

            // load the dop1's value
            LoadInst* dop1p = new LoadInst(dop1, "", false, 4, ii);
            LoadInst* dop1deref = new LoadInst(dop1p, "", false, 4, ii);


            // create alter BB from cloneing the obfBB
            const Twine & name = "clone";
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
	    std::map<Instruction*, Instruction*> fixssa;
            for (BasicBlock::iterator i = obfBB->begin(), j = alterBB->begin(),
                                      e = obfBB->end(), f = alterBB->end(); i != e && j != f; ++i, ++j) {
	      // errs() << "install fix ssa:" << "\n";
	      fixssa[i] = j;
            }
            // Fix use values in alterBB
            for (BasicBlock::iterator i = alterBB->begin(), e = alterBB->end() ; i != e; ++i) {
                for (User::op_iterator opi = i->op_begin(), ope = i->op_end(); opi != ope; ++opi) {
                    Instruction *vi = dyn_cast<Instruction>(*opi);
                    if (fixssa.find(vi) != fixssa.end()) {
                        *opi = (Value*)fixssa[vi];
                    }
                }
            }
            // for (std::map<Instruction*, Instruction*>::iterator it = fixssa.begin(), e = fixssa.end(); it != e; ++it) {
	    //   errs() << "print fix ssa:" << "\n";
	    //   errs() << "    " << it->first->getOpcodeName() << "\n";
	    //   errs() << "    " << it->second->getOpcodeName() << "\n";
	    // }

            // create the first dop at the end of preBB
            Twine * var3 = new Twine("dopbranch1");
            Value * rvalue = ConstantInt::get(Type::getInt32Ty(F.getContext()), 0);
            preBB->getTerminator()->eraseFromParent();
            ICmpInst * dopbranch1 = new ICmpInst(*preBB, CmpInst::ICMP_SGT , dop1deref, rvalue, *var3);
            BranchInst::Create(obfBB, alterBB, dopbranch1, preBB);

            // split the obfBB and alterBB with an offset
            BasicBlock::iterator splitpt1 = obfBB->begin(),
	                         splitpt2 = alterBB->begin();
            BasicBlock *obfBB2, *alterBB2;
            int num = 2;
	    int n = num;
            for (BasicBlock::iterator e = obfBB->end(); splitpt1 != e && n > 0; ++splitpt1, --n) ;
	    n = num+1;
            for (BasicBlock::iterator e = alterBB->end(); splitpt2 != e && n > 0; ++splitpt2, --n) ;
            Twine *var4 = new Twine("obfBB2");
            obfBB2 = obfBB->splitBasicBlock(splitpt1, *var4);
            Twine *var5 = new Twine("obfBBclone2");
            alterBB2 = alterBB->splitBasicBlock(splitpt2, *var5);

            // create the second dop as a separate BB
            BasicBlock* dop2BB = BasicBlock::Create(F.getContext(), "dop2BB", &F, obfBB2);
            LoadInst* dop2p = new LoadInst(dop2, "", false, 4, dop2BB);
            LoadInst* dop2deref = new LoadInst(dop2p, "", false, 4, dop2BB);
            Twine * var6 = new Twine("dopbranch2");
            Value * rvalue2 = ConstantInt::get(Type::getInt32Ty(F.getContext()), 0);
            // dop2BB->getTerminator()->eraseFromParent();
            ICmpInst * dopbranch2 = new ICmpInst(*dop2BB, CmpInst::ICMP_SGT , dop2deref, rvalue, *var3);
            BranchInst::Create(obfBB2, alterBB2, dopbranch2, dop2BB);
            
            // connect obfBB and alterBB to the second dop
            obfBB->getTerminator()->eraseFromParent();
            BranchInst::Create(dop2BB, obfBB);
            alterBB->getTerminator()->eraseFromParent();
            BranchInst::Create(dop2BB, alterBB);

            // insert phi node and update uses in postBB
            ii = postBB->begin();
            std::map<Instruction*, PHINode*> insertedPHI;
            for (BasicBlock::iterator i = postBB->begin(), e = postBB->end() ; i != e; ++i) {
                for(User::op_iterator opi = i->op_begin (), ope = i->op_end(); opi != ope; ++opi) {
                    Instruction *p;
                    Instruction *vi = dyn_cast<Instruction>(*opi);
		    PHINode *q;
                    if (fixssa.find(vi) != fixssa.end()) {
                        PHINode *fixnode;
                        p = fixssa[vi];
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

    };
}

char DopSeq::ID = 0;
static RegisterPass<DopSeq> X("DopSeq", "Dynamic opaque predicate obfuscation Pass for straight line code");

Pass *llvm::createDopSeq() {
  return new DopSeq();
}

Pass *llvm::createDopSeq(bool flag) {
  return new DopSeq(flag);
}
