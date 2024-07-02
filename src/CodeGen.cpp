#include "CodeGen.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include <iostream>
#include <map>
#include <vector>
#include <stack>

using namespace llvm;
using namespace std;

struct AssignmentLine {
  StringRef left;
  vector<StringRef> right;
  vector<Value*> addresses;
  vector<string> IRs;
}; 

// Define a visitor class for generating LLVM IR from the AST.
namespace
{
  class ToIRVisitor : public ASTVisitor
  {
    Module *M;
    IRBuilder<> Builder;
    Type *VoidTy;
    Type *Int32Ty;
    Type *Int8PtrTy;
    Type *Int8PtrPtrTy;
    Constant *Int32Zero;

    Value *V;
    Value *tmp1;
    Value *tmp2;
    StringMap<AllocaInst *> nameMap;

    Function *MainFn;

    FunctionType *CalcWriteFnTy;
    Function *CalcWriteFn;


    map<StringRef, vector<StringRef>> dependencies;
    bool assigning = false;
    StringRef left;
    vector<Value*> loads;

    vector<AssignmentLine> assignmentLines;
    AssignmentLine al;

    vector<StringRef> resultDependencies;

    StringRef resultRef;

    vector<string> acceptedIRs;

  public:
    // Constructor for the visitor class.
    ToIRVisitor(Module *M) : M(M), Builder(M->getContext())
    {
      // Initialize LLVM types and constants.
      VoidTy = Type::getVoidTy(M->getContext());
      Int32Ty = Type::getInt32Ty(M->getContext());
      Int8PtrTy = Type::getInt8PtrTy(M->getContext());
      Int8PtrPtrTy = Int8PtrTy->getPointerTo();
      Int32Zero = ConstantInt::get(Int32Ty, 0, true);
      CalcWriteFnTy = FunctionType::get(VoidTy, {Int32Ty}, false);
      CalcWriteFn = Function::Create(CalcWriteFnTy, GlobalValue::ExternalLinkage, "print", M);
    }

    bool isAllocationInstruction(llvm::Instruction *inst) {
        if (const llvm::AllocaInst *allocaInst = llvm::dyn_cast<llvm::AllocaInst>(inst)) {
            return true;
        }

        if (const llvm::CallInst *callInst = llvm::dyn_cast<llvm::CallInst>(inst)) {
            if (const llvm::Function *calledFunction = callInst->getCalledFunction()) {
                if (calledFunction->getName() == "malloc" || calledFunction->getName() == "calloc" || calledFunction->getName() == "operator new") {
                    return true;
                }
            }
        }

        return false;
    }

    llvm::Value* getAllocationAddress(llvm::Instruction *inst) {
        // Check if the instruction is AllocaInst (stack allocation)
        if (llvm::AllocaInst *allocaInst = llvm::dyn_cast<llvm::AllocaInst>(inst)) {
            return allocaInst; // Return the AllocaInst itself, which represents the allocated memory address
        }

        return nullptr; // Return nullptr if it's not an allocation instruction
    }

    vector<Value*> findDependencies(StringRef variable, stack<AssignmentLine> lines) {
        vector<Value*> addresses;
        AssignmentLine tmp;
        vector<Value*> tmpAddresses;
        while (!lines.empty()) {
          tmp = lines.top();
          lines.pop();
          if (tmp.left.str() == variable.str()) {
            addresses.push_back(llvm::dyn_cast<llvm::Value>(nameMap[tmp.left]));
            for (auto address : tmp.addresses) addresses.push_back(address);

            for (auto lineStr : tmp.IRs) {
              acceptedIRs.push_back(lineStr);
            }

            for (const StringRef &value : tmp.right) {
              vector<Value*> tmpAddresses = findDependencies(value, lines);
              for (auto address : tmpAddresses) addresses.push_back(address);
            }

            break;
          }
        }
        
        return addresses;
    }

    // Entry point for generating LLVM IR from the AST.
    void run(AST *Tree)
    {
      // Create the main function with the appropriate function type.
      FunctionType *MainFty = FunctionType::get(Int32Ty, {Int32Ty, Int8PtrPtrTy}, false);
      MainFn = Function::Create(MainFty, GlobalValue::ExternalLinkage, "main", M);

      // Create a basic block for the entry point of the main function.
      BasicBlock *BB = BasicBlock::Create(M->getContext(), "entry", MainFn);
      Builder.SetInsertPoint(BB);

      // Visit the root node of the AST to generate IR.
      Tree->accept(*this);

      stack<AssignmentLine> linesStack;
      
      for (const auto &entry : assignmentLines)
          linesStack.push(entry);

      vector<Value*> correctResults = findDependencies(resultRef, linesStack);


      llvm::Value *tmp;
      SmallVector<Instruction*,128> WL;

      std::string Str;
      raw_string_ostream OS(Str);
      for(inst_iterator I = inst_begin(MainFn), E = inst_end(MainFn); I != E; ++I) {
          if (isAllocationInstruction(&*I)) {
            tmp = getAllocationAddress(&*I);
            auto it = std::find(correctResults.begin(), correctResults.end(), tmp);
            if (it != correctResults.end()) {
                continue;
            }
          }

          Str = "";
          I->print(OS);
          auto it = std::find(acceptedIRs.begin(), acceptedIRs.end(), Str);
          if (it == acceptedIRs.end()) {
            WL.push_back(&*I);
          }
      }

      while (!WL.empty()) {
        Instruction* I = WL.pop_back_val();
        I->eraseFromParent();
      }

      for(inst_iterator I = inst_begin(MainFn), E = inst_end(MainFn); I != E; ++I) {
          Str = "";
          I->print(OS);
          if (Str.find("<badref>") != std::string::npos) {
            WL.push_back(&*I);
          } 
      }

      while (!WL.empty()) {
        Instruction* I = WL.pop_back_val();
        I->eraseFromParent();
      }


      Builder.CreateRet(Int32Zero);
    }

    // Visit function for the GSM node in the AST.
    virtual void visit(GSM &Node) override
    {
      // Iterate over the children of the GSM node and visit each child.
      for (auto I = Node.begin(), E = Node.end(); I != E; ++I)
      {
        (*I)->accept(*this);
      }
    };

    virtual void visit(Print &Node) override
    {
      // Visit the right-hand side of the assignment and get its value.
      Node.getExpr()->accept(*this);
      Value *val = V;

      // Create a call instruction to invoke the "print" function with the value.
      CallInst *Call = Builder.CreateCall(CalcWriteFnTy, CalcWriteFn, {val});
    };

    virtual void visit(Assignment &Node) override
    {
      al = AssignmentLine();
      assigning = true;
      left = Node.getLeft()->getVal();
      al.left = left;
      al.addresses.push_back(nameMap[left]);
      // Visit the right-hand side of the assignment and get its value.
      Node.getRight()->accept(*this);
      Value *val = V;
      

      // Get the name of the variable being assigned.
      auto varName = Node.getLeft()->getVal();

      // Create a store instruction to assign the value to the variable.
      V = Builder.CreateStore(val, nameMap[varName]);
      std::string Str;
      raw_string_ostream OS(Str);
      V->print(OS);
      if (assigning) al.IRs.push_back(Str);
      assignmentLines.push_back(al);
      assigning = false;
    };

    virtual void visit(Factor &Node) override
    {
      if (Node.getKind() == Factor::Ident)
      {
        // If the factor is an identifier, load its value from memory.
        V = Builder.CreateLoad(Int32Ty, nameMap[Node.getVal()]);
        loads.push_back(V);
        if (assigning) {
          dependencies[left].push_back(Node.getVal());
          al.right.push_back(Node.getVal());
          al.addresses.push_back(nameMap[Node.getVal()]);

          std::string Str;
          raw_string_ostream OS(Str);
          V->print(OS);
          if (assigning) al.IRs.push_back(Str);
        }
      }
      else
      {
        // If the factor is a literal, convert it to an integer and create a constant.
        int intval;
        Node.getVal().getAsInteger(10, intval);
        V = ConstantInt::get(Int32Ty, intval, true);
        if (assigning) {
          // llvm::errs() << "Literal " << Node.getVal() << " with address=" << V << "\n";
          al.right.push_back(Node.getVal());
          al.addresses.push_back(V);

          std::string Str;
          raw_string_ostream OS(Str);
          V->print(OS);
          if (assigning) al.IRs.push_back(Str);
        }
      }
    };

    virtual void visit(BinaryOp &Node) override
    {
      // Visit the left-hand side of the binary operation and get its value.
      Node.getLeft()->accept(*this);
      Value *Left = V;

      std::string Str;
      raw_string_ostream OS(Str);
      Left->print(OS);
      if (assigning) al.IRs.push_back(Str);

      // Visit the right-hand side of the binary operation and get its value.
      Node.getRight()->accept(*this);
      Value *Right = V;

      Str = "";
      Right->print(OS);
      if (assigning) al.IRs.push_back(Str);

      // Perform the binary operation based on the operator type and create the corresponding instruction.
      switch (Node.getOperator())
      {
      case BinaryOp::Plus:
        V = Builder.CreateNSWAdd(Left, Right);
        break;
      case BinaryOp::Minus:
        V = Builder.CreateNSWSub(Left, Right);
        break;
      case BinaryOp::Mul:
        V = Builder.CreateNSWMul(Left, Right);
        break;
      case BinaryOp::Div:
        V = Builder.CreateSDiv(Left, Right);
        break;
      case BinaryOp::Mod: {
        V = Builder.CreateSRem(Left, Right);
        break;
      }
      case BinaryOp::Power: {
        llvm::Value* tmp = Builder.CreateNSWAdd(Builder.getInt32(0), Right);
        llvm::AllocaInst* LocalVar = Builder.CreateAlloca(Int32Ty);
        Builder.CreateStore(tmp, LocalVar);

        tmp = Builder.CreateNSWAdd(Builder.getInt32(1), Builder.getInt32(0));
        llvm::AllocaInst* LocalVar2 = Builder.CreateAlloca(Int32Ty);
        Builder.CreateStore(tmp, LocalVar2);

        llvm::BasicBlock* PowerCondBB = llvm::BasicBlock::Create(M->getContext(), "power.cond", MainFn);
        llvm::BasicBlock* PowerBodyBB = llvm::BasicBlock::Create(M->getContext(), "power.body", MainFn);
        llvm::BasicBlock* AfterPowerBB = llvm::BasicBlock::Create(M->getContext(), "after.power", MainFn);

        Builder.CreateBr(PowerCondBB);
        Builder.SetInsertPoint(PowerCondBB);

        tmp = Builder.CreateLoad(LocalVar);
        llvm::Value* condition = Builder.CreateICmpSGT(tmp, Builder.getInt32(0));
        Builder.CreateCondBr(condition, PowerBodyBB, AfterPowerBB);

        Builder.SetInsertPoint(PowerBodyBB);

        tmp = Builder.CreateLoad(LocalVar2);
        tmp = Builder.CreateNSWMul(tmp, Left);
        Builder.CreateStore(tmp, LocalVar2);

        tmp = Builder.CreateLoad(LocalVar);
        tmp = Builder.CreateNSWSub(tmp, Builder.getInt32(1));
        Builder.CreateStore(tmp, LocalVar);

        Builder.CreateBr(PowerCondBB);
        Builder.SetInsertPoint(AfterPowerBB);

        V = Builder.CreateLoad(LocalVar2);

        break;
      }
      case BinaryOp::Or:
        V = Builder.CreateOr(Left, Right);
        break;
      case BinaryOp::And:
        V = Builder.CreateAnd(Left, Right);
        break;
      case BinaryOp::DoubleEqual:
        V = Builder.CreateICmpEQ(Left, Right);
        break;
      case BinaryOp::NotEqual:
        V = Builder.CreateICmpNE(Left, Right);
        break;
      case BinaryOp::GreaterEqual:
        V = Builder.CreateICmpSGE(Left, Right);
        break;
      case BinaryOp::LowerEqual:
        V = Builder.CreateICmpSLE(Left, Right);
        break;
      case BinaryOp::Greater:
        V = Builder.CreateICmpSGT(Left, Right);
        break;
      case BinaryOp::Lower:
        V = Builder.CreateICmpSLT(Left, Right);
        break;
      }
      if (assigning) {
          // llvm::errs() << "BinaryOp Assigning: " << al.left.str() << " -> " << V << "\n";
          al.addresses.push_back(V);

          Str = "";
          V->print(OS);
          if (assigning) al.IRs.push_back(Str);
      }
    };

    virtual void visit(Declaration &Node) override {
      Value *val = nullptr;

      
      auto Ie = Node.begin_exprs();
      auto Ee = Node.end_exprs();

      int count_vars = 0;
      int count_exprs = 0;
      bool finishedExprs = false;

      // Iterate over the variables declared in the declaration statement.
      for (auto I = Node.begin_vars(), E = Node.end_vars(); I != E; ++I, ++count_vars, ++count_exprs) {
        StringRef Var = *I;
        al = AssignmentLine();
        assigning = true;
        left = Var;
        al.left = Var;
        if (left.str() == "result") {
            resultRef = left;
        }
        if (Ie != Ee) {
          (* Ie) -> accept(*this);
          val = V;
          Ie++;
        } else if (Ie == Ee || finishedExprs) {
          finishedExprs = true;
          val = ConstantInt::get(Int32Ty, 0, true);
          if (assigning) al.addresses.push_back(val);
        }
      
        // Create an alloca instruction to allocate memory for the variable.
        nameMap[Var] = Builder.CreateAlloca(Int32Ty);
        std::string Str;
        raw_string_ostream OS(Str);
        nameMap[Var]->print(OS);
        if (assigning) al.IRs.push_back(Str);

        // Store the initial value (if any) in the variable's memory location.
        if (val != nullptr) {
          Str = "";
          V = Builder.CreateStore(val, nameMap[Var]);
          V->print(OS);
          if (assigning) al.IRs.push_back(Str);
        }
        assignmentLines.push_back(al);
        assigning = false;
      }
      while (Ie != Ee || count_exprs <= count_vars) {
        count_exprs++;
      }
      if (count_exprs > count_vars) {} //TODO: Should raise error
    };

    virtual void visit(IfElse &Node) override {
      llvm::SmallVector<Expr *> conditions = Node.getConditions();
      llvm::SmallVector<llvm::SmallVector<Assignment *>> assignments_of_assignments = Node.getAssignments();
      llvm::BasicBlock* ifCondBB;
      llvm::BasicBlock* ifBodyBB;
      llvm::BasicBlock* AfterifBB;
      llvm::BasicBlock* elseBodyBB;
      llvm::BasicBlock* AferAllBB = llvm::BasicBlock::Create(M->getContext(), "afterAll", MainFn);

      int count_conditions = 0;
      int count_assignments = 0;
      for (auto I = assignments_of_assignments.begin(), E = assignments_of_assignments.end(); I != E; ++I) count_assignments++;
      for (auto I = conditions.begin(), E = conditions.end(); I != E; ++I) count_conditions++;

      auto condition = conditions.begin();
      auto condition_end = conditions.end();
      bool reached_else = false;
      bool first = true;

      int i = 0;
      int j = 0;

      bool end_of_statements = false;

      for (auto I = assignments_of_assignments.begin(), E = assignments_of_assignments.end(); I != E; ++I){
        i++;
        end_of_statements = count_assignments == count_conditions && count_assignments == i;
        if (condition == condition_end) reached_else = true;
        else j++;

        if (first) {
          ifCondBB = llvm::BasicBlock::Create(M->getContext(), "ifc.cond", MainFn);
          ifBodyBB = llvm::BasicBlock::Create(M->getContext(), "ifc.body", MainFn);
          if (!end_of_statements)
            AfterifBB = llvm::BasicBlock::Create(M->getContext(), "after.ifc", MainFn);
          first = false;
        } else {
          if (!reached_else) {
            ifCondBB = llvm::BasicBlock::Create(M->getContext(), "elifc.cond", MainFn);
            ifBodyBB = llvm::BasicBlock::Create(M->getContext(), "elifc.body", MainFn);
            if (!end_of_statements)
              AfterifBB = llvm::BasicBlock::Create(M->getContext(), "after.elifc", MainFn);
          }
        }

        if (!reached_else) {
          Builder.CreateBr(ifCondBB);
          Builder.SetInsertPoint(ifCondBB);

          (*condition)->accept(*this);
          Value* val=V;
          if (end_of_statements) Builder.CreateCondBr(val, ifBodyBB, AferAllBB);
          else Builder.CreateCondBr(val, ifBodyBB, AfterifBB);
          Builder.SetInsertPoint(ifBodyBB);
        } else {
          elseBodyBB = llvm::BasicBlock::Create(M->getContext(), "elsec.body", MainFn);
          Builder.CreateBr(elseBodyBB);
          Builder.SetInsertPoint(elseBodyBB);
        }

        for (auto II = I -> begin(), EE =  I -> end(); II != EE; ++II){
          (*II)->accept(*this);
        }
        Builder.CreateBr(AferAllBB);
        if (!reached_else && !end_of_statements)
          Builder.SetInsertPoint(AfterifBB);
        
        condition++;
      }
      Builder.SetInsertPoint(AferAllBB);
    };

  virtual void visit(Loop &Node) override {
      llvm::BasicBlock* WhileCondBB = llvm::BasicBlock::Create(M->getContext(), "loopc.cond", MainFn);
      llvm::BasicBlock* WhileBodyBB = llvm::BasicBlock::Create(M->getContext(), "loopc.body", MainFn);
      llvm::BasicBlock* AfterWhileBB = llvm::BasicBlock::Create(M->getContext(), "after.loopc", MainFn);

      Builder.CreateBr(WhileCondBB);
      Builder.SetInsertPoint(WhileCondBB);
      Node.getCondition()->accept(*this);
      Value* val=V;
      Builder.CreateCondBr(val, WhileBodyBB, AfterWhileBB);
      Builder.SetInsertPoint(WhileBodyBB);
      llvm::SmallVector<Assignment* > assignments = Node.getAssignments();
      for (auto I = assignments.begin(), E = assignments.end(); I != E; ++I){
        (*I)->accept(*this);
      }
      Builder.CreateBr(WhileCondBB);
      Builder.SetInsertPoint(AfterWhileBB);
  };
};
}; // namespace

void CodeGen::compile(AST *Tree)
{
  // Create an LLVM context and a module.
  LLVMContext Ctx;
  Module *M = new Module("calc.expr", Ctx);

  // Create an instance of the ToIRVisitor and run it on the AST to generate LLVM IR.
  ToIRVisitor ToIR(M);
  ToIR.run(Tree);

  // Print the generated module to the standard output.
  M->print(outs(), nullptr);
}
