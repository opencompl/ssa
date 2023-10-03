import SSA.Projects.MLIRSyntax.Parser
import SSA.Projects.InstCombine.LLVM.Transform
import Init.Data.Repr

open MLIR AST

def regionTransform (region : Region) : Except ParseError 
  (Σ (Γ' : Context) (ty : InstCombine.Ty), Com Γ' ty) :=  
  let res := mkCom region
  match res with 
    | Except.error e => Except.error s!"Error:\n{reprStr e}" 
    | Except.ok res => Except.ok res

def parseIComFromFile (fileName : String) :
 IO (Option (Σ (Γ' : Context) (ty : InstCombine.Ty), Com Γ' ty)) :=
 parseRegionFromFile fileName regionTransform