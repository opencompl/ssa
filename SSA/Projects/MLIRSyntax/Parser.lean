import SSA.Projects.MLIRSyntax.AST
import SSA.Projects.MLIRSyntax.EDSL
import Lean

open Lean

variable {ParseOutput : Type} [ToString ParseOutput]

abbrev ParseError := String
abbrev ParseFun : Type := Lean.Environment → String → EIO ParseError ParseOutput

unsafe def elabIntoTermElab {α : Type} : Lean.Name → Lean.Syntax → Elab.Term.TermElabM α :=
  fun typeName stx => do
  let expr ← Lean.Elab.Term.elabTerm stx none
  let val ← Lean.Meta.evalExpr' α typeName expr 
  return val

unsafe def elabIntoMeta {α : Type} : Lean.Name → Lean.Syntax → MetaM α :=
  fun typeName stx => 
  elabIntoTermElab typeName stx |>.run'

unsafe def elabIntoCore {α : Type} : Lean.Name → Lean.Syntax → CoreM α :=
  fun typeName stx => do
  elabIntoMeta typeName stx |>.run'

unsafe def elabIntoEIO {α : Type} : Lean.Environment → Lean.Name → Lean.Syntax → EIO ParseError α :=
  fun env typeName stx => do
  let resE : EIO Exception α := elabIntoCore typeName stx |>.run' {fileName := "parserHack", fileMap := default} {env := env}
  resE.adaptExcept (fun _ => "Error in elaborator hack")

/--
  Parse `Lean.Syntax` into `MLIR.AST.Region`.
  
  This runs the Lean frontend stack and adds it to the TCB.
  It should be safe (if we trust the lean parser) since we ensure that the types match: see
  https://leanprover-community.github.io/mathlib4_docs/Std/Util/TermUnsafe.html#Std.TermUnsafe.termUnsafe_
 -/
def elabRegion : Lean.Environment → Lean.Syntax → EIO ParseError MLIR.AST.Region := 
fun env stx => do 
let reg ← unsafe elabIntoEIO (α := MLIR.AST.Region) env `MLIR.AST.Region stx
return reg

/--
  Parse `Lean.Syntax` into `MLIR.AST.Op`.
  
  This runs the Lean frontend stack and adds it to the TCB.
  It should be safe (if we trust the lean parser) since we ensure that the types match: see
  https://leanprover-community.github.io/mathlib4_docs/Std/Util/TermUnsafe.html#Std.TermUnsafe.termUnsafe_
 -/
def elabOp : Lean.Environment → Lean.Syntax → EIO ParseError MLIR.AST.Op := 
fun env stx => do 
let reg ← unsafe elabIntoEIO (α := MLIR.AST.Op) env `MLIR.AST.Op stx
return reg

def mkParseFun (syntaxcat : Name) 
  (ntparser : Syntax → EIO ParseError ParseOutput)
  (s : String) (env : Environment) : 
  EIO ParseError ParseOutput := do
  let syn ← ofExcept <| Parser.runParserCategory env syntaxcat s
  ntparser syn 

private def mkNonTerminalParser (syntaxcat : Name) 
  (ntparser : Syntax → EIO ParseError ParseOutput)
  (env : Environment) (s : String) : EIO ParseError ParseOutput :=
  let parseFun := mkParseFun syntaxcat ntparser
  parseFun s env

-- TODO: do we need this copy of the environment, or can I remove it from one of the two?
def regionParser : @ParseFun MLIR.AST.Region := 
  fun env : Lean.Environment => mkNonTerminalParser `MLIR.AST.Region (elabRegion env) env

private def parseFile (env: Lean.Environment)
  (parser: @ParseFun ParseOutput)
  (filepath: System.FilePath)
   : IO (Option ParseOutput) := do
  let lines <- IO.FS.lines filepath
  let fileStr := lines.foldl (λ s₁ s₂ => s₁ ++ "\n" ++ s₂) ""
  let parsed ← EIO.toIO' <| parser env fileStr
  match parsed with
    | .ok parseOutput => return parseOutput
    | .error msg => IO.println s!"error parsing {filepath}:\n{msg}"; return none

private def isFile (p: System.FilePath) : IO Bool := do
      return (<- p.metadata).type == IO.FS.FileType.file

def runParser  (parser : @ParseFun ParseOutput) (fileName : String) : IO (Option ParseOutput) := do
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let modules : List Import := [⟨`SSA.Projects.MLIRSyntax.EDSL, false⟩]
  let env ← importModules modules {}
  let filePath := System.mkFilePath [fileName]
  if !(← isFile filePath) then
    throw <| IO.userError s!"File {fileName} does not exist"
  parseFile env parser filePath 

def parseRegionFromFile (fileName : String) 
(regionParseFun : MLIR.AST.Region → Except ParseError α) : IO (Option α)  := do
  let ast ← runParser regionParser fileName
  match Option.map regionParseFun ast with
    | .some (.ok res) => return res
    | .some (.error msg) => throw <| IO.userError s!"Error parsing {fileName}:\n{msg}"; return none
    | .none => return none