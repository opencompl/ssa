import SSA.Projects.InstCombine.LLVM.Parser
import Cli

def runMainCmd (args : Cli.Parsed) : IO UInt32 := do
  let fileName := args.positionalArg! "file" |>.as! String
  let icom? ← parseIComFromFile fileName
  match icom? with
    | none => return 1
    | some (Sigma.mk Γ icom) => IO.println s!"Parsed"; return 0 -- TODO: print icom

def mainCmd := `[Cli|
    mlirnatural VIA runMainCmd;
    "opt: apply verified rewrites"
    ARGS:
      test: String; "Input filename"
    ]

def main (args : List String): IO UInt32 :=
  mainCmd.validate args