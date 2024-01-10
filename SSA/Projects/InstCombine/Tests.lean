import SSA.Projects.InstCombine.Base

-- What do we have:
-- ================
--   - we have a bunch of alive tests, in the ``alive language''.
--   - pipeline to translate those to our EDSL.
--   - we have CLI infra to run a hardcoded test.

-- What do we want:
-- ================
--   - take *all* the alive tests, populate them.
--   - gather them (using meta-code? `PersistentEnvAttribute`).
--   - expose them here.
--   - generating inputs.

-- Low-tech solution (goens/bollu)
-- ===============================
--   - take *all* the alive tests, populate them.
--   - gather them (using meta-code? `PersistentEnvAttribute`). [← goens]
--   - given a test program 
--        `alive_andorxor_input : (w : Nat) → Σ (Γ : SSA.Context [.bitvec 1, .bitvec w]), AliveProgram Γ`,
-- 
--    a. Pick a small bitwidth (w = 4), run with *all possible values of arguments*, dump to a CSV file.
--    b. Generate an LLVM file that does the same thing. (`src/Lean/Compiler/IR/LLVMBindings.lean`)
--    c. Check if alive can do this? If it can, consider not spending time on (b) before rebuttal.
--    d. If (c), check that (b) and (c) agree manally on a few examples.

--    1. List all test names.
--    2a. Given a test name, print its signature. Qq pattern matching on `Expr`. [← goens]
--    2b. Given a test name and its arguments, run the test using lean semantics. [← goens]
--    2c. Given a test name (and its arguments), produce/run ll file for running the test. [← bollu]

namespace InstCombine
def test1 (_params : Nat × Nat × Nat) : IO Bool := do 
  -- let (w, A, B) := params
  -- let E : EnvC ∅ := EnvC.empty 
  -- let out : Option (Bitvec w) := TSSA.eval
  --   [dsl_bb|
  --   ^bb
  --   %v9999 := unit: ;
  --   %v1 := op:const (Bitvec.ofInt w A) %v9999;
  --   %v2 := op:const (Bitvec.ofInt w B) %v9999;
  --   %v3 := pair:%v1 %v2;
  --   %v4 := op:xor w %v3;
  --   %v5 := op:const (Bitvec.ofInt w (-1)) %v9999;
  --   %v6 := pair:%v4 %v5;
  --   %v7 := op:xor w %v6;
  --   %v8 := pair:%v1 %v7;
  --   %v9 := op:or w %v8
  --   dsl_ret %v9
  --   ] E 
  -- IO.println (repr out)
  -- return true
  throw <| .userError "test1 not implemented yet!"
