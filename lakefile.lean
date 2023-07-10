import Lake
open Lake DSL

package «SSA» where

@[default_target]
lean_lib SSA {
  roots := #[`SSA]
}

lean_exe mlirnatural {
  root := `SSA.MLIRNatural
}
-- -- PROJECTS
-- -- ========
--
-- lean_lib «AliveAll» {
--   roots := #[`Projects.AliveAll]
-- }
--
-- lean_lib «Tensor1D» {
--   roots := #[`Projects.Tensor1D.Tensor1D]
-- }
--
-- lean_lib «InstCombine» {
--   srcDir := "Projects/InstCombine"
--   roots := #[`InstCombinePeepholeRewrites]
--   roots := #[`InstCombinePeepholeRewrites]
-- }
--
-- -- Experiments
-- -- ===========
--
-- lean_lib «Bits» {
--   roots := #[`Experiment.Bits.Decide]
-- }

-- NOTE: this must be 'm'mathlib, as indicated from:
--  https://github.com/leanprover-community/mathlib4#using-mathlib4-as-a-dependency
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "5a78ace"

require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "nightly"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "e888e9c"

