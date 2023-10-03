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

lean_exe opt {
  root := `SSA.Projects.InstCombine.LLVM.Opt
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
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "9c2f17f68a9bd84e93f2a7a0fc8b8921c88c033e"

require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "nightly"

require partax from git "https://github.com/tydeu/lean4-partax" @ "master"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "34165f3"
