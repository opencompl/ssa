import Mathlib.Tactic.IrreducibleDef

namespace Irred
irreducible_def foo (x : Nat) : Int := x

def bar (x : Nat) : Int := foo x
end Irred
