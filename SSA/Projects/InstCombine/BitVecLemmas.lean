import Std.Data.BitVec

namespace Std.BitVec

/-!
  These should be upstreamed to `Std` or `Mathlib` at some point
-/
set_option pp.analyze true
set_option pp.instances true
set_option pp.all true

@[simp]
theorem ofInt_ofNat (w x : Nat) : BitVec.ofInt w (OfNat.ofNat x) = BitVec.ofNat w x := rfl

-- example : BitVec.ofInt w 1 = 1#w := by
--   simp -- `simp made no progress`

-- example : BitVec.ofInt w 1 = 1#w := by
--   conv =>
--     lhs
--     simp

-- example : BitVec.ofInt w 1 = 1#w := by
--   rw [ofInt_ofNat] -- works!
