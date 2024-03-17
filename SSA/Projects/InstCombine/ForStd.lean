import Std.Data.BitVec
import Std.Data.Option.Lemmas

open Std

namespace Option

@[simp]
theorem none_bind'' (f : α → Option β) :
    none >>= f = none :=
  none_bind f

@[simp]
theorem some_bind'' (a : α) (f : α → Option β) :
    some a >>= f = f a :=
  pure_bind a f

end Option

namespace Std.BitVec

notation:50 x " ≤ᵤ " y => BitVec.ule x y
notation:50 x " <ᵤ " y => BitVec.ult x y
notation:50 x " ≥ᵤ " y => BitVec.ule y x
notation:50 x " >ᵤ " y => BitVec.ult y x

notation:50 x " ≤ₛ " y => BitVec.sle x y
notation:50 x " <ₛ " y => BitVec.slt x y
notation:50 x " ≥ₛ " y => BitVec.sle y x
notation:50 x " >ₛ " y => BitVec.slt y x

instance {n} : ShiftLeft (BitVec n) := ⟨fun x y => x <<< y.toNat⟩

instance {n} : ShiftRight (BitVec n) := ⟨fun x y => x >>> y.toNat⟩

infixl:75 ">>>ₛ" => fun x y => BitVec.sshiftRight x (BitVec.toNat y)

-- A lot of this should probably go to a differet file here and not Mathlib
inductive Refinement {α : Type u} : Option α → Option α → Prop
  | bothSome {x y : α } : x = y → Refinement (some x) (some y)
  | noneAny {x? : Option α} : Refinement none x?

infix:50 (priority:=low) " ⊑ " => Refinement

namespace Refinement

@[simp]
theorem some_some {α : Type u} {x y : α} :
    (some x) ⊑ (some y) ↔ x = y :=
  ⟨by intro h; cases h; assumption, Refinement.bothSome⟩

@[simp]
theorem none_left {x? : Option α} :
    none ⊑ x? :=
  .noneAny

@[simp]
theorem none_right {x? : Option α} :
    x? ⊑ none ↔ x? = none := by
  cases x?
  · simp only [none_left]
  · simp only [iff_false]
    rintro ⟨⟩

@[simp]
theorem some_left {x : α} {y? : Option α} :
    some x ⊑ y? ↔ y? = some x := by
  cases y? <;> simp [eq_comm]

-- @[simp]
-- theorem pure_right {x? : Option α} {y : α} :
--     x? ⊑ pure y ↔ x? = some y := by
--   cases x? <;> simp [pure]

@[simp]
theorem refl {α: Type u} : ∀ x : Option α, Refinement x x := by
  intro x ; cases x
  apply Refinement.noneAny
  apply Refinement.bothSome; rfl

theorem trans {α : Type u} : ∀ x y z : Option α, Refinement x y → Refinement y z → Refinement x z := by
  intro x y z h₁ h₂
  cases h₁ <;> cases h₂ <;> try { apply Refinement.noneAny } ; try {apply Refinement.bothSome; assumption}
  rename_i x y hxy y h
  rw [hxy, h]; apply refl

instance {α : Type u} [DecidableEq α] : DecidableRel (@Refinement α) := by
  intro x y
  cases x <;> cases y
  { apply isTrue; exact Refinement.noneAny}
  { apply isTrue; exact Refinement.noneAny }
  { apply isFalse; intro h; cases h }
  { rename_i val val'
    cases (decEq val val')
    { apply isFalse; intro h; cases h; contradiction }
    { apply isTrue; apply Refinement.bothSome; assumption }
  }



end Refinement

instance : Coe Bool (BitVec 1) := ⟨ofBool⟩

def coeWidth {m n : Nat} : BitVec m → BitVec n
  | x => BitVec.ofNat n x.toNat

-- not sure what the right `Coe`is for this case
-- See: https://leanprover-community.github.io/mathlib4_docs/Init/Coe.html#Important-typeclasses
--instance {m n: Nat} : CoeTail (BitVec m) (BitVec n) := ⟨BitVec.coeWidth⟩

instance decPropToBitvec1 (p : Prop) [Decidable p] : CoeDep Prop p (BitVec 1) where
  coe := ofBool $ decide p

-- This should become a lot simpler, if not obsolete after:
-- https://github.com/leanprover/lean4/pull/3474
theorem bitvec_minus_one : BitVec.ofInt w (Int.negSucc 0) = (-1 : BitVec w) := by
  change (BitVec.ofInt w (-1) = (-1 : BitVec w))
  ext i
  simp_all only [BitVec.ofInt, Neg.neg, Int.neg, Int.negOfNat]
  simp_all only [BitVec.getLsb_not, Bool.not_false, BitVec.ofNat_eq_ofNat,
    BitVec.neg_eq, Fin.is_lt, getLsb_ofNat]
  simp only [Bool.and_true, decide_True]
  rw [negOne_eq_allOnes]
  rw [getLsb_allOnes]
  simp
