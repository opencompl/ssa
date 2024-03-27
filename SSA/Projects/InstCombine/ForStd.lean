import Std.Data.BitVec
import Std.Data.Option.Lemmas

namespace BitVec

namespace Option

@[simp]
theorem none_bind'' (f : α → Option β) :
    none >>= f = none :=
  Option.none_bind f

@[simp]
theorem some_bind'' (a : α) (f : α → Option β) :
    some a >>= f = f a :=
  pure_bind a f

end Option

namespace Std.BitVec

def ofBool : (Bool) -> Std.BitVec 1
 | true   => 1
 | false  => 0

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

instance {α : Type u} [DEQ : DecidableEq α] : DecidableRel (@Refinement α) := by
  intro x y
  cases x <;> cases y
  { apply isTrue; exact Refinement.noneAny}
  { apply isTrue; exact Refinement.noneAny }
  { apply isFalse; intro h; cases h }
  { rename_i val val'
    cases (DEQ val val')
    { apply isFalse; intro h; cases h; contradiction }
    { apply isTrue; apply Refinement.bothSome; assumption }
  }



end Refinement

instance : Coe Bool (BitVec 1) := ⟨.ofBool⟩

def coeWidth {m n : Nat} : BitVec m → BitVec n
  | x => BitVec.ofNat n x.toNat

-- not sure what the right `Coe`is for this case
-- See: https://leanprover-community.github.io/mathlib4_docs/Init/Coe.html#Important-typeclasses
--instance {m n: Nat} : CoeTail (BitVec m) (BitVec n) := ⟨BitVec.coeWidth⟩

instance decPropToBitvec1 (p : Prop) [Decidable p] : CoeDep Prop p (BitVec 1) where
  coe := BitVec.ofBool $ decide p

open Std

theorem Int.natCast_pred_of_pos (x : Nat) (h : 0 < x) :
    (x : Int) - 1 = Nat.cast (x - 1) := by
  simp only [Nat.cast, NatCast.natCast]
  cases x
  case zero => contradiction
  case succ x =>
    simp only [(· - ·), Sub.sub, Int.sub, (· + ·), Add.add, Int.add,
      (-·), Int.neg, Int.negOfNat, Int.subNatNat]
    simp

-- This should become a lot simpler, if not obsolete after:
-- https://github.com/leanprover/lean4/pull/3474
theorem bitvec_minus_one : BitVec.ofInt w (Int.negSucc 0) = (-1 : _root_.BitVec w) := by
  simp
  by_cases zeroBitwidth : 0 < w
  case pos =>
    apply BitVec.eq_of_toInt_eq
    simp
    unfold BitVec.toInt
    simp
    have xx : 1 % 2 ^ w = 1 := by
      rw [Nat.mod_eq_of_lt]
      simp [Nat.pow_one]
      omega
    simp [xx]
    split
    · rename_i h
      rw [Nat.mod_eq_of_lt] at h
      · have xxx : 2 * (2 ^ w - 1) = 2 * 2 ^ w - 2 * 1 := by omega
        rw [xxx] at h
        simp at h
        omega
      · omega
    · simp only [Int.bmod, Int.reduceNeg, Int.natCast_pred_of_pos _ (Nat.two_pow_pos w),
        Int.neg_emod]
      omega
  case neg =>
    simp_all
    rw [zeroBitwidth]
    simp

  end BitVec
