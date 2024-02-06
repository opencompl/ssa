import Std.Data.Nat.Lemmas
-- import Std.Data.Nat.Bitwise | we don't have the right lemmas.
import Std.Data.Int.Lemmas
import Std.Data.BitVec
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.BitVec.Lemmas
import SSA.Projects.InstCombine.LLVM.EDSL
import SSA.Projects.InstCombine.AliveStatements
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.Base
import SSA.Core.ErasedContext
import Mathlib.Tactic

open MLIR AST
open Std (BitVec)
open Ctxt (Var DerivedCtxt)
open InstCombine (MOp)

namespace AliveHandwritten
set_option pp.proofs false
set_option pp.proofs.withType false


namespace BitVecTheory

/- There is only one inhabitatnt of BitVec 0) -/
instance : Subsingleton (BitVec 0) where
  allEq v w := by
    obtain ⟨vfin, hvlt⟩ := v
    obtain ⟨wfin, hwlt⟩ := w
    simp at hvlt
    simp at hwlt
    subst hvlt
    subst hwlt
    rfl

-- Any bitvec of width 0 is equal to the zero bitvector
theorem BitVec.width_zero_eq_zero (x : BitVec 0) : x = BitVec.ofNat 0 0 :=
  Subsingleton.allEq x _


@[simp]
theorem BitVec.with_zero (x : BitVec 0) : BitVec.toInt x = 0 := by
  rw [BitVec.width_zero_eq_zero x]
  simp (config := {unfoldPartialApp := true, decide := true})

theorem BitVec.ofInt_toFin_nonneg (w : ℕ) (v : Int) {v' : ℕ} (hv : v = ↑v') :
  (BitVec.ofInt w v).toFin = Fin.ofNat' v' (by simp) := by
  subst hv
  simp [BitVec.ofInt, BitVec.ofNat, BitVec.toFin]

@[simp]
theorem BitVec.toNat_ofInt_1 [WNEQ0 : Fact (0 < w)] : BitVec.toNat (BitVec.ofInt w 1) = 1 := by
  simp [BitVec.ofNat, BitVec.toNat, BitVec.ofInt, BitVec.toFin, Fin.val, Fin.ofNat']
  apply Nat.mod_eq_of_lt
  cases w
  . exfalso; simp (config := {decide := true}) only [] at WNEQ0; apply Fact.elim WNEQ0
  . simp

theorem BitVec.ofInt_Nat_nonneg (w : ℕ) (v : Int) {v' : ℕ} (hv : v = ↑v' := by simp) :
  (BitVec.ofInt w v).toNat = v' % 2^w := by
  subst hv
  simp [BitVec.ofInt, BitVec.ofNat, BitVec.toFin, Fin.val, Fin.ofNat']

-- TODO: what is a nice way to package up this kind of proof engineering?
-- Should I use Fact?
theorem BitVec.ofInt_Nat_nonneg_inbounds (w : ℕ) (v : Int) {v' : ℕ} (hv : v = ↑v' := by simp) (hinbounds: v' < 2^w := by simp; linarith) :
  (BitVec.ofInt w v).toNat = v' := by
  subst hv
  simp [BitVec.ofInt, BitVec.ofNat, BitVec.toFin, Fin.val, Fin.ofNat']
  apply Nat.mod_eq_of_lt hinbounds

@[simp]
theorem BitVec.toInt_width_zero (x : BitVec 0) : BitVec.toInt x = 0 := by
  rw [BitVec.width_zero_eq_zero x]
  simp

@[simp]
theorem BitVec.toFin_width_zero (x : BitVec 0) : BitVec.toInt x = 0 := by
  cases x
  case ofFin v =>
  simp [BitVec.toFin]

@[simp]
theorem BitVec.toInt_ofInt_width_one_one : BitVec.toInt (BitVec.ofInt 1 1) = -1 := rfl

@[simp]
theorem BitVec.toInt_ofInt_zero : BitVec.toInt (BitVec.ofInt w 0) = 0 := by
  simp [BitVec.msb, BitVec.getMsb, BitVec.getLsb, BitVec.ofInt, BitVec.toInt]

theorem BitVec.eq_zero_of_toInt_zero (x : BitVec w) (h : BitVec.toInt x = 0) : x = 0 := by
  obtain ⟨x, hx⟩ := x
  simp [BitVec.toInt, BitVec.msb, BitVec.toNat, BitVec.getMsb, BitVec.getLsb, Nat.cast, NatCast.natCast, Fin.val] at h
  split_ifs at h
  case pos h' =>
    norm_cast at h'
    have h2 :  (↑x : Int) =  ↑(2^w) := by
      simp at h
      linarith
    have h3 : x = 2^w := by linarith
    exfalso
    linarith
  case neg h' =>
    norm_cast at h
    subst h
    rfl


@[simp]
theorem BitVec.toInt_ofInt_1_width_zero :
    BitVec.toInt (BitVec.ofInt (n := 0) 1) = 0 := rfl


@[simp]
theorem BitVec.toInt_ofInt_1_width_one :
    BitVec.toInt (BitVec.ofInt (n := 1) 1) = -1 := rfl

@[simp]
theorem BitVec.neg_zero :
    - (BitVec.ofNat w 0 ) = BitVec.ofNat w 0 := by
  unfold BitVec.ofNat Neg.neg BitVec.instNegBitVec BitVec.neg
  simp

@[simp]
theorem BitVec.ofInt_1 [hone_lt_w: Fact (1 < w)] :
    (BitVec.ofInt w 1) = 1 := by
  simp [BitVec.ofInt]

-- if w = 0. then value is 0
-- if w = 1, then value is -1.
@[simp]
theorem BitVec.toInt_ofInt_1 [hone_lt_w: Fact (1 < w)] :
    BitVec.toInt (BitVec.ofInt w 1) = 1 := by
    simp [BitVec.toInt]
    simp [BitVec.msb]
    simp [BitVec.getMsb]
    have h' : 0 < w := by
      obtain ⟨this⟩ :=  hone_lt_w
      linarith
    rcases w with rfl | rfl | w
    · simp at h'
    . exfalso
      obtain ⟨h⟩ := hone_lt_w
      simp at h
    · simp [h']
      simp [BitVec.getLsb]
      have hone : 1 % 2^(Nat.succ (Nat.succ w)) = 1 := by
        rw [Nat.mod_eq_of_lt]
        apply Nat.one_lt_two_pow
        simp
      have honez : (1 : ℤ) % 2^(Nat.succ (Nat.succ w)) = 1 := by norm_cast
      simp [hone, honez]
      simp [Nat.testBit]
      simp [Nat.shiftRight_eq_div_pow]
      have two_pow_w_recip : 1 / 2^(w + 1) = 0 := by
         apply Nat.div_eq_of_lt
         apply Nat.one_lt_two_pow
         linarith
      simp [two_pow_w_recip]
      rfl

@[simp]
theorem BitVec.toNat_ofInt_one_width_zero : BitVec.toNat (BitVec.ofInt (n := 0) 1) = 0 := rfl

@[simp]
theorem BitVec.toNat_ofInt_one_width_one : BitVec.toNat (BitVec.ofInt (n := 1) 1) = 1 := rfl

@[simp]
theorem BitVec.toNat_ofInt_one [hzero_lt_w: Fact (0 < w)] : BitVec.toNat (BitVec.ofInt w 1) = 1 := by
  cases w
  case zero => simp at hzero_lt_w; apply False.elim hzero_lt_w.out
  case succ w' =>
      unfold BitVec.toNat BitVec.ofInt Fin.val BitVec.ofNat
      simp
      apply Nat.mod_eq_of_lt; simp

@[simp]
theorem BitVec.ofNat_toNat_zero :
BitVec.toNat (BitVec.ofInt w 0) = 0 := by
  unfold BitVec.toNat BitVec.ofInt BitVec.toFin BitVec.ofNat OfNat.ofNat instOfNatInt instOfNatNat
  simp


@[simp]
theorem BitVec.zeroExtend_id (b : BitVec w) :
  BitVec.zeroExtend w b = b := by
  obtain ⟨bval, hbval⟩ := b
  simp [BitVec.zeroExtend, BitVec.zeroExtend', BitVec.ofNat, BitVec.toNat, Fin.ofNat', BitVec.toFin, Fin.val]

@[simp]
lemma BitVec.ofInt_ofNat (w n : Nat)  :
    BitVec.ofInt w (OfNat.ofNat n) = BitVec.ofNat w n :=
  rfl

/- Not a simp lemma by default because we may want toFin or toInt in the future. -/
theorem BitVec.ult_toNat (x y : BitVec n) :
    (BitVec.ult (n := n) x y) = decide (x.toNat < y.toNat) := by
  simp [BitVec.ult]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  constructor <;>
  intros h <;>
  simp only [Fin.mk_lt_mk, BitVec.toNat] at h ⊢ <;>
  assumption


-- Std theorem
theorem Std.BitVec.getLsb_ge (x : BitVec w) (hi : i ≥ w) : BitVec.getLsb x i = false := by exact?

/-- The usual theorem is stated with nat as the index. -/
@[simp] lemma BitVec.getLsb_xor' (x y : BitVec w) (i : Nat) :
    (x ^^^ y).getLsb i = xor (x.getLsb i) (y.getLsb i) := by
    have hi : i < w ∨ i ≥ w := Nat.lt_or_ge _ _
    rcases hi with h | h
    . have hi : i = (Fin.mk i h).val := rfl
      rw [hi]
      apply BitVec.getLsb'_xor
    . simp [Std.BitVec.getLsb_ge _ h]


/-
https://github.com/leanprover/std4/commit/ecf1ec23eac8997d5964d480511ba93970fa455b#diff-8f36f4c14ec3f02f7b8ea0a193114c273871d6b0ddad6083cd74090b3befcb1eR227-R229
This exists in std4 as of 3 days ago.
We should rebase on mathlib4.
-/
lemma BitVec.getLsb'_ushr (x : BitVec w) (y : Nat) (i : Fin w) :
  (x >>> y).getLsb' i = if (y > i) then false else (x.getLsb' ⟨i - y, by sorry ⟩) := by sorry -- std sorry

end BitVecTheory

namespace LLVMTheory
open BitVecTheory

@[simp]
theorem LLVM.const?_eq : LLVM.const? (w := w) i = BitVec.ofInt w i := rfl

@[simp]
theorem LLVM.xor?_eq : LLVM.xor? a b  = BitVec.xor a b := rfl

/-- Note that this assumes that the input and output bitwidths are the same, which is by far the common case. -/
@[simp]
theorem LLVM.lshr?_eq_some {a b : BitVec w} (hb : b.toNat < w) : LLVM.lshr? a b = .some (BitVec.ushiftRight a b.toNat) := by
  simp only [LLVM.lshr?]
  split_ifs
  case pos contra => linarith
  case neg _ =>
    simp [HShiftRight.hShiftRight, BitVec.instHShiftRightBitVec]

/-- Note that this assumes that the input and output bitwidths are the same, which is by far the common case. -/
@[simp]
theorem LLVM.lshr?_eq_none {a b : BitVec w} (hb : b.toNat ≥ w) : LLVM.lshr? a b = .none := by
  simp only [LLVM.lshr?]
  split_ifs; simp

@[simp]
theorem LLVM.select?_eq_none : LLVM.select? (w := w) none a b = .none := rfl

@[simp]
theorem LLVM.select?_some_true : LLVM.select? (w := w) (.some true) a b = a := rfl

@[simp]
theorem LLVM.select?_some_false : LLVM.select? (w := w) (.some false) a b = b := rfl

@[simp]
theorem LLVM.add?_eq : LLVM.add? (w := w) a b = .some (a + b) := rfl

@[simp]
theorem LLVM.sub?_eq : LLVM.sub? (w := w) a b = .some (a - b) := rfl

@[simp]
theorem LLVM.icmp?_ult_eq {w : Nat} {a b : BitVec w} :
  LLVM.icmp? .ult a b =  Option.some (BitVec.ofBool (a <ᵤ b)) := rfl

@[simp]
theorem LLVM.icmp?_slt_eq {w : Nat} {a b : BitVec w} :
  LLVM.icmp? .slt a b =  Option.some (BitVec.ofBool (a <ₛ b)) := rfl

@[simp]
theorem LLVM.icmp?_sgt_eq {w : Nat} {a b : BitVec w} :
  LLVM.icmp? .sgt a b =  Option.some (BitVec.ofBool (a >ₛ b)) := rfl

@[simp]
theorem LLVM.select?_eq_some {w : Nat} {c : BitVec 1} {x y : Option (BitVec w)} :
    LLVM.select? (.some c) x y =  if c = 1 then x else y := by
  simp [LLVM.select?]
  obtain ⟨c, hc⟩ := c
  simp at hc
  have hc' : c = 0 ∨ c = 1 := by
    rcases c with rfl | rfl | hcontra <;> simp at hc ⊢
    contradiction
  rcases hc' with rfl | rfl <;> simp
  · rfl

@[simp]
theorem LLVM.sdiv?_denom_zero {w : Nat} {a b : BitVec w} (hb : b = 0) : LLVM.sdiv? a b = none :=
  by simp [LLVM.sdiv?, hb]


/-
@[simp]
theorem LLVM.sdiv?_denom_nonzero_inbounds {w : Nat} {a b : BitVec w} (hb : b ≠ 0)
    (hinbounds : LLVM.BitVec.isIntInbounds? w (a.toInt / b.toInt)) :
    LLVM.sdiv? a b = .some (BitVec.ofInt w (a.toInt / b.toInt)) := by
  simp [LLVM.sdiv?, hinbounds, hb, LLVM.BitVec.ofIntInbounds?]
  exact hb
-/


end LLVMTheory

namespace DivRemOfSelect

/-
Name: SimplifyDivRemOfSelect
precondition: true
%sel = select %c, %Y, 0
%r = udiv %X, %sel
  =>
%r = udiv %X, %Y

-/
def alive_DivRemOfSelect_src (w : Nat) :=
  [alive_icom (w)| {
  ^bb0(%c: i1, %y : _, %x : _):
    %c0 = "llvm.mlir.constant" () { value = 0 : _ } :() -> (_)
    %v1 = "llvm.select" (%c,%y, %c0) : (i1, _, _) -> (_)
    %v2 = "llvm.udiv"(%x, %v1) : (_, _) -> (_)
    "llvm.return" (%v2) : (_) -> ()
  }]

def alive_DivRemOfSelect_tgt (w : Nat) :=
  [alive_icom (w)| {
  ^bb0(%c: i1, %y : _, %x : _):
    %v1 = "llvm.udiv" (%x,%y) : (_, _) -> (_)
    "llvm.return" (%v1) : (_) -> ()
  }]

@[simp]
theorem BitVec.ofNat_toNat_zero :
BitVec.toNat (BitVec.ofInt w 0) = 0 := by
  simp[BitVec.toNat, BitVec.ofInt, BitVec.toFin, BitVec.ofNat, OfNat.ofNat]
  norm_cast

theorem alive_DivRemOfSelect (w : Nat) :
    alive_DivRemOfSelect_src w ⊑ alive_DivRemOfSelect_tgt w := by
  unfold alive_DivRemOfSelect_src alive_DivRemOfSelect_tgt
  intros Γv
  simp_peephole at Γv
  simp (config := {decide := false}) only [OpDenote.denote,
    InstCombine.Op.denote, HVector.toPair, HVector.toTriple, pairMapM, BitVec.Refinement,
    bind, Option.bind, pure, DerivedCtxt.ofCtxt, DerivedCtxt.snoc,
    Ctxt.snoc, ConcreteOrMVar.instantiate, Vector.get, HVector.toSingle,
    LLVM.and?, LLVM.or?, LLVM.xor?, LLVM.add?, LLVM.sub?,
    LLVM.mul?, LLVM.udiv?, LLVM.sdiv?, LLVM.urem?, LLVM.srem?,
    LLVM.sshr, LLVM.lshr?, LLVM.ashr?, LLVM.shl?, LLVM.select?,
    LLVM.const?, LLVM.icmp?, LLVM.udiv?,
    HVector.toTuple, List.nthLe, bitvec_minus_one]
  intro y x c
  simp only [List.length_singleton, Fin.zero_eta, List.get_cons_zero, List.map_eq_map, List.map_cons,
    List.map_nil, CharP.cast_eq_zero, Ctxt.Valuation.snoc_last, pairBind, bind, Option.bind, Int.ofNat_eq_coe]
  clear Γv
  cases c
  -- | select condition is itself `none`, nothing more to be done. propagate the `none`.
  case none => cases x <;> cases y <;> simp
  case some cond =>
     obtain ⟨vcond, hcond⟩ := cond
     obtain (h | h) : vcond = 1 ∨ vcond = 0 := by
       norm_num at hcond
       rcases vcond with zero | vcond <;> simp;
       rcases vcond with zero | vcond <;> simp;
       linarith
     . subst h
       simp
     . subst h; simp
       cases' x with vx <;>
       cases' y with vy <;> simp [LLVM.udiv?]

end DivRemOfSelect


/- Wrapper around Com, Expr constructors to easily hand-write IR -/
namespace ComWrappers

def const {Γ : Ctxt _} (w : ℕ) (n : ℤ) : Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.const w n)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)

def sdiv {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.sdiv w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def add {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.add w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def sub {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.sub w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def mul {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.mul w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def shl {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.shl w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def lshr {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.lshr w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def xor {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.xor w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def icmp {Γ : Ctxt _} (w : ℕ) (pred : LLVM.IntPredicate) (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.bitvec 1) :=
  Expr.mk
    (op := InstCombine.MOp.icmp pred w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def select {Γ : Ctxt _} (w : ℕ) (cond : Var Γ (InstCombine.Ty.bitvec 1))
    (e₁ e₂ : Var Γ (InstCombine.Ty.bitvec w)) : Expr InstCombine.Op Γ (InstCombine.Ty.bitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.select w)
    (ty_eq := rfl)
    (args := .cons cond <| .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)
end ComWrappers


namespace MulDivRem

/-
Name: MulDivRem:805
%r = sdiv 1, %X
  =>
%inc = add %X, 1
%c = icmp ult %inc, 3
%r = select %c, %X, 0

Proof:
======
  Values of LHS:
    - 1/x where x >= 2: 0
    - 1/1 = 1
    - 1/0 = UB
    - 1/ -1 = -1
    - 1/x where x <= -2: 0
  Values of RHS:
    RHS: (x + 2) <_u 3 ? x : 0
    - x >= 2: (x + 1) <_u 3 ? x : 0
              =  false ? x : 0 = false
    - x = 1: (1 + 1) <_u 3 ? x : 0
              = 2 <_u 3 ? x : 0
              = true ? x : 0
              = x = 1
    - x = 0: (0 + 1) <_u 3 ? x : 0
              = 1 <_u 3 ? 0 : 0
              = true ? 0 : 0
              = 0
    - x = -1: (-1 + 1) <_u 3 ? x : 0
              = 0 <_u 3 ? x : 0
              = true ? x : 0
              = x = -1
    - x <= -2 : (-2 + 1) <_u 3 ? x : 0
              = -1 <_u 3 ? x : 0
              = INT_MAX < 3 ? x : 0
              = false ? x : 0
              = 0
 Thus, LHS and RHS agree on values.
-/
open BitVecTheory
open LLVMTheory
open ComWrappers
def MulDivRem805_lhs (w : ℕ) : Com InstCombine.Op [/- %X -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- c1 = -/ Com.lete (const w 1) <|
  /- r = -/ Com.lete (sdiv w ⟨ /- c1-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-%X -/ 1, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def MulDivRem805_rhs (w : ℕ) : Com InstCombine.Op [/- %X -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- c1 = -/ Com.lete (const w 1) <|
  /- inc = -/ Com.lete (add w ⟨ /-c1 -/0, by simp [Ctxt.snoc]⟩ ⟨/-X-/1, by simp [Ctxt.snoc]⟩) <|
  /- c3 = -/ Com.lete (const w 3) <|
  /- c = -/ Com.lete (icmp w .ult ⟨ /-inc -/1, by simp [Ctxt.snoc]⟩ ⟨/-c3-/0, by simp [Ctxt.snoc]⟩) <|
  /- c0 = -/ Com.lete (const w 0) <|
  /- r = -/ Com.lete (select w ⟨/-%c-/1, by simp [Ctxt.snoc]⟩ ⟨/-X-/5, by simp [Ctxt.snoc]⟩ ⟨/-c0-/0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

-- rule: try to keep everything in Nat.
-- theorem :
def alive_simplifyMulDivRem805 (w : Nat) :
  MulDivRem805_lhs w ⊑ MulDivRem805_rhs w := by
  simp only [Com.Refinement]; intros Γv
  simp only [MulDivRem805_lhs, MulDivRem805_rhs,
    InstCombine.Ty.bitvec, const, sdiv, Ctxt.get?, Var.zero_eq_last, add, icmp, select]
  simp_peephole [MOp.sdiv, MOp.binary, MOp.BinaryOp.sdiv, MOp.select, MOp.select] at Γv
  -- figure out why add gets unfolded.
  intros a
  simp only [InstCombine.Op.denote, pairBind, HVector.toPair, HVector.toTuple, Function.comp_apply, HVector.toTriple, bind_assoc, LLVM.const?_eq,
    Bind.bind, Option.bind, LLVM.add?_eq, LLVM.icmp?_ult_eq]
  cases a <;> simp only [BitVec.Refinement.none_left, LLVM.select?_eq_none]
  case some val =>
    have hval : val = 0 ∨ val ≠ 0 := by tauto;
    rcases hval with rfl | hvalnonzero <;> try simp only [BitVec.ofNat_eq_ofNat, LLVM.sdiv?_denom_zero, BitVec.Refinement.none_left]
    case inr =>
      rcases w with zero | w <;> try simp only [Nat.zero_eq, BitVec.ofNat_eq_ofNat,
        eq_iff_true_of_subsingleton, LLVM.sdiv?_denom_zero, BitVec.Refinement.none_left]
      simp [BitVec.ofInt_ofNat _ 3, BitVec.ofInt_ofNat _ 1, BitVec.ofInt_ofNat _ 0]
      have hval : val = -1 ∨ val = 1 ∨ val = 2 ∨ val ≥ 2 ∨ val ≤ -2 := by sorry -- my sorry
      rcases hval with rfl | rfl | rfl | hval | hval <;> try simp
      . /- -1 -/
        conv =>
          rewrite [BitVec.ult_toNat (BitVec.ofNat (Nat.succ w) 0) (BitVec.ofNat (Nat.succ w) 3)]
        simp
        rcases w with rfl | w
        . sorry
        . sorry

      . /- 1 -/
        sorry
      . /- 2 -/
        sorry
      . /- >= 2-/
        sorry
      . /- <= -2 -/
        sorry

/-
Name: MulDivRem:290

%poty = shl 1, %Y
%r = mul %poty, %X
  =>
%r = shl %X, %Y

Proof
======
  1. Without taking UB into account
    ⟦LHS₁⟧: (1 << Y) . X = ( 2^Y) X = 2^Y . X
    ⟦RHS₁⟧: X << Y = X . 2^Y
    equal by ring.

  2. With UB into account
    ⟦LHS₂⟧: (1 << Y) . Op1 = Y >= n ? UB : ⟦LHS₁⟧
    ⟦RHS₂⟧: Op1 << Y = Y >= n ? UB : ⟦RHS₁⟧
    but ⟦LHS₁⟧ = ⟦ RHS₁⟧ and thus we are done.
-/

open ComWrappers
def MulDivRem290_lhs (w : ℕ) :
  Com InstCombine.Op
    [/- %X -/ InstCombine.Ty.bitvec w,
    /- %Y -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- c1 = -/ Com.lete (const w 1) <|
  /- poty = -/ Com.lete (shl w ⟨/- c1 -/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-%Y -/ 1, by simp [Ctxt.snoc]⟩) <|
  /- r = -/ Com.lete (mul w ⟨ /- poty -/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-%X -/ 3, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def MulDivRem290_rhs (w : ℕ) :
  Com InstCombine.Op [/- %X -/ InstCombine.Ty.bitvec w, /- %Y -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- r = -/ Com.lete (shl w ⟨/-X-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-Y-/0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def alive_simplifyMulDivRem290 (w : Nat) :
  MulDivRem290_lhs w ⊑ MulDivRem290_rhs w := by
  simp (config := { unfoldPartialApp := true, decide := true}) only [Com.Refinement]; intros Γv
  simp (config := { unfoldPartialApp := true, decide := true}) only [MulDivRem290_lhs, MulDivRem290_rhs,
    InstCombine.Ty.bitvec, const, shl, mul, Ctxt.get?, Var.zero_eq_last, add, icmp, select]
  simp_peephole [MOp.sdiv, MOp.binary, MOp.BinaryOp.shl, MOp.shl, MOp.mul] at Γv
  intros x y
  simp (config := { unfoldPartialApp := true, decide := true}) [InstCombine.Op.denote, pairBind, HVector.toPair, HVector.toTuple, Function.comp_apply, HVector.toTriple, bind_assoc]
  simp (config := { unfoldPartialApp := true, decide := true}) [bind, Option.bind, LLVM.const?, LLVM.shl?, ge_iff_le, BitVec.zeroExtend_id, LLVM.mul?]
  cases x
  case none => cases y <;> simp (config := { unfoldPartialApp := true, decide := true})
  case some x =>
    cases y <;> try simp (config := { unfoldPartialApp := true, decide := true})
    case none =>
      split_ifs <;> simp (config := { unfoldPartialApp := true, decide := true})
    case some y =>
      split_ifs <;> simp (config := { unfoldPartialApp := true, decide := true})
      case neg hwx =>
        unfold HShiftLeft.hShiftLeft BitVec.instHShiftLeftBitVec
        simp (config := { unfoldPartialApp := true, decide := true}) [HShiftLeft.hShiftLeft, BitVec.shiftLeft, ShiftLeft.shiftLeft]
        unfold HShiftLeft.hShiftLeft instHShiftLeft ShiftLeft.shiftLeft Nat.instShiftLeftNat
        simp (config := { unfoldPartialApp := true, decide := true})
        simp [Nat.shiftLeft_eq]
        cases w <;> try simp (config := { unfoldPartialApp := true, decide := true})  <;> try ring_nf
        case zero => apply Subsingleton.elim
        case succ w' =>
          rw[BitVec.toNat_ofInt_1 (WNEQ0 := Fact.mk (by simp))]
          ring_nf
          simp (config := { unfoldPartialApp := true, decide := true}) [HMul.hMul, Mul.mul, BitVec.mul, Fin.mul, Fin.ofNat', BitVec.toNat, Nat.mul_eq,
            BitVec.ofNat, BitVec.ofFin.injEq, Fin.mk.injEq]
          obtain ⟨x, hx⟩ := x
          obtain ⟨y, hy⟩ := y
          simp
          simp at hwx
          have hx' : 2^ x < 2^ (Nat.succ w') := by
            apply Nat.pow_lt_pow_of_lt_right
            apply Nat.lt_succ_self
            apply hwx
          have hx'' :  2 ^ x % 2 ^ Nat.succ w' = 2 ^ x := by
            apply Nat.mod_eq_of_lt
            apply hx'
          rw [hx'']
          ring_nf

end MulDivRem


namespace AndOrXor
/-
Name: AndOrXor:2515   ((X^C1) >> C2)^C3 = (X>>C2) ^ ((C1>>C2)^C3)
%e1  = xor %x, C1
%op0 = lshr %e1, C2
%r   = xor %op0, C3
  =>
%o = lshr %x, C2 -- (X>>C2)
%p = lshr(%C1,%C2)
%q = xor %p, %C3 -- ((C1>>C2)^C3)
%r = xor %o, %q
-/

open ComWrappers
open BitVecTheory
open LLVMTheory
def AndOrXor2515_lhs (w : ℕ):
  Com InstCombine.Op
    [/- C1 -/ InstCombine.Ty.bitvec w,
     /- C2 -/ InstCombine.Ty.bitvec w,
     /- C3 -/ InstCombine.Ty.bitvec w,
     /- %X -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- e1  = -/ Com.lete (xor w ⟨/-x-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-C1-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- op0 = -/ Com.lete (lshr w ⟨/-e1-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-C2-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- r   = -/ Com.lete (xor w ⟨/-op0-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-C3-/ 3, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def AndOrXor2515_rhs (w : ℕ) :
  Com InstCombine.Op
    [/- C1 -/ InstCombine.Ty.bitvec w,
     /- C2 -/ InstCombine.Ty.bitvec w,
     /- C3 -/ InstCombine.Ty.bitvec w,
     /- %X -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- o = -/ Com.lete (lshr w ⟨/-X-/ 0, by simp [Ctxt.snoc]⟩ ⟨/-C2-/2, by simp [Ctxt.snoc]⟩) <|
  /- p = -/ Com.lete (lshr w ⟨/-C1-/ 4, by simp [Ctxt.snoc]⟩ ⟨/-C2-/3, by simp [Ctxt.snoc]⟩) <|
  /- q = -/ Com.lete (xor w ⟨/-p-/0, by simp [Ctxt.snoc]⟩ ⟨/-C3-/3, by simp [Ctxt.snoc]⟩) <|
  /- r = -/ Com.lete (xor w ⟨/-o-/2, by simp [Ctxt.snoc]⟩ ⟨/-q-/0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩


def alive_simplifyAndOrXor2515 (w : Nat) :
  AndOrXor2515_lhs w ⊑ AndOrXor2515_rhs w := by
  simp only [Com.Refinement]; intros Γv
  simp only [AndOrXor2515_lhs, AndOrXor2515_rhs,
    InstCombine.Ty.bitvec, const, shl, mul, Ctxt.get?, Var.zero_eq_last, add, icmp, ComWrappers.xor, lshr, select]
  simp_peephole [MOp.sdiv, MOp.binary, MOp.BinaryOp.shl, MOp.shl, MOp.mul, MOp.and, MOp.or, MOp.xor, MOp.add] at Γv
  intros x c3 c2 c1
  simp only [InstCombine.Op.denote, pairBind, HVector.toPair, HVector.toTuple, Function.comp_apply, HVector.toTriple, bind_assoc]
  rcases c1 with none | c1 <;>
  rcases c2 with none | c2 <;>
  rcases c3 with none | c3 <;>
  rcases x with none | x <;> simp[Option.bind, Bind.bind]
  . rcases (LLVM.lshr? (x ^^^ c1) c2) with none | _ <;> simp
  . -- TODO: develop automation to automatically do the case split. See also: prime motivation for simproc.
    have hc2: (c2.toNat < w) ∨ ¬ (c2.toNat < w) := by tauto
    rcases hc2 with lt | gt
    . simp only [ge_iff_le, LLVM.lshr?_eq_some lt, BitVec.ushiftRight_eq,
      BitVec.Refinement.some_some]
      ext i
      simp only [BitVec.getLsb'_xor , BitVec.getLsb'_ushr]
      split_ifs <;> try simp
    . have hc2 : c2.toNat ≥ w := by linarith
      simp [LLVM.lshr?_eq_none hc2]
/-
Proof:
------
  bitwise reasoning.
  LHS:
  ----
  (((X^C1) >> C2)^C3))[i]
  = ((X^C1) >> C2)[i] ^ C3[i] [bit-of-lsh r]
  # NOTE: negative entries will be 0 because it is LOGICAL shift right. This is denoted by the []₀ operator.
  = ((X^C1))[i - C2]₀ ^ C3[i] [bit-of-lshr]
  = (X[i - C2]₀ ^ C1[i - C2]₀) ^ C3[i]  [bit-of-xor]
  = X[i - C2]₀ ^ C1[i - C2]₀ ^ C3[i] [assoc]


  RHS:
  ----
  ((X>>C2) ^ ((C1 >> C2)^C3))[i]
  = (X>>C2)[i] ^ (C1 >> C2)^C3)[i] [bit-of-xor]
  # NOTE: negative entries will be 0 because it is LOGICAL shift right
  = X[i - C2]₀ ^ ((C1 >> C2)[i] ^ C3[i]) [bit-of-lshr]
  = X[i - C2]₀ ^ (C1[i-C2] ^ C3[i]) [bit-of-lshr]
-/
end AndOrXor


namespace Select

/-
Name: Select:746
%c = icmp slt %A, 0
%minus = sub 0, %A
%abs = select %c, %A, %minus
%c2 = icmp sgt %abs, 0
%minus2 = sub 0, %abs
%abs2 = select %c2, %abs, %minus2
  =>
%c = icmp slt %A, 0
%minus = sub 0, %A
%abs = select %c, %A, %minus
%c3 = icmp sgt %A, 0
%abs2 = select %c3, %A, %minus
-/

open ComWrappers
open BitVecTheory
def Select746_lhs (w : ℕ):
  Com InstCombine.Op
    [/- A -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- c0     = -/ Com.lete (const w 0) <|
  /- c      = -/ Com.lete (icmp w .slt ⟨/-A-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- minus  = -/ Com.lete (sub w ⟨/-c0-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-A-/ 2, by simp [Ctxt.snoc]⟩) <|
  /- abs    = -/ Com.lete (select w ⟨/-c-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-A-/ 3, by simp [Ctxt.snoc]⟩ ⟨/-minus-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- c2     = -/ Com.lete (icmp w .sgt ⟨/-abs-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- minus2 = -/ Com.lete (sub w ⟨/-c0-/ 4, by simp [Ctxt.snoc]⟩ ⟨ /-abs-/ 1, by simp [Ctxt.snoc]⟩) <|
  /- abs2   = -/ Com.lete (select w ⟨/-c2-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-abs-/ 2, by simp [Ctxt.snoc]⟩ ⟨/-minus2-/ 0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩


def Select746_rhs (w : ℕ):
  Com InstCombine.Op
    [/- A -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- c0     = -/ Com.lete (const w 0) <|
  /- c      = -/ Com.lete (icmp w .slt ⟨/-A-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- minus  = -/ Com.lete (sub w ⟨/-c0-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-A-/ 2, by simp [Ctxt.snoc]⟩) <|
  /- abs    = -/ Com.lete (select w ⟨/-c-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-A-/ 3, by simp [Ctxt.snoc]⟩ ⟨/-minus-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- c3     = -/ Com.lete (icmp w .sgt ⟨/-A-/ 4, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- abs2   = -/ Com.lete (select w ⟨/-c3-/ 0, by simp [Ctxt.snoc]⟩ ⟨/-A-/ 5, by simp [Ctxt.snoc]⟩ ⟨/-minus-/ 2, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

open BitVecTheory
open LLVMTheory

@[simp]
theorem BitVec.ofBool_neq_1 (b : Bool) : BitVec.ofBool b ≠ (BitVec.ofNat 1 1) ↔ (BitVec.ofBool b) = (BitVec.ofNat 1 0) := by
  constructor <;> (intros h; cases b <;> simp at h; simp [BitVec.ofBool])
  · intros h
    contradiction
  · contradiction

@[simp]
theorem BitVec.ofBool_neq_0 (b : Bool) : BitVec.ofBool b ≠ (BitVec.ofNat 1 0) ↔ (BitVec.ofBool b) = (BitVec.ofNat 1 1) := by
  constructor <;> (intros h; cases b <;> simp at h <;> simp_all [BitVec.ofBool, h] <;> try contradiction)
  · intros h
    contradiction

@[simp]
theorem BitVec.ofBool_eq_1 (b : Bool) : BitVec.ofBool b = (BitVec.ofNat 1 1) ↔ b = True := by
  constructor <;> (intros h; cases b <;> simp at h <;> simp_all [BitVec.ofBool, h] <;> contradiction)

@[simp]
theorem BitVec.ofBool_eq_0 (b : Bool) : BitVec.ofBool b = (BitVec.ofNat 1 0) ↔ b = False := by
  constructor <;> (intros h; cases b <;> simp at h <;> simp [BitVec.ofBool] <;> contradiction)

@[simp]
theorem BitVec.neg_of_ofNat_0_minus_self (x : BitVec w) : (BitVec.ofNat w 0) - x = -x := by rfl

@[simp]
theorem BitVec.neg_of_ofInt_0_minus_self (x : BitVec w) : (BitVec.ofInt w 0) - x = -x := by rfl

private theorem Nat.eq_one_of_mod_two_ne_zero (n : Nat) (hn : n % 2 != 0) : n % 2 = 1 := by
  simp at hn
  assumption

theorem Nat.sub_mod_of_lt (n x : Nat) (hxgt0 : x > 0) (hxltn : x < n) : (n - x) % n = n - x := by
  rcases n with zero | n <;> simp
  apply Nat.sub_lt _ hxgt0
  simp only [Nat.zero_lt_succ]


#check Std.BitVec.toNat
-- https://github.com/leanprover/std4/blob/276953b13323ca151939eafaaec9129bf7970306/Std/Data/BitVec/Lemmas.lean#L329-L330
-- This was added 3 days ago by Joe Hendrix.
theorem Std.BitVec.neg_toNat{n : Nat} (x : Std.BitVec n) : Std.BitVec.toNat (-x) = (2 ^ n - Std.BitVec.toNat x) % 2 ^ n := by
  obtain ⟨x, hx⟩ := x
  simp [BitVec.toNat, Neg.neg]

theorem Std.BitVec.neg_toNat_nonzero {n : Nat} (x : Std.BitVec n) (hx : x ≠ 0) :  Std.BitVec.toNat (-x) = (2 ^ n - Std.BitVec.toNat x) := by
  rw [Std.BitVec.neg_toNat]
  apply Nat.mod_eq_of_lt
  obtain ⟨x, hx'⟩ := x
  simp
  apply Nat.sub_lt
  apply Nat.pow_two_pos
  apply Nat.pos_of_ne_zero
  cases x
  . contradiction
  . simp


/-- the value of (x / 2^ (w - 1)) can be either 1 or 0 if (x < 2^w) -/
private lemma Nat.div_two_pow_pred {w : Nat} (hx : x < 2 ^ w) : x / 2 ^ (w - 1) = if 2 ^ (w - 1) <= x then 1 else 0 := by
  split_ifs
  case pos h =>
    rw [Nat.div_eq_sub_div]
    simp
    apply Nat.div_eq_of_lt
    rcases w with rfl | w' <;> simp_all
    . apply Nat.sub_lt_right_of_lt_add h _
      ring_nf
      rw [← Nat.pow_succ]
      assumption
    . simp
    . assumption
  case neg h =>
    apply Nat.div_eq_of_lt
    linarith

-- rhs :  if BitVec.toNat x < 2 ^ w' then x else x - 2#(Nat.succ w') ^ Nat.succ w'
-- lhs:
-- ~~~~
--   (if (BitVec.toNat x / 2 ^ (Nat.succ w' - 1) % 2 != 0) = true then ↑(BitVec.toNat x) - 2#(Nat.succ w') ^ Nat.succ w'
--   else ↑(BitVec.toNat x))
-- lhs:
-- ~~~~
--   (if (BitVec.toNat x / 2 ^ (w') % 2 != 0) = true then ↑(BitVec.toNat x) - 2#(Nat.succ w') ^ Nat.succ w'
--   else ↑(BitVec.toNat x))
-- lhs:
-- ~~~~
--   (if BitVec.toNat x >= 2 ^ (w') then ↑(BitVec.toNat x) - 2#(Nat.succ w') ^ Nat.succ w'
--   else ↑(BitVec.toNat x))
theorem BitVec.toInt_eq (w : Nat) (x : BitVec w): BitVec.toInt x = if x.toNat < (2 : Nat)^(w - 1) then x else x - 2^w := by
  cases w <;> simp
  . apply Subsingleton.elim
  . case succ w' =>
      unfold BitVec.toInt BitVec.msb BitVec.getMsb BitVec.getLsb Nat.testBit
      simp
      rw [Nat.shiftRight_eq_div_pow]
      have hdiv : (BitVec.toNat x) / 2 ^ w' = (BitVec.toNat x) / 2^(Nat.succ w' - 1) := by simp
      rw [hdiv]
      rw [Nat.div_two_pow_pred, Nat.succ_sub_one]
      have hcases : (BitVec.toNat x < 2 ^ w') ∨ (BitVec.toNat x ≥ 2 ^ w') := by
        apply lt_or_ge
      cases hcases
      case inl hle =>
        simp [hle]
        have hle' : ¬ (2 ^ w' ≤ BitVec.toNat x) := by linarith
        simp [hle', bne, Nat.cast, NatCast.natCast]
      case inr hgt =>
        have hgt' : ¬ (BitVec.toNat x < 2 ^ w') := by linarith
        simp at hgt
        simp [hgt, hgt', bne, Nat.cast, NatCast.natCast, BEq.beq, Nat.beq]
      . exact x.toFin.2

theorem BitVec.toInt_eq' (w : Nat) (x : BitVec w): BitVec.toInt x = if x.toNat < (2 : Nat)^(w - 1) then (x.toNat : ℤ) else (x.toNat : ℤ) - 2^w := by
  cases w <;> simp
  . have hx : BitVec.toNat x = (0 : ℕ) := by
      obtain ⟨x, hx⟩ := x
      simp at hx
      subst hx
      rfl
    rw [hx]
    rfl
  . case succ w' =>
      unfold BitVec.toInt BitVec.msb BitVec.getMsb BitVec.getLsb Nat.testBit
      simp
      rw [Nat.shiftRight_eq_div_pow]
      have hdiv : (BitVec.toNat x) / 2 ^ w' = (BitVec.toNat x) / 2^(Nat.succ w' - 1) := by simp
      rw [hdiv]
      rw [Nat.div_two_pow_pred, Nat.succ_sub_one]
      have hcases : (BitVec.toNat x < 2 ^ w') ∨ (BitVec.toNat x ≥ 2 ^ w') := by
        apply lt_or_ge
      cases hcases
      case inl hle =>
        simp [hle]
        have hle' : ¬ (2 ^ w' ≤ BitVec.toNat x) := by linarith
        simp [hle', bne, Nat.cast, NatCast.natCast]
      case inr hgt =>
        have hgt' : ¬ (BitVec.toNat x < 2 ^ w') := by linarith
        simp at hgt
        simp [hgt, hgt', bne, Nat.cast, NatCast.natCast, BEq.beq, Nat.beq]
      . exact x.toFin.2


/-- If a bitvec's toInt is negative, then the toNat will be larger than half of the bitwidth. -/
lemma BitVec.large_of_toInt_lt_zero (w : Nat) (x : BitVec w) (hxToInt : BitVec.toInt x < 0) :
    x.toNat ≥ (2 : Nat) ^ (w - 1) := by
  rcases w with rfl | w'
  case zero => simp at hxToInt
  case succ =>
    rw [BitVec.toInt_eq'] at hxToInt
    split_ifs at hxToInt
    case pos h => linarith
    case neg h =>
      omega

lemma BitVec.toInt_lt_zero_of_large (w : Nat) (x : BitVec w) (hxLarge : x.toNat ≥ (2 : Nat) ^ (w - 1)) : BitVec.toInt x < 0
    := by
  rcases w with rfl | w'
  case zero =>
    simp [BitVec.toNat] at hxLarge
  case succ =>
    rw [BitVec.toInt_eq']
    split_ifs
    case pos h => omega
    case neg h =>
      norm_cast
      have hxToNatVal : x.toNat < 2 ^ (Nat.succ w') :=
        x.toFin.2
      rw [Int.subNatNat_eq_coe]
      omega

lemma BitVec.toInt_lt_zero_iff_large (w : Nat) (x : BitVec w) : BitVec.toInt x < 0 ↔ x.toNat ≥ (2 : Nat) ^ (w - 1) := by
  constructor
  apply BitVec.large_of_toInt_lt_zero
  apply BitVec.toInt_lt_zero_of_large

/-- If a bitvec's toInt is negative, then the toNat will be larger than half of the bitwidth. -/
lemma BitVec.small_of_toInt_pos (w : Nat) (x : BitVec w) (hxToInt : BitVec.toInt x ≥ 0) :
    x.toNat < (2 : Nat) ^ (w - 1) := by
  rcases w with rfl | w'
  case zero => simp [BitVec.width_zero_eq_zero]
  case succ =>
    rw [BitVec.toInt_eq'] at hxToInt
    split_ifs at hxToInt
    case pos h => linarith
    case neg h =>
      exfalso
      simp_all
      have hcontra : BitVec.toNat x < 2 ^ (Nat.succ w') :=
        x.toFin.2
      norm_cast at hxToInt
      linarith

lemma BitVec.toInt_pos_of_small (w : Nat) (x : BitVec w) (hxsmall : x.toNat < (2 : Nat) ^ (w - 1)) : BitVec.toInt x ≥ 0 := by
  rcases w with rfl | w'
  case zero => simp
  case succ =>
    rw [BitVec.toInt_eq']
    split_ifs
    norm_cast
    simp

lemma BitVec.toInt_pos_iff_small (w : Nat) (x : BitVec w) : x.toNat < (2 : Nat) ^ (w - 1) ↔ BitVec.toInt x ≥ 0 := by
  constructor
  apply BitVec.toInt_pos_of_small
  apply BitVec.small_of_toInt_pos

lemma BitVec.toInt_pos_iff_small' (w : Nat) (x : BitVec (w + 1)) : x.toNat < (2 : Nat) ^ w ↔ BitVec.toInt x ≥ 0 := by
  apply BitVec.toInt_pos_iff_small

lemma BitVec.toInt_zero_iff (w : Nat) (x : BitVec w) : BitVec.toInt x = 0 ↔ x = 0 := by
  constructor
  case mpr =>
    intros h
    subst h
    simp [BitVec.toInt, BitVec.msb, BitVec.getMsb, BitVec.getLsb]
  case mp =>
    cases w
    case zero =>
      simp
      apply Subsingleton.elim
    case succ w' =>
      rw [BitVec.toInt_eq']
      intros h
      simp at h
      split_ifs at h
      case pos hpos =>
        apply BitVec.eq_of_toNat_eq
        simp
        norm_cast at h
      case neg hneg =>
        exfalso
        norm_cast at h
        rw [Int.subNatNat_eq_coe] at h
        simp at h
        have h' : (↑(BitVec.toNat x) : ℤ) = ↑(2 ^ Nat.succ w') :=
          Int.eq_of_sub_eq_zero h
        norm_cast at h'
        have hcontra : BitVec.toNat x < 2 ^ (Nat.succ w') :=
          x.toFin.2
        omega
-- 0b100 (w=3)
-- conjecture: BitVec.toInt (- x) = - (BitVec.toInt x) := false
-- #reduce - BitVec.toInt (BitVec.ofNat 3 4) -- Int.ofNat 4
-- #reduce BitVec.toInt (- BitVec.ofNat 3 4) -- Int.negSucc 3

lemma BitVec.toInt_nonzero_iff (w : Nat) (x : BitVec w) : BitVec.toInt x ≠ 0 ↔ x ≠ 0 := by
  constructor
  case mp =>
    contrapose
    simp [BitVec.toInt_zero_iff]
  case mpr =>
    contrapose
    simp [BitVec.toInt_zero_iff]


@[simp]
lemma BitVec.toInt_zero : BitVec.toInt (BitVec.ofNat w 0) = 0 := by
  cases w
  case zero => rfl
  case succ w' =>
    simp [BitVec.toInt, BitVec.msb, BitVec.getMsb, BitVec.getLsb]

-- @[simp]
lemma BitVec.eq_zero_of_neg_eq_zero (w : Nat) (x : BitVec w) (h : -x = 0) : x = 0 := by
  obtain ⟨x, hx⟩ := x
  simp_all
  unfold Neg.neg BitVec.instNegBitVec BitVec.neg BitVec.sub at h
  simp at h
  exact h

lemma BitVec.eq_zero_of_toNat_zero (w : Nat) (x : BitVec w) (h : BitVec.toNat x = 0) : x = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [h]

theorem BitVec.toInt_neg_lt_zero_of_gt_zero (w : Nat) (x : BitVec w) (hx : x.toInt > 0) :
    BitVec.toInt (-x) < 0 := by
  have h : _ := (BitVec.toInt_pos_iff_small w x).mpr (by omega)
  rw [BitVec.toInt_lt_zero_iff_large]
  simp [BitVec.toNat_neg]
  have hxToIntNonzero : BitVec.toInt x ≠ 0 := by
    omega
  rw [BitVec.toInt_nonzero_iff] at hxToIntNonzero
  rw [Nat.sub_mod_of_lt]
  . cases w
    case zero => simp; simp [BitVec.width_zero_eq_zero]
    case succ w' =>
      simp
      have hlt : BitVec.toNat x < 2 ^ (Nat.succ w') := by
        exact x.toFin.2
      simp [Nat.pow_succ, Nat.mul_two] at hlt ⊢
      omega
  . by_contra h
    have hcontra : BitVec.toNat x = 0 := by omega
    have hcontra' : x = 0 := by
      apply BitVec.eq_zero_of_toNat_zero
      exact hcontra
    subst hcontra'
    contradiction
  . exact x.toFin.2



/-- if self is >= 2 ^ (w - 1), then 2^w - self is less that 2^(w - 1)-/
lemma two_pow_sub_of_self_leq_two_pow_pred_of_geq_two_pow_pred (hx : y ≥ 2 ^ (w - 1)) : 2 ^ w - y ≤ 2 ^ (w - 1) := by
  cases w
  case zero =>
    simp_all
  case succ w' =>
    simp_all [Nat.pow_succ]
    simp [Nat.pow_succ, Nat.mul_two] at hx ⊢
    omega


/-- if self is > 2 ^ (w - 1), then 2^w - self is less that 2^(w - 1)-/
lemma two_pow_sub_of_self_lt_two_pow_pred_of_gt_two_pow_pred (hx : y > 2 ^ (w - 1)) : 2 ^ w - y < 2 ^ (w - 1) := by
  cases w
  case zero =>
    simp_all
    linarith
  case succ w' =>
    simp_all [Nat.pow_succ]
    simp [Nat.pow_succ, Nat.mul_two] at hx ⊢
    have hlt : 2 ^ w' > 0 := by
      apply Nat.pow_two_pos
    omega

/-
have : BitVec.toInt A < 0
want : BitVec.toInt (- A) > 0
-/
#reduce (BitVec.ofNat 3 4).toInt  -- -4
#reduce (- (BitVec.ofNat 3 4)).toInt  -- -4

/-- If we know that 'x.toInt < 0', then the are two cases:
- Either the number is -2^(w-1), and it's negation is also the number itself.
- Or the numbe ris any other number, and its negation is positive. -/
theorem BitVec.toInt_neg_gt_zero_of_lt_zero (w : Nat) (x : BitVec w) (hx : x.toInt < 0) :
    -- (BitVec.toInt (-x) > 0 ∧ x ≠ (BitVec.ofNat w ((2 : ℕ) ^ (w - 1)))) ∨
    (BitVec.toInt (-x) > 0) ∨
    (BitVec.toInt (- x) = BitVec.toInt x /\ x = (BitVec.ofNat w ((2 : ℕ) ^ (w - 1)))) := by
  have h : _ := (BitVec.toInt_lt_zero_iff_large w x).mp (by omega)
  have hxvals : BitVec.toNat x = 2 ^ (w - 1) ∨ BitVec.toNat x > 2 ^ (w - 1) := by
    omega
  cases hxvals
  case inl heq =>
    cases w
    case zero =>
      simp_all
    case succ w =>
      repeat rw [BitVec.toInt_eq']
      rw [BitVec.toNat_neg]
      simp [heq]
      have hpot : 2 ^ w > 0 := by apply Nat.pow_two_pos
      have hpotpred : 2 ^ (w - 1) > 0 := by apply Nat.pow_two_pos
      have hcomputation : (2 ^ (Nat.succ w) - 2 ^ (w))= 2 ^ (w) := by
        simp_all [Nat.pow_succ]
        omega
      rw [hcomputation]
      rw [Nat.mod_eq_of_lt]
      simp
      right
      constructor
      . norm_cast
        apply Nat.mod_eq_of_lt
        omega
      . simp at heq
        apply BitVec.eq_of_toNat_eq
        simp [heq]
        symm
        apply Nat.mod_eq_of_lt
        omega
      . omega
  case inr hgt =>
    by_contra h'
    simp (config := {unfoldPartialApp := true}) at h'
    rw [BitVec.toInt_eq'] at h'
    simp [BitVec.toNat_neg] at h'
    rw [Nat.mod_eq_of_lt] at h'
    simp [two_pow_sub_of_self_lt_two_pow_pred_of_gt_two_pow_pred hgt] at h'
    norm_cast at h'
    rw [Nat.sub_mod_of_lt] at h'
    have h'' : BitVec.toNat x ≥ 2^w := by omega
    have hcontra : BitVec.toNat x < 2^w := by
      exact x.toFin.2
    omega
    . omega
    . exact x.toFin.2
    . apply Nat.sub_lt_self
      omega
      have hxmax := x.toFin.2
      omega



def alive_simplifySelect764 (w : Nat) :
  Select746_lhs w ⊑ Select746_rhs w := by
  simp only [Com.Refinement]; intros Γv
  simp only [Select746_lhs, Select746_rhs,
    InstCombine.Ty.bitvec, const, shl, mul, Ctxt.get?, Var.zero_eq_last, add, icmp, ComWrappers.xor, lshr, select, sub, const, icmp]
  simp_peephole [MOp.icmp, MOp.const, MOp.select, MOp.sdiv, MOp.binary, MOp.BinaryOp.shl, MOp.shl, MOp.mul, MOp.and, MOp.or, MOp.xor, MOp.add] at Γv
  intros A
  simp only [InstCombine.Op.denote, pairBind, HVector.toPair, HVector.toTuple, Function.comp_apply, HVector.toTriple, bind_assoc]
  rcases A with none | A  <;> simp [Option.bind, Bind.bind]
  split_ifs <;> try simp only [LLVM.select?_eq_some, BitVec.ofNat_eq_ofNat, BitVec.ofBool_eq_1,
    eq_iff_iff, iff_true]
  case neg h =>
    split_ifs <;> simp
    case pos contra => contradiction
  case pos h =>
    split_ifs <;> simp
  case neg ha hb =>
    split_ifs <;> simp
    case neg hc =>
      simp [BitVec.slt] at hc ha hb
      have h0 :  BitVec.toInt A = 0 := by linarith
      have h0' : A = 0 := by
        apply BitVec.eq_zero_of_toInt_zero
        exact h0
      simp [h0']
  case pos ha hb =>
    split_ifs
    case pos hc =>
      simp only [BitVec.slt, BitVec.toInt_ofInt_zero, decide_eq_true_eq, not_lt] at hc ha hb
      have h' : BitVec.toInt (- (-A)) < 0 := by
        apply BitVec.toInt_neg_lt_zero_of_gt_zero
        omega
      simp at h'
      exfalso
      omega
    case neg hc =>
      simp only [BitVec.slt, BitVec.toInt_ofInt_zero, decide_eq_true_eq, not_lt] at hc ha hb
      simp

#print axioms alive_simplifySelect764

/-
Proof:
======

LHS:
---
c = A <_s 0
minus = 0 - A  [minus = -A]
abs = c ? A : minus [abs = c < 0 ? A : -A] [abs = -|A|]
c2 = abs >= 0 [c2 = -|A| >= 0] [c2 = |A| < 0]
minus2 = -abs = [minus2 = - (-|A|) = |A|)]
abs2 = c2 ? abs : minus2 [abs2 = |A| < 0 ? _ : |A|]  [abs2 = |A|]


RHS:
----
abs2 = A >_s 0 ? A : -A  [abs2 = |A|]

Equivalence proof:
-------------------
  Note that by definition |A| will always be greater than or equal to zero.
  The main case distinction that is happening is on whether 'A <_s 0',
-/



/-
Name: Select:747
%c = icmp sgt %A, 0
%minus = sub 0, %A
%abs = select %c, %A, %minus
%c2 = icmp slt %abs, 0
%minus2 = sub 0, %abs
%abs2 = select %c2, %abs, %minus2
  =>
%c3 = icmp slt %A, 0
%abs2 = select %c3, %A, %minus


c = A s> 0
minus = 0 - A
abs = c ? A : minus (A > 0 ? A : -A)
-/

def Select747_lhs (w : ℕ):
  Com InstCombine.Op
    [/- A -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- c0     = -/ Com.lete (const w 0) <|
  /- c      = -/ Com.lete (icmp w .sgt ⟨/-A-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- minus  = -/ Com.lete (sub w ⟨/-c0-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-A-/ 2, by simp [Ctxt.snoc]⟩) <|
  /- abs    = -/ Com.lete (select w ⟨/-c-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-A-/ 3, by simp [Ctxt.snoc]⟩ ⟨/-minus-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- c2     = -/ Com.lete (icmp w .slt ⟨/-abs-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- minus2 = -/ Com.lete (sub w ⟨/-c0-/ 4, by simp [Ctxt.snoc]⟩ ⟨ /-abs-/ 1, by simp [Ctxt.snoc]⟩) <|
  /- abs2   = -/ Com.lete (select w ⟨/-c2-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-abs-/ 2, by simp [Ctxt.snoc]⟩ ⟨/-minus2-/ 0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def Select747_rhs (w : ℕ) :
  Com InstCombine.Op
    [/- A -/ InstCombine.Ty.bitvec w] (InstCombine.Ty.bitvec w) :=
  /- c0     = -/ Com.lete (const w 0) <|
  /- c3     = -/ Com.lete (icmp w .slt ⟨/-A-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- minus  = -/ Com.lete (sub w ⟨/-c0-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-A-/ 2, by simp [Ctxt.snoc]⟩) <|
  /- abs2   = -/ Com.lete (select w ⟨/-c3-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-A-/ 3, by simp [Ctxt.snoc]⟩ ⟨/-minus-/ 0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

theorem alive_simplifySelect747 (w : Nat) :
  Select747_lhs w ⊑ Select747_rhs w := by
  simp only [Com.Refinement]; intros Γv
  simp only [Select747_lhs, Select747_rhs,
    InstCombine.Ty.bitvec, const, shl, mul, Ctxt.get?, Var.zero_eq_last, add, icmp, ComWrappers.xor, lshr, select, sub, const, icmp]
  simp_peephole [MOp.icmp, MOp.const, MOp.select, MOp.sdiv, MOp.binary, MOp.BinaryOp.shl, MOp.shl, MOp.mul, MOp.and, MOp.or, MOp.xor, MOp.add] at Γv
  intros A
  simp only [InstCombine.Op.denote, pairBind, HVector.toPair, HVector.toTuple, Function.comp_apply, HVector.toTriple, bind_assoc]
  rcases A with none | A  <;> simp [Option.bind, Bind.bind]
  split_ifs <;> try simp
  case neg h =>
    split_ifs <;> simp
    case pos contra => contradiction
  case pos h =>
    split_ifs <;> simp
  case neg ha hb =>
    split_ifs <;> simp
    case neg hc =>
      simp [BitVec.slt] at hc ha hb
      have h0 :  BitVec.toInt A = 0 := by linarith
      have h0' : A = 0 := by
        apply BitVec.eq_zero_of_toInt_zero
        exact h0
      simp [h0']
  case pos ha hb =>
    split_ifs <;> simp
    case pos hc =>
      simp [BitVec.slt] at hc ha hb
      have hcases := BitVec.toInt_neg_gt_zero_of_lt_zero w A hb
      cases hcases
      case inl hlt => exfalso; omega
      case inr heq =>
        obtain ⟨heq1, heq2⟩ := heq
        cases w
        case zero => apply Subsingleton.elim
        case succ w =>
          simp_all
          apply BitVec.toNat_inj.mp
          rw [BitVec.toNat_neg]
          simp [BitVec.toNat_eq]
          repeat rw [Nat.mod_eq_of_lt]
          rw [Nat.pow_succ, Nat.mul_two]
          have hpot : 2^w > 0 :=  by simp [Nat.pow_two_pos]
          omega
          apply Nat.pow_lt_pow_succ
          decide
          rw [Nat.mod_eq_of_lt]
          rw [Nat.pow_succ, Nat.mul_two]
          have hpot : 2^w > 0 :=  by simp [Nat.pow_two_pos]
          omega
          apply Nat.pow_lt_pow_succ
          decide

#print axioms alive_simplifySelect747

end Select



end AliveHandwritten
