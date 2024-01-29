import Std.Data.Nat.Lemmas
import Std.Data.Int.Lemmas
import SSA.Projects.InstCombine.FromStd
import SSA.Projects.InstCombine.LLVM.EDSL
import SSA.Projects.InstCombine.AliveStatements
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.Base
import SSA.Core.ErasedContext

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
  simp

theorem BitVec.ofInt_toFin_nonneg (w : ℕ) (v : Int) {v' : ℕ} (hv : v = ↑v') :
  (BitVec.ofInt w v).toFin = Fin.ofNat' v' (by simp) := by
  subst hv
  simp [BitVec.ofInt, BitVec.ofNat, BitVec.toFin]

@[simp]
theorem BitVec.toNat_ofInt_1 [WNEQ0 : Fact (0 < w)] : BitVec.toNat (BitVec.ofInt w 1) = 1 := by
  simp [BitVec.ofNat, BitVec.toNat, BitVec.ofInt, BitVec.toFin, Fin.val, Fin.ofNat']
  apply Nat.mod_eq_of_lt
  cases w
  . exfalso; simp only[] at WNEQ0; apply Fact.elim WNEQ0
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
theorem BitVec.toInt_ofInt_1_width_zero :
    BitVec.toInt (BitVec.ofInt (n := 0) 1) = 0 := rfl


@[simp]
theorem BitVec.toInt_ofInt_1_width_one :
    BitVec.toInt (BitVec.ofInt (n := 1) 1) = -1 := rfl

-- if w = 0. then value is 0
-- if w = 1, then value is -1.
@[simp]
theorem BitVec.toInt_ofInt_1 [hone_lt_w: Fact (1 < w)] :
    BitVec.toInt (BitVec.ofInt w 1) = 1 := by
  cases w
  case zero => simp at hone_lt_w; apply False.elim hone_lt_w.out
  case succ w' =>
    cases w'
    case zero => simp at hone_lt_w; apply False.elim hone_lt_w.out
    case succ w'' =>
      simp [BitVec.toInt, BitVec.ofInt]
      simp [BitVec.msb, BitVec.getMsb, BitVec.getLsb]
      have hone : 1 % 2^(Nat.succ (Nat.succ w'')) = 1 := by
        apply Nat.mod_eq_of_lt; simp
      rw[hone, Nat.land_comm, Nat.and_one_is_mod]
      rw[Nat.pow_mod, Nat.mod_self]
      cases w''
      case zero =>
        simp
      case succ w'' =>
        rw[Nat.zero_pow (by simp)]
        rw[Nat.zero_mod]
        simp
        apply Int.emod_eq_of_lt <;> try simp
        . apply one_lt_pow; simp; linarith


@[simp]
theorem BitVec.toNat_ofInt_one_width_zero : BitVec.toNat (BitVec.ofInt (n := 0) 1) = 0 := rfl

@[simp]
theorem BitVec.toNat_ofInt_one_width_one : BitVec.toNat (BitVec.ofInt (n := 1) 1) = 1 := rfl

@[simp]
theorem BitVec.toNat_ofInt_one [hzero_lt_w: Fact (0 < w)] : BitVec.toNat (BitVec.ofInt w 1) = 1 := by
  cases w
  case zero => simp at hzero_lt_w; apply False.elim hzero_lt_w.out
  case succ w' =>
      simp [BitVec.toNat, BitVec.ofInt]
      simp [Fin.val, BitVec.ofNat]
      apply Nat.mod_eq_of_lt; simp

@[simp]
theorem BitVec.ofNat_toNat_zero :
BitVec.toNat (BitVec.ofInt w 0) = 0 :=
  by simp [BitVec.toNat, BitVec.ofInt, BitVec.toFin, BitVec.ofNat, OfNat.ofNat]


@[simp]
theorem BitVec.zeroExtend_id (b : BitVec w) :
  BitVec.zeroExtend w b = b := by
  obtain ⟨bval, hbval⟩ := b
  simp [BitVec.zeroExtend, BitVec.ofNat, BitVec.toNat, Fin.ofNat', BitVec.toFin, Fin.val]
  apply Nat.mod_eq_of_lt hbval

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

#check BitVec.getLsb_xor
/-- The usual theorem is stated with nat as the index. -/
@[simp] lemma BitVec.getLsb_xor' (x y : BitVec w) (i : Nat) :
    (x ^^^ y).getLsb i = xor (x.getLsb i) (y.getLsb i) := by sorry

@[simp] lemma BitVec.ushr_bitvec_eq (x y : BitVec w) :
    (x >>> y) = BitVec.ofNat w (x.toNat >>> y.toNat) := rfl

@[simp] lemma BitVec.getLsb_ushr' (x : BitVec w) (y : Nat) (i : Fin w) :
    (x >>> y).getLsb i = if (y > i) then false else (x.getLsb (i - y)) := by
  simp only [HShiftRight.hShiftRight, BitVec.instHShiftRightBitVec,
        HXor.hXor, Xor.xor, BitVec.xor, Fin.xor, Nat.xor, BitVec.ushiftRight,
        ShiftRight.shiftRight, Nat.shiftRight, BitVec.toNat, BitVec.getLsb, BitVec.ofNat,
        Fin.ofNat', Fin.val]
  simp [Nat.one_shiftLeft, Nat.and_two_pow, Nat.testBit]
  sorry

/-- simp normal form is shifting two bitvecs -/
@[simp low] lemma BitVec.ushr_nat_eq (x : BitVec w) (y : Nat) :
    (x >>> y) = (x >>> (BitVec.ofNat w y))  := sorry

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
theorem LLVM.lshr?_eq_none {a b : BitVec w} (hb : b.toNat ≥ w) : LLVM.lshr? (k := w) a b = .none := by
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
theorem LLVM.icmp?_ult_eq {w : Nat} {a b : BitVec w} :
  LLVM.icmp? .ult a b =  Option.some (BitVec.ofBool (a <ᵤ b)) := rfl

@[simp]
theorem LLVM.sdiv?_denom_zero {w : Nat} {a b : BitVec w} (hb : b = 0) : LLVM.sdiv? a b = none :=
  by simp [LLVM.sdiv?, hb]


@[simp]
theorem LLVM.sdiv?_denom_nonzero_inbounds {w : Nat} {a b : BitVec w} (hb : b ≠ 0)
    (hinbounds : LLVM.BitVec.isIntInbounds? w (a.toInt / b.toInt)) :
    LLVM.sdiv? a b = .some (BitVec.ofInt w (a.toInt / b.toInt)) := by
  simp [LLVM.sdiv?, hinbounds, hb, LLVM.BitVec.ofIntInbounds?]
  exact hb


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
    LLVM.const?, LLVM.icmp?,
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
       cases' y with vy <;> simp

end DivRemOfSelect


/- Wrapper around Com, Expr constructors to easily hand-write IR -/
namespace ComWrappers

def const {Γ : Ctxt _} (w : ℕ) (n : ℤ) : Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.const w n)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)

def sdiv {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.sdiv w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def add {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.add w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def sub {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.sub w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def mul {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.mul w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def shl {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.shl w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def lshr {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.lshr w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def xor {Γ : Ctxt _} (w : ℕ) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
  Expr.mk
    (op := InstCombine.MOp.xor w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def icmp {Γ : Ctxt _} (w : ℕ) (pred : LLVM.IntPredicate) (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) :
    Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec 1) :=
  Expr.mk
    (op := InstCombine.MOp.icmp pred w)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def select {Γ : Ctxt _} (w : ℕ) (cond : Var Γ (InstCombine.Ty.mkBitvec 1))
    (e₁ e₂ : Var Γ (InstCombine.Ty.mkBitvec w)) : Expr InstCombine.Op Γ (InstCombine.Ty.mkBitvec w) :=
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
def MulDivRem805_lhs (w : ℕ) : Com InstCombine.Op [/- %X -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
  /- c1 = -/ Com.lete (const w 1) <|
  /- r = -/ Com.lete (sdiv w ⟨ /- c1-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-%X -/ 1, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def MulDivRem805_rhs (w : ℕ) : Com InstCombine.Op [/- %X -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
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
    InstCombine.Ty.mkBitvec, const, sdiv, Ctxt.get?, Var.zero_eq_last, add, icmp, select]
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
      have hval : val = -1 ∨ val = 0 ∨ val = 1 ∨ val = 2 ∨ val ≥ 2 ∨ val ≤ -2 := by sorry
      rcases hval with rfl | rfl | rfl | rfl | hval | hval <;> try simp
      . conv =>
        rewrite [BitVec.ult_toNat (BitVec.ofNat (Nat.succ w) 0) (BitVec.ofNat (Nat.succ w) 3)]
        simp only [BitVec.ofNat_eq_ofNat, ne_eq, BitVec.ofNat_eq_mod_two_pow, Nat.zero_mod]
        rcases w with zero | w'
        . simp [Nat.pow_succ]
        . simp [Nat.pow_succ]; ring_nf
          have h3 : 3 % (2 ^ w' * 4) = 3 := by sorry
          simp [h3]
          sorry -- We need to fix the semantics of sdiv for this to go through.
      . sorry
      . sorry
      . sorry
      . sorry

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
    [/- %X -/ InstCombine.Ty.mkBitvec w,
    /- %Y -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
  /- c1 = -/ Com.lete (const w 1) <|
  /- poty = -/ Com.lete (shl w ⟨/- c1 -/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-%Y -/ 1, by simp [Ctxt.snoc]⟩) <|
  /- r = -/ Com.lete (mul w ⟨ /- poty -/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-%X -/ 3, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def MulDivRem290_rhs (w : ℕ) :
  Com InstCombine.Op [/- %X -/ InstCombine.Ty.mkBitvec w, /- %Y -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
  /- r = -/ Com.lete (shl w ⟨/-X-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-Y-/0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def alive_simplifyMulDivRem290 (w : Nat) :
  MulDivRem290_lhs w ⊑ MulDivRem290_rhs w := by
  simp only [Com.Refinement]; intros Γv
  simp only [MulDivRem290_lhs, MulDivRem290_rhs,
    InstCombine.Ty.mkBitvec, const, shl, mul, Ctxt.get?, Var.zero_eq_last, add, icmp, select]
  simp_peephole [MOp.sdiv, MOp.binary, MOp.BinaryOp.shl, MOp.shl, MOp.mul] at Γv
  intros x y
  simp only [InstCombine.Op.denote, pairBind, HVector.toPair, HVector.toTuple, Function.comp_apply, HVector.toTriple, bind_assoc]
  simp only [bind, Option.bind, LLVM.const?, LLVM.shl?, ge_iff_le, BitVec.zeroExtend_id, LLVM.mul?]
  cases x
  case none => cases y <;> simp
  case some x =>
    cases y <;> try simp
    case none =>
      split_ifs <;> simp
    case some y =>
      split_ifs <;> simp
      case neg hwx =>
        simp only [HShiftLeft.hShiftLeft, BitVec.shiftLeft, ShiftLeft.shiftLeft, Nat.shiftLeft_eq']
        cases w <;> try simp
        case succ w' =>
        rw[BitVec.toNat_ofInt_1 (WNEQ0 := Fact.mk (by simp))]
        simp only [HMul.hMul, Mul.mul, BitVec.mul, Fin.mul, Fin.ofNat', BitVec.toNat, Nat.mul_eq,
          BitVec.ofNat, BitVec.ofFin.injEq, Fin.mk.injEq]
        norm_num
        conv =>
          lhs
          rw[Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        congr 1
        ring

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
    [/- C1 -/ InstCombine.Ty.mkBitvec w,
     /- C2 -/ InstCombine.Ty.mkBitvec w,
     /- C3 -/ InstCombine.Ty.mkBitvec w,
     /- %X -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
  /- e1  = -/ Com.lete (xor w ⟨/-x-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-C1-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- op0 = -/ Com.lete (lshr w ⟨/-e1-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-C2-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- r   = -/ Com.lete (xor w ⟨/-op0-/ 0, by simp [Ctxt.snoc]⟩ ⟨ /-C3-/ 3, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

def AndOrXor2515_rhs (w : ℕ) :
  Com InstCombine.Op
    [/- C1 -/ InstCombine.Ty.mkBitvec w,
     /- C2 -/ InstCombine.Ty.mkBitvec w,
     /- C3 -/ InstCombine.Ty.mkBitvec w,
     /- %X -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
  /- o = -/ Com.lete (lshr w ⟨/-X-/ 0, by simp [Ctxt.snoc]⟩ ⟨/-C2-/2, by simp [Ctxt.snoc]⟩) <|
  /- p = -/ Com.lete (lshr w ⟨/-C1-/ 4, by simp [Ctxt.snoc]⟩ ⟨/-C2-/3, by simp [Ctxt.snoc]⟩) <|
  /- q = -/ Com.lete (xor w ⟨/-p-/0, by simp [Ctxt.snoc]⟩ ⟨/-C3-/3, by simp [Ctxt.snoc]⟩) <|
  /- r = -/ Com.lete (xor w ⟨/-o-/2, by simp [Ctxt.snoc]⟩ ⟨/-q-/0, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩


def alive_simplifyAndOrXor2515 (w : Nat) :
  AndOrXor2515_lhs w ⊑ AndOrXor2515_rhs w := by
  simp only [Com.Refinement]; intros Γv
  simp only [AndOrXor2515_lhs, AndOrXor2515_rhs,
    InstCombine.Ty.mkBitvec, const, shl, mul, Ctxt.get?, Var.zero_eq_last, add, icmp, ComWrappers.xor, lshr, select]
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
      simp only [BitVec.getLsb_xor, BitVec.getLsb_ushr']
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
def Select746_lhs (w : ℕ):
  Com InstCombine.Op
    [/- A -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
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
    [/- A -/ InstCombine.Ty.mkBitvec w] (InstCombine.Ty.mkBitvec w) :=
  /- c0     = -/ Com.lete (const w 0) <|
  /- c      = -/ Com.lete (icmp w .slt ⟨/-A-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- minus  = -/ Com.lete (sub w ⟨/-c0-/ 1, by simp [Ctxt.snoc]⟩ ⟨ /-A-/ 2, by simp [Ctxt.snoc]⟩) <|
  /- abs    = -/ Com.lete (select w ⟨/-c-/ 1, by simp [Ctxt.snoc]⟩ ⟨/-A-/ 3, by simp [Ctxt.snoc]⟩ ⟨/-minus-/ 0, by simp [Ctxt.snoc]⟩) <|
  /- c3     = -/ Com.lete (icmp w .sgt ⟨/-A-/ 4, by simp [Ctxt.snoc]⟩ ⟨ /-c0-/ 3, by simp [Ctxt.snoc]⟩) <|
  /- abs2   = -/ Com.lete (select w ⟨/-c3-/ 0, by simp [Ctxt.snoc]⟩ ⟨/-A-/ 5, by simp [Ctxt.snoc]⟩ ⟨/-minus-/ 2, by simp [Ctxt.snoc]⟩) <|
  Com.ret ⟨/-r-/0, by simp [Ctxt.snoc]⟩

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
end Select
end AliveHandwritten
