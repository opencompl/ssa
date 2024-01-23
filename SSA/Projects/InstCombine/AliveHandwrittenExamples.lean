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
BitVec.toNat (BitVec.ofInt w 0) = 0 :=
  by simp[BitVec.toNat, BitVec.ofInt, BitVec.toFin, BitVec.ofNat, OfNat.ofNat]

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
set_option pp.analyze true in
def alive_simplifyMulDivRem805 (w : Nat) :
    [alive_icom ( w )| {
    ^bb0(%X : _):
      %v1  = "llvm.mlir.constant" () { value = 1 : _ } :() -> (_)
      %r   = "llvm.sdiv" (%v1, %X) : (_, _) -> (_)
      "llvm.return" (%r) : (_) -> ()
    }] ⊑ [alive_icom ( w )| {
    ^bb0(%X : _):
      %v1  = "llvm.mlir.constant" () { value = 1 : _ } :() -> (_)
      %inc = "llvm.add" (%v1,%X) : (_, _) -> (_)
      %v3  = "llvm.mlir.constant" () { value = 3 : _ } :() -> (_)
      %c   = "llvm.icmp.ult" (%inc, %v3) : (_, _) -> (i1)
      %v0  = "llvm.mlir.constant" () { value = 0 : _ } :() -> (_)
      %r = "llvm.select" (%c, %X, %v0) : (i1, _, _) -> (_)
      "llvm.return" (%r) : (_) -> ()
    }] := by
  intros Γv
  change Ctxt.Valuation [InstCombine.MTy.bitvec (ConcreteOrMVar.concrete w)] at Γv 
  dsimp only [Com.Refinement]
  simp (config := {decide := false}) only [
    InstcombineTransformDialect.MOp.instantiateCom, InstcombineTransformDialect.instantiateMOp,
    ConcreteOrMVar.instantiate, Vector.get, List.nthLe, List.length_singleton, Var.toSnoc, Fin.coe_fin_one, Fin.zero_eta,
    List.get_cons_zero, Function.comp_apply, InstcombineTransformDialect.instantiateMTy, Ctxt.empty_eq, Ctxt.DerivedCtxt.snoc,
    Ctxt.DerivedCtxt.ofCtxt, List.map_eq_map, List.map, DialectMorphism.mapTy, List.get,
    Int.ofNat_eq_coe, Nat.cast_zero, Ctxt.DerivedCtxt.snoc, Ctxt.DerivedCtxt.ofCtxt,
    Ctxt.DerivedCtxt.ofCtxt_empty, Ctxt.Valuation.snoc_last,
    Com.denote, Expr.denote, HVector.denote, Var.zero_eq_last, Var.succ_eq_toSnoc,
    Ctxt.empty, Ctxt.empty_eq, Ctxt.snoc, Ctxt.Valuation.nil, Ctxt.Valuation.snoc_last,
    Ctxt.ofList, Ctxt.Valuation.snoc_toSnoc,
    HVector.map, HVector.toPair, HVector.toTuple, OpDenote.denote, Expr.op_mk, Expr.args_mk,
    DialectMorphism.mapOp, DialectMorphism.mapTy, List.map, Ctxt.snoc, List.map,
    -- extra lemmas
    OpDenote.denote,
    InstCombine.Op.denote, HVector.toPair, HVector.toTriple, pairMapM, BitVec.Refinement,
    bind, Option.bind, pure, Ctxt.DerivedCtxt.ofCtxt, Ctxt.DerivedCtxt.snoc,
    Ctxt.snoc,
    ConcreteOrMVar.instantiate, Vector.get, HVector.toSingle,
    LLVM.and?, LLVM.or?, LLVM.xor?, LLVM.add?, LLVM.sub?,
    LLVM.mul?, LLVM.udiv?, LLVM.sdiv?, LLVM.urem?, LLVM.srem?,
    LLVM.sshr, LLVM.lshr?, LLVM.ashr?, LLVM.shl?, LLVM.select?,
    LLVM.const?, LLVM.icmp?,
    HVector.toTuple, List.nthLe, bitvec_minus_one,
    DialectMorphism.mapTy,
    InstcombineTransformDialect.instantiateMTy,
    InstcombineTransformDialect.instantiateMOp,
    InstcombineTransformDialect.MOp.instantiateCom,
    InstcombineTransformDialect.instantiateCtxt,
    ConcreteOrMVar.instantiate, Com.Refinement,
    DialectMorphism.mapTy,
    List.get, InstcombineTransformDialect.MOp.instantiateCom, InstcombineTransformDialect.instantiateMOp,
    ConcreteOrMVar.instantiate, Vector.get, List.nthLe, List.length_singleton, Fin.coe_fin_one, Fin.zero_eta,
    List.get_cons_zero, Function.comp_apply, InstcombineTransformDialect.instantiateMTy, Ctxt.empty_eq, Ctxt.DerivedCtxt.snoc,
    Ctxt.DerivedCtxt.ofCtxt, List.map_eq_map, List.map, DialectMorphism.mapTy, List.get]
  simp [pairBind, Nat.cast_one, Ctxt.get?, List.length_singleton, Ctxt.empty_eq, Ctxt.DerivedCtxt.snoc,
    Ctxt.DerivedCtxt.ofCtxt, Ctxt.DerivedCtxt.ofCtxt_empty, Fin.zero_eta, List.map_cons, List.map_nil, zero_add,
    Var.succ_eq_toSnoc, Var.zero_eq_last, Ctxt.Valuation.snoc_toSnoc, BitVec.ofNat_eq_ofNat, Nat.cast_ofNat]
  generalize Γv { val := 0, property := _ } = a;
  sorry

/-
Proof state from commit 'a37ebf8bb078c3406ab197a657a50988d3fd0412' for 'alive_simplifyMulDivRem805' :
(if x0✝ = 0#w then none
  else
    if LLVM.ofIntInbounds w (BitVec.toInt (BitVec.ofInt w 1) / BitVec.toInt x0✝) then
      some (BitVec.ofInt w (BitVec.toInt (BitVec.ofInt w 1) / BitVec.toInt x0✝))
    else none) ⊑
  match some (BitVec.ofBool (LLVM.icmp LLVM.IntPredicate.ult (BitVec.ofInt w 1 + x0✝) (BitVec.ofInt w 3))) with
  | none => none
  | some { toFin := { val := 1, isLt := _ } } => some x0✝
  | some { toFin := { val := 0, isLt := _ } } => some (BitVec.ofInt w 0)
-/



/-
Name: MulDivRem:290

%Op0 = shl 1, %Y
%r = mul %Op0, %Op1
  =>
%r = shl %Op1, %Y

Proof
======
  1. Without taking UB into account
    ⟦LHS₁⟧: (1 << Y) . Op1 = (1 . 2^Y) X = 2^Y . Op1
    ⟦RHS₁⟧: Op1 << Y = Op1 . 2^Y
    equal by ring.

  2. With UB into account
    ⟦LHS₂⟧: (1 << Y) . Op1 = Y >= n ? UB : ⟦LHS₁⟧
    ⟦RHS₂⟧: Op1 << Y = Y >= n ? UB : ⟦RHS₁⟧
    but ⟦LHS₁⟧ = ⟦ RHS₁⟧ and thus we are done.

-/
def alive_simplifyMulDivRem290 (w : Nat) :
    [alive_icom ( w )| {
    ^bb0(%Op1 : _ , %Y : _):
      %v1  = "llvm.mlir.constant" () { value = 1 : _ } :() -> (_)
      %Op0   = "llvm.shl" (%v1, %Y) : (_, _) -> (_)
      %r = "llvm.mul"(%Op0, %Op1) : (_, _) -> (_)
      "llvm.return" (%r) : (_) -> ()
    }] ⊑ [alive_icom ( w )| {
    ^bb0(%Op1 : _, %Y : _):
      %r = "llvm.mul" (%Op1, %Y) : (_, _) -> (_)
      "llvm.return" (%r) : (_) -> ()
    }] := by
  dsimp only [Com.Refinement]
  intros Γv
  simp [InstcombineTransformDialect.MOp.instantiateCom, InstcombineTransformDialect.instantiateMOp,
    ConcreteOrMVar.instantiate, Vector.get, List.nthLe, List.length_singleton, Fin.coe_fin_one, Fin.zero_eta,
    List.get_cons_zero, Function.comp_apply, InstcombineTransformDialect.instantiateMTy, Ctxt.empty_eq, Ctxt.DerivedCtxt.snoc,
    Ctxt.DerivedCtxt.ofCtxt, List.map_eq_map, List.map, DialectMorphism.mapTy, List.get] at Γv

  generalize Γv { val := 0, property := _ } = a;
  sorry


end MulDivRem


namespace AndOrXor
/-
Name: AndOrXor:2515   ((X^C1) >> C2)^C3 -> (X>>C2) ^ ((C1>>C2)^C3)
%e1  = xor %x, C1
%op0 = lshr %e1, C2
%r   = xor %op0, C3
  =>
%0 = lshr %x, C2
%r = xor %0, lshr(C1,C2)^C3


Proof:
------
  bitwise reasoning.
  LHS:
  ----
  (((X^C1) >> C2)^C3))[i] 
  = ((X^C1) >> C2)[i] ^ C3[i] [bit-of-lshr]
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
%c3 = icmp sgt %A, 0
%abs2 = select %c3, %A, %minus


Proof:
======

LHS:
---
c = A <s 0
minus = 0 - A  [minus = -A]
abs = c ? A : minus [abs = c < 0 ? A : -A] [abs = -|A|]
c2 = abs >= 0 [c2 = -|A| >= 0] [c2 = |A| < 0]
minus2 = -abs = [minus2 = - (-|A|) = |A|)]
abs2 = c2 ? abs : minus2 [abs2 = |A| < 0 ? _ : |A|]  [abs2 = |A|]


RHS:
----
abs2 = A s> 0 ? A : -A  [abs2 = |A|]

Equivalence proof:
-------------------
  Note that by definition |A| will always be greater than or equal to zero.
  The main case distinction that is happening is on whether 'A <s 0',
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

