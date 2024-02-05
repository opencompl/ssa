import SSA.Core.Framework
import Qq

namespace SSA

open Ctxt (Var Valuation DerivedCtxt)

section

open Lean Meta Elab.Tactic Qq

/-- Given a `V : Valuation Γ`, fully reduce the context `Γ` in the type of `V` -/
elab "change_mlir_context " V:ident : tactic => do
  let V : Name := V.getId
  withMainContext do
    let ctx ← getLCtx
    let Vdecl : LocalDecl ← match ctx.findFromUserName? V with
      | some decl => pure decl
      | none => throwError f!"Failed to find variable `{V}` in the local context"

    -- Assert that the type of `V` is `Ctxt.Valuation ?Γ`
    let Ty ← mkFreshExprMVarQ q(Type)
    let Γ  ← mkFreshExprMVarQ q(Ctxt $Ty)
    let G  ← mkFreshExprMVarQ q(Goedel $Ty)
    let _  ← assertDefEqQ Vdecl.type q(@Ctxt.Valuation $Ty $G $Γ)

    -- Reduce the context `Γ`
    let Γr ← reduce Γ
    let Γr : Q(Ctxt $Ty) := Γr

    let goal ← getMainGoal
    let newGoal ← goal.changeLocalDecl Vdecl.fvarId q(Valuation $Γr)
    replaceMainGoal [newGoal]

end

/--
`simp_peephole [t1, t2, ... tn]` at Γ simplifies the evaluation of the context Γ,
leaving behind a bare Lean level proposition to be proven.
-/
macro "simp_peephole" "[" ts: Lean.Parser.Tactic.simpLemma,* "]" "at" ll:ident : tactic =>
  `(tactic|
      (
      change_mlir_context $ll
      try simp (config := {unfoldPartialApp := true}) only [
        Int.ofNat_eq_coe, Nat.cast_zero, DerivedCtxt.snoc, DerivedCtxt.ofCtxt,
        DerivedCtxt.ofCtxt_empty, Valuation.snoc_last,
        Com.denote, Expr.denote, HVector.denote, Var.zero_eq_last, Var.succ_eq_toSnoc,
        Ctxt.empty, Ctxt.empty_eq, Ctxt.snoc, Valuation.nil, Valuation.snoc_last,
        Valuation.snoc_eval, Ctxt.ofList, Valuation.snoc_toSnoc,
        HVector.map, HVector.toPair, HVector.toTuple, OpDenote.denote, Expr.op_mk, Expr.args_mk,
        DialectMorphism.mapOp, DialectMorphism.mapTy, List.map, Ctxt.snoc, List.map,
        Function.comp, Valuation.ofPair, Valuation.ofHVector, Function.uncurry,
        $ts,*]
      try generalize $ll { val := 0, property := _ } = a;
      try generalize $ll { val := 1, property := _ } = b;
      try generalize $ll { val := 2, property := _ } = c;
      try generalize $ll { val := 3, property := _ } = d;
      try generalize $ll { val := 4, property := _ } = e;
      try generalize $ll { val := 5, property := _ } = f;
      try simp (config := {decide := false}) [Goedel.toType] at a b c d e f;
      try clear f;
      try clear e;
      try clear d;
      try clear c;
      try clear b;
      try clear a;
      try revert f;
      try revert e;
      try revert d;
      try revert c;
      try revert b;
      try revert a;
      try clear $ll;
      )
   )

/-- `simp_peephole` with no extra user defined theorems. -/
macro "simp_peephole" "at" ll:ident : tactic => `(tactic| simp_peephole [] at $ll)

end SSA
