import SSA.Core.Framework
import SSA.Core.Util
import Qq

namespace SSA

open Ctxt (Var Valuation DerivedCtxt)

section

open Lean Meta Elab.Tactic Qq

/-- Given a `Γv : Valuation Γ`, fully reduce the context `Γ` in the type of `Γv`.
This is needed for some simp-lemmas to apply correctly -/
elab "change_mlir_context " Γv:ident : tactic => do
  let Γv : Name := Γv.getId
  withMainContext do
    let ctx ← getLCtx
    let Vdecl : LocalDecl ← match ctx.findFromUserName? Γv with
      | some decl => pure decl
      | none => throwError f!"Failed to find variable `{Γv}` in the local context"

    -- Assert that the type of `Γv` is `Ctxt.Valuation ?Γ`
    let Ty ← mkFreshExprMVarQ q(Type)
    let Γ  ← mkFreshExprMVarQ q(Ctxt $Ty)
    let G  ← mkFreshExprMVarQ q(TyDenote $Ty)
    let _  ← assertDefEqQ Vdecl.type q(@Ctxt.Valuation $Ty $G $Γ)

    -- Reduce the context `Γ`
    let Γr ← reduce Γ
    let Γr : Q(Ctxt $Ty) := Γr

    let goal ← getMainGoal
    let newGoal ← goal.changeLocalDecl Vdecl.fvarId q(Valuation $Γr)
    replaceMainGoal [newGoal]

end

@[simp]
private theorem Ctxt.destruct_cons {Ty} [TyDenote Ty] {Γ : Ctxt Ty} {t : Ty} {f : Ctxt.Valuation (t :: Γ) → Prop} :
    (∀ V, f V) ↔ (∀ (a : ⟦t⟧) (V : Γ.Valuation), f (V.snoc a)) := by
  constructor
  · intro h a V; apply h
  · intro h V; cases V; apply h

@[simp]
private theorem Ctxt.destruct_nil {Ty} [TyDenote Ty] {f : Ctxt.Valuation ([] : Ctxt Ty) → Prop} :
    (∀ V, f V) ↔ (f Ctxt.Valuation.nil) := by
  constructor
  · intro h; apply h
  · intro h V; rw [Ctxt.Valuation.eq_nil V]; exact h

/--
`simp_peephole at ΓV` simplifies away the framework overhead of denotating expressions/programs,
that are evaluated with the valuation `ΓV`.

In it's bare form, it only simplifies away the core framework definitions (e.g., `Expr.denote`), but
we can also pass it dialect-specific definitions to unfold, as in:
`simp_peephole [foo, bar, baz] at ΓV`

After simplifying, the goal state should only contiain occurense of `ΓV` directly applied to some
variable `v : Var Γ ty`. The tactic tries to eliminate the evaluation completely, by introducing a
new universally quantified (Lean) variable to the goal for every (object) variable `v`. -/
macro "simp_peephole" "[" ts: Lean.Parser.Tactic.simpLemma,* "]" "at" Γv:ident : tactic =>
  `(tactic|
      (
      /- First, massage the type of `Γv`.
      Generally, `simp_peephole` is expected to be run with the type of `Γv` a
      (not necessarily reduced) ground-term.
      After `change_mlir_context`, type of `Γv` should then be `[t₁, t₂, ..., tₙ]`, for some
      types `t₁`, `t₂`, etc. -/
      change_mlir_context $Γv

      /- unfold the definition of the denotation of a program -/
      simp (config := {unfoldPartialApp := true, failIfUnchanged := false}) only [
        Int.ofNat_eq_coe, Nat.cast_zero, DerivedCtxt.snoc, DerivedCtxt.ofCtxt,
        DerivedCtxt.ofCtxt_empty, Valuation.snoc_last,
        Var.zero_eq_last, Var.succ_eq_toSnoc,
        Ctxt.empty, Ctxt.empty_eq, Ctxt.snoc, Valuation.nil, Valuation.snoc_last,
        Valuation.snoc_eval, Ctxt.ofList, Valuation.snoc_toSnoc,
        HVector.map, HVector.toPair, HVector.toTuple, OpDenote.denote, Expr.op_mk, Expr.args_mk,
        DialectMorphism.mapOp, DialectMorphism.mapTy, List.map, Ctxt.snoc, List.map,
        Function.comp, Valuation.ofPair, Valuation.ofHVector, Function.uncurry,
        /- Unfold denotation -/
        Com.denote_lete, Com.denote_ret, Expr.denote_unfold, HVector.denote,
        /- Effect massaging -/
        EffectKind.toMonad_pure, EffectKind.toMonad_impure,
        EffectKind.liftEffect_rfl,
        Id.pure_eq, Id.bind_eq, id_eq,
        $ts,*]

      /- Attempt to replace all occurence of a variable accesses `Γ ⟨i, _⟩` with a new (Lean)
      variable in the local context
      HACK: for now, we assume no program contains a variable with `i > 5` -/
      try generalize $Γv { val := 0, property := _ } = a;
      try generalize $Γv { val := 1, property := _ } = b;
      try generalize $Γv { val := 2, property := _ } = c;
      try generalize $Γv { val := 3, property := _ } = d;
      try generalize $Γv { val := 4, property := _ } = e;
      try generalize $Γv { val := 5, property := _ } = f;
      try simp (config := {failIfUnchanged := false, decide := false, zetaDelta := true}) [TyDenote.toType]
        at a b c d e f

      /- The previous step will introduce all variables, even if there is no occurence of, say,
      `Γv ⟨5, _⟩`. Thus, we try to clear each of the newly introduced variables.
      If the variable does occur in the goal
      (i.e., there was a `Γv ⟨i, _⟩` in the original, simplified, goal),
      then clearing will fail (hence the `try`), leaving the variable in the context.

      However, if the variable was redundantly introduced, this will remove it from the context -/
      try clear f;
      try clear e;
      try clear d;
      try clear c;
      try clear b;
      try clear a;

      /- Now, revert each variable, so that the variable from the local context is turned into a
      universal quantifier (`∀ _, ...`) in the goal statement.
      We do this primarly because the introduces variables `a`, `b`, etc. are made inaccesible by
      macro hygiene, and we find a universally quantified goal more aesthetic than one with
      inaccessible names.

      Note, this will fail if the variable was removed in the previous step, hence we use `try` -/
      try revert f;
      try revert e;
      try revert d;
      try revert c;
      try revert b;
      try revert a;

      /- Finally, try to clear the valuation. This succeeds iff there are no more occurences of
      `Γv` in the goal, which happens iff the simplified goal contained `Γv` only applied direclty
      to a variable (with index `i ≤ 5`) -/
      try clear $Γv;
      )
   )

/-- `simp_peephole` with no extra user defined theorems. -/
macro "simp_peephole" "at" Γv:ident : tactic => `(tactic| simp_peephole [] at $Γv)

end SSA
