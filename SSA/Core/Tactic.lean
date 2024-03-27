import SSA.Core.Framework
import SSA.Core.Util
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
`simp_peephole [t1, t2, ... tn]` at Γ simplifies the evaluation of the context Γ,
leaving behind a bare Lean level proposition to be proven.
-/
macro "simp_peephole" "[" ts: Lean.Parser.Tactic.simpLemma,* "]" "at" ll:ident : tactic =>
  `(tactic|
      (
      change_mlir_context $ll
      revert $ll
      simp (config := {decide := false}) only [
        Int.ofNat_eq_coe, Nat.cast_zero, Nat.cast_one,
        DerivedCtxt.snoc, DerivedCtxt.ofCtxt, DerivedCtxt.ofCtxt_empty, Valuation.snoc_last,
        Com.denote, Expr.denote, HVector.denote, Var.zero_eq_last, Var.succ_eq_toSnoc,
        Ctxt.empty, Ctxt.empty_eq, Ctxt.snoc,
        Ctxt.Valuation.nil, Ctxt.Valuation.snoc_last, Ctxt.Valuation.snoc_eval, Ctxt.ofList,
        Ctxt.Valuation.snoc_toSnoc,
        HVector.map, HVector.toPair, HVector.toTuple, OpDenote.denote, Expr.op_mk, Expr.args_mk,
        DialectMorphism.mapOp, DialectMorphism.mapTy, List.map, Ctxt.snoc, List.map,
        Function.comp, Valuation.ofPair, Valuation.ofHVector, Function.uncurry,
        Ctxt.destruct_cons, Ctxt.destruct_nil,
        List.length_singleton, Fin.zero_eta, List.map_eq_map, List.map_cons, List.map_nil,
        bind_assoc, pairBind,
        $ts,*]

      -- HACK: For some reason `Ctxt.Valuation.snoc_last` is not applying when it ought to,
      -- so we just reduce it manually
      repeat (conv =>
            pattern ((Ctxt.Valuation.snoc _ _) _)
            whnf)
      )
   )

/-- `simp_peephole` with no extra user defined theorems. -/
macro "simp_peephole" "at" ll:ident : tactic => `(tactic| simp_peephole [] at $ll)

end SSA
