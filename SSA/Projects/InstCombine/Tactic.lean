import SSA.Core.WellTypedFramework
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForMathlib
import SSA.Projects.InstCombine.CommRing
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Vector.MapLemmas

open SSA 



namespace Bitvec.Tactic
  open Lean Meta Tactic Elab.Tactic

  /--
    Checks whether every occurence of free variable `x` is in an expression `get x i`, for
    possibly different values of `i`.
    Returns a list of all such `i` that were found, if indeed all occurences were guarded,
    or `none` if a non-guarded occurence of `x` was found
  -/
  def findBitvecGet : Expr → Option (Expr)
    | e@(.app (.app (.app (.app (.const ``Vector.get _) _) _) _) _) =>
        -- dbg_trace "Found (get x i) pattern (x={y.name}, i={i}), looking for {x.name}"
        e

    | .proj _ _ e
    | .mdata _ e =>
        findBitvecGet e

    | .forallE _ e₁ e₂ _
    | .lam _ e₁ e₂ _
    | .app e₁ e₂ => do
        (findBitvecGet e₁).orElse fun _ => findBitvecGet e₂

    | .letE _ e₁ e₂ e₃ _ => do
        ((findBitvecGet e₁).orElse fun _ => findBitvecGet e₂).orElse fun _ => findBitvecGet e₃

    | _ =>
        -- All other expression constructors are atomic, and do not contain free vars
        none

  open Lean.PrettyPrinter (delab) in
  /--
    For every variable `x : Bitvec n` in the local context, if the goal only contains `x` as part of 
    a `get x i` expression (for arbitary value of `i`), do a case split on `get x i`
  -/
  @[aesop unsafe 50% tactic]
  def bitblast_bitvec_get : TacticM Unit := do
    withMainContext do
      let goal ← getMainTarget
      match findBitvecGet goal with
        | some e =>
            let tgt ← delab e
            let tct ← `(tactic| cases ($tgt))
            dbg_trace "{tct}"
            evalTactic tct
        | none =>
            throwError "Could not find any instance of `get x i`, where `x` does not occur unguarded"

  elab "bitblast_bitvec_get" : tactic => bitblast_bitvec_get

  attribute [aesop norm simp]
    Bitvec.not
    Bitvec.and
    Bitvec.or
    Bitvec.xor
    Vector.map₂_comm
    Vector.mapAccumr₂_comm

  section Desugar
    variable (x y : Bitvec n)
    @[aesop norm 5 simp ]
    protected theorem desugar_not : ~~~x = Bitvec.not x :=
      rfl

    @[aesop norm 5 simp]
    protected theorem desugar_and : x &&& y = x.and y :=
      rfl

    @[aesop norm 5 simp]
    protected theorem desugar_or : x ||| y = x.or y :=
      rfl

    @[aesop norm 5 simp]
    protected theorem desugar_xor : x ^^^ y = x.xor y :=
      rfl

    @[aesop norm 4 simp]
    protected theorem desugar_zero : (0 : Bitvec n) = Vector.replicate n false :=
      rfl

    @[aesop norm 4 simp]
    protected theorem desugar_negOne : (-1 : Bitvec n) = Vector.replicate n true := by
      sorry
  end Desugar

  section Ext
    @[ext, aesop safe]
    protected theorem Bitvec.ext {xs ys : Bitvec n} :
        (∀ i, xs.get i = ys.get i) → xs = ys := by
      intro h
      induction xs, ys using Vector.inductionOn₂
      next => rfl
      next x y xs ys ih =>
        have : x = y := h 0
        rw[this, ih <| fun i => h i.succ]
  end Ext

  @[simp]
  theorem get_ofBool :
      Vector.get (ofBool b) i = b := by
    simp[ofBool]

  macro "aesop_bitvec" opt:Aesop.tactic_clause* : tactic =>
    `(tactic|
        aesop (options := {terminal := false}) $opt*
    )

  macro "aesop_bitvec?" opt:Aesop.tactic_clause* : tactic =>
    `(tactic|
        aesop? (options := {terminal := false}) $opt*
      )

end Bitvec.Tactic









macro "simp_alive": tactic =>
  `(tactic|
      (
        simp (config := {decide := false}) only [InstCombine.eval, pairMapM,
          tripleMapM, pairMapM, pairBind, bind_assoc, pure, Option.map, Option.bind_eq_some',
          Option.some_bind', Option.bind_eq_bind, Bitvec.Refinement.some_some]
      )
   )

macro "alive_auto": tactic =>
  `(tactic|
      (
        ring_nf 
        try aesop_bitvec
        try simp (config := {decide := false})--placeholder, as `simp` will currently timeout sometimes
      )
   )

