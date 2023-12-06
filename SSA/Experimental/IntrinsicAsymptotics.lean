-- Investigations on asymptotic behavior of representing programs with large explicit contexts

import SSA.Experimental.ErasedContext
import SSA.Experimental.HVector
import Mathlib.Data.List.AList
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Ctxt (Var VarSet)
open Goedel (toType)

set_option autoImplicit false

/-
  # Classes
-/

class OpSignature (Op : Type) (Ty : outParam (Type)) where
  sig : Op → List Ty
  regSig : Op → List (Ctxt Ty × Ty)
  outTy : Op → Ty

class OpDenote (Op Ty : Type) [Goedel Ty] [OpSignature Op Ty] where
  denote : (op : Op) → HVector toType (OpSignature.sig op) →
    HVector (fun t : Ctxt Ty × Ty => toType t.1 → toType t.2) (OpSignature.regSig op) →
    (toType <| OpSignature.outTy op)

/-
  # Datastructures
-/

variable (Op : Type) {Ty : Type} [OpSignature Op Ty]

abbrev RegT (Ty : Type) : Type := List Ty × Ty

instance [Goedel Ty] : Goedel (RegT Ty) where
  toType t := toType t.1 → toType t.2

abbrev RegMVars (Ty : Type) : Type := List (RegT Ty)

mutual

/-- In `Reg Op rg Γ ty`, `Γ` is the context of bound variables in the region.
For now we ban free variables in regions -/
inductive Reg (rg : RegMVars Ty) : (Γ : Ctxt Ty) → (ty : Ty) → Type
  | icom {Γ : Ctxt Ty} {ty : Ty} : ICom rg Γ ty → Reg rg Γ ty
  | mvar {Γ : Ctxt Ty} {ty : Ty} : Ctxt.Var rg (Γ, ty) → Reg rg Γ ty

/-- A very simple intrinsically typed expression. -/
inductive IExpr (rg : RegMVars Ty) : (Γ : Ctxt Ty) → (ty : Ty) → Type :=
  | mk {Γ} {ty} (op : Op)
    (ty_eq : ty = OpSignature.outTy op)
    (args : HVector (Ctxt.Var Γ) <| OpSignature.sig op)
    (regArgs : HVector (fun t : Ctxt Ty × Ty => Reg rg t.1 t.2)
      (OpSignature.regSig op)) : IExpr rg Γ ty

/-- A very simple intrinsically typed program: a sequence of let bindings. -/
inductive ICom (rg : RegMVars Ty) : Ctxt Ty → Ty → Type where
  | ret {Γ : Ctxt Ty} {t : Ty} (v : Γ.Var t) : ICom rg Γ t
  | lete {Γ : Ctxt Ty} {t₁ t₂ : Ty} (e : IExpr rg Γ t₁) (body : ICom rg (Γ.snoc t₁) t₂) :
    ICom rg Γ t₂

end

instance (rg : RegMVars Ty) (Γ : Ctxt Ty) (t : Ty) : DecidableEq (ICom Op rg Γ t) := sorry

/-- `Lets Op rg Γ₁ Γ₂` is a sequence of lets which are well-formed under context `Γ₂` and result in
    context `Γ₁`-/
inductive Lets (rg : RegMVars Ty) (Γ₁ : Ctxt Ty) : Ctxt Ty → Type where
  | nil : Lets rg Γ₁ Γ₁
  | lete {Γ₂ : Ctxt Ty} {t : Ty} (body : Lets rg Γ₁ Γ₂) (e : IExpr Op rg Γ₂ t) : Lets rg Γ₁ (Γ₂.snoc t)

/-
  # Definitions
-/

variable {Op Ty : Type} [OpSignature Op Ty] {rg : RegMVars Ty}

@[elab_as_elim]
def ICom.rec' {motive : (a : Ctxt Ty) → (a_1 : Ty) → ICom Op rg a a_1 → Sort*} :
    (ret : {Γ : Ctxt Ty} → {t : Ty} → (v : Var Γ t) → motive Γ t (ICom.ret v)) →
    (lete : {Γ : Ctxt Ty} →
        {α β : Ty} →
          (e : IExpr Op rg Γ α) →
            (body : ICom Op rg (Ctxt.snoc Γ α) β) →
              motive (Ctxt.snoc Γ α) β body → motive Γ β (ICom.lete e body)) →
      {a : Ctxt Ty} → {a_1 : Ty} → (t : ICom Op rg a a_1) → motive a a_1 t
  | hret, _, _, _, ICom.ret v => hret v
  | hret, hlete, _, _, ICom.lete e body => hlete e body (ICom.rec' hret hlete body)

def IExpr.op {Γ : Ctxt Ty} {ty : Ty} (e : IExpr Op rg Γ ty) : Op :=
  IExpr.casesOn e (fun op _ _ _ => op)

theorem IExpr.ty_eq {Γ : Ctxt Ty} {ty : Ty} (e : IExpr Op rg Γ ty) :
    ty = OpSignature.outTy e.op :=
  IExpr.casesOn e (fun _ ty_eq _ _ => ty_eq)

def IExpr.args {Γ : Ctxt Ty} {ty : Ty} (e : IExpr Op rg Γ ty) :
    HVector (Var Γ) (OpSignature.sig e.op) :=
  IExpr.casesOn e (fun _ _ args _ => args)

def IExpr.regArgs {Γ : Ctxt Ty} {ty : Ty} (e : IExpr Op rg Γ ty) :
    HVector (fun t : Ctxt Ty × Ty => Reg Op rg t.1 t.2) (OpSignature.regSig e.op) :=
  IExpr.casesOn e (fun _ _ _ regArgs => regArgs)

/-! Projection equations for `IExpr` -/
@[simp]
theorem IExpr.op_mk {Γ : Ctxt Ty} {ty : Ty} (op : Op) (ty_eq : ty = OpSignature.outTy op)
    (args : HVector (Var Γ) (OpSignature.sig op)) (regArgs):
    (IExpr.mk (rg := rg) op ty_eq args regArgs).op = op := rfl

@[simp]
theorem IExpr.args_mk {Γ : Ctxt Ty} {ty : Ty} (op : Op) (ty_eq : ty = OpSignature.outTy op)
    (args : HVector (Var Γ) (OpSignature.sig op)) (regArgs) :
    (IExpr.mk (rg := rg) op ty_eq args regArgs).args = args := rfl

@[simp]
theorem IExpr.regArgs_mk {Γ : Ctxt Ty} {ty : Ty} (op : Op) (ty_eq : ty = OpSignature.outTy op)
    (args : HVector (Var Γ) (OpSignature.sig op)) (regArgs) :
    (IExpr.mk (rg := rg) op ty_eq args regArgs).regArgs = regArgs := rfl

-- TODO: the following `variable` probably means we include these assumptions also in definitions
-- that might not strictly need them, we can look into making this more fine-grained
variable [Goedel Ty] [OpDenote Op Ty] [DecidableEq Ty]

mutual

def Reg.denote : {Γ : Ctxt Ty} → {ty : Ty} →
    (r : Reg Op rg Γ ty) → (mv : toType rg) → (Γ.Valuation → toType ty)
  | _, _, Reg.icom com, mv => com.denote mv
  | _, _, Reg.mvar i, mv => mv i

def HVector.denoteReg : {l : List (RegT Ty)} →
    (T : HVector (fun t => Reg Op rg t.1 t.2) l) →
    (mv : toType rg) → HVector toType l
  | _, .nil, _ => HVector.nil
  | _, .cons v vs, mv => HVector.cons (v.denote mv) (HVector.denoteReg vs mv)

def IExpr.denote {Γ : Ctxt Ty} : {ty : Ty} →
    (e : IExpr Op rg Γ ty) → (mv : toType rg) →
    (Γv : Γ.Valuation) → toType ty
  | _, ⟨op, Eq.refl _, args, regArgs⟩, mv, Γv =>
    OpDenote.denote op (args.map (fun _ v => Γv v)) <| regArgs.denoteReg mv

def ICom.denote {Γ : Ctxt Ty} {ty : Ty} : ICom Op rg Γ ty → (mv : toType rg) →
    (Γv : Γ.Valuation) → (toType ty)
  | .ret e, _, Γv => Γv e
  | .lete e body, mv, Γv => body.denote mv (Γv.snoc (e.denote mv Γv))

end
decreasing_by sorry
-- termination_by
--   Reg.denote _ _ _ r _ => sizeOf r
--   HVector.denote _  e _ => sizeOf e
--   IExpr.denote _ e _ _ => sizeOf e
--   ICom.denote _ e _ _ => sizeOf e

/-
https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Equational.20Lemmas
Recall that `simp` lazily generates equation lemmas.
Moreover, recall that `simp only` **does not** generate equation lemmas.
*but* if equation lemmas are present, then `simp only` *uses* the equation lemmas.

Hence, we build the equation lemmas by invoking the correct Lean meta magic,
so that `simp only` (which we use in `simp_peephole` can find them!)

This allows `simp only [HVector.denote]` to correctly simplify `HVector.denote`
args, since there now are equation lemmas for it.
-/
#eval Lean.Meta.getEqnsFor? ``HVector.denoteReg
#eval Lean.Meta.getEqnsFor? ``IExpr.denote
#eval Lean.Meta.getEqnsFor? ``ICom.denote


def Lets.denote {Γ₁ Γ₂ : Ctxt Ty} : Lets Op rg Γ₁ Γ₂ → toType rg → Γ₁.Valuation → Γ₂.Valuation
  | .nil => fun _ => id
  | .lete e body => fun mv ll t v => by
    cases v using Ctxt.Var.casesOn with
    | last =>
      apply body.denote mv
      apply e.denote mv
      exact ll
    | toSnoc v =>
      exact e.denote mv ll v

def IExpr.changeVars {Γ Γ' : Ctxt Ty} (varsMap : Γ.Hom Γ') :
    {ty : Ty} → (e : IExpr Op rg Γ ty) → IExpr Op rg Γ' ty
  | _, ⟨op, Eq.refl _, args, regArgs⟩ => ⟨op, rfl, args.map varsMap, regArgs⟩

@[simp]
theorem IExpr.denote_changeVars {ty : Ty} {Γ Γ' : Ctxt Ty}
    (varsMap : Γ.Hom Γ')
    (e : IExpr Op rg Γ ty)
    (mv : toType rg)
    (Γ'v : Γ'.Valuation) :
    (e.changeVars varsMap).denote mv Γ'v =
    e.denote mv (fun t v => Γ'v (varsMap v)) := by
  rcases e with ⟨_, rfl, _⟩
  simp [IExpr.denote, IExpr.changeVars, HVector.map_map]

def ICom.changeVars {Γ Γ' : Ctxt Ty} {ty : Ty} (varsMap : Γ.Hom Γ') :
    ICom Op rg Γ ty → ICom Op rg Γ' ty
  | .ret e => .ret (varsMap e)
  | .lete e body => .lete (e.changeVars varsMap)
      (body.changeVars (fun t v => varsMap.snocMap v))

@[simp]
theorem ICom.denote_changeVars {Γ Γ' : Ctxt Ty} {ty : Ty}
    (varsMap : Γ.Hom Γ') (c : ICom Op rg Γ ty)
    (mv : toType rg)
    (Γ'v : Γ'.Valuation) :
    (c.changeVars varsMap).denote mv Γ'v =
    c.denote mv (fun t v => Γ'v (varsMap v)) := by
  induction c using ICom.rec' generalizing Γ'v Γ' with
  | ret x => simp [ICom.denote, ICom.changeVars, *]
  | lete _ _ ih =>
    rw [changeVars, denote, ih]
    simp only [Goedel.toType.snoc, Ctxt.Hom.snocMap, IExpr.denote_changeVars, denote]
    congr
    funext t v
    cases v using Ctxt.Var.casesOn <;> simp


variable (Op : _) {Ty : _} [OpSignature Op Ty] (rg : RegMVars Ty) in
/-- The result returned by `addProgramToLets` -/
structure addProgramToLets.Result (Γ_in Γ_out : Ctxt Ty) (ty : Ty) where
  /-- The new out context -/
  {Γ_out_new : Ctxt Ty}
  /-- The new `lets`, with the program added to it -/
  lets : Lets Op rg Γ_in Γ_out_new
  /-- The difference between the old out context and the new out context
      This induces a context mapping from `Γ_out` to `Γ_out_new` -/
  diff : Ctxt.Diff Γ_out Γ_out_new
  /-- The variable in the new `lets` that represent the return value of the added program -/
  var : Γ_out_new.Var ty

/--
  Add a program to a list of `Lets`, returning
  * the new lets
  * a map from variables of the out context of the old lets to the out context of the new lets
  * a variable in the new out context, which is semantically equivalent to the return variable of
    the added program
-/
def addProgramToLets {Γ_in Γ_out Δ : Ctxt Ty} {ty : Ty}
    (lets : Lets Op rg Γ_in Γ_out) (varsMap : Δ.Hom Γ_out) : ICom Op rg Δ ty →
    addProgramToLets.Result Op rg Γ_in Γ_out ty
  | .ret v => ⟨lets, .zero _, varsMap v⟩
  | .lete (t₁:=t₁) e body =>
      let lets := Lets.lete lets (e.changeVars varsMap)
      let ⟨lets', diff, v'⟩ := addProgramToLets lets (varsMap.snocMap) body
      ⟨lets', diff.unSnoc, v'⟩

theorem denote_addProgramToLets_lets {Γ_in Γ_out Δ : Ctxt Ty} {ty : Ty} (mv : toType rg)
    (lets : Lets Op rg Γ_in Γ_out) {map} {com : ICom Op rg Δ ty}
    (ll : Γ_in.Valuation) ⦃t⦄ (var : Γ_out.Var t) :
    (addProgramToLets lets map com).lets.denote mv ll ((addProgramToLets lets map com).diff.toHom var)
    = lets.denote mv ll var := by
  induction com using ICom.rec' generalizing lets Γ_out
  next =>
    rfl
  next e body ih =>
    -- Was just `simp [addProgramToLets, ih, Lets.denote]
    rw [addProgramToLets]
    simp [ih, Lets.denote]

theorem denote_addProgramToLets_var
    {Γ_in Γ_out Δ : Ctxt Ty} {t : Ty} {mv : toType rg}
    {lets : Lets Op rg Γ_in Γ_out} {map} {com : ICom Op rg Δ t} :
    ∀ (ll : Γ_in.Valuation),
      (addProgramToLets lets map com).lets.denote mv ll (addProgramToLets lets map com).var
      = com.denote mv (fun _ v => lets.denote mv ll <| map v) := by
  intro ll
  induction com using ICom.rec' generalizing lets Γ_out
  next =>
    rfl
  next e body ih =>
    -- Was just `simp only [addProgramToLets, ih, ICom.denote]`
    rw [addProgramToLets]
    simp only [ih, ICom.denote]
    congr
    funext t v
    cases v using Ctxt.Var.casesOn
    . rfl
    . simp [Lets.denote]; rfl

/-- Add some `Lets` to the beginning of a program -/
def addLetsAtTop {Γ₁ Γ₂ : Ctxt Ty} {ty : Ty} : (lets : Lets Op rg Γ₁ Γ₂) →
    (inputProg : ICom Op rg Γ₂ ty) → ICom Op rg Γ₁ ty
  | Lets.nil, inputProg => inputProg
  | Lets.lete body e, inputProg =>
    addLetsAtTop body (.lete e inputProg)

theorem denote_addLetsAtTop {Γ₁ Γ₂ : Ctxt Ty} {ty : Ty} (mv : toType rg) :
    (lets : Lets Op rg Γ₁ Γ₂) → (inputProg : ICom Op rg Γ₂ ty) →
    (addLetsAtTop lets inputProg).denote mv =
      inputProg.denote mv ∘ lets.denote mv
  | Lets.nil, inputProg => rfl
  | Lets.lete body e, inputProg => by
    rw [addLetsAtTop, denote_addLetsAtTop mv body]
    funext
    simp only [ICom.denote, Goedel.toType.snoc, Function.comp_apply, Lets.denote,
      eq_rec_constant]
    congr
    funext t v
    cases v using Ctxt.Var.casesOn <;> simp

/-- `addProgramInMiddle v map lets rhs inputProg` appends the programs
`lets`, `rhs` and `inputProg`, while reassigning `v`, a free variable in
`inputProg`, to the output of `rhs`. It also assigns all free variables
in `rhs` to variables available at the end of `lets` using `map`. -/
def addProgramInMiddle [DecidableEq Ty] {Γ₁ Γ₂ Γ₃ : Ctxt Ty}
    {t₁ t₂ : Ty} (v : Γ₂.Var t₁)
    (map : Γ₃.Hom Γ₂)
    (lets : Lets Op rg Γ₁ Γ₂) (rhs : ICom Op rg Γ₃ t₁)
    (inputProg : ICom Op rg Γ₂ t₂) : ICom Op rg Γ₁ t₂ :=
  let r := addProgramToLets lets map rhs
  addLetsAtTop r.lets <| inputProg.changeVars (r.diff.toHom.with v r.var)

theorem denote_addProgramInMiddle {Γ₁ Γ₂ Γ₃ : Ctxt Ty} (mv : toType rg)
    {t₁ t₂ : Ty}
    (v : Γ₂.Var t₁) (s : Γ₁.Valuation)
    (map : Γ₃.Hom Γ₂)
    (lets : Lets Op rg Γ₁ Γ₂) (rhs : ICom Op rg Γ₃ t₁)
    (inputProg : ICom Op rg Γ₂ t₂) :
    (addProgramInMiddle v map lets rhs inputProg).denote mv s =
      inputProg.denote mv (fun t' v' =>
        let s' := lets.denote mv s
        if h : ∃ h : t₁ = t', h ▸ v = v'
        then h.fst ▸ rhs.denote mv (fun t' v' => s' (map v'))
        else s' v') := by
  simp only [addProgramInMiddle, Ctxt.Hom.with, denote_addLetsAtTop, Function.comp_apply,
              ICom.denote_changeVars]
  congr
  funext t' v'
  split_ifs
  next h =>
    rcases h with ⟨⟨⟩, ⟨⟩⟩
    simp [denote_addProgramToLets_var]
  next h₁ h₂ =>
    rcases h₁ with ⟨⟨⟩, ⟨⟩⟩
    simp at h₂
  next h₁ h₂ =>
    rcases h₂ with ⟨⟨⟩, ⟨⟩⟩
    simp at h₁
  next =>
    apply denote_addProgramToLets_lets

structure FlatICom (Op : _) {Ty : _} [OpSignature Op Ty] (rg : RegMVars Ty)
    (Γ : Ctxt Ty) (t : Ty) where
  {Γ_out : Ctxt Ty}
  /-- The let bindings of the original program -/
  lets : Lets Op rg Γ Γ_out
  /-- The return variable -/
  ret : Γ_out.Var t

def ICom.toLets {Γ : Ctxt Ty} {t : Ty} : ICom Op rg Γ t → FlatICom Op rg Γ t :=
  go .nil
where
  go {Γ_out} (lets : Lets Op rg Γ Γ_out) : ICom Op rg Γ_out t → FlatICom Op rg Γ t
    | .ret v => ⟨lets, v⟩
    | .lete e body => go (lets.lete e) body

@[simp]
theorem ICom.denote_toLets_go {Γ_in Γ_out : Ctxt Ty} {t : Ty} (mv : toType rg)
    (lets : Lets Op rg Γ_in Γ_out) (com : ICom Op rg Γ_out t) (s : Γ_in.Valuation) :
    (toLets.go lets com).lets.denote mv s (toLets.go lets com).ret =
      com.denote mv (lets.denote mv s) := by
  induction com using ICom.rec'
  . rfl
  next ih =>
    -- Was just `simp [toLets.go, denote, ih]`
    rw [toLets.go]
    simp [denote, ih]
    congr
    funext _ v
    cases v using Ctxt.Var.casesOn <;> simp[Lets.denote]

@[simp]
theorem ICom.denote_toLets {Γ : Ctxt Ty} {t : Ty}
    (mv : toType rg) (com : ICom Op rg Γ t) (s : Γ.Valuation) :
    com.toLets.lets.denote mv s com.toLets.ret = com.denote mv s :=
  denote_toLets_go ..

/-- Get the `IExpr` that a var `v` is assigned to in a sequence of `Lets`,
    without adjusting variables
-/
def Lets.getIExprAux {Γ₁ Γ₂ : Ctxt Ty} {t : Ty} : Lets Op rg Γ₁ Γ₂ → Γ₂.Var t →
    Option ((Δ : Ctxt Ty) × IExpr Op rg Δ t)
  | .nil, _ => none
  | .lete lets e, v => by
    cases v using Ctxt.Var.casesOn with
      | toSnoc v => exact (Lets.getIExprAux lets v)
      | last => exact some ⟨_, e⟩

/-- If `getIExprAux` succeeds,
    then the orignal context `Γ₁` is a prefix of the local context `Δ`, and
    their difference is exactly the value of the requested variable index plus 1
-/
def Lets.getIExprAuxDiff {Γ₁ Γ₂ Δ : Ctxt Ty} {t : Ty}
    {lets : Lets Op rg Γ₁ Γ₂} {e : IExpr Op rg Δ t} {v : Γ₂.Var t}
    (h : getIExprAux lets v = some ⟨Δ, e⟩) :
    Δ.Diff Γ₂ :=
  ⟨v.val + 1, by
    intro i t
    induction lets
    next =>
      simp only [getIExprAux] at h
    next lets e ih =>
      simp only [getIExprAux, eq_rec_constant] at h
      cases v using Ctxt.Var.casesOn <;> simp at h
      . intro h'
        simp [Ctxt.get?]
        simp[←ih h h', Ctxt.snoc, Ctxt.Var.toSnoc, List.get?]
      . rcases h with ⟨⟨⟩, ⟨⟩⟩
        simp[Ctxt.snoc, List.get?, Ctxt.Var.last]
  ⟩

theorem Lets.denote_getIExprAux {Γ₁ Γ₂ Δ : Ctxt Ty} {t : Ty} {mv : toType rg}
    {lets : Lets Op rg Γ₁ Γ₂} {v : Γ₂.Var t} {e : IExpr Op rg Δ t}
    (he : lets.getIExprAux v = some ⟨Δ, e⟩)
    (s : Γ₁.Valuation) :
    (e.changeVars (getIExprAuxDiff he).toHom).denote mv
      (lets.denote mv s) = (lets.denote mv s) v := by
  rw [getIExprAuxDiff]
  induction lets
  next => simp [getIExprAux] at he
  next ih =>
    simp [Ctxt.Diff.toHom_succ <| getIExprAuxDiff.proof_1 he]
    cases v using Ctxt.Var.casesOn with
    | toSnoc v =>
      simp only [getIExprAux, eq_rec_constant, Ctxt.Var.casesOn_toSnoc, Option.mem_def,
        Option.map_eq_some'] at he
      simp [denote, ←ih he]
    | last =>
      simp only [getIExprAux, eq_rec_constant, Ctxt.Var.casesOn_last,
        Option.mem_def, Option.some.injEq] at he
      rcases he with ⟨⟨⟩, ⟨⟩⟩
      simp [denote]


/-- Get the `IExpr` that a var `v` is assigned to in a sequence of `Lets`.
The variables are adjusted so that they are variables in the output context of a lets,
not the local context where the variable appears. -/
def Lets.getIExpr {Γ₁ Γ₂ : Ctxt Ty} (lets : Lets Op rg Γ₁ Γ₂) {t : Ty} (v : Γ₂.Var t) :
    Option (IExpr Op rg Γ₂ t) :=
  match h : getIExprAux lets v with
  | none => none
  | some r => r.snd.changeVars (getIExprAuxDiff h).toHom

theorem Lets.denote_getIExpr {Γ₁ Γ₂ : Ctxt Ty} (mv : toType rg) :
    {lets : Lets Op rg Γ₁ Γ₂} → {t : Ty} →
    {v : Γ₂.Var t} → {e : IExpr Op rg Γ₂ t} → (he : lets.getIExpr v = some e) → (s : Γ₁.Valuation) →
    e.denote mv (lets.denote mv s) = (lets.denote mv s) v := by
  intros lets _ v e he s
  simp [getIExpr] at he
  split at he
  . contradiction
  . rw[←Option.some_inj.mp he, denote_getIExprAux]



/-
  ## Matching
-/

abbrev Mapping (Γ Δ : Ctxt Ty) : Type :=
  @AList (Σ t, Γ.Var t) (fun x => Δ.Var x.1)


variable (Op : _) {Ty : _} [OpSignature Op Ty] (rg : RegMVars Ty) in
abbrev RegMapping : Type :=
  @AList (Σ t, Ctxt.Var (show Ctxt (RegT Ty) from rg) t)
    (fun t => ICom Op [] t.1.1 t.1.2)

def HVector.toVarSet {Γ : Ctxt Ty} : {l : List Ty} → (T : HVector (Ctxt.Var Γ) l) → Γ.VarSet
  | [], .nil => ∅
  | _::_, .cons v vs => insert ⟨_, v⟩ vs.toVarSet

def HVector.vars {Γ : Ctxt Ty} {l : List Ty}
    (T : HVector (Ctxt.Var Γ) l) : VarSet Γ :=
  T.foldl (fun _ s a => insert ⟨_, a⟩ s) ∅

@[simp]
theorem HVector.vars_nil {Γ : Ctxt Ty} :
    (HVector.nil : HVector (Ctxt.Var Γ) ([] : List Ty)).vars = ∅ := by
  simp [HVector.vars, HVector.foldl]

@[simp]
theorem HVector.vars_cons {Γ : Ctxt Ty} {t  : Ty} {l : List Ty}
    (v : Ctxt.Var Γ t) (T : HVector (Ctxt.Var Γ) l) :
    (HVector.cons v T).vars = insert ⟨_, v⟩ T.vars := by
  rw [HVector.vars, HVector.vars]
  generalize hs : (∅ : VarSet Γ) = s
  clear hs
  induction T generalizing s t v with
  | nil => simp [foldl]
  | cons v' T ih =>
    rename_i t2 _
    conv_rhs => rw [foldl]
    rw [← ih]
    rw [foldl,foldl, foldl]
    congr 1
    simp [Finset.ext_iff, or_comm, or_assoc]

/-- The free variables of `lets` that are (transitively) referred to by some variable `v` -/
def Lets.vars {Γ_in Γ_out : Ctxt Ty} {t : Ty} :
    Lets Op rg Γ_in Γ_out → Γ_out.Var t → Γ_in.VarSet
  | .nil, v => VarSet.ofVar v
  | .lete lets e, v => by
      cases v using Ctxt.Var.casesOn with
      | toSnoc v => exact lets.vars v
      -- this is wrong
      | last => exact (e.args.vars).biUnion (fun v => lets.vars v.2)

theorem HVector.map_eq_of_eq_on_vars
    {Γ : Ctxt Ty} {l : List Ty} {A : Ty → Type*}
    {T : HVector (Ctxt.Var Γ) l}
    {s₁ s₂ : ∀ (t), Γ.Var t → A t}
    (h : ∀ v, v ∈ T.vars → s₁ _ v.2 = s₂ _ v.2) :
    T.map s₁ = T.map s₂ := by
  induction T with
  | nil => simp [HVector.map]
  | cons v T ih =>
    rw [HVector.map, HVector.map, ih]
    · congr
      apply h ⟨_, v⟩
      simp
    · intro v hv
      apply h
      simp_all

theorem Lets.denote_eq_of_eq_on_vars
    {Γ_in Γ_out : Ctxt Ty} {t : Ty} {mv : toType rg}
    (lets : Lets Op rg Γ_in Γ_out)
    (v : Γ_out.Var t)
    {s₁ s₂ : Γ_in.Valuation}
    (h : ∀ w, w ∈ lets.vars v → s₁ w.2 = s₂ w.2) :
    lets.denote mv s₁ v = lets.denote mv s₂ v := by
  induction lets generalizing t
  next =>
    simp [vars] at h
    simp [denote, h]
  next lets e ih =>
    cases v using Ctxt.Var.casesOn
    . simp [vars] at h
      simp [denote]
      apply ih
      simpa
    . rcases e with ⟨op, rfl, args⟩
      simp [denote, IExpr.denote]
      congr 1
      apply HVector.map_eq_of_eq_on_vars
      intro v h'
      apply ih
      intro v' hv'
      apply h
      rw [vars, Var.casesOn_last]
      simp
      use v.1, v.2

def ICom.vars {Γ : Ctxt Ty} {t : Ty} : ICom Op rg Γ t → Γ.VarSet :=
  fun com => com.toLets.lets.vars com.toLets.ret

variable [DecidableEq Op]

/-
We need to generalize this. Sometimes we need to unify a region with

-/


/--
  Given two sequences of lets, `lets` and `matchLets`,
  and variables that indicate an expression, of the same type, in each sequence,
  attempt to assign free variables in `matchLets` to variables (free or bound) in `lets`, such that
  the original two variables are semantically equivalent.
  If this succeeds, return the mapping.
-/

def matchVar {rg : RegMVars Ty}
    {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty} {t : Ty}
    (lets : Lets Op [] Γ_in Γ_out) (v : Γ_out.Var t) :
    (matchLets : Lets Op rg Δ_in Δ_out) →
    (w : Δ_out.Var t) →
    (rma : RegMapping Op rg) →
    (ma : Mapping Δ_in Γ_out := ∅) →
    Option (RegMapping Op rg × Mapping Δ_in Γ_out)
  | .lete matchLets _, ⟨w+1, h⟩, rma, ma => -- w† = Var.toSnoc w
      let w := ⟨w, by simp_all[Ctxt.snoc]⟩
      matchVar lets v matchLets w rma ma
  | @Lets.lete _ _ _ _ _ Δ_out _ matchLets matchExpr, ⟨0, _⟩, rma, ma => do -- w† = Var.last
      let ie ← lets.getIExpr v
      if hs : ie.op = matchExpr.op
      then
        let rec matchArg : ∀ {l : List Ty}
            (_Tₗ : HVector (Var Γ_out) l) (_Tᵣ :  HVector (Var Δ_out) l),
            RegMapping Op rg → Mapping Δ_in Γ_out →
            Option (RegMapping Op rg × Mapping Δ_in Γ_out)
          | _, .nil, .nil, rma, ma => some (rma, ma)
          | t::l, .cons vₗ vsₗ, .cons vᵣ vsᵣ, rma, ma => do
              let ⟨rma, ma⟩ ← matchVar lets vₗ matchLets vᵣ rma ma
              matchArg vsₗ vsᵣ rma ma
        let rec matchReg : ∀ {l : List (Ctxt Ty × Ty)}
            (_Tₗ : HVector (fun t : Ctxt Ty × Ty => Reg Op [] t.1 t.2) l)
            (_Tᵣ : HVector (fun t : Ctxt Ty × Ty => Reg Op rg t.1 t.2) l),
            RegMapping Op rg → Mapping Δ_in Γ_out →
            Option (RegMapping Op rg × Mapping Δ_in Γ_out)
          | _, .nil, .nil, rma, ma => some (rma, ma)
          | t::l, .cons (Reg.icom comₗ) rsₗ, .cons (Reg.mvar i) rsᵣ, rma, ma =>
            match rma.lookup ⟨t, i⟩ with
            | none => matchReg rsₗ rsᵣ (AList.insert ⟨_, i⟩ comₗ rma) ma
            | some comᵣ =>
              by exact if comₗ = comᵣ
              then matchReg rsₗ rsᵣ rma ma
              else none
          | t::l, .cons (Reg.icom comₗ) rsₗ, .cons (Reg.icom comᵣ) rsᵣ, rma, ma => do
              let x ← matchVar comₗ.toLets.2 comₗ.toLets.3
                               comᵣ.toLets.2 comᵣ.toLets.3 rma ∅
              matchReg rsₗ rsᵣ x.1 ma
        let ⟨rma, ma⟩ ← matchArg ie.args (hs ▸ matchExpr.args) rma ma
        matchReg ie.regArgs (hs ▸ matchExpr.regArgs) rma ma
      else none
  | .nil, w, rma, ma => -- The match expression is just a free (meta) variable
      match ma.lookup ⟨_, w⟩ with
      | some v₂ =>
        by
          exact if v = v₂
            then some (rma, ma)
            else none
      | none => some (rma, AList.insert ⟨_, w⟩ v ma)
  decreasing_by matchVar => sorry

open AList

/-- For mathlib -/
theorem _root_.AList.mem_of_mem_entries {α : Type _} {β : α → Type _} {s : AList β}
    {k : α} {v : β k} : ⟨k, v⟩ ∈ s.entries → k ∈ s := by
  intro h
  rcases s with ⟨entries, nd⟩
  simp [(· ∈ ·), keys] at h ⊢
  clear nd
  induction h
  next    => apply List.Mem.head
  next ih => apply List.Mem.tail _ ih

theorem _root_.AList.mem_entries_of_mem {α : Type _} {β : α → Type _} {s : AList β} {k : α} :
    k ∈ s → ∃ v, ⟨k, v⟩ ∈ s.entries := by
  intro h
  rcases s with ⟨entries, nd⟩
  simp [(· ∈ ·), keys, List.keys] at h ⊢
  clear nd;
  induction entries
  next    => contradiction
  next hd tl ih =>
    cases h
    next =>
      use hd.snd
      apply List.Mem.head
    next h =>
      rcases ih h with ⟨v, ih⟩
      exact ⟨v, .tail _ ih⟩

set_option maxHeartbeats 1000000 in
mutual

/-- The output mapping of `matchVar` extends the input mapping when it succeeds. -/
theorem subset_entries_matchVar {rg : RegMVars Ty}
    {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty} {t : Ty}
    {rma : RegMapping Op rg} {ma : Mapping Δ_in Γ_out}
    {lets : Lets Op [] Γ_in Γ_out} {v : Γ_out.Var t} :
    {matchLets : Lets Op rg Δ_in Δ_out} → {w : Δ_out.Var t} →
    {rVarMap : RegMapping Op rg} → {varMap : Mapping Δ_in Γ_out} →
    (hvarMap : (rVarMap, varMap) ∈ matchVar lets v matchLets w rma ma) →
    rma.entries ⊆ rVarMap.entries ∧ ma.entries ⊆ varMap.entries
  | .nil, w => by
    simp [matchVar]
    intros h
    split at h
    . split_ifs at h
      . simp_all
    . simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨List.Subset.refl _, ?_⟩
      rintro ⟨x, y⟩ hxy
      simp only [List.subset_def, ← AList.mem_lookup_iff] at *
      by_cases hx : x = ⟨t, w⟩
      . subst x; simp_all
      . rwa [AList.lookup_insert_ne hx]
  | .lete matchLets _, ⟨w+1, h⟩ => by
    simp [matchVar]
    apply subset_entries_matchVar
  | .lete matchLets matchExpr, ⟨0, _⟩ => by
    simp [matchVar, Bind.bind, Option.bind]
    intro h
    split at h
    · simp at h
    · rename_i e he
      rcases e with ⟨op, rfl, args⟩
      dsimp at h
      split_ifs at h with hop
      · rcases hop with ⟨rfl, hop⟩
        dsimp at h
        split at h
        · simp at h
        · rename_i _ ma₁ hma₁
          dsimp at h
          have h₁ := subset_entries_matchVar_matchArg hma₁
          have h₂ := subset_entries_matchVar_matchReg h
          exact ⟨_root_.trans h₁.1 h₂.1, _root_.trans h₁.2 h₂.2⟩

theorem subset_entries_matchVar_matchArg
    {rg : RegMVars Ty} {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty}
    {lets : Lets Op [] Γ_in Γ_out}
    {matchLets : Lets Op rg Δ_in Δ_out}
    {rma : RegMapping Op rg} :
    {l : List Ty} →
    {Tₗ : HVector (Var Γ_out) l} →
    {Tᵣ : HVector (Var Δ_out) l} →
    {ma : Mapping Δ_in Γ_out} →
    {rVarMap : RegMapping Op rg} →
    {varMap : Mapping Δ_in Γ_out} →
    (hvarMap : (rVarMap, varMap) ∈
      matchVar.matchArg lets Δ_out matchLets Tₗ Tᵣ rma ma) →
    rma.entries ⊆ rVarMap.entries ∧ ma.entries ⊆ varMap.entries
  | _, .nil, .nil, ma => by
    simp (config := { contextual := true }) [matchVar.matchArg]
  | t::l, .cons vₗ vsₗ, .cons vᵣ vsᵣ, ma => by
    intro h
    simp [matchVar.matchArg, Bind.bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i _ ma₁ hma₁
      dsimp at h
      have h₁ := subset_entries_matchVar hma₁
      have h₂ := subset_entries_matchVar_matchArg h
      exact ⟨_root_.trans h₁.1 h₂.1, _root_.trans h₁.2 h₂.2⟩

theorem subset_entries_matchVar_matchReg {rg : RegMVars Ty}
    {Γ_out Δ_in : Ctxt Ty} : {l : List (Ctxt Ty × Ty)} →
    {Tₗ : HVector (fun t => Reg Op [] t.fst t.snd) l} →
    {Tᵣ : HVector (fun t => Reg Op rg t.fst t.snd) l} →
    {rma : RegMapping Op rg} →
    {ma : Mapping Δ_in Γ_out} →
    {rVarMap : RegMapping Op rg} → {varMap : Mapping Δ_in Γ_out} →
    (hvarMap : (rVarMap, varMap) ∈ matchVar.matchReg Tₗ Tᵣ rma ma) →
    rma.entries ⊆ rVarMap.entries ∧ ma.entries ⊆ varMap.entries
  | [], .nil, .nil, rma, ma => by
    simp (config := { contextual := true }) [matchVar.matchReg]
  | t::l, .cons (Reg.icom comₗ) rsₗ, .cons (Reg.mvar i) rsᵣ, rma, ma => by
    intro h
    simp [matchVar.matchReg] at h
    split at h
    · rename_i hnone
      have h' := subset_entries_matchVar_matchReg h
      refine ⟨_root_.trans ?_ h'.1, h'.2⟩
      rintro ⟨x, y⟩ hxy
      simp only [List.subset_def, ← AList.mem_lookup_iff] at *
      by_cases hx : x = ⟨t, i⟩
      . subst x; simp_all
      . erw [AList.lookup_insert_ne hx]
        assumption
    · split_ifs at h with hc
      · exact subset_entries_matchVar_matchReg h
  | t::l, .cons (Reg.icom comₗ) rsₗ, .cons (Reg.icom comᵣ) rsᵣ, rma, ma => by
    intro h
    simp only [matchVar.matchReg, bind, Option.mem_def, Option.bind_eq_some, Prod.exists] at h
    rcases h with ⟨x, y, h, h'⟩
    have h₁ := subset_entries_matchVar h
    have h₂ := subset_entries_matchVar_matchReg h'
    exact ⟨_root_.trans h₁.1 h₂.1, h₂.2⟩

end
decreasing_by subset_entries_matchVar => sorry


-- TODO: this assumption is too strong, we also want to be able to model non-inhabited types
variable [∀ (t : Ty), Inhabited (toType t)]

set_option maxHeartbeats 0 in
mutual

theorem denote_matchVar_of_subset {rg : RegMVars Ty}
    {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty} {t : Ty}
    {rma : RegMapping Op rg} {ma : Mapping Δ_in Γ_out}
    {lets : Lets Op [] Γ_in Γ_out} {v : Γ_out.Var t} :
    {matchLets : Lets Op rg Δ_in Δ_out} → {w : Δ_out.Var t} →
    {rVarMap₁ rVarMap₂ : RegMapping Op rg} → {varMap₁ varMap₂ : Mapping Δ_in Γ_out} →
    (hvarMap : (rVarMap₁, varMap₁) ∈ matchVar lets v matchLets w rma ma) →
    (h_sub_r : rVarMap₁.entries ⊆ rVarMap₂.entries) →
    (h_sub : varMap₁.entries ⊆ varMap₂.entries) →
    {s : Γ_in.Valuation} →
      matchLets.denote
        (fun t' v' => by
          match rVarMap₂.lookup ⟨_, v'⟩ with
          | some i =>
            exact i.denote (fun _ => Ctxt.Var.emptyElim)
          | none => exact fun _ => default)
        (fun t' v' => by
          match varMap₂.lookup ⟨_, v'⟩ with
          | some v' =>
            exact lets.denote (fun _ => Ctxt.Var.emptyElim) s v'
          | none => exact default
        ) w =
      lets.denote (fun _ => Ctxt.Var.emptyElim) s v
  | .nil, w => by
    intros hvarMap h_sub_r h_sub s
    simp [Lets.denote, matchVar] at *
    split at hvarMap
    next x v₂ heq =>
      split_ifs at hvarMap
      next v_eq_v₂ =>
        subst v_eq_v₂
        cases hvarMap
        rw [mem_lookup_iff.mpr ?_]
        apply h_sub
        apply mem_lookup_iff.mp
        exact heq
    next =>
      rw [mem_lookup_iff.mpr]
      cases hvarMap
      apply h_sub
      simp
  | .lete matchLets _, ⟨w+1, h⟩ => by
    simp only [matchVar]
    intros hvarMap h_sub h_sub_r s
    apply denote_matchVar_of_subset (matchLets := matchLets) hvarMap h_sub h_sub_r
  | .lete matchLets matchExpr, ⟨0, h_w⟩ => by
    rename_i t'
    have : t = t' := by simp[List.get?] at h_w; apply h_w.symm
    subst this
    simp only [matchVar, bind, Option.bind, Option.mem_def]
    intros hvarMap h_sub_r h_sub s
    split at hvarMap
    · simp_all
    · rename_i e he
      rcases e with ⟨op₁, rfl, args₁, regArgs₁⟩
      rcases matchExpr with ⟨op₂, h, args₂, regArgs₂⟩
      dsimp at hvarMap
      split_ifs at hvarMap with hop
      · rcases hop with ⟨rfl, hop⟩
        simp only [Lets.denote, Ctxt.get?, Var.zero_eq_last, eq_rec_constant,
          IExpr.denote, Var.casesOn_last]
        rw [← Lets.denote_getIExpr (fun x => Var.emptyElim) he]
        clear he
        simp only [IExpr.denote]
        split at hvarMap
        · simp_all
        · dsimp at hvarMap
          congr 1
          · rename_i x hvarMap'
            dsimp at hvarMap'
            refine denote_matchVar_matchArg hvarMap' ?_ ?_
            · exact (subset_entries_matchVar_matchReg hvarMap).1.trans h_sub_r
            · exact (subset_entries_matchVar_matchReg hvarMap).2.trans h_sub
          · rename_i x hvarMap'
            rcases x with ⟨x, y⟩
            admit

theorem denote_matchVar_matchArg
    {rg : RegMVars Ty} {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty}
    {lets : Lets Op [] Γ_in Γ_out}
    {matchLets : Lets Op rg Δ_in Δ_out} :
    {l : List Ty} →
    {Tₗ : HVector (Var Γ_out) l} →
    {Tᵣ : HVector (Var Δ_out) l} →
    {rma : RegMapping Op rg} →
    {ma : Mapping Δ_in Γ_out} →
    {rVarMap₁ rVarMap₂ : RegMapping Op rg} →
    {varMap₁ varMap₂ : Mapping Δ_in Γ_out} →
    (hvarMap : (rVarMap₁, varMap₁) ∈ matchVar.matchArg lets _ matchLets Tₗ Tᵣ rma ma) →
    (h_sub_r : rVarMap₁.entries ⊆ rVarMap₂.entries) →
    (h_sub : varMap₁.entries ⊆ varMap₂.entries) →
    {s : Γ_in.Valuation} →
    HVector.map (matchLets.denote
        (fun t' v' => by
          match rVarMap₂.lookup ⟨_, v'⟩ with
          | some i =>
            exact i.denote (fun _ => Ctxt.Var.emptyElim)
          | none => exact fun _ => default)
        (fun t' v' => by
          match varMap₂.lookup ⟨_, v'⟩ with
          | some v' =>
            exact lets.denote (fun _ => Ctxt.Var.emptyElim) s v'
          | none => exact default
        )) Tᵣ = HVector.map (lets.denote (fun _ => Ctxt.Var.emptyElim) s) Tₗ
  | _, .nil, .nil, rma, ma, _, _, _,_, _, _, _, _ => by simp [HVector.map]
  | t::l, .cons vₗ vsₗ, .cons vᵣ vsᵣ, rma, ma, rVarMap₁, rVarMap₂,
      varMap₁, varMap₂, hvarMap, h_sub_r, h_sub, s => by
    simp only [HVector.map]
    simp only [matchVar.matchArg, bind, Option.mem_def, Option.bind_eq_some] at hvarMap
    rcases hvarMap with ⟨⟨rVarMap', varMap'⟩, hvarMap', hvarMap''⟩
    congr 1
    · rw [denote_matchVar_of_subset hvarMap']
      · exact (subset_entries_matchVar_matchArg hvarMap'').1.trans h_sub_r
      · exact (subset_entries_matchVar_matchArg hvarMap'').2.trans h_sub
    · exact denote_matchVar_matchArg hvarMap'' h_sub_r h_sub

theorem denote_matchVar_matchReg {rg : RegMVars Ty}
    {Γ_out Δ_in : Ctxt Ty} : {l : List (Ctxt Ty × Ty)} →
    {Tₗ : HVector (fun t : Ctxt Ty × Ty => Reg Op [] t.fst t.snd) l} →
    {Tᵣ : HVector (fun t : Ctxt Ty × Ty => Reg Op rg t.fst t.snd) l} →
    {rma : RegMapping Op rg} →
    {ma : Mapping Δ_in Γ_out} →
    {rVarMap₁ rVarMap₂ : RegMapping Op rg} → {varMap : Mapping Δ_in Γ_out} →
    (hvarMap : (rVarMap₁, varMap) ∈ matchVar.matchReg Tₗ Tᵣ rma ma) →
    (h_sub_r : rVarMap₁.entries ⊆ rVarMap₂.entries) →
    HVector.denoteReg Tᵣ (fun t' v' => by
      match rVarMap₂.lookup ⟨_, v'⟩ with
      | some i =>
        exact i.denote (fun _ => Ctxt.Var.emptyElim)
      | none => exact fun _ => default) =
    HVector.denoteReg Tₗ (fun _ => Var.emptyElim)
  | [], .nil, .nil, rma, ma, rVarMap₁, rVarMap₂, varMap, hvarMap, h_sub_r => by
    rw [HVector.denoteReg, HVector.denoteReg]
  | t::l, .cons (Reg.icom comₗ) rsₗ, .cons (Reg.mvar i) rsᵣ, rma, ma, rVarMap₁,
      rVarMap₂, varMap, hvarMap, h_sub_r => by
    rw [HVector.denoteReg, HVector.denoteReg, Reg.denote, Reg.denote]
    simp only [matchVar.matchReg] at hvarMap
    congr 1
    · split
      · split at hvarMap
        · sorry --I know how to do this
        · split_ifs at hvarMap
          · subst comₗ
            sorry -- I know how to do this
          · simp_all
      · sorry -- I know how to do this
    · split at hvarMap
      · exact denote_matchVar_matchReg hvarMap h_sub_r
      · split_ifs at hvarMap
        · subst comₗ
          exact denote_matchVar_matchReg hvarMap h_sub_r
        · simp_all
  | t::l, .cons (Reg.icom comₗ) rsₗ, .cons (Reg.icom comᵣ) rsᵣ, rma, ma, rVarMap₁,
      rVarMap₂, varMap, hvarMap, h_sub_r => by
    rw [HVector.denoteReg, HVector.denoteReg, Reg.denote, Reg.denote]
    simp only [matchVar.matchReg, Bind.bind, Option.mem_def, Option.bind_eq_some] at hvarMap
    rcases hvarMap with ⟨⟨rVarMap', varMap'⟩, hvarMap', hvarMap''⟩
    rw [denote_matchVar_matchReg hvarMap'' h_sub_r]
    congr 1
    funext s
    simp only [← ICom.denote_toLets]
    rw [← denote_matchVar_of_subset hvarMap' _
      (List.Subset.refl _)]
    exact (denote_matchVar_of_subset _ _ _).symm


end
#exit
theorem denote_matchVar {lets : Lets Op rg Γ_in Γ_out} {v : Γ_out.Var t} {varMap : Mapping Δ_in Γ_out}
    {s₁ : Γ_in.Valuation}
    {ma : Mapping Δ_in Γ_out}
    {matchLets : Lets Op rg Δ_in Δ_out}
    {w : Δ_out.Var t} :
    varMap ∈ matchVar lets v matchLets w ma →
    matchLets.denote mv (fun t' v' => by
        match varMap.lookup ⟨_, v'⟩  with
        | some v' => exact lets.denote mv s₁ v'
        | none => exact default
        ) w =
      lets.denote mv s₁ v :=
  denote_matchVar_of_subset (List.Subset.refl _)

theorem lt_one_add_add (a b : ℕ) : b < 1 + a + b := by
  simp (config := { arith := true }); exact Nat.zero_le _

@[simp]
theorem zero_eq_zero : (Zero.zero : ℕ) = 0 := rfl

attribute [simp] lt_one_add_add

macro_rules | `(tactic| decreasing_trivial) => `(tactic| simp (config := {arith := true}))

mutual

theorem mem_matchVar_matchArg
    {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty} {lets : Lets Op rg Γ_in Γ_out}
    {matchLets : Lets Op rg Δ_in Δ_out} :
    {l : List Ty} → {argsₗ : HVector (Var Γ_out) l} →
    {argsᵣ : HVector (Var Δ_out) l} → {ma : Mapping Δ_in Γ_out} →
    {varMap : Mapping Δ_in Γ_out} →
    (hvarMap : varMap ∈ matchVar.matchArg Δ_out
        (fun t vₗ vᵣ ma =>
            matchVar (t := t) lets vₗ matchLets vᵣ ma) argsₗ argsᵣ ma) →
    ∀ {t' v'}, ⟨t', v'⟩ ∈ (argsᵣ.vars).biUnion (fun v => matchLets.vars v.2) →
      ⟨t', v'⟩ ∈ varMap
  | _, .nil, .nil, _, varMap, _ => by simp
  | _, .cons vₗ argsₗ, .cons vᵣ argsᵣ, ma, varMap, h => by
    simp [matchVar.matchArg, bind, pure] at h
    rcases h with ⟨ma', h₁, h₂⟩
    simp only [HVector.vars_cons, Finset.biUnion_insert, Finset.mem_union,
      Finset.mem_biUnion, Sigma.exists]
    rintro (h | ⟨a, b, hab⟩)
    · exact AList.keys_subset_keys_of_entries_subset_entries
        (subset_entries_matchVar_matchArg h₂)
        (mem_matchVar h₁ h)
    · exact mem_matchVar_matchArg h₂
        (Finset.mem_biUnion.2 ⟨⟨_, _⟩, hab.1, hab.2⟩)

/-- All variables contained in `matchExpr` are assigned by `matchVar`. -/
theorem mem_matchVar
    {varMap : Mapping Δ_in Γ_out} {ma : Mapping Δ_in Γ_out}
    {lets : Lets Op rg Γ_in Γ_out} {v : Γ_out.Var t} :
    {matchLets : Lets Op rg Δ_in Δ_out} → {w : Δ_out.Var t} →
    (hvarMap : varMap ∈ matchVar lets v matchLets w ma) →
    ∀ {t' v'}, ⟨t', v'⟩ ∈ matchLets.vars w → ⟨t', v'⟩ ∈ varMap
  | .nil, w, h, t', v' => by
    simp [Lets.vars]
    simp [matchVar] at h
    intro h_mem
    subst h_mem
    intro h; cases h
    split at h
    · split_ifs at h
      · simp at h
        subst h
        subst v
        exact AList.lookup_isSome.1 (by simp_all)
    · simp at h
      subst h
      simp

  | .lete matchLets matchE, w, h, t', v' => by
    cases w using Ctxt.Var.casesOn
    next w =>
      simp [matchVar] at h
      apply mem_matchVar h
    next =>
      simp [Lets.vars]
      intro _ _ hl h_v'
      simp [matchVar, pure, bind] at h
      rcases h with ⟨⟨ope, h, args⟩, he₁, he₂⟩
      subst t
      split_ifs at he₂ with h
      · dsimp at h
        dsimp
        apply @mem_matchVar_matchArg (hvarMap := he₂)
        simp
        refine ⟨_, _, ?_, h_v'⟩
        rcases matchE  with ⟨_, _, _⟩
        dsimp at h
        rcases h with ⟨rfl, _⟩
        exact hl

end
termination_by
  mem_matchVar_matchArg _ _ _ _ _ matchLets args _ _ _ _ _ _ _ => (sizeOf matchLets, sizeOf args)
  mem_matchVar _ _ _ _ matchLets _ _ _ _ => (sizeOf matchLets, 0)

/-- A version of `matchVar` that returns a `Hom` of `Ctxt`s instead of the `AList`,
provided every variable in the context appears as a free variable in `matchExpr`. -/
def matchVarMap {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty} {t : Ty}
    (lets : Lets Op rg Γ_in Γ_out) (v : Γ_out.Var t) (matchLets : Lets Op rg Δ_in Δ_out) (w : Δ_out.Var t)
    (hvars : ∀ t (v : Δ_in.Var t), ⟨t, v⟩ ∈ matchLets.vars w) :
    Option (Δ_in.Hom Γ_out) := do
  match hm : matchVar lets v matchLets w with
  | none => none
  | some m =>
    return fun t v' =>
    match h : m.lookup ⟨t, v'⟩ with
    | some v' => by exact v'
    | none => by
      have := AList.lookup_isSome.2 (mem_matchVar hm (hvars t v'))
      simp_all

theorem denote_matchVarMap {Γ_in Γ_out Δ_in Δ_out : Ctxt Ty}
    {lets : Lets Op rg Γ_in Γ_out}
    {t : Ty} {v : Γ_out.Var t}
    {matchLets : Lets Op rg Δ_in Δ_out}
    {w : Δ_out.Var t}
    {hvars : ∀ t (v : Δ_in.Var t), ⟨t, v⟩ ∈ matchLets.vars w}
    {map : Δ_in.Hom Γ_out}
    (mv : toType rg)
    (hmap : map ∈ matchVarMap lets v matchLets w hvars) (s₁ : Γ_in.Valuation) :
    matchLets.denote mv (fun t' v' => lets.denote mv s₁ (map v')) w =
      lets.denote mv s₁ v := by
  rw [matchVarMap] at hmap
  split at hmap
  next => simp_all
  next hm =>
    rw [← denote_matchVar hm]
    simp only [Option.mem_def, Option.some.injEq, pure] at hmap
    subst hmap
    congr
    funext t' v;
    split
    . congr
      dsimp
      split <;> simp_all
    . have := AList.lookup_isSome.2 (mem_matchVar hm (hvars _ v))
      simp_all

/-- `splitProgramAtAux pos lets prog`, will return a `Lets` ending
with the `pos`th variable in `prog`, and an `ICom` starting with the next variable.
It also returns, the type of this variable and the variable itself as an element
of the output `Ctxt` of the returned `Lets`.  -/
def splitProgramAtAux : (pos : ℕ) → (lets : Lets Op rg Γ₁ Γ₂) →
    (prog : ICom Op rg Γ₂ t) →
    Option (Σ (Γ₃ : Ctxt Ty), Lets Op rg Γ₁ Γ₃ × ICom Op rg Γ₃ t × (t' : Ty) × Γ₃.Var t')
  | 0, lets, .lete e body => some ⟨_, .lete lets e, body, _, Ctxt.Var.last _ _⟩
  | _, _, .ret _ => none
  | n+1, lets, .lete e body =>
    splitProgramAtAux n (lets.lete e) body

theorem denote_splitProgramAtAux : {pos : ℕ} → {lets : Lets Op rg Γ₁ Γ₂} →
    {prog : ICom Op rg Γ₂ t} →
    {res : Σ (Γ₃ : Ctxt Ty), Lets Op rg Γ₁ Γ₃ × ICom Op rg Γ₃ t × (t' : Ty) × Γ₃.Var t'} →
    (hres : res ∈ splitProgramAtAux pos lets prog) →
    (s : Γ₁.Valuation) →
    res.2.2.1.denote mv (res.2.1.denote mv s) = prog.denote mv (lets.denote mv s)
  | 0, lets, .lete e body, res, hres, s => by
    simp only [splitProgramAtAux, Option.mem_def, Option.some.injEq] at hres
    subst hres
    simp only [Lets.denote, eq_rec_constant, ICom.denote]
    congr
    funext t v
    cases v using Ctxt.Var.casesOn <;> simp
  | _+1, _, .ret _, res, hres, s => by
    simp [splitProgramAtAux] at hres
  | n+1, lets, .lete e body, res, hres, s => by
    rw [splitProgramAtAux] at hres
    rw [ICom.denote, denote_splitProgramAtAux hres s]
    simp only [Lets.denote, eq_rec_constant, Goedel.toType.snoc]
    congr
    funext t v
    cases v using Ctxt.Var.casesOn <;> simp

/-- `splitProgramAt pos prog`, will return a `Lets` ending
with the `pos`th variable in `prog`, and an `ICom` starting with the next variable.
It also returns, the type of this variable and the variable itself as an element
of the output `Ctxt` of the returned `Lets`.  -/
def splitProgramAt (pos : ℕ) (prog : ICom Op rg Γ₁ t) :
    Option (Σ (Γ₂ : Ctxt Ty), Lets Op rg Γ₁ Γ₂ × ICom Op rg Γ₂ t × (t' : Ty) × Γ₂.Var t') :=
  splitProgramAtAux pos .nil prog

theorem denote_splitProgramAt {pos : ℕ} {prog : ICom Op rg Γ₁ t}
    {res : Σ (Γ₂ : Ctxt Ty), Lets Op rg Γ₁ Γ₂ × ICom Op rg Γ₂ t × (t' : Ty) × Γ₂.Var t'}
    (hres : res ∈ splitProgramAt pos prog) (s : Γ₁.Valuation) :
    res.2.2.1.denote mv (res.2.1.denote mv s) = prog.denote mv s :=
  denote_splitProgramAtAux hres s



/-
  ## Rewriting
-/

/-- `rewriteAt lhs rhs hlhs pos target`, searches for `lhs` at position `pos` of
`target`. If it can match the variables, it inserts `rhs` into the program
with the correct assignment of variables, and then replaces occurences
of the variable at position `pos` in `target` with the output of `rhs`.  -/
def rewriteAt (lhs rhs : ICom Op rg Γ₁ t₁)
    (hlhs : ∀ t (v : Γ₁.Var t), ⟨t, v⟩ ∈ lhs.vars)
    (pos : ℕ) (target : ICom Op rg Γ₂ t₂) :
    Option (ICom Op rg Γ₂ t₂) := do
  let ⟨Γ₃, lets, target', t', vm⟩ ← splitProgramAt pos target
  if h : t₁ = t'
  then
    let flatLhs := lhs.toLets
    let m ← matchVarMap lets vm flatLhs.lets (h ▸ flatLhs.ret)
      (by subst h; exact hlhs)
    return addProgramInMiddle vm m lets (h ▸ rhs) target'
  else none

theorem denote_rewriteAt (lhs rhs : ICom Op rg Γ₁ t₁)
    (hlhs : ∀ t (v : Γ₁.Var t), ⟨t, v⟩ ∈ lhs.vars)
    (pos : ℕ) (target : ICom Op rg Γ₂ t₂)
    (hl : lhs.denote = rhs.denote)
    (rew : ICom Op rg Γ₂ t₂)
    (hrew : rew ∈ rewriteAt lhs rhs hlhs pos target) :
    rew.denote = target.denote := by
  ext mv s
  rw [rewriteAt] at hrew
  simp only [bind, pure, Option.bind] at hrew
  split at hrew
  . simp at hrew
  . rename_i hs
    simp only [Option.mem_def] at hrew
    split_ifs at hrew
    subst t₁
    split at hrew
    . simp at hrew
    . simp only [Option.some.injEq] at hrew
      subst hrew
      rw [denote_addProgramInMiddle, ← hl]
      rename_i _ _ h
      have := denote_matchVarMap mv h
      simp only [ICom.denote_toLets] at this
      simp only [this, ← denote_splitProgramAt hs s]
      congr
      funext t' v'
      simp only [dite_eq_right_iff, forall_exists_index]
      rintro rfl rfl
      simp

variable (Op : _) {Ty : _} [OpSignature Op Ty] [Goedel Ty] [OpDenote Op Ty] (rg : Ctxt (RegT Ty)) in
/--
  Rewrites are indexed with a concrete list of types, rather than an (erased) context, so that
  the required variable checks become decidable
-/
structure PeepholeRewrite (Γ : List Ty) (t : Ty) where
  lhs : ICom Op rg (.ofList Γ) t
  rhs : ICom Op rg (.ofList Γ) t
  correct : lhs.denote = rhs.denote

instance {Γ : List Ty} {t' : Ty} {lhs : ICom Op rg (.ofList Γ) t'} :
    Decidable (∀ (t : Ty) (v : Ctxt.Var (.ofList Γ) t), ⟨t, v⟩ ∈ lhs.vars) :=
  decidable_of_iff
    (∀ (i : Fin Γ.length),
      let v : Ctxt.Var (.ofList Γ) (Γ.get i) := ⟨i, by simp [List.get?_eq_get, Ctxt.ofList]⟩
      ⟨_, v⟩ ∈ lhs.vars) <|  by
  constructor
  . intro h t v
    rcases v with ⟨i, hi⟩
    rcases List.get?_eq_some.1 hi with ⟨h', rfl⟩
    simp at h'
    convert h ⟨i, h'⟩
  . intro h i
    apply h

def rewritePeepholeAt (pr : PeepholeRewrite Op rg Γ t)
    (pos : ℕ) (target : ICom Op [] Γ₂ t₂) :
    (ICom Op [] Γ₂ t₂) :=
    if hlhs : ∀ t (v : Ctxt.Var (.ofList Γ) t), ⟨_, v⟩ ∈ pr.lhs.vars then
      match rewriteAt pr.lhs pr.rhs hlhs pos target
      with
        | some res => res
        | none => target
      else target

theorem denote_rewritePeepholeAt (pr : PeepholeRewrite Op rg Γ t)
    (pos : ℕ) (target : ICom Op rg Γ₂ t₂) :
    (rewritePeepholeAt pr pos target).denote = target.denote := by
    simp only [rewritePeepholeAt]
    split_ifs
    case pos h =>
      generalize hrew : rewriteAt pr.lhs pr.rhs h pos target = rew
      cases rew with
        | some res =>
          exact denote_rewriteAt pr.lhs pr.rhs h pos target pr.correct _ hrew
        | none => simp
    case neg h => simp

section SimpPeephole


/--
Simplify evaluation junk, leaving behind Lean level proposition to be proven.
-/
macro "simp_peephole" "[" ts: Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
      (
      funext ll
      simp only [ICom.denote, IExpr.denote, HVector.denote, Var.zero_eq_last, Var.succ_eq_toSnoc,
        Ctxt.snoc, Goedel.toType.snoc_last, Ctxt.ofList, Goedel.toType.snoc_toSnoc,
        HVector.map, OpDenote.denote, IExpr.op_mk, IExpr.args_mk, $ts,*]
      generalize ll { val := 0, property := _ } = a;
      generalize ll { val := 1, property := _ } = b;
      generalize ll { val := 2, property := _ } = c;
      generalize ll { val := 3, property := _ } = d;
      generalize ll { val := 4, property := _ } = e;
      generalize ll { val := 5, property := _ } = f;
      simp [Goedel.toType] at a b c d e f;
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
      try clear ll;
      )
   )

/-- `simp_peephole` with no extra user defined theorems. -/
macro "simp_peephole" : tactic => `(tactic| simp_peephole [])


end SimpPeephole


/-
  ## Examples
-/

namespace Examples

/-- A very simple type universe. -/
inductive ExTy
  | nat
  | bool
  deriving DecidableEq, Repr

@[reducible]
instance : Goedel ExTy where
  toType
    | .nat => Nat
    | .bool => Bool

inductive ExOp :  Type
  | add : ExOp
  | beq : ExOp
  | cst : ℕ → ExOp
  deriving DecidableEq

instance : OpSignature ExOp ExTy where
  outTy
    | .add => .nat
    | .beq => .bool
    | .cst _ => .nat
  sig
    | .add => [.nat, .nat]
    | .beq => [.nat, .nat]
    | .cst _ => []
  regSig := fun _ => []

@[reducible]
instance : OpDenote ExOp ExTy where
  denote
    | .cst n, _, _ => n
    | .add, .cons (a : Nat) (.cons b .nil), _ => a + b
    | .beq, .cons (a : Nat) (.cons b .nil), _ => a == b

def cst {Γ : Ctxt _} (n : ℕ) : IExpr ExOp ∅ Γ .nat  :=
  IExpr.mk
    (op := .cst n)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)

def add {Γ : Ctxt _} (e₁ e₂ : Var Γ .nat) : IExpr ExOp ∅ Γ .nat :=
  IExpr.mk
    (op := .add)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

section SimpPeephole
macro "simp_peephole" "[" ts: Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
      (
      funext mv ll
      simp only [ICom.denote, IExpr.denote, Reg.denote, HVector.denote,
        Var.zero_eq_last, Var.succ_eq_toSnoc,
        Ctxt.snoc, Ctxt.ofList,
        Goedel.toType.snoc_last, Goedel.toType.snoc_toSnoc,
        HVector.map, OpDenote.denote, IExpr.op_mk, IExpr.args_mk, $ts,*]
      generalize ll { val := 0, property := _ } = a;
      generalize ll { val := 1, property := _ } = b;
      generalize ll { val := 2, property := _ } = c;
      generalize ll { val := 3, property := _ } = d;
      generalize ll { val := 4, property := _ } = e;
      generalize ll { val := 5, property := _ } = f;
      simp [Goedel.toType] at a b c d e f;
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
      try clear ll;
      )
   )

attribute [local simp] Ctxt.snoc

namespace Examples

def ex1 : ICom ExOp ∅ ∅ .nat :=
  ICom.lete (cst 1) <|
  ICom.lete (add ⟨0, by simp [Ctxt.snoc]⟩ ⟨0, by simp [Ctxt.snoc]⟩ ) <|
  ICom.ret ⟨0, by simp [Ctxt.snoc]⟩

def ex2 : ICom ExOp ∅ ∅ .nat :=
  ICom.lete (cst 1) <|
  ICom.lete (add ⟨0, by simp⟩ ⟨0, by simp⟩) <|
  ICom.lete (add ⟨1, by simp⟩ ⟨0, by simp⟩) <|
  ICom.lete (add ⟨1, by simp⟩ ⟨1, by simp⟩) <|
  ICom.lete (add ⟨1, by simp⟩ ⟨1, by simp⟩) <|
  ICom.ret ⟨0, by simp⟩

-- a + b => b + a
def m : ICom ExOp ∅ (.ofList [.nat, .nat]) .nat :=
  .lete (add ⟨0, by simp⟩ ⟨1, by simp⟩) (.ret ⟨0, by simp⟩)
def r : ICom ExOp ∅ (.ofList [.nat, .nat]) .nat :=
  .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩) (.ret ⟨0, by simp⟩)

def p1 : PeepholeRewrite ExOp ∅ [.nat, .nat] .nat:=
  { lhs := m, rhs := r, correct :=
    by
      rw [m, r]
      simp_peephole [add]
      apply Nat.add_comm
      done
    }

example : rewritePeepholeAt p1 1 ex1 = (
  ICom.lete (cst 1)  <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩)  <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩)  <|
     .ret ⟨0, by simp⟩) := by rfl

-- a + b => b + a
example : rewritePeepholeAt p1 0 ex1 = ex1 := by rfl

example : rewritePeepholeAt p1 1 ex2 = (
  ICom.lete (cst 1)   <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩) <|
     .lete (add ⟨2, by simp⟩ ⟨0, by simp⟩) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩ ) <|
     .ret ⟨0, by simp⟩) := by rfl

example : rewritePeepholeAt p1 2 ex2 = (
  ICom.lete (cst 1)   <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩) <|
     .lete (add ⟨1, by simp⟩ ⟨2, by simp⟩) <|
     .lete (add ⟨2, by simp⟩ ⟨2, by simp⟩) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩) <|
     .ret ⟨0, by simp⟩) := by rfl

example : rewritePeepholeAt p1 3 ex2 = (
  ICom.lete (cst 1)   <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (add ⟨2, by simp⟩ ⟨2, by simp⟩  ) <|
     .lete (add ⟨2, by simp⟩ ⟨2, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

example : rewritePeepholeAt p1 4 ex2 = (
  ICom.lete (cst 1)   <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (add ⟨2, by simp⟩ ⟨2, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

def ex2' : ICom ExOp ∅ ∅ .nat :=
  ICom.lete (cst 1) <|
  ICom.lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
  ICom.lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
  ICom.lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
  ICom.lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
  ICom.ret ⟨0, by simp⟩

-- a + b => b + (0 + a)
def r2 : ICom ExOp ∅ (.ofList [.nat, .nat]) .nat :=
  .lete (cst 0) <|
  .lete (add ⟨0, by simp⟩ ⟨1, by simp⟩) <|
  .lete (add ⟨3, by simp⟩ ⟨0, by simp⟩) <|
  .ret ⟨0, by simp⟩

def p2 : PeepholeRewrite ExOp ∅ [.nat, .nat] .nat:=
  { lhs := m, rhs := r2, correct :=
    by
      rw [m, r2]
      simp_peephole [add, cst]
      intros a b
      rw [Nat.zero_add]
      apply Nat.add_comm
      done
    }

example : rewritePeepholeAt p2 1 ex2' = (
     .lete (cst 1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (cst 0) <|
     .lete (add ⟨0, by simp⟩ ⟨2, by simp⟩  ) <|
     .lete (add ⟨3, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

example : rewritePeepholeAt p2 2 ex2 = (
  ICom.lete (cst  1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (cst  0) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨3, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨4, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

example : rewritePeepholeAt p2 3 ex2 = (
  ICom.lete (cst  1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (cst  0) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨4, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

example : rewritePeepholeAt p2 4 ex2 = (
  ICom.lete (cst  1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (cst  0) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨0, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

-- a + b => (0 + a) + b
def r3 : ICom ExOp ∅ (.ofList [.nat, .nat]) .nat :=
  .lete (cst 0) <|
  .lete (add ⟨0, by simp⟩ ⟨1, by simp⟩) <|
  .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩) <|
  .ret ⟨0, by simp⟩

def p3 : PeepholeRewrite ExOp ∅ [.nat, .nat] .nat:=
  { lhs := m, rhs := r3, correct :=
    by
      rw [m, r3]
      simp_peephole [add, cst]
      intros a b
      rw [Nat.zero_add]
    }

example : rewritePeepholeAt p3 1 ex2 = (
  ICom.lete (cst  1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (cst  0) <|
     .lete (add ⟨0, by simp⟩ ⟨2, by simp⟩  ) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

example : rewritePeepholeAt p3 2 ex2 = (
  ICom.lete (cst  1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (cst  0) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨4, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

example : rewritePeepholeAt p3 3 ex2 = (
  ICom.lete (cst  1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (cst  0) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨0, by simp⟩ ⟨4, by simp⟩  ) <|
     .lete (add ⟨4, by simp⟩ ⟨4, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

example : rewritePeepholeAt p3 4 ex2 = (
  ICom.lete (cst  1) <|
     .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (add ⟨1, by simp⟩ ⟨1, by simp⟩  ) <|
     .lete (cst  0) <|
     .lete (add ⟨0, by simp⟩ ⟨3, by simp⟩  ) <|
     .lete (add ⟨0, by simp⟩ ⟨4, by simp⟩  ) <|
     .ret ⟨0, by simp⟩  ) := by rfl

def ex3 : ICom ExOp ∅ ∅ .nat :=
  .lete (cst 1) <|
  .lete (cst 0) <|
  .lete (cst 2) <|
  .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩) <|
  .lete (add ⟨3, by simp⟩ ⟨1, by simp⟩) <|
  .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩) <| --here
  .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩) <|
  .ret ⟨0, by simp⟩

def p4 : PeepholeRewrite ExOp ∅ [.nat, .nat] .nat:=
  { lhs := r3, rhs := m, correct :=
    by
      rw [m, r3]
      simp_peephole [add, cst]
      intros a b
      rw [Nat.zero_add]
      done
    }

example : rewritePeepholeAt p4 5 ex3 = (
  .lete (cst 1) <|
  .lete (cst 0) <|
  .lete (cst 2) <|
  .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩) <|
  .lete (add ⟨3, by simp⟩ ⟨1, by simp⟩) <|
  .lete (add ⟨1, by simp⟩ ⟨0, by simp⟩) <|
  .lete (add ⟨3, by simp⟩ ⟨1, by simp⟩) <|
  .lete (add ⟨0, by simp⟩ ⟨0, by simp⟩) <|
  .ret ⟨0, by simp⟩) := rfl

end Examples

namespace RegionExamples

/-- A very simple type universe. -/
inductive ExTy
  | nat
  deriving DecidableEq, Repr

@[reducible]
instance : Goedel ExTy where
  toType
    | .nat => Nat

inductive ExOp :  Type
  | add : ExOp
  | runK : ℕ → ExOp
  deriving DecidableEq

instance : OpSignature ExOp ExTy where
  outTy
    | .add => .nat
    | .runK _ => .nat
  sig
    | .add => [.nat, .nat]
    | .runK _ => [.nat]
  regSig
    | .runK _ => [([.nat], .nat)]
    | _ => []


@[reducible]
instance : OpDenote ExOp ExTy where
  denote
    | .add, .cons (a : Nat) (.cons b .nil), _ => a + b
    | .runK (k : Nat), (.cons (v : Nat) .nil), (.cons rgn _nil) =>
      k.iterate (fun val => rgn (fun _ty _var => val)) v

def add {Γ : Ctxt _} (e₁ e₂ : Var Γ .nat) : IExpr ExOp ∅ Γ .nat :=
  IExpr.mk
    (op := .add)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def runK {Γ : Ctxt _} (k : Nat) {rg : RegMVars ExTy} (input : Var Γ .nat)
    (body : Reg ExOp rg [ExTy.nat] ExTy.nat) :
    IExpr ExOp rg Γ .nat :=
  IExpr.mk
    (op := .runK k)
    (ty_eq := rfl)
    (args := .cons input .nil)
    (regArgs := HVector.cons body HVector.nil)

attribute [local simp] Ctxt.snoc

namespace Example1

/-- running `f(x) = x + x` 0 times is the identity. -/
-- | pattern only has 'Reg.mvar', no concrete regions.
def peephole_lhs : ICom ExOp [([.nat], .nat)] [.nat] .nat :=
  ICom.lete (runK (k := 0) ⟨0, by simp[Ctxt.snoc]⟩ (
      Reg.mvar ⟨0, by simp⟩)
  ) <|
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩

def peephole_rhs : ICom ExOp [([.nat], .nat)] [.nat] .nat :=
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩

/--
%out = runK (?mvar)
  ({ ?rgn_mvar : (i32) -> (i32) })
  { k = 0 } : (i32) -> (i32)
==>
%out = ?mvar
-/
def peephole : PeepholeRewrite ExOp [([.nat], .nat)] [.nat] .nat:=
  { lhs := peephole_lhs, rhs := peephole_rhs, correct := by
      sorry
  }

/--
def concrete_prog1_lhs(%x : i32) {
  %out = runK (%x) ({
    ^entry(%arg0 : i32):
      return %arg0
  }) { k = 0 } : (i32, i32) -> i32
  return %out
}
-/
def concrete_prog1_lhs : ICom ExOp ∅ [.nat] .nat :=
  -- | The instance of the pattern occurs at the top-level ICom
  ICom.lete (runK (k := 0) ⟨0, by simp[Ctxt.snoc]⟩ (Reg.icom <|
    ICom.ret ⟨0, by simp[Ctxt.snoc]⟩
  )) <|
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩

/--
def concrete_prog1_rhs(%x : i32) {
  return %x : i32
}
-/
def concrete_prog1_rhs : ICom ExOp ∅ [.nat] .nat :=
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩


example : rewritePeepholeAt peephole 1 concrete_prog1_lhs =
  concrete_prog_rhs := sorry

end Example1

namespace Example2


-- | pattern only has 'Reg.mvar', no concrete regions.
def peephole_lhs : ICom ExOp [([.nat], .nat)] [.nat] .nat :=
  ICom.lete (runK (k := 0) ⟨0, by simp[Ctxt.snoc]⟩ (
      Reg.mvar ⟨0, by simp⟩)
  ) <|
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩

def peephole_rhs : ICom ExOp [([.nat], .nat)] [.nat] .nat :=
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩

/--
%out = runK (?mvar)
  ({ ?rgn_mvar : (i32) -> (i32) })
  { k = 0 } : (i32) -> (i32)
==>
%out = ?mvar
-/
def peephole : PeepholeRewrite ExOp [([.nat], .nat)] [.nat] .nat:=
  { lhs := peephole_lhs, rhs := peephole_rhs, correct := by
      sorry
  }

/--
def concrete_prog2_lhs(%x : i32) {
  %out = runK (%x) ({
    ^entry(%arg0 : i32):
      %out2 = runK (%arg0) ({
        ^entry(%nested_arg0 : i32)
          return %nested_arg0
      }) { k = 0 } : (i32, i32) -> i32
    })
  }) { k = 0 } : (i32, i32) -> i32
  return %out
}
-/
def concrete_prog2_lhs : ICom ExOp ∅ [.nat] .nat :=
  ICom.lete (runK (k := 3) ⟨0, by simp[Ctxt.snoc]⟩ (Reg.icom <|
      ICom.lete (runK (k := 0) ⟨0, by simp[Ctxt.snoc]⟩ (Reg.icom <|
        -- | The instance of the pattern occurs in a nested ICom(!)
        ICom.lete (add ⟨0, by simp[Ctxt.snoc]⟩ ⟨0, by simp[Ctxt.snoc]⟩) <|
        ICom.ret ⟨0, by simp[Ctxt.snoc]⟩)) <|
      ICom.ret ⟨0, by simp[Ctxt.snoc]⟩)
  ) <|
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩

/--
def concrete_prog2_lhs(%x : i32) {
  %out = runK (%x) ({
    ^entry(%arg0 : i32):
      return %arg0
    })
  }) { k = 0 } : (i32, i32) -> i32
  return %out
}
-/
def concrete_prog2_rhs : ICom ExOp ∅ [.nat] .nat :=
  ICom.lete (runK (k := 3) ⟨0, by simp[Ctxt.snoc]⟩ (Reg.icom <|
      ICom.ret ⟨0, by simp[Ctxt.snoc]⟩
  )) <|
  ICom.ret ⟨0, by simp[Ctxt.snoc]⟩

example : rewritePeepholeAt peephole 1 concrete_prog_lhs = concrete_prog_rhs := sorry

end Example2

end RegionExamples
