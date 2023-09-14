import Mathlib.Data.Erased
import Mathlib.Data.Finset.Basic

/-- 
  Typeclass for a `baseType` which is a Gödel code of Lean types.

  Intuitively, each `b : β` represents a Lean `Type`, but using `β` instead of `Type` directly
  avoids a universe bump
-/
class Goedel (β : Type) : Type 1 where
  toType : β → Type
open Goedel (toType) /- make toType publically visible in module. -/

notation "⟦" x "⟧" => Goedel.toType x

instance : Goedel Unit where toType := fun _ => Unit

def Ctxt (Ty : Type) : Type :=
  Erased <| List Ty
  -- List Ty

namespace Ctxt

variable {Ty : Type}

def empty : Ctxt Ty := Erased.mk []
-- def empty : Ctxt Ty := []

instance : EmptyCollection (Ctxt Ty) := ⟨Ctxt.empty⟩

@[match_pattern]
def snoc : Ctxt Ty → Ty → Ctxt Ty :=
  fun tl hd => Erased.map (hd :: ·) tl
  -- fun tl hd => hd :: tl

/-- Turn a list of types into a context -/
@[coe, simp]
def ofList : List Ty → Ctxt Ty :=
  Erased.mk
  -- fun Γ => Γ 

@[simp]
noncomputable def get? : Ctxt Ty → Nat → Option Ty :=
  fun Γ => Γ.out.get? 
  -- List.get?

@[simp]
theorem get?_snoc_succ {Γ : Ctxt Ty} {t : Ty} {n : Nat} :
    (Γ.snoc t).get? (n + 1) = Γ.get? n := by
  simp [snoc]

  

def Var (Γ : Ctxt Ty) (t : Ty) : Type :=
  { i : Nat // Γ.get? i = some t }

namespace Var

instance : DecidableEq (Var Γ t) := by
  delta Var
  infer_instance

@[match_pattern]
def last (Γ : Ctxt Ty) (t : Ty) : Ctxt.Var (Ctxt.snoc Γ t) t :=
  ⟨0, by simp [snoc, List.get?]⟩

def emptyElim {α : Sort _} {t : Ty} : Ctxt.Var ∅ t → α :=
  fun ⟨_, h⟩ => by 
    simp [EmptyCollection.emptyCollection, empty] at h


/-- Take a variable in a context `Γ` and get the corresponding variable
in context `Γ.snoc t`. This is marked as a coercion. -/
@[coe]
def toSnoc {Γ : Ctxt Ty} {t t' : Ty} (var : Var Γ t) : Var (snoc Γ t') t  :=
  ⟨var.1+1, get?_snoc_succ.symm ▸ var.2⟩

@[simp]
theorem zero_eq_last {Γ : Ctxt Ty} {t : Ty} (h) :
    ⟨0, h⟩ = last Γ t :=
  rfl

@[simp]
theorem succ_eq_toSnoc {Γ : Ctxt Ty} {t : Ty} {w} (h : (Γ.snoc t).get? (w+1) = some t') :
    ⟨w+1, h⟩ = toSnoc ⟨w, get?_snoc_succ.symm ▸ h⟩ :=
  rfl


  
/-- This is an induction principle that case splits on whether or not a variable 
is the last variable in a context. -/
@[elab_as_elim]
def casesOn 
    {motive : (Γ : Ctxt Ty) → (t t' : Ty) → Ctxt.Var (Γ.snoc t') t → Sort _}
    {Γ : Ctxt Ty} {t t' : Ty} (v : (Γ.snoc t').Var t)
    (toSnoc : {t t' : Ty} → 
        {Γ : Ctxt Ty} → (v : Γ.Var t) → motive Γ t t' v.toSnoc)
    (last : {Γ : Ctxt Ty} → {t : Ty} → motive Γ t t (Ctxt.Var.last _ _)) :
      motive Γ t t' v :=
  match v with
    | ⟨0, h⟩ => 
        cast (by 
          simp [snoc] at h
          subst h
          simp [Ctxt.Var.last]
          ) <| @last Γ t
    | ⟨i+1, h⟩ =>
        toSnoc ⟨i, by simpa [snoc] using h⟩

/-- `Ctxt.Var.casesOn` behaves in the expected way when applied to the last variable -/
@[simp]
def casesOn_last
    {motive : (Γ : Ctxt Ty) → (t t' : Ty) → Ctxt.Var (Γ.snoc t') t → Sort _}
    {Γ : Ctxt Ty} {t : Ty}
    (base : {t t' : Ty} → 
        {Γ : Ctxt Ty} → (v : Γ.Var t) → motive Γ t t' v.toSnoc)
    (last : {Γ : Ctxt Ty} → {t : Ty} → motive Γ t t (Ctxt.Var.last _ _)) :
    Ctxt.Var.casesOn (motive := motive)
        (Ctxt.Var.last Γ t) base last = last :=
  rfl

/-- `Ctxt.Var.casesOn` behaves in the expected way when applied to a previous variable,
that is not the last one. -/
@[simp]
def casesOn_toSnoc 
    {motive : (Γ : Ctxt Ty) → (t t' : Ty) → Ctxt.Var (Γ.snoc t') t → Sort _}
    {Γ : Ctxt Ty} {t t' : Ty} (v : Γ.Var t)
    (base : {t t' : Ty} → 
        {Γ : Ctxt Ty} → (v : Γ.Var t) → motive Γ t t' v.toSnoc)
    (last : {Γ : Ctxt Ty} → {t : Ty} → motive Γ t t (Ctxt.Var.last _ _)) :
      Ctxt.Var.casesOn (motive := motive) (Ctxt.Var.toSnoc (t' := t') v) base last = base v :=
  rfl

end Var
  
theorem toSnoc_injective {Γ : Ctxt Ty} {t t' : Ty} : 
    Function.Injective (@Ctxt.Var.toSnoc Ty Γ t t') := by
  let ofSnoc : (Γ.snoc t').Var t → Option (Γ.Var t) :=
    fun v => Ctxt.Var.casesOn v some none
  intro x y h
  simpa using congr_arg ofSnoc h

abbrev Hom (Γ Γ' : Ctxt Ty) := ⦃t : Ty⦄ → Γ.Var t → Γ'.Var t

@[simp]
abbrev Hom.id {Γ : Ctxt Ty} : Γ.Hom Γ :=
  fun _ v => v

/--
  `map.with v₁ v₂` adjusts a single variable of a Context map, so that in the resulting map
   * `v₁` now maps to `v₂`
   * all other variables `v` still map to `map v` as in the original map
-/
def Hom.with [DecidableEq Ty] {Γ₁ Γ₂ : Ctxt Ty} (f : Γ₁.Hom Γ₂) {t : Ty} 
    (v₁ : Γ₁.Var t) (v₂ : Γ₂.Var t) : Γ₁.Hom Γ₂ :=
  fun t' w =>
    if h : ∃ ty_eq : t = t', ty_eq ▸ w = v₁ then 
      h.fst ▸ v₂
    else
      f w


def Hom.snocMap {Γ Γ' : Ctxt Ty} (f : Hom Γ Γ') {t : Ty} : 
    (Γ.snoc t).Hom (Γ'.snoc t) := by
  intro t' v
  cases v using Ctxt.Var.casesOn with
  | toSnoc v => exact Ctxt.Var.toSnoc (f v)
  | last => exact Ctxt.Var.last _ _

@[simp]
abbrev Hom.snocRight {Γ Γ' : Ctxt Ty} (f : Hom Γ Γ') {t : Ty} : Γ.Hom (Γ'.snoc t) :=
  fun _ v => (f v).toSnoc


instance {Γ : Ctxt Ty} : Coe (Γ.Var t) ((Γ.snoc t').Var t) := ⟨Ctxt.Var.toSnoc⟩

section Valuation

variable [Goedel Ty] -- for a valuation, we need to evaluate the Lean `Type` corresponding to a `Ty`

/-- A valuation for a context. Provide a way to evaluate every variable in a context. -/
def Valuation (Γ : Ctxt Ty) : Type :=
  ⦃t : Ty⦄ → Γ.Var t → (toType t)

instance : Inhabited (Ctxt.Valuation (∅ : Ctxt Ty)) := ⟨fun _ v => v.emptyElim⟩ 

/-- Make a valuation for `Γ.snoc t` from a valuation for `Γ` and an element of `t.toType`. -/
def Valuation.snoc {Γ : Ctxt Ty} {t : Ty} (s : Γ.Valuation) (x : toType t) : 
    (Γ.snoc t).Valuation := by
  intro t' v
  revert s x
  refine Ctxt.Var.casesOn v ?_ ?_
  . intro _ _ _ v s _; exact s v
  . intro _ _ _ x; exact x

@[simp]
theorem Valuation.snoc_last {Γ : Ctxt Ty} {t : Ty} (s : Γ.Valuation) (x : toType t) :
    (s.snoc x) (Ctxt.Var.last _ _) = x := by 
  simp [Ctxt.Valuation.snoc]

@[simp]
theorem Valuation.snoc_toSnoc {Γ : Ctxt Ty} {t t' : Ty} (s : Γ.Valuation) (x : toType t)
    (v : Γ.Var t') : (s.snoc x) v.toSnoc = s v := by
  simp [Ctxt.Valuation.snoc]

end Valuation


/- ## VarSet -/

/-- A `Ty`-indexed family of sets of variables in context `Γ` -/
abbrev VarSet (Γ : Ctxt Ty) : Type := 
  Finset (Σ t, Γ.Var t)

namespace VarSet

/-- A `VarSet` with exactly one variable `v` -/
@[simp]
def ofVar {Γ : Ctxt Ty} (v : Γ.Var t) : VarSet Γ :=
  {⟨_, v⟩} 

end VarSet

namespace Var

@[simp] 
theorem val_last {Γ : Ctxt Ty} {t : Ty} : (last Γ t).val = 0 := 
  rfl

@[simp] 
theorem val_toSnoc {Γ : Ctxt Ty} {t t' : Ty} (v : Γ.Var t) : (@toSnoc _ _ _ t' v).val = v.val + 1 :=
  rfl

end Var

/-
## Context difference
-/

@[simp]
abbrev Diff.Valid (Γ₁ Γ₂ : Ctxt Ty) (d : Nat) : Prop :=
  ∀ {i t}, Γ₁.get? i = some t → Γ₂.get? (i+d) = some t

/--
  If `Γ₁` is a prefix of `Γ₂`, 
  then `d : Γ₁.Diff Γ₂` represents the number of elements that `Γ₂` has more than `Γ₁`
-/
def Diff (Γ₁ Γ₂ : Ctxt Ty) : Type :=
  {d : Nat // Diff.Valid Γ₁ Γ₂ d}

namespace Diff

/-- The difference between any context and itself is 0 -/
def zero (Γ : Ctxt Ty) : Diff Γ Γ :=
  ⟨0, fun h => h⟩

/-- Adding a new type to the right context corresponds to incrementing the difference by 1 -/
def toSnoc (d : Diff Γ₁ Γ₂) : Diff Γ₁ (Γ₂.snoc t) :=
  ⟨d.val + 1, by 
    intro i _ h_get_snoc
    rcases d with ⟨d, h_get_d⟩
    simp[←h_get_d h_get_snoc, snoc, List.get?]
  ⟩

/-- Removing a type from the left context corresponds to incrementing the difference by 1 -/
def unSnoc (d : Diff (Γ₁.snoc t) Γ₂) : Diff Γ₁ Γ₂ :=
  ⟨d.val + 1, by
    intro i t h_get
    rcases d with ⟨d, h_get_d⟩
    specialize @h_get_d (i+1) t
    simp [snoc, List.get?] at h_get_d
    rw[←h_get_d h_get, Nat.add_assoc, Nat.add_comm 1, get?]
  ⟩

/-- Adding the difference of two contexts to variable indices is a context mapping -/
def toHom (d : Diff Γ₁ Γ₂) : Hom Γ₁ Γ₂ :=
  fun _ v => ⟨v.val + d.val, d.property v.property⟩

theorem Valid.of_succ {Γ₁ Γ₂ : Ctxt Ty} {d : Nat} (h_valid : Valid Γ₁ (Γ₂.snoc t) (d+1)) :
    Valid Γ₁ Γ₂ d := by
  intro i t h_get
  simp[←h_valid h_get, snoc, List.get?]

theorem toHom_succ {Γ₁ Γ₂ : Ctxt Ty} {d : Nat} (h : Valid Γ₁ (Γ₂.snoc t) (d+1)) :
    toHom ⟨d+1, h⟩ = (toHom ⟨d, Valid.of_succ h⟩).snocRight := by
  rfl

@[simp]
theorem toHom_zero {Γ : Ctxt Ty} {h : Valid Γ Γ 0} :
    toHom ⟨0, h⟩ = Hom.id := by
  rfl

@[simp]
theorem toHom_unSnoc {Γ₁ Γ₂ : Ctxt Ty} (d : Diff (Γ₁.snoc t) Γ₂) : 
    toHom (unSnoc d) = fun _ v => (toHom d) v.toSnoc := by
  simp only [unSnoc, toHom, Var.toSnoc, Nat.add_assoc, Nat.add_comm 1]


end Diff


end Ctxt
