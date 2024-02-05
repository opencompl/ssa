import Mathlib.Data.Erased
import Mathlib.Data.Finset.Basic
import SSA.Core.HVector

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
  -- Erased <| List Ty
  List Ty

namespace Ctxt

variable {Ty : Type}

-- def empty : Ctxt := Erased.mk []
def empty : Ctxt Ty := []

instance : EmptyCollection (Ctxt Ty) := ⟨Ctxt.empty⟩
instance : Inhabited (Ctxt Ty) := ⟨Ctxt.empty⟩

@[simp] lemma empty_eq : (∅ : Ctxt Ty) = [] := rfl

@[match_pattern]
def snoc : Ctxt Ty → Ty → Ctxt Ty :=
  -- fun tl hd => do return hd :: (← tl)
  fun tl hd => hd :: tl

/-- Turn a list of types into a context -/
@[coe, simp]
def ofList : List Ty → Ctxt Ty :=
  -- Erased.mk
  fun Γ => Γ

-- Why was this noncomutable? (removed it to make transformation computable)
@[simp]
def get? : Ctxt Ty → Nat → Option Ty :=
  List.get?

/-- Map a function from one type universe to another over a context -/
def map (f : Ty₁ → Ty₂) : Ctxt Ty₁ → Ctxt Ty₂ :=
  List.map f

instance : Functor Ctxt where
  map := map

instance : LawfulFunctor Ctxt where
  comp_map  := by simp only [List.map_eq_map, List.map_map, forall_const, implies_true]
  id_map    := by simp only [List.map_eq_map, List.map_id, forall_const]
  map_const := by simp only [Functor.mapConst, Functor.map, Function.const, forall_const]

/-- Recursion principle for contexts in terms of `Ctxt.nil` and `Ctxt.snoc` -/
@[eliminator, elab_as_elim]
def recOn {motive : Ctxt Ty → Sort*}
    (nil  : motive empty)
    (snoc : (Γ : Ctxt Ty) → (t : Ty) → motive Γ → motive (Γ.snoc t)) :
    ∀ Γ, motive Γ
  | []        => nil
  | ty :: tys  => snoc tys ty (recOn nil snoc tys)

def Var (Γ : Ctxt Ty) (t : Ty) : Type :=
  { i : Nat // Γ.get? i = some t }

/-- constructor for Var. -/
def Var.mk (Γ : Ctxt Ty) (t : Ty) (i : Nat) (hi : Γ.get? i = some t) : Γ.Var t :=
  ⟨i, hi⟩

namespace Var

instance : DecidableEq (Var Γ t) := by
  delta Var
  infer_instance

@[match_pattern]
def last (Γ : Ctxt Ty) (t : Ty) : Ctxt.Var (Ctxt.snoc Γ t) t :=
  ⟨0, by simp [snoc, List.get?]⟩

def emptyElim {α : Sort _} {t : Ty} : Ctxt.Var [] t → α :=
  fun ⟨_, h⟩ => by
    simp only [get?, EmptyCollection.emptyCollection, empty, List.get?_nil] at h


/-- Take a variable in a context `Γ` and get the corresponding variable
in context `Γ.snoc t`. This is marked as a coercion. -/
@[coe]
def toSnoc {Γ : Ctxt Ty} {t t' : Ty} (var : Var Γ t) : Var (snoc Γ t') t  :=
  ⟨var.1+1, var.2⟩

@[simp]
theorem zero_eq_last {Γ : Ctxt Ty} {t : Ty} (h) :
    ⟨0, h⟩ = last Γ t :=
  rfl

@[simp]
theorem succ_eq_toSnoc {Γ : Ctxt Ty} {t : Ty} {w} (h : (Γ.snoc t).get? (w+1) = some t') :
    ⟨w+1, h⟩ = toSnoc ⟨w, h⟩ :=
  rfl

/-- Transport a variable from `Γ` to any mapped context `Γ.map f` -/
@[coe]
def toMap : Var Γ t → Var (Γ.map f) (f t)
  | ⟨i, h⟩ => ⟨i, by
      simp only [get?, map, List.get?_map, Option.map_eq_some']
      exact ⟨t, h, rfl⟩
    ⟩

def cast {Γ : Ctxt Op} (h_eq : ty₁ = ty₂) : Γ.Var ty₁ → Γ.Var ty₂
  | ⟨i, h⟩ => ⟨i, h_eq ▸ h⟩

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
        _root_.cast (by
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

/-- `f.comp g := g(f(x))` -/
def Hom.comp {Γ Γ' Γ'' : Ctxt Ty} (self : Hom Γ Γ') (rangeMap : Hom Γ' Γ'') : Hom Γ Γ'' :=
  fun _t v => rangeMap (self v)

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

/-- A valuation for a context. Provide a way to evaluate every variable in a context. -/
def Valuation.eval {Γ : Ctxt Ty} (VAL : Valuation Γ) ⦃t : Ty⦄ (v : Γ.Var t) : toType t :=
    VAL v

/-- Make a valuation for the empty context. -/
def Valuation.nil : Ctxt.Valuation ([] : Ctxt Ty) := fun _ v => v.emptyElim

instance : Inhabited (Ctxt.Valuation ([] : Ctxt Ty)) := ⟨Valuation.nil⟩

/-- Make a valuation for `Γ.snoc t` from a valuation for `Γ` and an element of `t.toType`. -/
def Valuation.snoc {Γ : Ctxt Ty} {t : Ty} (s : Γ.Valuation) (x : toType t) :
    (Γ.snoc t).Valuation := by
  intro t' v
  revert s x
  refine Ctxt.Var.casesOn v ?_ ?_
  . intro _ _ _ v s _; exact s v
  . intro _ _ _ x; exact x

/-- Show the equivalence between the definition in terms of `snoc` and `snoc'`. -/
theorem Valuation.snoc_eq {Γ : Ctxt Ty} {t : Ty} (s : Γ.Valuation) (x : toType t) :
    (s.snoc x) = fun t var => match var with
      | ⟨0, hvar⟩ => by
          simp[Ctxt.snoc] at hvar
          exact (hvar ▸ x)
      | ⟨.succ i, hvar⟩ => s ⟨i, hvar⟩ := by
  funext t' v
  rcases v with ⟨⟨⟩|i, hi⟩
  · injection hi with hi
    subst hi
    rfl
  · rfl

@[simp]
theorem Valuation.snoc_last {Γ : Ctxt Ty} {t : Ty} (s : Γ.Valuation) (x : toType t) :
    (s.snoc x) (Ctxt.Var.last _ _) = x := by
  simp [Ctxt.Valuation.snoc]

@[simp]
theorem Valuation.snoc_zero {Γ : Ctxt Ty} {ty : Ty} (s : Γ.Valuation) (x : toType ty)
    (h : get? (Ctxt.snoc Γ ty) 0 = some ty) :
    (s.snoc x) ⟨0, h⟩ = x := by
  simp [Ctxt.Valuation.snoc]

@[simp]
theorem Valuation.snoc_toSnoc {Γ : Ctxt Ty} {t t' : Ty} (s : Γ.Valuation) (x : toType t)
    (v : Γ.Var t') : (s.snoc x) v.toSnoc = s v := by
  simp [Ctxt.Valuation.snoc]

/-!
# Helper to simplify context manipulation with toSnoc and variable access.
-/
/--  (ctx.snoc v₁) ⟨n+1, _⟩ = ctx ⟨n, _⟩ -/
@[simp]
theorem Valuation.snoc_eval {ty : Ty} (Γ : Ctxt Ty) (V : Γ.Valuation) (v : ⟦ty⟧)
    (hvar : Ctxt.get? (Ctxt.snoc Γ ty) (n+1) = some var_val) :
    (V.snoc v) ⟨n+1, hvar⟩ = V ⟨n, by simp [Ctxt.get?,Ctxt.snoc] at hvar; exact hvar⟩ :=
  rfl

/-- There is only one distinct valuation for the empty context -/
theorem Valuation.eq_nil (V : Valuation (empty : Ctxt Ty)) : V = Valuation.nil := by
  funext _ ⟨_, h⟩; contradiction

@[simp]
theorem Valuation.snoc_toSnoc_last {Γ : Ctxt Ty} {t : Ty} (V : Valuation (Γ.snoc t)) :
    snoc (fun t v' => V v'.toSnoc) (V <|.last ..) = V := by
  funext _ v
  cases v using Var.casesOn <;> rfl

/-- Make a a valuation for a singleton value -/
def Valuation.singleton {t : Ty} (v : toType t) : Ctxt.Valuation [t] :=
  Ctxt.Valuation.nil.snoc v

/-- Build valuation from a vector of values of types `types`. -/
def Valuation.ofHVector {types : List Ty} : HVector toType types → Valuation (Ctxt.ofList types)
  | .nil => (default : Ctxt.Valuation ([] : Ctxt Ty))
  | .cons x xs => (Valuation.ofHVector xs).snoc x

/-- Build valuation from a vector of values of types `types`. -/
def Valuation.ofPair [Goedel Ty] {t₁ t₂ : Ty} (v₁: ⟦t₁⟧) (v₂ : ⟦t₂⟧) : Valuation (Ctxt.ofList [t₁, t₂]) :=
  Valuation.ofHVector (.cons v₁ <| .cons v₂ <| .nil )

@[simp]
theorem Valuation.ofPair_fst [Goedel Ty] {t₁ t₂ : Ty} (v₁: ⟦t₁⟧) (v₂ : ⟦t₂⟧) :
  (Ctxt.Valuation.ofPair v₁ v₂) ⟨0, by simp⟩ = v₁ := rfl
@[simp]
theorem Valuation.ofPair_snd [Goedel Ty] {t₁ t₂ : Ty} (v₁: ⟦t₁⟧) (v₂ : ⟦t₂⟧) :
  (Ctxt.Valuation.ofPair v₁ v₂) ⟨1, by simp⟩ = v₂ := rfl

/-- transport/pullback a valuation along a context homomorphism. -/
def Valuation.comap {Γi Γo : Ctxt Ty} (Γiv: Γi.Valuation) (hom : Ctxt.Hom Γo Γi) : Γo.Valuation :=
  fun _to vo =>  Γiv (hom vo)

/-- Recursion principle for valuations in terms of `Valuation.nil` and `Valuation.snoc` -/
@[eliminator, elab_as_elim]
def Valuation.recOn {motive : ∀ {Γ : Ctxt Ty}, Γ.Valuation → Sort*}
    (nil  : motive (Valuation.nil))
    (snoc : ∀ {Γ t} (V : Valuation Γ) (v : ⟦t⟧), motive V → motive (Valuation.snoc V v)) :
    ∀ {Γ} (V : Valuation Γ), motive V := by
  intro Γ V
  induction' Γ with Γ t ih
  · exact (eq_nil V).symm ▸ nil
  · exact snoc_toSnoc_last V ▸ (snoc (fun _ v' => V v'.toSnoc) (V <|.last ..) (ih _))

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

instance : Repr (Var Γ t) where
  reprPrec v _ := f!"%{v.val}"

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

/-- Mapping over contexts does not change their difference -/
@[coe]
def toMap (d : Diff Γ₁ Γ₂) : Diff (Γ₁.map f) (Γ₂.map f) :=
  ⟨d.val, by
    rcases d with ⟨d, h_get_d⟩
    simp only [Valid, get?, map, List.get?_map, Option.map_eq_some', forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h_get_d ⊢
    exact fun t h => ⟨t, h_get_d h, rfl⟩
  ⟩

theorem append_valid {Γ₁ Γ₂ Γ₃  : Ctxt Ty} {d₁ d₂ : Nat} :
  Diff.Valid Γ₁ Γ₂ d₁ →  Diff.Valid Γ₂ Γ₃ d₂ → Diff.Valid Γ₁ Γ₃ (d₁ + d₂) := by
  intros h₁ h₂ i t hi
  specialize @h₁ i t hi
  specialize @h₂ (i + d₁) t h₁
  rw [← h₂, Nat.add_assoc]

/-- Addition of the differences of two contexts -/
def append (d₁ : Diff Γ₁ Γ₂) (d₂ : Diff Γ₂ Γ₃) : Diff Γ₁ Γ₃ :=
  {val := d₁.val + d₂.val,  property := append_valid d₁.property d₂.property}

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
  unfold unSnoc Var.toSnoc toHom
  simp
  funext x v
  congr 1
  rw [Nat.add_assoc, Nat.add_comm 1]

def add : Diff Γ₁ Γ₂ → Diff Γ₂ Γ₃ → Diff Γ₁ Γ₃
  | ⟨d₁, h₁⟩, ⟨d₂, h₂⟩ => ⟨d₁ + d₂, fun h => by
      rw [←Nat.add_assoc]
      apply h₂ <| h₁ h
    ⟩

instance : HAdd (Diff Γ₁ Γ₂) (Diff Γ₂ Γ₃) (Diff Γ₁ Γ₃) := ⟨add⟩

end Diff

/-## Derived Contexts
Contexts that grow a base context-/

/-- `Δ : DerivedCtxt Γ` means that `Δ` is a context obtained by adding elements to context `Γ`.
That is, there exists a context difference `diff : Γ.Diff Δ`. -/
structure DerivedCtxt (Γ : Ctxt Ty) where
  ctxt : Ctxt Ty
  diff : Ctxt.Diff Γ ctxt

namespace DerivedCtxt

/-- Every context is trivially derived from itself -/
@[simp]
abbrev ofCtxt (Γ : Ctxt Ty) : DerivedCtxt Γ := ⟨Γ, .zero _⟩

/-- value of a dervied context from an empty context,
     is the empty context with a zero diff. -/
@[simp]
theorem ofCtxt_empty : DerivedCtxt.ofCtxt ([] : Ctxt Ty) = ⟨[], .zero _⟩ := rfl

/-- `snoc` of a derived context applies `snoc` to the underlying context, and updates the diff -/
@[simp]
def snoc {Γ : Ctxt Ty} : DerivedCtxt Γ → Ty → DerivedCtxt Γ
  | ⟨ctxt, diff⟩, ty => ⟨ty::ctxt, diff.toSnoc⟩

@[simp]
instance {Γ : Ctxt Ty} : CoeHead (DerivedCtxt Γ) (Ctxt Ty) where
  coe := fun ⟨Γ', _⟩ => Γ'

instance {Γ : Ctxt Ty} : CoeDep (Ctxt Ty) Γ (DerivedCtxt Γ) where
  coe := ⟨Γ, .zero _⟩

instance {Γ : Ctxt Ty} {Γ' : DerivedCtxt Γ} :
    CoeHead (DerivedCtxt (Γ' : Ctxt Ty)) (DerivedCtxt Γ) where
  coe := fun ⟨Γ'', diff⟩ => ⟨Γ'', Γ'.diff + diff⟩

instance {Γ' : DerivedCtxt Γ} : Coe (Ctxt.Var Γ t) (Ctxt.Var (Γ' : Ctxt Ty) t) where
  coe v := Γ'.diff.toHom v

end DerivedCtxt


end Ctxt
