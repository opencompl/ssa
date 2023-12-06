import Mathlib.Tactic

/-- A very simple type universe. -/
inductive Ty
  | nat
  | bool
  deriving DecidableEq, Repr

@[reducible]
def Ty.toType
  | nat => Nat
  | bool => Bool



def Ctxt : Type :=
  List Ty

namespace Ctxt

def empty : Ctxt := []

instance : EmptyCollection Ctxt := ⟨Ctxt.empty⟩

def snoc : Ctxt → Ty → Ctxt :=
  fun tl hd => hd :: tl

def Var (Γ : Ctxt) (t : Ty) : Type :=
  { i : Nat // Γ.get? i = some t }

namespace Var

instance : DecidableEq (Var Γ t) :=
  fun ⟨i, ih⟩ ⟨j, jh⟩ => match inferInstanceAs (Decidable (i = j)) with
    | .isTrue h => .isTrue <| by simp_all
    | .isFalse h => .isFalse <| by intro hc; apply h; apply Subtype.mk.inj hc

def last (Γ : Ctxt) (t : Ty) : Ctxt.Var (Ctxt.snoc Γ t) t :=
  ⟨0, by simp[snoc, List.get?]⟩

def emptyElim {α : Sort _} {t : Ty} : Ctxt.Var ∅ t → α :=
  fun ⟨_, h⟩ => by contradiction

/-- Take a variable in a context `Γ` and get the corresponding variable
in context `Γ.snoc t`. This is marked as a coercion. -/
@[coe]
def toSnoc {Γ : Ctxt} {t t' : Ty} (var : Ctxt.Var Γ t) : Ctxt.Var (Ctxt.snoc Γ t') t  :=
  ⟨var.1+1, by cases var; simp_all [snoc]⟩

/-- This is an induction principle that case splits on whether or not a variable
is the last variable in a context. -/
@[elab_as_elim]
def casesOn
    {motive : (Γ : Ctxt) → (t t' : Ty) → Ctxt.Var (Γ.snoc t') t → Sort _}
    {Γ : Ctxt} {t t' : Ty} (v : (Γ.snoc t').Var t)
    (base : {t t' : Ty} →
        {Γ : Ctxt} → (v : Γ.Var t) → motive Γ t t' v.toSnoc)
    (last : {Γ : Ctxt} → {t : Ty} → motive Γ t t (Ctxt.Var.last _ _)) :
      motive Γ t t' v :=
  match v with
    | ⟨0, h⟩ =>
        cast (by cases h; simp only [Var.last]) <| @last Γ t
    | ⟨i+1, h⟩ =>
        base ⟨i, h⟩

/-- `Ctxt.Var.casesOn` behaves in the expected way when applied to the last variable -/
@[simp]
def casesOn_last
    {motive : (Γ : Ctxt) → (t t' : Ty) → Ctxt.Var (Γ.snoc t') t → Sort _}
    {Γ : Ctxt} {t : Ty}
    (base : {t t' : Ty} →
        {Γ : Ctxt} → (v : Γ.Var t) → motive Γ t t' v.toSnoc)
    (last : {Γ : Ctxt} → {t : Ty} → motive Γ t t (Ctxt.Var.last _ _)) :
    Ctxt.Var.casesOn (motive := motive)
        (Ctxt.Var.last Γ t) base last = last :=
  rfl

/-- `Ctxt.Var.casesOn` behaves in the expected way when applied to a previous variable,
that is not the last one. -/
@[simp]
def casesOn_toSnoc
    {motive : (Γ : Ctxt) → (t t' : Ty) → Ctxt.Var (Γ.snoc t') t → Sort _}
    {Γ : Ctxt} {t t' : Ty} (v : Γ.Var t)
    (base : {t t' : Ty} →
        {Γ : Ctxt} → (v : Γ.Var t) → motive Γ t t' v.toSnoc)
    (last : {Γ : Ctxt} → {t : Ty} → motive Γ t t (Ctxt.Var.last _ _)) :
      Ctxt.Var.casesOn (motive := motive) (Ctxt.Var.toSnoc (t' := t') v) base last = base v :=
  rfl

end Var


section Append

def append : Ctxt → Ctxt → Ctxt :=
  fun xs ys => List.append ys xs


theorem append_empty (Γ : Ctxt) : append Γ ∅ = Γ := by
  simp[append, EmptyCollection.emptyCollection, empty]


theorem append_snoc (Γ Γ' : Ctxt) (t : Ty) :
    append Γ (Ctxt.snoc Γ' t) = (append Γ Γ').snoc t := by
  simp[append, snoc]

@[simp]
theorem _root_.List.get?_append_add :
    List.get? (xs ++ ys) (i + xs.length) = List.get? ys i := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    simp [List.get?_eq_get, Nat.add_succ, ih]

def Var.inl {Γ Γ' : Ctxt} {t : Ty} : Var Γ t → Var (Ctxt.append Γ Γ') t
  | ⟨v, h⟩ => ⟨v + Γ'.length, by simp[←h, append, List.get?_append_add]⟩

def Var.inr {Γ Γ' : Ctxt} {t : Ty} : Var Γ' t → Var (append Γ Γ') t
  | ⟨v, h⟩ => ⟨v, by
      simp[append]
      induction Γ' generalizing v
      case nil =>
        contradiction
      case cons ih =>
        cases v
        case zero =>
          rw[←h]; rfl
        case succ v =>
          apply ih v h
    ⟩

end Append

end Ctxt
