import Mathlib.Tactic
import Mathlib.Data.Erased

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
  Erased <| List Ty

namespace Ctxt

@[match_pattern]
def empty : Ctxt := Erased.mk []

instance : EmptyCollection Ctxt := ⟨Ctxt.empty⟩

@[match_pattern]
def snoc : Ctxt → Ty → Ctxt :=
  fun tl hd => do return hd :: (← tl)

def Var (Γ : Ctxt) (t : Ty) : Type :=
  { i : Nat // Γ.out.get? i = some t }

namespace Var

instance : DecidableEq (Var Γ t) := 
  fun ⟨i, ih⟩ ⟨j, jh⟩ => match inferInstanceAs (Decidable (i = j)) with
    | .isTrue h => .isTrue <| by simp_all
    | .isFalse h => .isFalse <| by intro hc; apply h; apply Subtype.mk.inj hc

def last (Γ : Ctxt) (t : Ty) : Ctxt.Var (Ctxt.snoc Γ t) t :=
  ⟨0, by simp [snoc, List.get?]⟩

def emptyElim {α : Sort _} {t : Ty} : Ctxt.Var ∅ t → α :=
  fun ⟨_, h⟩ => by 
    simp [EmptyCollection.emptyCollection, empty] at h


/-- Take a variable in a context `Γ` and get the corresponding variable
in context `Γ.snoc t`. This is marked as a coercion. -/
@[coe]
def toSnoc {Γ : Ctxt} {t t' : Ty} (var : Var Γ t) : Var (snoc Γ t') t  :=
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
        cast (by 
          simp [snoc] at h
          subst h
          simp [Ctxt.Var.last]
          ) <| @last Γ t
    | ⟨i+1, h⟩ =>
        base ⟨i, by simpa [snoc] using h⟩

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

@[elab_as_elim, eliminator]
noncomputable def casesOn {motive : Ctxt → Sort u}
    (Γ : Ctxt)
    (empty : motive .empty)
    (snoc : (Γ : Ctxt) → (t : Ty) → motive (snoc Γ t)) :
    motive Γ :=
  match h : Γ.out with
    | [] => cast (by simp[Ctxt.empty, ←h]) empty
    | t::Γ => cast (by simp[Ctxt.snoc, ←h]) <| snoc (Erased.mk Γ) t

@[simp]
theorem casesOn_empty {motive : Ctxt → Sort u} (empty : motive .empty) 
    (snoc : (Γ : Ctxt) → (t : Ty) → motive (snoc Γ t)) : 
    casesOn Ctxt.empty empty snoc = empty := by
  simp only [casesOn]
  have :
    (fun t Γ (h : Erased.out Ctxt.empty = t :: Γ) => 
      cast (casesOn.proof_2 (motive := motive) Ctxt.empty t Γ h) (snoc (Erased.mk Γ) t))
    = (fun _ _ _ => empty) := by 
      funext _ _ h
      simp[Ctxt.empty] at h
  simp only [this, cast_eq]
  simp only [Ctxt.empty]
  rw [Erased.out_mk]

@[simp]
theorem casesOn_snoc {motive : Ctxt → Sort u} (empty : motive .empty) 
    (snoc : (Γ : Ctxt) → (t : Ty) → motive (snoc Γ t)) : 
    casesOn (Ctxt.snoc Γ t) empty snoc = (snoc Γ t) := by
  simp only [casesOn]
  have :  
      (fun (h : Erased.out (Ctxt.snoc Γ t) = []) => 
        cast (casesOn.proof_1 (Ctxt.snoc Γ t) h) empty)
      = (fun _ => snoc Γ t) := by 
    funext h
    simp[Ctxt.snoc] at h
  rw [this]
  have :
      (fun t' Γ' h =>
        cast (casesOn.proof_2 (motive := motive) (Ctxt.snoc Γ t) t' Γ' h) (snoc (Erased.mk Γ') t'))
      = (fun _ _ _ => snoc Γ t) := by
    funext t' Γ' h
    unfold casesOn.proof_2
    dsimp [Ctxt.snoc] at h
    simp at h
    rcases h with ⟨h₁, h₂⟩
    cases h₁
    have : Γ = Erased.mk Γ' := by rw[←h₂]; simp
    cases this
    simp
  rw [this]
  simp [Ctxt.snoc]
  rw [Erased.out_mk]
  
  


  -- suffices ∀ Γ, (h : Γ = .empty) → casesOn Γ empty snoc = cast (by rw[←h]) empty
  --   from this .empty rfl
  -- intro Γ h
  -- have : Γ.out = [] := by simp[h, Ctxt.empty]



-- def append : Ctxt → Ctxt → Ctxt :=
--   fun xs ys => do return List.append (← ys) (← xs)


-- theorem append_empty (Γ : Ctxt) : append Γ ∅ = Γ := by
--   simp[append, EmptyCollection.emptyCollection, empty]
  

-- theorem append_snoc (Γ Γ' : Ctxt) (t : Ty) : 
--     append Γ (Ctxt.snoc Γ' t) = (append Γ Γ').snoc t := by
--   simp[append, snoc]

-- @[simp]
-- theorem _root_.List.get?_append_add :
--     List.get? (xs ++ ys) (i + xs.length) = List.get? ys i := by
--   induction xs
--   . rfl
--   . simp_all

-- def Var.inl {Γ Γ' : Ctxt} {t : Ty} : Var Γ t → Var (Ctxt.append Γ Γ') t
--   | ⟨v, h⟩ => ⟨v + Γ'.length, by simp[←h, append, List.get?_append_add]⟩

-- def Var.inr {Γ Γ' : Ctxt} {t : Ty} : Var Γ' t → Var (append Γ Γ') t
--   | ⟨v, h⟩ => ⟨v, by 
--       simp[append]
--       induction Γ' generalizing v
--       case nil =>
--         contradiction
--       case cons ih =>
--         cases v
--         case zero =>
--           rw[←h]; rfl
--         case succ v =>
--           apply ih v h
--     ⟩

-- end Append

/-- Drop the last `n` types from a context `Γ`.
    The context must have at least `n` types, otherwise `none` is returned -/
noncomputable def drop (n : Nat) (Γ : Ctxt) : Option Ctxt :=
  match n with 
    | 0   => Γ
    | n+1 => Γ.casesOn none fun Γ _ => drop n Γ  
  

@[simp]
theorem drop_zero (Γ : Ctxt) : drop 0 Γ = some Γ := by
  simp [drop]

@[simp]
theorem drop_succ_snoc (n : ℕ) (Γ : Ctxt) (t : Ty) : drop (n+1) (snoc Γ t) = drop n Γ := by
  simp [drop]
  

@[simp]
theorem drop_succ_empty (n : ℕ) : drop (n+1) .empty = none := by
  simp [drop]


theorem drop_drop {Δ : Ctxt} {n : ℕ} (Γ : Ctxt) (m : Nat) :
    Γ.drop m = Δ → Δ.drop n = Γ.drop (n+m) := by
  intro h
  induction m generalizing Γ
  case zero =>
    simp at h
    simp [h]

  case succ m ih =>
    cases Γ using Ctxt.casesOn <;> simp at h
    next Γ t =>
      show drop n Δ = drop ((n + m) + 1) (snoc Γ t)
      simp at h
      rw [drop_succ_snoc, ih _ h]


abbrev NonEmpty : Ctxt → Prop := fun Γ => (Γ.drop 1).isSome

/-- If a context contains a variable, it is not empty -/
@[coe]
def NonEmpty.ofVar {Γ : Ctxt} : Γ.Var t → Γ.NonEmpty := by
  cases Γ
  next => exact Var.emptyElim
  next => simp[NonEmpty]

/--
  The head of a non-empty context is the type of the most recently added variable
-/
noncomputable def head (Γ : Ctxt) (h : Γ.NonEmpty) : Ty := by
  cases Γ
  next => simp[NonEmpty] at h
  next _ t => exact t

/--
  The tail of a context is similar to `drop 1`, except that the tail of an empty context is defined
  to be the empty context again, so that `tail` is total instead of partial
-/
noncomputable def tail (Γ : Ctxt) : Ctxt :=
  Γ.casesOn .empty (fun Γ _ => Γ)

/--
  If the tail of a context is non-empty, the full-context is clearly also non-empty
-/
def NonEmpty.ofTail : NonEmpty (tail Γ) → NonEmpty Γ := by
  simp[NonEmpty, tail]
  cases Γ <;> simp

@[simp]
theorem tail_snoc : tail (snoc Γ t) = Γ := by
  simp[tail]

@[simp]
theorem snoc_tail_head (Γ : Ctxt) (h : NonEmpty Γ) :
    snoc (tail Γ) (head Γ h) = Γ := by
  simp[tail, head]
  cases Γ
  . simp[NonEmpty] at h
  . simp

/-- This theorem proves that `tail` and `drop 1` coincide on non-empty contexts -/
theorem tail_eq_drop_one {Γ Δ : Ctxt} (h : Γ.drop 1 = some Δ) : Γ.tail = Δ := by
  simp [drop] at h
  simp [tail]
  cases Γ <;> simp at h
  next => simp[h]




namespace Var

/-- Every variable in the tail of `Γ` is again a variable in `Γ` -/
@[coe]
def ofTail : Var (tail Γ) t → Var Γ t :=
  fun v => 
    cast (by 
      cases Γ
      next => 
        simp[tail] at v
        exact emptyElim v
      next =>
        simp[tail, head]
    ) <| v.toSnoc (t' := Γ.head (.ofTail <| .ofVar v))

-- def casesOnNe 
--     {motive : (Γ : Ctxt) → Ctxt.Var Γ t → NonEmpty Γ → Sort _}
--     {Γ : Ctxt} {t : Ty} (v : Γ.Var t) (NonEmpty Γ)
--     (base : {t : Ty} → 
--         {Γ : Ctxt} → (v : Γ.tail.Var t) → (h : NonEmpty Γ) → motive Γ t v.toSnoc)
--     (last : {Γ : Ctxt} → {t : Ty} → motive Γ t (Ctxt.Var.last _ _)) :
--       motive Γ t t' v :=

-- /--
--   If a variable `v` in context `Γ` is `last`, return `none`
--   Otherwise, returns `v` embedded in the context `Γ.tail`
-- -/
-- def tryEmbedTail {Γ : Ctxt} (v : Var Γ t) : Option (Var Γ.tail t) := by
--   have ne : NonEmpty Γ := sorry -- NonEmpty.ofVar v
--   let v : Var (snoc (tail Γ) (head Γ ne)) t := cast (by simp) v
--   cases v using Var.casesOn
--   next => exact none
--   next => exact none

end Var
  


  



/-- Given a change of variables map from `Γ` to `Γ'`, extend it to 
a map `Γ.snoc t` to `Γ'.snoc t` -/
@[simp] 
def Var.snocMap {Γ Γ' : Ctxt} {t : Ty}
    (f : (t : Ty) → Γ.Var t → Γ'.Var t) :
    (t' : Ty) → (Γ.snoc t).Var t' → (Γ'.snoc t).Var t' :=
  fun _ v => Ctxt.Var.casesOn v (fun v f => (f _ v).toSnoc) 
    (fun _ => Ctxt.Var.last _ _) f




namespace Var

protected def isHeq {Γ : Ctxt} (v₁ : Γ.Var t₁) (v₂ : Γ.Var t₂) : Bool :=
  if h : t₂ = t₁ then
    v₁ = cast (by congr) v₂
  else
    false

-- theorem isHeq_lawful : Var.isHeq v₁ v₂ ↔ HEq v₁ v₂ := by
--   simp[Var.isHeq]
--   split_ifs
--   next h =>
--     cases h
--     simp[cast_eq]
--     constructor
--     . exact of_decide_eq_true 
--     . exact decide_eq_true
--   . constructor
--     . apply False.elim
--     . intro h
--       have type_eq := type_eq_of_heq h
--       simp [Var] at type_eq
      

end Var

end Ctxt