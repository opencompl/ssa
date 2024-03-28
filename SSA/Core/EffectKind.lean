/- Kinds of effects, either pure or impure -/
inductive EffectKind
| pure -- pure effects.
| impure -- impure, lives in IO.
deriving Repr, DecidableEq

namespace EffectKind

@[reducible]
def toMonad (e : EffectKind) (m : Type → Type) : Type → Type :=
  match e with
  | pure => Id
  | impure => m

section Lemmas

@[simp] theorem toMonad_pure    : pure.toMonad m = Id := rfl
@[simp] theorem toMonad_impure  : impure.toMonad m = m := rfl

end Lemmas

section Instances
variable {e : EffectKind} {m : Type → Type}

/-!
NOTE: The `Monad` instance below also implies `Functor`, `Applicative`, etc.
If `m` is a `Functor`, but not a full `Monad`, then `e.toMonad m` should still be a functor too.
However, actually having these instances causes diamond problems with the aforementioned instances
implied by `Monad`. Thus, we just assume `m` is always a monad.
-/

instance [Monad m] : Monad (e.toMonad m) := by cases e <;> infer_instance
instance [Monad m] [LawfulMonad m] : LawfulMonad (e.toMonad m) := by cases e <;> infer_instance

end Instances

--TODO: rename `return` to `pure`
def «return» [Monad m] (e : EffectKind) (a : α) : e.toMonad m α := return a

@[simp] -- return is normal form.
def return_eq [Monad m] (e : EffectKind) (a : α) : e.return a = (return a : e.toMonad m α) := by rfl

@[simp]
def return_pure_toMonad_eq (a : α) : (return a : pure.toMonad m α) = a := rfl

@[simp]
def return_impure_toMonad_eq [Monad m] (a : α) : (return a : impure.toMonad m α) = (return a : m α) := rfl

inductive le : EffectKind → EffectKind → Prop
  | pure_le (e) : le .pure e
  | le_impure (e) : le e .impure

@[simp]
def decLe (e e' : EffectKind) : Decidable (le e e') :=
  match e with
  | .pure => match e' with
    | .pure => isTrue (by constructor)
    | .impure => isTrue (by constructor)
  | .impure => match e' with
    | .pure => isFalse (by intro; contradiction)
    | .impure => isTrue (by constructor)


instance : LE EffectKind where le := le
instance : DecidableRel (LE.le (α := EffectKind)) := decLe

@[simp]
theorem eq_of_le_pure {e : EffectKind}
    (he : e ≤ pure) : e = pure := by
  cases he; rfl


@[simp] theorem not_impure_le_pure : ¬(impure ≤ pure) := by
  intro; contradiction

@[simp] theorem pure_le (e : EffectKind) : pure ≤ e := le.pure_le e
@[simp] theorem le_impure (e : EffectKind) : e ≤ impure := le.le_impure e

@[simp] theorem le_refl (e : EffectKind) : e ≤ e := by cases e <;> constructor

@[simp]
theorem le_trans {e1 e2 e3 : EffectKind} (h12: e1 ≤ e2) (h23: e2 ≤ e3) : e1 ≤ e3 := by
  cases e1 <;> cases e2 <;> cases e3 <;> simp_all

@[simp]
theorem le_antisym {e1 e2 : EffectKind} (h12: e1 ≤ e2) (h21: e2 ≤ e1) : e1 ≤ e2 := by
  cases e1 <;> cases e2 <;> simp_all

theorem le_of_eq {e1 e2 : EffectKind} (h : e1 = e2) : e1 ≤ e2 := by
  subst h
  cases e1 <;> simp

def union : EffectKind → EffectKind → EffectKind
| .pure, .pure => .pure
| _, _ => .impure

@[simp] theorem pure_union_pure_eq : union .pure .pure = .pure := rfl
@[simp] theorem impure_union_eq : union .impure e = .impure := rfl
@[simp] theorem union_impure_eq : union e .impure = .impure := by cases e <;> rfl

/-!
## `liftEffect`
-/

/-- Lift a value wrapped in effect `e1` into effect `e2`, given that `e1 ≤ e2`.

Said differently, this is a functor from the category of EffectKind (with `e1 ≤ e2` as its arrows)
to Lean (with `e1.toMonad x → e2.toMonad x` as its arrows). -/
def liftEffect [Monad m] {e1 e2 : EffectKind} {α : Type}
    (hle : e1 ≤ e2) (v1 : e1.toMonad m α) : e2.toMonad m α :=
  match e1, e2, hle with
    | .pure, .pure, _ | .impure, .impure, _ => v1
    | .pure, .impure, _ => return v1

instance instMonadLiftOfLe {e1 e2 : EffectKind} (h : e1 ≤ e2) [Monad m] :
    MonadLiftT (e1.toMonad m) (e2.toMonad m) where
  monadLift := liftEffect h

instance (eff : EffectKind) {m} [Monad m] : MonadLiftT (eff.toMonad m) m :=
  instMonadLiftOfLe (le_impure eff)

@[simp] theorem liftEffect_rfl [Monad m] (hle : eff ≤ eff) :
    liftEffect hle (α := α) (m := m) = id := by cases eff <;> rfl

@[deprecated liftEffect_rfl]
theorem liftEffect_pure_pure [Monad m] (hle : pure ≤ pure) :
    liftEffect hle (α := α) (m := m) = id :=
  rfl

@[simp] theorem liftEffect_pure_impure [Monad m] (hle : pure ≤ impure) :
    liftEffect hle (α := α) (m := m) = Pure.pure :=
  rfl

/-- Forded version of `liftEffect_pure_impure` -/
theorem liftEffect_eq_pure_cast {m : Type → Type} [Monad m]
    {eff : EffectKind} (eff_eq : eff = .pure) (eff_le : eff ≤ .impure) :
    liftEffect eff_le = fun (x : eff.toMonad m α) =>
      Pure.pure (cast (by rw [eff_eq]; rfl) x) := by
  subst eff_eq; rfl

@[deprecated liftEffect_rfl]
theorem liftEffect_impure_impure [Monad m] (hle : impure ≤ impure) :
    liftEffect hle (α := α) (m := m) = id :=
  rfl

@[simp] theorem liftEffect_pure [Monad m] {e} (hle : e ≤ pure) :
    liftEffect hle (α := α) (m := m) = cast (by rw [eq_of_le_pure hle]) := by
  cases hle; rfl

@[simp] theorem liftEffect_impure [Monad m] {e} (hle : e ≤ impure) :
    liftEffect hle (α := α) (m := m) = match e with
      | .pure => fun v => return v
      | .impure => id := by
  cases e <;> rfl

/-- toMonad is functorial: it preserves identity. -/
@[simp]
theorem liftEffect_eq_id (hle : eff ≤ eff) [Monad m] :
    liftEffect hle (α := α) (m := m) = id  := by
  cases eff <;> rfl

/-- toMonad is functorial: it preserves composition. -/
def liftEffect_compose {e1 e2 e3 : EffectKind} {α : Type} [Monad m]
    (h12 : e1 ≤ e2)
    (h23 : e2 ≤ e3)
    (h13 : e1 ≤ e3 := le_trans h12 h23) :
    ((liftEffect (α := α) h23) ∘ (liftEffect h12)) = liftEffect (m := m) h13 := by
  cases e1 <;> cases e2 <;> cases e3 <;> (solve | rfl | contradiction)
