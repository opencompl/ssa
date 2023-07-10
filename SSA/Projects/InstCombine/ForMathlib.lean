import Mathlib.Data.Vector
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Basic
import SSA.Projects.InstCombine.CommRing -- copy-pasted for sorry

namespace Vector

instance {α : Type u} {n : Nat} : GetElem (Vector α n) (Fin n) α (fun _ _ => True) where
  getElem := fun v i _ => v.1[i.val]

@[simp]
theorem getElem_eq_get {α : Type u} {n : Nat} (v : Vector α n) (i : Fin n) : v[i] = v.get i := rfl

end Vector

namespace Bitvec

def width : Bitvec n → Nat := fun _ => n

-- Shouldn't this be inferred from the instance above? (as Bitvec is @[reducible])
instance {n : Nat} : GetElem (Bitvec n) (Fin n) Bool (fun _ _ => True) where
  getElem := fun v i _ => v.1[i.val]

instance (n : Nat) : Inhabited (Bitvec n) :=
  ⟨List.replicate n true, by apply List.length_replicate⟩

def Fun (width : Nat) := Fin width → Bool

/-- convert `Bitvec n` to `Fin n → Bool` -/
def ofFun {width : Nat} : Fun width → Bitvec width :=
  Vector.ofFn

/-- convert `Fin n → Bool` to `Bitvec n` -/
def toFun {width : Nat} : Bitvec width → Fun width :=
    Vector.get

instance {width : Nat} : Coe (Fun width) (Bitvec width) := ⟨@ofFun width⟩
instance {width : Nat} : Coe (Bitvec width) (Fun width) := ⟨@toFun width⟩

def ofVector : Vector Bool n → Bitvec n := id

-- inspired by: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Defining.20my.20own.20numerals
-- not ideal solution, as hard to type, but should be ok for now
prefix:max "𝟶"   => fun v => ofVector (Vector.cons false v)
prefix:max "𝟷"   => fun v => ofVector (Vector.cons true v)
notation:max "𝟶"   => ofVector (Vector.cons false (@Vector.nil Bool))
notation:max "𝟷"   => ofVector (Vector.cons true (@Vector.nil Bool))

-- examples:
-- #eval (𝟷𝟶𝟷𝟷).toNat
-- #eval (𝟶𝟷𝟷𝟷).toNat
-- #eval (𝟶𝟷𝟷𝟷) + (𝟷𝟶𝟷𝟷) |>.toNat
-- #eval 𝟷𝟶𝟷𝟷 + 𝟶𝟷𝟷𝟷
-- #eval Bitvec.adc (𝟷𝟶𝟷𝟷) (𝟶𝟷𝟷𝟷) true
-- #eval Bitvec.adc (𝟷𝟶𝟷𝟷) (𝟶𝟷𝟷𝟷) false
-- #eval Bitvec.adc (𝟷𝟶𝟷𝟷) (𝟶𝟷𝟷𝟷) true |>.toNat
-- #eval Bitvec.adc (𝟷𝟶𝟷𝟷) (𝟶𝟷𝟷𝟷) false |>.toNat
-- 
-- #eval Bitvec.adc (𝟶) (𝟶) true
-- #eval Bitvec.adc (𝟶) (𝟶) false

-- see https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pattern.20matching.20subtypes
def add? {n : Nat} (x y : Bitvec n) : Option (Bitvec n) := match Bitvec.adc x y false with
  | ⟨false :: z,hcons⟩ => some ⟨z, by aesop⟩
  | _ => none -- overflow

theorem some_add?_eq_add {n : Nat} {x y z : Bitvec n} : add? x y = some z → x + y = z := sorry

/-
#eval  (𝟷𝟶𝟷𝟷).toNat * (𝟷𝟶𝟷𝟷).toNat
#eval  Bitvec.mul (𝟷𝟶𝟷𝟷) (𝟷𝟶𝟷𝟷) |>.toNat
-/
protected def mul? {n : Nat} (x y : Bitvec n) : Option (Bitvec n) := do
  let f r b := do 
    let op₁ ← Bitvec.add? r r 
    let op₂ ← Bitvec.add? op₁ y
    return cond b op₂ op₁
  (x.toList).foldlM f 0

/-
#eval  Bitvec.mul? (𝟷𝟶𝟷𝟷) (𝟷𝟶𝟷𝟷)
#eval  Bitvec.mul? (𝟶𝟶𝟶𝟶𝟶𝟶𝟷𝟶𝟷𝟷) (𝟶𝟶𝟶𝟶𝟶𝟶𝟷𝟶𝟷𝟷) |>.get!|>.toNat
-/
theorem mul?_some_eq_mul : ∀ {n : Nat} {x y z : Bitvec n}, Bitvec.mul? x y = some z → x * y = z := sorry

/--
The value produced is the unsigned integer quotient of the two operands.
Note that unsigned integer division and signed integer division are distinct operations; for signed integer division, use ‘sdiv’.
Division by zero is undefined behavior.
-/
def udiv? {w : Nat} (x y : Bitvec w) : Option $ Bitvec w :=
  match y.toNat with
    | 0 => none
    | _ => some $ Bitvec.ofNat w (x.toNat / y.toNat)

/--
The value produced is the signed integer quotient of the two operands rounded towards zero.
Note that signed integer division and unsigned integer division are distinct operations; for unsigned integer division, use ‘udiv’.
Division by zero is undefined behavior.
Overflow also leads to undefined behavior; this is a rare case, but can occur, for example, by doing a 32-bit division of -2147483648 by -1.
-/
def sdiv? {w : Nat} (x y : Bitvec w) : Option $ Bitvec w := 
  if y.toInt = 0 
  then none
  else 
    let div := (x.toInt / y.toInt)
    if div < 2^w 
      then some $ Bitvec.ofInt w div
      else none

/--
This instruction returns the unsigned integer remainder of a division. This instruction always performs an unsigned division to get the remainder.
Note that unsigned integer remainder and signed integer remainder are distinct operations; for signed integer remainder, use ‘srem’.
Taking the remainder of a division by zero is undefined behavior. 
-/
def urem? {w : Nat} (x y : Bitvec w) : Option $ Bitvec w :=
  if y.toNat = 0 
  then none
  else some $ Bitvec.ofNat w (x.toNat % y.toNat)

def _root_.Int.rem (x y : Int) : Int :=
  if x ≥ 0 then (x % y) else ((x % y) - |y|)

-- TODO: prove this to make sure it's the right implementation!
theorem _root_.Int.rem_sign_dividend : 
  ∀ x y, Int.rem x y < 0 ↔ x < 0 :=  by sorry

/--
This instruction returns the remainder of a division (where the result is either zero or has the same sign as the dividend, op1), 
not the modulo operator (where the result is either zero or has the same sign as the divisor, op2) of a value.
For more information about the difference, see The Math Forum.
For a table of how this is implemented in various languages, please see Wikipedia: modulo operation.
Note that signed integer remainder and unsigned integer remainder are distinct operations; for unsigned integer remainder, use ‘urem’.
Taking the remainder of a division by zero is undefined behavior.
For vectors, if any element of the divisor is zero, the operation has undefined behavior.
Overflow also leads to undefined behavior; this is a rare case, but can occur, for example,
by taking the remainder of a 32-bit division of -2147483648 by -1.
(The remainder doesn’t actually overflow, but this rule lets srem be implemented using instructions that return both the result
of the division and the remainder.)
-/
def srem? {w : Nat} (x y : Bitvec w) : Option $ Bitvec w :=
  if y.toInt = 0 
  then none
  else
    let div := (x.toInt / y.toInt)
    if div < 2^w 
      then some $ Bitvec.ofInt w (x.toInt.rem y.toInt)
      else none

/--
 If the condition is an i1 and it evaluates to 1, the instruction returns the first value argument; otherwise, it returns the second value argument.
-/
def select {w : Nat} (c : Bitvec 1) (x y : Bitvec w) : Bitvec w :=
  cond c.head x y

theorem bitwise_eq_eq {w : Nat} {x y : Bitvec w} :
    (forall i : Fin w, x[i] = y[i]) ↔ x = y :=
  ⟨Vector.ext, fun h _ => h ▸ rfl⟩ 

theorem ext_get? {w : Nat} {x y : Bitvec w} (h : ∀ i, x.toList.get? i = y.toList.get? i) : x = y := by
  rcases x with ⟨x, rfl⟩
  rcases y with ⟨y, hy⟩
  exact Vector.toList_injective $ List.ext h

@[simp]
theorem toList_cong {w₁ w₂ : Nat} (h : w₁ = w₂) (b : Bitvec w₁) : (Bitvec.cong h b).toList = b.toList := 
  by subst h; rfl

theorem get?_shl (x : Bitvec n) (i j : ℕ) : 
    (x.shl i).toList.get? j = 
      if i + j < n 
      then x.toList.get? (i + j) 
      else if j < n then false
      else none := by
  unfold shl
  rcases x with ⟨x, rfl⟩
  simp only [toList_cong, Vector.toList_append, Vector.toList_drop, Vector.toList_mk, Bool.forall_bool,
    add_eq_zero, and_imp, Vector.replicate]
  split_ifs with h₁ h₂
  { rw [List.get?_append, List.get?_drop]
    . rw [List.length_drop]
      exact Nat.lt_sub_of_add_lt (add_comm i j ▸ h₁) }
  { rw [List.get?_append_right, List.get?_eq_get, List.get_replicate]
    . exact Nat.sub_lt_left_of_lt_add (by simpa [add_comm] using h₁) (by simpa)
    . simpa [add_comm] using h₁ }
  { rw [List.get?_eq_none]
    simpa using h₂ }
  
theorem get?_ushr (x : Bitvec n) (i j : ℕ) : 
    (x.ushr i).toList.get? j = 
      if j < x.length
      then if j < i
        then some false
        else x.toList.get? (j - i)
      else none := by
  unfold ushr
  rcases x with ⟨x, rfl⟩
  simp only [fillShr, Vector.replicate, ge_iff_le, toList_cong, Vector.toList_append, 
    Vector.toList_mk, Vector.toList_take, Bool.forall_bool, tsub_eq_zero_iff_le]
  split_ifs with h₁ h₂
  { rw [List.get?_append, List.get?_eq_get, List.get_replicate]
    . simp [*] at *
    . simp [*] at * }
  { have : i < x.length := lt_of_le_of_lt (le_of_not_lt h₂) h₁
    rw [min_eq_right (le_of_lt this), List.get?_append_right, List.get?_take]
    simp
    . exact Nat.sub_lt_left_of_lt_add (by simpa using h₂) 
        (by simpa [Nat.add_sub_cancel' (le_of_lt this)] using h₁)
    . simpa using h₂ }
  { rw [List.get?_eq_none]
    . rw [min_def]
      split_ifs with h
      { simpa [Nat.sub_eq_zero_of_le h] using h₁ }
      { simpa [Nat.add_sub_cancel' (le_of_not_le h)] using h₁  } }

theorem get?_and (x y : Bitvec n) (i : ℕ) : 
    (x.and y).toList.get? i = do return (← x.toList.get? i) && (← y.toList.get? i) := by
  rcases x with ⟨x, rfl⟩
  rcases y with ⟨y, hy⟩
  simp [Bitvec.and, Vector.map₂, List.get?_zip_with]
  cases (List.get? x i) <;> cases (List.get? y i) <;> simp [bind, pure]

theorem match_does_not_fold_away : List.get ((Bitvec.ofInt w (-1)).toList) i = true := by
  rw [← Option.some_inj, ← List.get?_eq_get]
  simp [ofNat_zero, Bitvec.ofInt, show -1 = Int.negSucc 0 by rfl, Bitvec.not, toList_zero]
  simp [Vector.replicate]; rw [List.get?_eq_get, List.get_replicate]
  simpa using i.2

theorem get?_ofInt_neg_one : (Bitvec.ofInt w (-1)).toList.get? i = 
    if i < w then some true else none := by
  simp only [Vector.cons, Bitvec.not, Vector.map, ofNat_zero, zero_def, List.map_replicate, Bool.not_false,
    Vector.toList_mk, List.cons.injEq, and_imp, forall_apply_eq_imp_iff', forall_eq']
  split_ifs with h
  { rw [List.get?_eq_get]; simp [match_does_not_fold_away]; simp; assumption }
  { rw [List.get?_eq_none]; simp only [Vector.toList_length]; linarith }

-- from InstCombine/Shift:279
theorem shl_ushr_eq_and_shl {w : Nat} {x C : Bitvec w} :
    Bitvec.shl (Bitvec.ushr x C.toNat) C.toNat = Bitvec.and x (Bitvec.shl (Bitvec.ofInt w (-1)) C.toNat) := by
  apply ext_get?
  intro i
  rw [get?_shl, get?_ushr, get?_and]
  simp only [pure, bind, Nat.lt_succ_iff, get?_ofInt_neg_one, get?_shl, Vector.length]
  simp only [add_lt_iff_neg_left, not_lt_zero', ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
    add_tsub_cancel_left, Bool.forall_bool, ite_false]
  split_ifs with h₁ h₂
  { simp only [Bool.forall_bool, Option.some_bind, Bool.and_true, Option.bind_some] }
  { rw [List.get?_eq_get] <;> simp [Nat.lt_succ_iff, *] }
  { rw [List.get?_eq_none.2] <;> simp [Nat.succ_le_iff, not_le, *] at *; assumption }

-- A lot of this should probably go to a differet file here and not Mathlib
inductive Refinement {α : Type u} : Option α → Option α → Prop
  | bothSome {x y : α } : x = y → Refinement (some x) (some y)
  | noneAny {x? : Option α} : Refinement none x?

theorem Refinement.some_some {α : Type u} {x y : α} :
  Refinement (some x) (some y) ↔ x = y :=
  ⟨by intro h; cases h; assumption, Refinement.bothSome⟩

namespace Refinement

theorem Refinement.refl {α: Type u} : ∀ x : Option α, Refinement x x := by 
  intro x ; cases x
  apply Refinement.noneAny
  apply Refinement.bothSome; rfl

theorem Refinement.trans {α : Type u} : ∀ x y z : Option α, Refinement x y → Refinement y z → Refinement x z := by
  intro x y z h₁ h₂
  cases h₁ <;> cases h₂ <;> try { apply Refinement.noneAny } ; try {apply Refinement.bothSome; assumption}
  rename_i x y hxy y h 
  rw [hxy, h]; apply Refinement.refl

instance {α : Type u} [DecidableEq α] : DecidableRel (@Refinement α) := by
  intro x y
  cases x <;> cases y
  { apply isTrue; exact Refinement.noneAny}
  { apply isTrue; exact Refinement.noneAny }
  { apply isFalse; intro h; cases h }
  { rename_i val val'
    cases (decEq val val')
    { apply isFalse; intro h; cases h; contradiction } 
    { apply isTrue; apply Refinement.bothSome; assumption }
  }

end Refinement

infix:50 " ⊑ " => Refinement

instance {w : Nat} : DecidableEq (Bitvec w) := inferInstance

theorem toInt_injective : ∀ {w : Nat}, Function.Injective (Bitvec.toInt : Bitvec w → ℤ)
  | 0, ⟨[], _⟩, ⟨[], _⟩, rfl => rfl
  | n+1, ⟨a::x, hx⟩, ⟨b::y, hy⟩, h => by
      dsimp [Bitvec.toInt, Vector.head] at h
      apply Vector.toList_injective
      cases a <;> cases b
      { simp [Vector.tail] at h
        apply_fun Vector.toList ∘ Bitvec.ofNat n at h
        simpa [Bitvec.ofNat_toNat, Vector.toList_injective.eq_iff] using h }
      { simp at h }
      { simp at h }
      { simp [Vector.tail] at h
        apply_fun Vector.toList ∘ Bitvec.ofNat n at h
        simpa [Bitvec.ofNat_toNat, Vector.toList_injective.eq_iff, Bitvec.not,
          (List.map_injective_iff.2 _).eq_iff] using h }

theorem toInt_zero {w : Nat} : (0 : Bitvec w).toInt = 0 := by
  simp [Bitvec.toInt]
  cases' w with w
  . rfl
  . have : Vector.head (0 : Bitvec (w + 1)) = false := rfl
    have : Vector.tail (0 : Bitvec (w + 1)) = 0 := rfl
    simp [*]

@[simp]
theorem toInt_eq_zero {w : Nat} (b : Bitvec w) : b.toInt = 0 ↔ b = 0 := by
  rw [← toInt_injective.eq_iff, toInt_zero]

theorem toInt_one : ∀ {w : ℕ} (_hw : 1 < w), Bitvec.toInt (1 : Bitvec w) = 1 
  | w+2, _ => by 
    have : Vector.head (1 : Bitvec (w+2)) = false := rfl
    have : Vector.tail (1 : Bitvec (w+2)) = 1 := rfl
    simp [*, Bitvec.toInt, Bitvec.toNat_one]

-- from InstCombine/:805
theorem one_sdiv_eq_add_cmp_select_some {w : Nat} {x : Bitvec w} (hw : w > 1) (hx : x ≠ 0) :
  Bitvec.sdiv? 1 x = Option.some (Bitvec.select 
    (((x + 1).toNat < 3) ::ᵥ Vector.nil) x 0) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw  
  simp only [sdiv?, toInt_eq_zero, hx, ite_false, Option.map_some', 
    select, Vector.head, toNat_add, toNat_one,
    if_neg hw0, Bool.cond_decide, Option.some.injEq, toInt_one hw]
  admit

theorem one_sdiv_ref_add_cmp_select :
  (Bitvec.sdiv? (Bitvec.ofInt w 1) x) ⊑ 
  Option.some (Bitvec.select ((Nat.blt (Bitvec.add x (Bitvec.ofNat w 1)).toNat (Bitvec.ofNat w 3).toNat) ::ᵥ Vector.nil)  x (Bitvec.ofNat w 0)) :=
  sorry

def beq {w : Nat} (x y : Bitvec w) : Bool := x = y

def ofBool : Bool → Bitvec 1 := fun b => b ::ᵥ Vector.nil

def toBool : Bitvec 1 → Bool 
  | b ::ᵥ Vector.nil => b

theorem ofBool_toBool : ∀ b : Bool, toBool (ofBool b) = b := by simp only [ofBool, toBool]
theorem toBool_ofBool : ∀ b : Bitvec 1, ofBool (toBool b) = b := by simp only [ofBool, toBool]

instance : Coe Bool (Bitvec 1) := ⟨ofBool⟩


instance : Coe (Bitvec 1) Bool := ⟨toBool⟩

instance decPropToBitvec1 (p : Prop) [Decidable p] : CoeDep Prop p (Bitvec 1) where
  coe := ofBool $ decide p


infixl:75 ">>>ₛ" => fun x y => Bitvec.sshr x (Bitvec.toNat y)

def ult (x y : Bitvec w) : Prop := x.toNat < y.toNat
def ule (x y : Bitvec w) : Prop := x.toNat ≤ y.toNat
def ugt (x y : Bitvec w) : Prop := x.toNat > y.toNat
def uge (x y : Bitvec w) : Prop := x.toNat ≥ y.toNat

instance {w : Nat} (x y : Bitvec w) : Decidable (ult x y) := by apply Nat.decLt
instance {w : Nat} (x y : Bitvec w) : Decidable (ule x y) := by apply Nat.decLe
instance {w : Nat} (x y : Bitvec w) : Decidable (ugt x y) := by apply Nat.decLt
instance {w : Nat} (x y : Bitvec w) : Decidable (uge x y) := by apply Nat.decLe

def slt (x y : Bitvec w) : Prop := x.toInt < y.toInt
def sle (x y : Bitvec w) : Prop := x.toInt ≤ y.toInt
def sgt (x y : Bitvec w) : Prop := x.toInt > y.toInt
def sge (x y : Bitvec w) : Prop := x.toInt ≥ y.toInt

instance {w : Nat} (x y : Bitvec w) : Decidable (slt x y) := by apply Int.decLt
instance {w : Nat} (x y : Bitvec w) : Decidable (sle x y) := by apply Int.decLe
instance {w : Nat} (x y : Bitvec w) : Decidable (sgt x y) := by apply Int.decLt
instance {w : Nat} (x y : Bitvec w) : Decidable (sge x y) := by apply Int.decLe

notation:50 x " ≤ᵤ " y  => ofBool (decide (ult x y))
notation:50 x " <ᵤ " y => ofBool  (decide (ule x y))
notation:50 x " ≥ᵤ " y => ofBool  (decide (uge x y))
notation:50 x " >ᵤ " y => ofBool  (decide (ugt x y))

notation:50 x " ≤ₛ " y => ofBool  (decide (slt x y))
notation:50 x " <ₛ " y => ofBool  (decide (sle x y))
notation:50 x " ≥ₛ " y => ofBool  (decide (sge x y))
notation:50 x " >ₛ " y => ofBool (decide ( sgt x y))

end Bitvec
