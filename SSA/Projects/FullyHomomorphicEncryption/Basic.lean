/-
This file contains the definition of the MLIR `Poly` dialect as implemented in HEIR, see:
https://github.com/google/heir/blob/a18d4e8ddc0031e2a0e6dd2dd0d7fe289b9d1651/include/Dialect/Poly/IR/PolyDialect.td
https://github.com/j2kun/heir/blob/5c5c0e2ff2ae37a7d1ec5791ec6c38046c4115c1/include/Dialect/Poly/IR/PolyOps.td
https://github.com/google/heir/blob/a18d4e8ddc0031e2a0e6dd2dd0d7fe289b9d1651/tests/poly/poly_ops.mlir

This dialect describes operations on equivalence classes of polynomials in ℤ/qℤ[X]/(X^(2^n) + 1).
For the rationale behind this, see:
 Junfeng Fan and Frederik Vercauteren, Somewhat Practical Fully Homomorphic Encryption
https://eprint.iacr.org/2012/144

-/
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.List.Basic
import Mathlib.Data.Polynomial.RingDivision
import SSA.Core.Framework

open Polynomial -- for R[X] notation

/-
We assume that `q > 1` is a natural number (not necessarily a prime) and `n` is a natural number.
We will use these to build `ℤ/qℤ[X]/(X^(2^n) + 1)`
-/
variable (q t : Nat) [ hqgt1 : Fact (q > 1)] (n : Nat)

-- Can we make this computable?
-- see: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Way.20to.20recover.20computability.3F/near/322382109
-- and :https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Groebner.20bases

-- Question: Can we make something like d := 2^n work as a macro?

noncomputable def f : (ZMod q)[X] := X^(2^n) + 1

-- theorem zmodq_eq_finq : ZMod q = Fin q := by
--   have h : q > 1 := hqgt1.elim
--   unfold ZMod
--   cases q
--   · exfalso
--     apply Nat.not_lt_zero 1
--     exact h
--   · simp [Fin]
--   done

def ZMod.toInt (x : ZMod q) : Int := ZMod.cast x
def ZMod.toFin (x : ZMod q) : Fin q := ZMod.cast x

@[simp]
theorem ZMod.toInt_inj {x y : ZMod q} : x.toInt = y.toInt ↔ x = y := by
  constructor
  · intro h
    simp [toInt] at h
    apply ZMod.val_injective
    rw[ZMod.cast_eq_val] at h
    rw[ZMod.cast_eq_val] at h
    norm_cast at h
  · intro h
    rw [h]

def ZMod.toInt_zero_iff_zero (x : ZMod q) : x = 0 ↔ x.toInt = 0 := by
  constructor
  · intro h
    rw [h]
    simp [toInt]
  · intro h
    have h0 : ZMod.toInt q 0 = (0 : Int) := by simp [ZMod.toInt]
    rw [← h0] at h
    apply (ZMod.toInt_inj q).1
    assumption

instance : Nontrivial (ZMod q) where
  exists_pair_ne := by
    exists 0
    exists 1
    norm_num

/-- Charaterizing `f`: `f` has degree `2^n` -/
theorem f_deg_eq : (f q n).degree = 2^n := by
  simp [f]
  rw [Polynomial.degree_add_eq_left_of_degree_lt]
  <;> rw [Polynomial.degree_X_pow]
  simp
  simp [Polynomial.degree_one]
  simp [Preorder.toLT, WithBot.preorder, OfNat.ofNat]
  simp [Zero.zero, WithTop.coe_zero, WithTop.coe_one, One.one]
  norm_cast
  exact Fin.size_pos'

/-- Charaterizing `f`: `f` is monic -/
theorem f_monic : Monic (f q n) := by
  have hn : 2^n = (2^n - 1) + 1 := by rw [Nat.sub_add_cancel (@Nat.one_le_two_pow n)]
  rw [f, hn]
  apply Polynomial.monic_X_pow_add
  simp

notation "(" v ")_" I => Ideal.span I v
notation r "∔" I => (Ideal.Quotient.mk I) r
/--
The basic ring of interest in this dialect is `R q n` which corresponds to
the ring `ℤ/qℤ[X]/(X^(2^n) + 1)`.
-/
abbrev R := (ZMod q)[X] ⧸ (Ideal.span {f q n})
-- Coefficients of `a : R' q n` are `a\_i : Zmod q`.
-- TODO: get this from mathlib

/-- Canonical epimorphism / quotient map: `ZMod q[X] ->*+ R q n` -/
abbrev R.fromPoly {q n : Nat} : (ZMod q)[X] →+* R q n := Ideal.Quotient.mk (Ideal.span {f q n})

/-- fromPoly, the canonical epi from `ZMod q[X] →*+ R q n` is surjective -/
theorem R.surjective_fromPoly (q n : ℕ) : Function.Surjective (R.fromPoly (q := q) (n := n)) := by
  simp[R.fromPoly]
  apply Ideal.Quotient.mk_surjective

private noncomputable def R.representative' : R q n → (ZMod q)[X] := Function.surjInv (R.surjective_fromPoly q n)

theorem R.injective_representative' (q n : ℕ) : Function.Injective (R.representative' (q := q) (n := n)) := by
  simp[R.representative']
  apply Function.injective_surjInv

/-- A concrete version that shows that mapping into the ideal back from the representative produces the representative'
  NOTE: Lean times out if I use the abbreviation `R.fromPoly` for unclear reasons! -/
theorem R.fromPoly_representatitive' (a : R q n) : R.fromPoly (R.representative' q n a) = ↑ a := by
  simp[R.fromPoly, R.representative']
  apply Function.surjInv_eq

theorem R.fromPoly_representatitive'_toFun (a : R q n) : (R.fromPoly (q := q) (n := n)).toFun (R.representative' q n a) = ↑a := by
  apply Function.surjInv_eq

/--
The representative of `a : R q n` is the (unique) polynomial `p : ZMod q[X]` of degree `< 2^n`
 such that `R.fromPoly p = a`.
-/
noncomputable def R.representative : R q n → (ZMod q)[X] := fun x => R.representative' q n x %ₘ (f q n)

@[simp]
theorem R.fromPoly_kernel_eq_zero (x : (ZMod q)[X]) : R.fromPoly (n := n) (f q n * x) = 0 := by
   unfold fromPoly
   apply Ideal.Quotient.eq_zero_iff_mem.2
   rw [Ideal.mem_span_singleton]
   simp [Dvd.dvd]
   use x

/--
`R.representative` is in fact a representative of the equivalence class.
-/
@[simp]
theorem R.fromPoly_representative : forall a : R q n, (R.fromPoly (n:=n) (R.representative q n a)) = a := by
 intro a
 simp [R.representative]
 rw [Polynomial.modByMonic_eq_sub_mul_div _ (f_monic q n)]
 rw [RingHom.map_sub (R.fromPoly (q := q) (n:=n)) _ _]
 rw [R.fromPoly_kernel_eq_zero]
 simp
 apply Function.surjInv_eq


/--
Characterization theorem for any potential representative (in terms of ideals).
For an  `a : (ZMod q)[X]`, the representative of its equivalence class
is just `a + i` for some `i ∈ (Ideal.span {f q n})`.
-/
theorem R.fromPoly_rep'_eq_ideal : forall a : (ZMod q)[X], ∃ i ∈ Ideal.span {f q n}, (R.fromPoly (n:=n) a).representative' = a + i := by
  intro a
  exists (R.fromPoly (n:=n) a).representative' - a
  constructor
  · apply Ideal.Quotient.eq.1
    simp [R.representative', Function.surjInv_eq]
  · ring
  done
/--
Characterization theorem for any potential representative (in terms of elements).
For an  `a : (ZMod q)[X]`, the representative of its equivalence class
is a concrete element of the form `a + k * (f q n)` for some `k ∈ (ZMod q)[X]`.
-/
theorem R.exists_representative_fromPoly_eq_mul_add (a : (ZMod q)[X]) : ∃ (k : (ZMod q)[X]), (R.fromPoly (n:=n) a).representative' = k * (f q n) + a := by
  have H : ∃ i ∈ Ideal.span {f q n}, (R.fromPoly (n:=n) a).representative' = a + i := by
    apply R.fromPoly_rep'_eq_ideal
  obtain ⟨i, iInIdeal, ih⟩ := H
  have fqn_div_i : (f q n) ∣ i  := by
    rw[← Ideal.mem_span_singleton]
    assumption
  have i_multiple_fqn : ∃ (k : (ZMod q)[X]), i = k * (f q n) := by
    apply dvd_iff_exists_eq_mul_left.mp
    assumption
  obtain ⟨k, hk⟩ := i_multiple_fqn
  exists k
  subst hk
  rw[ih]
  ring_nf

/-- A theorem similar to `R.fromPoly_rep'_eq_element` but uses `fromPoly.toFun` to be more deterministic,
  as the `toFun` sometimes sneaks in due to coercions. -/
theorem R.representatitive'_toFun_fromPoly_eq_element (a : (ZMod q)[X]) : ∃ (k : (ZMod q)[X]),
  R.representative' q n ((R.fromPoly (q := q) (n := n)).toFun a) = a + k * (f q n) := by
  have H : ∃ (k : (ZMod q)[X]), (R.fromPoly (n:=n) a).representative' = k * (f q n) + a := by apply
    R.exists_representative_fromPoly_eq_mul_add;
  obtain ⟨k, hk⟩ := H
  exists k
  ring_nf at hk ⊢
  rw[← hk]
  norm_cast

/-- The representative of 0 wil live in the ideal of {f q n}. To show that such an element is a multiple of {f q n}, use `Ideal.mem_span_singleton'`-/
theorem R.representative'_zero_ideal : R.representative' q n 0 ∈ Ideal.span {f q n} := by
  have H : ∃ i ∈ Ideal.span {f q n}, (R.fromPoly (n:=n) 0).representative' = 0 + i := by apply R.fromPoly_rep'_eq_ideal (a := 0)
  obtain ⟨i, hi, hi'⟩ := H
  simp[fromPoly] at hi'
  rw[hi']
  assumption

/-- The representatiatve of 0 is a multiple of `f q n`. -/
theorem R.representative'_zero_elem : ∃ (k : (ZMod q)[X]), R.representative' q n 0 = k * (f q n) := by
  have H : ∃ k : (ZMod q)[X], (R.fromPoly (n:=n) 0).representative' = k * (f q n) + 0 := by apply R.exists_representative_fromPoly_eq_mul_add (a := 0)
  obtain ⟨k, hk⟩ := H
  simp[fromPoly] at hk
  rw[hk]
  exists k

/-- Representative of (0 : R) is (0 : Z/qZ[X]) -/
theorem R.representative_zero : R.representative q n 0 = 0 := by
  simp[R.representative]
  obtain ⟨k, hk⟩ := R.representative'_zero_elem q n
  rw[hk]
  rw[dvd_iff_modByMonic_eq_zero]
  simp
  exact (f_monic q n)

/--
Characterization theorem for the representative.
Taking the representative of the equivalence class of a polynomial  `a : (ZMod q)[X]` is
the same as taking the remainder of `a` modulo `f q n`.
-/
theorem R.representative_fromPoly_toFun : forall a : (ZMod q)[X], ((R.fromPoly (n:=n) (q := q)).toFun a).representative = a %ₘ (f q n) := by
  intro a
  simp [R.representative]
  have ⟨i,⟨hiI,hi_eq⟩⟩ := R.fromPoly_rep'_eq_ideal q n a
  apply Polynomial.modByMonic_eq_of_dvd_sub (f_monic q n)
  ring_nf
  apply Ideal.mem_span_singleton.1
  rw [hi_eq]
  ring_nf
  assumption

theorem R.representative_fromPoly : forall a : (ZMod q)[X], (R.fromPoly (n:=n) a).representative = a %ₘ (f q n) := by
  intro a
  simp [R.representative]
  have ⟨i,⟨hiI,hi_eq⟩⟩ := R.fromPoly_rep'_eq_ideal q n a
  rw [hi_eq]
  apply Polynomial.modByMonic_eq_of_dvd_sub (f_monic q n)
  ring_nf
  apply Ideal.mem_span_singleton.1 hiI
  done

/-- Representative is an additive homomorphism -/
@[simp]
theorem R.representative_add [Fact (q > 1)](a b : R q n) : (a + b).representative = a.representative + b.representative := by
  have ⟨a', ha'⟩ := R.surjective_fromPoly q n a
  have ⟨b', hb'⟩ := R.surjective_fromPoly q n b
  have ⟨ab', hab'⟩ := R.surjective_fromPoly q n (a + b)
  rw[← hab']
  subst ha'
  subst hb'
  rw[← map_add] at hab'
  rw[hab']
  repeat rw[R.representative_fromPoly]
  rw[Polynomial.add_modByMonic]

/-- pushing and pulling negation through mod -/
theorem neg_modByMonic (p mod : (ZMod q)[X]) : (-p) %ₘ mod = - (p %ₘ mod) := by
    have H : -p = (-1 : ZMod q) • p := by norm_num
    have H' : - (p %ₘ mod) = (-1 : ZMod q) • (p %ₘ mod) := by norm_num
    rw[H, H']
    apply smul_modByMonic (R := (ZMod q)) (c := -1) (p := p) (q := mod)

/-- %ₘ is a subtraction homomorphism (obviously)-/
@[simp]
theorem sub_modByMonic (a b mod : (ZMod q)[X]) : (a - b) %ₘ mod = a %ₘ mod - b %ₘ mod := by
  ring_nf
  repeat rw[sub_eq_add_neg]
  simp[Polynomial.add_modByMonic]
  rw[Polynomial.neg_modByMonic]

/-- Representative is an multiplicative homomorphism upto modulo -/
@[simp]
theorem R.representative_mul [Fact (q > 1)] (a b : R q n) : (a * b).representative = (a.representative * b.representative) %ₘ (f q n) := by
  have ⟨a', ha'⟩ := R.surjective_fromPoly q n a
  have ⟨b', hb'⟩ := R.surjective_fromPoly q n b
  have ⟨ab', hab'⟩ := R.surjective_fromPoly q n (a * b)
  rw[← hab']
  subst ha'
  subst hb'
  rw[← map_mul] at hab'
  rw[hab']
  repeat rw[R.representative_fromPoly]
  -- rw[modByMonic_eq_sub_mul_div (p := a' * b') (_hq := f_monic q n)]
  rw[modByMonic_eq_sub_mul_div (p := a') (_hq := f_monic q n)]
  rw[modByMonic_eq_sub_mul_div (p := b') (_hq := f_monic q n)]
  ring_nf
  repeat rw[Polynomial.add_modByMonic]
  ring_nf
  repeat rw[sub_modByMonic]
  simp

  have H1 : (-(a' * f q n * (b' /ₘ f q n))) %ₘ f q n = 0 := by
    rw[Polynomial.dvd_iff_modByMonic_eq_zero (hq := f_monic q n)]
    rw[dvd_neg]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_right
    apply dvd_rfl
  rw[H1]
  have H2 : b' * f q n * (a' /ₘ f q n) %ₘ f q n = 0 := by
    rw[Polynomial.dvd_iff_modByMonic_eq_zero (hq := f_monic q n)]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_right
    apply dvd_rfl
  rw[H2]
  have H3 : f q n ^ 2 * (b' /ₘ f q n) * (a' /ₘ f q n) %ₘ f q n = 0 := by
    rw[Polynomial.dvd_iff_modByMonic_eq_zero (hq := f_monic q n)]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    apply dvd_pow_self
    simp
  rw[H3]
  ring

/- characterize representative', very precisely, in terms of elements -/
/-
theorem R.representative'_iff (r : R q n) (p : (ZMod q)[X]) :
  (∃ (k : (ZMod q)[X]), (R.representative' q n r) = (k * (f q n) + p)) ↔ (fromPoly (n := n) (q := q) p = r) := by
  constructor
-/

/-- Another characterization of the representative: if the degree of x is less than that of (f q n),
then we recover the same polynomial. -/
@[simp]
theorem R.representative_fromPoly_eq (x : (ZMod q)[X]) (DEGREE: x.degree < (f q n).degree) :
   R.representative q n (R.fromPoly (n:=n) x) = x := by
   simp[R.representative_fromPoly]
   rw[modByMonic_eq_self_iff] <;> simp[DEGREE, f_monic]

/--
The representative of `a : R q n` is the (unique) reperesntative with degree `< 2^n`.
-/
theorem R.rep_degree_lt_n : forall a : R q n, (R.representative q n a).degree < 2^n := by
  intro a
  simp [R.representative]
  rw [← f_deg_eq q n]
  apply Polynomial.degree_modByMonic_lt
  exact f_monic q n

/-- The representative `a : R q n` is the (unique) representative with degree less than degree of `f`. -/
theorem R.representative_degree_lt_f_degree {q n : ℕ} [Fact (q > 1)] : forall a : R q n, (R.representative q n a).degree < (f q n).degree := by
  rw[f_deg_eq (q := q)]
  intros a
  apply R.rep_degree_lt_n

noncomputable def R.repLength {q n} (a : R q n) : Nat := match
  Polynomial.degree a.representative with
    | none => 0
    | some d => d + 1

/- the repLength of any value is ≤ 1 + its natDegree. -/
theorem R.repLength_leq_representative_degree_plus_1 (a : R q n) :
  a.repLength ≤ (R.representative q n a).natDegree + 1 := by
  simp [repLength]
  generalize hdegree : degree (representative q n a) = d
  cases' d with d <;> simp[natDegree, hdegree, WithBot.unbot', WithBot.recBotCoe]



theorem R.repLength_lt_n_plus_1 : forall a : R q n, a.repLength < 2^n + 1 := by
  intro a
  simp only [R.repLength, representative]
  have : Polynomial.degree ( R.representative' q n a %ₘ f q n) < 2^n := by
    rw [← f_deg_eq q n]
    apply (Polynomial.degree_modByMonic_lt)
    apply f_monic
  simp only [LT.lt] at this
  let ⟨val, VAL, VAL_EQN⟩ := this
  rcases H : degree (R.representative' q n a %ₘ f q n) <;> simp[this]
  case some val' =>
    specialize (VAL_EQN _ H)
    norm_cast at VAL
    cases VAL
    norm_cast at VAL_EQN

/--
This function gets the `i`th coefficient of the polynomial representative
(with degree `< 2^n`) of an element `a : R q n`. Note that this is not
invariant under the choice of representative.
-/
noncomputable def R.coeff {q n} (a : R q n) (i : Nat) : ZMod q :=
  Polynomial.coeff a.representative i

/--
`R.monomial i c` is the equivalence class of the monomial `c * X^i` in `R q n`.
-/
noncomputable def R.monomial (q n : Nat) (c : ZMod q) (i : Nat): R q n :=
  R.fromPoly (Polynomial.monomial i c)

/--
Given an equivalence class of polynomials `a : R q n` with representative
`p = p_0 + p_1 X + ... + p_{2^n - 1} X^{2^n - 1}`, `R.slice a startIdx endIdx` yields
the equivalence class of the polynomial
`p_{startIdx}*X^{startIdx} + p_{startIdx + 1} X^{startIdx + 1} + ... + p_{endIdx - 1} X^{endIdx - 1}`
 Note that this is not invariant under the choice of representative.
-/
noncomputable def R.slice {q n : Nat} (a : R q n) (startIdx endIdx : Nat) : R q n :=
  let coeffIdxs := List.range (endIdx - startIdx)
  let coeffs := coeffIdxs.map (fun i => a.coeff (startIdx + i))
  let accum : R q n → (ZMod q × Nat) → R q n :=
    fun poly (c,i) => poly + R.monomial q n  c i
  coeffs.zip coeffIdxs |>.foldl accum (0 : R q n)

noncomputable def R.leadingTerm {q n} (a : R q n) : R q n :=
  let deg? := Polynomial.degree a.representative
  match deg? with
    | .none => 0
    | .some deg =>  R.monomial q n (a.coeff deg) deg

noncomputable def R.fromTensor {q n} (coeffs : List Int) : R q n :=
  coeffs.enum.foldl (init := 0) fun res (i,c) =>
    res + R.monomial q n ↑c i

/- `fromTensor (cs ++ [c])` equals `(fromTensor xs) + c X^n` -/
theorem R.fromTensor_snoc (q n : ℕ) (c : ℤ) (cs : List ℤ) : R.fromTensor (q := q) (n := n) (cs ++ [c])
  = (R.fromTensor (q := q) (n := n) cs) + R.monomial q n c cs.length := by
    induction cs using List.reverseRecOn generalizing c
    case nil =>
      simp[fromTensor]
    case append_singleton xs x _hxs =>
      simp[fromTensor]
      repeat rw[List.enum_append]
      repeat rw[List.foldl_append]
      simp[List.enumFrom]

/-- A definition of fromTensor that operates on Z/qZ[X], to provide a relationship between
    R and Z/qZ[X] as the polynomial in R is built.
-/
noncomputable def R.fromTensor' (coeffs : List Int) : (ZMod q)[X] :=
  coeffs.enum.foldl (init := 0) fun res (i,c) =>
    res + (Polynomial.monomial i ↑c)

theorem R.fromTensor_eq_fromTensor'_fromPoly_aux (coeffs : List Int) (rp : R q n) (p : (ZMod q)[X])
  (H : R.fromPoly (q := q) (n := n) p = rp) :
  ((List.enumFrom k coeffs).foldl (init := rp) fun res (i,c) =>
    res + R.monomial q n ↑c i) =
  R.fromPoly (q := q) (n := n)
    ((List.enumFrom k coeffs).foldl (init := p) fun res (i,c) =>
      res + (Polynomial.monomial i ↑c)) := by
      induction coeffs generalizing p rp k
      case nil =>
        simp[List.enum, H]
      case cons head tail tail_ih =>
        simp[List.enum_cons]
        specialize tail_ih (k := k + 1) (rp := (rp + monomial q n (↑head) k)) (p := (p + ↑(Polynomial.monomial k ↑head)))
        apply tail_ih
        simp[monomial, H]

/-- fromTensor = R.fromPoly ∘ fromTensor'.
This permits reasoning about fromTensor directly on the polynomial ring.
-/
theorem R.fromTensor_eq_fromTensor'_fromPoly {q n} : R.fromTensor (q := q) (n := n) coeffs =
  R.fromPoly (q := q) (n := n) (R.fromTensor' q coeffs) := by
    simp[fromTensor, fromTensor']
    induction coeffs
    . simp[List.enum]
    . simp[List.enum_cons]
      apply fromTensor_eq_fromTensor'_fromPoly_aux
      simp[monomial]


/-- an equivalent implementation of `fromTensor` that uses `Finsupp`
  to enable reasoning about values using mathlib's notions of
  support, coefficients, etc. -/
noncomputable def R.fromTensorFinsupp (coeffs : List ℤ) : (ZMod q)[X] :=
  Polynomial.ofFinsupp (List.toFinsupp (coeffs.map Int.cast))

theorem Polynomial.degree_toFinsupp [Semiring M] [DecidableEq M]
  (xs : List M) :
  degree { toFinsupp := List.toFinsupp (l := xs) } ≤ List.length xs := by
    cases xs
    case nil => simp [degree]
    case cons x xs =>
      simp [degree]
      simp [List.toFinsupp]
      simp [Finset.range_succ]
      apply Finset.max_le
      intros a ha
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_filter.mp ha
      have ha₃ := Finset.mem_insert.mp ha₁
      cases' ha₃ with ha₄ ha₅
      . subst ha₄
        norm_cast
        apply WithBot.coe_le_coe.mpr
        simp [Nat.cast]
      . have ha₆ := Finset.mem_range.mp ha₅
        norm_cast
        apply WithBot.coe_le_coe.mpr
        norm_cast
        simp at ha₆ ⊢
        simp [Nat.le_add_one_iff, ha₆]
        left
        apply Nat.le_of_lt ha₆

/-- degree of fromTensorFinsupp is at most the length of the coefficient list. -/
theorem R.fromTensorFinsupp_degree (coeffs : List ℤ) :
  (R.fromTensorFinsupp q coeffs).degree ≤ coeffs.length := by
  rw [fromTensorFinsupp]
  have hdeg := Polynomial.degree_toFinsupp (List.map (Int.cast (R := ZMod q)) coeffs)
  simp[List.length_map] at hdeg
  assumption

/-- the ith coefficient of fromTensorFinsupp is a coercion of the 'coeffs' into the right list. -/
theorem R.fromTensorFinsupp_coeffs (coeffs : List ℤ) :
  Polynomial.coeff (fromTensorFinsupp q coeffs) i = ↑(List.getD coeffs i 0) := by
  rw [fromTensorFinsupp]
  rw [coeff_ofFinsupp]
  rw [List.toFinsupp_apply]
  have hzero : (0 : ZMod q) = Int.cast (0 : ℤ) := by norm_num
  rw [hzero, List.getD_map]

/-- concatenating into a `fromTensorFinsupp` is the same as adding a ⟨Finsupp.single⟩. -/
theorem R.fromTensorFinsupp_concat_finsupp {q : ℕ} (c : ℤ) (cs : List ℤ) :
    (R.fromTensorFinsupp (q := q) (cs ++ [c])) = (R.fromTensorFinsupp (q := q) cs) + ⟨Finsupp.single cs.length (Int.cast c : (ZMod q))⟩ := by
    simp only[fromTensorFinsupp]
    simp only[← Polynomial.ofFinsupp_add]
    simp only[List.map_append, List.map]
    simp only[List.toFinsupp_concat_eq_toFinsupp_add_single]
    simp only[List.length_map]

/-- concatenating into a `fromTensorFinsupp` is the same as adding a monomial. -/
theorem R.fromTensorFinsupp_concat_monomial {q : ℕ} (c : ℤ) (cs : List ℤ) :
    (R.fromTensorFinsupp (q := q) (cs ++ [c])) = (R.fromTensorFinsupp (q := q) cs) + (Polynomial.monomial cs.length (Int.cast c : (ZMod q))) := by
    simp[fromTensorFinsupp]
    rw[← Polynomial.ofFinsupp_single]
    simp only[List.toFinsupp_concat_eq_toFinsupp_add_single]
    simp only[← Polynomial.ofFinsupp_add]
    rw[List.length_map]

/-- show that `fromTensor` is the same as `fromPoly ∘ fromTensorFinsupp`. -/
theorem R.fromTensor_eq_fromTensorFinsupp_fromPoly {q n} : R.fromTensor (q := q) (n := n) coeffs =
  R.fromPoly (q := q) (n := n) (R.fromTensorFinsupp q coeffs) := by
    simp[fromTensor, fromTensor']
    induction coeffs  using List.reverseRecOn
    case nil => simp[List.enum, fromTensorFinsupp]
    case append_singleton c cs hcs =>
      simp[List.enum_append]
      simp[R.fromTensorFinsupp_concat_monomial]
      rw[hcs]
      congr

/-- `coeff (p % f) = coeff p` if the degree of `p` is less than the degree of `f`. -/
theorem coeff_modByMonic_degree_lt_f {q n i : ℕ} [Fact (q > 1)] (p : (ZMod q)[X]) (DEGREE : p.degree < (f q n).degree) :
  (p %ₘ f q n).coeff i = p.coeff i := by
  have H := (modByMonic_eq_self_iff (hq := f_monic q n) (p := p)).mpr DEGREE
  simp[H]

/-- The coefficient of `fromPoly p` is the coefficient of `p` modulo `f q n`. -/
@[simp]
theorem R.coeff_fromPoly {q n : ℕ} [Fact (q > 1)] (p : (ZMod q)[X]) : R.coeff (R.fromPoly (q := q) (n := n) p) = Polynomial.coeff (p %ₘ (f q n)) := by
  unfold R.coeff
  simp [R.coeff]
  have H := R.representative_fromPoly_toFun (a := p) (n := n)
  norm_cast at H ⊢

/- 1. given a list of coefficients, building the ring element and then picking the repr from
   the equiv class, is the same as taking modulo (`representative_fromPoly_toFun`)
   2. if the length is less than 2^n, then the modulo by`f` equals the element itself
    (`representative_fromPoly_eq`).
  3.
-/
/-- The coefficient of `fromTensor` is the same as the values available in the tensor input. -/
theorem R.coeff_fromTensor [hqgt1 : Fact (q > 1)] (tensor : List Int) (htensorlen : tensor.length < 2^n)
: (R.fromTensor (q := q) (n := n) tensor).coeff i = (tensor.getD i 0) := by
  rw[fromTensor_eq_fromTensorFinsupp_fromPoly]
  have hfromTensorFinsuppDegree := fromTensorFinsupp_degree q tensor
  rw [coeff]
  rw [representative_fromPoly_eq]
  apply fromTensorFinsupp_coeffs
  case DEGREE =>
    generalize htensor_degree : degree (fromTensorFinsupp q tensor) = tensor_degree
    rw [f_deg_eq]
    cases tensor_degree
    case none => norm_cast; apply WithBot.none_lt_some
    case some tensor_degree =>
      /- I hate this coercion stuff -/
      norm_cast
      apply WithBot.coe_strictMono
      norm_cast
      have htrans : tensor_degree  ≤ List.length tensor := by
        rw [htensor_degree] at hfromTensorFinsuppDegree
        rw [WithBot.some_eq_coe] at hfromTensorFinsuppDegree
        rw [← WithBot.coe_le_coe]
        assumption
      apply Nat.lt_of_le_of_lt htrans htensorlen

theorem R.representative_fromTensor_eq_fromTensor' (tensor : List ℤ) : R.representative q n (R.fromTensor tensor) = R.representative' q n (R.fromTensor' q tensor)  %ₘ (f q n) := by
  simp [R.representative]
  rw[fromTensor_eq_fromTensor'_fromPoly];

/--
Converts an element of `R` into a tensor (modeled as a `List Int`)
with the representatives of the coefficients of the representative.
The length of the list is the degree of the representative + 1.
-/
noncomputable def R.toTensor {q n} [Fact (q > 1)] (a : R q n) : List Int :=
  List.range a.repLength |>.map fun i =>
        a.coeff i |>.toInt

/-- The length of the tensor `R.toTensor a` equals `a.repLength` -/
theorem R.toTensor_length {q n} [Fact (q > 1)] (a : R q n) : (R.toTensor a).length = a.repLength := by
  simp [R.toTensor, List.length_range]

/--
Converts an element of `R` into a tensor (modeled as a `List Int`)
with the representatives of the coefficients of the representative.
The length of the list is the degree of the generator polynomial `f` + 1.
-/
noncomputable def R.toTensor' {q n} [Fact (q > 1)] (a : R q n) : List Int :=
  let t := a.toTensor
  t ++ List.replicate (2^n - t.length + 1) 0

def trimTensor (tensor : List Int) : List Int
  := tensor.reverse.dropWhile (· = 0) |>.reverse

/--
We define the base type of the representation, which encodes both natural numbers
and elements in the ring `R q n` (which in FHE are sometimes called 'polynomials'
 in allusion to `R.representative`).

 In this context, `Tensor is a 1-D tensor, which we model here as a list of integers.
-/
inductive Ty (q : Nat) (n : Nat) [Fact (q > 1)]
  | index : Ty q n
  | integer : Ty q n
  | tensor : Ty q n
  | polynomialLike : Ty q n
  deriving DecidableEq, Repr

instance : Inhabited (Ty q n) := ⟨Ty.index⟩
instance : TyDenote (Ty q n) where
toType := fun
  | .index => Nat
  | .integer => Int
  | .tensor => List Int
  | .polynomialLike => (R q n)


/--
The operation type of the `Poly` dialect. Operations are parametrized by the
two parameters `p` and `n` that characterize the ring `R q n`.
We parametrize the entire type by these since it makes no sense to mix operations in different rings.
-/
inductive Op (q : Nat) (n : Nat) [Fact (q > 1)]
  | add : Op q n-- Addition in `R q n`
  | sub : Op q n-- Substraction in `R q n`
  | mul : Op q n-- Multiplication in `R q n`
  | mul_constant : Op q n-- Multiplication by a constant of the base ring (we assume this to be a `.integer` and take its representative)
  | leading_term : Op q n-- Leading term of representative
  | monomial : Op q n-- create a monomial
  | monomial_mul : Op q n-- multiply by(monic) monomial
  | from_tensor : Op q n-- interpret values as coefficients of a representative
  | to_tensor : Op q n-- give back coefficients from `R.representative`
  | const (c : R q n) : Op q n
  | const_int (c : Int) : Op q n
  | const_idx (i : Nat) : Op q n


open TyDenote (toType)


@[simp, reducible]
def Op.sig : Op  q n → List (Ty q n)
| Op.add => [Ty.polynomialLike, Ty.polynomialLike]
| Op.sub => [Ty.polynomialLike, Ty.polynomialLike]
| Op.mul => [Ty.polynomialLike, Ty.polynomialLike]
| Op.mul_constant => [Ty.polynomialLike, Ty.integer]
| Op.leading_term => [Ty.polynomialLike]
| Op.monomial => [Ty.integer, Ty.index]
| Op.monomial_mul => [Ty.polynomialLike, Ty.index]
| Op.from_tensor => [Ty.tensor]
| Op.to_tensor => [Ty.polynomialLike]
| Op.const _ => []
| Op.const_int _ => []
| Op.const_idx _ => []

@[simp, reducible]
def Op.outTy : Op q n → Ty q n
| Op.add | Op.sub | Op.mul | Op.mul_constant | Op.leading_term | Op.monomial
| Op.monomial_mul | Op.from_tensor | Op.const _  => Ty.polynomialLike
| Op.to_tensor => Ty.tensor
| Op.const_int _ => Ty.integer
| Op.const_idx _ => Ty.index

@[simp, reducible]
def Op.signature : Op q n → Signature (Ty q n) :=
  fun o => {sig := Op.sig q n o, outTy := Op.outTy q n o, regSig := []}

instance : OpSignature (Op q n) (Ty q n) := ⟨Op.signature q n⟩

noncomputable instance  FHEOpDenote : OpDenote (Op q n) (Ty q n) where
 denote
    | Op.add, arg, _ => (fun args : R q n × R q n => args.1 + args.2) arg.toPair
    | Op.sub, arg, _ => (fun args : R q n × R q n => args.1 - args.2) arg.toPair
    | Op.mul, arg, _ => (fun args : R q n × R q n => args.1 * args.2) arg.toPair
    | Op.mul_constant, arg, _ => (fun args : R q n × Int => args.1 * ↑(args.2)) arg.toPair
    | Op.leading_term, arg, _ => R.leadingTerm arg.toSingle
    | Op.monomial, arg, _ => (fun args => R.monomial q n (args.1 : ZMod q) args.2) arg.toPair
    | Op.monomial_mul, arg, _ => (fun args : R q n × Nat => args.1 * R.monomial q n 1 args.2) arg.toPair
    | Op.from_tensor, arg, _ => R.fromTensor arg.toSingle
    | Op.to_tensor, arg, _ => R.toTensor' arg.toSingle
    | Op.const c, _, _ => c
    | Op.const_int c, _, _ => c
    | Op.const_idx c, _, _ => c
