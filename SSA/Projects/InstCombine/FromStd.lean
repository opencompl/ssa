-- Lemmas stolen from Std that should eventually use the correct lemmas from Std
import Std.Data.Bool
import Std.Data.Nat.Lemmas
import Std.Tactic.RCases


namespace Nat

@[local simp]
private theorem one_div_two : 1/2 = 0 := by trivial

theorem mul_add_div {m : Nat} (m_pos : m > 0) (x y : Nat) : (m * x + y) / m = x + y / m := by
  match x with
  | 0 => simp
  | x + 1 =>
    simp [Nat.mul_succ, Nat.add_assoc _ m,
          mul_add_div m_pos x (m+y),
          div_eq (m+y) m,
          m_pos,
          Nat.le_add_right m, Nat.add_succ, Nat.succ_add]

private theorem two_pow_succ_sub_one_div : (2 ^ (n+1) - 1) / 2 = 2^n - 1 := by
  apply fun x => (Nat.sub_eq_of_eq_add x).symm
  apply Eq.trans _
  apply Nat.add_mul_div_left _ _ Nat.zero_lt_two
  rw [Nat.mul_one, ←Nat.sub_add_comm (Nat.pow_two_pos _)]
  rw [ Nat.add_sub_assoc Nat.zero_lt_two ]
  simp [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_add_div]

/-! ### Preliminaries -/

/--
An induction principal that works on divison by two.
-/
noncomputable def div2Induction {motive : Nat → Sort u}
    (n : Nat) (ind : ∀(n : Nat), (n > 0 → motive (n/2)) → motive n) : motive n := by
  induction n using Nat.strongInductionOn with
  | ind n hyp =>
    apply ind
    intro n_pos
    if n_eq : n = 0 then
      simp [n_eq] at n_pos
    else
      apply hyp
      exact Nat.div_lt_self n_pos (Nat.le_refl _)

@[simp] theorem zero_and (x : Nat) : 0 &&& x = 0 := by rfl

@[simp] theorem and_zero (x : Nat) : x &&& 0 = 0 := by
  simp only [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  simp

@[simp] theorem and_one_is_mod (x : Nat) : x &&& 1 = x % 2 := by
  if xz : x = 0 then
    simp [xz, zero_and]
  else
    have andz := and_zero (x/2)
    simp only [HAnd.hAnd, AndOp.and, land] at andz
    simp only [HAnd.hAnd, AndOp.and, land]
    unfold bitwise
    cases mod_two_eq_zero_or_one x with | _ p =>
      simp [xz, p, andz, one_div_two, mod_eq_of_lt]
end Nat
