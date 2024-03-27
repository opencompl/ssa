import SSA.Projects.MLIRSyntax.EDSL
import SSA.Core.Tactic
import SSA.Projects.FullyHomomorphicEncryption.Basic
import SSA.Projects.FullyHomomorphicEncryption.Statements
import SSA.Projects.FullyHomomorphicEncryption.Syntax

open Ctxt (Var Valuation DerivedCtxt)

open MLIR AST -- need this to support the unhygenic macros in the EDSL


namespace ExampleComm

variable {q : Nat} {n : Nat} [hq : Fact (q > 1)]

def lhs :=
[fhe_com q, n, hq| {
^bb0(%A : ! R, %B : ! R):
  %v1 = "poly.add" (%A,%B) : (! R, ! R) -> (! R)
  "return" (%v1) : (! R) -> ()
}]

def rhs :=
[fhe_com q, n, hq| {
^bb0(%A : ! R, %B : ! R):
  %v1 = "poly.add" (%B,%A) : (! R, ! R) -> (! R)
  "return" (%v1) : (! R) -> ()
}]

open MLIR AST in
noncomputable def p1 : PeepholeRewrite (Op q n) [.polynomialLike, .polynomialLike] .polynomialLike :=
  { lhs := lhs, rhs := rhs, correct :=
    by
      rw [lhs, rhs]
      /-:
      Com.denote
        (Com.lete (cst 0)
        (Com.lete (add { val := 1, property := _ } { val := 0, property := _ })
        (Com.ret { val := 0, property := ex1.proof_3 }))) =
      Com.denote (Com.ret { val := 0, property := _ })
      -/
      funext Γv
      simp_peephole [] at Γv
      /- ⊢ ∀ (a b : R 2 3), b + a = a + b -/
      intros a b
      rw [add_comm]
      /- No goals-/
      done
    }

end ExampleComm


section ExampleModulo
-- 2^n

@[irreducible]
def irreduciblePow (q n : Nat) : Nat := q^n
infixl:50 "**" => irreduciblePow


variable {q : Nat} {n : Nat} [hq : Fact (q > 1)]

-- code generator does not support recursor 'Decidable.rec' yet, consider using 'match ... with' and/or structural recursion
noncomputable def lhs :=
[fhe_com q, n, hq| {
^bb0(%a : ! R):
  %one_int = "arith.const" () {value = 1}: () -> (i16)
  %two_to_the_n = "arith.const" () {value = $((2**n : Int))}: () -> (index)
  %x2n = "poly.monomial" (%one_int,%two_to_the_n) : (i16, index) -> (! R)
  %oner = "poly.const" () {value = 1}: () -> (! R)
  %p = "poly.add" (%x2n, %oner) : (! R, ! R) -> (! R)
  %v1 = "poly.add" (%a, %p) : (! R, ! R) -> (! R)
  "return" (%v1) : (! R) -> ()
}]

def rhs :=
[fhe_com q, n, hq | {
^bb0(%a : ! R):
  "return" (%a) : (! R) -> ()
}]

#print axioms lhs

open MLIR AST in
noncomputable def p1 : PeepholeRewrite (Op q n) [.polynomialLike] .polynomialLike :=
  { lhs := lhs,
     rhs := rhs
  , correct :=
    by
      funext Γv
      unfold lhs rhs
       /-
       Com.denote
           (Com.lete (Expr.mk (Op.const_int (Int.ofNat 1)) lhs.proof_2 HVector.nil HVector.nil)
             (Com.lete (Expr.mk (Op.const_idx 1) lhs.proof_3 HVector.nil HVector.nil)
               (Com.lete
                 (Expr.mk Op.monomial lhs.proof_4
                   ({ val := 1, property := lhs.proof_5 }::ₕ({ val := 0, property := lhs.proof_6 }::ₕHVector.nil)) HVector.nil)
                 (Com.lete
                   (Expr.mk (Op.const (ROfZComputable_stuck_term 2 3 (Int.ofNat 1))) lhs.proof_7 HVector.nil HVector.nil)
                   (Com.lete
                     (Expr.mk Op.add lhs.proof_8
                       ({ val := 1, property := lhs.proof_9 }::ₕ({ val := 0, property := lhs.proof_10 }::ₕHVector.nil))
                       HVector.nil)
                     (Com.lete
                       (Expr.mk Op.add lhs.proof_8
                         ({ val := 5, property := lhs.proof_11 }::ₕ({ val := 0, property := lhs.proof_12 }::ₕHVector.nil))
                         HVector.nil)
                       (Com.ret { val := 0, property := lhs.proof_13 })))))))
           Γv =
         Com.denote (Com.ret { val := 0, property := rhs.proof_2 }) Γv
       -/
      simp_peephole [Nat.cast_one, Int.cast_one, ROfZComputable_def] at Γv
      /- ⊢ ∀ (a : ⟦Ty.polynomialLike⟧), a + (R.monomial q n 1 (2**n) + 1) = a -/
      simp [R.fromPoly, R.monomial]
      /- ⊢ a + ((Ideal.Quotient.mk (Ideal.span {f q n})) ((Polynomial.monomial (2**n)) 1) + 1) = a -/
      intros a
      unfold irreduciblePow
      --have hgenerator : f 2 3 = (Polynomial.monomial 8 1) + 1  := by simp [f, Polynomial.X_pow_eq_monomial]
      have hgenerator : f q n - (1 : Polynomial (ZMod q)) = (Polynomial.monomial (R := ZMod q) (2^n : Nat) 1)  := by simp  [f, Polynomial.X_pow_eq_monomial]
      --set_option pp.all true in
      -- `rw` bug? or because of the workaround?
      -- tactic 'rewrite' failed, motive is not type correct
      rw [← hgenerator]
      have add_congr_quotient : ((Ideal.Quotient.mk (Ideal.span {f q n})) (f q n - 1) + 1)  = ((Ideal.Quotient.mk (Ideal.span {f q n})) (f q n )) := by simp
      rw [add_congr_quotient]
      apply Poly.add_f_eq
      done
    }
end ExampleModulo
