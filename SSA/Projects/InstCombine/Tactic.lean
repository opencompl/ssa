import SSA.Projects.InstCombine.LLVM.EDSL
import SSA.Projects.InstCombine.AliveStatements
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.ForStd
import Mathlib.Tactic
import SSA.Core.ErasedContext
import SSA.Core.Tactic
import Std.Data.BitVec
import Mathlib.Data.BitVec.Lemmas

open MLIR AST
open Std (BitVec)
open Ctxt

theorem bitvec_minus_one : BitVec.ofInt w (Int.negSucc 0) = (-1 : BitVec w) := by
  change (BitVec.ofInt w (-1) = (-1 : BitVec w))
  ext i
  simp_all only [BitVec.ofInt, Neg.neg, Int.neg, Int.negOfNat]
  simp_all only [BitVec.getLsb'_not, BitVec.getLsb'_ofNat_zero, Bool.not_false, BitVec.ofNat_eq_ofNat, BitVec.neg_eq,
    BitVec.getLsb'_neg_ofNat_one]


-- TODO: Do we call this dialect the "Alive" dialect (as hinted by the `simp_alive_peephole` name),
--       or the "InstCombine" dialect (as hinted by the `InstCombine` namespace that everything
--       lives in)?

open MLIR AST in
/--
`simp_alive_peephole` extends `simp_peephole` to simplify goals about refinement of `InstCombine`
programs into statements about just bitvectors.

To wit, the tactic expects a goal of the form: `Com.Refinement com₁ com₂`
That is, goals of
of the form `Com.refine, com₁.denote Γv ⊑ com₂.denote Γv `, where
`com₁` and `com₂` are programs in the `InstCombine` dialect. -/
macro "simp_alive_peephole" : tactic =>
  `(tactic|
      (
        /- Unfold the meaning of refinement, to access the valuation -/
        dsimp only [Com.Refinement]
        intros Γv

        /- Simplify away the core framework -/
        simp_peephole at Γv

        /- Simplify away the `InstCombine` specific semantics. -/
        simp (config := {unfoldPartialApp := true}) only [OpDenote.denote,
          /- Note that we need `HVector.toPair`, `HVector.toSingle` and `HVector.toTriple`,
              since they're used in `InstCombine.Op.denote`,
              and we need `HVector.toTuple` since it's used in `MLIR.AST.mkOpExpr`. -/
          -- TODO: if `HVector.toTuple` is used in the core framework's AST translation, it should
          --       probably be part of the core `simp_peephole` simp-set
          InstCombine.Op.denote, HVector.toPair, HVector.toTriple, pairMapM, BitVec.Refinement,
          bind, Option.bind, pure, Ctxt.DerivedCtxt.ofCtxt, Ctxt.DerivedCtxt.snoc,
          Ctxt.snoc,
          ConcreteOrMVar.instantiate, Vector.get, HVector.toSingle,
          LLVM.and?, LLVM.or?, LLVM.xor?, LLVM.add?, LLVM.sub?,
          LLVM.mul?, LLVM.udiv?, LLVM.sdiv?, LLVM.urem?, LLVM.srem?,
          LLVM.sshr, LLVM.lshr?, LLVM.ashr?, LLVM.shl?, LLVM.select?,
          LLVM.const?, LLVM.icmp?,
          HVector.toTuple, List.nthLe, bitvec_minus_one,
          DialectMorphism.mapTy,
          InstcombineTransformDialect.instantiateMTy,
          InstcombineTransformDialect.instantiateMOp,
          InstcombineTransformDialect.MOp.instantiateCom,
          InstcombineTransformDialect.instantiateCtxt,
          ConcreteOrMVar.instantiate, Com.Refinement,
          DialectMorphism.mapTy]

        /-  At this point, we have should a goal of the form:
              `∀ (x₁ : Option (BitVec _)) ... (xₙ : Option (BitVec _)), ...`
            For some unknown number of variables `n` (but assumed to be `n ≤ 5`,
            as per the hack in `simp_peephole`).

            However, the `none` (i.e., poison) cases are generally trivial.
            Thus we attempt to introduce some variables (using `try` because the intro might fail
            if we have less universal quantifiers than `intro`s), case split on them, and simp
            through the monadic bind on `Option` (in the generally true assumption that the `none`
            case becomes trivial and is closed by `simp`).
        -/
        try intros v0
        try intros v1
        try intros v2
        try intros v3
        try intros v4
        try intros v5
        simp (config := {failIfUnchanged := false}) only [Option.bind, bind, Monad.toBind, Var.casesOn, cast, pairBind, Option.bind_eq_bind]
        try cases' v0 with x0 <;> simp[Option.bind, bind, Monad.toBind]
          <;> try cases' v1 with x1 <;> simp[Option.bind, bind, Monad.toBind]
          <;> try cases' v2 with x2 <;> simp[Option.bind, bind, Monad.toBind]
          <;> try cases' v3 with x3 <;> simp[Option.bind, bind, Monad.toBind]
          <;> try cases' v4 with x4 <;> simp[Option.bind, bind, Monad.toBind]
          <;> try cases' v5 with x5 <;> simp[Option.bind, bind, Monad.toBind]
          <;> dsimp[Option.bind, bind, Monad.toBind]

        /--
        CAVEAT: This does nothing, the variables `v$i` have been cases on, and the newly introduced
        variables (in the `some` cases) are called `x$i` instead, i'll document the intended behaviour.
        TODO: fix this

        Finally, revert the variables introduced in the `some` cases, so that we are left with a
        universally quantified goal of the form:
          `∀ (x₁ : BitVec _) ... (xₙ : BitVec _), ...` -/
        try revert v5
        try revert v4
        try revert v3
        try revert v2
        try revert v1
        try revert v0
      )
   )
