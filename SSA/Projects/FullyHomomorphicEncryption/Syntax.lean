import SSA.Projects.InstCombine.LLVM.Transform
import SSA.Projects.MLIRSyntax.AST
import SSA.Projects.MLIRSyntax.EDSL
import SSA.Projects.FullyHomomorphicEncryption.Basic

open MLIR AST Ctxt
open Polynomial -- for R[X] notation

def ROfZComputable_impl (z : ℤ) : R q n :=
  let zq : ZMod q := z
  let p : (ZMod q)[X] := {
      toFinsupp := Finsupp.mk
        (support := List.toFinset (if zq = 0 then  [] else [0]))
        (toFun := fun i => if i = 0 then z else 0)
        (mem_support_toFun := by
          intros a
          constructor
          · intros ha
            simp at ha
            split at ha
            case mp.inl hz =>
              simp at ha
            case mp.inr hz =>
              simp at ha
              subst ha
              simp [hz]
          · intros hb
            simp at hb
            obtain ⟨ha, hz⟩ := hb
            subst ha
            simp [hz]
        )
      : (ZMod q)[X]
  }
  R.fromPoly p

theorem ROfZComputable_eq (q n : Nat) (z : ℤ):
    ROfZComputable_impl z = (↑z : R q n) := by
  simp (config := { decide := true}) [ROfZComputable_impl] -- , Int.cast, Ring.toIntCast, IntCast.intCast]
  by_cases (z = 0)
  case pos h =>
    simp (config := { decide := true, eta := true}) [h, EmptyCollection.emptyCollection]
    have heta : forall a: Nat, ((fun (i : Nat) =>
                      @OfNat.ofNat.{0} (ZMod q) 0
                        (@Zero.toOfNat0.{0} (ZMod q)
                          (@NegZeroClass.toZero.{0} (ZMod q)
                            (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod q)
                              (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod q)
                                (@AddGroup.toSubtractionMonoid.{0} (ZMod q)
                                  (@AddGroupWithOne.toAddGroup.{0} (ZMod q)
                                    (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                      (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q))))))))))
                    a)  = (0 : ZMod q) := by simp
    set_option pp.all true in
    try rw [heta] -- literally copy-pasted!
    sorry
  case neg h =>
    sorry

/-- This definition is subtle.

1.  We make this an axiom so we can strongly normalize terms without lean
  unfolding the definition
2. We give it an implemented_by so we can use it in computable code that is used
   to create the expression in Meta code
3. We give it an equation lemma to make it what we *really* want in proof mode, which is the coe.

This ensures three properties simultaneously:
1. We can run it at meta time giving us the `ìmplemented_by` value
2. It strongly normalizes creating stuck term (`ROfZComputable`)
3. We can then `simp`it to become the value we really want (`coe z`).
4. The `theorem ROfZComputable_eq` tells us that this is safe to do.

See also [[NOTE: Wanting Stuck Terms During Strong Normalization of Com]]
-/
@[implemented_by ROfZComputable_impl]
axiom ROfZComputable_stuck_term (q n : Nat) (z : ℤ) : R q n

@[simp]
axiom ROfZComputable_def (q n :Nat) (z : ℤ) :
    ROfZComputable_stuck_term  q n z = (↑ z : R q n)

section MkFuns
variable {q : Nat} {n : Nat} [Fact (q > 1)]

def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM (Op q n) (Ty q n)
  | MLIR.AST.MLIRType.undefined "R" => do
    return .polynomialLike
  | MLIR.AST.MLIRType.int MLIR.AST.Signedness.Signless _ => do
    return .integer
  | MLIR.AST.MLIRType.index  => do
    return .index
  | _ => throw .unsupportedType

instance instTransformTy : MLIR.AST.TransformTy (Op q n) (Ty q n) 0 where
  mkTy := mkTy



def cstInt {Γ : Ctxt _} (z :Int) : Expr (Op q n) Γ .integer  :=
  Expr.mk
    (op := .const_int z)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)


def cstIdx {Γ : Ctxt _} (i : Nat) : Expr (Op q n) Γ .index :=
  Expr.mk
    (op := .const_idx i)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)

def add {Γ : Ctxt (Ty q n)} (e₁ e₂ : Var Γ .polynomialLike) : Expr (Op q n) Γ .polynomialLike :=
  Expr.mk
    (op := .add)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def mul {Γ : Ctxt (Ty q n)} (e₁ e₂ : Var Γ .polynomialLike) : Expr (Op q n) Γ .polynomialLike :=
  Expr.mk
    (op := .mul)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

def mon {Γ : Ctxt (Ty q n)} (a : Var Γ .integer) (i : Var Γ .index) : Expr (Op q n) Γ .polynomialLike :=
  Expr.mk
    (op := .monomial)
    (ty_eq := rfl)
    (args := .cons a <| .cons i .nil)
    (regArgs := .nil)




def cstComputable {Γ : Ctxt _} (z : Int) : Expr (Op q n) Γ .polynomialLike :=
  Expr.mk
    (op := Op.const (ROfZComputable_stuck_term q n z))
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)



-- /-- Introduce an irreducible def that turns an Int into an R.
-- For some reason, Lean is *incredibly* agressive at unfolding this particular
-- definition, and gives a crazy soup when trying to inspect what the integer
-- gets coerced to. We disable this by writing a custom definition.
-- -/
-- noncomputable irreducible_def R.ofInt (z : Int) [inst : Fact (q > 1)]  : R q n := z

-- -- A lot of this boilerplate should be automatable
-- @[implemented_by cstComputable]
-- def cstUncomputable {Γ : Ctxt _} (r : Int) : Expr (Op q n) Γ .polynomialLike  :=
--   Expr.mk
--     (op := .const (R.ofInt r))
--     (ty_eq := rfl)
--     (args := .nil)
--     (regArgs := .nil)

/-- We show that the uncomputable definition in terms of R.ofInt is equal t the
  definition we give by building the term directly. -/
-- theorem cst_computable_eq_cst_uncomputable [Fact (q > 1)] {Γ : Ctxt (Ty q n)}  (r : Int) :
--     cstComputable r = cstUncomputable (Γ := Γ) r := by
--   simp [cstComputable, cstUncomputable, R.ofZComputable]
--   sorry


-- Will for now not support poly constants, just integers
def mkExpr (Γ : Ctxt (Ty q n)) (opStx : MLIR.AST.Op 0) :
    MLIR.AST.ReaderM (Op q n) (Σ ty, Expr (Op q n) Γ ty) := do
  match opStx.name with
  | "poly.const" =>
    match opStx.attrs.find_int "value" with
    | .some (v, _ty) =>
      -- throw <| .generic s!"expected 'const' to have int attr 'value', found: {repr opStx}"
      return ⟨.polynomialLike, cstComputable v⟩
    | .none => throw <| .generic s!"expected 'const' to have int attr 'value', found: {repr opStx}"
  | "arith.const" =>
    match opStx.attrs.find_int "value" with
    | .some (v, vty) => match vty with
        | .int _ _ => match opStx.res with
          | [(_,MLIR.AST.MLIRType.int MLIR.AST.Signedness.Signless _)] => return ⟨.integer, cstInt v⟩
          | [(_,MLIR.AST.MLIRType.index)] => return ⟨.index, cstIdx v.toNat⟩
          | _ => throw <| .generic s!"unsupported result type {repr opStx.res} for arith.const"
        | _ => throw <| .generic s!"unsupported constant type {repr vty} for arith.const"
    | .none => throw <| .generic s!"expected 'const' to have int attr 'value', found: {repr opStx}"
  | "poly.monomial" =>
    match opStx.args with
    | v₁Stx::v₂Stx::[] =>
      let ⟨ty₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
      let ⟨ty₂, v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx
      match ty₁, ty₂ with
        | .integer, .index => return ⟨.polynomialLike, mon v₁ v₂⟩
        | _, _ => throw <| .generic s!"expected operands to be of types `integer` and `index` for `monomial`. Got: {repr ty₁}, {repr ty₂}"
    | _ => throw <| .generic s!"expected two operands for `monomial`, found #'{opStx.args.length}' in '{repr opStx.args}'"
  | "poly.add" =>
    match opStx.args with
    | v₁Stx::v₂Stx::[] =>
      let ⟨ty₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
      let ⟨ty₂, v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx
      match ty₁, ty₂ with
        | .polynomialLike, .polynomialLike => return ⟨.polynomialLike, add v₁ v₂⟩
        | _, _ => throw <| .generic s!"expected both operands to be of type 'polynomialLike'"
    | _ => throw <| .generic s!"expected two operands for `add`, found #'{opStx.args.length}' in '{repr opStx.args}'"
  | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"

instance : MLIR.AST.TransformExpr (Op q n) (Ty q n) 0 where
  mkExpr := mkExpr

def mkReturn (Γ : Ctxt (Ty q n)) (opStx : MLIR.AST.Op 0) : MLIR.AST.ReaderM (Op q n) (Σ ty, Com (Op q n) Γ ty) :=
  if opStx.name == "return"
  then match opStx.args with
  | vStx::[] => do
    let ⟨ty, v⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ vStx
    return ⟨ty, Com.ret v⟩
  | _ => throw <| .generic s!"Ill-formed return statement (wrong arity, expected 1, got {opStx.args.length})"
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"

instance : MLIR.AST.TransformReturn (Op q n) (Ty q n) 0 where
  mkReturn := mkReturn

def mlir2fhe (reg : MLIR.AST.Region 0) :
    MLIR.AST.ExceptM (Op q n) (Σ (Γ : Ctxt (Ty q n)) (ty : (Ty q n)), Com (Op q n) Γ ty) := MLIR.AST.mkCom reg

end MkFuns -- we don't want q and i here anymore

open Qq MLIR AST Lean Elab Term Meta in
/--
NOTE: Wanting Stuck Terms During Strong Normalization of Com

See that we unfold with `TransparencyMode.all`. We do this so we can expose Com.denote
fully. This is a crazy hack, and interacts extremely poorly with complex definitions found in FHE.

We currently work around Lean unfolding *everything* by making definitions that tend to explode
(e.g. R.monomial, R.ofZComputable) into *axioms*, to which we add another axiom
that is a rewrite equation.

We do this so that the strong normalizer can get stuck on the axiom,
which we can them simp during proof time.

The correct solution is a `match goal` like tactic to match on the proof state
and run the correct equation.
-/
elab "[fhe_com" qi:term "," ni:term "," hq:term " | " reg:mlir_region "]" : term => do
  let ast_stx ← `([mlir_region| $reg])
  let ast ← elabTermEnsuringTypeQ ast_stx q(Region 0)
  let qval : Q(Nat) ← elabTermEnsuringTypeQ qi q(Nat)
  let nval : Q(Nat) ← elabTermEnsuringTypeQ ni q(Nat)
  -- We need this for building `R  later
  -- I would like to synthesize this at elaboration time, not sure how
  let factval ← elabTermEnsuringTypeQ hq q(Fact ($qval > 1))
  let com := q(mlir2fhe (q := $qval) (n := $nval) $ast)
  synthesizeSyntheticMVarsNoPostponing
  let com : Q(MLIR.AST.ExceptM (Op 2 3) (Σ (Γ' : Ctxt (Ty 2 3)) (ty : Ty 2 3), Com (Op 2 3) Γ' ty)) ←
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      withTransparency (mode := TransparencyMode.default) <|
        return ←reduce com
  let comExpr : Expr := com
  trace[Meta] com
  trace[Meta] comExpr
  match comExpr.app3? ``Except.ok with
  | .some (_εexpr, _αexpr, aexpr) =>
      match aexpr.app4? ``Sigma.mk with
      | .some (_αexpr, _βexpr, _fstexpr, sndexpr) =>
        match sndexpr.app4? ``Sigma.mk with
        | .some (_αexpr, _βexpr, _fstexpr, sndexpr) =>
            return sndexpr
        | .none => throwError "Found `Except.ok (Sigma.mk _ WRONG)`, Expected (Except.ok (Sigma.mk _ (Sigma.mk _ _))"
      | .none => throwError "Found `Except.ok WRONG`, Expected (Except.ok (Sigma.mk _ _))"
  | .none => throwError "Expected `Except.ok`, found {comExpr}"
