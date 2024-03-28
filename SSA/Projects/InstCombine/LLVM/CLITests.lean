import SSA.Core.Util
import Std
import Lean.Environment
import Cli
import SSA.Projects.InstCombine.LLVM.Transform
import SSA.Projects.InstCombine.Base

open Lean TyDenote InstCombine

/-- Parse a tuple -/
instance instParseableTuple [A : Cli.ParseableType α] [B : Cli.ParseableType β] :
  Cli.ParseableType (α × β) where
    name :=  s!"({A.name} × {B.name})"
    parse? str := do
      let str := str.trim.splitOn ","
      match str with
      | [a, b] => do
        let a ← A.parse? a.trim
        let b ← B.parse? b.trim
        return (a, b)
      | _ => .none

abbrev MContext φ := Ctxt <| MTy φ
abbrev Context := MContext 0
abbrev MCom φ := Com (MOp φ)
abbrev MExpr φ := Expr (MOp φ)

instance : ToString Context := inferInstanceAs (ToString (List <| MTy 0))

structure CliTest where
  name : Name
  mvars : Nat
  context : MContext mvars
  ty : MTy mvars
  eff : EffectKind
  code : MCom mvars context eff ty

def CliTest.signature (test : CliTest) :
  List (InstCombine.MTy test.mvars) × (InstCombine.MTy test.mvars) :=
  (test.context, test.ty)

-- We add a special case for 1 because Nat × Unit ≠ Nat
private def natParams : Nat → Type
  | 0 => Unit
  | 1 => Nat
  | n + 1 => Nat × (natParams n)

theorem natParamsTup : ∀ n : Nat, n > 0 → natParams (n + 1) = (Nat × natParams n) := by
  intro n
  induction n <;> simp [natParams]

def instParseableNatParams {n : Nat} : Cli.ParseableType (natParams n) where
  name := s!"{n} nat(s)."
  parse? str :=
  match n with
    | 0 =>
      let inst : Cli.ParseableType Unit := inferInstance
      inst.parse? str
    | 1 =>
      let inst : Cli.ParseableType Nat := inferInstance
      inst.parse? str
    -- this feels unnecessarily complicated
    | (n + 1) + 1 =>
      let inst1 : Cli.ParseableType Nat := inferInstance
      let instn : Cli.ParseableType (natParams (n + 1)) := @instParseableNatParams (n + 1)
      let instTup : Cli.ParseableType (Nat × (natParams <| n + 1)) := @instParseableTuple Nat (natParams (n + 1)) inst1 instn
      let hn1gt0 : (n + 1) > 0 := by
        rename_i n_1 -- aesop?
        simp_all only [gt_iff_lt, add_pos_iff, zero_lt_one, or_true]
      let hn1eq := natParamsTup (n + 1) hn1gt0
      hn1eq ▸ instTup.parse? str

instance {n : Nat} : Cli.ParseableType (natParams n) := instParseableNatParams

def CliTest.params : CliTest → Type
| test => natParams test.mvars

def CliTest.paramsParseable (test : CliTest) : Cli.ParseableType (test.params) :=
  instParseableNatParams

instance {n : Nat} : Cli.ParseableType (BitVec n) where
  name := s!"BitVec {n}"
  parse? str := do
   let intVal ← Cli.instParseableTypeInt.parse? str
   return BitVec.ofInt n intVal

/--
We can only execute tests that are concrete.
This property ensures that they are concrete, i.e. have no metavariables
(`mvars = 0`)
-/
def CliTest.concrete : CliTest → Prop := fun test => test.mvars = 0

instance {test : CliTest} : Decidable test.concrete :=
 inferInstanceAs (DecidableEq Nat) test.mvars 0


structure ConcreteCliTest where
  name : Name
  context : Context
  ty : Ty
  -- TODO: add support for impure CLI tests
  code : MCom 0 context .pure ty

def InstCombine.MTy.cast_concrete (mvars : Nat) (ty : InstCombine.MTy mvars) (hMvars : mvars = 0) : InstCombine.MTy 0 :=
    hMvars ▸ ty

def InstCombine.MTy.cast_concrete? (mvars : Nat) (ty : InstCombine.MTy mvars) : Option <| InstCombine.MTy 0 :=
  if h : mvars = 0 then
    some <| cast_concrete mvars ty h
   else
     none

def MLIR.AST.Context.cast_concrete (mvars : Nat) (ctxt : MContext mvars)
  (hMVars : mvars = 0) : MContext 0 := hMVars ▸ ctxt

def MLIR.AST.Context.cast_concrete? (mvars : Nat) (ctxt : MContext mvars) :
Option <| MContext 0 :=
  if h : mvars = 0 then
    some <| cast_concrete mvars ctxt h
   else
     none

-- TODO: The commented code below is an attempt at generalizing this to
-- parametrized code, i.e. with mvars. This should be addressed later.
-- (see https://github.com/opencompl/ssa/issues/174)
/-
 mutual
 def Com.cast_concrete (mvars : Nat) (ctxt : MContext mvars) (ty : InstCombine.MTy mvars)
    (code : MCom mvars ctxt ty) (hMvars : mvars = 0) :
     Σ new : MContext 0 × InstCombine.MTy 0, MCom 0 new.1 new.2 :=
    match code with
    | .ret v =>
        let f := fun t => InstCombine.MTy.cast_concrete mvars t hMvars
        let ty' := f ty
        let ctxt' := (ctxt.map f)
        let v' : Ctxt.Var ctxt' ty' := v.toMap
        Sigma.mk (ctxt', ty') (Com.ret v')
     | .lete (α := t) e b =>
        let Sigma.mk (ctxt', ty') e' := Expr.cast_concrete mvars ctxt t e hMvars
        let Sigma.mk (ctxt'', ty'') b' := Com.cast_concrete mvars (t::ctxt) ty b hMvars
        by
         simp at e'
         simp at b'
         have hTy' : ty'' = ty' := by sorry
         have hCtxt' : ty' :: (ctxt', ty'').1 = ctxt'' := by sorry
         --exact Sigma.mk (ctxt', ty') <| .lete e' (hTy' ▸ hCtxt' ▸ b')
         sorry

 def Expr.cast_concrete (mvars : Nat) (ctxt : MContext mvars) (ty : MTy mvars)
    (code : MExpr mvars ctxt ty) (hMvars : mvars = 0) :
     Σ new : MContext 0 × InstCombine.MTy 0, MExpr 0 new.1 new.2 := sorry

 end
def CliTest.cast_concrete (test : CliTest) (hMvars : test.mvars = 0) : ConcreteCliTest :=
  let Sigma.mk (ctxt', ty') code' := test.code.cast_concrete hMvars
  { name := test.name, context := ctxt', ty := ty', code := code'}

def CliTest.cast_concrete? (test : CliTest)  : Option ConcreteCliTest :=
  if h : test.mvars = 0 then
    some <| test.cast_concrete h
  else
    none


-- TODO: This instantiates the parameters in a test. So far we assume al parameters are `Nat`s.
def CliTest.instantiateParameters (test : CliTest) (params : Vector Nat test.mvars) : ConcreteCliTest :=
  if h : test.concrete then
    let context : MLIR.AST.Context 0 := h ▸ test.context
    let ty : InstCombine.MTy 0 := h ▸ test.ty
    let test' : CliTest := { name := test.name, mvars := 0, context := context, ty := ty, code := test.code}
    -- is this the one that's impossible (becaue of the non-theorem of `HEq.congr`?)
    let hContext : HEq context test.context := by sorry --rfl
    let ty : InstCombine.MTy 0 := h ▸ test.ty
    let hTy : HEq ty test.ty := by sorry --rfl
    let code : MLIR.AST.Com context ty := HEq.rec hContext <| HEq.rec hTy test.code
   { name := test.name, context := context, ty := ty, code := code}
  else
  sorry


theorem cast_concrete_len_eq (test : CliTest) (hMvars : test.mvars = 0) : (test.cast_concrete hMvars).context.length = test.context.length := by sorry

def CliTest.eval (test : CliTest) (values : Vector ℤ test.context.length) (hMvars : test.mvars = 0 := by rfl) :
 IO ⟦(test.cast_concrete hMvars).ty⟧ := do
   let concrete_test := test.cast_concrete hMvars
   let h := cast_concrete_len_eq test hMvars
   let values' := h ▸ values
   concrete_test.eval values'
-/

def InstCombine.mkValuation (ctxt : MContext 0) (values : Vector (Option Int) ctxt.length): Ctxt.Valuation ctxt :=
match ctxt, values with
  | [], ⟨[],_⟩ => Ctxt.Valuation.nil
  | ty::tys, ⟨val::vals,hlen⟩ =>
    let valsVec : Vector (Option Int) tys.length := ⟨vals,by aesop⟩
    let valuation' := mkValuation tys valsVec
    match ty with
      | .bitvec (.concrete w) =>
         let newTy : toType (.bitvec (.concrete w)) := Option.map (BitVec.ofInt w) val
         Ctxt.Valuation.snoc valuation' newTy

def ConcreteCliTest.eval (test : ConcreteCliTest) (values : Vector (Option Int) test.context.length) :
 IO ⟦test.ty⟧ := do
  let valuesStack := values.reverse -- we reverse values since context is a stack
  let valuation := InstCombine.mkValuation test.context valuesStack
  return test.code.denote valuation

def ConcreteCliTest.eval? (test : ConcreteCliTest) (values : Array (Option Int)) :
  IO (Except String ⟦test.ty⟧) := do
    if h : values.size = test.context.length then
      let valuesVec : Vector (Option Int) test.context.length := h ▸ (Vector.ofArray values)
      return Except.ok <| (← test.eval valuesVec)
    else
      return Except.error s!"Invalid input length: {values} has length {values.size}, required {test.context.length}"

def ConcreteCliTest.parseableInputs (test : ConcreteCliTest) : Cli.ParseableType (Vector Int test.context.length)
  := inferInstance

def CocreteCliTest.signature (test : ConcreteCliTest) :
  List (InstCombine.MTy 0) × (InstCombine.MTy 0) := (test.context.reverse, test.ty)

def ConcreteCliTest.printSignature (test : ConcreteCliTest) : String :=
  s!"{test.context.reverse} → {test.ty}"

instance {test : ConcreteCliTest} : ToString (toType test.ty) where
 toString := match test.ty with
   | .bitvec w => inferInstanceAs (ToString (Option <| BitVec w)) |>.toString


-- Define an attribute to add up all LLVM tests
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Stateful.2FAggregating.20Macros.3F/near/301067121
abbrev NameExt := SimplePersistentEnvExtension (Name × Name) (NameMap Name)

private def mkExt (name attr : Name) (descr : String) : IO NameExt := do
  let addEntryFn | m, (n3, n4) => m.insert n3 n4
  let ext ← registerSimplePersistentEnvExtension {
    name, addEntryFn
    addImportedFn := mkStateFromImportedEntries addEntryFn {}
  }
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun declName stx attrKind => do
      let s := ext.getState (← getEnv)
      let ns ← stx[1].getArgs.mapM fun stx => do
        let n := stx.getId
        if s.contains n then throwErrorAt stx "test {n} already declared"
        pure n
      modifyEnv $ ns.foldl fun env n =>
        ext.addEntry env (n, declName)
  }
  pure ext

private def mkElab (ext : NameExt) (ty : Lean.Expr) : Elab.Term.TermElabM Lean.Expr := do
  let mut stx := #[]
  for (_, n4) in ext.getState (← getEnv) do
    stx := stx.push $ ← `($(mkIdent n4):ident)
  let listStx := (← `([$stx,*]))
  --let sorted ← `(Array.toList $ Array.qsort ($listStx).toArray (λ x y => Nat.ble x.weightedSize y.weightedSize))
  let list ← `($listStx)
  Elab.Term.elabTerm list (some ty)

syntax (name := llvmTest) "llvmTest " ident+ : attr
initialize llvmExtension : NameExt ←
  mkExt `MLIR.testExtension `llvmTest
    (descr := "LLVM Tests")

elab "llvmTests!" : term <= ty => do
  mkElab llvmExtension ty
