-- should replace with Lean import once Pure is upstream
import SSA.Projects.MLIRSyntax.AST
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.LLVM.Transform.NameMapping
import SSA.Projects.InstCombine.LLVM.Transform.TransformError
import SSA.Core.Framework

import Std.Data.BitVec

universe u

namespace MLIR.AST

open InstCombine (MOp MTy Width)
open Std (BitVec)

-- abbrev Context (φ) := List (MTy φ)

-- abbrev Expr (Γ : Context φ) (ty : MTy φ)  := _root_.Expr (MOp φ) Γ ty
-- abbrev Com (Γ : Context φ) (ty : MTy φ)   := _root_.Com (MOp φ) Γ ty
-- abbrev Var (Γ : Context φ) (ty : MTy φ)   := _root_.Ctxt.Var Γ ty

-- abbrev Com.lete (body : Expr Γ ty₁) (rest : Com (ty₁::Γ) ty₂) : Com Γ ty₂ :=
--   _root_.Com.lete body rest

-- namespace TransformError

instance : Lean.ToFormat (MTy φ) where
  format := repr

section Monads

/-!
  Even though we technically only need to know the `Ty` type,
  our typeclass hierarchy is fully based on `Op`.
  It is thus more convenient to incorporate `Op` in these types, so that there will be no ambiguity
  errors.
-/

abbrev ExceptM  (Op) [OpSignature Op Ty] := Except (TransformError Ty)
abbrev BuilderM (Op) [OpSignature Op Ty] := StateT NameMapping (ExceptM Op)
abbrev ReaderM  (Op) [OpSignature Op Ty] := ReaderT NameMapping (ExceptM Op)

-- instance : MonadLift ReaderM BuilderM where

-- variable {Op Ty} [OpSignature Op Ty]

instance {Op : Type} [OpSignature Op Ty] : MonadLift (ReaderM Op) (BuilderM Op) where
  monadLift x := do (ReaderT.run x (←get) : ExceptM ..)

instance {Op : Type} [OpSignature Op Ty] : MonadLift (ExceptM Op) (ReaderM Op) where
  monadLift x := do return ←x

def BuilderM.runWithNewMapping {Op : Type} [OpSignature Op Ty] (k : BuilderM Op α) : ExceptM Op α :=
  Prod.fst <$> StateT.run k []

end Monads

class TransformDialect (Op : Type) (Ty : outParam (Type)) (φ : outParam Nat) extends OpSignature Op Ty where
  mkType   : MLIRType φ → ExceptM Op Ty
  mkReturn : (Γ : List Ty) → (opStx : AST.Op φ) → (args : List (Σ (ty : Ty), Ctxt.Var Γ ty))
    → ReaderM Op (Σ ty, _root_.Com Op Γ ty)
  mkExpr   : (Γ : List Ty) → (opStx : AST.Op φ) → (args : List (Σ (ty : Ty), Ctxt.Var Γ ty))
    → ReaderM Op (Σ ty, _root_.Expr Op Γ ty)




variable {Op Ty φ} [OpSignature Op Ty]
abbrev Context (Ty) := List (Ty)

-- abbrev Expr (Γ : Context Ty) (ty : Ty)  := _root_.Expr Op Γ ty
-- abbrev Com (Γ : Context Ty) (ty : Ty)   := _root_.Com Op Γ ty
-- abbrev Var (Γ : Context Ty) (ty : Ty)   := Ctxt.Var Γ ty
-- variable [d : TransformDialect Op Ty φ] [DecidableEq Ty]

-- abbrev Com.lete {Γ : Context Ty} (body : Expr Γ ty₁) (rest : Com Op (ty₁::Γ) ty₂) : Com Op Γ ty₂ :=
--   _root_.Com.lete body rest





structure DerivedContext (Γ : Context Ty) where
  ctxt : Context Ty
  diff : Ctxt.Diff Γ ctxt

namespace DerivedContext

/-- Every context is trivially derived from itself -/
abbrev ofContext (Γ : Context Ty) : DerivedContext Γ := ⟨Γ, .zero _⟩

/-- `snoc` of a derived context applies `snoc` to the underlying context, and updates the diff -/
def snoc {Γ : Context Ty} : DerivedContext Γ → Ty → DerivedContext Γ
  | ⟨ctxt, diff⟩, ty => ⟨ty::ctxt, diff.toSnoc⟩

instance {Γ : Context Ty} : CoeHead (DerivedContext Γ) (Context Ty) where
  coe := fun ⟨Γ', _⟩ => Γ'

instance {Γ : Context Ty} : CoeDep (Context Ty) Γ (DerivedContext Γ) where
  coe := ⟨Γ, .zero _⟩

instance {Γ : Context Ty} {Γ' : DerivedContext Γ} :
    CoeHead (DerivedContext (Γ' : Context Ty)) (DerivedContext Γ) where
  coe := fun ⟨Γ'', diff⟩ => ⟨Γ'', Γ'.diff + diff⟩

instance {Γ : Context Ty} {Γ' : DerivedContext Γ} : Coe (Expr Op Γ t) (Expr Op Γ'.ctxt t) where
  coe e := e.changeVars Γ'.diff.toHom

instance {Γ' : DerivedContext Γ} : Coe (Ctxt.Var Γ t) (Ctxt.Var (Γ' : Context Ty) t) where
  coe v := Γ'.diff.toHom v

end DerivedContext

/--
  Add a new variable to the context, and record it's (absolute) index in the name mapping

  Throws an error if the variable name already exists in the mapping, essentially disallowing
  shadowing
-/
def addValToMapping (Γ : Context (MTy φ)) (name : String) (ty : MTy φ) :
    BuilderM (MOp φ) (Σ (Γ' : DerivedContext Γ), Ctxt.Var Γ'.ctxt ty) := do
  let some nm := (←get).add name
    | throw <| .nameAlreadyDeclared name
  set nm
  return ⟨DerivedContext.ofContext Γ |>.snoc ty, Ctxt.Var.last ..⟩

/--
  Look up a name from the name mapping, and return the corresponding variable in the given context.

  Throws an error if the name is not present in the mapping (this indicates the name may be free),
  or if the type of the variable in the context is different from `expectedType`
-/
def getValFromContext (Γ : Context (MTy φ)) (name : String) (expectedType : MTy φ) :
    ReaderM (MOp φ) (Ctxt.Var Γ expectedType) := do
  let index := (←read).lookup name
  let some index := index | throw <| .undeclaredName name
  let n := Γ.length
  if h : index >= n then
    /-  This should not happen, it indicates the passed context `Γ` is out of sync with the
        namemapping stored in the monad -/
    throw <| .indexOutOfBounds name index n
  else
    let t := List.get Γ ⟨index, Nat.lt_of_not_le h⟩
    if h : t = expectedType then
      return ⟨index, by simp[←h, ←List.get?_eq_get]⟩
    else
      throw <| .typeError expectedType t

def BuilderM.isOk {α : Type} (x : BuilderM Op α) : Bool :=
  match x.run [] with
  | Except.ok _ => true
  | Except.error _ => false

def BuilderM.isErr {α : Type} (x : BuilderM Op α) : Bool :=
  match x.run [] with
  | Except.ok _ => true
  | Except.error _ => false

#check Ctxt.Var
def mkUnaryOp {Γ : Ctxt (MTy φ)} {ty : MTy φ} (op : MOp φ)
  (e : Ctxt.Var Γ ty) : ExceptM (MOp φ) <| Expr (MOp φ) Γ ty :=
 match ty with
 | .bitvec w =>
   match op with
   -- Can't use a single arm, Lean won't write the rhs accordingly
    | .neg w' => if h : w = w'
      then return ⟨
        .neg w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e) .nil,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .not w' => if h : w = w'
      then return ⟨
        .not w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e) .nil,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .copy w' => if h : w = w'
      then return ⟨
        .copy w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e) .nil,
        .nil
      ⟩
      else throw <| .widthError w w'
    | _ => throw <| .unsupportedUnaryOp

def mkBinOp {Γ : Ctxt (MTy φ)} {ty : MTy φ} (op : MOp φ)
    (e₁ e₂ : Ctxt.Var Γ ty) : ExceptM (MOp φ) <| Expr (MOp φ) Γ ty :=
 match ty with
 | .bitvec w =>
   match op with
   -- Can't use a single arm, Lean won't write the rhs accordingly
    | .add w' => if h : w = w'
      then return ⟨
        .add w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .and w' => if h : w = w'
      then return ⟨
        .and w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .or w' => if h : w = w'
      then return ⟨
        .or w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .xor w' => if h : w = w'
      then return ⟨
        .xor w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .shl w' => if h : w = w'
      then return ⟨
        .shl w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .lshr w' => if h : w = w'
      then return ⟨
        .lshr w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
    | .ashr w' => if h : w = w'
      then return ⟨
        .ashr w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
     | .urem w' => if h : w = w'
      then return ⟨
        .urem w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
     | .srem w' => if h : w = w'
      then return ⟨
        .srem w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
     | .mul w' => if h : w = w'
      then return ⟨
        .mul w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
      | .sub w' => if h : w = w'
      then return ⟨
        .sub w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
      | .sdiv w' => if h : w = w'
      then return ⟨
        .sdiv w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
      | .udiv w' => if  h : w = w'
      then return ⟨
        .udiv w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
    | op => throw <| .unsupportedBinaryOp s!"unsupported binary operation {op}"

def mkIcmp {Γ : Ctxt _} {ty : MTy φ} (op : MOp φ)
    (e₁ e₂ : Ctxt.Var Γ ty) : ExceptM (MOp φ) <| Expr (MOp φ) Γ (.bitvec 1) :=
  match ty with
  | .bitvec w =>
    match op with
      | .icmp p w' => if  h : w = w'
      then return ⟨
        .icmp p w',
        by simp [OpSignature.outTy, signature, h],
        .cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
        .nil
      ⟩
      else throw <| .widthError w w'
      | _ => throw <| .unsupportedOp "unsupported icmp operation"

def mkSelect {Γ : Ctxt (MTy φ)} {ty : MTy φ} (op : MOp φ)
    (c : Ctxt.Var Γ (.bitvec 1)) (e₁ e₂ : Ctxt.Var Γ ty) :
    ExceptM (MOp φ) <| Expr (MOp φ) Γ ty :=
  match ty with
  | .bitvec w =>
    match op with
        | .select w' => if  h : w = w'
        then return ⟨
          .select w',
          by simp [OpSignature.outTy, signature, h],
          .cons c <|.cons (h ▸ e₁) <| .cons (h ▸ e₂) .nil ,
          .nil
        ⟩
        else throw <| .widthError w w'
        | _ => throw <| .unsupportedOp "Unsupported select operation"

def mkOpExpr {Γ : Context (MTy φ)} (op : MOp φ)
    (arg : HVector (fun t => Ctxt.Var Γ t) (OpSignature.sig op)) :
    ExceptM (MOp φ) <| Expr (MOp φ) Γ (OpSignature.outTy op) :=
  match op with
  | .and _ | .or _ | .xor _ | .shl _ | .lshr _ | .ashr _
  | .add _ | .mul _ | .sub _ | .udiv _ | .sdiv _
  | .srem _ | .urem _  =>
    let (e₁, e₂) := arg.toTuple
    mkBinOp op e₁ e₂
  | .icmp _ _ =>
    let (e₁, e₂) := arg.toTuple
    mkIcmp op e₁ e₂
  | .not _ | .neg _ | .copy _ =>
    mkUnaryOp op arg.head
  | .select _ =>
    let (c, e₁, e₂) := arg.toTuple
    mkSelect op c e₁ e₂
  | .const .. => throw <| .unsupportedOp  "Tried to build Op expression from constant"

def MLIRType.mkTy : MLIRType φ → ExceptM (MOp φ) (MTy φ)
  | MLIRType.int Signedness.Signless w => do
    return .bitvec w
  | _ => throw .unsupportedType -- "Unsupported type"

def TypedSSAVal.mkTy : TypedSSAVal φ → ExceptM (MOp φ) (MTy φ)
  | (.SSAVal _, ty) => MLIRType.mkTy ty

def mkVal (ty : InstCombine.Ty) : Int → BitVec ty.width
  | val => BitVec.ofInt ty.width val

/-- Translate a `TypedSSAVal` (a name with an expected type), to a variable in the context.
    This expects the name to have already been declared before -/
def TypedSSAVal.mkVal (Γ : Context (MTy φ)) : TypedSSAVal φ →
    ReaderM (MOp φ) (Σ (ty : MTy φ), Ctxt.Var Γ ty)
| (.SSAVal valStx, tyStx) => do
    let ty ← MLIRType.mkTy tyStx
    let var ← getValFromContext Γ valStx ty
    return ⟨ty, var⟩

/-- Declare a new variable,
    by adding the passed name to the name mapping stored in the monad state -/
def TypedSSAVal.newVal (Γ : Context (MTy φ)) : TypedSSAVal φ →
    BuilderM (MOp φ) (Σ (Γ' : DerivedContext Γ) (ty : MTy φ), Ctxt.Var Γ'.ctxt ty)
| (.SSAVal valStx, tyStx) => do
    let ty ← MLIRType.mkTy tyStx
    let ⟨Γ, var⟩ ← addValToMapping Γ valStx ty
    return ⟨Γ, ty, var⟩

def mkExpr (Γ : Context (MTy φ)) (opStx : MLIR.AST.Op φ) : ReaderM (MOp φ) (Σ ty, Expr (MOp φ) Γ ty) := do
  match opStx.args with
  | v₁Stx::v₂Stx::v₃Stx::[] =>
      let ⟨.bitvec w₁, v₁⟩ ← TypedSSAVal.mkVal Γ v₁Stx
      let ⟨.bitvec w₂, v₂⟩ ← TypedSSAVal.mkVal Γ v₂Stx
      let ⟨.bitvec w₃, v₃⟩ ← TypedSSAVal.mkVal Γ v₃Stx
      match opStx.name with
      | "llvm.select" =>
        if hw1 : w₁ = 1 then
          if hw23 : w₂  = w₃ then
            let selectOp ← mkSelect (MOp.select w₂) (hw1 ▸ v₁) v₂ (hw23 ▸ v₃)
            return ⟨.bitvec w₂, selectOp⟩
          else
            throw <| .widthError w₁ w₂ -- s!"mismatched types {ty₁} ≠ {ty₂} in binary op"
        else throw <| .unsupportedOp s!"expected select condtion to have width 1, found width '{w₁}'"
      | op => throw <| .unsupportedOp s!"Unsuported ternary operation or invalid arguments '{op}'"
  | v₁Stx::v₂Stx::[] =>
    let ⟨.bitvec w₁, v₁⟩ ← TypedSSAVal.mkVal Γ v₁Stx
    let ⟨.bitvec w₂, v₂⟩ ← TypedSSAVal.mkVal Γ v₂Stx
    -- let ty₁ := ty₁.instantiave
    let op ← match opStx.name with
      | "llvm.and"    => pure (MOp.and w₁)
      | "llvm.or"     => pure (MOp.or w₁)
      | "llvm.xor"    => pure (MOp.xor w₁)
      | "llvm.shl"    => pure (MOp.shl w₁)
      | "llvm.lshr"   => pure (MOp.lshr w₁)
      | "llvm.ashr"   => pure (MOp.ashr w₁)
      | "llvm.urem"   => pure (MOp.urem w₁)
      | "llvm.srem"   => pure (MOp.srem w₁)
      | "llvm.add"    => pure (MOp.add w₁)
      | "llvm.mul"    => pure (MOp.mul w₁)
      | "llvm.sub"    => pure (MOp.sub w₁)
      | "llvm.sdiv"   => pure (MOp.sdiv w₁)
      | "llvm.udiv"   => pure (MOp.udiv w₁)
      | "llvm.icmp.eq" => pure (MOp.icmp LLVM.IntPredicate.eq w₁)
      | "llvm.icmp.ne" => pure (MOp.icmp LLVM.IntPredicate.ne w₁)
      | "llvm.icmp.ugt" => pure (MOp.icmp LLVM.IntPredicate.ugt w₁)
      | "llvm.icmp.uge" => pure (MOp.icmp LLVM.IntPredicate.uge w₁)
      | "llvm.icmp.ult" => pure (MOp.icmp LLVM.IntPredicate.ult w₁)
      | "llvm.icmp.ule" => pure (MOp.icmp LLVM.IntPredicate.ule w₁)
      | "llvm.icmp.sgt" => pure (MOp.icmp LLVM.IntPredicate.sgt w₁)
      | "llvm.icmp.sge" => pure (MOp.icmp LLVM.IntPredicate.sge w₁)
      | "llvm.icmp.slt" => pure (MOp.icmp LLVM.IntPredicate.slt w₁)
      | "llvm.icmp.sle" => pure (MOp.icmp LLVM.IntPredicate.sle w₁)
      | opstr => throw <| .unsupportedOp s!"Unsuported binary operation or invalid arguments '{opstr}'"
    match op with
    | .icmp .. =>
      if hty : w₁ = w₂ then
        let icmpOp ← mkIcmp op v₁ (hty ▸ v₂)
        return ⟨.bitvec 1, icmpOp⟩
      else
        throw <| .widthError w₁ w₂ -- s!"mismatched types {ty₁} ≠ {ty₂} in binary op"
    | _ =>
      if hty : w₁ = w₂ then
        let binOp ← mkBinOp op v₁ (hty ▸ v₂)
        return ⟨.bitvec w₁, binOp⟩
      else
        throw <| .widthError w₁ w₂ -- s!"mismatched types {ty₁} ≠ {ty₂} in binary op"
  | vStx::[] =>
    let ⟨.bitvec w, v⟩ ← TypedSSAVal.mkVal Γ vStx
    let op ← match opStx.name with
        | "llvm.not" => pure <| MOp.not w
        | "llvm.neg" => pure <| MOp.neg w
        | "llvm.copy" => pure <| MOp.copy w
        | _ => throw <| .generic s!"Unknown (unary) operation syntax {opStx.name}"
    let op ← mkUnaryOp op v
    return ⟨.bitvec w, op⟩
  | [] =>
    if opStx.name ==  "llvm.mlir.constant"
    then do
    let some att := opStx.attrs.getAttr "value"
      | throw <| .generic "tried to resolve constant without 'value' attribute"
    match att with
      | .int val ty =>
          let opTy@(MTy.bitvec w) ← MLIRType.mkTy ty -- ty.mkTy
          return ⟨opTy, ⟨
            MOp.const w val,
            by simp [OpSignature.outTy, signature, *],
            HVector.nil,
            HVector.nil
          ⟩⟩
      | _ => throw <| .generic "invalid constant attribute"
    else
      throw <| .generic s!"invalid (0-ary) expression {opStx.name}"
  | _ => throw <| .generic s!"unsupported expression (with unsupported arity) {opStx.name}"

def mkReturn (Γ : Context (MTy φ)) (opStx : MLIR.AST.Op φ) : ReaderM (MOp φ) (Σ ty, Com (MOp φ) Γ ty) :=
  if opStx.name == "llvm.return"
  then match opStx.args with
  | vStx::[] => do
    let ⟨ty, v⟩ ← TypedSSAVal.mkVal Γ vStx
    return ⟨ty, _root_.Com.ret v⟩
  | _ => throw <| .generic s!"Ill-formed return statement (wrong arity, expected 1, got {opStx.args.length})"
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"

/-- Given a list of `TypedSSAVal`s, treat each as a binder and declare a new variable with the
    given name and type -/
private def declareBindings (Γ : Context (MTy φ)) (vals : List (TypedSSAVal φ)) :
    BuilderM (MOp φ) (DerivedContext Γ) := do
  vals.foldlM (fun Γ' ssaVal => do
    let ⟨Γ'', _⟩ ← TypedSSAVal.newVal Γ'.ctxt ssaVal
    return Γ''
  ) (.ofContext Γ)

private def mkComHelper (Γ : Context (MTy φ)) :
    List (MLIR.AST.Op φ) → BuilderM (MOp φ) (Σ (ty : _), Com (MOp φ) Γ ty)
  | [retStx] => mkReturn Γ retStx
  | lete::rest => do
    let ⟨ty₁, expr⟩ ← (mkExpr Γ lete)
    if h : lete.res.length != 1 then
      throw <| .generic s!"Each let-binding must have exactly one name on the left-hand side. Operations with multiple, or no, results are not yet supported.\n\tExpected a list of length one, found `{repr lete}`"
    else
      let _ ← addValToMapping Γ (lete.res[0]'(by simp_all) |>.fst |> SSAValToString) ty₁
      let ⟨ty₂, body⟩ ← mkComHelper (ty₁::Γ) rest
      return ⟨ty₂, Com.lete expr body⟩
  | [] => throw <| .generic "Ill-formed (empty) block"

def mkCom (reg : MLIR.AST.Region φ) : ExceptM (MOp φ)  (Σ (Γ : Context (MTy φ)) (ty : MTy φ), Com (MOp φ) Γ ty) :=
  match reg.ops with
  | [] => throw <| .generic "Ill-formed region (empty)"
  | coms => BuilderM.runWithNewMapping <| do
    let Γ ← declareBindings ∅ reg.args
    let com ← mkComHelper Γ coms
    return ⟨Γ, com⟩

/-!
  ## Instantiation
  Finally, we show how to instantiate a family of programs to a concrete program
-/

def _root_.InstCombine.MTy.instantiate (vals : Vector Nat φ) : MTy φ → InstCombine.Ty
  | .bitvec w => .bitvec <| .concrete <| w.instantiate vals

def _root_.InstCombine.MOp.instantiate (vals : Vector Nat φ) : MOp φ → InstCombine.Op
  | .and w => .and (w.instantiate vals)
  | .or w => .or (w.instantiate vals)
  | .not w => .not (w.instantiate vals)
  | .xor w => .xor (w.instantiate vals)
  | .shl w => .shl (w.instantiate vals)
  | .lshr w => .lshr (w.instantiate vals)
  | .ashr w => .ashr (w.instantiate vals)
  | .urem w => .urem (w.instantiate vals)
  | .srem w => .srem (w.instantiate vals)
  | .select w => .select (w.instantiate vals)
  | .add w => .add (w.instantiate vals)
  | .mul w => .mul (w.instantiate vals)
  | .sub w => .sub (w.instantiate vals)
  | .neg w => .neg (w.instantiate vals)
  | .copy w => .copy (w.instantiate vals)
  | .sdiv w => .sdiv (w.instantiate vals)
  | .udiv w => .udiv (w.instantiate vals)
  | .icmp c w => .icmp c (w.instantiate vals)
  | .const w val => .const (w.instantiate vals) val

def Context.instantiate (vals : Vector Nat φ) (Γ : Context (MTy φ)) : Ctxt InstCombine.Ty :=
  Γ.map (MTy.instantiate vals)

def MOp.instantiateCom (vals : Vector Nat φ) : DialectMorphism (MOp φ) (InstCombine.Op) where
  mapOp := MOp.instantiate vals
  mapTy := MTy.instantiate vals
  preserves_signature op := by
    simp only [MTy.instantiate, MOp.instantiate, ConcreteOrMVar.instantiate, (· <$> ·), signature,
      InstCombine.MOp.sig, InstCombine.MOp.outTy, Function.comp_apply, List.map, Signature.mk.injEq,
      true_and]
    cases op <;> simp only [List.map, and_self, List.cons.injEq]


open InstCombine (Op Ty) in
def mkComInstantiate (reg : Region φ) :
    ExceptM (MOp φ) (Vector Nat φ → Σ (Γ : Ctxt InstCombine.Ty) (ty : InstCombine.Ty), Com InstCombine.Op Γ ty) := do
  let ⟨Γ, ty, com⟩ ← mkCom reg
  return fun vals =>
    ⟨Γ.instantiate vals, ty.instantiate vals, com.map (MOp.instantiateCom vals)⟩

end MLIR.AST
