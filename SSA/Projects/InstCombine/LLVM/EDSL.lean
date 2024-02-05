import Qq
import SSA.Projects.InstCombine.Base
import Std.Data.BitVec
import SSA.Projects.MLIRSyntax.AST
import SSA.Projects.MLIRSyntax.EDSL
import SSA.Projects.InstCombine.LLVM.Transform
-- import SSA.Projects.InstCombine.LLVM.Transform.Dialects.InstCombine

open Qq Lean Meta Elab.Term Elab Command
open InstCombine (MOp MTy Width)

open MLIR

namespace InstcombineTransformDialect

def mkUnaryOp {Γ : Ctxt (MTy φ)} {w : Width φ} (op : MOp.UnaryOp)
  (e : Ctxt.Var Γ (.bitvec w)) : Expr (MOp φ) Γ (.bitvec w) :=
  ⟨
    .unary w op,
    rfl,
    .cons e .nil,
    .nil
  ⟩


def mkBinOp {Γ : Ctxt (MTy φ)} {w : Width φ} (op : MOp.BinaryOp)
    (e₁ e₂ : Ctxt.Var Γ (.bitvec w)) : Expr (MOp φ) Γ (.bitvec w) :=
  ⟨
    .binary w op,
    rfl,
    .cons e₁ <| .cons e₂ .nil ,
    .nil
  ⟩

def mkIcmp {Γ : Ctxt _} {w : Width φ} (p : LLVM.IntPredicate)
    (e₁ e₂ : Ctxt.Var Γ (.bitvec w)) : Expr (MOp φ) Γ (.bitvec 1) :=
  ⟨
    .icmp p w,
    rfl,
    .cons e₁ <| .cons e₂ .nil,
    .nil
  ⟩


def mkSelect {Γ : Ctxt (MTy φ)} {ty : (MTy φ)} (op : MOp φ)
    (c : Ctxt.Var Γ (.bitvec 1)) (e₁ e₂ : Ctxt.Var Γ ty) :
    MLIR.AST.ExceptM (MOp φ) <| Expr (MOp φ) Γ ty :=
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

def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM (MOp φ) (MTy φ)
  | MLIR.AST.MLIRType.int MLIR.AST.Signedness.Signless w => do
    return .bitvec w
  | _ => throw .unsupportedType -- "Unsupported type"

instance instTransformTy : MLIR.AST.TransformTy (MOp φ) (MTy φ) φ where
  mkTy := mkTy

def mkExpr (Γ : Ctxt (MTy φ)) (opStx : MLIR.AST.Op φ) : AST.ReaderM (MOp φ) (Σ ty, Expr (MOp φ) Γ ty) := do
  match opStx.args with
  | v₁Stx::v₂Stx::v₃Stx::[] =>
      let ⟨.bitvec w₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
      let ⟨.bitvec w₂, v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx
      let ⟨.bitvec w₃, v₃⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₃Stx
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
    let ⟨.bitvec w,  v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
    let ⟨.bitvec w', v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx

    if hty : w ≠ w' then
      throw <| .widthError w w' -- the arguments don't have the same width!
    else
      let v₂ : Γ.Var (.bitvec w) := (by simpa using hty) ▸ v₂

      let (op : MOp.BinaryOp ⊕ LLVM.IntPredicate) ← match opStx.name with
        | "llvm.and"    => pure <| Sum.inl .and
        | "llvm.or"     => pure <| Sum.inl .or
        | "llvm.xor"    => pure <| Sum.inl .xor
        | "llvm.shl"    => pure <| Sum.inl .shl
        | "llvm.lshr"   => pure <| Sum.inl .lshr
        | "llvm.ashr"   => pure <| Sum.inl .ashr
        | "llvm.urem"   => pure <| Sum.inl .urem
        | "llvm.srem"   => pure <| Sum.inl .srem
        | "llvm.add"    => pure <| Sum.inl .add
        | "llvm.mul"    => pure <| Sum.inl .mul
        | "llvm.sub"    => pure <| Sum.inl .sub
        | "llvm.sdiv"   => pure <| Sum.inl .sdiv
        | "llvm.udiv"   => pure <| Sum.inl .udiv
        | "llvm.icmp.eq"  => pure <| Sum.inr LLVM.IntPredicate.eq
        | "llvm.icmp.ne"  => pure <| Sum.inr LLVM.IntPredicate.ne
        | "llvm.icmp.ugt" => pure <| Sum.inr LLVM.IntPredicate.ugt
        | "llvm.icmp.uge" => pure <| Sum.inr LLVM.IntPredicate.uge
        | "llvm.icmp.ult" => pure <| Sum.inr LLVM.IntPredicate.ult
        | "llvm.icmp.ule" => pure <| Sum.inr LLVM.IntPredicate.ule
        | "llvm.icmp.sgt" => pure <| Sum.inr LLVM.IntPredicate.sgt
        | "llvm.icmp.sge" => pure <| Sum.inr LLVM.IntPredicate.sge
        | "llvm.icmp.slt" => pure <| Sum.inr LLVM.IntPredicate.slt
        | "llvm.icmp.sle" => pure <| Sum.inr LLVM.IntPredicate.sle
        | opstr => throw <| .unsupportedOp s!"Unsuported binary operation or invalid arguments '{opstr}'"
      return match op with
        | .inl binOp  => ⟨.bitvec w, mkBinOp binOp v₁ v₂⟩
        | .inr pred   => ⟨.bitvec 1, mkIcmp pred v₁ v₂⟩
  | vStx::[] =>
    let ⟨.bitvec w, v⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ vStx
    let op ← match opStx.name with
        | "llvm.not"  => pure .not
        | "llvm.neg"  => pure .neg
        | "llvm.copy" => pure .copy
        | _ => throw <| .generic s!"Unknown (unary) operation syntax {opStx.name}"
    return ⟨.bitvec w, mkUnaryOp op v⟩
  | [] =>
    if opStx.name ==  "llvm.mlir.constant"
    then do
    let some att := opStx.attrs.getAttr "value"
      | throw <| .generic "tried to resolve constant without 'value' attribute"
    match att with
      | .int val ty =>
          let opTy@(MTy.bitvec w) ← mkTy ty -- ty.mkTy
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

instance : AST.TransformExpr (MOp φ) (MTy φ) φ where
  mkExpr := mkExpr

def mkReturn (Γ : Ctxt (MTy φ)) (opStx : MLIR.AST.Op φ) : MLIR.AST.ReaderM (MOp φ) (Σ ty, Com (MOp φ) Γ ty) :=
  if opStx.name == "llvm.return"
  then match opStx.args with
  | vStx::[] => do
    let ⟨ty, v⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ vStx
    return ⟨ty, _root_.Com.ret v⟩
  | _ => throw <| .generic s!"Ill-formed return statement (wrong arity, expected 1, got {opStx.args.length})"
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"

instance : AST.TransformReturn (MOp φ) (MTy φ) φ where
  mkReturn := mkReturn


/-!
  ## Instantiation
  Finally, we show how to instantiate a family of programs to a concrete program
-/

def instantiateMTy (vals : Vector Nat φ) : (MTy φ) → InstCombine.Ty
  | .bitvec w => .bitvec <| w.instantiate vals

def instantiateMOp (vals : Vector Nat φ) : MOp φ → InstCombine.Op
  | .binary w binOp => .binary (w.instantiate vals) binOp
  | .unary w unOp => .unary (w.instantiate vals) unOp
  | .select w => .select (w.instantiate vals)
  | .icmp c w => .icmp c (w.instantiate vals)
  | .const w val => .const (w.instantiate vals) val

def instantiateCtxt (vals : Vector Nat φ) (Γ : Ctxt (MTy φ)) : Ctxt InstCombine.Ty :=
  Γ.map (instantiateMTy vals)

def MOp.instantiateCom (vals : Vector Nat φ) : DialectMorphism (MOp φ) (InstCombine.Op) where
  mapOp := instantiateMOp vals
  mapTy := instantiateMTy vals
  preserves_signature op := by
    have h1 : ∀ (φ : Nat), 1 = ConcreteOrMVar.concrete (φ := φ) 1 := by intros φ; rfl
    cases op <;> 
      simp only [instantiateMTy, instantiateMOp, ConcreteOrMVar.instantiate, (· <$> ·), signature,
      InstCombine.MOp.sig, InstCombine.MOp.outTy, Function.comp_apply, List.map, Signature.mk.injEq,
      List.map_cons, List.map_nil, and_self, MTy.bitvec,
      List.cons.injEq, MTy.bitvec.injEq, and_true, true_and, h1]

open InstCombine (Op Ty) in
def mkComInstantiate (reg : MLIR.AST.Region φ) :
    MLIR.AST.ExceptM (MOp φ) (Vector Nat φ → Σ (Γ : Ctxt InstCombine.Ty) (ty : InstCombine.Ty), Com InstCombine.Op Γ ty) := do
  let ⟨Γ, ty, com⟩ ← MLIR.AST.mkCom reg
  return fun vals =>
    ⟨instantiateCtxt vals Γ, instantiateMTy vals ty, com.map (MOp.instantiateCom vals)⟩

end InstcombineTransformDialect


/-
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Cannot.20Find.20.60Real.2Eadd.60/near/402089561
> I would recommend avoiding Qq for pattern matching.
> That part of the Qq implementation is spicy.

Therefore, we choose to match on raw `Expr`.
-/
open MLIR.AST InstCombine in
elab "[alive_icom (" mvars:term,* ")| " reg:mlir_region "]" : term => do
  let ast_stx ← `([mlir_region| $reg])
  let φ : Nat := mvars.getElems.size
  let ast ← elabTermEnsuringTypeQ ast_stx q(Region $φ)
  let mvalues ← `(⟨[$mvars,*], by rfl⟩)
  let mvalues : Q(Vector Nat $φ) ← elabTermEnsuringType mvalues q(Vector Nat $φ)
  let com := q(InstcombineTransformDialect.mkComInstantiate (φ := $φ) $ast |>.map (· $mvalues))
  synthesizeSyntheticMVarsNoPostponing
  let com : Q(MLIR.AST.ExceptM (MOp $φ) (Σ (Γ' : Ctxt (MTy $φ)) (ty : (MTy $φ)), Com (MOp $φ) Γ' ty)) ←
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      withTransparency (mode := TransparencyMode.all) <|
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
macro "[alive_icom| " reg:mlir_region "]" : term => `([alive_icom ()| $reg])
