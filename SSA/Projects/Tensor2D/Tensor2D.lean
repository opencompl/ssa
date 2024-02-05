import SSA.Core.Framework
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import SSA.Core.Util
import SSA.Core.Util

namespace Tensor2D
/-- Type of tensor dimensions and indexes into tensor dimensions.
  NOTE: see interaction with `linarith` where we need to unfold `Index` into `ℕ`
  https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Ergonomics.3A.20linarith.20does.20not.20work.20on.20Nat.20alias/near/365631549
-/
abbrev Index := ℕ

/-- Tensor2d with existential dimension sizes. -/
structure Tensor2d' (α : Type) where
  dim₀ : Index
  dim₁ : Index
  mat : Matrix (Fin dim₀) (Fin dim₁) α

def Tensor2d'.error (α : Type) : Tensor2d' α where
  dim₀ := 0
  dim₁ := 0
  mat := Matrix.of fun x _y => x.elim0

def Tensor2d'.transpose (t : Tensor2d' α) : Tensor2d' α where
  dim₀ := t.dim₁
  dim₁ := t.dim₀
  mat := t.mat.transpose

theorem Tensor2d'.transpose_transpose (t : Tensor2d' α) : t.transpose.transpose = t := rfl

def Tensor2d'.map (f : α → β) (t : Tensor2d' α) : Tensor2d' β where
  dim₀ := t.dim₀
  dim₁ := t.dim₁
  mat := t.mat.map f

theorem Tensor2d'.map_functorial (g : β → γ) (f : α → β) (t : Tensor2d' α) : t.map (g ∘ f) = (t.map f).map g := rfl

theorem Tensor2d'.map_error (f : α → β) : (Tensor2d'.error α).map f = Tensor2d'.error β := by {
  simp [error, map]
  unfold Matrix.map
  simp [Matrix.of]
  funext i j
  obtain ⟨i, hi⟩ := i
  contradiction
}
/-- K combinator / constant function. -/
def const (a : α) (_b : β) : α := a

def Tensor2d'.fill (v : β) (t : Tensor2d' α) : Tensor2d' β := t.map (const v)

/-- extract a submatrix of (sz₀ × sz₁) size at offset (δ₀, δ₁). Fails if this is out of bounds. -/
def Tensor2d'.extract (δ₀ δ₁ : Index) (sz₀ sz₁ : Index) (t : Tensor2d' α) : (Tensor2d' α) :=
  if SZ0 : δ₀ + sz₀ ≤ t.dim₀ then
    if SZ1 : δ₁ + sz₁ ≤ t.dim₁ then
      {
        dim₀ := sz₀,
        dim₁ := sz₁,
        mat := Matrix.of fun (ix₀ : Fin sz₀) (ix₁ : Fin sz₁) =>
          have INBOUNDS0 : δ₀ + ix₀ < t.dim₀ := by simp[Index] at *; linarith[ix₀.isLt]
          have INBOUNDS1 : δ₁ + ix₁ < t.dim₁ := by simp[Index] at *; linarith[ix₁.isLt]
          t.mat ⟨δ₀ + ix₀, INBOUNDS0⟩ ⟨δ₁ + ix₁, INBOUNDS1⟩
        : Tensor2d' α
      }
    else Tensor2d'.error (α := α)
  else Tensor2d'.error (α := α)

/-- This implies fill_extract -/
theorem Tensor2d'.map_extract (δ₀ δ₁ sz₀ sz₁ : ℕ) (t : Tensor2d' α) (f : α → β) :
  (t.map f).extract δ₀ δ₁ sz₀ sz₁ = (t.extract δ₀ δ₁ sz₀ sz₁).map f := by {
    simp only [extract];
    have MAP_dim₀ : (map f t).dim₀ = t.dim₀ := rfl
    simp only [MAP_dim₀]
    have MAP_dim₁ : (map f t).dim₁ = t.dim₁ := rfl
    simp only [MAP_dim₁]
    by_cases H₀ : δ₀ + sz₀ ≤ t.dim₀ <;> simp[H₀, Tensor2d'.map_error];
    by_cases H₁ : δ₁ + sz₁ ≤ t.dim₁ <;> simp[H₁, Tensor2d'.map_error];
    simp only [map, Matrix.map, Matrix.of_apply, Int.ofNat_add_ofNat, Eq.ndrec, Int.rawCast, Int.cast_id,
      Nat.rawCast, Nat.cast_id, Int.ofNat_eq_coe, eq_mp_eq_cast, id_eq]
}

theorem Tensor2d'.fill_extract (δ₀ δ₁ sz₀ sz₁ : ℕ) (t : Tensor2d' α) (v : β) :
  (t.fill v).extract δ₀ δ₁ sz₀ sz₁ = (t.extract δ₀ δ₁ sz₀ sz₁).fill v := by {
    simp only[fill, Tensor2d'.map_extract]
}


inductive Op
| add
-- TODO: generalize 'const'
| constIx (v: Nat) | constTensor (t : Tensor2d' Int) | constInt (v : Int)
| sub
| map2d
| fill2d
| extract2d

inductive Ty
| int : Ty
| ix : Ty
| tensor2d : Ty
deriving DecidableEq, Inhabited

def Ty.toType : Ty → Type
| .int => Int
| .ix => Index
| .tensor2d => Tensor2d' Int -- TODO: eventually generalize to arbitrary type.

instance : Goedel Ty where toType := Ty.toType

@[reducible, simp]
def Op.outTy : Op → Ty
  | .add => .int
  | .sub => .int
  | .constIx _ => .ix
  | .constTensor _ => .tensor2d
  | .constInt _ => .int
  | .map2d | .fill2d => .tensor2d
  | .extract2d => .tensor2d

@[reducible, simp]
def Op.sig : Op → List Ty
  | .add => [.int, .int]
  | .sub => [.int, .int]
  | .constIx _  => []
  | .constTensor _  => []
  | .constInt _  => []
  | .map2d => [.tensor2d]
  | .fill2d => [.int, .tensor2d]
  | .extract2d => [.ix, .ix, .ix, .ix, .tensor2d]

@[reducible, simp]
def Op.regSig : Op → RegionSignature Ty
  | .map2d => [([.int], .int)]
  | _ => []

@[reducible]
instance : OpSignature Op Ty where
  signature op := ⟨op.sig, op.regSig, op.outTy⟩


/-
-- error: unknown free variable: _kernel_fresh.97
@[reducible]
instance : OpDenote Op Ty where
  denote
  | .constIx v, _, _ => v
  | .constTensor v, _, _ => v
  | .constInt v, _, _ => v
  | .add, (.cons x (.cons y nil)), _ =>
    let x : Int := x;
    let y : Int := y;
    x + y
  | .sub, (.cons x (.cons y nil)), _ =>
    let x : Int := x;
    let y : Int := y;
    let out : Int := x - y
    out
  | .map2d, (.cons t .nil), (.cons r .nil) =>
    let t : Tensor2d' Int := t
    -- Is there a cleaner way to build the data below?
    let f : Int → Int := fun v =>  r (Ctxt.Valuation.ofHVector <| (.cons v .nil))
    t.map f
  | .fill2d, (.cons v (.cons t nil)), _ =>
    t.fill v
  | .extract2d, (.cons δ₁ (.cons δ₂ (.cons sz₁ (.cons sz₂ (.cons t .nil))))), _ =>
    t.extract δ₁ δ₂ sz₁ sz₂

-- NOTE: there is no way in MLIR to talk about composition of functions, so `map . map` is out
--       as a peephole rewrite
-- TODO: enable not writing the unit argument if not used.
-- TOTHINK: See that we encode the variables as constant values.
--          We should instead be able to have these be SSA variables of the
--          correct type. Not sure how to achieve this, as doing this
--          naively leads to errors about incorrect types:
--          https://github.com/bollu/ssa/issues/28
open SSA EDSL2 in
theorem map_fill_2d
    (t : Tensor2d' Int)
    (sz₀ sz₁ ix₀ ix₁: Index)
    (i : Int):
  TSSA.eval
  (e := e) (Op := Op) [dsl_bb2|
    return op:fill2d (op:constInt(i) (),
      op:extract2d (
          ((op:constIx(sz₀) () , op:constIx(sz₁) ()),
           (op:constIx(ix₀) (), op:constIx(ix₁) ())),
           op:constTensor(t) ()))
  ] =
  TSSA.eval (e := e) (Op := Op) [dsl_bb2|
    return op:extract2d
      (((op:constIx(sz₀) (), op:constIx(sz₁) ()),
        (op:constIx(ix₀) (), op:constIx(ix₁) ())),
        op:fill2d (op:constInt(i) (), op:constTensor(t) ()))
  ] := by {
    dsimp only[TSSAIndex.eval, TSSA.eval]
    simp[UserType.mkPair, TypedUserSemantics.eval, eval]
    simp[Tensor2d'.fill_extract]
  }
-/
end Tensor2D
