--import SSA.Core.WellTypedFramework
import SSA.Core.Framework
import SSA.Core.Util
import SSA.Core.Util.ConcreteOrMVar
import SSA.Projects.InstCombine.ForStd
import SSA.Projects.InstCombine.LLVM.Semantics

/-!
  # InstCombine Dialect

  This file defines a dialect of basic arithmetic and bitwise operations on bitvectors.

  The dialect supports types of arbitrary-width bitvectors.
  Thus, some definitions wil be parameterized by `φ`, the number of width meta-variables there are.
  This parameter will usually be either `0`, indicating that all widths are known, concrete values,
  or `1`, indicating there is exactly one distinct width meta-variable.

  In particular, we only define a denotational semantics for concrete programs (i.e., where `φ = 0`)


  see https://releases.llvm.org/14.0.0/docs/LangRef.html#bitwise-binary-operations
-/

namespace InstCombine

open BitVec

open LLVM

abbrev Width φ := ConcreteOrMVar Nat φ

inductive MTy (φ : Nat)
  | bitvec (w : Width φ) : MTy φ
  deriving DecidableEq, Inhabited

abbrev Ty := MTy 0

@[match_pattern] abbrev Ty.bitvec (w : Nat) : Ty := MTy.bitvec (.concrete w)

instance : Repr (MTy φ) where
  reprPrec
    | .bitvec (.concrete w), _ => "i" ++ repr w
    | .bitvec (.mvar ⟨i, _⟩), _ => f!"i$\{%{i}}"

instance : Lean.ToFormat (MTy φ) where
  format := repr

instance : ToString (MTy φ) where
  toString t := repr t |>.pretty

def Ty.width : Ty → Nat
  | .bitvec w => w

@[simp]
theorem Ty.width_eq (ty : Ty) : .bitvec (ty.width) = ty := by
  rcases ty with ⟨w|i⟩
  · rfl
  · exact i.elim0

@[simp]
def BitVec.width {n : Nat} (_ : BitVec n) : Nat := n

instance : TyDenote Ty where
toType := fun
  | .bitvec w => Option <| BitVec w

instance (ty : Ty) : Coe ℤ (TyDenote.toType ty) where
  coe z := match ty with
    | .bitvec w => some <| BitVec.ofInt w z

instance (ty : Ty) : Inhabited (TyDenote.toType ty) where
  default := match ty with
    | .bitvec _ => default

instance : Repr (BitVec n) where
  reprPrec
    | v, n => reprPrec (BitVec.toInt v) n

/-- Homogeneous, unary operations -/
inductive MOp.UnaryOp : Type
  | neg
  | not
  | copy
deriving Repr, DecidableEq, Inhabited

/-- Homogeneous, binary operations -/
inductive MOp.BinaryOp : Type
  | and
  | or
  | xor
  | shl
  | lshr
  | ashr
  | urem
  | srem
  | add
  | mul
  | sub
  | sdiv
  | udiv
deriving Repr, DecidableEq, Inhabited

-- See: https://releases.llvm.org/14.0.0/docs/LangRef.html#bitwise-binary-operations
inductive MOp (φ : Nat) : Type
  | unary   (w : Width φ) (op : MOp.UnaryOp) :  MOp φ
  | binary  (w : Width φ) (op : MOp.BinaryOp) :  MOp φ
  | select  (w : Width φ) : MOp φ
  | icmp    (c : IntPredicate) (w : Width φ) : MOp φ
  /-- Since the width of the const might not be known, we just store the value as an `Int` -/
  | const (w : Width φ) (val : ℤ) : MOp φ
deriving Repr, DecidableEq, Inhabited

namespace MOp

@[match_pattern] def neg    (w : Width φ) : MOp φ := .unary w .neg
@[match_pattern] def not    (w : Width φ) : MOp φ := .unary w .not
@[match_pattern] def copy   (w : Width φ) : MOp φ := .unary w .copy

@[match_pattern] def and    (w : Width φ) : MOp φ := .binary w .and
@[match_pattern] def or     (w : Width φ) : MOp φ := .binary w .or
@[match_pattern] def xor    (w : Width φ) : MOp φ := .binary w .xor
@[match_pattern] def shl    (w : Width φ) : MOp φ := .binary w .shl
@[match_pattern] def lshr   (w : Width φ) : MOp φ := .binary w .lshr
@[match_pattern] def ashr   (w : Width φ) : MOp φ := .binary w .ashr
@[match_pattern] def urem   (w : Width φ) : MOp φ := .binary w .urem
@[match_pattern] def srem   (w : Width φ) : MOp φ := .binary w .srem
@[match_pattern] def add    (w : Width φ) : MOp φ := .binary w .add
@[match_pattern] def mul    (w : Width φ) : MOp φ := .binary w .mul
@[match_pattern] def sub    (w : Width φ) : MOp φ := .binary w .sub
@[match_pattern] def sdiv   (w : Width φ) : MOp φ := .binary w .sdiv
@[match_pattern] def udiv   (w : Width φ) : MOp φ := .binary w .udiv

/-- Recursion principle in terms of individual operations, rather than `unary` or `binary` -/
def deepCasesOn {motive : ∀ {φ}, MOp φ → Sort*}
    (neg  : ∀ {φ} {w : Width φ}, motive (neg  w))
    (not  : ∀ {φ} {w : Width φ}, motive (not  w))
    (copy : ∀ {φ} {w : Width φ}, motive (copy w))
    (and  : ∀ {φ} {w : Width φ}, motive (and  w))
    (or   : ∀ {φ} {w : Width φ}, motive (or   w))
    (xor  : ∀ {φ} {w : Width φ}, motive (xor  w))
    (shl  : ∀ {φ} {w : Width φ}, motive (shl  w))
    (lshr : ∀ {φ} {w : Width φ}, motive (lshr w))
    (ashr : ∀ {φ} {w : Width φ}, motive (ashr w))
    (urem : ∀ {φ} {w : Width φ}, motive (urem w))
    (srem : ∀ {φ} {w : Width φ}, motive (srem w))
    (add  : ∀ {φ} {w : Width φ}, motive (add  w))
    (mul  : ∀ {φ} {w : Width φ}, motive (mul  w))
    (sub  : ∀ {φ} {w : Width φ}, motive (sub  w))
    (sdiv : ∀ {φ} {w : Width φ}, motive (sdiv w))
    (udiv : ∀ {φ} {w : Width φ}, motive (udiv w))
    (select : ∀ {φ} {w : Width φ}, motive (select w))
    (icmp   : ∀ {φ c} {w : Width φ}, motive (icmp c w))
    (const  : ∀ {φ v} {w : Width φ}, motive (const w v)) :
    ∀ {φ} (op : MOp φ), motive op
  | _, .neg _   => neg
  | _, .not _   => not
  | _, .copy _  => copy
  | _, .and _   => and
  | _, .or _    => or
  | _, .xor _   => xor
  | _, .shl _   => shl
  | _, .lshr _  => lshr
  | _, .ashr _  => ashr
  | _, .urem _  => urem
  | _, .srem _  => srem
  | _, .add  _  => add
  | _, .mul  _  => mul
  | _, .sub  _  => sub
  | _, .sdiv _  => sdiv
  | _, .udiv _  => udiv
  | _, .select _  => select
  | _, .icmp ..   => icmp
  | _, .const ..  => const

end MOp

instance : ToString (MOp φ) where
  toString
  | .and _ => "and"
  | .or _ => "or"
  | .not _ => "not"
  | .xor _ => "xor"
  | .shl _ => "shl"
  | .lshr _ => "lshr"
  | .ashr _ => "ashr"
  | .urem _ => "urem"
  | .srem _ => "srem"
  | .select _ => "select"
  | .add _ => "add"
  | .mul _ => "mul"
  | .sub _ => "sub"
  | .neg _ => "neg"
  | .copy _ => "copy"
  | .sdiv _ => "sdiv"
  | .udiv _ => "udiv"
  | .icmp ty _ => s!"icmp {ty}"
  | .const _ v => s!"const {v}"

abbrev Op := MOp 0

namespace Op

@[match_pattern] abbrev unary   (w : Nat) (op : MOp.UnaryOp)  : Op := MOp.unary (.concrete w) op
@[match_pattern] abbrev binary  (w : Nat) (op : MOp.BinaryOp) : Op := MOp.binary (.concrete w) op

@[match_pattern] abbrev and    : Nat → Op := MOp.and    ∘ .concrete
@[match_pattern] abbrev or     : Nat → Op := MOp.or     ∘ .concrete
@[match_pattern] abbrev not    : Nat → Op := MOp.not    ∘ .concrete
@[match_pattern] abbrev xor    : Nat → Op := MOp.xor    ∘ .concrete
@[match_pattern] abbrev shl    : Nat → Op := MOp.shl    ∘ .concrete
@[match_pattern] abbrev lshr   : Nat → Op := MOp.lshr   ∘ .concrete
@[match_pattern] abbrev ashr   : Nat → Op := MOp.ashr   ∘ .concrete
@[match_pattern] abbrev urem   : Nat → Op := MOp.urem   ∘ .concrete
@[match_pattern] abbrev srem   : Nat → Op := MOp.srem   ∘ .concrete
@[match_pattern] abbrev select : Nat → Op := MOp.select ∘ .concrete
@[match_pattern] abbrev add    : Nat → Op := MOp.add    ∘ .concrete
@[match_pattern] abbrev mul    : Nat → Op := MOp.mul    ∘ .concrete
@[match_pattern] abbrev sub    : Nat → Op := MOp.sub    ∘ .concrete
@[match_pattern] abbrev neg    : Nat → Op := MOp.neg    ∘ .concrete
@[match_pattern] abbrev copy   : Nat → Op := MOp.copy   ∘ .concrete
@[match_pattern] abbrev sdiv   : Nat → Op := MOp.sdiv   ∘ .concrete
@[match_pattern] abbrev udiv   : Nat → Op := MOp.udiv   ∘ .concrete

@[match_pattern] abbrev icmp (c : IntPredicate)   : Nat → Op  := MOp.icmp c ∘ .concrete
@[match_pattern] abbrev const (w : Nat) (val : ℤ) : Op        := MOp.const (.concrete w) val

end Op

instance : ToString Op where
  toString o := repr o |>.pretty

@[simp, reducible]
def MOp.sig : MOp φ → List (MTy φ)
| .binary w _ | .icmp _ w =>
  [.bitvec w, .bitvec w]
| .unary w _ => [.bitvec w]
| .select w => [.bitvec 1, .bitvec w, .bitvec w]
| .const _ _ => []

@[simp, reducible]
def MOp.outTy : MOp φ → MTy φ
| .binary w _ | .unary w _ | .select w | .const w _ =>
  .bitvec w
| .icmp _ _ => .bitvec 1

instance : OpSignature (MOp φ) (MTy φ) Id where
  signature op := ⟨op.sig, [], op.outTy, .pure⟩

@[simp]
def Op.denote (o : Op) (arg : HVector TyDenote.toType (OpSignature.sig o)) :
    (TyDenote.toType <| OpSignature.outTy o) :=
  match o with
  | Op.const _ val => const? val
  | Op.and _ => pairBind and? arg.toPair
  | Op.or _ => pairBind or? arg.toPair
  | Op.xor _ => pairBind xor? arg.toPair
  | Op.shl _ => pairBind shl? arg.toPair
  | Op.lshr _ => pairBind lshr? arg.toPair
  | Op.ashr _ => pairBind ashr? arg.toPair
  | Op.sub _ => pairBind sub?  arg.toPair
  | Op.add _ => pairBind add? arg.toPair
  | Op.mul _ => pairBind mul? arg.toPair
  | Op.sdiv _ => pairBind sdiv? arg.toPair
  | Op.udiv _ => pairBind udiv? arg.toPair
  | Op.urem _ => pairBind urem? arg.toPair
  | Op.srem _ => pairBind srem? arg.toPair
  | Op.not _ => Option.map (~~~.) arg.toSingle
  | Op.copy _ => arg.toSingle
  | Op.neg _ => Option.map (-.) arg.toSingle
  | Op.select _ =>
    let (ocond, otrue, ofalse) := arg.toTriple
    select? ocond otrue ofalse
  | Op.icmp c _ => pairBind (icmp? c) arg.toPair

instance : OpDenote Op Ty Id := ⟨
  fun o args _ => Op.denote o args
⟩

end InstCombine
