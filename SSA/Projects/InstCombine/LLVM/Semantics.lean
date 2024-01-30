import Std.Data.BitVec
import SSA.Projects.InstCombine.ForStd
import Mathlib.Tactic.Cases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto


open Std

namespace LLVM

/--
The ‘and’ instruction returns the bitwise logical and of its two operands.
-/
def and? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
 .some <| x &&& y

/--
The ‘or’ instruction returns the bitwise logical inclusive or of its two
operands.
-/
def or? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
 .some <| x ||| y

/--
The ‘xor’ instruction returns the bitwise logical exclusive or of its two
operands.  The xor is used to implement the “one’s complement” operation, which
is the “~” operator in C.
-/
def xor? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
 .some <| x ^^^ y

/--
The value produced is the integer sum of the two operands.
If the sum has unsigned overflow, the result returned is the mathematical result modulo 2n, where n is the bit width of the result.
Because LLVM integers use a two’s complement representation, this instruction is appropriate for both signed and unsigned integers.
-/
def add? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
 .some <| x + y

/--
The value produced is the integer difference of the two operands.
If the difference has unsigned overflow, the result returned is the mathematical result modulo 2n, where n is the bit width of the result.
Because LLVM integers use a two’s complement representation, this instruction is appropriate for both signed and unsigned integers.
-/
def sub? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
 .some <| x - y

/--
The value produced is the integer product of the two operands.
If the result of the multiplication has unsigned overflow, the result returned
is the mathematical result modulo 2n, where n is the bit width of the result.
Because LLVM integers use a two’s complement representation, and the result
is the same width as the operands, this instruction returns the correct
result for both signed and unsigned integers.

If a full product (e.g. i32 * i32 -> i64) is needed, the operands should be
sign-extended or zero-extended as appropriate to the width of the full product.
-/
def mul? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
 .some <| x * y

/--
The value produced is the unsigned integer quotient of the two operands.
Note that unsigned integer division and signed integer division are distinct operations; for signed integer division, use ‘sdiv’.
Division by zero is undefined behavior.
-/
def udiv? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
  match y.toNat with
    | 0 => none
    | _ => some <| BitVec.ofInt w (x.toNat / y.toNat)

def intMin (w : Nat) : BitVec w :=
  - BitVec.ofNat w (2^(w - 1))

def intMax (w : Nat) : BitVec w := intMin w - 1

theorem intMin_minus_one {w : Nat} : (intMin w - 1) = intMax w := rfl

/--
The value produced is the signed integer quotient of the two operands rounded towards zero.
Note that signed integer division and unsigned integer division are distinct operations; for unsigned integer division, use ‘udiv’.
Division by zero is undefined behavior.
Overflow also leads to undefined behavior; this is a rare case, but can occur, for example, by doing a 32-bit division of -2147483648 by -1.

Notes
-----

The rounding is round to zero, not round to -infty.
at width 1, -1 / -1 is considered -1
at width 2, -4 / -1 is considered overflow!

-/
-- only way overflow can happen is (INT_MIN / -1).
-- but we do not consider overflow when `w=1`, because `w=1` only has a sign bit, so there
-- is no magniture to overflow.
def sdiv? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
  if y == 0 || (w != 1 && x == (intMin w) && y == -1) 
  then .none
  else BitVec.sdiv x y

-- Probably not a Mathlib worthy name, not sure how you'd mathlibify the precondition
theorem sdiv?_eq_div_if {w : Nat} {x y : BitVec w} :
    sdiv? x y =
    if (y = 0) ∨ ((w ≠ 1) ∧ (x = intMin w) ∧ (y = -1))
      then none
    else some <| BitVec.sdiv x y
    := by
  simp [sdiv?]; split_ifs <;> try tauto

/--
This instruction returns the unsigned integer remainder of a division. This instruction always performs an unsigned division to get the remainder.
Note that unsigned integer remainder and signed integer remainder are distinct operations; for signed integer remainder, use ‘srem’.
Taking the remainder of a division by zero is undefined behavior.
-/
def urem? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
  if y.toNat = 0
  then none
  else some <| BitVec.ofNat w (x.toNat % y.toNat)

def _root_.Int.rem (x y : Int) : Int :=
  if x ≥ 0 then (x % y) else ((x % y) - y.natAbs)

-- TODO: prove this to make sure it's the right implementation!
theorem _root_.Int.rem_sign_dividend :
  ∀ x y, Int.rem x y < 0 ↔ x < 0 :=  by sorry

/--
This instruction returns the remainder of a division (where the result is either zero or has the same sign as the dividend, op1),
not the modulo operator (where the result is either zero or has the same sign as the divisor, op2) of a value.
For more information about the difference, see The Math Forum.
For a table of how this is implemented in various languages, please see Wikipedia: modulo operation.
Note that signed integer remainder and unsigned integer remainder are distinct operations; for unsigned integer remainder, use ‘urem’.
Taking the remainder of a division by zero is undefined behavior.
For vectors, if any element of the divisor is zero, the operation has undefined behavior.
Overflow also leads to undefined behavior; this is a rare case, but can occur, for example,
by taking the remainder of a 32-bit division of -2147483648 by -1.
(The remainder doesn’t actually overflow, but this rule lets srem be implemented using instructions that return both the result
of the division and the remainder.)

The fundamental equation of div/rem is: x = (x/y) * y + x%y
=> x%y = x - (x/y)
We use this equation to define srem.
-/
def srem? {w : Nat} (x y : BitVec w) : Option <| BitVec w :=
  (sdiv? x y).map (fun div => x - div * y)

def sshr (a : BitVec n) (s : Nat) := BitVec.sshiftRight a s

/--
Shift left instruction.
The value produced is op1 * 2^op2 mod 2n, where n is the width of the result.
If op2 is (statically or dynamically) equal to or larger than the number of
bits in op1, this instruction returns a poison value.

-/
def shl? {m n k} (op1 : BitVec n) (op2 : BitVec m) : Option (BitVec k) :=
  let bits := op2.toNat -- should this be toInt?
  if bits >= n then .none
  else .some <| BitVec.zeroExtend k (op1 <<< op2)

/--
This instruction always performs a logical shift right operation.
The most significant bits of the result will be filled with zero bits after
the shift.

If op2 is (statically or dynamically) equal to or larger than the number of bits in op1,
this instruction returns a poison value.

Corresponds to `Std.BitVec.ushiftRight` in the `some` case.
-/
def lshr? {m n k} (op1 : BitVec n) (op2 : BitVec m) : Option (BitVec k) :=
  let bits := op2.toNat -- should this be toInt?
  if bits >= n then .none
  else .some <| BitVec.zeroExtend k (op1 >>> op2)


/--
This instruction always performs an arithmetic shift right operation,
The most significant bits of the result will be filled with the sign bit of op1.

If op2 is (statically or dynamically) equal to or larger than the number of bits in op1,
this instruction returns a poison value.

Corresponds to `Std.BitVec.sshiftRight` in the `some` case.
-/
def ashr? {m n k} (op1 : BitVec n) (op2 : BitVec m) : Option (BitVec k) :=
  let bits := op2.toNat -- should this be toInt?
  if bits >= n then .none
  else .some <| BitVec.zeroExtend k (op1 >>>ₛ op2)

/--
 If the condition is an i1 and it evaluates to 1, the instruction returns the first value argument; otherwise, it returns the second value argument.

 If the condition is an i1 and it evaluates to 1, the instruction returns the first value argument; otherwise, it returns the second value argument.
-/
def select? {w : Nat} (c? : Option (BitVec 1)) (x? y? : Option (BitVec w)) : Option (BitVec w) :=
  match c? with
  | .none => .none
  | .some 1 => x?
  | .some 0 => y?

inductive IntPredicate where
  | eq
  | ne
  | ugt
  | uge
  | ult
  | ule
  | sgt
  | sge
  | slt
  | sle
deriving Inhabited, DecidableEq, Repr

instance : ToString IntPredicate where
  toString
  | .eq => "eq"
  | .ne => "ne"
  | .ugt => "ugt"
  | .uge => "uge"
  | .ult => "ult"
  | .ule => "ule"
  | .sgt => "sgt"
  | .sge => "sge"
  | .slt => "slt"
  | .sle => "sle"


/--
The ‘icmp’ instruction takes three operands.
The first operand is the condition code indicating the kind of comparison to perform. It is not a value, just a keyword.
The possible condition codes are:

  - eq: equal
  - ne: not equal
  - ugt: unsigned greater than
  - uge: unsigned greater or equal
  - ult: unsigned less than
  - ule: unsigned less or equal
  - sgt: signed greater than
  - sge: signed greater or equal
  - slt: signed less than
  - sle: signed less or equal

The remaining two arguments must be integer. They must also be identical types.
-/
def icmp {w : Nat} (c : IntPredicate) (x y : BitVec w) : Bool :=
  match c with
    | .eq => (x == y)
    | .ne => (x != y)
    | .sgt => (x >ₛ y)
    | .sge => (x ≥ₛ y)
    | .slt => (x <ₛ y)
    | .sle => (x ≤ₛ y)
    | .ugt => (x >ᵤ y)
    | .uge => (x ≥ᵤ y)
    | .ult => (x <ᵤ y)
    | .ule => (x ≤ᵤ y)


/--
Wrapper around `icmp` (this cannot become `none` on its own).

The ‘icmp’ instruction takes three operands.
The first operand is the condition code indicating the kind of comparison to perform. It is not a value, just a keyword.
The possible condition codes are:

  - eq: equal
  - ne: not equal
  - ugt: unsigned greater than
  - uge: unsigned greater or equal
  - ult: unsigned less than
  - ule: unsigned less or equal
  - sgt: signed greater than
  - sge: signed greater or equal
  - slt: signed less than
  - sle: signed less or equal

The remaining two arguments must be integer. They must also be identical types.
-/
def icmp? {w : Nat} (c : IntPredicate) (x y : BitVec w) : Option (BitVec 1) :=
  Option.some ↑(icmp c x y)

/--
Unlike LLVM IR, MLIR does not have first-class constant values.
Therefore, all constants must be created as SSA values before being used in other
operations. llvm.mlir.constant creates such values for scalars and vectors.
It has a mandatory value attribute, which must be an integer
(currently the only supported type in these semantics).

The type of the attribute is one of the corresponding MLIR builtin types.
The operation produces a new SSA value of the specified LLVM IR dialect type.
The type of that value must correspond to the attribute type converted to LLVM IR.

This interprets the value as a signed bitvector.
If the bitwidth is not enough it will be reduced, returning
the value `(2^w + (i mod 2^w)) mod 2^w`.

TODO: double-check that truncating works the same as MLIR (signedness, overflow, etc)
-/
def const? (i : Int): Option (BitVec w) :=
  BitVec.ofInt w i

end LLVM
