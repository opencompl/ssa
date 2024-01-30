-- Script that exhaustive enumerates the our LLVM semantics.
import Std.Data.BitVec
import Init.System.IO
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.Base

open Std
open System
open IO FS

/-- A row of CSV data. -/
structure Row where
  opName : String
  bitwidth : String
  v1 : String
  v2 : String
  v3 : String := "<none>"
  retval : String

instance : ToString Row where
  toString r :=
    s!"{r.opName}, {r.bitwidth}, {r.v1}, {r.v2}, {r.v3}, {r.retval}"

/-- CSV header row. -/
def rowHeader : Row := {
 opName := "op",
 bitwidth := "width",
 v1 := "in0",
 v2 := "in1",
 v3 := "in2",
 retval := "retval"
}

/-- Maximum width we bruteforce (inclusive). -/
def MAXW : Nat := 4

/-- List of bitvector inputs for a given bitwidth. Produces 'poison' and `[0..2^w)`. -/
def BitVec.inputsForWidth (w : Nat) : Array (Option (BitVec w)) := Id.run do
 let mut out := #[Option.none]
 for i  in [0:Nat.pow 2 w] do
   out := out.push (.some <| BitVec.ofNat w i)
 out

/-- Render the inputs as a string. These are guaranteed to always be natural numbers. -/
def BitVec.inputToString : Option (BitVec w) → String
| .none => "poison"
| .some bv => s!"{bv.toNat}"

/-- Render the output as a string. These are more complex, as i1 are printed as true/false, and outputs are printed as integers. -/
def BitVec.outputToString : Option (BitVec w) → String
| .none => "poison"
| .some bv =>
    let iv := BitVec.toInt bv
    if w == 1
    then
      if iv == 0 then "false"
      else if iv == -1 then "true"
      else "<unk_i1>"
    else toString iv

/-- Produce CSV rows for a binary operation given by 'f' -/
def binopRows (opName : String)
  (f : (w : Nat) → Option (BitVec w) → Option (BitVec w) → Option (BitVec w)) : Array Row := Id.run do
  let mut rows := #[]
  for w in [1:MAXW+1] do
    for i in BitVec.inputsForWidth w do
      for j in BitVec.inputsForWidth w do
        let retv := f (w := w) i j
        let retv := BitVec.outputToString retv
        let row : Row := {
          opName := opName,
          bitwidth := toString w,
          v1 := BitVec.inputToString i,
          v2 := BitVec.inputToString j,
          retval := retv
        }
        rows := rows.push row
  rows

/-- Produce CSV rows for 'llvm.select' -/
def selectRows : Array Row := Id.run do
  let mut rows := #[]
  for w in [1:MAXW+1] do
    for i in BitVec.inputsForWidth 1 do
      for j in BitVec.inputsForWidth w do
        for k in BitVec.inputsForWidth w do
            let retv := InstCombine.Op.denote (.select w) (.cons i <| .cons j <| .cons k .nil)
            let retv := BitVec.outputToString retv
            let row : Row := {
              opName := "select",
              bitwidth := toString w,
              v1 := BitVec.inputToString i,
              v2 := BitVec.inputToString j,
              v3 := BitVec.inputToString k,
              retval := retv
            }
            rows := rows.push row
  rows

/-- Produce CSV rows for 'llvm.icmp <pred> -/
def icmpRows (pred : LLVM.IntPredicate) : Array Row := Id.run do
  let mut rows := #[]
  for w in [1:MAXW+1] do
    for i in BitVec.inputsForWidth w do
      for j in BitVec.inputsForWidth w do
        let retv := InstCombine.Op.denote (.icmp pred w) (.cons i <| .cons j <| .nil)
        let retv := BitVec.outputToString retv
        let row : Row := {
          opName := s!"icmp.{pred}",
          bitwidth := toString w,
          v1 := BitVec.inputToString i,
          v2 := BitVec.inputToString j,
          retval := retv
        }
        rows := rows.push row
  rows

def main : IO Unit := do
  let filename := "generated-ssa-llvm-semantics.csv"
  let handle : Handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let stream : Stream := IO.FS.Stream.ofHandle handle
  let rows := #[rowHeader]
  let rows := rows.append (selectRows)
  --
  let rows := rows.append (icmpRows LLVM.IntPredicate.eq)
  let rows := rows.append (icmpRows LLVM.IntPredicate.ne)
  --
  let rows := rows.append (icmpRows LLVM.IntPredicate.ugt)
  let rows := rows.append (icmpRows LLVM.IntPredicate.uge)
  --
  let rows := rows.append (icmpRows LLVM.IntPredicate.ult)
  let rows := rows.append (icmpRows LLVM.IntPredicate.ule)
  --
  let rows := rows.append (icmpRows LLVM.IntPredicate.sgt)
  let rows := rows.append (icmpRows LLVM.IntPredicate.sge)
  --
  let rows := rows.append (icmpRows LLVM.IntPredicate.slt)
  let rows := rows.append (icmpRows LLVM.IntPredicate.sle)
  --
  let rows := rows.append (binopRows "and" (fun w a b => InstCombine.Op.denote (.and w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "or" (fun w a b => InstCombine.Op.denote (.or w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "xor" (fun w a b => InstCombine.Op.denote (.xor w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "add" (fun w a b => InstCombine.Op.denote (.add w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "sub" (fun w a b => InstCombine.Op.denote (.sub w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "mul" (fun w a b => InstCombine.Op.denote (.mul w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "udiv" (fun w a b => InstCombine.Op.denote (.udiv w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "sdiv" (fun w a b => InstCombine.Op.denote (.sdiv w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "urem" (fun w a b => InstCombine.Op.denote (.urem w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "srem" (fun w a b => InstCombine.Op.denote (.srem w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "shl" (fun w a b => InstCombine.Op.denote (.shl w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "lshr" (fun w a b => InstCombine.Op.denote (.lshr w) (.cons a (.cons b .nil))))
  let rows := rows.append (binopRows "ashr" (fun w a b => InstCombine.Op.denote (.ashr w) (.cons a (.cons b .nil))))
  rows.toList |>.map toString |> "\n".intercalate |> stream.putStr
  return ()
