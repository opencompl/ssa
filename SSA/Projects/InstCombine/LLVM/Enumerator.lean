-- Script that exhaustive enumerates the our LLVM semantics.
import Std.Data.BitVec
import Init.System.IO
-- import Mathlib.Data.BitVec
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.Base

open Std
open System
open IO FS

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

def rowHeader : Row := {
 opName := "op",
 bitwidth := "width",
 v1 := "in0",
 v2 := "in1",
 v3 := "in2",
 retval := "retval"
}

def MAXW : Nat := 3


def BitVecInputsForWidth (w : Nat) : Array (Option (BitVec w)) := Id.run do
 let mut out := #[Option.none]
 for i  in [0:Nat.pow 2 w] do
   out := out.push (.some <| BitVec.ofNat w i)
 out



def BitVecInputToString : Option (BitVec w) → String
| .none => "poison"
| .some bv => s!"{bv.toNat}"

def BitVecOutputToString : Option (BitVec w) → String 
| .none => "poison"
| .some bv =>
    let iv := BitVec.toInt bv
    if w == 1
    then
      if iv == 0 then "false"
      else if iv == -1 then "true"
      else "<unk_i1>"
    else toString iv


def binopRows (opName : String)
  (f : (w : Nat) → Option (BitVec w) → Option (BitVec w) → Option (BitVec w)) : Array Row := Id.run do
  let mut rows := #[]
  for w in [1:MAXW+1] do
    for i in BitVecInputsForWidth w do
      for j in BitVecInputsForWidth w do
        let retv := f (w := w) i j
        let retv := BitVecOutputToString retv
        let row : Row := {
          opName := opName,
          bitwidth := toString w,
          v1 := BitVecInputToString i,
          v2 := BitVecInputToString j,
          retval := retv
        }
        rows := rows.push row
  rows


def selectRows : Array Row := Id.run do
  let mut rows := #[]
  for w in [1:MAXW+1] do
    for i in BitVecInputsForWidth 1 do
      for j in BitVecInputsForWidth w do
        for k in BitVecInputsForWidth w do
            let retv := InstCombine.Op.denote (.select w) (.cons i <| .cons j <| .cons k .nil)
            let retv := BitVecOutputToString retv
            let row : Row := {
              opName := "select",
              bitwidth := toString w,
              v1 := BitVecInputToString i,
              v2 := BitVecInputToString j,
              v3 := BitVecInputToString k,
              retval := retv
            }
            rows := rows.push row
  rows

def icmpRows (pred : LLVM.IntPredicate) : Array Row := Id.run do
  let mut rows := #[]
  for w in [1:MAXW+1] do
    for i in BitVecInputsForWidth w do
      for j in BitVecInputsForWidth w do
        let retv := InstCombine.Op.denote (.icmp pred w) (.cons i <| .cons j <| .nil)
        let retv := BitVecOutputToString retv
        let row : Row := {
          opName := s!"icmp.{pred}",
          bitwidth := toString w,
          v1 := BitVecInputToString i,
          v2 := BitVecInputToString j,
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
