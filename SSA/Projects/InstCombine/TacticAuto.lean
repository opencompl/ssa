import Mathlib.Tactic.Ring
import Std.Data.BitVec
import Mathlib.Data.BitVec.Lemmas

macro "alive_auto": tactic =>
  `(tactic|
      (
        intros
        (try simp (config := {decide := false}) [-Std.BitVec.ofNat_eq_ofNat])
        try ring_nf
        try solve | (ext; simp;
                     try cases Std.BitVec.getLsb' _ _ <;> try simp;
                     try cases Std.BitVec.getLsb' _ _ <;> try simp;
                     try cases Std.BitVec.getLsb' _ _ <;> try simp;
                     try cases Std.BitVec.getLsb' _ _ <;> try simp;)
      )
   )
