#!/usr/bin/env python3
# Generate the file for LLVM
import itertools
from typing import *
import subprocess
import re

MAX_OP_ARITY = 3


def llvm_inputs(w : int):
  yield "poison"
  for i in range(0, 2 ** w): yield i

class LLVMSelectOpInfo:
  def __init__(self):
    self.arity = 3
    self.name = "select"
    pass

  def to_str(self, w : int) -> str:
    out = ""
    assert self.arity <= MAX_OP_ARITY
    for vs in itertools.product(llvm_inputs(1), llvm_inputs(w), llvm_inputs(w)):
      vs_underscore = "__".join([f"val_{v}" for v in vs])
      # vs_comma = ",".join([str(v) for v in vs])
      out += f"define i{w} @test_{self.name}__width_{w}__{vs_underscore}() {{\n"
      out += f"  %out = select i1 {vs[0]}, i{w} {vs[1]}, i{w} {vs[2]}\n"
      out += f"  ret i{w} %out\n"
      out += "}\n"
      out += "\n"
    return out


# eq: equal
# ne: not equal
# --
# ugt: unsigned greater than
# uge: unsigned greater or equal
# --
# ult: unsigned less than
# ule: unsigned less or equal
# --
# sgt: signed greater than
# sge: signed greater or equal
# --
# slt: signed less than
# sle: signed less or equal
class LLVMIcmpOfInfo:
  def __init__(self, cond):
    self.arity = 2
    self.name = "icmp"
    self.cond = cond
    pass

  def to_str(self, w : int) -> str:
    out = ""
    assert self.arity <= MAX_OP_ARITY
    for vs in itertools.product(llvm_inputs(w), llvm_inputs(w)):
      vs_underscore = "__".join([f"val_{v}" for v in vs])
      # vs_comma = ",".join([str(v) for v in vs])
      out += f"define i1 @test_{self.name}.{self.cond}__width_{w}__{vs_underscore}() {{\n"
      out += f"  %out = icmp {self.cond} i{w} {vs[0]}, {vs[1]}\n"
      out += f"  ret i1 %out\n"
      out += "}\n"
      out += "\n"
    return out

class LLVMArithBinopInfo:
  arity : int
  name : str

  def __init__(self, name : str, arity : int):
    self.name = name
    self.arity = arity

  def to_str(self, w : int) -> str:
    out = ""
    assert self.arity <= MAX_OP_ARITY
    for vs in itertools.product(*[llvm_inputs(w) for ix in range(self.arity)]):
      vs_underscore = "__".join([f"val_{v}" for v in vs])
      vs_comma = ",".join([str(v) for v in vs])
      out += f"define i{w} @test_{self.name}__width_{w}__{vs_underscore}() {{\n"
      out += f"  %out = {self.name} i{w} {vs_comma}\n"
      out += f"  ret i{w} %out\n"
      out += "}\n"
      out += "\n"
    return out



def sh(*commands):
  command_str = " ".join([str(s) for s in commands])
  print(f"running '{command_str}'")
  proc = subprocess.run([*commands])
  proc.check_returncode()
  print("stdout:")
  print(f"{proc.stdout}")
  print("---")
  print("stderr")
  print(f"{proc.stderr}")
  print("---")


class Row:
  def __init__(self, op : str, width : str, vs : List[str], ret_val : str):
    self.op = op
    self.width = width
    self.vs = vs
    self.ret_val = ret_val

  @staticmethod
  def header_row():
    return Row("op", "width", ["in0", "in1", "in2"], "retval")

  def to_csv(self):
    assert len(self.vs) >= 1
    assert len(self.vs) <= MAX_OP_ARITY
    vs = ", ".join([str(v) for v in self.vs] + \
                    ["<none>" for _ in range(MAX_OP_ARITY - len(self.vs))])
    return f"{self.op}, {self.width}, {vs}, {self.ret_val}"

def parse_generated_llvm_file(lines):
  i = 0
  # define i3 @test_add_width_3__val_7__val_6() {
  #   ret i3 -3
  # }
  while i < len(lines):
    i += 1
    if lines[i].startswith("define"):
      def_line = lines[i]; i += 1

      re_def_line = r"define i\d+ @test_([a-z.]+)__width"
      match = re.search(re_def_line, def_line)
      vals = None

      if match: # we have matched the regular expression.
        op_name = match.group(1)
        KNOWN_BINOPS  = ["and", "or", "xor", "add", "sub",
                          "mul", "udiv", "sdiv", "urem", "srem", "shl", "lshr", "ashr",
                          "icmp.eq", "icmp.ne", "icmp.ugt", "icmp.uge", "icmp.ult", "icmp.ule", "icmp.sgt", "icmp.sge", "icmp.slt", "icmp.sle"]
        if op_name in KNOWN_BINOPS:
          # binary operation
          re_def_line = r"define i\d+ @test_[a-z\.]+__width_(\d+)__val_(\d+|poison)__val_(\d+|poison)"
          match = re.search(re_def_line, def_line)
          if not match: print (f"ERR: unable to match definition '{def_line}' with pattern '{re_def_line}'")
          assert match
          width = match.group(1)
          vals = [match.group(2 + i) for i in range(0, 2)]
        elif op_name == "select":
          re_def_line = r"define i\d+ @test_[a-z\.]+__width_(\d+)__val_(\d+|poison)__val_(\d+|poison)__val_(\d+|poison)"
          match = re.search(re_def_line, def_line)
          if not match: print (f"ERR: unable to match definition '{def_line}' with pattern '{re_def_line}'")
          assert match
          width = match.group(1)
          vals = [match.group(2 + i) for i in range(0, 3)]
        else:
          raise RuntimeError(f"unknown operation '{op_name}'")
        assert vals
        assert width
        ret_line = lines[i]; i += 1
        re_ret = r"ret i\d+ ([+-]?\d+|false|true|poison)"
        match = re.search(re_ret, ret_line)
        if not match: print(f"ERR: unable to find pattern '{re_ret}' in '{ret_line}'")
        assert match
        ret_val = match.group(1)
        yield Row(op=op_name, width=width, vs=vals, ret_val=ret_val)
      else:
       i += 1
    i += 1; # skip }




LLVM_OPS = [
  LLVMSelectOpInfo(),
  LLVMIcmpOfInfo("eq"),
  LLVMIcmpOfInfo("ne"),
  # --
  LLVMIcmpOfInfo("ugt"),
  LLVMIcmpOfInfo("uge"),
  # --
  LLVMIcmpOfInfo("ult"),
  LLVMIcmpOfInfo("ule"),
  # --
  LLVMIcmpOfInfo("sgt"),
  LLVMIcmpOfInfo("sge"),
  # --
  LLVMIcmpOfInfo("slt"),
  LLVMIcmpOfInfo("sle"),
  LLVMArithBinopInfo("and", 2),
  LLVMArithBinopInfo("or", 2),
  LLVMArithBinopInfo("xor", 2),
  LLVMArithBinopInfo("add", 2),
  LLVMArithBinopInfo("sub", 2),
  LLVMArithBinopInfo("mul", 2),
  LLVMArithBinopInfo("udiv", 2),
  LLVMArithBinopInfo("sdiv", 2),
  LLVMArithBinopInfo("urem", 2),
  LLVMArithBinopInfo("srem", 2),
  LLVMArithBinopInfo("shl", 2),
  LLVMArithBinopInfo("lshr", 2),
  LLVMArithBinopInfo("ashr", 2),
]

MAX_WIDTH = 4
if __name__ == "__main__":
  with open("generated-llvm.ll", "w") as f:
    for (info, w) in itertools.product(LLVM_OPS, range(1, MAX_WIDTH+1)):
        f.write(info.to_str(w))

  sh("opt-15", "-S", "generated-llvm.ll", "-instcombine", "-o", "generated-llvm-optimized.ll")

  rows = [Row.header_row()]
  with open("generated-llvm-optimized.ll", "r") as f:
    rows.extend(list(parse_generated_llvm_file(f.readlines())))

  with open("generated-llvm-optimized-data.csv", "w") as f:
      f.write("\n".join([r.to_csv() for r in rows]))
