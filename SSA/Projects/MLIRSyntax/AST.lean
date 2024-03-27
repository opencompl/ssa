import SSA.Core.Util.ConcreteOrMVar
open Lean PrettyPrinter

namespace MLIR.AST

-- variable (MCtxt : Type*)

-- Affine expressions [TODO: find some way to separate this out]
-- ==================
inductive AffineExpr
  | Var: String -> AffineExpr
  deriving DecidableEq, Repr

inductive AffineTuple
  | mk: List AffineExpr -> AffineTuple
  deriving DecidableEq, Repr
  -- TODO: make prettier `Repr` instance

inductive AffineMap
  | mk: AffineTuple -> AffineTuple -> AffineMap
  deriving DecidableEq, Repr

-- EMBEDDING
-- ==========

inductive BBName
  | mk: String -> BBName
  deriving DecidableEq, Repr

/-- An ssa value is a variable name -/
inductive SSAVal : Type where
  | SSAVal : String -> SSAVal
deriving DecidableEq, Repr

def SSAValToString (s: SSAVal): String :=
  match s with
  | SSAVal.SSAVal str => str

instance : ToString SSAVal where
  toString := SSAValToString

inductive Signedness :=
  | Signless -- i*
  | Unsigned -- u*
  | Signed   -- si*
deriving DecidableEq, Repr

abbrev Width φ := ConcreteOrMVar Nat φ
abbrev Width.concrete : Nat → Width φ := ConcreteOrMVar.concrete
abbrev Width.mvar : Fin φ → Width φ := ConcreteOrMVar.mvar

inductive MLIRType (φ : Nat) : Type _ :=
  | int: Signedness -> Width φ -> MLIRType φ
  | float: Nat -> MLIRType φ
  | tensor1d: MLIRType φ -- tensor of int values.
  | tensor2d: MLIRType φ -- tensor of int values.
  | tensor4d: MLIRType φ -- tensor of int values.
  | index:  MLIRType φ
  | undefined: String → MLIRType φ
  deriving Repr, DecidableEq

variable (φ : Nat)

instance : ToFormat (Width φ) := ⟨repr⟩
instance : ToFormat (MLIRType φ) := ⟨repr⟩

-- We define "MLIRTy" to be just the basic types outside of any dialect
abbrev MLIRTy (φ := 0) := MLIRType φ

/-- Shorthand to build <iN> -/
def MLIRTy.i (width : Nat) : MLIRTy φ := MLIRType.int Signedness.Signless width
-- Other useful abbreviations
abbrev MLIRType.i1: MLIRType φ := MLIRType.int .Signless 1
abbrev MLIRType.i32: MLIRType φ := MLIRType.int .Signless 32
def MLIRType.i (width : Nat) : MLIRTy φ := MLIRType.int Signedness.Signless width

/-- An ssa value (variable name) with a type -/
abbrev TypedSSAVal := SSAVal × MLIRType φ

mutual
inductive AttrValue :=
  | symbol: String -> AttrValue -- symbol ref attr
  | str : String -> AttrValue
  | int : Int -> MLIRType φ -> AttrValue
  | nat: Nat -> AttrValue
  | bool : Bool -> AttrValue
  | float : Float -> MLIRType φ -> AttrValue
  | type : MLIRType φ -> AttrValue
  | affine: AffineMap -> AttrValue
  | permutation: List Nat -> AttrValue -- a permutation
  | list: List AttrValue -> AttrValue
  | nestedsymbol: AttrValue -> AttrValue -> AttrValue
  | alias: String -> AttrValue
  | dict: AttrDict -> AttrValue
  | opaque_: (dialect: String) -> (value: String) -> AttrValue
  | opaqueElements: (dialect: String) -> (value: String) -> (type: MLIRType φ) -> AttrValue
  | unit: AttrValue

-- https://mlir.llvm.org/docs/LangRef/#attributes
-- | TODO: add support for mutually inductive records / structures
inductive AttrEntry  :=
  | mk: (key: String)
      -> (value: AttrValue)
      -> AttrEntry

inductive AttrDict :=
  | mk: List AttrEntry -> AttrDict

end

def AttrEntry.destructure {φ} : AttrEntry φ → String × AttrValue φ
  | .mk name value => (name,value)

def AttrDict.getAttr {φ} : AttrDict φ → String →  Option (AttrValue φ)
  | .mk attrs, name => attrs.map AttrEntry.destructure |>.lookup name

-- We define "AttrVal" to be just the basic attributes outside of any dialect
abbrev AttrVal (φ := 0) := AttrValue φ


mutual
-- | TODO: make this `record` when mutual records are allowed?
-- | TODO: make these arguments optional?
inductive Op where
  | mk: (name: String)
        -> (res: List <| TypedSSAVal φ)
        -> (args: List <| TypedSSAVal φ)
        -> (regions: List Region)
        -> (attrs: AttrDict φ)
        -> Op

inductive Region where
  | mk: (name: String)
        -> (args: List <| TypedSSAVal φ)
        -> (ops: List Op) -> Region

end

-- Attribute definition on the form #<name> = <val>
inductive AttrDefn where
  | mk: (name: String) -> (val: AttrValue φ) -> AttrDefn

inductive Module where
  | mk: (functions: List <| Op φ)
        -> (attrs: List <| AttrDefn φ)
        ->  Module

def Op.name {φ} : Op φ -> String
  | Op.mk name .. => name

def Op.res {φ} : Op φ -> List (TypedSSAVal φ)
  | Op.mk _ res .. => res

def Op.resNames {φ} : Op φ → List SSAVal
  | Op.mk _ res .. => res.map Prod.fst

def Op.resTypes {φ} : Op φ → List (MLIRType φ)
  | Op.mk _ res .. => res.map Prod.snd

def Op.args {φ} : Op φ -> List (TypedSSAVal φ)
  | Op.mk _ _ args .. => args

def Op.argNames {φ} : Op φ → List SSAVal
  | Op.mk _ _ args .. => args.map Prod.fst

def Op.argTypes {φ} : Op φ → List (MLIRType φ)
  | Op.mk _ _ args .. => args.map Prod.snd

def Op.regions {φ} : Op φ -> List (Region φ)
  | Op.mk _ _ _ regions _ => regions

def Op.attrs {φ} : Op φ -> (AttrDict φ)
| Op.mk _ _ _ _ attrs => attrs

instance : Coe String SSAVal where
  coe (s: String) := SSAVal.SSAVal s

instance : Coe String (AttrValue φ) where
  coe (s: String) := AttrValue.str s

instance : Coe Int (AttrValue φ) where
  coe (i: Int) := AttrValue.int i (MLIRType.int .Signless 64)

instance : Coe Nat (AttrValue φ) where
  coe (n: Nat) := AttrValue.nat n

instance : Coe (MLIRType φ) (AttrValue φ) where
  coe := AttrValue.type

instance : Coe (String × AttrValue φ) (AttrEntry φ) where
  coe v := AttrEntry.mk v.fst v.snd

instance : Coe (String × MLIRType φ) (AttrEntry φ) where
  coe v := AttrEntry.mk v.fst (AttrValue.type v.snd)

instance : Coe (AttrEntry φ) (String × AttrValue φ) where
  coe
  | AttrEntry.mk key val => (key, val)

instance : Coe (List (AttrEntry φ)) (AttrDict φ) where
  coe
  | v => AttrDict.mk v

 instance : Coe (AttrDict φ) (List (AttrEntry φ)) where
  coe
  | AttrDict.mk as => as

def Region.name (region : Region φ) : BBName :=
  match region with
  | Region.mk name _ _ => BBName.mk name

def Region.args : Region φ → List (TypedSSAVal φ)
  | .mk _ args _ => args

def Region.ops (region: Region φ) : List (Op φ) :=
  match region with
  | Region.mk _ _ ops => ops


mutual
partial def docAttrVal {φ} : AttrValue φ → Format
  | .symbol s => f!"@\"{s}\""
  | .permutation ps => f!"[permutation {ps}]"
  | .nestedsymbol s t => (docAttrVal s) ++ "::" ++ (docAttrVal t)
  | .str str => f!"\"{str}\""
  | .type ty => repr ty
  | .int x ty | .float x ty => f!"{x} : {repr ty}"
  | .nat i => f!"{i} : index"
  | .bool b => if b then "true" else "false"
  | .affine aff => f!"affine_map< {repr aff} >"
  | .list xs => f!"[" ++ Format.join ((xs.map docAttrVal).intersperse ", ") ++ "]"
  | .alias a => "#" ++ a
  | .dict d => docAttrDict d
  | .opaque_ dialect val => f!"#${dialect}<${val}>"
  | .opaqueElements dialect val ty => f!"#opaque< {dialect}, #{val}> : #{repr ty}"
  | .unit => "()"

partial def docAttrEntry {φ} : AttrEntry φ → Format
  | .mk k v => f!"{k} = " ++ (docAttrVal v)

partial def docAttrDict {φ} : AttrDict φ → Format
  | .mk attrs =>
      if List.isEmpty attrs
      then f!""
      else f!"\{" ++ (Format.join ((attrs.map docAttrEntry).intersperse ", ")) ++ f!"}"
end

instance : Repr (AttrValue φ) where
  reprPrec x _ := docAttrVal x

instance : Repr (AttrEntry φ) where
  reprPrec x _ := docAttrEntry x

instance : Repr (AttrDict φ) where
  reprPrec x _ := docAttrDict x

instance : Repr (AttrDefn φ) where
  reprPrec x _ := match x with
    | AttrDefn.mk name val => f!"#{name} := {repr val}"

instance : Repr SSAVal where
  reprPrec x _ := match x with
    | SSAVal.SSAVal name => f!"%{name}"

instance : ToFormat SSAVal where
  format := repr

mutual
partial def op_to_format {φ} : Op φ →  Format
  | Op.mk name res args rgns attrs =>
      let doc_name := f!"\"{name}\""
      let doc_rgns := if rgns.isEmpty
                      then f!""
                      else rgns.map (Format.align true ++ rgn_to_format ·) |> Format.join
      let doc_args := f!"({args.map repr |>.intersperse f!", " |> Format.join})"
      let doc_res := f!"({res.map repr |>.intersperse f!", " |> Format.join})"

      doc_res ++ " := " ++ doc_name ++ doc_args ++ doc_rgns ++ repr attrs

partial def rgn_to_format {φ} : Region φ → Format
  | Region.mk name args ops =>
      let doc_args := if args.isEmpty then
          f!""
        else
          f!"({args.map (fun (v, t) => f!"{repr v} : {repr t}") |>.intersperse "," |> Format.join})"
      let doc_ops :=
        ops.map (Format.align true ++ op_to_format ·) |> Format.join
      f!"^{name}{doc_args} : " ++ doc_ops
end

instance : Repr (Op φ) := ⟨fun x _ => op_to_format x⟩
instance : Repr (Region φ) := ⟨fun x _ => rgn_to_format x⟩

def AttrEntry.key {φ} : AttrEntry φ → String
  | AttrEntry.mk k _ => k

def AttrEntry.value {φ} : AttrEntry φ → AttrValue φ
  | AttrEntry.mk _ v => v


def AttrDict.empty {φ} : AttrDict φ := AttrDict.mk []

def Op.empty {φ} (name : String) : Op φ := Op.mk name [] [] [] AttrDict.empty

def Op.addArg {φ} (o : Op φ) (arg : TypedSSAVal φ) : Op φ :=
  match o with
  | Op.mk name res args regions attrs =>
    Op.mk name res (args ++ [arg])  regions attrs

def Op.addResult {φ} (o : Op φ) (new_res : TypedSSAVal φ) : Op φ :=
 match o with
 | Op.mk name res args  regions attrs =>
    Op.mk name (res ++ [new_res]) args  regions attrs

def Op.appendRegion {φ} (o : Op φ) (r : Region φ) : Op φ :=
  match o with
  | Op.mk name res args regions attrs =>
      Op.mk name res args (regions ++ [r]) attrs


-- | Note: AttrEntry can be given as String × AttrValue
def AttrDict.add {φ} (attrs : AttrDict φ) (entry : AttrEntry φ) : AttrDict φ :=
    Coe.coe <| entry :: Coe.coe attrs

def AttrDict.find {φ} (attrs : AttrDict φ) (name : String) : Option (AttrValue φ) :=
  match attrs with
  | AttrDict.mk entries =>
      match entries.find? (fun entry => entry.key == name) with
      | some v => v.value
      | none => none

def AttrDict.find_nat {φ} (attrs : AttrDict φ) (name : String) : Option Nat :=
  match attrs.find name with
  | .some (AttrValue.nat i) =>  .some i
  | _ => .none

def AttrDict.find_int {φ} (attrs : AttrDict φ)
  (name : String): Option (Int × MLIRType φ) :=
  match attrs.find name with
  | .some (AttrValue.int i ty) =>  .some (i, ty)
  | _ => .none

def AttrDict.find_str {φ} (attrs : AttrDict φ) (name : String) : Option String :=
  match attrs.find name with
  | .some (AttrValue.str s) =>  .some s
  | _ => .none

def AttrDict.find_int' {φ} (attrs : AttrDict φ) (name : String): Option Int :=
  match attrs.find name with
  | .some (AttrValue.int i _) =>  .some i
  | _ => .none

def AttrDict.find_symbol {φ} (attrs : AttrDict φ) (name : String) : Option String :=
  match attrs.find name with
  | .some (AttrValue.symbol s) =>  .some s
  | _ => .none

@[simp] theorem AttrDict.find_none :
    AttrDict.find (@AttrDict.mk φ []) n' = none := by
  simp [AttrDict.find, List.find?]

@[simp] theorem AttrDict.find_next (v : AttrValue φ)
  (l : List (AttrEntry φ)):
    AttrDict.find (AttrDict.mk (AttrEntry.mk n v :: l)) n' =
    if n == n' then some v else AttrDict.find (AttrDict.mk l) n' := by
  cases H: n == n' <;>
  simp [AttrDict.find, List.find?, AttrEntry.key, AttrEntry.value, H]

def AttrDict.addString (attrs: AttrDict φ) (k: String) (v: String): AttrDict φ :=
    AttrEntry.mk k (v : AttrValue φ) :: attrs

def AttrDict.addType (attrs: AttrDict φ) (k: String) (v: MLIRType φ): AttrDict φ :=
    AttrEntry.mk k (v : AttrValue φ) :: attrs


def Op.addAttr (o: Op φ) (k: String) (v: AttrValue φ): Op φ :=
 match o with
 | Op.mk name res args regions attrs =>
    Op.mk name res args regions (attrs.add (k, v))

def Region.empty {φ} (name: String): Region φ := Region.mk name [] []
def Region.appendOp (bb: Region φ) (op: Op φ): Region φ :=
  match bb with
  | Region.mk name args bbs => Region.mk name args (bbs ++ [op])

def Region.appendOps (bb: Region φ) (ops: List (Op φ)): Region φ :=
  match bb with
  | Region.mk name args bbs => Region.mk name args (bbs ++ ops)


instance : Inhabited (MLIRType φ) where
  default := MLIRType.undefined "INHABITANT"

instance : Inhabited (AttrValue φ) where
  default := AttrValue.str "INHABITANT"

instance : Inhabited (Op φ) where
  default := Op.empty "INHABITANT"

instance : Inhabited (Region φ) where
  default := Region.empty "INHABITANT"

instance : Repr (Module φ) where
  reprPrec
  | Module.mk fs attrs, _ =>
      attrs.map repr ++ fs.map repr |>.map (Format.align true ++ ·) |> Format.join

def Region.fromOps {φ} (os: List (Op φ)) (name: String := "entry") : Region φ :=
  Region.mk name [] os

def Region.setArgs {φ} (bb: Region φ) (args: List (SSAVal × MLIRType φ)) : Region φ :=
  match bb with
    | (Region.mk name _ ops) => (Region.mk name args ops)

end MLIR.AST
