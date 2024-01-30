/-
This file implements common subexpression elimination for our SSA based IR.
-/
import SSA.Core.Framework
import SSA.Projects.DCE.DCE
import Mathlib.Data.HashMap

/- Decidable Equality for Coms. -/
section DecEqCom
variable [DecidableEq Ty]
variable [OP_DECEQ : DecidableEq Op]
variable [OpSignature Op Ty]

/-- can decide equality on argument vectors. -/
def argVector.decEq : DecidableEq (HVector (Ctxt.Var Γ) ts) :=
  fun as bs =>
    match as, bs with
    | .nil, .nil => .isTrue rfl
    | .cons (a := ty) a as', .cons b bs' =>
      have VAR_DECEQ : DecidableEq (Ctxt.Var Γ ty) := inferInstance
      match VAR_DECEQ a b with
      | .isTrue heq =>
        match argVector.decEq as' bs' with
        | .isFalse hneq => .isFalse (fun CONTRA => by obtain ⟨ha, has⟩ := CONTRA; contradiction)
        | .isTrue heq' => .isTrue (by simp [heq', heq])
      | .isFalse hneq => .isFalse (fun CONTRA => by obtain ⟨ha, has⟩ := CONTRA; contradiction)

mutual
def regionVector.decEq (ts : List (Ctxt Ty × Ty))
  (as bs : (HVector ((fun t : Ctxt Ty × Ty => Com Op t.1 t.2)) <| ts)) :
  Decidable (as = bs) :=
    match as, bs with
    | .nil, .nil => .isTrue rfl
    | .cons (a := α) a as', .cons b bs' =>
      match Com.decEq a b with
      | .isTrue HD_EQ =>
        match regionVector.decEq _ as' bs' with
        | .isTrue TL_EQ => .isTrue (by subst HD_EQ; subst TL_EQ; rfl; done)
        | .isFalse neq => .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)
      | .isFalse neq => .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)

def Expr.decEq (e e' : Expr Op Γ α) : Decidable (e = e') :=
  match e, e' with
  | .mk op ty_eq args regArgs, .mk op' ty_eq' args' regArgs' =>
    if OP : op = op'
    then
      match argVector.decEq args (OP ▸ args') with
      | .isTrue ARGEQ =>
        match regionVector.decEq _ regArgs (OP ▸ regArgs') with
        | .isTrue REGEQ =>
            .isTrue (by subst ty_eq; subst OP; subst ARGEQ; subst REGEQ; rfl; done)
        | .isFalse neq =>
          .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)
      | .isFalse neq =>
        .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)
    else .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)

def Com.decEq (c c' : Com Op Γ α) : Decidable (c = c') :=
  match c, c' with
  | .ret v, .ret v' =>
    have VAR_DECEQ : DecidableEq (Ctxt.Var Γ α) := inferInstance
    match VAR_DECEQ v v' with
    | .isTrue heq => .isTrue (by simp [heq])
    | .isFalse f => .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)
  | .lete (α := α) e body, .lete (α := β) e' body' =>
    match decEq α β with
    | .isTrue TY_EQ =>
      match Expr.decEq e (TY_EQ ▸ e') with
      | .isFalse neq => .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)
      | .isTrue EXPR_EQ =>
        match Com.decEq body (TY_EQ ▸ body') with
        | .isFalse neq =>  .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)
        | .isTrue BODY_EQ =>
          .isTrue (by subst TY_EQ; subst EXPR_EQ; subst BODY_EQ; rfl)
    | .isFalse f => .isFalse (fun CONTRA => by rcases CONTRA; . contradiction)
  | .ret .., .lete .. => .isFalse Com.noConfusion
  | .lete .., .ret .. => .isFalse Com.noConfusion
end
termination_by
Com.decEq c c' =>  sizeOf c
Expr.decEq e e' => sizeOf e
regionVector.decEq as bs => sizeOf as

end DecEqCom

namespace CSE

/-- State stored by CSE pass. -/
structure State (Op : Type) [Goedel Ty] [OpSignature Op Ty] [OpDenote Op Ty] (lets : Lets Op Γstart Γ) where
  /-- map variable to its canonical value -/
  var2var : (v : Γ.Var α) → { v' : Γ.Var α // ∀ (V : Γstart.Valuation), (lets.denote V) v = (lets.denote V) v' }
  /-- map an Expr to its canonical variable -/
  expr2cache : (α : Ty) → (e : Expr Op Γ α) → Option ({ v : Γ.Var α // ∀ (V : Γstart.Valuation), (lets.denote V) v = e.denote (lets.denote V) })

/-- The empty CSEing state. -/
def State.empty [Goedel Ty] [OpSignature Op Ty] [OpDenote Op Ty] (lets : Lets Op Γstart Γ) : State Op lets where
  var2var := fun v => ⟨v, by intros V; rfl⟩
  expr2cache := fun α e => .none

def State.snocNewExpr2Cache
 [Goedel Ty] [DecidableEq Ty] [DecidableEq Op] [OpSignature Op Ty] [OpDenote Op Ty]
 {Γ : Ctxt Ty} {α : Ty}
 {lets : Lets Op Γstart Γ}
 (s : State Op lets) (e : Expr Op Γ α) : State Op (Lets.lete lets e) :=
 {
  var2var := fun v => by
    apply Subtype.mk
    intros V
    rfl
  expr2cache := fun β eneedle =>
    let eneedleΓ? := DCE.Expr.deleteVar? (DEL := Deleted.deleteSnoc Γ α) (eneedle)
    match eneedleΓ? with
    | .none => .none -- this expression actually uses β in some nontrivial way, we're fucked,
    | .some ⟨eneedleΓ, heneedleΓ⟩ =>
        match s.expr2cache _ eneedleΓ with /- find in cache -/
        | .some ⟨v', hv'⟩ =>
          .some ⟨v', by {
            intros V
            rw [heneedleΓ]
            simp [Lets.denote]
            rw [hv' V]
            congr
            done
          }⟩
        | .none => /- not in cache, check if new expr. -/
          match decEq α β with
          | .isFalse _neq => .none
          | .isTrue hβ =>
            match Expr.decEq (hβ ▸  eneedleΓ) e with
            | .isTrue exprEq => /- same expression, return the variable. -/
                .some ⟨hβ ▸ Ctxt.Var.last Γ α, by {
                  intros V; subst hβ; simp at exprEq; subst exprEq; simp [cast_eq];
                  rw [heneedleΓ]; congr; done}⟩
            | .isFalse _neq => .none -- s.expr2cache β eneedleΓ /- different expression, query cache. -/
 }

/-- denoting a `lete` is the same as `snoc`ing the denotation of `e` onto the old valuation `V`. -/
@[simp]
theorem Lets.denote_lete [Goedel Ty] [OpSignature Op Ty] [OpDenote Op Ty]
  {Γstart Γ : Ctxt Ty}
  {lets : Lets Op Γstart Γ}
  (e : Expr Op Γ α)
  (V : Ctxt.Valuation Γstart) :
  Lets.denote (Lets.lete lets e) V = (Ctxt.Valuation.snoc (Lets.denote lets V) (Expr.denote e (Lets.denote lets V))) := by
  simp [Lets.denote, eq_rec_constant]
  funext t v
  cases v using Ctxt.Var.casesOn <;> simp
  done

/-- Remap the last variable in a context, to get a new context without the last variable -/
def _root_.Ctxt.Hom.remapLast [Goedel Ty]  {α : Ty} (Γ : Ctxt Ty) (var : Γ.Var α) :
  Ctxt.Hom (Γ.snoc α) Γ := fun ty' var' => by
    cases var' using Ctxt.Var.casesOn
    case toSnoc var' => exact var'
    case last => exact var

section RemapVar
def VarRemapVar [Goedel Ty] [DecidableEq Ty] [DecidableEq Op] [OpSignature Op Ty] [OpDenote Op Ty]
  {Γstart Γ Γ' : Ctxt Ty} {α : Ty}
  (lets : Lets Op Γstart Γ)
  (hom : Ctxt.Hom Γ' Γ)
  (vold : Γ.Var α) (vnew : Γ'.Var α)
  (VNEW: ∀ (Vstart : Ctxt.Valuation Γstart), (lets.denote Vstart) vold = ((lets.denote Vstart).comap hom) vnew)
  (w' : Γ'.Var β) :
  { w : Γ.Var β //
    ∀ (Vstart : Ctxt.Valuation Γstart), (lets.denote Vstart) w = ((lets.denote Vstart).comap hom) w' } :=
    if TY : β = α
    then
      if H : TY ▸ w' = vnew
      then ⟨TY ▸ vold, by
        subst TY
        simp at H ⊢
        subst H
        intros Vstart
        rw [VNEW Vstart]
        done⟩
      else ⟨hom w', by simp [Ctxt.Valuation.comap]⟩
    else ⟨hom w', by simp [Ctxt.Valuation.comap]⟩

def arglistRemapVar [Goedel Ty] [DecidableEq Ty] [DecidableEq Op] [OpSignature Op Ty] [OpDenote Op Ty]
  {Γstart Γ Γ' : Ctxt Ty} {α : Ty}
  (lets : Lets Op Γstart Γ)
  (hom : Ctxt.Hom Γ' Γ)
  (vold : Γ.Var α) (vnew : Γ'.Var α)
  (VNEW: ∀ (Vstart : Ctxt.Valuation Γstart), (lets.denote Vstart) vold = ((lets.denote Vstart).comap hom) vnew)
  {ts : List Ty} (as' : HVector (Ctxt.Var Γ') <| ts) :
    { as : HVector (Ctxt.Var Γ) <| ts //
      ∀ (Vstart : Γstart.Valuation), as.map (fun t v => (lets.denote Vstart) v) = as'.map (fun t v' => ((lets.denote Vstart).comap hom) v') } :=
  match as' with
  | .nil => ⟨.nil, by simp [HVector.map]⟩
  | .cons a' as' =>
    let ⟨a, ha⟩ := VarRemapVar lets hom vold vnew VNEW a'
    let ⟨as, has⟩ := arglistRemapVar lets hom vold vnew VNEW as'
    ⟨.cons a as, by
      intros Vstart
      simp [HVector.map]
      rw [ha Vstart]
      rw [has Vstart]
      constructor
      simp [ha]
      congr
      done
    ⟩

def ExprRemapVar [Goedel Ty] [DecidableEq Ty] [DecidableEq Op] [OpSignature Op Ty] [OpDenote Op Ty]
  {Γstart Γ Γ' : Ctxt Ty} {α : Ty}
  (lets : Lets Op Γstart Γ)
  (hom : Ctxt.Hom Γ' Γ)
  (vold : Γ.Var α) (vnew : Γ'.Var α)
  (VNEW: ∀ (Vstart : Ctxt.Valuation Γstart), (lets.denote Vstart) vold = ((lets.denote Vstart).comap hom) vnew)
  (e' : Expr Op Γ' β) :
  { e : Expr Op Γ β  // ∀ (Vstart : Ctxt.Valuation Γstart),
    e.denote (lets.denote Vstart) = e'.denote ((lets.denote Vstart).comap hom) } :=
    match e' with
    | .mk op ty_eq args regArgs =>
      let ⟨args', hargs'⟩ := arglistRemapVar lets hom vold vnew VNEW args
      ⟨.mk op ty_eq args' regArgs, by
        intros Vstart
        subst ty_eq
        simp [Expr.denote]
        rw [hargs']
        done
      ⟩
    -- TODO: extend to Com.
end RemapVar


/-
e: Expr Op Γ α
body: Com Op (Ctxt.snoc Γ α) α✝
e': Expr Op Γ α
he': Expr.denote e' = Expr.denote e
v'?: Option { v' // ∀ (V : Ctxt.Valuation Γstart), Lets.denote lets V v' = Expr.denote e (Lets.denote lets V) }
s': State Op (Lets.lete lets e') := snocNewExpr2Cache s e'
-/

def State.snocOldExpr2Cache
 [Goedel Ty] [DecidableEq Ty] [DecidableEq Op] [OpSignature Op Ty] [OpDenote Op Ty]
 {Γ : Ctxt Ty} {α : Ty}
 {lets : Lets Op Γstart Γ}
 (s : State Op lets) (enew : Expr Op Γ α) (eold : Expr Op Γ α) (henew :
    ∀ (V : Γstart.Valuation), enew.denote (lets.denote V) = eold.denote (lets.denote V))
  (vold : Γ.Var α) (hv : ∀ (V : Γstart.Valuation), eold.denote (lets.denote V) = lets.denote V vold) :
  State Op (Lets.lete lets enew) := {
    var2var := fun v => by
      cases v using Ctxt.Var.casesOn
      case toSnoc v => -- old variable, look up 'var2var'
        let ⟨v', hv'⟩ := s.var2var v
        apply (Subtype.mk v'.toSnoc)
        intros V
        simp [Lets.denote_lete]
        rw [hv']

      case last => -- new variable, return the CSE'd variable.
        apply (Subtype.mk vold.toSnoc)
        intros V
        simp [Lets.denote_lete]
        rw [← hv]
        rw [henew]
    expr2cache := fun β eneedle =>
      let homRemap := Ctxt.Hom.remapLast Γ vold
      let lastVar := (Ctxt.Var.last Γ α)
      let ⟨eneedle', heneedle'⟩ := ExprRemapVar lets homRemap vold lastVar (by {
        intros Vstart
        simp [Ctxt.Hom.remapLast, Ctxt.Valuation.comap]
        done
      })  eneedle
      match s.expr2cache β eneedle' with
      | .none => .none
      | .some ⟨e', he'⟩ =>
        .some ⟨e', by {
          intros V
          simp
          rw [he']
          rw [heneedle']
          congr
          funext ty var
          cases var using Ctxt.Var.casesOn
          case e_Γv.h.h.toSnoc v =>
            simp [Ctxt.Valuation.comap, Ctxt.Hom.remapLast]
            done
          case e_Γv.h.h.last =>
            simp [Ctxt.Valuation.comap, Ctxt.Hom.remapLast]
            rw [henew]
            rw [hv]
            done
        }⟩
}

/-- Replace the variables in `as` with new variables that have the same valuation -/
def State.cseArgList
 [Goedel Ty] [OpSignature Op Ty] [OpDenote Op Ty]
  {Γstart Γ : Ctxt Ty} {lets : Lets Op Γstart Γ} (s : State Op lets)
  {ts : List Ty}
  (as : HVector (Ctxt.Var Γ) <| ts) :
  { as' : HVector (Ctxt.Var Γ) <| ts // ∀ (V : Γstart.Valuation), as.map (lets.denote V).eval = as'.map (lets.denote V).eval  } :=
  match as with
  | .nil => ⟨.nil, by
      simp [HVector.map]
    ⟩
  | .cons a as =>
    let ⟨a', ha'⟩ :=  s.var2var a
    let ⟨as', has'⟩ := s.cseArgList as
    ⟨.cons a' as', by
          intros V
          simp [HVector.map]
          constructor
          apply ha'
          apply has'
    ⟩

/-- Default instance for `partial def` to compile. -/
instance [Goedel Ty] [OpSignature Op Ty] [OpDenote Op Ty] : Inhabited (
          {lets : Lets Op Γstart Γ} →
          State Op lets →
          {ts : List (Ctxt Ty × Ty)} →
          (rs : HVector (fun t => Com Op t.1 t.2) ts) →
          { rs' : HVector (fun t => Com Op t.1 t.2) ts // HVector.denote rs = HVector.denote rs' }) where
  default := fun _s _ts rs => ⟨rs, rfl⟩

/-- Default instance for `partial def` to compile. -/
instance [Goedel Ty] [OpSignature Op Ty] [OpDenote Op Ty] : Inhabited (
  {lets : Lets Op Γstart Γ} →
  State Op lets →
  (com: Com Op Γ α) →
  { com' : Com Op Γ α // ∀ (V: Ctxt.Valuation Γ), com.denote V = com'.denote V }) where
  default := fun _s com => ⟨com, by intros V; rfl⟩


/- CSE for HVector / Com / Expr. -/
mutual
variable [DecidableEq Ty] [DecidableEq Op] [Goedel Ty] [OpSignature Op Ty] [OpDenote Op Ty]

/-- Replace the regions in `rs` with new regions that have the same valuation -/
unsafe def State.cseRegionArgList
  {Γstart Γ : Ctxt Ty}
  {lets : Lets Op Γstart Γ}
  (s : State Op lets)
  {ts : List (Ctxt Ty × Ty)}
  (rs : HVector ((fun t : Ctxt Ty × Ty => Com Op t.1 t.2)) <| ts) :
  { rs' : HVector ((fun t : Ctxt Ty × Ty => Com Op t.1 t.2)) <| ts //
    HVector.denote rs = HVector.denote rs' } :=
  let H := HVector.map (fun _Γα com => Com.denote com) rs
  match rs with
  | .nil => ⟨.nil, by
      simp [HVector.map]
    ⟩
  | .cons r rs =>
    -- Need to create a fresh state to CSE the region.
    let s' := State.empty Lets.nil
    let ⟨r', hr'⟩ :=  s'.cseCom r
    let ⟨rs', hrs'⟩ := s.cseRegionArgList rs
    ⟨.cons r' rs', by
          simp [HVector.denote]
          constructor
          funext V
          apply hr'
          apply hrs'
    ⟩

/-- lookup an expression in the state and return a corresponding CSE'd variable for it, along with the CSE'd expression
  that was looked up in the map for the variable.  -/
unsafe def State.cseExpr
 {Γstart Γ : Ctxt Ty}
 {lets : Lets Op Γstart Γ}
 (s : State Op lets)
 (e : Expr Op Γ α) :
 {e' : Expr Op Γ α //
  ∀ (V : Γstart.Valuation), e'.denote (lets.denote V) = e.denote (lets.denote V) } × Option ({ v' : Γ.Var α // ∀ (V : Γstart.Valuation), (lets.denote V) v' = e.denote (lets.denote V) }) :=
  match E : e with
  | .mk op ty_eq args regArgs =>
      let ⟨args', hargs'⟩ := s.cseArgList args
      let regArgs' := s.cseRegionArgList regArgs
      let ⟨regArgs', hregArgs'⟩ := regArgs'
      let e' : Expr Op Γ α  := .mk op ty_eq args' regArgs'
      ⟨⟨e', by {
        intros V
        simp [E, hargs', Expr.denote_unfold]
        congr 1
        simp [Ctxt.Valuation.eval] at hargs'
        rw [hargs']
        rw [hregArgs']
        done
      }⟩,
        match s.expr2cache _ e with
        | .some ⟨v', hv'⟩ =>
          .some ⟨v', by
            intros V
            simp [hv']
            simp [E]
          ⟩
        | .none => .none
      ⟩

unsafe def State.cseCom {α : Ty}
  {lets : Lets Op Γstart Γ}
  (s : State Op lets)
  (com: Com Op Γ α) :
  { com' : Com Op Γ α // ∀ (V: Ctxt.Valuation Γstart), com.denote (lets.denote V) = com'.denote (lets.denote V) } :=
  match com with
  | .ret v => ⟨.ret (s.var2var v).val, by
      let ⟨v', hv'⟩ := s.var2var v
      intros VΓ
      simp
      simp [Com.denote, hv']⟩
  | .lete (α := α) e body =>
      let ⟨⟨e', he'⟩, v'?⟩ := s.cseExpr e
      match v'? with
      | .none => /- no variable to replace. -/
        let s' := s.snocNewExpr2Cache (e := e') /- add this expression into the cache for the latest variable. -/
        let ⟨body', hbody'⟩ := s'.cseCom body
        ⟨.lete e' body',  by
            intros VΓ
            simp [Com.denote]
            simp [Lets.denote_lete] at hbody' ⊢
            rw [← hbody']
            rw [he']
            done⟩
      | .some ⟨v', hv'⟩ =>
        let s' := s.snocOldExpr2Cache (enew := e') (eold := e) (henew := by { intros V; rw [he'] })
          (vold := v') (hv := by {intros V; rw [hv'] }) -- add this expression into the cache for the latest variable.
        let ⟨body', hbody'⟩ := s'.cseCom body
        -- TODO: delete the ``e` to get a `body'` in context `Γ`, not `Γ.snoc α`.
        ⟨.lete e body' -- we still keep the `e` for now. In the next version, we will delete the `e`
        , by
            intros V
            simp [Com.denote]
            simp [Lets.denote_lete] at hbody' ⊢
            specialize (hbody' V)
            specialize (he' V)
            rw [he'] at hbody'
            apply hbody'
            done
        ⟩

end -- mutual.

/-- common subexpression elimination entry point. -/
unsafe def cse' [DecidableEq Ty] [DecidableEq Op] [OpSignature Op Ty] [Goedel Ty] [OpDenote Op Ty]
  {α : Ty} {Γ : Ctxt Ty} (com: Com Op Γ α) :
  { com' : Com Op Γ α // ∀ (V: Ctxt.Valuation Γ), com.denote V = com'.denote V } :=
    let ⟨com', hcom'⟩ := State.cseCom (State.empty Lets.nil) com
    ⟨com', by {
      intros V
      specialize (hcom' V)
      simp [Lets.denote] at hcom'
      assumption
    }⟩

namespace Examples
/-- A very simple type universe. -/
inductive ExTy
  | nat
  | bool
  deriving DecidableEq, Repr

@[reducible]
instance : Goedel ExTy where
  toType
    | .nat => Nat
    | .bool => Bool

inductive ExOp :  Type
  | add : ExOp
  | beq : ExOp
  | cst : ℕ → ExOp
  deriving DecidableEq, Repr

instance : OpSignature ExOp ExTy where
  signature
    | .add    => ⟨[.nat, .nat], [], .nat⟩
    | .beq    => ⟨[.nat, .nat], [], .bool⟩
    | .cst _  => ⟨[], [], .nat⟩

@[reducible]
instance : OpDenote ExOp ExTy where
  denote
    | .cst n, _, _ => n
    | .add, .cons (a : Nat) (.cons b .nil), _ => a + b
    | .beq, .cons (a : Nat) (.cons b .nil), _ => a == b

def cst {Γ : Ctxt _} (n : ℕ) : Expr ExOp Γ .nat  :=
  Expr.mk
    (op := .cst n)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := .nil)

def add {Γ : Ctxt _} (e₁ e₂ : Ctxt.Var Γ .nat) : Expr ExOp Γ .nat :=
  Expr.mk
    (op := .add)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := .nil)

attribute [local simp] Ctxt.snoc

def ex1_pre_cse : Com ExOp ∅ .nat :=
  Com.lete (cst 1) <|
  Com.lete (cst 1) <|
  Com.lete (add ⟨0, by simp⟩ ⟨1, by simp⟩) <|
  Com.ret ⟨0, by simp [Ctxt.snoc]⟩
#eval ex1_pre_cse

unsafe def ex1_post_cse :
 { com' : Com ExOp ∅ .nat // ∀ V, ex1_pre_cse.denote V = com'.denote V } :=
   cse' ex1_pre_cse
#eval ex1_post_cse
/-
CSE.Examples.ExOp.cst 1[[]] -- %1
CSE.Examples.ExOp.cst 1[[]] -- %0
CSE.Examples.ExOp.add[[%1, ,, %1]] -- see that the more recent use is dead.
return %0
-/

unsafe def ex1_post_cse_post_dce :
  { com : Com ExOp ∅ .nat // ∀ V, ex1_post_cse.val.denote V = com.denote V } :=
    (DCE.dce' ex1_post_cse.val)
#eval ex1_post_cse_post_dce
/-
CSE.Examples.ExOp.cst 1[[]]
CSE.Examples.ExOp.add[[%0, ,, %0]] -- see that the dead use has been killed.
return %0
-/
end Examples

end CSE
