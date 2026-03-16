import Lean
import LeanFixpoint.Syntax
import LeanFixpoint.Constraint
import LeanFixpoint.Elab

/-!
  # Reflect.lean — Reflecting Lean Props back into Constraint AST

  ## Goal

  Given a Lean `Prop` of the form:
  ```
  ∃ κ₁ : Int → Prop, ∃ κ₂ : Int → Int → Prop, …,
    BODY
  ```

  We:
  1. Peel the leading `∃ κᵢ` binders → discover κ-variables
  2. Reflect BODY (∀/→/∧ tree) → `Constraint` AST with `Pred.kapp`
  3. Run κ-elimination (`sol1`, `elim1`)
  4. Elaborate solutions back to `Expr` (witnesses for ∃)
  5. Elaborate the κ-free residual to a `Prop` and discharge with `omega`/`grind`
  6. Assemble the full proof term: `⟨witness₁, ⟨witness₂, …, proof⟩⟩`

  ## Pipeline

  ```
  Expr (∃ κ … → Prop)
    │
    ├─ peelExistentialsCPS  → List KVarInfo × Expr body (with κ fvars in scope)
    │
    ├─ reflectConstraint    → Constraint (Pred.kapp for κ applications)
    │
    ├─ sol1 / elim1         → solved Preds + κ-free Constraint
    │
    ├─ buildKappaWitness    → Expr (fun z => …, the ∃ witness)
    │
    ├─ Constraint.toExpr    → Expr (κ-free Prop, the residual VC)
    │
    └─ grind / omega        → proof of residual
  ```
-/

open Lean Meta Elab Term Tactic

-- ============================================================
-- § 1. KVar Discovery — peeling ∃ binders
-- ============================================================

/-- Info about a κ-variable discovered from an existential binder -/
structure KVarInfo where
  /-- The name from the ∃ binder -/
  name   : Name
  /-- The fvar expr created for this binder -/
  fvar   : Expr
  /-- The FVarId -/
  fvarId : FVarId
  /-- Arity: number of arguments before the final `Prop` -/
  arity  : Nat
  /-- The KVar AST node for use in constraints -/
  kvar   : KVar
deriving Repr

/-- Count arity of `Int → Int → … → Prop` (or `Bool → … → Prop`) -/
private partial def countFunArity : Expr → MetaM Nat
  | .forallE _ _ body _ => do
    let rest ← countFunArity body
    return rest + 1
  | e =>
    if e.isProp then return 0
    else return 0

/-- Generate param names: arity 1 → [`z], arity 2 → [`z₀, `z₁], etc. -/
private def mkParamNames (arity : Nat) : List Name :=
  if arity == 1 then [`z]
  else (List.range arity).map fun i => Name.mkSimple s!"z{i}"

/--
  Peel leading `∃ κ : (Int → … → Prop), …` binders.

  CPS style: the κ-fvars are only valid inside the continuation `k`,
  because they live in `withLocalDeclD` scopes.
-/
partial def peelExistentialsCPS
    (e : Expr)
    (acc : List KVarInfo)
    (k : List KVarInfo → Expr → MetaM α)
    : MetaM α := do
  let e ← whnf e
  match_expr e with
  | Exists _T body =>
    let T ← whnf _T
    let arity ← countFunArity T
    if arity == 0 then
      -- Not κ-shaped (e.g., ∃ x : Int, …), stop peeling
      k acc e
    else
      -- κ-shaped: T = Int → … → Prop
      lambdaTelescope body fun fvars innerBody => do
        if h : fvars.size > 0 then
          let fvar := fvars[0]
          let name := (← fvar.fvarId!.getDecl).userName
          let params := mkParamNames arity
          let kv : KVar := { name := name, params := params }
          let info : KVarInfo := {
            name   := name
            fvar   := fvar
            fvarId := fvar.fvarId!
            arity  := arity
            kvar   := kv
          }
          peelExistentialsCPS innerBody (acc ++ [info]) k
        else
          k acc e
  | _ => k acc e

-- ============================================================
-- § 2. Expr → RExpr / Pred / Constraint reflection
-- ============================================================

/-- Reflection context: tracks which fvars are κ-vars vs ordinary vars -/
structure ReflectCtx where
  kappaMap  : Std.HashMap FVarId KVarInfo := {}
  varMap    : Std.HashMap FVarId Name := {}

def ReflectCtx.addKappa (ctx : ReflectCtx) (info : KVarInfo) : ReflectCtx :=
  { ctx with kappaMap := ctx.kappaMap.insert info.fvarId info }

def ReflectCtx.addVar (ctx : ReflectCtx) (id : FVarId) (name : Name) : ReflectCtx :=
  { ctx with varMap := ctx.varMap.insert id name }

/--
  Reflect a Lean `Expr` back to `RExpr`.

  Handles variables, Int literals, arithmetic, comparisons,
  boolean connectives, and negation.
-/
partial def reflectRExpr (ctx : ReflectCtx) (e : Expr) : MetaM RExpr := do
  let e ← whnf e

  -- fvar → variable
  if let .fvar id := e then
    if let some name := ctx.varMap.get? id then
      return .var name
    if let some info := ctx.kappaMap.get? id then
      return .var info.name

  -- Int literal: Int.ofNat n / Int.negSucc n / raw natLit
  match_expr e with
  | Int.ofNat n =>
    let n ← whnf n
    if let some v := n.natLit? then return .int (Int.ofNat v)
    if n.isAppOfArity ``Nat.zero 0 then return .int 0
  | _ => pure ()
  match_expr e with
  | Int.negSucc n =>
    let n ← whnf n
    if let some v := n.natLit? then return .int (Int.negSucc v)
  | _ => pure ()
  if let some v := e.natLit? then
    return .int (Int.ofNat v)

  -- Arithmetic: HAdd, HSub, HMul, HDiv
  match_expr e with
  | HAdd.hAdd _ _ _ _ l r =>
    return .arith .add (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | HSub.hSub _ _ _ _ l r =>
    return .arith .sub (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | HMul.hMul _ _ _ _ l r =>
    return .arith .mul (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | HDiv.hDiv _ _ _ _ l r =>
    return .arith .div (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()

  -- Comparisons: Eq, LE.le, LT.lt, GE.ge, GT.gt
  match_expr e with
  | Eq _ l r =>
    return .cmp .eq (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | LE.le _ _ l r =>
    return .cmp .le (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | LT.lt _ _ l r =>
    return .cmp .lt (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | GE.ge _ _ l r =>
    return .cmp .ge (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | GT.gt _ _ l r =>
    return .cmp .gt (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()

  -- Not (including Ne = Not (Eq …))
  match_expr e with
  | Not inner =>
    let inner ← whnf inner
    match_expr inner with
    | Eq _ l r =>
      return .cmp .ne (← reflectRExpr ctx l) (← reflectRExpr ctx r)
    | _ =>
      return .not (← reflectRExpr ctx inner)
  | _ => pure ()

  -- And / Or (Prop-level, used inside predicates)
  match_expr e with
  | And l r =>
    return .bop .and (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()
  match_expr e with
  | Or l r =>
    return .bop .or (← reflectRExpr ctx l) (← reflectRExpr ctx r)
  | _ => pure ()

  -- Implication: ∀ _ : P, Q where body has no loose bvars
  if e.isForall then
    let .forallE _ dom body _ := e | unreachable!
    if !body.hasLooseBVars then
      return .bop .imp (← reflectRExpr ctx dom) (← reflectRExpr ctx body)

  -- Fallback error
  throwError s!"reflectRExpr: cannot reflect: {← ppExpr e}"

/--
  Reflect a Lean `Expr` to `Pred`.

  Handles True, False, And, Or, ∃, κ-applications, and
  falls back to `Pred.rexpr` for atomic propositions.
-/
partial def reflectPred (ctx : ReflectCtx) (e : Expr) : MetaM Pred := do
  let e ← whnf e

  -- True / False
  match_expr e with | True  => return .tru | _ => pure ()
  match_expr e with | False => return .fls | _ => pure ()

  -- And
  match_expr e with
  | And l r => return .conj (← reflectPred ctx l) (← reflectPred ctx r)
  | _ => pure ()

  -- Or
  match_expr e with
  | Or l r => return .disj (← reflectPred ctx l) (← reflectPred ctx r)
  | _ => pure ()

  -- ∃ x : Int, p  →  Pred.exist
  match_expr e with
  | Exists _T body =>
    let T ← whnf _T
    let bty ←
      if ← isDefEq T (mkConst ``Int)  then pure BaseTy.int
      else if ← isDefEq T (mkConst ``Bool) then pure BaseTy.bool
      else throwError s!"reflectPred: unsupported ∃ type: {← ppExpr T}"
    lambdaTelescope body fun fvars innerBody => do
      if h : fvars.size > 0 then
        let fvar := fvars[0]
        let name := (← fvar.fvarId!.getDecl).userName
        let ctx' := ctx.addVar fvar.fvarId! name
        return .exist name bty (← reflectPred ctx' innerBody)
      else
        throwError "reflectPred: ∃ without binder"
  | _ => pure ()

  -- κ application: head is a κ-fvar applied to args
  let head := e.getAppFn
  if let .fvar id := head then
    if let some info := ctx.kappaMap.get? id then
      let args := e.getAppArgs
      let mut argNames : List Name := []
      for arg in args do
        let arg ← whnf arg
        if let .fvar argId := arg then
          if let some name := ctx.varMap.get? argId then
            argNames := argNames ++ [name]
          else
            let decl ← argId.getDecl
            argNames := argNames ++ [decl.userName]
        else
          throwError s!"reflectPred: κ arg is not a variable: {← ppExpr arg}"
      return .kapp info.kvar argNames

  -- Fallback: Pred.rexpr
  return .rexpr (← reflectRExpr ctx e)

/--
  Reflect a `Prop` body into `Constraint`.

  Recognizes:
  - `∀ x : Int, P → C`  →  `Constraint.imp x .int P C`
  - `C₁ ∧ C₂`           →  `Constraint.conj`
  - leaf predicate       →  `Constraint.pred`
-/
partial def reflectConstraint (ctx : ReflectCtx) (e : Expr) : MetaM Constraint := do
  let e ← whnf e

  -- And → Constraint.conj
  match_expr e with
  | And l r =>
    return .conj (← reflectConstraint ctx l) (← reflectConstraint ctx r)
  | _ => pure ()

  -- ∀ x : Int, P → C   →   Constraint.imp
  if e.isForall then
    let .forallE name dom body bi := e | unreachable!
    let dom ← whnf dom
    let btyOpt ←
      if ← isDefEq dom (mkConst ``Int)  then pure (some BaseTy.int)
      else if ← isDefEq dom (mkConst ``Bool) then pure (some BaseTy.bool)
      else pure none
    match btyOpt with
    | some bty =>
      withLocalDeclD name dom fun fvar => do
        let ctx' := ctx.addVar fvar.fvarId! name
        let bodyInst := body.instantiate1 fvar
        let bodyInst ← whnf bodyInst
        -- Check if body is `P → C` (implication, i.e., non-dependent ∀)
        if bodyInst.isForall then
          let .forallE _ hypTy concl _ := bodyInst | unreachable!
          -- If the conclusion does NOT depend on the hyp binder,
          -- this is an implication P → C
          if !concl.hasLooseBVars then
            let hyp  ← reflectPred ctx' hypTy
            let body ← reflectConstraint ctx' concl
            return .imp name bty hyp body
          else
            -- Dependent: treat as chained ∀
            -- `∀ x : bty, ∀ y : bty', …`
            -- Recur on the full bodyInst (which is itself a ∀)
            let inner ← reflectConstraint ctx' bodyInst
            return .imp name bty .tru inner
        else
          -- `∀ x : bty, body` with no further ∀ structure
          let inner ← reflectConstraint ctx' bodyInst
          return .imp name bty .tru inner
    | none => pure ()

  -- Leaf: Constraint.pred
  return .pred (← reflectPred ctx e)

/--
  Build the witness `Expr` for an existential κ.

  Given κ with arity n, params [z₀, …, zₙ₋₁], and solution `sol`,
  builds: `fun (z₀ : Int) (z₁ : Int) … (zₙ₋₁ : Int) => sol_as_Prop`
-/
def buildKappaWitness (info : KVarInfo) (sol : Pred) : MetaM Expr := do
  let intTy := mkConst ``Int
  go info.kvar.params intTy {} sol
where
  go (params : List Name) (intTy : Expr) (env : VarMap) (sol : Pred)
      : MetaM Expr :=
    match params with
    | [] => sol.toExpr env
    | p :: ps =>
      withLocalDeclD p intTy fun fvar => do
        let env' := env.insert p fvar
        let body ← go ps intTy env' sol
        mkLambdaFVars #[fvar] body

/--
  `fusion` — tactic that solves existential refinement-type VCs.

  Given a goal `⊢ ∃ κ₁ : Int → Prop, …, BODY`:
  1. Peels ∃ κ binders → discovers κ-variables
  2. Reflects BODY into `Constraint` AST (with `Pred.kapp`)
  3. Solves each κ via `sol1` + `elim1`
  4. Provides witnesses for each ∃ via `Exists.intro`
  5. Discharges the residual κ-free VC with `omega`/`grind`
-/
elab "fusion" : tactic => do
  let goal ← getMainGoal
  let goalTy ← goal.getType
  let goalTy ← instantiateMVars goalTy

  peelExistentialsCPS goalTy [] fun kvarInfos bodyExpr => do

    if kvarInfos.isEmpty then
      throwError "fusion: no existential κ-variables found in goal"

    -- Build reflection context
    let mut ctx : ReflectCtx := {}
    for info in kvarInfos do
      ctx := ctx.addKappa info

    -- Reflect body → Constraint
    let constraint ← reflectConstraint ctx bodyExpr

    logInfo m!"fusion: κ-vars: {kvarInfos.map (·.name)}"
    logInfo m!"fusion: constraint:\n{toString constraint}"

    -- Solve each κ
    let mut currentC := constraint
    let mut solutions : List (KVarInfo × Pred) := []

    for info in kvarInfos do
      let sol := currentC.sol1 info.kvar
      logInfo m!"  {info.name}({info.kvar.params}) = {toString sol}"
      solutions := solutions ++ [(info, sol)]
      currentC := currentC.elim1 info.kvar

    logInfo m!"fusion: residual:\n{toString currentC}"

    -- Provide existential witnesses
    let mut goalId := goal

    for (info, sol) in solutions do
      let witness ← buildKappaWitness info sol
      logInfo m!"fusion: witness for {info.name}: {← ppExpr witness}"

      -- `Exists.intro witness ?proof`
      let existsIntro := mkConst ``Exists.intro
      let newGoals ← goalId.apply existsIntro
      match newGoals with
      | [gWitness, gBody] =>
        gWitness.assign witness
        goalId := gBody
      | _ =>
        -- Sometimes `apply` unifies differently; try exact on the first
        -- and take the remaining
        throwError s!"fusion: expected 2 subgoals from Exists.intro, got {newGoals.length}"

    -- Discharge residual
    setGoals [goalId]
    try
      evalTactic (← `(tactic| first | grind | omega))
      logInfo m!"fusion: VC discharged ✅"
    catch e =>
      logWarning m!"fusion: could not auto-discharge residual"
      logWarning m!"fusion: {e.toMessageData}"

-- ============================================================
-- § 5. Tests
-- ============================================================

section FusionTests

/-
  Target Prop: the classic example from the paper.

  ∃ κ : Int → Prop,
    (∀ x, 0 ≤ x → ∀ ν, ν = x - 1 → κ ν) ∧
    (∀ y, κ y → ∀ ν, ν = y + 1 → 0 ≤ ν)

  Expected solution: κ(z) = ∃ x : Int. (0 ≤ x ∧ z = x - 1)
  Residual VC (after substitution + simplification):
    ∀ y, (∃ x, 0 ≤ x ∧ y = x - 1) → ∀ ν, ν = y + 1 → 0 ≤ ν
  Which should be dischargeable by omega.
-/
def ex1VCProp : Prop :=
  ∃ kappa : Int → Prop,
    (∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → kappa ν)) ∧
    (∀ y : Int, kappa y →
      ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

-- Attempt to prove it with fusion
theorem ex1VCProof : ex1VCProp := by
  fusion

end FusionTests
