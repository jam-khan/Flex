import Lean
import Std
import LeanFixpoint.VCG.While.Types
import LeanFixpoint.VCG.While.Semantics
import LeanFixpoint.Tactic.Tactics.Hoist

open Lean Meta Elab Tactic

partial def evalEraseDupsExpr (e : Expr) : MetaM Expr := do
  transform e fun subterm => do
    if subterm.isAppOf ``List.eraseDups then
      let reduced ← whnf subterm
      return .done (← instantiateMVars reduced)
    else
      return .continue

/-! ## `imp_vc_sound` tactic -/

private partial def collectStringArgs (e : Expr) : Array String :=
  match e with
  | .app f (.lit (.strVal s)) => (collectStringArgs f).push s
  | .app f a                  => collectStringArgs f ++ collectStringArgs a
  | .lam _ _ b _              => collectStringArgs b
  | .letE _ _ v b _           => collectStringArgs v ++ collectStringArgs b
  | .mdata _ b                => collectStringArgs b
  | _                         => #[]

private structure CmdInfo where
  initScope : Array String
  assigned  : Array String

private partial def analyzeCmdExpr (e : Expr) : MetaM CmdInfo := do
  let e ← withTransparency .all (whnf e)
  let args := e.getAppArgs
  if e.isConst && e.constName! == ``Cmd.skip then
    return { initScope := #[], assigned := #[] }
  else if e.isAppOfArity ``Cmd.assign 2 then
    let xStr := if let .lit (.strVal s) := args[0]! then s else ""
    return { initScope := collectStringArgs args[1]!, assigned := #[xStr] }
  else if e.isAppOfArity ``Cmd.seq 2 then
    let i1 ← analyzeCmdExpr args[0]!
    let i2 ← analyzeCmdExpr args[1]!
    let reads2 := i2.initScope.filter (fun v => !i1.assigned.contains v)
    return { initScope := i1.initScope ++ reads2,
             assigned  := i1.assigned ++ i2.assigned }
  else if e.isAppOfArity ``Cmd.ite 3 then
    let gReads := collectStringArgs args[0]!
    let i1 ← analyzeCmdExpr args[1]!
    let i2 ← analyzeCmdExpr args[2]!
    return { initScope := gReads ++ i1.initScope ++ i2.initScope,
             assigned  := i1.assigned ++ i2.assigned }
  else if e.isAppOfArity ``Cmd.cwhile 2 then
    let gReads := collectStringArgs args[0]!
    let ib ← analyzeCmdExpr args[1]!
    return { initScope := gReads ++ ib.initScope,
             assigned  := ib.assigned }
  else
    throwError "vcg_scope: cannot analyze Cmd expression: {e}"

elab "imp_vc_sound" : tactic => do
  let goal   ← getMainGoal
  let target ← goal.getType
  unless target.isAppOfArity ``ValidHoareTriple 3 do
    throwTacticEx `vcg_scope goal
      m!"goal must be of the form `ValidHoareTriple P c Q`, got: {target}"
  let cmdExpr := target.getAppArgs[1]!
  let info ← analyzeCmdExpr cmdExpr
  let inScope : List String := info.initScope.toList.eraseDups
  let inScopeTerms : Array (TSyntax `term) := inScope.toArray.map (fun s => Lean.quote s)
  let listTerm : TSyntax `term ← `([$inScopeTerms,*])
  let soundId : TSyntax `term := mkIdent `whileCHC_sound
  evalTactic (← `(tactic| apply $soundId $listTerm ; simp [*] ; hoist_exists))

elab "simp_scopes" : tactic => do
  liftMetaTactic fun goal => do
    let target ← goal.getType
    let target' ← evalEraseDupsExpr target
    if target == target' then
      pure [goal]
    else
      let eqProof ← mkEqRefl target'
      let newGoal ← goal.replaceTargetEq target' eqProof
      pure [newGoal]
  evalTactic (← `(tactic| try simp [*] ; hoist_exists))

/-! ## `replace_state` tactic

  Transforms every `∀ (s : State), body` subgoal into
  `∀ v₁ v₂ … : Int, body[s "x₁" ↦ v₁, s "x₂" ↦ v₂, …]`
  where `x₁, x₂, …` are the variable names read via `s "xi"` in `body`.
-/

/-- Check whether a type (after full reduction) is `State = CVar → Int = String → Int`. -/
private def isStateType (t : Expr) : MetaM Bool := do
  let t' ← withTransparency .all (whnf t)
  match t' with
  | .forallE _ d c _ =>
    let d' ← withTransparency .all (whnf d)
    let c' ← withTransparency .all (whnf c)
    return (d'.isConst && d'.constName! == ``String) &&
           (c'.isConst && c'.constName! == ``Int)
  | _ => return false

/-- Collect all variable names appearing as `s "name"` in `e`, where `s` is `stateVar`. -/
private partial def collectStateVarsFree (stateVar : Expr) (e : Expr) : Array String :=
  match e with
  | .app f (.lit (.strVal v)) =>
      (if f == stateVar then #[v] else #[]) ++
      collectStateVarsFree stateVar f
  | .app f a =>
      collectStateVarsFree stateVar f ++ collectStateVarsFree stateVar a
  | .lam _ t b _ =>
      collectStateVarsFree stateVar t ++ collectStateVarsFree stateVar b
  | .forallE _ t b _ =>
      collectStateVarsFree stateVar t ++ collectStateVarsFree stateVar b
  | .letE _ t v b _ =>
      collectStateVarsFree stateVar t ++ collectStateVarsFree stateVar v ++
      collectStateVarsFree stateVar b
  | .mdata _ b => collectStateVarsFree stateVar b
  | _ => #[]

/-- Replace every `stateVar "varNames[i]"` occurrence in `e` with `varExprs[i]`. -/
private partial def substituteStateVars
    (stateVar : Expr) (varNames : Array String) (varExprs : Array Expr)
    (e : Expr) : Expr :=
  match e with
  | .app f (.lit (.strVal v)) =>
      if f == stateVar then
        match varNames.findIdx? (· == v) with
        | some i => varExprs[i]!
        | none   => e
      else
        .app (substituteStateVars stateVar varNames varExprs f)
             (.lit (.strVal v))
  | .app f a =>
      .app (substituteStateVars stateVar varNames varExprs f)
           (substituteStateVars stateVar varNames varExprs a)
  | .lam n t b bi =>
      .lam n (substituteStateVars stateVar varNames varExprs t)
             (substituteStateVars stateVar varNames varExprs b) bi
  | .forallE n t b bi =>
      .forallE n (substituteStateVars stateVar varNames varExprs t)
                 (substituteStateVars stateVar varNames varExprs b) bi
  | .letE n t v b d =>
      .letE n (substituteStateVars stateVar varNames varExprs t)
             (substituteStateVars stateVar varNames varExprs v)
             (substituteStateVars stateVar varNames varExprs b) d
  | .mdata m b => .mdata m (substituteStateVars stateVar varNames varExprs b)
  | _ => e

/-- Introduce `n` fresh local `Int` constants and pass them to `k`. -/
private def withLocalInts (names : Array Name) (k : Array Expr → MetaM Expr) : MetaM Expr :=
  let rec go (i : Nat) (acc : Array Expr) : MetaM Expr :=
    if i >= names.size then k acc
    else withLocalDecl names[i]! .default (mkConst ``Int) fun v => go (i + 1) (acc.push v)
  go 0 #[]

/-- Recursively walk `e`, replacing every `∀ (s : State), body` with the
    corresponding `∀ v₁ … vₙ : Int, body[s "xᵢ" ↦ vᵢ]`. -/
private partial def replaceStateInExpr (e : Expr) : MetaM Expr := do
  match e with
  | .forallE n t body bi =>
    if ← isStateType t then
      -- Open the binder and collect which variables are read
      withLocalDecl n bi t fun s => do
        let bodyOpen := body.instantiate1 s
        let vars := (collectStateVarsFree s bodyOpen).toList.eraseDups.toArray
        -- Recursively transform nested State foralls inside the body first
        let bodyTransformed ← replaceStateInExpr bodyOpen
        -- Re-abstract over fresh Int vars, substituting s "xi" → vi
        withLocalInts (vars.map Name.mkSimple) fun vs => do
          let bodySubst := substituteStateVars s vars vs bodyTransformed
          mkForallFVars vs bodySubst
    else
      -- Regular forall: just recurse into body
      withLocalDecl n bi t fun x => do
        let bodyOpen := body.instantiate1 x
        let bodyTransformed ← replaceStateInExpr bodyOpen
        mkForallFVars #[x] bodyTransformed
  | .lam n t body bi =>
      withLocalDecl n bi t fun x => do
        let bodyOpen := body.instantiate1 x
        let bodyTransformed ← replaceStateInExpr bodyOpen
        mkLambdaFVars #[x] bodyTransformed
  | .app f a =>
      return .app (← replaceStateInExpr f) (← replaceStateInExpr a)
  | _ => return e

/-- Collect binder names from a chain of `∀ (v : Int), ...` foralls. -/
private partial def collectForallIntVarNames (e : Expr) : List String :=
  match e with
  | .forallE n t body _ =>
    if t.isConst && t.constName! == ``Int then
      n.toString :: collectForallIntVarNames body
    else []
  | _ => []

/-- Given `h : newType`, construct a proof of `oldType` where `oldType` and
    `newType` differ only in that each `∀ (s : State), body[s "xi"]` in `oldType`
    has become `∀ (v1 … vn : Int), body[vi]` in `newType`.

    Proof strategy:
    * `∃` — `Exists.elim` on `h`, re-wrap with `Exists.intro` using same witness
    * `∧` — project each component and recurse
    * `∀ s : State, …` — build `fun s => h (s "x1") … (s "xn")` (works by
      definitional equality since `body[vi := s "xi"]` is `body[s "xi"]`)
    * fallback — return `h` directly (types should be defeq) -/
private partial def proveOldFromNew (h : Expr) (oldType newType : Expr) : MetaM Expr := do
  let oldW ← whnf oldType
  let newW ← whnf newType
  -- Exists case
  if oldW.isAppOfArity ``Exists 2 && newW.isAppOfArity ``Exists 2 then
    let domTy := oldW.appFn!.appArg!
    let oldFn := oldW.appArg!
    let newFn := newW.appArg!
    withLocalDecl `w .default domTy fun w => do
      let oldBodyW ← whnf (oldFn.beta #[w])
      let newBodyW ← whnf (newFn.beta #[w])
      withLocalDecl `hw .default newBodyW fun hw => do
        let bodyProof ← proveOldFromNew hw oldBodyW newBodyW
        -- supply oldFn explicitly so Lean doesn't need higher-order unification for ?p
        let introExpr ← mkAppOptM ``Exists.intro #[domTy, oldFn, w, bodyProof]
        let k ← mkLambdaFVars #[w, hw] introExpr
        mkAppOptM ``Exists.elim #[domTy, newFn, oldType, h, k]
  -- And case
  else if oldW.isAppOfArity ``And 2 && newW.isAppOfArity ``And 2 then
    let oldL := oldW.appFn!.appArg!
    let oldR := oldW.appArg!
    let newL := newW.appFn!.appArg!
    let newR := newW.appArg!
    let hL := Expr.proj ``And 0 h
    let hR := Expr.proj ``And 1 h
    let proofL ← proveOldFromNew hL oldL newL
    let proofR ← proveOldFromNew hR oldR newR
    mkAppM ``And.intro #[proofL, proofR]
  -- ∀ s : State, … from ∀ v1 … vn : Int, …
  else if oldW.isForall && (← isStateType oldW.bindingDomain!) then
    let stateType := oldW.bindingDomain!
    let varNames  := collectForallIntVarNames newW
    withLocalDecl `s .default stateType fun s => do
      let args := varNames.toArray.map (fun xi => mkApp s (mkStrLit xi))
      mkLambdaFVars #[s] (mkAppN h args)
  -- Fallback: h itself (types are definitionally equal)
  else return h

elab "replace_state" : tactic => do
  let goal   ← getMainGoal
  let target ← goal.getType
  let newTarget ← replaceStateInExpr target
  if target == newTarget then pure ()
  else
    -- Fresh metavar for the new goal
    let newGoalMVar ← mkFreshExprMVar newTarget
    -- Prove old target from the new goal's proof
    let proof ← proveOldFromNew newGoalMVar target newTarget
    goal.assign proof
    replaceMainGoal [newGoalMVar.mvarId!]

macro "reify" : tactic => `(tactic| (simp_scopes; replace_state))
