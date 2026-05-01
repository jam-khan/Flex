import Lean
open Lean Elab Tactic Meta

/--
  `name_witness body` introduces a local `let`-binding for `body`
  named after the outermost `∃ κ : T, …` binder in the current goal,
  then closes that `∃` with it. Both the witness type and the name
  are read off the goal — you only supply `body`.
  The goal continues to display the binder name (folded), not `body`.
  Chain multiple times for nested `∃`s.
-/
syntax (name := nameWitness) "name_witness " term : tactic

elab_rules : tactic
  | `(tactic| name_witness $body:term) => withMainContext do
      let goalType ← whnf (← getMainTarget)
      unless goalType.isAppOfArity ``Exists 2 do
        throwError "name_witness: goal is not an ∃, got{indentExpr goalType}"
      let α := goalType.appFn!.appArg!
      let p := goalType.appArg!
      let kName := match p with
        | .lam n _ _ _ => n
        | _ => `k
      let αStx ← PrettyPrinter.delab α
      let kIdent := mkIdent kName
      evalTactic (← `(tactic| (let $kIdent : $αStx := $body; exists $kIdent)))

/--
  `lazy_unfold k₁ k₂ …` traverses the goal and every hypothesis,
  recursing under `∀`, `∃`, `∧`, `→`, etc., and replaces every
  application of the listed local `let`-bindings with their
  beta-reduced bodies — but only at this proof position. Anywhere
  else in the proof tree the lets stay folded.
-/
syntax (name := lazyUnfold) "lazy_unfold " (colGt ident)+ : tactic

/-- Manual traversal that, when it encounters an application whose head
is one of the `targets` let-fvars, replaces it with the let-value
beta-applied to the spine arguments. Recurses into the result so nested
occurrences also unfold. -/
private partial def lazyUnfoldExpr (targets : Array FVarId) (e : Expr) : MetaM Expr := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .fvar fvarId := f then
      if targets.contains fvarId then
        if let some val := (← fvarId.getDecl).value? then
          let args ← args.mapM (lazyUnfoldExpr targets)
          return ← lazyUnfoldExpr targets (val.beta args)
    let f ← lazyUnfoldExpr targets f
    let args ← args.mapM (lazyUnfoldExpr targets)
    return mkAppN f args
  | .forallE n d b bi =>
    let d ← lazyUnfoldExpr targets d
    withLocalDecl n bi d fun x => do
      let b ← lazyUnfoldExpr targets (b.instantiate1 x)
      mkForallFVars #[x] b
  | .lam n d b bi =>
    let d ← lazyUnfoldExpr targets d
    withLocalDecl n bi d fun x => do
      let b ← lazyUnfoldExpr targets (b.instantiate1 x)
      mkLambdaFVars #[x] b
  | .letE n t v b _ =>
    let t ← lazyUnfoldExpr targets t
    let v ← lazyUnfoldExpr targets v
    withLetDecl n t v fun x => do
      let b ← lazyUnfoldExpr targets (b.instantiate1 x)
      mkLetFVars #[x] b
  | .mdata _ b   => return e.updateMData! (← lazyUnfoldExpr targets b)
  | .proj _ _ b  => return e.updateProj! (← lazyUnfoldExpr targets b)
  | _            => return e

elab_rules : tactic
  | `(tactic| lazy_unfold $ks:ident*) => withMainContext do
      let mut targets : Array FVarId := #[]
      for k in ks do
        let term ← Tactic.elabTerm k none
        let .fvar fvarId := term.consumeMData
          | throwError "lazy_unfold: '{k}' is not a local hypothesis"
        let decl ← fvarId.getDecl
        unless decl.isLet do
          throwError "lazy_unfold: '{k}' is not a let-binding"
        targets := targets.push fvarId

      let mut goal ← getMainGoal
      let lctx ← getLCtx
      for hyp in lctx do
        if hyp.isImplementationDetail then continue
        if targets.contains hyp.fvarId then continue
        let newType ← lazyUnfoldExpr targets hyp.type
        if newType != hyp.type then
          goal ← goal.changeLocalDecl hyp.fvarId newType
      let goalType ← instantiateMVars (← goal.getType)
      let newGoalType ← lazyUnfoldExpr targets goalType
      if newGoalType != goalType then
        goal ← goal.change newGoalType
      replaceMainGoal [goal]

def ex6 : Prop :=
  ∃ κ1 : Int → Int → Prop,
  ∃ κ2 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν)

theorem ex6Proof : ex6 := by
  unfold ex6
  name_witness fun z0 z1 => ∃ ν, ν = z1 + 1 ∧ z0 = ν
  name_witness fun z0 z1 => ∃ ν, ν = z1 - 1 ∧ z0 = ν
  lazy_unfold κ1
  lazy_unfold κ2
  sorry
