import Lean

syntax (name := combine_n) "combine_n " num : tactic

open Lean Meta Elab Tactic in
@[tactic combine_n] def evalCombineN : Tactic := fun stx => do
  let n := stx[1].toNat

  let goals ← getGoals
  if goals.length < n then throwError "Not enough goals."

  let toCombine := goals.take n
  let rest := goals.drop n

  let types ← toCombine.mapM (fun g => g.getType)

  let newTarget ← types.take (n - 1) |>.foldrM
    (fun (t : Expr) (acc : Expr) => mkAppM ``And #[t, acc])
    (types[(n - 1)]!)

  let firstGoal := toCombine.head!
  let mvarDecl ← firstGoal.getDecl

  let mvarNew ← mkFreshExprMVarAt
    mvarDecl.lctx
    mvarDecl.localInstances
    newTarget
    MetavarKind.natural
    `combined_goal

  let mut currentProof := mvarNew
  for i in [:n-1] do
    let g := toCombine[i]!
    g.assign (← mkAppM ``And.left #[currentProof])
    currentProof ← mkAppM ``And.right #[currentProof]
  toCombine[(n-1)]!.assign currentProof

  setGoals (mvarNew.mvarId! :: rest)


theorem and_exists_hoist {α : Sort u} {P : Prop} {Q : α → Prop} :
    (P ∧ (∃ x, Q x)) ↔ ∃ x, P ∧ Q x := by
  constructor
  · intro h
    rcases h with ⟨hP, ⟨x, hQ⟩⟩
    exact ⟨x, hP, hQ⟩
  · intro h
    rcases h with ⟨x, hP, hQ⟩
    exact ⟨hP, ⟨x, hQ⟩⟩

theorem exists_and_hoist {α : Sort u} {P : α → Prop} {Q : Prop} :
    ((∃ x, P x) ∧ Q) ↔ ∃ x, P x ∧ Q := by
  constructor
  · intro h
    rcases h with ⟨⟨x, hP⟩, hQ⟩
    exact ⟨x, hP, hQ⟩
  · intro h
    rcases h with ⟨x, hP, hQ⟩
    exact ⟨⟨x, hP⟩, hQ⟩

theorem reorder_exists {P : α → β → Prop}
  : (∀ x : α, ∃ y: β, P x y) ↔ (∃ y : α → β, ∀ x : α, P x (y x)) := by
  apply Iff.intro
  · intro h
    classical
    refine ⟨fun x => Classical.choose (h x), ?_⟩
    intro x
    exact Classical.choose_spec (h x)
  · intro h x
    rcases h with ⟨wit, h⟩
    exists wit x
    apply_assumption

open Lean Elab Tactic Meta in
private partial def collectExistsNamesHoist (e : Expr) : MetaM (List Name) := do
  let e ← whnfR e
  match e with
  | .forallE n α body bi =>
      withLocalDecl n bi α fun x => collectExistsNamesHoist (body.instantiate1 x)
  | _ =>
      if e.isAppOfArity ``Exists 2 then
        let α := e.appFn!.appArg!
        let p := e.appArg!
        withLocalDecl p.bindingName! p.bindingInfo! α fun x => do
          let rest ← collectExistsNamesHoist (p.beta #[x])
          pure (p.bindingName! :: rest)
      else if e.isAppOfArity ``And 2 then
        let l := e.appFn!.appArg!
        let r := e.appArg!
        return (← collectExistsNamesHoist r) ++ (← collectExistsNamesHoist l)
      else
        pure []

open Lean Elab Tactic Meta in
private partial def collectTopForallNames (e : Expr) : MetaM (List Name) := do
  let e ← whnfR e
  match e with
  | .forallE n α body bi =>
      withLocalDecl n bi α fun x => do
        pure (n :: (← collectTopForallNames (body.instantiate1 x)))
  | _ => pure []

open Lean Elab Tactic Meta in
private partial def renameTopExists (e : Expr) (names : List Name) : MetaM Expr := do
  match names with
  | [] => pure e
  | n :: ns =>
    let e ← whnfR e
    if e.isAppOfArity ``Exists 2 then
      let α := e.appFn!.appArg!
      let p := e.appArg!
      withLocalDecl n .default α fun x => do
        let body := p.beta #[x]
        let body' ← renameTopExists body ns
        let p' ← mkLambdaFVars #[x] body'
        mkAppM ``Exists #[p']
    else
      pure e

open Lean Elab Tactic Meta in
private partial def renameTopForalls (e : Expr) (names : List Name) : MetaM Expr := do
  match names with
  | [] => pure e
  | n :: ns =>
    let e ← whnfR e
    match e with
    | .forallE _ α body bi =>
        withLocalDecl n bi α fun x => do
          let body' ← renameTopForalls (body.instantiate1 x) ns
          mkForallFVars #[x] body'
    | _ => pure e

open Lean Elab Tactic Meta in
private partial def renameTopExistsThenForalls
    (e : Expr) (exNames : List Name) (forallNames : List Name) : MetaM Expr := do
  match exNames with
  | [] => renameTopForalls e forallNames
  | n :: ns =>
    let e ← whnfR e
    if e.isAppOfArity ``Exists 2 then
      let α := e.appFn!.appArg!
      let p := e.appArg!
      withLocalDecl n .default α fun x => do
        let body := p.beta #[x]
        let body' ← renameTopExistsThenForalls body ns forallNames
        let p' ← mkLambdaFVars #[x] body'
        mkAppM ``Exists #[p']
    else
      renameTopForalls e forallNames

open Lean Elab Tactic Meta in
elab "hoist_exists" : tactic => do
  let g ← getMainGoal
  let targetBefore ← g.getType
  let exNames ← collectExistsNamesHoist targetBefore
  let forallNames ← collectTopForallNames targetBefore
  evalTactic (← `(tactic|
    repeat simp only [and_assoc, and_exists_hoist, exists_and_hoist, reorder_exists]
  ))
  let g' ← getMainGoal
  let targetAfter ← g'.getType
  let renamed ← renameTopExistsThenForalls targetAfter exNames forallNames
  let newGoal ← g'.replaceTargetDefEq renamed
  replaceMainGoal [newGoal]

-- `under_exists => tacs`
-- Runs `tacs` with the existential witness replaced by a fresh metavar.
-- If all subgoals are solved, the witness is determined and we're done.
-- If subgoals remain, they are combined with ∧, abstracted over the witness,
-- and re-wrapped as a single `∃ k, G1(k) ∧ ... ∧ Gn(k)` goal.
syntax (name := underExists) "under_exists" "=>" tacticSeq : tactic

open Lean Meta Elab Tactic in
@[tactic underExists] def evalUnderExists : Tactic := fun stx => do
  let tacs := stx[2]
  let g ← getMainGoal
  let target ← whnfR (← g.getType)
  unless target.isAppOfArity ``Exists 2 do
    throwError "under_exists: goal must be an existential (∃ ...)"
  let α     := target.appFn!.appArg!
  let p     := target.appArg!
  let bName := p.bindingName!
  -- Fresh metavar for the witness; instantiate the body with it
  let witMVar  ← mkFreshExprMVar α (kind := .natural) (userName := bName)
  let body     := p.beta #[witMVar]
  -- Fresh metavar for the body proof; close original goal via Exists.intro
  let bodyMVar ← mkFreshExprMVar body (kind := .natural)
  g.assign (← mkAppOptM ``Exists.intro #[α, p, witMVar, bodyMVar])
  -- Run user tactics on the body goal
  setGoals [bodyMVar.mvarId!]
  evalTactic tacs
  let remaining ← getGoals
  if remaining.isEmpty then return
  -- If the witness was already determined, just expose remaining goals
  let witExpr ← instantiateMVars witMVar
  if !witExpr.isMVar then
    setGoals remaining
    return
  -- Witness still undetermined: collect goal types and build a conjunction
  let types ← remaining.mapM fun goal => do instantiateMVars (← goal.getType)
  let conjType ← match types with
    | []  => throwError "under_exists: impossible empty remaining"
    | [t] => pure t
    | _   => types.dropLast.foldrM (fun t acc => mkAppM ``And #[t, acc]) types.getLast!
  -- Abstract the witness metavar to form the ∃ predicate
  let predBody  ← kabstract conjType witMVar (occs := .all)
  let pred       := mkLambda bName .default α predBody
  let newTarget ← mkAppM ``Exists #[pred]
  -- Create the new wrapped goal in the context of the first remaining goal
  let decl      ← remaining.head!.getDecl
  let newGoalMVar ← mkFreshExprMVarAt decl.lctx decl.localInstances newTarget
  -- Use Classical.choose to extract witness and proof from the new goal
  let chosen     ← mkAppOptM ``Classical.choose      #[α, pred, newGoalMVar]
  let chosenSpec ← mkAppOptM ``Classical.choose_spec #[α, pred, newGoalMVar]
  -- Assign the witness metavar so all remaining goals become concrete
  witMVar.mvarId!.assign chosen
  -- Distribute the conjunction proof back into the individual remaining goals
  let mut proof := chosenSpec
  for i in [: remaining.length - 1] do
    remaining[i]!.assign (← mkAppM ``And.left #[proof])
    proof ← mkAppM ``And.right #[proof]
  remaining.getLast!.assign proof
  setGoals [newGoalMVar.mvarId!]
