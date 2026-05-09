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
-- Runs `tacs` with all existential witnesses replaced by fresh metavars.
-- If all subgoals are solved, the witnesses are determined and we're done.
-- If subgoals remain, they are combined with ∧, abstracted over any
-- undetermined witnesses, and re-wrapped as nested ∃ goals.
syntax (name := underExists) "under_exists" "=>" tacticSeq : tactic

open Lean Meta Elab Tactic in
@[tactic underExists] def evalUnderExists : Tactic := fun stx => do
  let tacs := stx[2]
  let g ← getMainGoal
  -- Peel all top-level ∃ binders
  let mut target ← whnfR (← g.getType)
  let mut αs   : Array Expr := #[]
  let mut ps   : Array Expr := #[]  -- predicate lambda for each ∃
  let mut wits : Array Expr := #[]  -- fresh witness MVars
  while target.isAppOfArity ``Exists 2 do
    let α := target.appFn!.appArg!
    let p := target.appArg!
    let witMVar ← mkFreshExprMVar α (kind := .natural) (userName := p.bindingName!)
    αs   := αs.push α
    ps   := ps.push p
    wits := wits.push witMVar
    target ← whnfR (p.beta #[witMVar])
  if αs.isEmpty then
    throwError "under_exists: goal must be an existential (∃ ...)"
  -- Create body metavar and close the original goal via nested Exists.intro
  let bodyMVar ← mkFreshExprMVar target (kind := .natural)
  let mut proof : Expr := bodyMVar
  for i in (List.range αs.size).reverse do
    proof ← mkAppOptM ``Exists.intro #[αs[i]!, ps[i]!, wits[i]!, proof]
  g.assign proof
  -- Run user tactics on the fully-instantiated body
  setGoals [bodyMVar.mvarId!]
  evalTactic tacs
  let remaining ← getGoals
  if remaining.isEmpty then return
  -- Check which witnesses are still undetermined
  let witExprs ← wits.mapM instantiateMVars
  if witExprs.all (fun w => !w.isMVar) then
    setGoals remaining
    return
  -- Separate Prop goals (to wrap) from non-Prop goals (synthesis mvars from
  -- tactics like `rw` that create type-valued goals we must not put in ∧)
  let (propGoals, otherGoals) ← remaining.partitionM fun goal => do
    isProp (← instantiateMVars (← goal.getType))
  -- Build conjunction of Prop goal types
  let types ← propGoals.mapM fun goal => do instantiateMVars (← goal.getType)
  let conjType ← match types with
    | []  => throwError "under_exists: impossible empty remaining"
    | [t] => pure t
    | _   => types.dropLast.foldrM (fun t acc => mkAppM ``And #[t, acc]) types.getLast!
  -- Re-wrap with ∃ for each undetermined witness (innermost → outermost)
  -- and collect undetermined indices in outermost-first order
  let mut undetermIdx : List Nat := []
  let mut newTarget := conjType
  for i in (List.range αs.size).reverse do
    if witExprs[i]!.isMVar then
      undetermIdx := i :: undetermIdx
      let predBody ← kabstract newTarget witExprs[i]! (occs := .all)
      let pred := mkLambda ps[i]!.bindingName! .default αs[i]! predBody
      newTarget ← mkAppM ``Exists #[pred]
  -- Create the new wrapped goal in the context of the first Prop goal
  let decl ← propGoals.head!.getDecl
  let newGoalMVar ← mkFreshExprMVarAt decl.lctx decl.localInstances newTarget
  -- Extract witnesses via Classical.choose chain (outermost first)
  let mut specProof : Expr := newGoalMVar
  for i in undetermIdx do
    let chosen     ← mkAppOptM ``Classical.choose      #[αs[i]!, none, specProof]
    let chosenSpec ← mkAppOptM ``Classical.choose_spec #[αs[i]!, none, specProof]
    wits[i]!.mvarId!.assign chosen
    specProof := chosenSpec
  -- Distribute the conjunction proof back into the individual Prop goals
  let mut conjProof := specProof
  for i in [: propGoals.length - 1] do
    propGoals[i]!.assign (← mkAppM ``And.left #[conjProof])
    conjProof ← mkAppM ``And.right #[conjProof]
  propGoals.getLast!.assign conjProof
  -- Re-expose the new wrapped goal plus any non-Prop synthesis goals
  setGoals (newGoalMVar.mvarId! :: otherGoals)

-- `under_exists1 => tacs`
-- Runs `tacs` with the top-level existential witness replaced by a fresh metavar.
-- If all subgoals are solved, the witness is determined and we're done.
-- If subgoals remain, they are combined with ∧, abstracted over the
-- undetermined witness, and re-wrapped as a single ∃ goal.
syntax (name := underExists1) "under_exists1" "=>" tacticSeq : tactic

open Lean Meta Elab Tactic in
@[tactic underExists1] def evalUnderExists1 : Tactic := fun stx => do
  let tacs := stx[2]
  let g ← getMainGoal
  -- Peel the top-level ∃ binder
  let mut target ← whnfR (← g.getType)
  if !target.isAppOfArity ``Exists 2 then
    throwError "under_exists1: goal must be an existential (∃ ...)"
  let α := target.appFn!.appArg!
  let p := target.appArg!
  let witMVar ← mkFreshExprMVar α (kind := .natural) (userName := p.bindingName!)
  let αs   : Array Expr := #[α]
  let ps   : Array Expr := #[p]  -- predicate lambda for the ∃
  let wits : Array Expr := #[witMVar]  -- fresh witness MVar
  target ← whnfR (p.beta #[witMVar])
  -- Create body metavar and close the original goal via Exists.intro
  let bodyMVar ← mkFreshExprMVar target (kind := .natural)
  let proof ← mkAppOptM ``Exists.intro #[α, p, witMVar, bodyMVar]
  g.assign proof
  -- Run user tactics on the fully-instantiated body
  setGoals [bodyMVar.mvarId!]
  evalTactic tacs
  let remaining ← getGoals
  if remaining.isEmpty then return
  -- Check if the witness is still undetermined
  let witExpr ← instantiateMVars witMVar
  if !witExpr.isMVar then
    setGoals remaining
    return
  -- Separate Prop goals (to wrap) from non-Prop goals (synthesis mvars from
  -- tactics like `rw` that create type-valued goals we must not put in ∧)
  let (propGoals, otherGoals) ← remaining.partitionM fun goal => do
    isProp (← instantiateMVars (← goal.getType))
  -- Build conjunction of Prop goal types
  let types ← propGoals.mapM fun goal => do instantiateMVars (← goal.getType)
  let conjType ← match types with
    | []  => throwError "under_exists1: impossible empty remaining"
    | [t] => pure t
    | _   => types.dropLast.foldrM (fun t acc => mkAppM ``And #[t, acc]) types.getLast!
  -- Re-wrap with ∃ for the undetermined witness
  let predBody ← kabstract conjType witExpr (occs := .all)
  let pred := mkLambda p.bindingName! .default α predBody
  let newTarget ← mkAppM ``Exists #[pred]
  -- Create the new wrapped goal in the context of the first Prop goal
  let decl ← propGoals.head!.getDecl
  let newGoalMVar ← mkFreshExprMVarAt decl.lctx decl.localInstances newTarget
  -- Extract witness via Classical.choose
  let chosen     ← mkAppOptM ``Classical.choose      #[α, none, newGoalMVar]
  let chosenSpec ← mkAppOptM ``Classical.choose_spec #[α, none, newGoalMVar]
  witMVar.mvarId!.assign chosen
  let specProof := chosenSpec
  -- Distribute the conjunction proof back into the individual Prop goals
  let mut conjProof := specProof
  for i in [: propGoals.length - 1] do
    propGoals[i]!.assign (← mkAppM ``And.left #[conjProof])
    conjProof ← mkAppM ``And.right #[conjProof]
  propGoals.getLast!.assign conjProof
  -- Re-expose the new wrapped goal plus any non-Prop synthesis goals
  setGoals (newGoalMVar.mvarId! :: otherGoals)
