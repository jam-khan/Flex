import Lean

open Lean Elab Tactic Meta

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

private partial def collectExistsNames (e : Expr) : MetaM (List Name) := do
  let e ← whnfR e
  if e.isAppOfArity ``Exists 2 then
    let α := e.appFn!.appArg!
    let p := e.appArg!
    withLocalDecl p.bindingName! p.bindingInfo! α fun x => do
      let rest ← collectExistsNames (p.beta #[x])
      pure (p.bindingName! :: rest)
  else if e.isAppOfArity ``And 2 then
    let l := e.appFn!.appArg!
    let r := e.appArg!
    return (← collectExistsNames l) ++ (← collectExistsNames r)
  else
    pure []

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

elab "hoist_while_chc_exists" : tactic =>
  do
    let g ← getMainGoal
    let targetBefore ← g.getType
    let exNames ← collectExistsNames targetBefore
    evalTactic (← `(tactic|
      repeat simp only [and_assoc, and_exists_hoist, exists_and_hoist]))
    let g' ← getMainGoal
    let targetAfter ← g'.getType
    let renamed ← renameTopExists targetAfter exNames
    let newGoal ← g'.replaceTargetDefEq renamed
    replaceMainGoal [newGoal]
