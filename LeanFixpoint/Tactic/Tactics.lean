import Lean

open Lean Elab Tactic Meta in
private partial def zapCore : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => return ()
  | g :: restGoals =>
    let ty ← whnfR (← g.getType)
    if ty.isForall then
      -- goal is `p → q` or `∀ x, P x`: introduce
      evalTactic (← `(tactic| intro _))
      zapCore
    else if ty.isAppOfArity ``And 2 then
      -- goal is `p ∧ q`: split into two subgoals
      evalTactic (← `(tactic| and_intros))
      zapCore
    else
      -- Leaf goal: try grind, then rfl; if either closes the goal, continue with siblings.
      -- If both fail, skip this goal, process siblings, then restore it.
      let leafOk ← try evalTactic (← `(tactic| grind)); pure true catch _ =>
                   try evalTactic (← `(tactic| rfl));   pure true catch _ => pure false
      if leafOk then
        zapCore  -- g is closed; carry on with restGoals
      else
        setGoals restGoals
        zapCore
        let remaining ← getGoals
        setGoals (g :: remaining)

/-- decomposes implications (`p → q`) and conjunctions (`p ∧ q`)
    recursively via `intro` and `and_intros`, and applies `grind`
    (falling back to `rfl`) at leaf goals. -/
elab "zap" : tactic => zapCore


-- Build `fun x₁ x₂ … xₙ => True` for a type of the form `t₁ → t₂ → … → tₙ → Prop`.
open Lean Elab Tactic Meta in
private partial def mkTrueWitness (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isForall then
    let body ← mkTrueWitness ty.bindingBody!
    return .lam ty.bindingName! ty.bindingDomain! body ty.bindingInfo!
  else
    return mkConst ``True

open Lean Elab Tactic Meta in
private partial def trivialkCore : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => return ()
  | g :: _ =>
    let goalType ← whnfR (← g.getType)
    unless goalType.isAppOfArity ``Exists 2 do return ()
    let varType := goalType.appFn!.appArg!
    let varTypeWhnf ← whnfR varType
    unless varTypeWhnf.isForall do return ()
    let witness ← mkTrueWitness varType
    -- Extract the predicate directly from the goal type instead of
    -- letting mkAppM infer it, then build the Exists.intro application manually
    let pred := goalType.appArg!
    let u ← getLevel varType
    let newGoals ← g.apply (mkApp3 (mkConst ``Exists.intro [u]) varType pred witness)
    -- let newGoals ← g.apply (mkApp3 (mkConst ``Exists.intro) varType pred witness)
    setGoals newGoals
    trivialkCore


/-- For a goal `∃ f : t₁ → t₂ → … → tₙ → Prop, P f` (n ≥ 1),
    provides `fun x₁ x₂ … xₙ => True` as the witness and recurses
    until the top-level goal is no longer such an existential. -/
elab "trivialk" : tactic => trivialkCore

/-- Sequences `trivialk`, `simp`, and `zap`. -/
macro "elimT" : tactic => `(tactic| (trivialk; simp; zap))

open Lean Elab Tactic Meta in
private partial def splitAndsAllCore : TacticM Unit := do
  let ctx ← getLCtx
  for decl in ctx do
    let ty ← whnfR decl.type
    if ty.isAppOf ``And then
      let lhs    := ty.appFn!.appArg!
      let rhs    := ty.appArg!
      let fvar   := mkFVar decl.fvarId
      let h1Name := decl.userName.appendAfter "₁"
      let h2Name := decl.userName.appendAfter "₂"
      let h1Val  ← mkAppM ``And.left  #[fvar]
      let h2Val  ← mkAppM ``And.right #[fvar]
      let goal   ← getMainGoal
      let g1     ← goal.assert h1Name lhs h1Val
      let g2     ← g1.assert   h2Name rhs h2Val
      let g3     ← g2.tryClearMany #[decl.fvarId]
      replaceMainGoal [g3]
      splitAndsAllCore
      return

elab "split_ands_all" : tactic => splitAndsAllCore

open Lean Elab Tactic Meta in
partial def splitHypOrsOnGoal (g : MVarId) : TacticM (List MVarId) := do
  MVarId.withContext g do
    let mut didSplit := false
    for localDecl in (← getLCtx) do
      setGoals [g]
      let type ← instantiateMVars localDecl.type
      if localDecl.isAuxDecl || !type.isAppOf ``Or then
        continue
      let hName := mkIdent localDecl.userName
      -- let hName := mkIdent (← mkFreshId)
      evalTactic (← `(tactic| cases $hName:ident))
      didSplit := true
      break

    if didSplit then
      let gs ← getGoals
      let mut out := []
      for g' in gs do
        let gs' ← splitHypOrsOnGoal g'
        out := out ++ gs'
      return out
    else
      return [g]

open Lean Elab Tactic Meta in
partial def split_hyp_ors : TacticM Unit := do
  let goals ← getGoals
  let new_goals ← splitHypOrsOnGoal (← getMainGoal)
  if new_goals.all goals.contains then
    throwError "no dijunctions found in hypotheses"
  else
    setGoals new_goals


elab "split_hyp_ors" : tactic =>
  split_hyp_ors

-- ---------------------------------------------------------------------------
-- zapTrue: simplify a goal by replacing grind-provable conjuncts with True
-- ---------------------------------------------------------------------------

-- Return type for zapTrueExpr: (simplified proposition, backward proof)
-- Using a plain Prod to avoid anonymous-constructor elaboration quirks.
private abbrev ZTR := Lean.Expr × Lean.Expr

open Lean Elab Tactic Meta in
/-- Try to prove `e` using `grind` in a side goal.
    Returns the proof expression if successful, `none` otherwise.
    The current goal list is left unchanged. -/
private def tryGrindProve (e : Expr) : TacticM (Option Expr) := do
  let mvar      ← mkFreshExprMVar e
  let saved     ← saveState
  let prevGoals ← getGoals
  setGoals [mvar.mvarId!]
  let ok ←
    try
      evalTactic (← `(tactic| grind))
      let remaining ← getGoals
      pure remaining.isEmpty
    catch _ => pure false
  if ok then
    let proof ← instantiateMVars mvar
    setGoals prevGoals
    return some proof
  else
    restoreState saved
    return none

open Lean Elab Tactic Meta in
/-- Recurse under `∃` and `∧`, replacing `grind`-provable leaf propositions
    with `True`. Returns `(simplified, backward)` where `backward` proves
    `simplified → original`. -/
private partial def zapTrueExpr (e : Expr) : TacticM ZTR := do
  let e ← whnfR e
  if e.isAppOfArity ``Exists 2 then
    let α := e.appFn!.appArg!
    let P := e.appArg!
    -- Recurse under the binder with a fresh free variable, preserving the original name
    let (P', implFun) ← withLocalDecl P.bindingName! .default α fun x => do
      let (body', toOrig) ← zapTrueExpr (P.beta #[x])
      -- P' = fun x => simplified body
      let P'      ← mkLambdaFVars #[x] body'
      -- implFun : ∀ x, P' x → P x  (used to build the backward proof)
      let implFun ← withLocalDecl `hx .default body' fun hx =>
        mkLambdaFVars #[x, hx] (mkApp toOrig hx)
      return (P', implFun)
    -- simplified : ∃ x, P' x  (α is implicit in Exists, inferred from P')
    let simplified ← mkAppM ``Exists #[P']
    -- backward : (∃ x, P' x) → ∃ x, P x
    let backward   ← mkAppM ``Exists.imp #[implFun]
    return (simplified, backward)

  else if e.isAppOfArity ``And 2 then
    let p := e.appFn!.appArg!
    let q := e.appArg!
    let (p', backP) ← zapTrueExpr p
    let (q', backQ) ← zapTrueExpr q
    -- simplified : p' ∧ q'
    let simplified ← mkAppM ``And #[p', q']
    -- backward : p' ∧ q' → p ∧ q
    let backward   ← mkAppM ``And.imp #[backP, backQ]
    return (simplified, backward)

  else if e.isForall then
    -- goal is `∀ x : α, P x` (or `p → q`): recurse under the binder
    let α := e.bindingDomain!
    let (simplified, backward) ← withLocalDecl e.bindingName! e.bindingInfo! α fun x => do
      let (body', toOrig) ← zapTrueExpr (e.bindingBody!.instantiate1 x)
      if body' == mkConst ``True then
        -- The body fully simplified to True; collapse the whole forall to True.
        -- backward : True → ∀ x : α, original_body  =  fun _ x => toOrig trivial
        let backward ← withLocalDecl `_h .default (mkConst ``True) fun _h =>
          mkLambdaFVars #[_h, x] (mkApp toOrig (mkConst ``True.intro))
        return (mkConst ``True, backward)
      else
        -- simplified : ∀ x, body'
        let simplified ← mkForallFVars #[x] body'
        -- backward : (∀ x, body') → ∀ x, original_body
        --          = fun h x => toOrig (h x)
        let backward ← withLocalDecl `h .default simplified fun h =>
          mkLambdaFVars #[h, x] (mkApp toOrig (mkApp h x))
        return (simplified, backward)
    return (simplified, backward)

  else
    -- Leaf: try grind
    match ← tryGrindProve e with
    | some proof =>
      -- Replace leaf with True; backward: fun _ => proof
      let backward ← withLocalDecl `_h .default (mkConst ``True) fun _h =>
        mkLambdaFVars #[_h] proof
      return (mkConst ``True, backward)
    | none =>
      -- Keep as-is; backward = identity
      let backward ← withLocalDecl `h .default e fun h =>
        mkLambdaFVars #[h] h
      return (e, backward)

open Lean Elab Tactic Meta in
/-- Simplify the current goal by recursing under `∃`, `∧`, and `∀` (/ `→`),
    discharging `grind`-provable leaves and replacing them with `True`,
    then cleaning up with `simp [and_true, true_and]`.

    Examples:
    · `⊢ ∃ x, x > 100 ∧ 4 > 2`          ↝  `⊢ ∃ x, x > 100`
    · `⊢ ∃ x, P x ∧ (Q x → Q x)`        ↝  `⊢ ∃ x, P x`
    · `⊢ ∀ x, P x ∧ 4 > 2`              ↝  `⊢ ∀ x, P x`
    · `⊢ ∀ x, (x > 0 → x > 0) ∧ Q x`   ↝  `⊢ ∀ x, Q x` -/
private def zapTrueCore : TacticM Unit := do
  let goal ← getMainGoal
  let ty   ← goal.getType
  let (ty', backward) ← zapTrueExpr ty
  -- Introduce a new goal with the simplified type.
  -- Close the original goal via: original ← backward (proof of simplified).
  let newGoal ← mkFreshExprMVar ty' (kind := .syntheticOpaque)
  goal.assign (mkApp backward newGoal)
  setGoals [newGoal.mvarId!]
  -- Erase any remaining `_ ∧ True` / `True ∧ _` residue (no-op if none)
  try evalTactic (← `(tactic| simp only [and_true, true_and])) catch _ => pure ()

elab "zapTrue" : tactic => zapTrueCore

open Lean Meta Elab Tactic in

partial def split_hyp_ands (n : Nat) :=
  withMainContext do
    let mut done := true
    for localDecl in (← getLCtx) do
      let type ← instantiateMVars localDecl.type
      if localDecl.isAuxDecl || !type.isAppOf `And then
        continue
      -- UGLY let lName := mkIdent (← mkFreshId)
      -- UGLY let rName := mkIdent (← mkFreshId)
      let lName := mkIdent (← Term.mkFreshBinderName)
      let rName := mkIdent (← Term.mkFreshBinderName)
      let hName := mkIdent localDecl.userName
      evalTactic (← `(tactic| rcases $hName:ident with ⟨$(lName):ident, $(rName):ident⟩))
      done := false
    if !done then
      split_hyp_ands (n + 1)
      pure ()
    else if n = 0 then
      throwError "no conjunctions found in hypotheses"

elab "split_hyp_ands" : tactic =>
  split_hyp_ands 0


open Lean Meta Elab Tactic in

partial def split_hyp_exists (n : Nat) :=
  withMainContext do
    let mut done := true
    for localDecl in (← getLCtx) do
      let type ← instantiateMVars localDecl.type
      if localDecl.isAuxDecl || !type.isAppOf `Exists then
        continue
      let hName := mkIdent localDecl.userName
      -- let lName := mkIdent (localDecl.userName.appendAfter "exi")
      -- let rName := mkIdent (localDecl.userName.appendAfter "body")
      -- let lName := mkIdent (← mkFreshId)
      -- let rName := mkIdent (← mkFreshId)
      let lName := mkIdent (← Term.mkFreshBinderName)
      let rName := mkIdent (← Term.mkFreshBinderName)
      evalTactic (← `(tactic| rcases $hName:ident with ⟨$(lName):ident, $(rName):ident⟩))
      done := false
    if !done then
      split_hyp_exists (n + 1)
      pure ()
    else if n = 0 then
      throwError "no existential statements found in hypotheses"

elab "split_hyp_exists" : tactic =>
  split_hyp_exists 0

macro "split_hyp_and_exist" : tactic =>
  `(tactic| repeat (first | split_hyp_ands | split_hyp_exists))

macro "split_hyps" : tactic =>
  `(tactic| repeat (any_goals (first | split_hyp_ands | split_hyp_ors | split_hyp_exists)))

syntax "flatten_and_solve_leafs" ("(" tactic ")") : tactic

macro_rules
  | `(tactic| flatten_and_solve_leafs ( $t:tactic )) =>
    `(tactic|
      repeat (any_goals
        first
          | (intro)
          | apply And.intro
          | $t:tactic
      )
    )


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
