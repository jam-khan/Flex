import LeanFixpoint.VCG.STLC.Soundness
import LeanFixpoint.Tactic

-- Applies `under_exists` once, then dispatches `check_sound` inside it.
-- `args` (optional, default empty) are extra lemmas passed to `simp`.
macro "make_horn_under_k" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    under_exists =>
      apply check_sound
      · repeat (first | unfold check | unfold synth)
        simp [$args,*]; rfl
      focus simp)

macro "make_horn_under_k" : tactic => `(tactic| make_horn_under_k [])

/-- Transform `⊢ ∃ κ : KEnv, P κ` into a goal where `κ` is replaced by
    `mkKEnv [...]`, with each listed predicate left as its own metavariable.

    Usage:
    ```
    intro_kenv [("k1", liftK1 ?k1), ("k2", liftK2 ?k2)]
    · exact fun v => v = 99        -- fills ?k1
    · exact fun x y => x = y      -- fills ?k2
    · <proof of P (mkKEnv [...])>
    ``` -/
macro "intro_kenv" "[" es:term,* "]" : tactic =>
  `(tactic| apply STLC.exists_kenv_curried [$es,*])

section KEnvTactic
open Lean Elab Tactic Meta

private partial def countCons (e : Expr) : Nat :=
  if e.isAppOfArity `List.cons 3 then 1 + countCons e.appArg! else 0

private partial def collectKVarUses
    (κFVar : FVarId) (e : Expr) (acc : List (String × Nat)) : List (String × Nat) :=
  match e with
  | .app (.app (.fvar fv) (.lit (.strVal name))) args =>
    let acc' := if fv == κFVar && !acc.any (fun p => p.1 == name)
                then (name, countCons args) :: acc else acc
    collectKVarUses κFVar args acc'
  | .app f a =>
    collectKVarUses κFVar a (collectKVarUses κFVar f acc)
  | .lam _ t b _ | .forallE _ t b _ =>
    collectKVarUses κFVar b (collectKVarUses κFVar t acc)
  | .letE _ t v b _ =>
    collectKVarUses κFVar b (collectKVarUses κFVar v (collectKVarUses κFVar t acc))
  | .mdata _ e => collectKVarUses κFVar e acc
  | _ => acc

-- `intro_kenv`: scans `∃ κ : KEnv, body` for every `κ "name" args` application,
-- infers arities, and rewrites the goal to
-- `∃ (k1 : Int → Prop) ..., body[κ := mkKEnv [...]]`.
elab "intro_kenv" : tactic => do
  let goal ← getMainGoal
  let goalType ← whnf (← goal.getType)
  unless goalType.isAppOfArity ``Exists 2 do
    throwError "intro_kenv: goal must be `∃ κ : KEnv, ...`"
  let bodyFn := goalType.appArg!
  let .lam _ kenvTy innerBody _ := bodyFn
    | throwError "intro_kenv: expected lambda in ∃ body"
  withLocalDecl `κ₀ .default kenvTy fun κ₀ => do
    let openBody ← instantiateMVars (innerBody.instantiate1 κ₀)
    let kvars := collectKVarUses κ₀.fvarId! openBody []
    if kvars.isEmpty then
      throwError "intro_kenv: no κ-applications found; use `intro_kenv [...]` explicitly"
    let kvarArr := kvars.toArray
    let intTy  := mkConst ``Int
    let propTy := mkSort Level.zero
    let kPredTy : Nat → Expr
      | 1 => .forallE `_ intTy propTy .default
      | _ => .forallE `_ intTy (.forallE `_ intTy propTy .default) .default

    -- Fresh MVars for each k-predicate
    let kMVars ← kvarArr.mapM fun (name, arity) =>
      mkFreshExprMVar (kPredTy arity) (kind := .natural) (userName := name.toName)

    -- Build list [("k1", liftK1 ?k1), ...] using direct mkApp (no AppBuilder checks)
    -- Get element type from a dummy element to avoid List.nil type inference issues
    let liftFn0 := mkConst (if kvarArr[0]!.2 == 1 then ``STLC.liftK1 else ``STLC.liftK2)
    let lifted0 := mkApp liftFn0 kMVars[0]!
    let liftedTy ← inferType lifted0          -- List (Σ b, b.interp) → Prop
    let strTy    := mkConst ``String
    -- Prod.mk.{u,v} takes universe indices where α : Type u.
    -- String : Type 0 → u = 0;  liftedTy : Type 0 → v = 0.
    let prodMkC  := mkConst ``Prod.mk [Level.zero, Level.zero]
    let elem0    := mkApp4 prodMkC strTy liftedTy (mkStrLit kvarArr[0]!.1) lifted0
    let elemTy   ← inferType elem0             -- KVar × (List ... → Prop)
    -- List.{u} (α : Type u): α : Type 0 → u = 0.
    let nilC  := mkConst ``List.nil  [Level.zero]
    let consC := mkConst ``List.cons [Level.zero]
    let mut kenvListExpr := mkApp nilC elemTy
    for i in (List.range kvarArr.size).reverse do
      let (name, arity) := kvarArr[i]!
      let liftFn := mkConst (if arity == 1 then ``STLC.liftK1 else ``STLC.liftK2)
      let liftedKi := mkApp liftFn kMVars[i]!
      let elem := mkApp4 prodMkC strTy liftedTy (mkStrLit name) liftedKi
      kenvListExpr := mkApp3 consC elemTy elem kenvListExpr
    let kenvExpr := mkApp (mkConst ``STLC.mkKEnv) kenvListExpr

    -- Fresh MVar for the body proof P(mkKEnv [...])
    let mainGoalType := innerBody.instantiate1 kenvExpr
    let mainGoalMVar ← mkFreshExprMVar mainGoalType (kind := .natural)

    -- Compute the universe level of kenvTy (needed for Exists.intro level arg)
    let kenvLvl : Level ← do
      match ← whnf (← inferType kenvTy) with
      | .sort u => pure u
      | srt => throwError "intro_kenv: unexpected KEnv sort {srt}"
    -- Exists.{u} / Classical.choose.{u} : {α : Sort u} → ...
    -- kPredTy is Int → Prop or Int → Int → Prop, both in Sort 1 = Type 0.
    let kLvl : Level := Level.succ Level.zero

    -- Close original goal via Exists.intro with explicit level (bypasses AppBuilder)
    let exIntroC := mkConst ``Exists.intro [kenvLvl]
    goal.assign (mkApp4 exIntroC kenvTy bodyFn kenvExpr mainGoalMVar)

    -- Build ∃ k1 k2 ... goal by abstracting each kMVar out of mainGoalType
    let existsC := mkConst ``Exists [kLvl]
    let mut newTarget := mainGoalType
    for i in (List.range kvarArr.size).reverse do
      let (name, arity) := kvarArr[i]!
      let kTy      := kPredTy arity
      let abstBody ← kabstract newTarget kMVars[i]! (occs := .all)
      newTarget := mkApp2 existsC kTy (mkLambda name.toName .default kTy abstBody)

    -- Create the final ∃ k1 k2 ... goal MVar
    let decl ← mainGoalMVar.mvarId!.getDecl
    let finalGoalMVar ← mkFreshExprMVarAt decl.lctx decl.localInstances newTarget

    -- Extract k-witnesses and body proof via Classical.choose chain
    let chooseC     := mkConst ``Classical.choose     [kLvl]
    let chooseSpecC := mkConst ``Classical.choose_spec [kLvl]
    let mut specProof : Expr := finalGoalMVar
    for i in [:kvarArr.size] do
      let kTy  := kPredTy kvarArr[i]!.2
      let pred := (← whnf (← inferType specProof)).appArg!
      kMVars[i]!.mvarId!.assign (mkApp3 chooseC     kTy pred specProof)
      specProof :=                mkApp3 chooseSpecC kTy pred specProof
    mainGoalMVar.mvarId!.assign specProof

    replaceMainGoal [finalGoalMVar.mvarId!]

end KEnvTactic

/-- `vc_generate` — discharge the soundness bridge under the `∃ κ`, turning
    `∃ κ, Check κ Γ e T` into its verification conditions (a CHC goal over `κ`). -/
macro "vc_generate" : tactic =>
  `(tactic|
    under_exists =>
      apply check_sound
      simp ; rfl
      simp)

/-- `vc_reify` — reify the single `KEnv` into typed per-κ unknowns (arities
    inferred) and normalize the environment lookups, leaving a clean curried
    CHC goal. Handles both arity-1 (`liftK1`) and arity-2 (`liftK2`) κ. -/
macro "vc_reify" : tactic =>
  `(tactic| intro_kenv <;> simp [STLC.mkKEnv, List.lookup, STLC.liftK1, STLC.liftK2])
