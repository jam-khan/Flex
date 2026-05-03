import Lean

open Lean Meta Elab Tactic

/-! ## `perm_exists` tactic

  Proves `(∃ x₀ x₁ … xₙ, P) ↔ (∃ y₀ y₁ … yₙ, P)` (or the `→` direction)
  when both sides have the same body and the binder *names* match up
  (just in a different order).

  Strategy: `rintro ⟨src…, h⟩; exact ⟨dst…, h⟩`.
-/

/-- Walk the head ∃-chain, returning the binder names in source order. -/
private partial def collectExNames (e : Expr) : MetaM (List Name) := do
  let e ← whnf e
  if e.isAppOfArity ``Exists 2 then
    let pred := e.getArg! 1
    if pred.isLambda then
      let α := e.getArg! 0
      withLocalDeclD pred.bindingName! α fun fvar => do
        let rest ← collectExNames (pred.bindingBody!.instantiate1 fvar)
        return pred.bindingName! :: rest
    else return []
  else return []

/-- Build an rintro pattern `⟨n₀, n₁, …, nₖ₋₁, h⟩` from a list of names. -/
private def mkAnonPat (names : List Name) (hyp : Name) :
    MetaM (TSyntax `rintroPat) := do
  let idents : Array (TSyntax `rcasesPat) ←
    (names ++ [hyp]).toArray.mapM fun n =>
      `(rcasesPat| $(mkIdent n):ident)
  `(rintroPat| ⟨$idents,*⟩)

/-- Build an anonymous constructor `⟨n₀, …, nₖ₋₁, h⟩` term. -/
private def mkAnonCtorTerm (names : List Name) (hyp : Name) :
    MetaM (TSyntax `term) := do
  let idents : Array (TSyntax `term) ←
    (names ++ [hyp]).toArray.mapM fun n =>
      pure ⟨mkIdent n⟩
  `(term| ⟨$idents,*⟩)

/-- Prove one direction: `(∃ srcNames, P) → (∃ dstNames, P)`. -/
private def permDirection (srcNames dstNames : List Name) : TacticM Unit := do
  let hyp : Name := `h
  let srcPat ← mkAnonPat srcNames hyp
  let dstCtor ← mkAnonCtorTerm dstNames hyp
  evalTactic (← `(tactic| (rintro $srcPat; exact $dstCtor)))

/-- `perm_exists` — prove `P₁ ↔ P₂` (or `P₁ → P₂`) when both sides are
    `∃`-chains over the same body, just permuted. Matched by binder name. -/
elab "perm_exists" : tactic => withMainContext do
  let goalType ← (← getMainGoal).getType
  let goalType ← whnf goalType
  if goalType.isAppOfArity ``Iff 2 then
    let lhs := goalType.getArg! 0
    let rhs := goalType.getArg! 1
    let lNames ← collectExNames lhs
    let rNames ← collectExNames rhs
    if lNames.length != rNames.length then
      throwError "perm_exists: ∃-chains have different lengths \
        ({lNames.length} vs {rNames.length})"
    evalTactic (← `(tactic| constructor))
    permDirection lNames rNames
    permDirection rNames lNames
  else if goalType.isForall && !goalType.bindingBody!.hasLooseBVars then
    let lhs := goalType.bindingDomain!
    let rhs := goalType.bindingBody!
    let lNames ← collectExNames lhs
    let rNames ← collectExNames rhs
    if lNames.length != rNames.length then
      throwError "perm_exists: ∃-chains have different lengths"
    permDirection lNames rNames
  else
    throwError "perm_exists: expected ↔ or → between ∃-chains, \
      got{indentExpr goalType}"
