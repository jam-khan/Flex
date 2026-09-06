import Flex.Front.Solve

/-!
  # `#spec` — refinement-type specs over ordinary Lean definitions

  A *certifying* refinement-type frontend: the spec

    #spec inc (x : Int | x > 0) => (result : Int | result > x)

  over `def inc (x : Int) : Int := x + 1` desugars into

    theorem inc.spec : ∀ (x : Int), x > 0 → inc x > x

  and is discharged by the `flex_spec_solve` ladder (`Flex.Front.Solve`),
  bottoming out in the CHC solver (`fix`) for invariant inference. Unlike the
  verified VCG frontends (`Flex.VCG.*`), nothing here is proven sound as an
  algorithm — the desugared theorem *is* the meaning of the spec, and its
  proof is re-checked by the kernel. The only trusted step is that the
  generated statement is the one the user reads (`#print f.spec`).

  On success the spec is registered for modular composition via
  `grind_pattern f.spec => f x̄`, keying the lemma on occurrences of `f`, so
  callers verify against callee *specs* without unfolding them. (A plain
  `@[grind]` tag does not work: grind normalizes the conclusion, so the
  auto-selected pattern never fires.)

  An optional `by <tacticSeq>` trailer overrides the default ladder.

  Known prototype limitations, by design:
  * a binder *type* containing `|` (e.g. a pattern-match lambda) mis-parses;
  * a binder inside the result refinement that shadows the result variable
    (e.g. `∃ result, …`) is captured by the substitution;
  * a second `#spec` on the same function is a standard "already declared"
    error;
  * κ-inferred invariants for *recursive* definitions need a
    `fun_induction`→CHC VC generator — future work (see
    `CaseStudies/Recursion.lean` for the target CHC shape).
-/

open Lean Elab Command

declare_syntax_cat specBinder

/-- Refined binder: `(x : T | p)` — `p` may mention earlier binders and `x`. -/
syntax "(" ident " : " term " | " term ")" : specBinder
/-- Plain binder: `(x : T)` — no refinement, contributes no hypothesis. -/
syntax "(" ident " : " term ")" : specBinder

/-- `#spec f (x : T | p)* => (r : U | q) (by tacs)?` — generate and prove
`theorem f.spec : ∀ x̄, p̄ → q[r := f x̄]`, then register it for modular
composition. See the module docstring. -/
syntax (name := specCmd)
  "#spec " ident specBinder* " => " specBinder (" by " tacticSeq)? : command

private def parseSpecBinder (b : TSyntax `specBinder) :
    CommandElabM (Ident × Term × Option Term) := do
  match b with
  | `(specBinder| ($x:ident : $T:term | $p:term)) => return (x, T, some p)
  | `(specBinder| ($x:ident : $T:term))           => return (x, T, none)
  | _ => throwUnsupportedSyntax

/-- Substitute every occurrence of the result variable `r` in the result
refinement `q` by `repl` (the application `f x̄`). -/
private def substResult (r : Name) (repl : Term) (q : Term) : Term :=
  ⟨Id.run <| q.raw.replaceM fun s =>
    if s.isIdent && s.getId == r then pure (some repl.raw) else pure none⟩

elab_rules : command
  | `(#spec $f:ident $bs:specBinder* => $res:specBinder $[by $tac?:tacticSeq]?) => do
    let binders ← bs.mapM parseSpecBinder
    let (r, _U, qOpt) ← parseSpecBinder res
    let some q := qOpt | throwError "#spec: result binder needs a refinement"
    let xs : Array Term := binders.map (fun (x, _, _) => (x : Term))
    let app : Term := Syntax.mkApp f xs
    -- q[r := f x̄], then fold binders right-to-left into ∀s. Plain binders
    -- contribute no `True →` noise; each refinement sits under the earlier
    -- binders' ∀s, which is exactly its scope.
    let mut stmt : Term := substResult r.getId app q
    for (x, T, pOpt) in binders.reverse do
      match pOpt with
      | some p => stmt ← `(∀ ($x : $T), $p → $stmt)
      | none   => stmt ← `(∀ ($x : $T), $stmt)
    let fName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
    let thmName := fName ++ `spec
    let declId := mkIdent (`_root_ ++ thmName)
    let tacSeq ← match tac? with
      | some t => pure t
      | none   => `(tacticSeq| flex_spec_solve $f:ident)
    -- Error-count snapshot rather than `hasErrors`: an unrelated earlier error
    -- in the file must not mask or fake this command's outcome.
    let errsBefore := ((← get).messages.toList.filter (·.severity == .error)).length
    elabCommand (← `(command| theorem $declId:ident : $stmt := by $tacSeq))
    let errsAfter := ((← get).messages.toList.filter (·.severity == .error)).length
    if errsAfter > errsBefore then return
    -- `constructor <;> grind` inside `leafClosers` can silently insert
    -- `sorry`; refuse to register a spec whose proof contains one.
    if let some (.thmInfo v) := (← getEnv).find? thmName then
      if v.value.hasSorry then
        throwError "#spec: proof of {thmName} contains sorry"
    elabCommand (← `(command| grind_pattern $(mkIdent thmName):ident => $app:term))
    logInfo m!"#spec: {thmName} proved and registered"
