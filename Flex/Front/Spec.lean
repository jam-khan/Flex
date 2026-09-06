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

  Function-typed binders take the refined-arrow form
  `(f : (i : T | p) => (r : U | q))`, denoting `∀ i, p → q[r := f i]`.

  Known prototype limitations, by design:
  * a binder *type* containing a bare `|` (e.g. a pattern-match lambda)
    mis-parses — refined arrows are the one supported nesting;
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
/-- Function-typed refined binder: `(f : (i : T | p) => (r : U | q))` — `f`
gets type `T → U` and contributes the arrow denotation as its hypothesis:
`∀ i, p → q[r := f i]`. Nests, so higher-order arguments of any depth parse. -/
syntax "(" ident " : " specBinder " => " specBinder ")" : specBinder

/-- `#spec f (x : T | p)* => (r : U | q) (by tacs)?` — generate and prove
`theorem f.spec : ∀ x̄, p̄ → q[r := f x̄]`, then register it for modular
composition. See the module docstring. -/
syntax (name := specCmd)
  "#spec " ident specBinder* " => " specBinder (" by " tacticSeq)? : command

/-- Substitute every occurrence of the result variable `r` in the result
refinement `q` by `repl` (the application `f x̄`). Dot-notation on the result
variable (`r.length`) parses as a single dotted ident rooted at `r`, so it is
rewritten to a projection chain on `repl` (`(f x̄).length`). -/
private def substResult (r : Name) (repl : Term) (q : Term) : Term :=
  ⟨Id.run <| q.raw.replaceM fun s => do
    unless s.isIdent do return none
    let n := s.getId
    if n == r then return some repl.raw
    match n.components with
    | root :: rest =>
      if root == r && !rest.isEmpty then
        return some <| rest.foldl (init := repl.raw) fun acc c =>
          mkNode ``Lean.Parser.Term.proj #[acc, mkAtom ".", mkIdent c]
      else return none
    | _ => return none⟩

/-- Parse a binder into `(name, type, hypothesis?)`. For arrow binders the
type and hypothesis are synthesized: `(f : (i : T | p) => (r : U | q))`
becomes `(f, T → U, ∀ i, p → q[r := f i])`. -/
private partial def parseSpecBinder (b : TSyntax `specBinder) :
    CommandElabM (Ident × Term × Option Term) := do
  match b with
  | `(specBinder| ($x:ident : $T:term | $p:term)) => return (x, T, some p)
  | `(specBinder| ($x:ident : $T:term))           => return (x, T, none)
  | `(specBinder| ($f:ident : $arg:specBinder => $res:specBinder)) => do
    let (i, T, pOpt) ← parseSpecBinder arg
    let (r, U, qOpt) ← parseSpecBinder res
    let some q := qOpt
      | throwError "#spec: a function binder's result needs a refinement"
    let q' := substResult r.getId (Syntax.mkApp f #[i]) q
    let hyp ← match pOpt with
      | some p => `(∀ ($i : $T), $p → $q')
      | none   => `(∀ ($i : $T), $q')
    return (f, ← `($T → $U), some hyp)
  | _ => throwUnsupportedSyntax

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
    -- in the file must not mask or fake this command's outcome. The theorem is
    -- elaborated synchronously — under `Elab.async` its proof errors would
    -- land after the snapshot (the `hasSorry` guard below would still catch
    -- them, but the failure would surface as the wrong error).
    let errsBefore := ((← get).messages.toList.filter (·.severity == .error)).length
    elabCommand
      (← `(command| set_option Elab.async false in
                    theorem $declId:ident : $stmt := by $tacSeq))
    let errsAfter := ((← get).messages.toList.filter (·.severity == .error)).length
    if errsAfter > errsBefore then return
    -- `constructor <;> grind` inside `leafClosers` can silently insert
    -- `sorry`; refuse to register a spec whose proof contains one.
    if let some (.thmInfo v) := (← getEnv).find? thmName then
      if v.value.hasSorry then
        throwError "#spec: proof of {thmName} contains sorry"
    -- Registration is best-effort: `grind_pattern` requires the pattern to
    -- cover every top-level binder, which a result refinement of the shape
    -- `∀ b ∈ r, …` violates (its `b` outlives the pattern `f x̄`). The
    -- theorem stands either way; only search-composition is affected.
    let saved := (← get).messages
    elabCommand (← `(command| grind_pattern $(mkIdent thmName):ident => $app:term))
    if ((← get).messages.toList.filter (·.severity == .error)).length > errsBefore then
      modify fun s => { s with messages := saved }
      logInfo m!"#spec: {thmName} proved (not registered for composition: \
        grind_pattern rejected the pattern {app} — register one manually)"
    else
      logInfo m!"#spec: {thmName} proved and registered"
