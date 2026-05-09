
import LeanFixpoint.Core.Types
import LeanFixpoint.Monad

open Lean Meta
/-- Flatten: split `And` at top level, distribute `∀` over `And`. -/
partial def exprFlat (e : Expr) : KM (List Expr) := do
  -- reduce to weak head normal form
  let e ← whnf e

  -- flat(true) ≃ ∅
  if e.isConstOf ``True then
    return []
  -- flat(cₗ ∧ cᵣ) ≃ flat(cₗ) ⋃ flat(cᵣ)
  else if let some (l, r) := e.and? then
    return (← exprFlat l) ++ (← exprFlat r)
  -- flat(∀ x : b. c)
  -- NOTE: this works with multiple guards
  -- so, c can be p₁ → p₂ → ... → pₙ → c
  -- in Expr, p → q is essentially ∀ _ : p, q
  -- so it will be covered by below case
  else if e.isForall then
    -- introduce a free-variable for `x`
    withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
      -- flatCs ≃ flatten(c'),
      -- where c' is instantiation of c with free variable x
      let flatBodies ← exprFlat (e.bindingBody!.instantiate1 fvar)
      -- {∀ x : b. p ⇒ c'' | c'' ∈ flatCs}
      flatBodies.mapM fun fb => do
        let abstr := fb.abstract #[fvar]
        pure (Expr.forallE e.bindingName! e.bindingDomain! abstr e.bindingInfo!)
  else
    return [e]

/-- Run a `KM` action with no κ-variables. -/
def runEmpty (act : KM α) : MetaM α :=
  act.run { kvars := {} }



-------------------------------------------------------
-- Testing
-------------------------------------------------------

-- Unfold a named `def` to its body `Expr`.
private def unfoldDef (n : Name) : MetaM Expr := do
  let some ci := (← getEnv).find? n | throwError "unknown constant {n}"
  match ci with
  | .defnInfo v => whnf v.value
  | _ => throwError "{n} is not a def"

private def testFlat (name : String) (inputName : Name) (expectedNames : List Name) : MetaM Unit := do
  let input ← unfoldDef inputName
  let expected ← expectedNames.mapM unfoldDef
  let results : List Expr ← runEmpty (exprFlat input)
  if List.length results != List.length expected then
    logInfo m!"FAIL [{name}]: expected {List.length expected} clauses, got {List.length results}"
    let mut i : Nat := 0
    for r in results do
      logInfo m!"  got[{repr i}]: {← ppExpr r}"
      i := i + 1
    return
  let mut i : Nat := 0
  for (r, e) in List.zip results expected do
    unless ← isDefEq r e do
      logInfo m!"FAIL [{name}] clause {repr i}:"
      logInfo m!"  got:      {← ppExpr r}"
      logInfo m!"  expected: {← ppExpr e}"
      return
    i := i + 1
  logInfo m!"PASS [{name}]"

-- Test 1: flat(True) = []
def flat_in_1 : Prop := True

#eval! testFlat "flat(True) = []" ``flat_in_1 []

-- Test 2: flat(atom) = [atom]
def flat_in_2  : Prop := (0 : Nat) = 0
def flat_out_2 : Prop := (0 : Nat) = 0

#eval! testFlat "flat(atom) = [atom]" ``flat_in_2 [``flat_out_2]

-- Test 3: flat(A ∧ B) = [A, B]
def flat_in_3    : Prop := (0 : Nat) = 0 ∧ (1 : Nat) = 1
def flat_out_3_0 : Prop := (0 : Nat) = 0
def flat_out_3_1 : Prop := (1 : Nat) = 1

#eval! testFlat "flat(A ∧ B) = [A, B]" ``flat_in_3 [``flat_out_3_0, ``flat_out_3_1]

-- Test 4: flat(A ∧ (B ∧ True)) = [A, B]
def flat_in_4    : Prop := (0 : Nat) = 0 ∧ ((1 : Nat) = 1 ∧ True)
def flat_out_4_0 : Prop := (0 : Nat) = 0
def flat_out_4_1 : Prop := (1 : Nat) = 1

#eval! testFlat "flat(A ∧ (B ∧ True)) = [A, B]" ``flat_in_4 [``flat_out_4_0, ``flat_out_4_1]

-- Test 5: flat(∀ x : Nat, x = x ∧ 0 = 0)
--       = [∀ x, x = x,  ∀ x, 0 = 0]
def flat_in_5    : Prop := ∀ x : Nat, x = x ∧ (0 : Nat) = 0
def flat_out_5_0 : Prop := ∀ x : Nat, x = x
def flat_out_5_1 : Prop := ∀ _ : Nat, (0 : Nat) = 0

#eval! testFlat "flat(∀ x, A ∧ B)" ``flat_in_5 [``flat_out_5_0, ``flat_out_5_1]

-- Test 6: flat(∀ x : Nat, x = 0 → (x = x ∧ 0 = 0))
--       = [∀ x, x = 0 → x = x,
--          ∀ x, x = 0 → 0 = 0]
def flat_in_6    : Prop := ∀ x : Nat, x = 0 → (x = x ∧ (0 : Nat) = 0)
def flat_out_6_0 : Prop := ∀ x : Nat, x = 0 → x = x
def flat_out_6_1 : Prop := ∀ x : Nat, x = 0 → (0 : Nat) = 0

#eval! testFlat "flat(∀ x, guard → A ∧ B)" ``flat_in_6 [``flat_out_6_0, ``flat_out_6_1]
