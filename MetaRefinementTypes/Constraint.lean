import MetaRefinementTypes.Syntax
import MetaRefinementTypes.Subst
import MetaRefinementTypes.Macros

/-
  **Subtyping Rules**
  Required for constraint generation

  `Base Subtyping -- Implication`

  Γ, x: b ⊢ r₁ ⇒ r₂
  --------------------------------
  Γ ⊢ {x : b | r₁} <: {x : b | r₂}

  Refinement of the subtype must
  imply refinement of the supertype.

  `Function Subtyping (Contravariant / Covariant)`

  Γ ⊢ τ'₁ <: τ₁
  Γ, x : τ₁ ⊢ τ₂ <: τ'₂
  ------------------------------------
  Γ ⊢ (x : τ₁ → τ₂) <: (x : τ'₁ → τ'₂)

  Input is contravariant, and output is
  covariant. The `binder x` is shared.

  `Application constraint`

  Γ ⊢ f : (x : τ₁ → τ₂)
  Γ ⊢ e : τ' Γ ⊢ τ' <: τ₁
  ------------------------
  Γ ⊢ f e : τ₂[x ↦ e]

  Each argument type must be a subtype
  of the function f's input type.

  `Let-Binding constraint`
  Γ ⊢ e₁ : τ₁
  Γ, x : τ₁ ⊢ e₂ : τ₂
  Γ, x : τ₁ ⊢ τ₂ <: τ
  -------------------------
  Γ ⊢ let x = e₁ in e₂ : τ

  The body type of let-binding must be
  a subtype of the the whole body type τ
  of the let-expression.

  `Function Definition Constraint`

  Γ, x : τ₁ ⊢ τ'₂ <: τ₂
  Γ, x : τ₁ ⊢ e : τ'₂
  --------------------------
  Γ ⊢ λx. e : (x : τ₁ → τ₂)

  The inferred body mmust be a subtype
  of the declared output type.
-/

-- Extract `kvars` from predicate `p`
def Pred.kvars : Pred → List KVar
  | .tru          => []
  | .fls          => []
  | .rexpr _      => []
  | .kapp k _     => [k]
  | .conj p₁ p₂   => p₁.kvars ++ p₂.kvars
  | .disj p₁ p₂   => p₁.kvars ++ p₂.kvars
  | .exist _ _ p  => p.kvars

-- Extract `kvars` from constraint `c`
def Constraint.kvars : Constraint → List KVar
  | .pred p       => p.kvars
  | .conj c₁ c₂   => c₁.kvars ++ c₂.kvars
  | .imp _ _ p c  => p.kvars ++ c.kvars

-- Basic example
def kappa1 : KVar := { name := `κ₁, params := [`z] }
def kappa2 : KVar := { name := `κ₂, params := [`z] }
def constraintEx : Constraint :=
  c{
    ∀ x : int . true ⇒
      [∀ y : int . true ⇒ kappa1(x) ∧ kappa2(y)]
  }

#eval constraintEx.kvars

/-
  WARNING: Constraint.head and .body shall
  only be called on Flattened Horn Constraints
-/
-- the innermost predicate (the goal)
def Constraint.head : Constraint → Pred
  | .pred p      => p
  | .imp _ _ _ c => c.head
  -- shouldn't happen on flat constraints
  | .conj _ _    => .tru

-- all hypothesis predicates
def Constraint.body : Constraint → List Pred
  | .pred _       => []
  | .imp _ _ p c  => p :: c.body
  | .conj _ _     => []

def FlatConstraint.head (fc: FlatConstraint) : Pred := fc.val.head
def FlatConstraint.body (fc: FlatConstraint) : List Pred := fc.val.body
def FlatConstraint.kvars (fc: FlatConstraint) : List KVar :=
  fc.val.kvars

/-
  `flat : Constraint → list FlatConstraint`

  It performs flattening on Horn Clauses
  based on `flat` in `Fig. 12.`

  Note: Order is left to right, c₁ => ⋯ => cₙ => p
-/
def Constraint.flat : Constraint → List FlatConstraint
  | .pred .tru    => []
  | .pred p       => [⟨.pred p⟩]
  | .conj c₁ c₂   => c₁.flat ++ c₂.flat
  | .imp x b p c  => c.flat.map (fun ⟨c'⟩ => ⟨.imp x b p c'⟩)

/-
  Dependencies `deps(c)` over constraints

  Deals with two cases:
  deps(c) ≅ {(κ, κ') | κ ∈ body(c), k' ∈ head(c)} -- flat constraint `c`
  deps(c) ≅ ⋃ deps(c'), where c' ∈ flat(c) -- NNF constraint `c`
-/
def FlatConstraint.deps (fc : FlatConstraint) : List (KVar × KVar) :=
  let bodyKs := (fc.body.map Pred.kvars).flatten
  let headKs := fc.head.kvars
  (bodyKs.map (fun kb => headKs.map (fun kh => (kb, kh)))).flatten

def Constraint.deps (c : Constraint) : List (KVar × KVar) :=
  (c.flat.map (fun c' => c'.deps)).flatten

-- Dependencies in `deps(σ)`
def Assignment.deps (σ : Assignment) : List (KVar × KVar) :=
  σ.flatMap fun (k', (_, body)) =>
    body.kvars.map fun k => (k, k')

-- `deps(K̂, c) = deps(c) \ (K × K̂ U K̂ × K)`, exclude pairs involving K̂
def Constraint.depsExcluding (c : Constraint) (khat : List KVar) : List (KVar × KVar) :=
  c.deps.filter fun (k1, k2) => !khat.contains k1 && !khat.contains k2

/-
  `scope : (K × C) → C`

  `scope` takes a `κ` variable and constraint `c`
  then, it returns a sub-constraint c of the form
  `∀(xᵢ:pᵢ) => c'` s.t.
    1) κ does not occur in any pᵢ
    2) all occurences of κ in c occur in c'

  Based on `Fig. 9` of the paper `Local Refinement Typing`
  and explained in `Section 5.1`.
-/
def Constraint.scope (κ : KVar) : Constraint → Constraint
  | .conj c₁ c₂ =>
    let inC₁ := c₁.kvars.contains κ
    let inC₂ := c₂.kvars.contains κ
    if inC₁ && !inC₂
      then c₁.scope κ
      else
        if !inC₁ && inC₂
        then c₂.scope κ
        else .conj c₁ c₂
  | .imp x b p c' =>
    if !(p.kvars.contains κ)
    then .imp x b p (c'.scope κ)
    else .imp x b p c'
  | c => c


-- Simplifies the predicate, e.g. p ∧ false = false
def Pred.simplify : Pred → Pred
  | .conj p₁ p₂ =>
    match p₁.simplify, p₂.simplify with
    | .fls, _    => .fls
    | _, .fls    => .fls
    | .tru, s    => s
    | s, .tru    => s
    | s₁, s₂     => .conj s₁ s₂

  | .disj p₁ p₂ =>
    match p₁.simplify, p₂.simplify with
    | .tru, _    => .tru
    | _, .tru    => .tru
    | .fls, s    => s
    | s, .fls    => s
    | s₁, s₂     => .disj s₁ s₂

  | .exist x b p =>
    match p.simplify with
    | .fls => .fls
    | s    => .exist x b s

  | p => p

/-
  `sol1 : (K × C) → P`

  sol1(κ, c) is strongest solution
  procedure in `Section 5.2`.

  It returns a predicate that is
  guaranteed to satisfy all clauses
  where κ appears as the head.

  `Note`
    Rule `sol1(κ, ∀ x : b. p ⇒ c') ≡ ∃ x : b. p ∧ sol1(κ, c)`

    If we don't simplify,
      then we can get a case where
      `sol1` returns `∃ x : b. p ∧ false`
      where logically `p ∧ false ≡ false`
      so `p` might be left over with a `κ`

  Hence. simplification is called.
  In the paper, this is implicit.
-/
def Constraint.sol1 (κ : KVar) (c : Constraint) : Pred :=
  (sol1Aux c).simplify
  where
    sol1Aux : Constraint → Pred
      | .conj c₁ c₂           => .disj (sol1Aux c₁) (sol1Aux c₂)
      | .imp x b p c          => .exist x b (.conj p (sol1Aux c))
      | .pred (.kapp k' args) =>
        if κ == k' then
          let eqs := (κ.params.zip args).map fun (pi, ai) =>
            Pred.rexpr (RExpr.mkEq (.var pi) (.var ai))
          match eqs with
          | []      => .tru
          | [e]     => e
          | e :: es => es.foldl Pred.conj e
        else .fls
      | _                     => .fls

def substKVarInPred (κ : KVar) (sol : Pred) (p : Pred) : Pred :=
  go p
where
  go : Pred → Pred
    | .tru          => .tru
    | .fls          => .fls
    | .rexpr r      => .rexpr r
    | .kapp k args  =>
      if k == κ then Pred.applyKVarSol κ sol args
      else .kapp k args
    | .conj p₁ p₂  => .conj (go p₁) (go p₂)
    | .disj p₁ p₂  => .disj (go p₁) (go p₂)
    | .exist x b p  => .exist x b (go p)

/-
  `elim* : (σ × C) → C` from Fig. 11

  Replaces all occurrences of κ in c:
  - body (hypothesis): κ(args) → σ(κ) applied to args
  - head (goal): κ(args) → true (eliminated)
-/
def Constraint.elimStar (κ : KVar) (sol : Pred) : Constraint → Constraint
  | .conj c₁ c₂   => .conj (c₁.elimStar κ sol) (c₂.elimStar κ sol)
  | .imp x b p c  => .imp x b (substKVarInPred κ sol p) (c.elimStar κ sol)
  | .pred (.kapp k y) => if k == κ then .pred .tru else .pred (.kapp k y)
  | .pred p       => .pred p

/-
  `elim1 : (K × C) → C` from Fig. 11

  elim1(κ, c) = elimStar(κ, sol, c)
  where sol = sol1(κ, c') and scope(κ, c) = ∀(xᵢ:pᵢ) ⇒ c'
-/
def stripScope (κ : KVar) : Constraint → Constraint
  | .imp x b p c => if !p.kvars.contains κ then stripScope κ c else .imp x b p c
  | c => c

def Constraint.elim1 (κ : KVar) (c : Constraint) : Constraint :=
  let scoped' := c.scope κ
  let c'      := stripScope κ scoped'
  let sol     := c'.sol1 κ
  c.elimStar κ sol

/-
  `elim : (List K × C) → C` from Fig. 12

  Iteratively eliminate each κ.
-/
def Constraint.elim (kvars : List KVar) (c : Constraint) : Constraint :=
  kvars.foldl (fun acc κ => acc.elim1 κ) c

/-
  Cycle detection - `partitionKVars`
  and Eliminating Cyclic KVars
-/

/-- Check if κ appears in both head and body of any flat clause -/
def KVar.isCyclic (κ : KVar) (c : Constraint) : Bool :=
  c.deps.any fun (κ1, κ2) => κ1 == κ && κ2 == κ

/-- Split kvars into (acyclic, cyclic) -/
def Constraint.partitionKVars (c : Constraint) : List KVar × List KVar :=
  let allKs   := c.kvars.eraseDups
  let cuts    := allKs.filter (fun κ => κ.isCyclic c)
  let acyclic := allKs.filter (fun κ => !κ.isCyclic c)
  (acyclic, cuts)

section CyclicTests

def kappa_test : KVar := { name := `κ, params := [`z] }

def ex1Test : Constraint :=
  c{ ∀ x : int . 0 ≤ x ⇒
      [∀ v : int . v == x - 1 ⇒ kappa_test(v)]
    ∧ [∀ y : int . kappa_test(y) ⇒
        ∀ v : int . v == y + 1 ⇒ 0 ≤ v] }

#eval kappa_test.isCyclic ex1Test
-- expected: false

#eval ex1Test.deps
-- expected: []

#eval ex1Test.partitionKVars
-- expected: ([κ], [])

def ka : KVar := { name := `κa, params := [`z] }
def kb : KVar := { name := `κb, params := [`z] }
def kc : KVar := { name := `κc, params := [`z] }
def kd : KVar := { name := `κd, params := [`z] }

def mixedTest : Constraint :=
  c{  -- acyclic chain: κa → κb → κc (same as ex3)
      [∀ a : int . ka(a) ⇒ ∀ ν : int . ν == a - 1 ⇒ kb(ν)]
    ∧ [∀ b : int . kb(b) ⇒ ∀ ν : int . ν == b + 1 ⇒ kc(ν)]
    ∧ [∀ ν : int . 0 ≤ ν ⇒ ka(ν)]
    ∧ [∀ ν : int . kc(ν) ⇒ 0 ≤ ν]
      -- cyclic: κd depends on itself (recursive accumulator)
    ∧ [∀ x : int . 0 ≤ x ⇒
        ∀ ν : int . x == 0 ∧ ν == 0 ⇒ kd(ν)]
    ∧ [∀ x : int . 0 ≤ x ⇒
        ∀ r : int . kd(r) ⇒
          ∀ ν : int . ν == x + r ⇒ kd(ν)]
    ∧ [∀ y : int . kd(y) ⇒ 0 ≤ y] }

#eval ka.isCyclic mixedTest    -- expect: false
#eval kb.isCyclic mixedTest    -- expect: false
#eval kc.isCyclic mixedTest    -- expect: false
#eval kd.isCyclic mixedTest    -- expect: true

#eval mixedTest.partitionKVars
-- expect: ([κa, κb, κc], [κd])

-- Eliminate only the acyclic variables
def mixedAfterAcyclic :=
  let (acyclic, _cuts) := mixedTest.partitionKVars
  mixedTest.elim acyclic

#eval mixedAfterAcyclic.kvars.eraseDups

-- Check: κa, κb, κc gone?
#eval mixedAfterAcyclic.kvars.any (· == ka)  -- expect: false
#eval mixedAfterAcyclic.kvars.any (· == kb)  -- expect: false
#eval mixedAfterAcyclic.kvars.any (· == kc)  -- expect: false
#eval mixedAfterAcyclic.kvars.any (· == kd)  -- expect: true

-- Print the residual constraint to see what's left
#eval IO.println (toString mixedAfterAcyclic)

end CyclicTests
