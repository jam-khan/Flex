/-
══════════════════════════════════════════════════════════
  Kernel-Checked Elimination via Depth-Indexed Tactics
══════════════════════════════════════════════════════════

Given: Prop of form ∃ κ₁ … κₙ, Body(κ₁,…,κₙ)

We want `elim` to produce tactic sequences instead of
rewriting constraints. After the solver instantiates
∃ κᵢ := sol(κᵢ) and Lean β-reduces via `dsimp only`,
each conjunct has shape dictated by sol1. The proof
is fully determined by the ∃/∧ structure of sol1 plus
a mapping from ∃-nodes to proof-context fvars.

════════════════════
  Depth Annotations
════════════════════

When translating Prop → Expr → Constraint, annotate
each ⇒ node with depth d (ancestor ⇒ count). After
`intro`, depth d yields exactly two fvars in the Lean
context: value at position 2d, hypothesis at 2d+1.

  c  ::=  pᵈ  |  c₁ ∧ᵈ c₂  |  ∀ x:b. p ⇒ᵈ c

  depth(p, d)              = pᵈ
  depth(c₁ ∧ c₂, d)       = depth(c₁, d) ∧ᵈ depth(c₂, d)
  depth(∀x:b. p ⇒ c, d)   = ∀x:b. p ⇒ᵈ depth(c, d+1)

scope preserves annotations (selects subterms, never rebuilds):

  scope(κ, c₁ ∧ᵈ c₂)
    | κ ∈ c₁, κ ∉ c₂        = scope(κ, c₁)
    | κ ∉ c₁, κ ∈ c₂        = scope(κ, c₂)
  scope(κ, ∀x:b. p ⇒ᵈ c')
    | κ ∉ p                  = ∀x:b. p ⇒ᵈ scope(κ, c')
  scope(κ, c)                = c

════════════════════
  Extended sol1
════════════════════

sol1 now also returns the fvar-index list hs: the i-th
∃ node in the output uses hs[2i] as witness and hs[2i+1]
as hypothesis proof. Each ⇒ᵈ appends [2d, 2d+1].

  sol1 : K × C × [Nat] → P × [Nat]

  sol1(κ, c₁ ∧ᵈ c₂, hs)       = (s₁ ∨ s₂, hs₁ ++ hs₂)
      where (s₁, hs₁) = sol1(κ, c₁, hs)
            (s₂, hs₂) = sol1(κ, c₂, hs)

  sol1(κ, ∀x:b. p ⇒ᵈ c', hs)  = (∃x:b. p ∧ s, hs')
      where (s, hs') = sol1(κ, c', hs ++ [2d, 2d+1])

  sol1(κ, κ(y), hs)            = (⋀ᵢ zᵢ = yᵢ, hs)
      where z = params(κ)

  sol1(κ, p, hs)               = (⊥, hs)

Invariant: ∃-nodes appear left-to-right matching the
∀-binders in the constraint, so fvar order = ∃ order.

════════════════════
  stripScope
════════════════════

stripScope peels outer binders where κ ∉ p, splitting
hs into outer (shared scope fvars) and inner (clause-local):

  stripScope(κ, ∀x:b. p ⇒ᵈ c', hs)
    | κ ∉ p   = stripScope(κ, c', hs ++ [2d, 2d+1])
  stripScope(κ, c, hs)  = (c, hs)

The returned hs are the outer fvar indices. For a flat
clause, the full witness list is outer ++ local, where
local comes from intro'ing the clause's own ∀-binders.

════════════════════
  Conjunct Classification
════════════════════

After flat(c), each clause cᵢ is one of:

  headOnly   κ ∈ head(cᵢ), K ∩ body(cᵢ) = ∅
  headBody   κ ∈ head(cᵢ), κ' ∈ body(cᵢ)
  pureVC     K ∩ head(cᵢ) = ∅

════════════════════
  Proof Emission
════════════════════

Two mutually recursive procedures driven by the Pred tree:

  emit : P × [Nat] → Tactic
  ─────────────────────────────────────────────────────
  emit(∃x:b. p ∧ q, hs)  =  exists fvar[hs[0]]
                              constructor
                              · emitHyp(p, hs[1])
                              · emit(q, hs[2:])

  emit(∃x:b. leaf, hs)   =  exists fvar[hs[0]]

  emit(s₁ ∨ s₂, hs)      =  left;  emit(s₁, hs)
                           |  right; emit(s₂, hs)

  emit(_, _)              =  ε

  emitHyp : P × Nat → Tactic
  ─────────────────────────────────────────────────────
  emitHyp(r, i)               =  exact fvar[i]
                                  (fallback: grind)

  emitHyp(∃x:b. p ∧ q, i)    =  exists destr[i]
                                  constructor
                                  · emitHyp(p, i+1)
                                  · emitHyp(q, i+2)

  emitHyp(∃x:b. leaf, i)     =  exists destr[i]

For headOnly, emitHyp always hits the rexpr case
(simple predicates closed by exact or grind).

For headBody, the ∧-left child of the head solution
may itself be sol(κ'). Then emitHyp recurses into the
nested ∃/∧ using fvars from destructuring the body hyp:

  destr : Expr × P → [Expr]
  ─────────────────────────────────────────────────────
  destr(h, ∃x:b. p ∧ q)  =  obtain ⟨x, hp, rest⟩ := h
                              [x, hp] ++ destr(rest, q)

  destr(h, ∃x:b. leaf)   =  obtain ⟨x, hl⟩ := h
                              [x, hl]

Destructured fvars feed emitHyp in left-to-right order,
matching the nested ∃-nodes.

════════════════════
  Disjunction Branches
════════════════════

When stripScope(κ, scope(κ,c)) = c₁ ∧ᵈ c₂, sol1
returns s₁ ∨ s₂. A flat clause from c₁ emits
left; emit(s₁, hs). From c₂: right; emit(s₂, hs).
Branch provenance is tracked at flatten time.

════════════════════
  Full Tactic Sequence
════════════════════

  Phase 1  exists sol₁; …; exists solₙ; dsimp only
  Phase 2  intro x₀ h₀ … xₘ hₘ        (outer scope)
  Phase 3  refine ⟨?_, …, ?_⟩           (split ∧)
  Phase 4  for each conjunct cᵢ:
           ─ headOnly:  intro locals; emit(sol, hs)
           ─ headBody:  intro locals;
                         destr(hκ', bodySol);
                         [left|right];
                         emit(headSol, hs)
           ─ pureVC:    grind
-/
