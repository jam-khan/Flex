/-
Constraints
  now parametrized by depth d

  c   ::= pᵈ
        | c₁ ∧ᵈ c₂
        | ∀ x : b. p ⇒ᵈ c

  When we go from Prop → Expr → Constraint, we
  annotate depth.

  depth : C × Nat → C
  depth(p, d)             = pᵈ
  depth(c₁ ∧ c₂, d)       = depth(c₁, d) ∧ᵈ depth(c₂, d)
  depth(∀ x:b. p ⇒ c, d)  = ∀ x:b. p ⇒ᵈ depth(c, d+1)

  scope : K × C → C
  scope(κ, c₁ ∧ᵈ c₂)
  | κ ∈ c₁, κ ∉ c₂       ≡ scope(κ, c₁)
  | κ ∉ c₁, κ ∈ c₂       ≡ scope(κ, c₂)
  scope(κ, ∀x:b. p ⇒ᵈ c')
    | κ ∉ p              ≡ ∀x:b. p ⇒ᵈ scope(κ, c')
  scope(κ, c)            ≡ c

  sol1' : (K × C) → (P, [Nat])
  sol1(κ, c₁ ∧ᵈ c₂, hs)      ≡ sol1(κ, c₁) ∨ sol1(κ, c₂)
  sol1(κ, ∀x:b. p ⇒ᵈ c', hs) ≡ (∃ x:b, p ∧ c'', hs)
    where (c'', hs) = sol1(κ, c', hs ++ [2d, 2d + 1])
  sol1(κ, κ(y), hs)          ≡
  scope(κ, c, hs)            ≡ (c, hs)

  sol1(,c1 ^ c2) ⌘ sol1(,c1) _ sol1(,c2)
  sol1(, 8x :b. p ) c) ⌘ 9x :b. p ^ sol1(,c)
  sol1(,()) ⌘ ”
  i xi = i where x = params()
  sol1(,p) ⌘ false





scope(κ, c₁<i> ∧ c₂<j>)
  | κ ∈ c₁<i>, κ ∉ c₂<j>   ≡ scope(κ, c₁)<i>
  | κ ∉ c₁<i>, κ ∈ c₂<j>   ≡ scope(κ, c₂)
scope(κ, ∀x:b, p ⇒ c'<i>)
  | κ ∉ p                 ≡ ∀x:b, p ⇒ scope(κ, c')
scope(κ, c)               ≡ c

sol1 : K × C(i) × [Nat] → (P, [Nat])
sol1(κ, c₁(i) ∧ c₂(i), insts)
  ≡ sol1(κ, c₁, insts ) ∨ sol1(κ, c₂(i), insts)



-/
