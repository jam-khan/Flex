/-
1st iteration:
1. find kappa
2. exists kappa
3. do something such that we know
where kappa occurs


2nd iteration:
1. elim1(κ, Expr)

  elim1(κ, c₁ ∧ c₂) : Expr
    | κ ∈ c₁, κ ∉ c₂      = elim1(κ, c₁) ∧ c₂
    | κ ∉ c₁, κ ∈ c₂      = c₁ ∧ elim1(κ, c₂)
    | κ ∈ c₁, κ ∈ c₂      = sol1(κ, c)
    | κ ∉ c₁, κ ∉ c₂      = c
  elim1(κ, ∀ x : b, c')   = ∀ x : b, elim1(κ, c')
  elim1(κ, p ⇒ c)
    |  κ ∉ p  = p ⇒ elim1(κ, c')
    |  κ ∈ p  = sol1


sol1 : Prop (Type) -> fun Prop/Type, I: ? -> Term/Proof)

Prop in the head
Here is the proof

Type in the head
Here is the term

-/
