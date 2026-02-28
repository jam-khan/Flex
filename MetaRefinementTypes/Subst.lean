import MetaRefinementTypes.Syntax


-- NOTE: Careful with this one, try to get a terminating function
partial def RExpr.subst (target : Var) (val : RExpr) : RExpr → RExpr
  | .var x        => if x == target then val else .var x
  | .int n        => .int n
  | .bool b       => .bool b
  | .arith op l r => .arith op (l.subst target val) (r.subst target val)
  | .cmp op l r   => .cmp op (l.subst target val) (r.subst target val)
  | .bop op l r   => .bop op (l.subst target val) (r.subst target val)
  | .not e        => .not (e.subst target val)
  | .app f args   => .app f (args.map fun a => a.subst target val)

-- NOTE: ADD docs
partial def Pred.substVar (target : Var) (replacement : Var) : Pred → Pred
  | .tru          => .tru
  | .fls          => .fls
  | .rexpr r      => .rexpr (r.subst target (.var replacement))
  | .kapp k args  => .kapp k (args.map fun a => if a == target then replacement else a)
  | .conj p₁ p₂  => .conj (p₁.substVar target replacement) (p₂.substVar target replacement)
  | .disj p₁ p₂  => .disj (p₁.substVar target replacement) (p₂.substVar target replacement)
  | .exist x b p  => .exist x b (p.substVar target replacement)

-- NOTE: Add docs
partial def Pred.substKVar (κ : KVar) (sol : Pred) : Pred → Pred
  | .tru          => .tru
  | .fls          => .fls
  | .rexpr r      => .rexpr r
  | .kapp k args  =>
    if k == κ then
      let pairs := κ.params.zip args
      pairs.foldl (fun acc (param, arg) => acc.substVar param arg) sol
    else .kapp k args
  | .conj p₁ p₂  => .conj (p₁.substKVar κ sol) (p₂.substKVar κ sol)
  | .disj p₁ p₂  => .disj (p₁.substKVar κ sol) (p₂.substKVar κ sol)
  | .exist x b p  => .exist x b (p.substKVar κ sol)

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

def RExpr.substMany (params : List Var) (args : List Var) (body : RExpr) : RExpr :=
  (params.zip args).foldl (fun acc (p, a) => acc.subst p (.var a)) body
