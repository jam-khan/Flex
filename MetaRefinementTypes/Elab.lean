import MetaRefinementTypes.Syntax

/-
  Procedure `Shape` from `Section 4.4`
  in `Local Refinement Typing`.

  Erases refinements from a refined type `t`
  returning unrefined type `τ`.
-/
def RType.erase : RType → UType
  | .tvar α        => .tvar α
  -- {x : b | r} ⤳ b
  | .base _ b _    => .base b
  | .fn x t1 t2    => .fn x t1.erase t2.erase
  | .forallTy α t  => .forallTy α t.erase


def nu : Var := String.toName "v"

def primInt (n : Int) : RType :=
  .base nu .int (RExpr.mkEq (.var nu) (.int n))

def primAssert : RType :=
  .fn (String.toName "x") (.base nu .bool (.var nu))
           (.base nu .bool RExpr.tt)
