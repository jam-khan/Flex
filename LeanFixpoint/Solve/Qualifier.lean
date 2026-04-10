-- import Lean
-- import LeanFixpoint.Core.Types
-- import LeanFixpoint.Core.Subst
-- import LeanFixpoint.Core.Pretty
-- import LeanFixpoint.Core.Macros

-- open Lean

-- structure QualParam where
--   sym   : Var     -- name/symbol for the parameter
--   sort  : BaseTy  -- sort is just a base type, e.g., Int, Bool
-- deriving Repr, BEq, Inhabited

-- structure Qualifier where
--   name    : Name            -- name for qualifier
--   params  : List QualParam  -- list of qualifier parameters
--   body    : RExpr           -- body is the refinement expression
-- deriving Repr, BEq


-- /-- Insantiate qualifier: map each param to a concrete variable -/
-- def Qualifier.instantiate (q : Qualifier) (args : List Var) : RExpr :=
--   -- Create list of pairs of parameter symbols and corresponding arguments
--   let pairs := q.params.map (fun p => p.sym) |>.zip args
--   -- walk through list and subst each in body from param sym to the argument
--   pairs.foldl (fun e (from', to) => RExpr.subst from' (.var to) e) q.body

-- -- Qualifier param syntax, e.g. `v : int`
-- declare_syntax_cat qualParam
-- syntax ident ":" ident : qualParam

-- -- Qualifier syntax: `Name(params) | body`
-- declare_syntax_cat qual
-- syntax ident "(" qualParam,* ")" "|" rexpr : qual

-- -- Entry point
-- syntax "q{" qual "}" : term

-- macro_rules
--   | `(q{ $name:ident ( $[$ps],* ) | $body:rexpr }) => do
--       let params ← ps.mapM fun p => do
--         match p with
--         | `(qualParam| $sym:ident : $sort:ident) =>
--             let bty ← elabBaseTy sort
--             `({ sym := $(quote sym.getId), sort := $bty : QualParam })
--         | _ => Macro.throwError "invalid qualifier parameter"
--       `({ name := $(quote name.getId), params := [$params,*], body := r{$body} : Qualifier })

-- section Examples

-- -- (qualif Bar ((v Int)) (>= v 0))
-- private def ex1 : Qualifier := q{ Bar(v : int) | 0 ≤ v }

-- -- (qualif Baz ((v Int) (a Int)) (>= v a))
-- private def ex2 : Qualifier := q{ Baz(v : int, a : int) | a ≤ v }

-- -- (qualif EqConj ((v Int) (a Int)) (and (>= v a) (<= v a)))
-- private def ex3 : Qualifier := q{ EqConj(v : int, a : int) | a ≤ v ∧ v ≤ a }

-- -- (qualif Bounded ((v Int) (a Int) (b Int)) (and (>= v a) (<= v b)))
-- private def ex4 : Qualifier := q{ Bounded(v : int, a : int, b : int) | a ≤ v ∧ v ≤ b }

-- -- (qualif Sum ((v Int) (a Int) (b Int)) (= v (+ a b)))
-- private def ex5 : Qualifier := q{ Sum(v : int, a : int, b : int) | v == a + b }

-- -- (qualif Diff ((v Int) (a Int) (b Int)) (= v (- a b)))
-- private def ex6 : Qualifier := q{ Diff(v : int, a : int, b : int) | v == a - b }

-- #eval toString (ex1.instantiate [`z])         -- "0 <= z"
-- #eval toString (ex2.instantiate [`z, `n])     -- "n <= z"
-- #eval toString (ex4.instantiate [`x, `lo, `hi])  -- "lo <= x ∧ x <= hi"

-- end Examples
