import Lean
import MetaRefinementTypes.Syntax

open Lean

private def elabBaseTy (id : TSyntax `ident) : MacroM (TSyntax `term) := do
  match id.getId with
  | `int  => `(BaseTy.int)
  | `bool => `(BaseTy.bool)
  | n     => Macro.throwError s!"Unknown base type: {n}, expected `int` or `bool`"

declare_syntax_cat rexpr

syntax num      : rexpr
syntax "-" num  : rexpr
syntax "true"   : rexpr
syntax "false"  : rexpr
syntax ident    : rexpr

syntax:50 rexpr:50 " + " rexpr:51 : rexpr
syntax:50 rexpr:50 " - " rexpr:51 : rexpr
syntax:60 rexpr:60 " * " rexpr:61 : rexpr
syntax:60 rexpr:60 " / " rexpr:61 : rexpr

syntax:40 rexpr:41 " == " rexpr:41 : rexpr
syntax:40 rexpr:41 " != " rexpr:41 : rexpr
syntax:40 rexpr:41 " < "  rexpr:41 : rexpr
syntax:40 rexpr:41 " ≤ "  rexpr:41 : rexpr
syntax:40 rexpr:41 " > "  rexpr:41 : rexpr
syntax:40 rexpr:41 " ≥ "  rexpr:41 : rexpr

syntax:30 rexpr:31 " ∧ " rexpr:30 : rexpr
syntax:20 rexpr:21 " ∨ " rexpr:20 : rexpr
syntax:10 rexpr:11 " → " rexpr:10 : rexpr
syntax " ¬ " rexpr:70             : rexpr

syntax "(" rexpr ")" : rexpr

-- entry point for refinement expressions
syntax "r{" rexpr "}" : term

macro_rules
  | `(r{ $n:num })    => `(RExpr.int $n)
  | `(r{ - $n:num })  => `(RExpr.int (- $n))
  | `(r{ true })      => `(RExpr.bool Bool.true)
  | `(r{ false })     => `(RExpr.bool Bool.false)
  | `(r{ $x:ident })  => `(RExpr.var $(quote x.getId))
  -- arithmetic
  | `(r{ $l + $r })   => `(RExpr.arith .add r{$l} r{$r})
  | `(r{ $l - $r })   => `(RExpr.arith .sub r{$l} r{$r})
  | `(r{ $l * $r })   => `(RExpr.arith .mul r{$l} r{$r})
  | `(r{ $l / $r })   => `(RExpr.arith .div r{$l} r{$r})
  -- bool comparison
  | `(r{ $l == $r })  => `(RExpr.cmp .eq r{$l} r{$r})
  | `(r{ $l != $r })  => `(RExpr.cmp .ne r{$l} r{$r})
  | `(r{ $l < $r })   => `(RExpr.cmp .lt r{$l} r{$r})
  | `(r{ $l ≤ $r })   => `(RExpr.cmp .le r{$l} r{$r})
  | `(r{ $l > $r })   => `(RExpr.cmp .gt r{$l} r{$r})
  | `(r{ $l ≥ $r })   => `(RExpr.cmp .ge r{$l} r{$r})
  -- boolean
  | `(r{ $l ∧ $r })   => `(RExpr.bop .and r{$l} r{$r})
  | `(r{ $l ∨ $r })   => `(RExpr.bop .or  r{$l} r{$r})
  | `(r{ $l → $r })   => `(RExpr.bop .imp r{$l} r{$r})
  | `(r{ ¬ $e })      => `(RExpr.not r{$e})
  -- parens
  | `(r{ ( $e ) })    => `(r{$e})

declare_syntax_cat pred

syntax "true"   : pred
syntax "false"  : pred
syntax rexpr    : pred

syntax ident "(" ident,* ")" : pred

syntax:30 pred:31 " ∧ " pred:30 : pred
syntax:20 pred:21 " ∨ " pred:20 : pred

syntax "∃" ident ":" ident "." pred : pred
-- syntax "(" pred ")"   : pred
-- syntax "(" rexpr ")"  : pred

syntax "p{" pred "}" : term

macro_rules
  | `(p{ true })
      => `(Pred.tru)
  | `(p{ false })
      => `(Pred.fls)
  | `(p{ $k:ident ( $[$args:ident],* ) })
      => do let argTerms ← args.mapM fun a => `($(quote a.getId))
            `(Pred.kapp $k [$argTerms,*])
  | `(p{ $l ∧ $r })
      => `(Pred.conj p{$l} p{$r})
  | `(p{ $l ∨ $r })
      => `(Pred.disj p{$l} p{$r})
  | `(p{ ∃ $x:ident : $b:ident . $body })
      => do let bty ← elabBaseTy b
            `(Pred.exist $(quote x.getId) $bty p{$body})
  | `(p{ $r:rexpr })
      => `(Pred.rexpr r{$r})
  -- | `(p{ ( $e:pred ) })      => `(p{$e})
  -- | `(p{ ( $e:rexpr ) })     => `(Pred.rexpr r{$e})

declare_syntax_cat constr

syntax pred : constr

syntax:30 constr:31 " ∧ " constr:30 : constr

syntax "∀" ident ":" ident "." pred "⇒" constr : constr

syntax "[" constr "]" : constr

syntax "c{" constr "}" : term

macro_rules
  | `(c{ $l ∧ $r })
      =>  `(Constraint.conj c{$l} c{$r})
  | `(c{ ∀ $x:ident : $b:ident . $hyp:pred ⇒ $body:constr })
      => do let bty ← elabBaseTy b
            `(Constraint.imp $(quote x.getId) $bty p{$hyp} c{$body})
  | `(c{ $p:pred })
      =>  `(Constraint.pred p{$p})
  | `(c{ [ $e:constr ] }) => `(c{$e})
