import Lean
import LeanFixpoint.Core.Types

open Lean

def elabBaseTy (id : TSyntax `ident) : MacroM (TSyntax `term) := do
  match id.getId with
  | `int  => `(BaseTy.int)
  | `bool => `(BaseTy.bool)
  | n     => Macro.throwError s!"Unknown base type: {n}, expected `int` or `bool`"

declare_syntax_cat constr

syntax term : constr

syntax:30 constr:31 " ∧ " constr:30 : constr

syntax "∀" ident ":" ident "." term "⇒" constr : constr

syntax "[" constr "]" : constr

syntax "c{" constr "}" : term

macro_rules
  | `(c{ $l ∧ $r })
      =>  `(Constraint.conj c{$l} c{$r})
  | `(c{ ∀ $x:ident : $b:ident . $hyp:term ⇒ $body:constr })
      => do let bty ← elabBaseTy b
            `(Constraint.imp $(quote x.getId) $bty $hyp c{$body})
  | `(c{ $p:term })
      =>  `(Constraint.pred $p)
  | `(c{ [ $e:constr ] }) => `(c{$e})
