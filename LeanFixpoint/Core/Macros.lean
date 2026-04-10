import Lean
import LeanFixpoint.Core.Types

open Lean

def elabBaseTy (id : TSyntax `ident) : MacroM (TSyntax `term) := do
  match id.getId with
  | `int  => `(BaseTy.int)
  | `bool => `(BaseTy.bool)
  | n     => Macro.throwError s!"Unknown base type: {n}, expected `int` or `bool`"

declare_syntax_cat pred

syntax "true"   : pred
syntax "false"  : pred
syntax "(" term ")" : pred

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
      => do let argTerms ← args.mapM fun a =>
              `(Lean.mkFVar { name := $(quote a.getId) })
            `(Pred.kapp $k [$argTerms,*])
  | `(p{ $l ∧ $r })
      => `(Pred.conj p{$l} p{$r})
  | `(p{ $l ∨ $r })
      => `(Pred.disj p{$l} p{$r})
  | `(p{ ∃ $x:ident : $b:ident . $body })
      => do let bty ← elabBaseTy b
            `(Pred.exist $(quote x.getId) $bty p{$body})
  | `(p{ ( $e:term ) })
      => `(Pred.rexpr $e)

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
