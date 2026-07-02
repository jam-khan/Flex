import LeanFixpoint.VCG.While.Types
import LeanFixpoint.VCG.While.Semantics

/-! # Surface Syntax for While Programs

  Provides `<| ... |>` notation for writing While programs in an
  imperative style.  All identifiers in expressions are treated as
  program variables and compiled to state lookups `s "name"`.

  Grammar:
  ```
  expr  ::= ident | numeral | (expr) | -expr
           | expr * expr | expr + expr | expr - expr
  guard ::= expr < expr | expr ≤ expr | expr > expr | expr ≥ expr
           | expr = expr | expr ≠ expr | expr != expr
  cmd   ::= noop
           | ident := expr
           | (cmd)
           | cmd ; cmd
           | while guard do cmd          -- body is a single cmd; wrap in (…) for sequences
           | if guard then cmd else cmd
  ```

  Examples:
  ```lean
  <| x := 0 ; while x < n do x := x + 1 |>

  <| x := n ; y := 0 ;
     while x != 0 do (x := x - 1 ; y := y + 1) |>
  ```
-/

declare_syntax_cat whileExpr
declare_syntax_cat whileGuard
declare_syntax_cat whileCmd

-- Expressions
syntax:max "(" whileExpr ")"             : whileExpr
syntax:max ident                         : whileExpr
syntax:max num                           : whileExpr
syntax:max "-" whileExpr:max             : whileExpr
syntax:70 whileExpr:70 " * " whileExpr:71 : whileExpr
syntax:65 whileExpr:65 " + " whileExpr:66 : whileExpr
syntax:65 whileExpr:65 " - " whileExpr:66 : whileExpr

-- Guards
syntax whileExpr " < "  whileExpr : whileGuard
syntax whileExpr " ≤ "  whileExpr : whileGuard
syntax whileExpr " > "  whileExpr : whileGuard
syntax whileExpr " ≥ "  whileExpr : whileGuard
syntax whileExpr " = "  whileExpr : whileGuard
syntax whileExpr " ≠ "  whileExpr : whileGuard
syntax whileExpr " != " whileExpr : whileGuard

-- Commands
-- Note: the body of `while`/`if` is a single cmd:max.
-- Use (…) to group sequences, e.g. `while g do (c₁ ; c₂)`.
syntax:max "noop"                                              : whileCmd
syntax:max ident " := " whileExpr                             : whileCmd
syntax:max "(" whileCmd ")"                                   : whileCmd
syntax:10  whileCmd:11 " ; " whileCmd:10                      : whileCmd
syntax:20  "while " whileGuard " do " whileCmd:max            : whileCmd
syntax:20  "if " whileGuard " then " whileCmd:max
           " else " whileCmd:max                              : whileCmd

-- Top-level bracket
syntax (name := whileProg) "<|" whileCmd "|>" : term

/-! ## Elaboration via MacroM helpers -/

open Lean in
private partial def eExpr (e : TSyntax `whileExpr) : MacroM (TSyntax `term) := do
  match e with
  | `(whileExpr| ($inner:whileExpr))              => eExpr inner
  | `(whileExpr| $x:ident)                        => `(s $(Lean.quote x.getId.toString))
  | `(whileExpr| $n:num)                          => `(($n : Int))
  | `(whileExpr| -$inner:whileExpr)               => do let t ← eExpr inner; `(-$t)
  | `(whileExpr| $a:whileExpr * $b:whileExpr)     => do let a' ← eExpr a; let b' ← eExpr b; `($a' * $b')
  | `(whileExpr| $a:whileExpr + $b:whileExpr)     => do let a' ← eExpr a; let b' ← eExpr b; `($a' + $b')
  | `(whileExpr| $a:whileExpr - $b:whileExpr)     => do let a' ← eExpr a; let b' ← eExpr b; `($a' - $b')
  | _ => Macro.throwUnsupported

open Lean in
private partial def eGuard (g : TSyntax `whileGuard) : MacroM (TSyntax `term) := do
  match g with
  | `(whileGuard| $a:whileExpr <  $b:whileExpr) => do let a' ← eExpr a; let b' ← eExpr b; `($a' < $b')
  | `(whileGuard| $a:whileExpr ≤  $b:whileExpr) => do let a' ← eExpr a; let b' ← eExpr b; `($a' ≤ $b')
  | `(whileGuard| $a:whileExpr >  $b:whileExpr) => do let a' ← eExpr a; let b' ← eExpr b; `($a' > $b')
  | `(whileGuard| $a:whileExpr ≥  $b:whileExpr) => do let a' ← eExpr a; let b' ← eExpr b; `($a' ≥ $b')
  | `(whileGuard| $a:whileExpr =  $b:whileExpr) => do let a' ← eExpr a; let b' ← eExpr b; `($a' = $b')
  | `(whileGuard| $a:whileExpr ≠  $b:whileExpr) => do let a' ← eExpr a; let b' ← eExpr b; `($a' ≠ $b')
  | `(whileGuard| $a:whileExpr != $b:whileExpr) => do let a' ← eExpr a; let b' ← eExpr b; `($a' != $b')
  | _ => Macro.throwUnsupported

open Lean in
private partial def eCmd (c : TSyntax `whileCmd) : MacroM (TSyntax `term) := do
  match c with
  | `(whileCmd| noop)                                    => `(Cmd.skip)
  | `(whileCmd| ($inner:whileCmd))                       => eCmd inner
  | `(whileCmd| $x:ident := $e:whileExpr)                => do
      let body ← eExpr e
      `(Cmd.assign $(Lean.quote x.getId.toString) (fun s => $body))
  | `(whileCmd| $c₁:whileCmd ; $c₂:whileCmd)            => do
      let t₁ ← eCmd c₁; let t₂ ← eCmd c₂; `(Cmd.seq $t₁ $t₂)
  | `(whileCmd| while $g:whileGuard do $body:whileCmd)   => do
      let gt ← eGuard g; let bt ← eCmd body
      `(Cmd.cwhile (fun s => $gt) $bt)
  | `(whileCmd| if $g:whileGuard then $c₁:whileCmd else $c₂:whileCmd) => do
      let gt ← eGuard g; let t₁ ← eCmd c₁; let t₂ ← eCmd c₂
      `(Cmd.ite (fun s => $gt) $t₁ $t₂)
  | _ => Macro.throwUnsupported

macro_rules
  | `(<| $c |>) => eCmd c

/-! ## Hoare Triple Notation `|- P -| cmd |- Q -|`

  Propositions may use the same variable names as While programs; each
  identifier is elaborated to a state lookup `s "name"`.

  Grammar:
  ```
  prop ::= ⊤ | ⊥
         | prop ∧ prop | prop ∨ prop | ¬ prop | prop → prop
         | whileExpr = whileExpr | whileExpr ≠ whileExpr | whileExpr != whileExpr
         | whileExpr < whileExpr | whileExpr ≤ whileExpr
         | whileExpr > whileExpr | whileExpr ≥ whileExpr
  ```

  Example:
  ```lean
  |- x = 0 -| <| x := x + 1 |> |- x = 1 -|
  ```
-/

declare_syntax_cat whileProp

-- Atoms (use ⊤/⊥ to avoid conflict with Lean's term-level True/False)
syntax "⊤"                                            : whileProp
syntax "⊥"                                            : whileProp

-- Comparisons (Prop-valued)
syntax:50 whileExpr " = "  whileExpr                 : whileProp
syntax:50 whileExpr " ≠ "  whileExpr                 : whileProp
syntax:50 whileExpr " != " whileExpr                 : whileProp
syntax:50 whileExpr " < "  whileExpr                 : whileProp
syntax:50 whileExpr " ≤ "  whileExpr                 : whileProp
syntax:50 whileExpr " > "  whileExpr                 : whileProp
syntax:50 whileExpr " ≥ "  whileExpr                 : whileProp

-- Connectives
syntax:40 "¬ " whileProp:41                           : whileProp
syntax:35 whileProp:36 " ∧ " whileProp:35             : whileProp
syntax:30 whileProp:31 " ∨ " whileProp:30             : whileProp
syntax:20 whileProp:21 " → " whileProp:20             : whileProp

open Lean in
private partial def eProp (p : TSyntax `whileProp) : MacroM (TSyntax `term) := do
  match p with
  | `(whileProp| ⊤)                                 => `(True)
  | `(whileProp| ⊥)                                 => `(False)
  | `(whileProp| $a:whileExpr =  $b:whileExpr)      => do let a' ← eExpr a; let b' ← eExpr b; `($a' = $b')
  | `(whileProp| $a:whileExpr ≠  $b:whileExpr)      => do let a' ← eExpr a; let b' ← eExpr b; `($a' ≠ $b')
  | `(whileProp| $a:whileExpr != $b:whileExpr)      => do let a' ← eExpr a; let b' ← eExpr b; `($a' ≠ $b')
  | `(whileProp| $a:whileExpr <  $b:whileExpr)      => do let a' ← eExpr a; let b' ← eExpr b; `($a' < $b')
  | `(whileProp| $a:whileExpr ≤  $b:whileExpr)      => do let a' ← eExpr a; let b' ← eExpr b; `($a' ≤ $b')
  | `(whileProp| $a:whileExpr >  $b:whileExpr)      => do let a' ← eExpr a; let b' ← eExpr b; `($a' > $b')
  | `(whileProp| $a:whileExpr ≥  $b:whileExpr)      => do let a' ← eExpr a; let b' ← eExpr b; `($a' ≥ $b')
  | `(whileProp| ¬ $q:whileProp)                    => do let q' ← eProp q; `(¬ $q')
  | `(whileProp| $p:whileProp ∧ $q:whileProp)       => do let p' ← eProp p; let q' ← eProp q; `($p' ∧ $q')
  | `(whileProp| $p:whileProp ∨ $q:whileProp)       => do let p' ← eProp p; let q' ← eProp q; `($p' ∨ $q')
  | `(whileProp| $p:whileProp → $q:whileProp)       => do let p' ← eProp p; let q' ← eProp q; `($p' → $q')
  | _ => Macro.throwUnsupported

syntax (name := hoareTriple) "{|" whileProp "|}" term:max "{|" whileProp "|}" : term

open Lean in
macro_rules
  | `({| $p:whileProp |} $c:term {| $q:whileProp |}) => do
      let p' ← eProp p
      let q' ← eProp q
      `(ValidHoareTriple (fun s => $p') $c (fun s => $q'))
