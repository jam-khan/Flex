# Lean-Fixpoint

A Lean 4 library implementing a fixpoint-based constraint solving framework with predicate abstraction, fusion algorithms, and meta-programming support for refinement types.

> ⚠️ This is a private repository. You must be a collaborator to use it as a dependency.

---

## Using as a Dependency

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) installed via `elan`
- Access to this private GitHub repository

### Step 1 — Add to your `lakefile.toml`

```toml
[[require]]
name = "LeanFixpoint"
git = "https://github.com/jam-khan/lean-fixpoint"
rev = "main"
```

### Step 2 — Fetch the dependency

```bash
lake update
```

This clones the repo into `.lake/packages/LeanFixpoint/` using your local Git credentials.

### Step 3 — Build

```bash
lake build
```

> **Note:** The first build pulls in `mathlib` transitively, which can take a while. Run `lake exe cache get` beforehand to download prebuilt mathlib `.olean` files and skip most of the wait.

---

## Importing

A single import gives you everything:

```lean4
import LeanFixpoint
```

This includes all core types, tactics, elaboration, and the solver.

### Example

```lean4
import LeanFixpoint

def ex1 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
```

See the [`Demo/`](./Demo/Basic.lean) folder for more worked examples.

---

## Module Overview

| Module | Description |
|---|---|
| `LeanFixpoint.Core.Types` | Core AST for constraints |
| `LeanFixpoint.Core.Macros` | Custom Lean macros |
| `LeanFixpoint.Core.Pretty` | Pretty printing |
| `LeanFixpoint.Core.Fusion` | Fusion algorithm |
| `LeanFixpoint.Elab.ToExpr` | Elaboration → Lean `Expr` |
| `LeanFixpoint.Elab.FromExpr` | Lean `Expr` → constraint AST |
| `LeanFixpoint.Tactic.SolveFixpoint` | Main tactic for discharging VCs |
| `LeanFixpoint.Tactic.Tactics` | Additional tactics |
| `LeanFixpoint.Tactic.Grind` | Grind integration |
| `LeanFixpoint.Solve.Solver` | Fixpoint solver |
| `LeanFixpoint.Solve.Qualifier` | Qualifier / predicate AST |

