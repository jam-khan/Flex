# Flex

A Lean 4 library for a constraint-solving framework for Constrained Horn Clauses (CHCs).

> ⚠️ This is a private repository. You must be a collaborator to use it as a dependency.

---

## Using as a Dependency

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) installed via `elan`
- Access to this private GitHub repository

### Step 1 — Add to your `lakefile.toml`

```toml
[[require]]
name = "Flex"
git = "https://github.com/jam-khan/Flex"
rev = "main"
```

### Step 2 — Fetch the dependency

```bash
lake update
```

This clones the repo into `.lake/packages/Flex/` using your local Git credentials.

### Step 3 — Build

```bash
lake build
```

> **Note:** Flex is mathlib-free — the only dependency is `aesop` (built from source on the first build).

---

## Importing

A single import gives you everything:

```lean4
import Flex
```

This includes all core types, tactics, elaboration, and the solver.

### Example

```lean4
import Flex

def ex1 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
```

See the [`Demo/`](./Demo/Basic.lean) folder for more worked examples.
