# Flex — Artifact

Artifact for **"Foundational Constraint Solving for Expressive Refinement Typing"**. Flex is a foundational CHC solver in Lean 4: CHCs are Lean propositions with existentially bound Horn variables (κ), and the solver tactics compute witnesses together with kernel-checked certificates. The artifact contains the solver (§4), the two verified CHC generators (§5), and the benchmark suites (§6).

## 1. Build

Requires [`elan`](https://github.com/leanprover/elan); the pinned toolchain (`leanprover/lean4:v4.29.0-rc8`, [lean-toolchain](lean-toolchain)) installs automatically.

The [Makefile](Makefile) builds everything:

```bash
make        # build Flex, then every rq1_case_studies/**/lean_proofs project
make clean  # lake clean in Flex and all case-study projects
```

`make` first builds the Flex solver (root Lake project), then runs `lake build` inside each case-study proof project under [rq1_case_studies/](rq1_case_studies/) (each requires Flex via a path dependency, so order matters). Individual pieces: `make flex` (solver only), `make case-studies` (proofs only).

To build manually instead:

```bash
lake update
lake build
lake build Demo Tests
```

## 2. Solver tactics (paper §4)

| Paper | Tactic | Defined at |
|---|---|---|
| **Zap** (§4.2) | `zap` (alias `fusion`) | [Fusion.lean:33](Flex/Tactic/Tactics/Fusion.lean#L33) |
| **Fix** (§4.4) | `fix` = `pa_cert; try grind` | [PaCert.lean:94](Flex/Tactic/Tactics/PaCert.lean#L94) |
| full pipeline (§6.3) | `solve` (alias `solve_fixpoint`) | [SolveFixpoint.lean:185](Flex/Tactic/Tactics/SolveFixpoint.lean#L185) |

- **Zap**: §4.1 partitioning → [Fusion/Graph.lean](Flex/Fusion/Graph.lean); Fig. 10 (`Scope`, `Sol`, `Elim`, `Red`) → [Fusion/Scope.lean](Flex/Fusion/Scope.lean), [Sol1.lean](Flex/Fusion/Sol1.lean), [StripPres.lean](Flex/Fusion/StripPres.lean), [Elim.lean](Flex/Fusion/Elim.lean); Fig. 12 certificates (`Cert`, `Nav`) → [Zap/Emit.lean](Flex/Zap/Emit.lean), [Zap/Nav.lean](Flex/Zap/Nav.lean).
- **Fix** (Fig. 13): qualifiers are `@[qualif]`-tagged defs (paper: `@[qual]`) → [PA/Qualifier.lean](Flex/PA/Qualifier.lean); `Init` → [Instantiation.lean](Flex/PA/Instantiation.lean); `Weaken`/`Fixpoint` → [Weaken.lean](Flex/PA/Weaken.lean), [Fixpoint.lean](Flex/PA/Fixpoint.lean); `Oracle` (grind/aesop, rejects `sorry`) → [Check.lean](Flex/PA/Check.lean); `Cert_θ` → [Cert.lean](Flex/PA/Cert.lean).
- **solve**: partition, `zap` the acyclic κ's, predicate abstraction on the cyclic ones, close the residual VC with `grind`/`aesop`/`omega`/`bv_decide`/`native_decide`.

Full tactic reference: [docs/TACTICS.md](docs/TACTICS.md). Demos: [Demo/](Demo/).

## 3. `generate`: CHC generation (paper §5)

Both macros apply the verified generator-soundness theorem, then normalize the goal into the Fig. 8 grammar:

- **Imp**: `generate` = `imp_vc_sound; reify` ([While/Tactics.lean:311](Flex/VCG/While/Tactics.lean#L311)) — applies `whileCHC_sound`.
- **λRK**: `generate` = `vc_generate; vc_reify` ([STLC/Examples.lean:102](Flex/VCG/STLC/Examples.lean#L102), components in [MakeHornUnderK.lean](Flex/VCG/STLC/MakeHornUnderK.lean)) — applies `check_sound`, reifies the κ-environment.

## 4. Mechanization (paper §5)

**Imp (§5.1)** — [Flex/VCG/While/](Flex/VCG/While/), shallow embedding (`State = CVar → Int`; expressions/guards/assertions are state functions):

| Paper | Lean |
|---|---|
| syntax (Fig. 14) | `Cmd` — [Types.lean:21](Flex/VCG/While/Types.lean#L21) |
| big-step semantics | `Ceval` — [Semantics.lean:5](Flex/VCG/While/Semantics.lean#L5) |
| ⊨ {P} c {Q} | `ValidHoareTriple` (`⊧`) — [Semantics.lean:43](Flex/VCG/While/Semantics.lean#L43) |
| Floyd–Hoare rules | [Hoare.lean](Flex/VCG/While/Hoare.lean) |
| VC(P, c, Q), fresh κ per `while` | `vcGen`, `whileCHC` — [CHC.lean:26](Flex/VCG/While/CHC.lean#L26), [:54](Flex/VCG/While/CHC.lean#L54) |

**λRK (§5.2–5.4)** — [Flex/VCG/STLC/](Flex/VCG/STLC/), deep embedding, locally-nameless binders, stratified first-order refinement language:

| Paper | Lean |
|---|---|
| syntax (Fig. 15) | `Term`/`Formula`/`Refinement` — [Syntax.lean:58](Flex/VCG/STLC/Syntax.lean#L58)/[:77](Flex/VCG/STLC/Syntax.lean#L77)/[:98](Flex/VCG/STLC/Syntax.lean#L98); `Ty` — [:157](Flex/VCG/STLC/Syntax.lean#L157); `Exp` — [:168](Flex/VCG/STLC/Syntax.lean#L168) |
| K-assignment | `KEnv` — [Syntax.lean:112](Flex/VCG/STLC/Syntax.lean#L112) |
| e ⇓ v (CBV, big-step) | `BigStep` — [Semantics.lean:16](Flex/VCG/STLC/Semantics.lean#L16) |
| ⟦t⟧, ⟦φ⟧, ⟦r⟧; v ∈ ⟦τ⟧ | `Term.interp`/`Formula.interp`/`Refinement.interp`; `TyDenote` — [Model.lean:45](Flex/VCG/STLC/Model.lean#L45) |
| Γ ⊢_K e : τ (§5.3) | `Hastype` — [Declarative.lean:8](Flex/VCG/STLC/Declarative.lean#L8) |
| declarative subtyping, bidirectional relations | `Subtyp`, `Synth`/`Check` — [Typing.lean:23](Flex/VCG/STLC/Typing.lean#L23)/[:45](Flex/VCG/STLC/Typing.lean#L45) |
| Γ ⊢ e ⇒/⇐ τ ⇝ c (§5.4); closed top-level CHC | `sub`/`synth`/`check` — [VCGen.lean:33](Flex/VCG/STLC/VCGen.lean#L33)/[:58](Flex/VCG/STLC/VCGen.lean#L58)/[:101](Flex/VCG/STLC/VCGen.lean#L101); `topVC` — [:153](Flex/VCG/STLC/VCGen.lean#L153) |

## 5. Paper examples

- **Fig. 5 (Imp, `fibLoop`)** = `fibLoop_correct` — [While/CHC.lean:157](Flex/VCG/While/CHC.lean#L157). Same program, pre `s "n" = n ∧ n ≥ 2`, post `s "x" = fib_spec n`; `fib` = `fib_spec` ([:148](Flex/VCG/While/CHC.lean#L148)); qualifiers `q1`/`q2` = `q_eq_fib`/`q_eq_fib_pred` ([:153–155](Flex/VCG/While/CHC.lean#L153-L155)). Proof: `generate; fix` (`fix` ends in `try grind`, matching the paper's `generate; fix; grind`).
- **Fig. 6 (λRK, `max`)** = `exMax` — [STLC/Examples.lean:184](Flex/VCG/STLC/Examples.lean#L184); checked application at [:194–208](Flex/VCG/STLC/Examples.lean#L194-L208), proof `generate; zap; grind`. The unknown return refinement κ(ν, y, x) is `IntK3 "k"`. Difference: the mechanized constants are `99`/`100` with goal type `{ν | ν = 100 ∨ ν = 99}`, vs. the paper's `6`/`7` and `{ν | ν = 7}`; the CHC structure is identical.

## 6. Theorem mapping (paper main body ↔ Lean)

| Paper | Lean theorem | Location |
|---|---|---|
| Thm 5.1 (VC-generation soundness, Imp) | `whileCHC_sound` (via `vcGen_sound`) | [While/CHC.lean:89](Flex/VCG/While/CHC.lean#L89) ([:60](Flex/VCG/While/CHC.lean#L60)) |
| Thm 5.2 (type soundness, λRK) | `type_safety` (via `hastype_fundamental`, `subtyp_sound`) | [STLC/Safety.lean:1042](Flex/VCG/STLC/Safety.lean#L1042) ([:776](Flex/VCG/STLC/Safety.lean#L776), [:721](Flex/VCG/STLC/Safety.lean#L721)) |
| Thm 5.3 (constraint generation) | `check_decl_sound` (mutual `sub_sound`/`synth_sound`/`check_sound`) | [STLC/Soundness.lean:494](Flex/VCG/STLC/Soundness.lean#L494) ([:35](Flex/VCG/STLC/Soundness.lean#L35)/[:95](Flex/VCG/STLC/Soundness.lean#L95)/[:178](Flex/VCG/STLC/Soundness.lean#L178)) |
| Thm 5.4 (verifier soundness) | `vcgen_safety` = `type_safety` ∘ `topVC_decl_sound` | [STLC/Safety.lean:1057](Flex/VCG/STLC/Safety.lean#L1057) |
| Thms 4.1–4.4 (Zap/Fix correctness) | none, by design — see below | [Flex/Zap/](Flex/Zap/), [PA/Cert.lean](Flex/PA/Cert.lean) |

Theorems 4.1–4.4 are meta-theorems about the solver algorithms, proved in the paper's appendices. Their soundness halves (4.2, 4.3) are enforced per invocation instead: `zap`/`fix` emit a certificate of type `c′ → c` that the kernel re-checks on every run, so no result depends on the algorithms being correct. The completeness halves (4.1, 4.4) concern solution quality, not soundness, and are paper-only.
