import Demo.Basic

/-!
# Hypothesis: deterministic Zap vs. proof search

Both columns prove the *same* `∃κ. Horn-constraint` goals from `Demo.Basic`.

* `_zap`    — the deterministic Zap algorithm: `fusion` emits a search-free
              proof term (the And/Or mirror), leaving only κ-free arithmetic
              residuals, then *plain* `grind` discharges each.
* `_search` — pure proof search: `grind` alone, which must itself invent the
              κ-witness predicates.

Every goal uses `first | <closer> | sorry`, so the file always compiles and a
`declaration uses 'sorry'` warning marks exactly where the closer failed.
`set_option profiler true` reports elaboration time per command.
-/

set_option profiler true

-- ───────────────── Deterministic Zap: fusion + plain grind ─────────────────

theorem ex1_zap  : ex1  := by unfold ex1;  fusion <;> all_goals (first | grind | sorry)
theorem ex4_zap  : ex4  := by unfold ex4;  fusion <;> all_goals (first | grind | sorry)
theorem ex7_zap  : ex7  := by unfold ex7;  fusion <;> all_goals (first | grind | sorry)
theorem ex11_zap : ex11 := by unfold ex11; fusion <;> all_goals (first | grind | sorry)

set_option maxHeartbeats 1600000 in
theorem ex13_zap : ex13 := by unfold ex13; fusion <;> all_goals (first | grind | sorry)

set_option maxHeartbeats 1600000 in
theorem ex_stress_zap : ex_stress := by
  unfold ex_stress; fusion <;> all_goals (first | grind | sorry)

-- ───────────────── Pure proof search: grind alone ─────────────────

set_option maxHeartbeats 400000 in
theorem ex1_search  : ex1  := by unfold ex1;  first | grind | sorry

set_option maxHeartbeats 400000 in
theorem ex4_search  : ex4  := by unfold ex4;  first | grind | sorry

set_option maxHeartbeats 400000 in
theorem ex7_search  : ex7  := by unfold ex7;  first | grind | sorry

set_option maxHeartbeats 400000 in
theorem ex11_search : ex11 := by unfold ex11; first | grind | sorry

set_option maxHeartbeats 400000 in
theorem ex13_search : ex13 := by unfold ex13; first | grind | sorry

set_option maxHeartbeats 400000 in
theorem ex_stress_search : ex_stress := by unfold ex_stress; first | grind | sorry
