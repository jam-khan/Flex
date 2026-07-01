#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo $SCRIPT_DIR

DIRS=(
    flux_demo_lean_proofs
    vecdeque_lean_proofs
    pldi_lean_proofs
    wave_lean_proofs
)

# Build each of the flux-wick benchmark suites
for dir in "${DIRS[@]}"; do
    log="$SCRIPT_DIR/${dir}.log"
    time_file="$SCRIPT_DIR/${dir}.time"

    : >"$log"  # truncate log before each run

    echo "==> Running lake update in $dir"
    (cd "$SCRIPT_DIR/../$dir" && lake update) >>"$log" 2>&1 || echo "lake update failed (exit $?)" >>"$log"

    echo "==> Running lake clean in $dir"
    (cd "$SCRIPT_DIR/../$dir" && lake clean) >>"$log" 2>&1 || echo "lake clean failed (exit $?)" >>"$log"

    echo "==> Running lake build in $dir (output -> ${dir}.log, time -> ${dir}.time)"
    start=$(date +%s%N)
    (cd "$SCRIPT_DIR/../$dir" && lake build) >>"$log" 2>&1 || echo "lake build failed (exit $?)" >>"$log"
    end=$(date +%s%N)
    elapsed_ms=$(( (end - start) / 1000000 ))
    printf "%d\n" "$elapsed_ms" >"$time_file"
done

# Build the merged flux tests suites (lean_bench)
python3 "${SCRIPT_DIR}/run_merged_suite.py" "${SCRIPT_DIR}/../lean_bench_merged" || true

# Build the liquid-fixpoint suite
python3 "${SCRIPT_DIR}/../../scripts/run_benchmarks.py" || true

# Generate the summary tables (markdown + LaTeX) into tables.md / tables.tex
python3 "${SCRIPT_DIR}/make_table.py" --format both
