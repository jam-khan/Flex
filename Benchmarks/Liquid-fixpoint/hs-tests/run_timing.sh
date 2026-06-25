#!/usr/bin/env bash
# Run fixpoint on every test file in this directory and write the total
# elapsed time (ms) to hsf_bench.time, next to lf_bench.time in the repo root.
set -u

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$DIR/../../.." && pwd)"
OUT="$REPO_ROOT/hsf_bench.time"
FIXPOINT="${FIXPOINT:-fixpoint}"

total_ms=0

for f in "$DIR"/*.smt2; do
  name="$(basename "$f")"
  start=$(date +%s.%N)
  "$FIXPOINT" "$f" > /dev/null 2>&1
  code=$?
  end=$(date +%s.%N)
  elapsed_ms=$(awk -v s="$start" -v e="$end" 'BEGIN{printf "%d", (e-s)*1000}')
  total_ms=$((total_ms + elapsed_ms))
  printf "%-45s %6dms  (exit %d)\n" "$name" "$elapsed_ms" "$code"
done

echo "$total_ms" > "$OUT"

echo
echo "Total time: $(awk -v ms="$total_ms" 'BEGIN{printf "%.1f", ms/1000}')s  (saved to $OUT)"
