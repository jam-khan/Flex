#!/usr/bin/env python3
"""Run all Liquid-fixpoint benchmarks and save output to lf_bench.log.

Runs `lake update` once before starting, then `lake env lean <file>` for each
benchmark.  Per-file elapsed times are summed and written to lf_bench.time.

Log format (same style as flux/tools/runlean.py):
  [N/M] Building: filename.lean ... OK|ERROR
      <indented stdout+stderr lines>

Usage:
    python3 scripts/run_benchmarks.py
    python3 scripts/run_benchmarks.py --jobs 4
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

REPO_ROOT  = Path(__file__).resolve().parent.parent
BENCH_DIR  = REPO_ROOT / "Benchmarks" / "Liquid-fixpoint"
LOG_PATH   = REPO_ROOT / "lf_bench.log"
TIME_PATH  = REPO_ROOT / "lf_bench.time"


def run_file(path: Path) -> tuple[Path, bool, str, int]:
    t0 = time.monotonic()
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=300,
    )
    elapsed_ms = int((time.monotonic() - t0) * 1000)
    output = proc.stdout + proc.stderr
    success = proc.returncode == 0 and "error:" not in output
    return path, success, output, elapsed_ms


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=1,
                    help="parallel lean processes (default: 1)")
    args = ap.parse_args()

    files = sorted(BENCH_DIR.glob("*.lean"))
    if not files:
        print(f"No .lean files found in {BENCH_DIR}", file=sys.stderr)
        sys.exit(1)

    print("Running lake update...")
    subprocess.run(["lake", "update"], cwd=REPO_ROOT, check=False)

    n = len(files)
    print(f"Running {n} benchmarks with {args.jobs} job(s)...")

    results: dict[Path, tuple[bool, str, int]] = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futures = {ex.submit(run_file, f): f for f in files}
        done = 0
        for fut in as_completed(futures):
            path, success, output, elapsed_ms = fut.result()
            results[path] = (success, output, elapsed_ms)
            done += 1
            tag = "OK" if success else "ERROR"
            print(f"  [{done}/{n}] {path.name} ... {tag} ({elapsed_ms}ms)", flush=True)

    total_ms = sum(r[2] for r in results.values())

    with LOG_PATH.open("w") as log:
        for i, path in enumerate(files, 1):
            success, output, _ = results[path]
            tag = "OK" if success else "ERROR"
            log.write(f"[{i}/{n}] Building: {path.name} ... {tag}\n")
            for line in output.splitlines():
                log.write(f"    {line}\n")

    TIME_PATH.write_text(f"{total_ms}\n")

    print(f"\nLog saved to {LOG_PATH}")
    print(f"Total time: {total_ms / 1000:.1f}s  (saved to {TIME_PATH})")


if __name__ == "__main__":
    main()
