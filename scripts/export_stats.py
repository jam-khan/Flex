#!/usr/bin/env python3
"""Parse lf_bench.log and export per-benchmark stats as JSON.

Each Liquid-fixpoint .lean file is treated as one VC (no trivial concept).
Classification is based on solve_fixpoint kappa output.
Failure is determined by 'error:' lines or an ERROR build status.

Output (to stdout):
    JSON array of suite objects:
    [{"suite": "Liquid-fixpoint", "vcs": [{"name": ..., "trivial": false,
                                            "kappa": ..., "failed": ...}]}]

Usage:
    python3 scripts/export_stats.py
    python3 scripts/export_stats.py path/to/lf_bench.log
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from kappa_classify import parse_invocations, classify  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LOG = REPO_ROOT / "lf_bench.log"

BUILDING_RE = re.compile(r"^\[(\d+)/(\d+)\] Building: (.+?) \.\.\. (OK|ERROR)$")


def parse_log(text: str) -> list[dict]:
    """Return list of {name, failed, kappa} for each benchmark file."""
    chunks: list[tuple[str, bool, str]] = []
    current_name: str | None = None
    current_lines: list[str] = []
    current_failed: bool = False

    for line in text.splitlines():
        m = BUILDING_RE.match(line)
        if m:
            if current_name is not None:
                chunks.append((current_name, current_failed, "\n".join(current_lines)))
            current_name = m.group(3)
            current_failed = m.group(4) == "ERROR"
            current_lines = []
        else:
            current_lines.append(line)

    if current_name is not None:
        chunks.append((current_name, current_failed, "\n".join(current_lines)))

    results = []
    for name, failed, chunk in chunks:
        invocations = parse_invocations(chunk)
        # If any invocation has kappa, use the most complex classification.
        # Files with no invocations get "none".
        kappa = "none"
        for acyclic, cyclic in invocations:
            label = classify(acyclic, cyclic)
            if label == "both":
                kappa = "both"
                break
            if label == "cyclic_only" and kappa != "both":
                kappa = "cyclic_only"
            elif label == "acyclic_only" and kappa not in ("both", "cyclic_only"):
                kappa = "acyclic_only"

        # Also treat as failed if there are explicit error: lines in the chunk.
        if not failed and re.search(r"\berror:", chunk):
            failed = True

        # Strip .lean suffix from name for display.
        stem = Path(name).stem if name.endswith(".lean") else name

        results.append({"name": stem, "trivial": False, "kappa": kappa, "failed": failed})

    return results


def read_time_ms(time_path: Path) -> int | None:
    try:
        return int(time_path.read_text().strip())
    except Exception:
        return None


def main() -> None:
    log_path  = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_LOG
    time_path = log_path.with_suffix(".time")

    if not log_path.exists():
        print(f"error: log not found: {log_path}", file=sys.stderr)
        print(f"Run:  python3 {Path(__file__).parent}/run_benchmarks.py", file=sys.stderr)
        sys.exit(1)

    text = log_path.read_text(encoding="utf-8", errors="replace")
    vcs = parse_log(text)
    time_ms = read_time_ms(time_path)

    suite: dict = {"suite": "Liquid-fixpoint", "vcs": vcs}
    if time_ms is not None:
        suite["time_ms"] = time_ms

    print(json.dumps([suite], indent=2))


if __name__ == "__main__":
    main()
