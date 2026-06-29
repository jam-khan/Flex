#!/usr/bin/env python3
"""
Run `lake build` in a merged Lean project (produced by merge_projects.sh) and
collect timing/kappa/error statistics.

Writes lean_bench_log.txt (raw build log) and lean_bench.time (wall time in
ms) into this script's directory, and prints a summary to stdout.
"""

import re
import subprocess
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


# Matches the Lake build-status line, e.g.:
#   ✔ [12/300] Building AbstractRefinements.Test00.Flux.VC.Max (42ms)
#   ✖ [13/300] Building AbstractRefinements.Test00.User.Proof.MaxProof (234ms)
LAKE_MODULE_RE = re.compile(
    r"^([✔✖])\s+\[\d+/\d+\]\s+Building\s+([\w.]+)"
)

# Lean info/error lines carry the source file path:
#   info: AbstractRefinements/Test00/User/Proof/MaxProof.lean:30:4: [solve_fixpoint] ...
#   error: AbstractRefinements/Test00/User/Proof/MaxProof.lean:30:4: ...
LEAN_LINE_RE = re.compile(
    r"^(info|error|warning):\s+((\S+)/User/Proof/(\w+)Proof\.lean):\d+:\d+:\s+(.*)"
)

# Extract VC key from a proof path: "<cat>/<test>/<VCName>"
PROOF_MODULE_RE = re.compile(r"([\w/]+)/User/Proof/(\w+)Proof")


def _vc_key_from_proof_path(path_str: str) -> str | None:
    """Return '<cat>/<test>/<VCName>' from a proof file path or module name."""
    m = PROOF_MODULE_RE.search(path_str)
    if m:
        return f"{m.group(1)}/{m.group(2)}"
    return None


def run_lake_build(merged_dir: Path):
    """Run lake build in merged_dir; return (returncode, wall_ms, stdout_lines)."""
    try:
        t0 = time.monotonic()
        result = subprocess.run(
            ["lake", "build"], cwd=merged_dir,
            capture_output=True, text=True, timeout=3600,
        )
        wall_ms = int((time.monotonic() - t0) * 1000)
        return result.returncode, wall_ms, result.stdout.splitlines()
    except subprocess.TimeoutExpired:
        return 1, 3_600_000, ["error: lake build timed out (1 hour)"]
    except FileNotFoundError:
        return 1, 0, ["error: lake command not found"]
    except Exception as e:
        return 1, 0, [f"error: {e}"]


def parse_merged_output(lines: list[str]) -> dict:
    """
    Parse raw `lake build` stdout from a merged project.

    Returns a dict keyed by '<cat>/<test>/<VCName>' with:
      {
        "failed": bool,
        "acyclic": list[str],
        "cyclic": list[str],
        "fusion_acyclic": bool,
        "time_ms": int,
        "kappa_lines": list[str],
        "time_lines": list[str],
      }
    """
    vcs: dict[str, dict] = {}

    def _get(key: str) -> dict:
        if key not in vcs:
            vcs[key] = {
                "failed": False, "acyclic": [], "cyclic": [],
                "fusion_acyclic": False, "time_ms": 0,
                "kappa_lines": [], "time_lines": [],
            }
        return vcs[key]

    CYCLIC_BARE_RE = re.compile(r"^\[solve_fixpoint\] Cyclic κ:\s*\[([^\]]*)\]")
    failed_modules: set[str] = set()

    i = 0
    while i < len(lines):
        line = lines[i]

        # Lake module status line.
        mlm = LAKE_MODULE_RE.match(line)
        if mlm:
            status, module = mlm.group(1), mlm.group(2)
            if status == "✖":
                failed_modules.add(module)
            i += 1
            continue

        # Lean info/error/warning line.
        lm = LEAN_LINE_RE.match(line)
        if not lm:
            i += 1
            continue
        # group(1)=level, group(2)=full fpath, group(3)=test_path, group(4)=VCName, group(5)=message
        level, test_path, vc_name, message = lm.group(1), lm.group(3), lm.group(4), lm.group(5)

        key = f"{test_path}/{vc_name}"
        vc = _get(key)

        if level == "error":
            vc["failed"] = True
            i += 1
            continue

        if level != "info":
            i += 1
            continue

        if "[solve_fixpoint] Acyclic" in message:
            raw = re.search(r"κ:\s*\[([^\]]*)\]", message)
            acyclic = _items(raw.group(1)) if raw else []
            # Cyclic line immediately follows without an info: prefix.
            cyclic: list[str] = []
            if i + 1 < len(lines):
                cm = CYCLIC_BARE_RE.match(lines[i + 1])
                if cm:
                    cyclic = _items(cm.group(1))
                    i += 1
            vc["acyclic"].extend(acyclic)
            vc["cyclic"].extend(cyclic)
            vc["kappa_lines"].append(line)
            i += 1
            continue

        if "fusion: eliminated" in message:
            vc["fusion_acyclic"] = True
            vc["kappa_lines"].append(line)
            i += 1
            continue

        if "time: " in message:
            tm = re.search(r"time:\s*(\d+)ms", message)
            if tm:
                vc["time_ms"] += int(tm.group(1))
                vc["time_lines"].append(line)

        i += 1

    # Apply Lake-level failures from ✖ lines.
    for module in failed_modules:
        key = _vc_key_from_proof_path(module.replace(".", "/"))
        if key:
            _get(key)["failed"] = True

    return vcs


def main() -> None:
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <merged_lake_project_dir>", file=sys.stderr)
        sys.exit(1)

    merged_dir = Path(sys.argv[1]).resolve()
    if not merged_dir.is_dir():
        print(f"Error: '{merged_dir}' is not a directory", file=sys.stderr)
        sys.exit(1)

    log_path = SCRIPT_DIR / "lean_bench_log.txt"
    time_path = SCRIPT_DIR / "lean_bench.time"

    print(f"Building merged project: {merged_dir}")
    print("-" * 60, flush=True)

    returncode, wall_ms, lines = run_lake_build(merged_dir)

    log_path.write_text("\n".join(lines) + "\n")

    vcs = parse_merged_output(lines)
    failed_vcs = [k for k, v in vcs.items() if v["failed"]]

    time_path.write_text(f"{wall_ms}\n")

    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total VCs seen:   {len(vcs)}")
    print(f"Failed VCs:       {len(failed_vcs)}")
    print(f"lake build time:  {wall_ms / 1000:.1f}s")
    if failed_vcs:
        print("\nFailed VCs:")
        for n in sorted(failed_vcs):
            print(f"  - {n}")
    sys.exit(1 if (returncode != 0 or failed_vcs) else 0)


if __name__ == "__main__":
    main()
