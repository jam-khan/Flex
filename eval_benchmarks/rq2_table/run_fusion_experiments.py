#!/usr/bin/env python3
"""RQ2 fusion-experiment runner.

For each VC with ≥1 acyclic κ, measures acyclic-κ elimination cost under
three tactics (leaving residuals as `all_goals sorry`):

  zap   = fusion               (deterministic Zap proof term)
  grind = fusion_grind         (κ-head clauses via grind)
  aesop = fusion_aesop         (κ-head clauses via aesop)

Suites (fixed):
  flux-medium      — flux-demo + kani-vecdeque + pldi23 (logs from rq3_table/)
  liquid-fixpoint  — handled separately by make_rq2_table.py via --lf-results
  hashtable        — hashtable_lean_proofs/lean_proofs.log
  sorting          — flux_lean_demo_lean_proofs/lean_proofs.log

Results are written to rq2_results.json.

Usage:
    python3 run_fusion_experiments.py
    python3 run_fusion_experiments.py --jobs 4
    python3 run_fusion_experiments.py --filter BucketMap
    python3 run_fusion_experiments.py --append
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))
from kappa_classify import parse_log_kappa  # noqa: E402

# ── paths ─────────────────────────────────────────────────────────────────────

SCRIPT_DIR = Path(__file__).parent.resolve()
EVAL_DIR   = SCRIPT_DIR.parent
LF_ROOT    = EVAL_DIR.parent
RQ3_TABLE  = EVAL_DIR / "rq3_table"
PRELUDE    = LF_ROOT / "eval" / "Rq3Bench.lean"

# (suite_name, lean_proofs_dir, log_path)
SUITES: list[tuple[str, Path, Path]] = [
    # flux-medium: three sub-suites reported under one name
    ("flux-medium", EVAL_DIR / "flux_demo_lean_proofs",    RQ3_TABLE / "flux_demo_lean_proofs.log"),
    ("flux-medium", EVAL_DIR / "vecdeque_lean_proofs",     RQ3_TABLE / "vecdeque_lean_proofs.log"),
    ("flux-medium", EVAL_DIR / "pldi_lean_proofs",         RQ3_TABLE / "pldi_lean_proofs.log"),
    # hashtable
    ("hashtable", EVAL_DIR / "hashtable_lean_proofs",      EVAL_DIR / "hashtable_lean_proofs" / "lean_proofs.log"),
    # sorting (flux-to-lean-demo)
    ("sorting",   EVAL_DIR / "flux_lean_demo_lean_proofs", EVAL_DIR / "flux_lean_demo_lean_proofs" / "lean_proofs.log"),
]

CONFIGS = [
    ("zap",   "fusion"),
    ("grind", "fusion_grind"),
    ("aesop", "fusion_aesop"),
]

# ── regexes ───────────────────────────────────────────────────────────────────

PROOF_DEF_RE = re.compile(
    r"(?m)^set_option maxHeartbeats \d+\n(?:#time\s+)?def (\w+)\s*:\s*(\w+)\s*:=\s*by\b"
)
BL2_RE = re.compile(
    r"BENCHLINE2\s+(\S+)\s+status=(\S+)\s+hb=(\d+)\s+ms=(\d+)\s+"
    r"depth=(\d+)\s+nconst=(\d+)\s+kerus=(\d+)"
)
PHASE_RE = re.compile(r"\[phase\]\s+(\w+):(\w+)=(\d+)")


# ── prelude ───────────────────────────────────────────────────────────────────

def prelude_body() -> str:
    lines = PRELUDE.read_text().splitlines()
    return "\n".join(l for l in lines if not l.startswith("import"))


# ── acyclic-κ detection ───────────────────────────────────────────────────────

def acyclic_vcs_from_log(log_text: str) -> set[str]:
    """VCs with >=1 acyclic κ to eliminate, per fusion's Start/End κ logging
    (see kappa_classify.parse_log_kappa)."""
    kappa = parse_log_kappa(log_text)
    return {vc for vc, kind in kappa.items() if kind in ("acyclic_only", "both")}


# ── proof file parsing ────────────────────────────────────────────────────────

def parse_proof_file(path: Path) -> tuple[str, str, str] | None:
    text = path.read_text(encoding="utf-8", errors="replace")
    matches = list(PROOF_DEF_RE.finditer(text))
    if not matches:
        return None
    m = matches[-1]
    return text[: m.start()], m.group(1), m.group(2)


# ── temp file generation ──────────────────────────────────────────────────────

def build_temp_src(head: str, proof_name: str, vc_type: str, config: str, tactic: str) -> str:
    imports_patched = head.replace(
        "import LeanFixpoint\n",
        "import LeanFixpoint\nimport LeanFixpoint.Eval.FusionSearch\n",
        1,
    )
    bench_name = f"{proof_name}_{config}"
    return (
        f"{imports_patched}\n"
        f"end F  -- close namespace F opened by qualifs in head\n\n"
        f"{prelude_body()}\n\n"
        f'benchx "{bench_name}" in\n'
        f"def {bench_name} : F.{vc_type} := by\n"
        f"  unfold F.{vc_type}\n"
        f"  {tactic}\n"
        f"  all_goals sorry\n"
    )


# ── run one (proof_path, config) pair ─────────────────────────────────────────

def run_config(
    lean_proofs_dir: Path,
    proof_path: Path,
    proof_name: str,
    vc_type: str,
    config: str,
    tactic: str,
) -> dict:
    parsed = parse_proof_file(proof_path)
    if parsed is None:
        return _fail_result(config, tactic, "PARSE_ERROR")

    head, _, _ = parsed
    src = build_temp_src(head, proof_name, vc_type, config, tactic)

    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", dir=str(lean_proofs_dir), delete=False
    ) as f:
        f.write(src)
        tmp = f.name
    try:
        proc = subprocess.Popen(
            ["lake", "env", "lean", tmp],
            cwd=lean_proofs_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        try:
            stdout, stderr = proc.communicate(timeout=300)
            out = stdout + stderr
        except subprocess.TimeoutExpired:
            print(f"  [timeout] {proof_name} {config} — killing", flush=True)
            proc.kill()
            proc.communicate()
            return _fail_result(config, tactic, "TIMEOUT")
    finally:
        try:
            os.unlink(tmp)
        except Exception:
            pass

    res: dict = _fail_result(config, tactic, "FAIL")
    bl = BL2_RE.search(out)
    if bl:
        res.update(
            status=bl.group(2),
            hb=int(bl.group(3)),
            ms=int(bl.group(4)),
            depth=int(bl.group(5)),
            nconst=int(bl.group(6)),
            kerus=int(bl.group(7)),
        )
    for ptac, phase, hb in PHASE_RE.findall(out):
        k = f"{ptac}:{phase}"
        res["phases"][k] = res["phases"].get(k, 0) + int(hb)
    res["elim_hb"] = sum(res["phases"].values()) if res["phases"] else None
    if not bl and "error" in out.lower():
        res["error_excerpt"] = next(
            (l for l in out.splitlines() if "error" in l.lower()), ""
        )[:200]
    return res


def _fail_result(config: str, tactic: str, status: str) -> dict:
    return {
        "config": config,
        "tactic": tactic,
        "status": status,
        "hb": None,
        "ms": None,
        "depth": None,
        "nconst": None,
        "kerus": None,
        "phases": {},
        "elim_hb": None,
    }


# ── task collection ───────────────────────────────────────────────────────────

def collect_tasks(
    suite_name: str,
    lean_proofs_dir: Path,
    log_text: str,
    vc_filter: str | None,
) -> list[tuple]:
    if not lean_proofs_dir.is_dir():
        print(f"  [warn] missing dir: {lean_proofs_dir}", file=sys.stderr)
        return []
    acyclic = acyclic_vcs_from_log(log_text)
    proof_dir = lean_proofs_dir / "LeanProofs" / "User" / "Proof"
    if not proof_dir.is_dir():
        return []
    tasks = []
    for proof_path in sorted(proof_dir.glob("*Proof.lean")):
        vc_name = proof_path.stem.removesuffix("Proof")
        if vc_name not in acyclic:
            continue
        if vc_filter and vc_filter not in vc_name:
            continue
        parsed = parse_proof_file(proof_path)
        if parsed is None:
            print(f"  [warn] parse failed: {proof_path.name}", file=sys.stderr)
            continue
        _, proof_name, vc_type = parsed
        for config, tactic in CONFIGS:
            tasks.append((suite_name, lean_proofs_dir, proof_path,
                          proof_name, vc_type, config, tactic, proof_name))
    return tasks


# ── main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--jobs", type=int,
                    default=max(1, (os.cpu_count() or 2) // 2),
                    help="parallel workers (default: cpu_count/2)")
    ap.add_argument("--filter", default=None,
                    help="only run VCs whose name contains this substring")
    ap.add_argument("--out", default=str(SCRIPT_DIR / "rq2_results.json"),
                    help="output JSON path")
    ap.add_argument("--append", action="store_true",
                    help="merge results into existing JSON instead of overwriting")
    args = ap.parse_args()

    if not PRELUDE.exists():
        print(f"error: Rq3Bench.lean not found: {PRELUDE}", file=sys.stderr)
        return 1

    all_tasks: list[tuple] = []
    for suite_name, lean_proofs_dir, log_path in SUITES:
        if not log_path.exists():
            print(f"  [warn] missing log: {log_path}", file=sys.stderr)
            continue
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        all_tasks += collect_tasks(suite_name, lean_proofs_dir, log_text, args.filter)

    n_vcs = len({t[7] for t in all_tasks})
    print(
        f"RQ2 fusion: {n_vcs} qualifying VCs × {len(CONFIGS)} configs "
        f"= {len(all_tasks)} runs  ({args.jobs} parallel)\n"
    )

    out_path = Path(args.out)
    out: dict[str, dict] = {}
    if args.append and out_path.exists():
        out = json.loads(out_path.read_text())
        print(f"loaded {len(out)} existing entries from {args.out}")

    print(f"submitting {len(all_tasks)} tasks...", flush=True)
    n_done = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs: dict = {}
        for suite, lp_dir, proof_path, proof_name, vc_type, config, tactic, vc_id in all_tasks:
            key = f"{suite}/{vc_id}"
            if key not in out:
                out[key] = {"suite": suite, "proof_name": proof_name, "vc_type": vc_type}
            if args.append and config in out[key]:
                continue
            fut = ex.submit(run_config, lp_dir, proof_path, proof_name, vc_type, config, tactic)
            futs[fut] = (key, config)

        print(f"all {len(futs)} futures submitted, waiting for results...", flush=True)
        for fut in as_completed(futs):
            key, config = futs[fut]
            r = fut.result()
            out[key][config] = r
            n_done += 1
            print(
                f"  [{n_done}/{len(futs)}] {key:<60} {config:<6} status={r['status']:<8} "
                f"hb={r.get('hb')} elim={r.get('elim_hb')}",
                flush=True,
            )

    print(f"writing {args.out}...", flush=True)
    out_path.write_text(json.dumps(out, indent=2, ensure_ascii=False))
    print(f"wrote {args.out}")

    print(f"\n{'VC':<62} {'zap':>10} {'grind':>10} {'aesop':>10}   z/g/a")
    print("-" * 100)
    for key in sorted(out):
        row = out[key]

        def cell(k: str) -> str:
            c = row.get(k, {})
            e = c.get("elim_hb")
            if e is not None:
                return str(e)
            return "FAIL" if c.get("status") == "FAIL" else "—"

        st = "/".join(
            (row.get(k, {}).get("status", "?") or "?")[0]
            for k, _ in CONFIGS
        )
        print(f"{key:<62} {cell('zap'):>10} {cell('grind'):>10} {cell('aesop'):>10}   {st}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
