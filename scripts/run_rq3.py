#!/usr/bin/env python3
"""RQ3 driver: deterministic proof-term (fusion/Zap) vs proof-search (grind).

For each Liquid-fixpoint benchmark with ≥1 acyclic κ, run two pipelines on the
SAME VC and collect comparison metrics:

  A = `unfold VC; solve_fixpoint`                       (acyclic κ → grind closer)
  B = `unfold VC; fusion; all_goals solve_fixpoint`     (acyclic κ → proof term)

Each config runs in its OWN `lake env lean` invocation (so the per-phase
`[phase]` lines belong unambiguously to that config). Metrics per config:
  hb, ms, depth, nconst, kerus  (from `BENCHLINE2`, see eval/Rq3Bench.lean)
  phase heartbeats              (from `[phase] <tac>:<phase>=<hb>`)
plus the κ-partition (#acyclic / #cyclic) scraped from config A's trace.

Output: eval/rq3_results.json (consumed by rq3_aggregate.py) + a console table.

Usage:
    python3 scripts/run_rq3.py [--jobs 4] [--filter icfp]
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

REPO = Path(__file__).resolve().parent.parent
PRELUDE = REPO / "eval" / "Rq3Bench.lean"

# Subset with ≥1 acyclic κ (acyclic_only ∪ both), per benchmark_kappa_report.py
# (Quicksort is added explicitly: its proof is already `fusion; solve_fixpoint`,
#  so the classifier sees no acyclic κ post-fusion, but it genuinely has them).
SUBSET = (
    [("Liquid-fixpoint", b) for b in [
        "arbitrary-kvar-arg", "exists_oddity", "icfp17-ex1", "icfp17-ex2",
        "icfp17-ex3", "kut00", "mod00", "scrape03", "test02",  # acyclic_only
        "comment", "scrape02"]]                                # both
    + [("FluxRS", b) for b in [
        "Fix-Test4", "Fix-Test5", "Fix-Test7",                 # acyclic_only
        "FibMemoBoth", "Fix-Test1", "Fix-Test6",               # both
        "Quicksort"]]                                          # large, fusion-first
)

THM_RE = re.compile(r"(?m)^theorem\s+(\w+)\s*:\s*([\w'.]+)\s*:=\s*by\b")
BL2_RE = re.compile(
    r"BENCHLINE2\s+(\S+)\s+status=(\S+)\s+hb=(\d+)\s+ms=(\d+)\s+"
    r"depth=(\d+)\s+nconst=(\d+)\s+kerus=(\d+)")
PHASE_RE = re.compile(r"\[phase\]\s+(\w+):(\w+)=(\d+)")
ACY_RE = re.compile(r"\[solve_fixpoint\] Acyclic κ:\s*\[([^\]]*)\]")
CYC_RE = re.compile(r"\[solve_fixpoint\] Cyclic κ:\s*\[([^\]]*)\]")


def prelude_body() -> str:
    # Everything below the leading `import` line (driver re-supplies imports).
    lines = PRELUDE.read_text().splitlines()
    return "\n".join(l for l in lines if not l.startswith("import"))


def sanitize(name: str) -> str:
    return re.sub(r"\W", "_", name)


def find_solver_theorem(text: str):
    """The VC theorem is the one whose proof uses the solver (not a helper
    lemma). Pick the first `theorem _ : _ := by` whose body mentions
    `solve_fixpoint`/`fusion`; this keeps any preceding helper lemmas in `head`."""
    matches = list(THM_RE.finditer(text))
    if not matches:
        return None
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        window = text[m.end(): min(end, m.end() + 400)]
        if "solve_fixpoint" in window or re.search(r"\bfusion\b", window):
            return m
    return matches[0]


def build_file(group: str, bench: str, config: str) -> tuple[str, str]:
    """Return (lean source, theorem-name) for one config of one benchmark."""
    text = (REPO / "Benchmarks" / group / f"{bench}.lean").read_text()
    m = find_solver_theorem(text)
    if not m:
        raise RuntimeError(f"{bench}: no solver theorem found")
    vc = m.group(2)
    head = text[: m.start()]
    # Drop trailing scoped modifiers (`@[...]`, `set_option … in`) that belonged
    # to the now-removed VC theorem — else a dangling `set_option … in` swallows
    # the injected prelude's first command (e.g. its `open`).
    hlines = head.rstrip().split("\n")
    while hlines and re.match(r"^\s*(@\[.*\]|set_option .*\bin)\s*$", hlines[-1]):
        hlines.pop()
    head = "\n".join(hlines) + "\n"
    thm = f"{sanitize(bench)}_{config}"
    if config == "A":
        proof = f"by unfold {vc}; solve_fixpoint"
    else:
        proof = f"by unfold {vc}; fusion; all_goals solve_fixpoint"
    src = (
        f"{head}\n{prelude_body()}\n\n"
        f'benchx "{thm}" in\n'
        f"theorem {thm} : {vc} := {proof}\n"
    )
    return src, thm


def run_config(group: str, bench: str, config: str) -> dict:
    src, thm = build_file(group, bench, config)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=str(REPO),
                                     delete=False) as f:
        f.write(src)
        tmp = f.name
    try:
        proc = subprocess.run(["lake", "env", "lean", tmp], cwd=REPO,
                              capture_output=True, text=True)
        out = proc.stdout + proc.stderr
    finally:
        os.unlink(tmp)

    res: dict = {"config": config, "status": "FAIL", "hb": None, "ms": None,
                 "depth": None, "nconst": None, "kerus": None, "phases": {}}
    bl = BL2_RE.search(out)
    if bl:
        res.update(status=bl.group(2), hb=int(bl.group(3)), ms=int(bl.group(4)),
                   depth=int(bl.group(5)), nconst=int(bl.group(6)),
                   kerus=int(bl.group(7)))
    # phases: key "<tac>:<phase>"; B has two solve_fixpoint groups (the residual
    # one has fuse=0 since no acyclic remain) — sum same keys.
    for tac, phase, hb in PHASE_RE.findall(out):
        k = f"{tac}:{phase}"
        res["phases"][k] = res["phases"].get(k, 0) + int(hb)
    if config == "A":
        a = ACY_RE.search(out)
        c = CYC_RE.search(out)
        res["n_acyclic"] = len([x for x in (a.group(1) if a else "").split(",") if x.strip()])
        res["n_cyclic"] = len([x for x in (c.group(1) if c else "").split(",") if x.strip()])
    if not bl and "error" in out.lower():
        res["error_excerpt"] = next((l for l in out.splitlines() if "error" in l.lower()), "")[:200]
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--filter", default=None)
    ap.add_argument("--out", default=str(REPO / "eval" / "rq3_results.json"))
    args = ap.parse_args()

    benches = [(g, b) for g, b in SUBSET if not args.filter or args.filter in b]
    tasks = [(g, b, cfg) for g, b in benches for cfg in ("A", "B")]
    print(f"RQ3: {len(benches)} benchmarks × 2 configs = {len(tasks)} runs "
          f"({args.jobs} parallel)\n")

    out: dict[str, dict] = {b: {"group": g} for g, b in benches}
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(run_config, g, b, cfg): (b, cfg) for g, b, cfg in tasks}
        for fut in as_completed(futs):
            b, cfg = futs[fut]
            r = fut.result()
            out[b][cfg] = r
            print(f"  {b:<22} {cfg}  status={r['status']:<4} hb={r['hb']}", flush=True)

    Path(args.out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
    print(f"\nwrote {args.out}")

    # quick console table
    print(f"\n{'benchmark':<22} {'#acy':>4} {'#cyc':>4} {'A hb':>7} {'B hb':>7} "
          f"{'×':>5} {'A close':>8} {'B fus':>6} {'A':>3} {'B':>3}")
    for _g, b in benches:
        A, B = out[b].get("A", {}), out[b].get("B", {})
        ahb, bhb = A.get("hb"), B.get("hb")
        spd = f"{ahb/bhb:.1f}" if ahb and bhb else "—"
        aclose = A.get("phases", {}).get("solve_fixpoint:close", "—")
        bfus = sum(B.get("phases", {}).get(f"fusion:{p}", 0) for p in ("sol", "build", "clean")) or "—"
        print(f"{b:<22} {A.get('n_acyclic','?'):>4} {A.get('n_cyclic','?'):>4} "
              f"{str(ahb):>7} {str(bhb):>7} {spd:>5} {str(aclose):>8} {str(bfus):>6} "
              f"{A.get('status','?'):>3} {B.get('status','?'):>3}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
