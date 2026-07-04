#!/usr/bin/env python3
"""Produce two benchmark summary tables in Markdown and LaTeX.

Table 1: Non-trivial VCs and proof failures
Table 2: Kvar classification of non-trivial VCs (none / acyclic / cyclic / both)

Data sources:
  - flux-wick-benchmarks: inline (reads local log files + VC dirs)
  - Flux lean-bench:      subprocess call to flux/tools/export_lean_bench_stats.py
  - Liquid-fixpoint:      subprocess call to lean-fixpoint/scripts/export_stats.py

Usage:
    python3 make_tables.py
    python3 make_tables.py --flux-root /path/to/flux
                           --lf-root   /path/to/lean-fixpoint
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ── paths ────────────────────────────────────────────────────────────────────

ROOT = Path(__file__).parent
DEFAULT_LF_ROOT = ROOT.parent.parent

WICK_SUITES = [
    ("flux-demo",     "flux_demo_lean_proofs"),
    ("kani-vecdeque", "vecdeque_lean_proofs"),
    ("pldi23",        "pldi_lean_proofs"),
    ("wave",          "wave_lean_proofs"),
]

# Suites to merge into a single aggregate row in the output tables.
MERGED_SUITE_NAME = "flux-medium"
MERGED_SUITE_MEMBERS = {"flux-demo", "kani-vecdeque", "pldi23"}

# LaTeX macro to use for each suite's display name in table 1.
SUITE_MACROS = {
    "flux-medium":     r"\fluxmedium",
    "wave":             r"\wavesuite",
    "Flux lean-bench":  r"\fluxtests",
    "Liquid-fixpoint":  r"\lfsuite",
}

# ── shared regexes (same as classify_nontrivial_vcs.py / count_failures.py) ──

LAST_DEF_RE = re.compile(r"(?s).*\bdef\s+(\w+)\s*:=(.*)")
# `fusion` (which runs before `solve_fixpoint` in the current tactic pipeline)
# reports the κ's it started with and the κ's still unsolved afterward —
# see LeanFixpoint/Tactic/Tactics/Fusion.lean.
FUSION_START_RE = re.compile(
    r"info: .*/(\w+)Proof\.lean:\d+:\d+: \[fusion\] Start κ:\s*\[([^\]]*)\]"
)
FUSION_END_RE   = re.compile(r"\[fusion\] End κ:\s*\[([^\]]*)\]")
ERROR_RE    = re.compile(
    r"error: LeanProofs/User/Proof/(\w+)Proof\.lean:\d+:\d+: (.+)$",
    re.MULTILINE,
)


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


def classify(acyclic: list[str], cyclic: list[str]) -> str:
    if acyclic and cyclic:
        return "both"
    if acyclic:
        return "acyclic_only"
    if cyclic:
        return "cyclic_only"
    return "none"


def is_trivially_true(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    m = LAST_DEF_RE.match(text)
    if not m:
        return False
    body = re.sub(r"\bend\s+F\b", "", m.group(2)).strip()
    return body == "True"


def parse_log_kappa(text: str) -> dict[str, str]:
    """Classify each VC from fusion's Start/End κ lists.

    `fusion` runs before `solve_fixpoint` and reports the κ's it started
    with and the κ's still unsolved afterward (the rest were eliminated as
    acyclic). Per the classification rule:
      - no κ's to start with            -> none
      - something before, none after    -> acyclic_only
      - same count before and after     -> cyclic_only (fusion ate nothing)
      - fewer after than before         -> both
    """
    results: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = FUSION_START_RE.search(lines[i])
        if m:
            vc = m.group(1)
            start = _items(m.group(2))
            end: list[str] = []
            if i + 1 < len(lines):
                em = FUSION_END_RE.search(lines[i + 1])
                if em:
                    end = _items(em.group(1))
                    i += 1
            if not start:
                results[vc] = "none"
            elif not end:
                results[vc] = "acyclic_only"
            elif len(end) == len(start):
                results[vc] = "cyclic_only"
            else:
                results[vc] = "both"
        i += 1
    return results


def parse_log_failures(text: str) -> set[str]:
    return {m.group(1) for m in ERROR_RE.finditer(text)}


# ── per-VC dataclass ─────────────────────────────────────────────────────────

@dataclass
class VCStats:
    name: str
    trivial: bool
    kappa: str   # none / acyclic_only / cyclic_only / both
    failed: bool


@dataclass
class SuiteStats:
    name: str
    vcs: list[VCStats] = field(default_factory=list)
    time_ms: int | None = None       # Lean proof time
    flux_time_ms: int | None = None  # Flux type-checking time (no lean)

    def nontrivial(self) -> list[VCStats]:
        return [v for v in self.vcs if not v.trivial]

    def tally(self) -> dict[str, int]:
        t: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
        for v in self.nontrivial():
            t[v.kappa] += 1
        return t

    def n_failed(self) -> int:
        return sum(1 for v in self.nontrivial() if v.failed)

    def n_cyclic_proven(self) -> int:
        return sum(
            1 for v in self.nontrivial()
            if v.kappa in ("cyclic_only", "both") and not v.failed
        )


# ── load wick-benchmarks data ─────────────────────────────────────────────────

def _read_time_ms(path: Path) -> int | None:
    try:
        return int(path.read_text().strip())
    except Exception:
        return None


_TIMING_LINE_RE = re.compile(r"Total running time:\s+(\d+(?:\.\d+)?)(µs|ms|s|m)")


def _parse_timings_ms(path: Path) -> int | None:
    """Sum all 'Total running time' lines from a -Ftimings output file."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return None
    total_ms = 0.0
    found = False
    for m in _TIMING_LINE_RE.finditer(text):
        val, unit = float(m.group(1)), m.group(2)
        if unit == "µs":
            total_ms += val / 1000
        elif unit == "ms":
            total_ms += val
        elif unit == "s":
            total_ms += val * 1000
        elif unit == "m":
            total_ms += val * 60_000
        found = True
    return round(total_ms) if found else None


def load_wick_suite(display_name: str, dir_name: str) -> SuiteStats | None:
    log_path          = ROOT / f"{dir_name}.log"
    time_path         = ROOT / f"{dir_name}.time"
    flux_timings_path = ROOT / f"{dir_name}_flux.timings"
    flux_time_path    = ROOT / f"{dir_name}_flux.time"   # legacy fallback
    vc_dir            = ROOT.parent / dir_name / "LeanProofs" / "Flux" / "VC"

    if not log_path.exists():
        print(f"  [warning] missing log: {log_path}", file=sys.stderr)
        return None
    if not vc_dir.is_dir():
        print(f"  [warning] missing VC dir: {vc_dir}", file=sys.stderr)
        return None

    text = log_path.read_text(encoding="utf-8", errors="replace")
    kappa  = parse_log_kappa(text)
    failed = parse_log_failures(text)

    flux_time_ms = _parse_timings_ms(flux_timings_path)
    if flux_time_ms is None:
        flux_time_ms = _read_time_ms(flux_time_path)  # legacy fallback

    suite = SuiteStats(
        name         = display_name,
        time_ms      = _read_time_ms(time_path),
        flux_time_ms = flux_time_ms,
    )
    for f in sorted(vc_dir.glob("*.lean")):
        suite.vcs.append(VCStats(
            name    = f.stem,
            trivial = is_trivially_true(f),
            kappa   = kappa.get(f.stem, "none"),
            failed  = f.stem in failed,
        ))
    return suite


# ── load data from external export scripts ───────────────────────────────────

def load_from_script(script: Path) -> list[SuiteStats] | None:
    if not script.exists():
        print(f"  [warning] script not found: {script}", file=sys.stderr)
        return None
    try:
        result = subprocess.run(
            [sys.executable, str(script)],
            capture_output=True, text=True, timeout=60,
        )
    except subprocess.TimeoutExpired:
        print(f"  [warning] timeout calling {script}", file=sys.stderr)
        return None

    if result.returncode != 0:
        msg = result.stderr.strip().splitlines()[0] if result.stderr.strip() else "(no output)"
        print(f"  [warning] {script.name}: {msg}", file=sys.stderr)
        return None

    try:
        raw = json.loads(result.stdout)
    except json.JSONDecodeError as e:
        print(f"  [warning] bad JSON from {script.name}: {e}", file=sys.stderr)
        return None

    suites = []
    for s in raw:
        suite = SuiteStats(name=s["suite"], time_ms=s.get("time_ms"), flux_time_ms=s.get("flux_time_ms"))
        for v in s["vcs"]:
            suite.vcs.append(VCStats(
                name    = v["name"],
                trivial = v["trivial"],
                kappa   = v["kappa"],
                failed  = v["failed"],
            ))
        suites.append(suite)
    return suites


# ── suite merging ─────────────────────────────────────────────────────────────

def merge_suites(suites: list[SuiteStats], names: set[str], merged_name: str) -> list[SuiteStats]:
    """Combine all suites whose name is in *names* into one aggregate row."""
    to_merge = [s for s in suites if s.name in names]
    rest     = [s for s in suites if s.name not in names]
    if not to_merge:
        return suites
    merged = SuiteStats(name=merged_name, time_ms=0, flux_time_ms=0)
    for s in to_merge:
        merged.vcs.extend(s.vcs)
        merged.time_ms      = _acc_time(merged.time_ms,      s.time_ms)
        merged.flux_time_ms = _acc_time(merged.flux_time_ms, s.flux_time_ms)
    # Insert merged row where the first member appeared
    first_idx = next(i for i, s in enumerate(suites) if s.name in names)
    return rest[:first_idx] + [merged] + rest[first_idx:]


# ── table rendering ───────────────────────────────────────────────────────────

def _fmt_time(ms: int | None) -> str:
    if ms is None:
        return "—"
    s = ms / 1000
    if s >= 60:
        return f"{s/60:.1f}m"
    return f"{s:.1f}s"


def _acc_time(acc: int | None, ms: int | None) -> int | None:
    if ms is None or acc is None:
        return None
    return acc + ms


def _cyclic_pct(s: SuiteStats) -> str:
    t = s.tally()
    n_cyclic = t["cyclic_only"] + t["both"]
    if not n_cyclic:
        return "—"
    return f"{100*s.n_cyclic_proven()/n_cyclic:.1f}%"


def render_table1_md(suites: list[SuiteStats]) -> str:
    header = "| Benchmark | Non-trivial VCs | Failures | Success % | Success % (cyclic) | fixpoint-hs time | Lean Time |"
    sep    = "|-----------|----------------:|---------:|----------:|-------------------:|----------:|----------:|"
    rows   = [header, sep]
    tot_nt = tot_fail = tot_cyclic = tot_cyclic_proven = 0
    tot_ms: int | None = 0
    tot_flux_ms: int | None = 0
    for s in suites:
        nt   = len(s.nontrivial())
        fail = s.n_failed()
        t    = s.tally()
        n_cyclic = t["cyclic_only"] + t["both"]
        pct      = f"{100*(nt-fail)/nt:.1f}%" if nt else "—"
        cpct     = _cyclic_pct(s)
        rows.append(
            f"| {s.name} | {nt} | {fail} | {pct} | {cpct} "
            f"| {_fmt_time(s.flux_time_ms)} | {_fmt_time(s.time_ms)} |"
        )
        tot_nt += nt; tot_fail += fail
        tot_cyclic += n_cyclic; tot_cyclic_proven += s.n_cyclic_proven()
        tot_ms      = _acc_time(tot_ms, s.time_ms)
        tot_flux_ms = _acc_time(tot_flux_ms, s.flux_time_ms)
    tot_pct  = f"{100*(tot_nt-tot_fail)/tot_nt:.1f}%" if tot_nt else "—"
    tot_cpct = f"{100*tot_cyclic_proven/tot_cyclic:.1f}%" if tot_cyclic else "—"
    rows.append(
        f"| **Total** | **{tot_nt}** | **{tot_fail}** | **{tot_pct}** | **{tot_cpct}** "
        f"| **{_fmt_time(tot_flux_ms)}** | **{_fmt_time(tot_ms)}** |"
    )
    return "\n".join(rows)


def render_table2_md(suites: list[SuiteStats]) -> str:
    header = "| Benchmark | none | acyclic | cyclic | both | Total |"
    sep    = "|-----------|-----:|--------:|-------:|-----:|------:|"
    rows   = [header, sep]
    gtally: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
    for s in suites:
        t = s.tally()
        total = sum(t.values())
        rows.append(f"| {s.name} | {t['none']} | {t['acyclic_only']} | {t['cyclic_only']} | {t['both']} | {total} |")
        for k in gtally:
            gtally[k] += t[k]
    gt = sum(gtally.values())
    rows.append(
        f"| **Total** | **{gtally['none']}** | **{gtally['acyclic_only']}** | "
        f"**{gtally['cyclic_only']}** | **{gtally['both']}** | **{gt}** |"
    )
    return "\n".join(rows)


def render_table1_latex(suites: list[SuiteStats]) -> str:
    lines = [
        r"\begin{table}[t]",
        r"\centering\small",
        r"\begin{tabular}{lrrrrr}",
        r"\toprule",
        r"Benchmark & \#CHCs & Success & Success (cyclic) & LF time & \sys Time \\",
        r"\midrule",
    ]
    tot_nt = tot_cyclic = tot_cyclic_proven = 0
    tot_ms: int | None = 0
    tot_flux_ms: int | None = 0
    for s in suites:
        nt   = len(s.nontrivial())
        fail = s.n_failed()
        t    = s.tally()
        n_cyclic = t["cyclic_only"] + t["both"]
        pct  = f"{100*(nt-fail)/nt:.1f}" if nt else "--"
        cpct = f"{100*s.n_cyclic_proven()/n_cyclic:.1f}" if n_cyclic else "--"
        cstr = f"{n_cyclic} ({cpct}\\%)" if n_cyclic else "—"
        name = SUITE_MACROS.get(s.name, s.name.replace("_", r"\_"))
        lines.append(
            rf"{name} & {nt} & {pct}\% & {cstr} & {_fmt_time(s.flux_time_ms)} & {_fmt_time(s.time_ms)} \\"
        )
        tot_nt += nt
        tot_cyclic += n_cyclic; tot_cyclic_proven += s.n_cyclic_proven()
        tot_ms      = _acc_time(tot_ms, s.time_ms)
        tot_flux_ms = _acc_time(tot_flux_ms, s.flux_time_ms)
    tot_fail_total = sum(s.n_failed() for s in suites)
    tot_pct  = f"{100*(tot_nt-tot_fail_total)/tot_nt:.1f}" if tot_nt else "--"
    tot_cpct = f"{100*tot_cyclic_proven/tot_cyclic:.1f}" if tot_cyclic else "--"
    tot_cstr = f"{tot_cyclic} ({tot_cpct}\\%)" if tot_cyclic else "—"
    lines += [
        r"\midrule",
        rf"\textbf{{Total}} & {tot_nt} & {tot_pct}\% & {tot_cstr} & {_fmt_time(tot_flux_ms)} & {_fmt_time(tot_ms)} \\",
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{Automation coverage of the full solver pipeline (\zap{} followed by",
        r"  \Fixname{} with a \lean{grind}/\lean{aesop} oracle), run with no human input.",
        r"  \#CHCs is the number of constraints in the suite; Success is the fraction",
        r"  discharged, and Success (cyclic) the fraction discharged among those",
        r"  constraints with a cyclic $\kappa$-variable.",
        r"  LF time and \sys Time are the total wall-clock time to solve the entire suite",
        r"  with Liquid Fixpoint (SMT) and \sys, respectively.}",
        r"\label{tab:benchmarks}",
        r"\end{table}",
    ]
    return "\n".join(lines)


def render_table2_latex(suites: list[SuiteStats]) -> str:
    lines = [
        r"\begin{tabular}{lrrrrr}",
        r"\toprule",
        r"Benchmark & none & acyclic & cyclic & both & Total \\",
        r"\midrule",
    ]
    gtally: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
    for s in suites:
        t = s.tally()
        total = sum(t.values())
        name = s.name.replace("_", r"\_")
        lines.append(rf"{name} & {t['none']} & {t['acyclic_only']} & {t['cyclic_only']} & {t['both']} & {total} \\")
        for k in gtally:
            gtally[k] += t[k]
    gt = sum(gtally.values())
    lines += [
        r"\midrule",
        rf"\textbf{{Total}} & {gtally['none']} & {gtally['acyclic_only']} & "
        rf"{gtally['cyclic_only']} & {gtally['both']} & {gt} \\",
        r"\bottomrule",
        r"\end{tabular}",
    ]
    return "\n".join(lines)


# ── main ─────────────────────────────────────────────────────────────────────

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lf-root",   type=Path, default=DEFAULT_LF_ROOT,
                    help="path to the lean-fixpoint repo")
    ap.add_argument("--format", choices=["markdown", "latex", "both"], default="markdown",
                    help="output format (default: markdown)")
    args = ap.parse_args()

    suites: list[SuiteStats] = []

    # 1. Flux-wick benchmarks (inline)
    for display, dir_name in WICK_SUITES:
        s = load_wick_suite(display, dir_name)
        if s:
            suites.append(s)

    # 2. Flux lean-bench (merged suite)
    lean_bench_script = ROOT / "export_lean_bench_stats.py"
    result = load_from_script(lean_bench_script)
    if result:
        suites.extend(result)
    else:
        print(f"  [info] Flux lean-bench data unavailable "
              f"(check {ROOT}/lean_bench_log.txt)", file=sys.stderr)

    # 3. Liquid-fixpoint benchmarks
    lf_script = args.lf_root / "scripts" / "export_stats.py"
    result = load_from_script(lf_script)
    if result:
        suites.extend(result)
    else:
        print(f"  [info] Liquid-fixpoint data unavailable "
              f"(run python3 {args.lf_root}/scripts/run_benchmarks.py first)", file=sys.stderr)

    if not suites:
        print("No data available.", file=sys.stderr)
        sys.exit(1)

    suites = merge_suites(suites, MERGED_SUITE_MEMBERS, MERGED_SUITE_NAME)

    # ── output ────────────────────────────────────────────────────────────────
    fmt = args.format
    sep = "=" * 70

    md = (
        "# Table 1: Non-trivial VCs and Proof Failures\n\n"
        f"{render_table1_md(suites)}\n\n"
        "# Table 2: Kvar Classification of Non-trivial VCs\n\n"
        f"{render_table2_md(suites)}\n"
    )
    tex = (
        "% Table 1: Non-trivial VCs and Proof Failures\n"
        f"{render_table1_latex(suites)}\n\n"
        "% Table 2: Kvar Classification of Non-trivial VCs\n"
        f"{render_table2_latex(suites)}\n"
    )
    (ROOT / "tables.md").write_text(md)
    (ROOT / "tables.tex").write_text(tex)
    print(f"Wrote {ROOT / 'tables.md'}")
    print(f"Wrote {ROOT / 'tables.tex'}")

    print(sep)
    print("TABLE 1: Non-trivial VCs and Proof Failures")
    print(sep)
    if fmt in ("markdown", "both"):
        if fmt == "both":
            print("\n--- Markdown ---\n")
        print(render_table1_md(suites))
    if fmt in ("latex", "both"):
        if fmt == "both":
            print("\n--- LaTeX ---\n")
        print(render_table1_latex(suites))

    print()
    print(sep)
    print("TABLE 2: Kvar Classification of Non-trivial VCs")
    print(sep)
    if fmt in ("markdown", "both"):
        if fmt == "both":
            print("\n--- Markdown ---\n")
        print(render_table2_md(suites))
    if fmt in ("latex", "both"):
        if fmt == "both":
            print("\n--- LaTeX ---\n")
        print(render_table2_latex(suites))


if __name__ == "__main__":
    main()
