"""Shared kvar (κ) classification for VC logs.

`zap`/`fusion` runs before `solve_fixpoint` and reports, via `[fusion] Start
κ: [...]` / `[fusion] End κ: [...]` log lines, the κ's it started with and
the κ's still unsolved afterward (the rest were eliminated as acyclic) — see
Flex/Tactic/Tactics/Fusion.lean. Every eval script that needs to know which
kind of kvars a VC has (none / acyclic-only / cyclic-only / both) must derive
it from these lines rather than any other heuristic.
"""

from __future__ import annotations

import re

FUSION_START_RE = re.compile(
    r"info: .*/(\w+)Proof\.lean:\d+:\d+: \[fusion\] Start κ:\s*\[([^\]]*)\]"
)
FUSION_END_RE = re.compile(r"\[fusion\] End κ:\s*\[([^\]]*)\]")

# Path-qualified variant: captures the directory prefix before `/User/Proof/`
# so callers can disambiguate VCs whose basenames collide across test
# directories (e.g. lean_bench_merged, where many tests share names like
# `Test00Proof.lean`).
FUSION_START_PATHED_RE = re.compile(
    r"info: (\S+)/User/Proof/(\w+)Proof\.lean:\d+:\d+: \[fusion\] Start κ:\s*\[([^\]]*)\]"
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


def parse_log_kappa(text: str) -> dict[str, str]:
    """Classify each VC from fusion's Start/End κ lists.

    Per the classification rule:
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


def parse_log_kappa_pathed(text: str) -> dict[str, str]:
    """Like `parse_log_kappa`, but keys results by `<test_path>/<VCName>`
    (the directory prefix before `/User/Proof/`) instead of bare VC name.

    Use this for merged/multi-suite logs (e.g. lean_bench_merged) where the
    same VC basename appears under many different test directories — keying
    by bare name would silently conflate unrelated VCs' classifications.
    """
    results: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = FUSION_START_PATHED_RE.search(lines[i])
        if m:
            key = f"{m.group(1)}/{m.group(2)}"
            start = _items(m.group(3))
            end: list[str] = []
            if i + 1 < len(lines):
                em = FUSION_END_RE.search(lines[i + 1])
                if em:
                    end = _items(em.group(1))
                    i += 1
            if not start:
                results[key] = "none"
            elif not end:
                results[key] = "acyclic_only"
            elif len(end) == len(start):
                results[key] = "cyclic_only"
            else:
                results[key] = "both"
        i += 1
    return results
