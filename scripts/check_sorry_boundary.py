#!/usr/bin/env python3
"""Enforce the sorry boundary (issue #31).

Policy:

1. Everything transitively imported by `Hilbert10.lean` — the production root spine — is
   sorry-free.
2. Work in progress lives in the separate `Hilbert10Experimental` library and is never
   imported by the root spine. It may contain sorries; it still has to typecheck, which
   the `Hilbert10Experimental` lake target ensures.
3. Promotion into the root spine requires removing all sorries and passing the axiom
   audit. Promotion is the reviewable event: a file appearing in the transitive closure of
   `Hilbert10.lean` is a claim that it is finished.

This script checks 1 and 2. It computes the import closure from the source text rather
than from build artefacts, so it works on a clean checkout and cannot be fooled by a
stale `.lake`. Being a source-text check it is the cheap first line of defence, not the
only one: `sorryAx` is an axiom, so `scripts/AxiomAudit.lean` independently rejects any
spine declaration that actually uses one.

Usage: scripts/check_sorry_boundary.py   (from anywhere inside the repo)
Exit status 1 on any violation.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT_MODULE = "Hilbert10"
EXPERIMENTAL_PREFIX = "Hilbert10Experimental"

# `sorry` and friends as whole words. `sorryAx` is the kernel-level form; `admit` is the
# tactic alias. Substring matches like `sorryFree` are excluded by the word boundaries.
SORRY_RE = re.compile(r"\b(sorry|sorryAx|admit)\b")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")


def repo_root() -> Path:
    here = Path(__file__).resolve().parent.parent
    if not (here / "lakefile.toml").exists():
        sys.exit(f"check_sorry_boundary: no lakefile.toml at {here}")
    return here


def module_path(root: Path, module: str) -> Path | None:
    """Source file for a repo-local module name, or None if it is not ours.

    Locality is decided by whether the file exists in the repo, not by a namespace
    prefix, so both `Hilbert10.*` and `Hilbert10Experimental.*` resolve. (Those are
    separate top-level namespaces on purpose: Lake's `isLocalModule` treats a name
    prefix as library ownership, so `Hilbert10.Experimental.*` would be claimed by the
    strict `Hilbert10` library too and its `sorry`s would become build errors.)
    """
    p = root / (module.replace(".", "/") + ".lean")
    return p if p.exists() else None


def imports_of(path: Path) -> list[str]:
    out = []
    for line in path.read_text().splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def closure(root: Path) -> set[str]:
    """Transitive repo-local import closure of the root module."""
    seen: set[str] = set()
    stack = [ROOT_MODULE]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        p = module_path(root, mod)
        if p is None:
            continue  # mathlib or a missing module; `lake build` is the judge of those
        seen.add(mod)
        stack.extend(imports_of(p))
    return seen


def strip_comments(text: str) -> list[tuple[int, str]]:
    """Source lines with Lean comments removed, paired with 1-based line numbers.

    Handles `--` line comments and nested block comments, including the `/-!` and `/--`
    doc forms. Stripping rather than skipping whole comment lines lets a docstring discuss
    this policy by name without tripping the check, while still seeing a `sorry` that
    shares a line with a trailing comment.
    """
    out: list[tuple[int, str]] = []
    depth = 0
    for lineno, line in enumerate(text.splitlines(), 1):
        kept: list[str] = []
        i = 0
        while i < len(line):
            two = line[i:i + 2]
            if depth == 0 and two == "--":
                break
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/" and depth > 0:
                depth -= 1
                i += 2
                continue
            if depth == 0:
                kept.append(line[i])
            i += 1
        out.append((lineno, "".join(kept)))
    return out


def sorries_in(path: Path) -> list[tuple[int, str]]:
    return [(lineno, code.strip())
            for lineno, code in strip_comments(path.read_text())
            if SORRY_RE.search(code)]


def main() -> int:
    root = repo_root()
    spine = closure(root)
    status = 0

    # (1) the spine is sorry-free
    for mod in sorted(spine):
        p = module_path(root, mod)
        assert p is not None
        for lineno, text in sorries_in(p):
            rel = p.relative_to(root)
            print(f"{rel}:{lineno}: sorry in the root import spine — {text}",
                  file=sys.stderr)
            status = 1

    # (2) no Experimental module is in the spine
    for mod in sorted(spine):
        if mod == EXPERIMENTAL_PREFIX or mod.startswith(EXPERIMENTAL_PREFIX + "."):
            print(f"{mod} is reachable from {ROOT_MODULE}.lean: experimental modules must "
                  f"not be imported by the production root spine", file=sys.stderr)
            status = 1

    # Informational: what is staged outside the spine.
    exp_dir = root / "Hilbert10Experimental"
    staged = sorted(p.relative_to(root) for p in exp_dir.rglob("*.lean")) if exp_dir.is_dir() else []
    n_sorry = sum(1 for p in staged if sorries_in(root / p))

    if status == 0:
        print(f"check_sorry_boundary: {len(spine)} spine module(s) sorry-free; "
              f"{len(staged)} experimental module(s) outside the spine "
              f"({n_sorry} containing sorries)")
    return status


if __name__ == "__main__":
    sys.exit(main())
