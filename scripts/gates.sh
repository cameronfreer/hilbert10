#!/usr/bin/env bash
# Run every release gate, in CI order, from any working directory.
#
#   1. `lake build`            — both libraries; the spine under `warningAsError`
#   2. check_sorry_boundary.py — spine sorry-free, no staging imports, covers Hilbert10/
#   3. AxiomAudit.lean         — every spine declaration uses only the three standard axioms
#   4. ApiLeakageAudit.lean    — public statements mention no internal or staged constant
#
# Stops at the first failure; exit status is that gate's. This is the command a release is
# verified with, so a clean run here is the same evidence CI would produce for the tree.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

run() { printf '\n== %s ==\n' "$1"; shift; "$@"; }
run "build"          lake build
run "sorry boundary" python3 scripts/check_sorry_boundary.py
run "axiom audit"    lake env lean scripts/AxiomAudit.lean
run "API hygiene"    lake env lean scripts/ApiLeakageAudit.lean
printf '\nall gates passed\n'
