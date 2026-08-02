/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Hilbert's tenth problem

Root of the public `Hilbert10` library.

Everything reachable from `Hilbert10.lean` is finished work: sorry-free, built with
`warningAsError`, and swept for nonstandard axioms by `scripts/AxiomAudit.lean`. Promotion into
this spine is therefore the reviewable event — a module appearing here is a claim that it is
done, not merely that it compiles.

Work in progress lives in the separate `Hilbert10Experimental` library, which
`scripts/check_sorry_boundary.py` keeps out of this import closure. See `README.md` for the
layout and [issue #1](https://github.com/cameronfreer/hilbert10/issues/1) for the roadmap.
-/
