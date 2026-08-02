# Hilbert's tenth problem in Lean

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) development of the DPRM
theorem and the computability-theoretic form of Hilbert's tenth problem.

## Status

Active development. None of the target theorems below is proved yet; what exists is the
infrastructure they are assembled from, listed under [library layers](#library-layers). Finished
work is promoted into the `Hilbert10` spine, everything else lives in `Hilbert10Experimental`,
and the difference between them is a guarantee rather than a build setting — see
[verification](#verification).

## Target

```lean
theorem dioph_iff_rePred {n : ℕ} (R : (Fin n → ℕ) → Prop) : Dioph {x | R x} ↔ REPred R

theorem rePred_natSolvable : REPred NatSolvable
theorem rePred_manyOneReducible_natSolvable {R : ℕ → Prop} : REPred R → R ≤₀ NatSolvable
theorem not_computablePred_natSolvable : ¬ ComputablePred NatSolvable
```

`NatSolvable` is solvability over `ℕ` of a finitely encoded polynomial — the decision problem
itself, as a predicate on a natural number. Hilbert asked about integer solutions; that
equivalence is a separate layer on top of this one.

## Scope

DPRM is developed as a **semantic** theorem: for each recursively enumerable predicate there
*exists* a representing polynomial. It is not a verified compiler.

The distinction is what makes the project finite. Because `R ≤₀ NatSolvable` is a proposition,
existential elimination may fix the representing code locally, and the reduction
`fun a => code.instantiate [a]` is computable in `a` because `code` is a constant. So H10 gets a
genuine computable many-one reduction without any uniform, data-valued

```lean
def compile : Nat.Partrec.Code → PolynomialCode   -- not a goal
```

which is where a verified polynomial programming language would begin. A constraint DSL, a
fresh-variable allocator, an optimiser and a polynomial pretty-printer are all outside the scope
of this development.

## Architecture

```
   REPred R  ──────────────────────────►  Dioph {x | R x}
       ▲          register machines,              │
       │          arithmetised runs               │
       └──────────────────────────────────────────┘
                   the easy direction

                    ExpDioph  ─────────►  Dioph
        exponential Diophantine      via mathlib's Diophantineness of x ^ y


   Dioph {x | R x}  ──►  MvPolynomial (Fin n ⊕ Fin m) ℤ  ──►  PolynomialCode  ──►  NatSolvable
                            finite normal form               encoding        specialisation
```

`ExpDioph` is an internal `ℕ`-valued exponential-polynomial layer; natural-number valuations are
what make `p ^ q` well specified, and mathlib's `pow_dioph` supplies the bridge down to `Dioph`.
The primary H10 predicate uses natural-number assignments throughout.

## Library layers

* a finite `MvPolynomial` normal form for mathlib's semantic `Dioph`, and the ring map from
  `MvPolynomial` into mathlib's `Poly`;
* a permissive sparse polynomial encoding with computable evaluation, denotation into
  `MvPolynomial`, and parameter specialisation;
* the easy direction `Dioph → REPred`, and the nonuniform many-one reduction from a represented
  predicate to `NatSolvable`;
* an exponential-Diophantine layer with its closure lemmas, including binomial coefficients and
  binary submasks;
* guarded block packing, and an exact exponential-Diophantine encoding of an unbounded
  computation;
* a register machine with its semantics, and the renaming and concatenation discipline used to
  combine machines.

The remaining DPRM work scales the register-machine encoding to arbitrary computations.

## Repository layout

* `Hilbert10.lean` and `Hilbert10/` — the public import spine.
* `Hilbert10Experimental/` — work awaiting promotion into the spine.
* `Hilbert10Experimental/ForMathlib/` — self-contained additions intended for mathlib.
* `Hilbert10Experimental/Spike/` — executable evidence supporting architectural decisions.
* `scripts/` — the import-boundary and axiom-audit checks run by CI.

"Experimental" describes promotion status, not a weaker logic or an unchecked target: both
libraries are default build targets, so everything here typechecks. What differs is the
guarantee, and promotion is the reviewable event — a module entering the spine is a claim that it
is finished.

## Verification

Three CI gates:

* both libraries build, the spine additionally under `warningAsError`;
* `scripts/check_sorry_boundary.py` — the spine is free of `sorry` and imports nothing from
  staging;
* `scripts/AxiomAudit.lean` — an environment sweep over every declaration owned by a spine
  module, private and compiler-generated ones included, rejecting anything beyond `propext`,
  `Classical.choice` and `Quot.sound`.

The last two gate the spine only. Staged work is audited when it is promoted, which is what makes
promotion mean something.

## Building

Lean and the mathlib revision are pinned by `lean-toolchain` and `lakefile.toml`.

```bash
lake exe cache get   # mathlib build cache
lake build
```

## Roadmap

The milestone plan and dependency graph live in
[issue #1](https://github.com/cameronfreer/hilbert10/issues/1). Design decisions and the
reasoning behind them are recorded in the module docstrings and in the issues they cite.

## References

* Yuri Matiyasevich, *Hilbert's Tenth Problem*, MIT Press, 1993.
* `Mathlib/NumberTheory/Dioph.lean` — the `Dioph`, `DiophFn` and `Poly` API this builds on, and
  the source of the two TODOs this project aims to close.

## License

Apache-2.0. See [LICENSE](LICENSE).
