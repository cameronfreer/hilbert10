# Hilbert's tenth problem in Lean

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) development of the DPRM
theorem and the computability-theoretic form of Hilbert's tenth problem.

## Status

Semantic DPRM over `ℕ` is proved in staging. Promotion into the reviewed public spine is
pending. Remaining v1 work derives RE-completeness and undecidability of `NatSolvable`; v2
relates natural and integer solutions.

The public spine carries reviewed results; completed work stays in staging until promotion, and
[issue #1](https://github.com/cameronfreer/hilbert10/issues/1) records current progress. The
difference between the two libraries is a guarantee, not a build setting — see
[verification](#verification).

## Main result and remaining endpoints

Proved:

```lean
theorem dioph_iff_rePred {n : ℕ} (R : (Fin n → ℕ) → Prop) : Dioph {x | R x} ↔ REPred R
```

Still open — the H10 endpoints that consume it:

```lean
theorem rePred_natSolvable : REPred NatSolvable
theorem rePred_manyOneReducible_natSolvable {R : ℕ → Prop} : REPred R → R ≤₀ NatSolvable
theorem not_computablePred_natSolvable : ¬ ComputablePred NatSolvable
```

`NatSolvable` is solvability over `ℕ` of a finitely encoded polynomial: a predicate on
`PolynomialCode`, which carries a `Primcodable` instance, so `REPred` and `≤₀` apply to it
directly and it is a decision problem in the ordinary sense. Hilbert asked about integer
solutions; that equivalence is a separate layer on top of this one.

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
       ▲      semantic DPRM — proved              │
       │                                          │
       └──────────────────────────────────────────┘
                   the easy direction

   proof architecture:

     machine graph  ──►  semantic packed run  ──►  ExpDioph  ──►  Dioph
                                             ▲                ▲
                              selector encoding       mathlib's x ^ y


   Dioph {x | R x}  ──►  MvPolynomial (Fin n ⊕ Fin m) ℤ  ──►  PolynomialCode  ──►  NatSolvable
                            finite normal form               encoding        specialisation
```

All three arrows of the core are closed. A partial recursive function's graph is the trace
relation of a register machine; that is equivalent to the existence of a single number packing
the whole run; and acceptance by an arbitrary register machine is an exponential-Diophantine
condition, hence Diophantine by mathlib's Diophantineness of `x ^ y`.

The middle arrow was the project's deep risk, because the packed run carries a conjunction of
encoded transitions over a *variable* number of indices, and a representation of that would have
been a second Matiyasevich-sized theorem. It is closed by a selector encoding instead: the
transitions are replaced by a fixed number of identities between packed numbers, plus a finite
number of side conditions determined by the program and its register count rather than by the run
length. No bounded universal quantifier is represented anywhere.

The machine graph, selector arithmetisation, finite-tuple bridge, and final assembly are all
proved. Route-specific machinery disappears from the public theorem.

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
* guarded block packing, together with an exact exponential-Diophantine encoding of one
  unbounded computation — a decrement loop, the spike that fixed the block layout;
* a register machine with its semantics, and the renaming and concatenation discipline used to
  combine machines;
* a compiler from partial recursive codes to register machines, at the level of the accepted
  relation;
* the selector encoding, which makes acceptance by an arbitrary register machine an
  exponential-Diophantine condition;
* a finite-tuple bridge — an explicit `Nat.pair` coding whose decoder is computable and whose
  encoder's graph is Diophantine;
* the assembly of these into `REPred ↔ Dioph`.

Acceptance by a register machine is encoded exactly and in both directions: it is *equivalent*
to the existence of a packed run at arbitrary run length, and that packed run is described by a
finite system of exponential-Diophantine conditions. Both halves of the machine route therefore
exist; joining them into the public statements is bookkeeping over the two libraries' interfaces
rather than further mathematics.

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
  the source of the two TODOs this project aims to close. The `Poly`-to-`MvPolynomial` TODO is
  solved locally here, in the finite normal form and the ring map. Of the H10 TODO, the semantic
  DPRM component is now solved locally too; what remains is the natural-root endpoints,
  promotion into the spine, and Hilbert's integer formulation.

## License

Apache-2.0. See [LICENSE](LICENSE).
