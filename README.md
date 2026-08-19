# Hilbert's tenth problem in Lean

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) development of the DPRM
theorem and the computability-theoretic form of Hilbert's tenth problem.

## Status

All of v1 and v2 is **available in the public spine**: semantic DPRM over `ℕ`, the
RE-completeness and undecidability of `NatSolvable`, and Hilbert's own integer formulation —
`NatSolvable` and `IntSolvable` are many-one equivalent, so the endpoints hold in both forms.

The spine is `Hilbert10.lean` and everything it imports, and it is what the CI gates cover: no
`sorry`, no axioms beyond the three standard ones, and a strict build. What remains in staging is
route evidence and one module bound for mathlib, neither of which the results depend on;
[issue #1](https://github.com/cameronfreer/hilbert10/issues/1) records current progress. The
difference between the two libraries is a guarantee, not a build setting — see
[verification](#verification).

## Main results

Semantic DPRM:

```lean
theorem dioph_iff_rePred {n : ℕ} (R : (Fin n → ℕ) → Prop) : Dioph {x | R x} ↔ REPred R
```

and the H10 endpoints that consume it:

```lean
theorem rePred_natSolvable : REPred NatSolvable
theorem natSolvable_re_complete {α : Type*} [Primcodable α] {R : α → Prop} :
    REPred R → R ≤₀ NatSolvable
theorem not_computablePred_natSolvable : ¬ ComputablePred NatSolvable
```

`NatSolvable` is therefore many-one complete among recursively enumerable predicates, which says
more than undecidability: undecidability is the corollary obtained by reducing the halting
problem. All of these are in the public spine, `#print axioms`-clean and covered by the gates.

`NatSolvable` is solvability over `ℕ` of a finitely encoded polynomial: a predicate on
`PolynomialCode`, which carries a `Primcodable` instance, so `REPred` and `≤₀` apply to it
directly and it is a decision problem in the ordinary sense.

Hilbert asked about integer solutions, and that formulation is a layer on top of this one:

```lean
theorem intSolvable_manyOneReducible_natSolvable : IntSolvable ≤₀ NatSolvable
theorem natSolvable_manyOneReducible_intSolvable : NatSolvable ≤₀ IntSolvable
theorem intSolvable_re_complete {α : Type*} [Primcodable α] {R : α → Prop} :
    REPred R → R ≤₀ IntSolvable
theorem not_computablePred_intSolvable : ¬ ComputablePred IntSolvable
```

The two reductions are the substitution `x = u - v` and Lagrange's four-square theorem, each
proved as an equivalence of codes and then packaged with the computability of the code
transformation. Stating them separately from the endpoints says the sharper thing: the two
formulations have the same many-one degree, not merely that both are undecidable.

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
* the assembly of these into `REPred ↔ Dioph`;
* the integer formulation: a small code algebra, the substitution `x = u - v`, the four-square
  constraint transformation, and the two reductions they certify.

Acceptance by a register machine is encoded exactly and in both directions: it is *equivalent*
to the existence of a packed run at arbitrary run length, and that packed run is described by a
finite system of exponential-Diophantine conditions. Those layers are joined by `REPred.dioph`
and `dioph_iff_rePred`, and all of them are in the public spine.

## Repository layout

* `Hilbert10.lean` and `Hilbert10/` — the public import spine.
* `Hilbert10Experimental/` — work outside the spine: route evidence, and material staged for
  upstreaming. Nothing the public results depend on.
* `Hilbert10/Internal/` — implementation dependencies of the public results. Importable, but
  **not** part of the supported API: anything here may change or disappear without notice.
  `Hilbert10/Internal/ForMathlib/` holds self-contained additions intended for mathlib, kept
  locally under upstream-compatible names until they land there.
* `Hilbert10Experimental/Spike/` — executable evidence supporting architectural decisions.
* `scripts/` — the import-boundary and axiom-audit checks run by CI.

"Experimental" describes promotion status, not a weaker logic or an unchecked target: both
libraries are default build targets, so everything here typechecks. What differs is the
guarantee, and promotion is the reviewable event — a module entering the spine is a claim that it
is finished. The v1 promotion is recorded tranche by tranche in
[issue #52](https://github.com/cameronfreer/hilbert10/issues/52); v2's modules were written
inside the spine from the start.

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
[docs/proof-map.md](docs/proof-map.md) is a routing table from each headline result down to the
module that proves it and the mathlib inputs it rests on.
[docs/lessons.md](docs/lessons.md) is a retrospective on what the DPRM formalisation actually
cost, with the counterexamples and cost claims tied to the files that support them;
[docs/comparison.md](docs/comparison.md) compares the route taken here with the Coq
mechanisation of Larchey-Wendling and Forster.

## References

* Yuri Matiyasevich, *Hilbert's Tenth Problem*, MIT Press, 1993.
* `Mathlib/NumberTheory/Dioph.lean` — the `Dioph`, `DiophFn` and `Poly` API this builds on, and
  the source of the two TODOs this project aims to close. The `Poly`-to-`MvPolynomial` TODO is
  solved locally here, in the finite normal form and the ring map. Of the H10 TODO, the semantic
  DPRM component, the endpoints and Hilbert's integer formulation are now solved locally too, for
  this project's encoded wire format; upstreaming any of it is a separate question.

## Development provenance

This project was developed with substantial assistance from Claude-family and OpenAI GPT/Codex
models. They were used for planning, Lean code and proof drafts, debugging, documentation, and
cross-review of proposed designs and proofs. The workflows used
[lean4-skills](https://github.com/cameronfreer/lean4-skills) and
[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) to inspect and test against the pinned
Lean/mathlib environment.

The repository author selected the architecture, reviewed and revised the generated material,
verified the cited claims, and takes responsibility for the resulting mathematics and code.
Lean's kernel, the build, the import-boundary check, and the axiom audit — not model review —
are the trust boundary.

AI use is disclosed separately when code is submitted upstream, according to the receiving
project's policy; mathlib's is
[here](https://leanprover-community.github.io/contribute/index.html#use-of-ai).

## License

Apache-2.0. See [LICENSE](LICENSE).
