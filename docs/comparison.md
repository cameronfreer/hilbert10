# Comparison with the Coq mechanisation

Dominique Larchey-Wendling and Yannick Forster, *Hilbert's Tenth Problem in Coq (Extended
Version)*, Logical Methods in Computer Science **18**(1), 2022, 35:1–35:41
([lmcs.episciences.org/9153](https://lmcs.episciences.org/9153/pdf), also
[arXiv:2003.04604v5](https://arxiv.org/abs/2003.04604)). The system has since been renamed
Rocq; the paper says Coq, and so does this document.

Theirs is the first full mechanisation of DPRM. It reaches several of our most important
engineering conclusions independently, and its central arithmetisation is materially different
from ours. Both facts are worth recording: the agreements are evidence that those lessons are
about formalising this theorem rather than about Lean, and the difference is the one place where
our route is genuinely cheaper.

Section numbers below refer to the LMCS version, and quoted phrases are from it.

---

## Where the conclusions agree

**A register-machine intermediary works, and machine verification needs compositional
reasoning.** They start from Minsky-machine recognisability and give "a certified compiler from
µ-recursive functions" to it (§1, §10), using "the compositional reasoning techniques developed"
in earlier work (§6.1, §10). That is the same conclusion we reached with `Realises`,
`PartRealises`, the clean-scratch calling convention, the renaming discipline and the controller
invariants — and the reason
[#39](https://github.com/cameronfreer/hilbert10/issues/39) exists as its own issue.

**Diophantine closure needs its own language.** Their `Drel`/`Dfun` classes (Definitions 2.1,
2.3) with automated "Diophantine shape recognition" (§2.2) play the role of our
`ExpTerm`/`ExpDioph`: routine closure and witness plumbing become structural, leaving semantic
equivalences as the real obligations. They also note that the informal literature moves between
"several equivalent approaches to characterise these relations" (§2.1) and that a mechanisation
has to fix one — the same reason our layer is `ℕ`-valued and explicit about it.

**Fixed program data should be hard-coded.** In their Gödel encoding the primes representing
registers "are hard-coded in the Diophantine representation, which means we do not need to
encode the algorithm that actually computes them, which would otherwise be very painful"
(Proposition 8.1). Our analogue is compiling `P.get p` into `ExpTerm.const` coefficients and a
finite conjunction over the fixed program, with no lookup at evaluation time — the guardrail
recorded in `SelectorRegsDioph.lean`'s docstring.

**Slack in a packed representation is load-bearing, not decorative.** This is the sharpest
convergence. Matiyasevich's sparse ciphers use base `r := 2^(2q)`; they raise it to `r := 2^(4q)`
because the product of ciphers "generates artefacts on in-between digits that need to be masked
out and, with Matiyasevich's choice for `r`, some overflow could occur within these artefacts, a
subtlety which we speculate he might have missed" (§5.2). They add that "any power of 2 greater
than `2^(2q+1)` would work as well".

That is our guard bit, our deliberately oversized `runWidth`, and our carry bounds, arrived at
independently and for the same reason. Our version of the finding is two executable
counterexamples rather than a remark
(`Spike/DecLoop.lean`, `ConfigCoding.lean`; see [lessons.md §2](lessons.md)), but the lesson is
identical: informal "choose the base large enough" hides the obligation, and the natural first
choice of base is too small.

**Binary submasks via binomial coefficients and Lucas are the right bridge.** They prove
`a ≼ b ↔ C(b,a) is odd` and derive bitwise operations from it, proving Lucas's theorem for the
purpose (§5.2, Appendix B); the binomial coefficient is recovered as "the `k`-th digit of the
development of `(1 + q)^n`" (§5.2). Those are exactly our
`Nat.isBinarySubmask_iff_odd_choose` and `Nat.choose_eq_baseDigit`. The difference is cost, not
content: mathlib already had Lucas and the digits API, so our layer is a few short files
(see [lessons.md §3](lessons.md)).

**The summit theorem is short because the infrastructure is not.** Their `DPRM.v` is reported as
170 lines (Appendix A). Our `DPRM.lean` is 139, and `TupleCoding.lean` another 156 — against an
import closure of 45 modules and roughly 11,700 lines. In both developments the final assembly
hides the entire machine, arithmetic and representation stack, and neither line count means
anything on its own.

---

## The central difference

Their chain is

```
Halt ⪯ PCP ⪯ MM ⪯ FRACTRAN ⪯ DIO_FORM ⪯ DIO_ELEM ⪯ DIO_SINGLE ⪯ H10
```

with µ-recursive functions compiled into `MM` (§1, Figure in §1.2). FRACTRAN is chosen because
its one-step relation is very simple to represent; an arbitrary-length chain is then encoded
with base-`q` digits and eliminated by a general theorem on **bounded universal quantification**,
built on Matiyasevich's sparse ciphers (§2.3, §5.2, §§6–7).

Ours is

```
Nat.Partrec.Code → register machine → packed lanes → selector identities → ExpDioph → Dioph
```

We expected to need the same bounded-universal theorem — it was the tracked risk of
[#21](https://github.com/cameronfreer/hilbert10/issues/21) and
[#49](https://github.com/cameronfreer/hilbert10/issues/49) for most of the project. Instead, for
a fixed finite program, selectors replace

```
∀ i < n, EncodedStep P w (block R i) (block R (i + 1))
```

by finitely many global identities and masks, whose number depends on the program and its
register count but never on the run length. We dissolved the bounded conjunction rather than
representing it.

**This does not refute their construction, and does not make ours stronger.** They prove the
generic closure result — that a Diophantine relation has Diophantine reflexive-transitive
closure — which is reusable and is a genuine theorem about arbitrary relations. We prove the
narrower fact needed for compiled register machines. The narrow theorem was substantially
cheaper in our environment; the general one is worth more.

---

## Other differences

| | Coq development | This development |
|---|---|---|
| Intermediate model | Minsky machine → FRACTRAN | register machine, directly |
| RE interface | `MM`-recognisability, later related to µ-recursion | mathlib's `REPred`, directly |
| Output | computes a *single* Diophantine equation from a recogniser (Theorem 8.3) | semantic `REPred ↔ Dioph`; deliberately no `Code → PolynomialCode` compiler |
| Computability | synthetic — definability in Coq without axioms certifies the reductions (§2.1) | explicit mathlib `Primrec` / `Computable` / `Partrec` / `REPred` |
| Number theory | formalises exponentiation, Lucas, sparse ciphers, bounded-∀ elimination | reuses mathlib's `pow_dioph`, Lucas, `choose` and digits |
| Tuples | vectors and valuations identified in the exposition | explicit `tupleCode`/`tupleDecode` with a round trip and a Diophantine graph |
| Endpoints | natural *and* integer H10 undecidability included | semantic DPRM proved; natural-root endpoints, promotion and the integer version remain |

Their Theorem 8.3 is the substantive strength: *one can compute* a single equation from a machine
recogniser, which is more than an existence statement. Ours is intentionally semantic and
proposition-valued, for the scope reason recorded in
[#1](https://github.com/cameronfreer/hilbert10/issues/1) — and in exchange it lands directly on
mathlib's own notion of a recursively enumerable predicate, and avoids the polynomial compiler
that the intended H10 reductions do not need.

---

## Provenance

Every claim about the Coq development above is drawn from the LMCS text, at the section given,
and the quoted phrases are verbatim. Nothing here is based on reading their Coq sources, so
statements about what their code does — as opposed to what the paper says it does — should be
treated as second-hand. Claims about this repository name the file or theorem and are checkable
in the build.

Line counts are snapshots: theirs as reported in their Appendix A, ours measured at the commit
that added this document.
