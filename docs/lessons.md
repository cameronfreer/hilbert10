# What formalising DPRM actually cost

A retrospective on the machine route, written when `dioph_iff_rePred` landed
([#23](https://github.com/cameronfreer/hilbert10/issues/23)). Every claim below names the file,
theorem or issue that supports it, so that a reader can disagree with the conclusion by checking
the artifact.

The short version: **the formalisation relocated the hard part.** The number theory DPRM is
famous for was not the dominant obstacle. Exact machine soundness, and choosing a packed
representation that makes soundness provable, were.

---

## 1. The machine route did not need general bounded-universal elimination

The expected shape was

```
packed run  →  ∀ i < N, Step i  →  bounded product / binomial machinery
```

and the bounded universal was tracked as the project's deep risk for most of M4
([#21](https://github.com/cameronfreer/hilbert10/issues/21),
[#49](https://github.com/cameronfreer/hilbert10/issues/49)).

It was never represented. For a fixed program, two selector lanes per instruction make the whole
run equivalent to

* one-hot selector identities,
* a program-counter identity and a jump identity,
* one update identity per register,
* finitely many side conditions per selected branch.

The count depends on the program and its register count, never on the run length. So
`Aggregation (k + 1)` is proved with no bounded universal quantifier represented anywhere.

**Evidence.** `Hilbert10Experimental/SelectorRegsGlobal.lean` (`GlobalConditionsK`,
`globalConditionsK_iff`) and `Hilbert10Experimental/SelectorRegsDioph.lean`
(`aggregation_succ`, `dioph_accepts_regs`). The two combinators the packaging needs —
`ExpDioph.fin_and` and `ExpTerm.sumTerm`, both in `Hilbert10Experimental/ExpDioph.lean` — are
finite conjunction and finite summation at a length fixed by the program, which is why neither
conceals an input-dependent quantifier.

**Against the literature, carefully.** This does not contradict the mechanised accounts. The
Coq/FRACTRAN development uses bounded-universal elimination explicitly
([Larchey-Wendling and Forster, *Hilbert's Tenth Problem in Coq*,
arXiv:2003.04604](https://arxiv.org/abs/2003.04604)); the Isabelle register-machine account
removes the time dependence and reports a fixed system of equations
([Bayer, David, Pal, Stock and Schleicher, *The DPRM Theorem in Isabelle*, ITP
2019](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.33)). What was wrong
was our own summary: the frozen comparison in
[#15](https://github.com/cameronfreer/hilbert10/issues/15) treated the two routes as needing the
same theorem. They do not. The direct route does; this one eliminated its specialised
conjunction through selectors. [comparison.md](comparison.md) sets the two side by side in
detail, including where they agree.

---

## 2. Most of the soundness content was "no hidden carry or borrow"

Two counterexamples changed the design, and both are kept in the repository as regressions
rather than as prose.

**A naive decrement packing admits a false run even when every digit is below the base.** The
step identity is satisfied by a trace that is not a run, because a borrow propagates
consistently. What is missing is a no-borrow *guard bit*, not a digit bound — power-of-two
blocks with a spare bit per block are essential, not a convenience.
See `not_sound_without_guard_bits` in `Hilbert10Experimental/Spike/DecLoop.lean`.

**An inner configuration field can overflow into the next while the packed number stays globally
bounded.** So `EncodedStep` has to bound the *written* successor value and the jump target, not
merely the code. The counterexample (width 2, registers `[3, 0]`) is kept as an `example` in
`Hilbert10Experimental/ConfigCoding.lean`, immediately after `not_encodedStep_of_not_fits`.

A further refinement mattered: those bounds must be **conditional on the selected branch**,

```lean
selector = 0 ∨ target < 2 ^ w
```

rather than imposed on every target in the program. An unreachable oversized jump must not
invalidate an otherwise valid encoding — and the per-branch form is exactly what
`fieldsCode_selected_smul_eq_iff` (`Hilbert10Experimental/SelectorMask.lean`) consumes.
`Spike/SelectorSlice.lean` exists partly to keep this honest: its third instruction carries an
oversized target that is reachable, so both regimes are exercised.

**The lesson.** The informal instruction "choose the base large enough" is not wrong, but it
hides nearly all of the soundness obligations.

---

## 3. Binary masking was much cheaper here than mechanisation costs elsewhere suggest

The feared coefficient-extraction theorem is
`Hilbert10Experimental/ForMathlib/ChooseDigit.lean` — a 90-line file, of which the headline
`Nat.choose_eq_baseDigit` is 19 lines, composed from mathlib's existing digits API
(`Nat.digits_ofDigits`, `Nat.getD_digits`), binomial bounds and `add_pow`. Lucas-to-submask and
the masking layer (`ForMathlib/BinarySubmask.lean`, `ForMathlib/SubmaskChoose.lean`,
`ExpDiophChoose.lean`) were similarly small.

The Isabelle account reports binary-digit infrastructure as a substantial share of its effort,
because those utilities had to be built there. Mathlib's `Nat.testBit`, digits, Lucas and
binomial APIs changed the economics completely.

**The lesson.** Proof-cost estimates do not transfer between libraries. A step that dominated
one mechanisation can be a page in another, and the reverse is equally possible.

---

## 4. Unary to finite arity was not "reindexing"

Once unary partial-recursive graphs were Diophantine it was tempting to call the general theorem
a reindexing. That would have concealed a circularity:

* a `Nat.Partrec.Code` consumes one natural number;
* `REPred R` may consume a `Fin n → ℕ`;
* using `Primcodable`'s encoding would require proving *that* encoding's graph Diophantine;
* invoking closure under arbitrary computable preimages would already be DPRM.

The honest bridge is explicit and small: a right-associated `Nat.pair` encoding, a computable
`Nat.unpair` decoder, a round trip, and a Diophantine graph obtained from the piecewise
polynomial graph of `Nat.pair`. See `Hilbert10Experimental/TupleCoding.lean`, whose docstring
records both traps.

**The lesson.** A "standard coding" step that a paper can safely suppress is a real obligation
for a formal API. The cost was one short module; the cost of not noticing would have been a
circular proof.

---

## 5. Semantic DPRM genuinely does not need a polynomial compiler

No function

```lean
def compile : Nat.Partrec.Code → PolynomialCode   -- never needed
```

was written. The proof fixes a representing polynomial existentially inside a proposition, and
the eventual H10 reduction specialises that fixed code computably
([#1](https://github.com/cameronfreer/hilbert10/issues/1) records the scope argument;
`Hilbert10Experimental/Specialization.lean` carries it out).

Two precisions worth keeping. Eliminating an existential into a `Prop` is `Exists.elim`, which
needs no choice. And `Classical.choice` in the final axiom list does not come from that step: it
is already present in the wire format, well below any specialisation —
`#print axioms Hilbert10.PolynomialCode.eval_denote` reports it.

**The lesson.** The scope reduction was not philosophy. It removed the certificate/allocator/DSL
project that a uniform compiler would have required — see
[#29](https://github.com/cameronfreer/hilbert10/issues/29), which exists to keep that project
out.

---

## 6. Total, permissive encodings won every time

`PolynomialCode` gives semantics to every code, well formed or not; completeness is a separate
theorem. `configField` and `setField` are total on every natural number, with bounds appearing
as hypotheses on the theorems that need them rather than as a well-formedness predicate threaded
through the development (`Hilbert10Experimental/ConfigCoding.lean`, "Total, permissive
semantics").

**The lesson.** Make lookup total, then state exact local bounds where soundness actually needs
them. The alternative — a global well-formedness predicate — contaminates every downstream
statement, and was explicitly rejected.

---

## 7. An `ℕ`-valued exponential layer was the right intermediate language

`ExpTerm`/`ExpDioph` (`Hilbert10Experimental/ExpDioph.lean`) aligns with mathlib's `DiophFn`
combinators, so the bridge down to `Dioph` is one structural induction (`ExpTerm.diophFn`).
Truncated subtraction supplies conjunction over the naturals; `div` and `mod` make digit
extraction compositional. The layer stayed small while carrying the whole arithmetisation, and
grew by exactly two combinators when the selector encoding arrived.

---

## What we had wrong

Mostly the literature was fine and our abstractions were too coarse.

| Belief | Status |
|---|---|
| "Both routes eventually need the same bounded-universal theorem" | **False.** The direct route does; the machine route eliminates its specialised conjunction through selectors (#49). |
| "Digit bounds prevent the bad decrement encoding" | **False.** A no-borrow guard bit is required (`Spike/DecLoop.lean`). |
| "Bound every jump target in the program" | **Too strong,** and incompatible with a sharp step equivalence. Only selected targets must fit. |
| "The `n`-ary theorem follows from the unary one by reindexing" | **Incomplete.** An explicit tuple graph is required (`TupleCoding.lean`). |
| "Binomial coefficient extraction will take weeks" | **False in this library** — most of the infrastructure was already in mathlib. |
| "Fixing the representing polynomial requires classical choice" | **Imprecise.** Existential elimination into a proposition-valued reduction does not. |
| "Unpairing requires implementing `Nat.sqrt` on the machine" | **False.** Enumerating `Nat.pair`'s shells via `pairNext` gives a simpler terminating machine with an exact step bound (`ForMathlib/PairingEnumeration.lean`, #51). |

---

## Provenance

External:

* Dominique Larchey-Wendling and Yannick Forster, *Hilbert's Tenth Problem in Coq*,
  [arXiv:2003.04604](https://arxiv.org/abs/2003.04604) — the FRACTRAN route, with explicit
  bounded-universal elimination.
* Jonas Bayer, Marco David, Abhik Pal, Benedikt Stock and Dierk Schleicher, *The DPRM Theorem in
  Isabelle*, ITP 2019,
  [10.4230/LIPIcs.ITP.2019.33](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.33)
  — the register-machine route, and the source of the binary-digit cost comparison.
* Yuri Matiyasevich, *Hilbert's Tenth Problem*, MIT Press, 1993.

Internal: decisions are recorded in the issues they were made in, and the module docstrings cite
those issues. The route decision is #15; the arithmetisation epic is #21; the aggregation
obstacle and its dissolution are #49; the final assembly is #23. Where a claim above is about
cost or size, it is measured against the files named, at the commit that closed the corresponding
issue.

Two caveats on reading this document. First, the counterexamples are regressions in the build,
so they stay true; the cost claims are snapshots and will drift. Second, the comparison in §1 and
§3 rests on how the two cited papers describe their own developments — the checkable part is what
this repository does, not what they had to do.
