/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ExpDioph

/-!
# Route spike, direct route: sequence coding

Issue #15, second slice. The direct route replaces the machine's packed registers with
*coded sequences*, so this measures what that costs.

## The shape being tested

A witness-free step relation would understate the cost and merely retest the arithmetic
trace problem the machine slice already validated. What `prec` actually produces is a step
relation with **step-local existential witnesses**:

```
∀ i < t, ∃ w, Step params i (state i) (state (i + 1)) w
```

so the slice must code two variable-length objects — the state history *and* the collection
of per-step witness tuples — and then eliminate the bounded universal.

## Two gates

1. **Sequence coding.** Lookup has an `ExpDioph` graph, and every finite sequence is
   encodable.
2. **Bounded verification.** The variable conjunction of the *witnessed* step relation
   collapses to one `ExpDioph` relation, in both directions.

Gate 2 is where #33 — or a differently named theorem of comparable difficulty, whether
coefficient extraction, CRT aggregation, or masking — must be charged. The cost must not be
allowed to disappear into a strong sequence-coding lemma: what gets recorded is the theorem
that actually converts all indexed checks into one finite equation.

## Gate 1, first half: the lookup graph

`beta a b i = a % (1 + (i + 1) * b)` is the Gödel β-function. Its graph is `ExpDioph` for
free, because `mod`, `mul` and `add` are `ExpTerm` constructors — a direct consequence of
#16's design decision to make `div` and `mod` constructors rather than closure lemmas.
-/

namespace Hilbert10Experimental

/-- The Gödel β-function: the `i`-th entry of the sequence coded by `(a, b)`. -/
def beta (a b i : ℕ) : ℕ := a % (1 + (i + 1) * b)

/-- The lookup term, over variables `a`, `b`, `i` given as an index map. -/
def betaTerm {α : Type} (a b i : α) : ExpTerm α :=
  .mod (.var a) (.add (.const 1) (.mul (.add (.var i) (.const 1)) (.var b)))

@[simp] theorem betaTerm_eval {α : Type} (a b i : α) (v : α → ℕ) :
    (betaTerm a b i).eval v = beta (v a) (v b) (v i) := rfl

/-- **Gate 1, first half.** The graph of the β-function is exponential Diophantine, with no
witnesses at all. This is free because `mod` is an `ExpTerm` constructor. -/
theorem expDioph_beta {α : Type} (a b i r : α) :
    ExpDioph {v : α → ℕ | beta (v a) (v b) (v i) = v r} :=
  ExpDioph.of_eq (s := betaTerm a b i) (t := .var r)

theorem dioph_beta {α : Type} (a b i r : α) :
    Dioph {v : α → ℕ | beta (v a) (v b) (v i) = v r} :=
  (expDioph_beta a b i r).dioph

/-! ### What remains of gate 1

The other half is the encoding theorem: for every finite sequence `s` and length `n`, there
are `a, b` with `beta a b i = s i` for all `i < n`. That is the Chinese-remainder argument —
choose `b` a common multiple making the moduli `1 + (i + 1) * b` pairwise coprime and each
larger than every entry, then take `a` by CRT. Mathlib supplies `Nat.chineseRemainder`; the
coprimality bookkeeping is the work.
-/

end Hilbert10Experimental
