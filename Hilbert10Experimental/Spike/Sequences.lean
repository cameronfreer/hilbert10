/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ExpDioph
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorial.Basic

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

/-! ### Gate 1, second half: the encoding theorem

Built on `Nat.chineseRemainderOfFinset`, which mathlib motivates by the β-function itself,
rather than on a recursive CRT of our own.

The modulus at index `i` is `1 + (i + 1) * b` with `b = n ! * (M + 1)` and `M` bounding the
entries. The factorial is used **only semantically**, to show an encoding exists; it does not
appear in any `ExpDioph` relation, so gate 1 charges no factorial-graph obligation.
-/

/-- The moduli used to code a sequence with spacing `b`. -/
private def modulus (b i : ℕ) : ℕ := 1 + (i + 1) * b

private theorem modulus_pos (b i : ℕ) : 0 < modulus b i := by simp [modulus]

/-- Any divisor of a modulus is coprime to the spacing: it divides `1 + (i + 1) * b`, and a
common factor with `b` would have to divide `1`. -/
private theorem coprime_of_dvd_modulus {b i d : ℕ} (hd : d ∣ modulus b i) :
    Nat.Coprime d b := by
  have hgd : Nat.gcd d b ∣ modulus b i := (Nat.gcd_dvd_left d b).trans hd
  have hgb : Nat.gcd d b ∣ (i + 1) * b := (Nat.gcd_dvd_right d b).mul_left (i + 1)
  have h1 : Nat.gcd d b ∣ 1 := by
    have := Nat.dvd_sub hgd hgb
    simpa [modulus] using this
  exact Nat.dvd_one.mp h1

/-- Distinct moduli are coprime, provided the spacing is divisible by the index gap. -/
private theorem coprime_modulus {b i j : ℕ} (hij : i < j)
    (hdvd : (j - i) ∣ b) : Nat.Coprime (modulus b i) (modulus b j) := by
  set d := Nat.gcd (modulus b i) (modulus b j) with hd
  have hdi : d ∣ modulus b i := Nat.gcd_dvd_left _ _
  have hdj : d ∣ modulus b j := Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime d b := coprime_of_dvd_modulus hdi
  -- `d` divides the difference of the moduli, which is `(j - i) * b`
  have hdiff : d ∣ (j - i) * b := by
    have := Nat.dvd_sub hdj hdi
    have heq : modulus b j - modulus b i = (j - i) * b := by
      simp only [modulus]
      have : (j + 1) * b - (i + 1) * b = (j - i) * b := by
        rw [← Nat.sub_mul]
        congr 1
        omega
      omega
    rwa [heq] at this
  -- coprimality with `b` promotes that to dividing `j - i`, hence dividing `b`
  have hdji : d ∣ j - i := (Nat.Coprime.dvd_of_dvd_mul_right hcop hdiff)
  have hdb : d ∣ b := hdji.trans hdvd
  exact hcop.eq_one_of_dvd hdb

end Hilbert10Experimental
