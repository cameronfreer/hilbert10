/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Internal.CodeAlgebra

/-!
# The four-square constraint transformation

Issue #28, fourth piece. A natural root of `p` is an integer root of

```
p(x)² + Σ_{i < n} (xᵢ - (aᵢ² + bᵢ² + cᵢ² + dᵢ²))²
```

because over `ℤ` a sum of squares vanishes exactly when every summand does, and Lagrange's
theorem says the naturals are exactly the sums of four squares.

## Constraints, not substitution

The original variables are *kept*. Nothing is substituted into `p`, which is why this direction
does not expand every occurrence of every variable — unlike `x = u - v`, where the difference
really has to be substituted. That asymmetry between the two reductions is real and was expected.

## Layout, frozen in #28

For `n := p.arity`, the transformed code uses `5 * n` variables:

* `0 .. n-1` — the original `xᵢ`;
* `n + 4i .. n + 4i + 3` — the four-square witnesses for `xᵢ`.

## Main definitions

* `Hilbert10.PolynomialCode.fourSquares`
-/

namespace Hilbert10

namespace PolynomialCode

/-- The sum of four squares drawn from variable `i`'s witness block. -/
def fourSq (n i : ℕ) : PolynomialCode :=
  add (add (npow (X (n + 4 * i)) 2) (npow (X (n + 4 * i + 1)) 2))
    (add (npow (X (n + 4 * i + 2)) 2) (npow (X (n + 4 * i + 3)) 2))

/-- The constraint forcing `xᵢ` to equal a sum of four squares, as a square so that it is
nonnegative over `ℤ`. -/
def fourSqConstraint (n i : ℕ) : PolynomialCode :=
  npow (add (X i) (neg (fourSq n i))) 2

/-- **The four-square transformation.** -/
def fourSquares (p : PolynomialCode) : PolynomialCode :=
  add (npow p 2)
    (((List.range p.arity).map fun i => fourSqConstraint p.arity i).foldr add zero)

/-! ### Evaluation -/

theorem evalInt_foldr_add {α : Type*} (l : List α) (f : α → PolynomialCode) (y : List ℤ) :
    evalInt ((l.map f).foldr add zero) y = (l.map fun i => evalInt (f i) y).sum := by
  induction l with
  | nil => simp [zero]
  | cons a as ih => simp only [List.map_cons, List.foldr_cons, evalInt_add, ih, List.sum_cons]

@[simp] theorem evalInt_fourSq (n i : ℕ) (y : List ℤ) :
    evalInt (fourSq n i) y
      = (y.getD (n + 4 * i) 0) ^ 2 + (y.getD (n + 4 * i + 1) 0) ^ 2
        + ((y.getD (n + 4 * i + 2) 0) ^ 2 + (y.getD (n + 4 * i + 3) 0) ^ 2) := by
  simp [fourSq]

@[simp] theorem evalInt_fourSqConstraint (n i : ℕ) (y : List ℤ) :
    evalInt (fourSqConstraint n i) y
      = (y.getD i 0 - evalInt (fourSq n i) y) ^ 2 := by
  simp only [fourSqConstraint, evalInt_npow, evalInt_add, evalInt_neg, evalInt_X]
  ring

/-- The value of the transformed code: the original squared, plus one square per variable. -/
theorem evalInt_fourSquares (p : PolynomialCode) (y : List ℤ) :
    evalInt (fourSquares p) y
      = (evalInt p y) ^ 2
        + ((List.range p.arity).map fun i =>
            (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2).sum := by
  simp only [fourSquares, evalInt_add, evalInt_npow, evalInt_foldr_add,
    evalInt_fourSqConstraint]

/-! ### Arity -/

theorem arity_fourSq_le (n i : ℕ) : (fourSq n i).arity ≤ n + 4 * i + 4 := by
  have h : ∀ k : ℕ, (npow (X k) 2).arity ≤ k + 1 := fun k =>
    le_trans (arity_npow_le _ 2) (by simp)
  simp only [fourSq, arity_add, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)

theorem arity_fourSqConstraint_le (n i : ℕ) :
    (fourSqConstraint n i).arity ≤ max (i + 1) (n + 4 * i + 4) := by
  refine le_trans (arity_npow_le _ 2) ?_
  simp only [arity_add, arity_neg, arity_X, max_le_iff]
  exact ⟨le_max_left _ _, le_trans (arity_fourSq_le n i) (le_max_right _ _)⟩

theorem arity_foldr_add_le {α : Type*} (l : List α) (f : α → PolynomialCode) (m : ℕ)
    (h : ∀ a ∈ l, (f a).arity ≤ m) : (((l.map f).foldr add zero)).arity ≤ m := by
  induction l with
  | nil => simp [zero, arity]
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons, arity_add, max_le_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

/-- **The frozen arity bound.** -/
theorem arity_fourSquares_le (p : PolynomialCode) : (fourSquares p).arity ≤ 5 * p.arity := by
  simp only [fourSquares, arity_add, max_le_iff]
  refine ⟨le_trans (arity_npow_le _ 2) (by omega), ?_⟩
  refine arity_foldr_add_le _ _ _ fun i hi => ?_
  have hi' : i < p.arity := by simpa using hi
  refine le_trans (arity_fourSqConstraint_le p.arity i) ?_
  simp only [max_le_iff]
  omega

end PolynomialCode

end Hilbert10
