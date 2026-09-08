/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Internal.CodeAlgebra

/-!
# The sum-of-squares transformation

Issue #53, first layer. A finite system of equations `p₁ = 0, …, pₖ = 0` with one shared
assignment has a solution exactly when the single equation

```
p₁² + ⋯ + pₖ² = 0
```

does, because over `ℤ` a sum of squares vanishes exactly when every summand does. The same
argument carries the natural formulation, since `eval` is `evalInt` restricted along the cast.

## The shared assignment is the contract

`sumSquaresCode` says nothing about relabelling variables: every member of the system reads the
*same* assignment, and a variable index means the same variable in every equation. That is the
point of a system, and it is what distinguishes "one witness for the whole system" from "a
witness for each equation" — see the contradictory pair in `Systems.lean`. Any relabelling or
fresh-variable machinery is a separate consumer's concern (#57).

## Public, unlike its computability

Like `subUV` and `fourSquares`, the transformation is API and its square argument stands alone;
`Primrec sumSquaresCode`, which turns it into a many-one reduction, is in
`Internal/SumSquaresComp.lean`.

## Main definitions

* `Hilbert10.PolynomialCode.sumSquaresCode`
* `Hilbert10.PolynomialCode.systemArity`

## Main results

* `Hilbert10.PolynomialCode.evalInt_sumSquaresCode`, `eval_sumSquaresCode`
* `Hilbert10.PolynomialCode.evalInt_sumSquaresCode_eq_zero_iff`, `eval_sumSquaresCode_eq_zero_iff`
* `Hilbert10.PolynomialCode.arity_sumSquaresCode_le`
-/

namespace Hilbert10

namespace PolynomialCode

/-- The sum of the squares of a list of codes. -/
def sumSquaresCode (ps : List PolynomialCode) : PolynomialCode :=
  (ps.map fun p => mul p p).foldr add zero

/-- The arity of a system: the largest arity of a member, `0` for the empty system. -/
def systemArity (ps : List PolynomialCode) : ℕ := (ps.map arity).foldr max 0

@[simp] theorem sumSquaresCode_nil : sumSquaresCode [] = ⟨[]⟩ := rfl

@[simp] theorem systemArity_nil : systemArity [] = 0 := rfl

@[simp] theorem systemArity_cons (p : PolynomialCode) (ps : List PolynomialCode) :
    systemArity (p :: ps) = max p.arity (systemArity ps) := rfl

theorem arity_le_systemArity {p : PolynomialCode} {ps : List PolynomialCode} (h : p ∈ ps) :
    p.arity ≤ systemArity ps := by
  induction ps with
  | nil => simp at h
  | cons q qs ih =>
    rw [systemArity_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih h')

/-! ### Evaluation -/

/-- **The evaluation formula, over `ℤ`.** -/
theorem evalInt_sumSquaresCode (ps : List PolynomialCode) (x : List ℤ) :
    evalInt (sumSquaresCode ps) x = (ps.map fun p => (evalInt p x) ^ 2).sum := by
  rw [sumSquaresCode, evalInt_foldr_add]
  congr 1
  exact List.map_congr_left fun p _ => by rw [evalInt_mul, sq]

/-- **The evaluation formula, over `ℕ`**, through the cast bridge. -/
theorem eval_sumSquaresCode (ps : List PolynomialCode) (x : List ℕ) :
    eval (sumSquaresCode ps) x = (ps.map fun p => (eval p x) ^ 2).sum := by
  rw [← evalInt_map_natCast, evalInt_sumSquaresCode]
  simp only [evalInt_map_natCast]

/-! ### A sum of squares vanishes exactly when every summand does -/

private theorem sq_nonneg' (a : ℤ) : 0 ≤ a ^ 2 := by
  rw [pow_two, ← Int.natAbs_mul_self]
  exact Int.natCast_nonneg _

private theorem sum_map_sq_nonneg {α : Type*} (f : α → ℤ) :
    ∀ l : List α, 0 ≤ (l.map fun a => f a ^ 2).sum
  | [] => le_rfl
  | a :: as => by
    have h := sum_map_sq_nonneg f as
    have ha : 0 ≤ f a ^ 2 := sq_nonneg' _
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_sq_eq_zero_iff {α : Type*} (f : α → ℤ) :
    ∀ l : List α, (l.map fun a => f a ^ 2).sum = 0 ↔ ∀ a ∈ l, f a = 0
  | [] => by simp
  | a :: as => by
    have has := sum_map_sq_nonneg f as
    have ha : 0 ≤ f a ^ 2 := sq_nonneg' _
    rw [List.map_cons, List.sum_cons, List.forall_mem_cons, ← sum_map_sq_eq_zero_iff f as]
    constructor
    · intro h
      have h1 : f a ^ 2 = 0 := by omega
      exact ⟨pow_eq_zero_iff two_ne_zero |>.mp h1, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      simp

/-- **The pointwise zero equivalence, over `ℤ`.** -/
theorem evalInt_sumSquaresCode_eq_zero_iff (ps : List PolynomialCode) (x : List ℤ) :
    evalInt (sumSquaresCode ps) x = 0 ↔ ∀ p ∈ ps, evalInt p x = 0 := by
  rw [evalInt_sumSquaresCode]
  exact sum_map_sq_eq_zero_iff _ ps

/-- **The pointwise zero equivalence, over `ℕ`.** -/
theorem eval_sumSquaresCode_eq_zero_iff (ps : List PolynomialCode) (x : List ℕ) :
    eval (sumSquaresCode ps) x = 0 ↔ ∀ p ∈ ps, eval p x = 0 := by
  rw [eval_sumSquaresCode]
  exact sum_map_sq_eq_zero_iff _ ps

/-! ### Arity -/

/-- **The transformation introduces no variables**: its arity is bounded by the system's. -/
theorem arity_sumSquaresCode_le (ps : List PolynomialCode) :
    (sumSquaresCode ps).arity ≤ systemArity ps :=
  arity_foldr_add_le _ _ _ fun p hp =>
    (arity_mul_le p p).trans (by rw [max_self]; exact arity_le_systemArity hp)

end PolynomialCode

end Hilbert10
