/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.NatSolvable
import Hilbert10.IntSolvable
import Hilbert10.SumSquares
import Hilbert10.Internal.SumSquaresComp
import Mathlib.Computability.Reduce

/-!
# Finite systems of equations with a shared assignment

Issue #53. A *system* is a list of codes, and it is solvable when **one** assignment is a root of
every member. This module defines the two system predicates, proves each equivalent to single
solvability of the sum-of-squares code with *the same witness*, and packages the equivalences
as many-one reductions in both directions. Systems and single equations therefore have the same
many-one degree, over `ℕ` and over `ℤ`.

## One witness for the whole system

The contract is the shared assignment. `x₀ = 0` and `x₀ = 1` are each solvable, but their system
is not, and that pair is the regression test that distinguishes the definition below from "a
witness for each equation". Nothing here relabels variables between equations; a consumer that
needs fresh variables (#57) supplies its own allocation.

## Main definitions

* `Hilbert10.SystemNatSolvable`, `Hilbert10.SystemIntSolvable`

## Main results

* `Hilbert10.systemNatSolvable_iff_natSolvable_sumSquaresCode`,
  `Hilbert10.systemIntSolvable_iff_intSolvable_sumSquaresCode`
* `Hilbert10.natSolvable_manyOneEquiv_systemNatSolvable`,
  `Hilbert10.intSolvable_manyOneEquiv_systemIntSolvable`
-/

namespace Hilbert10

open PolynomialCode

/-- **A system with a natural root**: one assignment at which every member vanishes. -/
def SystemNatSolvable (ps : List PolynomialCode) : Prop :=
  ∃ x : List ℕ, ∀ p ∈ ps, p.eval x = 0

/-- **A system with an integer root**: one assignment at which every member vanishes. -/
def SystemIntSolvable (ps : List PolynomialCode) : Prop :=
  ∃ x : List ℤ, ∀ p ∈ ps, p.evalInt x = 0

theorem systemNatSolvable_iff (ps : List PolynomialCode) :
    SystemNatSolvable ps ↔ ∃ x : List ℕ, ∀ p ∈ ps, p.eval x = 0 := Iff.rfl

theorem systemIntSolvable_iff (ps : List PolynomialCode) :
    SystemIntSolvable ps ↔ ∃ x : List ℤ, ∀ p ∈ ps, p.evalInt x = 0 := Iff.rfl

/-! ### Systems reduce to single equations, with the same witness -/

/-- **A system has a natural root exactly when its sum of squares does**, at the same
assignment. -/
theorem systemNatSolvable_iff_natSolvable_sumSquaresCode (ps : List PolynomialCode) :
    SystemNatSolvable ps ↔ NatSolvable (sumSquaresCode ps) :=
  exists_congr fun x => (eval_sumSquaresCode_eq_zero_iff ps x).symm

/-- **A system has an integer root exactly when its sum of squares does**, at the same
assignment. -/
theorem systemIntSolvable_iff_intSolvable_sumSquaresCode (ps : List PolynomialCode) :
    SystemIntSolvable ps ↔ IntSolvable (sumSquaresCode ps) :=
  exists_congr fun x => (evalInt_sumSquaresCode_eq_zero_iff ps x).symm

/-! ### Single equations are one-element systems -/

theorem natSolvable_iff_systemNatSolvable_singleton (p : PolynomialCode) :
    NatSolvable p ↔ SystemNatSolvable [p] :=
  exists_congr fun _ => by simp

theorem intSolvable_iff_systemIntSolvable_singleton (p : PolynomialCode) :
    IntSolvable p ↔ SystemIntSolvable [p] :=
  exists_congr fun _ => by simp

/-! ### The reductions -/

private theorem computable_singleton : Computable fun p : PolynomialCode => [p] :=
  (Primrec₂.comp Primrec.list_cons Primrec.id (Primrec.const [])).to_comp

theorem systemNatSolvable_manyOneReducible_natSolvable : SystemNatSolvable ≤₀ NatSolvable :=
  ⟨sumSquaresCode, computable_sumSquaresCode, systemNatSolvable_iff_natSolvable_sumSquaresCode⟩

theorem natSolvable_manyOneReducible_systemNatSolvable : NatSolvable ≤₀ SystemNatSolvable :=
  ⟨fun p => [p], computable_singleton, natSolvable_iff_systemNatSolvable_singleton⟩

theorem systemIntSolvable_manyOneReducible_intSolvable : SystemIntSolvable ≤₀ IntSolvable :=
  ⟨sumSquaresCode, computable_sumSquaresCode, systemIntSolvable_iff_intSolvable_sumSquaresCode⟩

theorem intSolvable_manyOneReducible_systemIntSolvable : IntSolvable ≤₀ SystemIntSolvable :=
  ⟨fun p => [p], computable_singleton, intSolvable_iff_systemIntSolvable_singleton⟩

/-- **Systems and single equations have the same many-one degree over `ℕ`.** -/
theorem natSolvable_manyOneEquiv_systemNatSolvable : ManyOneEquiv NatSolvable SystemNatSolvable :=
  ⟨natSolvable_manyOneReducible_systemNatSolvable, systemNatSolvable_manyOneReducible_natSolvable⟩

/-- **Systems and single equations have the same many-one degree over `ℤ`.** -/
theorem intSolvable_manyOneEquiv_systemIntSolvable : ManyOneEquiv IntSolvable SystemIntSolvable :=
  ⟨intSolvable_manyOneReducible_systemIntSolvable, systemIntSolvable_manyOneReducible_intSolvable⟩

/-! ### Regression examples

The specification tests for the shared-assignment contract. -/

/-- The empty system is satisfied by the empty assignment. -/
example : SystemNatSolvable [] := ⟨[], by simp⟩
example : SystemIntSolvable [] := ⟨[], by simp⟩

/-- `x₀ = 0`. -/
private def xEq0 : PolynomialCode := ⟨[(1, [1])]⟩
/-- `x₀ - 1 = 0`. -/
private def xEq1 : PolynomialCode := ⟨[(1, [1]), (-1, [])]⟩

example : NatSolvable xEq0 := ⟨[0], by decide⟩
example : NatSolvable xEq1 := ⟨[1], by decide⟩

/-- **The contradictory pair.** Each equation is solvable; the system is not, because one
assignment must serve both. This is the test that separates "one witness for the whole system"
from "a witness for each equation". -/
example : ¬ SystemNatSolvable [xEq0, xEq1] := by
  rintro ⟨x, hx⟩
  have h0 := hx xEq0 (by simp)
  have h1 := hx xEq1 (by simp)
  cases x with
  | nil => simp [xEq1, eval, evalMonomial] at h1
  | cons a as =>
    simp [xEq0, xEq1, eval, evalMonomial] at h0 h1
    omega

example : ¬ SystemIntSolvable [xEq0, xEq1] := by
  rintro ⟨x, hx⟩
  have h0 := hx xEq0 (by simp)
  have h1 := hx xEq1 (by simp)
  cases x with
  | nil => simp [xEq1, evalInt, evalMonomialInt] at h1
  | cons a as =>
    simp [xEq0, xEq1, evalInt, evalMonomialInt] at h0 h1
    omega

/-- A satisfiable pair genuinely sharing variables: `x₀ + x₁ = 5` and `x₀ - x₁ = 1`, solved by
`[3, 2]`. -/
example : SystemNatSolvable
    [⟨[(1, [1]), (1, [0, 1]), (-5, [])]⟩, ⟨[(1, [1]), (-1, [0, 1]), (-1, [])]⟩] :=
  ⟨[3, 2], by decide⟩

/-- Constant equations: `0 = 0` is satisfied by anything, `1 = 0` by nothing. -/
example : SystemNatSolvable [const 0, const 0] := ⟨[], by simp⟩
example : ¬ SystemNatSolvable [const 1] := by
  rintro ⟨x, hx⟩
  simpa using hx (const 1) (by simp)

/-- Ragged exponent vectors: arities `1` and `3` in one system, one assignment for both. -/
example : SystemNatSolvable [⟨[(1, [1])]⟩, ⟨[(1, [0, 0, 1]), (-1, [])]⟩] :=
  ⟨[0, 0, 1], by decide⟩
example : systemArity [⟨[(1, [1])]⟩, ⟨[(1, [0, 0, 1]), (-1, [])]⟩] = 3 := by decide

end Hilbert10
