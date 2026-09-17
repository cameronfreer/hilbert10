/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.QuadraticLowering
import Hilbert10.Internal.QuadraticLoweringComp
import Hilbert10.Internal.SumSquaresComp
import Hilbert10.Endpoints

/-!
# Hilbert's tenth problem in degree four

Issue #57, third checkpoint. The quadratic system of a polynomial, summed by squares, is a single
equation of degree at most four with the same roots. So solvability of *arbitrary* encoded
polynomials reduces to solvability of those of degree at most four, and the restricted problems
inherit recursive enumerability, many-one completeness and undecidability.

## The restricted problems are syntactic

`QuarticNatSolvable p` is `p.degreeBound ≤ 4 ∧ NatSolvable p`, on ordinary codes. Restricting the
*type* of codes would forfeit the existing computability infrastructure; restricting by a
syntactic predicate keeps it, and `totalDegree_denote_le` supplies the mathematical meaning: a
code passing the test denotes a polynomial of total degree at most four.

## Both reductions

`quarticCode` sends any code to a quartic one with the same roots, in both domains. The reverse
direction is *not* the identity on all codes: a code failing the degree test is sent to a fixed
unsatisfiable constant, since otherwise a solvable high-degree code would be a counterexample.
With both, the restricted and unrestricted problems have the same many-one degree.

## Main definitions

* `Hilbert10.PolynomialCode.quarticCode`, `Hilbert10.PolynomialCode.restrictQuartic`
* `Hilbert10.QuarticNatSolvable`, `Hilbert10.QuarticIntSolvable`

## Main results

* `Hilbert10.PolynomialCode.degreeBound_quarticCode_le` (`≤ 4`), `arity_quarticCode_le`
  (`≤ p.arity + gateCount p`)
* `Hilbert10.natSolvable_iff_natSolvable_quarticCode`, `intSolvable_iff_intSolvable_quarticCode`
* `Hilbert10.natSolvable_manyOneEquiv_quarticNatSolvable`,
  `Hilbert10.intSolvable_manyOneEquiv_quarticIntSolvable`
* `Hilbert10.quarticNatSolvable_re_complete`, `not_computablePred_quarticNatSolvable`, and the
  integer twins
-/

namespace Hilbert10

open PolynomialCode

namespace PolynomialCode

/-- **The quartic code of a polynomial**: the sum of squares of its quadratic system. -/
def quarticCode (p : PolynomialCode) : PolynomialCode := sumSquaresCode (quadraticSystem p)

/-- **Degree at most four.** -/
theorem degreeBound_quarticCode_le (p : PolynomialCode) : (quarticCode p).degreeBound ≤ 4 :=
  (degreeBound_sumSquaresCode_le _).trans
    (by have := systemDegreeBound_quadraticSystem_le p; omega)

/-- **No new variables**: the sum of squares introduces none, so the lowering's bound survives. -/
theorem arity_quarticCode_le (p : PolynomialCode) :
    (quarticCode p).arity ≤ p.arity + gateCount p :=
  (arity_sumSquaresCode_le _).trans (systemArity_quadraticSystem_le p)

/-- Every code of degree at most four is sent to itself; every other code to `1 = 0`, which has
no root in either domain. -/
def restrictQuartic (p : PolynomialCode) : PolynomialCode :=
  if p.degreeBound ≤ 4 then p else ⟨[(1, [])]⟩

theorem primrec_quarticCode : Primrec quarticCode :=
  primrec_sumSquaresCode.comp primrec_quadraticSystem

theorem computable_quarticCode : Computable quarticCode := primrec_quarticCode.to_comp

theorem primrec_restrictQuartic : Primrec restrictQuartic :=
  Primrec.ite (primrecPred_degreeBound_le 4) Primrec.id (Primrec.const _)

theorem computable_restrictQuartic : Computable restrictQuartic := primrec_restrictQuartic.to_comp

end PolynomialCode

/-! ### Root equivalence with the quartic code -/

theorem natSolvable_iff_natSolvable_quarticCode (p : PolynomialCode) :
    NatSolvable p ↔ NatSolvable (quarticCode p) :=
  (natSolvable_iff_systemNatSolvable_quadraticSystem p).trans
    (systemNatSolvable_iff_natSolvable_sumSquaresCode _)

theorem intSolvable_iff_intSolvable_quarticCode (p : PolynomialCode) :
    IntSolvable p ↔ IntSolvable (quarticCode p) :=
  (intSolvable_iff_systemIntSolvable_quadraticSystem p).trans
    (systemIntSolvable_iff_intSolvable_sumSquaresCode _)

/-! ### The restricted decision problems -/

/-- **Hilbert's tenth problem in degree four, over `ℕ`.** -/
def QuarticNatSolvable (p : PolynomialCode) : Prop := p.degreeBound ≤ 4 ∧ NatSolvable p

/-- **Hilbert's tenth problem in degree four, over `ℤ`.** -/
def QuarticIntSolvable (p : PolynomialCode) : Prop := p.degreeBound ≤ 4 ∧ IntSolvable p

theorem natSolvable_iff_quarticNatSolvable_quarticCode (p : PolynomialCode) :
    NatSolvable p ↔ QuarticNatSolvable (quarticCode p) :=
  (natSolvable_iff_natSolvable_quarticCode p).trans
    (and_iff_right (degreeBound_quarticCode_le p)).symm

theorem intSolvable_iff_quarticIntSolvable_quarticCode (p : PolynomialCode) :
    IntSolvable p ↔ QuarticIntSolvable (quarticCode p) :=
  (intSolvable_iff_intSolvable_quarticCode p).trans
    (and_iff_right (degreeBound_quarticCode_le p)).symm

private theorem not_natSolvable_one : ¬ NatSolvable ⟨[(1, [])]⟩ := by
  rintro ⟨x, hx⟩
  simp [eval, evalMonomial] at hx

private theorem not_intSolvable_one : ¬ IntSolvable ⟨[(1, [])]⟩ := by
  rintro ⟨x, hx⟩
  simp [evalInt, evalMonomialInt] at hx

theorem quarticNatSolvable_iff_natSolvable_restrictQuartic (p : PolynomialCode) :
    QuarticNatSolvable p ↔ NatSolvable (restrictQuartic p) := by
  unfold QuarticNatSolvable restrictQuartic
  split_ifs with h
  · exact and_iff_right h
  · exact ⟨fun hp => absurd hp.1 h, fun hp => absurd hp not_natSolvable_one⟩

theorem quarticIntSolvable_iff_intSolvable_restrictQuartic (p : PolynomialCode) :
    QuarticIntSolvable p ↔ IntSolvable (restrictQuartic p) := by
  unfold QuarticIntSolvable restrictQuartic
  split_ifs with h
  · exact and_iff_right h
  · exact ⟨fun hp => absurd hp.1 h, fun hp => absurd hp not_intSolvable_one⟩

/-! ### The reductions, and the same many-one degree -/

theorem natSolvable_manyOneReducible_quarticNatSolvable : NatSolvable ≤₀ QuarticNatSolvable :=
  ⟨quarticCode, computable_quarticCode, natSolvable_iff_quarticNatSolvable_quarticCode⟩

theorem quarticNatSolvable_manyOneReducible_natSolvable : QuarticNatSolvable ≤₀ NatSolvable :=
  ⟨restrictQuartic, computable_restrictQuartic, quarticNatSolvable_iff_natSolvable_restrictQuartic⟩

theorem intSolvable_manyOneReducible_quarticIntSolvable : IntSolvable ≤₀ QuarticIntSolvable :=
  ⟨quarticCode, computable_quarticCode, intSolvable_iff_quarticIntSolvable_quarticCode⟩

theorem quarticIntSolvable_manyOneReducible_intSolvable : QuarticIntSolvable ≤₀ IntSolvable :=
  ⟨restrictQuartic, computable_restrictQuartic, quarticIntSolvable_iff_intSolvable_restrictQuartic⟩

/-- **Degree four is as hard as any degree, over `ℕ`.** -/
theorem natSolvable_manyOneEquiv_quarticNatSolvable :
    ManyOneEquiv NatSolvable QuarticNatSolvable :=
  ⟨natSolvable_manyOneReducible_quarticNatSolvable, quarticNatSolvable_manyOneReducible_natSolvable⟩

/-- **Degree four is as hard as any degree, over `ℤ`.** -/
theorem intSolvable_manyOneEquiv_quarticIntSolvable :
    ManyOneEquiv IntSolvable QuarticIntSolvable :=
  ⟨intSolvable_manyOneReducible_quarticIntSolvable, quarticIntSolvable_manyOneReducible_intSolvable⟩

/-! ### Endpoints

Recursive enumerability of the restricted problems comes through the reverse reduction, which is
where the *computability* of the degree test is used — its decidability alone would not do. -/

theorem rePred_quarticNatSolvable : REPred QuarticNatSolvable :=
  REPred.of_manyOneReducible quarticNatSolvable_manyOneReducible_natSolvable rePred_natSolvable

theorem rePred_quarticIntSolvable : REPred QuarticIntSolvable :=
  REPred.of_manyOneReducible quarticIntSolvable_manyOneReducible_intSolvable rePred_intSolvable

/-- **`QuarticNatSolvable` is many-one complete among recursively enumerable predicates.** -/
theorem quarticNatSolvable_re_complete {α : Type*} [Primcodable α] {R : α → Prop}
    (hR : REPred R) : R ≤₀ QuarticNatSolvable :=
  (natSolvable_re_complete hR).trans natSolvable_manyOneReducible_quarticNatSolvable

/-- **`QuarticIntSolvable` is many-one complete among recursively enumerable predicates.** -/
theorem quarticIntSolvable_re_complete {α : Type*} [Primcodable α] {R : α → Prop}
    (hR : REPred R) : R ≤₀ QuarticIntSolvable :=
  (intSolvable_re_complete hR).trans intSolvable_manyOneReducible_quarticIntSolvable

theorem halting_manyOneReducible_quarticNatSolvable :
    (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ QuarticNatSolvable :=
  quarticNatSolvable_re_complete (ComputablePred.halting_problem_re 0)

theorem halting_manyOneReducible_quarticIntSolvable :
    (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ QuarticIntSolvable :=
  quarticIntSolvable_re_complete (ComputablePred.halting_problem_re 0)

/-- **Hilbert's tenth problem is undecidable already in degree four, over `ℕ`.** -/
theorem not_computablePred_quarticNatSolvable : ¬ ComputablePred QuarticNatSolvable := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_quarticNatSolvable h)

/-- **Hilbert's tenth problem is undecidable already in degree four, over `ℤ`.** -/
theorem not_computablePred_quarticIntSolvable : ¬ ComputablePred QuarticIntSolvable := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_quarticIntSolvable h)

/-! ### Regression: a polynomial of degree five

`x₀⁵ − 32` has syntactic degree five, so it is outside the restricted problem, yet its quartic
code is inside it and has a root — the reduction's advertised purpose, visibly exercised. -/

/-- `x₀⁵ − 32`. -/
private def quintic : PolynomialCode := ⟨[(1, [5]), (-32, [])]⟩

example : quintic.degreeBound = 5 := by decide

example : ¬ QuarticNatSolvable quintic := fun h => absurd h.1 (by decide)

example : NatSolvable quintic := ⟨[2], by decide⟩

example : QuarticNatSolvable (quarticCode quintic) :=
  (natSolvable_iff_quarticNatSolvable_quarticCode quintic).mp ⟨[2], by decide⟩

/-- The degree really is four: fourteen gates (`1 + (5 + 4) + (0 + 4)`), fifteen quadratic
equations, and their squares. -/
example : gateCount quintic = 14 := by decide
set_option maxRecDepth 8000 in
example : (quarticCode quintic).degreeBound = 4 := by decide

/-- The reverse reduction sends a high-degree code to the unsatisfiable constant. -/
example : restrictQuartic quintic = ⟨[(1, [])]⟩ := by
  rw [restrictQuartic, if_neg (by decide)]

end Hilbert10
