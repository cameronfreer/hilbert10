/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.PolynomialCodeDenote
import Hilbert10.SumSquares

/-!
# A syntactic degree bound

Issue #57, first checkpoint. The quartic result is a statement about *degree*, so the wire format
needs a notion of degree that can be read off a code and checked by `decide`. `degreeBound` is
the largest exponent sum among the terms — conservative, because cancellation is ignored: the
code for `x − x` has bound `1` and denotes `0`. What makes it honest is `totalDegree_denote_le`:
the bound dominates the total degree of the polynomial the code denotes, so "degree at most
four" of a code is a fact about the polynomial, not only about its presentation.

## Main definitions

* `Hilbert10.PolynomialCode.monomialDegree`, `degreeBound`, `systemDegreeBound`

## Main results

* `Hilbert10.PolynomialCode.totalDegree_denote_le`
* `Hilbert10.PolynomialCode.degreeBound_le_iff`, the workhorse for every bound on a construction
-/

namespace Hilbert10

namespace PolynomialCode

/-- The degree of a monomial code: the sum of its exponents. -/
def monomialDegree (e : MonomialCode) : ℕ := e.sum

/-- A conservative syntactic degree bound: the largest monomial degree among the terms, `0` for
the zero code. Cancellation is ignored. -/
def degreeBound (p : PolynomialCode) : ℕ :=
  (p.terms.map fun t => monomialDegree t.2).foldr max 0

/-- The degree bound of a system: the largest bound of a member, `0` when empty. -/
def systemDegreeBound (ps : List PolynomialCode) : ℕ := (ps.map degreeBound).foldr max 0

/-- `foldr max 0` is bounded by `d` exactly when every entry is. -/
theorem foldr_max_le_iff (d : ℕ) : ∀ l : List ℕ, l.foldr max 0 ≤ d ↔ ∀ a ∈ l, a ≤ d
  | [] => by simp
  | a :: as => by
    simp only [List.foldr_cons, max_le_iff, List.forall_mem_cons, foldr_max_le_iff d as]

theorem degreeBound_le_iff (p : PolynomialCode) (d : ℕ) :
    p.degreeBound ≤ d ↔ ∀ t ∈ p.terms, monomialDegree t.2 ≤ d := by
  simp only [degreeBound, foldr_max_le_iff, List.forall_mem_map]

theorem monomialDegree_le_degreeBound {p : PolynomialCode} {t : ℤ × MonomialCode}
    (ht : t ∈ p.terms) : monomialDegree t.2 ≤ p.degreeBound :=
  (degreeBound_le_iff p _).mp le_rfl t ht

theorem systemDegreeBound_le_iff (ps : List PolynomialCode) (d : ℕ) :
    systemDegreeBound ps ≤ d ↔ ∀ p ∈ ps, p.degreeBound ≤ d := by
  simp only [systemDegreeBound, foldr_max_le_iff, List.forall_mem_map]

theorem degreeBound_le_systemDegreeBound {p : PolynomialCode} {ps : List PolynomialCode}
    (h : p ∈ ps) : p.degreeBound ≤ systemDegreeBound ps :=
  (systemDegreeBound_le_iff ps _).mp le_rfl p h

@[simp] theorem degreeBound_mk_nil : degreeBound ⟨[]⟩ = 0 := rfl

@[simp] theorem systemDegreeBound_nil : systemDegreeBound [] = 0 := rfl

/-! ### The bound dominates the denotation's total degree -/

open MvPolynomial in
private theorem totalDegree_list_sum_le :
    ∀ l : List (MvPolynomial ℕ ℤ), l.sum.totalDegree ≤ (l.map totalDegree).foldr max 0
  | [] => by simp
  | a :: as => by
    simp only [List.sum_cons, List.map_cons, List.foldr_cons]
    exact (totalDegree_add _ _).trans (max_le_max le_rfl (totalDegree_list_sum_le as))

/-- **The syntactic bound dominates the total degree of the denoted polynomial.** -/
theorem totalDegree_denote_le (p : PolynomialCode) : p.denote.totalDegree ≤ p.degreeBound := by
  rw [denote]
  refine (totalDegree_list_sum_le _).trans ?_
  rw [foldr_max_le_iff]
  intro a ha
  simp only [List.map_map, List.mem_map, Function.comp_def] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  exact (totalDegree_denoteMonomial_le t.2).trans (monomialDegree_le_degreeBound ht)

end PolynomialCode

end Hilbert10
