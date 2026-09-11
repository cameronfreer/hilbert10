/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Degree
import Hilbert10.Internal.CodeAlgebra

/-!
# Degree bounds for the code algebra

Issue #57. How `degreeBound` behaves under the six internal operations, stated as bounds
(`≤`) because the bound itself is only an upper estimate. Everything is proved through
`degreeBound_le_iff`, term by term.

## Main results

* `Hilbert10.PolynomialCode.degreeBound_add_le`, `degreeBound_mul_le`, `degreeBound_npow_le`,
  `degreeBound_foldr_add_le` and friends
-/

namespace Hilbert10

namespace PolynomialCode

theorem sum_addExponents : ∀ e f : MonomialCode, (addExponents e f).sum = e.sum + f.sum
  | [], f => by simp [addExponents]
  | e :: es, [] => by simp [addExponents]
  | a :: es, b :: fs => by
    simp only [addExponents, List.sum_cons, sum_addExponents es fs]
    omega

@[simp] theorem degreeBound_zero : zero.degreeBound = 0 := rfl

@[simp] theorem degreeBound_const (c : ℤ) : (const c).degreeBound = 0 := rfl

@[simp] theorem degreeBound_one : one.degreeBound = 0 := rfl

@[simp] theorem degreeBound_X (i : ℕ) : (X i).degreeBound = 1 := by
  simp [degreeBound, X, monomialDegree]

theorem degreeBound_add_le (p q : PolynomialCode) :
    (add p q).degreeBound ≤ max p.degreeBound q.degreeBound := by
  rw [degreeBound_le_iff]
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact le_max_of_le_left (monomialDegree_le_degreeBound h)
  · exact le_max_of_le_right (monomialDegree_le_degreeBound h)

theorem degreeBound_neg_le (p : PolynomialCode) : (neg p).degreeBound ≤ p.degreeBound := by
  rw [degreeBound_le_iff]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact monomialDegree_le_degreeBound (t := s) hs

theorem degreeBound_mul_le (p q : PolynomialCode) :
    (mul p q).degreeBound ≤ p.degreeBound + q.degreeBound := by
  rw [degreeBound_le_iff]
  intro t ht
  simp only [mul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  simp only [monomialDegree, sum_addExponents]
  exact Nat.add_le_add (monomialDegree_le_degreeBound ha) (monomialDegree_le_degreeBound hb)

theorem degreeBound_npow_le (p : PolynomialCode) :
    ∀ n : ℕ, (npow p n).degreeBound ≤ n * p.degreeBound
  | 0 => by simp [npow]
  | n + 1 => by
    refine (degreeBound_mul_le p (npow p n)).trans ?_
    have := degreeBound_npow_le p n
    rw [Nat.succ_mul]
    omega

theorem degreeBound_foldr_add_le {α : Type*} (l : List α) (f : α → PolynomialCode) (m : ℕ)
    (h : ∀ a ∈ l, (f a).degreeBound ≤ m) : ((l.map f).foldr add zero).degreeBound ≤ m := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons]
    refine (degreeBound_add_le _ _).trans (max_le (h a (by simp)) ?_)
    exact ih fun b hb => h b (by simp [hb])

end PolynomialCode

end Hilbert10
