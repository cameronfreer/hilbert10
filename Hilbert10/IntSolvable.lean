/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.NatSolvable
import Hilbert10.Internal.SubUV

/-!
# Integer solvability, and its equivalence with the natural version

Issue #28. `IntSolvable` is Hilbert's own question for the encoded wire format: does the coded
polynomial have an **integer** root? This file defines it and proves that it holds exactly when
the difference-substituted code has a natural root.

## Why the equivalence is stated on codes

`intSolvable_iff_natSolvable_subUV` is the mathematical content of the reduction
`IntSolvable ≤₀ NatSolvable`; what the reduction adds is that `subUV` is computable. Keeping the
two apart means the arithmetic can be checked without reading a computability proof, and the
computability proof does not have to re-establish any arithmetic.

## Both directions normalise first

The predicates quantify over arbitrary-length assignments, while the two-block reading needs a
fixed boundary at `p.arity`. Each direction therefore normalises its witness to an exact length
before splitting: integer witnesses through `exists_length_eq_arity_evalInt_eq`, natural ones
through the arity bound `arity_subUV_le` and zero-extension. Skipping that step would let a short
witness make `take` and `drop` describe the wrong blocks.

## Main results

* `Hilbert10.IntSolvable`
* `Hilbert10.intSolvable_iff_natSolvable_subUV`
-/

namespace Hilbert10

open PolynomialCode

/-- **Hilbert's tenth problem over the integers**, for the encoded wire format. -/
def IntSolvable (p : PolynomialCode) : Prop := ∃ x : List ℤ, p.evalInt x = 0

theorem intSolvable_iff (p : PolynomialCode) :
    IntSolvable p ↔ ∃ x : List ℤ, p.evalInt x = 0 := Iff.rfl

namespace PolynomialCode

/-- Every integer assignment is a difference of two natural ones, componentwise. -/
theorem diffList_toNat (y : List ℤ) :
    diffList (y.map Int.toNat) (y.map fun z => (-z).toNat) = y := by
  induction y with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, diffList_cons, ih]
    congr 1
    omega

end PolynomialCode

/-- **The reduction, as an equivalence of codes.** An integer root of `p` is exactly a natural
root of the difference-substituted code. -/
theorem intSolvable_iff_natSolvable_subUV (p : PolynomialCode) :
    IntSolvable p ↔ NatSolvable (subUV p) := by
  constructor
  · rintro ⟨x, hx⟩
    -- normalise the integer witness, then split it componentwise
    obtain ⟨y, hylen, hy⟩ := exists_length_eq_arity_evalInt_eq p x
    refine ⟨y.map Int.toNat ++ y.map fun z => (-z).toNat, ?_⟩
    rw [eval_subUV p (by simpa using hylen) (by simpa using hylen), diffList_toNat, hy, hx]
  · rintro ⟨w, hw⟩
    -- normalise the natural witness to exactly `2 * p.arity`, then split it in half
    set n := p.arity with hn
    set w' := (w ++ List.replicate (2 * n) 0).take (2 * n) with hw'
    have hw'len : w'.length = 2 * n := by
      simp only [hw', List.length_take, List.length_append, List.length_replicate]
      omega
    have hw'eval : eval (subUV p) w' = 0 := by
      have hsplit : (w ++ List.replicate (2 * n) 0)
          = w' ++ (w ++ List.replicate (2 * n) 0).drop (2 * n) := by
        simp [hw']
      have hlen : (subUV p).arity ≤ w'.length := by
        rw [hw'len]; exact arity_subUV_le p
      calc eval (subUV p) w'
          = eval (subUV p) (w' ++ (w ++ List.replicate (2 * n) 0).drop (2 * n)) :=
            (eval_append_of_arity_le hlen _).symm
        _ = eval (subUV p) (w ++ List.replicate (2 * n) 0) := by rw [← hsplit]
        _ = eval (subUV p) w := eval_append_replicate_zero _ _ _
        _ = 0 := hw
    refine ⟨diffList (w'.take n) (w'.drop n), ?_⟩
    have hu : (w'.take n).length = n := by
      simp only [List.length_take, hw'len]
      omega
    have hv : (w'.drop n).length = n := by
      simp only [List.length_drop, hw'len]
      omega
    rw [← eval_subUV p hu hv, List.take_append_drop, hw'eval]

end Hilbert10
