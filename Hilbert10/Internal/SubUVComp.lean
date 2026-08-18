/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Internal.SubUV
import Hilbert10.PolynomialCodePrimcodable
import Hilbert10.Internal.ForMathlib.PrimrecInt
import Mathlib.Computability.Partrec

/-!
# The difference substitution is primitive recursive

Issue #28, third piece, computability half. `IntSolvable ≤₀ NatSolvable` needs a *computable* map
on codes, so this file proves `Primrec subUV`. Everything else about the substitution — semantics
and arity — lives on the structural definitions in `SubUV`; this file works through the index
presentations proved equal to them there.

## One vocabulary

The whole chain uses five list operations, all of which mathlib supplies `Primrec` lemmas for:
`list_range`, `list_map`, `list_getD`, `list_foldr`, `list_flatMap`. Nothing needs truncated
subtraction, and nothing needs a `zipWith` lemma — which mathlib does not have.

## The integer dependency, certified by the proof rather than predicted

Only two integer operations are reached:

* `Primrec.int_neg`, for `neg`;
* `Primrec.int_mul`, for the coefficients of a convolution product.

Nothing combines coefficients by integer *addition* — `add` is list append, and `const` merely
transports its coefficient. That is the minimal scope #36 should propose upstream.

## Main results

* `Hilbert10.PolynomialCode.primrec_subUV`
-/

namespace Hilbert10

namespace PolynomialCode

open Primrec

/-! ### Exponent addition -/

private theorem primrec₂_addExponents : Primrec₂ addExponents := by
  have h : Primrec fun q : MonomialCode × MonomialCode =>
      (List.range (max q.1.length q.2.length)).map fun i => q.1.getD i 0 + q.2.getD i 0 := by
    refine Primrec.list_map
      (Primrec.list_range.comp (Primrec₂.comp Primrec.nat_max
        (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))) ?_
    exact Primrec₂.comp Primrec.nat_add
      (Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0) (Primrec.list_getD 0)
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0) (Primrec.list_getD 0)
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun q => (addExponents_eq_range q.1 q.2).symm

/-! ### The operations -/

private theorem primrec_const : Primrec const := by
  have h : Primrec fun c : ℤ => mk [(c, ([] : MonomialCode))] :=
    primrec_mk.comp (Primrec.list_cons.comp
      (Primrec.id.pair (Primrec.const ([] : MonomialCode)))
      (Primrec.const []))
  exact h.of_eq fun c => rfl

private theorem primrec_X : Primrec X := by
  have h : Primrec fun i : ℕ => mk [((1 : ℤ), List.replicate i 0 ++ [1])] := by
    have hexp : Primrec fun i : ℕ => List.replicate i (0 : ℕ) ++ [1] :=
      Primrec₂.comp Primrec.list_append Primrec.list_replicate_zero (Primrec.const [1])
    exact primrec_mk.comp (Primrec.list_cons.comp
      ((Primrec.const (1 : ℤ)).pair hexp) (Primrec.const []))
  exact h.of_eq fun i => rfl

private theorem primrec₂_add : Primrec₂ add := by
  have h : Primrec fun q : PolynomialCode × PolynomialCode => mk (q.1.terms ++ q.2.terms) :=
    primrec_mk.comp (Primrec₂.comp Primrec.list_append
      (primrec_terms.comp Primrec.fst) (primrec_terms.comp Primrec.snd))
  exact h.of_eq fun q => rfl

private theorem primrec_neg : Primrec neg := by
  have h : Primrec fun p : PolynomialCode => mk (p.terms.map fun t => (-t.1, t.2)) := by
    refine primrec_mk.comp (Primrec.list_map primrec_terms ?_)
    exact (Primrec.int_neg.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun p => rfl

private theorem primrec₂_mul : Primrec₂ mul := by
  have h : Primrec fun q : PolynomialCode × PolynomialCode =>
      mk (q.1.terms.flatMap fun t => q.2.terms.map fun s =>
        (t.1 * s.1, addExponents t.2 s.2)) := by
    refine primrec_mk.comp (Primrec.list_flatMap (primrec_terms.comp Primrec.fst) ?_)
    refine Primrec.list_map (primrec_terms.comp (Primrec.snd.comp Primrec.fst)) ?_
    exact (Primrec₂.comp Primrec.int_mul
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec₂.comp primrec₂_addExponents
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun q => rfl

private theorem primrec₂_npow : Primrec₂ npow := by
  have h := Primrec.nat_rec' (f := fun q : PolynomialCode × ℕ => q.2)
    (g := fun _ : PolynomialCode × ℕ => one)
    (h := fun (q : PolynomialCode × ℕ) (r : ℕ × PolynomialCode) => mul q.1 r.2)
    Primrec.snd (Primrec.const one)
    (Primrec₂.comp primrec₂_mul (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun q => ?_
  obtain ⟨p, n⟩ := q
  induction n with
  | zero => rfl
  | succ m ih => simp only [npow, ← ih]

/-! ### The substitution -/

private theorem primrec_diffVar : Primrec fun q : ℕ × ℕ => diffVar q.1 q.2 := by
  have h : Primrec fun q : ℕ × ℕ => add (X q.2) (neg (X (q.1 + q.2))) :=
    Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.snd)
      (primrec_neg.comp (primrec_X.comp
        (Primrec₂.comp Primrec.nat_add Primrec.fst Primrec.snd)))
  exact h.of_eq fun q => rfl

private theorem primrec_subUVMonomialFrom :
    Primrec fun q : (ℕ × ℕ) × MonomialCode => subUVMonomialFrom q.1.1 q.1.2 q.2 := by
  have hfactors : Primrec fun q : (ℕ × ℕ) × MonomialCode =>
      (List.range q.2.length).map fun j => npow (diffVar q.1.1 (q.1.2 + j)) (q.2.getD j 0) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
    refine Primrec₂.comp primrec₂_npow ?_ ?_
    · exact primrec_diffVar.comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec₂.comp Primrec.nat_add
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
    · exact Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0)
        (Primrec.list_getD 0) (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h : Primrec fun q : (ℕ × ℕ) × MonomialCode =>
      ((List.range q.2.length).map fun j =>
        npow (diffVar q.1.1 (q.1.2 + j)) (q.2.getD j 0)).foldr mul one := by
    refine Primrec.list_foldr (h := fun _ (r : PolynomialCode × PolynomialCode) => mul r.1 r.2)
      hfactors (Primrec.const one) ?_
    exact Primrec₂.comp primrec₂_mul (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun q => (subUVMonomialFrom_eq_foldr q.1.1 q.1.2 q.2).symm

/-- **The difference substitution is primitive recursive**, hence computable — which is what the
many-one reduction consumes. -/
theorem primrec_subUV : Primrec subUV := by
  have h : Primrec fun p : PolynomialCode =>
      mk (p.terms.flatMap fun t => (mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)).terms) := by
    refine primrec_mk.comp (Primrec.list_flatMap primrec_terms ?_)
    refine primrec_terms.comp (Primrec₂.comp primrec₂_mul
      (primrec_const.comp (Primrec.fst.comp Primrec.snd)) ?_)
    exact primrec_subUVMonomialFrom.comp
      (((primrec_arity.comp Primrec.fst).pair (Primrec.const 0)).pair
        (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun p => rfl

theorem computable_subUV : Computable subUV := primrec_subUV.to_comp

end PolynomialCode

end Hilbert10
