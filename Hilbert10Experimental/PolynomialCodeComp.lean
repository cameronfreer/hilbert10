/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.PolynomialCode
import Hilbert10Experimental.ForMathlib.PrimrecInt
import Mathlib.Computability.Primrec.List

/-!
# Computability of the wire format

Issue #9. `PolynomialCode` is a one-field structure over `List (ℤ × List ℕ)`, so the
`Primcodable` instance is transported along an explicit equivalence rather than built by
hand. Computability of the constructor and of the `terms` projection is proved
immediately, so that no later proof ever has to unfold the encoding.

## Note on integers

`eval` is `ℤ`-valued, and at the pinned mathlib revision the computability library exposes
no lemmas about `ℤ` at all. That layer lives in
`Hilbert10Experimental/ForMathlib/PrimrecInt.lean` (issue #36), deliberately separate: it
is a mathlib gap rather than anything about this wire format, and it must not be allowed to
reshape `PolynomialCode` or `evalMonomial`.
-/

namespace Hilbert10Experimental

namespace PolynomialCode

/-- A `PolynomialCode` is exactly its list of terms. -/
def equivTerms : PolynomialCode ≃ List (ℤ × MonomialCode) where
  toFun := terms
  invFun := mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance : Primcodable PolynomialCode := Primcodable.ofEquiv _ equivTerms

/-- The `terms` projection is primitive recursive. Downstream proofs use this rather than
unfolding the encoding. -/
theorem primrec_terms : Primrec terms :=
  Primrec.of_equiv (e := equivTerms)

/-- The constructor is primitive recursive. -/
theorem primrec_mk : Primrec mk :=
  Primrec.of_equiv_symm (e := equivTerms)

/-! ### Arity -/

theorem arity_eq_foldr (p : PolynomialCode) :
    p.arity = p.terms.foldr (fun t acc => max t.2.length acc) 0 := by
  simp only [arity]
  induction p.terms with
  | nil => rfl
  | cons s ss ih => simp [ih]

theorem primrec_arity : Primrec arity := by
  have hstep : Primrec₂ fun (_ : PolynomialCode) (q : (ℤ × MonomialCode) × ℕ) =>
      max q.1.2.length q.2 :=
    Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr (f := fun p : PolynomialCode => p.terms)
    (g := fun _ : PolynomialCode => (0 : ℕ))
    (h := fun _ q => max q.1.2.length q.2) primrec_terms (Primrec.const 0) hstep
  exact h.of_eq fun p => (arity_eq_foldr p).symm

end PolynomialCode

end Hilbert10Experimental
