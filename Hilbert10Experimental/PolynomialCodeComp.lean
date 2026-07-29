/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.PolynomialCode
import Mathlib.Computability.Primrec.List

/-!
# Computability of the wire format

Issue #9. `PolynomialCode` is a one-field structure over `List (ℤ × List ℕ)`, so the
`Primcodable` instance is transported along an explicit equivalence rather than built by
hand. Computability of the constructor and of the `terms` projection is proved
immediately, so that no later proof ever has to unfold the encoding.

## Note on integers

At the pinned mathlib revision the computability library exposes **no** lemmas about `ℤ` —
no `Primrec`, no `Computable`, for any integer operation. `Primcodable ℤ` exists only
because `Denumerable ℤ` does. So anything about `eval`, which is `ℤ`-valued, has to build
that layer; it is isolated in `Hilbert10Experimental.Int` lemmas below rather than allowed
to reshape `PolynomialCode` or `evalMonomial`.

The encoding is pinned down by `Equiv.intEquivNat = intEquivNatSumNat.trans natSumNatEquivNat`
together with `Equiv.natSumNatEquivNat_apply`, which give
`encode z = if 0 ≤ z then 2 * z.toNat else 2 * (-z - 1).toNat + 1`.
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

/-! ### The missing integer layer

`Primcodable ℤ` comes from `Denumerable ℤ`, whose encoding is
`Equiv.intEquivNat = intEquivNatSumNat.trans natSumNatEquivNat`. Since
`Encodable.encodeSum` is `2 * encode ·` / `2 * encode · + 1` and
`Equiv.natSumNatEquivNat_apply` is `Sum.elim (2 * ·) (2 * · + 1)`, the encodings of `ℤ` and
of `ℕ ⊕ ℕ` agree *on the nose*. So the sign-case view of an integer is primitive recursive
for free, and every integer operation reduces to case analysis over `ℕ ⊕ ℕ`.
-/

/-- Viewing an integer by its sign case is primitive recursive. -/
theorem primrec_intCases : Primrec (Equiv.intEquivNatSumNat) := by
  have h : ∀ z : ℤ, Encodable.encode (Equiv.intEquivNatSumNat z) = Encodable.encode z := by
    intro z
    cases z <;> rfl
  exact Primrec.encode_iff.mp (Primrec.encode.of_eq fun z => (h z).symm)

/-- Rebuilding an integer from its sign case is primitive recursive. -/
theorem primrec_intOfCases : Primrec (Equiv.intEquivNatSumNat.symm) := by
  have h : ∀ s : ℕ ⊕ ℕ,
      Encodable.encode (Equiv.intEquivNatSumNat.symm s) = Encodable.encode s := by
    rintro (m | n) <;> rfl
  exact Primrec.encode_iff.mp (Primrec.encode.of_eq fun s => (h s).symm)

/-- `Int.natAbs` is primitive recursive. -/
theorem primrec_intNatAbs : Primrec Int.natAbs := by
  have h := Primrec.sumCasesOn primrec_intCases
    (g := fun _ (m : ℕ) => m) (h := fun _ (n : ℕ) => n + 1)
    Primrec.snd (Primrec.succ.comp Primrec.snd)
  exact h.of_eq fun z => by cases z <;> rfl

/-- `Int.toNat` is primitive recursive. -/
theorem primrec_intToNat : Primrec Int.toNat := by
  have h := Primrec.sumCasesOn primrec_intCases
    (g := fun _ (m : ℕ) => m) (h := fun _ (_ : ℕ) => 0)
    Primrec.snd (Primrec.const 0)
  exact h.of_eq fun z => by cases z <;> rfl

/-- Nonnegativity of an integer is a primitive recursive predicate. -/
theorem primrecPred_intNonneg : PrimrecPred fun z : ℤ => 0 ≤ z := by
  refine primrecPred_iff_primrec_decide.mpr ?_
  have h := Primrec.sumCasesOn primrec_intCases
    (g := fun _ (_ : ℕ) => true) (h := fun _ (_ : ℕ) => false)
    (Primrec.const true) (Primrec.const false)
  exact h.of_eq fun z => by cases z <;> rfl

/-- The cast `ℕ → ℤ` is primitive recursive. -/
theorem primrec_natCastInt : Primrec ((↑) : ℕ → ℤ) := by
  have h := primrec_intOfCases.comp (Primrec.sumInl (β := ℕ) (α := ℕ))
  exact h.of_eq fun n => rfl

/-- Truncated subtraction of naturals, valued in `ℤ`, is primitive recursive. This is the
only integer arithmetic the evaluation proof needs. -/
theorem primrec₂_natSubInt : Primrec₂ fun a b : ℕ => ((a : ℤ) - b) := by
  have h : Primrec fun q : ℕ × ℕ =>
      if q.2 ≤ q.1 then Equiv.intEquivNatSumNat.symm (Sum.inl (q.1 - q.2))
      else Equiv.intEquivNatSumNat.symm (Sum.inr (q.2 - q.1 - 1)) := by
    refine Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst) ?_ ?_
    · exact primrec_intOfCases.comp
        (Primrec.sumInl.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    · exact primrec_intOfCases.comp
        (Primrec.sumInr.comp
          (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
            (Primrec.const 1)))
  refine h.of_eq fun q => ?_
  obtain ⟨a, b⟩ := q
  by_cases hba : b ≤ a
  · simp only [hba, if_true]
    change (((a - b : ℕ) : ℤ)) = ((a : ℤ) - b)
    omega
  · simp only [hba, if_false]
    change Int.negSucc (b - a - 1) = ((a : ℤ) - b)
    rw [Int.negSucc_eq]
    omega

end Hilbert10Experimental
