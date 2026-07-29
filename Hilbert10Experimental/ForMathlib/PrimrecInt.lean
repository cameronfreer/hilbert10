/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Primrec.Basic

/-!
# Integers are primitive recursive

Issue #36, destined for `Mathlib/Computability/Primrec/Int.lean`. At the pinned mathlib
revision the computability library exposes no lemmas about `ℤ` at all — no `Primrec`, no
`Computable`, for any integer operation. `Primcodable ℤ` exists only because
`Denumerable ℤ` does.

## Main results

* `Primrec.intEquivNatSumNat` / `Primrec.intEquivNatSumNat_symm`: the sign-case view
  `ℤ ≃ ℕ ⊕ ℕ` is primitive recursive in both directions.
* `Primrec.int_natAbs`, `Primrec.int_toNat`, `Primrec.int_nonneg`, `Primrec.int_natCast`,
  `Primrec.int_subNat`.

## Implementation notes

`Primcodable ℤ` encodes through `Equiv.intEquivNat = intEquivNatSumNat.trans
natSumNatEquivNat`, and `Equiv.natSumNatEquivNat_apply` is `Sum.elim (2 * ·) (2 * · + 1)`.
`Encodable.encodeSum` is `2 * encode ·` / `2 * encode · + 1`. These are the same function,
so the two encodings agree definitionally and the sign-case view is primitive recursive by
`cases z <;> rfl`. Everything else is a `Primrec.sumCasesOn` over that.

Only what is needed downstream is proved. The full integer ring API — `Int.add`, `Int.mul`
and friends — is each a further sign case analysis, and should be added when something
requires it.
-/

namespace Primrec

/-- Viewing an integer by its sign case is primitive recursive. -/
theorem intEquivNatSumNat : Primrec (Equiv.intEquivNatSumNat) := by
  have h : ∀ z : ℤ, Encodable.encode (Equiv.intEquivNatSumNat z) = Encodable.encode z := by
    intro z
    cases z <;> rfl
  exact Primrec.encode_iff.mp (Primrec.encode.of_eq fun z => (h z).symm)

/-- Rebuilding an integer from its sign case is primitive recursive. -/
theorem intEquivNatSumNat_symm : Primrec (Equiv.intEquivNatSumNat.symm) := by
  have h : ∀ s : ℕ ⊕ ℕ,
      Encodable.encode (Equiv.intEquivNatSumNat.symm s) = Encodable.encode s := by
    rintro (m | n) <;> rfl
  exact Primrec.encode_iff.mp (Primrec.encode.of_eq fun s => (h s).symm)

/-- `Int.natAbs` is primitive recursive. -/
theorem int_natAbs : Primrec Int.natAbs := by
  have h := Primrec.sumCasesOn intEquivNatSumNat
    (g := fun _ (m : ℕ) => m) (h := fun _ (n : ℕ) => n + 1)
    Primrec.snd (Primrec.succ.comp Primrec.snd)
  exact h.of_eq fun z => by cases z <;> rfl

/-- `Int.toNat` is primitive recursive. -/
theorem int_toNat : Primrec Int.toNat := by
  have h := Primrec.sumCasesOn intEquivNatSumNat
    (g := fun _ (m : ℕ) => m) (h := fun _ (_ : ℕ) => 0)
    Primrec.snd (Primrec.const 0)
  exact h.of_eq fun z => by cases z <;> rfl

/-- Nonnegativity of an integer is a primitive recursive predicate. -/
theorem int_nonneg : PrimrecPred fun z : ℤ => 0 ≤ z := by
  refine primrecPred_iff_primrec_decide.mpr ?_
  have h := Primrec.sumCasesOn intEquivNatSumNat
    (g := fun _ (_ : ℕ) => true) (h := fun _ (_ : ℕ) => false)
    (Primrec.const true) (Primrec.const false)
  exact h.of_eq fun z => by cases z <;> rfl

/-- The cast `ℕ → ℤ` is primitive recursive. -/
theorem int_natCast : Primrec ((↑) : ℕ → ℤ) := by
  have h := intEquivNatSumNat_symm.comp (Primrec.sumInl (β := ℕ) (α := ℕ))
  exact h.of_eq fun n => rfl

/-- The difference of two natural numbers, valued in `ℤ`, is primitive recursive. Note the
result is a genuine integer difference, not truncated subtraction. -/
theorem int_subNat : Primrec₂ fun a b : ℕ => ((a : ℤ) - b) := by
  have h : Primrec fun q : ℕ × ℕ =>
      if q.2 ≤ q.1 then Equiv.intEquivNatSumNat.symm (Sum.inl (q.1 - q.2))
      else Equiv.intEquivNatSumNat.symm (Sum.inr (q.2 - q.1 - 1)) := by
    refine Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst) ?_ ?_
    · exact intEquivNatSumNat_symm.comp
        (Primrec.sumInl.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    · exact intEquivNatSumNat_symm.comp
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

end Primrec
