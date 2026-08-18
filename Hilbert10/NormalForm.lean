/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.PolyBridge
import Hilbert10.Internal.ForMathlib.RightRename

/-!
# The finite Diophantine normal form

Issue #6, the headline result of M1. Mathlib's `Dioph` existentially quantifies an
arbitrary witness type `β : Type u` and a bespoke `Poly`. Here we show that for relations
on finite tuples one may always take the witnesses to be `Fin m` and the polynomial to be
an honest `MvPolynomial`.

This fixes the convention every later milestone depends on: **inputs are the left summand
`Fin n`, existentially quantified witnesses are the right summand `Fin m`**.

## Implementation notes

The order of the two steps matters. Finiteness of the witness block is *created* by
`Hilbert10.exists_mvPolynomial` (in `PolyBridge`), whose output has finite support by
construction; the arbitrary `β` in `Dioph` gives no finiteness on its own. Only then can
`exists_fin_right_rename` compact that support to `Fin m`.

Witnesses outside the range of the compacting injection are unused, so the reverse
inclusion extends a `Fin m`-tuple back to a `β`-tuple with `Function.extend`.
-/

namespace Hilbert10

open MvPolynomial

variable {α β : Type*} {n : ℕ}

/-- Casting a `Sum.elim` of natural-valued tuples agrees with `Sum.elim` of the casts. -/
theorem sum_elim_cast (x : α → ℕ) (y : β → ℕ) :
    (Sum.elim (fun i => (x i : ℤ)) fun j => (y j : ℤ)) = fun i => ((Sum.elim x y i : ℕ) : ℤ) := by
  funext i
  cases i <;> rfl

/-- **The finite Diophantine normal form.** A relation on `Fin n`-tuples of naturals is
Diophantine exactly when it is represented by a multivariate integer polynomial in `n`
input variables and finitely many witness variables.

This discharges the "Connect `Poly` to `MvPolynomial`" TODO of `Mathlib.NumberTheory.Dioph`
in the form the rest of the project needs. -/
theorem dioph_iff_exists_fin_mvPolynomial (R : (Fin n → ℕ) → Prop) :
    Dioph {x : Fin n → ℕ | R x} ↔
      ∃ (m : ℕ) (p : MvPolynomial (Fin n ⊕ Fin m) ℤ), RepresentsNat p R := by
  constructor
  · rintro ⟨β, p, hp⟩
    have hp' : ∀ v : Fin n → ℕ, R v ↔ ∃ t : β → ℕ, p (Sum.elim v t) = 0 := hp
    -- Replace the bespoke `Poly` by an `MvPolynomial`: this is where finiteness appears.
    obtain ⟨q, hq⟩ := exists_mvPolynomial p
    -- Compact the witness variables, leaving the inputs alone.
    obtain ⟨m, f, hf, q', rfl⟩ := exists_fin_right_rename (σ := Fin n) q
    -- Evaluating the compacted polynomial at a witness tuple pulled back along `f`.
    have key : ∀ (x : Fin n → ℕ) (t : β → ℕ),
        eval (Sum.elim (fun i => (x i : ℤ)) fun j => ((t (f j) : ℕ) : ℤ)) q' =
          p (Sum.elim x t) := by
      intro x t
      rw [← hq (Sum.elim x t), ← sum_elim_cast]
      exact (eval_of_exists_fin_right_rename _ rfl (fun i => (x i : ℤ)) fun b => (t b : ℤ)).symm
    refine ⟨m, q', fun x => ?_⟩
    rw [hp' x]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨fun j => t (f j), (key x t).trans ht⟩
    · rintro ⟨y, hy⟩
      classical
      refine ⟨Function.extend f y (fun _ => 0), ?_⟩
      rw [← key x (Function.extend f y fun _ => 0)]
      simpa only [hf.extend_apply] using hy
  · rintro ⟨m, p, hp⟩
    refine ⟨Fin m, toDiophPoly p, fun x => ?_⟩
    change R x ↔ _
    rw [hp x]
    exact exists_congr fun y => by rw [toDiophPoly_apply, ← sum_elim_cast]

end Hilbert10
