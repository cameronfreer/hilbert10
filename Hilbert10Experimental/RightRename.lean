/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Compacting only the witness variables

Issue #2, staged here for upstreaming to mathlib.

`MvPolynomial.exists_fin_rename` reindexes the *entire* variable type along an injection
`Fin n → σ`. Applied at `σ = Fin n ⊕ β` it renumbers the input variables together with the
witnesses, which destroys the input/witness partition that the whole Hilbert-tenth
development is built on (issue #6 fixes inputs as the left summand and existential
witnesses as the right one).

What is needed instead is a *right-only* compaction: the `Fin n` block is fixed pointwise
and only `β` is compacted to its finite support.
-/

namespace Hilbert10Experimental

open MvPolynomial

variable {n : ℕ} {β R : Type*} [CommSemiring R]

/-- Compact only the right summand of the variable type: the `Fin n` inputs are preserved
pointwise, and the witnesses are reindexed by a finite injection.

The proof: `MvPolynomial.exists_finset_rename` gives `p = rename Subtype.val q` for `q`
over some `s : Finset (Fin n ⊕ β)`. Enumerate `s.toRight` with `Fintype.equivFin` and send
`s` into `Fin n ⊕ Fin m` by leaving left-hand variables alone and reindexing right-hand
ones — the whole content is that this map composed with `Sum.map id f` is `Subtype.val`.
Note the left part is *not* cut down to those inputs that actually occur: keeping all of
`Fin n` is what makes the statement usable, and unused variables are harmless. -/
theorem exists_fin_right_rename (p : MvPolynomial (Fin n ⊕ β) R) :
    ∃ (m : ℕ) (f : Fin m → β) (_ : Function.Injective f) (q : MvPolynomial (Fin n ⊕ Fin m) R),
      p = rename (Sum.map id f) q := by
  classical
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let e := Fintype.equivFin {x // x ∈ s.toRight}
  let g : {x // x ∈ s} → Fin n ⊕ Fin (Fintype.card {x // x ∈ s.toRight}) := fun x =>
    match h : x.1 with
    | Sum.inl a => Sum.inl a
    | Sum.inr b => Sum.inr (e ⟨b, Finset.mem_toRight.mpr (h ▸ x.2)⟩)
  have hcomp : ∀ x : {x // x ∈ s},
      Sum.map id (fun i => (e.symm i : β)) (g x) = (x : Fin n ⊕ β) := by
    rintro ⟨v, hv⟩
    cases v with
    | inl a => rfl
    | inr b => simp [g]
  refine ⟨_, fun i => (e.symm i : β), fun i j hij => e.symm.injective (Subtype.ext hij),
    rename g q, ?_⟩
  have hfun : ((Sum.map id fun i => (e.symm i : β)) ∘ g) = Subtype.val := funext hcomp
  rw [rename_rename, hfun]

/-- The evaluation corollary that downstream actually consumes. Stated with assignments in
the coefficient ring; for a different target ring use `eval₂` with a `RingHom R →+* S`
rather than an `S`-valued `eval`, which would not typecheck against `R` coefficients. -/
theorem eval_of_exists_fin_right_rename (p : MvPolynomial (Fin n ⊕ β) R)
    {m : ℕ} {f : Fin m → β} {q : MvPolynomial (Fin n ⊕ Fin m) R}
    (hq : p = rename (Sum.map id f) q) (x : Fin n → R) (y : β → R) :
    eval (Sum.elim x y) p = eval (Sum.elim x (y ∘ f)) q := by
  subst hq
  have hassign : Sum.elim x y ∘ Sum.map id f = Sum.elim x (y ∘ f) := by
    funext i
    cases i <;> rfl
  rw [eval_rename, hassign]

end Hilbert10Experimental
