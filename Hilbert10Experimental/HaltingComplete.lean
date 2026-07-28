/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

/-!
# Many-one completeness of the halting problem

Issue #24, staged here for upstreaming to mathlib. `Mathlib/Computability/Halting.lean`
proves the halting problem recursively enumerable (`ComputablePred.halting_problem_re`) and
non-computable (`ComputablePred.halting_problem`), but never proves it *many-one complete*:
at the pinned revision, `Halting.lean` and `RE.lean` contain no occurrence of `≤₀` at all.

This file supplies the missing lemma. It is not imported by the `Hilbert10` root spine: it
is an independent upstream contribution, and in the fallback endpoint factorization
recorded in issue #1 it is what turns Diophantineness of the *single* universal halting
predicate into RE-completeness of `HilbertTenth.NatSolvable`.
-/

namespace Hilbert10Experimental

open Nat.Partrec (Code)

/-- The halting problem: does the program with code `c` halt on input `0`? This is the
form used by `ComputablePred.halting_problem`. -/
def Halts (c : Code) : Prop := (Code.eval c 0).Dom

/-- Every recursively enumerable predicate on `ℕ` many-one reduces to the halting problem.

The reduction is `fun a ↦ c.comp (Code.const a)`, where `c` is a code for a partial
recursive function whose domain is the predicate: partially applying `c` to the constant
`a` produces a program that halts on *any* input exactly when `c` halts on `a`.

Note that `Code.curry`/`smn` alone does not do this, since `eval (curry c a) 0 =
eval c (Nat.pair a 0)` feeds `c` the *pair* rather than `a`. The `comp`-with-a-constant
form avoids the adapter; `Code.primrec₂_comp` and `Code.primrec_const` make it
computable. -/
theorem rePred_manyOneReducible_halts {R : ℕ → Prop} (h : REPred R) : R ≤₀ Halts := by
  -- Turn the `Unit`-valued witness of `REPred` into a partial function `ℕ →. ℕ`
  -- with the same domain.
  have hf : Partrec fun a : ℕ => (Part.assert (R a) fun _ => Part.some ()).map fun _ => (0 : ℕ) :=
    h.map (Computable.const (0 : ℕ)).to₂
  set f : ℕ →. ℕ := fun a => (Part.assert (R a) fun _ => Part.some ()).map fun _ => (0 : ℕ)
    with hf_def
  have hdom : ∀ a, (f a).Dom ↔ R a := by
    intro a
    simp [hf_def, Part.assert]
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨fun a => c.comp (Code.const a), ?_, ?_⟩
  · exact (Code.primrec₂_comp.comp (Primrec.const c) Code.primrec_const).to_comp
  · intro a
    have : Code.eval (c.comp (Code.const a)) 0 = f a := by
      simp [Code.eval, hc]
    rw [Halts, this]
    exact (hdom a).symm

end Hilbert10Experimental
