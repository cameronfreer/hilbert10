/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.DerivedDioph

/-!
# Worked examples: the two routes to a Diophantine predicate

A coherence test for the public surface, kept as a regression rather than as API. Divisibility is
proved Diophantine twice — once by mathlib's `Dioph` closure combinators, once through DPRM by way
of computability — and both proofs inhabit *literally the same* proposition, `DvdDioph`. If the
two routes needed different statements, the adapter vocabulary would be wrong.

Primality then goes through the abstract route only, as the example nobody would build by hand.

## What this measures

The direct route exercises mathlib's closure API. The abstract route exercises what this library
adds: `dioph_iff_rePred` and the derived closure on finite tuples. Agreement of the two
*statements* is the test; agreement of the two proofs is neither expected nor meaningful.

## A namespace hazard, recorded

`Hilbert10.Dioph` exists (it holds `Dioph.rePred`), so inside `namespace Hilbert10` an
`open Dioph` resolves there and shadows mathlib's `Dioph` namespace. Consumers of the closure API
must write `_root_.Dioph.dvd_dioph`. That is a naming decision worth revisiting before any of this
is offered as a library.
-/

namespace Hilbert10

/-! ### Divisibility, twice -/

/-- The statement both routes must reach, named so that agreement is mechanical. -/
private def DvdDioph : Prop := Dioph {v : Fin 2 → ℕ | v 0 ∣ v 1}

/-- **Route 1: mathlib's closure API.** Divisibility of two Diophantine functions, at two
projections. -/
private theorem dvdDioph_direct : DvdDioph :=
  _root_.Dioph.dvd_dioph (_root_.Dioph.proj_dioph 0) (_root_.Dioph.proj_dioph 1)

/-- **Route 2: through DPRM.** Divisibility is a computable predicate, and every computable
predicate on tuples is Diophantine. -/
private theorem dvdDioph_viaDPRM : DvdDioph := by
  refine ComputablePred.dioph
    (ComputablePred.of_eq (p := fun v : Fin 2 → ℕ => v 1 % v 0 = 0) ?_
      fun v => (Nat.dvd_iff_mod_eq_zero).symm)
  refine PrimrecPred.computablePred ?_
  have h0 : Primrec fun v : Fin 2 → ℕ => v 0 := Primrec.fin_app.comp Primrec.id (Primrec.const 0)
  have h1 : Primrec fun v : Fin 2 → ℕ => v 1 := Primrec.fin_app.comp Primrec.id (Primrec.const 1)
  exact PrimrecRel.comp Primrec.eq (Primrec₂.comp Primrec.nat_mod h1 h0) (Primrec.const 0)

example : DvdDioph := dvdDioph_direct
example : DvdDioph := dvdDioph_viaDPRM

/-! ### Primality, only the abstract route

Nothing here constructs a polynomial. That is the point of DPRM: it is enough that the predicate
is decided by an algorithm.

Mathlib has no `Primrec` or `Computable` lemma for `Nat.Prime`, so trial division has to be built
and related to `Nat.Prime` by hand. That cost is the finding, not an accident of this file. -/

/-- One turn of trial division, named so that `simp` cannot normalise the definition and the
lemma about it into different shapes. -/
private def stepTest (n m : ℕ) (acc : Bool) : Bool :=
  if m = 1 then acc else if n % m = 0 then false else acc

private theorem foldr_stepTest_iff (n : ℕ) (l : List ℕ) :
    (l.foldr (stepTest n) true = true) ↔ ∀ m ∈ l, m ≠ 1 → n % m ≠ 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.foldr_cons, stepTest]
    split_ifs with h1 h2
    · simp [ih, List.mem_cons, h1]
    · simp [List.mem_cons, h1, h2]
    · simp [ih, List.mem_cons, h1, h2]

/-- Trial division: no `m < n` other than `1` divides `n`. `m = 0` needs no special case, since
`0 ∣ n` forces `n = 0`, excluded by `2 ≤ n`. -/
private def primeTest (n : ℕ) : Bool :=
  if 2 ≤ n then (List.range n).foldr (stepTest n) true else false

private theorem primeTest_iff (n : ℕ) : primeTest n = true ↔ n.Prime := by
  rw [Nat.prime_def_lt, primeTest]
  by_cases hn : 2 ≤ n
  · simp only [hn, if_true, foldr_stepTest_iff, List.mem_range, true_and]
    constructor
    · intro hall m hm hdvd
      by_contra h1
      exact hall m hm h1 (Nat.dvd_iff_mod_eq_zero.mp hdvd)
    · intro hall m hm h1 hmod
      exact h1 (hall m hm (Nat.dvd_iff_mod_eq_zero.mpr hmod))
  · simp [hn]

private theorem primrec_primeTest : Primrec primeTest := by
  have hone : PrimrecPred fun q : ℕ × (ℕ × Bool) => q.2.1 = 1 :=
    PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have hmod : PrimrecPred fun q : ℕ × (ℕ × Bool) => q.1 % q.2.1 = 0 :=
    PrimrecRel.comp Primrec.eq
      (Primrec₂.comp Primrec.nat_mod Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0)
  have hacc : Primrec fun q : ℕ × (ℕ × Bool) => q.2.2 := Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ fun (n : ℕ) (q : ℕ × Bool) => stepTest n q.1 q.2 :=
    Primrec.ite hone hacc (Primrec.ite hmod (Primrec.const false) hacc)
  have hfold : Primrec fun n : ℕ => (List.range n).foldr (stepTest n) true :=
    Primrec.list_foldr Primrec.list_range (Primrec.const true) hstep
  have hle : PrimrecPred fun n : ℕ => 2 ≤ n :=
    PrimrecRel.comp Primrec.nat_le (Primrec.const 2) Primrec.id
  exact Primrec.ite hle hfold (Primrec.const false)

/-- **Primality is Diophantine**, with no polynomial in sight. -/
theorem prime_dioph : Dioph {v : Fin 1 → ℕ | (v 0).Prime} := by
  refine ComputablePred.dioph (ComputablePred.of_eq
    (p := fun v : Fin 1 → ℕ => primeTest (v 0) = true) ?_ fun v => primeTest_iff (v 0))
  refine PrimrecPred.computablePred ?_
  have h0 : Primrec fun v : Fin 1 → ℕ => v 0 := Primrec.fin_app.comp Primrec.id (Primrec.const 0)
  exact PrimrecRel.comp Primrec.eq (primrec_primeTest.comp h0) (Primrec.const true)

end Hilbert10
