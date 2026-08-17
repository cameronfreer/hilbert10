/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.DPRM
import Hilbert10.Specialization

/-!
# H10 endpoints: recursively enumerable predicates reduce to `NatSolvable`

Issue #25. DPRM (#23) says a recursively enumerable predicate is Diophantine; #35 says a
represented predicate many-one reduces to `NatSolvable`. This file is the wrapper that composes
them, so the only content here is the shuffle between `R : ℕ → Prop` and the unary tuple
predicate `fun v : Fin 1 → ℕ => R (v 0)` that `Dioph` is stated for.

## The code is fixed per relation

The polynomial is obtained by eliminating an existential inside a proposition, so it is chosen
*for each* `R` and there is no function from predicates to codes here. Nothing in this
development produces a code uniform in `R`, and nothing needs one — the reduction
`fun a => code.instantiate [a]` is computable because `code` is a constant. See
`Specialization.lean` and #1's scope argument.

## Arbitrary domains, including the empty one

`REPred.manyOneReducible_natSolvable'` is the same statement for a predicate on any
`Primcodable` type, with **no `Inhabited` hypothesis**. #26 offered two ways to get there:
carry `[Inhabited α]`, or hand-roll the transported predicate `fun n => ∃ a, encode a = n ∧ R a`.
Neither was needed. Nonemptiness is decided inside the proof: when `α` is inhabited, mathlib's
`toNat` applies and `manyOneReducible_toNat` supplies the reduction; when it is empty, any
computable function is a reduction because the equivalence it has to satisfy is vacuous.

Recording that so it is not re-litigated: the case split costs two lines and keeps the
hypothesis off the statement, which is what a completeness theorem should look like.

## What the endpoints say

`NatSolvable` is **many-one complete among recursively enumerable predicates**: it is itself
recursively enumerable (#14), and every recursively enumerable predicate reduces to it. That is
the computability-theoretic content of Hilbert's tenth problem, and it says more than
undecidability — undecidability is the corollary obtained by reducing the halting problem.

Over the naturals, and for the encoded-polynomial form of the problem. Hilbert asked about
integer solutions; that equivalence is #28.

## Main results

* `Hilbert10.REPred.manyOneReducible_natSolvable`
* `Hilbert10.REPred.manyOneReducible_natSolvable'`
* `Hilbert10.natSolvable_re_complete`
* `Hilbert10.halting_manyOneReducible_natSolvable`
* `Hilbert10.not_computablePred_natSolvable`
-/

namespace Hilbert10

/-- A unary predicate on `ℕ`, read as a predicate on one-element tuples, stays recursively
enumerable: it is the original composed with the computable projection.

Stated as a plain lemma rather than for dot notation, since `REPred` unfolds through `Partrec`
to `Nat.Partrec` and dot notation resolves against that. -/
theorem REPred.fin_one {R : ℕ → Prop} (hR : REPred R) : REPred fun v : Fin 1 → ℕ => R (v 0) :=
  Partrec.comp hR ((Primrec.fin_app.comp Primrec.id (Primrec.const 0)).to_comp)

/-- **Every recursively enumerable predicate on `ℕ` many-one reduces to `NatSolvable`.**

DPRM supplies a Diophantine representation, the normal form turns it into a polynomial, and the
specialisation lemma turns that into a computable reduction. -/
theorem REPred.manyOneReducible_natSolvable {R : ℕ → Prop} (hR : REPred R) :
    R ≤₀ NatSolvable :=
  representsNat_manyOneReducible_natSolvable
    ((dioph_iff_exists_fin_mvPolynomial _).mp (REPred.dioph (REPred.fin_one hR)))

/-- **The same, for a predicate on any `Primcodable` type.** No `Inhabited` hypothesis: the empty
case is handled separately, where the reduction's equivalence is vacuous. -/
theorem REPred.manyOneReducible_natSolvable' {α : Type*} [Primcodable α] {R : α → Prop}
    (hR : REPred R) : R ≤₀ NatSolvable := by
  by_cases hne : Nonempty α
  · obtain ⟨a₀⟩ := hne
    haveI : Inhabited α := ⟨a₀⟩
    have hRE : REPred fun n : ℕ => R ((Encodable.decode (α := α) n).getD default) :=
      Partrec.comp hR (Computable.option_getD Computable.decode (Computable.const default))
    exact manyOneReducible_toNat.trans (REPred.manyOneReducible_natSolvable hRE)
  · exact ⟨fun _ => ⟨[]⟩, Computable.const _, fun a => absurd ⟨a⟩ hne⟩

/-! ### The endpoints

`rePred_natSolvable` is the other half of completeness and lives in `DiophToRE` (#14): evaluating
an encoded polynomial at a witness is computable, so solvability is recursively enumerable. -/

/-- **`NatSolvable` is many-one complete among recursively enumerable predicates.** Together with
`rePred_natSolvable` this is the computability-theoretic form of Hilbert's tenth problem. -/
theorem natSolvable_re_complete {α : Type*} [Primcodable α] {R : α → Prop} (hR : REPred R) :
    R ≤₀ NatSolvable :=
  REPred.manyOneReducible_natSolvable' hR

/-- **The halting problem reduces to `NatSolvable`.** An instance of completeness, and the one
that makes the undecidability corollary immediate. -/
theorem halting_manyOneReducible_natSolvable :
    (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ NatSolvable :=
  natSolvable_re_complete (ComputablePred.halting_problem_re 0)

/-- **Hilbert's tenth problem over the naturals is undecidable.** -/
theorem not_computablePred_natSolvable : ¬ ComputablePred NatSolvable := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_natSolvable h)

end Hilbert10
