/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.PolynomialCode

/-!
# Evaluating an encoded polynomial at an integer assignment

Issue #28, first piece. The wire format's `eval` takes a *natural* assignment, because that is
what the natural-root problem needs. Hilbert asked about integer solutions, so the same code has
to be readable at an integer assignment too.

## The same recursion, one type up

`evalMonomialInt` and `evalInt` mirror `evalMonomial` and `eval` exactly: same shape, same
out-of-range convention (variables past the end of the assignment are `0`), same permissiveness.
Only the assignment's type changes. That is deliberate — the two evaluations agree on natural
assignments, `evalInt_map_natCast`, which is what lets the two solvability predicates be compared
rather than merely coexist.

## Computability is not proved here

`primrec₂_eval` exists because `NatSolvable`'s recursive enumerability needs it. The integer
analogue has no consumer yet: `rePred_intSolvable` is expected to follow from
`IntSolvable ≤₀ NatSolvable` and recursive enumerability of the natural version, since recursive
enumerability transfers along many-one reductions. If some later step does need
`Primrec₂ evalInt`, it should be added then — the sign handling it requires is real work, and
speculative work here is exactly what #28 says to avoid.

## Main results

* `Hilbert10.PolynomialCode.evalInt`
* `Hilbert10.PolynomialCode.evalInt_map_natCast` — the two evaluations agree under the cast
-/

namespace Hilbert10

namespace PolynomialCode

/-- The value of a monomial at an integer assignment, by structural recursion on the exponent
vector and the assignment in parallel. Variables past the end of the assignment are taken to be
`0`, exactly as in `evalMonomial`. -/
def evalMonomialInt : MonomialCode → List ℤ → ℤ
  | [], _ => 1
  | e :: es, [] => (0 : ℤ) ^ e * evalMonomialInt es []
  | e :: es, v :: vs => v ^ e * evalMonomialInt es vs

/-- The value of an encoded polynomial at an integer assignment. -/
def evalInt (p : PolynomialCode) (x : List ℤ) : ℤ :=
  (p.terms.map fun t => t.1 * evalMonomialInt t.2 x).sum

@[simp] theorem evalMonomialInt_nil (x : List ℤ) : evalMonomialInt [] x = 1 := rfl

@[simp] theorem evalInt_mk_nil (x : List ℤ) : evalInt ⟨[]⟩ x = 0 := rfl

@[simp] theorem evalInt_mk_cons (t : ℤ × MonomialCode) (ts : List (ℤ × MonomialCode))
    (x : List ℤ) :
    evalInt ⟨t :: ts⟩ x = t.1 * evalMonomialInt t.2 x + evalInt ⟨ts⟩ x := by
  simp [evalInt]

/-! ### Agreement with the natural evaluation -/

theorem evalMonomialInt_map_natCast :
    ∀ (m : MonomialCode) (x : List ℕ),
      evalMonomialInt m (x.map (Nat.cast : ℕ → ℤ)) = evalMonomial m x
  | [], _ => rfl
  | _ :: es, [] => by
    have ih : evalMonomialInt es [] = evalMonomial es [] := by
      simpa using evalMonomialInt_map_natCast es []
    simp only [List.map_nil, evalMonomialInt, evalMonomial, ih]
  | _ :: es, v :: vs => by
    simp only [List.map_cons, evalMonomialInt, evalMonomial,
      evalMonomialInt_map_natCast es vs]

/-- **The two evaluations agree on natural assignments.** This is what makes the natural and
integer formulations comparable: a natural root is an integer root of the same code. -/
theorem evalInt_map_natCast (p : PolynomialCode) (x : List ℕ) :
    evalInt p (x.map (Nat.cast : ℕ → ℤ)) = eval p x := by
  simp only [evalInt, eval, evalMonomialInt_map_natCast]

end PolynomialCode

end Hilbert10
