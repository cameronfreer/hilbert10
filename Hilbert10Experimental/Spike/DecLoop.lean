/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ExpDioph
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Route spike: arithmetising a decrement-to-zero loop

Issue #15, machine route. The smallest machine fragment with an *unbounded* run length: one
register, one instruction, "while `r ≠ 0` do `r := r - 1`". A fixed-length run would be a
finite conjunction and would test nothing; this run has length `n`, so the arithmetisation
must handle a length it cannot see.

## What is being tested

Whether a run can be *packed* into a single number — its base-`b` digits being the successive
register values — with the step relation expressed as one arithmetic identity between the
packed run and its shift. That is the technique #21 would use at scale, so the spike is
about the technique, not about this loop.

## Result so far

Completeness works and is cheap. **Soundness fails for the naive constraint system**, and the
failure is instructive rather than incidental: see `not_sound_without_digit_bounds` below.
-/

namespace Hilbert10Experimental

namespace DecLoop

open Finset

/-! ### The machine -/

/-- One step: decrement the register. -/
def step (r : ℕ) : ℕ := r - 1

/-- The register value after `t` steps. -/
def run (r : ℕ) : ℕ → ℕ
  | 0 => r
  | t + 1 => step (run r t)

/-- The loop halts from `r` in exactly `t` steps: the register is zero then, and never
before. -/
def HaltsIn (r t : ℕ) : Prop := run r t = 0 ∧ ∀ s, s < t → run r s ≠ 0

@[simp] theorem run_eq (r t : ℕ) : run r t = r - t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [run, step, ih]; omega

/-- The operational semantics, solved: the loop halts in exactly `r` steps. Everything below
must be proved *without* using this, or the spike would be testing nothing. -/
theorem haltsIn_iff (r t : ℕ) : HaltsIn r t ↔ r = t := by
  constructor
  · rintro ⟨h0, hlt⟩
    by_contra hne
    rcases Nat.lt_or_ge r t with h | h
    · exact hlt r h (by simp)
    · exact hne (by simp at h0; omega)
  · rintro rfl
    exact ⟨by simp, fun s hs => by simp; omega⟩

/-! ### The packed encoding -/

/-- `∑ i < t, b ^ i`, the geometric sum that counts one decrement per step. -/
def geom (b t : ℕ) : ℕ := ∑ i ∈ range t, b ^ i

/-- The run from `n`, packed into base-`b` digits: digit `i` is the register value after `i`
steps. -/
def packed (n b t : ℕ) : ℕ := ∑ i ∈ range (t + 1), run n i * b ^ i

/-- Peeling the first digit: one more step multiplies the geometric sum by the base. -/
theorem geom_succ (b n : ℕ) : geom b (n + 1) = 1 + b * geom b n := by
  simp only [geom, Finset.sum_range_succ']
  rw [Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- The same peeling for the packed run: one more step prepends the new register value. -/
theorem packed_succ (n b : ℕ) : packed (n + 1) b (n + 1) = (n + 1) + b * packed n b n := by
  simp only [packed, run_eq]
  rw [Finset.sum_range_succ' (fun i => (n + 1 - i) * b ^ i) (n + 1), Finset.mul_sum]
  simp only [Nat.succ_sub_succ, Nat.sub_zero, pow_zero, mul_one, pow_succ]
  rw [Finset.sum_congr rfl fun i _ => show (n - i) * (b ^ i * b) = b * ((n - i) * b ^ i) by ring]
  ring

/-- The geometric identity, in the subtraction-free form the arithmetisation needs. Holds
for every base, including degenerate ones. -/
theorem geom_spec (b t : ℕ) : geom b t * b + 1 = geom b t + b ^ t := by
  induction t with
  | zero => simp [geom]
  | succ t ih =>
    rw [geom_succ, pow_succ]
    nlinarith [ih]

/-- **Packed-run completeness.** A real run yields a satisfying encoding: the packed run and
the geometric sum satisfy the step identity, for every base. -/
theorem packed_spec (n b : ℕ) :
    packed n b n + b * geom b n = n + b * packed n b n := by
  induction n with
  | zero => simp [packed, geom]
  | succ n ih =>
    rw [packed_succ, geom_succ]
    nlinarith [ih]

/-! ### Where the naive system fails

The three constraints

* `n < b` — the digit bound,
* `geom b t * b + 1 = geom b t + b ^ t` — the geometric identity,
* `R + b * geom b t = n + b * R` — the step identity,

are satisfied by `n = 2, b = 3, t = 4, R = 59`, where the true run has length `2`. In base
`3`, `59` has digits `2, 1, 0, 2`: the first three are a real run, and then the fourth
*wraps* — `0 - 1` is not representable, so the borrow silently produces a digit of `2`
instead of failing.

So the step identity encodes "each digit is one less than the previous" only when the digits
are known to stay below the base. Constraining `R < b ^ t` does not help: `59 < 81`.
Controlling digits is exactly what binary masking (#18, #33, #34) exists to do, which places
that machinery on the critical path for even this trivial loop. -/
theorem not_sound_without_digit_bounds :
    2 < 3 ∧ geom 3 4 * 3 + 1 = geom 3 4 + 3 ^ 4 ∧
      59 + 3 * geom 3 4 = 2 + 3 * 59 ∧ ¬ HaltsIn 2 4 := by
  refine ⟨by norm_num, by decide, by decide, ?_⟩
  rw [haltsIn_iff]
  decide

end DecLoop

end Hilbert10Experimental
