/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ExpDioph
import Mathlib.Algebra.BigOperators.Intervals
import Hilbert10Experimental.BlockPacking

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
failure is instructive: the counterexample's digits are all below the base, so what is missing
is a no-borrow *guard bit*, not a digit bound. See `not_sound_without_guard_bits` below.
-/

namespace Hilbert10

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

/-- The run from `n`, packed into base-`b` digits: digit `i` is the register value after `i`
steps. -/
def packed (n b t : ℕ) : ℕ := ∑ i ∈ range (t + 1), run n i * b ^ i

/-- The same peeling for the packed run: one more step prepends the new register value. -/
theorem packed_succ (n b : ℕ) : packed (n + 1) b (n + 1) = (n + 1) + b * packed n b n := by
  simp only [packed, run_eq]
  rw [Finset.sum_range_succ' (fun i => (n + 1 - i) * b ^ i) (n + 1), Finset.mul_sum]
  simp only [Nat.succ_sub_succ, Nat.sub_zero, pow_zero, mul_one, pow_succ]
  rw [Finset.sum_congr rfl fun i _ => show (n - i) * (b ^ i * b) = b * ((n - i) * b ^ i) by ring]
  ring

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

* `n < b` — a bound on the initial value,
* `geom b t * b + 1 = geom b t + b ^ t` — the geometric identity,
* `R + b * geom b t = n + b * R` — the step identity,

are satisfied by `n = 2, b = 3, t = 4, R = 59`, where the true run has length `2`.

**The digits are not the problem.** In base `3`, `59` is `2, 1, 0, 2`, and every digit is
already below the base. The sequence is a real run for three digits and then *wraps*: at the
fourth, `0 - 1` borrows, and the borrow propagates consistently enough that the step identity
still holds. Constraining `R < b ^ t` does not detect it either — `59 < 81`.

What is missing is a **no-borrow guard**, not a digit bound. The fix is to give every block a
spare high bit that a wrap would have to touch:

```
D := 2 ^ k                    -- permitted register values are `< D`
B := 2 * D                    -- one guard bit per block
A := (D - 1) * geom B t       -- only the low `k` bits allowed, in every block
```

and to require `n < D` together with `Nat.IsBinarySubmask R A`. The mask forces every
`B`-block of `R` below `D`; a wrap from zero produces `B - 1 ≥ D`, which sets the guard bit
and so violates the mask. It also implies `R < B ^ t`, making a separate size condition
unnecessary.

That is the invariant the masking machinery (#18, #33, #34) exists to supply, which places it
on the critical path for even this one-instruction loop. -/
theorem not_sound_without_guard_bits :
    2 < 3 ∧ geom 3 4 * 3 + 1 = geom 3 4 + 3 ^ 4 ∧
      59 + 3 * geom 3 4 = 2 + 3 * 59 ∧ ¬ HaltsIn 2 4 := by
  refine ⟨by norm_num, by decide, by decide, ?_⟩
  rw [haltsIn_iff]
  decide

/-! ### The guarded encoding

Parameterised by the **bit width** `k`, not by an arbitrary bound. The mask has its intended
block reading only when the data bound is `2 ^ k` and the block base is `2 ^ (k + 1)`: for a
general `D`, `(D - 1) * geom (2 * D) t` need not be repeated aligned binary fields at all —
base `2 * D` is not a power of two — so `IsBinarySubmask` would say nothing about base-`2D`
digits. Carrying `k` rather than an equation `D = 2 ^ k` keeps that fact out of every proof.

The geometric sum is an **existential witness** `G`, not the computed `geom`. Otherwise `geo`
is merely a true statement about an already-computed value and tests nothing: in the
`ExpDioph` encoding `G` is a variable, so the system must pin it down. `geo_unique` below
discharges that, leaving exactly one non-`ExpTerm` obligation — `mask` — rather than quietly
leaving geometric-sum arithmetisation outstanding as well.

`Nat.IsBinarySubmask` is defined here on `Nat.testBit`, so this development fixes #34's
consumer lemma instead of waiting on it, and #18's eventual public contract should match this
consumer rather than carrying a separate digit-list formulation.
-/

/-- The guarded constraint system. Every component is an `ExpTerm` equation except `mask`,
which is the single obligation #34 must supply. -/
structure Guarded (n k t R G : ℕ) : Prop where
  base : n < dataBound k
  geo : G * blockBase k + 1 = G + blockBase k ^ t
  step : R + blockBase k * G = n + blockBase k * R
  mask : Nat.IsBinarySubmask R ((dataBound k - 1) * G)

/-! ### Guarded soundness

Digits are read straight off the step equation. The characterisation supplies `r i < D`, so
`r i + 1 ≤ D < B` and no carry can occur; the wrap digit `B - 1` is therefore unreachable,
which is exactly what excludes a run that continues past zero. No induction through `n - 1`
and so no positivity obligation.
-/

private theorem sound_aux (k : ℕ) : ∀ t n R : ℕ, n < dataBound k → R < blockBase k ^ t →
    (∀ i < t, (R / blockBase k ^ i) % blockBase k < dataBound k) →
    R + blockBase k * geom (blockBase k) t = n + blockBase k * R → n = t := by
  have hB : 0 < blockBase k := by simp [blockBase]
  have hDB : dataBound k < blockBase k := by
    simp only [dataBound, blockBase]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  intro t
  induction t with
  | zero =>
    intro n R hn hR _ hstep
    simp only [pow_zero, Nat.lt_one_iff] at hR
    subst hR
    simpa [geom] using hstep.symm
  | succ t ih =>
    intro n R hn hR hdig hstep
    rw [geom_succ] at hstep
    -- digit 0 of `R` is `n`
    have hmod : R % blockBase k = n := by
      have e1 : (R + blockBase k * (1 + blockBase k * geom (blockBase k) t)) % blockBase k
          = R % blockBase k := by
        simp [Nat.add_mul_mod_self_left]
      have e2 : (n + blockBase k * R) % blockBase k = n % blockBase k := by
        simp [Nat.add_mul_mod_self_left]
      rw [hstep] at e1
      rw [e2, Nat.mod_eq_of_lt (lt_trans hn hDB)] at e1
      exact e1.symm
    set R' := R / blockBase k with hR'
    have hsplit : R = blockBase k * R' + n := by
      conv_lhs => rw [← Nat.div_add_mod R (blockBase k)]
      rw [hmod]
    have hR'lt : R' < blockBase k ^ t := by
      rw [hR', Nat.div_lt_iff_lt_mul hB, ← pow_succ]
      exact hR
    have hdig' : ∀ i < t, (R' / blockBase k ^ i) % blockBase k < dataBound k := by
      intro i hi
      rw [hR', Nat.div_div_eq_div_mul, ← pow_succ']
      exact hdig (i + 1) (by omega)
    -- cancel one block from the step equation
    have hstep' : R' + 1 + blockBase k * geom (blockBase k) t = blockBase k * R' + n := by
      refine Nat.eq_of_mul_eq_mul_left hB ?_
      have h' : blockBase k * R' + n +
            (blockBase k + blockBase k * (blockBase k * geom (blockBase k) t))
          = n + (blockBase k * (blockBase k * R') + blockBase k * n) := by
        calc blockBase k * R' + n +
              (blockBase k + blockBase k * (blockBase k * geom (blockBase k) t))
            = blockBase k * R' + n +
                blockBase k * (1 + blockBase k * geom (blockBase k) t) := by ring
          _ = n + blockBase k * (blockBase k * R' + n) := by rw [← hsplit]; exact hstep
          _ = n + (blockBase k * (blockBase k * R') + blockBase k * n) := by ring
      have goal1 : blockBase k * (R' + 1 + blockBase k * geom (blockBase k) t)
          = blockBase k * R' + blockBase k +
            blockBase k * (blockBase k * geom (blockBase k) t) := by ring
      have goal2 : blockBase k * (blockBase k * R' + n)
          = blockBase k * (blockBase k * R') + blockBase k * n := by ring
      rw [goal1, goal2]
      omega
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · -- `n = 0` would need the wrap digit `B - 1`, which the mask forbids
      exfalso
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · have hz : R' = 0 := by simpa using hR'lt
        rw [hz] at hstep'
        simp [geom] at hstep'
      · have hd1 : R' % blockBase k < dataBound k := by
          simpa using hdig' 0 htpos
        have : (R' + 1) % blockBase k = 0 := by
          have e : (R' + 1 + blockBase k * geom (blockBase k) t) % blockBase k
              = (R' + 1) % blockBase k := by simp [Nat.add_mul_mod_self_left]
          rw [hstep'] at e
          simpa [Nat.mul_mod_right] using e.symm
        have hlt : R' % blockBase k + 1 < blockBase k := by omega
        have hB2 : 1 < blockBase k := by
          have := Nat.two_pow_pos k
          simp only [dataBound] at hDB
          omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt hB2, Nat.mod_eq_of_lt hlt] at this
        omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have : m + 1 = t + 1 := by
        have := ih m R' (by omega) hR'lt hdig' (by omega)
        omega
      exact this

/-- **Guarded soundness.** A satisfying encoding yields a real run. -/
theorem guarded_sound {n k t R G : ℕ} (h : Guarded n k t R G) : HaltsIn n t := by
  obtain ⟨hbase, hgeo, hstep, hmask⟩ := h
  have hG : G = geom (blockBase k) t := geom_unique (two_le_blockBase k) hgeo
  subst hG
  rw [← guardMask_eq] at hmask
  obtain ⟨hlt, hdig⟩ := isBinarySubmask_guardMask_iff.mp hmask
  exact (haltsIn_iff n t).mpr (sound_aux k t n R hbase hlt hdig hstep)

/-! ### Guarded completeness

Structural, and consuming the recursive split directly rather than the characterisation:
`packed_succ` and `guardMask_succ` peel one block from each side in step, so
`isBinarySubmask_split` reduces the mask obligation to a digit bound plus the induction
hypothesis. That is the second of the two real use patterns — soundness consumes the
characterisation, completeness the split — and between them they fix what the eventual
block-packing module needs to export.
-/

/-- The packed countdown is a submask of the guard mask, provided the initial value fits in
the data field. -/
theorem packed_mask (k : ℕ) : ∀ n : ℕ, n < dataBound k →
    Nat.IsBinarySubmask (packed n (blockBase k) n) (guardMask k n) := by
  have hB : 0 < blockBase k := by simp [blockBase]
  have hDB : dataBound k < blockBase k := by
    simp only [dataBound, blockBase]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  intro n
  induction n with
  | zero => intro _; simp [packed, guardMask_zero]
  | succ n ih =>
    intro hn
    rw [packed_succ, guardMask_succ]
    have hlow : dataBound k - 1 < blockBase k := by omega
    rw [isBinarySubmask_split hlow]
    have hmod : ((n + 1) + blockBase k * packed n (blockBase k) n) % blockBase k = n + 1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hdiv : ((n + 1) + blockBase k * packed n (blockBase k) n) / blockBase k
        = packed n (blockBase k) n := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    rw [hmod, hdiv]
    exact ⟨isBinarySubmask_dataBound_sub_one_iff.mpr hn, ih (by omega)⟩

/-- **Guarded completeness.** A real run yields a satisfying encoding: take the bit width
from the initial value, the geometric sum for `G`, and the packed countdown for `R`. -/
theorem guarded_complete {n t : ℕ} (h : HaltsIn n t) :
    ∃ k R G, Guarded n k t R G := by
  obtain rfl : n = t := (haltsIn_iff n t).mp h
  have hk : n < dataBound n := by simpa [dataBound] using Nat.lt_two_pow_self
  exact ⟨n, packed n (blockBase n) n, geom (blockBase n) n,
    hk, geom_spec _ _, packed_spec n _, packed_mask n n hk⟩

/-- **The spike's public slice.** The machine encoding is semantically exact: a decrement
loop halts in `t` steps from `n` exactly when the guarded constraint system has a solution.

`k` is quantified existentially because `base : n < 2 ^ k` is representation data — a choice
of bit width wide enough to hold the run — and not a restriction on the relation being
encoded. -/
theorem haltsIn_iff_guarded (n t : ℕ) :
    HaltsIn n t ↔ ∃ k R G, Guarded n k t R G :=
  ⟨guarded_complete, fun ⟨_, _, _, hg⟩ => guarded_sound hg⟩

/-- The slice at work on a concrete run. -/
example : ∃ k R G, Guarded 3 k 3 R G :=
  (haltsIn_iff_guarded 3 3).mp ((haltsIn_iff 3 3).mpr rfl)

end DecLoop

end Hilbert10
