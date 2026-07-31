/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ExpDioph
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Bitwise

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

/-- Every binary digit of `a` is at most the corresponding digit of `b`. -/
def _root_.Nat.IsBinarySubmask (a b : ℕ) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

/-- Permitted register values are `< 2 ^ k`. -/
def dataBound (k : ℕ) : ℕ := 2 ^ k

/-- The packing base: one guard bit above the data field. -/
def blockBase (k : ℕ) : ℕ := 2 ^ (k + 1)

theorem blockBase_eq (k : ℕ) : blockBase k = 2 * dataBound k := by
  simp [blockBase, dataBound, pow_succ, mul_comm]

theorem two_le_blockBase (k : ℕ) : 2 ≤ blockBase k := by
  simpa [blockBase] using Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ (Nat.zero_le k))

/-- The guarded constraint system. Every component is an `ExpTerm` equation except `mask`,
which is the single obligation #34 must supply. -/
structure Guarded (n k t R G : ℕ) : Prop where
  base : n < dataBound k
  geo : G * blockBase k + 1 = G + blockBase k ^ t
  step : R + blockBase k * G = n + blockBase k * R
  mask : Nat.IsBinarySubmask R ((dataBound k - 1) * G)

/-- The geometric identity pins `G` down: it has exactly one solution, the geometric sum.
So making `G` a variable costs nothing, and the arithmetisation of the geometric series is
not left as a hidden obligation. -/
theorem geo_unique {k t G : ℕ} (h : G * blockBase k + 1 = G + blockBase k ^ t) :
    G = geom (blockBase k) t := by
  obtain ⟨C, hC⟩ : ∃ C, blockBase k = C + 1 :=
    ⟨blockBase k - 1, by have := two_le_blockBase k; omega⟩
  have hC0 : 0 < C := by have := two_le_blockBase k; omega
  have h1 : G * C + 1 = blockBase k ^ t := by
    have h' : G * C + G + 1 = G + blockBase k ^ t := by
      calc G * C + G + 1 = G * (C + 1) + 1 := by ring
        _ = G + blockBase k ^ t := by rw [← hC]; exact h
    omega
  have h2 : geom (blockBase k) t * C + 1 = blockBase k ^ t := by
    have hg := geom_spec (blockBase k) t
    have h' : geom (blockBase k) t * C + geom (blockBase k) t + 1 =
        geom (blockBase k) t + blockBase k ^ t := by
      calc geom (blockBase k) t * C + geom (blockBase k) t + 1
          = geom (blockBase k) t * (C + 1) + 1 := by ring
        _ = geom (blockBase k) t + blockBase k ^ t := by rw [← hC]; exact hg
    omega
  exact Nat.eq_of_mul_eq_mul_right hC0 (Nat.add_right_cancel (h1.trans h2.symm))


/-! ### The mask characterisation

The single theorem both directions need. It is stated as an equivalence rather than as a
one-way consumer lemma so that it also fixes #34's **semantic contract**: whatever #34 proves
exponential Diophantine must be equivalent to exactly this.
-/

/-- `guardMask k t` is the number whose set bits are the low `k` bits of each of the first
`t` blocks of width `k + 1`. -/
def guardMask' (k t : ℕ) : ℕ := (dataBound k - 1) * geom (blockBase k) t

theorem guardMask'_zero (k : ℕ) : guardMask' k 0 = 0 := by simp [guardMask', geom]

/-- One more block, prepended below the rest. -/
theorem guardMask'_succ (k t : ℕ) :
    guardMask' k (t + 1) = (dataBound k - 1) + blockBase k * guardMask' k t := by
  simp only [guardMask', geom_succ, Nat.mul_add, mul_one]
  ring

/-- Splitting a submask condition at a power-of-two boundary. This is the engine of the
characterisation: because `blockBase k` is a power of two, the low block and the remaining
blocks are independent bit ranges. -/
theorem isBinarySubmask_split {k x a b : ℕ} (ha : a < blockBase k) :
    Nat.IsBinarySubmask x (a + blockBase k * b) ↔
      Nat.IsBinarySubmask (x % blockBase k) a ∧ Nat.IsBinarySubmask (x / blockBase k) b := by
  have ha' : a < 2 ^ (k + 1) := by simpa [blockBase] using ha
  have hmask : ∀ j, (a + 2 ^ (k + 1) * b).testBit j =
      if j < k + 1 then a.testBit j else b.testBit (j - (k + 1)) := by
    intro j
    have h : a + 2 ^ (k + 1) * b = 2 ^ (k + 1) * b + a := by ring
    rw [h, Nat.testBit_two_pow_mul_add b ha' j]
  simp only [Nat.IsBinarySubmask, blockBase, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i hi.2
      rw [hmask i, if_pos hi.1] at this
      exact this
    · have := h (i + (k + 1)) hi
      rw [hmask _, if_neg (by omega)] at this
      simpa using this
  · rintro ⟨hlo, hhi⟩ i hi
    rw [hmask i]
    by_cases hik : i < k + 1
    · rw [if_pos hik]
      exact hlo i ⟨hik, hi⟩
    · rw [if_neg hik]
      exact hhi (i - (k + 1)) (by rwa [Nat.sub_add_cancel (by omega)])

/-- The API bridge: `Guarded.mask` is stated with the closed form `(dataBound k - 1) * G`, and
after `geo_unique` that *is* `guardMask' k t`. Definitional, but named so the rewrite step is
explicit. -/
theorem guardMask'_eq (k t : ℕ) :
    guardMask' k t = (dataBound k - 1) * geom (blockBase k) t := rfl

/-- A number is a submask of `2 ^ k - 1` exactly when it fits in `k` bits. This is where the
guard bit does its work: `dataBound k - 1` permits precisely the low `k` bits, so the extra
bit of each `(k + 1)`-bit block is unavailable. -/
theorem isBinarySubmask_dataBound_sub_one_iff {k x : ℕ} :
    Nat.IsBinarySubmask x (dataBound k - 1) ↔ x < dataBound k := by
  simp only [Nat.IsBinarySubmask, dataBound, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  constructor
  · intro h
    refine Nat.lt_pow_two_of_testBit x fun i hi => ?_
    by_contra hc
    exact absurd (h i (by simpa using hc)) (by omega)
  · intro hx i hi
    by_contra hik
    have hle : (2 : ℕ) ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle)] at hi
    simp at hi

/-- **The mask characterisation.** Stated as an equivalence, so that it serves soundness
(every block bound, plus the global bound), completeness (the mask reduced to ordinary bounds
on packed values), and fixes #34's exact semantic contract. -/
theorem isBinarySubmask_guardMask_iff {k t R : ℕ} :
    Nat.IsBinarySubmask R (guardMask' k t) ↔
      R < blockBase k ^ t ∧ ∀ i < t, (R / blockBase k ^ i) % blockBase k < dataBound k := by
  induction t generalizing R with
  | zero =>
    simp only [guardMask'_zero, pow_zero, Nat.lt_one_iff]
    constructor
    · intro h
      refine ⟨Nat.zero_of_testBit_eq_false fun i => ?_, by omega⟩
      by_contra hc
      simpa using h i (by simpa using hc)
    · rintro ⟨rfl, -⟩ i hi
      simp at hi
  | succ t ih =>
    have hlow : dataBound k - 1 < blockBase k := by
      simp only [dataBound, blockBase]
      have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
      have h2 : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    rw [guardMask'_succ, isBinarySubmask_split hlow, isBinarySubmask_dataBound_sub_one_iff, ih]
    have hB : 0 < blockBase k := by simp [blockBase]
    constructor
    · rintro ⟨hmod, hdiv, hblk⟩
      refine ⟨?_, fun i hi => ?_⟩
      · rw [pow_succ]
        exact (Nat.div_lt_iff_lt_mul hB).mp hdiv
      · cases i with
        | zero => simpa using hmod
        | succ i =>
          have := hblk i (by omega)
          rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this
    · rintro ⟨hlt, hblk⟩
      refine ⟨by simpa using hblk 0 (by omega), ?_, fun i hi => ?_⟩
      · refine (Nat.div_lt_iff_lt_mul hB).mpr ?_
        rwa [← pow_succ]
      · have := hblk (i + 1) (by omega)
        rwa [Nat.div_div_eq_div_mul, ← pow_succ']

end DecLoop

end Hilbert10Experimental
