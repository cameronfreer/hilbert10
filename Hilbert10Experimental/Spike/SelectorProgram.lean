/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.Spike.SelectorSlice

/-!
# The selector encoding for an arbitrary one-register program: the blockwise layer

#49, phase 3. `Spike/SelectorSlice` proved the selector encoding correct for one fixed program.
The obligation is `Aggregation 1`, which is the same statement for *every* `P : Program 1`, so
what has to be replaced is the hand-written condition list: the selector family must be indexed
by the instruction list rather than enumerated.

## Two lanes per instruction

Each instruction gets an *ordinary* selector `A p` and a *zero* selector `Z p`. For a decrement
these are the positive and zero branches. For an increment the zero selector is forced to `0` by
`Z p ≤ (P[p]).zeroBranch`, so an increment costs a selector it never uses rather than a
dependent branch index — the shape of the condition list then does not depend on which
instruction sits at `p`, only its coefficients do.

The per-instruction coefficients are five numbers: `posTarget`, `zeroTarget`, `gain`, `loss`,
`zeroBranch`. Every condition is a sum over `Fin P.length` of a coefficient times a selector,
which is the shape `Spike/SelectorMask`'s `fieldsCode_sum_smul` already packs.

## Subtraction-free, still

`gain` and `loss` split the register update into two nonnegative parts, so the decrement's
`r0 - 1` is `r0Next + 1 = r0Here` and never a subtraction. The residual `res` witnesses
`r0Here ≥ 1` on any branch that decrements, exactly as in the slice, and one residual suffices
for the whole program because the selectors are one-hot.

## Scope

This file is the blockwise layer only: `blockStep_iff` says the encoded step relation, at a
sequence of fitting configurations, is exactly the existence of selector families satisfying
`BlockStep`. Packing it into global identities and representing those is the next layer, and
`Aggregation 1` is not proved here.
-/

namespace Hilbert10

namespace RegisterMachine

/-! ### Per-instruction coefficients -/

namespace Instr

/-- The target of the ordinary branch: an increment's jump, a decrement's positive jump. -/
def posTarget : Instr 1 → ℕ
  | .inc _ j => j
  | .dec _ jpos _ => jpos

/-- The target of the zero branch. An increment has none; the value is irrelevant, because its
zero selector is forced to `0`. -/
def zeroTarget : Instr 1 → ℕ
  | .inc _ _ => 0
  | .dec _ _ jzero => jzero

/-- What the ordinary branch adds to the register. -/
def gain : Instr 1 → ℕ
  | .inc _ _ => 1
  | .dec _ _ _ => 0

/-- What the ordinary branch removes from the register. -/
def loss : Instr 1 → ℕ
  | .inc _ _ => 0
  | .dec _ _ _ => 1

/-- Whether a zero branch exists at all. -/
def zeroBranch : Instr 1 → ℕ
  | .inc _ _ => 0
  | .dec _ _ _ => 1

end Instr

/-! ### Sums against a one-hot family -/

/-- A sum against an index indicator collapses to one term. -/
theorem sum_indicator {L m : ℕ} (h : m < L) (f : Fin L → ℕ) :
    ∑ p : Fin L, (if (p : ℕ) = m then f p else 0) = f ⟨m, h⟩ := by
  rw [Finset.sum_congr rfl (g := fun p : Fin L => if p = ⟨m, h⟩ then f p else 0) fun p _ => ?_]
  · simp
  · by_cases hp : (p : ℕ) = m
    · rw [if_pos hp, if_pos (Fin.ext hp)]
    · rw [if_neg hp, if_neg (fun he : p = ⟨m, h⟩ => hp (by rw [he]))]

/-- A sum whose family vanishes off one index collapses to that index. -/
theorem sum_eq_of_vanishing {L : ℕ} {g : Fin L → ℕ} {q : Fin L} (h : ∀ p, p ≠ q → g p = 0) :
    ∑ p : Fin L, g p = g q :=
  Finset.sum_eq_single q (fun p _ hp => h p hp) (fun hq => absurd (Finset.mem_univ q) hq)

/-- A family of naturals summing to `1` is `1` at one index and `0` everywhere else. -/
theorem exists_unique_of_sum_eq_one {L : ℕ} {g : Fin L → ℕ} (h : ∑ p : Fin L, g p = 1) :
    ∃ q, g q = 1 ∧ ∀ p, p ≠ q → g p = 0 := by
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ p : Fin L, g p ≠ 0)
  have hsplit : g q + ∑ p ∈ Finset.univ.erase q, g p = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ q)]; exact h
  refine ⟨q, by omega, fun p hp => ?_⟩
  have hz : ∑ p ∈ Finset.univ.erase q, g p = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp hz) p (Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩)

/-! ### The blockwise conditions -/

/-- **The selector conditions at one step, for an arbitrary one-register program.**

`A p` selects instruction `p`'s ordinary branch and `Z p` its zero branch. Read in order: the
selectors are one-hot; the program counter names the selected instruction and jumps to its
selected target; the register update splits into `gain` and `loss`; only a decrement may take a
zero branch, and taking one forces the register to vanish; the residual forces the register to
be at least one on any branch that decrements; and each selected target fits. -/
def BlockStep (P : Program 1) (w pcHere pcNext r0Here r0Next res : ℕ)
    (A Z : Fin P.length → ℕ) : Prop :=
  ∑ p : Fin P.length, (A p + Z p) = 1 ∧
  pcHere = ∑ p : Fin P.length, (p : ℕ) * (A p + Z p) ∧
  pcNext = ∑ p : Fin P.length, ((P.get p).posTarget * A p + (P.get p).zeroTarget * Z p) ∧
  r0Next + ∑ p : Fin P.length, (P.get p).loss * A p
    = r0Here + ∑ p : Fin P.length, (P.get p).gain * A p ∧
  (∀ p, Z p ≤ (P.get p).zeroBranch) ∧
  (∑ p : Fin P.length, Z p = 1 → r0Here = 0) ∧
  r0Here = res + ∑ p : Fin P.length, (P.get p).loss * A p ∧ res < 2 ^ w ∧
  (∀ p, A p = 1 → (P.get p).posTarget < 2 ^ w) ∧
  (∀ p, Z p = 1 → (P.get p).zeroTarget < 2 ^ w) ∧
  pcNext < 2 ^ w ∧ r0Next < 2 ^ w

/-! ### The equivalence -/

/-- The ordinary selector of the configuration `c`: instruction `p` is selected unless it is a
decrement whose register has run out. -/
private def ordFlag (P : Program 1) (c : Config 1) (p : Fin P.length) : ℕ :=
  if (P.get p).zeroBranch = 1 ∧ c.regs 0 = 0 then 0 else 1

/-- **The blockwise equivalence, for an arbitrary one-register program.** For a sequence of
fitting configurations, the encoded step relation holding at every index is exactly the existence
of selector families satisfying `BlockStep`.

Both directions are a case split on the selected instruction, with a decrement split again on
whether the register is zero. `n = 0` needs no separate treatment: both sides are vacuous. -/
theorem blockStep_iff (P : Program 1) (w n : ℕ) (cs : ℕ → Config 1)
    (hfit : ∀ i, FitsConfig w (cs i)) :
    (∀ i < n, EncodedStep P w (configCode w (cs i)) (configCode w (cs (i + 1)))) ↔
      ∃ A Z : ℕ → Fin P.length → ℕ, ∃ res : ℕ → ℕ, ∀ i < n,
        BlockStep P w (cs i).pc (cs (i + 1)).pc ((cs i).regs 0) ((cs (i + 1)).regs 0) (res i)
          (A i) (Z i) := by
  constructor
  · intro h
    refine ⟨fun i p => if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0,
      fun i p => if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0,
      fun i => (cs i).regs 0 - ∑ p : Fin P.length, (P.get p).loss *
        (if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0), ?_⟩
    intro i hi
    dsimp only
    have hstep := h i hi
    have hpc : (cs i).pc < P.length := by
      have := configField_zero_lt_of_encodedStep hstep
      rwa [field_configCode_zero (hfit i)] at this
    obtain ⟨hfits, hz⟩ := (encodedStep_iff (hfit i) hpc).mp hstep
    have hnext : cs (i + 1) = step P (cs i) :=
      configCode_injective (hfit (i + 1)) hfits hz
    set q : Fin P.length := ⟨(cs i).pc, hpc⟩ with hq
    have hget : step P (cs i) = (P.get q).exec (cs i).regs :=
      step_of_getElem? (by simp [hq])
    -- every sum collapses to the selected instruction
    have hsumA : ∀ f : Fin P.length → ℕ,
        ∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
          = f q * ordFlag P (cs i) q := by
      intro f
      have e : (fun p : Fin P.length =>
          f p * (if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0))
          = fun p : Fin P.length =>
            if (p : ℕ) = (cs i).pc then f p * ordFlag P (cs i) p else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, Nat.mul_zero]
      rw [show ∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
          = ∑ p : Fin P.length,
            (if (p : ℕ) = (cs i).pc then f p * ordFlag P (cs i) p else 0) from by rw [e],
        sum_indicator hpc]
    have hsumZ : ∀ f : Fin P.length → ℕ,
        ∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0)
          = f q * (1 - ordFlag P (cs i) q) := by
      intro f
      have e : (fun p : Fin P.length =>
          f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0))
          = fun p : Fin P.length =>
            if (p : ℕ) = (cs i).pc then f p * (1 - ordFlag P (cs i) p) else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, Nat.mul_zero]
      rw [show ∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0)
          = ∑ p : Fin P.length,
            (if (p : ℕ) = (cs i).pc then f p * (1 - ordFlag P (cs i) p) else 0) from by rw [e],
        sum_indicator hpc]
    have hsum1 : ∑ p : Fin P.length,
        ((if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
          + (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0)) = 1 := by
      have e : (fun p : Fin P.length =>
          (if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0))
          = fun p : Fin P.length => if (p : ℕ) = (cs i).pc then 1 else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hle : ordFlag P (cs i) p ≤ 1 := by unfold ordFlag; split <;> omega
          rw [if_pos hp, if_pos hp, if_pos hp]
          omega
        · rw [if_neg hp, if_neg hp, if_neg hp]
      rw [show ∑ p : Fin P.length,
          ((if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0))
          = ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then 1 else 0) from by rw [e]]
      simpa using sum_indicator hpc (fun _ => 1)
    have hsumPc : ∑ p : Fin P.length, (p : ℕ) *
        ((if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
          + (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0)) = (cs i).pc := by
      have e : (fun p : Fin P.length => (p : ℕ) *
          ((if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0)))
          = fun p : Fin P.length => if (p : ℕ) = (cs i).pc then (p : ℕ) else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hle : ordFlag P (cs i) p ≤ 1 := by unfold ordFlag; split <;> omega
          rw [if_pos hp, if_pos hp, if_pos hp,
            show ordFlag P (cs i) p + (1 - ordFlag P (cs i) p) = 1 from by omega, Nat.mul_one]
        · rw [if_neg hp, if_neg hp, if_neg hp, Nat.add_zero, Nat.mul_zero]
      rw [show ∑ p : Fin P.length, (p : ℕ) *
          ((if (p : ℕ) = (cs i).pc then ordFlag P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0))
          = ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then (p : ℕ) else 0) from by rw [e],
        sum_indicator hpc (fun p => (p : ℕ))]
    have hr : (cs i).regs 0 < 2 ^ w := (hfit i).2 0
    have hb0 : (cs (i + 1)).pc < 2 ^ w := (hfit (i + 1)).1
    have hb1 : (cs (i + 1)).regs 0 < 2 ^ w := (hfit (i + 1)).2 0
    rcases hinstr : (P.get q) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
    · -- an increment
      have hord : ordFlag P (cs i) q = 1 := by
        unfold ordFlag
        rw [hinstr]
        simp [Instr.zeroBranch]
      have hexec : cs (i + 1) = ⟨j, Function.update (cs i).regs 0 ((cs i).regs 0 + 1)⟩ := by
        rw [hnext, hget, hinstr, show r = 0 from Subsingleton.elim r 0]
        rfl
      have hpcn : (cs (i + 1)).pc = j := by rw [hexec]
      have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 + 1 := by rw [hexec]; simp
      refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by omega, by omega⟩ <;> (try dsimp only)
      · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).posTarget),
          hsumZ (fun p => (P.get p).zeroTarget), hord, hinstr]
        simp [Instr.posTarget, hpcn]
      · rw [hsumA (fun p => (P.get p).loss), hsumA (fun p => (P.get p).gain), hord, hinstr]
        simp [Instr.loss, Instr.gain]
        omega
      · intro p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hpq : p = q := Fin.ext hp
          rw [if_pos hp, hpq, hord]
          simp
        · simp [hp]
      · intro hzsum
        exfalso
        rw [show ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0)
            = 1 - ordFlag P (cs i) q from by
          simpa using sum_indicator hpc (fun p => 1 - ordFlag P (cs i) p)] at hzsum
        rw [hord] at hzsum
        omega
      · rw [hsumA (fun p => (P.get p).loss), hord, hinstr]
        simp [Instr.loss]
      · rw [hsumA (fun p => (P.get p).loss), hord, hinstr]
        simp [Instr.loss]
        omega
      · intro p hA
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hpq : p = q := Fin.ext hp
          rw [hpq, hinstr]
          simpa [Instr.posTarget, hpcn] using hb0
        · rw [if_neg hp] at hA; omega
      · intro p hZ
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hZ; omega
        · rw [if_neg hp] at hZ; omega
    · -- a decrement
      rcases eq_or_ne ((cs i).regs 0) 0 with hz0 | hz0
      · -- the zero branch
        have hord : ordFlag P (cs i) q = 0 := by
          unfold ordFlag
          rw [hinstr]
          simp [Instr.zeroBranch, hz0]
        have hexec : cs (i + 1) = ⟨jzero, (cs i).regs⟩ := by
          rw [hnext, hget, hinstr, show r = 0 from Subsingleton.elim r 0]
          simp only [Instr.exec]
          rw [if_pos hz0]
        have hpcn : (cs (i + 1)).pc = jzero := by rw [hexec]
        have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 := by rw [hexec]
        refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          by omega, by omega⟩ <;> (try dsimp only)
        · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).posTarget),
            hsumZ (fun p => (P.get p).zeroTarget), hord, hinstr]
          simp [Instr.zeroTarget, hpcn]
        · rw [hsumA (fun p => (P.get p).loss), hsumA (fun p => (P.get p).gain), hord]
          simp
          omega
        · intro p
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [if_pos hp, hpq, hord, hinstr]
            simp [Instr.zeroBranch]
          · simp [hp]
        · intro _; exact hz0
        · rw [hsumA (fun p => (P.get p).loss), hord]
          simp
        · rw [hsumA (fun p => (P.get p).loss), hord]
          simp
          omega
        · intro p hA
          by_cases hp : (p : ℕ) = (cs i).pc
          · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hA; omega
          · rw [if_neg hp] at hA; omega
        · intro p hZ
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [hpq, hinstr]
            simpa [Instr.zeroTarget, hpcn] using hb0
          · rw [if_neg hp] at hZ; omega
      · -- the positive branch
        have hord : ordFlag P (cs i) q = 1 := by
          unfold ordFlag
          rw [hinstr]
          simp [Instr.zeroBranch, hz0]
        have hexec : cs (i + 1)
            = ⟨jpos, Function.update (cs i).regs 0 ((cs i).regs 0 - 1)⟩ := by
          rw [hnext, hget, hinstr, show r = 0 from Subsingleton.elim r 0]
          simp only [Instr.exec]
          rw [if_neg hz0]
        have hpcn : (cs (i + 1)).pc = jpos := by rw [hexec]
        have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 - 1 := by rw [hexec]; simp
        have hpos : 0 < (cs i).regs 0 := Nat.pos_of_ne_zero hz0
        refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          by omega, by omega⟩ <;> (try dsimp only)
        · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).posTarget),
            hsumZ (fun p => (P.get p).zeroTarget), hord, hinstr]
          simp [Instr.posTarget, hpcn]
        · rw [hsumA (fun p => (P.get p).loss), hsumA (fun p => (P.get p).gain), hord, hinstr]
          simp [Instr.loss, Instr.gain]
          omega
        · intro p
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [if_pos hp, hpq, hord, hinstr]
            simp [Instr.zeroBranch]
          · simp [hp]
        · intro hzsum
          exfalso
          rw [show ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then 1 - ordFlag P (cs i) p else 0)
              = 1 - ordFlag P (cs i) q from by
            simpa using sum_indicator hpc (fun p => 1 - ordFlag P (cs i) p)] at hzsum
          rw [hord] at hzsum
          omega
        · rw [hsumA (fun p => (P.get p).loss), hord, hinstr]
          simp only [Instr.loss, Nat.mul_one]
          omega
        · rw [hsumA (fun p => (P.get p).loss), hord, hinstr]
          simp [Instr.loss]
          omega
        · intro p hA
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [hpq, hinstr]
            simpa [Instr.posTarget, hpcn] using hb0
          · rw [if_neg hp] at hA; omega
        · intro p hZ
          by_cases hp : (p : ℕ) = (cs i).pc
          · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hZ; omega
          · rw [if_neg hp] at hZ; omega
  · rintro ⟨A, Z, res, h⟩ i hi
    obtain ⟨hone, hpcH, hpcN, hupd, hzb, hzero, hres, hresb, htA, htZ, hpb, hrb⟩ := h i hi
    obtain ⟨q, hq1, hq0⟩ := exists_unique_of_sum_eq_one hone
    have hcollapse : ∀ f : Fin P.length → ℕ,
        ∑ p : Fin P.length, f p * (A i p + Z i p) = f q * (A i q + Z i q) :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show A i p + Z i p = 0 from by omega, Nat.mul_zero]
    have hpcq : (cs i).pc = (q : ℕ) := by
      rw [hpcH, show ∑ p : Fin P.length, (p : ℕ) * (A i p + Z i p)
        = (q : ℕ) * (A i q + Z i q) from hcollapse _, hq1, mul_one]
    have hpcLt : (cs i).pc < P.length := by rw [hpcq]; exact q.isLt
    have hAZ : (A i q = 1 ∧ Z i q = 0) ∨ (A i q = 0 ∧ Z i q = 1) := by omega
    have hsumA : ∀ f : Fin P.length → ℕ, ∑ p : Fin P.length, f p * A i p = f q * A i q :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show A i p = 0 from by omega]; ring
    have hsumZ : ∀ f : Fin P.length → ℕ, ∑ p : Fin P.length, f p * Z i p = f q * Z i q :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show Z i p = 0 from by omega]; ring
    have hsumZ1 : ∑ p : Fin P.length, Z i p = Z i q :=
      sum_eq_of_vanishing fun p hp => by have := hq0 p hp; omega
    have hget : step P (cs i) = (P.get ⟨(cs i).pc, hpcLt⟩).exec (cs i).regs :=
      step_of_getElem? (by simp)
    have hqe : (⟨(cs i).pc, hpcLt⟩ : Fin P.length) = q := Fin.ext hpcq
    rw [hqe] at hget
    have hnext : cs (i + 1) = step P (cs i) := by
      rw [hget]
      rcases hinstr : (P.get q) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
      · -- an increment: the zero selector is forced off
        have hZq : Z i q = 0 := by
          have := hzb q
          rw [hinstr] at this
          simpa [Instr.zeroBranch] using this
        have hAq : A i q = 1 := by omega
        have hpcn : (cs (i + 1)).pc = j := by
          rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).posTarget),
            hsumZ (fun p => (P.get p).zeroTarget), hAq, hZq, hinstr]
          simp [Instr.posTarget]
        have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 + 1 := by
          rw [hsumA (fun p => (P.get p).loss), hsumA (fun p => (P.get p).gain), hAq, hinstr]
            at hupd
          simp [Instr.loss, Instr.gain] at hupd
          omega
        rw [show r = 0 from Subsingleton.elim r 0]
        simp only [Instr.exec]
        exact config_one_ext (by simpa using hpcn) (by simpa using hrn)
      · rcases hAZ with ⟨hAq, hZq⟩ | ⟨hAq, hZq⟩
        · -- the positive branch
          have hloss : ∑ p : Fin P.length, (P.get p).loss * A i p = 1 := by
            rw [hsumA (fun p => (P.get p).loss), hAq, hinstr]
            simp [Instr.loss]
          have hpos : 0 < (cs i).regs 0 := by omega
          have hpcn : (cs (i + 1)).pc = jpos := by
            rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).posTarget),
              hsumZ (fun p => (P.get p).zeroTarget), hAq, hZq, hinstr]
            simp [Instr.posTarget]
          have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 - 1 := by
            rw [hloss, hsumA (fun p => (P.get p).gain), hAq, hinstr] at hupd
            simp [Instr.gain] at hupd
            omega
          rw [show r = 0 from Subsingleton.elim r 0]
          simp only [Instr.exec]
          rw [if_neg (by omega : ¬ (cs i).regs 0 = 0)]
          exact config_one_ext (by simpa using hpcn) (by simpa using hrn)
        · -- the zero branch
          have hr0 : (cs i).regs 0 = 0 := hzero (by rw [hsumZ1]; exact hZq)
          have hpcn : (cs (i + 1)).pc = jzero := by
            rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).posTarget),
              hsumZ (fun p => (P.get p).zeroTarget), hAq, hZq, hinstr]
            simp [Instr.zeroTarget]
          have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 := by
            rw [hsumA (fun p => (P.get p).loss), hsumA (fun p => (P.get p).gain), hAq] at hupd
            simp at hupd
            omega
          rw [show r = 0 from Subsingleton.elim r 0]
          simp only [Instr.exec]
          rw [if_pos hr0]
          exact config_one_ext (by simpa using hpcn) (by simpa using hrn)
    have hfits : FitsConfig w (step P (cs i)) := by rw [← hnext]; exact hfit (i + 1)
    have := encodedStep_configCode (hfit i) hfits hpcLt
    rwa [← hnext] at this

end RegisterMachine

end Hilbert10
