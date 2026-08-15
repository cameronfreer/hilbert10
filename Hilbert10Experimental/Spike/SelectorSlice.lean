/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.Spike.SelectorMask

/-!
# Acceptance slice for the selector encoding: the blockwise layer

#49, phase 2. `Spike/SelectorMask` proves that global identities between packed numbers reduce
to identities between their blocks. What it does not show is that the *blockwise* selector
conditions say the same thing as `EncodedStep`. This file does, for a fixed program.

## The program

```lean
def sliceP : Program 1 := [.inc 0 1, .dec 0 0 2, .inc 0 1000]
```

One register, so two lanes. Instruction `0` is an increment. Instruction `1` is a decrement with
both branches live — `jpos = 0` loops back, `jzero = 2` leaves the loop. Instruction `2` carries
an oversized target.

Instruction `2` is *not* statically unreachable: a trace that reaches it must prove
`1000 < 2 ^ w`, and only a trace stopping earlier has `s₂ = 0` throughout. That is a sharper test
of the conditional bound than an unreachable branch would be, because both regimes are live and
the encoding has to distinguish them.

## Where the target bounds actually bite

Blockwise, `s₂ i = 1 → 1000 < 2 ^ w` is *implied* by `pcNext < 2 ^ w`, since `pcNext` **is** the
target. They are still listed as separate conditions, because globally the implication runs the
other way: `pcNext < 2 ^ w` is a consequence of the lane mask, and reading the lane mask blockwise
off the global jump equation is exactly what the target bound licenses. Dropping them here would
therefore look harmless and break the layer above.

## Scope

Blockwise only. Globalising these conditions to packed numbers, and representing the result, are
the remaining layers.
-/

namespace Hilbert10

namespace RegisterMachine

/-- The slice program. -/
def sliceP : Program 1 := [.inc 0 1, .dec 0 0 2, .inc 0 1000]

@[simp] theorem sliceP_length : sliceP.length = 3 := rfl

theorem step_sliceP_of_pc_zero {c : Config 1} (h : c.pc = 0) :
    step sliceP c = ⟨1, Function.update c.regs 0 (c.regs 0 + 1)⟩ := by
  simp [step, h, sliceP, Instr.exec]

theorem step_sliceP_of_pc_one {c : Config 1} (h : c.pc = 1) :
    step sliceP c =
      if c.regs 0 = 0 then ⟨2, c.regs⟩ else ⟨0, Function.update c.regs 0 (c.regs 0 - 1)⟩ := by
  simp [step, h, sliceP, Instr.exec]

theorem step_sliceP_of_pc_two {c : Config 1} (h : c.pc = 2) :
    step sliceP c = ⟨1000, Function.update c.regs 0 (c.regs 0 + 1)⟩ := by
  simp [step, h, sliceP, Instr.exec]

/-- A one-register configuration is determined by two numbers. -/
theorem config_one_ext {c₁ c₂ : Config 1} (hpc : c₁.pc = c₂.pc) (hr : c₁.regs 0 = c₂.regs 0) :
    c₁ = c₂ := by
  obtain ⟨p₁, r₁⟩ := c₁
  obtain ⟨p₂, r₂⟩ := c₂
  simp only [Config.mk.injEq]
  exact ⟨hpc, funext fun i => by rw [Subsingleton.elim i 0]; exact hr⟩

/-- **The blockwise selector conditions at one step.**

`s0`, `s1p`, `s1z`, `s2` select instruction `0`, instruction `1`'s positive branch, instruction
`1`'s zero branch, and instruction `2`. `res` is the positive-branch residual, whose bound is
what forces `r0Here ≥ 1` when `s1p = 1`. -/
def SliceStep (w pcHere pcNext r0Here r0Next s0 s1p s1z s2 res : ℕ) : Prop :=
  s0 + s1p + s1z + s2 = 1 ∧
  pcHere = s1p + s1z + 2 * s2 ∧
  pcNext = s0 + 2 * s1z + 1000 * s2 ∧
  r0Next + s1p = r0Here + s0 + s2 ∧
  (s1z = 1 → r0Here = 0) ∧
  r0Here = res + s1p ∧ res < 2 ^ w ∧
  (s0 = 1 → 1 < 2 ^ w) ∧ (s1z = 1 → 2 < 2 ^ w) ∧ (s2 = 1 → 1000 < 2 ^ w) ∧
  pcNext < 2 ^ w ∧ r0Next < 2 ^ w

/-- **The slice, blockwise.** For a sequence of fitting configurations, the encoded step relation
holding at every index is exactly the existence of selector sequences satisfying `SliceStep`.

Both directions are a case split on the program counter, with the decrement split again on
whether the register is zero — the four cases the slice is meant to exercise. `n = 0` needs no
separate treatment: both sides are vacuous. -/
theorem sliceStep_iff (w n : ℕ) (cs : ℕ → Config 1) (hfit : ∀ i, FitsConfig w (cs i)) :
    (∀ i < n, EncodedStep sliceP w (configCode w (cs i)) (configCode w (cs (i + 1)))) ↔
      ∃ s0 s1p s1z s2 res : ℕ → ℕ, ∀ i < n,
        SliceStep w (cs i).pc (cs (i + 1)).pc ((cs i).regs 0) ((cs (i + 1)).regs 0)
          (s0 i) (s1p i) (s1z i) (s2 i) (res i) := by
  constructor
  · intro h
    refine ⟨fun i => if (cs i).pc = 0 then 1 else 0,
      fun i => if (cs i).pc = 1 ∧ (cs i).regs 0 ≠ 0 then 1 else 0,
      fun i => if (cs i).pc = 1 ∧ (cs i).regs 0 = 0 then 1 else 0,
      fun i => if (cs i).pc = 2 then 1 else 0,
      fun i => (cs i).regs 0 - (if (cs i).pc = 1 ∧ (cs i).regs 0 ≠ 0 then 1 else 0), ?_⟩
    intro i hi
    have hstep := h i hi
    have hpc : (cs i).pc < sliceP.length := by
      have := configField_zero_lt_of_encodedStep hstep
      rwa [field_configCode_zero (hfit i)] at this
    obtain ⟨hfits, hz⟩ := (encodedStep_iff (hfit i) hpc).mp hstep
    have hnext : cs (i + 1) = step sliceP (cs i) :=
      configCode_injective (hfit (i + 1)) hfits hz
    have hr : (cs i).regs 0 < 2 ^ w := (hfit i).2 0
    have hpc3 : (cs i).pc = 0 ∨ (cs i).pc = 1 ∨ (cs i).pc = 2 := by
      rw [sliceP_length] at hpc; omega
    rcases hpc3 with hp | hp | hp
    · -- instruction 0: the increment
      rw [step_sliceP_of_pc_zero hp] at hnext
      have hpcn : (cs (i + 1)).pc = 1 := by rw [hnext]
      have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 + 1 := by rw [hnext]; simp
      have hb0 : (cs (i + 1)).pc < 2 ^ w := (hfit (i + 1)).1
      have hb2 : (cs (i + 1)).regs 0 < 2 ^ w := (hfit (i + 1)).2 0
      have e0 : (if (cs i).pc = 0 then 1 else 0) = 1 := by simp [hp]
      have e1 : (if (cs i).pc = 1 ∧ (cs i).regs 0 ≠ 0 then 1 else 0) = 0 := by simp [hp]
      have e2 : (if (cs i).pc = 1 ∧ (cs i).regs 0 = 0 then 1 else 0) = 0 := by simp [hp]
      have e3 : (if (cs i).pc = 2 then 1 else 0) = 0 := by simp [hp]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (try dsimp only) <;> (try simp only [e0, e1, e2, e3]) <;> (try simp only [hp]) <;> omega
    · rcases eq_or_ne ((cs i).regs 0) 0 with hz0 | hz0
      · -- instruction 1, zero branch
        rw [step_sliceP_of_pc_one hp, if_pos hz0] at hnext
        have hpcn : (cs (i + 1)).pc = 2 := by rw [hnext]
        have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 := by rw [hnext]
        have hb0 : (cs (i + 1)).pc < 2 ^ w := (hfit (i + 1)).1
        have hb2 : (cs (i + 1)).regs 0 < 2 ^ w := (hfit (i + 1)).2 0
        have e0 : (if (cs i).pc = 0 then 1 else 0) = 0 := by simp [hp]
        have e1 : (if (cs i).pc = 1 ∧ (cs i).regs 0 ≠ 0 then 1 else 0) = 0 := by simp [hp, hz0]
        have e2 : (if (cs i).pc = 1 ∧ (cs i).regs 0 = 0 then 1 else 0) = 1 := by simp [hp, hz0]
        have e3 : (if (cs i).pc = 2 then 1 else 0) = 0 := by simp [hp]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (try dsimp only) <;> (try simp only [e0, e1, e2, e3]) <;> (try simp only [hp]) <;> omega
      · -- instruction 1, positive branch
        rw [step_sliceP_of_pc_one hp, if_neg hz0] at hnext
        have hpcn : (cs (i + 1)).pc = 0 := by rw [hnext]
        have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 - 1 := by rw [hnext]; simp
        have hb0 : (cs (i + 1)).pc < 2 ^ w := (hfit (i + 1)).1
        have hb2 : (cs (i + 1)).regs 0 < 2 ^ w := (hfit (i + 1)).2 0
        have hz1 : 0 < (cs i).regs 0 := Nat.pos_of_ne_zero hz0
        have e0 : (if (cs i).pc = 0 then 1 else 0) = 0 := by simp [hp]
        have e1 : (if (cs i).pc = 1 ∧ (cs i).regs 0 ≠ 0 then 1 else 0) = 1 := by simp [hp, hz0]
        have e2 : (if (cs i).pc = 1 ∧ (cs i).regs 0 = 0 then 1 else 0) = 0 := by simp [hp, hz0]
        have e3 : (if (cs i).pc = 2 then 1 else 0) = 0 := by simp [hp]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (try dsimp only) <;> (try simp only [e0, e1, e2, e3]) <;> (try simp only [hp]) <;> omega
    · -- instruction 2: the oversized target
      rw [step_sliceP_of_pc_two hp] at hnext
      have hpcn : (cs (i + 1)).pc = 1000 := by rw [hnext]
      have hrn : (cs (i + 1)).regs 0 = (cs i).regs 0 + 1 := by rw [hnext]; simp
      have hb0 : (cs (i + 1)).pc < 2 ^ w := (hfit (i + 1)).1
      have hb2 : (cs (i + 1)).regs 0 < 2 ^ w := (hfit (i + 1)).2 0
      have e0 : (if (cs i).pc = 0 then 1 else 0) = 0 := by simp [hp]
      have e1 : (if (cs i).pc = 1 ∧ (cs i).regs 0 ≠ 0 then 1 else 0) = 0 := by simp [hp]
      have e2 : (if (cs i).pc = 1 ∧ (cs i).regs 0 = 0 then 1 else 0) = 0 := by simp [hp]
      have e3 : (if (cs i).pc = 2 then 1 else 0) = 1 := by simp [hp]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (try dsimp only) <;> (try simp only [e0, e1, e2, e3]) <;> (try simp only [hp]) <;> omega
  · rintro ⟨s0, s1p, s1z, s2, res, h⟩ i hi
    obtain ⟨hsum, hpcH, hpcN, hupd, hzero, hres, hresb, ht0, ht1, ht2, hpb, hrb⟩ := h i hi
    have hcase : (s0 i = 1 ∧ s1p i = 0 ∧ s1z i = 0 ∧ s2 i = 0) ∨
        (s1p i = 1 ∧ s0 i = 0 ∧ s1z i = 0 ∧ s2 i = 0) ∨
        (s1z i = 1 ∧ s0 i = 0 ∧ s1p i = 0 ∧ s2 i = 0) ∨
        (s2 i = 1 ∧ s0 i = 0 ∧ s1p i = 0 ∧ s1z i = 0) := by omega
    have hnext : cs (i + 1) = step sliceP (cs i) := by
      rcases hcase with ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩
      · rw [step_sliceP_of_pc_zero (by omega)]
        exact config_one_ext (by simp; omega) (by simp; omega)
      · rw [step_sliceP_of_pc_one (by omega), if_neg (by omega)]
        exact config_one_ext (by simp; omega) (by simp; omega)
      · rw [step_sliceP_of_pc_one (by omega), if_pos (by omega)]
        exact config_one_ext (by simp; omega) (by simp; omega)
      · rw [step_sliceP_of_pc_two (by omega)]
        exact config_one_ext (by simp; omega) (by simp; omega)
    have hpc : (cs i).pc < sliceP.length := by rw [sliceP_length]; omega
    have hfits : FitsConfig w (step sliceP (cs i)) := by
      rw [← hnext]; exact hfit (i + 1)
    have := encodedStep_configCode (hfit i) hfits hpc
    rwa [← hnext] at this

end RegisterMachine

end Hilbert10
