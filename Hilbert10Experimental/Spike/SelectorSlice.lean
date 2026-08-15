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

The blockwise equivalence is proved. `SliceGlobalConditions` states the packed-level conditions,
but the theorem relating them to `EncodedStep` is **not** proved here:

```
P.length < 2 ^ w ∧ IsBinarySubmask R (guardMask (w * 2) (n + 1)) ∧
  (∀ i < n, EncodedStep sliceP w (block R i) (block R (i + 1)))
↔ ∃ Xpc X0 S0 S1p S1z S2 Res Zres,
    SliceGlobalConditions w n R Xpc X0 S0 S1p S1z S2 Res Zres
```

Completeness decodes `R`, applies `sliceStep_iff`, and packs the result; soundness reads the lane
masks as per-block bounds, recovers `SliceStep` blockwise from the global identities, and applies
`sliceStep_iff` in reverse. Two cases need explicit attention: `n = 0`, where the selector and
residual packings must exist with no semantic input; and small `w` with `S₂ = 0`, where the
target disjunction has to take its zero-selector branch, while `S₂ ≠ 0` must recover
`1000 < 2 ^ w`. Only after that is `ExpDioph` finite plumbing.

Setting the equivalence up already found one missing condition — see
`SliceGlobalConditions` on why the program-length bound has to be listed — so no claim is made
here that the rest is mechanical. No further mathematical ingredient is *currently identified*,
which is a weaker statement, and the global equivalence is exactly the test that could identify
one.
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

/-! ### The global conditions

Layer 1 for the packed level: the fixed program's global selector conditions, written down so
that the remaining work is proof rather than design.

Everything is packed at the outer base `B = 2 ^ (w * 2 + 1)`, which for this one-register program
is the same base `R` uses. Lanes carry `n + 1` blocks, selectors and the residual carry `n`.
`laneMask` and `bitMask` are the two constant packings: `w`-bit fields and single bits. -/

/-- The `w`-bit data mask over `t` blocks. -/
def laneMask (w t : ℕ) : ℕ := (2 ^ w - 1) * geom (2 ^ (w * 2 + 1)) t

/-- The one-bit-per-block mask over `t` blocks. -/
def bitMask (w t : ℕ) : ℕ := geom (2 ^ (w * 2 + 1)) t

/-- **The global selector conditions for `sliceP`.**

Read in order: the program length fits; the two lanes are `w`-bit packings; they reassemble `R`;
the four selectors are bit packings partitioning every block; the program counter agrees with the
selector and jumps to the selected target; the register update is subtraction-free; the
decrement's zero branch forces the register to vanish and its positive branch forces the register
to be at least one, each needing its own masked witness; and each selected target fits.

Fourteen conditions, and the count depends only on `sliceP`.

The zero branch is an *equation*, not a submask condition. Reading
`IsBinarySubmask (S1z * (2 ^ w - 1)) (M - X0 % Bⁿ)` blockwise would need
`IsBinarySubmask a b → a ≤ b`, a bit-level fact this development does not have and should not
need. Blockwise, `x0 i + s1z i * (2 ^ w - 1) + z i = 2 ^ w - 1` forces `x0 i = 0` when
`s1z i = 1`, and is satisfiable with `z i = 2 ^ w - 1 - x0 i` when `s1z i = 0` — the same content
subtraction-free, and symmetric with how the positive branch was already stated.

The program-length bound is not decoration and is not implied by the rest. At `n = 0` every
selector is forced to `0` by `bitMask w 0 = 0`, so all three target disjunctions take their
zero-selector branch and nothing else mentions `2 ^ w` from below: `w = 1`, `R = 0` satisfies
every other condition while `sliceP.length = 3 < 2` is false. It has to be re-exported here
because `Aggregation` bundles it on the other side. -/
def SliceGlobalConditions (w n R Xpc X0 S0 S1p S1z S2 Res Zres : ℕ) : Prop :=
  sliceP.length < 2 ^ w ∧
  Nat.IsBinarySubmask Xpc (laneMask w (n + 1)) ∧
  Nat.IsBinarySubmask X0 (laneMask w (n + 1)) ∧
  R = Xpc + 2 ^ w * X0 ∧
  Nat.IsBinarySubmask S0 (bitMask w n) ∧ Nat.IsBinarySubmask S1p (bitMask w n) ∧
    Nat.IsBinarySubmask S1z (bitMask w n) ∧ Nat.IsBinarySubmask S2 (bitMask w n) ∧
  S0 + S1p + S1z + S2 = bitMask w n ∧
  Xpc % (2 ^ (w * 2 + 1)) ^ n = S1p + S1z + 2 * S2 ∧
  Xpc / 2 ^ (w * 2 + 1) = S0 + 2 * S1z + 1000 * S2 ∧
  X0 / 2 ^ (w * 2 + 1) + S1p = X0 % (2 ^ (w * 2 + 1)) ^ n + S0 + S2 ∧
  (X0 % (2 ^ (w * 2 + 1)) ^ n + S1z * (2 ^ w - 1) + Zres = laneMask w n ∧
    Nat.IsBinarySubmask Zres (laneMask w n)) ∧
  (X0 % (2 ^ (w * 2 + 1)) ^ n = Res + S1p ∧ Nat.IsBinarySubmask Res (laneMask w n)) ∧
  (S0 = 0 ∨ 1 < 2 ^ w) ∧ (S1z = 0 ∨ 2 < 2 ^ w) ∧ (S2 = 0 ∨ 1000 < 2 ^ w)

/-! ### Soundness, in packages

Rather than destructing thirteen conditions at once, each group is turned into its pointwise
consequence separately. -/

theorem two_le_of_sliceP_length_lt {w : ℕ} (hlen : sliceP.length < 2 ^ w) : 2 ≤ w := by
  by_contra hc
  simp only [not_le] at hc
  have h : (2 : ℕ) ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [sliceP, List.length_cons, List.length_nil] at hlen
  omega

theorem four_lt_outer {w : ℕ} (hw : 2 ≤ w) : 4 < 2 ^ (w * 2 + 1) := by
  have h : (2 : ℕ) ^ 5 ≤ 2 ^ (w * 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h
  omega

theorem bitMask_eq (w t : ℕ) : bitMask w t = (2 ^ 1 - 1) * geom (2 ^ (w * 2 + 1)) t := by
  simp [bitMask]

/-- A bit-masked packing has `0`/`1` blocks and is the packing of them. -/
theorem selector_norm {w t S : ℕ} (h : Nat.IsBinarySubmask S (bitMask w t)) :
    S = fieldsCode (w * 2 + 1) (fun i : Fin t => configField (w * 2 + 1) S i) ∧
      ∀ i : Fin t, configField (w * 2 + 1) S i < 2 := by
  have := packed_eq_fieldsCode (v := 1) (W := w * 2 + 1) (by omega) (by rwa [← bitMask_eq])
  simpa using this

/-- A lane-masked packing has `w`-bit blocks and is the packing of them. -/
theorem lane_norm {w t X : ℕ} (h : Nat.IsBinarySubmask X (laneMask w t)) :
    X = fieldsCode (w * 2 + 1) (fun i : Fin t => configField (w * 2 + 1) X i) ∧
      ∀ i : Fin t, configField (w * 2 + 1) X i < 2 ^ w :=
  packed_eq_fieldsCode (v := w) (W := w * 2 + 1) (by omega) h

/-- **Package 3: the selectors are one-hot in every block.** This is the first place the
program-length bound is used: without `2 ≤ w` the four-term sum could overflow a block and the
global partition would not be the pointwise one. -/
theorem slice_one_hot {w n : ℕ} (hlen : sliceP.length < 2 ^ w) {S0 S1p S1z S2 : ℕ}
    (h0 : Nat.IsBinarySubmask S0 (bitMask w n)) (h1 : Nat.IsBinarySubmask S1p (bitMask w n))
    (h2 : Nat.IsBinarySubmask S1z (bitMask w n)) (h3 : Nat.IsBinarySubmask S2 (bitMask w n))
    (hsum : S0 + S1p + S1z + S2 = bitMask w n) (i : Fin n) :
    configField (w * 2 + 1) S0 i + configField (w * 2 + 1) S1p i
      + configField (w * 2 + 1) S1z i + configField (w * 2 + 1) S2 i = 1 := by
  obtain ⟨e0, b0⟩ := selector_norm h0
  obtain ⟨e1, b1⟩ := selector_norm h1
  obtain ⟨e2, b2⟩ := selector_norm h2
  obtain ⟨e3, b3⟩ := selector_norm h3
  have hfour : (4 : ℕ) < 2 ^ (w * 2 + 1) := four_lt_outer (two_le_of_sliceP_length_lt hlen)
  have hbit : bitMask w n = fieldsCode (w * 2 + 1) (fun _ : Fin n => 1) := by
    rw [fieldsCode_const]; simp [bitMask]
  have hkey : fieldsCode (w * 2 + 1)
      (fun i : Fin n => configField (w * 2 + 1) S0 i + configField (w * 2 + 1) S1p i
        + configField (w * 2 + 1) S1z i + configField (w * 2 + 1) S2 i)
      = fieldsCode (w * 2 + 1) (fun _ : Fin n => 1) := by
    rw [← hbit, ← hsum]
    conv_rhs => rw [e0, e1, e2, e3]
    rw [fieldsCode_add, fieldsCode_add, fieldsCode_add]
  exact congrFun (fieldsCode_injective
    (fun j => by have := b0 j; have := b1 j; have := b2 j; have := b3 j; omega)
    (fun _ => by omega) hkey) i

/-- **Package 5: a selected constant fits.** The zero-selector branch of each target disjunction
is discharged by the block of `0` being `0`; no packing argument is needed. -/
theorem slice_target {w S c : ℕ} (hd : S = 0 ∨ c < 2 ^ w) {i : ℕ}
    (hs : configField (w * 2 + 1) S i = 1) : c < 2 ^ w := by
  rcases hd with rfl | h
  · simp [configField] at hs
  · exact h

end RegisterMachine

end Hilbert10
