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

Both layers are proved. `sliceStep_iff` is the blockwise equivalence, and `sliceGlobal_iff` is
the packed one:

```
P.length < 2 ^ w ∧ IsBinarySubmask R (guardMask (w * 2) (n + 1)) ∧
  (∀ i < n, EncodedStep sliceP w (block R i) (block R (i + 1)))
↔ ∃ Xpc X0 S0 S1p S1z S2 Res Zres,
    SliceGlobalConditions w n R Xpc X0 S0 S1p S1z S2 Res Zres
```

Completeness decodes `R`, applies `sliceStep_iff`, and packs the result; soundness reads the lane
masks as per-block bounds, recovers `SliceStep` blockwise from the global identities, and applies
`sliceStep_iff` in reverse. The right-hand side has no bounded universal quantifier, so for this
program the `∀ i < n` is eliminated outright rather than reduced to a smaller one.

Setting the equivalence up found one missing condition — see `SliceGlobalConditions` on why the
program-length bound has to be listed — and proving it found no further one. What the slice
establishes is that the selector vocabulary is sufficient for a program exercising an increment,
both branches of a decrement, and an oversized jump target; it is not a proof for arbitrary
programs, which is what `Aggregation` in `AcceptsDioph` still asks for.

`Spike/SelectorSliceDioph` makes `SliceGlobalConditions` exponential Diophantine, which carries
this program to the endpoint of #48.
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

/-- With one register there are exactly two fields, so the code is the two lanes. -/
theorem configCode_one (w : ℕ) (c : Config 1) : configCode w c = c.pc + 2 ^ w * c.regs 0 := by
  simp [configCode, fieldsCode]

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

/-- The carry bound the zero-branch equation needs: three `w`-bit quantities, one of them scaled
by a selector, still fit in one block. `2 ≤ w` comes from the program-length condition. -/
theorem zero_branch_carry {w x s z : ℕ} (hw : 2 ≤ w) (hx : x < 2 ^ w) (hs : s ≤ 1)
    (hz : z < 2 ^ w) : x + s * (2 ^ w - 1) + z < 2 ^ (w * 2 + 1) := by
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    have h : (2 : ℕ) ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    norm_num at h
    omega
  have hsq : 2 ^ w * 2 ^ w ≤ 2 ^ (w * 2 + 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 3 * 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ (by omega)
  have hsb : s * (2 ^ w - 1) ≤ 2 ^ w - 1 := by
    calc s * (2 ^ w - 1) ≤ 1 * (2 ^ w - 1) := Nat.mul_le_mul_right _ hs
      _ = 2 ^ w - 1 := one_mul _
  omega

/-- **Package 4, the shared core.** A lane packing equal to three scaled selector packings is
that equation in every block. Both the program-counter agreement and the jump are instances;
so is the zero-branch equation, with the constant lane on the other side. -/
theorem selector_eq_blockwise {W n : ℕ} {f : Fin n → ℕ} {a b c : ℕ} {g h k : Fin n → ℕ}
    (hf : ∀ i, f i < 2 ^ W) (hbd : ∀ i, a * g i + b * h i + c * k i < 2 ^ W)
    (heq : fieldsCode W f = a * fieldsCode W g + b * fieldsCode W h + c * fieldsCode W k)
    (i : Fin n) : f i = a * g i + b * h i + c * k i := by
  rw [fieldsCode_three] at heq
  exact congrFun (fieldsCode_injective hf hbd heq) i

/-! ### Soundness -/

/-- **Soundness of the global system.** -/
theorem sliceGlobal_sound {w n R Xpc X0 S0 S1p S1z S2 Res Zres : ℕ}
    (h : SliceGlobalConditions w n R Xpc X0 S0 S1p S1z S2 Res Zres) :
    sliceP.length < 2 ^ w ∧
      Nat.IsBinarySubmask R (guardMask (w * 2) (n + 1)) ∧
      ∀ i < n, EncodedStep sliceP w (configField (w * 2 + 1) R i)
        (configField (w * 2 + 1) R (i + 1)) := by
  obtain ⟨hlen, hmpc, hm0, hR, hs0, hs1p, hs1z, hs2, hsum, hpcEq, hjump, hupd,
    ⟨hzeq, hzm⟩, ⟨hres, hresm⟩, ht0, ht1, ht2⟩ := h
  have hw2 : 2 ≤ w := two_le_of_sliceP_length_lt hlen
  obtain ⟨epc, bpc⟩ := lane_norm hmpc
  obtain ⟨e0, b0⟩ := lane_norm hm0
  obtain ⟨f0, c0⟩ := selector_norm hs0
  obtain ⟨f1p, c1p⟩ := selector_norm hs1p
  obtain ⟨f1z, c1z⟩ := selector_norm hs1z
  obtain ⟨f2, c2⟩ := selector_norm hs2
  obtain ⟨eres, bres⟩ := lane_norm hresm
  obtain ⟨ez, bz⟩ := lane_norm hzm
  have hpow : (2 : ℕ) ^ w * 2 ^ w = 2 ^ (w * 2) := by rw [← pow_add]; ring_nf
  have hppos : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
  have hmul : 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ (w * 2) := by
    have hr : 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * ((2 ^ w - 1) + 1) := by ring
    rw [hr, show (2 : ℕ) ^ w - 1 + 1 = 2 ^ w from by omega, hpow]
  have hlt : (2 : ℕ) ^ (w * 2) < 2 ^ (w * 2 + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- the two lanes reassemble `R` blockwise
  have hblk : ∀ i : Fin (n + 1), configField (w * 2 + 1) R i
      = configField (w * 2 + 1) Xpc i + 2 ^ w * configField (w * 2 + 1) X0 i := by
    have hbd : ∀ i : Fin (n + 1),
        configField (w * 2 + 1) Xpc i + 2 ^ w * configField (w * 2 + 1) X0 i < 2 ^ (w * 2 + 1) := by
      intro i
      have h1 := bpc i
      have h2 := b0 i
      have : 2 ^ w * configField (w * 2 + 1) X0 i ≤ 2 ^ w * (2 ^ w - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    intro i
    have hRe : R = fieldsCode (w * 2 + 1)
        (fun j : Fin (n + 1) => configField (w * 2 + 1) Xpc j
          + 2 ^ w * configField (w * 2 + 1) X0 j) := by
      rw [hR]
      conv_lhs => rw [epc, e0]
      rw [fieldsCode_smul, fieldsCode_add]
    rw [hRe, field_fieldsCode hbd i]
  have hRblk : ∀ i : Fin (n + 1), configField (w * 2 + 1) R i < 2 ^ (w * 2) := by
    intro i
    have h1 := bpc i
    have h2 := b0 i
    have h3 : 2 ^ w * configField (w * 2 + 1) X0 i ≤ 2 ^ w * (2 ^ w - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hblk i]; omega
  have hRlt : R < (2 ^ (w * 2 + 1)) ^ (n + 1) := by
    rw [hR]
    conv_lhs => rw [epc, e0]
    rw [fieldsCode_smul, fieldsCode_add]
    exact fieldsCode_lt fun j => by
      have h1 := bpc j
      have h2 := b0 j
      have h3 : 2 ^ w * configField (w * 2 + 1) X0 j ≤ 2 ^ w * (2 ^ w - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  refine ⟨hlen, isBinarySubmask_guardMask_iff.mpr ⟨hRlt, fun i hi => hRblk ⟨i, hi⟩⟩, ?_⟩
  -- decode and hand over to the blockwise slice
  set cs : ℕ → Config 1 := fun i => decodeConfig w (configField (w * 2 + 1) R i) with hcs
  have hcode : ∀ i : Fin (n + 1), configCode w (cs i) = configField (w * 2 + 1) R i := by
    intro i
    exact configCode_decodeConfig (by simpa using hRblk i)
  have hfitcs : ∀ i, FitsConfig w (cs i) := fun _ => fits_decodeConfig
  have hpcv : ∀ i : Fin (n + 1), (cs i).pc = configField (w * 2 + 1) Xpc i := by
    intro i
    have h1 := bpc i
    change configField w (configField (w * 2 + 1) R i) 0 = _
    rw [configField_zero, hblk i, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have hr0v : ∀ i : Fin (n + 1), (cs i).regs 0 = configField (w * 2 + 1) X0 i := by
    intro i
    have h1 := bpc i
    have h2 := b0 i
    change configField w (configField (w * 2 + 1) R i) (((0 : Fin 1) : ℕ) + 1) = _
    rw [show (((0 : Fin 1) : ℕ) + 1) = 0 + 1 from rfl, configField_succ, configField_zero,
      hblk i, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt h1, Nat.zero_add,
      Nat.mod_eq_of_lt h2]
  have hfour : (4 : ℕ) < 2 ^ (w * 2 + 1) := four_lt_outer hw2
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * 2 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hone := slice_one_hot hlen hs0 hs1p hs1z hs2 hsum
  -- the four global equations, blockwise
  have hA : ∀ j : Fin n, configField (w * 2 + 1) Xpc j
      = configField (w * 2 + 1) S1p j + configField (w * 2 + 1) S1z j
        + 2 * configField (w * 2 + 1) S2 j := by
    intro j
    have heq : fieldsCode (w * 2 + 1)
        (Fin.init fun i : Fin (n + 1) => configField (w * 2 + 1) Xpc i)
        = 1 * fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) S1p i)
          + 1 * fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) S1z i)
          + 2 * fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) S2 i) := by
      rw [← fieldsCode_mod_pow (fun i => lt_trans (bpc i) hwlt), ← epc, hpcEq, ← f1p, ← f1z, ← f2]
      ring
    have := selector_eq_blockwise
      (fun i => lt_trans (bpc _) hwlt)
      (fun i => by have := c1p i; have := c1z i; have := c2 i; omega) heq j
    simpa [Fin.init] using this
  have hB : ∀ j : Fin n, configField (w * 2 + 1) Xpc (j + 1)
      = configField (w * 2 + 1) S0 j + 2 * configField (w * 2 + 1) S1z j
        + 1000 * configField (w * 2 + 1) S2 j := by
    intro j
    have heq : fieldsCode (w * 2 + 1)
        ((fun i : Fin (n + 1) => configField (w * 2 + 1) Xpc i) ∘ Fin.succ)
        = 1 * fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) S0 i)
          + 2 * fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) S1z i)
          + 1000 * fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) S2 i) := by
      rw [← fieldsCode_div _ _ (lt_trans (bpc 0) hwlt), ← epc, hjump, ← f0, ← f1z, ← f2]
      ring
    have hbd : ∀ i : Fin n, 1 * configField (w * 2 + 1) S0 i + 2 * configField (w * 2 + 1) S1z i
        + 1000 * configField (w * 2 + 1) S2 i < 2 ^ (w * 2 + 1) := by
      intro i
      rcases Nat.eq_zero_or_pos (configField (w * 2 + 1) S2 i) with hz | hz
      · have := c0 i; have := c1z i; omega
      · have h2 : configField (w * 2 + 1) S2 i = 1 := by have := c2 i; omega
        have := slice_target ht2 h2
        have := c0 i; have := c1z i
        have : (1000 : ℕ) < 2 ^ (w * 2 + 1) := lt_trans (slice_target ht2 h2) hwlt
        omega
    have := selector_eq_blockwise (fun i => lt_trans (bpc _) hwlt) hbd heq j
    simpa using this
  have hC : ∀ j : Fin n, configField (w * 2 + 1) X0 (j + 1) + configField (w * 2 + 1) S1p j
      = configField (w * 2 + 1) X0 j + configField (w * 2 + 1) S0 j
        + configField (w * 2 + 1) S2 j := by
    intro j
    have heq : fieldsCode (w * 2 + 1)
        (fun i : Fin n => configField (w * 2 + 1) X0 (i.succ)
          + configField (w * 2 + 1) S1p i)
        = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) X0 (i.castSucc)
          + configField (w * 2 + 1) S0 i + configField (w * 2 + 1) S2 i) := by
      rw [← fieldsCode_add, ← fieldsCode_add, ← fieldsCode_add]
      have hd : fieldsCode (w * 2 + 1)
          ((fun i : Fin (n + 1) => configField (w * 2 + 1) X0 i) ∘ Fin.succ)
          = X0 / 2 ^ (w * 2 + 1) := by
        rw [← fieldsCode_div _ _ (lt_trans (b0 0) hwlt), ← e0]
      have hm : fieldsCode (w * 2 + 1)
          (Fin.init fun i : Fin (n + 1) => configField (w * 2 + 1) X0 i)
          = X0 % (2 ^ (w * 2 + 1)) ^ n := by
        rw [← fieldsCode_mod_pow (fun i => lt_trans (b0 i) hwlt), ← e0]
      rw [show (fun i : Fin n => configField (w * 2 + 1) X0 (i.succ)) =
        ((fun i : Fin (n + 1) => configField (w * 2 + 1) X0 i) ∘ Fin.succ) from rfl, hd,
        show (fun i : Fin n => configField (w * 2 + 1) X0 (i.castSucc)) =
          (Fin.init fun i : Fin (n + 1) => configField (w * 2 + 1) X0 i) from rfl, hm,
        ← f1p, ← f0, ← f2, hupd]
    have hbd1 : ∀ i : Fin n, configField (w * 2 + 1) X0 (i.succ)
        + configField (w * 2 + 1) S1p i < 2 ^ (w * 2 + 1) := by
      intro i; have := b0 i.succ; have := c1p i; omega
    have hbd2 : ∀ i : Fin n, configField (w * 2 + 1) X0 (i.castSucc)
        + configField (w * 2 + 1) S0 i + configField (w * 2 + 1) S2 i < 2 ^ (w * 2 + 1) := by
      intro i; have := b0 i.castSucc; have := c0 i; have := c2 i; omega
    have := congrFun (fieldsCode_injective hbd1 hbd2 heq) j
    simpa using this
  have hD : ∀ j : Fin n, configField (w * 2 + 1) X0 j
      + configField (w * 2 + 1) S1z j * (2 ^ w - 1) + configField (w * 2 + 1) Zres j
      = 2 ^ w - 1 := by
    intro j
    have hm : fieldsCode (w * 2 + 1)
        (Fin.init fun i : Fin (n + 1) => configField (w * 2 + 1) X0 i)
        = X0 % (2 ^ (w * 2 + 1)) ^ n := by
      rw [← fieldsCode_mod_pow (fun i => lt_trans (b0 i) hwlt), ← e0]
    have heq : fieldsCode (w * 2 + 1) (fun i : Fin n =>
        configField (w * 2 + 1) X0 (i.castSucc)
          + configField (w * 2 + 1) S1z i * (2 ^ w - 1)
          + configField (w * 2 + 1) Zres i)
        = fieldsCode (w * 2 + 1) (fun _ : Fin n => 2 ^ w - 1) := by
      rw [← fieldsCode_add, ← fieldsCode_add, fieldsCode_const,
        show (fun i : Fin n => configField (w * 2 + 1) X0 (i.castSucc)) =
          (Fin.init fun i : Fin (n + 1) => configField (w * 2 + 1) X0 i) from rfl, hm,
        show (fun i : Fin n => configField (w * 2 + 1) S1z i * (2 ^ w - 1)) =
          (fun i : Fin n => (2 ^ w - 1) * configField (w * 2 + 1) S1z i) from
            funext fun i => Nat.mul_comm _ _,
        ← fieldsCode_smul, ← f1z, ← ez,
        show (2 ^ w - 1) * geom (2 ^ (w * 2 + 1)) n = laneMask w n from rfl]
      simpa [Nat.mul_comm] using hzeq
    have hbd1 : ∀ i : Fin n, configField (w * 2 + 1) X0 (i.castSucc)
        + configField (w * 2 + 1) S1z i * (2 ^ w - 1)
        + configField (w * 2 + 1) Zres i < 2 ^ (w * 2 + 1) := fun i =>
      zero_branch_carry hw2 (b0 _) (by have := c1z i; omega) (bz i)
    have := congrFun (fieldsCode_injective hbd1
      (fun _ => lt_trans (by omega : 2 ^ w - 1 < 2 ^ w) hwlt) heq) j
    simpa using this
  have hE : ∀ j : Fin n, configField (w * 2 + 1) X0 j
      = configField (w * 2 + 1) Res j + configField (w * 2 + 1) S1p j := by
    intro j
    have heq : fieldsCode (w * 2 + 1)
        (Fin.init fun i : Fin (n + 1) => configField (w * 2 + 1) X0 i)
        = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) Res i
          + configField (w * 2 + 1) S1p i) := by
      rw [← fieldsCode_add, ← fieldsCode_mod_pow (fun i => lt_trans (b0 i) hwlt), ← e0, ← eres,
        ← f1p, hres]
    have hbd2 : ∀ i : Fin n, configField (w * 2 + 1) Res i
        + configField (w * 2 + 1) S1p i < 2 ^ (w * 2 + 1) := by
      intro i; have := bres i; have := c1p i; omega
    have := congrFun (fieldsCode_injective (fun i => lt_trans (b0 _) hwlt) hbd2 heq) j
    simpa [Fin.init] using this
  intro i hi
  rw [show configField (w * 2 + 1) R i = configCode w (cs i) from (hcode ⟨i, by omega⟩).symm,
    show configField (w * 2 + 1) R (i + 1) = configCode w (cs (i + 1)) from
      (hcode ⟨i + 1, by omega⟩).symm]
  refine (sliceStep_iff w n cs hfitcs).mpr ⟨fun j => configField (w * 2 + 1) S0 j,
    fun j => configField (w * 2 + 1) S1p j, fun j => configField (w * 2 + 1) S1z j,
    fun j => configField (w * 2 + 1) S2 j, fun j => configField (w * 2 + 1) Res j, ?_⟩ i hi
  intro j hj
  dsimp only
  have p1 := hone ⟨j, hj⟩
  have p2 := hA ⟨j, hj⟩
  have p3 := hB ⟨j, hj⟩
  have p4 := hC ⟨j, hj⟩
  have p5 := hD ⟨j, hj⟩
  have p6 := hE ⟨j, hj⟩
  have q1 := hpcv ⟨j, by omega⟩
  have q2 := hpcv ⟨j + 1, by omega⟩
  have q3 := hr0v ⟨j, by omega⟩
  have q4 := hr0v ⟨j + 1, by omega⟩
  have q5 := b0 ⟨j, by omega⟩
  have q6 := bpc (⟨j + 1, by omega⟩ : Fin (n + 1))
  have q7 := b0 (⟨j + 1, by omega⟩ : Fin (n + 1))
  have q8 := bres ⟨j, hj⟩
  have q9 := c1z ⟨j, hj⟩
  dsimp only at p1 p2 p3 p4 p5 p6 q1 q2 q3 q4 q5 q6 q7 q8 q9
  refine ⟨by omega, by omega, by omega, by omega, ?_, by omega, by omega, ?_, ?_, ?_,
    by omega, by omega⟩
  · intro hz
    have hp : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
    rw [hz, one_mul] at p5
    omega
  · intro hz; exact slice_target ht0 hz
  · intro hz; exact slice_target ht1 hz
  · intro hz; exact slice_target ht2 hz

/-! ### Completeness

The other direction needs no packing theory beyond linearity: decode `R`, read the selectors off
`sliceStep_iff`, and pack each of them. Every global condition is then the packing of its
blockwise instance, so the only real content is the two witnesses that the blockwise layer
leaves implicit — the zero-branch residual, and the case split that decides whether
`1000 < 2 ^ w` has to hold. -/

/-- **Completeness of the global system.** -/
theorem sliceGlobal_complete {w n R : ℕ} (hlen : sliceP.length < 2 ^ w)
    (hmask : Nat.IsBinarySubmask R (guardMask (w * 2) (n + 1)))
    (hstep : ∀ i < n, EncodedStep sliceP w (configField (w * 2 + 1) R i)
      (configField (w * 2 + 1) R (i + 1))) :
    ∃ Xpc X0 S0 S1p S1z S2 Res Zres,
      SliceGlobalConditions w n R Xpc X0 S0 S1p S1z S2 Res Zres := by
  have hw2 : 2 ≤ w := two_le_of_sliceP_length_lt hlen
  have hlen3 : 3 < 2 ^ w := by simpa using hlen
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * 2 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2lt : (2 : ℕ) < 2 ^ (w * 2 + 1) := by have := four_lt_outer hw2; omega
  obtain ⟨hRlt, hRblk⟩ := isBinarySubmask_guardMask_iff.mp hmask
  have hRlt' : R < (2 ^ (w * 2 + 1)) ^ (n + 1) := hRlt
  set cs : ℕ → Config 1 := fun i => decodeConfig w (configField (w * 2 + 1) R i) with hcs
  have hblkR : ∀ i : Fin (n + 1), configField (w * 2 + 1) R i < 2 ^ (w * 2) :=
    fun i => hRblk i i.isLt
  have hfitcs : ∀ i, FitsConfig w (cs i) := fun _ => fits_decodeConfig
  have hcode : ∀ i : Fin (n + 1), configCode w (cs i) = configField (w * 2 + 1) R i :=
    fun i => configCode_decodeConfig (by simpa using hblkR i)
  have hbpc : ∀ i : Fin (n + 1), (cs i).pc < 2 ^ w := fun i => (hfitcs i).1
  have hbr : ∀ i : Fin (n + 1), (cs i).regs 0 < 2 ^ w := fun i => (hfitcs i).2 0
  -- the blockwise selectors
  have hstep' : ∀ i < n,
      EncodedStep sliceP w (configCode w (cs i)) (configCode w (cs (i + 1))) := by
    intro i hi
    rw [show configCode w (cs i) = configField (w * 2 + 1) R i from hcode ⟨i, by omega⟩,
      show configCode w (cs (i + 1)) = configField (w * 2 + 1) R (i + 1) from
        hcode ⟨i + 1, by omega⟩]
    exact hstep i hi
  obtain ⟨s0, s1p, s1z, s2, res, hsl⟩ := (sliceStep_iff w n cs hfitcs).mp hstep'
  have hsl' : ∀ i : Fin n, SliceStep w (cs (i : ℕ)).pc (cs ((i : ℕ) + 1)).pc
      ((cs (i : ℕ)).regs 0) ((cs ((i : ℕ) + 1)).regs 0) (s0 i) (s1p i) (s1z i) (s2 i) (res i) :=
    fun i => hsl i i.isLt
  have e1 : ∀ i : Fin n, s0 i + s1p i + s1z i + s2 i = 1 := fun i => (hsl' i).1
  have e2 : ∀ i : Fin n, (cs (i : ℕ)).pc = s1p i + s1z i + 2 * s2 i := fun i => (hsl' i).2.1
  have e3 : ∀ i : Fin n, (cs ((i : ℕ) + 1)).pc = s0 i + 2 * s1z i + 1000 * s2 i :=
    fun i => (hsl' i).2.2.1
  have e4 : ∀ i : Fin n, (cs ((i : ℕ) + 1)).regs 0 + s1p i
      = (cs (i : ℕ)).regs 0 + s0 i + s2 i := fun i => (hsl' i).2.2.2.1
  have e5 : ∀ i : Fin n, s1z i = 1 → (cs (i : ℕ)).regs 0 = 0 := fun i => (hsl' i).2.2.2.2.1
  have e6 : ∀ i : Fin n, (cs (i : ℕ)).regs 0 = res i + s1p i := fun i => (hsl' i).2.2.2.2.2.1
  have e7 : ∀ i : Fin n, res i < 2 ^ w := fun i => (hsl' i).2.2.2.2.2.2.1
  have e8 : ∀ i : Fin n, s2 i = 1 → 1000 < 2 ^ w := fun i => (hsl' i).2.2.2.2.2.2.2.2.2.1
  -- packing a bounded family into its mask
  have laneOf : ∀ {t : ℕ} (f : Fin t → ℕ), (∀ i, f i < 2 ^ w) →
      Nat.IsBinarySubmask (fieldsCode (w * 2 + 1) f) (laneMask w t) := by
    intro t f hf
    rw [laneMask]
    refine (isBinarySubmask_constMask_iff (by omega)).mpr
      ⟨fieldsCode_lt (fun i => lt_trans (hf i) hwlt), fun i hi => ?_⟩
    rw [field_fieldsCode (fun j => lt_trans (hf j) hwlt) ⟨i, hi⟩]
    exact hf ⟨i, hi⟩
  have bitOf : ∀ {t : ℕ} (f : Fin t → ℕ), (∀ i, f i < 2) →
      Nat.IsBinarySubmask (fieldsCode (w * 2 + 1) f) (bitMask w t) := by
    intro t f hf
    rw [bitMask_eq]
    refine (isBinarySubmask_constMask_iff (v := 1) (by omega)).mpr
      ⟨fieldsCode_lt (fun i => lt_trans (hf i) h2lt), fun i hi => ?_⟩
    rw [field_fieldsCode (fun j => lt_trans (hf j) h2lt) ⟨i, hi⟩]
    simpa using hf ⟨i, hi⟩
  have hbit : bitMask w n = fieldsCode (w * 2 + 1) (fun _ : Fin n => 1) := by
    rw [fieldsCode_const]; simp [bitMask]
  have hlane : laneMask w n = fieldsCode (w * 2 + 1) (fun _ : Fin n => 2 ^ w - 1) :=
    (fieldsCode_const _ _).symm
  -- truncating and shifting the two lanes
  have hXpcmod : (fieldsCode (w * 2 + 1) fun i : Fin (n + 1) => (cs (i : ℕ)).pc)
      % (2 ^ (w * 2 + 1)) ^ n = fieldsCode (w * 2 + 1) fun i : Fin n => (cs (i : ℕ)).pc :=
    fieldsCode_mod_pow (fun i => lt_trans (hbpc i) hwlt)
  have hXpcdiv : (fieldsCode (w * 2 + 1) fun i : Fin (n + 1) => (cs (i : ℕ)).pc)
      / 2 ^ (w * 2 + 1) = fieldsCode (w * 2 + 1) fun i : Fin n => (cs ((i : ℕ) + 1)).pc :=
    fieldsCode_div _ _ (lt_trans (hbpc 0) hwlt)
  have hX0mod : (fieldsCode (w * 2 + 1) fun i : Fin (n + 1) => (cs (i : ℕ)).regs 0)
      % (2 ^ (w * 2 + 1)) ^ n = fieldsCode (w * 2 + 1) fun i : Fin n => (cs (i : ℕ)).regs 0 :=
    fieldsCode_mod_pow (fun i => lt_trans (hbr i) hwlt)
  have hX0div : (fieldsCode (w * 2 + 1) fun i : Fin (n + 1) => (cs (i : ℕ)).regs 0)
      / 2 ^ (w * 2 + 1) = fieldsCode (w * 2 + 1) fun i : Fin n => (cs ((i : ℕ) + 1)).regs 0 :=
    fieldsCode_div _ _ (lt_trans (hbr 0) hwlt)
  -- the zero-branch residual, blockwise: `2 ^ w - 1` minus what the branch already spends
  have hzb : ∀ i : Fin n, (cs (i : ℕ)).regs 0 + (2 ^ w - 1) * s1z i
      + ((2 ^ w - 1) - ((cs (i : ℕ)).regs 0 + s1z i * (2 ^ w - 1))) = 2 ^ w - 1 := by
    intro i
    have h1 : (cs (i : ℕ)).regs 0 < 2 ^ w := hbr i.castSucc
    have h2 := e1 i
    rcases (by omega : s1z i = 0 ∨ s1z i = 1) with h | h
    · rw [h]; omega
    · rw [h, e5 i h]; omega
  refine ⟨fieldsCode (w * 2 + 1) (fun i : Fin (n + 1) => (cs (i : ℕ)).pc),
    fieldsCode (w * 2 + 1) (fun i : Fin (n + 1) => (cs (i : ℕ)).regs 0),
    fieldsCode (w * 2 + 1) (fun i : Fin n => s0 i),
    fieldsCode (w * 2 + 1) (fun i : Fin n => s1p i),
    fieldsCode (w * 2 + 1) (fun i : Fin n => s1z i),
    fieldsCode (w * 2 + 1) (fun i : Fin n => s2 i),
    fieldsCode (w * 2 + 1) (fun i : Fin n => res i),
    fieldsCode (w * 2 + 1) (fun i : Fin n =>
      (2 ^ w - 1) - ((cs (i : ℕ)).regs 0 + s1z i * (2 ^ w - 1))), ?_⟩
  refine ⟨hlen, laneOf _ hbpc, laneOf _ hbr, ?_, bitOf _ (fun i => by have := e1 i; omega),
    bitOf _ (fun i => by have := e1 i; omega), bitOf _ (fun i => by have := e1 i; omega),
    bitOf _ (fun i => by have := e1 i; omega), ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    Or.inr (by omega), Or.inr (by omega), ?_⟩
  · -- `R` is the scaled sum of its lanes
    rw [fieldsCode_smul, fieldsCode_add]
    have h1 : fieldsCode (w * 2 + 1) (fun i : Fin (n + 1) => configField (w * 2 + 1) R i) = R :=
      fieldsCode_configField hRlt'
    rw [← h1]
    exact congrArg _ (funext fun i => by rw [← hcode i, configCode_one])
  · -- the selectors partition every block
    rw [fieldsCode_add, fieldsCode_add, fieldsCode_add, hbit]
    exact congrArg _ (funext e1)
  · -- program-counter agreement
    rw [hXpcmod, fieldsCode_add, fieldsCode_smul, fieldsCode_add]
    exact congrArg _ (funext e2)
  · -- the jump
    rw [hXpcdiv, fieldsCode_smul, fieldsCode_smul, fieldsCode_add, fieldsCode_add]
    exact congrArg _ (funext e3)
  · -- the register update
    rw [hX0div, hX0mod, fieldsCode_add, fieldsCode_add, fieldsCode_add]
    exact congrArg _ (funext e4)
  · -- the zero branch
    rw [hX0mod, Nat.mul_comm (fieldsCode (w * 2 + 1) fun i : Fin n => s1z i) (2 ^ w - 1),
      fieldsCode_smul, fieldsCode_add, fieldsCode_add, hlane]
    exact congrArg _ (funext hzb)
  · exact laneOf _ (fun i => by have := hbr i.castSucc; omega)
  · -- the positive branch
    rw [hX0mod, fieldsCode_add]
    exact congrArg _ (funext e6)
  · exact laneOf _ e7
  · -- the one target bound that does not follow from the program length
    by_cases hall : ∀ i : Fin n, s2 i = 0
    · left
      rw [show (fun i : Fin n => s2 i) = (fun _ : Fin n => 0) from funext hall,
        fieldsCode_const_zero]
    · right
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact e8 i (by have := e1 i; omega)

/-- **The global equivalence.** For the slice program, the packed selector conditions say exactly
what the encoded run says: the program length fits, `R` is a guarded packing, and every adjacent
pair of blocks is an encoded step.

Both directions are proved without any bounded universal quantifier, which is the point: the
`∀ i < n` on the left is discharged into finitely many identities between packed numbers, and the
identities are recovered from it. `n = 0` is not a special case on either side — the selector
packings are empty, `bitMask w 0 = 0`, and the program-length condition is what keeps the
right-hand side from being satisfiable at `w = 1`. -/
theorem sliceGlobal_iff (w n R : ℕ) :
    (sliceP.length < 2 ^ w ∧ Nat.IsBinarySubmask R (guardMask (w * 2) (n + 1)) ∧
        ∀ i < n, EncodedStep sliceP w (configField (w * 2 + 1) R i)
          (configField (w * 2 + 1) R (i + 1))) ↔
      ∃ Xpc X0 S0 S1p S1z S2 Res Zres,
        SliceGlobalConditions w n R Xpc X0 S0 S1p S1z S2 Res Zres := by
  constructor
  · rintro ⟨hlen, hmask, hstep⟩
    exact sliceGlobal_complete hlen hmask hstep
  · rintro ⟨_, _, _, _, _, _, _, _, h⟩
    exact sliceGlobal_sound h

end RegisterMachine

end Hilbert10
