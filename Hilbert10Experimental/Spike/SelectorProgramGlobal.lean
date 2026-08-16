/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.Spike.SelectorProgram

/-!
# The selector encoding for an arbitrary one-register program: the global layer

#49, phase 3, second layer. `Spike/SelectorProgram` reduced the encoded step relation to
`BlockStep`, one condition list per block. This file packs the blocks: the whole run becomes a
fixed number of identities between packed numbers, plus a side condition per branch.

## Branches, not instructions

The selector family is indexed by `Fin P.length ⊕ Fin P.length` — one *branch* per instruction
per side. The program-counter agreement and the jump are then the *same* shape,
`∑ branch, coefficient · selector`, differing only in the coefficient: the branch's instruction
index in one case, its target in the other. That is `fieldsCode_selected_smul_eq_iff`'s shape,
which is why neither needs an argument of its own.

## Which conditions are sums

The aggregate conditions — one-hotness, the program counter, the jump, the register update, the
two residuals — are identities between packed numbers, and there is a fixed number of them
regardless of the program. The target-fit disjunctions and `zeroBranch = 0 → S = 0` are *not*
sums: there is one per branch, so their number is `2 * P.length`. Both groups are finite and
neither depends on the run length `n`, but only the first group is aggregation.

## Scope

`globalConditions_iff` is the equivalence. Representing it is the next layer; `Aggregation 1` is
not proved here.
-/

namespace Hilbert10

namespace RegisterMachine

variable {P : Program 1} {w n R Xpc X0 Res Zres : ℕ}

/-! ### Branches -/

/-- The instruction index a branch belongs to. Both sides of an instruction share it, which is
what makes the program counter and the jump the same shape. -/
def branchIndex (P : Program 1) : Fin P.length ⊕ Fin P.length → ℕ
  | .inl p => (p : ℕ)
  | .inr p => (p : ℕ)

/-- The target a branch jumps to. -/
def branchTarget (P : Program 1) : Fin P.length ⊕ Fin P.length → ℕ
  | .inl p => (P.get p).posTarget
  | .inr p => (P.get p).zeroTarget

theorem branchIndex_lt (hlen : P.length < 2 ^ w) (c : Fin P.length ⊕ Fin P.length) :
    branchIndex P c < 2 ^ w := by
  cases c with
  | inl p => exact lt_of_lt_of_le p.isLt (by omega)
  | inr p => exact lt_of_lt_of_le p.isLt (by omega)

/-- Twice the program length fits in one block. The one-hot reading of the selector partition
needs it, and it is all the program length is used for at this layer. -/
theorem two_mul_length_lt (hlen : P.length < 2 ^ w) : 2 * P.length < 2 ^ (w * 2 + 1) := by
  have h1 : (2 : ℕ) ^ (w + 1) ≤ 2 ^ (w * 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
  omega

theorem one_lt_outer (w : ℕ) : 1 < 2 ^ (w * 2 + 1) := by
  calc (1 : ℕ) < 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (w * 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem two_pow_lt_outer (w : ℕ) : 2 ^ w < 2 ^ (w * 2 + 1) :=
  Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Two `w`-bit blocks with a `2 ^ w` scale on the second still fit in one outer block. -/
theorem lane_carry {x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    x + 2 ^ w * y < 2 ^ (w * 2 + 1) := by
  have hsq : (2 : ℕ) ^ w * 2 ^ w ≤ 2 ^ (w * 2) := by rw [← pow_add]; exact le_of_eq (by ring_nf)
  have hlt : (2 : ℕ) ^ (w * 2) < 2 ^ (w * 2 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hmul : 2 ^ w * y ≤ 2 ^ w * (2 ^ w - 1) := Nat.mul_le_mul_left _ (by omega)
  have hfill : 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * 2 ^ w := by
    have hpos : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
    rw [show 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * ((2 ^ w - 1) + 1) from by ring,
      show (2 : ℕ) ^ w - 1 + 1 = 2 ^ w from by omega]
  omega

/-- The zero branch's carry bound, with no lower bound on the width: three `w`-bit quantities,
one of them scaled by a selector, still fit in one block. -/
theorem zero_carry {x s z : ℕ} (hx : x < 2 ^ w) (hs : s ≤ 1) (hz : z < 2 ^ w) :
    x + s * (2 ^ w - 1) + z < 2 ^ (w * 2 + 1) := by
  have hpos2 : 0 < (2 : ℕ) ^ (w * 2 + 1) := Nat.two_pow_pos _
  have hpos : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
  have hdouble : (2 : ℕ) ^ (w * 2 + 1) = 2 * 2 ^ (w * 2) := by rw [pow_succ]; ring
  have hsq : (2 : ℕ) ^ w * 2 ^ w ≤ 2 ^ (w * 2) := by rw [← pow_add]; exact le_of_eq (by ring_nf)
  have hsb : s * (2 ^ w - 1) ≤ 2 ^ w - 1 := by
    calc s * (2 ^ w - 1) ≤ 1 * (2 ^ w - 1) := Nat.mul_le_mul_right _ hs
      _ = 2 ^ w - 1 := one_mul _
  rcases Nat.lt_or_ge (2 ^ w) 2 with hsmall | hbig
  · have h1 : (2 : ℕ) ^ w = 1 := by omega
    have hzero : x + s * (2 ^ w - 1) + z = 0 := by rw [h1]; omega
    omega
  · have h4 : 2 * 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ hbig
    omega

/-! ### The global conditions -/

/-- **The global selector conditions for an arbitrary one-register program.**

`S (.inl p)` is instruction `p`'s ordinary lane and `S (.inr p)` its zero lane. Read in order:
the program length fits; the two data lanes are `w`-bit packings; they reassemble `R`; every
branch lane is a bit packing and they partition every block; the program counter names the
selected branch's instruction and jumps to its target; the register update is subtraction-free;
only a decrement may take a zero branch, and taking one forces the register to vanish; the
positive residual forces the register to be at least one; and each selected target fits.

The last two groups are per branch. Everything before them is a fixed number of identities. -/
def GlobalConditions (P : Program 1) (w n R Xpc X0 : ℕ)
    (S : Fin P.length ⊕ Fin P.length → ℕ) (Res Zres : ℕ) : Prop :=
  P.length < 2 ^ w ∧
  Nat.IsBinarySubmask Xpc (laneMask w (n + 1)) ∧
  Nat.IsBinarySubmask X0 (laneMask w (n + 1)) ∧
  R = Xpc + 2 ^ w * X0 ∧
  (∀ c, Nat.IsBinarySubmask (S c) (bitMask w n)) ∧
  (∑ c : Fin P.length ⊕ Fin P.length, S c) = bitMask w n ∧
  Xpc % (2 ^ (w * 2 + 1)) ^ n = ∑ c : Fin P.length ⊕ Fin P.length, branchIndex P c * S c ∧
  Xpc / 2 ^ (w * 2 + 1) = ∑ c : Fin P.length ⊕ Fin P.length, branchTarget P c * S c ∧
  X0 / 2 ^ (w * 2 + 1) + ∑ p : Fin P.length, (P.get p).loss * S (.inl p)
    = X0 % (2 ^ (w * 2 + 1)) ^ n + ∑ p : Fin P.length, (P.get p).gain * S (.inl p) ∧
  (∀ p, (P.get p).zeroBranch = 0 → S (.inr p) = 0) ∧
  (X0 % (2 ^ (w * 2 + 1)) ^ n + (∑ p : Fin P.length, S (.inr p)) * (2 ^ w - 1) + Zres
      = laneMask w n ∧
    Nat.IsBinarySubmask Zres (laneMask w n)) ∧
  (X0 % (2 ^ (w * 2 + 1)) ^ n = Res + ∑ p : Fin P.length, (P.get p).loss * S (.inl p) ∧
    Nat.IsBinarySubmask Res (laneMask w n)) ∧
  (∀ c, S c = 0 ∨ branchTarget P c < 2 ^ w)

/-! ### Soundness -/

/-- **Soundness of the global system.** -/
theorem globalConditions_sound {S : Fin P.length ⊕ Fin P.length → ℕ}
    (h : GlobalConditions P w n R Xpc X0 S Res Zres) :
    P.length < 2 ^ w ∧
      Nat.IsBinarySubmask R (guardMask (w * 2) (n + 1)) ∧
      ∀ i < n, EncodedStep P w (configField (w * 2 + 1) R i)
        (configField (w * 2 + 1) R (i + 1)) := by
  obtain ⟨hlen, hmpc, hm0, hR, hmS, hsum, hpcEq, hjump, hupd, hzb, ⟨hzeq, hzm⟩,
    ⟨hres, hresm⟩, htgt⟩ := h
  obtain ⟨epc, bpc⟩ := lane_norm hmpc
  obtain ⟨e0, b0⟩ := lane_norm hm0
  obtain ⟨eres, bres⟩ := lane_norm hresm
  obtain ⟨ez, bz⟩ := lane_norm hzm
  have eS : ∀ c, S c = fieldsCode (w * 2 + 1)
      (fun i : Fin n => configField (w * 2 + 1) (S c) i) := fun c => (selector_norm (hmS c)).1
  have bS : ∀ c, ∀ i : Fin n, configField (w * 2 + 1) (S c) i < 2 :=
    fun c => (selector_norm (hmS c)).2
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * 2 + 1) := two_pow_lt_outer w
  have h2L : 2 * P.length < 2 ^ (w * 2 + 1) := two_mul_length_lt hlen
  -- the two lanes reassemble `R` blockwise
  have hblk : ∀ i : Fin (n + 1), configField (w * 2 + 1) R i
      = configField (w * 2 + 1) Xpc i + 2 ^ w * configField (w * 2 + 1) X0 i := by
    intro i
    have hRe : R = fieldsCode (w * 2 + 1)
        (fun j : Fin (n + 1) => configField (w * 2 + 1) Xpc j
          + 2 ^ w * configField (w * 2 + 1) X0 j) := by
      rw [hR]
      conv_lhs => rw [epc, e0]
      rw [fieldsCode_smul, fieldsCode_add]
    rw [hRe, field_fieldsCode (fun j => lane_carry (bpc j) (b0 j)) i]
  have hRblk : ∀ i : Fin (n + 1), configField (w * 2 + 1) R i < 2 ^ (w * 2) := by
    intro i
    have h1 := bpc i
    have h2 := b0 i
    have hmul : 2 ^ w * configField (w * 2 + 1) X0 i ≤ 2 ^ w * (2 ^ w - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsq : (2 : ℕ) ^ w * 2 ^ w ≤ 2 ^ (w * 2) := by
      rw [← pow_add]; exact le_of_eq (by ring_nf)
    have hpos : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
    have hfill : 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * 2 ^ w := by
      rw [show 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * ((2 ^ w - 1) + 1) from by ring,
        show (2 : ℕ) ^ w - 1 + 1 = 2 ^ w from by omega]
    rw [hblk i]; omega
  have hRlt : R < (2 ^ (w * 2 + 1)) ^ (n + 1) := by
    rw [hR]
    conv_lhs => rw [epc, e0]
    rw [fieldsCode_smul, fieldsCode_add]
    exact fieldsCode_lt fun j => lane_carry (bpc j) (b0 j)
  refine ⟨hlen, isBinarySubmask_guardMask_iff.mpr ⟨hRlt, fun i hi => hRblk ⟨i, hi⟩⟩, ?_⟩
  -- decode and hand over to the blockwise layer
  set cs : ℕ → Config 1 := fun i => decodeConfig w (configField (w * 2 + 1) R i) with hcs
  have hcode : ∀ i : Fin (n + 1), configCode w (cs i) = configField (w * 2 + 1) R i :=
    fun i => configCode_decodeConfig (by simpa using hRblk i)
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
  -- the selectors are one-hot in every block
  have hone : ∀ i : Fin n,
      (∑ c : Fin P.length ⊕ Fin P.length, configField (w * 2 + 1) (S c) i) = 1 := by
    have hbit : bitMask w n = fieldsCode (w * 2 + 1) (fun _ : Fin n => 1) := by
      rw [fieldsCode_const]; simp [bitMask]
    have hkey : fieldsCode (w * 2 + 1)
        (fun i : Fin n => ∑ c : Fin P.length ⊕ Fin P.length, configField (w * 2 + 1) (S c) i)
        = fieldsCode (w * 2 + 1) (fun _ : Fin n => 1) := by
      rw [← fieldsCode_sum (w * 2 + 1) Finset.univ
        (fun c => fun i : Fin n => configField (w * 2 + 1) (S c) i),
        show (∑ c : Fin P.length ⊕ Fin P.length, fieldsCode (w * 2 + 1)
            (fun i : Fin n => configField (w * 2 + 1) (S c) i))
            = ∑ c : Fin P.length ⊕ Fin P.length, S c from
          Finset.sum_congr rfl fun c _ => (eS c).symm, hsum, hbit]
    have hcard : Fintype.card (Fin P.length ⊕ Fin P.length) = 2 * P.length := by
      rw [Fintype.card_sum, Fintype.card_fin]; ring
    have hbd : ∀ i : Fin n,
        (∑ c : Fin P.length ⊕ Fin P.length, configField (w * 2 + 1) (S c) i)
          < 2 ^ (w * 2 + 1) := by
      intro i
      have hle : (∑ c : Fin P.length ⊕ Fin P.length, configField (w * 2 + 1) (S c) i)
          ≤ ∑ _c : Fin P.length ⊕ Fin P.length, 1 :=
        Finset.sum_le_sum fun c _ => by have := bS c i; omega
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] at hle
      omega
    exact fun i => congrFun (fieldsCode_injective hbd (fun _ => one_lt_outer w) hkey) i
  have honeL : ∀ i : Fin n, (∑ p : Fin P.length, (configField (w * 2 + 1) (S (.inl p)) i
      + configField (w * 2 + 1) (S (.inr p)) i)) = 1 := by
    intro i
    calc (∑ p : Fin P.length, (configField (w * 2 + 1) (S (.inl p)) i
          + configField (w * 2 + 1) (S (.inr p)) i))
        = (∑ p : Fin P.length, configField (w * 2 + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length, configField (w * 2 + 1) (S (.inr p)) i :=
          Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, configField (w * 2 + 1) (S c) i :=
          (Fintype.sum_sum_type (fun c => configField (w * 2 + 1) (S c) i)).symm
      _ = 1 := hone i
  -- truncation and shift of the two lanes
  have hXpcmod : Xpc % (2 ^ (w * 2 + 1)) ^ n
      = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) Xpc i) := by
    conv_lhs => rw [epc]
    exact fieldsCode_mod_pow (fun i => lt_trans (bpc i) hwlt)
  have hXpcdiv : Xpc / 2 ^ (w * 2 + 1)
      = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) Xpc ((i : ℕ) + 1)) := by
    conv_lhs => rw [epc]
    exact fieldsCode_div _ _ (lt_trans (bpc 0) hwlt)
  have hX0mod : X0 % (2 ^ (w * 2 + 1)) ^ n
      = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) X0 i) := by
    conv_lhs => rw [e0]
    exact fieldsCode_mod_pow (fun i => lt_trans (b0 i) hwlt)
  have hX0div : X0 / 2 ^ (w * 2 + 1)
      = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) X0 ((i : ℕ) + 1)) := by
    conv_lhs => rw [e0]
    exact fieldsCode_div _ _ (lt_trans (b0 0) hwlt)
  -- the two selector sums that bound the register update
  have hbdl : ∀ i : Fin n,
      (∑ p : Fin P.length, (P.get p).loss * configField (w * 2 + 1) (S (.inl p)) i) ≤ 1 := by
    intro i
    calc (∑ p : Fin P.length, (P.get p).loss * configField (w * 2 + 1) (S (.inl p)) i)
        ≤ ∑ p : Fin P.length, configField (w * 2 + 1) (S (.inl p)) i :=
          Finset.sum_le_sum fun p _ => by
            have hl : (P.get p).loss ≤ 1 := by unfold Instr.loss; split <;> omega
            calc (P.get p).loss * configField (w * 2 + 1) (S (.inl p)) i
                ≤ 1 * configField (w * 2 + 1) (S (.inl p)) i := Nat.mul_le_mul_right _ hl
              _ = configField (w * 2 + 1) (S (.inl p)) i := one_mul _
      _ ≤ ∑ p : Fin P.length, (configField (w * 2 + 1) (S (.inl p)) i
            + configField (w * 2 + 1) (S (.inr p)) i) :=
          Finset.sum_le_sum fun p _ => Nat.le_add_right _ _
      _ = 1 := honeL i
  have hbdg : ∀ i : Fin n,
      (∑ p : Fin P.length, (P.get p).gain * configField (w * 2 + 1) (S (.inl p)) i) ≤ 1 := by
    intro i
    calc (∑ p : Fin P.length, (P.get p).gain * configField (w * 2 + 1) (S (.inl p)) i)
        ≤ ∑ p : Fin P.length, configField (w * 2 + 1) (S (.inl p)) i :=
          Finset.sum_le_sum fun p _ => by
            have hl : (P.get p).gain ≤ 1 := by unfold Instr.gain; split <;> omega
            calc (P.get p).gain * configField (w * 2 + 1) (S (.inl p)) i
                ≤ 1 * configField (w * 2 + 1) (S (.inl p)) i := Nat.mul_le_mul_right _ hl
              _ = configField (w * 2 + 1) (S (.inl p)) i := one_mul _
      _ ≤ ∑ p : Fin P.length, (configField (w * 2 + 1) (S (.inl p)) i
            + configField (w * 2 + 1) (S (.inr p)) i) :=
          Finset.sum_le_sum fun p _ => Nat.le_add_right _ _
      _ = 1 := honeL i
  have hbdz : ∀ i : Fin n, (∑ p : Fin P.length, configField (w * 2 + 1) (S (.inr p)) i) ≤ 1 := by
    intro i
    calc (∑ p : Fin P.length, configField (w * 2 + 1) (S (.inr p)) i)
        ≤ ∑ p : Fin P.length, (configField (w * 2 + 1) (S (.inl p)) i
            + configField (w * 2 + 1) (S (.inr p)) i) :=
          Finset.sum_le_sum fun p _ => Nat.le_add_left _ _
      _ = 1 := honeL i
  -- the aggregate equations, blockwise
  have hA : ∀ i : Fin n, configField (w * 2 + 1) Xpc i
      = ∑ p : Fin P.length, (p : ℕ) * (configField (w * 2 + 1) (S (.inl p)) i
        + configField (w * 2 + 1) (S (.inr p)) i) := by
    have heq : (∑ c : Fin P.length ⊕ Fin P.length, branchIndex P c * fieldsCode (w * 2 + 1)
        (fun i : Fin n => configField (w * 2 + 1) (S c) i))
        = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) Xpc i) := by
      rw [← hXpcmod, hpcEq]
      exact Finset.sum_congr rfl fun c _ => congrArg _ (eS c).symm
    have hkey := (fieldsCode_selected_smul_eq_iff (m := branchIndex P) hone
      (fun c _ => Or.inr (lt_trans (branchIndex_lt hlen c) hwlt))
      (fun i => lt_trans (bpc i.castSucc) hwlt)).mp heq
    intro i
    calc configField (w * 2 + 1) Xpc i
        = ∑ c : Fin P.length ⊕ Fin P.length,
            branchIndex P c * configField (w * 2 + 1) (S c) i := (hkey i).symm
      _ = (∑ p : Fin P.length, branchIndex P (.inl p) * configField (w * 2 + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length,
              branchIndex P (.inr p) * configField (w * 2 + 1) (S (.inr p)) i :=
          Fintype.sum_sum_type (fun c => branchIndex P c * configField (w * 2 + 1) (S c) i)
      _ = ∑ p : Fin P.length, ((p : ℕ) * configField (w * 2 + 1) (S (.inl p)) i
            + (p : ℕ) * configField (w * 2 + 1) (S (.inr p)) i) := Finset.sum_add_distrib.symm
      _ = ∑ p : Fin P.length, (p : ℕ) * (configField (w * 2 + 1) (S (.inl p)) i
            + configField (w * 2 + 1) (S (.inr p)) i) :=
          Finset.sum_congr rfl fun p _ => (Nat.mul_add _ _ _).symm
  have hB : ∀ i : Fin n, configField (w * 2 + 1) Xpc ((i : ℕ) + 1)
      = ∑ p : Fin P.length, ((P.get p).posTarget * configField (w * 2 + 1) (S (.inl p)) i
        + (P.get p).zeroTarget * configField (w * 2 + 1) (S (.inr p)) i) := by
    have heq : (∑ c : Fin P.length ⊕ Fin P.length, branchTarget P c * fieldsCode (w * 2 + 1)
        (fun i : Fin n => configField (w * 2 + 1) (S c) i))
        = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) Xpc ((i : ℕ) + 1)) := by
      rw [← hXpcdiv, hjump]
      exact Finset.sum_congr rfl fun c _ => congrArg _ (eS c).symm
    have hkey := (fieldsCode_selected_smul_eq_iff (m := branchTarget P) hone
      (fun c _ => by
        rcases htgt c with hzero | hfit
        · exact Or.inl fun i => by rw [hzero]; simp [configField]
        · exact Or.inr (lt_trans hfit hwlt))
      (fun i => by
        have h1 : configField (w * 2 + 1) Xpc ((i : ℕ) + 1) < 2 ^ w :=
          bpc ⟨(i : ℕ) + 1, by omega⟩
        exact lt_trans h1 hwlt)).mp heq
    intro i
    calc configField (w * 2 + 1) Xpc ((i : ℕ) + 1)
        = ∑ c : Fin P.length ⊕ Fin P.length,
            branchTarget P c * configField (w * 2 + 1) (S c) i := (hkey i).symm
      _ = (∑ p : Fin P.length, branchTarget P (.inl p) * configField (w * 2 + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length,
              branchTarget P (.inr p) * configField (w * 2 + 1) (S (.inr p)) i :=
          Fintype.sum_sum_type (fun c => branchTarget P c * configField (w * 2 + 1) (S c) i)
      _ = ∑ p : Fin P.length, ((P.get p).posTarget * configField (w * 2 + 1) (S (.inl p)) i
            + (P.get p).zeroTarget * configField (w * 2 + 1) (S (.inr p)) i) :=
          Finset.sum_add_distrib.symm
  have hC : ∀ i : Fin n, configField (w * 2 + 1) X0 ((i : ℕ) + 1)
      + ∑ p : Fin P.length, (P.get p).loss * configField (w * 2 + 1) (S (.inl p)) i
      = configField (w * 2 + 1) X0 i
        + ∑ p : Fin P.length, (P.get p).gain * configField (w * 2 + 1) (S (.inl p)) i := by
    have heq : fieldsCode (w * 2 + 1)
        (fun i : Fin n => configField (w * 2 + 1) X0 ((i : ℕ) + 1)
          + ∑ p : Fin P.length, (P.get p).loss * configField (w * 2 + 1) (S (.inl p)) i)
        = fieldsCode (w * 2 + 1)
          (fun i : Fin n => configField (w * 2 + 1) X0 i
            + ∑ p : Fin P.length, (P.get p).gain * configField (w * 2 + 1) (S (.inl p)) i) := by
      rw [← fieldsCode_add, ← fieldsCode_add, ← fieldsCode_sum_smul, ← fieldsCode_sum_smul,
        ← hX0div, ← hX0mod,
        show (∑ p : Fin P.length, (P.get p).loss * fieldsCode (w * 2 + 1)
            (fun i : Fin n => configField (w * 2 + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).loss * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm,
        show (∑ p : Fin P.length, (P.get p).gain * fieldsCode (w * 2 + 1)
            (fun i : Fin n => configField (w * 2 + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).gain * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      exact hupd
    refine fun i => congrFun (fieldsCode_injective (fun i => ?_) (fun i => ?_) heq) i
    · have h1 : configField (w * 2 + 1) X0 ((i : ℕ) + 1) < 2 ^ w := b0 ⟨(i : ℕ) + 1, by omega⟩
      have h2 := hbdl i
      have h3 := hwlt
      omega
    · have h1 : configField (w * 2 + 1) X0 (i : ℕ) < 2 ^ w := b0 i.castSucc
      have h2 := hbdg i
      have h3 := hwlt
      omega
  have hD : ∀ i : Fin n, configField (w * 2 + 1) X0 i
      + (∑ p : Fin P.length, configField (w * 2 + 1) (S (.inr p)) i) * (2 ^ w - 1)
      + configField (w * 2 + 1) Zres i = 2 ^ w - 1 := by
    have hlane : laneMask w n = fieldsCode (w * 2 + 1) (fun _ : Fin n => 2 ^ w - 1) :=
      (fieldsCode_const _ _).symm
    have heq : fieldsCode (w * 2 + 1)
        (fun i : Fin n => configField (w * 2 + 1) X0 i
          + (∑ p : Fin P.length, configField (w * 2 + 1) (S (.inr p)) i) * (2 ^ w - 1)
          + configField (w * 2 + 1) Zres i)
        = fieldsCode (w * 2 + 1) (fun _ : Fin n => 2 ^ w - 1) := by
      rw [← fieldsCode_add, ← fieldsCode_add, ← hlane, ← hzeq, ← hX0mod, ← ez,
        show (fun i : Fin n =>
            (∑ p : Fin P.length, configField (w * 2 + 1) (S (.inr p)) i) * (2 ^ w - 1))
          = (fun i : Fin n =>
            (2 ^ w - 1) * ∑ p : Fin P.length, configField (w * 2 + 1) (S (.inr p)) i) from
            funext fun i => Nat.mul_comm _ _,
        ← fieldsCode_smul, ← fieldsCode_sum,
        show (∑ p : Fin P.length, fieldsCode (w * 2 + 1)
            (fun i : Fin n => configField (w * 2 + 1) (S (.inr p)) i))
          = ∑ p : Fin P.length, S (.inr p) from Finset.sum_congr rfl fun p _ => (eS _).symm]
      rw [Nat.mul_comm (2 ^ w - 1) (∑ p : Fin P.length, S (.inr p))]
    refine fun i => congrFun (fieldsCode_injective (fun i => ?_)
      (fun _ => lt_trans (by omega : 2 ^ w - 1 < 2 ^ w) hwlt) heq) i
    have h1 : configField (w * 2 + 1) X0 (i : ℕ) < 2 ^ w := b0 i.castSucc
    exact zero_carry h1 (hbdz i) (bz i)
  have hE : ∀ i : Fin n, configField (w * 2 + 1) X0 i
      = configField (w * 2 + 1) Res i
        + ∑ p : Fin P.length, (P.get p).loss * configField (w * 2 + 1) (S (.inl p)) i := by
    have heq : fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) X0 i)
        = fieldsCode (w * 2 + 1) (fun i : Fin n => configField (w * 2 + 1) Res i
          + ∑ p : Fin P.length, (P.get p).loss * configField (w * 2 + 1) (S (.inl p)) i) := by
      rw [← fieldsCode_add, ← fieldsCode_sum_smul, ← hX0mod, ← eres,
        show (∑ p : Fin P.length, (P.get p).loss * fieldsCode (w * 2 + 1)
            (fun i : Fin n => configField (w * 2 + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).loss * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      exact hres
    refine fun i => congrFun (fieldsCode_injective
      (fun i => lt_trans (show configField (w * 2 + 1) X0 (i : ℕ) < 2 ^ w from b0 i.castSucc) hwlt)
      (fun i => ?_) heq) i
    have h1 : configField (w * 2 + 1) Res (i : ℕ) < 2 ^ w := bres i
    have h2 := hbdl i
    have h3 := hwlt
    omega
  -- assemble
  intro i hi
  rw [show configField (w * 2 + 1) R i = configCode w (cs i) from (hcode ⟨i, by omega⟩).symm,
    show configField (w * 2 + 1) R (i + 1) = configCode w (cs (i + 1)) from
      (hcode ⟨i + 1, by omega⟩).symm]
  refine (blockStep_iff P w n cs hfitcs).mpr
    ⟨fun i p => configField (w * 2 + 1) (S (.inl p)) i,
      fun i p => configField (w * 2 + 1) (S (.inr p)) i,
      fun i => configField (w * 2 + 1) Res i, ?_⟩ i hi
  intro j hj
  dsimp only
  refine ⟨honeL ⟨j, hj⟩, ?_, ?_, ?_, ?_, ?_, ?_, bres ⟨j, hj⟩, ?_, ?_, ?_, ?_⟩
  · rw [show (cs j).pc = configField (w * 2 + 1) Xpc j from hpcv ⟨j, by omega⟩]
    exact hA ⟨j, hj⟩
  · rw [show (cs (j + 1)).pc = configField (w * 2 + 1) Xpc (j + 1) from
      hpcv ⟨j + 1, by omega⟩]
    exact hB ⟨j, hj⟩
  · rw [show (cs (j + 1)).regs 0 = configField (w * 2 + 1) X0 (j + 1) from
      hr0v ⟨j + 1, by omega⟩,
      show (cs j).regs 0 = configField (w * 2 + 1) X0 j from hr0v ⟨j, by omega⟩]
    exact hC ⟨j, hj⟩
  · intro p
    dsimp only
    rcases Nat.eq_zero_or_pos ((P.get p).zeroBranch) with hz | hz
    · rw [hzb p hz]
      simp [configField]
    · have h1 : configField (w * 2 + 1) (S (.inr p)) j < 2 := bS (.inr p) ⟨j, hj⟩
      omega
  · intro hzsum
    have hz1 : (∑ p : Fin P.length,
        configField (w * 2 + 1) (S (.inr p)) (⟨j, hj⟩ : Fin n)) = 1 := hzsum
    have hd := hD ⟨j, hj⟩
    rw [hz1, one_mul] at hd
    dsimp only at hd
    rw [show (cs j).regs 0 = configField (w * 2 + 1) X0 j from hr0v ⟨j, by omega⟩]
    have h1 : configField (w * 2 + 1) X0 j < 2 ^ w := b0 (⟨j, by omega⟩ : Fin (n + 1))
    have h2 : configField (w * 2 + 1) Zres j < 2 ^ w := bz (⟨j, hj⟩ : Fin n)
    have h3 : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
    omega
  · rw [show (cs j).regs 0 = configField (w * 2 + 1) X0 j from hr0v ⟨j, by omega⟩]
    exact hE ⟨j, hj⟩
  · intro p hA1
    dsimp only at hA1
    rcases htgt (.inl p) with hzero | hfit
    · rw [hzero] at hA1; simp [configField] at hA1
    · exact hfit
  · intro p hZ1
    dsimp only at hZ1
    rcases htgt (.inr p) with hzero | hfit
    · rw [hzero] at hZ1; simp [configField] at hZ1
    · exact hfit
  · exact (hfitcs (j + 1)).1
  · exact (hfitcs (j + 1)).2 0

/-! ### Completeness -/

/-- **Completeness of the global system.** -/
theorem globalConditions_complete (hlen : P.length < 2 ^ w)
    (hmask : Nat.IsBinarySubmask R (guardMask (w * 2) (n + 1)))
    (hstep : ∀ i < n, EncodedStep P w (configField (w * 2 + 1) R i)
      (configField (w * 2 + 1) R (i + 1))) :
    ∃ (Xpc X0 : ℕ) (S : Fin P.length ⊕ Fin P.length → ℕ) (Res Zres : ℕ),
      GlobalConditions P w n R Xpc X0 S Res Zres := by
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * 2 + 1) := two_pow_lt_outer w
  have h2le : (2 : ℕ) ≤ 2 ^ (w * 2 + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (w * 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
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
  have hstep' : ∀ i < n,
      EncodedStep P w (configCode w (cs i)) (configCode w (cs (i + 1))) := by
    intro i hi
    rw [show configCode w (cs i) = configField (w * 2 + 1) R i from hcode ⟨i, by omega⟩,
      show configCode w (cs (i + 1)) = configField (w * 2 + 1) R (i + 1) from
        hcode ⟨i + 1, by omega⟩]
    exact hstep i hi
  obtain ⟨A, Z, res, hbs⟩ := (blockStep_iff P w n cs hfitcs).mp hstep'
  have hbs' : ∀ i : Fin n, BlockStep P w (cs (i : ℕ)).pc (cs ((i : ℕ) + 1)).pc
      ((cs (i : ℕ)).regs 0) ((cs ((i : ℕ) + 1)).regs 0) (res (i : ℕ)) (A (i : ℕ)) (Z (i : ℕ)) :=
    fun i => hbs i i.isLt
  -- the selector family, and the two ways of summing over it
  set selv : Fin P.length ⊕ Fin P.length → Fin n → ℕ :=
    Sum.elim (fun p i => A (i : ℕ) p) (fun p i => Z (i : ℕ) p) with hselv
  have hone : ∀ i : Fin n, (∑ c : Fin P.length ⊕ Fin P.length, selv c i) = 1 := by
    intro i
    calc (∑ c : Fin P.length ⊕ Fin P.length, selv c i)
        = (∑ p : Fin P.length, A (i : ℕ) p) + ∑ p : Fin P.length, Z (i : ℕ) p :=
          Fintype.sum_sum_type (fun c => selv c i)
      _ = ∑ p : Fin P.length, (A (i : ℕ) p + Z (i : ℕ) p) := Finset.sum_add_distrib.symm
      _ = 1 := (hbs' i).1
  have hbnd : ∀ (c : Fin P.length ⊕ Fin P.length) (i : Fin n), selv c i < 2 := by
    intro c i
    have hle : selv c i ≤ ∑ c' : Fin P.length ⊕ Fin P.length, selv c' i :=
      Finset.single_le_sum (f := fun c' => selv c' i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)
    rw [hone i] at hle
    omega
  have hboundA : ∀ (i : Fin n) (p : Fin P.length), A (i : ℕ) p < 2 := fun i p => hbnd (.inl p) i
  have hboundZ : ∀ (i : Fin n) (p : Fin P.length), Z (i : ℕ) p < 2 := fun i p => hbnd (.inr p) i
  -- packing helpers
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
      ⟨fieldsCode_lt (fun i => lt_of_lt_of_le (hf i) h2le), fun i hi => ?_⟩
    rw [field_fieldsCode (fun j => lt_of_lt_of_le (hf j) h2le) ⟨i, hi⟩]
    simpa using hf ⟨i, hi⟩
  have hbit : bitMask w n = fieldsCode (w * 2 + 1) (fun _ : Fin n => 1) := by
    rw [fieldsCode_const]; simp [bitMask]
  have hlane : laneMask w n = fieldsCode (w * 2 + 1) (fun _ : Fin n => 2 ^ w - 1) :=
    (fieldsCode_const _ _).symm
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
  -- the zero-branch residual, blockwise
  have hzsum : ∀ i : Fin n, (∑ p : Fin P.length, Z (i : ℕ) p) ≤ 1 := by
    intro i
    calc (∑ p : Fin P.length, Z (i : ℕ) p)
        ≤ ∑ p : Fin P.length, (A (i : ℕ) p + Z (i : ℕ) p) :=
          Finset.sum_le_sum fun p _ => Nat.le_add_left _ _
      _ = 1 := (hbs' i).1
  have hzb : ∀ i : Fin n, (cs (i : ℕ)).regs 0
      + (∑ p : Fin P.length, Z (i : ℕ) p) * (2 ^ w - 1)
      + ((2 ^ w - 1) - ((cs (i : ℕ)).regs 0 + (∑ p : Fin P.length, Z (i : ℕ) p) * (2 ^ w - 1)))
      = 2 ^ w - 1 := by
    intro i
    have h1 : (cs (i : ℕ)).regs 0 < 2 ^ w := hbr i.castSucc
    have h2 := hzsum i
    rcases (by omega : (∑ p : Fin P.length, Z (i : ℕ) p) = 0
        ∨ (∑ p : Fin P.length, Z (i : ℕ) p) = 1) with h | h
    · rw [h]; omega
    · rw [h, (hbs' i).2.2.2.2.2.1 h]; omega
  refine ⟨fieldsCode (w * 2 + 1) (fun i : Fin (n + 1) => (cs (i : ℕ)).pc),
    fieldsCode (w * 2 + 1) (fun i : Fin (n + 1) => (cs (i : ℕ)).regs 0),
    fun c => fieldsCode (w * 2 + 1) (selv c),
    fieldsCode (w * 2 + 1) (fun i : Fin n => res (i : ℕ)),
    fieldsCode (w * 2 + 1) (fun i : Fin n =>
      (2 ^ w - 1) - ((cs (i : ℕ)).regs 0 + (∑ p : Fin P.length, Z (i : ℕ) p) * (2 ^ w - 1))),
    hlen, laneOf _ hbpc, laneOf _ hbr, ?_, fun c => bitOf _ (hbnd c), ?_, ?_, ?_, ?_, ?_,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- `R` is the scaled sum of its lanes
    rw [fieldsCode_smul, fieldsCode_add]
    have h1 : fieldsCode (w * 2 + 1) (fun i : Fin (n + 1) => configField (w * 2 + 1) R i) = R :=
      fieldsCode_configField hRlt'
    rw [← h1]
    exact congrArg _ (funext fun i => by rw [← hcode i, configCode_one])
  · -- the branches partition every block
    dsimp only
    rw [fieldsCode_sum (w * 2 + 1) Finset.univ selv, hbit]
    exact congrArg _ (funext hone)
  · -- program-counter agreement
    dsimp only
    rw [hXpcmod, fieldsCode_sum_smul]
    refine congrArg _ (funext fun i => ?_)
    calc (cs (i : ℕ)).pc = ∑ p : Fin P.length, (p : ℕ) * (A (i : ℕ) p + Z (i : ℕ) p) :=
          (hbs' i).2.1
      _ = ∑ p : Fin P.length, ((p : ℕ) * A (i : ℕ) p + (p : ℕ) * Z (i : ℕ) p) :=
          Finset.sum_congr rfl fun p _ => Nat.mul_add _ _ _
      _ = (∑ p : Fin P.length, (p : ℕ) * A (i : ℕ) p)
            + ∑ p : Fin P.length, (p : ℕ) * Z (i : ℕ) p := Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, branchIndex P c * selv c i :=
          (Fintype.sum_sum_type (fun c => branchIndex P c * selv c i)).symm
  · -- the jump
    dsimp only
    rw [hXpcdiv, fieldsCode_sum_smul]
    refine congrArg _ (funext fun i => ?_)
    calc (cs ((i : ℕ) + 1)).pc
        = ∑ p : Fin P.length, ((P.get p).posTarget * A (i : ℕ) p
            + (P.get p).zeroTarget * Z (i : ℕ) p) := (hbs' i).2.2.1
      _ = (∑ p : Fin P.length, (P.get p).posTarget * A (i : ℕ) p)
            + ∑ p : Fin P.length, (P.get p).zeroTarget * Z (i : ℕ) p := Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, branchTarget P c * selv c i :=
          (Fintype.sum_sum_type (fun c => branchTarget P c * selv c i)).symm
  · -- the register update
    dsimp only
    rw [hX0div, hX0mod, fieldsCode_sum_smul, fieldsCode_sum_smul, fieldsCode_add,
      fieldsCode_add]
    exact congrArg _ (funext fun i => (hbs' i).2.2.2.1)
  · -- only a decrement takes a zero branch
    intro p hp
    dsimp only
    have hz : ∀ i : Fin n, Z (i : ℕ) p = 0 := by
      intro i
      have := (hbs' i).2.2.2.2.1 p
      omega
    rw [show selv (.inr p) = (fun _ : Fin n => 0) from funext hz]
    simp
  · -- the zero branch
    dsimp only
    rw [hX0mod, fieldsCode_sum (w * 2 + 1) Finset.univ (fun p : Fin P.length => selv (.inr p)),
      Nat.mul_comm (fieldsCode (w * 2 + 1) fun i : Fin n =>
        ∑ p : Fin P.length, selv (.inr p) i) (2 ^ w - 1),
      fieldsCode_smul, fieldsCode_add, fieldsCode_add, hlane]
    refine congrArg _ (funext fun i => ?_)
    rw [Nat.mul_comm (2 ^ w - 1) (∑ p : Fin P.length, selv (.inr p) i)]
    exact hzb i
  · exact laneOf _ fun i => by have := hbr i.castSucc; omega
  · -- the positive residual
    dsimp only
    rw [hX0mod, fieldsCode_sum_smul, fieldsCode_add]
    exact congrArg _ (funext fun i => (hbs' i).2.2.2.2.2.2.1)
  · exact laneOf _ fun i => (hbs' i).2.2.2.2.2.2.2.1
  · -- each selected target fits
    intro c
    dsimp only
    by_cases hall : ∀ i : Fin n, selv c i = 0
    · left
      rw [show selv c = (fun _ : Fin n => 0) from funext hall]
      simp
    · right
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      have h1 : selv c i = 1 := by have := hbnd c i; omega
      cases c with
      | inl p => exact (hbs' i).2.2.2.2.2.2.2.2.1 p h1
      | inr p => exact (hbs' i).2.2.2.2.2.2.2.2.2.1 p h1

/-- **The global equivalence, for an arbitrary one-register program.** -/
theorem globalConditions_iff (P : Program 1) (w n R : ℕ) :
    (P.length < 2 ^ w ∧ Nat.IsBinarySubmask R (guardMask (w * 2) (n + 1)) ∧
        ∀ i < n, EncodedStep P w (configField (w * 2 + 1) R i)
          (configField (w * 2 + 1) R (i + 1))) ↔
      ∃ (Xpc X0 : ℕ) (S : Fin P.length ⊕ Fin P.length → ℕ) (Res Zres : ℕ),
        GlobalConditions P w n R Xpc X0 S Res Zres := by
  constructor
  · rintro ⟨hlen, hmask, hstep⟩
    exact globalConditions_complete hlen hmask hstep
  · rintro ⟨_, _, _, _, _, h⟩
    exact globalConditions_sound h

end RegisterMachine

end Hilbert10
