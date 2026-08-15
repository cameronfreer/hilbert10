/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ConfigCoding
import Hilbert10Experimental.ForMathlib.BinarySubmask

/-!
# Route probe: can selector masks aggregate a run without a bounded universal?

Time-boxed probe for #49, phase 2. `Aggregation` is a bounded conjunction over block indices.
The question is whether, for a *fixed* program, it can instead be expressed by finitely many
global identities over per-register packed numbers.

## The distinction that decides it

A condition on a packed number is acceptable if the equivalence

> global identity between numbers  ⟺  the same identity in every block

is a **theorem proved by induction on the block index**, and unacceptable if it is a
*Diophantine condition* that itself needs representing. The circularity trap in
`Spike/Sequences.lean` is the second kind: coding partial products and requiring
`p (i + 1) = p i * h i` reproduces the bounded conjunction one level down.

The primitives below are all of the first kind. That is the whole content of the probe:
`fieldsCode` is linear, so sums and scalar multiples of packed numbers are blockwise for free,
and equality of two in-range packings is blockwise by base-`2 ^ W` uniqueness. No new
representation theorem is involved, only induction.

## The intended encoding

Per *register*, not per configuration: `Xpc, X₀, …, X_k`, each packing `n + 1` values in
blocks of width `W = w + 1`. For a fixed program `P` of `m` instructions, selectors
`S₀, …, S_{m-1}` pack `n` bits, one per step, and each `dec` selector splits as
`S⁺ₚ + S⁰ₚ`. The conditions are then, all global:

* `IsBinarySubmask Sₚ (geom B n)` — each selector is one bit per block;
* `∑ₚ Sₚ = geom B n` — exactly one instruction runs per step (no carries, since `m < 2 ^ w`);
* `Xpc % Bⁿ = ∑ₚ p · Sₚ` — the selector agrees with the program counter;
* `Xpc / B = ∑ₚ targetₚ · Sₚ^branch` — the jump;
* `X_r / B + ∑_{dec r} S⁺ₚ = X_r % Bⁿ + ∑_{inc r} Sₚ` — the register update, subtraction-free;
* `S⁰ₚ + S⁺ₚ = Sₚ`, `IsBinarySubmask (S⁰ₚ · (2 ^ w - 1)) (M - X_r % Bⁿ)` and
  `X_r % Bⁿ = X''ₚ + S⁺ₚ` — the two branch conditions of `dec`.

Every one is a single equation or submask atom, and the count depends only on `P`.

## Status

**Not a discharge of `Aggregation`.** This file proves the primitives and nothing else. The
acceptance slice — a program with an `inc` and both `dec` branches, verified in both directions
at arbitrary run length — is not built, and until it is, the analysis above is an argument, not
a theorem.
-/

namespace Hilbert10

namespace RegisterMachine

variable {W : ℕ}

/-! ### Blockwise arithmetic

`fieldsCode` is a `∑ᵢ fᵢ · Bⁱ`, so it is linear. That is why sums and scalar multiples of
packed numbers need no hypotheses at all: the bounds enter only when *recovering* the blocks. -/

theorem fieldsCode_add (W : ℕ) : ∀ {n : ℕ} (a c : Fin n → ℕ),
    fieldsCode W a + fieldsCode W c = fieldsCode W fun i => a i + c i
  | 0, _, _ => rfl
  | n + 1, a, c => by
    rw [fieldsCode_succ, fieldsCode_succ, fieldsCode_succ,
      show ((fun i => a i + c i) ∘ Fin.succ) = (fun i => (a ∘ Fin.succ) i + (c ∘ Fin.succ) i) from
        rfl,
      ← fieldsCode_add W (a ∘ Fin.succ) (c ∘ Fin.succ)]
    ring

theorem fieldsCode_smul (W m : ℕ) : ∀ {n : ℕ} (a : Fin n → ℕ),
    m * fieldsCode W a = fieldsCode W fun i => m * a i
  | 0, _ => by simp [fieldsCode]
  | n + 1, a => by
    rw [fieldsCode_succ, fieldsCode_succ,
      show ((fun i => m * a i) ∘ Fin.succ) = (fun i => m * (a ∘ Fin.succ) i) from rfl,
      ← fieldsCode_smul W m (a ∘ Fin.succ)]
    ring

/-- Base-`2 ^ W` uniqueness, in packing form. -/
theorem fieldsCode_injective {n : ℕ} {a c : Fin n → ℕ} (ha : ∀ i, a i < 2 ^ W)
    (hc : ∀ i, c i < 2 ^ W) (h : fieldsCode W a = fieldsCode W c) : a = c := by
  funext i
  rw [← field_fieldsCode ha i, ← field_fieldsCode hc i, h]

/-- **The primitive the probe turns on.** A single equation between packed numbers *is* the
family of equations between their blocks, provided nothing overflows a block. Proved by
induction; nothing here is a Diophantine condition. -/
theorem fieldsCode_add_eq_iff {n : ℕ} {a c d : Fin n → ℕ} (h : ∀ i, a i + c i < 2 ^ W)
    (hd : ∀ i, d i < 2 ^ W) :
    fieldsCode W a + fieldsCode W c = fieldsCode W d ↔ ∀ i, a i + c i = d i := by
  rw [fieldsCode_add]
  constructor
  · intro heq i
    exact congrFun (fieldsCode_injective h hd heq) i
  · intro heq
    exact congrArg _ (funext heq)

/-- The same for a sum of scalar multiples, which is the shape of the selector conditions
`Xpc % Bⁿ = ∑ₚ p · Sₚ` and the jump equation. -/
theorem fieldsCode_smul_add_eq_iff {n m₁ m₂ : ℕ} {a c d : Fin n → ℕ}
    (h : ∀ i, m₁ * a i + m₂ * c i < 2 ^ W) (hd : ∀ i, d i < 2 ^ W) :
    m₁ * fieldsCode W a + m₂ * fieldsCode W c = fieldsCode W d ↔
      ∀ i, m₁ * a i + m₂ * c i = d i := by
  rw [fieldsCode_smul, fieldsCode_smul]
  exact fieldsCode_add_eq_iff h hd

/-! ### Blockwise masking

The other half: a submask condition between packed numbers is the family of submask conditions
between their blocks. This is the one that decides whether *selector validity* is cheap, since
every selector is constrained by a mask rather than an equation. -/

theorem fieldsCode_mod (W : ℕ) {n : ℕ} (f : Fin (n + 1) → ℕ) (h0 : f 0 < 2 ^ W) :
    fieldsCode W f % 2 ^ W = f 0 := by
  rw [fieldsCode_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

theorem fieldsCode_div (W : ℕ) {n : ℕ} (f : Fin (n + 1) → ℕ) (h0 : f 0 < 2 ^ W) :
    fieldsCode W f / 2 ^ W = fieldsCode W (f ∘ Fin.succ) := by
  rw [fieldsCode_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt h0,
    Nat.zero_add]

/-- **A submask condition is blockwise too.** This is the lemma that decides the probe: every
selector is constrained by a mask rather than an equation, so if selector validity were to
recreate a bounded universal, it would have to happen here. It does not — the peeling step is
`Nat.isBinarySubmask_add_mul_two_pow_iff`, and the recursion is on the number of blocks. -/
theorem isBinarySubmask_fieldsCode_iff : ∀ {n : ℕ} {a c : Fin n → ℕ}, (∀ i, a i < 2 ^ W) →
    (∀ i, c i < 2 ^ W) →
      (Nat.IsBinarySubmask (fieldsCode W a) (fieldsCode W c) ↔
        ∀ i, Nat.IsBinarySubmask (a i) (c i)) := by
  intro n
  induction n with
  | zero =>
    intro a c _ _
    exact ⟨fun _ i => i.elim0, fun _ => Nat.isBinarySubmask_refl 0⟩
  | succ n ih =>
    intro a c ha hc
    rw [show fieldsCode W c = c 0 + 2 ^ W * fieldsCode W (c ∘ Fin.succ) from fieldsCode_succ W n c,
      Nat.isBinarySubmask_add_mul_two_pow_iff (hc 0), fieldsCode_mod W a (ha 0),
      fieldsCode_div W a (ha 0),
      ih (a := a ∘ Fin.succ) (c := c ∘ Fin.succ) (fun i => ha i.succ) (fun i => hc i.succ)]
    constructor
    · rintro ⟨h0, hs⟩ i
      exact Fin.cases h0 (fun j => hs j) i
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

end RegisterMachine

end Hilbert10
