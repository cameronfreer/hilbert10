/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.RegisterMachinePair
import Hilbert10Experimental.CleanScratch
import Mathlib.Computability.PartrecCode

/-!
# Compiling `Nat.Partrec.Code.pair`

Issue #51, step 6. The closure theorem for `pair`: given clean machines for two subcodes, build
one for `fun n => Nat.pair <$> cf n <*> cg n`. Assembling this over `Code.rec` is #44.

This is a controller and calling-convention proof rather than an arithmetic one. The arithmetic
was step 5.

## The source semantics, once

Mathlib evaluates `pair cf cg` applicatively. `mem_eval_pair` below turns that into an explicit
existential, so no `Seq.seq` or `Part.bind` reasoning reaches the machine proof, and the
`cf`-before-`cg` order is fixed in one place.
-/

namespace Hilbert10

namespace RegisterMachine

/-- The applicative source semantics of `Code.pair`, as an existential. `cf`'s value is `a`,
`cg`'s is `b`, and the result is `Nat.pair a b` in that order. -/
theorem mem_eval_pair {f g : ℕ →. ℕ} {n y : ℕ} :
    y ∈ (Nat.pair <$> f n <*> g n) ↔ ∃ a ∈ f n, ∃ b ∈ g n, y = Nat.pair a b := by
  simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩

/-- The evaluation of `Code.pair` really is that applicative expression. -/
theorem mem_eval_code_pair {cf cg : Nat.Partrec.Code} {n y : ℕ} :
    y ∈ (Nat.Partrec.Code.pair cf cg).eval n ↔
      ∃ a ∈ cf.eval n, ∃ b ∈ cg.eval n, y = Nat.pair a b :=
  mem_eval_pair


/-! ## The controller's register layout

One explicit layout, over `Fin (k + k' + 13)`:

| register | role |
|---|---|
| `0` | the original input, preserved across both calls, then the output |
| `1`, `2` | the two subresults, and `pairMachine`'s targets |
| `3` | `pairMachine`'s answer |
| `4`–`9` | `pairMachine`'s candidate, accumulator and scratch |
| `10` | the temporary `copy` borrows |
| `11 …` | `cf`'s block, then `cg`'s block |

The facts below are arithmetic about *this* layout, nothing more: three embeddings are
injective, their images are pairwise disjoint, and the fixed registers `0` and `10` lie outside
all of them. They are proved once so that `Fin` index juggling stays out of the semantic proof.

This is not an allocator. The embeddings are three explicit offsets, written down here and
supplied to `CleanPartComputesUnary.call` by hand. -/

variable (k k' : ℕ)

/-- `cf`'s block, starting at register `11`. -/
def embedF (i : Fin (k + 1)) : Fin (k + k' + 13) := ⟨11 + i.val, by omega⟩

/-- `cg`'s block, immediately after `cf`'s. -/
def embedG (j : Fin (k' + 1)) : Fin (k + k' + 13) := ⟨12 + k + j.val, by omega⟩

/-- `pairMachine`'s nine registers, onto `1`–`9`. -/
def embedP (i : Fin 9) : Fin (k + k' + 13) := ⟨1 + i.val, by omega⟩

variable {k k'}

@[simp] theorem embedF_val (i : Fin (k + 1)) : (embedF k k' i).val = 11 + i.val := rfl
@[simp] theorem embedG_val (j : Fin (k' + 1)) : (embedG k k' j).val = 12 + k + j.val := rfl
@[simp] theorem embedP_val (i : Fin 9) : (embedP k k' i).val = 1 + i.val := rfl

theorem embedF_injective : Function.Injective (embedF k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedG_injective : Function.Injective (embedG k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedP_injective : Function.Injective (embedP k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-! ### Register `0` and the borrowed temporary lie outside every block -/

theorem zero_ne_embedF (i : Fin (k + 1)) : (0 : Fin (k + k' + 13)) ≠ embedF k k' i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem zero_ne_embedG (j : Fin (k' + 1)) : (0 : Fin (k + k' + 13)) ≠ embedG k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem ten_ne_embedF (i : Fin (k + 1)) : (⟨10, by omega⟩ : Fin (k + k' + 13)) ≠ embedF k k' i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem ten_ne_embedG (j : Fin (k' + 1)) :
    (⟨10, by omega⟩ : Fin (k + k' + 13)) ≠ embedG k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

/-! ### The three blocks are pairwise disjoint -/

theorem embedF_ne_embedG (i : Fin (k + 1)) (j : Fin (k' + 1)) :
    embedF k k' i ≠ embedG k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem embedP_ne_embedF (i : Fin 9) (j : Fin (k + 1)) : embedP k k' i ≠ embedF k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem embedP_ne_embedG (i : Fin 9) (j : Fin (k' + 1)) : embedP k k' i ≠ embedG k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- `pairMachine`'s block is exactly registers `1`–`9`, so the controller's fixed registers `0`
and `10` are outside it too. -/
theorem embedP_ne_zero (i : Fin 9) : embedP k k' i ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp at this

theorem embedP_ne_ten (i : Fin 9) : embedP k k' i ≠ (⟨10, by omega⟩ : Fin (k + k' + 13)) := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-! ### The layout is exhaustive

The lemmas above say the blocks are separated. This one says they cover: registers `0`, `1`–`9`,
`10`, `cf`'s block and `cg`'s block account for every register, with nothing left over.

It is the eliminator for the final `funext` — showing the controller returns a clean unary
configuration means saying something about *every* register, and without this the proof would
rediscover the offset arithmetic one register at a time. -/
theorem layout_cases (r : Fin (k + k' + 13)) :
    r = 0 ∨ (∃ i, r = embedP k k' i) ∨ r = ⟨10, by omega⟩ ∨
      (∃ i, r = embedF k k' i) ∨ ∃ j, r = embedG k k' j := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ (1 ≤ r.val ∧ r.val ≤ 9) ∨ r.val = 10 ∨
      (11 ≤ r.val ∧ r.val ≤ 11 + k) ∨ 12 + k ≤ r.val by omega) with h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl ⟨⟨r.val - 1, by omega⟩, Fin.ext (by simp [embedP]; omega)⟩)
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 11, by omega⟩, Fin.ext (by simp [embedF]; omega)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 12 - k, by omega⟩, Fin.ext (by simp [embedG]; omega)⟩)))

end RegisterMachine

end Hilbert10
