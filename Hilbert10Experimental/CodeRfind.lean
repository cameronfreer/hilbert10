/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.CodePrec

/-!
# The source semantics of `Nat.Partrec.Code.rfind'`

Issue #43, before any register is chosen — the same order as #41, #51 and #42.

`rfind'` minimises *from an offset*: on input `Nat.pair a m` it returns the least `y ≥ m` with
`f (Nat.pair a y) = 0`. Mathlib writes that with `Nat.rfind` over a shifted predicate and a
`Part.map`, and `Nat.mem_rfind` is the decisive fact.

## Keeping the offset

`mem_rfindSem` is stated in terms of the number of *unsuccessful turns* `q`, not as an interval
`m ≤ z < y`:

```lean
y ∈ rfindSem f a m ↔ ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
  ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0
```

That is what the machine does: after `q` unsuccessful turns its candidate is `q + m`. An interval
form is a corollary if a consumer ever wants one; stating it that way first would put an
arithmetic translation between the machine and its specification, which is exactly the sort of
gap the earlier constructors avoided by naming the recurrence first.
-/

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- Minimisation from an offset, named. -/
def rfindSem (f : ℕ →. ℕ) (a m : ℕ) : Part ℕ :=
  (Nat.rfind fun n => (fun z => z = 0) <$> f (Nat.pair a (n + m))).map (· + m)

/-- The predicate the search minimises, spelled out: `true` means the callee returned zero. -/
private theorem mem_map_decide_true {f : ℕ →. ℕ} {u : ℕ} :
    true ∈ ((fun z => decide (z = 0)) <$> f u) ↔ 0 ∈ f u := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    have hz' : z = 0 := by simpa using hz0
    exact hz' ▸ hz
  · intro h
    exact ⟨0, h, by simp⟩

private theorem mem_map_decide_false {f : ℕ →. ℕ} {u : ℕ} :
    false ∈ ((fun z => decide (z = 0)) <$> f u) ↔ ∃ z ∈ f u, z ≠ 0 := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩

/-- **The search characterisation**, counting unsuccessful turns. -/
theorem mem_rfindSem {f : ℕ →. ℕ} {a m y : ℕ} :
    y ∈ rfindSem f a m ↔
      ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
        ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0 := by
  rw [rfindSem, Part.mem_map_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Nat.mem_rfind] at hq
    exact ⟨q, rfl, mem_map_decide_true.mp hq.1,
      fun j hj => mem_map_decide_false.mp (hq.2 hj)⟩
  · rintro ⟨q, rfl, hq, hmin⟩
    exact ⟨q, Nat.mem_rfind.mpr ⟨mem_map_decide_true.mpr hq,
      fun {j} hj => mem_map_decide_false.mpr (hmin j hj)⟩, rfl⟩

/-- **The bridge.** `Code.rfind'`'s evaluation on a paired input is the named search. -/
theorem eval_rfind_eq (cf : Code) (a m : ℕ) :
    (Code.rfind' cf).eval (Nat.pair a m) = rfindSem cf.eval a m := by
  rw [Code.eval, Nat.unpaired, Nat.unpair_pair]
  rfl

/-- The same for an arbitrary input, which is what the machine receives. -/
theorem eval_rfind_unpair (cf : Code) (x : ℕ) :
    (Code.rfind' cf).eval x = rfindSem cf.eval x.unpair.1 x.unpair.2 := by
  conv_lhs => rw [← Nat.pair_unpair x]
  exact eval_rfind_eq cf _ _

/-! ## The controller's register layout

`Fin (k + 20)`:

| register | role |
|---|---|
| `0` | the input, and at the end the answer |
| `1` | the parameter `a` |
| `2` | the current candidate |
| `3` | the temporary `copy` borrows |
| `4`–`12` | the `pairMachine` block |
| `13`–`18` | the `unpairLoop` block |
| `19 …` | the predicate callee's block |

Simpler than `prec`'s: one callee, one pairing block, no accumulator. -/

variable (k)

/-- The parameter. -/ def sA : Fin (k + 20) := ⟨1, by omega⟩
/-- The current candidate. -/ def sC : Fin (k + 20) := ⟨2, by omega⟩
/-- The temporary. -/ def sT : Fin (k + 20) := ⟨3, by omega⟩

/-- The pairing block. -/
def sPair (i : Fin 9) : Fin (k + 20) := ⟨4 + i.val, by omega⟩

/-- The unpairing block. -/
def sUnpair (i : Fin 6) : Fin (k + 20) := ⟨13 + i.val, by omega⟩

/-- The predicate callee's block. -/
def sCall (i : Fin (k + 1)) : Fin (k + 20) := ⟨19 + i.val, by omega⟩

variable {k}

@[simp] theorem sA_val : (sA k).val = 1 := rfl
@[simp] theorem sC_val : (sC k).val = 2 := rfl
@[simp] theorem sT_val : (sT k).val = 3 := rfl
@[simp] theorem sPair_val (i : Fin 9) : (sPair k i).val = 4 + i.val := rfl
@[simp] theorem sUnpair_val (i : Fin 6) : (sUnpair k i).val = 13 + i.val := rfl
@[simp] theorem sCall_val (i : Fin (k + 1)) : (sCall k i).val = 19 + i.val := rfl

theorem sPair_injective : Function.Injective (sPair k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem sUnpair_injective : Function.Injective (sUnpair k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem sCall_injective : Function.Injective (sCall k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- **The layout is exhaustive**: `4 + 9 + 6 + (k+1) = k + 20`. -/
theorem sLayout_cases (r : Fin (k + 20)) :
    r = 0 ∨ r = sA k ∨ r = sC k ∨ r = sT k ∨ (∃ i, r = sPair k i) ∨
      (∃ i, r = sUnpair k i) ∨ ∃ i, r = sCall k i := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ (4 ≤ r.val ∧ r.val ≤ 12) ∨
      (13 ≤ r.val ∧ r.val ≤ 18) ∨ 19 ≤ r.val by omega) with h | h | h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 4, by omega⟩, Fin.ext (by simp; omega)⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 13, by omega⟩, Fin.ext (by simp; omega)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 19, by omega⟩, Fin.ext (by simp; omega)⟩)))))

/-! ### Separation -/

theorem sFixed_ne :
    (0 : Fin (k + 20)) ≠ sA k ∧ (0 : Fin (k + 20)) ≠ sC k ∧ (0 : Fin (k + 20)) ≠ sT k ∧
    sA k ≠ sC k ∧ sA k ≠ sT k ∧ sC k ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; have := congrArg Fin.val h; simp at this)

theorem sFixed_ne' :
    sA k ≠ (0 : Fin (k + 20)) ∧ sC k ≠ (0 : Fin (k + 20)) ∧ sT k ≠ (0 : Fin (k + 20)) ∧
    sC k ≠ sA k ∧ sT k ≠ sA k ∧ sT k ≠ sC k :=
  ⟨sFixed_ne.1.symm, sFixed_ne.2.1.symm, sFixed_ne.2.2.1.symm, sFixed_ne.2.2.2.1.symm,
    sFixed_ne.2.2.2.2.1.symm, sFixed_ne.2.2.2.2.2.symm⟩

theorem sPair_ne_fixed (i : Fin 9) :
    sPair k i ≠ 0 ∧ sPair k i ≠ sA k ∧ sPair k i ≠ sC k ∧ sPair k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sUnpair_ne_fixed (i : Fin 6) :
    sUnpair k i ≠ 0 ∧ sUnpair k i ≠ sA k ∧ sUnpair k i ≠ sC k ∧ sUnpair k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sCall_ne_fixed (i : Fin (k + 1)) :
    sCall k i ≠ 0 ∧ sCall k i ≠ sA k ∧ sCall k i ≠ sC k ∧ sCall k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sPair_ne_fixed' (i : Fin 9) :
    (0 : Fin (k + 20)) ≠ sPair k i ∧ sA k ≠ sPair k i ∧ sC k ≠ sPair k i ∧ sT k ≠ sPair k i :=
  ⟨(sPair_ne_fixed i).1.symm, (sPair_ne_fixed i).2.1.symm, (sPair_ne_fixed i).2.2.1.symm,
    (sPair_ne_fixed i).2.2.2.symm⟩

theorem sUnpair_ne_fixed' (i : Fin 6) :
    (0 : Fin (k + 20)) ≠ sUnpair k i ∧ sA k ≠ sUnpair k i ∧ sC k ≠ sUnpair k i ∧
      sT k ≠ sUnpair k i :=
  ⟨(sUnpair_ne_fixed i).1.symm, (sUnpair_ne_fixed i).2.1.symm, (sUnpair_ne_fixed i).2.2.1.symm,
    (sUnpair_ne_fixed i).2.2.2.symm⟩

theorem sCall_ne_fixed' (i : Fin (k + 1)) :
    (0 : Fin (k + 20)) ≠ sCall k i ∧ sA k ≠ sCall k i ∧ sC k ≠ sCall k i ∧ sT k ≠ sCall k i :=
  ⟨(sCall_ne_fixed i).1.symm, (sCall_ne_fixed i).2.1.symm, (sCall_ne_fixed i).2.2.1.symm,
    (sCall_ne_fixed i).2.2.2.symm⟩

theorem sPair_ne_sUnpair (i : Fin 9) (j : Fin 6) : sPair k i ≠ sUnpair k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sPair_ne_sCall (i : Fin 9) (j : Fin (k + 1)) : sPair k i ≠ sCall k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sUnpair_ne_sCall (i : Fin 6) (j : Fin (k + 1)) : sUnpair k i ≠ sCall k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sUnpair_ne_sPair (j : Fin 6) (i : Fin 9) : sUnpair k j ≠ sPair k i :=
  (sPair_ne_sUnpair i j).symm

theorem sCall_ne_sPair (j : Fin (k + 1)) (i : Fin 9) : sCall k j ≠ sPair k i :=
  (sPair_ne_sCall i j).symm

theorem sCall_ne_sUnpair (j : Fin (k + 1)) (i : Fin 6) : sCall k j ≠ sUnpair k i :=
  (sUnpair_ne_sCall i j).symm

attribute [local simp] sFixed_ne sFixed_ne' sPair_ne_fixed sPair_ne_fixed'
  sUnpair_ne_fixed sUnpair_ne_fixed' sCall_ne_fixed sCall_ne_fixed'
  sPair_ne_sUnpair sPair_ne_sCall sUnpair_ne_sCall
  sUnpair_ne_sPair sCall_ne_sPair sCall_ne_sUnpair

/-! ## The machine

One callee, one pairing, and a branch on its answer. The loop body is a *prefix* of the loop
rather than a middle segment, so `run_append_of_lt` and `halts_append_of_exits` suffice and
`run_middle` is not needed at all. -/

variable (Cf : Program (k + 1))

/-- Compute `Nat.pair a c` in the pairing block. -/
def rfindPairUp : Program (k + 20) :=
  seq (copy (sA k) (sPair k 0) (sT k))
    (seq (copy (sC k) (sPair k 1) (sT k)) (renameRegs (sPair k) pairMachine))

/-- Hand it to the callee and give the pairing block back clean. -/
def rfindSeedCall : Program (k + 20) :=
  seq (copy (sPair k 2) (sCall k 0) (sT k))
    (seq (clear (sPair k 0)) (seq (clear (sPair k 1)) (clear (sPair k 2))))

/-- One evaluation of the predicate at the current candidate. -/
def rfindBody : Program (k + 20) :=
  seq (rfindPairUp (k := k)) (seq (rfindSeedCall (k := k)) (renameRegs (sCall k) Cf))

/-- The search: evaluate, and on a nonzero answer discard it, step the candidate and repeat.

The `dec` at `rfindBody.length` is the branch — a zero answer leaves the loop, anything else
falls into the drain and then the increment, which also jumps back. -/
def rfindLoop : Program (k + 20) :=
  rfindBody (k := k) Cf ++
    [Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 3),
      Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 2),
      Instr.inc (sC k) 0]

theorem length_rfindLoop :
    (rfindLoop (k := k) Cf).length = (rfindBody (k := k) Cf).length + 3 := by
  simp [rfindLoop]

/-- Split the input. -/
def rfindSplit : Program (k + 20) :=
  seq (copy 0 (sUnpair k 0) (sT k)) (renameRegs (sUnpair k) unpairLoop)

/-- Move the parameter and the initial candidate into place. -/
def rfindSeed : Program (k + 20) :=
  seq (move (sUnpair k 1) (sA k)) (seq (move (sUnpair k 2) (sC k)) (clear 0))

/-- Return the candidate the search stopped at. -/
def rfindFinish : Program (k + 20) := seq (clear (sA k)) (move (sC k) 0)

/-- The whole controller. -/
def rfindController : Program (k + 20) :=
  seq (rfindSplit (k := k))
    (seq (rfindSeed (k := k)) (seq (rfindLoop (k := k) Cf) (rfindFinish (k := k))))

variable {Cf}

/-! ### The loop head

The only state the search carries: the parameter and the current candidate. There is no counter,
which is what makes soundness an induction on halting time rather than on a register. -/

/-- The register file at a loop head. -/
def searchState (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c else 0

/-- After the pairing: the candidate's argument built. -/
def searchPaired (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sPair k 0 then a else if r = sPair k 1 then c
    else if r = sPair k 2 then Nat.pair a c else 0

/-- After the callee is seeded and the pairing block cleaned. -/
def searchSeeded (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sCall k 0 then Nat.pair a c else 0

/-- After the call. -/
def searchAnswered (a c z : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sCall k 0 then z else 0

end RegisterMachine

end Hilbert10
