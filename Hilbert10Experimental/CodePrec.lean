/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.CodePair

/-!
# The source semantics of `Nat.Partrec.Code.prec`

Issue #42, before any register is chosen. `Code.prec`'s evaluation is written with `Nat.rec`
inside `Nat.unpaired`, and the recursion, the nested pairing and the `Part` bind would all reach
the machine proof if it were used in that form.

`precSem` names the recurrence instead, and `eval_prec_eq` is the bridge, proved once:

```lean
precSem f g a 0       = f a
precSem f g a (k + 1) = precSem f g a k >>= fun acc => g (Nat.pair a (Nat.pair k acc))
```

Mathlib's `eval_prec_zero` and `eval_prec_succ` supply both cases, so the bridge is an induction
and nothing more.
-/

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- The primitive-recursion recurrence, named. `a` is the preserved parameter, `k` the index, and
the accumulator is threaded through the bind. -/
def precSem (f g : ℕ →. ℕ) (a : ℕ) : ℕ → Part ℕ
  | 0 => f a
  | k + 1 => precSem f g a k >>= fun acc => g (Nat.pair a (Nat.pair k acc))

@[simp] theorem precSem_zero (f g : ℕ →. ℕ) (a : ℕ) : precSem f g a 0 = f a := rfl

theorem precSem_succ (f g : ℕ →. ℕ) (a k : ℕ) :
    precSem f g a (k + 1) = precSem f g a k >>= fun acc => g (Nat.pair a (Nat.pair k acc)) :=
  rfl

/-- The step of the recurrence, as an existential — the form the loop's one-turn theorem wants. -/
theorem mem_precSem_succ {f g : ℕ →. ℕ} {a k y : ℕ} :
    y ∈ precSem f g a (k + 1) ↔
      ∃ acc ∈ precSem f g a k, y ∈ g (Nat.pair a (Nat.pair k acc)) := by
  rw [precSem_succ]
  exact Part.mem_bind_iff

/-- **The bridge.** `Code.prec`'s evaluation on a paired input is the recurrence. -/
theorem eval_prec_eq (cf cg : Code) (a n : ℕ) :
    (Code.prec cf cg).eval (Nat.pair a n) = precSem cf.eval cg.eval a n := by
  induction n with
  | zero => rw [Code.eval_prec_zero, precSem_zero]
  | succ n ih => rw [Code.eval_prec_succ, ih, precSem_succ]

/-- The same for an arbitrary input, which is what the machine actually receives. -/
theorem eval_prec_unpair (cf cg : Code) (x : ℕ) :
    (Code.prec cf cg).eval x = precSem cf.eval cg.eval x.unpair.1 x.unpair.2 := by
  conv_lhs => rw [← Nat.pair_unpair x]
  exact eval_prec_eq cf cg _ _

/-- The loop invariant's semantic step: one successful call to the step machine advances the
accumulator from stage `k` to stage `k + 1`. -/
theorem mem_precSem_step {f g : ℕ →. ℕ} {a k acc acc' : ℕ} (h : acc ∈ precSem f g a k)
    (h' : acc' ∈ g (Nat.pair a (Nat.pair k acc))) : acc' ∈ precSem f g a (k + 1) :=
  mem_precSem_succ.mpr ⟨acc, h, h'⟩

/-! ## The controller's register layout

`Fin (k + k' + 32)`:

| register | role |
|---|---|
| `0` | the input, and at the end the answer |
| `1` | the parameter `a` |
| `2` | the current index `k` |
| `3` | the remaining iterations `r` |
| `4` | the accumulator |
| `5` | the temporary `copy` borrows |
| `6`–`14` | the inner `pairMachine` block, computing `Nat.pair k acc` |
| `15`–`23` | the outer `pairMachine` block, computing `Nat.pair a` of that |
| `24`–`29` | the `unpairLoop` block, used once on the way in |
| `30 …` | the base callee's block, then the step callee's |

**Two pairing blocks, not one.** Sharing a single block is safe — the two pairings are
sequential and `pairMachine` returns its scratch clean — but reusing it costs a clear-and-move
phase between them, which is four more blocks and two more interface states in the turn proof.
Nine registers are cheaper than that.

**The outer pairing's result reaches the step callee by `copy`.** Making `pairMachine`'s result
register *be* the callee's input would save the copy, but the two embeddings would then overlap
in one point and every separation lemma below would acquire a case split. Keeping this section
flat is what it is for.

None of this is allocation: five explicit offsets, written down once. -/

variable (k k')

/-- The parameter `a`. -/ def rA : Fin (k + k' + 32) := ⟨1, by omega⟩
/-- The current index. -/ def rK : Fin (k + k' + 32) := ⟨2, by omega⟩
/-- The remaining iterations. -/ def rR : Fin (k + k' + 32) := ⟨3, by omega⟩
/-- The accumulator. -/ def rAcc : Fin (k + k' + 32) := ⟨4, by omega⟩
/-- The temporary `copy` borrows. -/ def rTmp : Fin (k + k' + 32) := ⟨5, by omega⟩

/-- The inner pairing block, for `Nat.pair k acc`. -/
def embedPairA (i : Fin 9) : Fin (k + k' + 32) := ⟨6 + i.val, by omega⟩

/-- The outer pairing block, for `Nat.pair a` of the inner result. -/
def embedPairB (i : Fin 9) : Fin (k + k' + 32) := ⟨15 + i.val, by omega⟩

/-- The `unpairLoop` block. -/
def embedUnpair (i : Fin 6) : Fin (k + k' + 32) := ⟨24 + i.val, by omega⟩

/-- The base callee's block. -/
def embedBase (i : Fin (k + 1)) : Fin (k + k' + 32) := ⟨30 + i.val, by omega⟩

/-- The step callee's block. -/
def embedStep (j : Fin (k' + 1)) : Fin (k + k' + 32) := ⟨31 + k + j.val, by omega⟩

variable {k k'}

@[simp] theorem rA_val : (rA k k').val = 1 := rfl
@[simp] theorem rK_val : (rK k k').val = 2 := rfl
@[simp] theorem rR_val : (rR k k').val = 3 := rfl
@[simp] theorem rAcc_val : (rAcc k k').val = 4 := rfl
@[simp] theorem rTmp_val : (rTmp k k').val = 5 := rfl
@[simp] theorem embedPairA_val (i : Fin 9) : (embedPairA k k' i).val = 6 + i.val := rfl
@[simp] theorem embedPairB_val (i : Fin 9) : (embedPairB k k' i).val = 15 + i.val := rfl
@[simp] theorem embedUnpair_val (i : Fin 6) : (embedUnpair k k' i).val = 24 + i.val := rfl
@[simp] theorem embedBase_val (i : Fin (k + 1)) : (embedBase k k' i).val = 30 + i.val := rfl
@[simp] theorem embedStep_val (j : Fin (k' + 1)) :
    (embedStep k k' j).val = 31 + k + j.val := rfl

theorem embedPairA_injective : Function.Injective (embedPairA k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedPairB_injective : Function.Injective (embedPairB k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedUnpair_injective : Function.Injective (embedUnpair k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedBase_injective : Function.Injective (embedBase k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedStep_injective : Function.Injective (embedStep k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- **The layout is exhaustive**: `6 + 9 + 9 + 6 + (k+1) + (k'+1) = k + k' + 32`. -/
theorem precLayout_cases (r : Fin (k + k' + 32)) :
    r = 0 ∨ r = rA k k' ∨ r = rK k k' ∨ r = rR k k' ∨ r = rAcc k k' ∨ r = rTmp k k' ∨
      (∃ i, r = embedPairA k k' i) ∨ (∃ i, r = embedPairB k k' i) ∨
      (∃ i, r = embedUnpair k k' i) ∨ (∃ i, r = embedBase k k' i) ∨
      ∃ j, r = embedStep k k' j := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨
      (6 ≤ r.val ∧ r.val ≤ 14) ∨ (15 ≤ r.val ∧ r.val ≤ 23) ∨ (24 ≤ r.val ∧ r.val ≤ 29) ∨
      (30 ≤ r.val ∧ r.val ≤ 30 + k) ∨ 31 + k ≤ r.val by omega)
    with h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 6, by omega⟩, Fin.ext (by simp; omega)⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 15, by omega⟩, Fin.ext (by simp; omega)⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 24, by omega⟩, Fin.ext (by simp; omega)⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 30, by omega⟩, Fin.ext (by simp; omega)⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 31 - k, by omega⟩, Fin.ext (by simp; omega)⟩)))))))))

/-! ### Separation

Bundled per block rather than per pair: the register case analysis quantifies over whole blocks,
so that is the shape the proofs consume. -/

theorem precFixed_ne :
    (0 : Fin (k + k' + 32)) ≠ rA k k' ∧ (0 : Fin (k + k' + 32)) ≠ rK k k' ∧
    (0 : Fin (k + k' + 32)) ≠ rR k k' ∧ (0 : Fin (k + k' + 32)) ≠ rAcc k k' ∧
    (0 : Fin (k + k' + 32)) ≠ rTmp k k' ∧ rA k k' ≠ rK k k' ∧ rA k k' ≠ rR k k' ∧
    rA k k' ≠ rAcc k k' ∧ rA k k' ≠ rTmp k k' ∧ rK k k' ≠ rR k k' ∧ rK k k' ≠ rAcc k k' ∧
    rK k k' ≠ rTmp k k' ∧ rR k k' ≠ rAcc k k' ∧ rR k k' ≠ rTmp k k' ∧ rAcc k k' ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this)

theorem embedPairA_ne_fixed (i : Fin 9) :
    embedPairA k k' i ≠ 0 ∧ embedPairA k k' i ≠ rA k k' ∧ embedPairA k k' i ≠ rK k k' ∧
    embedPairA k k' i ≠ rR k k' ∧ embedPairA k k' i ≠ rAcc k k' ∧
    embedPairA k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedPairB_ne_fixed (i : Fin 9) :
    embedPairB k k' i ≠ 0 ∧ embedPairB k k' i ≠ rA k k' ∧ embedPairB k k' i ≠ rK k k' ∧
    embedPairB k k' i ≠ rR k k' ∧ embedPairB k k' i ≠ rAcc k k' ∧
    embedPairB k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedUnpair_ne_fixed (i : Fin 6) :
    embedUnpair k k' i ≠ 0 ∧ embedUnpair k k' i ≠ rA k k' ∧ embedUnpair k k' i ≠ rK k k' ∧
    embedUnpair k k' i ≠ rR k k' ∧ embedUnpair k k' i ≠ rAcc k k' ∧
    embedUnpair k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedBase_ne_fixed (i : Fin (k + 1)) :
    embedBase k k' i ≠ 0 ∧ embedBase k k' i ≠ rA k k' ∧ embedBase k k' i ≠ rK k k' ∧
    embedBase k k' i ≠ rR k k' ∧ embedBase k k' i ≠ rAcc k k' ∧
    embedBase k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedStep_ne_fixed (j : Fin (k' + 1)) :
    embedStep k k' j ≠ 0 ∧ embedStep k k' j ≠ rA k k' ∧ embedStep k k' j ≠ rK k k' ∧
    embedStep k k' j ≠ rR k k' ∧ embedStep k k' j ≠ rAcc k k' ∧
    embedStep k k' j ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedPairA_ne_embedPairB (i j : Fin 9) : embedPairA k k' i ≠ embedPairB k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairA_ne_embedUnpair (i : Fin 9) (j : Fin 6) :
    embedPairA k k' i ≠ embedUnpair k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairA_ne_embedBase (i : Fin 9) (j : Fin (k + 1)) :
    embedPairA k k' i ≠ embedBase k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairA_ne_embedStep (i : Fin 9) (j : Fin (k' + 1)) :
    embedPairA k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairB_ne_embedUnpair (i : Fin 9) (j : Fin 6) :
    embedPairB k k' i ≠ embedUnpair k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairB_ne_embedBase (i : Fin 9) (j : Fin (k + 1)) :
    embedPairB k k' i ≠ embedBase k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairB_ne_embedStep (i : Fin 9) (j : Fin (k' + 1)) :
    embedPairB k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedUnpair_ne_embedBase (i : Fin 6) (j : Fin (k + 1)) :
    embedUnpair k k' i ≠ embedBase k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedUnpair_ne_embedStep (i : Fin 6) (j : Fin (k' + 1)) :
    embedUnpair k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedBase_ne_embedStep (i : Fin (k + 1)) (j : Fin (k' + 1)) :
    embedBase k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

/- The same facts in the reverse orientation.

A register condition reaches `simp` as an *equation*, so the canonical disequality bundle only
fires if the equation is already the right way round. `ne_comm` cannot help — it acts on
disequalities. `eq_comm` can, but only sometimes: it normalises by term order, which puts
`rA k k' = embedPairA k k' i` the useful way round but leaves `0 = embedPairA k k' i` and
`embedBase k k' i = embedPairA k k' j` untouched, because a numeral and a differently-named
embedding order the other way. Rather than depend on which way `simp` happens to orient a given
pair, both directions are stated. Bundled, so this is sixteen declarations rather than
fifty-five. -/
theorem precFixed_ne' :
    rA k k' ≠ (0 : Fin (k + k' + 32)) ∧ rK k k' ≠ (0 : Fin (k + k' + 32)) ∧
    rR k k' ≠ (0 : Fin (k + k' + 32)) ∧ rAcc k k' ≠ (0 : Fin (k + k' + 32)) ∧
    rTmp k k' ≠ (0 : Fin (k + k' + 32)) ∧ rK k k' ≠ rA k k' ∧ rR k k' ≠ rA k k' ∧
    rAcc k k' ≠ rA k k' ∧ rTmp k k' ≠ rA k k' ∧ rR k k' ≠ rK k k' ∧ rAcc k k' ≠ rK k k' ∧
    rTmp k k' ≠ rK k k' ∧ rAcc k k' ≠ rR k k' ∧ rTmp k k' ≠ rR k k' ∧ rTmp k k' ≠ rAcc k k' :=
  ⟨precFixed_ne.1.symm, precFixed_ne.2.1.symm, precFixed_ne.2.2.1.symm,
    precFixed_ne.2.2.2.1.symm, precFixed_ne.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm⟩

theorem embedPairA_ne_fixed' (i : Fin 9) :
    (0 : Fin (k + k' + 32)) ≠ embedPairA k k' i ∧ rA k k' ≠ embedPairA k k' i ∧
    rK k k' ≠ embedPairA k k' i ∧
    rR k k' ≠ embedPairA k k' i ∧ rAcc k k' ≠ embedPairA k k' i ∧ rTmp k k' ≠ embedPairA k k' i :=
  ⟨(embedPairA_ne_fixed i).1.symm, (embedPairA_ne_fixed i).2.1.symm,
    (embedPairA_ne_fixed i).2.2.1.symm,
    (embedPairA_ne_fixed i).2.2.2.1.symm, (embedPairA_ne_fixed i).2.2.2.2.1.symm,
    (embedPairA_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedPairB_ne_fixed' (i : Fin 9) :
    (0 : Fin (k + k' + 32)) ≠ embedPairB k k' i ∧ rA k k' ≠ embedPairB k k' i ∧
    rK k k' ≠ embedPairB k k' i ∧
    rR k k' ≠ embedPairB k k' i ∧ rAcc k k' ≠ embedPairB k k' i ∧ rTmp k k' ≠ embedPairB k k' i :=
  ⟨(embedPairB_ne_fixed i).1.symm, (embedPairB_ne_fixed i).2.1.symm,
    (embedPairB_ne_fixed i).2.2.1.symm,
    (embedPairB_ne_fixed i).2.2.2.1.symm, (embedPairB_ne_fixed i).2.2.2.2.1.symm,
    (embedPairB_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedUnpair_ne_fixed' (i : Fin 6) :
    (0 : Fin (k + k' + 32)) ≠ embedUnpair k k' i ∧ rA k k' ≠ embedUnpair k k' i ∧
    rK k k' ≠ embedUnpair k k' i ∧
    rR k k' ≠ embedUnpair k k' i ∧ rAcc k k' ≠ embedUnpair k k' i ∧
    rTmp k k' ≠ embedUnpair k k' i :=
  ⟨(embedUnpair_ne_fixed i).1.symm, (embedUnpair_ne_fixed i).2.1.symm,
    (embedUnpair_ne_fixed i).2.2.1.symm,
    (embedUnpair_ne_fixed i).2.2.2.1.symm, (embedUnpair_ne_fixed i).2.2.2.2.1.symm,
    (embedUnpair_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedBase_ne_fixed' (i : Fin (k + 1)) :
    (0 : Fin (k + k' + 32)) ≠ embedBase k k' i ∧ rA k k' ≠ embedBase k k' i ∧
    rK k k' ≠ embedBase k k' i ∧
    rR k k' ≠ embedBase k k' i ∧ rAcc k k' ≠ embedBase k k' i ∧ rTmp k k' ≠ embedBase k k' i :=
  ⟨(embedBase_ne_fixed i).1.symm, (embedBase_ne_fixed i).2.1.symm,
    (embedBase_ne_fixed i).2.2.1.symm,
    (embedBase_ne_fixed i).2.2.2.1.symm, (embedBase_ne_fixed i).2.2.2.2.1.symm,
    (embedBase_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedStep_ne_fixed' (i : Fin (k' + 1)) :
    (0 : Fin (k + k' + 32)) ≠ embedStep k k' i ∧ rA k k' ≠ embedStep k k' i ∧
    rK k k' ≠ embedStep k k' i ∧
    rR k k' ≠ embedStep k k' i ∧ rAcc k k' ≠ embedStep k k' i ∧ rTmp k k' ≠ embedStep k k' i :=
  ⟨(embedStep_ne_fixed i).1.symm, (embedStep_ne_fixed i).2.1.symm,
    (embedStep_ne_fixed i).2.2.1.symm,
    (embedStep_ne_fixed i).2.2.2.1.symm, (embedStep_ne_fixed i).2.2.2.2.1.symm,
    (embedStep_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedPairB_ne_embedPairA (i : Fin 9) (j : Fin 9) : embedPairB k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedPairB j i).symm

theorem embedUnpair_ne_embedPairA (i : Fin 6) (j : Fin 9) :
    embedUnpair k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedUnpair j i).symm

theorem embedBase_ne_embedPairA (i : Fin (k + 1)) (j : Fin 9) :
    embedBase k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedBase j i).symm

theorem embedStep_ne_embedPairA (i : Fin (k' + 1)) (j : Fin 9) :
    embedStep k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedStep j i).symm

theorem embedUnpair_ne_embedPairB (i : Fin 6) (j : Fin 9) :
    embedUnpair k k' i ≠ embedPairB k k' j :=
  (embedPairB_ne_embedUnpair j i).symm

theorem embedBase_ne_embedPairB (i : Fin (k + 1)) (j : Fin 9) :
    embedBase k k' i ≠ embedPairB k k' j :=
  (embedPairB_ne_embedBase j i).symm

theorem embedStep_ne_embedPairB (i : Fin (k' + 1)) (j : Fin 9) :
    embedStep k k' i ≠ embedPairB k k' j :=
  (embedPairB_ne_embedStep j i).symm

theorem embedBase_ne_embedUnpair (i : Fin (k + 1)) (j : Fin 6) :
    embedBase k k' i ≠ embedUnpair k k' j :=
  (embedUnpair_ne_embedBase j i).symm

theorem embedStep_ne_embedUnpair (i : Fin (k' + 1)) (j : Fin 6) :
    embedStep k k' i ≠ embedUnpair k k' j :=
  (embedUnpair_ne_embedStep j i).symm

theorem embedStep_ne_embedBase (i : Fin (k' + 1)) (j : Fin (k + 1)) :
    embedStep k k' i ≠ embedBase k k' j :=
  (embedBase_ne_embedStep j i).symm

/- Registering the separation theorems as *declarations* rather than passing them as
hypotheses is what makes them usable: `simp` decomposes a conjunction on registration, but
`simp_all` cannot decompose a local conjunction hypothesis into rewrite rules. The reversed
bundles above cover orientation. Kept file-local — this is arithmetic
about one layout, not a fact anyone else should be simplifying with. -/
attribute [local simp] precFixed_ne embedPairA_ne_fixed embedPairB_ne_fixed
  embedUnpair_ne_fixed embedBase_ne_fixed embedStep_ne_fixed
  embedPairA_ne_embedPairB embedPairA_ne_embedUnpair embedPairA_ne_embedBase
  embedPairA_ne_embedStep embedPairB_ne_embedUnpair embedPairB_ne_embedBase
  embedPairB_ne_embedStep embedUnpair_ne_embedBase embedUnpair_ne_embedStep
  embedBase_ne_embedStep
  precFixed_ne' embedPairA_ne_fixed' embedPairB_ne_fixed' embedUnpair_ne_fixed'
  embedBase_ne_fixed' embedStep_ne_fixed'
  embedPairB_ne_embedPairA embedUnpair_ne_embedPairA embedBase_ne_embedPairA
  embedStep_ne_embedPairA embedUnpair_ne_embedPairB embedBase_ne_embedPairB
  embedStep_ne_embedPairB embedBase_ne_embedUnpair embedStep_ne_embedUnpair
  embedStep_ne_embedBase

/-! ### The loop head

The interface the whole loop is proved against, parameterised by the index and the accumulator
exactly as #51's `state1`–`state5` were parameterised by their contents.

The remaining count `rem` is what the loop branches on. There is no stored target and no
comparison: the `dec` that tests `rem` *is* the branch, so `idx ≤ n` never has to be maintained
and no residual has to be related back to the run length. -/

/-- The register file at a loop head. -/
def precLoopState (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc else 0

/-! ## The turn body

Five units, `B1`–`B5`, with an interface state after each. `B4` is the only partial one; the
other four are `Realises` macros. -/

variable (P : Program (k + 1)) (Q : Program (k' + 1))

/-- `B1`: compute `Nat.pair k acc` in the inner block. -/
def precInner : Program (k + k' + 32) :=
  seq (copy (rK k k') (embedPairA k k' 0) (rTmp k k'))
    (seq (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k'))
      (renameRegs (embedPairA k k') pairMachine))

/-- `B2`: compute `Nat.pair a` of that in the outer block. -/
def precOuter : Program (k + k' + 32) :=
  seq (copy (rA k k') (embedPairB k k' 0) (rTmp k k'))
    (seq (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k'))
      (renameRegs (embedPairB k k') pairMachine))

/-- `B3`: hand the argument to the step callee and give both pairing blocks back clean. -/
def precSeedStep : Program (k + k' + 32) :=
  seq (copy (embedPairB k k' 2) (embedStep k k' 0) (rTmp k k'))
    (seq (clear (embedPairA k k' 0))
      (seq (clear (embedPairA k k' 1))
        (seq (clear (embedPairA k k' 2))
          (seq (clear (embedPairB k k' 0))
            (seq (clear (embedPairB k k' 1)) (clear (embedPairB k k' 2)))))))

/-- `B5`: replace the accumulator with the step callee's answer. -/
def precSaveAcc : Program (k + k' + 32) :=
  seq (clear (rAcc k k')) (move (embedStep k k' 0) (rAcc k k'))

/-- The whole turn body: the four total units around the one call. -/
def precBody : Program (k + k' + 32) :=
  seq (precInner (k := k) (k' := k'))
    (seq (precOuter (k := k) (k' := k'))
      (seq (precSeedStep (k := k) (k' := k'))
        (seq (renameRegs (embedStep k k') Q) (precSaveAcc (k := k) (k' := k')))))

/-- The loop: test the remaining count, run a turn, increment the index, jump back.

The `dec` at position `0` is the branch; there is no comparison and no stored target. The `inc`
at the end both counts and jumps back, so no jump gadget is needed either. -/
def precLoop : Program (k + k' + 32) :=
  [Instr.dec (rR k k') 1 ((precBody (k := k) (k' := k') Q).length + 2)] ++
    shiftJumps 1 (precBody (k := k) (k' := k') Q) ++ [Instr.inc (rK k k') 0]

theorem length_precLoop :
    (precLoop (k := k) (k' := k') Q).length = (precBody (k := k) (k' := k') Q).length + 2 := by
  simp [precLoop]

/-! ### The body's interface states -/

/-- After `B1`: the inner pairing done. -/
def precState2 (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc else 0

/-- After `B2`: the outer pairing done. -/
def precState3 (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc
    else if r = embedPairB k k' 0 then a
    else if r = embedPairB k k' 1 then Nat.pair idx acc
    else if r = embedPairB k k' 2 then Nat.pair a (Nat.pair idx acc) else 0

/-- After `B3`: the step callee seeded, both pairing blocks clean. -/
def precState4 (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedStep k k' 0 then Nat.pair a (Nat.pair idx acc) else 0

/-- After the call: the step callee's answer in its own input register. -/
def precState5 (a idx rem acc acc' : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedStep k k' 0 then acc' else 0

/-! ### Separation facts, regrouped

The body's transitions each need the fixed-register disequalities in context so that `simp_all`
can use them without an explicit argument list. Grouped rather than flat because a fifteen-way
`obtain` pattern is unreadable at every use site. -/

/-- The separation facts every body transition needs, in context. -/
theorem precFacts (k k' : ℕ) :
    ((0 : Fin (k + k' + 32)) ≠ rA k k' ∧ (0 : Fin (k + k' + 32)) ≠ rK k k' ∧
      (0 : Fin (k + k' + 32)) ≠ rR k k' ∧ (0 : Fin (k + k' + 32)) ≠ rAcc k k' ∧
      (0 : Fin (k + k' + 32)) ≠ rTmp k k') ∧
    (rA k k' ≠ rK k k' ∧ rA k k' ≠ rR k k' ∧ rA k k' ≠ rAcc k k' ∧ rA k k' ≠ rTmp k k') ∧
    (rK k k' ≠ rR k k' ∧ rK k k' ≠ rAcc k k' ∧ rK k k' ≠ rTmp k k') ∧
    (rR k k' ≠ rAcc k k' ∧ rR k k' ≠ rTmp k k') ∧ rAcc k k' ≠ rTmp k k' :=
  ⟨⟨precFixed_ne.1, precFixed_ne.2.1, precFixed_ne.2.2.1, precFixed_ne.2.2.2.1,
      precFixed_ne.2.2.2.2.1⟩,
    ⟨precFixed_ne.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.2.1,
      precFixed_ne.2.2.2.2.2.2.2.2.1⟩,
    ⟨precFixed_ne.2.2.2.2.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.2.2.2.2.1,
      precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.1⟩,
    ⟨precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩


/-! ### `precInner`'s interior

A unit that ends in a renamed block call needs its *own* interior named. `blockState` takes the
incoming register file as an argument, so that argument has to be small — and after two `copy`
transformations it is a composite several lines long. `precInnerA` and `precInnerB` name the two
intermediate files, and the projection lemma is then stated about a name.

The same will be true of `precOuter`, whose block call is also preceded by two copies. -/

/-- After copying the index into the inner block's first target. -/
def precInnerA (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else 0

/-- After copying the accumulator into the inner block's second target. -/
def precInnerB (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 0 then idx else 0

/-- What `pairMachine` sees inside the inner block. Domain `Fin 9`, so `fin_cases` settles it and
no layout case split enters. -/
theorem precInnerB_comp_embedPairA (a idx rem acc : ℕ) :
    precInnerB (k := k) (k' := k') a idx rem acc ∘ embedPairA k k' =
      fun i => if i = 0 then idx else if i = 1 then acc else 0 := by
  have ha := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.1
  have hk := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.2.1
  have hr := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.2.2.1
  have hacc := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.2.2.2.1
  funext i
  fin_cases i <;>
    simp [precInnerB, embedPairA_injective.eq_iff, ha, hk, hr, hacc]


/-! ### `precInner`'s three stages

Each is its own top-level lemma so that no earlier exit equation is in scope when its register
case analysis runs. With the separation theorems registered above, every branch is `simp` against
the state definitions — no argument list of disequalities and no `split_ifs`. -/

/-- Stage 1: the index reaches the inner block's first target. -/
theorem run_precInner_copyK (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (rK k k') (embedPairA k k' 0) (rTmp k k'))
          ⟨0, precLoopState a idx rem acc⟩ m).pc <
        (copy (rK k k') (embedPairA k k' 0) (rTmp k k')).length) ∧
      run (copy (rK k k') (embedPairA k k' 0) (rTmp k k'))
        ⟨0, precLoopState a idx rem acc⟩ N =
        ⟨(copy (rK k k') (embedPairA k k' 0) (rTmp k k')).length,
          precInnerA a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := rK k k') (s := embedPairA k k' 0) (t := rTmp k k')
      (by simp) (by simp) (by simp)
      (precLoopState (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precLoopState, precInnerA, embedPairA_injective.eq_iff]

/-- Stage 2: the accumulator reaches the second target. -/
theorem run_precInner_copyAcc (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k'))
          ⟨0, precInnerA a idx rem acc⟩ m).pc <
        (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k')).length) ∧
      run (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k'))
        ⟨0, precInnerA a idx rem acc⟩ N =
        ⟨(copy (rAcc k k') (embedPairA k k' 1) (rTmp k k')).length,
          precInnerB a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := rAcc k k') (s := embedPairA k k' 1) (t := rTmp k k')
      (by simp) (by simp) (by simp)
      (precInnerA (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precInnerA, precInnerB, embedPairA_injective.eq_iff]

/-- Stage 3: the block call. Its argument is `precInnerB`, a name — which is the point of having
named the interior at all. -/
theorem run_precInner_pair (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (renameRegs (embedPairA k k') pairMachine)
          ⟨0, precInnerB a idx rem acc⟩ m).pc <
        (renameRegs (embedPairA k k') pairMachine).length) ∧
      run (renameRegs (embedPairA k k') pairMachine) ⟨0, precInnerB a idx rem acc⟩ N =
        ⟨(renameRegs (embedPairA k k') pairMachine).length, precState2 a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    (realises_pairMachine.renameRegs_blockState embedPairA_injective)
      (precInnerB (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_apply embedPairA_injective, precInnerB_comp_embedPairA]
    simp only [precState2]
    fin_cases i <;> simp [embedPairA_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]

/-- `B1`, the three stages spliced. -/
theorem run_precInner (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (precInner (k := k) (k' := k'))
          ⟨0, precLoopState a idx rem acc⟩ m).pc < (precInner (k := k) (k' := k')).length) ∧
      run (precInner (k := k) (k' := k')) ⟨0, precLoopState a idx rem acc⟩ N =
        ⟨(precInner (k := k) (k' := k')).length, precState2 a idx rem acc⟩ := by
  rw [precInner]
  obtain ⟨N1, i1, e1⟩ := run_precInner_copyK (k := k) (k' := k') a idx rem acc
  obtain ⟨N2, i2, e2⟩ := run_precInner_copyAcc (k := k) (k' := k') a idx rem acc
  obtain ⟨N3, i3, e3⟩ := run_precInner_pair (k := k) (k' := k') a idx rem acc
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

/-! ### `precOuter`'s interior and three stages

The same shape as `precInner`: two named interior states, a projection lemma over `Fin 9`, three
top-level stage lemmas, spliced. -/

/-- After copying the parameter into the outer block's first target. -/
def precOuterA (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedPairB k k' 0 then a
    else if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc else 0

/-- After copying the inner pairing's result into the outer block's second target. -/
def precOuterB (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedPairB k k' 1 then Nat.pair idx acc
    else if r = embedPairB k k' 0 then a
    else if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc else 0

/-- What `pairMachine` sees inside the outer block. -/
theorem precOuterB_comp_embedPairB (a idx rem acc : ℕ) :
    precOuterB (k := k) (k' := k') a idx rem acc ∘ embedPairB k k' =
      fun i => if i = 0 then a else if i = 1 then Nat.pair idx acc else 0 := by
  funext i
  fin_cases i <;> simp [precOuterB, embedPairB_injective.eq_iff]

/-- Stage 1: the parameter reaches the outer block's first target. -/
theorem run_precOuter_copyA (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (rA k k') (embedPairB k k' 0) (rTmp k k'))
          ⟨0, precState2 a idx rem acc⟩ m).pc <
        (copy (rA k k') (embedPairB k k' 0) (rTmp k k')).length) ∧
      run (copy (rA k k') (embedPairB k k' 0) (rTmp k k'))
        ⟨0, precState2 a idx rem acc⟩ N =
        ⟨(copy (rA k k') (embedPairB k k' 0) (rTmp k k')).length,
          precOuterA a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := rA k k') (s := embedPairB k k' 0) (t := rTmp k k')
      (by simp) (by simp) (by simp) (precState2 (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precState2, precOuterA, embedPairA_injective.eq_iff, embedPairB_injective.eq_iff]

/-- Stage 2: the inner result reaches the second target. -/
theorem run_precOuter_copyInner (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k'))
          ⟨0, precOuterA a idx rem acc⟩ m).pc <
        (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k')).length) ∧
      run (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k'))
        ⟨0, precOuterA a idx rem acc⟩ N =
        ⟨(copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k')).length,
          precOuterB a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := embedPairA k k' 2) (s := embedPairB k k' 1) (t := rTmp k k')
      (by simp) (by simp) (by simp) (precOuterA (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precOuterA, precOuterB, embedPairA_injective.eq_iff, embedPairB_injective.eq_iff]

/-- Stage 3: the block call. -/
theorem run_precOuter_pair (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (renameRegs (embedPairB k k') pairMachine)
          ⟨0, precOuterB a idx rem acc⟩ m).pc <
        (renameRegs (embedPairB k k') pairMachine).length) ∧
      run (renameRegs (embedPairB k k') pairMachine) ⟨0, precOuterB a idx rem acc⟩ N =
        ⟨(renameRegs (embedPairB k k') pairMachine).length, precState3 a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    (realises_pairMachine.renameRegs_blockState embedPairB_injective)
      (precOuterB (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precOuterB, precState3, embedPairA_injective.eq_iff]
  · rw [blockState_apply embedPairB_injective, precOuterB_comp_embedPairB]
    simp only [precState3]
    fin_cases i <;> simp [embedPairB_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [precOuterB, precState3]

/-- `B2`, the three stages spliced. -/
theorem run_precOuter (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (precOuter (k := k) (k' := k'))
          ⟨0, precState2 a idx rem acc⟩ m).pc < (precOuter (k := k) (k' := k')).length) ∧
      run (precOuter (k := k) (k' := k')) ⟨0, precState2 a idx rem acc⟩ N =
        ⟨(precOuter (k := k) (k' := k')).length, precState3 a idx rem acc⟩ := by
  rw [precOuter]
  obtain ⟨N1, i1, e1⟩ := run_precOuter_copyA (k := k) (k' := k') a idx rem acc
  obtain ⟨N2, i2, e2⟩ := run_precOuter_copyInner (k := k) (k' := k') a idx rem acc
  obtain ⟨N3, i3, e3⟩ := run_precOuter_pair (k := k) (k' := k') a idx rem acc
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

/-! ### `B3`, the call, and `B5`

These are simpler: `B3` and `B5` end in ordinary total macros rather than a block call, so they
need no interior states, and the call transition is a `callState` equality. -/

/-- `B3`: the argument reaches the step callee and both pairing blocks come back clean. -/
theorem run_precSeedStep (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (precSeedStep (k := k) (k' := k'))
          ⟨0, precState3 a idx rem acc⟩ m).pc <
        (precSeedStep (k := k) (k' := k')).length) ∧
      run (precSeedStep (k := k) (k' := k')) ⟨0, precState3 a idx rem acc⟩ N =
        ⟨(precSeedStep (k := k) (k' := k')).length, precState4 a idx rem acc⟩ := by
  rw [precSeedStep]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_copy (r := embedPairB k k' 2) (s := embedStep k k' 0) (t := rTmp k k')
        (by simp) (by simp) (by simp)).seq
      ((realises_clear (embedPairA k k' 0)).seq
        ((realises_clear (embedPairA k k' 1)).seq
          ((realises_clear (embedPairA k k' 2)).seq
            ((realises_clear (embedPairB k k' 0)).seq
              ((realises_clear (embedPairB k k' 1)).seq
                (realises_clear (embedPairB k k' 2))))))))
      (precState3 (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  have sset : ∀ i : Fin (k' + 1), i ≠ 0 → precState4 (k := k) (k' := k') a idx rem acc
      (embedStep k k' i) = 0 := by
    intro i hi
    simp [precState4, embedStep_injective.eq_iff, hi]
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · fin_cases i <;>
      simp [precState3, precState4, embedPairA_injective.eq_iff]
  · fin_cases i <;>
      simp [precState3, precState4, embedPairB_injective.eq_iff]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · by_cases hi : i = 0
    · subst hi; simp [precState3, precState4, embedPairB_injective.eq_iff]
    · simp [precState3, precState4, embedStep_injective.eq_iff, hi]

/-- The call's exit, as one register file. -/
theorem callState_precState4 (a idx rem acc acc' : ℕ) :
    callState (embedStep k k') (precState4 (k := k) (k' := k') a idx rem acc) acc' =
      precState5 a idx rem acc acc' := by
  classical
  funext r
  by_cases hrng : ∃ j, r = embedStep k k' j
  · obtain ⟨j, rfl⟩ := hrng
    rw [callState_apply embedStep_injective]
    by_cases hj : j = 0
    · subst hj; simp [precState5]
    · rw [unaryConfig_of_ne hj]
      simp [precState5, embedStep_injective.eq_iff, hj]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp [precState4, precState5, hrng 0]

/-- `B5`: the callee's answer becomes the accumulator, and the loop head is restored. -/
theorem run_precSaveAcc (a idx rem acc acc' : ℕ) :
    ∃ N, (∀ m < N, (run (precSaveAcc (k := k) (k' := k'))
          ⟨0, precState5 a idx rem acc acc'⟩ m).pc <
        (precSaveAcc (k := k) (k' := k')).length) ∧
      run (precSaveAcc (k := k) (k' := k')) ⟨0, precState5 a idx rem acc acc'⟩ N =
        ⟨(precSaveAcc (k := k) (k' := k')).length, precLoopState a idx rem acc'⟩ := by
  rw [precSaveAcc]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_clear (rAcc k k')).seq
      (realises_move (r := embedStep k k' 0) (s := rAcc k k') (by simp)))
      (precState5 (k := k) (k' := k') a idx rem acc acc')
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · by_cases hi : i = 0
    · subst hi; simp [precLoopState]
    · simp [precState5, precLoopState, embedStep_injective.eq_iff, hi]

end RegisterMachine

end Hilbert10
