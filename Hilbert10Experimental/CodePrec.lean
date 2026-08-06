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

`Fin (k + k' + 23)`:

| register | role |
|---|---|
| `0` | the input, and at the end the answer |
| `1` | the parameter `a` |
| `2` | the current index `k` |
| `3` | the remaining iterations `r` |
| `4` | the accumulator |
| `5` | the temporary `copy` borrows |
| `6`–`14` | one `pairMachine` block |
| `15`–`20` | one `unpairLoop` block |
| `21 …` | the base callee's block, then the step callee's |

**One pairing block, not two.** A turn pairs twice — `Nat.pair k acc`, then `Nat.pair a` of that
— but the two are sequential and `pairMachine` returns its scratch clean, so the same nine
registers serve both.

**The pairing writes to a register the step callee then reads, via `copy`.** Making
`pairMachine`'s result register *be* the callee's input would save that copy, but the two
embeddings would then overlap in one point, and every separation lemma below would acquire a case
split. The layout arithmetic is the thing this section exists to keep flat; one `copy` is the
cheaper side of that trade. -/

variable (k k')

/-- The parameter `a`. -/ def rA : Fin (k + k' + 23) := ⟨1, by omega⟩
/-- The current index. -/ def rK : Fin (k + k' + 23) := ⟨2, by omega⟩
/-- The remaining iterations. -/ def rR : Fin (k + k' + 23) := ⟨3, by omega⟩
/-- The accumulator. -/ def rAcc : Fin (k + k' + 23) := ⟨4, by omega⟩
/-- The temporary `copy` borrows. -/ def rTmp : Fin (k + k' + 23) := ⟨5, by omega⟩

/-- The shared `pairMachine` block. -/
def embedPair (i : Fin 9) : Fin (k + k' + 23) := ⟨6 + i.val, by omega⟩

/-- The `unpairLoop` block, used once on the way in. -/
def embedUnpair (i : Fin 6) : Fin (k + k' + 23) := ⟨15 + i.val, by omega⟩

/-- The base callee's block. -/
def embedBase (i : Fin (k + 1)) : Fin (k + k' + 23) := ⟨21 + i.val, by omega⟩

/-- The step callee's block. -/
def embedStep (j : Fin (k' + 1)) : Fin (k + k' + 23) := ⟨22 + k + j.val, by omega⟩

variable {k k'}

@[simp] theorem rA_val : (rA k k').val = 1 := rfl
@[simp] theorem rK_val : (rK k k').val = 2 := rfl
@[simp] theorem rR_val : (rR k k').val = 3 := rfl
@[simp] theorem rAcc_val : (rAcc k k').val = 4 := rfl
@[simp] theorem rTmp_val : (rTmp k k').val = 5 := rfl
@[simp] theorem embedPair_val (i : Fin 9) : (embedPair k k' i).val = 6 + i.val := rfl
@[simp] theorem embedUnpair_val (i : Fin 6) : (embedUnpair k k' i).val = 15 + i.val := rfl
@[simp] theorem embedBase_val (i : Fin (k + 1)) : (embedBase k k' i).val = 21 + i.val := rfl
@[simp] theorem embedStep_val (j : Fin (k' + 1)) : (embedStep k k' j).val = 22 + k + j.val := rfl

theorem embedPair_injective : Function.Injective (embedPair k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedUnpair_injective : Function.Injective (embedUnpair k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedBase_injective : Function.Injective (embedBase k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedStep_injective : Function.Injective (embedStep k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- **The layout is exhaustive.** Registers `0`–`5`, the pairing block, the unpairing block and
the two callee blocks account for every register: `6 + 9 + 6 + (k+1) + (k'+1) = k + k' + 23`. -/
theorem precLayout_cases (r : Fin (k + k' + 23)) :
    r = 0 ∨ r = rA k k' ∨ r = rK k k' ∨ r = rR k k' ∨ r = rAcc k k' ∨ r = rTmp k k' ∨
      (∃ i, r = embedPair k k' i) ∨ (∃ i, r = embedUnpair k k' i) ∨
      (∃ i, r = embedBase k k' i) ∨ ∃ j, r = embedStep k k' j := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨
      (6 ≤ r.val ∧ r.val ≤ 14) ∨ (15 ≤ r.val ∧ r.val ≤ 20) ∨
      (21 ≤ r.val ∧ r.val ≤ 21 + k) ∨ 22 + k ≤ r.val by omega)
    with h | h | h | h | h | h | h | h | h | h
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
      ⟨⟨r.val - 21, by omega⟩, Fin.ext (by simp; omega)⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 22 - k, by omega⟩, Fin.ext (by simp; omega)⟩))))))))

/-! ### Separation

Bundled the way #51's `entry_ne` was, one bundle per block rather than one lemma per pair: the
register case analysis quantifies over whole blocks, so that is the shape the proofs consume. -/

theorem precFixed_ne :
    (0 : Fin (k + k' + 23)) ≠ rA k k' ∧ (0 : Fin (k + k' + 23)) ≠ rK k k' ∧
    (0 : Fin (k + k' + 23)) ≠ rR k k' ∧ (0 : Fin (k + k' + 23)) ≠ rAcc k k' ∧
    (0 : Fin (k + k' + 23)) ≠ rTmp k k' ∧ rA k k' ≠ rK k k' ∧ rA k k' ≠ rR k k' ∧
    rA k k' ≠ rAcc k k' ∧ rA k k' ≠ rTmp k k' ∧ rK k k' ≠ rR k k' ∧ rK k k' ≠ rAcc k k' ∧
    rK k k' ≠ rTmp k k' ∧ rR k k' ≠ rAcc k k' ∧ rR k k' ≠ rTmp k k' ∧ rAcc k k' ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this)

theorem embedPair_ne_fixed (i : Fin 9) :
    embedPair k k' i ≠ 0 ∧ embedPair k k' i ≠ rA k k' ∧ embedPair k k' i ≠ rK k k' ∧
    embedPair k k' i ≠ rR k k' ∧ embedPair k k' i ≠ rAcc k k' ∧ embedPair k k' i ≠ rTmp k k' := by
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

theorem embedPair_ne_embedUnpair (i : Fin 9) (j : Fin 6) :
    embedPair k k' i ≠ embedUnpair k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPair_ne_embedBase (i : Fin 9) (j : Fin (k + 1)) :
    embedPair k k' i ≠ embedBase k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPair_ne_embedStep (i : Fin 9) (j : Fin (k' + 1)) :
    embedPair k k' i ≠ embedStep k k' j := by
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

/-! ### The loop head

The interface the whole loop is proved against, parameterised by the index and the accumulator
exactly as #51's `state1`–`state5` were parameterised by their contents.

The remaining count `rem` is what the loop branches on. There is no stored target and no
comparison: the `dec` that tests `rem` *is* the branch, so `idx ≤ n` never has to be maintained
and no residual has to be related back to the run length. -/

/-- The register file at a loop head. -/
def precLoopState (a idx rem acc : ℕ) : Fin (k + k' + 23) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc else 0

end RegisterMachine

end Hilbert10
