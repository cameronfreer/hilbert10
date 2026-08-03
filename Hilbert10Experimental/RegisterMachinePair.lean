/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.RegisterMachineUnpair

/-!
# `Nat.pair` by walking the enumeration

Issue #51, step 5. Enumerate from `(0, 0)`, counting steps, until the candidate is the target.
`Nat.iterate_pairNext_pair` says that happens after exactly `Nat.pair a b` steps, so the loop
terminates and the count is the answer. No unbounded search and no `rfind'`.

## Layout

`Fin 9`:

| register | role |
|---|---|
| `0`, `1` | the target pair, preserved |
| `2` | the step count, and the result |
| `3`, `4` | the candidate pair |
| `5` | accumulated distance from candidate to target |
| `6`, `7`, `8` | `compare`'s residuals and temporary |

**On the extra register.** Testing a *pair* for equality needs two comparisons, and `compare`
needs three scratch registers of its own, which is eight before an accumulator. With one more the
loop body is a straight line ending in a single branch, and its proof is one splice. Testing the
coordinates separately fits in eight registers but branches forward out of the middle of the
body from two places, giving four entry paths into the advance block and four splices. The
register is cheaper than the proof.

## The loop

```
0 … T-1    measure the distance into register 5
T          decrement 5; positive → drain and advance, zero → exit
T+1        drain the rest of 5
T+2 … T+M+1  the relocated pairNextMachine
T+M+2      increment the count, jump back to 0
```

The advance block cleans registers `6`, `7`, `8` whatever they held, so the drain at `T+1` is the
only cleanup the loop performs — the measurement's leftovers are somebody else's problem, and
that somebody already handles them.
-/

namespace Hilbert10

namespace RegisterMachine

/-! ## Measuring the distance -/

/-- Add the coordinatewise distance from `(3, 4)` to `(0, 1)` into register `5`. -/
def measure : Program 9 :=
  seq (compare 3 0 6 7 8)
    (seq (move 6 5) (seq (move 7 5)
      (seq (compare 4 1 6 7 8) (seq (move 6 5) (move 7 5)))))

theorem realises_measure : Realises measure fun regs i =>
    if i = 5 then regs 5 + ((regs 0 - regs 3) + (regs 3 - regs 0))
        + ((regs 1 - regs 4) + (regs 4 - regs 1))
      else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0 else regs i := by
  refine (((realises_compare (a := 3) (b := 0) (lo := 6) (hi := 7) (tmp := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).seq
      ((realises_move (show (6 : Fin 9) ≠ 5 by decide)).seq
        ((realises_move (show (7 : Fin 9) ≠ 5 by decide)).seq
          ((realises_compare (a := 4) (b := 1) (lo := 6) (hi := 7) (tmp := 8)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).seq
              ((realises_move (show (6 : Fin 9) ≠ 5 by decide)).seq
                (realises_move (show (7 : Fin 9) ≠ 5 by decide))))))).congr fun regs => ?_)
  funext i
  fin_cases i <;> simp
  all_goals omega

/-! ## Advancing the candidate -/

/-- Where `pairNextMachine`'s five registers go: the candidate pair and the top three scratch
registers. The accumulator, register `5`, is deliberately outside the block. -/
def pairAdvanceIdx (i : Fin 5) : Fin 9 :=
  if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 6 else if i = 3 then 7 else 8

def pairAdvance : Program 9 := renameRegs pairAdvanceIdx pairNextMachine

theorem realises_pairAdvance : Realises pairAdvance fun regs i =>
    if i = 3 then (Nat.pairNext (regs 3, regs 4)).1
    else if i = 4 then (Nat.pairNext (regs 3, regs 4)).2
    else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0 else regs i := by
  refine realises_pairNextMachine.renameRegs
    (show Function.Injective pairAdvanceIdx by decide) ?_ ?_
  · intro regs i
    fin_cases i <;> simp [pairAdvanceIdx]
  · intro regs r hr
    have h3 : r ≠ 3 := by simpa [pairAdvanceIdx] using hr 0
    have h4 : r ≠ 4 := by simpa [pairAdvanceIdx] using hr 1
    have h6 : r ≠ 6 := by simpa [pairAdvanceIdx] using hr 2
    have h7 : r ≠ 7 := by simpa [pairAdvanceIdx] using hr 3
    have h8 : r ≠ 8 := by simpa [pairAdvanceIdx] using hr 4
    simp [h3, h4, h6, h7, h8]

/-- The distance is zero exactly when the candidate is the target. -/
theorem measure_eq_zero_iff (regs : Fin 9 → ℕ) :
    ((regs 0 - regs 3) + (regs 3 - regs 0)) + ((regs 1 - regs 4) + (regs 4 - regs 1)) = 0 ↔
      (regs 3, regs 4) = (regs 0, regs 1) := by
  rw [Prod.mk.injEq]
  omega

end RegisterMachine

end Hilbert10
