/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.RegisterMachineComp

/-!
# The exit contract

Issue #40. What a compiled program has to satisfy for #41 to be able to compose it.

A bare halting equivalence is too weak: `halts_append_of_exits` (#39) needs to know *where* a
program stops and *what* it leaves behind, not merely that it stops. So the contract is a single
predicate on runs:

```lean
Realises P F ↔ from every register file, `P` starts at 0, stays inside itself, exits at exactly
  `P.length`, and leaves the register file `F regs`
```

Two things follow from stating it this way rather than as a list of clauses.

*Output and preservation are one clause, not two.* `F` describes the whole final register file,
so a constructor's statement — say `fun regs => Function.update regs r 0` — says both what was
produced and that nothing else moved. There is no separate "owns these registers" side condition
to carry, and no way for the two halves to drift apart.

*It is exactly the hypothesis `halts_append_of_exits` wants.* `Realises.append` discharges that
lemma once and for all, so #41 composes machines without ever reasoning about program counters
again.

## Totality

`Realises` describes machines that always halt, which is what the constructors here are. `rfind'`
is the constructor that need not, and it will need a partial companion; that belongs to #43,
not to a predicate stretched in advance to accommodate it.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- `P` transforms the register file by `F`: from program counter `0` it stays inside itself,
exits at exactly `P.length`, and leaves `F regs`.

The exit position matters as much as the fact of halting. A program that jumps past its own end
would still halt, but concatenating it would drop control into the middle of whatever follows. -/
def Realises (P : Program k) (F : (Fin k → ℕ) → Fin k → ℕ) : Prop :=
  ∀ regs : Fin k → ℕ, ∃ n,
    (∀ m < n, (run P ⟨0, regs⟩ m).pc < P.length) ∧
      run P ⟨0, regs⟩ n = ⟨P.length, F regs⟩

theorem Realises.halts {P : Program k} {F} (h : Realises P F) (regs : Fin k → ℕ) :
    Halts P ⟨0, regs⟩ := by
  obtain ⟨n, _, hn⟩ := h regs
  exact ⟨n, by rw [hn]; exact Nat.le_refl _⟩

theorem Realises.congr {P : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ} (h : Realises P F)
    (hFG : ∀ regs, F regs = G regs) : Realises P G := by
  intro regs
  obtain ⟨n, hin, hex⟩ := h regs
  exact ⟨n, hin, by rw [hex, hFG]⟩

/-- The empty program realises the identity. It is the unit for `Realises.append`. -/
theorem realises_nil : Realises ([] : Program k) id := fun _ => ⟨0, by omega, rfl⟩

/-- **Sequencing.** This is the lemma #41 consumes: composing realised machines needs no
reasoning about program counters at the call site. -/
theorem Realises.append {P Q : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ}
    (hP : Realises P F) (hQ : Realises Q G) :
    Realises (P ++ shiftJumps P.length Q) fun regs => G (F regs) := by
  intro regs
  obtain ⟨nP, hPin, hPex⟩ := hP regs
  obtain ⟨nQ, hQin, hQex⟩ := hQ (F regs)
  have hlen : (P ++ shiftJumps P.length Q).length = P.length + Q.length := by simp
  -- control reaches the join at step `nP`, with the register file `P` produced
  have hmid : run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ nP = ⟨0 + P.length, F regs⟩ := by
    rw [run_append_of_lt hPin, hPex, Nat.zero_add]
  -- afterwards the run is `Q`'s, offset by `P.length`
  have hafter : ∀ j, run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ (nP + j) =
      ⟨(run Q ⟨0, F regs⟩ j).pc + P.length, (run Q ⟨0, F regs⟩ j).regs⟩ := by
    intro j
    rw [run_add, hmid, run_append_shiftJumps]
  refine ⟨nP + nQ, fun m hm => ?_, ?_⟩
  · by_cases hmP : m < nP
    · rw [run_append_of_lt fun j hj => hPin j (Nat.lt_trans hj hmP)]
      exact Nat.lt_of_lt_of_le (hPin m hmP) (hlen ▸ Nat.le_add_right _ _)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp hmP)
      have hj := hQin j (by omega)
      rw [hafter j, hlen]
      -- the goal projects out of a `Config` literal, which `omega` treats as an opaque atom
      exact show (run Q ⟨0, F regs⟩ j).pc + P.length < P.length + Q.length by omega
  · rw [hafter nQ, hQex, hlen]
    simp [Nat.add_comm]

/-! ## Primitive machines

The two one-instruction programs. `incr` exercises the exit contract on a straight-line
program, `clear` on a loop, and `Realises.append` glues them; nothing here needs a
well-formedness predicate, a register allocator, or a name supply. -/

/-- Increment register `r`. -/
def incr (r : Fin k) : Program k := [.inc r 1]

theorem realises_incr (r : Fin k) :
    Realises (incr r) fun regs => Function.update regs r (regs r + 1) := by
  intro regs
  refine ⟨1, fun m hm => ?_, ?_⟩
  · rw [Nat.lt_one_iff.mp hm]
    exact Nat.zero_lt_one
  · rw [run_succ, run_zero, step_of_getElem? (i := .inc r 1) rfl]
    rfl

/-- Set register `r` to zero, by decrementing until it is. -/
def clear (r : Fin k) : Program k := [.dec r 0 1]

private theorem run_clear (r : Fin k) (regs : Fin k → ℕ) :
    ∀ j ≤ regs r, run (clear r) ⟨0, regs⟩ j = ⟨0, Function.update regs r (regs r - j)⟩ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hlt : j < regs r := by omega
    rw [run_succ, ih (by omega), step_of_getElem? (i := .dec r 0 1) rfl]
    have hval : Function.update regs r (regs r - j) r = regs r - j := by simp
    simp only [Instr.exec, hval]
    rw [if_neg (by omega), Function.update_idem,
      show regs r - j - 1 = regs r - (j + 1) by omega]

theorem realises_clear (r : Fin k) :
    Realises (clear r) fun regs => Function.update regs r 0 := by
  intro regs
  refine ⟨regs r + 1, fun m hm => ?_, ?_⟩
  · rw [run_clear r regs m (by omega)]
    exact Nat.zero_lt_one
  · rw [run_succ, run_clear r regs _ (Nat.le_refl _), step_of_getElem? (i := .dec r 0 1) rfl]
    simp [Instr.exec, clear]

/-! ## The constructors

`Nat.Partrec.Code` denotes unary functions, so a compiled machine reads its input from and
writes its result to register `0`. `ComputesUnary` fixes that convention, and by being stated
through `Function.update` it says in the same breath that every other register survives. -/

/-- `P` computes the unary function `f` in register `0`, leaving every other register alone. -/
def ComputesUnary (P : Program (k + 1)) (f : ℕ → ℕ) : Prop :=
  Realises P fun regs => Function.update regs 0 (f (regs 0))

/-- The machine for `Nat.Partrec.Code.zero`. -/
def zeroMachine (k : ℕ) : Program (k + 1) := clear 0

theorem computesUnary_zeroMachine : ComputesUnary (zeroMachine k) fun _ => 0 :=
  realises_clear 0

/-- The machine for `Nat.Partrec.Code.succ`. -/
def succMachine (k : ℕ) : Program (k + 1) := incr 0

theorem computesUnary_succMachine : ComputesUnary (succMachine k) fun n => n + 1 :=
  realises_incr 0

/-! ## A composite

`clear` then `incr`, on the same register: the first machine whose run genuinely moves through a
concatenation, and a check that `Realises.append` is usable without unfolding it. -/

example (r : Fin k) :
    Realises (clear r ++ shiftJumps (clear r).length (incr r))
      fun regs => Function.update regs r 1 := by
  refine ((realises_clear r).append (realises_incr r)).congr fun regs => ?_
  simp

end RegisterMachine

end Hilbert10
