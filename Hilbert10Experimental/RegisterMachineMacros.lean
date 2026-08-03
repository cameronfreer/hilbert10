/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.RegisterMachineRealises

/-!
# Register plumbing

Issue #51, step 2. The total macros the pairing machines are built from.

Each is stated as a `Realises` fact with an explicit whole-register transformation, so the
statement says at once what was produced *and* that every temporary was left at zero. A macro
that returned the right value while leaving a counter dirty would not typecheck against these
statements, which is the point: the clean-scratch convention of `CleanScratch` is only worth
something if the macros actually give back what they borrow.

Every macro takes the registers it uses as arguments, with distinctness as explicit hypotheses.
There is no allocator and no name supply here, per the standing guard from #39.

## Proving loops

Two small pieces of technique, both learned the hard way.

`step_dec_pos`, `step_dec_zero` and `step_inc` turn one machine step into one equation about
register files, so a loop body becomes a chain of rewrites rather than a nest of `step`
applications.

Each loop's body is proved *once*, for an arbitrary register file, as a `run … c p` fact for the
body's length `p`. The induction over turns of the loop then goes through `run_add`, never
through `run_succ`. This matters: `Config` is a structure, so structure eta lets the pattern
`step P ⟨p, regs⟩` match *any* `step P c`, and `rw` will happily aim a step lemma at the
outermost step of a nest instead of the innermost one.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

theorem run_one (P : Program k) (c : Config k) : run P c 1 = step P c := rfl

theorem step_dec_pos {P : Program k} {r : Fin k} {a b p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.dec r a b)) (h : regs r ≠ 0) :
    step P ⟨p, regs⟩ = ⟨a, Function.update regs r (regs r - 1)⟩ := by
  rw [step_of_getElem? hp]
  simp [Instr.exec, h]

theorem step_dec_zero {P : Program k} {r : Fin k} {a b p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.dec r a b)) (h : regs r = 0) : step P ⟨p, regs⟩ = ⟨b, regs⟩ := by
  rw [step_of_getElem? hp]
  simp [Instr.exec, h]

theorem step_inc {P : Program k} {r : Fin k} {a p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.inc r a)) :
    step P ⟨p, regs⟩ = ⟨a, Function.update regs r (regs r + 1)⟩ := by
  rw [step_of_getElem? hp]
  rfl

/-- Sequential composition: `++` with the second program relocated. Named because the macros
below chain four of them and the raw form is unreadable at that length. -/
def seq (P Q : Program k) : Program k := P ++ shiftJumps P.length Q

@[simp] theorem length_seq (P Q : Program k) : (seq P Q).length = P.length + Q.length :=
  length_append_shiftJumps P Q

theorem Realises.seq {P Q : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ} (hP : Realises P F)
    (hQ : Realises Q G) : Realises (RegisterMachine.seq P Q) fun regs => G (F regs) :=
  hP.append hQ

/-! ## Moving

`move` empties one register into another; `moveTwo` empties it into two at once, which is what
makes a non-destructive copy possible. -/

/-- Add `r` into `s`, leaving `r` at zero. -/
def move (r s : Fin k) : Program k := [.dec r 1 2, .inc s 0]

/-- The register file after `j` turns of `move`'s loop. -/
private def moveState (r s : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = r then regs r - j else if i = s then regs s + j else regs i

/-- One turn of `move`'s loop, for an arbitrary register file. -/
private theorem run_move_body {r s : Fin k} (hrs : r ≠ s) (R : Fin k → ℕ) (hR : R r ≠ 0) :
    run (move r s) ⟨0, R⟩ 2 =
      ⟨0, fun i => if i = r then R r - 1 else if i = s then R s + 1 else R i⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
    step_dec_pos (P := move r s) (b := 2) rfl hR,
    step_inc (P := move r s) (p := 1) (a := 0) rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem run_move {r s : Fin k} (hrs : r ≠ s) (regs : Fin k → ℕ) : ∀ j ≤ regs r,
    run (move r s) ⟨0, regs⟩ (2 * j) = ⟨0, moveState r s regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [moveState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hval : moveState r s regs j r = regs r - j := by simp [moveState]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, run_add, ih (by omega),
      run_move_body hrs _ (by rw [hval]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [moveState]
    split_ifs <;> simp_all <;> omega

private theorem pc_run_move {r s : Fin k} (hrs : r ≠ s) (regs : Fin k → ℕ) :
    ∀ m < 2 * regs r + 1, (run (move r s) ⟨0, regs⟩ m).pc < (move r s).length := by
  intro m hm
  obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 2 ∧ m = 2 * j + c :=
    ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
  have hval : moveState r s regs j r = regs r - j := by simp [moveState]
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · rw [Nat.add_zero, run_move hrs regs j (by omega)]
    simp [move]
  · rw [run_add, run_move hrs regs j (by omega), run_one,
      step_dec_pos (P := move r s) (b := 2) rfl (by rw [hval]; omega)]
    simp [move]

theorem realises_move {r s : Fin k} (hrs : r ≠ s) :
    Realises (move r s) fun regs i =>
      if i = r then 0 else if i = s then regs s + regs r else regs i := by
  intro regs
  refine ⟨2 * regs r + 1, pc_run_move hrs regs, ?_⟩
  have hval : moveState r s regs (regs r) r = 0 := by simp [moveState]
  rw [run_add, run_move hrs regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := move r s) (a := 1) rfl hval, show (move r s).length = 2 from rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [moveState]
  split_ifs <;> simp_all

/-- Add `r` into both `s` and `t`, leaving `r` at zero. -/
def moveTwo (r s t : Fin k) : Program k := [.dec r 1 3, .inc s 2, .inc t 0]

/-- The register file after `j` turns of `moveTwo`'s loop. -/
private def moveTwoState (r s t : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = r then regs r - j else if i = s then regs s + j
    else if i = t then regs t + j else regs i

/-- One turn of `moveTwo`'s loop, for an arbitrary register file. -/
private theorem run_moveTwo_body {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (R : Fin k → ℕ) (hR : R r ≠ 0) :
    run (moveTwo r s t) ⟨0, R⟩ 3 =
      ⟨0, fun i => if i = r then R r - 1 else if i = s then R s + 1
        else if i = t then R t + 1 else R i⟩ := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, run_add, run_add, run_one, run_one, run_one,
    step_dec_pos (P := moveTwo r s t) (b := 3) rfl hR,
    step_inc (P := moveTwo r s t) (p := 1) (a := 2) rfl,
    step_inc (P := moveTwo r s t) (p := 2) (a := 0) rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem run_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (regs : Fin k → ℕ) : ∀ j ≤ regs r,
    run (moveTwo r s t) ⟨0, regs⟩ (3 * j) = ⟨0, moveTwoState r s t regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [moveTwoState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hval : moveTwoState r s t regs j r = regs r - j := by simp [moveTwoState]
    rw [show 3 * (j + 1) = 3 * j + 3 by omega, run_add, ih (by omega),
      run_moveTwo_body hrs hrt hst _ (by rw [hval]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [moveTwoState]
    split_ifs <;> simp_all <;> omega

private theorem pc_run_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (regs : Fin k → ℕ) : ∀ m < 3 * regs r + 1,
    (run (moveTwo r s t) ⟨0, regs⟩ m).pc < (moveTwo r s t).length := by
  intro m hm
  obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 3 ∧ m = 3 * j + c :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by omega), by omega⟩
  have hjr : j ≤ regs r := by omega
  have hval : moveTwoState r s t regs j r = regs r - j := by simp [moveTwoState]
  -- `hstep` is only available once we know the loop has not already exited, which is exactly
  -- the case `c ≠ 0`: at `c = 0` the machine is sitting on the zero test.
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
  · rw [Nat.add_zero, run_moveTwo hrs hrt hst regs j hjr]
    simp [moveTwo]
  · rw [run_add, run_moveTwo hrs hrt hst regs j hjr, run_one,
      step_dec_pos (P := moveTwo r s t) (b := 3) rfl (by rw [hval]; omega)]
    simp [moveTwo]
  · rw [show 3 * j + 2 = 3 * j + 1 + 1 by omega, run_add, run_add,
      run_moveTwo hrs hrt hst regs j hjr, run_one, run_one,
      step_dec_pos (P := moveTwo r s t) (regs := moveTwoState r s t regs j) (b := 3) rfl
        (by rw [hval]; omega),
      step_inc (P := moveTwo r s t) (p := 1) (a := 2) rfl]
    simp [moveTwo]

theorem realises_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Realises (moveTwo r s t) fun regs i => if i = r then 0 else if i = s then regs s + regs r
      else if i = t then regs t + regs r else regs i := by
  intro regs
  refine ⟨3 * regs r + 1, pc_run_moveTwo hrs hrt hst regs, ?_⟩
  have hval : moveTwoState r s t regs (regs r) r = 0 := by simp [moveTwoState]
  rw [run_add, run_moveTwo hrs hrt hst regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := moveTwo r s t) (a := 1) rfl hval,
    show (moveTwo r s t).length = 3 from rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [moveTwoState]
  split_ifs <;> simp_all

/-! ## Copying

`copy` is the first macro whose statement carries a cleanliness claim: `t` is borrowed as working
storage and handed back at zero, whatever it held before. -/

/-- Copy `r` into `s`, using `t` as working storage and returning it at zero. `r` is unchanged. -/
def copy (r s t : Fin k) : Program k :=
  seq (clear s) (seq (clear t) (seq (moveTwo r s t) (move t r)))

theorem realises_copy {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Realises (copy r s t) fun regs i =>
      if i = s then regs r else if i = t then 0 else regs i := by
  refine (((realises_clear s).seq ((realises_clear t).seq
    ((realises_moveTwo hrs hrt hst).seq (realises_move (Ne.symm hrt))))).congr fun regs => ?_)
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end RegisterMachine

end Hilbert10
