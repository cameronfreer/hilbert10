/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.RegisterMachineComp
import Mathlib.Data.PFun

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

`Realises` describes machines that always halt, which is what the constructors here are, and it
stays the right contract for total macros: register plumbing, and later the pairing arithmetic
of #51.

It is *not* enough for the compiler. `rfind'` is where divergence originates, but divergence
propagates: `comp cf cg` diverges wherever `cg` does, and so does `prec`, and so does `pair`. So
the recursive compilation already needs a partial contract at #41, not at #43. `PartRealises`
below is that companion, and `Realises.toPartRealises` embeds the total machines into it.
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

theorem length_append_shiftJumps (P Q : Program k) :
    (P ++ shiftJumps P.length Q).length = P.length + Q.length := by simp

/-- Once the prefix has exited into the join, the rest of the concatenation's run is `Q`'s,
offset by `P.length`. -/
theorem run_join {P Q : Program k} {regs mid : Fin k → ℕ} {nP : ℕ}
    (hPin : ∀ m < nP, (run P ⟨0, regs⟩ m).pc < P.length)
    (hPex : run P ⟨0, regs⟩ nP = ⟨P.length, mid⟩) (j : ℕ) :
    run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ (nP + j) =
      ⟨(run Q ⟨0, mid⟩ j).pc + P.length, (run Q ⟨0, mid⟩ j).regs⟩ := by
  have hmid : run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ nP = ⟨0 + P.length, mid⟩ := by
    rw [run_append_of_lt hPin, hPex, Nat.zero_add]
  rw [run_add, hmid, run_append_shiftJumps]

/-- Two exact exits splice into one. Shared by the total and partial sequencing lemmas, which
differ only in where the two halves' data comes from. -/
theorem join_exit {P Q : Program k} {regs mid out : Fin k → ℕ} {nP nQ : ℕ}
    (hPin : ∀ m < nP, (run P ⟨0, regs⟩ m).pc < P.length)
    (hPex : run P ⟨0, regs⟩ nP = ⟨P.length, mid⟩)
    (hQin : ∀ m < nQ, (run Q ⟨0, mid⟩ m).pc < Q.length)
    (hQex : run Q ⟨0, mid⟩ nQ = ⟨Q.length, out⟩) :
    (∀ m < nP + nQ, (run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ m).pc <
        (P ++ shiftJumps P.length Q).length) ∧
      run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ (nP + nQ) =
        ⟨(P ++ shiftJumps P.length Q).length, out⟩ := by
  have hlen := length_append_shiftJumps P Q
  refine ⟨fun m hm => ?_, ?_⟩
  · by_cases hmP : m < nP
    · rw [run_append_of_lt fun j hj => hPin j (Nat.lt_trans hj hmP)]
      exact Nat.lt_of_lt_of_le (hPin m hmP) (hlen ▸ Nat.le_add_right _ _)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp hmP)
      have hj := hQin j (by omega)
      rw [run_join hPin hPex j, hlen]
      -- the goal projects out of a `Config` literal, which `omega` treats as an opaque atom
      exact show (run Q ⟨0, mid⟩ j).pc + P.length < P.length + Q.length by omega
  · rw [run_join hPin hPex nQ, hQex, hlen]
    simp [Nat.add_comm]

/-- **Sequencing.** Composing realised machines needs no reasoning about program counters at
the call site. -/
theorem Realises.append {P Q : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ}
    (hP : Realises P F) (hQ : Realises Q G) :
    Realises (P ++ shiftJumps P.length Q) fun regs => G (F regs) := by
  intro regs
  obtain ⟨nP, hPin, hPex⟩ := hP regs
  obtain ⟨nQ, hQin, hQex⟩ := hQ (F regs)
  exact ⟨nP + nQ, join_exit hPin hPex hQin hQex⟩

/-! ## The partial contract

`rfind'` is where divergence originates, but it propagates: `comp cf cg` diverges wherever `cg`
does, and so do `prec` and `pair`. So the recursive compilation needs this companion from #41
onward, and `Realises` remains the contract for total macros. -/

/-- `P` partially transforms the register file by `F`.

Both clauses are load-bearing. Every value of `F` is reached by an *exact* exit at `P.length`;
and conversely, whenever `P` halts at all, `F` is defined there.

The converse clause is what rules out halting by jumping past the end. Without it a machine
could satisfy the first clause vacuously on an input where `F` diverges and still stop, and
concatenating that machine would drop control into the middle of whatever follows. -/
def PartRealises (P : Program k) (F : (Fin k → ℕ) →. (Fin k → ℕ)) : Prop :=
  ∀ regs : Fin k → ℕ,
    (∀ out ∈ F regs, ∃ n, (∀ m < n, (run P ⟨0, regs⟩ m).pc < P.length) ∧
        run P ⟨0, regs⟩ n = ⟨P.length, out⟩) ∧
      (Halts P ⟨0, regs⟩ → (F regs).Dom)

theorem PartRealises.exit {P : Program k} {F} (h : PartRealises P F) {regs out}
    (hout : out ∈ F regs) :
    ∃ n, (∀ m < n, (run P ⟨0, regs⟩ m).pc < P.length) ∧
      run P ⟨0, regs⟩ n = ⟨P.length, out⟩ :=
  (h regs).1 out hout

theorem PartRealises.dom {P : Program k} {F} (h : PartRealises P F) {regs}
    (hh : Halts P ⟨0, regs⟩) : (F regs).Dom :=
  (h regs).2 hh

/-- Halting and convergence coincide — the statement the two clauses exist to make true. -/
theorem PartRealises.halts_iff {P : Program k} {F} (h : PartRealises P F) (regs : Fin k → ℕ) :
    Halts P ⟨0, regs⟩ ↔ (F regs).Dom := by
  refine ⟨h.dom, fun hd => ?_⟩
  obtain ⟨n, _, hn⟩ := h.exit (Part.get_mem hd)
  exact ⟨n, by rw [hn]; exact Nat.le_refl _⟩

/-- The second clause is not redundant. `[inc r 5]` halts by jumping past its own end, and on an
input where the intended function diverges the first clause is vacuous — so only the converse
clause rejects it. -/
example (r : Fin k) (regs : Fin k → ℕ) :
    ¬ PartRealises [Instr.inc r 5] fun _ => (Part.none : Part (Fin k → ℕ)) := by
  intro h
  refine (h regs).2 ⟨1, ?_⟩
  rw [run_succ, run_zero, step_of_getElem? (i := .inc r 5) rfl]
  simp [Halted, Instr.exec]

theorem PartRealises.congr {P : Program k} {F G : (Fin k → ℕ) →. (Fin k → ℕ)}
    (h : PartRealises P F) (hFG : ∀ regs, F regs = G regs) : PartRealises P G := by
  intro regs
  rw [← hFG]
  exact h regs

/-- A total machine is a partial one. -/
theorem Realises.toPartRealises {P : Program k} {F} (h : Realises P F) :
    PartRealises P fun regs => Part.some (F regs) := by
  refine fun regs => ⟨fun out hout => ?_, fun _ => trivial⟩
  have hEq : out = F regs := by simpa using hout
  subst hEq
  exact h regs

/-- If a concatenation halts then its prefix does: a run that never leaves `P` never leaves
`P ++ R` either. -/
theorem halts_prefix_of_halts_append {P R : Program k} {c : Config k} (h : Halts (P ++ R) c) :
    Halts P c := by
  by_contra hn
  simp only [Halts, not_exists] at hn
  have hlt : ∀ m, (run P c m).pc < P.length := fun m => Nat.lt_of_not_le (hn m)
  obtain ⟨N, hN⟩ := h
  rw [run_append_of_lt fun j _ => hlt j] at hN
  exact absurd hN (Nat.not_le.mpr (Nat.lt_of_lt_of_le (hlt N) (by simp)))

/-- **Partial sequencing**, realising Kleisli composition. This is what #41 consumes for
`Code.comp`, where either half may diverge. -/
theorem PartRealises.append {P Q : Program k} {F G : (Fin k → ℕ) →. (Fin k → ℕ)}
    (hP : PartRealises P F) (hQ : PartRealises Q G) :
    PartRealises (P ++ shiftJumps P.length Q) fun regs => F regs >>= G := by
  refine fun regs => ⟨fun out hout => ?_, fun hh => ?_⟩
  · obtain ⟨mid, hmid, hout'⟩ := Part.mem_bind_iff.mp hout
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hmid
    obtain ⟨nQ, hQin, hQex⟩ := hQ.exit hout'
    exact ⟨nP + nQ, join_exit hPin hPex hQin hQex⟩
  · -- the concatenation halted, so the prefix did, so `F regs` converges
    have hFd : (F regs).Dom := hP.dom (halts_prefix_of_halts_append hh)
    have hmid : (F regs).get hFd ∈ F regs := Part.get_mem hFd
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hmid
    obtain ⟨N, hN⟩ := hh
    -- it cannot have halted before reaching the join, since the prefix stays in range there
    have hNge : nP ≤ N := by
      by_contra hlt
      rw [run_append_of_lt fun j hj => hPin j (Nat.lt_trans hj (Nat.not_le.mp hlt))] at hN
      exact absurd hN (Nat.not_le.mpr (Nat.lt_of_lt_of_le (hPin N (Nat.not_le.mp hlt)) (by simp)))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hNge
    rw [run_join hPin hPex j] at hN
    have hQh : Halts Q ⟨0, (F regs).get hFd⟩ := by
      refine ⟨j, ?_⟩
      have hle : (P ++ shiftJumps P.length Q).length
          ≤ (run Q ⟨0, (F regs).get hFd⟩ j).pc + P.length := hN
      rw [length_append_shiftJumps] at hle
      exact show Q.length ≤ (run Q ⟨0, (F regs).get hFd⟩ j).pc by omega
    have hGd := hQ.dom hQh
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_bind hmid (Part.get_mem hGd)⟩

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

/-- `P` computes the unary partial function `f` in register `0`, leaving every other register
alone wherever it converges. -/
def PartComputesUnary (P : Program (k + 1)) (f : ℕ →. ℕ) : Prop :=
  PartRealises P fun regs => (f (regs 0)).map fun y => Function.update regs 0 y

theorem ComputesUnary.toPart {P : Program (k + 1)} {f : ℕ → ℕ} (h : ComputesUnary P f) :
    PartComputesUnary P fun n => Part.some (f n) :=
  h.toPartRealises.congr fun regs => by simp

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
