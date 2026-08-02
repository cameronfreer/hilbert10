/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.RegisterMachineRealises

/-!
# The clean-scratch calling convention

`PartComputesUnary` makes every register except `0` caller-owned: a machine must work from
arbitrary contents and give them back unchanged. That is the right contract for `zero`, `succ`
and for composition, but it is the wrong one for a machine that needs working storage.

A machine with counters has two bad options under it. Assuming the counters start at zero would
be a silent extra hypothesis, true of the callers we happen to write and invisible in the
statement. Saving and restoring arbitrary contents would be a large amount of work about a
question nobody asked.

So there is a second contract. The caller hands over a *clean* register file — input in `0`, the
rest zero — and gets one back in the same shape. `CleanPartComputesUnary` says exactly that.

## The call lemma

`CleanPartComputesUnary.call` is what makes the convention usable. Renaming along a
caller-supplied injection gives the callee a private scratch block that starts and ends zero,
while every register outside the block is preserved. Controller state therefore lives *outside*
the callee's image, which is the arrangement `prec` (#42) will need: a loop counter the callee
cannot see, and a callee that cannot leak into it.

The injection is still supplied by the caller, so this introduces no allocator — the standing
guard from #39.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- The register file a clean machine is called with, and returns: the value in register `0` and
zero everywhere else. -/
def unaryConfig (k : ℕ) (x : ℕ) : Fin (k + 1) → ℕ := Function.update (fun _ => 0) 0 x

@[simp] theorem unaryConfig_zero (k x : ℕ) : unaryConfig k x 0 = x := by simp [unaryConfig]

theorem unaryConfig_of_ne {x : ℕ} {i : Fin (k + 1)} (h : i ≠ 0) : unaryConfig k x i = 0 := by
  simp [unaryConfig, h]

@[simp] theorem update_unaryConfig (k x y : ℕ) :
    Function.update (unaryConfig k x) 0 y = unaryConfig k y := by
  simp [unaryConfig, Function.update_idem]

/-- `P` computes `f` from a clean register file to a clean register file. -/
def CleanPartComputesUnary (P : Program (k + 1)) (f : ℕ →. ℕ) : Prop :=
  ∀ x : ℕ,
    (∀ y ∈ f x, ∃ n, (∀ m < n, (run P ⟨0, unaryConfig k x⟩ m).pc < P.length) ∧
        run P ⟨0, unaryConfig k x⟩ n = ⟨P.length, unaryConfig k y⟩) ∧
      (Halts P ⟨0, unaryConfig k x⟩ → (f x).Dom)

theorem CleanPartComputesUnary.exit {P : Program (k + 1)} {f} (h : CleanPartComputesUnary P f)
    {x y : ℕ} (hy : y ∈ f x) :
    ∃ n, (∀ m < n, (run P ⟨0, unaryConfig k x⟩ m).pc < P.length) ∧
      run P ⟨0, unaryConfig k x⟩ n = ⟨P.length, unaryConfig k y⟩ :=
  (h x).1 y hy

theorem CleanPartComputesUnary.dom {P : Program (k + 1)} {f} (h : CleanPartComputesUnary P f)
    {x : ℕ} (hh : Halts P ⟨0, unaryConfig k x⟩) : (f x).Dom :=
  (h x).2 hh

/-- Halting from a clean register file is convergence. As in `PartRealises`, only one direction
is taken as the definition; the other follows from the exit clause. -/
theorem CleanPartComputesUnary.halts_iff {P : Program (k + 1)} {f}
    (h : CleanPartComputesUnary P f) (x : ℕ) :
    Halts P ⟨0, unaryConfig k x⟩ ↔ (f x).Dom := by
  refine ⟨h.dom, fun hd => ?_⟩
  obtain ⟨n, _, hn⟩ := h.exit (Part.get_mem hd)
  exact ⟨n, by rw [hn]; exact Nat.le_refl _⟩

theorem CleanPartComputesUnary.congr {P : Program (k + 1)} {f g : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) (hfg : ∀ x, f x = g x) : CleanPartComputesUnary P g := by
  intro x
  rw [← hfg]
  exact h x

/-- The framed contract is the stronger one: a machine that tolerates arbitrary scratch in
particular tolerates clean scratch. -/
theorem PartComputesUnary.toClean {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : PartComputesUnary P f) : CleanPartComputesUnary P f := by
  intro x
  refine ⟨fun y hy => ?_, fun hh => ?_⟩
  · have hy' : y ∈ f (unaryConfig k x 0) := by simpa using hy
    obtain ⟨n, hin, hex⟩ := h.exit (regs := unaryConfig k x)
      (Part.mem_map (fun z => Function.update (unaryConfig k x) 0 z) hy')
    exact ⟨n, hin, by rw [hex]; simp⟩
  · have hd : (f (unaryConfig k x 0)).Dom := h.dom hh
    simpa using hd

/-- Clean contracts compose, by the same splicing argument as `PartRealises.append`. -/
theorem CleanPartComputesUnary.comp {P Q : Program (k + 1)} {inner outer : ℕ →. ℕ}
    (hP : CleanPartComputesUnary P inner) (hQ : CleanPartComputesUnary Q outer) :
    CleanPartComputesUnary (P ++ shiftJumps P.length Q) fun x => inner x >>= outer := by
  intro x
  refine ⟨fun z hz => ?_, fun hh => ?_⟩
  · obtain ⟨y, hy, hz'⟩ := Part.mem_bind_iff.mp hz
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hy
    obtain ⟨nQ, hQin, hQex⟩ := hQ.exit hz'
    exact ⟨nP + nQ, join_exit hPin hPex hQin hQex⟩
  · have hPd : (inner x).Dom := hP.dom (halts_prefix_of_halts_append hh)
    have hy : (inner x).get hPd ∈ inner x := Part.get_mem hPd
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hy
    obtain ⟨N, hN⟩ := hh
    have hNge : nP ≤ N := by
      by_contra hlt
      rw [run_append_of_lt fun j hj => hPin j (Nat.lt_trans hj (Nat.not_le.mp hlt))] at hN
      exact absurd hN (Nat.not_le.mpr (Nat.lt_of_lt_of_le (hPin N (Nat.not_le.mp hlt)) (by simp)))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hNge
    rw [run_join hPin hPex j] at hN
    have hQh : Halts Q ⟨0, unaryConfig k ((inner x).get hPd)⟩ := by
      refine ⟨j, ?_⟩
      have hle : (P ++ shiftJumps P.length Q).length
          ≤ (run Q ⟨0, unaryConfig k ((inner x).get hPd)⟩ j).pc + P.length := hN
      rw [length_append_shiftJumps] at hle
      exact show Q.length ≤ (run Q ⟨0, unaryConfig k ((inner x).get hPd)⟩ j).pc by omega
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_bind hy (Part.get_mem (hQ.dom hQh))⟩

/-- **Calling a clean machine from a wider register file.**

The caller picks the injection, seeds `σ 0` with the input and zeroes the rest of the image. On
return the image holds the output in `σ 0` and zeros elsewhere, and every register outside the
image is exactly as it was — so the caller may keep controller state there and the callee cannot
disturb it. -/
theorem CleanPartComputesUnary.call {k' : ℕ} {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) {σ : Fin (k + 1) → Fin (k' + 1)} (hσ : Function.Injective σ)
    {regs : Fin (k' + 1) → ℕ} {x : ℕ} (hx : regs (σ 0) = x)
    (hclean : ∀ i, i ≠ 0 → regs (σ i) = 0) :
    (∀ y ∈ f x, ∃ n out,
        (∀ m < n, (run (renameRegs σ P) ⟨0, regs⟩ m).pc < (renameRegs σ P).length) ∧
        run (renameRegs σ P) ⟨0, regs⟩ n = ⟨(renameRegs σ P).length, out⟩ ∧
        out (σ 0) = y ∧ (∀ i, i ≠ 0 → out (σ i) = 0) ∧
        ∀ r, (∀ i, r ≠ σ i) → out r = regs r) ∧
      (Halts (renameRegs σ P) ⟨0, regs⟩ → (f x).Dom) := by
  have hcomp : regs ∘ σ = unaryConfig k x := by
    funext i
    by_cases hi : i = 0
    · subst hi; simpa using hx
    · simpa [unaryConfig_of_ne hi] using hclean i hi
  have hren : Renamed σ ⟨0, unaryConfig k x⟩ ⟨0, regs⟩ := ⟨rfl, fun i => congrFun hcomp i⟩
  refine ⟨fun y hy => ?_, fun hh => h.dom ((halts_renameRegs_iff hσ hren).mp hh)⟩
  obtain ⟨n, hin, hex⟩ := h.exit hy
  have hexr : (run P ⟨0, unaryConfig k x⟩ n).regs = unaryConfig k y := by rw [hex]
  refine ⟨n, (run (renameRegs σ P) ⟨0, regs⟩ n).regs, fun m hm => ?_, ?_, ?_, fun i hi => ?_,
    fun r hr => ?_⟩
  · rw [(hren.run (P := P) hσ m).pc, length_renameRegs]
    exact hin m hm
  · have hpc : (run (renameRegs σ P) ⟨0, regs⟩ n).pc = (renameRegs σ P).length := by
      rw [(hren.run (P := P) hσ n).pc, hex, length_renameRegs]
    rw [← hpc]
  · rw [(hren.run (P := P) hσ n).regs 0, hexr, unaryConfig_zero]
  · rw [(hren.run (P := P) hσ n).regs i, hexr, unaryConfig_of_ne hi]
  · exact regs_run_renameRegs_of_ne hr n

end RegisterMachine

end Hilbert10
