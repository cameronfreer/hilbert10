/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.CodeMachine
import Hilbert10Experimental.Spike.SelectorRegsDioph
import Mathlib.Computability.RE

/-!
# DPRM on `ℕ`: the machine route's endpoint

Issue #23, first part. Two facts are already available and this file only joins them:

* `exists_machine_graph` (#20) compiles a `Nat.Partrec.Code` into a register machine whose
  accepted relation is the graph of `c.eval`;
* `dioph_accepts_regs` (#21, #49) says acceptance by an arbitrary register machine is
  Diophantine.

Composing them gives the graph of any partial recursive function, and projecting the output
gives its domain. A recursively enumerable predicate on `ℕ` is the domain of such a function,
which is the unary case of DPRM.

## Where the register count goes

`exists_machine_graph` produces a machine on `k + 1` registers, and `dioph_accepts_regs` is
stated for `Program (k + 1)`, so the two fit with no side condition: there is no `Aggregation 0`
to discharge, because a compiled machine always has at least one register.

## Scope

`ℕ` only. Tuples are the next file: a machine consumes one number, while an `n`-ary predicate
receives a `Fin n → ℕ`.

## Main results

* `Nat.Partrec.graph_dioph`, `Nat.Partrec.dom_dioph`
* `REPred.dioph_nat` — the unary case of DPRM
-/

namespace Hilbert10

open Nat.Partrec (Code)
open RegisterMachine

/-- The graph of a `Nat.Partrec.Code` is Diophantine: compile it, then arithmetise the
machine's accepted relation. -/
private theorem dioph_code_graph (c : Code) :
    Dioph {v : Fin 2 → ℕ | v 1 ∈ c.eval (v 0)} := by
  obtain ⟨k, P, hP⟩ := exists_machine_graph c
  have hset : {v : Fin 2 → ℕ | v 1 ∈ c.eval (v 0)} = {v : Fin 2 → ℕ | Accepts P (v 0) (v 1)} :=
    Set.ext fun v => (hP (v 0) (v 1)).symm
  rw [hset]
  exact dioph_accepts_regs P (.var 0) (.var 1)

/-- **The graph of a partial recursive function is Diophantine.** -/
theorem Nat.Partrec.graph_dioph {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) :
    Dioph {v : Fin 2 → ℕ | v 1 ∈ f (v 0)} := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  have hset : {v : Fin 2 → ℕ | v 1 ∈ f (v 0)} = {v : Fin 2 → ℕ | v 1 ∈ c.eval (v 0)} := by
    rw [hc]
  rw [hset]
  exact dioph_code_graph c

/-- **The domain of a partial recursive function is Diophantine.** The output is projected out
as a witness, which is one `ExpDioph.ex` rather than a second arithmetisation. -/
theorem Nat.Partrec.dom_dioph {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) :
    Dioph {v : Fin 1 → ℕ | (f (v 0)).Dom} := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  obtain ⟨k, P, hP⟩ := exists_machine_graph c
  refine (ExpDioph.congr (ExpDioph.ex (expDioph_accepts_regs P
    (.var (Sum.inl 0)) (.var (Sum.inr ())))) fun v => ?_).dioph
  simp only [Set.mem_setOf_eq, Part.dom_iff_mem]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w (), by rw [← hc]; exact (hP (v 0) (w ())).mp hw⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, (hP (v 0) y).mpr (by rw [hc]; exact hy)⟩

/-- **DPRM on `ℕ`.** A recursively enumerable predicate on the naturals is Diophantine.

The `Unit`-valued witness of `REPred` is turned into a partial function with the same domain,
exactly as in `HaltingComplete`; its domain is then Diophantine. -/
theorem REPred.dioph_nat {R : ℕ → Prop} (h : REPred R) : Dioph {v : Fin 1 → ℕ | R (v 0)} := by
  have hf : Partrec fun a : ℕ =>
      (Part.assert (R a) fun _ => Part.some ()).map fun _ => (0 : ℕ) :=
    h.map (Computable.const (0 : ℕ)).to₂
  set f : ℕ →. ℕ := fun a => (Part.assert (R a) fun _ => Part.some ()).map fun _ => (0 : ℕ)
    with hf_def
  have hdom : ∀ a, (f a).Dom ↔ R a := by
    intro a
    simp [hf_def, Part.assert]
  have hset : {v : Fin 1 → ℕ | R (v 0)} = {v : Fin 1 → ℕ | (f (v 0)).Dom} :=
    Set.ext fun v => (hdom (v 0)).symm
  rw [hset]
  exact Nat.Partrec.dom_dioph (Partrec.nat_iff.mp hf)

end Hilbert10
