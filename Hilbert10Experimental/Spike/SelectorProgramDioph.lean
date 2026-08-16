/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.AcceptsDioph
import Hilbert10Experimental.Spike.SelectorProgramGlobal

/-!
# `Aggregation 1`

#49, phase 3, final layer. `Spike/SelectorProgramGlobal` reduced the bounded conjunction of
encoded steps, for an arbitrary `P : Program 1`, to `GlobalConditions`. This file represents
`GlobalConditions`, which discharges `Aggregation` at one register.

## Two kinds of finiteness

`GlobalConditions` has two groups of conditions, and they are represented differently:

* the aggregate identities are single `ExpDioph` atoms whose terms contain `ExpTerm.sumTerm`, a
  *term-level* sum of `2 * P.length` summands with constant coefficients;
* the per-branch side conditions are `ExpDioph.fin_and`, a conjunction of `2 * P.length` atoms.

Neither is the bounded universal `∀ i < N` the obligation is about: both lengths are determined
by the program when the condition is written down, and neither depends on the run length. The
instruction data — `branchIndex`, `branchTarget`, `gain`, `loss`, `zeroBranch` — enters as
*constants* in those terms. Nothing looks an instruction up at evaluation time, and there is no
encoded program.

## The witnesses

`(Fin P.length ⊕ Fin P.length) ⊕ Fin 5`: one lane per branch, then the two data lanes, the two
residuals, and the geometric sum. `geom` is pinned by `geom_spec`/`geom_unique` exactly as in
`Spike/SelectorSliceDioph`, and `geom_succ` again covers the `(n + 1)`-block mask.

## Main results

* `RegisterMachine.expDioph_stepBundle_program` — `StepBundle` for every one-register program
* `RegisterMachine.aggregation_one` — `Aggregation 1`
* `RegisterMachine.dioph_accepts_program` — acceptance by any `P : Program 1` is Diophantine
-/

namespace Hilbert10

namespace RegisterMachine

variable {α : Type}

/-- The witness block: one lane per branch, then `Xpc`, `X0`, `Res`, `Zres`, `geom`. -/
abbrev ProgramWitness (P : Program 1) := (Fin P.length ⊕ Fin P.length) ⊕ Fin 5

/-- The body under the witnesses: the geometric sum is pinned, and the rest is
`GlobalConditions` verbatim. -/
def programBody (P : Program 1) (N W R : ExpTerm α) :
    Set ((α ⊕ ProgramWitness P) → ℕ) :=
  {u | u (.inr (.inr 4)) * 2 ^ ((W.map Sum.inl).eval u * 2 + 1) + 1
        = u (.inr (.inr 4)) + (2 ^ ((W.map Sum.inl).eval u * 2 + 1)) ^ (N.map Sum.inl).eval u ∧
      GlobalConditions P ((W.map Sum.inl).eval u) ((N.map Sum.inl).eval u)
        ((R.map Sum.inl).eval u) (u (.inr (.inr 0))) (u (.inr (.inr 1)))
        (fun c => u (.inr (.inl c))) (u (.inr (.inr 2))) (u (.inr (.inr 3)))}

theorem expDioph_programBody (P : Program 1) (N W R : ExpTerm α) :
    ExpDioph (programBody P N W R) := by
  set W' : ExpTerm (α ⊕ ProgramWitness P) := W.map Sum.inl with hW'
  set N' : ExpTerm (α ⊕ ProgramWitness P) := N.map Sum.inl with hN'
  set R' : ExpTerm (α ⊕ ProgramWitness P) := R.map Sum.inl with hR'
  set pw : ExpTerm (α ⊕ ProgramWitness P) := .pow (.const 2) W' with hpw
  set B : ExpTerm (α ⊕ ProgramWitness P) :=
    .pow (.const 2) (.add (.mul W' (.const 2)) (.const 1)) with hB
  set Bn : ExpTerm (α ⊕ ProgramWitness P) := .pow B N' with hBn
  set vXpc : ExpTerm (α ⊕ ProgramWitness P) := .var (.inr (.inr 0)) with hvXpc
  set vX0 : ExpTerm (α ⊕ ProgramWitness P) := .var (.inr (.inr 1)) with hvX0
  set vRes : ExpTerm (α ⊕ ProgramWitness P) := .var (.inr (.inr 2)) with hvRes
  set vZres : ExpTerm (α ⊕ ProgramWitness P) := .var (.inr (.inr 3)) with hvZres
  set vG : ExpTerm (α ⊕ ProgramWitness P) := .var (.inr (.inr 4)) with hvG
  set vS : Fin P.length ⊕ Fin P.length → ExpTerm (α ⊕ ProgramWitness P) :=
    fun c => .var (.inr (.inl c)) with hvS
  set laneN : ExpTerm (α ⊕ ProgramWitness P) := .mul (.sub pw (.const 1)) vG with hlaneN
  set laneS : ExpTerm (α ⊕ ProgramWitness P) :=
    .mul (.sub pw (.const 1)) (.add (.const 1) (.mul B vG)) with hlaneS
  -- the conditions, assembled from the last one back
  have c13 : ExpDioph {u : (α ⊕ ProgramWitness P) → ℕ |
      ∀ c, u (.inr (.inl c)) = 0 ∨ branchTarget P c < 2 ^ W'.eval u} :=
    ExpDioph.fin_and fun c =>
      ExpDioph.or (ExpDioph.of_eq (s := vS c) (t := .const 0))
        (ExpDioph.of_lt (s := .const (branchTarget P c)) (t := pw))
  have c12 := ExpDioph.and (ExpDioph.and
    (ExpDioph.of_eq (s := .mod vX0 Bn)
      (t := .add vRes (ExpTerm.sumTerm fun p : Fin P.length =>
        .mul (.const (P.get p).loss) (vS (.inl p)))))
    (ExpDioph.of_isBinarySubmask vRes laneN)) c13
  have c11 := ExpDioph.and (ExpDioph.and
    (ExpDioph.of_eq
      (s := .add (.add (.mod vX0 Bn)
        (.mul (ExpTerm.sumTerm fun p : Fin P.length => vS (.inr p)) (.sub pw (.const 1)))) vZres)
      (t := laneN))
    (ExpDioph.of_isBinarySubmask vZres laneN)) c12
  have c10 : ExpDioph {u : (α ⊕ ProgramWitness P) → ℕ |
      ∀ p, (P.get p).zeroBranch = 0 → u (.inr (.inl (.inr p))) = 0} :=
    ExpDioph.fin_and fun p => by
      by_cases hp : (P.get p).zeroBranch = 0
      · exact (ExpDioph.of_eq (s := vS (.inr p)) (t := .const 0)).congr fun u => by
          simp only [Set.mem_setOf_eq, hvS, ExpTerm.eval]
          exact ⟨fun h _ => h, fun h => h hp⟩
      · exact ExpDioph.of_true.congr fun u => by
          simp only [Set.mem_univ, true_iff]
          exact fun h => absurd h hp
  have c9 := ExpDioph.and (ExpDioph.of_eq
    (s := .add (.div vX0 B) (ExpTerm.sumTerm fun p : Fin P.length =>
      .mul (.const (P.get p).loss) (vS (.inl p))))
    (t := .add (.mod vX0 Bn) (ExpTerm.sumTerm fun p : Fin P.length =>
      .mul (.const (P.get p).gain) (vS (.inl p)))))
    (ExpDioph.and c10 c11)
  have c8 := ExpDioph.and (ExpDioph.of_eq (s := .div vXpc B)
    (t := ExpTerm.sumTerm fun c => .mul (.const (branchTarget P c)) (vS c))) c9
  have c7 := ExpDioph.and (ExpDioph.of_eq (s := .mod vXpc Bn)
    (t := ExpTerm.sumTerm fun c => .mul (.const (branchIndex P c)) (vS c))) c8
  have c6 := ExpDioph.and
    (ExpDioph.of_eq (s := ExpTerm.sumTerm fun c => vS c) (t := vG)) c7
  have c5 : ExpDioph {u : (α ⊕ ProgramWitness P) → ℕ |
      ∀ c, Nat.IsBinarySubmask (u (.inr (.inl c))) (vG.eval u)} :=
    ExpDioph.fin_and fun c => ExpDioph.of_isBinarySubmask (vS c) vG
  have c4 := ExpDioph.and
    (ExpDioph.of_eq (s := R') (t := .add vXpc (.mul pw vX0))) (ExpDioph.and c5 c6)
  have c3 := ExpDioph.and (ExpDioph.of_isBinarySubmask vX0 laneS) c4
  have c2 := ExpDioph.and (ExpDioph.of_isBinarySubmask vXpc laneS) c3
  have c1 := ExpDioph.and (ExpDioph.of_lt (s := .const P.length) (t := pw)) c2
  have c0 := ExpDioph.and
    (ExpDioph.of_eq (s := .add (.mul vG B) (.const 1)) (t := .add vG Bn)) c1
  refine ExpDioph.congr c0 ?_
  intro u
  have hb : (2 : ℕ) ≤ 2 ^ (W'.eval u * 2 + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (W'.eval u * 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, programBody,
    GlobalConditions, laneMask, bitMask, geom_succ, hlaneN, hlaneS, hpw, hB, hBn,
    hvXpc, hvX0, hvRes, hvZres, hvG, hvS, hW', hN', hR', ExpTerm.eval, ExpTerm.eval_sumTerm]
  constructor
  · rintro ⟨hpin, rest⟩
    have hG := geom_unique hb hpin
    refine ⟨hpin, ?_⟩
    rw [← hG]
    exact rest
  · rintro ⟨hpin, rest⟩
    have hG := geom_unique hb hpin
    refine ⟨hpin, ?_⟩
    rw [← hG] at rest
    exact rest

/-- **The obligation, for every one-register program.** -/
theorem expDioph_stepBundle_program (P : Program 1) (N W R : ExpTerm α) :
    ExpDioph (StepBundle P N W R) := by
  refine ExpDioph.congr (ExpDioph.ex (expDioph_programBody P N W R)) fun v => ?_
  simp only [StepBundle, programBody, Set.mem_setOf_eq, ExpTerm.eval_map, Sum.elim_comp_inl,
    Sum.elim_inr]
  rw [globalConditions_iff]
  constructor
  · rintro ⟨u, _, h⟩
    exact ⟨u (.inr 0), u (.inr 1), fun c => u (.inl c), u (.inr 2), u (.inr 3), h⟩
  · rintro ⟨Xpc, X0, S, Res, Zres, h⟩
    exact ⟨Sum.elim S ![Xpc, X0, Res, Zres, geom (2 ^ (W.eval v * 2 + 1)) (N.eval v)],
      geom_spec _ _, h⟩

/-- **`Aggregation` at one register.** The bounded conjunction of encoded steps is exponential
Diophantine for every one-register program, so #49's obligation holds at `k = 1`. -/
theorem aggregation_one : Aggregation 1 :=
  fun P N W R => expDioph_stepBundle_program P N W R

/-- **Acceptance by any one-register program is Diophantine**, unconditionally. -/
theorem expDioph_accepts_program (P : Program 1) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  expDioph_accepts_of_bundle (fun {β} N W R => expDioph_stepBundle_program (α := β) P N W R) X Y

theorem dioph_accepts_program (P : Program 1) (X Y : ExpTerm α) :
    Dioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  (expDioph_accepts_program P X Y).dioph

end RegisterMachine

end Hilbert10
