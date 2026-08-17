/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Internal.AcceptsDioph
import Hilbert10Experimental.Spike.SelectorSlice

/-!
# Acceptance slice for the selector encoding: representability

#49, phase 2, final layer. `Spike/SelectorSlice` proves the *semantic* elimination: for the fixed
program `sliceP`, the bounded conjunction of encoded steps is equivalent to a finite system of
identities between packed numbers. This file makes that system exponential Diophantine, so that
one program is end-to-end rather than merely eliminated.

## The statement

`StepBundle` is `Aggregation`'s body at a one-register program, extracted as a definition so that
the gap is machine-checked rather than asserted: `aggregation_one_iff` says `Aggregation 1` is
exactly `StepBundle` for *every* one-register program, and `expDioph_stepBundle_sliceP` proves it
for *one*.

## The geometric-sum witness

`laneMask` and `bitMask` are built from `geom`, which is not an `ExpTerm` — it is a sum of a
variable number of powers. It enters as a ninth witness pinned by `geom_spec`/`geom_unique`:

```
G * B + 1 = G + B ^ N   ↔   G = geom B N
```

subtraction-free, one equation, no bounded quantifier. `geom B (N + 1)` needs no second witness,
since `geom_succ` writes it as `1 + B * G`. This is the same device `AcceptsDioph` describes for
`guardMask`, used here for the two narrower masks as well.

## What this does and does not show

Every conjunct of `SliceGlobalConditions` is an atom: `of_lt`, `of_eq`, `of_isBinarySubmask`
(#34), and `or` for the three target disjunctions. Nothing here needs a new combinator, and in
particular nothing needs a bounded product or a bounded universal — which is the claim the slice
exists to test.

Because `expDioph_accepts_of_bundle` assumes `StepBundle` only for the program it is applied to,
this reaches the endpoint of #48 outright: `dioph_accepts_sliceP` says acceptance by `sliceP` is
Diophantine, with no hypothesis. That is the whole machine route, for one program.

It is still one fixed program with one register. Generic `Aggregation` needs the selector family
to be indexed by an arbitrary instruction list, and that is not what is proved here.

## Main results

* `RegisterMachine.expDioph_stepBundle_sliceP` — the packed selector system is exponential
  Diophantine
* `RegisterMachine.dioph_accepts_sliceP` — acceptance by `sliceP` is Diophantine
-/

namespace Hilbert10

namespace RegisterMachine

variable {α : Type}

/-! ### Terms -/

/-- The outer packing base for a one-register machine, as a term. -/
def sliceBaseTerm (W : ExpTerm α) : ExpTerm α :=
  .pow (.const 2) (.add (.mul W (.const 2)) (.const 1))

@[simp] theorem eval_sliceBaseTerm (W : ExpTerm α) (v : α → ℕ) :
    (sliceBaseTerm W).eval v = 2 ^ (W.eval v * 2 + 1) := rfl

/-! ### The obligation, for one register -/

/-- The obligation of #49 at one register is `StepBundle`, for *every* program; what is proved
below is the same statement at a single `P`. The distance between them is a quantifier, stated
rather than described. -/
theorem aggregation_one_iff :
    Aggregation 1 ↔ ∀ {α : Type} (P : Program 1) (N W R : ExpTerm α),
      ExpDioph (StepBundle P N W R) := Iff.rfl

/-! ### The witness block

Nine witnesses: the two lanes, the four selectors, the two residuals, and the geometric sum.
The order is the one `SliceGlobalConditions` lists them in, with `geom` last. -/

/-- The body under the nine existentials: the geometric sum is pinned, and the rest is
`SliceGlobalConditions` verbatim. -/
def sliceBody (N W R : ExpTerm α) : Set ((α ⊕ Fin 9) → ℕ) :=
  {u | u (Sum.inr 8) * 2 ^ ((W.map Sum.inl).eval u * 2 + 1) + 1
        = u (Sum.inr 8) + (2 ^ ((W.map Sum.inl).eval u * 2 + 1)) ^ (N.map Sum.inl).eval u ∧
      SliceGlobalConditions ((W.map Sum.inl).eval u) ((N.map Sum.inl).eval u)
        ((R.map Sum.inl).eval u) (u (Sum.inr 0)) (u (Sum.inr 1)) (u (Sum.inr 2))
        (u (Sum.inr 3)) (u (Sum.inr 4)) (u (Sum.inr 5)) (u (Sum.inr 6)) (u (Sum.inr 7))}

theorem expDioph_sliceBody (N W R : ExpTerm α) : ExpDioph (sliceBody N W R) := by
  -- abbreviations for the terms over the extended variable type
  set W' : ExpTerm (α ⊕ Fin 9) := W.map Sum.inl with hW'
  set N' : ExpTerm (α ⊕ Fin 9) := N.map Sum.inl with hN'
  set R' : ExpTerm (α ⊕ Fin 9) := R.map Sum.inl with hR'
  set P : ExpTerm (α ⊕ Fin 9) := .pow (.const 2) W' with hP
  set B : ExpTerm (α ⊕ Fin 9) := sliceBaseTerm W' with hB
  set Bn : ExpTerm (α ⊕ Fin 9) := .pow B N' with hBn
  set vXpc : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 0) with hvXpc
  set vX0 : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 1) with hvX0
  set vS0 : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 2) with hvS0
  set vS1p : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 3) with hvS1p
  set vS1z : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 4) with hvS1z
  set vS2 : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 5) with hvS2
  set vRes : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 6) with hvRes
  set vZres : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 7) with hvZres
  set vG : ExpTerm (α ⊕ Fin 9) := .var (Sum.inr 8) with hvG
  -- the two masks, with `geom` replaced by its witness
  set laneN : ExpTerm (α ⊕ Fin 9) := .mul (.sub P (.const 1)) vG with hlaneN
  set laneS : ExpTerm (α ⊕ Fin 9) :=
    .mul (.sub P (.const 1)) (.add (.const 1) (.mul B vG)) with hlaneS
  -- the conditions, assembled from the last one back, so that the nesting matches
  -- `SliceGlobalConditions` exactly
  have c17 := ExpDioph.or (ExpDioph.of_eq (s := vS2) (t := .const 0))
    (ExpDioph.of_lt (s := .const 1000) (t := P))
  have c16 := ExpDioph.and (ExpDioph.or (ExpDioph.of_eq (s := vS1z) (t := .const 0))
    (ExpDioph.of_lt (s := .const 2) (t := P))) c17
  have c15 := ExpDioph.and (ExpDioph.or (ExpDioph.of_eq (s := vS0) (t := .const 0))
    (ExpDioph.of_lt (s := .const 1) (t := P))) c16
  have c14 := ExpDioph.and (ExpDioph.and
    (ExpDioph.of_eq (s := .mod vX0 Bn) (t := .add vRes vS1p))
    (ExpDioph.of_isBinarySubmask vRes laneN)) c15
  have c13 := ExpDioph.and (ExpDioph.and
    (ExpDioph.of_eq (s := .add (.add (.mod vX0 Bn) (.mul vS1z (.sub P (.const 1)))) vZres)
      (t := laneN))
    (ExpDioph.of_isBinarySubmask vZres laneN)) c14
  have c12 := ExpDioph.and (ExpDioph.of_eq (s := .add (.div vX0 B) vS1p)
    (t := .add (.add (.mod vX0 Bn) vS0) vS2)) c13
  have c11 := ExpDioph.and (ExpDioph.of_eq (s := .div vXpc B)
    (t := .add (.add vS0 (.mul (.const 2) vS1z)) (.mul (.const 1000) vS2))) c12
  have c10 := ExpDioph.and (ExpDioph.of_eq (s := .mod vXpc Bn)
    (t := .add (.add vS1p vS1z) (.mul (.const 2) vS2))) c11
  have c9 := ExpDioph.and
    (ExpDioph.of_eq (s := .add (.add (.add vS0 vS1p) vS1z) vS2) (t := vG)) c10
  have c8 := ExpDioph.and (ExpDioph.of_isBinarySubmask vS2 vG) c9
  have c7 := ExpDioph.and (ExpDioph.of_isBinarySubmask vS1z vG) c8
  have c6 := ExpDioph.and (ExpDioph.of_isBinarySubmask vS1p vG) c7
  have c5 := ExpDioph.and (ExpDioph.of_isBinarySubmask vS0 vG) c6
  have c4 := ExpDioph.and (ExpDioph.of_eq (s := R') (t := .add vXpc (.mul P vX0))) c5
  have c3 := ExpDioph.and (ExpDioph.of_isBinarySubmask vX0 laneS) c4
  have c2 := ExpDioph.and (ExpDioph.of_isBinarySubmask vXpc laneS) c3
  have c1 := ExpDioph.and (ExpDioph.of_lt (s := .const 3) (t := P)) c2
  have c0 := ExpDioph.and
    (ExpDioph.of_eq (s := .add (.mul vG B) (.const 1)) (t := .add vG Bn)) c1
  refine ExpDioph.congr c0 ?_
  intro u
  have hb : (2 : ℕ) ≤ 2 ^ ((W.map Sum.inl).eval u * 2 + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ((W.map Sum.inl).eval u * 2 + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, sliceBody,
    SliceGlobalConditions, laneMask, bitMask, sliceP_length, geom_succ, hlaneN, hlaneS, hP, hB,
    hBn, hvXpc, hvX0, hvS0, hvS1p, hvS1z, hvS2, hvRes, hvZres, hvG, hW', hN', hR',
    sliceBaseTerm, ExpTerm.eval]
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

/-- **The slice is representable.** The packed selector system of `sliceGlobal_iff` is
exponential Diophantine, so for this program the bounded conjunction of encoded steps is not only
eliminated but represented. -/
theorem expDioph_stepBundle_sliceP (N W R : ExpTerm α) :
    ExpDioph (StepBundle sliceP N W R) := by
  refine ExpDioph.congr (ExpDioph.ex (expDioph_sliceBody N W R)) fun v => ?_
  simp only [StepBundle, sliceBody, Set.mem_setOf_eq, ExpTerm.eval_map, Sum.elim_comp_inl,
    Sum.elim_inr, show (1 : ℕ) + 1 = 2 from rfl]
  rw [sliceGlobal_iff]
  constructor
  · rintro ⟨u, _, h⟩
    exact ⟨u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, h⟩
  · rintro ⟨Xpc, X0, S0, S1p, S1z, S2, Res, Zres, h⟩
    exact ⟨![Xpc, X0, S0, S1p, S1z, S2, Res, Zres,
      geom (2 ^ (W.eval v * 2 + 1)) (N.eval v)], geom_spec _ _, h⟩

/-! ### End to end

`expDioph_accepts_of_bundle` assumes the bundle only for the program it is applied to, so the
slice reaches the endpoint of #48 without waiting for `Aggregation`. -/

/-- **The slice, end to end.** Acceptance by `sliceP` is exponential Diophantine, and so
Diophantine, with no hypothesis. This is `expDioph_accepts` for one program, unconditional. -/
theorem expDioph_accepts_sliceP (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts sliceP (X.eval v) (Y.eval v)} :=
  expDioph_accepts_of_bundle (fun {β} N W R => expDioph_stepBundle_sliceP (α := β) N W R) X Y

theorem dioph_accepts_sliceP (X Y : ExpTerm α) :
    Dioph {v : α → ℕ | Accepts sliceP (X.eval v) (Y.eval v)} :=
  (expDioph_accepts_sliceP X Y).dioph

end RegisterMachine

end Hilbert10
