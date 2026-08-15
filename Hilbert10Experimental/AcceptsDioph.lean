/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ConfigCodingDioph
import Hilbert10Experimental.ExpDiophChoose
import Hilbert10Experimental.PackedRun

/-!
# The machine route, reduced to one obligation

Issue #49, first phase. #48 closed the semantic chain: `Accepts` is *equivalent* to the
existence of a packed run. This file represents every part of that statement except one, and
gives the remainder a name.

## What is discharged here

The endpoint of `accepts_iff_exists_encodedRun` has eight conjuncts under four existentials.
Seven of them are ordinary exponential Diophantine atoms:

* three boundary bounds, `of_lt`;
* the guard mask, `ExpDioph.of_isBinarySubmask` (#34) — with `geom` carried as a *variable*
  rather than computed, which is exactly what `geom_unique` was proved for;
* two endpoint equalities, `of_eq`, using the closed form `configCode w ⟨p, unaryConfig k x⟩
  = p + 2 ^ w * x`;
* the per-index step relation, `expDioph_encodedStep` (#45).

The eighth is the bounded conjunction over indices. It is named `Aggregation` and taken as a
hypothesis, so that the accounting cannot drift: `expDioph_accepts` is *conditional*, and the
condition is a single `def` one can read.

## What is not discharged, and must not be faked

`Aggregation` is the same bounded-universal theorem the direct-route spike isolated in
`Spike/Sequences.lean`. Two things do not count as progress on it:

* adding a bounded-product or bounded-forall constructor to `ExpTerm` — that relocates the
  missing proof into new syntax;
* `boundedForall_eq_iff_prod`. Product-equals-one is *equivalent* to the bounded universal for
  those gap factors, so the reduction is free and the representation of the variable product is
  the whole of the difficulty.

Any discharge must come from an independently proved representation theorem, and attribution
belongs at the deepest non-circular one.

## Main definitions

* `RegisterMachine.blockTerm` — outer block lookup at a **variable** index
* `RegisterMachine.Aggregation` — the sole remaining obligation

## Main results

* `RegisterMachine.expDioph_accepts` — conditional on `Aggregation`
-/

namespace Hilbert10

namespace RegisterMachine

variable {α : Type} {k : ℕ}

/-! ### Terms for the outer layer

`ConfigCodingDioph`'s `fieldTerm` reads a field at a numeral index, which is right for the
inner layer: the program is fixed, so its register indices are numerals. The outer index runs
over blocks and is a variable, so it needs its own term. -/

/-- The data width of one block: `w * (k + 1)` for a `k`-register machine. -/
def dataBaseTerm (k : ℕ) (W : ExpTerm α) : ExpTerm α :=
  .pow (.const 2) (.mul W (.const (k + 1)))

@[simp] theorem eval_dataBaseTerm (k : ℕ) (W : ExpTerm α) (v : α → ℕ) :
    (dataBaseTerm k W).eval v = 2 ^ (W.eval v * (k + 1)) := rfl

/-- The outer packing base: one block is the data plus one guard bit. -/
def outerBaseTerm (k : ℕ) (W : ExpTerm α) : ExpTerm α :=
  .pow (.const 2) (.add (.mul W (.const (k + 1))) (.const 1))

@[simp] theorem eval_outerBaseTerm (k : ℕ) (W : ExpTerm α) (v : α → ℕ) :
    (outerBaseTerm k W).eval v = 2 ^ (W.eval v * (k + 1) + 1) := rfl

/-- **Outer block lookup at a variable index.** -/
def blockTerm (k : ℕ) (W R I : ExpTerm α) : ExpTerm α :=
  .mod (.div R (.pow (outerBaseTerm k W) I)) (outerBaseTerm k W)

@[simp] theorem eval_blockTerm (k : ℕ) (W R I : ExpTerm α) (v : α → ℕ) :
    (blockTerm k W R I).eval v
      = configField (W.eval v * (k + 1) + 1) (R.eval v) (I.eval v) := rfl

/-! ### The obligation -/

/-- **The sole remaining representability obligation of #21**: a bounded conjunction of step
relations over a variable number of block indices.

Stated with `N`, `W`, `R` as terms and the index quantified semantically, so that it cannot be
satisfied by making the index a numeral or by assuming a representable lookup function. -/
def Aggregation (k : ℕ) : Prop :=
  ∀ {α : Type} (P : Program k) (N W R : ExpTerm α),
    ExpDioph {v : α → ℕ | ∀ i < N.eval v,
      EncodedStep P (W.eval v)
        (configField (W.eval v * (k + 1) + 1) (R.eval v) i)
        (configField (W.eval v * (k + 1) + 1) (R.eval v) (i + 1))}

/-! ### Everything else -/

/-- The witness block of `expDioph_accepts`, spelled out: `0` is the run length, `1` the width,
`2` the packed run, `3` the geometric sum carried as a variable. -/
def runBody (P : Program (k + 1)) (X Y : ExpTerm α) : Set ((α ⊕ Fin 4) → ℕ) :=
  {u | (X.map Sum.inl).eval u < 2 ^ u (Sum.inr 1) ∧
    (Y.map Sum.inl).eval u < 2 ^ u (Sum.inr 1) ∧
    P.length < 2 ^ u (Sum.inr 1) ∧
    u (Sum.inr 3) * 2 ^ (u (Sum.inr 1) * (k + 1 + 1) + 1) + 1
      = u (Sum.inr 3) + (2 ^ (u (Sum.inr 1) * (k + 1 + 1) + 1)) ^ (u (Sum.inr 0) + 1) ∧
    Nat.IsBinarySubmask (u (Sum.inr 2))
      ((2 ^ (u (Sum.inr 1) * (k + 1 + 1)) - 1) * u (Sum.inr 3)) ∧
    configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) 0
      = 2 ^ u (Sum.inr 1) * (X.map Sum.inl).eval u ∧
    configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) (u (Sum.inr 0))
      = P.length + 2 ^ u (Sum.inr 1) * (Y.map Sum.inl).eval u ∧
    ∀ i < u (Sum.inr 0),
      EncodedStep P (u (Sum.inr 1))
        (configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) i)
        (configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) (i + 1))}

theorem expDioph_runBody (hagg : Aggregation (k + 1)) (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph (runBody P X Y) := by
  refine ExpDioph.congr (ExpDioph.and
    (ExpDioph.of_lt (s := X.map Sum.inl) (t := widthTerm (.var (Sum.inr 1)))) (ExpDioph.and
    (ExpDioph.of_lt (s := Y.map Sum.inl) (t := widthTerm (.var (Sum.inr 1)))) (ExpDioph.and
    (ExpDioph.of_lt (s := .const P.length) (t := widthTerm (.var (Sum.inr 1)))) (ExpDioph.and
    (ExpDioph.of_eq
      (s := .add (.mul (.var (Sum.inr 3)) (outerBaseTerm (k + 1) (.var (Sum.inr 1)))) (.const 1))
      (t := .add (.var (Sum.inr 3))
        (.pow (outerBaseTerm (k + 1) (.var (Sum.inr 1)))
          (.add (.var (Sum.inr 0)) (.const 1))))) (ExpDioph.and
    (ExpDioph.of_isBinarySubmask (.var (Sum.inr 2))
      (.mul (.sub (dataBaseTerm (k + 1) (.var (Sum.inr 1))) (.const 1)) (.var (Sum.inr 3))))
      (ExpDioph.and
    (ExpDioph.of_eq
      (s := blockTerm (k + 1) (.var (Sum.inr 1)) (.var (Sum.inr 2)) (.const 0))
      (t := .mul (widthTerm (.var (Sum.inr 1))) (X.map Sum.inl))) (ExpDioph.and
    (ExpDioph.of_eq
      (s := blockTerm (k + 1) (.var (Sum.inr 1)) (.var (Sum.inr 2)) (.var (Sum.inr 0)))
      (t := .add (.const P.length)
        (.mul (widthTerm (.var (Sum.inr 1))) (Y.map Sum.inl))))
    (hagg P (.var (Sum.inr 0)) (.var (Sum.inr 1)) (.var (Sum.inr 2)))))))))) ?_
  intro u
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, runBody, widthTerm, ExpTerm.eval,
    eval_dataBaseTerm, eval_outerBaseTerm, eval_blockTerm]

/-- **The endpoint, conditional on aggregation.**

Every conjunct of `accepts_iff_exists_encodedRun` other than the bounded conjunction is
discharged here. The geometric sum is carried as the fourth witness and pinned by
`geom_unique`, which is the one place `BlockPacking`'s subtraction-free identity earns its
keep: the guard mask is a *variable* satisfying one equation, never a computed sum. -/
theorem expDioph_accepts (hagg : Aggregation (k + 1)) (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} := by
  refine ExpDioph.congr (ExpDioph.ex (expDioph_runBody hagg P X Y)) fun v => ?_
  simp only [runBody, Set.mem_setOf_eq, ExpTerm.eval_map, Sum.elim_comp_inl, Sum.elim_inr]
  rw [accepts_iff_exists_encodedRun]
  simp only [EncodedRun, configCode_unaryConfig, Nat.zero_add]
  constructor
  · rintro ⟨u, hx, hy, hlen, hgeom, hmask, h0, hn, hstep⟩
    have hG : u 3 = geom (blockBase (u 1 * (k + 1 + 1))) (u 0 + 1) :=
      geom_unique (two_le_blockBase _) hgeom
    refine ⟨u 0, u 1, u 2, hx, hy, hlen, ?_, h0, hn, hstep⟩
    rw [guardMask_eq, ← hG]
    simpa [dataBound] using hmask
  · rintro ⟨n, w, R, hx, hy, hlen, hmask, h0, hn, hstep⟩
    refine ⟨![n, w, R, geom (2 ^ (w * (k + 1 + 1) + 1)) (n + 1)], hx, hy, hlen,
      geom_spec _ _, ?_, h0, hn, hstep⟩
    rw [guardMask_eq] at hmask
    simpa [dataBound, blockBase] using hmask

end RegisterMachine

end Hilbert10
