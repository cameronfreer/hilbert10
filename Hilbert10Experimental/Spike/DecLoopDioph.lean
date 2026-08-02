/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ExpDiophChoose
import Hilbert10Experimental.Spike.DecLoop

/-!
# The route spike's criterion 5

Assembling `Guarded` into an exponential Diophantine relation, closing the last of the five
acceptance criteria in #15.

Every field is a closure lemma applied to explicit terms:

| field | lemma |
|---|---|
| `base : n < 2 ^ k` | `ExpDioph.of_lt` |
| `geo`, `step` | `ExpDioph.of_eq` |
| `mask` | `ExpDioph.of_isBinarySubmask` (#34) |

combined with `ExpDioph.and` and projected with `ExpDioph.ex`. No new syntax is needed: the
guard-mask term `(2 ^ k - 1) * G` uses truncated subtraction, an `ExpTerm` constructor.
-/

namespace Hilbert10

namespace DecLoop

open ExpTerm

/-- Inputs `n, t`; witnesses `k, R, G`. -/
private abbrev V := Fin 2 ⊕ Fin 3

private def tN : ExpTerm V := .var (.inl 0)
private def tT : ExpTerm V := .var (.inl 1)
private def tK : ExpTerm V := .var (.inr 0)
private def tR : ExpTerm V := .var (.inr 1)
private def tG : ExpTerm V := .var (.inr 2)

/-- `dataBound k = 2 ^ k`, as a term. -/
private def tD : ExpTerm V := .pow (.const 2) tK

/-- `blockBase k = 2 ^ (k + 1)`, as a term. -/
private def tB : ExpTerm V := .pow (.const 2) (.add tK (.const 1))

/-- The guarded system, as a set over inputs together with witnesses. -/
private def guardedSet : Set (V → ℕ) :=
  {v | tN.eval v < tD.eval v} ∩
    ({v | (ExpTerm.add (.mul tG tB) (.const 1)).eval v = (ExpTerm.add tG (.pow tB tT)).eval v} ∩
      ({v | (ExpTerm.add tR (.mul tB tG)).eval v = (ExpTerm.add tN (.mul tB tR)).eval v} ∩
        {v | Nat.IsBinarySubmask (tR.eval v)
              ((ExpTerm.mul (.sub tD (.const 1)) tG).eval v)}))

private theorem expDioph_guardedSet : ExpDioph guardedSet :=
  ExpDioph.of_lt.and (ExpDioph.of_eq.and (ExpDioph.of_eq.and (ExpDioph.of_isBinarySubmask _ _)))

private theorem mem_guardedSet (v : Fin 2 → ℕ) (w : Fin 3 → ℕ) :
    Sum.elim v w ∈ guardedSet ↔ Guarded (v 0) (w 0) (v 1) (w 1) (w 2) := by
  constructor
  · rintro ⟨hbase, hgeo, hstep, hmask⟩
    exact ⟨hbase, hgeo, hstep, hmask⟩
  · rintro ⟨hbase, hgeo, hstep, hmask⟩
    exact ⟨hbase, hgeo, hstep, hmask⟩

/-- **Criterion 5.** The decrement loop's halting relation is exponential Diophantine, and
hence Diophantine. -/
theorem expDioph_haltsIn : ExpDioph {v : Fin 2 → ℕ | HaltsIn (v 0) (v 1)} := by
  refine (ExpDioph.ex expDioph_guardedSet).congr fun v => ?_
  simp only [Set.mem_setOf_eq]
  rw [haltsIn_iff_guarded]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w 0, w 1, w 2, (mem_guardedSet v w).mp hw⟩
  · rintro ⟨k, R, G, hg⟩
    exact ⟨![k, R, G], (mem_guardedSet v ![k, R, G]).mpr (by simpa using hg)⟩

theorem dioph_haltsIn : Dioph {v : Fin 2 → ℕ | HaltsIn (v 0) (v 1)} :=
  expDioph_haltsIn.dioph

end DecLoop

end Hilbert10
