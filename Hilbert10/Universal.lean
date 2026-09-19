/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.DPRM
import Hilbert10.ExistsCode
import Hilbert10.Quartic

/-!
# One universal Diophantine polynomial, and its degree-four form

Issue #54. The first stage is the universal polynomial; the second lowers that one fixed
polynomial to degree four. `dioph_iff_rePred` says every recursively enumerable predicate has *some*
representing polynomial, chosen for that predicate. The classical statement is stronger: one
fixed polynomial represents universal program evaluation, with the program index, the input and
the output as its three parameters.

## The quantifier order is the theorem

```
∃ k U, ∀ e x y,  y ∈ eval e x ↔ ∃ z : Fin k → ℕ, U (e, x, y, z) = 0
```

`k` and `U` are chosen *before* `e`, `x` and `y`. Letting the polynomial depend on the index is
`dioph_iff_rePred` restated, and is not what is proved here. The proof is short because it is
DPRM applied to the *universal* relation, which is recursively enumerable by the step-indexed
evaluator `Nat.Partrec.Code.evaln`.

## The index-decoding convention, frozen

An index is a natural number, decoded through the `Denumerable` instance on `Nat.Partrec.Code`:
`program e := Denumerable.ofNat Code e`. Under this convention every natural number is a valid
program, and every program has an index (`program_encode`), so there are no invalid indices to
treat and no side condition on `e`.

## Existence only

Nothing here produces a polynomial from a program, and the witness count `k` is fixed because the
polynomial is fixed — not because individual programs have bounded compilation size. No bound on
`k` is claimed.

## The degree-four form

The quadratic lowering of #57 is applied to the *fixed* universal code, allocating from wire
`3 + k` so that the three parameter positions and the `k` original witness positions are
preserved as a prefix; the fresh wires follow. The new witness count `k + gateCountFrom q (3 + k)`
is again fixed because the code being lowered is fixed. This is a consumer of the extension
theorem in its prefix-preserving form: root-existence equivalence alone would not give the
parameterised statement, since the parameters must stay where they are.

## Main definitions

* `Hilbert10.program`, `Hilbert10.UnivEval`

## Main results

* `Hilbert10.rePred_univEval`, `Hilbert10.dioph_univEval`
* `Hilbert10.exists_universal_mvPolynomial` — the universal polynomial
* `Hilbert10.exists_universal_code` — the same, in the wire format
* `Hilbert10.dom_iff_of_universal` — the parameterised halting set, by projecting the output
* `Hilbert10.exists_universal_quartic_code` — one universal polynomial of degree at most four
-/

-- Opened *outside* the namespace: `Hilbert10.Nat.Partrec` exists (it holds `graph_dioph`), and
-- inside `namespace Hilbert10` an `open Nat.Partrec` would resolve there and find no `Code`.
open Nat.Partrec (Code)

namespace Hilbert10

/-- **The index-decoding convention**: every natural number is a program. -/
def program (e : ℕ) : Code := Denumerable.ofNat Code e

/-- Every program has an index. -/
theorem program_encode (c : Code) : program (Encodable.encode c) = c :=
  Denumerable.ofNat_encode c

/-- **Universal evaluation**, as a relation on triples: program index, input, output. -/
def UnivEval (v : Fin 3 → ℕ) : Prop := v 2 ∈ (program (v 0)).eval (v 1)

/-! ### The universal relation is recursively enumerable, hence Diophantine -/

private theorem univEval_iff_exists_evaln (v : Fin 3 → ℕ) :
    UnivEval v ↔ ∃ s : ℕ, Code.evaln s (program (v 0)) (v 1) = some (v 2) := by
  simp only [UnivEval, Code.evaln_complete, Option.mem_def]

private theorem primrec_proj (i : Fin 3) : Primrec fun z : (Fin 3 → ℕ) × ℕ => z.1 i :=
  Primrec.fin_app.comp Primrec.fst (Primrec.const i)

theorem rePred_univEval : REPred UnivEval := by
  have hP : ComputablePred fun z : (Fin 3 → ℕ) × ℕ =>
      Code.evaln z.2 (program (z.1 0)) (z.1 1) = some (z.1 2) := by
    refine PrimrecPred.computablePred (PrimrecRel.comp Primrec.eq ?_ ?_)
    · exact Code.primrec_evaln.comp
        ((Primrec.snd.pair ((Primrec.ofNat Code).comp (primrec_proj 0))).pair (primrec_proj 1))
    · exact Primrec.option_some.comp (primrec_proj 2)
  exact (ComputablePred.rePred_exists hP).of_eq fun v => (univEval_iff_exists_evaln v).symm

theorem dioph_univEval : Dioph {v : Fin 3 → ℕ | UnivEval v} := REPred.dioph rePred_univEval

/-! ### The universal polynomial -/

/-- **One universal polynomial.** There are `k` and `U` in `3 + k` variables such that, for every
index `e`, input `x` and output `y`, the program `e` returns `y` on `x` exactly when
`U (e, x, y, z) = 0` has a natural solution `z`. -/
theorem exists_universal_mvPolynomial :
    ∃ (k : ℕ) (U : MvPolynomial (Fin 3 ⊕ Fin k) ℤ), ∀ e x y : ℕ,
      y ∈ (program e).eval x ↔
        ∃ z : Fin k → ℕ,
          MvPolynomial.eval (Sum.elim (fun i => ((![e, x, y] i : ℕ) : ℤ)) fun j => (z j : ℤ)) U
            = 0 := by
  obtain ⟨k, U, hU⟩ := (dioph_iff_exists_fin_mvPolynomial UnivEval).mp dioph_univEval
  refine ⟨k, U, fun e x y => ?_⟩
  simpa [UnivEval] using hU ![e, x, y]

/-- **The universal polynomial, in the wire format**: a code of arity at most `3 + k`, read at the
parameters followed by the witnesses. This is the input the degree-four stage lowers. -/
theorem exists_universal_code :
    ∃ (k : ℕ) (q : PolynomialCode), q.arity ≤ 3 + k ∧ ∀ e x y : ℕ,
      y ∈ (program e).eval x ↔
        ∃ z : Fin k → ℕ, q.eval (List.ofFn ![e, x, y] ++ List.ofFn z) = 0 := by
  obtain ⟨k, U, hU⟩ := exists_universal_mvPolynomial
  obtain ⟨q, hq, hden⟩ := PolynomialCode.exists_code U
  refine ⟨k, q, hq, fun e x y => (hU e x y).trans (exists_congr fun z => ?_)⟩
  rw [PolynomialCode.eval_exists_code hden]

/-- **The parameterised halting set**, from any universal polynomial: program `e` halts on `x`
exactly when `U (e, x, y, z) = 0` has a solution in `y` and `z`. The same polynomial, with the
output projected away. -/
theorem dom_iff_of_universal {k : ℕ} {U : MvPolynomial (Fin 3 ⊕ Fin k) ℤ}
    (hU : ∀ e x y : ℕ, y ∈ (program e).eval x ↔
      ∃ z : Fin k → ℕ,
        MvPolynomial.eval (Sum.elim (fun i => ((![e, x, y] i : ℕ) : ℤ)) fun j => (z j : ℤ)) U = 0)
    (e x : ℕ) :
    ((program e).eval x).Dom ↔
      ∃ (y : ℕ) (z : Fin k → ℕ),
        MvPolynomial.eval (Sum.elim (fun i => ((![e, x, y] i : ℕ) : ℤ)) fun j => (z j : ℤ)) U
          = 0 := by
  rw [Part.dom_iff_mem]
  exact exists_congr fun y => hU e x y

/-! ### One universal quartic polynomial -/

/-- A list of the right length is `List.ofFn` of some function. -/
private theorem exists_ofFn_eq {m : ℕ} {l : List ℕ} (hl : l.length = m) :
    ∃ w : Fin m → ℕ, List.ofFn w = l := by
  subst hl
  exact ⟨fun i => l[i], List.ofFn_getElem⟩

/-- **One universal polynomial of degree at most four.** There is a code `Q` of degree bound at
most four in `3 + k` variables such that program `e` returns `y` on `x` exactly when
`Q (e, x, y, w) = 0` has a natural solution `w`. Obtained by lowering the universal code of
`exists_universal_code` with the parameters kept in place. -/
theorem exists_universal_quartic_code :
    ∃ (k : ℕ) (Q : PolynomialCode), Q.degreeBound ≤ 4 ∧ Q.arity ≤ 3 + k ∧ ∀ e x y : ℕ,
      y ∈ (program e).eval x ↔
        ∃ w : Fin k → ℕ, Q.eval (List.ofFn ![e, x, y] ++ List.ofFn w) = 0 := by
  obtain ⟨k, q, hq, hU⟩ := exists_universal_code
  -- allocate the lowering from wire `3 + k`: parameters, then the original witnesses, are a prefix
  refine ⟨k + gateCountFrom q (3 + k),
    PolynomialCode.sumSquaresCode (quadraticSystemFrom q (3 + k)), ?_, ?_, fun e x y => ?_⟩
  · exact (PolynomialCode.degreeBound_sumSquaresCode_le _).trans
      (by have := systemDegreeBound_quadraticSystemFrom_le q (3 + k); omega)
  · exact (PolynomialCode.arity_sumSquaresCode_le _).trans
      (by have := systemArity_quadraticSystemFrom_le q (3 + k) hq; omega)
  · rw [hU e x y]
    constructor
    · rintro ⟨z, hz⟩
      have hlen : (List.ofFn ![e, x, y] ++ List.ofFn z).length = 3 + k := by
        simp only [List.length_append, List.length_ofFn]
      obtain ⟨aux, haux, hsys⟩ :=
        (eval_eq_zero_iff_exists_aux_from q (3 + k) hq _ hlen).mp hz
      obtain ⟨w, hw⟩ := exists_ofFn_eq (m := k + gateCountFrom q (3 + k))
        (l := List.ofFn z ++ aux) (by simp [haux])
      refine ⟨w, ?_⟩
      rw [hw, ← List.append_assoc, PolynomialCode.eval_sumSquaresCode_eq_zero_iff]
      exact hsys
    · rintro ⟨w, hw⟩
      rw [PolynomialCode.eval_sumSquaresCode_eq_zero_iff] at hw
      -- the first `k` witness wires are the original witnesses; the rest are the fresh wires
      obtain ⟨z, hz⟩ := exists_ofFn_eq (m := k) (l := (List.ofFn w).take k)
        (by simp only [List.length_take, List.length_ofFn]; omega)
      refine ⟨z, ?_⟩
      have hlen : (List.ofFn ![e, x, y] ++ List.ofFn z).length = 3 + k := by
        simp only [List.length_append, List.length_ofFn]
      refine (eval_eq_zero_iff_exists_aux_from q (3 + k) hq _ hlen).mpr
        ⟨(List.ofFn w).drop k, ?_, ?_⟩
      · simp only [List.length_drop, List.length_ofFn]
        omega
      · rw [hz, List.append_assoc, List.take_append_drop]
        exact hw

/-! ### Regression: the convention -/

/-- Every program has an index, and decoding it gives the program back. -/
example (c : Code) : ∃ e : ℕ, program e = c := ⟨Encodable.encode c, program_encode c⟩

/-- Every natural number is a program: there is nothing to reject. -/
example (e : ℕ) : Encodable.encode (program e) = e := Denumerable.encode_ofNat e

end Hilbert10
