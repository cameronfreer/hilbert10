/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Degree
import Hilbert10.Internal.CodeAlgebraDegree

/-!
# Elementary gates of degree at most two, and the allocation contract

Issue #57, first checkpoint. Lowering a polynomial equation to a system of quadratic equations
introduces one auxiliary variable per intermediate value, and a *gate* is the single equation
that defines such a variable: a constant, a copy, a sum or a product of variables read earlier.
This module provides the four gate codes, their exact semantics at every assignment, their
degree bounds (`≤ 2`, the point of the exercise) and their arities, together with the contract
the compiler of the next checkpoint must respect.

## The allocation contract

A gate *writes* one variable, its `out`, and *reads* only variables with smaller index. A list of
gates is `WellOrdered n` when the gates write `n, n + 1, …` in order and each reads below what
it writes. That ordering is what makes soundness an induction (`exists_extension`): any
assignment of the first `n` variables extends, gate by gate, to one satisfying every gate — and
it rules out circular "definitions" of intermediate values, which an equation for every
auxiliary variable alone would not.

Gate constants are naturals. Signed coefficients are handled by the compiler keeping positive and
negative contributions in separate accumulators, so that a natural assignment extends to a
natural one (`exists_extension` is stated over any semiring, so it serves `ℕ` and `ℤ` alike).

## Main definitions

* `Hilbert10.PolynomialCode.constGate`, `eqGate`, `addGate`, `mulGate`
* `Hilbert10.Gate`, `Gate.code`, `Gate.Holds`, `Gate.Fresh`, `Hilbert10.WellOrdered`

## Main results

* `Hilbert10.PolynomialCode.evalInt_constGate_eq_zero_iff` and the other three, over `ℤ` and `ℕ`
* `Hilbert10.PolynomialCode.degreeBound_mulGate_le` and the other three
* `Hilbert10.Gate.evalInt_code_eq_zero_iff`, `Gate.eval_code_eq_zero_iff`,
  `Gate.degreeBound_code_le`, `Gate.arity_code_le`
* `Hilbert10.exists_extension`
* `Hilbert10.PolynomialCode.degreeBound_sumSquaresCode_le`
-/

namespace Hilbert10

namespace PolynomialCode

/-! ### The four gate codes -/

/-- `xᵢ − c`. -/
def constGate (i : ℕ) (c : ℤ) : PolynomialCode := add (X i) (const (-c))

/-- `xᵢ − xⱼ`. -/
def eqGate (i j : ℕ) : PolynomialCode := add (X i) (neg (X j))

/-- `xᵢ − (xⱼ + xₖ)`. -/
def addGate (i j k : ℕ) : PolynomialCode := add (X i) (neg (add (X j) (X k)))

/-- `xᵢ − xⱼ xₖ`. -/
def mulGate (i j k : ℕ) : PolynomialCode := add (X i) (neg (mul (X j) (X k)))

/-! ### Semantics over `ℤ` -/

theorem evalInt_constGate_eq_zero_iff (i : ℕ) (c : ℤ) (x : List ℤ) :
    evalInt (constGate i c) x = 0 ↔ x.getD i 0 = c := by
  simp only [constGate, evalInt_add, evalInt_X, evalInt_const, ← sub_eq_add_neg, sub_eq_zero]

theorem evalInt_eqGate_eq_zero_iff (i j : ℕ) (x : List ℤ) :
    evalInt (eqGate i j) x = 0 ↔ x.getD i 0 = x.getD j 0 := by
  simp only [eqGate, evalInt_add, evalInt_X, evalInt_neg, ← sub_eq_add_neg, sub_eq_zero]

theorem evalInt_addGate_eq_zero_iff (i j k : ℕ) (x : List ℤ) :
    evalInt (addGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 + x.getD k 0 := by
  simp only [addGate, evalInt_add, evalInt_X, evalInt_neg, ← sub_eq_add_neg, sub_eq_zero]

theorem evalInt_mulGate_eq_zero_iff (i j k : ℕ) (x : List ℤ) :
    evalInt (mulGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 * x.getD k 0 := by
  simp only [mulGate, evalInt_add, evalInt_X, evalInt_neg, evalInt_mul, ← sub_eq_add_neg,
    sub_eq_zero]

/-! ### Semantics over `ℕ`, through the cast bridge -/

theorem eval_constGate_eq_zero_iff (i : ℕ) (c : ℤ) (x : List ℕ) :
    eval (constGate i c) x = 0 ↔ ((x.getD i 0 : ℕ) : ℤ) = c := by
  rw [← evalInt_map_natCast, evalInt_constGate_eq_zero_iff, getD_map_natCast]

theorem eval_eqGate_eq_zero_iff (i j : ℕ) (x : List ℕ) :
    eval (eqGate i j) x = 0 ↔ x.getD i 0 = x.getD j 0 := by
  rw [← evalInt_map_natCast, evalInt_eqGate_eq_zero_iff, getD_map_natCast, getD_map_natCast]
  exact Nat.cast_inj

theorem eval_addGate_eq_zero_iff (i j k : ℕ) (x : List ℕ) :
    eval (addGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 + x.getD k 0 := by
  rw [← evalInt_map_natCast, evalInt_addGate_eq_zero_iff, getD_map_natCast, getD_map_natCast,
    getD_map_natCast, ← Nat.cast_add]
  exact Nat.cast_inj

theorem eval_mulGate_eq_zero_iff (i j k : ℕ) (x : List ℕ) :
    eval (mulGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 * x.getD k 0 := by
  rw [← evalInt_map_natCast, evalInt_mulGate_eq_zero_iff, getD_map_natCast, getD_map_natCast,
    getD_map_natCast, ← Nat.cast_mul]
  exact Nat.cast_inj

/-! ### Degree: the gates are quadratic -/

theorem degreeBound_constGate_le (i : ℕ) (c : ℤ) : (constGate i c).degreeBound ≤ 1 := by
  refine (degreeBound_add_le _ _).trans ?_
  simp

theorem degreeBound_eqGate_le (i j : ℕ) : (eqGate i j).degreeBound ≤ 1 := by
  refine (degreeBound_add_le _ _).trans (max_le (by simp) ?_)
  exact (degreeBound_neg_le _).trans (by simp)

theorem degreeBound_addGate_le (i j k : ℕ) : (addGate i j k).degreeBound ≤ 1 := by
  refine (degreeBound_add_le _ _).trans (max_le (by simp) ?_)
  refine (degreeBound_neg_le _).trans ((degreeBound_add_le _ _).trans ?_)
  simp

theorem degreeBound_mulGate_le (i j k : ℕ) : (mulGate i j k).degreeBound ≤ 2 := by
  refine (degreeBound_add_le _ _).trans (max_le (by simp) ?_)
  refine (degreeBound_neg_le _).trans ((degreeBound_mul_le _ _).trans ?_)
  simp

/-! ### Arity -/

theorem arity_constGate_le (i : ℕ) (c : ℤ) : (constGate i c).arity ≤ i + 1 := by
  simp [constGate]

theorem arity_eqGate_le (i j : ℕ) : (eqGate i j).arity ≤ max (i + 1) (j + 1) := by
  simp [eqGate]

theorem arity_addGate_le (i j k : ℕ) :
    (addGate i j k).arity ≤ max (i + 1) (max (j + 1) (k + 1)) := by
  simp [addGate]

theorem arity_mulGate_le (i j k : ℕ) :
    (mulGate i j k).arity ≤ max (i + 1) (max (j + 1) (k + 1)) := by
  simp only [mulGate, arity_add, arity_neg, arity_X]
  exact max_le_max le_rfl ((arity_mul_le _ _).trans (by simp))

/-! ### The sum of squares at most doubles the degree -/

/-- **`sumSquaresCode` at most doubles the degree bound.** With quadratic members this is the
quartic bound of #57. -/
theorem degreeBound_sumSquaresCode_le (ps : List PolynomialCode) :
    (sumSquaresCode ps).degreeBound ≤ 2 * systemDegreeBound ps := by
  refine degreeBound_foldr_add_le _ _ _ fun p hp => ?_
  refine (degreeBound_mul_le p p).trans ?_
  have := degreeBound_le_systemDegreeBound hp
  omega

end PolynomialCode

/-! ### Gates as data, and the allocation contract -/

/-- An elementary gate: the equation defining variable `out` from variables read earlier. The
constant of a `const` gate is a natural number; signs are the compiler's business. -/
inductive Gate
  /-- `x_out = c`. -/
  | const (out : ℕ) (c : ℕ)
  /-- `x_out = x_i`. -/
  | copy (out i : ℕ)
  /-- `x_out = x_i + x_j`. -/
  | add (out i j : ℕ)
  /-- `x_out = x_i * x_j`. -/
  | mul (out i j : ℕ)

namespace Gate

/-- The variable a gate writes. -/
def out : Gate → ℕ
  | const o _ => o
  | copy o _ => o
  | add o _ _ => o
  | mul o _ _ => o

/-- The variables a gate reads. -/
def reads : Gate → List ℕ
  | const _ _ => []
  | copy _ i => [i]
  | add _ i j => [i, j]
  | mul _ i j => [i, j]

/-- The gate's equation, as a code. -/
def code : Gate → PolynomialCode
  | const o c => PolynomialCode.constGate o c
  | copy o i => PolynomialCode.eqGate o i
  | add o i j => PolynomialCode.addGate o i j
  | mul o i j => PolynomialCode.mulGate o i j

/-- The value a gate computes from an assignment, over any semiring. -/
def value {R : Type*} [Semiring R] : Gate → List R → R
  | const _ c, _ => c
  | copy _ i, x => x.getD i 0
  | add _ i j, x => x.getD i 0 + x.getD j 0
  | mul _ i j, x => x.getD i 0 * x.getD j 0

/-- The gate's equation holds at an assignment: the output variable carries the computed value. -/
def Holds {R : Type*} [Semiring R] (g : Gate) (x : List R) : Prop := x.getD g.out 0 = g.value x

instance {R : Type*} [Semiring R] [DecidableEq R] (g : Gate) (x : List R) :
    Decidable (g.Holds x) := by
  unfold Holds
  infer_instance

/-- **A gate's code vanishes exactly when its equation holds**, over `ℤ`. -/
theorem evalInt_code_eq_zero_iff (g : Gate) (x : List ℤ) :
    PolynomialCode.evalInt g.code x = 0 ↔ g.Holds x := by
  cases g <;> simp [code, Holds, out, value, PolynomialCode.evalInt_constGate_eq_zero_iff,
    PolynomialCode.evalInt_eqGate_eq_zero_iff, PolynomialCode.evalInt_addGate_eq_zero_iff,
    PolynomialCode.evalInt_mulGate_eq_zero_iff]

/-- **A gate's code vanishes exactly when its equation holds**, over `ℕ`. -/
theorem eval_code_eq_zero_iff (g : Gate) (x : List ℕ) :
    PolynomialCode.eval g.code x = 0 ↔ g.Holds x := by
  cases g <;> simp [code, Holds, out, value, PolynomialCode.eval_constGate_eq_zero_iff,
    PolynomialCode.eval_eqGate_eq_zero_iff, PolynomialCode.eval_addGate_eq_zero_iff,
    PolynomialCode.eval_mulGate_eq_zero_iff]

/-- **Every gate is quadratic.** -/
theorem degreeBound_code_le (g : Gate) : g.code.degreeBound ≤ 2 := by
  cases g with
  | const o c => exact (PolynomialCode.degreeBound_constGate_le o c).trans one_le_two
  | copy o i => exact (PolynomialCode.degreeBound_eqGate_le o i).trans one_le_two
  | add o i j => exact (PolynomialCode.degreeBound_addGate_le o i j).trans one_le_two
  | mul o i j => exact PolynomialCode.degreeBound_mulGate_le o i j

/-- A gate that reads below what it writes uses no variable beyond its output. -/
theorem arity_code_le (g : Gate) (h : ∀ r ∈ g.reads, r < g.out) : g.code.arity ≤ g.out + 1 := by
  cases g with
  | const o c => exact PolynomialCode.arity_constGate_le o c
  | copy o i =>
    have hi := h i (by simp [reads])
    exact (PolynomialCode.arity_eqGate_le o i).trans (by simp [out] at hi ⊢; omega)
  | add o i j =>
    have hi := h i (by simp [reads])
    have hj := h j (by simp [reads])
    exact (PolynomialCode.arity_addGate_le o i j).trans (by simp [out] at hi hj ⊢; omega)
  | mul o i j =>
    have hi := h i (by simp [reads])
    have hj := h j (by simp [reads])
    exact (PolynomialCode.arity_mulGate_le o i j).trans (by simp [out] at hi hj ⊢; omega)

/-- The value depends only on the variables read. -/
theorem value_congr {R : Type*} [Semiring R] (g : Gate) {x y : List R}
    (h : ∀ r ∈ g.reads, x.getD r 0 = y.getD r 0) : g.value x = g.value y := by
  cases g <;> simp_all [reads, value]

/-- **The allocation contract for one gate**: it writes `n` and reads only below `n`. -/
def Fresh (g : Gate) (n : ℕ) : Prop := g.out = n ∧ ∀ r ∈ g.reads, r < n

end Gate

/-- **The allocation contract for a gate list**: starting at `n`, the gates write `n, n + 1, …`
in order, each reading only original variables (below `n`) or the outputs of earlier gates. -/
def WellOrdered : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs => g.Fresh n ∧ WellOrdered (n + 1) gs

@[simp] theorem wellOrdered_nil (n : ℕ) : WellOrdered n [] := trivial

@[simp] theorem wellOrdered_cons (n : ℕ) (g : Gate) (gs : List Gate) :
    WellOrdered n (g :: gs) ↔ g.Fresh n ∧ WellOrdered (n + 1) gs := Iff.rfl

private theorem getD_of_take_eq {R : Type*} [Zero R] {y x : List R} {n : ℕ} (h : y.take n = x)
    {r : ℕ} (hr : r < n) : y.getD r 0 = x.getD r 0 := by
  rw [← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hr]

/-- **Soundness of the contract.** An assignment of the first `n` variables extends, along a
well-ordered gate list, to an assignment of `n + gs.length` variables satisfying every gate; the
original variables are preserved as a prefix. Over any semiring, so natural inputs get natural
auxiliary values. -/
theorem exists_extension {R : Type*} [Semiring R] :
    ∀ (gs : List Gate) (n : ℕ), WellOrdered n gs → ∀ x : List R, x.length = n →
      ∃ y : List R, y.length = n + gs.length ∧ y.take n = x ∧ ∀ g ∈ gs, g.Holds y
  | [], n, _, x, hx => ⟨x, by simp [hx], by rw [← hx, List.take_length], by simp⟩
  | g :: gs, n, ⟨⟨hout, hreads⟩, hwo⟩, x, hx => by
    obtain ⟨y, hy, hyx, hgs⟩ :=
      exists_extension gs (n + 1) hwo (x ++ [g.value x]) (by simp [hx])
    have hsplit : y = (x ++ [g.value x]) ++ y.drop (n + 1) := by
      rw [← hyx, List.take_append_drop]
    have hyn : y.take n = x := by
      rw [hsplit, List.append_assoc, List.take_left' hx]
    refine ⟨y, by simp [hy]; omega, hyn, ?_⟩
    rw [List.forall_mem_cons]
    refine ⟨?_, hgs⟩
    have hval : g.value y = g.value x :=
      g.value_congr fun r hr => getD_of_take_eq hyn (hreads r hr)
    have hread : y.getD n 0 = g.value x := by
      rw [hsplit, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hx]), ← hx,
        List.getElem?_concat_length, Option.getD_some]
    change y.getD g.out 0 = g.value y
    rw [hout, hread, hval]

/-! ### Regression examples -/

/-- The degree bounds are computable, and exact on the gates. -/
example : (PolynomialCode.mulGate 2 0 1).degreeBound = 2 := by decide
example : (PolynomialCode.addGate 2 0 1).degreeBound = 1 := by decide
example : (PolynomialCode.constGate 0 7).degreeBound = 1 := by decide
example : (PolynomialCode.eqGate 0 1).degreeBound = 1 := by decide

/-- `x₂ = x₀ · x₁`, then `x₃ = x₂ + x₀`: two original variables, two gates, well ordered. -/
example : WellOrdered 2 [Gate.mul 2 0 1, Gate.add 3 2 0] := by
  simp [WellOrdered, Gate.Fresh, Gate.reads, Gate.out]

/-- A gate that reads what it writes is not fresh: circular definitions are excluded. -/
example : ¬ (Gate.copy 3 3).Fresh 3 := by simp [Gate.Fresh, Gate.reads, Gate.out]

/-- A gate that reads a *later* variable is not fresh either. -/
example : ¬ WellOrdered 2 [Gate.add 2 0 3, Gate.const 3 1] := by
  simp [WellOrdered, Gate.Fresh, Gate.reads, Gate.out]

/-- The extension theorem, instantiated: `[3, 4]` extends to `[3, 4, 12, 15]`. -/
example : ∀ g ∈ [Gate.mul 2 0 1, Gate.add 3 2 0], g.Holds ([3, 4, 12, 15] : List ℕ) := by
  decide

end Hilbert10
