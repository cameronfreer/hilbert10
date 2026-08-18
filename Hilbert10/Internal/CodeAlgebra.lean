/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.PolynomialCodeInt
import Mathlib.Tactic.Ring

/-!
# Arithmetic on encoded polynomials

Issue #28, second piece. The two solvability reductions substitute into a code, so they need to
build codes: constants, variables, sums, products, powers. This is the minimum those consumers
ask for, and it is deliberately **internal** — a wire-format algebra, not the polynomial DSL
parked in #29.

## The one real trap

Exponent vectors are ragged: `[2]` and `[0, 3]` are the same polynomial's monomials with
different presentations, and a trailing zero is invisible. So multiplying two monomials means
adding exponent vectors **with zero-extension**, and `List.zipWith` is wrong — it truncates to
the shorter vector, silently discarding the tail of the longer one.

`addExponents` is that operation, and `evalMonomialInt_addExponents` is the theorem everything
else rests on: once monomial multiplication is right, convolution multiplication of codes is
list-sum distributivity.

## One evaluation, two readings

Every law is proved for `evalInt` and then *derived* for `eval` through
`evalInt_map_natCast`, rather than proved twice. The natural evaluation is the integer one at a
cast assignment, so there is nothing separate to check.

## Not here

No general renaming. With the original variables in the first block, extending an assignment
leaves a code's value unchanged, and both consumers can build the variables they need directly
at the indices they want. If a consumer ever asks for a rename, add it then.

## Main definitions

* `Hilbert10.PolynomialCode.addExponents` — zero-extended pointwise addition
* `Hilbert10.PolynomialCode.const`, `X`, `add`, `neg`, `mul`, `pow`
-/

namespace Hilbert10

namespace PolynomialCode

/-! ### Zero-extended exponent addition -/

/-- Pointwise addition of exponent vectors, extending the shorter with zeros. `List.zipWith`
would truncate instead, which drops the longer vector's tail. -/
def addExponents : MonomialCode → MonomialCode → MonomialCode
  | [], f => f
  | e :: es, [] => e :: es
  | a :: es, b :: fs => (a + b) :: addExponents es fs

@[simp] theorem addExponents_nil_left (f : MonomialCode) : addExponents [] f = f := rfl

@[simp] theorem addExponents_nil_right : ∀ e : MonomialCode, addExponents e [] = e
  | [] => rfl
  | _ :: _ => rfl

/-- **Monomial multiplication is exponent addition.** Everything else in this file reduces to
this and list-sum distributivity. -/
theorem evalMonomialInt_addExponents :
    ∀ (e f : MonomialCode) (x : List ℤ),
      evalMonomialInt (addExponents e f) x = evalMonomialInt e x * evalMonomialInt f x
  | [], f, x => by simp [evalMonomialInt]
  | e :: es, [], x => by simp [evalMonomialInt]
  | a :: es, b :: fs, [] => by
    simp only [addExponents, evalMonomialInt, evalMonomialInt_addExponents es fs [], pow_add]
    ring
  | a :: es, b :: fs, v :: vs => by
    simp only [addExponents, evalMonomialInt, evalMonomialInt_addExponents es fs vs, pow_add]
    ring

/-! ### The operations -/

/-- The zero polynomial. -/
def zero : PolynomialCode := ⟨[]⟩

/-- A constant. -/
def const (c : ℤ) : PolynomialCode := ⟨[(c, [])]⟩

/-- The polynomial `1`. -/
def one : PolynomialCode := const 1

/-- The variable with index `i`. -/
def X (i : ℕ) : PolynomialCode := ⟨[(1, List.replicate i 0 ++ [1])]⟩

/-- Sum: sparse representations concatenate. -/
def add (p q : PolynomialCode) : PolynomialCode := ⟨p.terms ++ q.terms⟩

/-- Negation: negate every coefficient. -/
def neg (p : PolynomialCode) : PolynomialCode := ⟨p.terms.map fun t => (-t.1, t.2)⟩

/-- Product: convolution of the term lists, multiplying coefficients and adding exponents. -/
def mul (p q : PolynomialCode) : PolynomialCode :=
  ⟨p.terms.flatMap fun t => q.terms.map fun s => (t.1 * s.1, addExponents t.2 s.2)⟩

/-- Powers, by structural recursion. -/
def npow (p : PolynomialCode) : ℕ → PolynomialCode
  | 0 => one
  | n + 1 => mul p (npow p n)

/-! ### Evaluation laws, at an integer assignment -/

@[simp] theorem evalInt_zero (x : List ℤ) : evalInt zero x = 0 := rfl

@[simp] theorem evalInt_const (c : ℤ) (x : List ℤ) : evalInt (const c) x = c := by
  simp [evalInt, const, evalMonomialInt]

@[simp] theorem evalInt_one (x : List ℤ) : evalInt one x = 1 := by simp [one]

theorem evalMonomialInt_X : ∀ (i : ℕ) (x : List ℤ),
    evalMonomialInt (List.replicate i 0 ++ [1]) x = x.getD i 0
  | 0, [] => by simp [evalMonomialInt]
  | 0, v :: vs => by simp [evalMonomialInt]
  | i + 1, [] => by
    have ih := evalMonomialInt_X i ([] : List ℤ)
    simp only [List.replicate_succ, List.cons_append, evalMonomialInt, ih]
    simp
  | i + 1, v :: vs => by
    have ih := evalMonomialInt_X i vs
    simp only [List.replicate_succ, List.cons_append, evalMonomialInt, ih]
    simp

@[simp] theorem evalInt_X (i : ℕ) (x : List ℤ) : evalInt (X i) x = x.getD i 0 := by
  simp [evalInt, X, evalMonomialInt_X]

@[simp] theorem evalInt_add (p q : PolynomialCode) (x : List ℤ) :
    evalInt (add p q) x = evalInt p x + evalInt q x := by
  simp [evalInt, add]

@[simp] theorem evalInt_neg (p : PolynomialCode) (x : List ℤ) :
    evalInt (neg p) x = -evalInt p x := by
  simp only [evalInt, neg, List.map_map, Function.comp_def]
  induction p.terms with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_map_const_mul {α : Type*} (c : ℤ) (l : List α) (h : α → ℤ) :
    (l.map fun s => c * h s).sum = c * (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

@[simp] theorem evalInt_mul (p q : PolynomialCode) (x : List ℤ) :
    evalInt (mul p q) x = evalInt p x * evalInt q x := by
  obtain ⟨ts⟩ := p
  simp only [evalInt, mul]
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have hterm : (List.map (fun s : ℤ × MonomialCode =>
        (t.1 * s.1) * evalMonomialInt (addExponents t.2 s.2) x) q.terms).sum
        = (t.1 * evalMonomialInt t.2 x)
          * (List.map (fun s : ℤ × MonomialCode => s.1 * evalMonomialInt s.2 x) q.terms).sum := by
      rw [← sum_map_const_mul]
      congr 1
      exact List.map_congr_left fun s _ => by
        rw [evalMonomialInt_addExponents]; ring
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, List.map_cons, List.sum_cons, ih, hterm]
    ring

@[simp] theorem evalInt_npow (p : PolynomialCode) : ∀ (n : ℕ) (x : List ℤ),
    evalInt (npow p n) x = evalInt p x ^ n
  | 0, x => by simp [npow]
  | n + 1, x => by simp [npow, evalInt_npow p n x, pow_succ, mul_comm]

/-! ### The same laws at a natural assignment

Derived, not reproved: the natural evaluation is the integer one at a cast assignment. -/

theorem eval_eq_evalInt (p : PolynomialCode) (x : List ℕ) :
    eval p x = evalInt p (x.map (Nat.cast : ℕ → ℤ)) := (evalInt_map_natCast p x).symm

@[simp] theorem eval_const (c : ℤ) (x : List ℕ) : eval (const c) x = c := by
  rw [eval_eq_evalInt, evalInt_const]

@[simp] theorem eval_add (p q : PolynomialCode) (x : List ℕ) :
    eval (add p q) x = eval p x + eval q x := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, eval_eq_evalInt q, evalInt_add]

@[simp] theorem eval_neg (p : PolynomialCode) (x : List ℕ) :
    eval (neg p) x = -eval p x := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, evalInt_neg]

@[simp] theorem eval_mul (p q : PolynomialCode) (x : List ℕ) :
    eval (mul p q) x = eval p x * eval q x := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, eval_eq_evalInt q, evalInt_mul]

@[simp] theorem eval_npow (p : PolynomialCode) (n : ℕ) (x : List ℕ) :
    eval (npow p n) x = eval p x ^ n := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, evalInt_npow]

theorem getD_map_natCast (x : List ℕ) (i : ℕ) :
    (x.map (Nat.cast : ℕ → ℤ)).getD i 0 = ((x.getD i 0 : ℕ) : ℤ) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases x[i]? <;> simp

@[simp] theorem eval_X (i : ℕ) (x : List ℕ) : eval (X i) x = ((x.getD i 0 : ℕ) : ℤ) := by
  rw [eval_eq_evalInt, evalInt_X, getD_map_natCast]

end PolynomialCode

end Hilbert10
