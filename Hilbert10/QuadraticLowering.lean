/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.QuadraticGates

/-!
# Quadratic lowering: compiling expressions to well-ordered gate lists

Issue #57, second checkpoint. This module will hold the transformation from one polynomial
equation to a quadratic system; its first stage, and the only one so far, is **one monomial**.
Compiling an exponent vector returns a gate list, the wire carrying the monomial's value, and
the next unused wire. The contract has three parts, and each later stage (powers, weighted
terms, the two accumulators) composes them without reopening the allocation argument:

* **well-ordering** — the gates are `WellOrdered next`, so `exists_extension` (completeness)
  applies;
* **bookkeeping** — the next unused wire is exactly `next + gates.length`, and the output wire
  lies below it;
* **soundness** — *any* assignment satisfying the gates reads the intended value from the output
  wire. This is the direction well-ordering exists for: existence of a satisfying extension says
  nothing about what a satisfying assignment must contain.

The empty exponent vector compiles to a wire holding `1`; zero exponents allocate nothing.

## Values, generically

`monomialValueFrom j e x` is the monomial's value read off an assignment by `getD`, over any
semiring, so one soundness proof serves `ℤ` and `ℕ`; `evalMonomialInt_eq_monomialValue` and
`evalMonomial_eq_monomialValue` connect it to the wire format's two evaluators.

## Main definitions

* `Hilbert10.Compiled`, `Hilbert10.mulPow`, `Hilbert10.compileMonomial`

## Main results

* `Hilbert10.compileMonomial_wellOrdered`, `compileMonomial_next`, `compileMonomial_out_lt`
* `Hilbert10.compileMonomial_sound`, and its `ℤ` and `ℕ` readings
-/

namespace Hilbert10

open PolynomialCode

/-! ### Monomial values, read by `getD` -/

/-- The value of the exponent vector `e`, its first entry referring to variable `j`, at an
assignment, over any semiring. Variables past the end of the assignment read as `0`. -/
def monomialValueFrom {R : Type*} [Semiring R] : ℕ → MonomialCode → List R → R
  | _, [], _ => 1
  | j, a :: es, x => x.getD j 0 ^ a * monomialValueFrom (j + 1) es x

theorem evalMonomialInt_drop_eq (x : List ℤ) :
    ∀ (e : MonomialCode) (i : ℕ), evalMonomialInt e (x.drop i) = monomialValueFrom i e x := by
  intro e
  induction e with
  | nil => intro i; simp [monomialValueFrom]
  | cons a es ih =>
    intro i
    by_cases hi : i < x.length
    · rw [List.drop_eq_getElem_cons hi]
      simp only [evalMonomialInt, monomialValueFrom, List.getD_eq_getElem _ _ hi, ih]
    · have hnil : x.drop i = [] := List.drop_eq_nil_of_le (le_of_not_gt hi)
      have hnil' : x.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h0 : x.getD i 0 = 0 := List.getD_eq_default _ _ (le_of_not_gt hi)
      rw [hnil]
      simp only [evalMonomialInt, monomialValueFrom, h0, ← ih (i + 1), hnil']

/-- The wire format's integer monomial evaluator, in `getD` form. -/
theorem evalMonomialInt_eq_monomialValue (e : MonomialCode) (x : List ℤ) :
    evalMonomialInt e x = monomialValueFrom 0 e x := by
  simpa using evalMonomialInt_drop_eq x e 0

theorem monomialValueFrom_map_natCast (x : List ℕ) :
    ∀ (e : MonomialCode) (j : ℕ),
      monomialValueFrom j e (x.map (Nat.cast : ℕ → ℤ)) = ((monomialValueFrom j e x : ℕ) : ℤ) := by
  intro e
  induction e with
  | nil => intro j; simp [monomialValueFrom]
  | cons a es ih =>
    intro j
    simp only [monomialValueFrom, getD_map_natCast, ih, Nat.cast_mul, Nat.cast_pow]

/-- The wire format's natural monomial evaluator, in `getD` form. -/
theorem evalMonomial_eq_monomialValue (e : MonomialCode) (x : List ℕ) :
    evalMonomial e x = ((monomialValueFrom 0 e x : ℕ) : ℤ) := by
  rw [← evalMonomialInt_map_natCast, evalMonomialInt_eq_monomialValue,
    monomialValueFrom_map_natCast]

/-! ### Well-ordering composes along `++` -/

theorem wellOrdered_append (n : ℕ) :
    ∀ gs₁ gs₂ : List Gate,
      WellOrdered n (gs₁ ++ gs₂) ↔ WellOrdered n gs₁ ∧ WellOrdered (n + gs₁.length) gs₂
  | [], gs₂ => by simp
  | g :: gs₁, gs₂ => by
    simp only [List.cons_append, wellOrdered_cons, List.length_cons, wellOrdered_append (n + 1)
      gs₁ gs₂, and_assoc]
    rw [Nat.add_assoc, Nat.add_comm gs₁.length 1]

/-! ### The output of a compilation -/

/-- A compiled expression: its defining gates, the wire carrying its value, and the next
unused wire. -/
structure Compiled where
  /-- The defining gates, well ordered from the wire the compilation started at. -/
  gates : List Gate
  /-- The wire carrying the expression's value. -/
  out : ℕ
  /-- The next unused wire. -/
  next : ℕ
  deriving DecidableEq, Repr

/-! ### Repeated multiplication by one variable -/

/-- `a` multiplications of wire `acc` by variable `j`, allocating from `next`. -/
def mulPow (j acc next : ℕ) : ℕ → Compiled
  | 0 => ⟨[], acc, next⟩
  | a + 1 =>
    let c := mulPow j next (next + 1) a
    ⟨Gate.mul next acc j :: c.gates, c.out, c.next⟩

theorem mulPow_next (j acc next : ℕ) : ∀ a : ℕ, (mulPow j acc next a).next = next + a
  | 0 => rfl
  | a + 1 => by
    simp only [mulPow, mulPow_next j next (next + 1) a]
    omega

theorem mulPow_length (j acc next : ℕ) : ∀ a : ℕ, (mulPow j acc next a).gates.length = a
  | 0 => rfl
  | a + 1 => by simp [mulPow, mulPow_length j next (next + 1) a]

theorem mulPow_out_lt (j : ℕ) :
    ∀ (a acc next : ℕ), acc < next → (mulPow j acc next a).out < next + a
  | 0, acc, next, h => by simpa [mulPow] using h
  | a + 1, acc, next, _ => by
    have := mulPow_out_lt j a next (next + 1) (Nat.lt_succ_self next)
    simp only [mulPow]
    omega

theorem mulPow_wellOrdered (j : ℕ) :
    ∀ (a acc next : ℕ), acc < next → j < next → WellOrdered next (mulPow j acc next a).gates
  | 0, _, _, _, _ => trivial
  | a + 1, acc, next, hacc, hj => by
    refine ⟨⟨rfl, ?_⟩, mulPow_wellOrdered j a next (next + 1) (Nat.lt_succ_self next) (by omega)⟩
    intro r hr
    simp only [Gate.reads, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption

/-- **Soundness**: any assignment satisfying the gates reads `acc · xⱼᵃ` from the output. -/
theorem mulPow_sound {R : Type*} [Semiring R] (j : ℕ) (x : List R) :
    ∀ (a acc next : ℕ), (∀ g ∈ (mulPow j acc next a).gates, g.Holds x) →
      x.getD (mulPow j acc next a).out 0 = x.getD acc 0 * x.getD j 0 ^ a
  | 0, acc, next, _ => by simp [mulPow]
  | a + 1, acc, next, h => by
    simp only [mulPow, List.forall_mem_cons] at h
    obtain ⟨hg, hrest⟩ := h
    have ih := mulPow_sound j x a next (next + 1) hrest
    simp only [Gate.Holds, Gate.out, Gate.value] at hg
    simp only [mulPow, ih, hg, pow_succ', mul_assoc]

/-! ### One monomial -/

/-- Multiply wire `acc` by the monomial `es` whose first entry refers to variable `j`,
allocating from `next`. -/
def compileMonomialFrom (acc next : ℕ) : ℕ → MonomialCode → Compiled
  | _, [] => ⟨[], acc, next⟩
  | j, a :: es =>
    let c₁ := mulPow j acc next a
    let c₂ := compileMonomialFrom c₁.out c₁.next (j + 1) es
    ⟨c₁.gates ++ c₂.gates, c₂.out, c₂.next⟩

theorem compileMonomialFrom_next :
    ∀ (es : MonomialCode) (acc next j : ℕ),
      (compileMonomialFrom acc next j es).next = next + es.sum
  | [], _, _, _ => by simp [compileMonomialFrom]
  | a :: es, acc, next, j => by
    simp only [compileMonomialFrom, compileMonomialFrom_next es, mulPow_next, List.sum_cons]
    omega

theorem compileMonomialFrom_length :
    ∀ (es : MonomialCode) (acc next j : ℕ),
      (compileMonomialFrom acc next j es).gates.length = es.sum
  | [], _, _, _ => rfl
  | a :: es, acc, next, j => by
    simp [compileMonomialFrom, mulPow_length, compileMonomialFrom_length es]

theorem compileMonomialFrom_out_lt :
    ∀ (es : MonomialCode) (acc next j : ℕ), acc < next →
      (compileMonomialFrom acc next j es).out < next + es.sum
  | [], acc, next, j, h => by simpa [compileMonomialFrom] using h
  | a :: es, acc, next, j, h => by
    have h1 := mulPow_out_lt j a acc next h
    have h2 := compileMonomialFrom_out_lt es (mulPow j acc next a).out (mulPow j acc next a).next
      (j + 1) (by rw [mulPow_next]; exact h1)
    simp only [compileMonomialFrom, mulPow_next, List.sum_cons] at h2 ⊢
    omega

theorem compileMonomialFrom_wellOrdered :
    ∀ (es : MonomialCode) (acc next j : ℕ), acc < next → j + es.length ≤ next →
      WellOrdered next (compileMonomialFrom acc next j es).gates
  | [], _, _, _, _, _ => trivial
  | a :: es, acc, next, j, hacc, hj => by
    simp only [List.length_cons] at hj
    have h1 := mulPow_wellOrdered j a acc next hacc (by omega)
    have h2 := compileMonomialFrom_wellOrdered es (mulPow j acc next a).out
      (mulPow j acc next a).next (j + 1)
      (by rw [mulPow_next]; exact mulPow_out_lt j a acc next hacc) (by rw [mulPow_next]; omega)
    simp only [compileMonomialFrom, wellOrdered_append, mulPow_length]
    simp only [mulPow_next] at h2 ⊢
    exact ⟨h1, h2⟩

/-- **Soundness**: any assignment satisfying the gates reads `acc · (the monomial)` from the
output. -/
theorem compileMonomialFrom_sound {R : Type*} [Semiring R] (x : List R) :
    ∀ (es : MonomialCode) (acc next j : ℕ),
      (∀ g ∈ (compileMonomialFrom acc next j es).gates, g.Holds x) →
        x.getD (compileMonomialFrom acc next j es).out 0 = x.getD acc 0 * monomialValueFrom j es x
  | [], acc, next, j, _ => by simp [compileMonomialFrom, monomialValueFrom]
  | a :: es, acc, next, j, h => by
    simp only [compileMonomialFrom, List.forall_mem_append] at h
    obtain ⟨h1, h2⟩ := h
    have s1 := mulPow_sound j x a acc next h1
    have s2 := compileMonomialFrom_sound x es _ _ (j + 1) h2
    simp only [compileMonomialFrom, monomialValueFrom, s2, s1, mul_assoc]

/-- Compile one monomial, allocating from `next`: a wire holding `1`, then the multiplications.
The empty exponent vector compiles to that single wire. -/
def compileMonomial (e : MonomialCode) (next : ℕ) : Compiled :=
  let c := compileMonomialFrom next (next + 1) 0 e
  ⟨Gate.const next 1 :: c.gates, c.out, c.next⟩

theorem compileMonomial_next (e : MonomialCode) (n : ℕ) :
    (compileMonomial e n).next = n + 1 + e.sum := by
  simp [compileMonomial, compileMonomialFrom_next]

theorem compileMonomial_length (e : MonomialCode) (n : ℕ) :
    (compileMonomial e n).gates.length = 1 + e.sum := by
  simp [compileMonomial, compileMonomialFrom_length]
  omega

theorem compileMonomial_out_lt (e : MonomialCode) (n : ℕ) :
    (compileMonomial e n).out < (compileMonomial e n).next := by
  have := compileMonomialFrom_out_lt e n (n + 1) 0 (Nat.lt_succ_self n)
  simp only [compileMonomial, compileMonomialFrom_next]
  omega

/-- **Well-ordering**, given that the monomial reads only original variables below `n`. -/
theorem compileMonomial_wellOrdered (e : MonomialCode) (n : ℕ) (h : e.length ≤ n) :
    WellOrdered n (compileMonomial e n).gates :=
  ⟨⟨rfl, by simp [Gate.reads]⟩,
    compileMonomialFrom_wellOrdered e n (n + 1) 0 (Nat.lt_succ_self n) (by omega)⟩

/-- **Soundness**: any assignment satisfying the gates reads the monomial's value from the
output wire, over any semiring. -/
theorem compileMonomial_sound {R : Type*} [Semiring R] (e : MonomialCode) (n : ℕ) (x : List R)
    (h : ∀ g ∈ (compileMonomial e n).gates, g.Holds x) :
    x.getD (compileMonomial e n).out 0 = monomialValueFrom 0 e x := by
  simp only [compileMonomial, List.forall_mem_cons] at h
  obtain ⟨h0, hrest⟩ := h
  simp only [Gate.Holds, Gate.out, Gate.value, Nat.cast_one] at h0
  simp only [compileMonomial, compileMonomialFrom_sound x e n (n + 1) 0 hrest, h0, one_mul]

/-- The `ℤ` reading: the output wire carries `evalMonomialInt e x`. -/
theorem compileMonomial_sound_int (e : MonomialCode) (n : ℕ) (x : List ℤ)
    (h : ∀ g ∈ (compileMonomial e n).gates, g.Holds x) :
    x.getD (compileMonomial e n).out 0 = evalMonomialInt e x := by
  rw [compileMonomial_sound e n x h, evalMonomialInt_eq_monomialValue]

/-- The `ℕ` reading: the output wire carries `evalMonomial e x`, up to the cast. -/
theorem compileMonomial_sound_nat (e : MonomialCode) (n : ℕ) (x : List ℕ)
    (h : ∀ g ∈ (compileMonomial e n).gates, g.Holds x) :
    ((x.getD (compileMonomial e n).out 0 : ℕ) : ℤ) = evalMonomial e x := by
  rw [compileMonomial_sound e n x h, evalMonomial_eq_monomialValue]

/-! ### Regression examples -/

/-- The empty exponent vector: one wire, holding `1`. -/
example : compileMonomial [] 3 = ⟨[Gate.const 3 1], 3, 4⟩ := by decide

/-- Zero exponents allocate nothing: `x₂³` costs one constant and three multiplications. -/
example : (compileMonomial [0, 0, 3] 5).gates.length = 4 := by decide
example : (compileMonomial [0, 0, 3] 5).next = 9 := by decide

/-- `x₀² x₁` from wire `2`: the gates, in allocation order. -/
example : compileMonomial [2, 1] 2 =
    ⟨[Gate.const 2 1, Gate.mul 3 2 0, Gate.mul 4 3 0, Gate.mul 5 4 1], 5, 6⟩ := by
  decide

/-- Soundness, instantiated: at `x₀ = 3, x₁ = 4` the wires read `1, 3, 9, 36`, and the output
wire is the last. -/
example : ∀ g ∈ (compileMonomial [2, 1] 2).gates, g.Holds ([3, 4, 1, 3, 9, 36] : List ℕ) := by
  decide
example : ([3, 4, 1, 3, 9, 36] : List ℕ).getD (compileMonomial [2, 1] 2).out 0 = 36 := by
  decide

/-- The direction well-ordering exists for: a wrong value on the output wire cannot satisfy the
gates. -/
example : ¬ ∀ g ∈ (compileMonomial [2, 1] 2).gates, g.Holds ([3, 4, 1, 3, 9, 35] : List ℕ) := by
  decide

end Hilbert10
