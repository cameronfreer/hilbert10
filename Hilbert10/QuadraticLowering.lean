/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.QuadraticGates

/-!
# Quadratic lowering: compiling expressions to well-ordered gate lists

Issue #57, second checkpoint. This module will hold the transformation from one polynomial
equation to a quadratic system. Its first stage is **one monomial**; the second compiles the
**whole polynomial** into two accumulators, below.
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
* `Hilbert10.CompiledPoly`, `Hilbert10.compileTerm`, `Hilbert10.compilePoly`

## Main results

* `Hilbert10.compileMonomial_wellOrdered`, `compileMonomial_next`, `compileMonomial_out_lt`
* `Hilbert10.compileMonomial_sound`, and its `ℤ` and `ℕ` readings
* `Hilbert10.compilePoly_wellOrdered`, `compilePoly_length` (exact: `1 + Σ (exponent sum + 4)`),
  `compilePoly_next`, `compilePoly_pos_lt`, `compilePoly_neg_lt`
* `Hilbert10.compilePoly_sound` (`evalInt p y = y[pos] − y[neg]` at any satisfying `y`) and
  `compilePoly_sound_nat`
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

/-! ### The whole polynomial, with two accumulators

A polynomial is compiled in one pass. The state carries the gates so far, the next unused wire,
and the two accumulator wires: `pos` collects the terms with nonnegative coefficient, `neg` those
with negative coefficient, each as a sum of `|c| · monomial`. Both start at one wire holding
`0`. Zero coefficients are processed like any other; skipping them would be an optimisation
with no role in correctness.

The invariant `evalInt p y = y[pos] − y[neg]` is stated over `ℤ` for *any* satisfying
assignment, and the natural reading is obtained through the cast — never through truncated
subtraction. -/

/-- A partially or fully compiled polynomial. -/
structure CompiledPoly where
  /-- The defining gates so far. -/
  gates : List Gate
  /-- The wire accumulating the terms with nonnegative coefficient. -/
  pos : ℕ
  /-- The wire accumulating the terms with negative coefficient. -/
  neg : ℕ
  /-- The next unused wire. -/
  next : ℕ
  deriving DecidableEq, Repr

/-- The gates one term adds: its monomial, a constant holding `|c|`, their product, and the
addition into the accumulator its sign selects. -/
def termGates (s : CompiledPoly) (t : ℤ × MonomialCode) : List Gate :=
  let cm := compileMonomial t.2 s.next
  cm.gates ++ [Gate.const cm.next t.1.natAbs, Gate.mul (cm.next + 1) cm.out cm.next,
    Gate.add (cm.next + 2) (if 0 ≤ t.1 then s.pos else s.neg) (cm.next + 1)]

/-- Compile one term onto the state. -/
def compileTerm (s : CompiledPoly) (t : ℤ × MonomialCode) : CompiledPoly :=
  let cm := compileMonomial t.2 s.next
  { gates := s.gates ++ termGates s t
    pos := if 0 ≤ t.1 then cm.next + 2 else s.pos
    neg := if 0 ≤ t.1 then s.neg else cm.next + 2
    next := cm.next + 3 }

/-- Compile a term list onto the state, left to right. -/
def compileTerms (s : CompiledPoly) : List (ℤ × MonomialCode) → CompiledPoly
  | [] => s
  | t :: ts => compileTerms (compileTerm s t) ts

/-- **Compile a polynomial**, allocating from `next`: a zero wire that both accumulators start
from, then the terms in order. -/
def compilePoly (p : PolynomialCode) (next : ℕ) : CompiledPoly :=
  compileTerms ⟨[Gate.const next 0], next, next, next + 1⟩ p.terms

theorem termGates_length (s : CompiledPoly) (t : ℤ × MonomialCode) :
    (termGates s t).length = t.2.sum + 4 := by
  simp only [termGates, List.length_append, compileMonomial_length, List.length_cons,
    List.length_nil]
  omega

theorem termGates_wellOrdered (s : CompiledPoly) (t : ℤ × MonomialCode) (hpos : s.pos < s.next)
    (hneg : s.neg < s.next) (he : t.2.length ≤ s.next) : WellOrdered s.next (termGates s t) := by
  have hout := compileMonomial_out_lt t.2 s.next
  have hnext := compileMonomial_next t.2 s.next
  simp only [termGates, wellOrdered_append, compileMonomial_length]
  refine ⟨compileMonomial_wellOrdered _ _ he, ?_⟩
  by_cases hc : 0 ≤ t.1 <;>
    simp only [hc, if_true, if_false, WellOrdered, Gate.Fresh, Gate.out, Gate.reads,
      List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] <;>
    omega

/-- **Soundness of one term**: any assignment satisfying its gates moves `pos − neg` by exactly
`c · monomial`. -/
theorem termGates_sound (s : CompiledPoly) (t : ℤ × MonomialCode) (y : List ℤ)
    (h : ∀ g ∈ termGates s t, g.Holds y) :
    y.getD (compileTerm s t).pos 0 - y.getD (compileTerm s t).neg 0 =
      y.getD s.pos 0 - y.getD s.neg 0 + t.1 * evalMonomialInt t.2 y := by
  simp only [termGates, List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true] at h
  obtain ⟨hm, hk, hmul, hadd⟩ := h
  have hout := compileMonomial_sound_int t.2 s.next y hm
  simp only [Gate.Holds, Gate.out, Gate.value] at hk hmul hadd
  simp only [compileTerm]
  rw [Int.natCast_natAbs] at hk
  by_cases hc : 0 ≤ t.1
  · simp only [hc, if_true] at hadd ⊢
    rw [hadd, hmul, hout, hk, abs_of_nonneg hc]
    ring
  · simp only [hc, if_false] at hadd ⊢
    rw [hadd, hmul, hout, hk, abs_of_neg (lt_of_not_ge hc)]
    ring

theorem mem_gates_compileTerms (s : CompiledPoly) :
    ∀ ts, ∀ g ∈ s.gates, g ∈ (compileTerms s ts).gates
  | [], _, hg => hg
  | t :: ts, g, hg =>
    mem_gates_compileTerms (compileTerm s t) ts g (by simp [compileTerm, hg])

/-- The invariant carried along the fold: well ordered from `n`, exact bookkeeping, and both
accumulators already allocated. -/
structure CompiledPoly.Inv (n : ℕ) (s : CompiledPoly) : Prop where
  wellOrdered : WellOrdered n s.gates
  next_eq : s.next = n + s.gates.length
  pos_lt : s.pos < s.next
  neg_lt : s.neg < s.next

theorem CompiledPoly.Inv.compileTerm {n : ℕ} {s : CompiledPoly} (hs : s.Inv n)
    {t : ℤ × MonomialCode} (he : t.2.length ≤ n) : (Hilbert10.compileTerm s t).Inv n where
  wellOrdered := by
    simp only [Hilbert10.compileTerm, wellOrdered_append]
    rw [← hs.next_eq]
    exact ⟨hs.wellOrdered, termGates_wellOrdered s t hs.pos_lt hs.neg_lt
      (he.trans (by rw [hs.next_eq]; exact Nat.le_add_right n _))⟩
  next_eq := by
    have := compileMonomial_next t.2 s.next
    simp only [Hilbert10.compileTerm, List.length_append, termGates_length, hs.next_eq] at this ⊢
    omega
  pos_lt := by
    have := compileMonomial_next t.2 s.next
    have := hs.pos_lt
    simp only [Hilbert10.compileTerm]
    split_ifs <;> omega
  neg_lt := by
    have := compileMonomial_next t.2 s.next
    have := hs.neg_lt
    simp only [Hilbert10.compileTerm]
    split_ifs <;> omega

theorem CompiledPoly.Inv.compileTerms {n : ℕ} :
    ∀ (ts : List (ℤ × MonomialCode)) {s : CompiledPoly}, s.Inv n → (∀ t ∈ ts, t.2.length ≤ n) →
      (Hilbert10.compileTerms s ts).Inv n
  | [], _, hs, _ => hs
  | t :: ts, s, hs, h =>
    CompiledPoly.Inv.compileTerms ts (hs.compileTerm (h t (by simp)))
      fun u hu => h u (by simp [hu])

theorem compileTerms_length (s : CompiledPoly) :
    ∀ ts : List (ℤ × MonomialCode),
      (compileTerms s ts).gates.length = s.gates.length + (ts.map fun t => t.2.sum + 4).sum
  | [] => by simp [compileTerms]
  | t :: ts => by
    change (compileTerms (compileTerm s t) ts).gates.length = _
    rw [compileTerms_length (compileTerm s t) ts]
    simp only [compileTerm, List.length_append, termGates_length, List.map_cons, List.sum_cons]
    omega

theorem compileTerms_next (s : CompiledPoly) :
    ∀ ts : List (ℤ × MonomialCode),
      (compileTerms s ts).next = s.next + (ts.map fun t => t.2.sum + 4).sum
  | [] => by simp [compileTerms]
  | t :: ts => by
    change (compileTerms (compileTerm s t) ts).next = _
    rw [compileTerms_next (compileTerm s t) ts]
    simp only [compileTerm, compileMonomial_next, List.map_cons, List.sum_cons]
    omega

/-- **Soundness of the fold**: any satisfying assignment moves `pos − neg` by exactly the value
of the terms compiled. -/
theorem compileTerms_sound (y : List ℤ) :
    ∀ (ts : List (ℤ × MonomialCode)) (s : CompiledPoly),
      (∀ g ∈ (compileTerms s ts).gates, g.Holds y) →
        y.getD (compileTerms s ts).pos 0 - y.getD (compileTerms s ts).neg 0 =
          y.getD s.pos 0 - y.getD s.neg 0 + evalInt ⟨ts⟩ y
  | [], s, _ => by simp [compileTerms]
  | t :: ts, s, h => by
    have h1 : ∀ g ∈ termGates s t, g.Holds y := fun g hg =>
      h g (mem_gates_compileTerms _ ts g (by simp [compileTerm, hg]))
    have e1 := termGates_sound s t y h1
    have e2 := compileTerms_sound y ts (compileTerm s t) h
    simp only [compileTerms] at e2 ⊢
    rw [e2, e1, evalInt_mk_cons]
    ring

/-! ### The polynomial-level contracts -/

theorem compilePoly_inv (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    (compilePoly p n).Inv n := by
  have h0 : CompiledPoly.Inv n ⟨[Gate.const n 0], n, n, n + 1⟩ :=
    ⟨by simp [WellOrdered, Gate.Fresh, Gate.reads, Gate.out], rfl, Nat.lt_succ_self n,
      Nat.lt_succ_self n⟩
  exact CompiledPoly.Inv.compileTerms p.terms h0 fun t ht => (length_le_arity ht).trans h

/-- **Well-ordering**, given that allocation starts at or above the arity. -/
theorem compilePoly_wellOrdered (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    WellOrdered n (compilePoly p n).gates :=
  (compilePoly_inv p n h).wellOrdered

/-- **Exact bookkeeping**: one zero wire, then `exponent sum + 4` gates per term. -/
theorem compilePoly_length (p : PolynomialCode) (n : ℕ) :
    (compilePoly p n).gates.length = 1 + (p.terms.map fun t => t.2.sum + 4).sum := by
  simp [compilePoly, compileTerms_length]

/-- Bookkeeping needs no freshness hypothesis: the next wire is always `n + gates.length`. -/
theorem compilePoly_next (p : PolynomialCode) (n : ℕ) :
    (compilePoly p n).next = n + (compilePoly p n).gates.length := by
  rw [compilePoly_length]
  simp only [compilePoly, compileTerms_next]
  omega

theorem compilePoly_pos_lt (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    (compilePoly p n).pos < (compilePoly p n).next :=
  (compilePoly_inv p n h).pos_lt

theorem compilePoly_neg_lt (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    (compilePoly p n).neg < (compilePoly p n).next :=
  (compilePoly_inv p n h).neg_lt

/-- **Soundness over `ℤ`**: at any assignment satisfying the gates, the polynomial's value is
the positive accumulator minus the negative one. No freshness hypothesis: this is algebra. -/
theorem compilePoly_sound (p : PolynomialCode) (n : ℕ) (y : List ℤ)
    (h : ∀ g ∈ (compilePoly p n).gates, g.Holds y) :
    evalInt p y = y.getD (compilePoly p n).pos 0 - y.getD (compilePoly p n).neg 0 := by
  have hz : y.getD n 0 = 0 := by
    have := h (Gate.const n 0) (mem_gates_compileTerms _ p.terms _ (by simp))
    simpa [Gate.Holds, Gate.out, Gate.value] using this
  rw [compilePoly, compileTerms_sound y p.terms _ h, hz]
  simp

/-- **Soundness over `ℕ`**, through the cast: never a truncated subtraction. -/
theorem compilePoly_sound_nat (p : PolynomialCode) (n : ℕ) (y : List ℕ)
    (h : ∀ g ∈ (compilePoly p n).gates, g.Holds y) :
    eval p y =
      ((y.getD (compilePoly p n).pos 0 : ℕ) : ℤ) - ((y.getD (compilePoly p n).neg 0 : ℕ) : ℤ) := by
  rw [← evalInt_map_natCast, compilePoly_sound p n (y.map Nat.cast)
    (fun g hg => (Gate.holds_map_natCast g y).mpr (h g hg)), getD_map_natCast, getD_map_natCast]

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

/-- The constant `1`: a zero wire, a `1` wire, `|1|`, their product, and the positive
accumulator. Five gates, `pos` last, `neg` still the zero wire. -/
example : compilePoly ⟨[(1, [])]⟩ 0 =
    ⟨[Gate.const 0 0, Gate.const 1 1, Gate.const 2 1, Gate.mul 3 1 2, Gate.add 4 0 3],
      4, 0, 5⟩ := by
  decide

/-- The constant `−1` takes the other branch: `neg` last, `pos` the zero wire. -/
example : (compilePoly ⟨[(-1, [])]⟩ 0).pos = 0 := by decide
example : (compilePoly ⟨[(-1, [])]⟩ 0).neg = 4 := by decide

/-- Soundness, instantiated on `−1`: the satisfying assignment reads `pos − neg = 0 − 1`. -/
example : ∀ g ∈ (compilePoly ⟨[(-1, [])]⟩ 0).gates, g.Holds ([0, 1, 1, 1, 1] : List ℤ) := by
  decide
example : ([0, 1, 1, 1, 1] : List ℤ).getD (compilePoly ⟨[(-1, [])]⟩ 0).pos 0 -
    ([0, 1, 1, 1, 1] : List ℤ).getD (compilePoly ⟨[(-1, [])]⟩ 0).neg 0 = -1 := by
  decide

/-- The count formula on `x₀ − 1` from wire `1`: `1 + (1 + 4) + (0 + 4)`. -/
example : (compilePoly ⟨[(1, [1]), (-1, [])]⟩ 1).gates.length = 10 := by decide

end Hilbert10
