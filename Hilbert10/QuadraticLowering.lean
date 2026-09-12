/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.QuadraticGates
import Hilbert10.Systems

/-!
# Quadratic lowering: compiling expressions to well-ordered gate lists

Issue #57, second checkpoint: the transformation from one polynomial equation to a system of
equations of degree at most two. Its first stage is **one monomial**; the second compiles the
**whole polynomial** into two accumulators; the third turns the gates into equations, appends
the terminal equality, and proves root equivalence over `ℕ` and `ℤ` with the bounds.
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
* `Hilbert10.quadraticSystem`, `gateCount`; `quadraticSystem_eval_zero_iff` (pointwise semantics),
  `evalInt_eq_zero_iff_exists_aux` (extension correctness), and the two root equivalences
  `intSolvable_iff_systemIntSolvable_quadraticSystem`,
  `natSolvable_iff_systemNatSolvable_quadraticSystem`
* `Hilbert10.systemDegreeBound_quadraticSystem_le` (`≤ 2`), `systemArity_quadraticSystem_le`
  (`≤ p.arity + gateCount p`), `quadraticSystem_length` (`gateCount p + 1`)
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

/-! ### The quadratic system

The defining gates become equations, and one more equation — the terminal equality of the two
accumulators — is appended. That last equation is a *constraint*, not a gate: it allocates no
wire, takes no part in `WellOrdered`, and is exactly what relates the accumulators. Without it
every nonzero constant would be "solvable". -/

/-- The number of auxiliary variables the lowering allocates. -/
def gateCount (p : PolynomialCode) : ℕ := (compilePoly p p.arity).gates.length

/-- **The quadratic system of a polynomial**: its defining gates as equations, then the terminal
equality `pos = neg`. Allocation starts at `p.arity`, so the original variables are a prefix. -/
def quadraticSystem (p : PolynomialCode) : List PolynomialCode :=
  (compilePoly p p.arity).gates.map Gate.code ++
    [eqGate (compilePoly p p.arity).pos (compilePoly p p.arity).neg]

theorem quadraticSystem_length (p : PolynomialCode) :
    (quadraticSystem p).length = gateCount p + 1 := by
  simp [quadraticSystem, gateCount]

/-- **Pointwise semantics over `ℤ`**: the system vanishes at `y` exactly when every defining
gate holds and the two accumulators agree. -/
theorem quadraticSystem_eval_zero_iff (p : PolynomialCode) (y : List ℤ) :
    (∀ q ∈ quadraticSystem p, evalInt q y = 0) ↔
      (∀ g ∈ (compilePoly p p.arity).gates, g.Holds y) ∧
        y.getD (compilePoly p p.arity).pos 0 = y.getD (compilePoly p p.arity).neg 0 := by
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    Gate.evalInt_code_eq_zero_iff, evalInt_eqGate_eq_zero_iff]

/-- **Pointwise semantics over `ℕ`.** -/
theorem quadraticSystem_eval_zero_iff_nat (p : PolynomialCode) (y : List ℕ) :
    (∀ q ∈ quadraticSystem p, eval q y = 0) ↔
      (∀ g ∈ (compilePoly p p.arity).gates, g.Holds y) ∧
        y.getD (compilePoly p p.arity).pos 0 = y.getD (compilePoly p p.arity).neg 0 := by
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    Gate.eval_code_eq_zero_iff, eval_eqGate_eq_zero_iff]

/-! ### Extension correctness

Freshness guarantees the gates can be satisfied; the polynomial's arity guarantees that the
auxiliary suffix is invisible to it. Both are needed, and they are used at different steps. -/

/-- **Extension correctness over `ℤ`**: an exact-arity assignment is a root exactly when some
auxiliary suffix of length `gateCount p` makes the whole system vanish. -/
theorem evalInt_eq_zero_iff_exists_aux (p : PolynomialCode) (x : List ℤ)
    (hx : x.length = p.arity) :
    evalInt p x = 0 ↔
      ∃ aux : List ℤ, aux.length = gateCount p ∧
        ∀ q ∈ quadraticSystem p, evalInt q (x ++ aux) = 0 := by
  have hwo := compilePoly_wellOrdered p p.arity le_rfl
  constructor
  · intro h0
    obtain ⟨y, hy, hyx, hg⟩ := exists_extension _ _ hwo x hx
    refine ⟨y.drop p.arity, ?_, ?_⟩
    · simp [hy, gateCount]
    · have hsplit : x ++ y.drop p.arity = y := by rw [← hyx, List.take_append_drop]
      rw [hsplit, quadraticSystem_eval_zero_iff]
      refine ⟨hg, ?_⟩
      have hs := compilePoly_sound p p.arity y hg
      have hval : evalInt p y = 0 := by
        rw [← hsplit, evalInt_append_of_arity_le (by rw [hx])]
        exact h0
      rw [hval] at hs
      exact sub_eq_zero.mp hs.symm
  · rintro ⟨aux, -, hsys⟩
    rw [quadraticSystem_eval_zero_iff] at hsys
    obtain ⟨hg, heq⟩ := hsys
    have hs := compilePoly_sound p p.arity (x ++ aux) hg
    rw [evalInt_append_of_arity_le (by rw [hx]), heq, sub_self] at hs
    exact hs

/-- **Extension correctness over `ℕ`**: natural inputs get natural auxiliaries. -/
theorem eval_eq_zero_iff_exists_aux (p : PolynomialCode) (x : List ℕ)
    (hx : x.length = p.arity) :
    eval p x = 0 ↔
      ∃ aux : List ℕ, aux.length = gateCount p ∧
        ∀ q ∈ quadraticSystem p, eval q (x ++ aux) = 0 := by
  have hwo := compilePoly_wellOrdered p p.arity le_rfl
  constructor
  · intro h0
    obtain ⟨y, hy, hyx, hg⟩ := exists_extension _ _ hwo x hx
    refine ⟨y.drop p.arity, ?_, ?_⟩
    · simp [hy, gateCount]
    · have hsplit : x ++ y.drop p.arity = y := by rw [← hyx, List.take_append_drop]
      rw [hsplit, quadraticSystem_eval_zero_iff_nat]
      refine ⟨hg, ?_⟩
      have hs := compilePoly_sound_nat p p.arity y hg
      have hval : eval p y = 0 := by
        rw [← hsplit, eval_append_of_arity_le (by rw [hx])]
        exact h0
      rw [hval] at hs
      exact_mod_cast sub_eq_zero.mp hs.symm
  · rintro ⟨aux, -, hsys⟩
    rw [quadraticSystem_eval_zero_iff_nat] at hsys
    obtain ⟨hg, heq⟩ := hsys
    have hs := compilePoly_sound_nat p p.arity (x ++ aux) hg
    rw [eval_append_of_arity_le (by rw [hx]), heq, sub_self] at hs
    exact hs

/-! ### Root equivalence, unrestricted

Forward, the source witness is normalised to exact arity and extended. Backward, the entire
satisfying assignment is the source witness: `compilePoly_sound` holds at any length, and the
polynomial does not see the suffix, so no prefix has to be reconstructed. -/

/-- **A polynomial has an integer root exactly when its quadratic system does.** -/
theorem intSolvable_iff_systemIntSolvable_quadraticSystem (p : PolynomialCode) :
    IntSolvable p ↔ SystemIntSolvable (quadraticSystem p) := by
  constructor
  · intro h
    obtain ⟨x, hx, h0⟩ := (intSolvable_iff_arity p).mp h
    obtain ⟨aux, -, hsys⟩ := (evalInt_eq_zero_iff_exists_aux p x hx).mp h0
    exact ⟨x ++ aux, hsys⟩
  · rintro ⟨y, hy⟩
    rw [quadraticSystem_eval_zero_iff] at hy
    obtain ⟨hg, heq⟩ := hy
    refine ⟨y, ?_⟩
    rw [compilePoly_sound p p.arity y hg, heq, sub_self]

/-- **A polynomial has a natural root exactly when its quadratic system does.** -/
theorem natSolvable_iff_systemNatSolvable_quadraticSystem (p : PolynomialCode) :
    NatSolvable p ↔ SystemNatSolvable (quadraticSystem p) := by
  constructor
  · intro h
    obtain ⟨x, hx, h0⟩ := (natSolvable_iff_arity p).mp h
    obtain ⟨aux, -, hsys⟩ := (eval_eq_zero_iff_exists_aux p x hx).mp h0
    exact ⟨x ++ aux, hsys⟩
  · rintro ⟨y, hy⟩
    rw [quadraticSystem_eval_zero_iff_nat] at hy
    obtain ⟨hg, heq⟩ := hy
    refine ⟨y, ?_⟩
    rw [compilePoly_sound_nat p p.arity y hg, heq, sub_self]

/-! ### Bounds -/

/-- **Every equation of the system is quadratic.** -/
theorem systemDegreeBound_quadraticSystem_le (p : PolynomialCode) :
    systemDegreeBound (quadraticSystem p) ≤ 2 := by
  rw [systemDegreeBound_le_iff]
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true]
  exact ⟨fun g _ => Gate.degreeBound_code_le g, (degreeBound_eqGate_le _ _).trans one_le_two⟩

/-- In a well-ordered list starting at `n`, every gate writes below `n + length` and reads below
what it writes. -/
theorem WellOrdered.out_lt_and_reads_lt {n : ℕ} :
    ∀ {gs : List Gate}, WellOrdered n gs →
      ∀ g ∈ gs, g.out < n + gs.length ∧ ∀ r ∈ g.reads, r < g.out
  | [], _, g, hg => by simp at hg
  | g' :: gs, ⟨⟨hout, hreads⟩, hwo⟩, g, hg => by
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact ⟨by simp [hout], by rw [hout]; exact hreads⟩
    · obtain ⟨h1, h2⟩ := WellOrdered.out_lt_and_reads_lt hwo g hg'
      exact ⟨by simp only [List.length_cons]; omega, h2⟩

/-- **The system uses at most `p.arity + gateCount p` variables.** -/
theorem systemArity_quadraticSystem_le (p : PolynomialCode) :
    systemArity (quadraticSystem p) ≤ p.arity + gateCount p := by
  have hwo := compilePoly_wellOrdered p p.arity le_rfl
  have hnext := compilePoly_next p p.arity
  rw [systemArity_le_iff]
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true, gateCount]
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨hout, hreads⟩ := hwo.out_lt_and_reads_lt g hg
    exact (Gate.arity_code_le g hreads).trans (by omega)
  · have hp := compilePoly_pos_lt p p.arity le_rfl
    have hn := compilePoly_neg_lt p p.arity le_rfl
    exact (arity_eqGate_le _ _).trans (by omega)

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

/-- **The first end-to-end rejections**: the constants `1` and `−1`, one per accumulator branch.
Without the terminal constraint both systems would be satisfiable. -/
example : ¬ SystemNatSolvable (quadraticSystem ⟨[(1, [])]⟩) := by
  rw [← natSolvable_iff_systemNatSolvable_quadraticSystem]
  rintro ⟨x, hx⟩
  simp [eval, evalMonomial] at hx

example : ¬ SystemIntSolvable (quadraticSystem ⟨[(-1, [])]⟩) := by
  rw [← intSolvable_iff_systemIntSolvable_quadraticSystem]
  rintro ⟨x, hx⟩
  simp [evalInt, evalMonomialInt] at hx

/-- The empty polynomial is satisfiable, and its system is one zero wire and the terminal equality
of that wire with itself. -/
example : SystemNatSolvable (quadraticSystem ⟨[]⟩) :=
  (natSolvable_iff_systemNatSolvable_quadraticSystem _).mp ⟨[], rfl⟩
example : quadraticSystem ⟨[]⟩ = [constGate 0 0, eqGate 0 0] := rfl

/-- **Cancellation**: `x₀ − x₀`. Both accumulators are nonzero at `x₀ = 3`, yet the terminal
equality holds; the system is satisfied at the extension `[3, 0, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3]`,
where the positive accumulator (wire `6`) and the negative one (wire `11`) both read `3`. -/
example : ∀ q ∈ quadraticSystem ⟨[(1, [1]), (-1, [1])]⟩,
    evalInt q ([3, 0, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3] : List ℤ) = 0 := by
  decide
example : SystemIntSolvable (quadraticSystem ⟨[(1, [1]), (-1, [1])]⟩) :=
  ⟨[3, 0, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3], by decide⟩

/-- The bounds, instantiated on `x₀² + x₁ − 5`: `gateCount = 1 + 6 + 5 + 4 = 16`, so seventeen
equations of degree at most two, in at most `2 + 16` variables. -/
example : gateCount ⟨[(1, [2]), (1, [0, 1]), (-5, [])]⟩ = 16 := by decide
example : (quadraticSystem ⟨[(1, [2]), (1, [0, 1]), (-5, [])]⟩).length = 17 := by decide
example : systemDegreeBound (quadraticSystem ⟨[(1, [2]), (1, [0, 1]), (-5, [])]⟩) = 2 := by
  decide

end Hilbert10
