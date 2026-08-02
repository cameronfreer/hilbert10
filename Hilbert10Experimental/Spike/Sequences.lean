/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.ExpDioph
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Route spike, direct route: sequence coding

Issue #15, second slice. The direct route replaces the machine's packed registers with
*coded sequences*, so this measures what that costs.

## The shape being tested

A witness-free step relation would understate the cost and merely retest the arithmetic
trace problem the machine slice already validated. What `prec` actually produces is a step
relation with **step-local existential witnesses**:

```
∀ i < t, ∃ w, Step params i (state i) (state (i + 1)) w
```

so the slice must code two variable-length objects — the state history *and* the collection
of per-step witness tuples — and then eliminate the bounded universal.

## Two gates

1. **Sequence coding.** Lookup has an `ExpDioph` graph, and every finite sequence is
   encodable.
2. **Bounded verification.** The variable conjunction of the *witnessed* step relation
   collapses to one `ExpDioph` relation, in both directions.

Gate 2 is where #33 — or a differently named theorem of comparable difficulty, whether
coefficient extraction, CRT aggregation, or masking — must be charged. The cost must not be
allowed to disappear into a strong sequence-coding lemma: what gets recorded is the theorem
that actually converts all indexed checks into one finite equation.

## The finite-witness boundary, for gate 2

`ExpDioph` existentially quantifies an *arbitrary* witness type, but the per-step witnesses
must be packed into finitely many β-coded sequences. Only finitely many witness variables
occur in the two `ExpTerm`s, yet that finiteness is not exposed by the proposition — so gate
2's converting theorem consumes an **explicit finite witness block**:

```lean
theorem expDioph_bounded_forall_eq
    (bound : ExpTerm α) (s t : ExpTerm ((α ⊕ Unit) ⊕ Fin m)) :
    ExpDioph { v | ∀ i < bound.eval v, ∃ w : Fin m → ℕ, s.eval … = t.eval … }
```

with the four ingredients visible: a variable bound, indexed checks, a genuinely nonempty
finite local witness block, and one witness tuple per index. Lifting this to arbitrary
`ExpDioph` relations is a finite-witness normalisation theorem, charged separately as
representation plumbing rather than as gate 2's number theory.

**The endpoint stays method-neutral.** No `product` in its statement, and no bounded-product
or bounded-forall constructor added to `ExpTerm` — either would relocate the missing proof
into new syntax rather than supply it. If the classical route is taken, its crucial
intermediate step is exposed *separately*, as `expDioph_bounded_product`, so the dependency
chain is visible:

```
#33 (or an alternative extraction theorem)
  ↓
bounded-product graph
  ↓
bounded witnessed conjunction
  ↓
expDioph_bounded_forall_eq
```

A cheaper non-product construction, if one exists, still fits the method-neutral endpoint.
And defining the semantic bounded product without proving its `ExpDioph` representation does
not advance gate 2 at all — the representation *is* the obligation.

## Gate 1, first half: the lookup graph

`beta a b i = a % (1 + (i + 1) * b)` is the Gödel β-function. Its graph is `ExpDioph` for
free, because `mod`, `mul` and `add` are `ExpTerm` constructors — a direct consequence of
#16's design decision to make `div` and `mod` constructors rather than closure lemmas.
-/

namespace Hilbert10

/-- The Gödel β-function: the `i`-th entry of the sequence coded by `(a, b)`. -/
def beta (a b i : ℕ) : ℕ := a % (1 + (i + 1) * b)

/-- The lookup term, over variables `a`, `b`, `i` given as an index map. -/
def betaTerm {α : Type} (a b i : α) : ExpTerm α :=
  .mod (.var a) (.add (.const 1) (.mul (.add (.var i) (.const 1)) (.var b)))

@[simp] theorem betaTerm_eval {α : Type} (a b i : α) (v : α → ℕ) :
    (betaTerm a b i).eval v = beta (v a) (v b) (v i) := rfl

/-- **Gate 1, first half.** The graph of the β-function is exponential Diophantine, with no
witnesses at all. This is free because `mod` is an `ExpTerm` constructor. -/
theorem expDioph_beta {α : Type} (a b i r : α) :
    ExpDioph {v : α → ℕ | beta (v a) (v b) (v i) = v r} :=
  ExpDioph.of_eq (s := betaTerm a b i) (t := .var r)

theorem dioph_beta {α : Type} (a b i r : α) :
    Dioph {v : α → ℕ | beta (v a) (v b) (v i) = v r} :=
  (expDioph_beta a b i r).dioph

/-! ### Gate 1, second half: the encoding theorem

Built on `Nat.chineseRemainderOfFinset`, which mathlib motivates by the β-function itself,
rather than on a recursive CRT of our own.

The modulus at index `i` is `1 + (i + 1) * b` with `b = n ! * (M + 1)` and `M` bounding the
entries. The factorial is used **only semantically**, to show an encoding exists; it does not
appear in any `ExpDioph` relation, so gate 1 charges no factorial-graph obligation.
-/

/-- The moduli used to code a sequence with spacing `b`. -/
private def modulus (b i : ℕ) : ℕ := 1 + (i + 1) * b

private theorem modulus_pos (b i : ℕ) : 0 < modulus b i := by simp [modulus]

/-- Any divisor of a modulus is coprime to the spacing: it divides `1 + (i + 1) * b`, and a
common factor with `b` would have to divide `1`. -/
private theorem coprime_of_dvd_modulus {b i d : ℕ} (hd : d ∣ modulus b i) :
    Nat.Coprime d b := by
  have hgd : Nat.gcd d b ∣ modulus b i := (Nat.gcd_dvd_left d b).trans hd
  have hgb : Nat.gcd d b ∣ (i + 1) * b := (Nat.gcd_dvd_right d b).mul_left (i + 1)
  have h1 : Nat.gcd d b ∣ 1 := by
    have := Nat.dvd_sub hgd hgb
    simpa [modulus] using this
  exact Nat.dvd_one.mp h1

/-- Distinct moduli are coprime, provided the spacing is divisible by the index gap. -/
private theorem coprime_modulus {b i j : ℕ} (hij : i < j)
    (hdvd : (j - i) ∣ b) : Nat.Coprime (modulus b i) (modulus b j) := by
  set d := Nat.gcd (modulus b i) (modulus b j) with hd
  have hdi : d ∣ modulus b i := Nat.gcd_dvd_left _ _
  have hdj : d ∣ modulus b j := Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime d b := coprime_of_dvd_modulus hdi
  -- `d` divides the difference of the moduli, which is `(j - i) * b`
  have hdiff : d ∣ (j - i) * b := by
    have := Nat.dvd_sub hdj hdi
    have heq : modulus b j - modulus b i = (j - i) * b := by
      simp only [modulus]
      have : (j + 1) * b - (i + 1) * b = (j - i) * b := by
        rw [← Nat.sub_mul]
        congr 1
        omega
      omega
    rwa [heq] at this
  -- coprimality with `b` promotes that to dividing `j - i`, hence dividing `b`
  have hdji : d ∣ j - i := (Nat.Coprime.dvd_of_dvd_mul_right hcop hdiff)
  have hdb : d ∣ b := hdji.trans hdvd
  exact hcop.eq_one_of_dvd hdb

/-- **Gate 1, second half.** Every finite sequence has a β-code.

Note the asymmetry, which is the point: the Chinese-remainder argument is needed only for
*completeness* — that every desired sequence has some code. Soundness needs no code-validity
predicate at all, because **every** pair `(a, b)` already denotes a sequence through `beta`.
Factorials, coprimality and CRT therefore live entirely in this existence proof and never
enter an `ExpDioph` relation.

This is the same permissiveness that paid off for `PolynomialCode`: malformed or
non-canonical representations do not exist, because every representation simply has
semantics. -/
theorem exists_beta_code {n : ℕ} (x : Fin n → ℕ) : ∃ a b, ∀ i : Fin n, beta a b i = x i := by
  classical
  set M := Finset.univ.sup x with hM
  set b := Nat.factorial n * (M + 1) with hb
  have hfac : 0 < Nat.factorial n := Nat.factorial_pos n
  have hbM : M < b := by
    have : M + 1 ≤ Nat.factorial n * (M + 1) := Nat.le_mul_of_pos_left _ hfac
    omega
  -- each entry is below its modulus
  have hlt : ∀ i : Fin n, x i < modulus b i := by
    intro i
    have hxM : x i ≤ M := Finset.le_sup (Finset.mem_univ i)
    have : b ≤ (i + 1) * b := Nat.le_mul_of_pos_left _ (by omega)
    simp only [modulus]
    omega
  -- distinct moduli are coprime, since the index gap divides `b`
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin n)))
      (Function.onFun Nat.Coprime fun i : Fin n => modulus b i) := by
    intro i _ j _ hij
    have key : ∀ p q : Fin n, p < q → Nat.Coprime (modulus b p) (modulus b q) := by
      intro p q hpq
      refine coprime_modulus hpq ?_
      have h1 : 0 < (q : ℕ) - p := by omega
      have h2 : (q : ℕ) - p ≤ n := by have := q.isLt; omega
      exact Dvd.dvd.mul_right (Nat.dvd_factorial h1 h2) _
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h) : (i : ℕ) ≠ j) with h | h
    · exact key i j h
    · exact (key j i h).symm
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset x (fun i : Fin n => modulus b i)
    Finset.univ (fun i _ => (modulus_pos b i).ne') hpair
  refine ⟨a, b, fun i => ?_⟩
  have hmod : a % modulus b i = x i % modulus b i := ha i (Finset.mem_univ i)
  rw [beta, ← modulus, hmod, Nat.mod_eq_of_lt (hlt i)]

/-! ### Substituting a lookup for a local witness

The plumbing gate 2 needs, demonstrated at `m = 1` on an equation the witness genuinely
affects — so the instance cannot degenerate to the witness-free case. `ExpTerm.map` cannot
express this, since it only renames variables; `ExpTerm.subst` replaces a variable by a term.
-/

/-- Replace the single local witness variable by a lookup into the sequence coded by
`(a, b)` at index `i`, leaving the outer variables alone. -/
def substLookup {α : Type} (a b i : α) : ExpTerm (α ⊕ Fin 1) → ExpTerm α :=
  ExpTerm.subst (Sum.elim ExpTerm.var fun _ => betaTerm a b i)

@[simp] theorem eval_substLookup {α : Type} (a b i : α) (s : ExpTerm (α ⊕ Fin 1))
    (v : α → ℕ) :
    (substLookup a b i s).eval v =
      s.eval (Sum.elim v fun _ => beta (v a) (v b) (v i)) := by
  simp only [substLookup, ExpTerm.eval_subst]
  congr 1
  funext z
  cases z <;> simp [ExpTerm.eval]

/-- Acceptance instance: the local witness occurs on both sides of a nontrivial equation, so
substituting a lookup for it cannot collapse to a witness-free statement. -/
example {α : Type} (a b i : α) (v : α → ℕ) :
    (substLookup a b i (.add (.var (Sum.inr 0)) (.var (Sum.inr 0)))).eval v =
      2 * beta (v a) (v b) (v i) := by
  simp [ExpTerm.eval]
  ring

/-- And the witness really is load-bearing: the substituted equation constrains the coded
value, rather than holding for every sequence. -/
example {α : Type} (a b i x : α) (v : α → ℕ) :
    ((substLookup a b i (.add (.var (Sum.inr 0)) (.const 1))).eval v = v x) ↔
      beta (v a) (v b) (v i) + 1 = v x := by
  simp [ExpTerm.eval]

/-! ### Gate 2, step one: eliminating the per-step witnesses

Before attacking the bounded universal itself, separate out the *witness* half. Coding one
sequence per witness variable turns

```
∀ i < N, ∃ w : Fin m → ℕ, P i w
```

into a statement with no inner existential at all, at the cost of `2 * m` outer variables.
This direction is cheap — it is exactly what gate 1 bought — and isolating it means the
residual cost is attributable to the bounded universal *alone*.

Note which way the two halves of gate 1 are used: completeness (`exists_beta_code`, and so
CRT) proves the forward direction, while the backward direction needs only that every
`(a, b)` denotes *some* sequence, i.e. the totality of `beta`. -/
theorem bounded_forall_witness_iff {m : ℕ} (N : ℕ) (P : ℕ → (Fin m → ℕ) → Prop) :
    (∀ i < N, ∃ w : Fin m → ℕ, P i w) ↔
      ∃ a b : Fin m → ℕ, ∀ i < N, P i fun j => beta (a j) (b j) i := by
  classical
  constructor
  · intro h
    -- pick a witness tuple at each index, then code each component as a sequence
    let W : Fin N → (Fin m → ℕ) := fun i => Classical.choose (h i i.isLt)
    have hW : ∀ i : Fin N, P i (W i) := fun i => Classical.choose_spec (h i i.isLt)
    choose a b hab using fun j : Fin m => exists_beta_code fun i : Fin N => W i j
    refine ⟨a, b, fun i hi => ?_⟩
    have hfun : (fun j => beta (a j) (b j) i) = W ⟨i, hi⟩ := by
      funext j
      exact hab j ⟨i, hi⟩
    rw [hfun]
    exact hW ⟨i, hi⟩
  · rintro ⟨a, b, h⟩ i hi
    exact ⟨_, h i hi⟩

/-- The residual obligation, stated so the accounting is unmistakable: after
`bounded_forall_witness_iff`, what remains is a bounded universal over a **witness-free**
condition. Gate 2's entire mathematical cost lives here. -/
def BoundedForall (N : ℕ) (Q : ℕ → Prop) : Prop := ∀ i < N, Q i

theorem bounded_forall_witness_iff' {m : ℕ} (N : ℕ) (P : ℕ → (Fin m → ℕ) → Prop) :
    (∀ i < N, ∃ w : Fin m → ℕ, P i w) ↔
      ∃ a b : Fin m → ℕ, BoundedForall N fun i => P i fun j => beta (a j) (b j) i :=
  bounded_forall_witness_iff N P

/-! ### Gate 2, step two: the bounded universal becomes a bounded product

With the witnesses eliminated, what remains is `∀ i < N, f i = g i` for exponential-polynomial
`f, g`. Over `ℕ` this collapses to a single **bounded product** equalling one, since each
factor is at least one and a product of naturals is one exactly when every factor is:

```
(∀ i < N, f i = g i)  ↔  ∏ i < N, (1 + (f i ∸ g i) + (g i ∸ f i)) = 1
```

The reduction itself is elementary arithmetic — proved below. What it does **not** do is
discharge gate 2: it relocates the obligation onto the exponential-Diophantine representation
of the bounded product, which is where the mathematical cost actually sits.

Naming that residual obligation explicitly, per the method-neutrality guardrail, so the
dependency chain stays legible rather than being absorbed into the endpoint:

```
extraction theorem (#33, or an alternative)
  ↓  expDioph_bounded_product     -- the graph of ∏ i < N, h i
  ↓  bounded witnessed conjunction
  ↓  expDioph_bounded_forall_eq
```

Defining the semantic product, as done here, advances the *reduction* but not the
representation. The representation is the obligation, and it remains open.

### The residual theorem, stated properly

Two constraints on how it may be stated, both of which prevent a vacuous claim.

**Index by an `ExpTerm`, not a semantic function.** Written with an arbitrary `h : ℕ → ℕ`
the statement would silently assume `h` representable, which is most of the difficulty. So:

```lean
theorem expDioph_bounded_product_eq_one
    (bound : ExpTerm α) (h : ExpTerm (α ⊕ Unit)) :
    ExpDioph { v | ∏ i ∈ Finset.range (bound.eval v),
                     h.eval (Sum.elim v fun _ => i) = 1 }
```

**Prove only what the endpoint needs.** Equality to `1`, not a general graph with arbitrary
output; the stronger theorem is not required unless it falls out free.

### The circularity trap

Coding the successive partial products with `beta` and requiring

```
p (i + 1) = p i * h i
```

does **not** discharge this. That trace-validity condition is itself a variable bounded
conjunction of step equations — the very thing being eliminated — so the construction merely
reproduces the problem one level down. It counts only if that condition is aggregated by an
*independently proved* theorem.

Attribution therefore belongs at the **deepest non-circular representation theorem**, not at
whichever lemma happens to sit closest to the endpoint.
-/

/-- The gap term: zero exactly when the two sides agree. -/
def gap (f g : ℕ → ℕ) (i : ℕ) : ℕ := 1 + (f i - g i) + (g i - f i)

theorem one_le_gap (f g : ℕ → ℕ) (i : ℕ) : 1 ≤ gap f g i := by simp only [gap]; omega

theorem gap_eq_one_iff {f g : ℕ → ℕ} {i : ℕ} : gap f g i = 1 ↔ f i = g i := by
  simp only [gap]; omega

/-- **The reduction.** A bounded universal over an equation is a single bounded product
equalling one. Elementary; the cost is in representing the product, not in this step. -/
theorem boundedForall_eq_iff_prod (f g : ℕ → ℕ) (N : ℕ) :
    BoundedForall N (fun i => f i = g i) ↔ ∏ i ∈ Finset.range N, gap f g i = 1 := by
  rw [Finset.prod_eq_one_iff]
  constructor
  · intro h i hi
    exact gap_eq_one_iff.mpr (h i (Finset.mem_range.mp hi))
  · intro h i hi
    exact gap_eq_one_iff.mp (h i (Finset.mem_range.mpr hi))

end Hilbert10
