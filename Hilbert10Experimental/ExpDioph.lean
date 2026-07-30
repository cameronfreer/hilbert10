/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.NumberTheory.Dioph

/-!
# Exponential Diophantine relations

Issue #16, and the first piece of M4. This layer is **route-independent**: both the machine
route and the direct route arithmetise into exponential Diophantine relations, and #15's
spike must produce one, so it is a prerequisite for the route decision rather than a
consequence of it.

## Why ℕ-valued

`ExpTerm` is valued in `ℕ`, and `ExpDioph` is *equality of two ℕ-valued terms* under ℕ
witnesses. An `ℤ`-valued exponential term would leave `s ^ t` ill-specified when the
exponent evaluates negatively, and `Dioph.pow_dioph` supplies only the graph of **natural**
exponentiation. So there is no negation, and equations are `s = t` rather than `p = 0`.

The payoff is that the bridge to `Dioph` is a structural induction over combinators mathlib
already has. `DiophFn` is itself ℕ-valued, and every term constructor here is backed by a
`DiophFn`-valued lemma:

| constructor | mathlib |
|---|---|
| `var`, `const` | `Dioph.proj_dioph`, `Dioph.const_dioph` |
| `add`, `mul`, `pow` | `Dioph.add_dioph`, `Dioph.mul_dioph`, `Dioph.pow_dioph` |
| `div`, `mod` | `Dioph.div_dioph`, `Dioph.mod_dioph` |

`div` and `mod` are constructors for a concrete reason: base-`u` digit extraction (#33) needs
them at the `ExpDioph` level, and `ExpDioph.dioph` is one-directional, so a `Dioph`-level
lemma could not be pulled back. Relations that are *not* `DiophFn`-valued in mathlib —
`≤`, `<`, `∣` — appear instead as closure lemmas below.

## Universes

Everything here lives at `Type 0`. That is forced: `Dioph` itself is universe-polymorphic,
but mathlib states the entire `DiophFn` combinator API — `add_dioph`, `mul_dioph`,
`pow_dioph`, `div_dioph`, `mod_dioph`, `eq_dioph` — inside a section fixing
`variable {α : Type}`. No loss here, since every variable type in this project is `Fin n`,
but it is a real restriction on the API and worth generalising upstream some day.

This syntax stays internal to the DPRM core; it is not the DSL of #29, having no
fresh-variable discipline, no gadget calls and no extraction.
-/

namespace Hilbert10Experimental

variable {α β : Type}

/-- Syntax of exponential polynomials over `ℕ`. -/
inductive ExpTerm (α : Type) : Type
  | var : α → ExpTerm α
  | const : ℕ → ExpTerm α
  | add : ExpTerm α → ExpTerm α → ExpTerm α
  | mul : ExpTerm α → ExpTerm α → ExpTerm α
  | pow : ExpTerm α → ExpTerm α → ExpTerm α
  | div : ExpTerm α → ExpTerm α → ExpTerm α
  | mod : ExpTerm α → ExpTerm α → ExpTerm α

namespace ExpTerm

/-- Value of an exponential term at an assignment. -/
def eval : ExpTerm α → (α → ℕ) → ℕ
  | var i, x => x i
  | const n, _ => n
  | add s t, x => s.eval x + t.eval x
  | mul s t, x => s.eval x * t.eval x
  | pow s t, x => s.eval x ^ t.eval x
  | div s t, x => s.eval x / t.eval x
  | mod s t, x => s.eval x % t.eval x

/-- **The bridge.** Every exponential term denotes a Diophantine function.

One structural induction, each case a mathlib combinator; `pow` is where
`Pell.eq_pow_of_pell` enters, through `Dioph.pow_dioph`. -/
theorem diophFn (t : ExpTerm α) : Dioph.DiophFn fun x => t.eval x := by
  induction t with
  | var i => exact Dioph.proj_dioph i
  | const n => exact Dioph.const_dioph n
  | add s t hs ht => exact Dioph.add_dioph hs ht
  | mul s t hs ht => exact Dioph.mul_dioph hs ht
  | pow s t hs ht => exact Dioph.pow_dioph hs ht
  | div s t hs ht => exact Dioph.div_dioph hs ht
  | mod s t hs ht => exact Dioph.mod_dioph hs ht

/-- Reindex the variables of a term. -/
def map (f : α → β) : ExpTerm α → ExpTerm β
  | var i => var (f i)
  | const n => const n
  | add s t => add (s.map f) (t.map f)
  | mul s t => mul (s.map f) (t.map f)
  | pow s t => pow (s.map f) (t.map f)
  | div s t => div (s.map f) (t.map f)
  | mod s t => mod (s.map f) (t.map f)

@[simp] theorem eval_map (f : α → β) (t : ExpTerm α) (x : β → ℕ) :
    (t.map f).eval x = t.eval (x ∘ f) := by
  induction t <;> simp_all [map, eval]

end ExpTerm

/-- A set is exponential Diophantine when it is the projection of an equality between two
exponential terms. -/
def ExpDioph (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type) (s t : ExpTerm (α ⊕ β)),
    ∀ v, v ∈ S ↔ ∃ w : β → ℕ, s.eval (Sum.elim v w) = t.eval (Sum.elim v w)

namespace ExpDioph

/-- **Exponential Diophantine implies Diophantine.** The witnesses are projected away by
`Dioph.ex_dioph`, and the equation is `Dioph` by `Dioph.eq_dioph` applied to the two
`DiophFn`s from `ExpTerm.diophFn`. -/
theorem dioph {S : Set (α → ℕ)} (h : ExpDioph S) : Dioph S := by
  obtain ⟨β, s, t, hst⟩ := h
  have heq : Dioph {z : α ⊕ β → ℕ | s.eval z = t.eval z} :=
    Dioph.eq_dioph s.diophFn t.diophFn
  exact (Dioph.ex_dioph heq).ext fun v => (hst v).symm

/-- Any equation between exponential terms with no witnesses is exponential Diophantine. -/
theorem of_eq {s t : ExpTerm α} : ExpDioph {v | s.eval v = t.eval v} := by
  refine ⟨PEmpty, s.map Sum.inl, t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval_map]
  exact ⟨fun h => ⟨PEmpty.elim, by simpa using h⟩, fun ⟨_, hw⟩ => by simpa using hw⟩

end ExpDioph

/-! ### Acceptance tests

Nested powers are the case a representation that does not really compose fails on, so the
layer is exercised on one before anything is built above it.
-/

/-- A nested power: `2 ^ (2 ^ x₀) = x₁` is exponential Diophantine, and hence Diophantine. -/
theorem expDioph_two_pow_two_pow {α : Type} (i j : α) :
    ExpDioph {v : α → ℕ | 2 ^ (2 ^ v i) = v j} :=
  ExpDioph.of_eq (s := .pow (.const 2) (.pow (.const 2) (.var i))) (t := .var j)

theorem dioph_two_pow_two_pow {α : Type} (i j : α) :
    Dioph {v : α → ℕ | 2 ^ (2 ^ v i) = v j} :=
  (expDioph_two_pow_two_pow i j).dioph

/-- A term mixing every constructor, to check the induction covers them together. -/
theorem dioph_mixed {α : Type} (i j : α) :
    Dioph {v : α → ℕ | (v i ^ v j + v i * v j) / (v j % 3 + 1) = v i} :=
  (ExpDioph.of_eq
    (s := .div (.add (.pow (.var i) (.var j)) (.mul (.var i) (.var j)))
      (.add (.mod (.var j) (.const 3)) (.const 1)))
    (t := .var i)).dioph

end Hilbert10Experimental
