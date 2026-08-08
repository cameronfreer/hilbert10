/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.CodePrec

/-!
# The source semantics of `Nat.Partrec.Code.rfind'`

Issue #43, before any register is chosen — the same order as #41, #51 and #42.

`rfind'` minimises *from an offset*: on input `Nat.pair a m` it returns the least `y ≥ m` with
`f (Nat.pair a y) = 0`. Mathlib writes that with `Nat.rfind` over a shifted predicate and a
`Part.map`, and `Nat.mem_rfind` is the decisive fact.

## Keeping the offset

`mem_rfindSem` is stated in terms of the number of *unsuccessful turns* `q`, not as an interval
`m ≤ z < y`:

```lean
y ∈ rfindSem f a m ↔ ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
  ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0
```

That is what the machine does: after `q` unsuccessful turns its candidate is `q + m`. An interval
form is a corollary if a consumer ever wants one; stating it that way first would put an
arithmetic translation between the machine and its specification, which is exactly the sort of
gap the earlier constructors avoided by naming the recurrence first.
-/

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- Minimisation from an offset, named. -/
def rfindSem (f : ℕ →. ℕ) (a m : ℕ) : Part ℕ :=
  (Nat.rfind fun n => (fun z => z = 0) <$> f (Nat.pair a (n + m))).map (· + m)

/-- The predicate the search minimises, spelled out: `true` means the callee returned zero. -/
private theorem mem_map_decide_true {f : ℕ →. ℕ} {u : ℕ} :
    true ∈ ((fun z => decide (z = 0)) <$> f u) ↔ 0 ∈ f u := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    have hz' : z = 0 := by simpa using hz0
    exact hz' ▸ hz
  · intro h
    exact ⟨0, h, by simp⟩

private theorem mem_map_decide_false {f : ℕ →. ℕ} {u : ℕ} :
    false ∈ ((fun z => decide (z = 0)) <$> f u) ↔ ∃ z ∈ f u, z ≠ 0 := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩

/-- **The search characterisation**, counting unsuccessful turns. -/
theorem mem_rfindSem {f : ℕ →. ℕ} {a m y : ℕ} :
    y ∈ rfindSem f a m ↔
      ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
        ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0 := by
  rw [rfindSem, Part.mem_map_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Nat.mem_rfind] at hq
    exact ⟨q, rfl, mem_map_decide_true.mp hq.1,
      fun j hj => mem_map_decide_false.mp (hq.2 hj)⟩
  · rintro ⟨q, rfl, hq, hmin⟩
    exact ⟨q, Nat.mem_rfind.mpr ⟨mem_map_decide_true.mpr hq,
      fun {j} hj => mem_map_decide_false.mpr (hmin j hj)⟩, rfl⟩

/-- **The bridge.** `Code.rfind'`'s evaluation on a paired input is the named search. -/
theorem eval_rfind_eq (cf : Code) (a m : ℕ) :
    (Code.rfind' cf).eval (Nat.pair a m) = rfindSem cf.eval a m := by
  rw [Code.eval, Nat.unpaired, Nat.unpair_pair]
  rfl

/-- The same for an arbitrary input, which is what the machine receives. -/
theorem eval_rfind_unpair (cf : Code) (x : ℕ) :
    (Code.rfind' cf).eval x = rfindSem cf.eval x.unpair.1 x.unpair.2 := by
  conv_lhs => rw [← Nat.pair_unpair x]
  exact eval_rfind_eq cf _ _

end RegisterMachine

end Hilbert10
