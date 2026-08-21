/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Computability
import Hilbert10.DPRM

/-!
# Derived Diophantine closure, on finite tuples

The computability-side consequences of `dioph_iff_rePred`, at the domains where they can honestly
be stated.

## Post-DPRM only

Every result here consumes `REPred.dioph`. None may be used inside the DPRM development itself:
the tuple bridge, the code-to-machine compiler and the arithmetisation all have to reach `Dioph`
without a "closure under computable preimages" step, because that closure *is* DPRM. The
circularity is why `Internal/TupleCoding.lean` exists, and it would return at once if any of
these were imported earlier in the spine.

## Finite tuples, deliberately

The domains are `Fin n → ℕ`, not arbitrary `Primcodable` types. `Dioph` is a predicate on
`Fin n → ℕ` while `≤₀` is a predicate on `Primcodable` types, so a general statement needs a
Diophantine encoding contract to transport across — and an opaque `Primcodable` instance would
reintroduce the tuple-coding problem in a new API, this time with no proof obligation attached.

## Main results

* `Hilbert10.Dioph.of_manyOneReducible`
* `Hilbert10.ComputablePred.dioph`
* `Hilbert10.Computable.graph_dioph`
* `Hilbert10.Nat.Partrec.range_dioph`
-/

namespace Hilbert10

/-- **Diophantine predicates on tuples are closed downwards under many-one reduction.**

The proof is a round trip: `Dioph → REPred` by the easy direction, transport along the reduction,
and `REPred → Dioph` by DPRM. -/
theorem Dioph.of_manyOneReducible {n m : ℕ} {R : (Fin n → ℕ) → Prop} {S : (Fin m → ℕ) → Prop}
    (hRS : R ≤₀ S) (hS : Dioph {x | S x}) : Dioph {x | R x} :=
  REPred.dioph (REPred.of_manyOneReducible hRS (Dioph.rePred hS))

/-- **Every computable predicate on tuples is Diophantine.** -/
theorem ComputablePred.dioph {n : ℕ} {R : (Fin n → ℕ) → Prop} (hR : ComputablePred R) :
    Dioph {x | R x} :=
  REPred.dioph hR.to_re

/-- **The graph of a computable function is Diophantine**, unary case.

Stated at the two-coordinate layout `v 1 = f (v 0)`, which is the shape mathlib's `DiophFn`
consumers expect. -/
theorem Computable.graph_dioph {f : ℕ → ℕ} (hf : Computable f) :
    Dioph {v : Fin 2 → ℕ | v 1 = f (v 0)} := by
  have hp : _root_.Nat.Partrec fun a => Part.some (f a) := Partrec.nat_iff.mp hf.partrec
  have hset : {v : Fin 2 → ℕ | v 1 = f (v 0)}
      = {v : Fin 2 → ℕ | v 1 ∈ (fun a => Part.some (f a)) (v 0)} := by
    ext v
    simp [eq_comm]
  rw [hset]
  exact Nat.Partrec.graph_dioph hp

/-- **The range of a partial recursive function is Diophantine.**

No adapter is needed. `Dioph.ex_dioph` already projects an arbitrary sum-indexed block, so the
input coordinate of the graph is retyped into the right summand by one reindexing and then
quantified away. The `Fin2`/`Vector3`-shaped projection lemmas are not the general ones. -/
theorem Nat.Partrec.range_dioph {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) :
    Dioph {v : Fin 1 → ℕ | ∃ a, v 0 ∈ f a} := by
  -- the graph, with coordinate `0` the input and `1` the output
  have hg := Nat.Partrec.graph_dioph hf
  -- retype: the output stays an input coordinate, the input becomes the block to quantify away
  have hr : Dioph {u : Fin 1 ⊕ Unit → ℕ | u (.inl 0) ∈ f (u (.inr ()))} := by
    refine Dioph.ext (Dioph.reindex_dioph (Fin 1 ⊕ Unit) ![Sum.inr (), Sum.inl 0] hg) fun u => ?_
    simp [Set.mem_setOf_eq]
  refine Dioph.ext hr.ex_dioph fun v => ?_
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x (), hx⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, ha⟩

end Hilbert10
