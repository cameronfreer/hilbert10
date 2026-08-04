/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10Experimental.RegisterMachinePair
import Hilbert10Experimental.CleanScratch
import Mathlib.Computability.PartrecCode

/-!
# Compiling `Nat.Partrec.Code.pair`

Issue #51, step 6. The closure theorem for `pair`: given clean machines for two subcodes, build
one for `fun n => Nat.pair <$> cf n <*> cg n`. Assembling this over `Code.rec` is #44.

This is a controller and calling-convention proof rather than an arithmetic one. The arithmetic
was step 5.

## The source semantics, once

Mathlib evaluates `pair cf cg` applicatively. `mem_eval_pair` below turns that into an explicit
existential, so no `Seq.seq` or `Part.bind` reasoning reaches the machine proof, and the
`cf`-before-`cg` order is fixed in one place.
-/

namespace Hilbert10

namespace RegisterMachine

/-- The applicative source semantics of `Code.pair`, as an existential. `cf`'s value is `a`,
`cg`'s is `b`, and the result is `Nat.pair a b` in that order. -/
theorem mem_eval_pair {f g : ℕ →. ℕ} {n y : ℕ} :
    y ∈ (Nat.pair <$> f n <*> g n) ↔ ∃ a ∈ f n, ∃ b ∈ g n, y = Nat.pair a b := by
  simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩

/-- The evaluation of `Code.pair` really is that applicative expression. -/
theorem mem_eval_code_pair {cf cg : Nat.Partrec.Code} {n y : ℕ} :
    y ∈ (Nat.Partrec.Code.pair cf cg).eval n ↔
      ∃ a ∈ cf.eval n, ∃ b ∈ cg.eval n, y = Nat.pair a b :=
  mem_eval_pair

end RegisterMachine

end Hilbert10
