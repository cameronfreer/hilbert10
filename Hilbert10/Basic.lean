/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.NormNum

/-!
# Hilbert's tenth problem

Scaffolding module for the `Hilbert10` library. The placeholder below exists only so the
root import spine, the build, and CI are exercised from the first commit; it is expected
to be replaced by the first real unit.
-/

namespace Hilbert10

/-- A solvable instance of a Diophantine equation: `x ^ 2 + y ^ 2 = 25` has a solution
over `ℕ`. Placeholder declaration for the initial scaffold. -/
theorem exists_sq_add_sq_eq_25 : ∃ x y : ℕ, x ^ 2 + y ^ 2 = 25 := ⟨3, 4, by norm_num⟩

end Hilbert10
