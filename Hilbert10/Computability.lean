/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Reduce
import Mathlib.Computability.RE

/-!
# Computability closure used before DPRM

Generic facts about recursively enumerable predicates that this development needs *below* the
DPRM theorem. Nothing here mentions `Dioph`, and nothing here may depend on `REPred.dioph`.

## Why this is its own module

The import direction is the point:

```
Computability  →  DPRM  →  DerivedDioph  →  endpoints and examples
```

`REPred.of_manyOneReducible` is pure computability theory: it is proved from `Partrec.comp`
and may be used anywhere, the DPRM proof included. What must *not* be used inside DPRM is its
Diophantine shadow, `Dioph.of_manyOneReducible`, since that goes through DPRM itself. Placing this
module below `DPRM` and the shadow in `DerivedDioph` above it makes the two directions visible in
the import graph rather than in a comment: the pre-DPRM closure sits here, the post-DPRM
consequences there.

Its consumers are the integer formulation (`rePred_intSolvable`) and that derived layer.

## Main results

* `Hilbert10.REPred.of_manyOneReducible`
-/

namespace Hilbert10

/-- **Recursive enumerability transfers backwards along a many-one reduction.** -/
theorem REPred.of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} (h : p ≤₀ q) (hq : REPred q) : REPred p := by
  obtain ⟨f, hf, hfp⟩ := h
  refine (Partrec.comp hq hf).of_eq fun a => ?_
  rw [propext (hfp a)]

end Hilbert10
