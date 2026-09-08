/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.SumSquares
import Hilbert10.Internal.CodeAlgebraComp

/-!
# The sum-of-squares transformation is primitive recursive

Issue #53, third layer. `sumSquaresCode` is a `map` of `mul` under a `foldr` of `add`, so its
computability is exactly mathlib's `Primrec.list_map` and `Primrec.list_foldr` applied to the
operation-level lemmas of `Internal/CodeAlgebraComp.lean`. Nothing new about codes is proved.

## Main results

* `Hilbert10.PolynomialCode.primrec_sumSquaresCode`
* `Hilbert10.PolynomialCode.computable_sumSquaresCode`
-/

namespace Hilbert10

namespace PolynomialCode

theorem primrec_sumSquaresCode : Primrec sumSquaresCode := by
  refine (Primrec.list_foldr (f := fun ps : List PolynomialCode => ps.map fun p => mul p p)
    (g := fun _ => zero) (h := fun _ q => add q.1 q.2) ?_ (Primrec.const zero) ?_).of_eq
    fun ps => rfl
  · exact Primrec.list_map (f := fun ps => ps) (g := fun _ p => mul p p) Primrec.id
      (Primrec₂.comp primrec₂_mul Primrec.snd Primrec.snd)
  · exact Primrec₂.comp primrec₂_add (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)

theorem computable_sumSquaresCode : Computable sumSquaresCode := primrec_sumSquaresCode.to_comp

end PolynomialCode

end Hilbert10
