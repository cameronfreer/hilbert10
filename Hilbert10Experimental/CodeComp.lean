/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Internal.RegisterMachineRealises
import Mathlib.Computability.PartrecCode

/-!
# Compiling `Nat.Partrec.Code.comp`

Issue #41. Sequential composition of compiled machines.

Mathlib evaluates `comp cf cg` as

```lean
| comp cf cg => fun n => eval cg n >>= eval cf
```

so `cg` runs **first** and `cf` consumes its result. Concatenation therefore puts `cg`'s machine
in front, and the naming below says `inner` for `cg` and `outer` for `cf` rather than trusting
the argument order of `comp` to be self-explanatory.

## Nothing here mentions program counters

`PartRealises.append` (#40) already realises Kleisli composition of register-file
transformations, and `PartComputesUnary.renameRegs` (#40, via #39) already lifts a machine into
a wider register file. So this file is a `Part`-level calculation and two applications of those
lemmas. If a proof here ever needs `run` or `.pc`, the contract is missing a lemma and it
belongs upstream in `RegisterMachineRealises`, not worked around locally.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- The register-file calculation behind composition: threading a register file through two
`ComputesUnary`-shaped transformations is the same as composing the functions and updating once.

The two `Function.update`s collapse by `update_idem`, and the intermediate read of register `0`
sees exactly what the first machine wrote. -/
private theorem bind_map_update (regs : Fin (k + 1) → ℕ) (inner outer : ℕ →. ℕ) :
    ((inner (regs 0)).map fun y => Function.update regs 0 y) >>=
        (fun mid => (outer (mid 0)).map fun z => Function.update mid 0 z) =
      (inner (regs 0) >>= outer).map fun z => Function.update regs 0 z := by
  rw [Part.bind_eq_bind, Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext y
  simp

/-- **`Code.comp`, at equal width.** `P` runs first and computes the inner function, `Q` runs
second and computes the outer one. -/
theorem PartComputesUnary.comp {P Q : Program (k + 1)} {inner outer : ℕ →. ℕ}
    (hP : PartComputesUnary P inner) (hQ : PartComputesUnary Q outer) :
    PartComputesUnary (P ++ shiftJumps P.length Q) fun x => inner x >>= outer :=
  (hP.append hQ).congr fun regs => bind_map_update regs inner outer

/-! ## Width lifting

Two machines compiled independently need not use the same number of registers. Renaming along an
injection that fixes register `0` widens either of them without disturbing what it computes, and
the injection is supplied by the caller — there is no allocator here, by the standing guard on
#39. -/

example : PartComputesUnary
    (renameRegs (Fin.castLE (by omega) : Fin 1 → Fin 3) (succMachine 0))
    fun n => Part.some (n + 1) :=
  computesUnary_succMachine.toPart.renameRegs (k' := 2) (Fin.castLE_injective _) rfl

/-! ## Partiality

Two regression cases, one for each way a composition can fail to converge. Total examples would
simplify correctly without exercising either clause of `PartRealises`. -/

/-- The inner computation diverges, so the composite does. Here the *first* clause of
`PartRealises` is vacuous throughout and the whole content is the converse clause. -/
example (r : Fin (k + 1)) :
    PartComputesUnary
      (loopMachine r ++ shiftJumps (loopMachine r).length (succMachine k))
      fun _ => Part.none :=
  ((partComputesUnary_loopMachine r).comp computesUnary_succMachine.toPart).congr fun _ => by simp

/-- The inner computation converges and the outer one then diverges. This is the case that
exercises the harder half of `PartRealises.append`: control really does reach the join, so the
proof has to rule out an early halt before it. -/
example (r : Fin (k + 1)) :
    PartComputesUnary
      (succMachine k ++ shiftJumps (succMachine k).length (loopMachine r))
      fun _ => Part.none :=
  (computesUnary_succMachine.toPart.comp (partComputesUnary_loopMachine r)).congr fun _ => by simp

end RegisterMachine

end Hilbert10
