/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean
import Hilbert10

/-!
# Axiom audit

Checks that the library depends only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. Run via `lake env lean scripts/AxiomAudit.lean`
(done by CI); any disallowed axiom is a hard error.

Two layers:

* **Environment sweep**: every declaration whose *owning module* is `Hilbert10` or a
  submodule is checked — including `private` declarations (whose mangled `_private.*`
  names defeat any namespace-prefix filter) and compiler-generated auxiliaries — so a
  `native_decide`/`ofReduceBool` (or any custom axiom) anywhere in the library fails the
  gate, whether or not the declaration is listed below.
* **Headline regression list**: `headlineDecls` names the results the library exists to
  provide, and grows as they are promoted. It is a rename/deletion tripwire rather than
  the main guarantee — the double-backtick names resolve at elaboration, so removing a
  headline result fails the gate instead of silently shrinking it.

The sweep only sees modules reachable from `Hilbert10`, i.e. the root import spine.
`Hilbert10Experimental.*` is deliberately outside it (see
`scripts/check_sorry_boundary.py`), so work in progress is not audited until it is
promoted.
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Headline declarations to audit; extended as results are promoted into the spine. -/
def headlineDecls : List Name :=
  [-- The wire format: encoding contract, semantics, and the decision problem (#50)
   ``Hilbert10.PolynomialCode.eval_denote,
   ``Hilbert10.PolynomialCode.exists_code,
   ``Hilbert10.PolynomialCode.eval_exists_code,
   ``Hilbert10.PolynomialCode.hasNatRoot_iff,
   ``Hilbert10.NatSolvable,
   ``Hilbert10.natSolvable_iff_arity,
   -- the easy direction of DPRM, promoted in #52's tranche 2
   ``Hilbert10.Dioph.rePred,
   ``Hilbert10.rePred_natSolvable]

#eval show CoreM Unit from do
  for t in headlineDecls do
    let axs ← collectAxioms t
    for a in axs do
      unless allowedAxioms.contains a do
        throwError "axiom audit: {t} depends on disallowed axiom {a}"
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut swept := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`Hilbert10).isPrefixOf moduleNames[idx.toNat]! then
        let axs ← collectAxioms name
        for a in axs do
          unless allowedAxioms.contains a do
            throwError "axiom audit (sweep): {name} depends on disallowed axiom {a}"
        swept := swept + 1
  IO.println
    s!"axiom audit: {headlineDecls.length} headline declaration(s) clean; swept {swept}"
