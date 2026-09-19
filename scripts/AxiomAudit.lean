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
   -- integer semantics of the wire format, and presentation independence (v2.2)
   ``Hilbert10.PolynomialCode.evalInt_denote,
   ``Hilbert10.natSolvable_iff_of_denote_eq,
   ``Hilbert10.intSolvable_iff_of_denote_eq,
   ``Hilbert10.intSolvable_iff_arity,
   -- DPRM, both directions (#14, #23)
   ``Hilbert10.Dioph.rePred,
   ``Hilbert10.REPred.dioph,
   ``Hilbert10.dioph_iff_rePred,
   ``Hilbert10.Nat.Partrec.graph_dioph,
   ``Hilbert10.Nat.Partrec.dom_dioph,
   -- the H10 endpoints (#14, #25, #26, #27)
   ``Hilbert10.rePred_natSolvable,
   ``Hilbert10.REPred.manyOneReducible_natSolvable,
   ``Hilbert10.natSolvable_re_complete,
   ``Hilbert10.halting_manyOneReducible_natSolvable,
   ``Hilbert10.not_computablePred_natSolvable,
   ``Hilbert10.not_rePred_not_natSolvable,
   -- the integer formulation, both reductions and its endpoints (#28)
   ``Hilbert10.IntSolvable,
   ``Hilbert10.intSolvable_iff_natSolvable_subUV,
   ``Hilbert10.intSolvable_manyOneReducible_natSolvable,
   ``Hilbert10.natSolvable_iff_intSolvable_fourSquares,
   ``Hilbert10.natSolvable_manyOneReducible_intSolvable,
   ``Hilbert10.rePred_intSolvable,
   ``Hilbert10.intSolvable_re_complete,
   ``Hilbert10.not_computablePred_intSolvable,
   ``Hilbert10.not_rePred_not_intSolvable,
   ``Hilbert10.natSolvable_manyOneEquiv_intSolvable,
   -- finite systems with a shared assignment (#53)
   ``Hilbert10.SystemNatSolvable,
   ``Hilbert10.SystemIntSolvable,
   ``Hilbert10.PolynomialCode.evalInt_sumSquaresCode,
   ``Hilbert10.PolynomialCode.evalInt_sumSquaresCode_eq_zero_iff,
   ``Hilbert10.PolynomialCode.arity_sumSquaresCode_le,
   ``Hilbert10.systemNatSolvable_iff_natSolvable_sumSquaresCode,
   ``Hilbert10.systemIntSolvable_iff_intSolvable_sumSquaresCode,
   ``Hilbert10.natSolvable_manyOneEquiv_systemNatSolvable,
   ``Hilbert10.intSolvable_manyOneEquiv_systemIntSolvable,
   -- degree, and the quadratic gates with their allocation contract (#57, checkpoint 1)
   ``Hilbert10.PolynomialCode.totalDegree_denote_le,
   ``Hilbert10.PolynomialCode.degreeBound_sumSquaresCode_le,
   ``Hilbert10.Gate.evalInt_code_eq_zero_iff,
   ``Hilbert10.Gate.eval_code_eq_zero_iff,
   ``Hilbert10.Gate.degreeBound_code_le,
   ``Hilbert10.exists_extension,
   -- quadratic lowering, stage one: a monomial (#57, checkpoint 2)
   ``Hilbert10.compileMonomial_wellOrdered,
   ``Hilbert10.compileMonomial_sound,
   ``Hilbert10.compilePoly_wellOrdered,
   ``Hilbert10.compilePoly_length,
   ``Hilbert10.compilePoly_sound,
   ``Hilbert10.compilePoly_sound_nat,
   ``Hilbert10.evalInt_eq_zero_iff_exists_aux,
   ``Hilbert10.eval_eq_zero_iff_exists_aux,
   ``Hilbert10.intSolvable_iff_systemIntSolvable_quadraticSystem,
   ``Hilbert10.natSolvable_iff_systemNatSolvable_quadraticSystem,
   ``Hilbert10.systemDegreeBound_quadraticSystem_le,
   ``Hilbert10.systemArity_quadraticSystem_le,
   -- Hilbert's tenth problem in degree four (#57, checkpoint 3)
   ``Hilbert10.QuarticNatSolvable,
   ``Hilbert10.QuarticIntSolvable,
   ``Hilbert10.PolynomialCode.degreeBound_quarticCode_le,
   ``Hilbert10.PolynomialCode.arity_quarticCode_le,
   ``Hilbert10.natSolvable_iff_natSolvable_quarticCode,
   ``Hilbert10.intSolvable_iff_intSolvable_quarticCode,
   ``Hilbert10.natSolvable_manyOneEquiv_quarticNatSolvable,
   ``Hilbert10.intSolvable_manyOneEquiv_quarticIntSolvable,
   ``Hilbert10.quarticNatSolvable_re_complete,
   ``Hilbert10.quarticIntSolvable_re_complete,
   ``Hilbert10.not_computablePred_quarticNatSolvable,
   ``Hilbert10.not_computablePred_quarticIntSolvable,
   -- one universal Diophantine polynomial (#54, first stage)
   ``Hilbert10.rePred_univEval,
   ``Hilbert10.exists_universal_mvPolynomial,
   ``Hilbert10.exists_universal_code,
   ``Hilbert10.dom_iff_of_universal,
   ``Hilbert10.eval_eq_zero_iff_exists_aux_from,
   ``Hilbert10.exists_universal_quartic_code,
   -- the derived Diophantine API, all strictly post-DPRM (v2.1.0)
   ``Hilbert10.REPred.of_manyOneReducible,
   ``Hilbert10.dioph_iff_exists_finite_mvPolynomial,
   ``Hilbert10.Dioph.of_manyOneReducible,
   ``Hilbert10.ComputablePred.dioph,
   ``Hilbert10.computablePred_iff_dioph_compl_dioph,
   ``Hilbert10.Computable.graph_dioph,
   ``Hilbert10.Nat.Partrec.range_dioph]

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
