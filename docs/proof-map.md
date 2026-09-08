# Proof map

A routing table from each headline result to the module that proves it, and from there to the
layer below. It is written to be *checked*, not read for understanding: every name below is a
declaration in the public spine, and every path is a file in this repository. The mathematics is
explained in the module docstrings; this document only says where things are and what depends on
what.

The spine is `Hilbert10.lean` and its import closure: 60 modules, about 13,900 lines. The gates
that cover it are described in [README](../README.md#verification);
[lessons.md](lessons.md) is the retrospective and [comparison.md](comparison.md) the comparison
with the Coq mechanisation.

---

## 1. The endpoints

```
                     REPred R
                        │  REPred.dioph            (DPRM.lean, §3)
                        ▼
              Dioph {v : Fin n → ℕ | R v}
                        │  dioph_iff_exists_fin_mvPolynomial   (NormalForm.lean, §4)
                        ▼
        RepresentsNat p R  for a finite MvPolynomial
                        │  exists_code_representsNat           (ExistsCodeRepresents.lean, §4)
                        ▼
        a PolynomialCode representing R
                        │  representsNat_manyOneReducible_natSolvable  (Specialization.lean, §4)
                        ▼
                  R ≤₀ NatSolvable
                        │  natSolvable_manyOneReducible_intSolvable    (IntSolvable.lean, §5)
                        ▼
                  R ≤₀ IntSolvable
```

| Result | Module |
|---|---|
| `rePred_natSolvable` | `Hilbert10/DiophToRE.lean` |
| `natSolvable_re_complete` | `Hilbert10/Endpoints.lean` |
| `halting_manyOneReducible_natSolvable` | `Hilbert10/Endpoints.lean` |
| `not_computablePred_natSolvable` | `Hilbert10/Endpoints.lean` |
| `not_rePred_not_natSolvable` | `Hilbert10/Endpoints.lean` |
| `rePred_intSolvable` | `Hilbert10/Endpoints.lean` |
| `intSolvable_re_complete` | `Hilbert10/Endpoints.lean` |
| `not_computablePred_intSolvable` | `Hilbert10/Endpoints.lean` |
| `not_rePred_not_intSolvable` | `Hilbert10/Endpoints.lean` |

Undecidability is a corollary of completeness in both cases: the halting problem is recursively
enumerable, so it reduces, and `ComputablePred.computable_of_manyOneReducible` finishes. That
insolubility is not recursively enumerable is the same fact read through
`ComputablePred.computable_iff_re_compl_re'`: solvability is enumerable, so its complement cannot
be.

---

## 2. The wire format

`PolynomialCode` is a one-field structure over `List (ℤ × List ℕ)`. Everything a decision problem
needs about it is proved once, at the bottom of the spine.

| Concern | Result | Module |
|---|---|---|
| encoding | `instance : Primcodable PolynomialCode`, `primrec_terms`, `primrec_arity` | `PolynomialCodePrimcodable.lean` |
| semantics | `eval`, `evalInt`, `evalInt_map_natCast` | `PolynomialCode.lean`, `PolynomialCodeInt.lean` |
| agreement with `MvPolynomial` | `denote`, `evalInt_denote`, `eval_denote` | `PolynomialCodeDenote.lean` |
| only the denotation matters | `evalInt_eq_of_denote_eq`, `eval_eq_of_denote_eq` | `PolynomialCodeDenote.lean` |
| every finite polynomial has a code | `exists_code`, `eval_exists_code` | `ExistsCode.lean` |
| the decision problem | `NatSolvable`, `hasNatRoot_iff`, `natSolvable_iff_arity`, `natSolvable_iff_of_denote_eq` | `NatSolvable.lean` |
| substituting inputs | `instantiate`, `eval_instantiate`, `computable₂_instantiate` | `Instantiate.lean` |
| evaluation is computable | `primrec₂_eval`, `computable₂_eval` | `PolynomialCodeComp.lean` |

`evalInt_denote` is where `Classical.choice` enters the spine — through `MvPolynomial`, not through
any nonuniform choice of code; `eval_denote` is its restriction along the cast. `Instantiate` is what makes the reduction computable in the input.

---

## 3. DPRM

Both directions, and the only two theorems the rest of the development calls.

```lean
theorem Dioph.rePred {n : ℕ} {R : (Fin n → ℕ) → Prop} : Dioph {x | R x} → REPred R
theorem REPred.dioph {n : ℕ} {R : (Fin n → ℕ) → Prop} : REPred R → Dioph {x | R x}
theorem dioph_iff_rePred {n : ℕ} (R : (Fin n → ℕ) → Prop) : Dioph {x | R x} ↔ REPred R
```

**Dioph → RE** (`DiophToRE.lean`) is short: an existential over a computable predicate is
recursively enumerable, and evaluation of a code is computable.

**RE → Dioph** (`DPRM.lean`) runs through the machine route:

| Step | Result | Module |
|---|---|---|
| a partial recursive code becomes a register machine | `exists_machine_graph` | `Internal/CodeMachine.lean` |
| acceptance by *any* register machine is Diophantine | `dioph_accepts_regs` | `Internal/SelectorRegsDioph.lean` |
| graph and domain of a partial recursive function | `Nat.Partrec.graph_dioph`, `Nat.Partrec.dom_dioph` | `DPRM.lean` |
| the unary case | `REPred.dioph_nat` | `DPRM.lean` |
| arbitrary finite arity | `REPred.dioph` | `DPRM.lean` |

The last step is not reindexing: it needs an explicit tuple code with a Diophantine graph and a
computable decoder — `tupleCode`, `tupleDecode_tupleCode`, `computable_tupleDecode`,
`expDioph_tupleCode_graph` in `Internal/TupleCoding.lean`.

### 3.1 The compiler half (`Code → register machine`)

| Layer | Module |
|---|---|
| machines, configurations, `Halts` | `Internal/RegisterMachine.lean` |
| macros and program composition | `Internal/RegisterMachineMacros.lean`, `Internal/RegisterMachineRealises.lean` |
| pairing and unpairing, by shell enumeration | `Internal/RegisterMachinePair*.lean`, `Internal/RegisterMachineUnpair.lean`, `Internal/ForMathlib/PairingEnumeration.lean` |
| scratch discipline and the graph relation | `Internal/CleanScratch.lean` (`CleanPartComputesUnary`, `Accepts`) |
| the five `Nat.Partrec.Code` constructors | `Internal/CodePair.lean`, `Internal/CodePrec.lean`, `Internal/CodeRfind.lean` |
| the interface | `Internal/CodeMachine.lean` |

### 3.2 The arithmetisation half (`Accepts → Dioph`)

| Layer | Result | Module |
|---|---|---|
| packed runs and their fields | `configCode`, `FitsConfig`, `EncodedStep` | `Internal/ConfigCoding.lean`, `Internal/PackedRun.lean` |
| the exponential Diophantine layer | `ExpTerm`, `ExpDioph`, `ExpDioph.fin_and` | `Internal/ExpDioph.lean` |
| binomial digits and submasks | `Nat.choose_eq_baseDigit`, `isBinarySubmask_iff_odd_choose`, `ExpDioph.of_isBinarySubmask` | `Internal/ForMathlib/ChooseDigit.lean`, `Internal/ForMathlib/BinarySubmask.lean`, `Internal/ForMathlib/SubmaskChoose.lean`, `Internal/ExpDiophChoose.lean` |
| the obligation, isolated | `Aggregation`, `expDioph_accepts` | `Internal/AcceptsDioph.lean` |
| selector algebra | `fieldsCode_selected_smul_eq_iff`, `subSum_le_one` | `Internal/SelectorMask.lean` |
| blockwise step, many registers | `blockStepK_iff` | `Internal/SelectorRegs.lean` |
| global lanes | `globalConditionsK_iff` | `Internal/SelectorRegsGlobal.lean` |
| the obligation discharged | `aggregation_succ`, `dioph_accepts_regs` | `Internal/SelectorRegsDioph.lean` |

`Aggregation` is the bounded conjunction over run positions. It is *dissolved* rather than
represented: one-hot selector lanes turn the variable-length conjunction into finitely many
identities whose number depends on the program and register count, never on the run length. That
is the one place this route differs mathematically from the Coq and Isabelle developments; see
[comparison.md §3](comparison.md).

---

## 4. From `Dioph` to a reduction

| Step | Result | Module |
|---|---|---|
| `Poly` ↔ `MvPolynomial` | `toDiophPoly`, `exists_mvPolynomial` | `PolyBridge.lean` |
| compact the witness block to `Fin m` | `exists_fin_right_rename` | `Internal/ForMathlib/RightRename.lean` (#2) |
| the normal form | `dioph_iff_exists_fin_mvPolynomial` | `NormalForm.lean` |
| a code for the polynomial | `exists_code_representsNat` | `ExistsCodeRepresents.lean` |
| the computable reduction | `representsNat_manyOneReducible_natSolvable` | `Specialization.lean` |

The code is fixed *per relation*, by eliminating an existential inside a proposition; the
reduction `fun a => code.instantiate [a]` is computable because `code` is then a constant. No
uniform `Code → PolynomialCode` compiler exists here, and none is needed — see
[README §Scope](../README.md#scope) and #29.

---

## 5. The integer formulation

| Step | Result | Module |
|---|---|---|
| the predicate | `IntSolvable`, `intSolvable_iff_arity`, `intSolvable_iff_of_denote_eq` | `IntSolvable.lean` |
| code arithmetic | `const`, `X`, `add`, `neg`, `mul`, `npow` and their evaluation laws | `Internal/CodeAlgebra.lean` |
| … is primitive recursive | `primrec₂_add`, `primrec₂_mul`, `primrec₂_npow`, … | `Internal/CodeAlgebraComp.lean` |
| `x = u - v` | `eval_subUV`, `arity_subUV_le` | `SubUV.lean` (public) |
| … is primitive recursive | `primrec_subUV` | `Internal/SubUVComp.lean` |
| four squares | `evalInt_fourSquares_eq_zero_iff`, `arity_fourSquares_le` | `FourSquares.lean` (public) |
| … is primitive recursive | `primrec_fourSquares` | `Internal/FourSquaresComp.lean` |
| the two equivalences | `intSolvable_iff_natSolvable_subUV`, `natSolvable_iff_intSolvable_fourSquares` | `IntSolvable.lean` |
| the two reductions | `intSolvable_manyOneReducible_natSolvable`, `natSolvable_manyOneReducible_intSolvable` | `IntSolvable.lean` |

The two transformations are public: they are the reductions themselves, and their evaluation and
arity theorems stand alone. Their computability proofs are not — those are what turn a
transformation into a many-one reduction, and they stay internal.

Each direction is stated first as an equivalence of *codes* and only then packaged with the
computability of the transformation, so the arithmetic can be checked without reading a
computability proof. Computability of `evalInt` is deliberately absent: nothing consumes it,
because what a many-one reduction needs is the code map, not the evaluator.

### 5.1 Finite systems with a shared assignment (#53)

| Step | Result | Module |
|---|---|---|
| the predicates | `SystemNatSolvable`, `SystemIntSolvable` | `Systems.lean` |
| the sum of squares | `sumSquaresCode`, `systemArity`, `evalInt_sumSquaresCode`, `eval_sumSquaresCode` | `SumSquares.lean` (public) |
| a sum of squares vanishes iff every summand does | `evalInt_sumSquaresCode_eq_zero_iff`, `eval_sumSquaresCode_eq_zero_iff`, `arity_sumSquaresCode_le` | `SumSquares.lean` |
| … is primitive recursive | `primrec_sumSquaresCode` | `Internal/SumSquaresComp.lean` |
| the equivalences, same witness | `systemNatSolvable_iff_natSolvable_sumSquaresCode`, `systemIntSolvable_iff_intSolvable_sumSquaresCode` | `Systems.lean` |
| the same many-one degree | `natSolvable_manyOneEquiv_systemNatSolvable`, `intSolvable_manyOneEquiv_systemIntSolvable` | `Systems.lean` |

One assignment serves every member of the system; the contradictory pair `x₀ = 0`, `x₀ = 1`
(each solvable, jointly not) is the regression that pins that contract. The folded-sum laws
`evalInt_foldr_add` and `arity_foldr_add_le` in `Internal/CodeAlgebra.lean` now serve both this
transformation and `fourSquares`.

---

## 6. The derived API, above DPRM

Consequences of `dioph_iff_rePred` for consumers, none of which the DPRM proof may use. The
import direction is the design: `Computability.lean` sits *below* `DPRM.lean` and holds the pure
computability fact, `DerivedDioph.lean` sits *above* it and holds the Diophantine consequences.

| Step | Result | Module |
|---|---|---|
| RE transfers backwards along `≤₀` (pre-DPRM) | `REPred.of_manyOneReducible` | `Computability.lean` |
| the normal form at any finite input type | `dioph_iff_exists_finite_mvPolynomial` | `NormalForm.lean` |
| Diophantine sets are closed under `≤₀` | `Dioph.of_manyOneReducible` | `DerivedDioph.lean` |
| computable predicates are Diophantine | `ComputablePred.dioph` | `DerivedDioph.lean` |
| Post's theorem, read through DPRM | `computablePred_iff_dioph_compl_dioph` | `DerivedDioph.lean` |
| graphs and ranges | `Computable.graph_dioph`, `Nat.Partrec.range_dioph` | `DerivedDioph.lean` |
| every headline at its advertised type | `example`s only | `Examples/Headlines.lean` |
| divisibility both ways, primality | `prime_dioph` | `Examples/DerivedDioph.lean` |

The domains are `Fin n → ℕ`, not arbitrary `Primcodable` types: transporting across an opaque
encoding would need a Diophantine encoding contract, and none is stated here.

---

## 7. What the spine takes from mathlib

Load-bearing inputs, all at the pinned revision:

* `Mathlib.NumberTheory.Dioph` — `Dioph`, `DiophFn`, `Poly`, and the closure lemmas, including
  `pow_dioph`, which is why exponentiation is never re-formalised here;
* `Mathlib.Computability.Partrec.Code` — `Nat.Partrec.Code`, `Code.exists_code`;
* `Mathlib.Computability.Reduce` — `≤₀`, `ManyOneReducible.trans`, `manyOneReducible_toNat`;
* `Mathlib.Computability.Halting` — `ComputablePred.halting_problem(_re)`;
* `Mathlib.Data.Nat.Digits.Lemmas` and `Mathlib.Data.Nat.Choose.{Sum, Bounds}` — the digit and
  binomial API behind `Internal/ForMathlib/ChooseDigit.lean`;
* `Mathlib.NumberTheory.SumFourSquares` — Lagrange, used once, in `IntSolvable.lean`.

Four small shims are staged for upstream and used internally in the meantime:
`RightRename` (#2), `PrimrecInt` (#36, exactly `int_neg`, `int_mul`, `list_replicate_zero`),
`BinarySubmask` (#37), `PrimrecNat`.

---

## 8. What is *not* in the spine

`Hilbert10Experimental.lean` imports `Hilbert10` plus nine modules kept as route evidence: the
one-register and fixed-slice selector spikes, the decrement-loop counterexamples, the
direct-route sequence spike, and `HaltingComplete` (#24), which is outside the endpoint closure.
The import boundary is enforced by `scripts/check_sorry_boundary.py`; nothing in the spine
depends on any of it.

---

## 9. Snapshot

Measured at v2.2.0, not a benchmark:

| | |
|---|---|
| spine modules | 60 |
| spine lines | ~13,900 |
| headline declarations audited | 38 |
| axioms used | `propext`, `Classical.choice`, `Quot.sound` |
| `sorry` in the spine | none |
