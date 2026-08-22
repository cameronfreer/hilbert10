# Roadmap probes, 2026-08-21

Evidence gathered before proposing a Tau Ceti roadmap for Diophantine computability. **Dated and
fixed**: this document records what was measured on 2026-08-21 and is not maintained afterwards.
The roadmap should cite it as provenance for design choices, never as a status page.

* Source release: `hilbert10` v2.0.0 (`70a5260`), built against mathlib `81a5d25`, Lean `v4.32.0`.
* Target pins tested: mathlib `4fae4090fac768a5f28c40290d3b3b80a1365c1a`,
  toolchain `leanprover/lean4:v4.34.0-rc1` — read from Tau Ceti's `lake-manifest.json` and
  `lean-toolchain`.

Every claim below was produced by building, by an environment sweep, or by targeted source
search — the duplicate ledger and the body-use check use the last of these deliberately, since a
clean build cannot show that an upstream equivalent exists under another name.

---

## 1. Compatibility ledger (probe D)

The v2.0.0 spine was built in an isolated worktree at Tau Ceti's pin, twice: once with
`warningAsError` on (so deprecations are fatal) and once off (so genuine breakage is isolated).

| | Result |
|---|---|
| public spine, 56 modules | builds after **one line** changed |
| staging | `Hilbert10Experimental/HaltingComplete.lean` fails, 2 goals |
| deprecations | 171 occurrences, 5 renames |

The single spine repair, in `Internal/CodeRfind.lean`:

```lean
-    rw [Nat.mem_rfind] at hq
+    replace hq := Nat.mem_rfind.mp hq
```

The rewrite no longer finds its pattern under the new elaboration of `Nat.rfind`'s `Part.map`
argument. Statement and proof idea unchanged. `HaltingComplete` breaks at `Part.some a >>= f = f a`;
it is outside the released spine, but it is issue #24's content, so it needs repair before that
upstream PR.

| deprecated | replacement | count |
|---|---|---|
| `if_neg` | `ite_eq_right` | 75 |
| `if_pos` | `ite_eq_left` | 62 |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` | 22 |
| `if_false` | `ite_false` | 7 |
| `if_true` | `ite_true` | 5 |

**Reading.** One substantive line across two Lean releases supports reconstruction in Tau Ceti.
The 171 deprecations argue against a file-for-file port: reconstruct with current names.

### Duplicate search at the same revision

By search, not by build — a clean build does not prove absence of an upstream equivalent under
another name.

| ours | upstream at `4fae409` | action |
|---|---|---|
| `Primrec.int_neg`, `int_mul`, `list_replicate_zero` (#36) | absent; no `Computability/Primrec/Int.lean` | retain |
| `Nat.IsBinarySubmask` and lemmas (#37) | absent | retain |
| `Nat.choose_eq_baseDigit` | absent | retain |
| `Nat.pairNext` enumeration | absent | retain |
| `Primrec.nat_pow` | absent | retain |
| `exists_fin_right_rename` (#2) | `MvPolynomial.exists_fin_rename` exists, but does not fix the left summand | adapt: #2 is its right-summand refinement |
| — | `ManyOneEquiv` exists (`Computability/Reduce.lean`) | consume |
| DPRM / H10 | absent; both `Dioph.lean` TODOs still open | — |
| many-one completeness of halting (#24) | absent | retain |

---

## 2. Signatures compiled (probes A–C)

All of the following compiled under the spine's strict options
(`autoImplicit=false`, mathlib standard linters, `warningAsError`).

```lean
-- below DPRM, in Hilbert10/Computability.lean
theorem REPred.of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop} (h : p ≤₀ q) (hq : REPred q) : REPred p

-- strictly above DPRM, in Hilbert10/DerivedDioph.lean
theorem Dioph.of_manyOneReducible {n m : ℕ} {R : (Fin n → ℕ) → Prop} {S : (Fin m → ℕ) → Prop}
    (hRS : R ≤₀ S) (hS : Dioph {x | S x}) : Dioph {x | R x}
theorem ComputablePred.dioph {n : ℕ} {R : (Fin n → ℕ) → Prop} (hR : ComputablePred R) :
    Dioph {x | R x}
theorem Computable.graph_dioph {f : ℕ → ℕ} (hf : Computable f) :
    Dioph {v : Fin 2 → ℕ | v 1 = f (v 0)}
theorem Nat.Partrec.range_dioph {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    Dioph {v : Fin 1 → ℕ | ∃ a, v 0 ∈ f a}

-- in Hilbert10/NormalForm.lean
theorem dioph_iff_exists_finite_mvPolynomial {α : Type} [Finite α] (R : (α → ℕ) → Prop) :
    Dioph {x : α → ℕ | R x} ↔
      ∃ (m : ℕ) (p : MvPolynomial (α ⊕ Fin m) ℤ), RepresentsNat p R

-- in Hilbert10/IntSolvable.lean
theorem natSolvable_manyOneEquiv_intSolvable : ManyOneEquiv NatSolvable IntSolvable
```

### What the derived layer costs

`Dioph.of_manyOneReducible` and `ComputablePred.dioph` are one-liners: `Dioph → REPred`,
transport, `REPred → Dioph`. `Computable.graph_dioph` is three lines, and cheapest through
`Nat.Partrec.graph_dioph` rather than through the computable-predicate route, whose decidability
plumbing is the harder path.

**No coordinate adapter was needed.** `Dioph.ex_dioph` projects an arbitrary sum-indexed block, so
`range_dioph` is one reindexing (`![Sum.inr (), Sum.inl 0]`) followed by `ex_dioph`. An earlier
inventory looked only at `ex1_dioph` and `vec_ex1_dioph`, which are the `Fin2`/`Vector3` special
cases, and wrongly concluded that a finite-coordinate existential adapter was missing. Nothing of
the kind was introduced: one consumer does not justify an abstraction.

### Domains: finite tuples, not `Primcodable`

`Dioph` is a predicate on `Fin n → ℕ`; `≤₀` is a predicate on `Primcodable` types. Everything in
the derived layer is therefore stated at `Fin n → ℕ`. Transport across an opaque `Primcodable`
encoding would reintroduce exactly the tuple-coding circularity that `Internal/TupleCoding.lean`
exists to avoid, this time in an API with no proof obligation attached. A general version needs an
explicit Diophantine encoding contract, which is not proved here and should not be promised.

### `Finite`, and the universe answer

Both settled negatively and mechanically:

* **`Fintype` restatement: rejected by mathlib itself.** The `[Fintype α]` companion was written
  and deleted — `unusedFintypeInType` fires, because the hypothesis does not occur in the
  conclusion. There is one theorem, at `Finite`.
* **Universe polymorphism: not available downstream.** `Dioph` is universe-polymorphic
  (`{α : Type u}`, witness type in the same `u`), but `reindex_dioph` and the whole closure API
  from `abs_poly_dioph` onwards sit in a section with `variable {α β γ : Type u}`. A reindexing
  cannot cross universes, so transporting an arbitrary input type to `Fin n` forces `Type 0`.
  Universe generalisation is an upstream change to that section; a roadmap must not promise it.

### Two conventions the probes forced

* `PrimrecPred p` is `∃ (_ : DecidablePred p), Primrec fun a => decide (p a)` — the instance is
  existentially bound. Proofs must stay inside the `PrimrecPred` world (`Primrec.ite`,
  `PrimrecRel.comp`, `PrimrecPred.computablePred`) rather than manipulate `decide` directly.
* `Hilbert10.Dioph` exists in this project, so inside `namespace Hilbert10` an `open Dioph`
  shadows mathlib's namespace and consumers must write `_root_.Dioph.dvd_dioph`. Tau Ceti should
  extend the root mathlib namespaces (`Dioph.rePred`, `REPred.dioph`) rather than reproduce the
  enclosing namespace. The released API is not renamed for this.

### The two routes agree (probe B)

Divisibility is proved Diophantine twice and both proofs inhabit the same named proposition; two
`example`s check that mechanically. No adapter was needed, because mathlib's closure API
(`dvd_dioph`, `proj_dioph`) is stated for `Set (α → ℕ)` at general `α` and lands on `Fin 2 → ℕ`
directly.

**Primality is a commitment, not a corollary.** Mathlib has no `Primrec` or `Computable` lemma for
`Nat.Prime`, so the example carries a hand-built primitive recursive trial division and its
correctness proof. A roadmap listing primality as a DPRM-derived example is committing to that
component.

---

## 3. Ownership and the leakage gate (probe E)

`scripts/ApiLeakageAudit.lean` checks that the *statement* of every exported declaration owned by
a public module mentions no constant owned by `Hilbert10.Internal.*` or `Hilbert10Experimental.*`.

Policy, and the reasons for each part:

* **ownership by module, not namespace prefix** — internal declarations deliberately live in
  ordinary namespaces (`Hilbert10.ExpTerm`, `Hilbert10.RegisterMachine`), so a name filter would
  miss exactly what the gate is for;
* **types only** — a public abstraction implemented by internal machinery is the design, not a
  leak;
* **reducible public aliases unfolded** — otherwise a public `abbrev` conceals an internal type;
* **compiler-generated companions skipped** (`f.eq_def`, `f.eq_1`, …) — they restate a body, so
  they fall under the same policy as bodies.

First run: three failures, all in the integer layer. They were a real contradiction in the
boundary, not gate noise, and were resolved by promotion rather than by exemption:

| was | now |
|---|---|
| `Internal/SubUV.lean` | `SubUV.lean`, public |
| `Internal/FourSquares.lean` | `FourSquares.lean`, public |
| `diffList_toNat` in `IntSolvable` | in `SubUV`, beside `diffList` |
| `subUVMonomialFrom_eq_foldr` in `SubUV` | in `Internal/SubUVComp`, its only consumer |
| two fold helpers in `FourSquares` | `private` |

The computability halves (`SubUVComp`, `FourSquaresComp`) and the code algebra
(`CodeAlgebra`, `CodeAlgebraComp`) stay internal. Result after promotion: **155 public
declarations clean**, and the gate is CI-enforced.

---

## 4. Extraction matrix (probe F)

Two measurements. Import closures are exact. Consumer counts come from an environment sweep over
declaration *types*, so they measure interface-level dependence; body-level uses were checked
separately by qualified-name search where they mattered.

### The machine layer is import-independent of the arithmetisation

Every one of `RegisterMachine`, `RegisterMachineComp`, `RegisterMachineMacros`,
`RegisterMachinePair`, `RegisterMachinePairing`, `RegisterMachineRealises`,
`RegisterMachineUnpair`, `CleanScratch`, `CodePair`, `CodePrec`, `CodeRfind`, `CodeMachine` has an
import closure containing **no** packing, selector or `ExpDioph` module. The compiler half —
roughly 4,600 lines — is separable as it stands.

### Consumers, by abstraction

| abstraction | consumers in the arithmetisation | consumers elsewhere | reading |
|---|---|---|---|
| `RegisterMachine` core (`Program`, `Config`, `step`, `Accepts`) | 9 | 11 | genuinely shared; the reusable core |
| `Realises` (`RegisterMachineRealises`) | 0 | 8 | clean generic composition discipline |
| `RegisterMachineMacros` | 0 | 6 | generic |
| `CleanPartComputesUnary` (`CleanScratch`) | 3 | 5 | the interface where the two halves meet |
| `PartRealises` | 0 | 1 | no second consumer — keep internal |
| `ExpDioph` / `ExpTerm` | 4 | 1 (`Internal/TupleCoding`) | see below |
| `Aggregation` | 1 | 0 | route-internal |

**`ExpDioph` fails the second-consumer test.** Its only consumer outside the arithmetisation is
`Internal/TupleCoding`, which exists to supply the tuple graph for DPRM — part of the same
assembly, not an independent client. It is an excellent internal representation layer; that is not
the same as a public abstraction, and a roadmap should not promise it as one until something
outside the route uses it.

### Conventions baked into the machine model

Anything reusing this layer inherits these; they are design decisions, not incidental:

* **no `halt` instruction** — a configuration is halted exactly when its program counter is out of
  range, which makes list concatenation the sequential-composition operator;
* **every instruction carries its jump targets**, including `inc`, so relocation is a map rather
  than a case split;
* **clean scratch, unary convention** — `CleanPartComputesUnary` calls and returns with the value
  in register `0` and zeros elsewhere;
* **no configuration encoding in the machine layer** — the encoding, its base and its guard-bit
  width are chosen with the run packing that has to fit them.

---

## 5. Deliberately not done

Recorded so that a roadmap does not silently promise them:

* a generic finite-coordinate existential adapter (`Dioph.ex_fin`) — `ex_dioph` sufficed, and one
  consumer would not justify it;
* `REPred.range` — nothing consumes it; `range_dioph` reaches the Diophantine statement directly;
* arbitrary-`Primcodable` Diophantine transport — needs an encoding contract, see above;
* universe-polymorphic Diophantine closure — upstream, not restatable here;
* a `[Fintype α]` companion to the finite normal form — rejected by mathlib's own linter;
* computability of `evalInt` — no consumer; reductions need a computable map on codes;
* promoting `ExpDioph`, `CodeAlgebra` or tuple coding to public API — no second consumer;
* renaming the released `Hilbert10.Dioph` namespace to avoid the shadowing hazard — Tau Ceti can
  choose root namespaces from the start instead.
