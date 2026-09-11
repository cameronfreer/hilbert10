/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.PolynomialCodeDenote
import Hilbert10.ExistsCode
import Hilbert10.NatSolvable
import Hilbert10.IntSolvable
import Hilbert10.SumSquares
import Hilbert10.Systems
import Hilbert10.Degree
import Hilbert10.QuadraticGates
import Hilbert10.NormalForm
import Hilbert10.Computability
import Hilbert10.DPRM
import Hilbert10.DerivedDioph
import Hilbert10.Endpoints

/-!
# The headline results, at their advertised types

`scripts/AxiomAudit.lean` protects the headline declarations by *name*: renaming or deleting one
fails the gate. It says nothing about their *types*. This file closes that gap: every headline is
applied once, at the signature the documentation states for it, written out in full rather than
inferred. A change to a headline's statement — an extra hypothesis, a narrowed domain, a
different layout — fails here, at the line that spells out what was promised.

Two properties are exercised deliberately, since both were design decisions rather than
accidents:

* completeness holds on an **empty** input type, with no `Inhabited` hypothesis;
* the two definitions of solvability are **definitionally** the root-existence statements the
  documentation gives, so `Iff.rfl` is a proof.

This file imports the public constituent modules rather than `Hilbert10`, because the root
imports it: it is a regression, and belongs in the audited spine.
-/

namespace Hilbert10

/-! ### The wire format -/

example (p : PolynomialCode) (x : List ℤ) :
    MvPolynomial.eval (fun i => x.getD i 0) p.denote = p.evalInt x :=
  PolynomialCode.evalInt_denote p x

example (p : PolynomialCode) (x : List ℕ) :
    MvPolynomial.eval (fun i => ((x.getD i 0 : ℕ) : ℤ)) p.denote = p.eval x :=
  PolynomialCode.eval_denote p x

example {n m : ℕ} (p : MvPolynomial (Fin n ⊕ Fin m) ℤ) :
    ∃ q : PolynomialCode, q.arity ≤ n + m ∧
      q.denote = MvPolynomial.rename (PolynomialCode.varIndex n m) p :=
  PolynomialCode.exists_code p

example {n m : ℕ} {p : MvPolynomial (Fin n ⊕ Fin m) ℤ} {q : PolynomialCode}
    (hq : q.denote = MvPolynomial.rename (PolynomialCode.varIndex n m) p)
    (x : Fin n → ℕ) (y : Fin m → ℕ) :
    q.eval (List.ofFn x ++ List.ofFn y) =
      MvPolynomial.eval (Sum.elim (fun i => ((x i : ℕ) : ℤ)) fun j => ((y j : ℕ) : ℤ)) p :=
  PolynomialCode.eval_exists_code hq x y

example (p : PolynomialCode) :
    p.HasNatRoot ↔ ∃ x : List ℕ, x.length = p.arity ∧ p.eval x = 0 :=
  PolynomialCode.hasNatRoot_iff p

/-! ### The two decision problems -/

example (p : PolynomialCode) : NatSolvable p ↔ ∃ x : List ℕ, p.eval x = 0 := Iff.rfl

example (p : PolynomialCode) : IntSolvable p ↔ ∃ x : List ℤ, p.evalInt x = 0 := Iff.rfl

example (p : PolynomialCode) :
    NatSolvable p ↔ ∃ x : List ℕ, x.length = p.arity ∧ p.eval x = 0 :=
  natSolvable_iff_arity p

example (p : PolynomialCode) :
    IntSolvable p ↔ ∃ x : List ℤ, x.length = p.arity ∧ p.evalInt x = 0 :=
  intSolvable_iff_arity p

example {p q : PolynomialCode} (h : p.denote = q.denote) : NatSolvable p ↔ NatSolvable q :=
  natSolvable_iff_of_denote_eq h

example {p q : PolynomialCode} (h : p.denote = q.denote) : IntSolvable p ↔ IntSolvable q :=
  intSolvable_iff_of_denote_eq h

/-! ### DPRM, both directions -/

example {n : ℕ} {R : (Fin n → ℕ) → Prop} (h : Dioph {x | R x}) : REPred R :=
  Dioph.rePred h

example {n : ℕ} {R : (Fin n → ℕ) → Prop} (h : REPred R) : Dioph {x | R x} :=
  REPred.dioph h

example {n : ℕ} (R : (Fin n → ℕ) → Prop) : Dioph {x | R x} ↔ REPred R :=
  dioph_iff_rePred R

example {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) : Dioph {v : Fin 2 → ℕ | v 1 ∈ f (v 0)} :=
  Nat.Partrec.graph_dioph hf

example {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) : Dioph {v : Fin 1 → ℕ | (f (v 0)).Dom} :=
  Nat.Partrec.dom_dioph hf

/-! ### The natural endpoints -/

example : REPred NatSolvable := rePred_natSolvable

example {R : ℕ → Prop} (hR : REPred R) : R ≤₀ NatSolvable :=
  REPred.manyOneReducible_natSolvable hR

example {α : Type*} [Primcodable α] {R : α → Prop} (hR : REPred R) : R ≤₀ NatSolvable :=
  natSolvable_re_complete hR

/-- Completeness on the empty type: no `Inhabited` hypothesis. -/
example (R : Empty → Prop) (hR : REPred R) : R ≤₀ NatSolvable :=
  natSolvable_re_complete hR

example : (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ NatSolvable :=
  halting_manyOneReducible_natSolvable

example : ¬ ComputablePred NatSolvable := not_computablePred_natSolvable

example : ¬ REPred fun p => ¬ NatSolvable p := not_rePred_not_natSolvable

/-! ### The integer formulation -/

example (p : PolynomialCode) : IntSolvable p ↔ NatSolvable p.subUV :=
  intSolvable_iff_natSolvable_subUV p

example : IntSolvable ≤₀ NatSolvable := intSolvable_manyOneReducible_natSolvable

example (p : PolynomialCode) : NatSolvable p ↔ IntSolvable p.fourSquares :=
  natSolvable_iff_intSolvable_fourSquares p

example : NatSolvable ≤₀ IntSolvable := natSolvable_manyOneReducible_intSolvable

example : ManyOneEquiv NatSolvable IntSolvable := natSolvable_manyOneEquiv_intSolvable

example : REPred IntSolvable := rePred_intSolvable

example {α : Type*} [Primcodable α] {R : α → Prop} (hR : REPred R) : R ≤₀ IntSolvable :=
  intSolvable_re_complete hR

/-- Completeness on the empty type, integer version. -/
example (R : Empty → Prop) (hR : REPred R) : R ≤₀ IntSolvable :=
  intSolvable_re_complete hR

example : ¬ ComputablePred IntSolvable := not_computablePred_intSolvable

example : ¬ REPred fun p => ¬ IntSolvable p := not_rePred_not_intSolvable

/-! ### Finite systems with a shared assignment -/

example (ps : List PolynomialCode) : SystemNatSolvable ps ↔ ∃ x : List ℕ, ∀ p ∈ ps, p.eval x = 0 :=
  Iff.rfl

example (ps : List PolynomialCode) :
    SystemIntSolvable ps ↔ ∃ x : List ℤ, ∀ p ∈ ps, p.evalInt x = 0 :=
  Iff.rfl

example (ps : List PolynomialCode) (x : List ℤ) :
    PolynomialCode.evalInt (PolynomialCode.sumSquaresCode ps) x =
      (ps.map fun p => (p.evalInt x) ^ 2).sum :=
  PolynomialCode.evalInt_sumSquaresCode ps x

example (ps : List PolynomialCode) (x : List ℕ) :
    PolynomialCode.eval (PolynomialCode.sumSquaresCode ps) x =
      (ps.map fun p => (p.eval x) ^ 2).sum :=
  PolynomialCode.eval_sumSquaresCode ps x

example (ps : List PolynomialCode) (x : List ℤ) :
    PolynomialCode.evalInt (PolynomialCode.sumSquaresCode ps) x = 0 ↔ ∀ p ∈ ps, p.evalInt x = 0 :=
  PolynomialCode.evalInt_sumSquaresCode_eq_zero_iff ps x

example (ps : List PolynomialCode) :
    (PolynomialCode.sumSquaresCode ps).arity ≤ PolynomialCode.systemArity ps :=
  PolynomialCode.arity_sumSquaresCode_le ps

example (ps : List PolynomialCode) :
    SystemNatSolvable ps ↔ NatSolvable (PolynomialCode.sumSquaresCode ps) :=
  systemNatSolvable_iff_natSolvable_sumSquaresCode ps

example (ps : List PolynomialCode) :
    SystemIntSolvable ps ↔ IntSolvable (PolynomialCode.sumSquaresCode ps) :=
  systemIntSolvable_iff_intSolvable_sumSquaresCode ps

example : ManyOneEquiv NatSolvable SystemNatSolvable := natSolvable_manyOneEquiv_systemNatSolvable

example : ManyOneEquiv IntSolvable SystemIntSolvable := intSolvable_manyOneEquiv_systemIntSolvable

/-! ### Degree, and the quadratic gates -/

example (p : PolynomialCode) : p.denote.totalDegree ≤ p.degreeBound :=
  PolynomialCode.totalDegree_denote_le p

example (ps : List PolynomialCode) :
    (PolynomialCode.sumSquaresCode ps).degreeBound ≤ 2 * PolynomialCode.systemDegreeBound ps :=
  PolynomialCode.degreeBound_sumSquaresCode_le ps

example (g : Gate) (x : List ℤ) : PolynomialCode.evalInt g.code x = 0 ↔ g.Holds x :=
  Gate.evalInt_code_eq_zero_iff g x

example (g : Gate) (x : List ℕ) : PolynomialCode.eval g.code x = 0 ↔ g.Holds x :=
  Gate.eval_code_eq_zero_iff g x

example (g : Gate) : g.code.degreeBound ≤ 2 := Gate.degreeBound_code_le g

example {R : Type} [Semiring R] (gs : List Gate) (n : ℕ) (h : WellOrdered n gs) (x : List R)
    (hx : x.length = n) :
    ∃ y : List R, y.length = n + gs.length ∧ y.take n = x ∧ ∀ g ∈ gs, g.Holds y :=
  exists_extension gs n h x hx

/-! ### The derived Diophantine API -/

example {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop}
    (h : p ≤₀ q) (hq : REPred q) : REPred p :=
  REPred.of_manyOneReducible h hq

example {α : Type} [Finite α] (R : (α → ℕ) → Prop) :
    Dioph {x | R x} ↔ ∃ (m : ℕ) (p : MvPolynomial (α ⊕ Fin m) ℤ), RepresentsNat p R :=
  dioph_iff_exists_finite_mvPolynomial R

/-- A finite input type that is not a `Fin n`. -/
example (R : (Bool → ℕ) → Prop) :
    Dioph {x | R x} ↔ ∃ (m : ℕ) (p : MvPolynomial (Bool ⊕ Fin m) ℤ), RepresentsNat p R :=
  dioph_iff_exists_finite_mvPolynomial R

example {n m : ℕ} {R : (Fin n → ℕ) → Prop} {S : (Fin m → ℕ) → Prop} (hRS : R ≤₀ S)
    (hS : Dioph {x | S x}) : Dioph {x | R x} :=
  Dioph.of_manyOneReducible hRS hS

example {n : ℕ} {R : (Fin n → ℕ) → Prop} (hR : ComputablePred R) : Dioph {x | R x} :=
  ComputablePred.dioph hR

example {n : ℕ} (R : (Fin n → ℕ) → Prop) :
    ComputablePred R ↔ Dioph {x | R x} ∧ Dioph {x | ¬ R x} :=
  computablePred_iff_dioph_compl_dioph R

example {f : ℕ → ℕ} (hf : Computable f) : Dioph {v : Fin 2 → ℕ | v 1 = f (v 0)} :=
  Computable.graph_dioph hf

example {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) : Dioph {v : Fin 1 → ℕ | ∃ a, v 0 ∈ f a} :=
  Nat.Partrec.range_dioph hf

end Hilbert10
