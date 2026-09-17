/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.QuadraticLowering
import Hilbert10.Internal.CodeAlgebraComp

/-!
# The quadratic lowering is primitive recursive

Issue #57, third checkpoint. `quadraticSystem` is proved computable for the raw transformation:
none of the correctness certificates (`WellOrdered`, the invariants) become encoded data.

## Presentations

The structural definitions of `QuadraticLowering.lean` are kept. Where mathlib's computability
API wants a fold or a closed form, an equivalent presentation is introduced *here* and proved
equal to the structural one, so the public module never changes shape for the sake of a
`Primrec` proof:

* `mulPow` has a closed form over `List.range`;
* `compileMonomialFrom` is a `foldl` over the exponent vector carrying `(gates, acc, next, j)`;
* `compileTerms` is literally `foldl compileTerm`.

`Gate`, `Compiled` and `CompiledPoly` get `Primcodable` instances through explicit equivalences
with sums and products of naturals, following `PolynomialCodePrimcodable.lean`.

## Main results

* `Hilbert10.primrec_quadraticSystem`, `computable_quadraticSystem`
* `Hilbert10.PolynomialCode.primrec_degreeBound`, `primrecPred_degreeBound_le`
-/

namespace Hilbert10

open PolynomialCode Primrec

/-! ### Encodings -/

/-- `Gate` as a sum of tuples: the tag is the summand. -/
def Gate.equivSum : Gate ≃ (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ ((ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ))) where
  toFun
    | .const o c => .inl (o, c)
    | .copy o i => .inr (.inl (o, i))
    | .add o i j => .inr (.inr (.inl (o, i, j)))
    | .mul o i j => .inr (.inr (.inr (o, i, j)))
  invFun
    | .inl (o, c) => .const o c
    | .inr (.inl (o, i)) => .copy o i
    | .inr (.inr (.inl (o, i, j))) => .add o i j
    | .inr (.inr (.inr (o, i, j))) => .mul o i j
  left_inv g := by cases g <;> rfl
  right_inv s := by rcases s with _ | _ | _ | _ <;> rfl

instance : Primcodable Gate := Primcodable.ofEquiv _ Gate.equivSum

/-- `Compiled` as a triple. -/
def Compiled.equivProd : Compiled ≃ List Gate × ℕ × ℕ where
  toFun c := (c.gates, c.out, c.next)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Compiled := Primcodable.ofEquiv _ Compiled.equivProd

/-- `CompiledPoly` as a quadruple. -/
def CompiledPoly.equivProd : CompiledPoly ≃ List Gate × ℕ × ℕ × ℕ where
  toFun s := (s.gates, s.pos, s.neg, s.next)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable CompiledPoly := Primcodable.ofEquiv _ CompiledPoly.equivProd

/-! ### Gates -/

theorem primrec_gate_const : Primrec fun q : ℕ × ℕ => Gate.const q.1 q.2 :=
  (Primrec.of_equiv_symm (e := Gate.equivSum)).comp Primrec.sumInl

theorem primrec_gate_mul : Primrec fun q : ℕ × ℕ × ℕ => Gate.mul q.1 q.2.1 q.2.2 :=
  (Primrec.of_equiv_symm (e := Gate.equivSum)).comp
    (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem primrec_gate_add : Primrec fun q : ℕ × ℕ × ℕ => Gate.add q.1 q.2.1 q.2.2 :=
  (Primrec.of_equiv_symm (e := Gate.equivSum)).comp
    (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))

/-- `Sum.elim` of primitive recursive functions is primitive recursive. -/
private theorem primrec_sumElim {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → σ} {g : β → σ} (hf : Primrec f) (hg : Primrec g) : Primrec (Sum.elim f g) :=
  (Primrec.sumCasesOn Primrec.id (hf.comp Primrec.snd).to₂ (hg.comp Primrec.snd).to₂).of_eq
    fun s => by cases s <;> rfl

/-- The gate codes, on the sum presentation. -/
private def codeOfSum : (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ ((ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ))) → PolynomialCode :=
  Sum.elim (fun q => constGate q.1 q.2) (Sum.elim (fun q => eqGate q.1 q.2)
    (Sum.elim (fun q => addGate q.1 q.2.1 q.2.2) (fun q => mulGate q.1 q.2.1 q.2.2)))

private theorem gate_code_eq (g : Gate) : g.code = codeOfSum (Gate.equivSum g) := by
  cases g <;> rfl

private theorem primrec_constGate : Primrec fun q : ℕ × ℕ => constGate q.1 (q.2 : ℤ) :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_const.comp (Primrec.int_neg.comp (Primrec.int_natCast.comp Primrec.snd)))).of_eq
    fun _ => rfl

private theorem primrec_eqGate : Primrec fun q : ℕ × ℕ => eqGate q.1 q.2 :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_neg.comp (primrec_X.comp Primrec.snd))).of_eq fun _ => rfl

private theorem primrec_addGate : Primrec fun q : ℕ × ℕ × ℕ => addGate q.1 q.2.1 q.2.2 :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_neg.comp (Primrec₂.comp primrec₂_add (primrec_X.comp (Primrec.fst.comp Primrec.snd))
      (primrec_X.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => rfl

private theorem primrec_mulGate : Primrec fun q : ℕ × ℕ × ℕ => mulGate q.1 q.2.1 q.2.2 :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_neg.comp (Primrec₂.comp primrec₂_mul (primrec_X.comp (Primrec.fst.comp Primrec.snd))
      (primrec_X.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => rfl

private theorem primrec_codeOfSum : Primrec codeOfSum :=
  primrec_sumElim primrec_constGate (primrec_sumElim primrec_eqGate
    (primrec_sumElim primrec_addGate primrec_mulGate))

theorem primrec_gate_code : Primrec Gate.code :=
  (primrec_codeOfSum.comp (Primrec.of_equiv (e := Gate.equivSum))).of_eq fun g =>
    (gate_code_eq g).symm

/-! ### `mulPow`, in closed form -/

/-- The closed form: gate `k` writes `next + k` and reads the previous wire (or `acc` first). -/
def mulPowC (j acc next a : ℕ) : Compiled :=
  ⟨(List.range a).map fun k => Gate.mul (next + k) (if k = 0 then acc else next + k - 1) j,
    if a = 0 then acc else next + (a - 1), next + a⟩

theorem mulPow_out_eq (j acc next : ℕ) :
    ∀ a : ℕ, (mulPow j acc next a).out = if a = 0 then acc else next + (a - 1)
  | 0 => rfl
  | a + 1 => by
    rw [mulPow]
    dsimp only
    rw [mulPow_out_eq j next (next + 1) a]
    by_cases ha : a = 0
    · subst ha
      simp
    · simp only [ha, if_false, Nat.add_one_ne_zero]
      omega

theorem mulPow_gates_eq (j acc next : ℕ) :
    ∀ a : ℕ, (mulPow j acc next a).gates =
      (List.range a).map fun k => Gate.mul (next + k) (if k = 0 then acc else next + k - 1) j
  | 0 => rfl
  | a + 1 => by
    rw [mulPow]
    dsimp only
    rw [mulPow_gates_eq j next (next + 1) a, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.cons.injEq]
    refine ⟨by simp, List.map_congr_left fun k _ => ?_⟩
    simp only [Function.comp_def, Nat.succ_ne_zero, if_false]
    congr 1
    · omega
    · split_ifs <;> omega

theorem mulPow_eq_mulPowC (j a acc next : ℕ) : mulPow j acc next a = mulPowC j acc next a := by
  unfold mulPowC
  rw [← mulPow_gates_eq, ← mulPow_out_eq, ← mulPow_next]

theorem primrec_mulPowC : Primrec fun q : ℕ × ℕ × ℕ × ℕ => mulPowC q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  -- projections
  have hj : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.1 := Primrec.fst
  have hacc : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
  have hnext : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hgates : Primrec fun q : ℕ × ℕ × ℕ × ℕ => (List.range q.2.2.2).map fun k =>
      Gate.mul (q.2.2.1 + k) (if k = 0 then q.2.1 else q.2.2.1 + k - 1) q.1 := by
    have harg : Primrec fun r : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
        (r.1.2.2.1 + r.2, (if r.2 = 0 then r.1.2.1 else r.1.2.2.1 + r.2 - 1), r.1.1) := by
      refine (Primrec₂.comp Primrec.nat_add (hnext.comp Primrec.fst) Primrec.snd).pair ?_
      refine (Primrec.ite (PrimrecRel.comp (Primrec.eq (α := ℕ)) Primrec.snd
        (Primrec.const (0 : ℕ))) (hacc.comp Primrec.fst) ?_).pair (hj.comp Primrec.fst)
      exact Primrec₂.comp Primrec.nat_sub
        (Primrec₂.comp Primrec.nat_add (hnext.comp Primrec.fst) Primrec.snd)
        (Primrec.const (1 : ℕ))
    exact Primrec.list_map (Primrec.list_range.comp ha) (primrec_gate_mul.comp harg).to₂
  have hout : Primrec fun q : ℕ × ℕ × ℕ × ℕ =>
      if q.2.2.2 = 0 then q.2.1 else q.2.2.1 + (q.2.2.2 - 1) :=
    Primrec.ite (PrimrecRel.comp (Primrec.eq (α := ℕ)) ha (Primrec.const (0 : ℕ))) hacc
      (Primrec₂.comp Primrec.nat_add hnext
        (Primrec₂.comp Primrec.nat_sub ha (Primrec.const (1 : ℕ))))
  exact (Primrec.of_equiv_symm (e := Compiled.equivProd)).comp
    (hgates.pair (hout.pair (Primrec₂.comp Primrec.nat_add hnext ha)))

theorem primrec_mulPow : Primrec fun q : ℕ × ℕ × ℕ × ℕ => mulPow q.1 q.2.1 q.2.2.1 q.2.2.2 :=
  primrec_mulPowC.of_eq fun _ => (mulPow_eq_mulPowC _ _ _ _).symm

/-! ### `compileMonomialFrom`, as a fold -/

/-- The fold state: gates so far, accumulator wire, next wire, current variable. -/
private def monoStep (s : List Gate × ℕ × ℕ × ℕ) (a : ℕ) : List Gate × ℕ × ℕ × ℕ :=
  let c := mulPow s.2.2.2 s.2.1 s.2.2.1 a
  (s.1 ++ c.gates, c.out, c.next, s.2.2.2 + 1)

private theorem foldl_monoStep :
    ∀ (es : MonomialCode) (gates : List Gate) (acc next j : ℕ),
      es.foldl monoStep (gates, acc, next, j) =
        (gates ++ (compileMonomialFrom acc next j es).gates,
          (compileMonomialFrom acc next j es).out, (compileMonomialFrom acc next j es).next,
          j + es.length)
  | [], gates, acc, next, j => by simp [compileMonomialFrom]
  | a :: es, gates, acc, next, j => by
    rw [List.foldl_cons, monoStep, foldl_monoStep es]
    simp only [compileMonomialFrom, List.append_assoc, List.length_cons, Prod.mk.injEq, true_and]
    omega

private theorem primrec_monoStep : Primrec₂ monoStep := by
  have hc : Primrec fun q : (List Gate × ℕ × ℕ × ℕ) × ℕ =>
      mulPow q.1.2.2.2 q.1.2.1 q.1.2.2.1 q.2 :=
    primrec_mulPow.comp
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
            Primrec.snd)))
  have hgates : Primrec fun c : Compiled => c.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := Compiled.equivProd))
  have hout : Primrec fun c : Compiled => c.out :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have hnext : Primrec fun c : Compiled => c.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have h : Primrec fun q : (List Gate × ℕ × ℕ × ℕ) × ℕ => monoStep q.1 q.2 :=
    (Primrec₂.comp Primrec.list_append (Primrec.fst.comp Primrec.fst) (hgates.comp hc)).pair
      ((hout.comp hc).pair ((hnext.comp hc).pair (Primrec₂.comp Primrec.nat_add
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const (1 : ℕ)))))
  exact h.to₂

theorem primrec_compileMonomialFrom :
    Primrec fun q : ℕ × ℕ × ℕ × MonomialCode => compileMonomialFrom q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hfold : Primrec fun q : ℕ × ℕ × ℕ × MonomialCode =>
      q.2.2.2.foldl (fun s b => monoStep s b) (([] : List Gate), q.1, q.2.1, q.2.2.1) :=
    Primrec.list_foldl (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      ((Primrec.const ([] : List Gate)).pair (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
      (primrec_monoStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  refine ((Primrec.of_equiv_symm (e := Compiled.equivProd)).comp
    ((Primrec.fst.comp hfold).pair ((Primrec.fst.comp (Primrec.snd.comp hfold)).pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hfold)))))).of_eq fun q => ?_
  rw [foldl_monoStep]
  rfl

theorem primrec_compileMonomial : Primrec₂ compileMonomial := by
  have hc : Primrec fun q : MonomialCode × ℕ => compileMonomialFrom q.2 (q.2 + 1) 0 q.1 :=
    primrec_compileMonomialFrom.comp (Primrec.snd.pair
      ((Primrec₂.comp Primrec.nat_add Primrec.snd (Primrec.const (1 : ℕ))).pair
        ((Primrec.const (0 : ℕ)).pair Primrec.fst)))
  have hgates : Primrec fun c : Compiled => c.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := Compiled.equivProd))
  have hout : Primrec fun c : Compiled => c.out :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have hnext : Primrec fun c : Compiled => c.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have h : Primrec fun q : MonomialCode × ℕ => compileMonomial q.1 q.2 :=
    ((Primrec.of_equiv_symm (e := Compiled.equivProd)).comp
      ((Primrec₂.comp Primrec.list_cons
          (primrec_gate_const.comp (Primrec.snd.pair (Primrec.const (1 : ℕ))))
          (hgates.comp hc)).pair
        ((hout.comp hc).pair (hnext.comp hc)))).of_eq fun _ => rfl
  exact h.to₂

/-! ### Terms and the polynomial -/

private theorem primrec_compileTerm : Primrec₂ compileTerm := by
  have hsg : Primrec fun s : CompiledPoly => s.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := CompiledPoly.equivProd))
  have hsp : Primrec fun s : CompiledPoly => s.pos :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := CompiledPoly.equivProd)))
  have hsn : Primrec fun s : CompiledPoly => s.neg :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := CompiledPoly.equivProd))))
  have hsx : Primrec fun s : CompiledPoly => s.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := CompiledPoly.equivProd))))
  have hcg : Primrec fun c : Compiled => c.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := Compiled.equivProd))
  have hco : Primrec fun c : Compiled => c.out :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have hcx : Primrec fun c : Compiled => c.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  -- the compiled monomial of the term, from the state's next wire
  have hcm : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) => compileMonomial q.2.2 q.1.next :=
    primrec_compileMonomial.comp (Primrec.snd.comp Primrec.snd) (hsx.comp Primrec.fst)
  have hnonneg : PrimrecPred fun q : CompiledPoly × (ℤ × MonomialCode) => 0 ≤ q.2.1 :=
    Primrec.int_nonneg.comp (Primrec.fst.comp Primrec.snd)
  have hnx := hcx.comp hcm
  have hplus : ∀ k : ℕ, Primrec fun q : CompiledPoly × (ℤ × MonomialCode) =>
      (compileMonomial q.2.2 q.1.next).next + k := fun k =>
    Primrec₂.comp Primrec.nat_add hnx (Primrec.const (k : ℕ))
  have hsel : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) =>
      if 0 ≤ q.2.1 then q.1.pos else q.1.neg :=
    Primrec.ite hnonneg (hsp.comp Primrec.fst) (hsn.comp Primrec.fst)
  have htg : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) => termGates q.1 q.2 := by
    refine (Primrec₂.comp Primrec.list_append (hcg.comp hcm) ?_).of_eq fun q => rfl
    refine Primrec₂.comp Primrec.list_cons
      (primrec_gate_const.comp (hnx.pair (Primrec.int_natAbs.comp (Primrec.fst.comp Primrec.snd))))
      ?_
    refine Primrec₂.comp Primrec.list_cons
      (primrec_gate_mul.comp ((hplus 1).pair ((hco.comp hcm).pair hnx))) ?_
    exact Primrec₂.comp Primrec.list_cons
      (primrec_gate_add.comp ((hplus 2).pair (hsel.pair (hplus 1))))
      (Primrec.const ([] : List Gate))
  have h : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) => compileTerm q.1 q.2 :=
    ((Primrec.of_equiv_symm (e := CompiledPoly.equivProd)).comp
      ((Primrec₂.comp Primrec.list_append (hsg.comp Primrec.fst) htg).pair
        ((Primrec.ite hnonneg (hplus 2) (hsp.comp Primrec.fst)).pair
          ((Primrec.ite hnonneg (hsn.comp Primrec.fst) (hplus 2)).pair (hplus 3))))).of_eq
      fun _ => rfl
  exact h.to₂

private theorem compileTerms_eq_foldl (s : CompiledPoly) :
    ∀ ts : List (ℤ × MonomialCode), compileTerms s ts = ts.foldl compileTerm s
  | [] => rfl
  | t :: ts => compileTerms_eq_foldl (compileTerm s t) ts

private theorem primrec_compileTerms : Primrec₂ compileTerms := by
  have h : Primrec fun q : CompiledPoly × List (ℤ × MonomialCode) => compileTerms q.1 q.2 :=
    (Primrec.list_foldl (f := fun q : CompiledPoly × List (ℤ × MonomialCode) => q.2)
      (g := fun q => q.1) (h := fun _ r => compileTerm r.1 r.2) Primrec.snd Primrec.fst
      (primrec_compileTerm.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun q => (compileTerms_eq_foldl q.1 q.2).symm
  exact h.to₂

theorem primrec_compilePoly : Primrec₂ compilePoly := by
  have hinit : Primrec fun q : PolynomialCode × ℕ =>
      (⟨[Gate.const q.2 0], q.2, q.2, q.2 + 1⟩ : CompiledPoly) :=
    (Primrec.of_equiv_symm (e := CompiledPoly.equivProd)).comp
      ((Primrec₂.comp Primrec.list_cons
        (primrec_gate_const.comp (Primrec.snd.pair (Primrec.const (0 : ℕ))))
        (Primrec.const ([] : List Gate))).pair
        (Primrec.snd.pair (Primrec.snd.pair (Primrec₂.comp Primrec.nat_add Primrec.snd
          (Primrec.const (1 : ℕ))))))
  have h : Primrec fun q : PolynomialCode × ℕ => compilePoly q.1 q.2 :=
    (primrec_compileTerms.comp hinit (primrec_terms.comp Primrec.fst)).of_eq fun _ => rfl
  exact h.to₂

theorem primrec_quadraticSystem : Primrec quadraticSystem := by
  have hcp : Primrec fun p : PolynomialCode => compilePoly p p.arity :=
    primrec_compilePoly.comp Primrec.id primrec_arity
  have hsg : Primrec fun s : CompiledPoly => s.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := CompiledPoly.equivProd))
  have hsp : Primrec fun s : CompiledPoly => s.pos :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := CompiledPoly.equivProd)))
  have hsn : Primrec fun s : CompiledPoly => s.neg :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := CompiledPoly.equivProd))))
  refine (Primrec₂.comp Primrec.list_append
    (Primrec.list_map (hsg.comp hcp) (primrec_gate_code.comp Primrec.snd).to₂)
    (Primrec₂.comp Primrec.list_cons
      (primrec_eqGate.comp ((hsp.comp hcp).pair (hsn.comp hcp)))
      (Primrec.const ([] : List PolynomialCode)))).of_eq
    fun p => rfl

theorem computable_quadraticSystem : Computable quadraticSystem :=
  primrec_quadraticSystem.to_comp

/-! ### The degree test -/

namespace PolynomialCode

private theorem primrec_list_sum : Primrec fun l : List ℕ => l.sum := by
  refine (Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ => 0)
    (h := fun _ q => q.1 + q.2) Primrec.id (Primrec.const (0 : ℕ))
    (Primrec₂.comp Primrec.nat_add (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem primrec_degreeBound : Primrec degreeBound := by
  refine (Primrec.list_foldr (f := fun p : PolynomialCode => p.terms) (g := fun _ => 0)
    (h := fun _ q => max q.1.2.sum q.2) primrec_terms (Primrec.const (0 : ℕ))
    (Primrec₂.comp Primrec.nat_max
      (primrec_list_sum.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun p => ?_
  simp only [degreeBound, monomialDegree]
  induction p.terms with
  | nil => rfl
  | cons t ts ih => simp [ih]

/-- **The degree test is primitive recursive**, which is what recursive enumerability of the
restricted problems needs — decidability alone would not do. -/
theorem primrecPred_degreeBound_le (d : ℕ) :
    PrimrecPred fun p : PolynomialCode => p.degreeBound ≤ d :=
  PrimrecRel.comp Primrec.nat_le primrec_degreeBound (Primrec.const d)

end PolynomialCode

end Hilbert10
