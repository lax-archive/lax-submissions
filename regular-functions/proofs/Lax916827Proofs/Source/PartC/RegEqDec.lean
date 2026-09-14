/- Theorem `thm:decidable-equivalence-regular` of *Transducers* (M. Bojańczyk): equivalence is
decidable for regular functions, here in the form of a decision procedure on codes of two-way
transducers (which compute exactly the regular functions, Theorem
`thm:2dfa-decomposition-into-primes`).

The proof is the expected one, and follows the shape of the decision procedure of Theorems
`thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata` in
`RequestProject/PartB/WeightedDec.lean`: compute the equivalence bound `N` for the two codes and
compare the two behaviours on all inputs of length at most `N`.  Two things have to be checked for
this to be a *total* procedure and a correct one.

* Only the finitely many strings over the letters occurring in the two codes,
  together with one fresh letter, are tested.  This is enough because a code
  cannot distinguish two letters that are both absent from its transition
  table: renaming every letter outside the two tables to the fresh letter
  changes neither behaviour (`Transducers.RegDec.twoWayCodeRel_map`) and
  preserves the length of the input.
* The two coded transducers have to be compared on a given input, and the equivalence bound has to
  be computed from the two codes.  Both are proved: `Transducers.EffectiveTwoWayEvalEq` in
  `RequestProject/PartC/TwoWaySimPrimrec.lean`, and `Transducers.effectiveTwoWayBound` in
  `RequestProject/PartC/RegEffBound.lean` (which discharges the former hypothesis
  `Transducers.EffectiveTwoWayBound` of `RequestProject/PartC/EffectiveReg.lean`, with the explicit
  bound `Transducers.RegDec.codeBound`).  The decision procedure below is therefore
  unconditional.
-/
import Lax916827Proofs.Source.PartC.EffectiveReg
import Lax916827Proofs.Source.PartC.RegCodeBound
import Lax916827Proofs.Source.PartC.RegEffBound
import Lax132576Proofs.Source.PartB.WeightedDec
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace RegDec

/-! ## The decision procedure -/

/-- The strings tested by the decision procedure: those of length at most the
equivalence bound over the letters of the two codes and the fresh letter. -/
def testWords (N : TwoWayCode → TwoWayCode → ℕ) (p : TwoWayCode × TwoWayCode) :
    List (List ℕ) :=
  WDec.wordsUpto (testAlphabet p) (N p.1 p.2)

/-- The decision procedure for Theorem `thm:decidable-equivalence-regular`, built from a pointwise
equivalence test `D` and an equivalence bound `N`. -/
def regEqB (D : TwoWayCode × TwoWayCode × List ℕ → Bool) (N : TwoWayCode → TwoWayCode → ℕ)
    (p : TwoWayCode × TwoWayCode) : Bool :=
  WDec.allIdx (testWords N p) (fun w => D (p.1, p.2, w)) (testWords N p).length

lemma regEqB_iff {D : TwoWayCode × TwoWayCode × List ℕ → Bool} {N : TwoWayCode → TwoWayCode → ℕ}
    (hD : ∀ c₁ c₂ (w : List ℕ), TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      (D (c₁, c₂, w) = true ↔ twoWayCodeRel c₁ w = twoWayCodeRel c₂ w))
    (hN : ∀ c₁ c₂, TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      ((∀ w : List ℕ, w.length ≤ N c₁ c₂ → twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) →
        twoWayCodeRel c₁ = twoWayCodeRel c₂))
    (p : TwoWayCode × TwoWayCode) (h₁ : TwoWayCodeTotal p.1) (h₂ : TwoWayCodeTotal p.2) :
    regEqB D N p = true ↔ twoWayCodeRel p.1 = twoWayCodeRel p.2 := by
  rw [regEqB, WDec.allIdx_iff]
  constructor
  · intro h
    refine hN p.1 p.2 h₁ h₂ ?_
    intro w hw
    have hmem : w.map (sanLetter p) ∈ testWords N p := by
      refine (WDec.mem_wordsUpto _ _ _).2 ⟨by simpa using hw, ?_⟩
      intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact sanLetter_mem_testAlphabet p y
    have hsan := (hD p.1 p.2 _ h₁ h₂).1 (h _ hmem)
    funext v
    have e₁ := twoWayCodeRel_map (blind_sanLetter_left p) w v
    have e₂ := twoWayCodeRel_map (blind_sanLetter_right p) w v
    have := congrFun hsan v
    simp only [eq_iff_iff] at this ⊢
    rw [← e₁, ← e₂]
    exact this
  · intro h w _
    exact (hD p.1 p.2 w h₁ h₂).2 (by rw [h])

/-! ## Computability of the procedure -/

lemma primrec_alphabet : Primrec alphabet := by
  refine Primrec.list_flatMap Primrec.id ?_
  show Primrec fun z : TwoWayCode ×
      ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool))) =>
    [z.2.1.1.getD 0, z.2.1.2.2.getD 0]
  have h1 : Primrec fun z : TwoWayCode ×
      ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool))) => z.2.1.1.getD 0 :=
    Primrec.option_getD.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0)
  have h2 : Primrec fun z : TwoWayCode ×
      ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool))) => z.2.1.2.2.getD 0 :=
    Primrec.option_getD.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.const 0)
  exact Primrec.list_cons.comp h1
    (Primrec.list_cons.comp h2 (Primrec.const ([] : List ℕ)))

lemma primrec_freshLetter : Primrec freshLetter := by
  have hfold : Primrec fun L : List ℕ => L.foldr max 0 := by
    have h : Primrec₂ fun (_ : List ℕ) (z : ℕ × ℕ) => max z.1 z.2 :=
      Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    exact (Primrec.list_foldr (f := fun L : List ℕ => L) (g := fun _ => 0)
      Primrec.id (Primrec.const 0) h).of_eq (fun L => rfl)
  exact Primrec.succ.comp hfold

lemma primrec_testAlphabet : Primrec testAlphabet := by
  have hL : Primrec fun p : TwoWayCode × TwoWayCode => alphabet p.1 ++ alphabet p.2 :=
    Primrec.list_append.comp (primrec_alphabet.comp Primrec.fst)
      (primrec_alphabet.comp Primrec.snd)
  exact Primrec.list_cons.comp (primrec_freshLetter.comp hL) hL

lemma computable_regEqB {D : TwoWayCode × TwoWayCode × List ℕ → Bool}
    {N : TwoWayCode → TwoWayCode → ℕ} (hD : Computable D) (hN : Computable₂ N) :
    Computable (regEqB D N) := by
  have hwords : Computable (testWords N) :=
    WDec.primrec_wordsUpto.to_comp.comp primrec_testAlphabet.to_comp
      (hN.comp Computable.fst Computable.snd)
  have hD' : Computable₂ (fun (p : TwoWayCode × TwoWayCode) (w : List ℕ) => D (p.1, p.2, w)) :=
    hD.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
  exact WDec.computable_allIdx hwords hD' (Computable.list_length.comp hwords)

end RegDec

/-- **Theorem `thm:decidable-equivalence-regular`.**  Equivalence is decidable for the two-way
transducers computing regular functions.  Both effectivity ingredients are proved:
`Transducers.EffectiveTwoWayEvalEq` and `Transducers.effectiveTwoWayBound`. -/
theorem regular_equivalence_decidable_aux :
    DecidableUnderPromise
      (fun p : TwoWayCode × TwoWayCode => TwoWayCodeTotal p.1 ∧ TwoWayCodeTotal p.2)
      (fun p => twoWayCodeRel p.1 = twoWayCodeRel p.2) := by
  obtain ⟨D, hDcomp, hD⟩ := EffectiveTwoWayEvalEq
  obtain ⟨N, hNcomp, hN⟩ := effectiveTwoWayBound
  exact ⟨RegDec.regEqB D N, RegDec.computable_regEqB hDcomp hNcomp,
    fun p hp => RegDec.regEqB_iff hD hN p hp.1 hp.2⟩

end Lax916827Proofs.Transducers
