/- Theorems `thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata` of
*Transducers* (M. Bojańczyk): equivalence and zeroness are decidable for weighted automata over the
field of rationals.

Both are proved here outright.  The two effectivity facts they use are theorems: the computable
equality test `Transducers.EffectiveWeightedEvalEq` (`RequestProject/PartB/WCodePrimrec.lean`) and
the effective Schützenberger bound `Transducers.effectiveWeightedBound`
(`RequestProject/PartB/WeightedBound.lean`).
The decision procedure for equivalence is the expected one: compute the
Schützenberger bound `N` for the two codes and compare the two values on all
strings of length at most `N`.  Two things have to be checked for this to be a
*total* procedure and a correct one.

* Only the finitely many strings over the letters occurring in the two codes are
  tested; on a string using any other letter both automata have no accepting run
  at all and hence take the value `0` (`wcodeEval_eq_zero_of_foreign`).
* Zeroness is the special case of equivalence with the code of the empty
  automaton (`zeroWCode`), which computes the constant function `0`.
-/
import Lax132576Proofs.Source.PartB.WeightedBound
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace WDec

/-! ## Bounded universal quantification over a list

Mathlib's `Computable` API has no combinator for folding a computable function
over a list, so a bounded universal quantifier is written here as a primitive
recursion on the index, for which `Computable.nat_rec` is available. -/

/-- `allIdx l p k` tests `p` on the entries of `l` with index `< k`. -/
def allIdx {α : Type} (l : List α) (p : α → Bool) (k : ℕ) : Bool :=
  Nat.rec true (fun n ih => ((l[n]?.map p).getD true) && ih) k

lemma allIdx_iff_lt {α : Type} (l : List α) (p : α → Bool) (k : ℕ) :
    allIdx l p k = true ↔ ∀ n < k, ((l[n]?.map p).getD true) = true := by
  induction k with
  | zero => simp [allIdx]
  | succ k ih =>
      simp only [allIdx, Bool.and_eq_true] at *
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩ n hn
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | rfl
        · exact h2 n h
        · exact h1
      · intro h
        exact ⟨h k (Nat.lt_succ_self k), fun n hn => h n (Nat.lt_succ_of_lt hn)⟩

lemma allIdx_iff {α : Type} (l : List α) (p : α → Bool) :
    allIdx l p l.length = true ↔ ∀ x ∈ l, p x = true := by
  rw [allIdx_iff_lt]
  constructor
  · intro h x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hx
    have := h n hn
    simpa [List.getElem?_eq_getElem hn] using this
  · intro h n hn
    simpa [List.getElem?_eq_getElem hn] using h _ (List.getElem_mem hn)

lemma computable_allIdx {α β : Type} [Primcodable α] [Primcodable β]
    {L : α → List β} {D : α → β → Bool} {k : α → ℕ}
    (hL : Computable L) (hD : Computable₂ D) (hk : Computable k) :
    Computable (fun a => allIdx (L a) (D a) (k a)) := by
  have h1 : Computable (fun z : α × (ℕ × Bool) => (L z.1)[z.2.1]?) :=
    Computable.list_getElem?.comp (hL.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hD' : Computable₂ (fun (z : α × (ℕ × Bool)) (b : β) => D z.1 b) :=
    hD.comp (Computable.fst.comp Computable.fst) Computable.snd
  have h2 : Computable (fun z : α × (ℕ × Bool) => (((L z.1)[z.2.1]?).map (D z.1)).getD true) :=
    Computable.option_getD (Computable.option_map h1 hD') (Computable.const true)
  have key : Computable₂ (fun (a : α) (q : ℕ × Bool) =>
      ((((L a)[q.1]?).map (D a)).getD true) && q.2) :=
    (Primrec.and.to_comp).comp h2 (Computable.snd.comp Computable.snd)
  exact (Computable.nat_rec hk (Computable.const true) key).of_eq (fun a => rfl)

/-! ## Enumeration of the short strings over a finite set of letters -/

/-- All strings of length at most `k` over the letters of `L`. -/
def wordsUpto (L : List ℕ) (k : ℕ) : List (List ℕ) :=
  Nat.rec [[]] (fun _ ih => [] :: L.flatMap (fun a => ih.map (fun w => a :: w))) k

@[simp] lemma wordsUpto_zero (L : List ℕ) : wordsUpto L 0 = [[]] := rfl

@[simp] lemma wordsUpto_succ (L : List ℕ) (k : ℕ) :
    wordsUpto L (k + 1) = [] :: L.flatMap (fun a => (wordsUpto L k).map (fun w => a :: w)) := rfl

lemma mem_wordsUpto (L : List ℕ) (k : ℕ) (w : List ℕ) :
    w ∈ wordsUpto L k ↔ w.length ≤ k ∧ ∀ x ∈ w, x ∈ L := by
  induction k generalizing w with
  | zero =>
      simp only [wordsUpto_zero, List.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact h
  | succ k ih =>
      constructor
      · intro h
        simp only [wordsUpto_succ, List.mem_cons, List.mem_flatMap, List.mem_map] at h
        rcases h with rfl | ⟨a, haL, rest, hrest, rfl⟩
        · simp
        · obtain ⟨h1, h2⟩ := (ih rest).1 hrest
          refine ⟨by simpa using h1, ?_⟩
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact haL
          · exact h2 x hx'
      · rintro ⟨h1, h2⟩
        simp only [wordsUpto_succ, List.mem_cons, List.mem_flatMap, List.mem_map]
        match w with
        | [] => exact Or.inl rfl
        | a :: rest =>
            refine Or.inr ⟨a, h2 a (by simp), rest, ?_, rfl⟩
            exact (ih rest).2 ⟨by simpa using h1, fun x hx => h2 x (by simp [hx])⟩

lemma primrec_wordsUpto : Primrec₂ wordsUpto := by
  refine Primrec.nat_rec (f := fun _ : List ℕ => ([[]] : List (List ℕ)))
    (g := fun L p => ([] : List ℕ) :: L.flatMap (fun a => p.2.map (fun w => a :: w)))
    (Primrec.const _) ?_
  show Primrec fun z : List ℕ × (ℕ × List (List ℕ)) =>
    ([] : List ℕ) :: z.1.flatMap (fun a => z.2.2.map (fun w => a :: w))
  refine Primrec.list_cons.comp (Primrec.const ([] : List ℕ)) ?_
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun v : (List ℕ × (ℕ × List (List ℕ))) × ℕ =>
    v.1.2.2.map (fun w => v.2 :: w)
  refine Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) ?_
  show Primrec fun u : ((List ℕ × (ℕ × List (List ℕ))) × ℕ) × List ℕ => u.1.2 :: u.2
  exact Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd

lemma primrec_wcodeAlphabet : Primrec wcodeAlphabet := by
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun z : WCode × (ℕ × List ℕ × (ℤ × ℕ) × ℕ) => z.2.2.1
  exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

/-! ## The decision procedure -/

/-- The strings tested by the decision procedure: those of length at most the
Schützenberger bound over the letters occurring in one of the two codes. -/
def testWords (N : WCode → WCode → ℕ) (p : WCode × WCode) : List (List ℕ) :=
  wordsUpto (wcodeAlphabet p.1 ++ wcodeAlphabet p.2) (N p.1 p.2)

/-- The decision procedure for Theorem `thm:equivalence-weighted-automata`, built from an evaluation
test `D` and a Schützenberger bound `N`. -/
def wEqB (D : WCode × WCode × List ℕ → Bool) (N : WCode → WCode → ℕ) (p : WCode × WCode) : Bool :=
  allIdx (testWords N p) (fun v => D (p.1, p.2, v)) (testWords N p).length

lemma wEqB_iff {D : WCode × WCode × List ℕ → Bool} {N : WCode → WCode → ℕ}
    (hD : ∀ c₁ c₂ (v : List ℕ), WCodeValid c₁ → WCodeValid c₂ →
      (D (c₁, c₂, v) = true ↔ wcodeEval c₁ v = wcodeEval c₂ v))
    (hN : ∀ c₁ c₂, WCodeValid c₁ → WCodeValid c₂ →
      ((∀ v : List ℕ, v.length ≤ N c₁ c₂ → wcodeEval c₁ v = wcodeEval c₂ v) →
        wcodeEval c₁ = wcodeEval c₂))
    (p : WCode × WCode) (h₁ : WCodeValid p.1) (h₂ : WCodeValid p.2) :
    wEqB D N p = true ↔ wcodeEval p.1 = wcodeEval p.2 := by
  rw [wEqB, allIdx_iff]
  constructor
  · intro h
    refine hN p.1 p.2 h₁ h₂ ?_
    intro v hv
    by_cases hall : ∀ x ∈ v, x ∈ wcodeAlphabet p.1 ++ wcodeAlphabet p.2
    · have hmem : v ∈ testWords N p := (mem_wordsUpto _ _ _).2 ⟨hv, hall⟩
      exact (hD p.1 p.2 v h₁ h₂).1 (h v hmem)
    · push_neg at hall
      obtain ⟨x, hxv, hx⟩ := hall
      rw [List.mem_append] at hx
      push_neg at hx
      rw [wcodeEval_eq_zero_of_foreign hxv hx.1, wcodeEval_eq_zero_of_foreign hxv hx.2]
  · intro h v _
    exact (hD p.1 p.2 v h₁ h₂).2 (by rw [h])

lemma computable_wEqB {D : WCode × WCode × List ℕ → Bool} {N : WCode → WCode → ℕ}
    (hD : Computable D) (hN : Computable₂ N) : Computable (wEqB D N) := by
  have hwords : Computable (testWords N) := by
    have h1 : Primrec (fun p : WCode × WCode => wcodeAlphabet p.1 ++ wcodeAlphabet p.2) :=
      Primrec.list_append.comp (primrec_wcodeAlphabet.comp Primrec.fst)
        (primrec_wcodeAlphabet.comp Primrec.snd)
    exact primrec_wordsUpto.to_comp.comp h1.to_comp (hN.comp Computable.fst Computable.snd)
  have hD' : Computable₂ (fun (p : WCode × WCode) (v : List ℕ) => D (p.1, p.2, v)) :=
    hD.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
  exact computable_allIdx hwords hD' (Computable.list_length.comp hwords)

end WDec

/-- **Theorem `thm:equivalence-weighted-automata`** from the effectivity hypotheses.  Given two
weighted automata over the field of rationals, it is decidable whether they compute the same
function. -/
theorem weighted_equivalence_decidable_aux :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2) := by
  obtain ⟨D, hDcomp, hD⟩ := EffectiveWeightedEvalEq
  obtain ⟨N, hNcomp, hN⟩ := effectiveWeightedBound
  exact ⟨WDec.wEqB D N, WDec.computable_wEqB hDcomp hNcomp,
    fun p hp => WDec.wEqB_iff hD hN p hp.1 hp.2⟩

/-- **Theorem `thm:zeroness-weighted-automata`** from the effectivity hypotheses.  The zeroness
problem is decidable for weighted automata over the field of rationals; it is the special case of
Theorem `thm:equivalence-weighted-automata` in which the second automaton is the empty one. -/
theorem weighted_zeroness_decidable_aux :
    DecidableUnderPromise WCodeValid (fun c => wcodeEval c = 0) := by
  obtain ⟨D, hDcomp, hD⟩ := weighted_equivalence_decidable_aux
  refine ⟨fun c => D (c, zeroWCode), hDcomp.comp (Computable.pair Computable.id
    (Computable.const zeroWCode)), fun c hc => ?_⟩
  rw [hD (c, zeroWCode) ⟨hc, wCodeValid_zeroWCode⟩]
  simp [wcodeEval_zeroWCode]

end Lax132576Proofs.Transducers
