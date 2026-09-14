/- Theorem `thm:equivalence-rational-functions` of *Transducers* (M. Bojańczyk): the equivalence
problem is decidable for rational functions.

Following the book, equivalence of two rational functions is reduced to equivalence of two weighted
automata over `ℚ` (Theorem `thm:equivalence-weighted-automata`).  The reduction is the one of
`RequestProject/PartB/PairWeighted.lean`: after putting the two codes into the letter-atomic normal
form `normCode`, the product automaton `pairW K M N` computes, on a nonempty input `w`,

  `(number of accepting runs of M over w) * (number of accepting runs of N over w)
     * iota K (value of M on w)`,

where `iota K` is the injective numerical encoding of strings of
`RequestProject/PartB/Iota.lean`.  The symmetric product `pairW K N M` has the
same two counting factors in front, and both are nonzero as soon as `w` is in
the domain, so the two weighted automata are equivalent exactly when the two
coded functions agree on all nonempty strings of the common domain.

Two further checks make this an equivalence with `codeRel c₁ = codeRel c₂`:

* the two codes must read the same letters (`sameAlpha`) -- under the promise
  the domain of the relation described by a code is exactly the set of strings
  over its alphabet, so this is the statement that the two domains agree;
* the two coded functions must agree on the empty string (`CodeEps.epsOut`),
  which the product automaton cannot see, since it has no accepting run over the
  empty string.
-/
import Lax132576Proofs.Source.PartB.PairWeightedEval
import Lax132576Proofs.Source.PartB.PairPrimrec
import Lax132576Proofs.Source.PartB.CodeEps
import Lax132576Proofs.Source.PartB.WeightedDec
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace RatEq

open LabAut CodeMerge PairWeighted CodeEps Iota LenDec

/-! ## The base of the numerical encoding -/

/-- A base larger than every letter that the two normalised codes can write, so
that the encoding `iota` of `RequestProject/PartB/Iota.lean` is injective on
their outputs. -/
def kBound (c₁ c₂ : RelCode) : ℕ :=
  (codeOutAlphabet (normCode c₁) ++ codeOutAlphabet (normCode c₂)).foldr max 0 + 2

lemma lt_kBound_left {c₁ c₂ : RelCode} {w v : List ℕ} (h : codeRel (normCode c₁) w v) :
    ∀ x ∈ v, x + 1 < kBound c₁ c₂ := by
  intro x hx
  have hmem : x ∈ codeOutAlphabet (normCode c₁) := codeRel_output_mem h hx
  have : x ≤ (codeOutAlphabet (normCode c₁) ++ codeOutAlphabet (normCode c₂)).foldr max 0 :=
    le_foldr_max (List.mem_append_left _ hmem)
  simp only [kBound]
  omega

lemma lt_kBound_right {c₁ c₂ : RelCode} {w v : List ℕ} (h : codeRel (normCode c₂) w v) :
    ∀ x ∈ v, x + 1 < kBound c₁ c₂ := by
  intro x hx
  have hmem : x ∈ codeOutAlphabet (normCode c₂) := codeRel_output_mem h hx
  have : x ≤ (codeOutAlphabet (normCode c₁) ++ codeOutAlphabet (normCode c₂)).foldr max 0 :=
    le_foldr_max (List.mem_append_right _ hmem)
  simp only [kBound]
  omega

/-! ## The normal form under the promise -/

/-- Under the promise, the normal form describes the same relation as the code
on nonempty inputs. -/
lemma normCode_rel_iff {c : RelCode} (hc : CodeFunctional c) {w : List ℕ} (hw : w ≠ [])
    (v : List ℕ) : codeRel (normCode c) w v ↔ codeRel c w v := by
  constructor
  · exact fun h => normCode_sound c h
  · intro h
    obtain ⟨u, -, hu⟩ := hc w (codeRel_codeWord h)
    obtain ⟨x, hx⟩ := normCode_complete c h hw
    have hxv : x = v := by rw [hu _ (normCode_sound c hx), hu _ h]
    exact hxv ▸ hx

/-! ## The value of the product automaton under the promise -/

lemma eval_pair_eq (K : ℕ) {c₁ c₂ : RelCode} (h₁ : CodeFunctional c₁) {w v : List ℕ}
    (hw : w ≠ []) (hv : codeRel c₁ w v) :
    wcodeEval (pairW K (normCode c₁) (normCode c₂)) w
      = ((nAll (normCode c₁) w : ℚ) * (iota K v : ℚ)) * (nAll (normCode c₂) w : ℚ) := by
  obtain ⟨u, -, hu⟩ := h₁ w (codeRel_codeWord hv)
  have huniq : ∀ v', codeRel (normCode c₁) w v' → v' = v := by
    intro v' hv'
    rw [hu _ ((normCode_rel_iff h₁ hw v').1 hv'), hu _ hv]
  have hiAll : iAll K (normCode c₁) w = nAll (normCode c₁) w * iota K v :=
    iAll_eq_of_unique (normCode_letterAtomic c₁) huniq
  rw [pairW_eval K (normCode c₁) (normCode c₂) (normCode_letterAtomic c₁)
    (normCode_nodup c₁) (normCode_nodup c₂) (normCode_canonical c₁) (normCode_canonical c₂)
    (normCode_init_nodup c₁) (normCode_init_nodup c₂) hw, hiAll]
  push_cast
  ring

lemma eval_pair_zero_left (K : ℕ) {c₁ c₂ : RelCode} (h₁ : CodeFunctional c₁) {w : List ℕ}
    (hw : w ≠ []) (hv : ∀ v, ¬ codeRel c₁ w v) :
    wcodeEval (pairW K (normCode c₁) (normCode c₂)) w = 0 := by
  have hno : ∀ v, ¬ codeRel (normCode c₁) w v :=
    fun v h => hv v ((normCode_rel_iff h₁ hw v).1 h)
  rw [pairW_eval K (normCode c₁) (normCode c₂) (normCode_letterAtomic c₁)
    (normCode_nodup c₁) (normCode_nodup c₂) (normCode_canonical c₁) (normCode_canonical c₂)
    (normCode_init_nodup c₁) (normCode_init_nodup c₂) hw,
    iAll_eq_zero (normCode_letterAtomic c₁) hno]
  simp

lemma eval_pair_zero_right (K : ℕ) {c₁ c₂ : RelCode} (h₂ : CodeFunctional c₂) {w : List ℕ}
    (hw : w ≠ []) (hv : ∀ v, ¬ codeRel c₂ w v) :
    wcodeEval (pairW K (normCode c₁) (normCode c₂)) w = 0 := by
  have hno : ∀ v, ¬ codeRel (normCode c₂) w v :=
    fun v h => hv v ((normCode_rel_iff h₂ hw v).1 h)
  rw [pairW_eval K (normCode c₁) (normCode c₂) (normCode_letterAtomic c₁)
    (normCode_nodup c₁) (normCode_nodup c₂) (normCode_canonical c₁) (normCode_canonical c₂)
    (normCode_init_nodup c₁) (normCode_init_nodup c₂) hw,
    nAll_eq_zero (normCode_letterAtomic c₂) hno]
  simp

/-! ## Correctness of the reduction on a fixed nonempty string -/

lemma value_eq_iff {c₁ c₂ : RelCode} (h₁ : CodeFunctional c₁) (h₂ : CodeFunctional c₂)
    (hsame : ∀ x, x ∈ codeAlphabet c₁ ↔ x ∈ codeAlphabet c₂) {w : List ℕ} (hw : w ≠ []) :
    (wcodeEval (pairW (kBound c₁ c₂) (normCode c₁) (normCode c₂)) w
        = wcodeEval (pairW (kBound c₁ c₂) (normCode c₂) (normCode c₁)) w)
      ↔ ∀ v, codeRel c₁ w v ↔ codeRel c₂ w v := by
  set K := kBound c₁ c₂ with hK
  by_cases hword : CodeWord c₁ w
  · -- both codes have a value on `w`
    obtain ⟨v₁, hv₁, hu₁⟩ := h₁ w hword
    obtain ⟨v₂, hv₂, hu₂⟩ := h₂ w (fun x hx => (hsame x).1 (hword x hx))
    have hpos₁ : 0 < nAll (normCode c₁) w :=
      nAll_pos (normCode_letterAtomic c₁) ((normCode_rel_iff h₁ hw v₁).2 hv₁)
    have hpos₂ : 0 < nAll (normCode c₂) w :=
      nAll_pos (normCode_letterAtomic c₂) ((normCode_rel_iff h₂ hw v₂).2 hv₂)
    rw [eval_pair_eq K h₁ hw hv₁, eval_pair_eq K h₂ hw hv₂]
    constructor
    · intro heq
      have hiota : iota K v₁ = iota K v₂ := by
        have hne₁ : ((nAll (normCode c₁) w : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hpos₁.ne'
        have hne₂ : ((nAll (normCode c₂) w : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hpos₂.ne'
        have h' : ((nAll (normCode c₁) w : ℚ) * (nAll (normCode c₂) w : ℚ))
              * ((iota K v₁ : ℕ) : ℚ)
            = ((nAll (normCode c₁) w : ℚ) * (nAll (normCode c₂) w : ℚ))
              * ((iota K v₂ : ℕ) : ℚ) := by
          linear_combination heq
        exact Nat.cast_injective (mul_left_cancel₀ (mul_ne_zero hne₁ hne₂) h')
      have hv : v₁ = v₂ :=
        Iota.iota_inj (lt_kBound_left ((normCode_rel_iff h₁ hw v₁).2 hv₁))
          (lt_kBound_right ((normCode_rel_iff h₂ hw v₂).2 hv₂)) hiota
      intro v
      constructor
      · intro h; rw [hu₁ _ h, hv]; exact hv₂
      · intro h; rw [hu₂ _ h, ← hv]; exact hv₁
    · intro h
      have hv : v₁ = v₂ := hu₂ _ ((h v₁).1 hv₁)
      rw [hv]
      ring
  · -- `w` uses a letter that neither code can read
    obtain ⟨x, hxw, hx⟩ : ∃ x ∈ w, x ∉ codeAlphabet c₁ := by
      simpa [CodeWord, not_forall] using hword
    have hno₁ : ∀ v, ¬ codeRel c₁ w v := not_codeRel_of_foreign hxw hx
    have hno₂ : ∀ v, ¬ codeRel c₂ w v :=
      not_codeRel_of_foreign hxw (fun hc => hx ((hsame x).2 hc))
    rw [eval_pair_zero_left K h₁ hw hno₁, eval_pair_zero_left K h₂ hw hno₂]
    simp only [true_iff]
    intro v
    exact ⟨fun h => absurd h (hno₁ v), fun h => absurd h (hno₂ v)⟩

/-! ## The decision procedure -/

/-- The decision procedure for Theorem `thm:equivalence-rational-functions`, built from a decision
procedure `D` for equivalence of weighted automata over `ℚ` (Theorem
`thm:equivalence-weighted-automata`). -/
def ratEqB (D : WCode × WCode → Bool) (p : RelCode × RelCode) : Bool :=
  sameAlpha p.1 p.2 && decide (epsOut p.1 = epsOut p.2) &&
    D (pairW (kBound p.1 p.2) (normCode p.1) (normCode p.2),
      pairW (kBound p.1 p.2) (normCode p.2) (normCode p.1))

lemma ratEqB_iff {D : WCode × WCode → Bool}
    (hD : ∀ q : WCode × WCode, WCodeValid q.1 → WCodeValid q.2 →
      (D q = true ↔ wcodeEval q.1 = wcodeEval q.2))
    (p : RelCode × RelCode) (h₁ : CodeFunctional p.1) (h₂ : CodeFunctional p.2) :
    ratEqB D p = true ↔ codeRel p.1 = codeRel p.2 := by
  obtain ⟨c₁, c₂⟩ := p
  have hvalid₁ : WCodeValid (pairW (kBound c₁ c₂) (normCode c₁) (normCode c₂)) :=
    pairW_valid _ _ _ (normCode_letterAtomic c₁)
  have hvalid₂ : WCodeValid (pairW (kBound c₁ c₂) (normCode c₂) (normCode c₁)) :=
    pairW_valid _ _ _ (normCode_letterAtomic c₂)
  have hDq := hD (pairW (kBound c₁ c₂) (normCode c₁) (normCode c₂),
    pairW (kBound c₁ c₂) (normCode c₂) (normCode c₁)) hvalid₁ hvalid₂
  simp only [ratEqB, Bool.and_eq_true, decide_eq_true_eq, hDq, sameAlpha_iff]
  constructor
  · rintro ⟨⟨hsame, heps⟩, hval⟩
    funext w
    funext v
    by_cases hw : w = []
    · subst hw
      exact propext ((epsOut_eq_iff h₁ h₂).1 heps v)
    · exact propext ((value_eq_iff h₁ h₂ hsame hw).1 (congrFun hval w) v)
  · intro heq
    have hsame : ∀ x, x ∈ codeAlphabet c₁ ↔ x ∈ codeAlphabet c₂ := by
      have key : ∀ (d₁ d₂ : RelCode), CodeFunctional d₁ → codeRel d₁ = codeRel d₂ →
          ∀ x, x ∈ codeAlphabet d₁ → x ∈ codeAlphabet d₂ := by
        intro d₁ d₂ hd hrel x hx
        obtain ⟨v, hv, -⟩ := hd [x] (by
          intro y hy
          rcases List.mem_singleton.1 hy with rfl
          exact hx)
        have : codeRel d₂ [x] v := by rw [← hrel]; exact hv
        exact codeRel_codeWord this x (by simp)
      intro x
      exact ⟨fun hx => key c₁ c₂ h₁ heq x hx, fun hx => key c₂ c₁ h₂ heq.symm x hx⟩
    refine ⟨⟨hsame, (epsOut_eq_iff h₁ h₂).2 (fun v => by rw [heq])⟩, ?_⟩
    funext w
    by_cases hw : w = []
    · subst hw
      rw [pairW_eval_nil _ _ _ (normCode_letterAtomic c₁),
        pairW_eval_nil _ _ _ (normCode_letterAtomic c₂)]
    · exact (value_eq_iff h₁ h₂ hsame hw).2 (fun v => by rw [heq])

/-! ## Computability of the decision procedure -/

lemma primrec_kBound : Primrec (fun p : RelCode × RelCode => kBound p.1 p.2) := by
  have hn₁ : Primrec (fun p : RelCode × RelCode => normCode p.1) :=
    primrec_normCode.comp Primrec.fst
  have hn₂ : Primrec (fun p : RelCode × RelCode => normCode p.2) :=
    primrec_normCode.comp Primrec.snd
  have hl : Primrec (fun p : RelCode × RelCode =>
      codeOutAlphabet (normCode p.1) ++ codeOutAlphabet (normCode p.2)) :=
    Primrec.list_append.comp (primrec_codeOutAlphabet.comp hn₁)
      (primrec_codeOutAlphabet.comp hn₂)
  have hf : Primrec (fun p : RelCode × RelCode =>
      (codeOutAlphabet (normCode p.1) ++ codeOutAlphabet (normCode p.2)).foldr max 0) :=
    Primrec.list_foldr hl (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_add.comp hf (Primrec.const 2)).of_eq (fun _ => rfl)

lemma computable_ratEqB {D : WCode × WCode → Bool} (hD : Computable D) :
    Computable (ratEqB D) := by
  have hsame : Primrec (fun p : RelCode × RelCode => sameAlpha p.1 p.2) := primrec_sameAlpha
  have heps : Primrec (fun p : RelCode × RelCode => decide (epsOut p.1 = epsOut p.2)) :=
    primrec_decEq (primrec_epsOut.comp Primrec.fst) (primrec_epsOut.comp Primrec.snd)
  have hK : Primrec (fun p : RelCode × RelCode => kBound p.1 p.2) := primrec_kBound
  have hn₁ : Primrec (fun p : RelCode × RelCode => normCode p.1) :=
    primrec_normCode.comp Primrec.fst
  have hn₂ : Primrec (fun p : RelCode × RelCode => normCode p.2) :=
    primrec_normCode.comp Primrec.snd
  have hp₁ : Primrec (fun p : RelCode × RelCode =>
      pairW (kBound p.1 p.2) (normCode p.1) (normCode p.2)) :=
    (primrec_pairW.comp (Primrec.pair hK (Primrec.pair hn₁ hn₂))).of_eq (fun _ => rfl)
  have hp₂ : Primrec (fun p : RelCode × RelCode =>
      pairW (kBound p.1 p.2) (normCode p.2) (normCode p.1)) :=
    (primrec_pairW.comp (Primrec.pair hK (Primrec.pair hn₂ hn₁))).of_eq (fun _ => rfl)
  have hDc : Computable (fun p : RelCode × RelCode =>
      D (pairW (kBound p.1 p.2) (normCode p.1) (normCode p.2),
        pairW (kBound p.1 p.2) (normCode p.2) (normCode p.1))) :=
    hD.comp (Primrec.pair hp₁ hp₂).to_comp
  have hb : Computable (fun p : RelCode × RelCode =>
      sameAlpha p.1 p.2 && decide (epsOut p.1 = epsOut p.2)) :=
    (Primrec.and.comp hsame heps).to_comp
  refine (Computable.cond hb hDc (Computable.const false)).of_eq (fun p => ?_)
  cases h : (sameAlpha p.1 p.2 && decide (epsOut p.1 = epsOut p.2)) <;> simp [ratEqB, h]

end RatEq

/-- **Theorem `thm:equivalence-rational-functions`** from the effectivity hypotheses of
`RequestProject/PartB/Effective.lean`: the equivalence problem `f = g` is
decidable for rational functions. -/
theorem rationalFun_equivalence_decidable_aux :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => codeRel p.1 = codeRel p.2) := by
  obtain ⟨D, hDcomp, hD⟩ := weighted_equivalence_decidable_aux
  exact ⟨RatEq.ratEqB D, RatEq.computable_ratEqB hDcomp,
    fun p hp => RatEq.ratEqB_iff (fun q hq₁ hq₂ => hD q ⟨hq₁, hq₂⟩) p hp.1 hp.2⟩

end Lax132576Proofs.Transducers
