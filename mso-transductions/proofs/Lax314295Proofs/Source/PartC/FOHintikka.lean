/-
The right-to-left implication of Lemma `lem:k-types-fo-equivalence` of *Transducers*
(M. Bojańczyk): strings that satisfy the same first-order sentences of
quantifier rank at most `k` have the same `k`-type.

It is proved in the contrapositive form `exists_fo_sentence_of_tp_ne`: if two
strings have different `k`-types then a first-order sentence of quantifier rank
at most `k` distinguishes them.  This is the book's argument: for `k = 0` there
is nothing to prove, and at the step `k + 1` one takes a split
`w = w₁ a w₂` whose triple of the `k`-types of `w₁`, of `a` and of `w₂` is not
realised in `v`, and writes the sentence

  `∃x (a(x) ∧ ⋀_{j < |v|} δ_j (x))`,

in which the conjunct `δ_j` rules out the `j`-th position of `v`: either its
letter is not `a`, or, by the induction assumption, a sentence of quantifier
rank at most `k` distinguishes `w₁` from the prefix of `v` before `j`, or one
distinguishes `w₂` from the suffix of `v` after `j`.  The sentences of the
induction assumption are relativised to the positions `< x` and `> x`
(`RequestProject/PartC/FORel.lean`), which does not change the quantifier rank.
-/
import Lax314295Proofs.Source.PartC.FORename
import Lax916827Proofs.Source.PartC.KTypes
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

open MSO

variable {A : Type}

/-- If two strings have different `k`-types then some first-order sentence of
quantifier rank at most `k` distinguishes them. -/
theorem exists_fo_sentence_of_tp_ne : ∀ (k : ℕ) (w v : List A), tp k w ≠ tp k v →
    ∃ φ : MSO A, φ.IsFO ∧ φ.freeFO = ∅ ∧ φ.qrank ≤ k ∧
      ¬ (MSO.Sat w (fun _ => 0) (fun _ => ∅) φ ↔ MSO.Sat v (fun _ => 0) (fun _ => ∅) φ) := by
  intro k
  induction k with
  | zero => intro w v h; exact absurd rfl h
  | succ k ih =>
      -- a one-sided form of the induction assumption
      have hone : ∀ (x y : List A), tp k x ≠ tp k y →
          ∃ χ : MSO A, χ.IsFO ∧ χ.freeFO = ∅ ∧ χ.qrank ≤ k ∧
            Sat x (fun _ => 0) (fun _ => ∅) χ ∧ ¬ Sat y (fun _ => 0) (fun _ => ∅) χ := by
        intro x y hxy
        obtain ⟨χ, h1, h2, h3, h4⟩ := ih x y hxy
        by_cases hx : Sat x (fun _ => 0) (fun _ => ∅) χ
        · exact ⟨χ, h1, h2, h3, hx, fun hy => h4 ⟨fun _ => hy, fun _ => hx⟩⟩
        · have hy : Sat y (fun _ => 0) (fun _ => ∅) χ := by
            by_contra hy
            exact h4 ⟨fun h => absurd h hx, fun h => absurd h hy⟩
          exact ⟨MSO.not χ, h1, h2, h3, hx, fun hn => hn hy⟩
      -- the one-sided statement at level `k + 1`
      have hsub : ∀ (w v : List A), ¬ (tpSet k w ⊆ tpSet k v) →
          ∃ φ : MSO A, φ.IsFO ∧ φ.freeFO = ∅ ∧ φ.qrank ≤ k + 1 ∧
            Sat w (fun _ => 0) (fun _ => ∅) φ ∧ ¬ Sat v (fun _ => 0) (fun _ => ∅) φ := by
        intro w v hns
        obtain ⟨t, htw, htv⟩ := Set.not_subset.mp hns
        obtain ⟨w₁, a, w₂, hw, rfl⟩ := (mem_tpSet k w t).mp htw
        -- the conjunct ruling out the `j`-th position of `v`
        have hδ : ∀ j : ℕ, ∃ d : MSO A, d.IsFO ∧ d.freeFO ⊆ {0} ∧ d.qrank ≤ k ∧
            Sat w (fun _ => w₁.length) (fun _ => ∅) d ∧
            (v[j]? = some a → ¬ Sat v (fun _ => j) (fun _ => ∅) d) := by
          intro j
          by_cases hja : v[j]? = some a
          · obtain ⟨hjlt, hjv⟩ := List.getElem?_eq_some_iff.mp hja
            have hvsplit : v = v.take j ++ a :: v.drop (j + 1) := by
              conv_lhs => rw [← List.take_append_drop j v]
              rw [List.drop_eq_getElem_cons hjlt, hjv]
            have hmem : (tp k (v.take j), a, tp k (v.drop (j + 1))) ∈ tpSet k v := by
              exact ⟨v.take j, a, v.drop (j + 1), hvsplit, rfl⟩
            have hne : ¬ (tp k (v.take j) = tp k w₁ ∧ tp k (v.drop (j + 1)) = tp k w₂) := by
              rintro ⟨e1, e2⟩
              rw [e1, e2] at hmem
              exact htv hmem
            by_cases h1 : tp k (v.take j) = tp k w₁
            · -- the suffixes differ
              have h2 : tp k w₂ ≠ tp k (v.drop (j + 1)) := fun h => hne ⟨h1, h.symm⟩
              obtain ⟨χ, hχfo, hχfree, hχq, hχw, hχv⟩ := hone w₂ (v.drop (j + 1)) h2
              have hψfo : (shiftUp 1 χ).IsFO := isFO_shiftUp 1 hχfo
              have hψfree : (shiftUp 1 χ).freeFO = ∅ := freeFO_shiftUp_eq_empty 1 hχfree
              have hψvars : (0 : ℕ) ∉ (shiftUp 1 χ).foVars := zero_notMem_foVars_shiftUp 0 χ
              have hcond : ∀ (fo : ℕ → ℕ), ∀ i ∈ (shiftUp 1 χ).freeFO, fo 0 < fo i := by
                intro fo i hi
                rw [hψfree] at hi
                exact hi.elim
              refine ⟨relGt 0 (shiftUp 1 χ), isFO_relGt 0 hψfo, ?_, ?_, ?_, ?_⟩
              · refine subset_trans (freeFO_relGt 0 _) ?_
                rw [hψfree]
                simp
              · rw [qrank_relGt, qrank_shiftUp]; exact hχq
              · rw [sat_relGt w 0 _ hψfo hψvars _ _ (hcond _)]
                have hdrop : w.drop (w₁.length + 1) = w₂ := by rw [hw]; simp
                rw [hdrop]
                exact (sat_shiftUp_sentence hχfo hχfree 1 w₂ _ _ _ _).mpr hχw
              · intro _
                rw [sat_relGt v 0 _ hψfo hψvars _ _ (hcond _)]
                intro hcontra
                exact hχv ((sat_shiftUp_sentence hχfo hχfree 1 _ _ _ _ _).mp hcontra)
            · -- the prefixes differ
              obtain ⟨χ, hχfo, hχfree, hχq, hχw, hχv⟩ := hone w₁ (v.take j) (Ne.symm h1)
              have hψfo : (shiftUp 1 χ).IsFO := isFO_shiftUp 1 hχfo
              have hψfree : (shiftUp 1 χ).freeFO = ∅ := freeFO_shiftUp_eq_empty 1 hχfree
              have hψvars : (0 : ℕ) ∉ (shiftUp 1 χ).foVars := zero_notMem_foVars_shiftUp 0 χ
              have hcond : ∀ (fo : ℕ → ℕ), ∀ i ∈ (shiftUp 1 χ).freeFO, fo i < fo 0 := by
                intro fo i hi
                rw [hψfree] at hi
                exact hi.elim
              refine ⟨relLt 0 (shiftUp 1 χ), isFO_relLt 0 hψfo, ?_, ?_, ?_, ?_⟩
              · refine subset_trans (freeFO_relLt 0 _) ?_
                rw [hψfree]
                simp
              · rw [qrank_relLt, qrank_shiftUp]; exact hχq
              · rw [sat_relLt w 0 _ hψfo hψvars _ _ (hcond _)]
                have htake : w.take w₁.length = w₁ := by rw [hw]; simp
                rw [htake]
                exact (sat_shiftUp_sentence hχfo hχfree 1 w₁ _ _ _ _).mpr hχw
              · intro _
                rw [sat_relLt v 0 _ hψfo hψvars _ _ (hcond _)]
                intro hcontra
                exact hχv ((sat_shiftUp_sentence hχfo hχfree 1 _ _ _ _ _).mp hcontra)
          · exact ⟨tt, trivial, by intro x hx; rcases hx with rfl | rfl <;> rfl,
              Nat.zero_le k, sat_tt _ _ _, fun h => absurd h hja⟩
        choose d hdFO hdfree hdq hdw hdv using hδ
        -- the distinguishing sentence
        refine ⟨MSO.exFO 0 (MSO.and (MSO.lab a 0) (bigAnd ((List.range v.length).map d))),
          ⟨trivial, isFO_bigAnd _ ?_⟩, ?_, ?_, ?_, ?_⟩
        · intro φ hφ
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hφ
          exact hdFO j
        · -- the sentence has no free variables
          have hbody : (MSO.and (MSO.lab a 0) (bigAnd ((List.range v.length).map d))).freeFO
              ⊆ ({0} : Set ℕ) := by
            intro x hx
            rcases hx with hx | hx
            · exact hx
            · refine freeFO_bigAnd_subset (S := ({0} : Set ℕ)) rfl _ ?_ hx
              intro φ hφ
              obtain ⟨j, _, rfl⟩ := List.mem_map.mp hφ
              exact hdfree j
          refine Set.eq_empty_of_subset_empty ?_
          rintro x ⟨hx1, hx2⟩
          exact hx2 (hbody hx1)
        · -- the quantifier rank
          have : (bigAnd ((List.range v.length).map d)).qrank ≤ k := by
            refine qrank_bigAnd_le _ k ?_
            intro φ hφ
            obtain ⟨j, _, rfl⟩ := List.mem_map.mp hφ
            exact hdq j
          exact Nat.succ_le_succ (by simpa [qrank] using this)
        · -- the sentence holds in `w`
          refine ⟨w₁.length, by rw [hw]; simp, ?_, ?_⟩
          · show w[Function.update (fun _ => 0) 0 w₁.length 0]? = some a
            rw [Function.update_self, hw]
            simp
          · refine (sat_bigAnd _ _ _ _).mpr ?_
            intro φ hφ
            obtain ⟨j, _, rfl⟩ := List.mem_map.mp hφ
            refine (MSO.sat_congr w (d j) _ _ _ _ ?_ ?_).mp (hdw j)
            · intro i hi
              rw [show i = 0 from hdfree j hi, Function.update_self]
            · intro i hi
              rw [freeSO_eq_empty_of_isFO _ (hdFO j)] at hi
        · -- the sentence fails in `v`
          rintro ⟨q, hq, hlab, hand⟩
          have hlab' : v[q]? = some a := by
            have : v[Function.update (fun _ => 0) 0 q 0]? = some a := hlab
            rwa [Function.update_self] at this
          refine hdv q hlab' ?_
          have hmem : d q ∈ (List.range v.length).map d :=
            List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
          have hsat := (sat_bigAnd _ _ _ _).mp hand (d q) hmem
          refine (MSO.sat_congr v (d q) _ _ _ _ ?_ ?_).mp hsat
          · intro i hi
            rw [show i = 0 from hdfree q hi, Function.update_self]
          · intro i hi
            rw [freeSO_eq_empty_of_isFO _ (hdFO q)] at hi
      -- both directions
      intro w v hne
      have hne' : tpSet k w ≠ tpSet k v := hne
      by_cases hs : tpSet k w ⊆ tpSet k v
      · have h : ¬ (tpSet k v ⊆ tpSet k w) := fun h => hne' (Set.Subset.antisymm hs h)
        obtain ⟨φ, h1, h2, h3, hv, hw⟩ := hsub v w h
        exact ⟨φ, h1, h2, h3, fun hiff => hw (hiff.mpr hv)⟩
      · obtain ⟨φ, h1, h2, h3, hw, hv⟩ := hsub w v hs
        exact ⟨φ, h1, h2, h3, fun hiff => hv (hiff.mp hw)⟩

/-- Strings that satisfy the same first-order sentences of quantifier rank at
most `k` have the same `k`-type. -/
theorem tp_eq_of_fo_equiv (k : ℕ) (w v : List A)
    (h : ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
      (MSO.Sat w (fun _ => 0) (fun _ => ∅) φ ↔ MSO.Sat v (fun _ => 0) (fun _ => ∅) φ)) :
    tp k w = tp k v := by
  by_contra hne
  obtain ⟨φ, hfo, hfree, hq, hdiff⟩ := exists_fo_sentence_of_tp_ne k w v hne
  exact hdiff (h φ hfo hfree hq)

end Lax314295Proofs.Transducers
