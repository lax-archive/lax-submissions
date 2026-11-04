import Lax185574Proofs.MC.Bounds.Rounds

/-!
The time bounds of the callees along a construction sequence.

`realT_le`: along a construction sequence of width at most `K`, the time
bound `realT` of the callee of every call is at most `realB`, which is
polynomial in the tree bound `T = treeMax`, in `n` and in `K`. The size
of a partial graph on `n` vertices is at most `n + n ^ 2`, its largest
tree is at most `T`, and the parameter of the resolve lift is at most
`(q + 1) (1 + q) K` by `treeCount_le_count`.
-/

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.TypeTrees Lax185574.PartialGraphEncoding
open Lax185574.ResolveLift Lax185574.Width Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus rhoPlus)

theorem size_le {n : ℕ} (G : PartialGraph (Fin n)) : G.size ≤ n + n ^ 2 := by
  classical
  unfold PartialGraph.size
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.resolved)
  rw [Fintype.card_fin, Nat.choose_two_right] at h1
  have h2 : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
  have h3 : n * (n - 1) ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

theorem maxTreeSize_le {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) {t : ℕ}
    (ht : t < s.length) : maxTreeSize (sAt s t) 1 q ≤ treeMax s q :=
  Finset.sup_le fun a _ => tree_le_treeMax s q ht a

theorem sAt_eq {n : ℕ} {s : List (PartialGraph (Fin n))} {t : ℕ} (ht : t < s.length) :
    sAt s t = s[t] := by
  simp [sAt, List.getD_eq_getElem?_getD, ht]

/-- The bound of the time bounds of the callees. -/
noncomputable def realB (n T q K : ℕ) (φ : Lax3.FirstOrder.FO 0) (k : CCst) : ℕ :=
  k.cM * (n + 1) ^ 2 * (T + 3) ^ k.aM + k.cE * (T + (toWord (loc q φ)).length + 1) ^ k.aE +
    k.cR * (n + 1) ^ 2 * (T + (q + 1) * (1 + q) * K + 1) ^ k.aR

open Lax185574Proofs.Words.Fast (maxLen maxLen_le) in
/-- The longest job of a merge step. -/
theorem maxLen_mjobs_le {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) {t : ℕ}
    (ht : t < s.length) (P Q : ℕ) : maxLen (mjobs (sAt s t) q P Q) ≤ treeMax s q + 2 := by
  refine maxLen_le fun u hu => ?_
  simp only [mjobs, List.mem_ofFn] at hu
  obtain ⟨a, rfl⟩ := hu
  have h1 := tree_le_treeMax s q ht a
  have e : (toWord (tree (sAt s t) 1 q ![a], P, Q)).length =
      wordLength (tree (sAt s t) 1 q ![a]) + 2 := by simp [wordLength, word_simps]
  omega

/-- **Time bounds of the callees.** -/
theorem realT_le {n : ℕ} (σ : Script n) (q : ℕ) {K : ℕ}
    (hK : width (rhoPlus 1 q) (rhoPlus 1 q + 1 + q) σ.run ≤ K) (φ : Lax3.FirstOrder.FO 0)
    (k : CCst) {c : PCall n} (hc : c ∈ pcalls n σ.steps) :
    realT σ.run q φ k c ≤ realB n (treeMax σ.run q) q K φ k := by
  set s := σ.run
  set T := treeMax s q
  have hl : s.length = σ.steps.length + 1 := by simp [s, Script.run]
  have hfrom := fromStep_pcalls hc
  unfold realB
  cases c with
  | merge t P Q =>
    simp only [FromStep] at hfrom
    have ht : t < σ.steps.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hfrom; simp at hfrom
    by_cases hpq : P = Q
    · simp only [realT, hpq, if_true]; omega
    · simp only [realT, hpq, if_false]
      have h1 := maxLen_mjobs_le s q (t := t) (by omega) P Q
      have : k.cM * (n + 1) ^ 2 * (Lax185574Proofs.Words.Fast.maxLen (mjobs (sAt s t) q P Q) + 1) ^ k.aM ≤
          k.cM * (n + 1) ^ 2 * (T + 3) ^ k.aM :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      omega
  | resolve t sg P Q =>
    simp only [FromStep] at hfrom
    have ht : t < σ.steps.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hfrom; simp at hfrom
    have hrs : resolveBy (sAt s t) sg P Q = sAt s (t + 1) := by
      rw [sAt_run_succ σ ht]
      rw [List.getElem?_eq_getElem ht] at hfrom
      simp only [Option.some.injEq] at hfrom
      rw [hfrom]; cases sg <;> rfl
    simp only [realT, hrs]
    have h2 := maxTreeSize_le s q (t := t) (by omega)
    have hw : ∀ a : Fin n, partialTypeCount s[t] (rhoPlus 1 q + 1 + q) (rhoPlus 1 q + 1 + q)
        (s[t + 1].ball (rhoPlus 1 q) a) ≤ K :=
      fun a => le_trans (le_width _ _ s (by omega) a) hK
    have h3 := treeCount_le_count s[t] s[t + 1] 1 q le_rfl K hw
    rw [← sAt_eq (by omega), ← sAt_eq (by omega)] at h3
    have : k.cR * (n + 1) ^ 2 *
        (maxTreeSize (sAt s t) 1 q + treeCount (sAt s t) (sAt s (t + 1)) 1 q + 1) ^ k.aR ≤
        k.cR * (n + 1) ^ 2 * (T + (q + 1) * (1 + q) * K + 1) ^ k.aR := by
      gcongr
    omega
  | eval a =>
    simp only [realT, callQE]
    have h1 := tree_le_treeMax s q (t := s.length - 1) (by omega) a
    have e : (toWord (tree (sAt s (s.length - 1)) 1 q ![a], loc q φ)).length =
        wordLength (tree (sAt s (s.length - 1)) 1 q ![a]) + (toWord (loc q φ)).length := by
      simp [wordLength, word_simps]; omega
    rw [e]
    have : k.cE * (wordLength (tree (sAt s (s.length - 1)) 1 q ![a]) +
        (toWord (loc q φ)).length + 1) ^ k.aE ≤
        k.cE * (T + (toWord (loc q φ)).length + 1) ^ k.aE :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega

end Lax185574Proofs.MC
