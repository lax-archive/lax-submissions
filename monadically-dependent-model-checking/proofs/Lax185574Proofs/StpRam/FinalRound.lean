import Lax185574Proofs.StpRam.FinalRead

/-!
The final round of the glue program of lem:compute-stp: from its input
after the tag and the length of the state, to `0` followed by the word
of the scatter type. The blocked vertices of the greedy scans are read
off the distance matrix: an entry `d` of the word of `D_G` is positive and
at most `r + 1` exactly if the vertices are within distance `r`
(`dT_iff`).
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.PartialGraphs
open Lax185574.TypeTrees Lax185574.ScatterTypes Lax185574.DistanceMatrix
open Lax185574Proofs.DistMatrix Lax185574Proofs.TreeAlgo

def finalRound : Com := .seq finalRead finalCompute

theorem aFacts_answers {n : ℕ} (G : PartialGraph (Fin n)) (k q L : ℕ)
    (hL : ∀ u ∈ answers G k q, u.length ≤ L) : AFacts (answers G k q) n k q L := by
  refine ⟨by simp [answers], fun u hu => ?_, fun u hu => ?_, hL⟩
  · obtain ⟨i, hi1, hiq, v, rfl⟩ := (mem_answers k q).mp hu
    rw [headD_toWord, tree_k]; omega
  · obtain ⟨i, hi1, hiq, v, rfl⟩ := (mem_answers k q).mp hu
    simp [word_simps]

/-- The array of the codes of the entries of `D_G`. -/
noncomputable def dmG {n : ℕ} (G : PartialGraph (Fin n)) : ℕ → ℕ :=
  dmArr n fun u v => dcode (distMatrix G u v)

/-- **The test of the greedy scan is the ball test.** -/
theorem dT_iff {n : ℕ} (G : PartialGraph (Fin n)) (s v : Fin n) (r : ℕ) :
    DT (dmG G) n s v r ↔ v ∈ ballFrom (adjOf G) s r := by
  unfold DT dmG
  rw [dmArr_apply, dcode_test, distMatrix_le_iff, mem_ballFrom (fun u v => mem_adjOf_resolved G u v)]

theorem dmG_le {n : ℕ} (G : PartialGraph (Fin n)) (j : ℕ) : dmG G j ≤ n := by
  unfold dmG dmArr
  split_ifs
  · exact dcode_distMatrix_le G _ _
  · exact Nat.zero_le _

set_option maxHeartbeats 1000000 in
/-- **The final round.** -/
theorem finalRound_run {B n k q : ℕ} (G : PartialGraph (Fin n)) {hd rest : List ℕ}
    {Fs : List (List ℕ)} (hhd : hd.length = 6) {L : ℕ} (hFL : ∀ u ∈ Fs, u.length ≤ L)
    (hAL : ∀ u ∈ answers G k q, u.length ≤ L) (hq : 1 ≤ q) {σ : Env}
    (hinp : σ.inp = (toWord G ++ [k, q]) ++ toWord (distMatrix G) ++ hd ++ toWord Fs ++
      toWord (answers G k q) ++ rest)
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = offL G.nonEdge n)
    (ha : total (answers G k q) ≤ (σ.arrs "a").length)
    (hst : (answers G k q).length ≤ (σ.arrs "st").length)
    (hln : (answers G k q).length ≤ (σ.arrs "ln").length)
    (hrt : (σ.arrs "rt").length = q + 1) (hord : (answers G k q).length ≤ (σ.arrs "ord").length)
    (hdd : (σ.arrs "dd").length = n * n) (hdn : (σ.arrs "dn").length = n)
    (hbl : (σ.arrs "bl").length = n)
    (hb : WordsBound B (answers G k q)) (hnB : n + 2 < B) (hnnB : n * n < B)
    (hEB : offL G.edge n + 1 < B)
    (hNB : offL G.nonEdge n + 1 < B) (hFB : Fs.length < B) (hLB : L < B)
    (hAB : (toWord (answers G k q)).length < B) (hAv : ∀ v ∈ toWord (answers G k q), v < B)
    (hRB : radius k q 0 + 1 < B) (h9B : 9 < B)
    (hTB : radius k q 1 * (answers G k q).length + 1 < B) (htB : total (answers G k q) + 3 < B) :
    ∃ σ', Run B finalRound σ σ'
        (readCost n L Fs.length (toWord (answers G k q)).length +
          finalCost n k q L (answers G k q).length (radius k q 1)) ∧
      σ'.out = σ.out ++ 0 :: toWord (stp G k q) := by
  obtain ⟨σ1, r1, hG1, hw1, hk1, hq1, hm1, ho1, hdd1, ha1⟩ := finalRead_run (B := B) G
    (fun u v => dcode (distMatrix G u v)) hhd hFL (by rw [hinp, toWord_distMatrix]) hdd hnnB
    (fun u v => by have := dcode_distMatrix_le G u v; omega) heo het
    hno hnt ha hst hln (by omega) hEB hNB hFB hLB hAB hAv (by omega)
  obtain ⟨σ2, r2, ho2⟩ := finalCompute_run (adj := adjOf G) (g := dmG G)
    (dT_iff G) (aFacts_answers G k q L hAL) hb hq hnB hnnB
    (fun j _ => by have := dmG_le G j; omega) hRB h9B
    hTB htB hG1 hw1 hk1 hq1 hm1 (by rw [ha1 _ (by decide), hrt]) (by rw [ha1 _ (by decide)]; exact hord)
    hdd1 (by rw [ha1 _ (by decide), hdn]) (by rw [ha1 _ (by decide), hbl])
  refine ⟨σ2, Run.seq r1 r2, ?_⟩
  rw [ho2, ho1, toWord_stp (fun u v => mem_adjOf_resolved G u v)]

end Lax185574Proofs.StpRam
