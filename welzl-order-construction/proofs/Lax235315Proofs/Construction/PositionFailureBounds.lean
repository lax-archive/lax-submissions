import Lax235315Proofs.Construction.GraphSampling
import Lax235315Proofs.Construction.ScanSampleTransport
import Lax235315Proofs.Construction.RationalFailureBounds
import Mathlib.Tactic

/-! The graph's bad-sample fraction also bounds the bad event on positions
in the literal increasing scan of active vertices. -/

namespace Lax235315Proofs.Construction.PositionFailureBounds

open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.ScanIndexEquiv
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.RationalFailureBounds
open Lax235315Proofs.Construction.KeyFailureBounds
open Lax235315Proofs.Construction.FiniteRandomKeys

noncomputable section

lemma familyBadSamples_subset_samples {α ι : Type*}
    [DecidableEq α] [DecidableEq ι] (R : Finset ι) (F : ι → Finset α)
    (A : Finset α) (c L : ℕ) :
    familyBadSamples R F A c L ⊆ samples A (sampleSize A.card c) := by
  intro W hW
  obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hW
  dsimp [pairBadSamples] at hp
  split_ifs at hp with hlarge
  · exact (Finset.mem_filter.mp hp).1
  · simp at hp

lemma activeFinset_card_eq_activeVertices (active : ℕ → ℕ) (n : ℕ) :
    (activeFinset (n := n) active).card = (activeVertices n active).card := by
  calc
    (activeFinset (n := n) active).card =
        (Finset.univ.map (scanVertex active n)).card := by
          rw [scanVertex_range]
    _ = (Finset.univ : Finset (Fin (activeVertices n active).card)).card := by
          simp
    _ = (activeVertices n active).card := by simp

/-- The bad event for actual scan positions has at most the paper's
`c²/n` fraction of the uniformly chosen position samples. -/
lemma bad_position_fraction_le {n c L : ℕ} {G : SimpleGraph (Fin n)}
    (activeA activeB : ℕ → ℕ)
    (hc : 1 ≤ c)
    (hA : (activeFinset (n := n) activeA).Nonempty)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hNpow : n ≤ 2 ^ L) :
    let A := activeFinset (n := n) activeA
    let B := activeFinset (n := n) activeB
    let bad := familyBadSamples (traceFamily G A B) id A c L
    let s := sampleSize A.card c
    ((badPositionSamples activeA n bad).card : ℝ) /
        (samples (Finset.univ : Finset (Fin (activeVertices n activeA).card)) s).card ≤
      (c : ℝ) ^ 2 / n := by
  dsimp
  let A := activeFinset (n := n) activeA
  let B := activeFinset (n := n) activeB
  let bad := familyBadSamples (traceFamily G A B) id A c L
  let s := sampleSize A.card c
  have hbadcard : (badPositionSamples activeA n bad).card ≤ bad.card :=
    card_badPositionSamples_le activeA n bad
  have hsamplecard :
      (samples (Finset.univ : Finset (Fin (activeVertices n activeA).card)) s).card =
        (samples A s).card := by
    rw [card_samples, card_samples]
    simp [activeFinset_card_eq_activeVertices activeA n, A]
  have hgraph : ((bad.card : ℝ) / (samples A s).card) ≤ (c : ℝ) ^ 2 / n := by
    exact graph_bad_fraction_le G hc hA hG
      (by simpa using Finset.card_le_univ A) hNpow
  rw [hsamplecard]
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hbadcard) (by positivity)).trans hgraph

/-- A fresh assignment of the eight-digit keys has the paper's rational
one-round failure bound, using the actual active scan as its index type. -/
lemma position_assignment_failure_le {n c L : ℕ} {G : SimpleGraph (Fin n)}
    (activeA activeB : ℕ → ℕ) (hc : 1 ≤ c)
    (hA : (activeFinset (n := n) activeA).Nonempty)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hNpow : n ≤ 2 ^ L) :
    let A := activeFinset (n := n) activeA
    let B := activeFinset (n := n) activeB
    let bad := familyBadSamples (traceFamily G A B) id A c L
    let positions := Fin (activeVertices n activeA).card
    let badPositions := badPositionSamples activeA n bad
    let s := sampleSize A.card c
    ((failingAssignments ((2 ^ L) ^ 8) s badPositions).card : ℚ) /
        (allAssignments positions ((2 ^ L) ^ 8)).card ≤
      1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n := by
  dsimp
  let A := activeFinset (n := n) activeA
  let B := activeFinset (n := n) activeB
  let bad := familyBadSamples (traceFamily G A B) id A c L
  let s := sampleSize A.card c
  have ha : 0 < (activeVertices n activeA).card := by
    rw [← activeFinset_card_eq_activeVertices activeA n]
    exact Finset.card_pos.mpr hA
  have hn : 0 < n := lt_of_lt_of_le ha (activeVertices_card_le n activeA)
  have hbad : bad ⊆ samples A s :=
    familyBadSamples_subset_samples (traceFamily G A B) id A c L
  have hbadPositions : badPositionSamples activeA n bad ⊆
      samples (Finset.univ : Finset (Fin (activeVertices n activeA).card)) s := by
    exact badPositionSamples_subset_samples activeA n s bad hbad
  have hs : s ≤ Fintype.card (Fin (activeVertices n activeA).card) := by
    have hsA : s ≤ A.card := sampleSize_le_self hc (Finset.card_pos.mpr hA)
    simpa [A, activeFinset_card_eq_activeVertices activeA n] using hsA
  have hfrac := bad_position_fraction_le activeA activeB hc hA hG hNpow
  exact failingAssignments_fraction_le_paper_rat hn
    (by simpa using activeVertices_card_le n activeA) hNpow hs hbadPositions
    (by simpa [A, B, bad, s] using hfrac)

end

end Lax235315Proofs.Construction.PositionFailureBounds
