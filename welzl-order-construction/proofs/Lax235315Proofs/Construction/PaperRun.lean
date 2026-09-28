import Lax235315Proofs.Construction.Correctness
import Lax235315Proofs.Construction.Iterations
import Lax235315Proofs.Construction.TracePartitions

/-!
A successful execution certificate for Figure 1 of the paper.
-/

namespace Lax235315Proofs.Construction.PaperRun

open scoped symmDiff
open Lax195003.WelzlOrdersInGraphs
open Lax235315Proofs.Construction.Iterations
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- A run of the paper algorithm which passes every near-twin check. Besides
the reconstruction reduction, every step records the two trace partitions
and the prescribed sample size, exactly the data used in the size analysis. -/
inductive SuccessfulRun (c L : ℕ) :
    ℕ → Set (Fin n) → Set (Fin n) → List (Fin n) → Prop
  | base {A B : Set (Fin n)} {l : List (Fin n)}
      (enumerates : Enumerates A l)
      (small : A.ncard ≤ 12 * c ^ 2 * L) :
      SuccessfulRun c L 0 A B l
  | step {rounds : ℕ} {A B W A' B' : Set (Fin n)}
      {small big : List (Fin n)}
      (large : 12 * c ^ 2 * L < A.ncard)
      (B_nonempty : B.Nonempty)
      (sample_nonempty : W.Nonempty)
      (sample_subset : W ⊆ A)
      (sample_card : W.ncard = sampleSize A.ncard c)
      (B_partition : TracePartition G B W B')
      (A_partition : TracePartition G A B' A')
      (near : ∀ b ∈ B,
        ((G.neighborSet b ∩ A) ∆
          (G.neighborSet (B_partition.representative b) ∩ A)).ncard ≤
            6 * c ^ 2 * L)
      (reduction : Reduction G (6 * c ^ 2 * L)
        A B A' B' small big)
      (tail : SuccessfulRun c L rounds A' B' small) :
      SuccessfulRun c L (rounds + 1) A B big

lemma SuccessfulRun.toCertifiedRun {c L rounds : ℕ}
    {A B : Set (Fin n)} {l : List (Fin n)}
    (h : SuccessfulRun G c L rounds A B l) :
    CertifiedRun G (6 * c ^ 2 * L) (12 * c ^ 2 * L)
      rounds A B l := by
  induction h with
  | base henum hsmall => exact CertifiedRun.base henum hsmall
  | step _ _ _ _ _ _ _ _ reduction _ ih =>
      exact CertifiedRun.step reduction ih

lemma ShrinkingRun.prepend {d threshold first second rounds last : ℕ}
    (hone : threshold < first) (hshrink : second ≤ first / 2 + d)
    (h : ShrinkingRun d threshold second rounds last) :
    ShrinkingRun d threshold first (rounds + 1) last := by
  induction h with
  | base => exact ShrinkingRun.step ShrinkingRun.base hone hshrink
  | step previous large shrinks ih =>
      simpa [Nat.add_assoc] using ShrinkingRun.step ih large shrinks

/-- The active-side cardinalities of a successful run obey the recurrence
from Theorem 3.1. -/
lemma SuccessfulRun.toShrinkingRun {c L rounds : ℕ}
    {A B : Set (Fin n)} {l : List (Fin n)}
    (hc : 1 ≤ c)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant
      G c)
    (h : SuccessfulRun G c L rounds A B l) :
    ∃ finalCard,
      ShrinkingRun (c ^ 2) (12 * c ^ 2 * L)
        A.ncard rounds finalCard := by
  induction h with
  | base => exact ⟨_, ShrinkingRun.base⟩
  | @step rounds A B W A' B' small big large hBne hW hWsub hWcard hBp hAp
      near reduction tail ih =>
      obtain ⟨finalCard, htail⟩ := ih
      have hshrink : A'.ncard ≤ A.ncard / 2 + c ^ 2 :=
        partitions_ground_ncard_le_half_add G hc hG hBp hAp hW hBne hWcard
      exact ⟨finalCard, ShrinkingRun.prepend large hshrink htail⟩

/-- For `n>1`, a successful full graph run already satisfies the exact
output relation and crossing bound of the submitted theorem. -/
lemma SuccessfulRun.encodesGraphWelzlOrder {c rounds : ℕ}
    (hc : 1 ≤ c) (hn : 1 < n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant
      G c)
    {l : List (Fin n)}
    (h : SuccessfulRun G c (Nat.clog 2 n) rounds
      Set.univ Set.univ l) :
    EncodesGraphWelzlOrder G 1
      (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) (l.map Fin.val) := by
  obtain ⟨finalCard, hshrink⟩ := h.toShrinkingRun G hc hG
  have hshrink' : ShrinkingRun (c ^ 2)
      (12 * c ^ 2 * Nat.clog 2 n) n rounds finalCard := by
    simpa using hshrink
  have hrounds := hshrink'.rounds_succ_le_clog hc hn
  exact Lax235315Proofs.Construction.Correctness.certifiedRun_encodesGraphWelzlOrder_paperBound
    G l (h.toCertifiedRun G) hrounds

end

end Lax235315Proofs.Construction.PaperRun
