import Lax235315Proofs.Construction.PositionFailureBits
import Lax235315Proofs.Construction.ScanSampleTransport
import Mathlib.Tactic

/-! A bit block outside the counted failure event has distinct keys and a
sample outside the designated bad family. -/

namespace Lax235315Proofs.Construction.GoodRoundBits

open Lax235315Proofs.Construction.PositionFailureBits
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.KeyFailureBounds
open Lax235315Proofs.Construction.KeySamplingBounds
open Lax235315Proofs.Construction.KeySampling
open Lax235315Proofs.Construction.FiniteRandomKeys
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness

noncomputable section

lemma injective_of_not_mem_collisions {α : Type*} [Fintype α]
    [DecidableEq α] {M : ℕ} {f : α → Fin M}
    (h : f ∉ collisions α M) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  apply h
  apply Finset.mem_biUnion.mpr
  refine ⟨(x, y), ?_, ?_⟩
  · simp [hne]
  · simp [pairCollisions, allAssignments, hxy]

/-- The complement of the concrete bad-block event gives both properties
needed to execute an accepted round. -/
lemma good_assignment_of_not_badRoundBits (a L s : ℕ) (hL : 0 < L)
    (badSamples : Finset (Finset (Fin a)))
    (ρ : Fin ((a * 8) * L) → Bool)
    (hgood : ρ ∉ badRoundBits a L s hL badSamples) :
    ∃ f : KeyInjection (Fin a) ((2 ^ L) ^ 8),
      f.1 = roundAssignmentEquiv a L hL ρ ∧
      keySample f s ∉ badSamples := by
  have hbad : roundAssignmentEquiv a L hL ρ ∉
      failingAssignments ((2 ^ L) ^ 8) s badSamples := by
    simpa [badRoundBits] using hgood
  have hcollision : roundAssignmentEquiv a L hL ρ ∉
      collisions (Fin a) ((2 ^ L) ^ 8) := by
    intro hf
    exact hbad (Finset.mem_union_left _ hf)
  have hinj := injective_of_not_mem_collisions hcollision
  refine ⟨⟨roundAssignmentEquiv a L hL ρ, hinj⟩, rfl, ?_⟩
  intro hsample
  apply hbad
  apply Finset.mem_union_right
  unfold badInjectionAssignments
  apply Finset.mem_map.mpr
  refine ⟨(⟨roundAssignmentEquiv a L hL ρ, hinj⟩ :
    KeyInjection (Fin a) ((2 ^ L) ^ 8)), ?_, rfl⟩
  simp [badInjections, hsample]

/-- After relabeling positions by the literal active scan, a good bit block
has a fixed-size active graph sample outside the graph's bad family. -/
lemma good_graph_sample_of_not_badRoundBits
    {n L s : ℕ} (active : ℕ → ℕ) (hL : 0 < L)
    (bad : Finset (Finset (Fin n)))
    (ρ : Fin (((activeVertices n active).card * 8) * L) → Bool)
    (hs : s ≤ (activeVertices n active).card)
    (hgood : ρ ∉ badRoundBits (activeVertices n active).card L s hL
      (badPositionSamples active n bad)) :
    ∃ f : KeyInjection (Fin (activeVertices n active).card) ((2 ^ L) ^ 8),
      f.1 = roundAssignmentEquiv (activeVertices n active).card L hL ρ ∧
      let W := liftSample active n (keySample f s)
      W ⊆ activeFinset active ∧ W.card = s ∧ W ∉ bad := by
  obtain ⟨f, hf, hnotbad⟩ := good_assignment_of_not_badRoundBits
    (activeVertices n active).card L s hL (badPositionSamples active n bad) ρ hgood
  refine ⟨f, hf, liftSample_subset_active active n _, ?_, ?_⟩
  · rw [liftSample_card]
    exact card_keySample f (by simpa using hs)
  · simpa [badPositionSamples] using hnotbad

end

end Lax235315Proofs.Construction.GoodRoundBits
