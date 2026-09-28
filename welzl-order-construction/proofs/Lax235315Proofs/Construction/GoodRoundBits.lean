import Lax235315Proofs.Construction.PositionFailureBits
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

end

end Lax235315Proofs.Construction.GoodRoundBits
