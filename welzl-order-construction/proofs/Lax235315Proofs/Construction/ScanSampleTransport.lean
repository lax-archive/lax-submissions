import Lax235315Proofs.Construction.ScanIndexEquiv
import Lax235315Proofs.Construction.NearCounterCorrectness
import Lax235315Proofs.Construction.Sampling
import Mathlib.Tactic

/-! Transfer bad samples from graph vertices to positions in the literal
increasing active-vertex scan, without increasing their number. -/
namespace Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.ScanIndexEquiv
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.Sampling

noncomputable section

/-- The source scan position's actual graph vertex. -/
def scanVertex (active : ℕ → ℕ) (n : ℕ) :
    Fin (activeVertices n active).card ↪ Fin n where
  toFun i := (scanIndexEquiv active n i).val
  inj' := by
    intro i j hij
    exact (scanIndexEquiv active n).injective (Subtype.ext hij)

/-- A set of source scan positions as the corresponding graph sample. -/
def liftSample (active : ℕ → ℕ) (n : ℕ)
    (W : Finset (Fin (activeVertices n active).card)) : Finset (Fin n) :=
  W.map (scanVertex active n)

@[simp] lemma liftSample_card (active : ℕ → ℕ) (n : ℕ)
    (W : Finset (Fin (activeVertices n active).card)) :
    (liftSample active n W).card = W.card := by
  simp [liftSample]

lemma scanVertex_range (active : ℕ → ℕ) (n : ℕ) :
    Finset.univ.map (scanVertex active n) = activeFinset active := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hv
    have hvactive := (scanIndexEquiv active n i).property
    rw [mem_activeFinset]
    rw [← hi]
    exact hvactive
  · intro hv
    let w : ActiveVertex n active := ⟨v, (mem_activeFinset.mp hv)⟩
    obtain ⟨i, hi⟩ := (scanIndexEquiv active n).surjective w
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val hi

lemma liftSample_subset_active (active : ℕ → ℕ) (n : ℕ)
    (W : Finset (Fin (activeVertices n active).card)) :
    liftSample active n W ⊆ activeFinset active := by
  rw [← scanVertex_range]
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- A bad graph sample pulls back to precisely those position samples whose
literal scan image is bad. -/
def badPositionSamples (active : ℕ → ℕ) (n : ℕ)
    (bad : Finset (Finset (Fin n))) :
    Finset (Finset (Fin (activeVertices n active).card)) :=
  Finset.univ.filter fun W => liftSample active n W ∈ bad

lemma badPositionSamples_subset_samples (active : ℕ → ℕ) (n s : ℕ)
    (bad : Finset (Finset (Fin n)))
    (hbad : bad ⊆ samples (activeFinset active) s) :
    badPositionSamples active n bad ⊆ samples Finset.univ s := by
  intro W hW
  have hgraph := hbad (Finset.mem_filter.mp hW).2
  have hcard : (liftSample active n W).card = s :=
    (Finset.mem_powersetCard.mp hgraph).2
  apply Finset.mem_powersetCard.mpr
  exact ⟨Finset.subset_univ _, by simpa using hcard⟩

/-- Passing to source scan positions cannot increase the bad-sample count. -/
lemma card_badPositionSamples_le (active : ℕ → ℕ) (n : ℕ)
    (bad : Finset (Finset (Fin n))) :
    (badPositionSamples active n bad).card ≤ bad.card := by
  let f := liftSample active n
  have hinj : Function.Injective f := Finset.map_injective (scanVertex active n)
  have hsub : (badPositionSamples active n bad).image f ⊆ bad := by
    intro W hW
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hW
    exact (Finset.mem_filter.mp hX).2
  calc
    (badPositionSamples active n bad).card =
        ((badPositionSamples active n bad).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ bad.card := Finset.card_le_card hsub

end

end Lax235315Proofs.Construction.ScanSampleTransport
