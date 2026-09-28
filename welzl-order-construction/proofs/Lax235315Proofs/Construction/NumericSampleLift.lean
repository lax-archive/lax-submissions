import Lax235315Proofs.Construction.ActiveBookkeeping
import Lax235315Proofs.Construction.NearCounterCorrectness
import Lax235315Proofs.Construction.ScanSampleTransport
import Mathlib.Tactic

/-! Move a literal numeric source sample into the finite graph vertex type. -/

namespace Lax235315Proofs.Construction.NumericSampleLift

open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.ScanSampleTransport

noncomputable section

def finSample (n : ℕ) (W : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val ∈ W

@[simp] lemma coe_finSample (n : ℕ) (W : Finset ℕ) :
    (finSample n W : Set (Fin n)) = finSetAsSet W := by
  ext v
  simp [finSample, finSetAsSet]

lemma finSample_card {n : ℕ} {W : Finset ℕ}
    (hrange : ∀ v ∈ W, v < n) :
    (finSample n W).card = W.card := by
  rw [← Set.ncard_coe_finset, coe_finSample]
  exact finSetAsSet_ncard hrange

lemma finSample_subset_active {n : ℕ} {W : Finset ℕ}
    {active : ℕ → ℕ}
    (hsub : W ⊆ activeVertices n active) :
    finSample n W ⊆ activeFinset active := by
  intro v hv
  have hvW : v.val ∈ W := by simpa [finSample] using hv
  have hvA := hsub hvW
  rw [mem_activeFinset]
  exact (mem_activeVertices.mp hvA).2

lemma finSample_map_val {n : ℕ} (vertices : List (Fin n)) :
    finSample n ((vertices.map Fin.val).toFinset) = vertices.toFinset := by
  ext v
  simp [finSample, List.mem_map]
  constructor
  · rintro ⟨u, hu, heq⟩
    have huv : u = v := Fin.ext heq
    simpa [huv] using hu
  · intro hv
    exact ⟨v, hv, rfl⟩

lemma finSample_scan_positions (active : ℕ → ℕ) (n : ℕ)
    (positions : List (Fin (activeVertices n active).card)) :
    finSample n ((positions.map fun i => (scanVertex active n i).val).toFinset) =
      Finset.map (scanVertex active n) positions.toFinset := by
  have h := finSample_map_val (vertices := positions.map (scanVertex active n))
  have hmap : (positions.map (scanVertex active n)).toFinset =
      Finset.map (scanVertex active n) positions.toFinset := by
    ext v
    simp
  simpa [List.map_map, Function.comp_def, hmap] using h

end

end Lax235315Proofs.Construction.NumericSampleLift
