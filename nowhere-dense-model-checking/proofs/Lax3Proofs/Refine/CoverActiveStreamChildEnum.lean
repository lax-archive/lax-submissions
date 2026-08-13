import Lax3Proofs.Refine.CoverActiveStreamChild
import Lax3Proofs.Refine.CoverActiveStreamEnum

/-!
# Enumerating a completed streamed child

This module is the exact seam between the streamed child-mask/member result
and the existing streamed batch enumerator.  The recursion record is an
explicit precondition: constructing it belongs to the later fused driver,
not to this row-local enumeration step.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamChildEnum

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.CoverActiveStreamChild
open Lax3Proofs.Refine.CoverActiveStreamEnum
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- **Enumerate one completed streamed child.**  `StreamChildOut` supplies
the exact ambient-arena `BatchData` and identifies the resident row with the
current cluster.  Its sorted state separately retains the progressively
depleted cover-search mask.  The only additional semantic inputs are the already-built
successor recursion record, nonemptiness/cardinality of the batch, and the
formula-sized output allocation.  The command is just `enumStreamCom`, with
its exact `enumStreamCost tail mb` charge. -/
theorem streamChildEnumStep
    {B n ns nt na q cap mb j c tail bits d mm : ℕ}
    {G : SimpleGraph (Fin n)}
    {A₀ O T centre Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} (hB : WordBoundK B n d ns cap mb) :
    Spec B
      (fun σ =>
        StreamChildOut B ns nt na q cap j c tail bits G A₀ π centre O T
          Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem mm σ ∧
        PlayRec B cap G (j + 1) Alv Gam σ ∧
        (markSet n Wa ∩ markSet n Xa).Nonempty ∧
        (markSet n Wa).ncard ≤ mb ∧
        ∃ g, σ.arrs "wa" = arrOf mb g)
      (enumStreamCom "xmem" (batName j) (cluName j) mb)
      (fun σ σ' =>
        StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
            Xmem asg M σ' ∧
          PlayRec B cap G (j + 1) Alv Gam σ' ∧ σ'.out = σ.out ∧
          ∃ w : Fin mb → Fin n,
            ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w
                Alv Gam σ' ∧
              ClusterWa mb w σ')
      (enumStreamCost tail mb) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hchild, hplay, hne, hcard, hwa⟩ := hσ
  have hcluster : ∀ v : Fin n, v ∈ markSet n Xa →
      v ∈ Lax3Proofs.Refine.MassMath.clusterAt G A₀ π centre cap c := by
    intro v hv
    rw [← hchild.cluster_set]
    exact hv
  obtain ⟨σ', hr, hsorted, hplay', hout, w, hclusterData, hclusterWa⟩ :=
    (enumStreamStepA (G := G) (X := markSet n Xa) (W := markSet n Wa)
      (Alv' := Alv) (Gam' := Gam) hB (le_refl _)).run (σ := σ)
      ⟨hchild.sorted, hchild.batch, hplay, hne, hcard, hcluster, hwa⟩
  exact ⟨σ', enumStreamCost tail mb, hr, le_rfl, hsorted, hplay', hout,
    w, hclusterData, hclusterWa⟩

#print axioms streamChildEnumStep

end Lax3Proofs.Refine.CoverActiveStreamChildEnum
