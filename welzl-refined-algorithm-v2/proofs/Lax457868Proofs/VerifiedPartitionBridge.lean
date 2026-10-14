import Lax457868Proofs.ContractionRounds
import Lax457868Proofs.GraphTraceBounds
import Lax457868Proofs.ReusedOriginal.Construction.TracePartitions
import Lax457868Proofs.ReusedOriginal.Construction.PartitionResult

set_option autoImplicit false

/-!
Adapters from the verified Welzl trace partitions to the finite contraction
used by the refined algorithm.  The representative maps below are the maps
stored in the verified partitions; no new representative selection is made.
-/

namespace Lax457868Proofs.VerifiedPartitionBridge

open Lax457868Proofs.ContractionRounds
open Lax457868Proofs.GraphTraceBounds
open Lax457868Proofs.ReusedOriginal.Construction.TracePartitions
open Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult

private lemma finiteNeighborhood_inter_coe_eq_trace {n : ℕ}
    (G : SimpleGraph (Fin n)) {A X : Finset (Fin n)} (hXA : X ⊆ A)
    (v : Fin n) :
    ((finiteNeighborhood G A v ∩ X : Finset (Fin n)) : Set (Fin n)) =
      neighborhoodTrace G (X : Set (Fin n)) v := by
  ext x
  simp only [SetLike.mem_coe, Finset.mem_inter, finiteNeighborhood,
    Finset.mem_filter, neighborhoodTrace,
    Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨⟨ha, hadj⟩, hx⟩
    exact ⟨hadj, hx⟩
  · rintro ⟨hadj, hx⟩
    exact ⟨⟨hXA hx, hadj⟩, hx⟩

private lemma trace_eq_of_finiteNeighborhood_inter_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) {A X : Finset (Fin n)} (hXA : X ⊆ A)
    {u v : Fin n}
    (heq : finiteNeighborhood G A u ∩ X = finiteNeighborhood G A v ∩ X) :
    neighborhoodTrace G (X : Set (Fin n)) u =
      neighborhoodTrace G (X : Set (Fin n)) v := by
  rw [← finiteNeighborhood_inter_coe_eq_trace G hXA u,
    ← finiteNeighborhood_inter_coe_eq_trace G hXA v, heq]

private lemma finiteNeighborhood_inter_eq_of_trace_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) {A X : Finset (Fin n)} (hXA : X ⊆ A)
    {u v : Fin n}
    (heq : neighborhoodTrace G (X : Set (Fin n)) u =
      neighborhoodTrace G (X : Set (Fin n)) v) :
    finiteNeighborhood G A u ∩ X = finiteNeighborhood G A v ∩ X := by
  apply Finset.coe_injective
  rw [finiteNeighborhood_inter_coe_eq_trace G hXA u,
    finiteNeighborhood_inter_coe_eq_trace G hXA v, heq]

private lemma finiteNeighborhood_label_eq_iff_trace_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) {A X : Finset (Fin n)} (hXA : X ⊆ A)
    {u v : Fin n} :
    (finiteNeighborhood G A u ∩ X = finiteNeighborhood G A v ∩ X) ↔
      neighborhoodTrace G (X : Set (Fin n)) u =
        neighborhoodTrace G (X : Set (Fin n)) v := by
  exact ⟨trace_eq_of_finiteNeighborhood_inter_eq G hXA,
    finiteNeighborhood_inter_eq_of_trace_eq G hXA⟩

private lemma tracePartition_fixed {n : ℕ} {G : SimpleGraph (Fin n)}
    {V S R : Set (Fin n)} (h : TracePartition G V S R)
    {r : Fin n} (hr : r ∈ R) : h.representative r = r := by
  have hrv := h.reps_mem hr
  have hsame := h.same_trace r hrv
  have hrepR := h.representative_mem r hrv
  exact h.reps_separated hrepR hr hsame

private lemma tracePartition_range_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    {V S R : Set (Fin n)} (h : TracePartition G V S R) :
    h.representative '' V = R := by
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact h.representative_mem v hv
  · intro hr
    exact ⟨r, h.reps_mem hr, tracePartition_fixed h hr⟩

private lemma finset_image_partition_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    {V S R : Set (Fin n)} (h : TracePartition G V S R)
    (Vf Rf : Finset (Fin n)) (hV : (Vf : Set (Fin n)) = V)
    (hR : (Rf : Set (Fin n)) = R) :
    Vf.image h.representative = Rf := by
  classical
  apply Finset.ext
  intro r
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩
    have hvV : v ∈ V := by rw [← hV]; exact hv
    have hrepR := h.representative_mem v hvV
    have hrepRf : h.representative v ∈ (Rf : Set (Fin n)) := by
      rw [hR]
      exact hrepR
    exact hrepRf
  · intro hr
    have hrR : r ∈ R := by rw [← hR]; exact hr
    have hrV := h.reps_mem hrR
    have hrVf : r ∈ (Vf : Set (Fin n)) := by rw [hV]; exact hrV
    apply Finset.mem_image.mpr
    exact ⟨r, hrVf, tracePartition_fixed h hrR⟩

private noncomputable def representative_choice_of_tracePartition {n : ℕ}
    {G : SimpleGraph (Fin n)} {V S R : Set (Fin n)}
    (h : TracePartition G V S R)
    (Vf : Finset (Fin n)) (hV : (Vf : Set (Fin n)) = V)
    (label : Fin n → Finset (Fin n))
    (hlabel : ∀ u v : Fin n, u ∈ V → v ∈ V →
      (label u = label v ↔
        neighborhoodTrace G S u = neighborhoodTrace G S v)) :
    RepresentativeChoice Vf label := by
  refine ⟨h.representative, ?_, ?_, ?_⟩
  · intro v hv
    have hvV : v ∈ V := by rw [← hV]; exact hv
    have hrepR := h.representative_mem v hvV
    have hrepV : h.representative v ∈ V := h.reps_mem hrepR
    have hrepVf : h.representative v ∈ (Vf : Set (Fin n)) := by
      rw [hV]
      exact hrepV
    exact Finset.mem_coe.mp hrepVf
  · intro v hv
    have hvV : v ∈ V := by rw [← hV]; exact hv
    have hrepV : h.representative v ∈ V :=
      h.reps_mem (h.representative_mem v hvV)
    apply (hlabel (h.representative v) v hrepV hvV).2
    exact h.same_trace v hvV
  · intro u hu v hv heq
    have huV : u ∈ V := by rw [← hV]; exact hu
    have hvV : v ∈ V := by rw [← hV]; exact hv
    have htraces := (hlabel u v huV hvV).1 heq
    have huR := h.representative_mem u huV
    have hvR := h.representative_mem v hvV
    apply h.reps_separated huR hvR
    calc
      neighborhoodTrace G S (h.representative u) = neighborhoodTrace G S u :=
        h.same_trace u huV
      _ = neighborhoodTrace G S v := htraces
      _ = neighborhoodTrace G S (h.representative v) :=
        (h.same_trace v hvV).symm

private lemma primal_label_iff_trace {n : ℕ}
    (G : SimpleGraph (Fin n)) (A W : Finset (Fin n)) (hWA : W ⊆ A)
    (u v : Fin n) :
    (finiteNeighborhood G A u ∩ W = finiteNeighborhood G A v ∩ W ↔
      neighborhoodTrace G (W : Set (Fin n)) u =
        neighborhoodTrace G (W : Set (Fin n)) v) :=
  ⟨trace_eq_of_finiteNeighborhood_inter_eq G hWA,
    finiteNeighborhood_inter_eq_of_trace_eq G hWA⟩

private lemma mem_finiteNeighborhood {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a b : Fin n) :
    a ∈ finiteNeighborhood G A b ↔ a ∈ A ∧ G.Adj b a := by
  simp [finiteNeighborhood]

private lemma dual_label_iff_trace {n : ℕ}
    (G : SimpleGraph (Fin n)) (A R : Finset (Fin n))
    {u v : Fin n} (hu : u ∈ A) (hv : v ∈ A) :
    (R.filter (fun b => u ∈ finiteNeighborhood G A b) =
        R.filter (fun b => v ∈ finiteNeighborhood G A b) ↔
      neighborhoodTrace G (R : Set (Fin n)) u =
        neighborhoodTrace G (R : Set (Fin n)) v) := by
  constructor
  · intro heq
    apply Set.ext
    intro b
    simp only [neighborhoodTrace, Set.mem_inter_iff, SetLike.mem_coe,
      SimpleGraph.mem_neighborSet]
    constructor
    · rintro ⟨hadj, hbR⟩
      have huLabel : b ∈ R.filter (fun x => u ∈ finiteNeighborhood G A x) := by
        apply Finset.mem_filter.mpr
        refine ⟨hbR, ?_⟩
        exact (mem_finiteNeighborhood G A u b).mpr ⟨hu, hadj.symm⟩
      have hvLabel : b ∈ R.filter (fun x => v ∈ finiteNeighborhood G A x) := by
        rw [← heq]
        exact huLabel
      rcases Finset.mem_filter.mp hvLabel with ⟨_, hmem⟩
      rcases (mem_finiteNeighborhood G A v b).mp hmem with ⟨_, hadj'⟩
      exact ⟨hadj'.symm, hbR⟩
    · rintro ⟨hadj, hbR⟩
      have hvLabel : b ∈ R.filter (fun x => v ∈ finiteNeighborhood G A x) := by
        apply Finset.mem_filter.mpr
        refine ⟨hbR, ?_⟩
        exact (mem_finiteNeighborhood G A v b).mpr ⟨hv, hadj.symm⟩
      have huLabel : b ∈ R.filter (fun x => u ∈ finiteNeighborhood G A x) := by
        rw [heq]
        exact hvLabel
      rcases Finset.mem_filter.mp huLabel with ⟨_, hmem⟩
      rcases (mem_finiteNeighborhood G A u b).mp hmem with ⟨_, hadj'⟩
      exact ⟨hadj'.symm, hbR⟩
  · intro heq
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hbR, hmem⟩
      rcases (mem_finiteNeighborhood G A u b).mp hmem with ⟨_, hadj⟩
      have htrace := Set.ext_iff.mp heq b
      simp only [neighborhoodTrace, Set.mem_inter_iff, SetLike.mem_coe,
        SimpleGraph.mem_neighborSet] at htrace
      rcases htrace.mp ⟨hadj.symm, hbR⟩ with ⟨hadjV, _⟩
      exact ⟨hbR, (mem_finiteNeighborhood G A v b).mpr ⟨hv, hadjV.symm⟩⟩
    · rintro ⟨hbR, hmem⟩
      rcases (mem_finiteNeighborhood G A v b).mp hmem with ⟨_, hadj⟩
      have htrace := Set.ext_iff.mp heq b
      simp only [neighborhoodTrace, Set.mem_inter_iff, SetLike.mem_coe,
        SimpleGraph.mem_neighborSet] at htrace
      rcases htrace.mpr ⟨hadj.symm, hbR⟩ with ⟨hadjU, _⟩
      exact ⟨hbR, (mem_finiteNeighborhood G A u b).mpr ⟨hu, hadjU.symm⟩⟩

/-- The original two certified trace partitions induce the refined finite
contraction.  Its representative functions are exactly those stored in the
source partitions, and their images are exactly the supplied representative
sets. -/
noncomputable def traceContractionOfVerifiedPartitions {n : ℕ}
    (G : SimpleGraph (Fin n)) (A B W B' A' : Finset (Fin n))
    (hWA : W ⊆ A)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    (hA : TracePartition G (A : Set (Fin n)) (B' : Set (Fin n))
      (A' : Set (Fin n))) :
    TraceContraction A B (finiteNeighborhood G A) W := by
  classical
  let bEvidence := representative_choice_of_tracePartition hB B rfl
      (fun b => finiteNeighborhood G A b ∩ W)
      (fun u v _ _ => primal_label_iff_trace G A W hWA u v)
  have hBimage : B.image hB.representative = B' :=
    finset_image_partition_eq hB B B' rfl rfl
  let aEvidence := representative_choice_of_tracePartition hA A rfl
      (fun a => B'.filter (fun b => a ∈ finiteNeighborhood G A b))
      (fun u v hu hv => dual_label_iff_trace G A B' hu hv)
  have bEvidenceRep : bEvidence.representative = hB.representative := by
    dsimp [bEvidence, representative_choice_of_tracePartition]
  let bChoice : RepresentativeChoice B (fun b => finiteNeighborhood G A b ∩ W) := {
    representative := hB.representative
    representative_mem := by simpa only [bEvidenceRep] using bEvidence.representative_mem
    representative_label := by simpa only [bEvidenceRep] using bEvidence.representative_label
    representative_constant := by simpa only [bEvidenceRep] using bEvidence.representative_constant
  }
  have aEvidenceRep : aEvidence.representative = hA.representative := by
    dsimp [aEvidence, representative_choice_of_tracePartition]
  let aChoice : RepresentativeChoice A
      (fun a => (B.image hB.representative).filter
        (fun b => a ∈ finiteNeighborhood G A b)) := {
    representative := hA.representative
    representative_mem := by simpa only [aEvidenceRep] using aEvidence.representative_mem
    representative_label := by
      simpa only [aEvidenceRep, hBimage] using aEvidence.representative_label
    representative_constant := by
      simpa only [aEvidenceRep, hBimage] using aEvidence.representative_constant
  }
  have aChoice' : RepresentativeChoice A
      (fun a => (B.image bChoice.representative).filter
        (fun b => a ∈ finiteNeighborhood G A b)) := by
    simpa only [bChoice] using aChoice
  exact ⟨bChoice, aChoice'⟩


@[simp] lemma traceContractionOfVerifiedPartitions_brepresentative
    {n : ℕ} (G : SimpleGraph (Fin n)) (A B W B' A' : Finset (Fin n))
    (hWA : W ⊆ A)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    (hA : TracePartition G (A : Set (Fin n)) (B' : Set (Fin n))
      (A' : Set (Fin n))) :
    (traceContractionOfVerifiedPartitions G A B W B' A' hWA hB hA).bChoice.representative =
      hB.representative := rfl

@[simp] lemma traceContractionOfVerifiedPartitions_arepresentative
    {n : ℕ} (G : SimpleGraph (Fin n)) (A B W B' A' : Finset (Fin n))
    (hWA : W ⊆ A)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    (hA : TracePartition G (A : Set (Fin n)) (B' : Set (Fin n))
      (A' : Set (Fin n))) :
    (traceContractionOfVerifiedPartitions G A B W B' A' hWA hB hA).aChoice.representative =
      hA.representative := rfl

@[simp] lemma traceContractionOfVerifiedPartitions_retainedB
    {n : ℕ} (G : SimpleGraph (Fin n)) (A B W B' A' : Finset (Fin n))
    (hWA : W ⊆ A)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    (hA : TracePartition G (A : Set (Fin n)) (B' : Set (Fin n))
      (A' : Set (Fin n))) :
    (traceContractionOfVerifiedPartitions G A B W B' A' hWA hB hA).retainedB = B' := by
  simp only [TraceContraction.retainedB, traceContractionOfVerifiedPartitions]
  exact finset_image_partition_eq hB B B' rfl rfl

@[simp] lemma traceContractionOfVerifiedPartitions_retainedA
    {n : ℕ} (G : SimpleGraph (Fin n)) (A B W B' A' : Finset (Fin n))
    (hWA : W ⊆ A)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    (hA : TracePartition G (A : Set (Fin n)) (B' : Set (Fin n))
      (A' : Set (Fin n))) :
    (traceContractionOfVerifiedPartitions G A B W B' A' hWA hB hA).retainedA = A' := by
  simp only [TraceContraction.retainedA, traceContractionOfVerifiedPartitions]
  exact finset_image_partition_eq hA A A' rfl rfl


/-- The finite subset of `Fin n` encoded by a numeric source representative
set. -/
def finsetOfNumeric {n : ℕ} (R : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val ∈ R

lemma coe_finsetOfNumeric {n : ℕ} (R : Finset ℕ) :
    ((finsetOfNumeric R : Finset (Fin n)) : Set (Fin n)) = finSetAsSet R := by
  ext v
  simp [finsetOfNumeric, finSetAsSet]

private def reindexTracePartition {n : ℕ} {G : SimpleGraph (Fin n)}
    {V S R V' S' R' : Set (Fin n)}
    (h : TracePartition G V S R) (hV : V' = V) (hS : S' = S)
    (hR : R' = R) : TracePartition G V' S' R' := hV ▸ hS ▸ hR ▸ h

private lemma reindexTracePartition_representative {n : ℕ}
    {G : SimpleGraph (Fin n)} {V S R V' S' R' : Set (Fin n)}
    (h : TracePartition G V S R) (hV : V' = V) (hS : S' = S)
    (hR : R' = R) :
    (reindexTracePartition h hV hS hR).representative = h.representative := by
  cases hV
  cases hS
  cases hR
  rfl

/-- Reuse the concrete source's two representative arrays as the refined
contraction. The retained sets are precisely the source arrays' numeric
representative sets, interpreted in `Fin n`. -/
noncomputable def concreteTraceContractionOfVerifiedPartitions {n : ℕ}
    (G : SimpleGraph (Fin n)) (A B W : Finset (Fin n))
    (activeA activeB repA repB : ℕ → ℕ)
    (R Q : Finset ℕ)
    (hAactive : ∀ v : Fin n, v ∈ A ↔ activeA v.val = 1)
    (hBactive : ∀ v : Fin n, v ∈ B ↔ activeB v.val = 1)
    (hWA : W ⊆ A)
    (hB : ConcreteTracePartition G activeB (W : Set (Fin n)) R repB)
    (hA : ConcreteTracePartition G activeA (finSetAsSet R) Q repA) :
    TraceContraction A B (finiteNeighborhood G A) W := by
  classical
  let B' := finsetOfNumeric (n := n) R
  let A' := finsetOfNumeric (n := n) Q
  have hBactiveSet : {v : Fin n | activeB v.val = 1} = (B : Set (Fin n)) := by
    ext v
    exact (hBactive v).symm
  have hAactiveSet : {v : Fin n | activeA v.val = 1} = (A : Set (Fin n)) := by
    ext v
    exact (hAactive v).symm
  let hBsource := reindexTracePartition hB.partition hBactiveSet.symm rfl
    (coe_finsetOfNumeric (n := n) R)
  let hAsource := reindexTracePartition hA.partition hAactiveSet.symm
    (coe_finsetOfNumeric (n := n) R) (coe_finsetOfNumeric (n := n) Q)
  exact traceContractionOfVerifiedPartitions G A B W B' A' hWA hBsource hAsource

lemma concreteTraceContractionOfVerifiedPartitions_bval {n : ℕ}
    (G : SimpleGraph (Fin n)) (A B W : Finset (Fin n))
    (activeA activeB repA repB : ℕ → ℕ)
    (R Q : Finset ℕ)
    (hAactive : ∀ v : Fin n, v ∈ A ↔ activeA v.val = 1)
    (hBactive : ∀ v : Fin n, v ∈ B ↔ activeB v.val = 1)
    (hWA : W ⊆ A)
    (hB : ConcreteTracePartition G activeB (W : Set (Fin n)) R repB)
    (hA : ConcreteTracePartition G activeA (finSetAsSet R) Q repA)
    (b : Fin n) (hb : b ∈ B) :
    ((concreteTraceContractionOfVerifiedPartitions G A B W activeA activeB
      repA repB R Q hAactive hBactive hWA hB hA).bChoice.representative b).val =
        repB b.val := by
  have hactive := (hBactive b).mp hb
  simp only [concreteTraceContractionOfVerifiedPartitions,
    traceContractionOfVerifiedPartitions_brepresentative,
    reindexTracePartition_representative]
  exact hB.representative_val b hactive

lemma concreteTraceContractionOfVerifiedPartitions_aval {n : ℕ}
    (G : SimpleGraph (Fin n)) (A B W : Finset (Fin n))
    (activeA activeB repA repB : ℕ → ℕ)
    (R Q : Finset ℕ)
    (hAactive : ∀ v : Fin n, v ∈ A ↔ activeA v.val = 1)
    (hBactive : ∀ v : Fin n, v ∈ B ↔ activeB v.val = 1)
    (hWA : W ⊆ A)
    (hB : ConcreteTracePartition G activeB (W : Set (Fin n)) R repB)
    (hA : ConcreteTracePartition G activeA (finSetAsSet R) Q repA)
    (a : Fin n) (ha : a ∈ A) :
    ((concreteTraceContractionOfVerifiedPartitions G A B W activeA activeB
      repA repB R Q hAactive hBactive hWA hB hA).aChoice.representative a).val =
        repA a.val := by
  have hactive := (hAactive a).mp ha
  simp only [concreteTraceContractionOfVerifiedPartitions,
    traceContractionOfVerifiedPartitions_arepresentative,
    reindexTracePartition_representative]
  exact hA.representative_val a hactive


end Lax457868Proofs.VerifiedPartitionBridge
