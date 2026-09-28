import Lax235315Proofs.Construction.RecordRemovedSource
import Lax235315Proofs.Construction.PartitionSource
import Lax235315Proofs.Construction.PartitionResult

/-! Exact active/deleted cardinality identities used by the outer loop. -/

namespace Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.RecordRemovedSource
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.TracePartitions

lemma removedList_eq_filter (active next : ℕ → ℕ) (start count : ℕ) :
    removedList active next start count =
      (scanList active start count).filter (fun v => next v == 0) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    by_cases ha : active start = 1 <;> by_cases hn : next start = 0 <;>
      simp [removedList, scanList, ha, hn, ih]

lemma removedList_nodup (active next : ℕ → ℕ) (start count : ℕ) :
    (removedList active next start count).Nodup := by
  rw [removedList_eq_filter]
  exact (scanList_nodup active start count).filter _

lemma mem_removedList {active next : ℕ → ℕ} {start count v : ℕ} :
    v ∈ removedList active next start count ↔
      start ≤ v ∧ v < start + count ∧ active v = 1 ∧ next v = 0 := by
  rw [removedList_eq_filter]
  simp only [List.mem_filter, mem_scanList, beq_iff_eq]
  tauto

lemma removedList_toFinset {n : ℕ} {active next : ℕ → ℕ}
    (hbits : ∀ i < n, next i ≤ 1) :
    (removedList active next 0 n).toFinset =
      activeVertices n active \ activeVertices n next := by
  ext i
  simp only [List.mem_toFinset, mem_removedList, Nat.zero_le, Nat.zero_add,
    true_and, Finset.mem_sdiff, mem_activeVertices]
  constructor
  · rintro ⟨hi, ha, hn⟩
    exact ⟨⟨hi, ha⟩, by simp [hn]⟩
  · rintro ⟨⟨hi, ha⟩, hn⟩
    have hb := hbits i hi
    exact ⟨hi, ha, by omega⟩

lemma removed_length_add_next {n : ℕ} {active next : ℕ → ℕ}
    (hbits : ∀ i < n, next i ≤ 1)
    (hsub : activeVertices n next ⊆ activeVertices n active) :
    (removedList active next 0 n).length + (activeVertices n next).card =
      (activeVertices n active).card := by
  rw [← List.toFinset_card_of_nodup (removedList_nodup active next 0 n),
    removedList_toFinset hbits]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- Deleted plus still-active vertices remains exactly the original size. -/
lemma deleted_active_conservation {n base : ℕ} {active next : ℕ → ℕ}
    (hbits : ∀ i < n, next i ≤ 1)
    (hsub : activeVertices n next ⊆ activeVertices n active)
    (hcount : base + (activeVertices n active).card = n) :
    base + (removedList active next 0 n).length +
      (activeVertices n next).card = n := by
  have h := removed_length_add_next hbits hsub
  omega

lemma finSetAsSet_ncard {n : ℕ} {R : Finset ℕ}
    (hrange : ∀ v ∈ R, v < n) : (finSetAsSet (n := n) R).ncard = R.card := by
  have hinj : Set.InjOn Fin.val (finSetAsSet (n := n) R) :=
    Fin.val_injective.injOn
  have himage : Fin.val '' finSetAsSet (n := n) R = (R : Set ℕ) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hv
      exact ⟨⟨v, hrange v hv⟩, hv, rfl⟩
  rw [← Set.ncard_coe_finset, ← himage, hinj.ncard_image]

lemma finSetAsSet_activeVertices (n : ℕ) (active : ℕ → ℕ) :
    finSetAsSet (n := n) (activeVertices n active) =
      {v : Fin n | active v.val = 1} := by
  ext v
  simp [finSetAsSet, mem_activeVertices]

lemma activeSet_ncard (n : ℕ) (active : ℕ → ℕ) :
    ({v : Fin n | active v.val = 1} : Set (Fin n)).ncard =
      (activeVertices n active).card := by
  rw [← finSetAsSet_activeVertices]
  exact finSetAsSet_ncard (fun v hv => (mem_activeVertices.mp hv).1)

lemma RepData.active_eq {n current : ℕ} {active label table reps next : ℕ → ℕ}
    {R : Finset ℕ} (h : RepData n current n active label table reps next R) :
    activeVertices n next = R := by
  ext v
  rw [mem_activeVertices]
  constructor
  · rintro ⟨hi, hv⟩
    exact (h.out_mem v hi).mp hv
  · intro hv
    have hi := (mem_activeVertices.mp (h.reps_processed hv)).1
    exact ⟨hi, (h.out_mem v hi).mpr hv⟩

lemma RepData.next_subset {n current : ℕ} {active label table reps next : ℕ → ℕ}
    {R : Finset ℕ} (h : RepData n current n active label table reps next R) :
    activeVertices n next ⊆ activeVertices n active := by
  rw [RepData.active_eq h]
  exact h.reps_processed

lemma ConcreteTracePartition.next_nonempty
    {n : ℕ} {G : SimpleGraph (Fin n)} {active rep : ℕ → ℕ}
    {W : Set (Fin n)} {R : Finset ℕ}
    (h : ConcreteTracePartition G active W R rep)
    (hne : (activeVertices n active).Nonempty) : R.Nonempty := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨hi, ha⟩ := mem_activeVertices.mp hv
  exact ⟨rep v, by
    have hm := h.partition.representative_mem ⟨v, hi⟩ ha
    change (h.partition.representative ⟨v, hi⟩).val ∈ R at hm
    rwa [h.representative_val ⟨v, hi⟩ ha] at hm⟩

/-- The numeric representative counts satisfy the paper recurrence. -/
lemma concrete_partitions_shrink {n c : ℕ} {G : SimpleGraph (Fin n)}
    {activeA activeB repA repB : ℕ → ℕ} {W R S : Finset ℕ}
    (hc : 1 ≤ c)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hB : ConcreteTracePartition G activeB (finSetAsSet W) R repB)
    (hA : ConcreteTracePartition G activeA (finSetAsSet R) S repA)
    (hWr : ∀ v ∈ W, v < n) (hSr : ∀ v ∈ S, v < n)
    (hW : W.Nonempty) (hBne : (activeVertices n activeB).Nonempty)
    (hWcard : W.card = sampleSize (activeVertices n activeA).card c) :
    S.card ≤ (activeVertices n activeA).card / 2 + c ^ 2 := by
  have hWne : (finSetAsSet (n := n) W).Nonempty := by
    obtain ⟨v, hv⟩ := hW
    exact ⟨⟨v, hWr v hv⟩, hv⟩
  have hBn : ({v : Fin n | activeB v.val = 1} : Set (Fin n)).Nonempty := by
    obtain ⟨v, hv⟩ := hBne
    obtain ⟨hi, ha⟩ := mem_activeVertices.mp hv
    exact ⟨⟨v, hi⟩, ha⟩
  have h := partitions_ground_ncard_le_half_add G hc hG hB.partition hA.partition
    hWne hBn (by rw [finSetAsSet_ncard hWr, activeSet_ncard, hWcard])
  simpa [finSetAsSet_ncard hSr, activeSet_ncard] using h

end Lax235315Proofs.Construction.ActiveBookkeeping
