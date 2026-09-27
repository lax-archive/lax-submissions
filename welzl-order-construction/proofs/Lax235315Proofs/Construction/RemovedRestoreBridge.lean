import Lax235315Proofs.Construction.ActiveBookkeeping
import Lax235315Proofs.Construction.ConcreteReconstruction
import Mathlib.Tactic

/-! Connect the numeric deletion log to the order-sensitive twin restoration. -/

namespace Lax235315Proofs.Construction.RemovedRestoreBridge

open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.ConcreteReconstruction
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.RecordRemovedSource
open Lax235315Proofs.Construction.TracePartitions

/-- The deletion scan, represented as a `Fin n` list in its actual scan order. -/
def removedFinList {n : ℕ} (active next : ℕ → ℕ) : List (Fin n) :=
  (removedList active next 0 n).attach.map fun x =>
    ⟨x.1, by
      have hx := mem_removedList.mp x.2
      omega⟩

lemma mem_removedFinList {n : ℕ} {active next : ℕ → ℕ} {v : Fin n} :
    v ∈ removedFinList (n := n) active next ↔
      v.val ∈ removedList active next 0 n := by
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨x, hx, hval⟩
    have hx' : x.1 = v.val := congrArg Fin.val hval
    simpa [hx'] using x.2
  · intro hv
    apply List.mem_map.mpr
    refine ⟨⟨v.val, hv⟩, List.mem_attach _ _, ?_⟩
    apply Fin.ext
    rfl

lemma removedFinList_nodup {n : ℕ} (active next : ℕ → ℕ) :
    (removedFinList (n := n) active next).Nodup := by
  apply List.Nodup.map (f := fun x : {x // x ∈ removedList active next 0 n} =>
    (⟨x.1, by have hx := mem_removedList.mp x.2; omega⟩ : Fin n))
  · intro x y hxy
    apply Subtype.ext
    exact congrArg Fin.val hxy
  · exact List.nodup_attach.mpr (removedList_nodup active next 0 n)

/-- The numeric deletion log, lifted to `Fin n`, enumerates exactly the old
active vertices outside the representatives selected by the completed pass. -/
lemma removedFinList_enumerates {n : ℕ} {active next label table reps : ℕ → ℕ}
    {R : Finset ℕ} (hbits : ∀ i < n, next i ≤ 1)
    (hdata : RepData n n n active label table reps next R) :
    Enumerates (({v : Fin n | active v.val = 1} : Set (Fin n)) \ finSetAsSet R)
      (removedFinList (n := n) active next) := by
  constructor
  · exact removedFinList_nodup active next
  · intro v
    rw [mem_removedFinList, mem_removedList]
    have hactive : activeVertices n next = R := RepData.active_eq hdata
    simp only [Nat.zero_le, Nat.zero_add, true_and]
    constructor
    · rintro ⟨hvn, ha, hn⟩
      refine ⟨ha, ?_⟩
      intro hR
      have hnext : v.val ∈ activeVertices n next := by
        rw [hactive]
        exact hR
      have hnextOne := (mem_activeVertices.mp hnext).2
      omega
    · rintro ⟨ha, hnotR⟩
      have hnextOne : next v.val ≠ 1 := by
        intro hn
        apply hnotR
        change v.val ∈ R
        rw [← hactive]
        exact mem_activeVertices.mpr ⟨v.isLt, hn⟩
      have hnzero : next v.val = 0 := by
        have := hbits v.val v.isLt
        omega
      exact ⟨v.isLt, ha, hnzero⟩

/-- The lifted deletion list carries the same concrete representative values
as the source's parallel `removedRepList` array, point by point. -/
lemma removedFinList_map_representative_val {n : ℕ}
    (active next rep : ℕ → ℕ) :
    (removedFinList (n := n) active next).map (fun v => rep v.val) =
      (removedRepList active next rep 0 n) := by
  simp [removedFinList, removedRepList]

/-- On every logged deletion, the abstract representative used by the
restoration theorem is exactly the numeric `repOf` array entry. -/
lemma removedFinList_concrete_representative_map {n : ℕ}
    {G : SimpleGraph (Fin n)} {active next repOf : ℕ → ℕ}
    {S : Set (Fin n)} {R : Finset ℕ}
    (hpart : ConcreteTracePartition G active S R repOf) :
    (removedFinList (n := n) active next).map
        (fun v => (hpart.partition.representative v).val) =
      removedRepList active next repOf 0 n := by
  calc
    (removedFinList (n := n) active next).map
        (fun v => (hpart.partition.representative v).val) =
      (removedFinList (n := n) active next).map (fun v => repOf v.val) := by
        apply List.map_congr_left
        intro v hv
        have hscan := mem_removedList.mp (mem_removedFinList.mp hv)
        exact hpart.representative_val v hscan.2.2.1
    _ = removedRepList active next repOf 0 n :=
      removedFinList_map_representative_val active next repOf

/-- Replaying the actual deletion-log order gives the order-sensitive
restoration theorem for the concrete partition produced by the arrays. -/
lemma ConcreteTracePartition.restore_removed_log
    {n : ℕ} {G : SimpleGraph (Fin n)} {active next label table reps repOf : ℕ → ℕ}
    {S : Set (Fin n)} {R : Finset ℕ}
    (hpart : ConcreteTracePartition G active S R repOf)
    (hdata : RepData n n n active label table reps next R)
    (hbits : ∀ i < n, next i ≤ 1)
    {small : List (Fin n)} (hsmall : Enumerates (finSetAsSet R) small) :
    Enumerates ({v : Fin n | active v.val = 1} : Set (Fin n))
        (restoreAfter hpart.partition.representative small (removedFinList (n := n) active next)) ∧
      TwinExpansion G S small
        (restoreAfter hpart.partition.representative small (removedFinList (n := n) active next)) := by
  exact TracePartition.restoreAfter_nonrepresentatives hpart.partition hsmall
    (removedFinList_enumerates hbits hdata)

end Lax235315Proofs.Construction.RemovedRestoreBridge
