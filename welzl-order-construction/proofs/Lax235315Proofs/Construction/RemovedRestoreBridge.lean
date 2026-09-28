import Lax235315Proofs.Construction.ActiveBookkeeping
import Lax235315Proofs.Construction.ConcreteReconstruction
import Mathlib.Tactic

/-! Connect the numeric deletion log to the order-sensitive twin restoration. -/

namespace Lax235315Proofs.Construction.RemovedRestoreBridge

open scoped symmDiff

open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.ListCrossing
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
lemma removedFinList_enumerates {n current : ℕ}
    {active next label table reps : ℕ → ℕ}
    {R : Finset ℕ} (hbits : ∀ i < n, next i ≤ 1)
    (hdata : RepData n current n active label table reps next R) :
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

/-- Mapping an insertion through an injective encoding preserves its
position and its target. -/
lemma insertAfter_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (a x : α) (l : List α) :
    (insertAfter a x l).map f = insertAfter (f a) (f x) (l.map f) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      by_cases h : b = a
      · subst b
        simp [insertAfter]
      · have h' : f b ≠ f a := fun hfa => h (hf hfa)
        simp [insertAfter, h, h', ih]

/-- Restoration commutes with an injective encoding when the two
representative maps agree on every vertex being restored. -/
lemma restoreAfter_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f)
    (repA : α → α) (repB : β → β) (current removed : List α)
    (hrep : ∀ x ∈ removed, f (repA x) = repB (f x)) :
    (restoreAfter repA current removed).map f =
      restoreAfter repB (current.map f) (removed.map f) := by
  induction removed generalizing current with
  | nil => rfl
  | cons x xs ih =>
      have hx := hrep x (by simp)
      have htail : ∀ y ∈ xs, f (repA y) = repB (f y) := by
        intro y hy
        exact hrep y (by simp [hy])
      rw [restoreAfter_cons, ih _ htail, insertAfter_map f hf]
      rw [hx]
      rfl

/-- The actual scan-order log retains exactly the same natural-number order
when its `Fin n` entries are mapped through `Fin.val`. -/
lemma removedFinList_map_val {n : ℕ} (active next : ℕ → ℕ) :
    (removedFinList (n := n) active next).map Fin.val =
      removedList active next 0 n := by
  simp [removedFinList]

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

/-- Mapping the restored `Fin n` order to numeric vertices is exactly the
linked-list replay from the scanned deletion log and its `repOf` array. -/
lemma ConcreteTracePartition.restore_removed_log_map_val {n : ℕ}
    {G : SimpleGraph (Fin n)} {active next repOf : ℕ → ℕ}
    {S : Set (Fin n)} {R : Finset ℕ}
    (hpart : ConcreteTracePartition G active S R repOf)
    (small : List (Fin n)) :
    (restoreAfter hpart.partition.representative small
      (removedFinList (n := n) active next)).map Fin.val =
      restoreAfter repOf (small.map Fin.val) (removedList active next 0 n) := by
  rw [restoreAfter_map Fin.val_injective]
  · rw [removedFinList_map_val]
  · intro v hv
    have hscan := mem_removedList.mp (mem_removedFinList.mp hv)
    exact hpart.representative_val v hscan.2.2.1

/-- Replaying the actual deletion-log order gives the order-sensitive
restoration theorem for the concrete partition produced by the arrays. -/
lemma ConcreteTracePartition.restore_removed_log
    {n current : ℕ} {G : SimpleGraph (Fin n)}
    {active next label table reps repOf : ℕ → ℕ}
    {S : Set (Fin n)} {R : Finset ℕ}
    (hpart : ConcreteTracePartition G active S R repOf)
    (hdata : RepData n current n active label table reps next R)
    (hbits : ∀ i < n, next i ≤ 1)
    {small : List (Fin n)} (hsmall : Enumerates (finSetAsSet R) small) :
    Enumerates ({v : Fin n | active v.val = 1} : Set (Fin n))
        (restoreAfter hpart.partition.representative small (removedFinList (n := n) active next)) ∧
      TwinExpansion G S small
        (restoreAfter hpart.partition.representative small (removedFinList (n := n) active next)) := by
  exact TracePartition.restoreAfter_nonrepresentatives hpart.partition hsmall
    (removedFinList_enumerates hbits hdata)

/-- The two concrete partitions, completed representative data, and near
certificate form a `Reduction` whose larger order restores the actual
scan-order deletion log. -/
lemma ConcreteTracePartition.reduction_of_removed_log
    {n k currentA : ℕ} {G : SimpleGraph (Fin n)}
    {activeA activeB nextA labelA tableA repsA repA repB : ℕ → ℕ}
    {W : Set (Fin n)} {R S : Finset ℕ}
    (hB : ConcreteTracePartition G activeB W R repB)
    (hA : ConcreteTracePartition G activeA (finSetAsSet R) S repA)
    (hdataA : RepData n currentA n activeA labelA tableA repsA nextA S)
    (hbitsA : ∀ i < n, nextA i ≤ 1)
    (hnear : ∀ b ∈ ({v : Fin n | activeB v.val = 1} : Set (Fin n)),
      ((G.neighborSet b ∩ {v : Fin n | activeA v.val = 1}) ∆
        (G.neighborSet (hB.partition.representative b) ∩
          {v : Fin n | activeA v.val = 1})).ncard ≤ k)
    {small : List (Fin n)} (hsmall : Enumerates (finSetAsSet S) small) :
    Nonempty (Reduction G k
      {v : Fin n | activeA v.val = 1}
      {v : Fin n | activeB v.val = 1}
      (finSetAsSet S) (finSetAsSet R) small
      (restoreAfter hA.partition.representative small
        (removedFinList (n := n) activeA nextA))) := by
  obtain ⟨hbig, hexpands⟩ :=
    ConcreteTracePartition.restore_removed_log hA hdataA hbitsA hsmall
  exact ⟨{
    small_enumerates := hsmall
    big_enumerates := hbig
    expands := hexpands
    representative := hB.partition.representative
    representative_mem := hB.partition.representative_mem
    near := hnear
  }⟩

end Lax235315Proofs.Construction.RemovedRestoreBridge
