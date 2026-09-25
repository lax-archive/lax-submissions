import Lax235315Proofs.Construction.TracePartitions
import Mathlib.Tactic

/-! A deterministic, list-ordered version of the paper's twin restoration.
This is the form implemented by the reconstruction arrays. -/

namespace Lax235315Proofs.Construction.ConcreteReconstruction

open Lax235315Proofs.Construction.ListCrossing
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

/-- Insert the listed vertices, in list order, immediately after their
chosen representatives. -/
def restoreAfter {α : Type*} [DecidableEq α] (representative : α → α) :
    List α → List α → List α
  | current, [] => current
  | current, x :: xs =>
      restoreAfter representative (insertAfter (representative x) x current) xs

@[simp] theorem restoreAfter_nil {α : Type*} [DecidableEq α]
    (representative : α → α)
    (current : List α) : restoreAfter representative current [] = current := rfl

@[simp] theorem restoreAfter_cons {α : Type*} [DecidableEq α]
    (representative : α → α)
    (current : List α) (x : α) (xs : List α) :
    restoreAfter representative current (x :: xs) =
      restoreAfter representative
        (insertAfter (representative x) x current) xs := rfl

theorem restoreAfter_append {α : Type*} [DecidableEq α]
    (representative : α → α) (current xs ys : List α) :
    restoreAfter representative current (xs ++ ys) =
      restoreAfter representative (restoreAfter representative current xs) ys := by
  induction xs generalizing current with
  | nil => rfl
  | cons x xs ih => simpa using ih (insertAfter (representative x) x current)

/-- Replaying any duplicate-free enumeration of all nonrepresentatives gives
an enumeration of the old active set and a genuine twin expansion. -/
theorem TracePartition.restoreAfter_nonrepresentatives
    {n : ℕ} {G : SimpleGraph (Fin n)} {V S R : Set (Fin n)}
    (h : TracePartition G V S R) {small removed : List (Fin n)}
    (hsmall : Enumerates R small)
    (hremoved : Enumerates (V \ R) removed) :
    Enumerates V (restoreAfter h.representative small removed) ∧
      TwinExpansion G S small
        (restoreAfter h.representative small removed) := by
  have hgo : ∀ (todo done : List (Fin n)),
      removed.Perm (done ++ todo) →
      Enumerates (R ∪ ({v | v ∈ done} : Set (Fin n)))
        (restoreAfter h.representative small done) →
      TwinExpansion G S small (restoreAfter h.representative small done) →
      let final := restoreAfter h.representative
        (restoreAfter h.representative small done) todo
      Enumerates V final ∧ TwinExpansion G S small final := by
    intro todo
    induction todo with
    | nil =>
        intro done hperm hcurrent hexpand
        dsimp
        refine ⟨?_, hexpand⟩
        have hdone : ∀ v, v ∈ done ↔ v ∈ V \ R := by
          intro v
          rw [← hremoved.2]
          simpa using hperm.mem_iff.symm
        refine ⟨hcurrent.1, fun v => (hcurrent.2 v).trans ?_⟩
        simp only [Set.mem_union, Set.mem_setOf_eq]
        rw [hdone]
        constructor
        · rintro (hvR | ⟨hvV, -⟩)
          · exact h.reps_mem hvR
          · exact hvV
        · intro hvV
          by_cases hvR : v ∈ R
          · exact Or.inl hvR
          · exact Or.inr ⟨hvV, hvR⟩
    | cons x xs ih =>
        intro done hperm hcurrent hexpand
        have hxRemoved : x ∈ V \ R := by
          apply (hremoved.2 x).mp
          apply hperm.mem_iff.mpr
          simp
        have hxNotDone : x ∉ done := by
          intro hxDone
          have hnodup := hremoved.1.perm hperm
          rw [List.nodup_append] at hnodup
          exact (hnodup.2.2 x hxDone x (by simp)) rfl
        have hrepR : h.representative x ∈ R :=
          h.representative_mem x hxRemoved.1
        have hrepCurrent : h.representative x ∈
            restoreAfter h.representative small done :=
          (hcurrent.2 _).mpr (Or.inl hrepR)
        have hxCurrent : x ∉ restoreAfter h.representative small done := by
          intro hxc
          rcases (hcurrent.2 x).mp hxc with hxR | hxDone'
          · exact hxRemoved.2 hxR
          · exact hxNotDone hxDone'
        let next := insertAfter (h.representative x) x
          (restoreAfter h.representative small done)
        have hnext : Enumerates
            (R ∪ ({v | v ∈ done ++ [x]} : Set (Fin n))) next := by
          constructor
          · exact nodup_insertAfter hcurrent.1 hrepCurrent hxCurrent
          · intro v
            rw [mem_insertAfter_iff hrepCurrent, hcurrent.2]
            simp only [List.mem_append, List.mem_singleton, Set.mem_union,
              Set.mem_setOf_eq]
            tauto
        have hexpandNext : TwinExpansion G S small next :=
          TwinExpansion.insert hexpand hrepCurrent hxCurrent
            (fun s hs => by
              have heq := Set.ext_iff.mp (h.same_trace x hxRemoved.1) s
              simpa [NeighborhoodComplexity.neighborhoodTrace, hs,
                G.adj_comm] using heq)
        have hperm' : removed.Perm ((done ++ [x]) ++ xs) := by
          exact hperm.trans (by simp [List.append_assoc])
        have hnext' : Enumerates
            (R ∪ ({v | v ∈ done ++ [x]} : Set (Fin n)))
            (restoreAfter h.representative small (done ++ [x])) := by
          simpa [restoreAfter_append, next] using hnext
        have hexpandNext' : TwinExpansion G S small
            (restoreAfter h.representative small (done ++ [x])) := by
          simpa [restoreAfter_append, next] using hexpandNext
        simpa [restoreAfter_append] using
          ih (done ++ [x]) hperm' hnext' hexpandNext'
  have hstart : Enumerates (R ∪ ({v | v ∈ ([] : List (Fin n))} : Set (Fin n)))
      (restoreAfter h.representative small []) := by
    simpa using hsmall
  simpa using hgo removed [] (by simp) hstart (TwinExpansion.refl small)

/-- Canonical increasing restoration order for finite vertex sets. -/
def removedVertices {n : ℕ} (V R : Set (Fin n)) : List (Fin n) :=
  (Set.toFinite (V \ R)).toFinset.toList

theorem removedVertices_enumerates {n : ℕ} (V R : Set (Fin n)) :
    Enumerates (V \ R) (removedVertices V R) := by
  classical
  exact ⟨Finset.nodup_toList _, by simp [removedVertices]⟩

theorem TracePartition.canonical_restore
    {n : ℕ} {G : SimpleGraph (Fin n)} {V S R : Set (Fin n)}
    (h : TracePartition G V S R) {small : List (Fin n)}
    (hsmall : Enumerates R small) :
    Enumerates V
        (restoreAfter h.representative small (removedVertices V R)) ∧
      TwinExpansion G S small
        (restoreAfter h.representative small (removedVertices V R)) :=
  TracePartition.restoreAfter_nonrepresentatives h hsmall
    (removedVertices_enumerates V R)

end

end Lax235315Proofs.Construction.ConcreteReconstruction
