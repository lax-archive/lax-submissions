import Lax68.SeriesParallelPlanar
import Mathlib

set_option autoImplicit false
namespace Lax303502Proofs
open Lax68.SeriesParallel

theorem support_union {V : Type*} (G H : SimpleGraph V) :
    (G ⊔ H).support = G.support ∪ H.support := by
  ext v
  simp only [SimpleGraph.mem_support, SimpleGraph.sup_adj, Set.mem_union]
  exact exists_or

theorem edge_support {V : Type*} {s t : V} (hst : s ≠ t) :
    (edgeGraph s t).support = {s, t} := by
  ext v
  simp only [SimpleGraph.mem_support, edgeGraph, SimpleGraph.fromRel_adj,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, _, (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨_, rfl⟩ | ⟨_, rfl⟩)⟩ <;> simp
  · rintro (rfl | rfl)
    · exact ⟨t, hst, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨s, hst.symm, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩

theorem twoTerminal_support {V : Type*} {G : SimpleGraph V} {s t : V}
    (h : TwoTerminal G s t) :
    s ≠ t ∧ s ∈ G.support ∧ t ∈ G.support ∧ G.support.Finite := by
  induction h with
  | edge s t hst =>
    rw [edge_support hst]
    exact ⟨hst, by simp, by simp, Set.toFinite _⟩
  | @series G H s m t hG hH meet ihG ihH =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hst
      have hsm := meet s ihG.2.1 (hst ▸ ihH.2.2.1)
      exact ihG.1 hsm
    · rw [support_union]; exact Or.inl ihG.2.1
    · rw [support_union]; exact Or.inr ihH.2.2.1
    · rw [support_union]; exact ihG.2.2.2.union ihH.2.2.2
  | @parallel G H s t hG hH meet ihG ihH =>
    refine ⟨ihG.1, ?_, ?_, ?_⟩
    · rw [support_union]; exact Or.inl ihG.2.1
    · rw [support_union]; exact Or.inl ihG.2.2.1
    · rw [support_union]; exact ihG.2.2.2.union ihH.2.2.2

theorem seriesParallel_finite {V : Type*} {G : SimpleGraph V}
    (hG : IsSeriesParallel G) : Finite V := by
  obtain ⟨s, t, h, hs⟩ := hG
  have hf := (twoTerminal_support h).2.2.2
  rw [hs] at hf
  exact Set.finite_univ_iff.mp hf

end Lax303502Proofs
