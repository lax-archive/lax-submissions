import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Localizing a well-linked terminal set to one connected component

A nonempty terminal set that is scaled edge-well-linked in the whole graph is
contained in one connected component.  The same cut inequalities then hold in
that component.
-/

namespace SimpleGraph


namespace Section46

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A nonempty terminal set that is scaled edge-well-linked in the whole graph
is scaled edge-well-linked in a connected-component cluster containing all
terminals.  The last field records that this cluster has no outgoing edge. -/
theorem exists_closed_cluster_scaledEdgeWellLinkedIn_of_univ
    {T : Finset V} {alphaNum alphaDen : ℕ}
    (hT : T.Nonempty)
    (hwell : ScaledEdgeWellLinkedIn G Finset.univ T alphaNum alphaDen) :
    ∃ C : Finset V,
      IsCluster G C ∧ T ⊆ C ∧
        ScaledEdgeWellLinkedIn G C T alphaNum alphaDen ∧
          Section44.edgeBoundary G C (Finset.univ \ C) = ∅ := by
  classical
  obtain ⟨t₀, ht₀T⟩ := hT
  let component : G.ConnectedComponent := G.connectedComponentMk t₀
  let C : Finset V := Finset.univ.filter fun v => v ∈ component.supp

  have mem_C_iff (v : V) : v ∈ C ↔ v ∈ component.supp := by
    simp [C]

  have ht₀C : t₀ ∈ C := by
    rw [mem_C_iff]
    exact _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem

  have component_closed {x y : V} (hx : x ∈ C) (hxy : G.Adj x y) : y ∈ C := by
    rw [mem_C_iff] at hx ⊢
    exact component.mem_supp_of_adj_mem_supp hx hxy

  have hcluster : IsCluster G C := by
    rw [IsCluster]
    have hset : {v : V | v ∈ C} = component.supp := by
      ext v
      exact mem_C_iff v
    rw [hset]
    exact component.connected_toSimpleGraph

  have hboundary_component :
      Section44.edgeBoundary G C (Finset.univ \ C) = ∅ := by
    ext e
    constructor
    · intro he
      rcases ((Section44.mem_edgeBoundary (G := G) C (Finset.univ \ C) e).1 he) with
        ⟨heG, x, hxC, y, hyC, rfl⟩
      have hxy : G.Adj x y := by simpa using heG
      exfalso
      exact (Finset.mem_sdiff.mp hyC).2 (component_closed hxC hxy)
    · intro he
      simp at he

  have hTC : T ⊆ C := by
    intro t htT
    by_contra htC
    have htComp : t ∈ Finset.univ \ C := by simp [htC]
    have hcut := hwell.2.2.2 C (Finset.univ \ C)
      (by simp) (by simp) (by simp) (by
        rw [Finset.disjoint_left]
        intro v hvC hvDiff
        exact (Finset.mem_sdiff.mp hvDiff).2 hvC)
    rw [hboundary_component] at hcut
    have hleft : 0 < (C ∩ T).card := by
      exact Finset.card_pos.mpr ⟨t₀, Finset.mem_inter.mpr ⟨ht₀C, ht₀T⟩⟩
    have hright : 0 < ((Finset.univ \ C) ∩ T).card := by
      exact Finset.card_pos.mpr ⟨t, Finset.mem_inter.mpr ⟨htComp, htT⟩⟩
    have hproduct :
        0 < alphaNum * min (C ∩ T).card ((Finset.univ \ C) ∩ T).card := by
      exact Nat.mul_pos hwell.1 (by omega)
    simp only [Finset.card_empty, Nat.mul_zero] at hcut
    exact (Nat.not_lt_of_ge hcut) hproduct

  have boundary_partition_eq {X Y : Finset V}
      (hXC : X ⊆ C) (hYC : Y ⊆ C)
      (hcover : X ∪ Y = C) (hdisj : Disjoint X Y) :
      Section44.edgeBoundary G X (Finset.univ \ X) =
        Section44.edgeBoundary G X Y := by
    ext e
    constructor
    · intro he
      rcases ((Section44.mem_edgeBoundary (G := G) X (Finset.univ \ X) e).1 he) with
        ⟨heG, x, hxX, y, hyX, rfl⟩
      have hxy : G.Adj x y := by simpa using heG
      have hyC : y ∈ C := component_closed (hXC hxX) hxy
      have hyXY : y ∈ X ∪ Y := by simpa [hcover] using hyC
      have hyY : y ∈ Y := by
        rcases Finset.mem_union.mp hyXY with hyX' | hyY
        · exact False.elim ((Finset.mem_sdiff.mp hyX).2 hyX')
        · exact hyY
      exact (Section44.mem_edgeBoundary (G := G) X Y s(x, y)).2
        ⟨heG, x, hxX, y, hyY, rfl⟩
    · intro he
      rcases ((Section44.mem_edgeBoundary (G := G) X Y e).1 he) with
        ⟨heG, x, hxX, y, hyY, rfl⟩
      have hyNotX : y ∉ X := fun hyX => Finset.disjoint_left.mp hdisj hyX hyY
      exact (Section44.mem_edgeBoundary (G := G) X (Finset.univ \ X) s(x, y)).2
        ⟨heG, x, hxX, y, by simp [hyNotX], rfl⟩

  refine ⟨C, hcluster, hTC, ?_, hboundary_component⟩
  refine ⟨hwell.1, hwell.2.1, hTC, ?_⟩
  intro X Y hXC hYC hcover hdisj
  have hglobal := hwell.2.2.2 X (Finset.univ \ X)
    (by simp) (by simp) (by simp) (by
      rw [Finset.disjoint_left]
      intro v hvX hvDiff
      exact (Finset.mem_sdiff.mp hvDiff).2 hvX)
  have hterminal_complement :
      (Finset.univ \ X) ∩ T = Y ∩ T := by
    ext t
    constructor
    · intro ht
      have htNotX : t ∉ X := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ht).1).2
      have htC : t ∈ C := hTC (Finset.mem_inter.mp ht).2
      have htXY : t ∈ X ∪ Y := by simpa [hcover] using htC
      rcases Finset.mem_union.mp htXY with htX | htY
      · exact False.elim (htNotX htX)
      · exact Finset.mem_inter.mpr ⟨htY, (Finset.mem_inter.mp ht).2⟩
    · intro ht
      have htNotX : t ∉ X := fun htX =>
        Finset.disjoint_left.mp hdisj htX (Finset.mem_inter.mp ht).1
      exact Finset.mem_inter.mpr
        ⟨by simp [htNotX], (Finset.mem_inter.mp ht).2⟩
  rw [hterminal_complement, boundary_partition_eq hXC hYC hcover hdisj] at hglobal
  exact hglobal

/-- Projection of the closed-component form retaining the original public
interface. -/
theorem exists_cluster_scaledEdgeWellLinkedIn_of_univ
    {T : Finset V} {alphaNum alphaDen : ℕ}
    (hT : T.Nonempty)
    (hwell : ScaledEdgeWellLinkedIn G Finset.univ T alphaNum alphaDen) :
    ∃ C : Finset V,
      IsCluster G C ∧ T ⊆ C ∧
        ScaledEdgeWellLinkedIn G C T alphaNum alphaDen := by
  obtain ⟨C, hC, hTC, hwellC, _hclosed⟩ :=
    exists_closed_cluster_scaledEdgeWellLinkedIn_of_univ hT hwell
  exact ⟨C, hC, hTC, hwellC⟩

end Section46

end SimpleGraph

end Lax17Proofs
