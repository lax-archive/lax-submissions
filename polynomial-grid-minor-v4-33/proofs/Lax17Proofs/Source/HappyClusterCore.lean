import Lax17Proofs.Source.Section44
import Lax17Proofs.Source.LocalSubgraph
import Lax17Proofs.Source.PathOfSets

namespace Lax17Proofs

universe u v w

/-!
# Connected cores of happy Section 4.4 clusters

The splitting proof of Theorem 4.11 represents a cluster only by its vertex
set, so it may retain irrelevant isolated vertices.  The paper subsequently
uses the cluster as a connected Path-of-Sets cluster.  This module removes
those irrelevant vertices: positive weak well-linkedness puts every terminal,
and hence every retained row segment, in one component of the induced graph.
-/

namespace SimpleGraph


namespace Section44

open Finset
open PathPacking

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A reachable vertex of the same-vertex induced graph remains in the
inducing finite set. -/
private theorem reachable_target_mem_inducedOnFinset
    {C : Finset V} {x y : V} (hx : x ∈ C)
    (hxy : (inducedOnFinset G C).Reachable x y) :
    y ∈ C := by
  have walk_target_mem :
      ∀ {a b : V}, (W : (inducedOnFinset G C).Walk a b) →
        a ∈ C → b ∈ C := by
    intro a b W
    induction W with
    | nil =>
        intro ha
        exact ha
    | @cons a z b haz W ih =>
        intro _ha
        exact ih haz.2.2
  exact hxy.elim fun W => walk_target_mem W hx

/-- A happy cluster with positive parameters has a connected subcluster that
contains exactly the same selected row paths and carries the same weak
well-linked terminal set. -/
theorem exists_connected_happy_core
    {S T : Finset V}
    (P : PathPacking G S T) (I : Finset P.Index)
    (C : Finset V) {w D : ℕ}
    (hw : 0 < w) (hD : 0 < D)
    (hhappy : HappyCluster P I C w D) :
    ∃ Ccore : Finset V,
      IsCluster G Ccore ∧
        Ccore ⊆ C ∧
          containedInCluster P I Ccore = containedInCluster P I C ∧
            WeakEdgeWellLinkedIn G Ccore
              (endpointSetInCluster P I Ccore) w := by
  classical
  let J := containedInCluster P I C
  have hJpos : 0 < J.card := hD.trans_le hhappy.2
  obtain ⟨j₀, hj₀J⟩ := Finset.card_pos.mp hJpos
  let t₀ := (P.path j₀).source
  have hj₀C :
      (P.path j₀).vertexSet ⊆ C :=
    ((mem_containedInCluster P I C j₀).1 hj₀J).2
  have ht₀C : t₀ ∈ C := hj₀C (GraphPath.source_mem_vertexSet _)
  let H := inducedOnFinset G C
  let component : H.ConnectedComponent := H.connectedComponentMk t₀
  let Ccore : Finset V :=
    Finset.univ.filter fun v => v ∈ component.supp

  have mem_Ccore_iff (v : V) :
      v ∈ Ccore ↔ v ∈ component.supp := by
    simp [Ccore]

  have hcoreC : Ccore ⊆ C := by
    intro v hv
    have hvSupp : v ∈ component.supp := (mem_Ccore_iff v).1 hv
    have hcomp :
        H.connectedComponentMk v = H.connectedComponentMk t₀ := by
      simpa [component] using hvSupp
    exact reachable_target_mem_inducedOnFinset ht₀C
      (_root_.SimpleGraph.ConnectedComponent.exact hcomp.symm)

  have terminal_mem_core :
      endpointSetInCluster P I C ⊆ Ccore := by
    intro t htT
    rw [mem_Ccore_iff,
      _root_.SimpleGraph.ConnectedComponent.mem_supp_iff]
    by_cases htt : t = t₀
    · simpa [component, htt]
    · have htC :=
        endpointSetInCluster_subset_cluster P I C htT
      have ht₀T :
          t₀ ∈ endpointSetInCluster P I C := by
        apply (mem_endpointSetInCluster P I C t₀).2
        exact Or.inl ⟨j₀, hj₀J, rfl⟩
      have hsingleDisjoint :
          Disjoint ({t₀} : Finset V) ({t} : Finset V) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        have hxt₀ : x = t₀ := by simpa using hx
        have hxt : x = t := by simpa using hy
        exact htt (hxt.symm.trans hxt₀)
      rcases hhappy.1.2
          (show ({t₀} : Finset V) ⊆ endpointSetInCluster P I C by
            simpa using ht₀T)
          (show ({t} : Finset V) ⊆ endpointSetInCluster P I C by
            simpa using htT)
          hsingleDisjoint with
        ⟨L, hLcard, hLstay⟩
      have hLpos : 0 < L.card := by
        rw [hLcard]
        simpa using hw
      let l₀ : L.Index :=
        Classical.choice (Fintype.card_pos_iff.mp (by
          simpa [EdgePathPacking.card] using hLpos))
      let Q := (L.path l₀).inInducedOnFinset (hLstay l₀)
      have hreach : H.Reachable t₀ t := by
        rcases L.connects l₀ with hst | hts
        · have hs : (L.path l₀).source = t₀ := by simpa using hst.1
          have ht : (L.path l₀).target = t := by simpa using hst.2
          have hr := Q.walk.reachable
          change H.Reachable (L.path l₀).source (L.path l₀).target at hr
          rw [hs, ht] at hr
          exact hr
        · have hs : (L.path l₀).source = t := by simpa using hts.1
          have ht : (L.path l₀).target = t₀ := by simpa using hts.2
          have hr := Q.walk.reachable.symm
          change H.Reachable (L.path l₀).target (L.path l₀).source at hr
          rw [hs, ht] at hr
          exact hr
      exact
        (_root_.SimpleGraph.ConnectedComponent.sound hreach).symm.trans
          (by rfl)

  have hcontained :
      containedInCluster P I Ccore =
        containedInCluster P I C := by
    apply Finset.Subset.antisymm
    · intro j hj
      exact (mem_containedInCluster P I C j).2
        ⟨((mem_containedInCluster P I Ccore j).1 hj).1,
          fun v hv => hcoreC
            (((mem_containedInCluster P I Ccore j).1 hj).2 hv)⟩
    · intro j hj
      have hjdata := (mem_containedInCluster P I C j).1 hj
      apply (mem_containedInCluster P I Ccore j).2
      refine ⟨hjdata.1, ?_⟩
      intro v hv
      rw [mem_Ccore_iff,
        _root_.SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hsT :
          (P.path j).source ∈ endpointSetInCluster P I C :=
        (mem_endpointSetInCluster P I C _).2
          (Or.inl ⟨j, hj, rfl⟩)
      have hsCore := terminal_mem_core hsT
      have hsComp :
          H.connectedComponentMk (P.path j).source = component :=
        (mem_Ccore_iff _).1 hsCore
      let Q := (P.path j).inInducedOnFinset hjdata.2
      have hvQ : v ∈ Q.vertexSet := by simpa [Q] using hv
      have hreach :
          H.Reachable (P.path j).source v :=
        (Q.takeUntil hvQ).walk.reachable
      exact
        (_root_.SimpleGraph.ConnectedComponent.sound hreach).symm.trans hsComp

  have hcluster : IsCluster G Ccore := by
    rw [IsCluster]
    let f : component.toSimpleGraph →g
        G.induce {v : V | v ∈ Ccore} :=
      { toFun := fun x => ⟨x.1, (mem_Ccore_iff x.1).2 x.2⟩
        map_rel' := by
          intro x y hxy
          exact hxy.1 }
    apply component.connected_toSimpleGraph.map f
    intro y
    exact ⟨⟨y.1, (mem_Ccore_iff y.1).1 y.2⟩, rfl⟩

  have hterminalEq :
      endpointSetInCluster P I Ccore =
        endpointSetInCluster P I C := by
    rw [endpointSetInCluster_eq_source_union_target,
      endpointSetInCluster_eq_source_union_target]
    unfold sourceEndpointSetInCluster targetEndpointSetInCluster
    rw [hcontained]

  refine ⟨Ccore, hcluster, hcoreC, hcontained, ?_⟩
  rw [hterminalEq]
  constructor
  · exact terminal_mem_core
  · intro A B hA hB hdisj
    rcases hhappy.1.2 hA hB hdisj with ⟨L, hcard, hstay⟩
    refine ⟨L, hcard, ?_⟩
    intro l v hv
    rw [mem_Ccore_iff,
      _root_.SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hsT :
        (L.path l).source ∈ endpointSetInCluster P I C := by
      rcases L.connects l with h | h
      · exact hA h.1
      · exact hB h.1
    have hsCore := terminal_mem_core hsT
    have hsComp :
        H.connectedComponentMk (L.path l).source = component :=
      (mem_Ccore_iff _).1 hsCore
    let Q := (L.path l).inInducedOnFinset (hstay l)
    have hvQ : v ∈ Q.vertexSet := by simpa [Q] using hv
    have hreach : H.Reachable (L.path l).source v :=
      (Q.takeUntil hvQ).walk.reachable
    exact
      (_root_.SimpleGraph.ConnectedComponent.sound hreach).symm.trans hsComp

end Section44

end SimpleGraph

end Lax17Proofs
