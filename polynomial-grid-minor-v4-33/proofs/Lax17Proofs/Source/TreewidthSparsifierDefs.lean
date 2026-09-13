import Lax17Proofs.Source.FlowDefs
import Lax17Proofs.Source.LocalSubgraph
import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.Treewidth
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Axiom-free definitions for `treewidth-sparsifier.pdf`

This file contains the shared definitions used by the contract statements and
by the self-contained Section 2 proof work.  It deliberately contains no paper
theorem axioms.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


open scoped Classical

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Topological minors -/

/-- Internal vertices of a path: all vertices on the path except the two
endpoints. -/
noncomputable def pathInternalVertexSet {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} (P : GraphPath G) : Finset V :=
  (P.vertexSet.erase P.source).erase P.target

/-- A vertex in the drop-last part of a nontrivial path is either the source
endpoint or an internal vertex of the original path. -/
theorem mem_dropLast_vertexSet_eq_source_or_mem_internal
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    (P : GraphPath G) (h : P.source ≠ P.target) {v : V}
    (hv : v ∈ P.dropLast.vertexSet) :
    v = P.source ∨ v ∈ pathInternalVertexSet P := by
  classical
  by_cases hvsource : v = P.source
  · exact Or.inl hvsource
  · right
    have hvVertex : v ∈ P.vertexSet :=
      P.dropLast_vertexSet_subset hv
    have hvtarget : v ≠ P.target := by
      intro hvt
      exact P.target_not_mem_dropLast_vertexSet h (by simpa [hvt] using hv)
    simp [pathInternalVertexSet, hvsource, hvtarget, hvVertex]

/-- A subdivision-style model witnessing that `H` is a topological minor of
`G`.

Each vertex of `H` is mapped injectively to a branch vertex of `G`; each edge
of `H` is mapped to a path in `G` between the corresponding branch vertices;
edge paths are internally disjoint from each other and from all unrelated
branch vertices. -/
structure TopologicalMinorModel {W : Type u} [DecidableEq W]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) where
  /-- Branch vertex in the host for each vertex of the pattern graph. -/
  branchVertex : W → V
  /-- Distinct pattern vertices have distinct branch vertices. -/
  branch_injective : Function.Injective branchVertex
  /-- An arbitrary orientation of each pattern edge. -/
  edgeSource : H.edgeSet → W
  /-- The target endpoint in the chosen orientation of each pattern edge. -/
  edgeTarget : H.edgeSet → W
  /-- The chosen endpoints are adjacent in the pattern. -/
  edge_adj : ∀ e : H.edgeSet, H.Adj (edgeSource e) (edgeTarget e)
  /-- The chosen endpoints represent the underlying unordered edge. -/
  edge_eq : ∀ e : H.edgeSet, s(edgeSource e, edgeTarget e) = (e : Sym2 W)
  /-- The host path realizing a pattern edge. -/
  edgePath : (e : H.edgeSet) → GraphPath G
  /-- The realizing path starts at the source branch vertex. -/
  edgePath_source :
    ∀ e : H.edgeSet, (edgePath e).source = branchVertex (edgeSource e)
  /-- The realizing path ends at the target branch vertex. -/
  edgePath_target :
    ∀ e : H.edgeSet, (edgePath e).target = branchVertex (edgeTarget e)
  /-- Internal vertices of a realizing path avoid all unrelated branch
  vertices. -/
  edgePath_internal_disjoint_branches :
    ∀ (e : H.edgeSet) (z : W),
      z ≠ edgeSource e →
        z ≠ edgeTarget e →
          branchVertex z ∉ pathInternalVertexSet (edgePath e)
  /-- Distinct realizing paths have disjoint internal vertices. -/
  edgePath_pairwise_internal_disjoint :
    ∀ ⦃e f : H.edgeSet⦄,
      e ≠ f →
        Disjoint
          (pathInternalVertexSet (edgePath e))
          (pathInternalVertexSet (edgePath f))

namespace TopologicalMinorModel

variable {V₀ W : Type u} [DecidableEq V₀] [Fintype W] [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V₀}

/-- The branch vertices used by a topological-minor model. -/
noncomputable def branchVertexSet
    (M : TopologicalMinorModel H G) : Finset V₀ :=
  (Finset.univ : Finset W).image M.branchVertex

/-- The vertices lying on one of the realizing paths of a topological-minor
model. -/
noncomputable def edgeVertexSet
    (M : TopologicalMinorModel H G) : Finset V₀ :=
  (Finset.univ : Finset H.edgeSet).biUnion fun e => (M.edgePath e).vertexSet

/-- The full vertex support of a topological-minor model. -/
noncomputable def vertexSupport
    (M : TopologicalMinorModel H G) : Finset V₀ :=
  M.branchVertexSet ∪ M.edgeVertexSet

/-- The edge support of a topological-minor model: all host edges used by the
realizing paths. -/
noncomputable def edgeSupport
    (M : TopologicalMinorModel H G) : Finset (Sym2 V₀) :=
  (Finset.univ : Finset H.edgeSet).biUnion fun e => (M.edgePath e).edgeSet

/-- The same-vertex support graph of a topological-minor model. -/
noncomputable def supportGraph
    (M : TopologicalMinorModel H G) : _root_.SimpleGraph V₀ :=
  _root_.SimpleGraph.fromEdgeSet (M.edgeSupport : Set (Sym2 V₀))

/-- Every support edge of a topological-minor model is an edge of the host
graph. -/
theorem edgeSupport_subset_host
    (M : TopologicalMinorModel H G) :
    (M.edgeSupport : Set (Sym2 V₀)) ⊆ G.edgeSet := by
  intro e he
  rcases Finset.mem_biUnion.mp he with ⟨f, _hf, hef⟩
  exact (M.edgePath f).edgeSet_subset_edgeSet hef

/-- The support graph of a topological-minor model is a spanning subgraph of
the host graph. -/
theorem supportGraph_le
    (M : TopologicalMinorModel H G) :
    M.supportGraph ≤ G := by
  intro u v huv
  rw [supportGraph, _root_.SimpleGraph.fromEdgeSet_adj] at huv
  exact M.edgeSupport_subset_host huv.1

/-- Each realizing path uses only edges of the support graph. -/
theorem edgePath_edgeSet_subset_supportGraph
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    ((M.edgePath e).edgeSet : Set (Sym2 V₀)) ⊆ M.supportGraph.edgeSet := by
  intro f hf
  rw [supportGraph, _root_.SimpleGraph.edgeSet_fromEdgeSet]
  have hfG : f ∈ G.edgeSet :=
    (M.edgePath e).edgeSet_subset_edgeSet (by simpa using hf)
  refine ⟨?_, G.edgeSet_subset_compl_diagSet hfG⟩
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, by simpa using hf⟩

/-- The realizing path for a pattern edge, viewed inside the model's support
graph. -/
noncomputable def edgePathInSupportGraph
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    GraphPath M.supportGraph :=
  (M.edgePath e).transfer M.supportGraph (by
    intro f hf
    exact M.edgePath_edgeSet_subset_supportGraph e (by
      simpa [GraphPath.edgeSet] using hf))

@[simp] theorem edgePathInSupportGraph_source
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    (M.edgePathInSupportGraph e).source = (M.edgePath e).source := rfl

@[simp] theorem edgePathInSupportGraph_target
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    (M.edgePathInSupportGraph e).target = (M.edgePath e).target := rfl

@[simp] theorem edgePathInSupportGraph_vertexSet
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    (M.edgePathInSupportGraph e).vertexSet = (M.edgePath e).vertexSet := by
  classical
  simp [edgePathInSupportGraph]

@[simp] theorem edgePathInSupportGraph_edgeSet
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    (M.edgePathInSupportGraph e).edgeSet = (M.edgePath e).edgeSet := by
  classical
  simp [edgePathInSupportGraph]

/-- A realized pattern edge has distinct endpoints in the support graph. -/
theorem edgePathInSupportGraph_source_ne_target
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    (M.edgePathInSupportGraph e).source ≠
      (M.edgePathInSupportGraph e).target := by
  intro h
  have hbranch :
      M.branchVertex (M.edgeSource e) =
        M.branchVertex (M.edgeTarget e) := by
    simpa [M.edgePath_source e, M.edgePath_target e] using h
  exact (H.ne_of_adj (M.edge_adj e)) (M.branch_injective hbranch)

/-- Branch set obtained by allocating every realized edge path to its chosen
source endpoint, with the final target vertex removed. -/
noncomputable def orientedBranchSet
    (M : TopologicalMinorModel H G) (x : W) : Finset V₀ :=
  {M.branchVertex x} ∪
    (Finset.univ : Finset H.edgeSet).biUnion fun e =>
      if M.edgeSource e = x then
        (M.edgePathInSupportGraph e).dropLast.vertexSet
      else
        ∅

@[simp] theorem branchVertex_mem_orientedBranchSet
    (M : TopologicalMinorModel H G) (x : W) :
    M.branchVertex x ∈ M.orientedBranchSet x := by
  classical
  simp [orientedBranchSet]

theorem mem_orientedBranchSet_iff
    (M : TopologicalMinorModel H G) {x : W} {v : V₀} :
    v ∈ M.orientedBranchSet x ↔
      v = M.branchVertex x ∨
        ∃ e : H.edgeSet,
          M.edgeSource e = x ∧
            v ∈ (M.edgePathInSupportGraph e).dropLast.vertexSet := by
  classical
  constructor
  · intro hv
    rw [orientedBranchSet] at hv
    rw [Finset.mem_union] at hv
    rcases hv with hv | hv
    · left
      simpa using hv
    · rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨e, _he, hvif⟩
      by_cases hsource : M.edgeSource e = x
      · right
        exact ⟨e, hsource, by simpa [hsource] using hvif⟩
      · simp [hsource] at hvif
  · intro hv
    rcases hv with hv | hv
    · rw [orientedBranchSet]
      exact Finset.mem_union_left _ (by simp [hv])
    · rcases hv with ⟨e, hsource, hvpath⟩
      rw [orientedBranchSet]
      exact Finset.mem_union_right _ <|
        Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, by
          simpa [hsource] using hvpath⟩

/-- The penultimate vertex of a realized edge path belongs to the branch set
of its chosen source endpoint. -/
theorem edge_penultimate_mem_orientedBranchSet
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    (M.edgePathInSupportGraph e).penultimate ∈
      M.orientedBranchSet (M.edgeSource e) := by
  classical
  have hmem :
      (M.edgePathInSupportGraph e).penultimate ∈
        (M.edgePathInSupportGraph e).dropLast.vertexSet := by
    simpa using
      GraphPath.target_mem_vertexSet ((M.edgePathInSupportGraph e).dropLast)
  rw [orientedBranchSet]
  exact Finset.mem_union_right _ <|
    Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, by
      simpa using hmem⟩

/-- Each source-owned oriented branch set is connected in the support graph. -/
theorem orientedBranchSet_connected
    (M : TopologicalMinorModel H G) (x : W) :
    (M.supportGraph.induce {v : V₀ | v ∈ M.orientedBranchSet x}).Connected := by
  classical
  refine M.supportGraph.induce_connected_of_patches (M.branchVertex x)
    (M.branchVertex_mem_orientedBranchSet x) ?_
  intro v hv
  change v ∈ M.orientedBranchSet x at hv
  rw [orientedBranchSet] at hv
  rw [Finset.mem_union] at hv
  rcases hv with hv | hv
  · have hv_eq : v = M.branchVertex x := by
      simpa using hv
    subst v
    refine ⟨({M.branchVertex x} : Set V₀), ?_, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Set.mem_singleton_iff] at hz
      simp [hz, M.branchVertex_mem_orientedBranchSet x]
    · simp
    · simp
    · exact _root_.SimpleGraph.Reachable.refl _
  · rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨e, _he, hvif⟩
    by_cases hsource : M.edgeSource e = x
    · have hvpath :
          v ∈ (M.edgePathInSupportGraph e).dropLast.vertexSet := by
        simpa [hsource] using hvif
      let S : Set V₀ :=
        {z : V₀ | z ∈ (M.edgePathInSupportGraph e).dropLast.vertexSet}
      refine ⟨S, ?_, ?_, hvpath, ?_⟩
      · intro z hz
        rw [orientedBranchSet]
        exact Finset.mem_union_right _ <|
          Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, by
            simpa [hsource] using hz⟩
      · have hpathSource :
            (M.edgePathInSupportGraph e).dropLast.source =
              M.branchVertex x := by
          rw [GraphPath.dropLast_source, edgePathInSupportGraph_source,
            M.edgePath_source e, hsource]
        simpa [S, ← hpathSource] using
          GraphPath.source_mem_vertexSet ((M.edgePathInSupportGraph e).dropLast)
      · have hconn :=
          GraphPath.connected_induce_vertexSet
            ((M.edgePathInSupportGraph e).dropLast)
        exact hconn ⟨M.branchVertex x, by
          have hpathSource :
              (M.edgePathInSupportGraph e).dropLast.source =
                M.branchVertex x := by
            rw [GraphPath.dropLast_source, edgePathInSupportGraph_source,
              M.edgePath_source e, hsource]
          simpa [S, ← hpathSource] using
            GraphPath.source_mem_vertexSet
              ((M.edgePathInSupportGraph e).dropLast)⟩
          ⟨v, hvpath⟩
    · simp [hsource] at hvif

/-- The source-owned oriented branch sets witness adjacency for each pattern
edge in the support graph. -/
theorem orientedBranchSet_adjacent
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    ∃ u ∈ M.orientedBranchSet (M.edgeSource e),
      ∃ v ∈ M.orientedBranchSet (M.edgeTarget e),
        M.supportGraph.Adj u v := by
  refine ⟨(M.edgePathInSupportGraph e).penultimate,
    M.edge_penultimate_mem_orientedBranchSet e,
    M.branchVertex (M.edgeTarget e),
    M.branchVertex_mem_orientedBranchSet (M.edgeTarget e), ?_⟩
  have hadj :=
    (M.edgePathInSupportGraph e).penultimate_adj_target
      (M.edgePathInSupportGraph_source_ne_target e)
  simpa [edgePathInSupportGraph_target, M.edgePath_target e] using hadj

@[simp] theorem pathInternalVertexSet_edgePathInSupportGraph
    (M : TopologicalMinorModel H G) (e : H.edgeSet) :
    pathInternalVertexSet (M.edgePathInSupportGraph e) =
      pathInternalVertexSet (M.edgePath e) := by
  classical
  simp [pathInternalVertexSet]

/-- A branch vertex not equal to the chosen source endpoint of a realized edge
does not lie in that edge's source-owned drop-last path. -/
theorem branchVertex_not_mem_dropLast_of_ne_source
    (M : TopologicalMinorModel H G) (e : H.edgeSet) {z : W}
    (hz : z ≠ M.edgeSource e) :
    M.branchVertex z ∉ (M.edgePathInSupportGraph e).dropLast.vertexSet := by
  intro hv
  rcases
      mem_dropLast_vertexSet_eq_source_or_mem_internal
        (M.edgePathInSupportGraph e)
        (M.edgePathInSupportGraph_source_ne_target e) hv with
    hvSource | hvInternal
  · have hbranch :
        M.branchVertex z = M.branchVertex (M.edgeSource e) := by
      simpa [edgePathInSupportGraph_source, M.edgePath_source e] using hvSource
    exact hz (M.branch_injective hbranch)
  · have hvInternal' :
        M.branchVertex z ∈ pathInternalVertexSet (M.edgePath e) := by
      simpa using hvInternal
    by_cases hztarget : z = M.edgeTarget e
    · subst z
      simpa [pathInternalVertexSet, M.edgePath_target e] using hvInternal'
    · exact M.edgePath_internal_disjoint_branches e z hz hztarget hvInternal'

/-- Source-owned drop-last paths for edges with different source endpoints are
disjoint. -/
theorem dropLast_disjoint_of_edgeSource_ne
    (M : TopologicalMinorModel H G) {e f : H.edgeSet}
    (hsource : M.edgeSource e ≠ M.edgeSource f) :
    Disjoint
      (M.edgePathInSupportGraph e).dropLast.vertexSet
      (M.edgePathInSupportGraph f).dropLast.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hve hvf
  rcases
      mem_dropLast_vertexSet_eq_source_or_mem_internal
        (M.edgePathInSupportGraph e)
        (M.edgePathInSupportGraph_source_ne_target e) hve with
    hveSource | hveInternal
  · have hvf' :
        M.branchVertex (M.edgeSource e) ∈
          (M.edgePathInSupportGraph f).dropLast.vertexSet := by
      simpa [hveSource, edgePathInSupportGraph_source, M.edgePath_source e]
        using hvf
    exact M.branchVertex_not_mem_dropLast_of_ne_source f hsource hvf'
  · rcases
        mem_dropLast_vertexSet_eq_source_or_mem_internal
          (M.edgePathInSupportGraph f)
          (M.edgePathInSupportGraph_source_ne_target f) hvf with
      hvfSource | hvfInternal
    · have hve' :
          M.branchVertex (M.edgeSource f) ∈
            (M.edgePathInSupportGraph e).dropLast.vertexSet := by
        simpa [hvfSource, edgePathInSupportGraph_source, M.edgePath_source f]
          using hve
      exact M.branchVertex_not_mem_dropLast_of_ne_source e hsource.symm hve'
    · have hef : e ≠ f := by
        intro hef
        exact hsource (by rw [hef])
      have hveInternal' :
          v ∈ pathInternalVertexSet (M.edgePath e) := by
        simpa using hveInternal
      have hvfInternal' :
          v ∈ pathInternalVertexSet (M.edgePath f) := by
        simpa using hvfInternal
      exact Finset.disjoint_left.mp
        (M.edgePath_pairwise_internal_disjoint hef)
        hveInternal' hvfInternal'

/-- Distinct source-owned oriented branch sets of a topological-minor model
are disjoint. -/
theorem orientedBranchSet_disjoint
    (M : TopologicalMinorModel H G) {x y : W} (hxy : x ≠ y) :
    Disjoint (M.orientedBranchSet x) (M.orientedBranchSet y) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvx hvy
  have hvx' := (M.mem_orientedBranchSet_iff).1 hvx
  have hvy' := (M.mem_orientedBranchSet_iff).1 hvy
  rcases hvx' with hvxBranch | hvxPath
  · rcases hvy' with hvyBranch | hvyPath
    · have hbranch : M.branchVertex x = M.branchVertex y :=
        hvxBranch.symm.trans hvyBranch
      exact hxy (M.branch_injective hbranch)
    · rcases hvyPath with ⟨f, hfsource, hvf⟩
      have hx_ne_source : x ≠ M.edgeSource f := by
        intro hxsource
        exact hxy (hxsource.trans hfsource)
      exact M.branchVertex_not_mem_dropLast_of_ne_source f hx_ne_source
        (by simpa [hvxBranch] using hvf)
  · rcases hvxPath with ⟨e, hesource, hve⟩
    rcases hvy' with hvyBranch | hvyPath
    · have hy_ne_source : y ≠ M.edgeSource e := by
        intro hysource
        exact hxy (hesource.symm.trans hysource.symm)
      exact M.branchVertex_not_mem_dropLast_of_ne_source e hy_ne_source
        (by simpa [hvyBranch] using hve)
    · rcases hvyPath with ⟨f, hfsource, hvf⟩
      have hsource_ne : M.edgeSource e ≠ M.edgeSource f := by
        intro hsource
        exact hxy (hesource.symm.trans (hsource.trans hfsource))
      exact Finset.disjoint_left.mp
        (M.dropLast_disjoint_of_edgeSource_ne hsource_ne) hve hvf

/-- A topological-minor model gives a minor model of the pattern graph in the
same-vertex support graph of the subdivision paths. -/
noncomputable def toMinorModelSupportGraph
    (M : TopologicalMinorModel H G) :
    MinorModel H M.supportGraph where
  branchSet := M.orientedBranchSet
  branch_nonempty := by
    intro x
    exact ⟨M.branchVertex x, M.branchVertex_mem_orientedBranchSet x⟩
  branch_connected := M.orientedBranchSet_connected
  branch_disjoint := by
    intro x y hxy
    exact M.orientedBranchSet_disjoint hxy
  adjacent := by
    intro x y hxy
    have hEdge : s(x, y) ∈ H.edgeSet := by
      simpa [_root_.SimpleGraph.mem_edgeSet] using hxy
    let e : H.edgeSet := ⟨s(x, y), hEdge⟩
    have heq : s(M.edgeSource e, M.edgeTarget e) = s(x, y) := by
      simpa [e] using M.edge_eq e
    rw [Sym2.eq_iff] at heq
    rcases heq with hforward | hbackward
    · rcases hforward with ⟨hsource, htarget⟩
      rcases M.orientedBranchSet_adjacent e with
        ⟨u, hu, v, hv, huv⟩
      refine ⟨u, ?_, v, ?_, huv⟩
      · simpa [hsource] using hu
      · simpa [htarget] using hv
    · rcases hbackward with ⟨hsource, htarget⟩
      rcases M.orientedBranchSet_adjacent e with
        ⟨u, hu, v, hv, huv⟩
      refine ⟨v, ?_, u, ?_, M.supportGraph.symm huv⟩
      · simpa [htarget] using hv
      · simpa [hsource] using hu

/-- A topological-minor model contains the pattern as a graph minor of its
same-vertex support graph. -/
theorem isMinor_supportGraph
    (M : TopologicalMinorModel H G) :
    IsMinor H M.supportGraph :=
  ⟨M.toMinorModelSupportGraph⟩

end TopologicalMinorModel

/-- `H` is a topological minor of `G`. -/
def IsTopologicalMinor {W : Type u} [DecidableEq W]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) : Prop :=
  Nonempty (TopologicalMinorModel H G)

/-- A topological-minor model that identifies a specified terminal set in the
host with a specified terminal set in the pattern graph. -/
structure TerminalRespectingTopologicalMinor {W : Type u} [DecidableEq W]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V)
    (Ahost : Finset V) (Apattern : Finset W) where
  /-- The underlying topological-minor model. -/
  model : TopologicalMinorModel H G
  /-- Pattern terminals map into the named host terminal set. -/
  terminal_image_subset :
    ∀ ⦃x : W⦄, x ∈ Apattern → model.branchVertex x ∈ Ahost
  /-- Every named host terminal is represented by a pattern terminal. -/
  terminal_image_surjective :
    ∀ ⦃a : V⦄, a ∈ Ahost →
      ∃ x ∈ Apattern, model.branchVertex x = a

/-! ## Routing and small two-pair sparsifiers -/

/-- A pair of terminal sets is routable when a perfect node-disjoint path
packing connects one side to the other. -/
def RoutableIn (G : _root_.SimpleGraph V) (S T : Finset V) : Prop :=
  Nonempty (PerfectPathPacking G S T)

/-- The paper's `τ(G)`: the number of vertices whose degree is more than two. -/
noncomputable def branchVertexCount
    (G : _root_.SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter fun v : V => ¬ DegreeAtMost G v 2).card

/-- The graph obtained as the union of two path packings. -/
noncomputable def twoPackingUnionGraph
    {S₁ T₁ S₂ T₂ : Finset V} {G : _root_.SimpleGraph V}
    (P : PerfectPathPacking G S₁ T₁) (Q : PerfectPathPacking G S₂ T₂) :
    _root_.SimpleGraph V :=
  P.toPathPacking.spanningGraph ⊔ Q.toPathPacking.spanningGraph

/-- The conclusion of Theorem 1.3: two routings whose union has few vertices
of degree more than two. -/
def TwoPairRoutingSparsifier
    (G : _root_.SimpleGraph V)
    (S₁ T₁ S₂ T₂ : Finset V) (k₁ : ℕ) : Prop :=
  ∃ (P : PerfectPathPacking G S₁ T₁)
    (Q : PerfectPathPacking G S₂ T₂),
      branchVertexCount (twoPackingUnionGraph P Q) ≤ 8 * k₁ ^ 4 + 8 * k₁

end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
