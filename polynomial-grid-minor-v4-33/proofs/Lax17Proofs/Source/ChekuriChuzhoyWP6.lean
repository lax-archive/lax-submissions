import Lax17Proofs.Source.ChekuriChuzhoyTheorem31Sharp
import Lax17Proofs.Source.ChekuriChuzhoyStitchedRows
import Lax17Proofs.Source.PathOfSetsGrid

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy strong path-of-sets to grid

This module packages Appendix B.1 and the sharp Theorem 3.1 count into the
cluster-local interface used by Corollary 3.2.  The localization is carried
out on the genuine induced subtype graph, so the connectedness hypothesis is
exactly `IsCluster G C`; paths, bridges, and grid minors are then transported
back along the canonical induced-subgraph embedding.
-/

namespace SimpleGraph

namespace PathPacking


variable {V : Type u} {W : Type v}
variable [DecidableEq V] [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
variable {S T : Finset V}

/-- Map a path packing along a graph embedding. -/
noncomputable def mapEmbedding (P : PathPacking G S T) (φ : G ↪g H) :
    PathPacking H (S.map φ.toEmbedding) (T.map φ.toEmbedding) where
  Index := P.Index
  path := fun i => (P.path i).mapEmbedding φ
  connects := by
    intro i
    rcases P.connects i with h | h
    · exact Or.inl ⟨Finset.mem_map.mpr ⟨_, h.1, rfl⟩,
        Finset.mem_map.mpr ⟨_, h.2, rfl⟩⟩
    · exact Or.inr ⟨Finset.mem_map.mpr ⟨_, h.1, rfl⟩,
        Finset.mem_map.mpr ⟨_, h.2, rfl⟩⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, GraphPath.mapEmbedding_vertexSet,
      GraphPath.mapEmbedding_vertexSet, Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_image.mp hxi with ⟨a, hai, hax⟩
    rcases Finset.mem_image.mp hxj with ⟨b, hbj, hbx⟩
    have hab : a = b := φ.injective (hax.trans hbx.symm)
    exact Finset.disjoint_left.mp (P.node_disjoint hij) hai (by
      simpa [hab] using hbj)

@[simp] theorem mapEmbedding_card (P : PathPacking G S T) (φ : G ↪g H) :
    (P.mapEmbedding φ).card = P.card := rfl

@[simp] theorem mapEmbedding_path_vertexSet
    (P : PathPacking G S T) (φ : G ↪g H)
    (i : (P.mapEmbedding φ).Index) :
    ((P.mapEmbedding φ).path i).vertexSet =
      (P.path i).vertexSet.image φ.toEmbedding := by
  simp [mapEmbedding]

@[simp] theorem mapEmbedding_vertexSet
    (P : PathPacking G S T) (φ : G ↪g H) :
    (P.mapEmbedding φ).vertexSet =
      P.vertexSet.image φ.toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    rcases (P.mapEmbedding φ).mem_vertexSet.mp hx with ⟨i, hxi⟩
    rcases Finset.mem_image.mp
        (by simpa [mapEmbedding_path_vertexSet] using hxi) with
      ⟨v, hvi, hvx⟩
    exact Finset.mem_image.mpr
      ⟨v, P.mem_vertexSet.mpr ⟨i, hvi⟩, hvx⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, hvx⟩
    rcases P.mem_vertexSet.mp hv with ⟨i, hvi⟩
    exact (P.mapEmbedding φ).mem_vertexSet.mpr
      ⟨i, by
        rw [mapEmbedding_path_vertexSet]
        exact Finset.mem_image.mpr ⟨v, hvi, hvx⟩⟩

/-- Reinterpret a path packing after replacing its two terminal finsets by
equal finsets. -/
def copyTerminals {S' T' : Finset V} (P : PathPacking G S T)
    (hS : S = S') (hT : T = T') :
    PathPacking G S' T' where
  Index := P.Index
  path := P.path
  connects := by
    intro i
    simpa [← hS, ← hT] using P.connects i
  node_disjoint := P.node_disjoint

@[simp] theorem copyTerminals_card {S' T' : Finset V}
    (P : PathPacking G S T) (hS : S = S') (hT : T = T') :
    (P.copyTerminals hS hT).card = P.card := rfl

/-- Mapping an internally disjoint bridge along the same embedding as its
packing preserves the bridge relation. -/
noncomputable def BridgeBetween.mapEmbedding
    (P : PathPacking G S T) (φ : G ↪g H)
    {i j : P.Index} (β : P.BridgeBetween i j) :
    (P.mapEmbedding φ).BridgeBetween i j where
  path := β.path.mapEmbedding φ
  connects := by
    rcases β.connects with h | h
    · exact Or.inl ⟨by
        simp only [PathPacking.mapEmbedding]
        rw [GraphPath.mapEmbedding_vertexSet]
        exact Finset.mem_image.mpr ⟨β.path.source, h.1, rfl⟩, by
        simp only [PathPacking.mapEmbedding]
        rw [GraphPath.mapEmbedding_vertexSet]
        exact Finset.mem_image.mpr ⟨β.path.target, h.2, rfl⟩⟩
    · exact Or.inr ⟨by
        simp only [PathPacking.mapEmbedding]
        rw [GraphPath.mapEmbedding_vertexSet]
        exact Finset.mem_image.mpr ⟨β.path.source, h.1, rfl⟩, by
        simp only [PathPacking.mapEmbedding]
        rw [GraphPath.mapEmbedding_vertexSet]
        exact Finset.mem_image.mpr ⟨β.path.target, h.2, rfl⟩⟩
  internallyDisjoint := by
    intro x hx hP
    rw [GraphPath.mapEmbedding_vertexSet] at hx
    rw [mapEmbedding_vertexSet] at hP
    rcases Finset.mem_image.mp hx with ⟨v, hv, hvx⟩
    rcases Finset.mem_image.mp hP with ⟨w, hw, hwx⟩
    have hvw : v = w := φ.injective (hvx.trans hwx.symm)
    change x = φ β.path.source ∨ x = φ β.path.target
    rcases β.internallyDisjoint hv (by simpa [hvw] using hw) with hs | ht
    · exact Or.inl (hvx.symm.trans (congrArg φ hs))
    · exact Or.inr (hvx.symm.trans (congrArg φ ht))

theorem mapEmbedding_hasPairwiseBridgesIn
    (P : PathPacking G S T) (φ : G ↪g H) {U : Finset V}
    (h : P.HasPairwiseBridgesIn U) :
    (P.mapEmbedding φ).HasPairwiseBridgesIn
      (U.map φ.toEmbedding) := by
  intro i j hij
  rcases h hij with ⟨β, hβU⟩
  refine ⟨β.mapEmbedding P φ, ?_⟩
  simp only [BridgeBetween.mapEmbedding, GraphPath.mapEmbedding_vertexSet]
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨v, hv, hvx⟩
  exact Finset.mem_map.mpr ⟨v, hβU hv, hvx⟩

end PathPacking

namespace ChekuriChuzhoy


open AppendixB1

namespace AppendixB1.IndexedAuxiliaryPrefix


variable {V : Type v} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

/-- Replacing a free hill by its row interval preserves disjointness from
every other current terminal column.

This is the first preservation assertion in the hill-elimination paragraph of
Appendix B.1.  The replacement path is contained in the union of the old
column and the free row interval; those two pieces are disjoint from every
other column by, respectively, the column-packing invariant and the definition
of a free hill. -/
theorem TerminalPathHill.replacement_nodeDisjoint_other
    {L : PerfectPathPacking G A B} {h : ℕ}
    {R : IndexedAuxiliaryPrefix L h} {hpos : 0 < h}
    {Q : PerfectPathPacking G R.X R.Y}
    {Q0 : TypeOneQStarFamily R hpos Q}
    {I : IterationInput R hpos Q0}
    {inv : TypeOneIterationInvariants I}
    {columns : TerminalPathColumnOrder I inv}
    (H : TerminalPathHill columns)
    (j : Fin h) (hj : j ≠ H.candidate.col) :
    H.candidate.replacementColumnPath.path.NodeDisjoint
      (columns.qstar j) := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro x hx hother
  rcases Finset.mem_union.mp
      (H.candidate.replacementColumnPath.vertexSet_subset hx) with
    hxold | hxrow
  · exact Finset.disjoint_left.mp
      (columns.qstar_nodeDisjoint hj.symm) hxold hother
  · exact Finset.disjoint_left.mp
      (H.rowInterval_free_of_other_columns j hj) hxrow hother

end AppendixB1.IndexedAuxiliaryPrefix

/-- The canonical embedding of an induced cluster graph into its ambient
graph. -/
private def clusterEmbedding
    {V : Type u} [DecidableEq V] (G : _root_.SimpleGraph V)
    (C : Finset V) :
    G.induce {v : V | v ∈ C} ↪g G :=
  _root_.SimpleGraph.Embedding.induce (G := G) {v : V | v ∈ C}

/-- Node-linkedness inside a cluster is node-linkedness of the corresponding
terminal subtype sets in the induced cluster graph. -/
private theorem nodeLinkedIn_induce_cluster
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {C A B : Finset V}
    (h : NodeLinkedIn G C A B) :
    NodeLinkedIn
      (G.induce {v : V | v ∈ C}) Finset.univ
      (PathPacking.subtypeFinset A C h.1)
      (PathPacking.subtypeFinset B C h.2.1) := by
  classical
  have hAC : A ⊆ C := h.1
  have hBC : B ⊆ C := h.2.1
  have hAB : Disjoint A B := h.2.2.1
  have hroute := h.2.2.2
  refine ⟨Finset.subset_univ _, Finset.subset_univ _, ?_, ?_⟩
  · apply Finset.disjoint_left.2
    intro a ha hb
    exact Finset.disjoint_left.mp hAB
      ((PathPacking.mem_subtypeFinset hAC a).1 ha)
      ((PathPacking.mem_subtypeFinset hBC a).1 hb)
  · intro A' B' hA' hB'
    let Aval : Finset V := A'.map ⟨Subtype.val, Subtype.val_injective⟩
    let Bval : Finset V := B'.map ⟨Subtype.val, Subtype.val_injective⟩
    have hAvalA : Aval ⊆ A := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨a, ha, rfl⟩
      exact (PathPacking.mem_subtypeFinset hAC a).1 (hA' ha)
    have hBvalB : Bval ⊆ B := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
      exact (PathPacking.mem_subtypeFinset hBC b).1 (hB' hb)
    rcases hroute hAvalA hBvalB with ⟨P, hPcard, hPstay⟩
    have hAvalC : Aval ⊆ C := subset_trans hAvalA hAC
    have hBvalC : Bval ⊆ C := subset_trans hBvalB hBC
    let Psub := P.induce C hPstay hAvalC hBvalC
    have hAeq :
        PathPacking.subtypeFinset Aval C hAvalC = A' := by
      ext a
      simp [Aval, PathPacking.mem_subtypeFinset]
    have hBeq :
        PathPacking.subtypeFinset Bval C hBvalC = B' := by
      ext b
      simp [Bval, PathPacking.mem_subtypeFinset]
    let Q : PathPacking (G.induce {v : V | v ∈ C}) A' B' :=
      Psub.copyTerminals hAeq hBeq
    refine ⟨Q, ?_, ?_⟩
    · change P.card = min A'.card B'.card
      rw [hPcard]
      simp [Aval, Bval]
    · intro i v _hv
      exact Finset.mem_univ v

/-- A uniform proof of Appendix B.1 implies the exact cluster-local Theorem
3.1 interface.  This is the formal localization step used in Corollary 3.2. -/
theorem localRoutingClusterInput_of_theoremB1
    (hB1 :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {A B : Finset V} (h : ℕ)
        (L : PerfectPathPacking G A B),
          AppendixB1.TheoremB1Statement G h L) :
    LocalRoutingClusterInput.{u} := by
  classical
  intro V instF instD G C A B h q w hh hq hcluster hlink hAcard hBcard hwidth
  let GC : _root_.SimpleGraph {v : V // v ∈ C} :=
    G.induce {v : V | v ∈ C}
  let AC : Finset {v : V // v ∈ C} :=
    PathPacking.subtypeFinset A C hlink.1
  let BC : Finset {v : V // v ∈ C} :=
    PathPacking.subtypeFinset B C hlink.2.1
  have hlinkC : NodeLinkedIn GC Finset.univ AC BC := by
    simpa [GC, AC, BC] using nodeLinkedIn_induce_cluster hlink
  have hACcard : AC.card = w := by
    simpa [AC, PathPacking.subtypeFinset] using hAcard
  have hBCcard : BC.card = w := by
    simpa [BC, PathPacking.subtypeFinset] using hBcard
  rcases
      exists_pathPacking_pairwiseBridges_or_gridMinor_of_theoremB1Statement_sharp
        (G := GC) (A := AC) (B := BC) (h := h) (q := q)
        (fun L => hB1 GC h L) hcluster hlinkC
        (hACcard.trans hBCcard.symm) hh hq (by simpa [hACcard] using hwidth)
    with hgrid | ⟨P, hPcard, _hPuniv, hPbridges⟩
  · left
    rcases hgrid with ⟨W, hWfin, hWdec, H, hHgrid, hminor⟩
    letI : Fintype W := hWfin
    letI : DecidableEq W := hWdec
    exact
      ⟨W, inferInstance, inferInstance, H, hHgrid,
        hminor.trans (IsMinor.of_embedding (clusterEmbedding G C))⟩
  · right
    let φ := clusterEmbedding G C
    let Pmap := P.mapEmbedding φ
    have hACmap : AC.map φ.toEmbedding = A := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_map.mp hv with ⟨x, hx, hxv⟩
        change x ∈ PathPacking.subtypeFinset A C hlink.1 at hx
        have hxA : x.1 ∈ A :=
          (PathPacking.mem_subtypeFinset hlink.1 x).1 hx
        simpa [φ, clusterEmbedding] using hxv ▸ hxA
      · intro hv
        let x : {v : V // v ∈ C} := ⟨v, hlink.1 hv⟩
        have hxAC : x ∈ AC := by
          change x ∈ PathPacking.subtypeFinset A C hlink.1
          exact (PathPacking.mem_subtypeFinset hlink.1 x).2 hv
        exact Finset.mem_map.mpr ⟨x, hxAC, by rfl⟩
    have hBCmap : BC.map φ.toEmbedding = B := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_map.mp hv with ⟨x, hx, hxv⟩
        change x ∈ PathPacking.subtypeFinset B C hlink.2.1 at hx
        have hxB : x.1 ∈ B :=
          (PathPacking.mem_subtypeFinset hlink.2.1 x).1 hx
        simpa [φ, clusterEmbedding] using hxv ▸ hxB
      · intro hv
        let x : {v : V // v ∈ C} := ⟨v, hlink.2.1 hv⟩
        have hxBC : x ∈ BC := by
          change x ∈ PathPacking.subtypeFinset B C hlink.2.1
          exact (PathPacking.mem_subtypeFinset hlink.2.1 x).2 hv
        exact Finset.mem_map.mpr ⟨x, hxBC, by rfl⟩
    let Q : PathPacking G A B :=
      Pmap.copyTerminals hACmap hBCmap
    refine ⟨Q, ?_, ?_, ?_⟩
    · exact hPcard
    · intro i v hv
      change v ∈ (Pmap.path i).vertexSet at hv
      rw [PathPacking.mapEmbedding_path_vertexSet] at hv
      rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
      exact x.2
    · intro i j hij
      rcases hPbridges hij with ⟨β, _hβ⟩
      let βmap := β.mapEmbedding P φ
      refine ⟨{
        path := βmap.path
        connects := by
          change βmap.path.Connects
            (Pmap.path i).vertexSet (Pmap.path j).vertexSet
          exact βmap.connects
        internallyDisjoint := by
          change βmap.path.InternallyDisjointFromSet Pmap.vertexSet
          exact βmap.internallyDisjoint
      }, ?_⟩
      intro v hv
      change v ∈ (β.path.mapEmbedding φ).vertexSet at hv
      rw [GraphPath.mapEmbedding_vertexSet] at hv
      rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
      exact x.2

/-- A uniform proof of Appendix B.1 closes the whole Chekuri--Chuzhoy
Corollary 3.2 package.  The local half is the induced-cluster localization
above; the global half is the proved stitched-row construction. -/
theorem corollary32Input_of_theoremB1
    (hB1 :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {A B : Finset V} (h : ℕ)
        (L : PerfectPathPacking G A B),
          AppendixB1.TheoremB1Statement G h L) :
    Corollary32Input.{u} :=
  corollary32Input_of_localRoutingClusterInput_and_stitchingInput
    (localRoutingClusterInput_of_theoremB1 hB1)
    stitchingInput_proved

/-- Conditional WP6 endpoint in the exact quantitative form consumed by the
degree-ten proof: a proof of Appendix B.1 yields the strong-path-of-sets grid
minor theorem with no further semantic input. -/
theorem strongPathOfSets_containsGridMinor_of_theoremB1
    (hB1 :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {A B : Finset V} (h : ℕ)
        (L : PerfectPathPacking G A B),
          AppendixB1.TheoremB1Statement G h L)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (hg : 2 ≤ g)
    (hell : 2 * g * (g - 1) ≤ ell)
    (hw : 16 * g ^ 2 + 10 * g ≤ w)
    (P : StrongPathOfSetsSystem G ell w) :
    ContainsGridMinor G g :=
  containsGridMinor_of_strongPathOfSets_ge_of_corollary32Input
    (corollary32Input_of_theoremB1 hB1) G hg hell hw P

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
