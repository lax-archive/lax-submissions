import Lax17Proofs.Source.TreewidthSparsifierTheorem51Terminals

namespace Lax17Proofs

universe u v w

/-!
# Carrier-clean blue chunks

This module performs the degree-two suppression used implicitly in Step 1 of
Chekuri--Chuzhoy Theorem 5.1.  For an abstract matching edge crossing a rail
cut, its physical blue path is shortened from the last red-carried vertex on
the first side to the first red-carried vertex on the second side.  The
interior of the resulting chunk contains no red-carried vertex.  Since every
degree-four vertex lies on a red rail, only the two endpoints of such a chunk
can make a thinning choice that damages it.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- All vertices lying on one of the concatenated red rails. -/
noncomputable def redCarrierVertices
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) : Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ x : Fin h, E.RedCarrier hbudget v x

/-- Red-carried vertices whose rail label belongs to `S`. -/
noncomputable def redCarrierSide
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) : Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ x : Fin h, E.RedCarrier hbudget v x ∧ x ∈ S

@[simp] theorem mem_redCarrierVertices
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (v : V) :
    v ∈ E.redCarrierVertices hbudget ↔
      ∃ x : Fin h, E.RedCarrier hbudget v x := by
  classical
  simp [redCarrierVertices]

@[simp] theorem mem_redCarrierSide
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) (v : V) :
    v ∈ E.redCarrierSide hbudget S ↔
      ∃ x : Fin h, E.RedCarrier hbudget v x ∧ x ∈ S := by
  classical
  simp [redCarrierSide]

theorem redCarrierSide_union_compl
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) :
    E.redCarrierSide hbudget S ∪ E.redCarrierSide hbudget Sᶜ =
      E.redCarrierVertices hbudget := by
  classical
  ext v
  simp only [Finset.mem_union, mem_redCarrierSide,
    mem_redCarrierVertices]
  constructor
  · rintro (⟨x, hx, _⟩ | ⟨x, hx, _⟩)
    · exact ⟨x, hx⟩
    · exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    by_cases hxs : x ∈ S
    · exact Or.inl ⟨x, hx, hxs⟩
    · exact Or.inr ⟨x, hx, by simpa using hxs⟩

theorem redCarrierSides_disjoint
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) :
    Disjoint
      (E.redCarrierSide hbudget S)
      (E.redCarrierSide hbudget Sᶜ) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvS hvC
  rcases (E.mem_redCarrierSide hbudget S v).mp hvS with
    ⟨x, hvx, hxS⟩
  rcases (E.mem_redCarrierSide hbudget Sᶜ v).mp hvC with
    ⟨y, hvy, hyC⟩
  have hxy : x = y := E.redCarrier_unique hbudget hvx hvy
  subst y
  have hxNot : x ∉ S := by simpa using hyC
  exact hxNot hxS

/-- A first-hit prefix followed by a last-hit suffix gives a path from `A`
to `B` with no internal vertex in either set. -/
theorem exists_clean_segment_between
    {K : _root_.SimpleGraph V} (Q : GraphPath K)
    (A B : Finset V)
    (hsource : Q.source ∈ A) (htarget : Q.target ∈ B) :
    ∃ R : GraphPath K,
      R.source ∈ A ∧
        R.target ∈ B ∧
          R.vertexSet ⊆ Q.vertexSet ∧
            R.edgeSet ⊆ Q.edgeSet ∧
              R.InternallyDisjointFromSet (A ∪ B) := by
  classical
  have hBmeet : (Q.vertexSet ∩ B).Nonempty := by
    exact ⟨Q.target,
      Finset.mem_inter.mpr
        ⟨GraphPath.target_mem_vertexSet Q, htarget⟩⟩
  let Q₁ := Q.cleanPrefixToSet B hBmeet
  have hAmeet : (Q₁.vertexSet ∩ A).Nonempty := by
    exact ⟨Q.source,
      Finset.mem_inter.mpr
        ⟨by
          rw [← Q.cleanPrefixToSet_source B hBmeet]
          exact GraphPath.source_mem_vertexSet Q₁,
          hsource⟩⟩
  let R := Q₁.cleanSuffixFromSet A hAmeet
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · exact Q₁.cleanSuffixFromSet_source_mem A hAmeet
  · have htargetEq : R.target = Q₁.target := by rfl
    rw [htargetEq]
    exact Q.cleanPrefixToSet_target_mem B hBmeet
  · exact
      (Q₁.cleanSuffixFromSet_vertexSet_subset A hAmeet).trans
        (Q.cleanPrefixToSet_vertexSet_subset B hBmeet)
  · exact
      (Q₁.cleanSuffixFromSet_edgeSet_subset A hAmeet).trans
        (Q.takeUntil_edgeSet_subset
          (Q.firstHitVertex_mem_vertexSet B hBmeet))
  · intro v hvR hvAB
    rcases Finset.mem_union.mp hvAB with hvA | hvB
    · exact Q₁.cleanSuffixFromSet_internallyDisjointFromSet
        A hAmeet hvR hvA
    · have hQ₁ :
          Q₁.InternallyDisjointFromSet B :=
        Q.cleanPrefixToSet_internallyDisjointFromSet B hBmeet
      exact
        Q₁.dropUntil_internallyDisjointFromSet
          (Q₁.lastHitVertex_mem_vertexSet A hAmeet) hQ₁ hvR hvB

/-- The carrier-clean physical chunk selected for one matching-boundary
instance. -/
structure CrossingChunk
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) (z : E.RecordBoundary S) where
  path : GraphPath (E.recordAt z.1).layer.localGraph
  source_mem : path.source ∈ E.redCarrierSide hbudget S
  target_mem : path.target ∈ E.redCarrierSide hbudget Sᶜ
  vertexSet_subset :
    path.vertexSet ⊆ (E.localBluePath z.1 z.2.1).vertexSet
  edgeSet_subset :
    path.edgeSet ⊆ (E.localBluePath z.1 z.2.1).edgeSet
  internally_carrier_clean :
    path.InternallyDisjointFromSet (E.redCarrierVertices hbudget)

/-- Every abstract matching edge crossing `S` has a carrier-clean physical
blue chunk joining the two rail sides. -/
theorem exists_crossingChunk
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) (z : E.RecordBoundary S) :
    Nonempty (CrossingChunk E hbudget S z) := by
  classical
  let Q := E.localBluePath z.1 z.2.1
  have hcross :
      (E.recordAt z.1).round.edgeCrosses S z.2.1 :=
    LazyRound.mem_edgeBoundary.mp z.2.2
  have hsourceCarrier :
      E.RedCarrier hbudget Q.source z.2.1.1 := by
    left
    refine ⟨z.1, ?_⟩
    rw [show Q.source = (E.localRedPath z.1 z.2.1.1).source by
      simp [Q]]
    exact GraphPath.source_mem_vertexSet _
  have htargetCarrier :
      E.RedCarrier hbudget Q.target
        ((E.recordAt z.1).round.matching.rightEndpoint z.2.1) := by
    left
    refine ⟨z.1, ?_⟩
    rw [show Q.target =
        (E.localRedPath z.1
          ((E.recordAt z.1).round.matching.rightEndpoint z.2.1)).source by
      simp [Q]]
    exact GraphPath.source_mem_vertexSet _
  rcases hcross with hforward | hbackward
  · have hsourceSide :
        Q.source ∈ E.redCarrierSide hbudget S :=
      (E.mem_redCarrierSide hbudget S Q.source).2
        ⟨z.2.1.1, hsourceCarrier, hforward.1⟩
    have htargetSide :
        Q.target ∈ E.redCarrierSide hbudget Sᶜ :=
      (E.mem_redCarrierSide hbudget Sᶜ Q.target).2
        ⟨_, htargetCarrier, by simpa using hforward.2⟩
    rcases exists_clean_segment_between Q
        (E.redCarrierSide hbudget S)
        (E.redCarrierSide hbudget Sᶜ)
        hsourceSide htargetSide with
      ⟨R, hRA, hRB, hRvQ, hReQ, hclean⟩
    refine ⟨{
      path := R
      source_mem := hRA
      target_mem := hRB
      vertexSet_subset := hRvQ
      edgeSet_subset := hReQ
      internally_carrier_clean := ?_ }⟩
    intro v hvR hvCarrier
    have hvUnion :
        v ∈ E.redCarrierSide hbudget S ∪
          E.redCarrierSide hbudget Sᶜ := by
      rw [E.redCarrierSide_union_compl hbudget S]
      exact hvCarrier
    exact hclean hvR hvUnion
  · have hsourceSide :
        Q.reverse.source ∈ E.redCarrierSide hbudget S := by
      have hq : Q.reverse.source = Q.target := by simp
      rw [hq]
      exact (E.mem_redCarrierSide hbudget S Q.target).2
        ⟨_, htargetCarrier, hbackward.1⟩
    have htargetSide :
        Q.reverse.target ∈ E.redCarrierSide hbudget Sᶜ := by
      have hq : Q.reverse.target = Q.source := by simp
      rw [hq]
      exact (E.mem_redCarrierSide hbudget Sᶜ Q.source).2
        ⟨z.2.1.1, hsourceCarrier, by simpa using hbackward.2⟩
    rcases exists_clean_segment_between Q.reverse
        (E.redCarrierSide hbudget S)
        (E.redCarrierSide hbudget Sᶜ)
        hsourceSide htargetSide with
      ⟨R, hRA, hRB, hRvQ, hReQ, hclean⟩
    refine ⟨{
      path := R
      source_mem := hRA
      target_mem := hRB
      vertexSet_subset := by
        intro v hv
        have : v ∈ Q.reverse.vertexSet := hRvQ hv
        simpa using this
      edgeSet_subset := by
        intro e he
        have : e ∈ Q.reverse.edgeSet := hReQ he
        simpa using this
      internally_carrier_clean := ?_ }⟩
    intro v hvR hvCarrier
    have hvUnion :
        v ∈ E.redCarrierSide hbudget S ∪
          E.redCarrierSide hbudget Sᶜ := by
      rw [E.redCarrierSide_union_compl hbudget S]
      exact hvCarrier
    exact hclean hvR hvUnion

/-- A fixed, canonically chosen clean chunk. -/
noncomputable def crossingChunk
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) (z : E.RecordBoundary S) :
    CrossingChunk E hbudget S z :=
  Classical.choice (E.exists_crossingChunk hbudget S z)

theorem crossingChunk_source_ne_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) (z : E.RecordBoundary S) :
    (E.crossingChunk hbudget S z).path.source ≠
      (E.crossingChunk hbudget S z).path.target := by
  intro heq
  have hsource :=
    (E.crossingChunk hbudget S z).source_mem
  have htarget :=
    (E.crossingChunk hbudget S z).target_mem
  rw [← heq] at htarget
  exact Finset.disjoint_left.mp
    (E.redCarrierSides_disjoint hbudget S) hsource htarget

/-- Every edge of a selected chunk belongs to the global blue support. -/
theorem crossingChunk_edge_mem_blueSupport
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h)) (z : E.RecordBoundary S)
    {e : Sym2 V}
    (he : e ∈ (E.crossingChunk hbudget S z).path.edgeSet) :
    e ∈ E.blueSupport.edgeSet := by
  classical
  let Q := E.localBluePath z.1 z.2.1
  have heQ : e ∈ Q.edgeSet :=
    (E.crossingChunk hbudget S z).edgeSet_subset he
  have heOut : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  have heQOut : s(e.out.1, e.out.2) ∈ Q.edgeSet := by
    simpa [heOut] using heQ
  have heLocal :
      e ∈ (E.recordAt z.1).layer.localGraph.edgeSet :=
    GraphPath.edgeSet_subset_edgeSet Q heQ
  have hne : e.out.1 ≠ e.out.2 := by
    have hadj :
        (E.recordAt z.1).layer.localGraph.Adj e.out.1 e.out.2 := by
      rw [← _root_.SimpleGraph.mem_edgeSet]
      simpa [heOut] using heLocal
    exact hadj.ne
  have hspan :
      (E.recordAt z.1).layer.blue.toPathPacking.spanningGraph.Adj
        e.out.1 e.out.2 := by
    rw [PathPacking.spanningGraph_adj_iff_exists_path_edge]
    refine ⟨?_, hne⟩
    refine ⟨(E.recordAt z.1).layer.blue.indexOfSource
      (labelledImageEquiv
        (E.recordAt z.1).label (E.recordAt z.1).cut.left z.2.1), ?_⟩
    simpa [Q, localBluePath] using heQOut
  have hblue : E.blueSupport.Adj e.out.1 e.out.2 := by
    exact
      (le_iSup
        (fun j : Fin E.finalState.records.length =>
          (E.recordAt j).layer.blue.toPathPacking.spanningGraph) z.1)
        hspan
  rw [← _root_.SimpleGraph.mem_edgeSet] at hblue
  simpa [heOut] using hblue

/-- Chunks selected from distinct matching-boundary instances are
vertex-disjoint.  This follows from node-disjointness inside one physical
record and from the disjoint clusters used by distinct records. -/
theorem crossingChunk_vertex_disjoint
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (S : Finset (Fin h))
    {z w : E.RecordBoundary S} (hzw : z ≠ w) :
    Disjoint
      (E.crossingChunk hbudget S z).path.vertexSet
      (E.crossingChunk hbudget S w).path.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvz hvw
  have hvz' :
      v ∈ (E.localBluePath z.1 z.2.1).vertexSet :=
    (E.crossingChunk hbudget S z).vertexSet_subset hvz
  have hvw' :
      v ∈ (E.localBluePath w.1 w.2.1).vertexSet :=
    (E.crossingChunk hbudget S w).vertexSet_subset hvw
  have hjk : z.1 = w.1 :=
    E.localBluePath_record_unique hbudget hvz' hvw'
  cases z with
  | mk j x =>
    cases w with
    | mk k y =>
      dsimp only at hjk
      subst k
      have hxy : x.1 = y.1 :=
        E.localBluePath_label_unique j hvz' hvw'
      have hxy' : x = y := Subtype.ext hxy
      subst y
      exact hzw rfl

private theorem graphPath_edge_neighbor_eq_of_source
    {K : _root_.SimpleGraph V} (Q : GraphPath K) {y z : V}
    (hy : s(Q.source, y) ∈ Q.edgeSet)
    (hz : s(Q.source, z) ∈ Q.edgeSet) :
    y = z := by
  classical
  have hyV := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q hy).2
  have hzV := (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q hz).2
  have hyNe : y ≠ Q.source := by
    intro h
    subst y
    exact (Q.edgeSet_subset_edgeSet hy).ne rfl
  have hzNe : z ≠ Q.source := by
    intro h
    subst z
    exact (Q.edgeSet_subset_edgeSet hz).ne rfl
  have hyIndex : Q.vertexIndex y = 1 := by
    have hle : Q.vertexIndex y ≤ 1 := by
      simpa using Q.edge_vertexIndex_le_succ hy
    have hne : Q.vertexIndex y ≠ 0 := by
      intro hzero
      exact hyNe
        (GraphPath.eq_of_vertexIndex_eq Q hyV Q.source_mem_vertexSet
          (by simpa using hzero))
    omega
  have hzIndex : Q.vertexIndex z = 1 := by
    have hle : Q.vertexIndex z ≤ 1 := by
      simpa using Q.edge_vertexIndex_le_succ hz
    have hne : Q.vertexIndex z ≠ 0 := by
      intro hzero
      exact hzNe
        (GraphPath.eq_of_vertexIndex_eq Q hzV Q.source_mem_vertexSet
          (by simpa using hzero))
    omega
  exact
    GraphPath.eq_of_vertexIndex_eq Q hyV hzV
      (hyIndex.trans hzIndex.symm)

private theorem graphPath_edge_neighbor_eq_of_endpoint
    {K : _root_.SimpleGraph V} (Q : GraphPath K) {x y z : V}
    (hx : Q.IsEndpoint x)
    (hy : s(x, y) ∈ Q.edgeSet)
    (hz : s(x, z) ∈ Q.edgeSet) :
    y = z := by
  rcases hx with rfl | rfl
  · exact graphPath_edge_neighbor_eq_of_source Q hy hz
  · have hy' : s(Q.reverse.source, y) ∈ Q.reverse.edgeSet := by
      simpa [Sym2.eq_swap] using hy
    have hz' : s(Q.reverse.source, z) ∈ Q.reverse.edgeSet := by
      simpa [Sym2.eq_swap] using hz
    exact graphPath_edge_neighbor_eq_of_source Q.reverse hy' hz'

/-- A nontrivial path has a unique edge incident with each of its two
endpoints.  This is the edge whose thinning choice is controlled below. -/
theorem graphPath_edge_eq_of_endpoint_incident
    {K : _root_.SimpleGraph V} (Q : GraphPath K) {x : V}
    (hx : Q.IsEndpoint x) {e f : Sym2 V}
    (he : e ∈ Q.edgeSet) (hf : f ∈ Q.edgeSet)
    (hxe : x ∈ e) (hxf : x ∈ f) :
    e = f := by
  classical
  rcases Sym2.mem_iff_exists.mp hxe with ⟨y, rfl⟩
  rcases Sym2.mem_iff_exists.mp hxf with ⟨z, hz⟩
  have hf' : s(x, z) ∈ Q.edgeSet := by
    simpa [hz] using hf
  have hyz :=
    graphPath_edge_neighbor_eq_of_endpoint Q hx he hf'
  subst z
  simpa [hz]

namespace CrossingChunk

/-- Endpoint zero is the source and endpoint one is the target. -/
def endpoint
    {E : ExpanderBlocks P count}
    {hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell}
    {S : Finset (Fin h)} {z : E.RecordBoundary S}
    (C : CrossingChunk E hbudget S z) (k : Fin 2) : V :=
  if k = 0 then C.path.source else C.path.target

theorem endpoint_mem_vertexSet
    {E : ExpanderBlocks P count}
    {hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell}
    {S : Finset (Fin h)} {z : E.RecordBoundary S}
    (C : CrossingChunk E hbudget S z) (k : Fin 2) :
    C.endpoint k ∈ C.path.vertexSet := by
  fin_cases k
  · exact GraphPath.source_mem_vertexSet _
  · exact GraphPath.target_mem_vertexSet _

theorem endpoint_isEndpoint
    {E : ExpanderBlocks P count}
    {hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell}
    {S : Finset (Fin h)} {z : E.RecordBoundary S}
    (C : CrossingChunk E hbudget S z) (k : Fin 2) :
    C.path.IsEndpoint (C.endpoint k) := by
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The canonical path edge incident with endpoint `k`. -/
noncomputable def endpointEdge
    {E : ExpanderBlocks P count}
    {hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell}
    {S : Finset (Fin h)} {z : E.RecordBoundary S}
    (C : CrossingChunk E hbudget S z)
    (hne : C.path.source ≠ C.path.target) (k : Fin 2) : Sym2 V :=
  Classical.choose
    (C.path.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hne (C.endpoint_mem_vertexSet k))

theorem endpointEdge_mem_edgeSet
    {E : ExpanderBlocks P count}
    {hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell}
    {S : Finset (Fin h)} {z : E.RecordBoundary S}
    (C : CrossingChunk E hbudget S z)
    (hne : C.path.source ≠ C.path.target) (k : Fin 2) :
    C.endpointEdge hne k ∈ C.path.edgeSet :=
  (Classical.choose_spec
    (C.path.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hne (C.endpoint_mem_vertexSet k))).1

theorem endpoint_mem_endpointEdge
    {E : ExpanderBlocks P count}
    {hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell}
    {S : Finset (Fin h)} {z : E.RecordBoundary S}
    (C : CrossingChunk E hbudget S z)
    (hne : C.path.source ≠ C.path.target) (k : Fin 2) :
    C.endpoint k ∈ C.endpointEdge hne k :=
  (Classical.choose_spec
    (C.path.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hne (C.endpoint_mem_vertexSet k))).2

theorem edge_eq_endpointEdge_of_endpoint_mem
    {E : ExpanderBlocks P count}
    {hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell}
    {S : Finset (Fin h)} {z : E.RecordBoundary S}
    (C : CrossingChunk E hbudget S z)
    (hne : C.path.source ≠ C.path.target) (k : Fin 2)
    {e : Sym2 V} (he : e ∈ C.path.edgeSet)
    (hendpoint : C.endpoint k ∈ e) :
    e = C.endpointEdge hne k :=
  graphPath_edge_eq_of_endpoint_incident C.path
    (C.endpoint_isEndpoint k) he (C.endpointEdge_mem_edgeSet hne k)
    hendpoint (C.endpoint_mem_endpointEdge hne k)

end CrossingChunk

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
