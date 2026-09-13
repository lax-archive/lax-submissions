import Lax17Proofs.Source.ChekuriChuzhoySection5TerminalCore
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Host-graph bridge for the Section 5 terminal skeleton

The named multigraph used by the Hind--Oellermann and Mader formalizations
keeps its edge index in `Type 0`.  A finite simple host graph may have its
edge type in a higher universe, so this module names its edges by a finite
ordinal and records the exact bijection back to `G.edgeFinset`.  This is the
first, universe-safe bridge needed to apply the named-multigraph core to the
host paths in journal Theorem 5.12.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A universe-zero name for every edge of a finite simple host graph. -/
abbrev HostEdgeIndex (G : _root_.SimpleGraph V) [Fintype G.edgeSet] :=
  Fin G.edgeFinset.card

/-- Recover the host edge represented by a finite name. -/
noncomputable def hostEdgeOrigin (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : HostEdgeIndex G) : Sym2 V :=
  ((Finset.equivFin G.edgeFinset).symm e).val

theorem hostEdgeOrigin_mem (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : HostEdgeIndex G) :
    hostEdgeOrigin G e ∈ G.edgeFinset :=
  ((Finset.equivFin G.edgeFinset).symm e).property

theorem hostEdgeOrigin_injective (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] : Function.Injective (hostEdgeOrigin G) := by
  intro e f hef
  apply (Finset.equivFin G.edgeFinset).symm.injective
  exact Subtype.ext hef

theorem exists_hostEdgeIndex (G : _root_.SimpleGraph V) {e : Sym2 V}
    [Fintype G.edgeSet]
    (he : e ∈ G.edgeFinset) :
    ∃ i : HostEdgeIndex G, hostEdgeOrigin G i = e := by
  let x : {e : Sym2 V // e ∈ G.edgeFinset} := ⟨e, he⟩
  refine ⟨Finset.equivFin G.edgeFinset x, ?_⟩
  exact congrArg Subtype.val
    ((Finset.equivFin G.edgeFinset).symm_apply_apply x)

/-- The endpoint order is only bookkeeping for an unordered host edge. -/
noncomputable def hostEdgeLeft (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : HostEdgeIndex G) : V :=
  (Quot.out (hostEdgeOrigin G e)).1

/-- The endpoint order is only bookkeeping for an unordered host edge. -/
noncomputable def hostEdgeRight (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : HostEdgeIndex G) : V :=
  (Quot.out (hostEdgeOrigin G e)).2

theorem sym2_mk_hostEdgeEndpoints (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : HostEdgeIndex G) :
    s(hostEdgeLeft G e, hostEdgeRight G e) = hostEdgeOrigin G e := by
  exact Quot.out_eq (hostEdgeOrigin G e)

theorem hostEdge_end_ne (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : HostEdgeIndex G) : hostEdgeLeft G e ≠ hostEdgeRight G e := by
  intro h
  have hdiag : (hostEdgeOrigin G e).IsDiag := by
    rw [← sym2_mk_hostEdgeEndpoints G e, Sym2.mk_isDiag_iff]
    exact h
  exact (G.not_isDiag_of_mem_edgeFinset (hostEdgeOrigin_mem G e)) hdiag

/-- The host simple graph viewed as a named edge-indexed multigraph. -/
noncomputable def hostEdgeIndexedGraph (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] : FiniteEdgeIndexedGraph V where
  Edge := HostEdgeIndex G
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  left := hostEdgeLeft G
  right := hostEdgeRight G
  end_ne := hostEdge_end_ne G

@[simp] theorem hostEdgeIndexedGraph_left (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : (hostEdgeIndexedGraph G).Edge) :
    (hostEdgeIndexedGraph G).left e = hostEdgeLeft G e := rfl

@[simp] theorem hostEdgeIndexedGraph_right (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : (hostEdgeIndexedGraph G).Edge) :
    (hostEdgeIndexedGraph G).right e = hostEdgeRight G e := rfl

/-- Exact host-edge provenance for the initial named graph. -/
noncomputable def hostEdgeIndexedOrigin (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] : (hostEdgeIndexedGraph G).Edge -> Sym2 V :=
  hostEdgeOrigin G

theorem hostEdgeIndexedOrigin_injective (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] : Function.Injective (hostEdgeIndexedOrigin G) :=
  hostEdgeOrigin_injective G

theorem hostEdgeIndexedOrigin_mem (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : (hostEdgeIndexedGraph G).Edge) :
    hostEdgeIndexedOrigin G e ∈ G.edgeFinset :=
  hostEdgeOrigin_mem G e

theorem hostEdgeIndexedOrigin_endpoints (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    (e : (hostEdgeIndexedGraph G).Edge) :
    s((hostEdgeIndexedGraph G).left e, (hostEdgeIndexedGraph G).right e) =
      hostEdgeIndexedOrigin G e :=
  sym2_mk_hostEdgeEndpoints G e

/-- The other endpoint of a named host edge incident with `v`.  Simplicity of
the host graph makes this a neighbor rather than merely another edge copy. -/
noncomputable def hostIncidentNeighbor (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] (v : V)
    (e : (hostEdgeIndexedGraph G).incidentEdges v) : G.neighborSet v :=
  ⟨if hleft : (hostEdgeIndexedGraph G).left e.1 = v then
      (hostEdgeIndexedGraph G).right e.1
    else (hostEdgeIndexedGraph G).left e.1, by
      have hAdj : G.Adj ((hostEdgeIndexedGraph G).left e.1)
          ((hostEdgeIndexedGraph G).right e.1) := by
        have hmem :
            s((hostEdgeIndexedGraph G).left e.1,
              (hostEdgeIndexedGraph G).right e.1) ∈ G.edgeFinset := by
          rw [hostEdgeIndexedOrigin_endpoints]
          exact hostEdgeIndexedOrigin_mem G e.1
        simpa [_root_.SimpleGraph.mem_edgeFinset] using hmem
      have hincident := (hostEdgeIndexedGraph G).mem_incidentEdges v e.1 |>.mp e.2
      split_ifs with hleft
      · apply (G.mem_neighborSet v _).mpr
        simpa only [hleft] using hAdj
      · apply (G.mem_neighborSet v _).mpr
        rcases hincident with hleft' | hright
        · exact (hleft hleft').elim
        · simpa only [hright] using hAdj.symm⟩

@[simp] theorem hostIncidentNeighbor_val (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] (v : V)
    (e : (hostEdgeIndexedGraph G).incidentEdges v) :
    (hostIncidentNeighbor G v e).1 =
      if hleft : (hostEdgeIndexedGraph G).left e.1 = v then
        (hostEdgeIndexedGraph G).right e.1
      else (hostEdgeIndexedGraph G).left e.1 := rfl

theorem hostEdgeOrigin_eq_sym2_hostIncidentNeighbor (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] (v : V)
    (e : (hostEdgeIndexedGraph G).incidentEdges v) :
    hostEdgeOrigin G e.1 = s(v, (hostIncidentNeighbor G v e).1) := by
  classical
  by_cases hleft : (hostEdgeIndexedGraph G).left e.1 = v
  · calc
      hostEdgeOrigin G e.1 =
          s((hostEdgeIndexedGraph G).left e.1,
            (hostEdgeIndexedGraph G).right e.1) := by
        simpa [hostEdgeIndexedOrigin] using
          (hostEdgeIndexedOrigin_endpoints G e.1).symm
      _ = s(v, (hostIncidentNeighbor G v e).1) := by
        rw [hostIncidentNeighbor_val, dif_pos hleft]
        exact congrArg (fun z => s(z, (hostEdgeIndexedGraph G).right e.1)) hleft
  · have hincident := (hostEdgeIndexedGraph G).mem_incidentEdges v e.1 |>.mp e.2
    rcases hincident with hleft' | hright
    · exact (hleft hleft').elim
    · calc
        hostEdgeOrigin G e.1 =
            s((hostEdgeIndexedGraph G).left e.1,
              (hostEdgeIndexedGraph G).right e.1) := by
          simpa [hostEdgeIndexedOrigin] using
            (hostEdgeIndexedOrigin_endpoints G e.1).symm
        _ = s((hostEdgeIndexedGraph G).right e.1,
            (hostEdgeIndexedGraph G).left e.1) := Sym2.eq_swap
        _ = s(v, (hostIncidentNeighbor G v e).1) := by
          rw [hostIncidentNeighbor_val, dif_neg hleft]
          exact congrArg (fun z => s(z, (hostEdgeIndexedGraph G).left e.1)) hright

theorem hostIncidentNeighbor_injective (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] (v : V) :
    Function.Injective (hostIncidentNeighbor G v) := by
  intro e f hef
  apply Subtype.ext
  apply hostEdgeOrigin_injective G
  calc
    hostEdgeOrigin G e.1 = s(v, (hostIncidentNeighbor G v e).1) :=
      hostEdgeOrigin_eq_sym2_hostIncidentNeighbor G v e
    _ = s(v, (hostIncidentNeighbor G v f).1) := by rw [hef]
    _ = hostEdgeOrigin G f.1 :=
      (hostEdgeOrigin_eq_sym2_hostIncidentNeighbor G v f).symm

theorem hostEdgeIndexedGraph_degree_le_neighborNcard (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] (v : V) :
    (hostEdgeIndexedGraph G).degree v <= (G.neighborSet v).ncard := by
  classical
  have hcard := Fintype.card_le_of_injective
    (hostIncidentNeighbor G v) (hostIncidentNeighbor_injective G v)
  change ((hostEdgeIndexedGraph G).incidentEdges v).card <=
    (G.neighborSet v).ncard
  rw [← Fintype.card_coe]
  calc
    Fintype.card ((hostEdgeIndexedGraph G).incidentEdges v) <=
        Fintype.card (G.neighborSet v) := hcard
    _ = (G.neighborSet v).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      exact (Set.toFinset_card _).symm

/-- The finite name of an adjacent pair in the host graph. -/
noncomputable def hostEdgeNameOfAdj (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    {x y : V} (hxy : G.Adj x y) : HostEdgeIndex G :=
  Finset.equivFin G.edgeFinset ⟨s(x, y), by
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hxy⟩

@[simp] theorem hostEdgeOrigin_nameOfAdj (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    {x y : V} (hxy : G.Adj x y) :
    hostEdgeOrigin G (hostEdgeNameOfAdj G hxy) = s(x, y) := by
  exact congrArg Subtype.val
    ((Finset.equivFin G.edgeFinset).symm_apply_apply
      ⟨s(x, y), by simpa [_root_.SimpleGraph.mem_edgeFinset] using hxy⟩)

theorem hostEdgeIndexedGraph_joins_nameOfAdj (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    {x y : V} (hxy : G.Adj x y) :
    (hostEdgeIndexedGraph G).Joins (hostEdgeNameOfAdj G hxy) x y := by
  unfold FiniteEdgeIndexedGraph.Joins
  have hends := hostEdgeIndexedOrigin_endpoints G (hostEdgeNameOfAdj G hxy)
  change s(hostEdgeLeft G (hostEdgeNameOfAdj G hxy),
    hostEdgeRight G (hostEdgeNameOfAdj G hxy)) =
      hostEdgeOrigin G (hostEdgeNameOfAdj G hxy) at hends
  rw [hostEdgeOrigin_nameOfAdj G hxy] at hends
  rw [Sym2.eq_iff] at hends
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.2, h.1⟩

/-- Interpret a host-graph walk as a named-edge walk in its finite indexing.
This preserves every edge occurrence, unlike later cycle-erasure operations. -/
noncomputable def hostNamedWalkOfWalk (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    {x y : V} : G.Walk x y -> (hostEdgeIndexedGraph G).NamedEdgeWalk x y
  | .nil => .nil x
  | .cons hxy P => .cons (hostEdgeNameOfAdj G hxy)
      (hostEdgeIndexedGraph_joins_nameOfAdj G hxy)
      (hostNamedWalkOfWalk G P)

@[simp] theorem hostNamedWalkOfWalk_nil (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] (x : V) :
    hostNamedWalkOfWalk G (_root_.SimpleGraph.Walk.nil : G.Walk x x) =
      .nil x := rfl

@[simp] theorem hostNamedWalkOfWalk_cons (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    {x y z : V} (hxy : G.Adj x y) (P : G.Walk y z) :
    hostNamedWalkOfWalk G (_root_.SimpleGraph.Walk.cons hxy P) =
      .cons (hostEdgeNameOfAdj G hxy)
        (hostEdgeIndexedGraph_joins_nameOfAdj G hxy)
        (hostNamedWalkOfWalk G P) := rfl

/-- Every named edge used by the translated walk is exactly an edge occurrence
of the original host walk. -/
theorem hostNamedWalkOfWalk_edge_provenance (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet]
    {x y : V} (P : G.Walk x y) {e : (hostEdgeIndexedGraph G).Edge}
    (he : e ∈ (hostNamedWalkOfWalk G P).edgeList) :
    hostEdgeIndexedOrigin G e ∈ P.edges.toFinset := by
  induction P with
  | nil => simp [hostNamedWalkOfWalk] at he
  | @cons x y z hxy P ih =>
      simp only [hostNamedWalkOfWalk_cons,
        FiniteEdgeIndexedGraph.NamedEdgeWalk.edgeList_cons,
        List.mem_cons] at he
      rcases he with he | he
      · subst e
        simp [hostEdgeIndexedOrigin, hostEdgeOrigin_nameOfAdj]
      · have htail := ih he
        simpa [_root_.SimpleGraph.Walk.edges_cons] using Or.inr htail

/-- A host path between the two sides of an element cut either uses a removed
vertex or uses a host edge carrying a removed finite edge name.  This is the
path-level bridge from the simple graph formulation of Theorem 5.12 to the
named-edge cut formulation used by the Hind--Oellermann reduction. -/
theorem graphPath_hits_hostElementCut
    {terminals : Finset V} {a b : TerminalVertex terminals}
    [Fintype G.edgeSet]
    (C : FiniteEdgeIndexedGraph.TerminalElementCut
      (hostEdgeIndexedGraph G) terminals a.1 b.1)
    (P : GraphPath G) (hsource : P.source = a.1) (htarget : P.target = b.1) :
    (∃ v ∈ P.vertexSet, v ∈ C.removedVertices) ∨
      ∃ i ∈ C.removedEdges, hostEdgeIndexedOrigin G i ∈ P.edgeSet := by
  classical
  by_cases hvertex : ∃ v ∈ P.vertexSet, v ∈ C.removedVertices
  · exact Or.inl hvertex
  · right
    have hnotRemoved : ∀ v, v ∈ P.vertexSet -> v ∉ C.removedVertices := by
      intro v hv hremoved
      exact hvertex ⟨v, hv, hremoved⟩
    have hsub : P.vertexSet ⊆ C.side ∪ C.sideᶜ := by
      intro v _hv
      by_cases hv : v ∈ C.side
      · exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ (by simp [hv])
    have hsourceSide : P.source ∈ C.side := by
      rw [hsource]
      exact C.source_mem
    have hnotSide : ¬ P.vertexSet ⊆ C.side := by
      intro hPside
      apply C.target_not_mem
      simpa only [htarget] using hPside (GraphPath.target_mem_vertexSet P)
    obtain ⟨e, heP, heBoundary⟩ :=
      Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
        (P := P) (X := C.side) (Y := C.sideᶜ) hsub hsourceSide hnotSide
    have heG : e ∈ G.edgeFinset := by
      simpa [_root_.SimpleGraph.mem_edgeFinset] using
        P.edgeSet_subset_edgeSet heP
    obtain ⟨i, hiOrigin⟩ : ∃ i : HostEdgeIndex G, hostEdgeOrigin G i = e :=
      exists_hostEdgeIndex (V := V) G (e := e) heG
    rw [Section44.mem_edgeBoundary] at heBoundary
    obtain ⟨_heG, x, hx, y, hy, hxy⟩ := heBoundary
    have heList : s(x, y) ∈ P.walk.edges := by
      apply List.mem_toFinset.mp
      simpa [GraphPath.edgeSet, hxy] using heP
    have hxP : x ∈ P.vertexSet := by
      simpa [GraphPath.vertexSet] using
        P.walk.fst_mem_support_of_mem_edges heList
    have hyP : y ∈ P.vertexSet := by
      simpa [GraphPath.vertexSet] using
        P.walk.snd_mem_support_of_mem_edges heList
    have hends : s((hostEdgeIndexedGraph G).left i,
        (hostEdgeIndexedGraph G).right i) = s(x, y) := by
      calc
        s((hostEdgeIndexedGraph G).left i, (hostEdgeIndexedGraph G).right i) =
            hostEdgeIndexedOrigin G i := hostEdgeIndexedOrigin_endpoints G i
        _ = e := hiOrigin
        _ = s(x, y) := hxy
    rw [Sym2.eq_iff] at hends
    have hleftP : (hostEdgeIndexedGraph G).left i ∈ P.vertexSet := by
      rcases hends with h | h
      · rw [h.1]
        exact hxP
      · rw [h.1]
        exact hyP
    have hrightP : (hostEdgeIndexedGraph G).right i ∈ P.vertexSet := by
      rcases hends with h | h
      · rw [h.2]
        exact hyP
      · rw [h.2]
        exact hxP
    have hcross : (hostEdgeIndexedGraph G).Crosses C.side i := by
      have hny : y ∉ C.side := by simpa using hy
      unfold FiniteEdgeIndexedGraph.Crosses
      rcases hends with h | h
      · rw [h.1, h.2]
        exact Or.inl ⟨hx, hny⟩
      · rw [h.1, h.2]
        exact Or.inr ⟨hx, hny⟩
    refine ⟨i, ?_, ?_⟩
    · apply C.crossing_removed i
      · exact hnotRemoved _ hleftP
      · exact hnotRemoved _ hrightP
      · exact hcross
    · simpa [hostEdgeIndexedOrigin, hiOrigin] using heP

/-- The source element-connectivity assumption for Theorem 5.12 transfers to
the finite edge-named copy of the host graph.  A path packing charges every
path to a removed vertex or a removed named edge; the packing disjointness
makes that charge injective. -/
theorem hostEdgeIndexedGraph_terminalElementConnectedAtLeast
    {terminals : Finset V} {mu : Nat} [Fintype G.edgeSet]
    (hconn : TerminalsElementConnectedAtLeast G terminals mu) :
    (hostEdgeIndexedGraph G).TerminalElementConnectedAtLeast terminals mu := by
  classical
  intro a ha b hb hab C
  rcases hconn ⟨a, ha⟩ ⟨b, hb⟩ (by
      intro hab'
      exact hab (congrArg Subtype.val hab')) with ⟨P, hPcard⟩
  let Charges : P.Index → C.removedVertices ⊕ C.removedEdges → Prop :=
    fun j z => match z with
      | .inl v => v.1 ∈ (P.path j).vertexSet
      | .inr e => hostEdgeIndexedOrigin G e.1 ∈ (P.path j).edgeSet
  have hcharge_exists : ∀ j : P.Index, ∃ z, Charges j z := by
    intro j
    rcases graphPath_hits_hostElementCut (G := G) C (P.path j)
        (P.source_eq j) (P.target_eq j) with hvertex | hedge
    · rcases hvertex with ⟨v, hvPath, hvRemoved⟩
      exact ⟨.inl ⟨v, hvRemoved⟩, hvPath⟩
    · rcases hedge with ⟨e, heRemoved, hePath⟩
      exact ⟨.inr ⟨e, heRemoved⟩, hePath⟩
  let charge : P.Index → C.removedVertices ⊕ C.removedEdges :=
    fun j => Classical.choose (hcharge_exists j)
  have hcharge_spec : ∀ j, Charges j (charge j) :=
    fun j => Classical.choose_spec (hcharge_exists j)
  have hinjective : Function.Injective charge := by
    intro j k heq
    by_contra hjk
    have hjSpec := hcharge_spec j
    have hkSpec := hcharge_spec k
    cases hj : charge j with
    | inl v =>
        cases hk : charge k with
        | inl w =>
            rw [hj, hk] at heq
            injection heq with hvw
            subst w
            rw [hj] at hjSpec
            rw [hk] at hkSpec
            change v.1 ∈ (P.path j).vertexSet at hjSpec
            change v.1 ∈ (P.path k).vertexSet at hkSpec
            have hterminal := P.nonterminal_disjoint hjk hjSpec hkSpec
            exact Finset.disjoint_left.mp C.removedVertices_nonterminal v.2 hterminal
        | inr e => simp [hj, hk] at heq
    | inr e =>
        cases hk : charge k with
        | inl v => simp [hj, hk] at heq
        | inr f =>
            rw [hj, hk] at heq
            injection heq with hef
            subst f
            rw [hj] at hjSpec
            rw [hk] at hkSpec
            change hostEdgeIndexedOrigin G e.1 ∈ (P.path j).edgeSet at hjSpec
            change hostEdgeIndexedOrigin G e.1 ∈ (P.path k).edgeSet at hkSpec
            exact Finset.disjoint_left.mp (P.edge_disjoint hjk) hjSpec hkSpec
  calc
    mu ≤ P.card := hPcard
    _ = Fintype.card P.Index := rfl
    _ ≤ Fintype.card (C.removedVertices ⊕ C.removedEdges) :=
      Fintype.card_le_of_injective charge hinjective
    _ = C.removedVertices.card + C.removedEdges.card := by
      rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
    _ = C.order := rfl

/-- The fully proved Hind--Oellermann/Mader producer is applicable directly
to the public simple-host element-connectivity premise. -/
theorem exists_hostTerminalConnectivityDegreeOutput
    {terminals : Finset V} {mu : Nat} [Fintype G.edgeSet]
    (hconn : TerminalsElementConnectedAtLeast G terminals mu) :
    Nonempty ((hostEdgeIndexedGraph G).TerminalConnectivityDegreeOutput
      terminals mu) :=
  (hostEdgeIndexedGraph G).exists_terminalConnectivityDegreeOutput terminals mu
    (hostEdgeIndexedGraph_terminalElementConnectedAtLeast (G := G) hconn)

/-- The quantitative terminal graph from Theorem 5.12, now measured against
the original simple host rather than its named-edge presentation. -/
structure HostTerminalConnectivityDegreeOutput
    (G : _root_.SimpleGraph V) (terminals : Finset V) (mu : Nat) where
  graph : FiniteEdgeIndexedGraph (TerminalVertex terminals)
  edge_connected : graph.IsEdgeConnected (2 * mu)
  terminal_degree_le : ∀ t : TerminalVertex terminals,
    graph.degree t <= 2 * (G.neighborSet t.1).ncard

theorem exists_hostTerminalConnectivityDegreeOutput_of_elementConnected
    {terminals : Finset V} {mu : Nat} [Fintype G.edgeSet]
    (hconn : TerminalsElementConnectedAtLeast G terminals mu) :
    Nonempty (HostTerminalConnectivityDegreeOutput G terminals mu) := by
  rcases exists_hostTerminalConnectivityDegreeOutput (G := G) hconn with ⟨C⟩
  exact ⟨{
    graph := C.graph
    edge_connected := C.edge_connected
    terminal_degree_le := by
      intro t
      exact (C.terminal_degree_le t).trans
        (Nat.mul_le_mul_left 2
          (hostEdgeIndexedGraph_degree_le_neighborNcard G t.1)) }⟩

end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
