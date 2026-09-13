import Lax17Proofs.Source.ChekuriChuzhoySection5ElementConnectivity
import Lax17Proofs.Source.ChekuriChuzhoySection5HostBridge
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Contracting a family of routers

This is the parallel-edge-preserving contraction used at the start of
Chekuri--Chuzhoy Section 5.4.  Every router is represented by one terminal.
Vertices outside the routers remain as old vertices, and every original edge
whose projected endpoints differ retains its own finite name.

The main theorem transfers pairwise node-disjoint router packings to terminal
element-connectivity of the named contracted graph.  The proof works directly
with element cuts: pull the cut side back to the host graph, charge each
node-disjoint path to a removed old vertex or a removed named edge, and use
injectivity of that charge.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RouterContraction


open Finset
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {n : Nat} {cluster : Fin n → Finset V}

/-- Vertices of the router-contracted named multigraph.  Old copies of router
vertices are present in the finite type but isolated. -/
inductive Vertex (V : Type u) (n : Nat) where
  | router : Fin n → Vertex V n
  | old : V → Vertex V n
deriving DecidableEq

namespace Vertex

instance : Fintype (Vertex V n) where
  elems :=
    ((Finset.univ : Finset (Fin n)).image router) ∪
      ((Finset.univ : Finset V).image old)
  complete := by
    intro z
    cases z with
    | router i => simp
    | old v => simp

@[simp] theorem router_injective :
    Function.Injective (router : Fin n → Vertex V n) := by
  intro i j h
  injection h

@[simp] theorem old_injective :
    Function.Injective (old : V → Vertex V n) := by
  intro x y h
  injection h

end Vertex

/-- A host vertex belongs to at most one router. -/
def RouterPairwiseDisjoint (cluster : Fin n → Finset V) : Prop :=
  Pairwise fun i j => Disjoint (cluster i) (cluster j)

/-- Project a host vertex to its router terminal when it belongs to a router,
and to its old copy otherwise. -/
noncomputable def projection (cluster : Fin n → Finset V) (v : V) :
    Vertex V n :=
  if h : ∃ i : Fin n, v ∈ cluster i then
    Vertex.router (Classical.choose h)
  else
    Vertex.old v

theorem projection_eq_router_of_mem
    (hpair : RouterPairwiseDisjoint cluster)
    {i : Fin n} {v : V} (hvi : v ∈ cluster i) :
    projection cluster v = Vertex.router i := by
  classical
  unfold projection
  split_ifs with h
  · let j := Classical.choose h
    have hvj : v ∈ cluster j := Classical.choose_spec h
    have hji : j = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (hpair hne) hvj hvi
    have hchoose : Classical.choose h = i := by
      simpa [j] using hji
    rw [hchoose]
  · exact False.elim (h ⟨i, hvi⟩)

theorem projection_eq_old_of_forall_not_mem
    {v : V} (hv : ∀ i : Fin n, v ∉ cluster i) :
    projection cluster v = Vertex.old v := by
  classical
  unfold projection
  split_ifs with h
  · exact False.elim (by
      rcases h with ⟨i, hi⟩
      exact hv i hi)
  · rfl

theorem eq_of_projection_eq_old
    {v w : V} (h : projection cluster v = Vertex.old w) :
    v = w := by
  classical
  by_cases hv : ∃ i : Fin n, v ∈ cluster i
  · rw [projection, dif_pos hv] at h
    cases h
  · rw [projection, dif_neg hv] at h
    exact Vertex.old_injective h

/-- The contracted terminals are precisely the router constructors. -/
noncomputable def terminals : Finset (Vertex V n) :=
  (Finset.univ : Finset (Fin n)).image Vertex.router

@[simp] theorem mem_terminals_router (i : Fin n) :
    Vertex.router (V := V) i ∈ terminals (V := V) (n := n) := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem exists_router_of_mem_terminals
    {z : Vertex V n} (hz : z ∈ terminals (V := V) (n := n)) :
    ∃ i : Fin n, z = Vertex.router i := by
  classical
  rcases Finset.mem_image.mp hz with ⟨i, _hi, hzi⟩
  exact ⟨i, hzi.symm⟩

@[simp] theorem terminals_card :
    (terminals (V := V) (n := n)).card = n := by
  classical
  rw [terminals, Finset.card_image_of_injective]
  · simp
  · exact Vertex.router_injective

section NamedGraph

variable [Fintype G.edgeSet]

/-- Original host edges whose router projections have distinct endpoints. -/
abbrev Edge :=
  {e : ChekuriChuzhoySection5TerminalSkeleton.HostEdgeIndex G //
    projection cluster
        (ChekuriChuzhoySection5TerminalSkeleton.hostEdgeLeft G e) ≠
      projection cluster
        (ChekuriChuzhoySection5TerminalSkeleton.hostEdgeRight G e)}

/-- The parallel-edge-preserving router contraction. -/
noncomputable def graph :
    FiniteEdgeIndexedGraph (Vertex V n) where
  Edge := Edge (G := G) (cluster := cluster)
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  left := fun e =>
    projection cluster
      (ChekuriChuzhoySection5TerminalSkeleton.hostEdgeLeft G e.1)
  right := fun e =>
    projection cluster
      (ChekuriChuzhoySection5TerminalSkeleton.hostEdgeRight G e.1)
  end_ne := fun e => e.2

/-- Recover the original host edge represented by a contracted edge copy. -/
noncomputable def edgeOrigin
    (e : (graph (G := G) (cluster := cluster)).Edge) : Sym2 V :=
  ChekuriChuzhoySection5TerminalSkeleton.hostEdgeOrigin G e.1

theorem edgeOrigin_injective :
    Function.Injective (edgeOrigin (G := G) (cluster := cluster)) := by
  intro e f hef
  apply Subtype.ext
  exact
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeOrigin_injective G hef

theorem edgeOrigin_mem_edgeFinset
    (e : (graph (G := G) (cluster := cluster)).Edge) :
    edgeOrigin (G := G) (cluster := cluster) e ∈ G.edgeFinset :=
  ChekuriChuzhoySection5TerminalSkeleton.hostEdgeOrigin_mem G e.1

/-- Name a host adjacency whose projected endpoints differ. -/
noncomputable def edgeOfAdj
    {x y : V} (hxy : G.Adj x y)
    (hne : projection cluster x ≠ projection cluster y) :
    (graph (G := G) (cluster := cluster)).Edge := by
  let e :=
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeNameOfAdj G hxy
  have hjoins :=
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeIndexedGraph_joins_nameOfAdj
      G hxy
  refine ⟨e, ?_⟩
  rcases hjoins with hends | hends
  · have hleft :
        ChekuriChuzhoySection5TerminalSkeleton.hostEdgeLeft G e = x := by
      simpa [e] using hends.1
    have hright :
        ChekuriChuzhoySection5TerminalSkeleton.hostEdgeRight G e = y := by
      simpa [e] using hends.2
    rw [hleft, hright]
    exact hne
  · have hright :
        ChekuriChuzhoySection5TerminalSkeleton.hostEdgeRight G e = x := by
      simpa [e] using hends.1
    have hleft :
        ChekuriChuzhoySection5TerminalSkeleton.hostEdgeLeft G e = y := by
      simpa [e] using hends.2
    rw [hleft, hright]
    exact hne.symm

@[simp] theorem edgeOrigin_edgeOfAdj
    {x y : V} (hxy : G.Adj x y)
    (hne : projection cluster x ≠ projection cluster y) :
    edgeOrigin (G := G) (cluster := cluster)
        (edgeOfAdj (cluster := cluster) hxy hne) = s(x, y) := by
  exact
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeOrigin_nameOfAdj G hxy

theorem edgeOfAdj_joins
    {x y : V} (hxy : G.Adj x y)
    (hne : projection cluster x ≠ projection cluster y) :
    (graph (G := G) (cluster := cluster)).Joins
      (edgeOfAdj (cluster := cluster) hxy hne)
      (projection cluster x) (projection cluster y) := by
  let e :=
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeNameOfAdj G hxy
  have hjoins :=
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeIndexedGraph_joins_nameOfAdj
      G hxy
  rcases hjoins with hends | hends
  · apply Or.inl
    constructor
    · exact congrArg (projection cluster) (by simpa [e] using hends.1)
    · exact congrArg (projection cluster) (by simpa [e] using hends.2)
  · apply Or.inr
    constructor
    · exact congrArg (projection cluster) (by simpa [e] using hends.1)
    · exact congrArg (projection cluster) (by simpa [e] using hends.2)

private theorem edge_fst_mem_vertexSet
    (P : Lax17Proofs.SimpleGraph.GraphPath G) {x y : V}
    (hxy : s(x, y) ∈ P.edgeSet) :
    x ∈ P.vertexSet := by
  have hwalk : s(x, y) ∈ P.walk.edges :=
    List.mem_toFinset.mp
      (by simpa [Lax17Proofs.SimpleGraph.GraphPath.edgeSet] using hxy)
  simpa [Lax17Proofs.SimpleGraph.GraphPath.vertexSet] using
    P.walk.fst_mem_support_of_mem_edges hwalk

private theorem edge_snd_mem_vertexSet
    (P : Lax17Proofs.SimpleGraph.GraphPath G) {x y : V}
    (hxy : s(x, y) ∈ P.edgeSet) :
    y ∈ P.vertexSet := by
  have hwalk : s(x, y) ∈ P.walk.edges :=
    List.mem_toFinset.mp
      (by simpa [Lax17Proofs.SimpleGraph.GraphPath.edgeSet] using hxy)
  simpa [Lax17Proofs.SimpleGraph.GraphPath.vertexSet] using
    P.walk.snd_mem_support_of_mem_edges hwalk

/-- A host path from router `i` to router `j` crosses every element cut
separating the corresponding contracted terminals. -/
theorem graphPath_hits_terminalElementCut
    (hpair : RouterPairwiseDisjoint cluster)
    {i j : Fin n}
    (C : TerminalElementCut
      (graph (G := G) (cluster := cluster))
      (terminals (V := V) (n := n))
      (Vertex.router i) (Vertex.router j))
    (P : Lax17Proofs.SimpleGraph.GraphPath G)
    (hsource : P.source ∈ cluster i)
    (htarget : P.target ∈ cluster j) :
    (∃ v ∈ P.vertexSet,
      projection cluster v ∈ C.removedVertices) ∨
    ∃ e ∈ C.removedEdges,
      edgeOrigin (G := G) (cluster := cluster) e ∈ P.edgeSet := by
  classical
  let X : Finset V :=
    Finset.univ.filter fun v => projection cluster v ∈ C.side
  have hsourceX : P.source ∈ X := by
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [projection_eq_router_of_mem hpair hsource]
    exact C.source_mem
  have htargetNotX : P.target ∉ X := by
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [projection_eq_router_of_mem hpair htarget]
    exact C.target_not_mem
  have hsub : P.vertexSet ⊆ X ∪ Xᶜ := by
    intro v _hv
    by_cases hv : v ∈ X
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ (by simpa using hv)
  have hnot : ¬ P.vertexSet ⊆ X := by
    intro hPX
    exact htargetNotX (hPX P.target_mem_vertexSet)
  obtain ⟨e, heP, heCut⟩ :=
    Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
      (P := P) hsub hsourceX hnot
  rw [Section44.mem_edgeBoundary] at heCut
  obtain ⟨heG, x, hxX, y, hyComp, hxy⟩ := heCut
  have hyNotX : y ∉ X := by simpa using hyComp
  have hxSide : projection cluster x ∈ C.side := by
    simpa [X] using hxX
  have hyNotSide : projection cluster y ∉ C.side := by
    simpa [X] using hyNotX
  have hprojNe : projection cluster x ≠ projection cluster y := by
    intro hxyProj
    exact hyNotSide (hxyProj ▸ hxSide)
  have hAdj : G.Adj x y := by
    have : s(x, y) ∈ G.edgeSet := by simpa [← hxy] using heG
    simpa [_root_.SimpleGraph.mem_edgeSet] using this
  let q := edgeOfAdj (cluster := cluster) hAdj hprojNe
  have hqCross :
      (graph (G := G) (cluster := cluster)).Crosses C.side q := by
    rcases edgeOfAdj_joins (cluster := cluster) hAdj hprojNe with hends | hends
    · exact Or.inl
        ⟨by rw [hends.1]; exact hxSide,
          by rw [hends.2]; exact hyNotSide⟩
    · exact Or.inr
        ⟨by rw [hends.1]; exact hxSide,
          by rw [hends.2]; exact hyNotSide⟩
  by_cases hxRemoved : projection cluster x ∈ C.removedVertices
  · exact Or.inl
      ⟨x, edge_fst_mem_vertexSet P (by simpa [hxy] using heP), hxRemoved⟩
  by_cases hyRemoved : projection cluster y ∈ C.removedVertices
  · exact Or.inl
      ⟨y, edge_snd_mem_vertexSet P (by simpa [hxy] using heP), hyRemoved⟩
  · right
    refine ⟨q, C.crossing_removed q ?_ ?_ hqCross, ?_⟩
    · rcases edgeOfAdj_joins (cluster := cluster) hAdj hprojNe with hends | hends
      · change
          (graph (G := G) (cluster := cluster)).left
              (edgeOfAdj (cluster := cluster) hAdj hprojNe) ∉
            C.removedVertices
        rw [hends.1]
        exact hxRemoved
      · change
          (graph (G := G) (cluster := cluster)).left
              (edgeOfAdj (cluster := cluster) hAdj hprojNe) ∉
            C.removedVertices
        rw [hends.2]
        exact hyRemoved
    · rcases edgeOfAdj_joins (cluster := cluster) hAdj hprojNe with hends | hends
      · change
          (graph (G := G) (cluster := cluster)).right
              (edgeOfAdj (cluster := cluster) hAdj hprojNe) ∉
            C.removedVertices
        rw [hends.2]
        exact hyRemoved
      · change
          (graph (G := G) (cluster := cluster)).right
              (edgeOfAdj (cluster := cluster) hAdj hprojNe) ∉
            C.removedVertices
        rw [hends.1]
        exact hxRemoved
    · simpa [q, hxy] using heP

/-- Each path in a node-disjoint router packing receives a distinct element of
any contracted terminal cut. -/
theorem pathPacking_card_le_terminalElementCut_order
    (hpair : RouterPairwiseDisjoint cluster)
    {i j : Fin n}
    (P : PathPacking G (cluster i) (cluster j))
    (C : TerminalElementCut
      (graph (G := G) (cluster := cluster))
      (terminals (V := V) (n := n))
      (Vertex.router i) (Vertex.router j)) :
    P.card ≤ C.order := by
  classical
  let O := P.orient
  let Charge :=
    Sum {z // z ∈ C.removedVertices} {e // e ∈ C.removedEdges}
  let Hit : O.Index → Charge → Prop :=
    fun a c =>
      match c with
      | Sum.inl z =>
          ∃ v ∈ (O.path a).vertexSet, projection cluster v = z.1
      | Sum.inr e =>
          edgeOrigin (G := G) (cluster := cluster) e.1 ∈
            (O.path a).edgeSet
  have hexists : ∀ a : O.Index, ∃ c : Charge, Hit a c := by
    intro a
    have hsource :
        (O.path a).source ∈ cluster i := by
      exact GraphPath.orient_source_mem (P.path a) (P.connects a)
    have htarget :
        (O.path a).target ∈ cluster j := by
      exact GraphPath.orient_target_mem (P.path a) (P.connects a)
    rcases graphPath_hits_terminalElementCut hpair C (O.path a)
        hsource htarget with hvertex | hedge
    · rcases hvertex with ⟨v, hvPath, hvRemoved⟩
      exact ⟨Sum.inl ⟨projection cluster v, hvRemoved⟩,
        ⟨v, hvPath, rfl⟩⟩
    · rcases hedge with ⟨e, heRemoved, hePath⟩
      exact ⟨Sum.inr ⟨e, heRemoved⟩, hePath⟩
  let charge : O.Index → Charge :=
    fun a => Classical.choose (hexists a)
  have hcharge : ∀ a : O.Index, Hit a (charge a) :=
    fun a => Classical.choose_spec (hexists a)
  have hinjective : Function.Injective charge := by
    intro a b hab
    by_contra habIndex
    have hdisjoint : Disjoint (O.path a).vertexSet (O.path b).vertexSet :=
      O.node_disjoint habIndex
    cases hca : charge a with
    | inl za =>
        cases hcb : charge b with
        | inl zb =>
            have hsum : (Sum.inl za : Charge) = Sum.inl zb :=
              hca.symm.trans (hab.trans hcb)
            have hz : za = zb := Sum.inl.inj hsum
            have haHit := hcharge a
            rw [hca] at haHit
            have hbHit := hcharge b
            rw [hcb] at hbHit
            rcases haHit with
              ⟨x, hxPath, hxProjection⟩
            rcases hbHit with
              ⟨y, hyPath, hyProjection⟩
            rw [← hz] at hyProjection
            cases hzVertex : za.1 with
            | router k =>
                have hkTerminal :
                    Vertex.router (V := V) k ∈
                      terminals (V := V) (n := n) :=
                  mem_terminals_router k
                exact Finset.disjoint_left.mp
                  C.removedVertices_nonterminal za.2
                  (by simpa [hzVertex] using hkTerminal)
            | old z =>
                have hxz : x = z :=
                  eq_of_projection_eq_old
                    (cluster := cluster) (by simpa [hzVertex] using hxProjection)
                have hyz : y = z :=
                  eq_of_projection_eq_old
                    (cluster := cluster) (by simpa [hzVertex] using hyProjection)
                have hxy : x = y := hxz.trans hyz.symm
                exact Finset.disjoint_left.mp hdisjoint
                  hxPath (hxy.symm ▸ hyPath)
        | inr eb =>
            have hsum : (Sum.inl za : Charge) = Sum.inr eb :=
              hca.symm.trans (hab.trans hcb)
            cases hsum
    | inr ea =>
        cases hcb : charge b with
        | inl zb =>
            have hsum : (Sum.inr ea : Charge) = Sum.inl zb :=
              hca.symm.trans (hab.trans hcb)
            cases hsum
        | inr eb =>
            have hsum : (Sum.inr ea : Charge) = Sum.inr eb :=
              hca.symm.trans (hab.trans hcb)
            have he : ea = eb := Sum.inr.inj hsum
            have haHit := hcharge a
            rw [hca] at haHit
            have hbHit := hcharge b
            rw [hcb] at hbHit
            have hea :
                edgeOrigin (G := G) (cluster := cluster) ea.1 ∈
                  (O.path a).edgeSet := by
              exact haHit
            have heb :
                edgeOrigin (G := G) (cluster := cluster) ea.1 ∈
                  (O.path b).edgeSet := by
              rw [he]
              exact hbHit
            have hedgeDisjoint :
                GraphPath.EdgeDisjoint (O.path a) (O.path b) :=
              GraphPath.edgeDisjoint_of_nodeDisjoint hdisjoint
            exact Finset.disjoint_left.mp hedgeDisjoint hea heb
  have hcard := Fintype.card_le_of_injective charge hinjective
  change Fintype.card O.Index ≤ C.order
  calc
    Fintype.card O.Index ≤ Fintype.card Charge := hcard
    _ = C.removedVertices.card + C.removedEdges.card := by
      simp [Charge, Fintype.card_sum, Fintype.card_coe]
    _ = C.order := rfl

/-- Pairwise node-disjoint router packings imply the exact terminal
element-connectivity needed by Theorem 5.10. -/
theorem terminalElementConnectedAtLeast_of_pairwise_packings
    (hpair : RouterPairwiseDisjoint cluster)
    {mu : Nat}
    (hpacking :
      ∀ i j : Fin n, i ≠ j →
        ∃ P : PathPacking G (cluster i) (cluster j), mu ≤ P.card) :
    (graph (G := G) (cluster := cluster)).TerminalElementConnectedAtLeast
      (terminals (V := V) (n := n)) mu := by
  intro a ha b hb hab C
  obtain ⟨i, rfl⟩ := exists_router_of_mem_terminals ha
  obtain ⟨j, rfl⟩ := exists_router_of_mem_terminals hb
  have hij : i ≠ j := by
    intro hij
    apply hab
    simpa [hij]
  obtain ⟨P, hPcard⟩ := hpacking i j hij
  exact hPcard.trans
    (pathPacking_card_le_terminalElementCut_order hpair P C)

end NamedGraph

end ChekuriChuzhoySection5RouterContraction
end SimpleGraph

end Lax17Proofs
