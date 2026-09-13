import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Lax17Proofs.Source.EdgeMengerDefs
import Lax17Proofs.Source.Menger

namespace Lax17Proofs

universe u v w

/-!
# Finite edge-Menger

This file contains the proof-facing line-graph bridge for finite edge-Menger in
the form used by Chuzhoy--Tan Section 4.4.
-/

namespace SimpleGraph
namespace EdgeMenger


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The spanning subgraph induced by a finite vertex set, kept on the original
vertex type.  Vertices outside `C` are isolated. -/
def restrictToVertexSet (G : _root_.SimpleGraph V) (C : Finset V) :
    _root_.SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ C ∧ v ∈ C
  symm := by
    intro u v h
    exact ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

omit [DecidableEq V] in
@[simp] theorem restrictToVertexSet_adj
    (G : _root_.SimpleGraph V) (C : Finset V) (u v : V) :
    (restrictToVertexSet G C).Adj u v ↔ G.Adj u v ∧ u ∈ C ∧ v ∈ C :=
  Iff.rfl

omit [DecidableEq V] in
/-- The spanning induced subgraph is a subgraph of the ambient graph. -/
theorem restrictToVertexSet_le
    (G : _root_.SimpleGraph V) (C : Finset V) :
    restrictToVertexSet G C ≤ G := by
  intro u v h
  exact h.1

noncomputable instance restrictToVertexSet_edgeSet_fintype
    [Fintype V] (G : _root_.SimpleGraph V) (C : Finset V) :
    Fintype (restrictToVertexSet G C).edgeSet :=
  Fintype.ofFinite _

omit [DecidableEq V] in
private theorem restrictToVertexSet_walk_support_subset
    {C : Finset V} {u v : V}
    (W : (restrictToVertexSet G C).Walk u v) (hu : u ∈ C) :
    ∀ x ∈ W.support, x ∈ C := by
  induction W with
  | nil =>
      intro x hx
      simp at hx
      simpa [hx] using hu
  | @cons u y z h W ih =>
      intro x hx
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih h.2.2 x hx

/-- A path in the spanning induced subgraph, whose source is in `C`, stays in
`C`. -/
theorem restrictToVertexSet_path_vertexSet_subset
    {C : Finset V} (P : GraphPath (restrictToVertexSet G C))
    (hsource : P.source ∈ C) :
    P.vertexSet ⊆ C := by
  intro v hv
  exact restrictToVertexSet_walk_support_subset (G := G) P.walk hsource v
    (by simpa [GraphPath.vertexSet] using hv)

namespace LineGraphBridge

variable {e f : G.edgeSet}

omit [DecidableEq V] in
theorem adj_of_mem_edge_of_ne
    {e : G.edgeSet} {x y : V} (hx : x ∈ (e : Sym2 V))
    (hy : y ∈ (e : Sym2 V)) (hxy : x ≠ y) :
    G.Adj x y := by
  have heq : (e : Sym2 V) = s(x, y) :=
    (Sym2.mem_and_mem_iff hxy).1 ⟨hx, hy⟩
  rw [← _root_.SimpleGraph.mem_edgeSet, ← heq]
  exact e.2

omit [DecidableEq V] in
/-- A line-graph walk between two edges gives a walk in the original graph
between any chosen endpoint of the first edge and any chosen endpoint of the
last edge, together with the fact that every edge of the constructed walk is
one of the line-graph vertices visited by the original walk. -/
noncomputable def walkDataOfLineWalk {e f : G.edgeSet}
    (W : G.lineGraph.Walk e f) {a b : V}
    (ha : a ∈ (e : Sym2 V)) (hb : b ∈ (f : Sym2 V)) :
    {W' : G.Walk a b //
      ∀ ⦃g : Sym2 V⦄, g ∈ W'.edges →
        ∃ h : G.edgeSet, h ∈ W.support.toFinset ∧ (h : Sym2 V) = g} := by
  induction W generalizing a with
  | @nil u =>
      by_cases hab : a = b
      · subst b
        refine ⟨_root_.SimpleGraph.Walk.nil, ?_⟩
        intro g hg
        simp at hg
      · refine ⟨_root_.SimpleGraph.Walk.cons
          (adj_of_mem_edge_of_ne (G := G) ha hb hab)
          _root_.SimpleGraph.Walk.nil, ?_⟩
        intro g hg
        simp only [_root_.SimpleGraph.Walk.edges_cons,
          _root_.SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hg
        subst hg
        exact ⟨u, by simp, (Sym2.mem_and_mem_iff hab).1 ⟨ha, hb⟩⟩
  | @cons e₀ e₁ e₂ h W ih =>
      let z : V :=
        Classical.choose ((_root_.SimpleGraph.lineGraph_adj_iff_exists.mp h).2)
      have hz_spec :
          z ∈ (e₀ : Sym2 V) ∧ z ∈ (e₁ : Sym2 V) :=
        Classical.choose_spec
          ((_root_.SimpleGraph.lineGraph_adj_iff_exists.mp h).2)
      have hz₀ : z ∈ (e₀ : Sym2 V) := hz_spec.1
      have hz₁ : z ∈ (e₁ : Sym2 V) := hz_spec.2
      let tail := ih hz₁ hb
      by_cases haz : a = z
      · subst a
        refine ⟨tail.1, ?_⟩
        intro g hg
        rcases tail.2 hg with ⟨q, hq, hqg⟩
        exact ⟨q, by simp [hq], hqg⟩
      · refine ⟨_root_.SimpleGraph.Walk.cons
          (adj_of_mem_edge_of_ne (G := G) ha hz₀ haz) tail.1, ?_⟩
        intro g hg
        simp only [_root_.SimpleGraph.Walk.edges_cons, List.mem_cons] at hg
        rcases hg with hg | hg
        · subst hg
          exact ⟨e₀, by simp, (Sym2.mem_and_mem_iff haz).1 ⟨ha, hz₀⟩⟩
        · rcases tail.2 hg with ⟨q, hq, hqg⟩
          exact ⟨q, by simp [hq], hqg⟩

omit [DecidableEq V] in
/-- The walk component of `walkDataOfLineWalk`. -/
noncomputable def walkOfLineWalk {e f : G.edgeSet}
    (W : G.lineGraph.Walk e f) {a b : V}
    (ha : a ∈ (e : Sym2 V)) (hb : b ∈ (f : Sym2 V)) :
    G.Walk a b :=
  (walkDataOfLineWalk (G := G) W ha hb).1

theorem walkOfLineWalk_edges_subset {e f : G.edgeSet}
    (W : G.lineGraph.Walk e f) {a b : V}
    (ha : a ∈ (e : Sym2 V)) (hb : b ∈ (f : Sym2 V)) :
    ∀ ⦃g : Sym2 V⦄, g ∈ (walkOfLineWalk (G := G) W ha hb).edges →
      ∃ h : G.edgeSet, h ∈ W.support.toFinset ∧ (h : Sym2 V) = g := by
  exact (walkDataOfLineWalk (G := G) W ha hb).2

/-- Turn a graph path in the line graph into a graph path in the original
graph.  `a` and `b` choose the terminal vertices on the endpoint edges. -/
noncomputable def pathOfLinePath (P : GraphPath G.lineGraph)
    {a b : V} (ha : a ∈ (P.source : Sym2 V))
    (hb : b ∈ (P.target : Sym2 V)) :
    GraphPath G where
  source := a
  target := b
  walk := (walkOfLineWalk (G := G) P.walk ha hb).toPath
  isPath := (walkOfLineWalk (G := G) P.walk ha hb).toPath.property

theorem pathOfLinePath_edgeSet_subset (P : GraphPath G.lineGraph)
    {a b : V} (ha : a ∈ (P.source : Sym2 V))
    (hb : b ∈ (P.target : Sym2 V)) :
    ∀ ⦃g : Sym2 V⦄, g ∈ (pathOfLinePath (G := G) P ha hb).edgeSet →
      ∃ h : G.edgeSet, h ∈ P.vertexSet ∧ (h : Sym2 V) = g := by
  intro g hg
  have hgWalk :
      g ∈ ((walkOfLineWalk (G := G) P.walk ha hb).toPath :
          G.Walk a b).edges := by
    exact List.mem_toFinset.1 (by
      simpa [pathOfLinePath, GraphPath.edgeSet] using hg)
  have hgOrig :
      g ∈ (walkOfLineWalk (G := G) P.walk ha hb).edges :=
    _root_.SimpleGraph.Walk.edges_toPath_subset
      (walkOfLineWalk (G := G) P.walk ha hb) hgWalk
  rcases walkOfLineWalk_edges_subset (G := G) P.walk ha hb hgOrig with
    ⟨h, hh, hhg⟩
  exact ⟨h, by simpa [GraphPath.vertexSet] using hh, hhg⟩

/-- The line-graph vertex corresponding to a dart of the original graph. -/
def dartEdge (d : G.Dart) : G.edgeSet :=
  ⟨d.edge, d.edge_mem⟩

/-- The list of line-graph vertices traced by the edges of a walk. -/
def edgeListOfWalk {u v : V} (W : G.Walk u v) : List G.edgeSet :=
  W.darts.map dartEdge

omit [DecidableEq V] in
theorem edgeListOfWalk_ne_nil {u v : V} (W : G.Walk u v)
    (hW : ¬ W.Nil) :
    edgeListOfWalk (G := G) W ≠ [] := by
  intro hnil
  have hdarts : W.darts = [] := by
    simpa [edgeListOfWalk] using hnil
  exact hW (_root_.SimpleGraph.Walk.darts_eq_nil.mp hdarts)

omit [DecidableEq V] in
theorem mem_edgeListOfWalk_edges {u v : V} (W : G.Walk u v)
    {e : G.edgeSet} (he : e ∈ edgeListOfWalk (G := G) W) :
    (e : Sym2 V) ∈ W.edges := by
  rcases List.mem_map.mp he with ⟨d, hd, rfl⟩
  change d.edge ∈ W.darts.map _root_.SimpleGraph.Dart.edge
  exact List.mem_map.mpr ⟨d, hd, rfl⟩

omit [DecidableEq V] in
private theorem dartEdge_ne_of_dartAdj_of_mem_path_darts
    {u v : V} {W : G.Walk u v} (hW : W.IsPath)
    {d d' : G.Dart} (hd : d ∈ W.darts) (hd' : d' ∈ W.darts)
    (hdd' : G.DartAdj d d') :
    dartEdge (G := G) d ≠ dartEdge (G := G) d' := by
  intro heq
  have hedge : d.edge = d'.edge :=
    congrArg Subtype.val heq
  have hnodup : (W.darts.map _root_.SimpleGraph.Dart.edge).Nodup := by
    simpa [_root_.SimpleGraph.Walk.edges] using hW.isTrail.edges_nodup
  have hdinj := List.inj_on_of_nodup_map hnodup hd hd' hedge
  rw [_root_.SimpleGraph.DartAdj] at hdd'
  subst d'
  exact d.snd_ne_fst hdd'

omit [DecidableEq V] in
theorem edgeListOfWalk_isChain_lineGraph {u v : V} (W : G.Walk u v)
    (hW : W.IsPath) :
    (edgeListOfWalk (G := G) W).IsChain G.lineGraph.Adj := by
  unfold edgeListOfWalk
  rw [List.isChain_map]
  refine (_root_.SimpleGraph.Walk.isChain_dartAdj_darts W).imp_of_mem_imp ?_
  intro d d' hd hd' hdd'
  rw [_root_.SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, ?_⟩
  · exact dartEdge_ne_of_dartAdj_of_mem_path_darts
      (G := G) hW hd hd' hdd'
  · exact ⟨d.snd, by
      change d.snd ∈ s(d.fst, d.snd)
      exact Sym2.mem_mk_right d.fst d.snd, by
      change d.snd ∈ s(d'.fst, d'.snd)
      rw [hdd']
      exact Sym2.mem_mk_left d'.fst d'.snd⟩

omit [DecidableEq V] in
theorem head_edgeListOfWalk_mem_source {u v : V} (W : G.Walk u v)
    (hW : ¬ W.Nil) :
    u ∈ (((edgeListOfWalk (G := G) W).head
      (edgeListOfWalk_ne_nil (G := G) W hW) : G.edgeSet) : Sym2 V) := by
  cases W with
  | nil =>
      exact False.elim (hW _root_.SimpleGraph.Walk.Nil.nil)
  | cons h W =>
      simp [edgeListOfWalk, dartEdge]

omit [DecidableEq V] in
theorem getLast_edgeListOfWalk_mem_target {u v : V} (W : G.Walk u v)
    (hW : ¬ W.Nil) :
    v ∈ (((edgeListOfWalk (G := G) W).getLast
      (edgeListOfWalk_ne_nil (G := G) W hW) : G.edgeSet) : Sym2 V) := by
  induction W with
  | nil =>
      exact False.elim (hW _root_.SimpleGraph.Walk.Nil.nil)
  | @cons u x v h W ih =>
      cases W with
      | nil =>
          simp [edgeListOfWalk, dartEdge]
      | @cons x y v h' W' =>
          have htail :
              ¬ (_root_.SimpleGraph.Walk.cons h' W').Nil :=
            _root_.SimpleGraph.Walk.not_nil_cons
          simpa [edgeListOfWalk, dartEdge] using
            ih htail

/-- A nontrivial original path gives a line-graph path whose vertices are the
edges of the original path. -/
noncomputable def linePathOfGraphPath (P : GraphPath G)
    (hP : P.source ≠ P.target) : GraphPath G.lineGraph where
  source :=
    (edgeListOfWalk (G := G) P.walk).head
      (edgeListOfWalk_ne_nil (G := G) P.walk
        (GraphPath.walk_not_nil_of_source_ne_target P hP))
  target :=
    (edgeListOfWalk (G := G) P.walk).getLast
      (edgeListOfWalk_ne_nil (G := G) P.walk
        (GraphPath.walk_not_nil_of_source_ne_target P hP))
  walk :=
    (_root_.SimpleGraph.Walk.ofSupport
      (edgeListOfWalk (G := G) P.walk)
      (edgeListOfWalk_ne_nil (G := G) P.walk
        (GraphPath.walk_not_nil_of_source_ne_target P hP))
      (edgeListOfWalk_isChain_lineGraph (G := G) P.walk P.isPath)).toPath.1
  isPath :=
    (_root_.SimpleGraph.Walk.ofSupport
      (edgeListOfWalk (G := G) P.walk)
      (edgeListOfWalk_ne_nil (G := G) P.walk
        (GraphPath.walk_not_nil_of_source_ne_target P hP))
      (edgeListOfWalk_isChain_lineGraph (G := G) P.walk P.isPath)).toPath.property

theorem linePathOfGraphPath_vertexSet_subset_edgeSet
    (P : GraphPath G) (hP : P.source ≠ P.target) :
    ∀ ⦃e : G.edgeSet⦄,
      e ∈ (linePathOfGraphPath (G := G) P hP).vertexSet →
        (e : Sym2 V) ∈ P.edgeSet := by
  intro e he
  let hne :=
    GraphPath.walk_not_nil_of_source_ne_target P hP
  let L := edgeListOfWalk (G := G) P.walk
  let hLne := edgeListOfWalk_ne_nil (G := G) P.walk hne
  let hchain := edgeListOfWalk_isChain_lineGraph (G := G) P.walk P.isPath
  let Wline : G.lineGraph.Walk (L.head hLne) (L.getLast hLne) :=
    _root_.SimpleGraph.Walk.ofSupport L hLne hchain
  have hwalk : e ∈ Wline.toPath.1.support := by
    simpa [linePathOfGraphPath, GraphPath.vertexSet, Wline, L, hne, hLne, hchain]
      using he
  have hwalkOrig :
      e ∈ Wline.support :=
    _root_.SimpleGraph.Walk.support_toPath_subset Wline hwalk
  have helist : e ∈ edgeListOfWalk (G := G) P.walk := by
    simpa [Wline, L] using hwalkOrig
  exact List.mem_toFinset.2
    (mem_edgeListOfWalk_edges (G := G) P.walk helist)

variable [Fintype G.edgeSet]

/-- Edges incident with a finite vertex set, as vertices of the line graph. -/
noncomputable def incidentEdges (A : Finset V) : Finset G.edgeSet := by
  classical
  exact (Finset.univ : Finset G.edgeSet).filter fun e =>
    ∃ a ∈ A, a ∈ (e : Sym2 V)

theorem mem_incidentEdges (A : Finset V) (e : G.edgeSet) :
    e ∈ incidentEdges (G := G) A ↔ ∃ a ∈ A, a ∈ (e : Sym2 V) := by
  classical
  simp [incidentEdges]

noncomputable def incidentVertex {A : Finset V} {e : G.edgeSet}
    (he : e ∈ incidentEdges (G := G) A) : V :=
  Classical.choose ((mem_incidentEdges (G := G) A e).1 he)

theorem incidentVertex_mem_set {A : Finset V} {e : G.edgeSet}
    (he : e ∈ incidentEdges (G := G) A) :
    incidentVertex (G := G) he ∈ A :=
  (Classical.choose_spec ((mem_incidentEdges (G := G) A e).1 he)).1

theorem incidentVertex_mem_edge {A : Finset V} {e : G.edgeSet}
    (he : e ∈ incidentEdges (G := G) A) :
    incidentVertex (G := G) he ∈ (e : Sym2 V) :=
  (Classical.choose_spec ((mem_incidentEdges (G := G) A e).1 he)).2

theorem linePathOfGraphPath_connects
    {A B : Finset V} (P : GraphPath G) (hP : P.source ≠ P.target)
    (hA : P.source ∈ A) (hB : P.target ∈ B) :
    (linePathOfGraphPath (G := G) P hP).Connects
      (incidentEdges (G := G) A) (incidentEdges (G := G) B) := by
  classical
  refine Or.inl ⟨?_, ?_⟩
  · rw [mem_incidentEdges]
    refine ⟨P.source, hA, ?_⟩
    simpa [linePathOfGraphPath] using
      head_edgeListOfWalk_mem_source (G := G) P.walk
        (GraphPath.walk_not_nil_of_source_ne_target P hP)
  · rw [mem_incidentEdges]
    refine ⟨P.target, hB, ?_⟩
    simpa [linePathOfGraphPath] using
      getLast_edgeListOfWalk_mem_target (G := G) P.walk
        (GraphPath.walk_not_nil_of_source_ne_target P hP)

variable {A B : Finset V}

noncomputable def pathOfLinePackingPath
    (P : PathPacking G.lineGraph (incidentEdges (G := G) A)
      (incidentEdges (G := G) B)) (i : P.Index) :
    GraphPath G := by
  classical
  by_cases h :
      (P.path i).source ∈ incidentEdges (G := G) A ∧
        (P.path i).target ∈ incidentEdges (G := G) B
  · exact pathOfLinePath (G := G) (P.path i)
      (incidentVertex_mem_edge (G := G) h.1)
      (incidentVertex_mem_edge (G := G) h.2)
  · have hrev :
        (P.path i).target ∈ incidentEdges (G := G) A ∧
          (P.path i).source ∈ incidentEdges (G := G) B := by
      rcases P.connects i with hconn | hconn
      · exact (h hconn).elim
      · exact ⟨hconn.2, hconn.1⟩
    exact pathOfLinePath (G := G) (P.path i).reverse
      (incidentVertex_mem_edge (G := G) hrev.1)
      (incidentVertex_mem_edge (G := G) hrev.2)

theorem pathOfLinePackingPath_connects
    (P : PathPacking G.lineGraph (incidentEdges (G := G) A)
      (incidentEdges (G := G) B)) (i : P.Index) :
    (pathOfLinePackingPath (G := G) (A := A) (B := B) P i).Connects A B := by
  classical
  unfold pathOfLinePackingPath
  by_cases h :
      (P.path i).source ∈ incidentEdges (G := G) A ∧
        (P.path i).target ∈ incidentEdges (G := G) B
  · change (pathOfLinePackingPath (G := G) (A := A) (B := B) P i).Connects A B
    simp [pathOfLinePackingPath, h]
    exact Or.inl
      ⟨incidentVertex_mem_set (G := G) h.1,
        incidentVertex_mem_set (G := G) h.2⟩
  · have hrev :
        (P.path i).target ∈ incidentEdges (G := G) A ∧
          (P.path i).source ∈ incidentEdges (G := G) B := by
      rcases P.connects i with hconn | hconn
      · exact (h hconn).elim
      · exact ⟨hconn.2, hconn.1⟩
    change (pathOfLinePackingPath (G := G) (A := A) (B := B) P i).Connects A B
    simp [pathOfLinePackingPath, h]
    exact Or.inl
      ⟨incidentVertex_mem_set (G := G) hrev.1,
        incidentVertex_mem_set (G := G) hrev.2⟩

theorem pathOfLinePackingPath_edgeSet_subset
    (P : PathPacking G.lineGraph (incidentEdges (G := G) A)
      (incidentEdges (G := G) B)) (i : P.Index) :
    ∀ ⦃g : Sym2 V⦄,
      g ∈ (pathOfLinePackingPath (G := G) (A := A) (B := B) P i).edgeSet →
        ∃ h : G.edgeSet, h ∈ (P.path i).vertexSet ∧ (h : Sym2 V) = g := by
  classical
  unfold pathOfLinePackingPath
  by_cases h :
      (P.path i).source ∈ incidentEdges (G := G) A ∧
        (P.path i).target ∈ incidentEdges (G := G) B
  · intro g hg
    have hg' : g ∈ (pathOfLinePath (G := G) (P.path i)
        (incidentVertex_mem_edge (G := G) h.1)
        (incidentVertex_mem_edge (G := G) h.2)).edgeSet := by
      simpa [pathOfLinePackingPath, h] using hg
    exact pathOfLinePath_edgeSet_subset (G := G) (P.path i)
      (incidentVertex_mem_edge (G := G) h.1)
      (incidentVertex_mem_edge (G := G) h.2) hg'
  · have hrev :
        (P.path i).target ∈ incidentEdges (G := G) A ∧
        (P.path i).source ∈ incidentEdges (G := G) B := by
      rcases P.connects i with hconn | hconn
      · exact (h hconn).elim
      · exact ⟨hconn.2, hconn.1⟩
    intro g hg
    have hg' : g ∈ (pathOfLinePath (G := G) (P.path i).reverse
        (incidentVertex_mem_edge (G := G) hrev.1)
        (incidentVertex_mem_edge (G := G) hrev.2)).edgeSet := by
      simpa [pathOfLinePackingPath, h] using hg
    rcases pathOfLinePath_edgeSet_subset (G := G) (P.path i).reverse
        (incidentVertex_mem_edge (G := G) hrev.1)
        (incidentVertex_mem_edge (G := G) hrev.2) hg' with
      ⟨q, hq, hqg⟩
    exact ⟨q, by simpa [GraphPath.reverse_vertexSet] using hq, hqg⟩

/-- A vertex-disjoint packing in the line graph gives an edge-disjoint packing
in the original graph. -/
noncomputable def edgePathPackingOfLinePacking
    (P : PathPacking G.lineGraph (incidentEdges (G := G) A)
      (incidentEdges (G := G) B)) :
    EdgePathPacking G A B where
  Index := P.Index
  path := pathOfLinePackingPath (G := G) (A := A) (B := B) P
  connects := pathOfLinePackingPath_connects (G := G) (A := A) (B := B) P
  edge_disjoint := by
    intro i j hij
    rw [GraphPath.EdgeDisjoint, Finset.disjoint_left]
    intro g hgi hgj
    rcases pathOfLinePackingPath_edgeSet_subset
        (G := G) (A := A) (B := B) P i hgi with
      ⟨ei, hei, heig⟩
    rcases pathOfLinePackingPath_edgeSet_subset
        (G := G) (A := A) (B := B) P j hgj with
      ⟨ej, hej, hejg⟩
    have heq : ei = ej := Subtype.ext (heig.trans hejg.symm)
    exact Finset.disjoint_left.mp (P.node_disjoint hij)
      hei (by simpa [heq] using hej)

@[simp] theorem edgePathPackingOfLinePacking_card
    (P : PathPacking G.lineGraph (incidentEdges (G := G) A)
      (incidentEdges (G := G) B)) :
    (edgePathPackingOfLinePacking (G := G) (A := A) (B := B) P).card =
      P.card := rfl

end LineGraphBridge

open LineGraphBridge

/-- The positive half of the line-graph reduction: vertex-disjoint line-graph
paths between incident edge sets give edge-disjoint original graph paths. -/
theorem hasEdgeDisjointPathsIn_univ_of_lineGraph_paths
    [Fintype V] [Fintype G.edgeSet] {A B : Finset V} {k : ℕ}
    (h :
      HasDisjointSTPaths G.lineGraph
        (LineGraphBridge.incidentEdges (G := G) A)
        (LineGraphBridge.incidentEdges (G := G) B) k) :
    HasEdgeDisjointPathsIn G (Finset.univ : Finset V) A B k := by
  classical
  rcases h with ⟨P, hk⟩
  refine ⟨LineGraphBridge.edgePathPackingOfLinePacking
    (G := G) (A := A) (B := B) P, ?_, ?_⟩
  · simpa using hk
  · intro i v hv
    simp

/-- The positive branch of the line-graph reduction inside a finite vertex
set.  A line-graph packing in the graph induced by `C` gives an edge-disjoint
original packing whose vertices all stay in `C`. -/
theorem hasEdgeDisjointPathsIn_of_lineGraph_paths_restrictToVertexSet
    [Fintype V] {C A B : Finset V} {k : ℕ}
    (hA : A ⊆ C) (hB : B ⊆ C)
    (h :
      HasDisjointSTPaths (restrictToVertexSet G C).lineGraph
        (LineGraphBridge.incidentEdges
          (G := restrictToVertexSet G C) A)
        (LineGraphBridge.incidentEdges
          (G := restrictToVertexSet G C) B) k) :
    HasEdgeDisjointPathsIn G C A B k := by
  classical
  let H := restrictToVertexSet G C
  rcases hasEdgeDisjointPathsIn_univ_of_lineGraph_paths
      (G := H) (A := A) (B := B) h with
    ⟨P, hk, _hstay_univ⟩
  refine ⟨P.mapLe (restrictToVertexSet_le G C), ?_, ?_⟩
  · simpa [EdgePathPacking.mapLe, EdgePathPacking.card] using hk
  · intro i v hv
    have hvH : v ∈ (P.path i).vertexSet := by
      simpa [EdgePathPacking.mapLe] using hv
    have hsourceC : (P.path i).source ∈ C := by
      rcases P.connects i with hconn | hconn
      · exact hA hconn.1
      · exact hB hconn.1
    exact restrictToVertexSet_path_vertexSet_subset
      (G := G) (C := C) (P.path i) hsourceC hvH

namespace LineGraphBridge

variable [Fintype G.edgeSet]

/-- A line-graph vertex separator blocks reachability after deleting the
corresponding original edges. -/
theorem not_reachable_deleteEdges_of_lineGraph_separator
    {A B : Finset V} {J : Finset G.edgeSet}
    (hJ : STSeparator G.lineGraph
      (incidentEdges (G := G) A) (incidentEdges (G := G) B) J)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) (hab : a ≠ b) :
    ¬ (G.deleteEdges
      ((J.image (fun e : G.edgeSet => (e : Sym2 V)) :
        Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b := by
  classical
  intro hreach
  let F : Finset (Sym2 V) :=
    J.image (fun e : G.edgeSet => (e : Sym2 V))
  let D := G.deleteEdges (F : Set (Sym2 V))
  let W : D.Walk a b := Classical.choice hreach
  let Pdel : GraphPath D :=
    { source := a
      target := b
      walk := W.toPath.1
      isPath := W.toPath.property }
  let P : GraphPath G := Pdel.mapLe (_root_.SimpleGraph.deleteEdges_le (G := G) (F : Set (Sym2 V)))
  have hPne : P.source ≠ P.target := by
    simpa [P, Pdel] using hab
  let Q := linePathOfGraphPath (G := G) P hPne
  have hQconn :
      Q.Connects (incidentEdges (G := G) A) (incidentEdges (G := G) B) := by
    simpa [Q, P, Pdel] using
      linePathOfGraphPath_connects (G := G) (A := A) (B := B) P hPne ha hb
  rcases hJ Q hQconn with ⟨e, heQ, heJ⟩
  have heP : (e : Sym2 V) ∈ P.edgeSet :=
    linePathOfGraphPath_vertexSet_subset_edgeSet (G := G) P hPne
      (by simpa [Q] using heQ)
  have heD : (e : Sym2 V) ∈ Pdel.edgeSet := by
    simpa [P, GraphPath.mapLe_edgeSet] using heP
  have he_notF : (e : Sym2 V) ∉ F := by
    have heDedge : (e : Sym2 V) ∈ D.edgeSet :=
      GraphPath.edgeSet_subset_edgeSet Pdel heD
    have heDedge' :
        (e : Sym2 V) ∈ G.edgeSet \ (F : Set (Sym2 V)) := by
      simpa [D, _root_.SimpleGraph.edgeSet_deleteEdges] using heDedge
    exact heDedge'.2
  have heF : (e : Sym2 V) ∈ F := by
    exact Finset.mem_image.mpr ⟨e, heJ, rfl⟩
  exact he_notF heF

end LineGraphBridge

/-- Finite edge-Menger, cut form used by Section 4.4. -/
theorem edge_menger_cut : EdgeMengerCutStatement.{u} :=
by
  classical
  intro V hV hVEq G C A B k hA hB hAB hno
  let H := restrictToVertexSet G C
  let S := LineGraphBridge.incidentEdges (G := H) A
  let T := LineGraphBridge.incidentEdges (G := H) B
  rcases Menger.finite_vertex_menger_sharp (G := H.lineGraph) S T k with hpaths | hsep
  ·
      exact False.elim (hno
        (hasEdgeDisjointPathsIn_of_lineGraph_paths_restrictToVertexSet
          (G := G) (C := C) (A := A) (B := B) hA hB (by
            simpa [H, S, T] using hpaths)))
  ·
      rcases hsep with ⟨J, hJcard, hJsep⟩
      let F : Finset (Sym2 V) :=
        J.image (fun e : H.edgeSet => (e : Sym2 V))
      let D := H.deleteEdges (F : Set (Sym2 V))
      let X : Finset V := C.filter fun v => ∃ a ∈ A, D.Reachable a v
      let Y : Finset V := C \ X
      have hXsubset : X ⊆ C := by
        intro v hv
        exact (Finset.mem_filter.mp hv).1
      have hcover : X ∪ Y = C := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_union.mp hv with hvX | hvY
          · exact hXsubset hvX
          · exact (Finset.mem_sdiff.mp hvY).1
        · intro hvC
          by_cases hvX : v ∈ X
          · exact Finset.mem_union_left Y hvX
          · exact Finset.mem_union_right X (Finset.mem_sdiff.2 ⟨hvC, hvX⟩)
      have hdisj : Disjoint X Y := by
        rw [Finset.disjoint_left]
        intro v hvX hvY
        exact (Finset.mem_sdiff.mp hvY).2 hvX
      have hleft : A ⊆ X := by
        intro a ha
        exact Finset.mem_filter.2
          ⟨hA ha, ⟨a, ha, ⟨_root_.SimpleGraph.Walk.nil⟩⟩⟩
      have hright : B ⊆ Y := by
        intro b hb
        have hbC : b ∈ C := hB hb
        refine Finset.mem_sdiff.2 ⟨hbC, ?_⟩
        intro hbX
        rcases Finset.mem_filter.mp hbX with ⟨_hbC, a, ha, hreach⟩
        have hab : a ≠ b := by
          intro h
          exact Finset.disjoint_left.mp hAB ha (by simpa [h] using hb)
        exact LineGraphBridge.not_reachable_deleteEdges_of_lineGraph_separator
          (G := H) (A := A) (B := B) (J := J) hJsep ha hb hab hreach
      have hboundary_subset : edgeBoundary G X Y ⊆ F := by
        intro e he
        rw [mem_edgeBoundary] at he
        rcases he with ⟨heG, x, hxX, y, hyY, rfl⟩
        by_contra hnot
        have hxC : x ∈ C := hXsubset hxX
        have hyC : y ∈ C := (Finset.mem_sdiff.mp hyY).1
        have hHxy : H.Adj x y := by
          exact ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using heG, hxC, hyC⟩
        have hDxy : D.Adj x y := by
          simpa [D] using (show H.Adj x y ∧ s(x, y) ∉ (F : Set (Sym2 V)) from
            ⟨hHxy, hnot⟩)
        rcases Finset.mem_filter.mp hxX with ⟨_hxC, a, ha, hreach⟩
        have hyX : y ∈ X := by
          refine Finset.mem_filter.2 ⟨hyC, a, ha, ?_⟩
          exact hreach.trans hDxy.reachable
        exact (Finset.mem_sdiff.mp hyY).2 hyX
      have hboundary_card_le : (edgeBoundary G X Y).card ≤ F.card :=
        Finset.card_le_card hboundary_subset
      have hFcard : F.card = J.card := by
        dsimp [F]
        rw [Finset.card_image_of_injective]
        intro e f hef
        exact Subtype.ext hef
      let cut : CutPartition G C A B k :=
        { X := X,
          Y := Y,
          cover := hcover,
          disjoint := hdisj,
          left_subset := hleft,
          right_subset := hright,
          boundary_lt :=
            lt_of_le_of_lt (by simpa [hFcard] using hboundary_card_le) hJcard }
      exact ⟨cut⟩

end EdgeMenger
end SimpleGraph

end Lax17Proofs
