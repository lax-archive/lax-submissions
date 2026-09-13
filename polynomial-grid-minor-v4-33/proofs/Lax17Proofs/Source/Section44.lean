import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lax17Proofs.Source.EdgeMenger
import Lax17Proofs.Source.Section43

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Section 4.4: weak well-linked clusters

This file contains the proof-facing vocabulary for Section 4.4 of
Chuzhoy--Tan.  It formalizes the weak edge-well-linkedness definition used in
the paper, proves Observations 4.9, 4.10, 4.13, and 4.14 in the finite
path-packing language, and proves the graph-theoretic form of Theorem 4.11.

The sparse-cut direction of Observation 4.10 is the edge-Menger step of the
paper.  The vocabulary below isolates that step and the finite bookkeeping
used by the splitting algorithm.
-/

namespace SimpleGraph


namespace Section44

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The Section 4.4 weak edge-well-linkedness notion.

For every two disjoint terminal subfamilies `A` and `B`, the cluster contains
`min |A| |B| w` edge-disjoint paths connecting them.  The paths are required to
stay in the cluster vertex set `C`. -/
def WeakEdgeWellLinkedIn
    (G : _root_.SimpleGraph V) (C T : Finset V) (w : ℕ) : Prop :=
  T ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → Disjoint A B →
      ∃ P : EdgePathPacking G A B,
        P.card = min (min A.card B.card) w ∧ P.StaysIn C

namespace WeakEdgeWellLinkedIn

variable {C T U : Finset V} {w : ℕ}

/-- Weak edge-well-linkedness is inherited by smaller terminal sets. -/
theorem mono_terminals
    (h : WeakEdgeWellLinkedIn G C T w) (hU : U ⊆ T) :
    WeakEdgeWellLinkedIn G C U w := by
  constructor
  · exact subset_trans hU h.1
  · intro A B hA hB hdisj
    exact h.2 (subset_trans hA hU) (subset_trans hB hU) hdisj

/-- Weak edge-well-linkedness is preserved when graph edges are added. -/
theorem mono_graph {G' : _root_.SimpleGraph V}
    (h : WeakEdgeWellLinkedIn G C T w) (hGG' : G ≤ G') :
    WeakEdgeWellLinkedIn G' C T w := by
  constructor
  · exact h.1
  · intro A B hA hB hdisj
    rcases h.2 hA hB hdisj with ⟨P, hcard, hstay⟩
    refine ⟨P.mapLe hGG', ?_, ?_⟩
    · simpa using hcard
    · intro i
      change ((P.path i).mapLe hGG').vertexSet ⊆ C
      simpa using hstay i

end WeakEdgeWellLinkedIn

/-- If two disjoint subsets of a terminal set of size at most `2w` are chosen,
then the smaller one has size at most `w`. -/
theorem min_card_le_of_disjoint_subsets_card_le_two_mul
    {A B T : Finset V} {w : ℕ}
    (hA : A ⊆ T) (hB : B ⊆ T) (hdisj : Disjoint A B)
    (hT : T.card ≤ 2 * w) :
    min A.card B.card ≤ w := by
  classical
  have hUnionSubset : A ∪ B ⊆ T := by
    intro v hv
    rcases Finset.mem_union.1 hv with hvA | hvB
    · exact hA hvA
    · exact hB hvB
  have hsum : A.card + B.card ≤ 2 * w := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_card hUnionSubset).trans hT
  by_contra hnot
  have hwlt : w < min A.card B.card := Nat.lt_of_not_ge hnot
  have hAw : w < A.card := hwlt.trans_le (Nat.min_le_left _ _)
  have hBw : w < B.card := hwlt.trans_le (Nat.min_le_right _ _)
  omega

/-- Observation 4.9.  If `|T| ≤ 2w`, weak `w`-well-linkedness already gives
ordinary edge-well-linkedness. -/
theorem observation49
    {C T : Finset V} {w : ℕ}
    (hcard : T.card ≤ 2 * w)
    (hweak : WeakEdgeWellLinkedIn G C T w) :
    EdgeWellLinkedIn G C T := by
  constructor
  · exact hweak.1
  · intro A B hA hB hdisj
    rcases hweak.2 hA hB hdisj with ⟨P, hPcard, hstay⟩
    have hmin : min A.card B.card ≤ w :=
      min_card_le_of_disjoint_subsets_card_le_two_mul hA hB hdisj hcard
    refine ⟨P, ?_, hstay⟩
    rw [hPcard, Nat.min_eq_left hmin]

/-- The finite edge boundary between two vertex sets.  An edge is counted when
one endpoint lies in `X` and the other in `Y`.  This is the formal
`E(X,Y)` used in Observation 4.10 and in the splitting algorithm. -/
noncomputable def edgeBoundary [Fintype V]
    (G : _root_.SimpleGraph V) (X Y : Finset V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e : Sym2 V =>
    e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y)

theorem mem_edgeBoundary [Fintype V]
    (X Y : Finset V) (e : Sym2 V) :
    e ∈ edgeBoundary G X Y ↔
      e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y) := by
  classical
  simp [edgeBoundary]

theorem edgeBoundary_eq_edgeMenger [Fintype V]
    (X Y : Finset V) :
    edgeBoundary G X Y = EdgeMenger.edgeBoundary G X Y := by
  classical
  ext e
  simp [mem_edgeBoundary, EdgeMenger.mem_edgeBoundary]

theorem edgeBoundary_subset_edgeSet [Fintype V]
    (X Y : Finset V) :
    ↑(edgeBoundary G X Y) ⊆ G.edgeSet := by
  intro e he
  exact ((mem_edgeBoundary (G := G) X Y e).1 he).1

theorem edgeBoundary_comm [Fintype V]
    (X Y : Finset V) :
    edgeBoundary G X Y = edgeBoundary G Y X := by
  classical
  ext e
  constructor
  · intro he
    rcases ((mem_edgeBoundary (G := G) X Y e).1 he) with
      ⟨heG, x, hx, y, hy, rfl⟩
    exact (mem_edgeBoundary (G := G) Y X s(x, y)).2
      ⟨heG, y, hy, x, hx, by simp [Sym2.eq_swap]⟩
  · intro he
    rcases ((mem_edgeBoundary (G := G) Y X e).1 he) with
      ⟨heG, y, hy, x, hx, rfl⟩
    exact (mem_edgeBoundary (G := G) X Y s(y, x)).2
      ⟨heG, x, hx, y, hy, by simp [Sym2.eq_swap]⟩

@[simp] theorem edgeBoundary_empty_left [Fintype V]
    (Y : Finset V) :
    edgeBoundary G (∅ : Finset V) Y = ∅ := by
  classical
  ext e
  simp [mem_edgeBoundary]

@[simp] theorem edgeBoundary_empty_right [Fintype V]
    (X : Finset V) :
    edgeBoundary G X (∅ : Finset V) = ∅ := by
  classical
  rw [edgeBoundary_comm (G := G) X (∅ : Finset V)]
  simp

/-- The current boundary of a cluster, measured against the rest of the finite
ambient vertex set. -/
noncomputable def clusterBoundary [Fintype V]
    (G : _root_.SimpleGraph V) (C : Finset V) : Finset (Sym2 V) :=
  edgeBoundary G C ((Finset.univ : Finset V) \ C)

/-- A paper-style sparse cut for a terminal set inside a cluster.  The cluster
is represented by its vertex set; `X` and `Y` partition that set and the
edge-boundary is smaller than all three quantities from Observation 4.10. -/
structure SparseTerminalCut [Fintype V]
    (G : _root_.SimpleGraph V) (C T : Finset V) (w : ℕ) where
  /-- One side of the partition. -/
  X : Finset V
  /-- The other side of the partition. -/
  Y : Finset V
  /-- The two sides cover the cluster. -/
  cover : X ∪ Y = C
  /-- The two sides are disjoint. -/
  disjoint : Disjoint X Y
  /-- The cut is smaller than the weak-linkage threshold. -/
  boundary_lt_w : (edgeBoundary G X Y).card < w
  /-- The cut is smaller than the number of terminals on the `X` side. -/
  boundary_lt_left : (edgeBoundary G X Y).card < (T ∩ X).card
  /-- The cut is smaller than the number of terminals on the `Y` side. -/
  boundary_lt_right : (edgeBoundary G X Y).card < (T ∩ Y).card

/-- Observation 4.10 as an explicit proposition.  The theorem itself is the
edge-Menger step: non-weak well-linkedness gives a sparse terminal cut. -/
def Observation410Statement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (C T : Finset V) (w : ℕ),
      T ⊆ C →
        ¬ WeakEdgeWellLinkedIn G C T w →
          Nonempty (SparseTerminalCut G C T w)

/-- Observation 4.10, reduced to the finite edge-Menger cut theorem. -/
theorem observation410 : Observation410Statement.{u} := by
  intro V _instFintype _instDecidableEq G C T w hTC hnot
  classical
  have hfail :
      ¬ ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → Disjoint A B →
        ∃ P : EdgePathPacking G A B,
          P.card = min (min A.card B.card) w ∧ P.StaysIn C := by
    intro hall
    exact hnot ⟨hTC, hall⟩
  push Not at hfail
  rcases hfail with ⟨A, B, hA, hB, hdisj, hno⟩
  let k := min (min A.card B.card) w
  have hnoHas :
      ¬ EdgeMenger.HasEdgeDisjointPathsIn G C A B k := by
    intro hhas
    rcases EdgeMenger.exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn
        (G := G) hhas with
      ⟨P, hPcard, hPstay⟩
    exact hno P hPcard hPstay
  rcases EdgeMenger.edge_menger_cut
      (G := G) (C := C) (A := A) (B := B) (k := k)
      (subset_trans hA hTC) (subset_trans hB hTC) hdisj hnoHas with
    ⟨M⟩
  refine ⟨{
    X := M.X
    Y := M.Y
    cover := M.cover
    disjoint := M.disjoint
    boundary_lt_w := ?_
    boundary_lt_left := ?_
    boundary_lt_right := ?_ }⟩
  · have hboundary : (edgeBoundary G M.X M.Y).card < k := by
      simpa [edgeBoundary_eq_edgeMenger] using M.boundary_lt
    exact hboundary.trans_le (Nat.min_le_right _ _)
  · have hboundary : (edgeBoundary G M.X M.Y).card < k := by
      simpa [edgeBoundary_eq_edgeMenger] using M.boundary_lt
    have hAle : A.card ≤ (T ∩ M.X).card := by
      refine Finset.card_le_card ?_
      intro v hv
      exact Finset.mem_inter.2 ⟨hA hv, M.left_subset hv⟩
    exact hboundary.trans_le ((Nat.min_le_left _ _).trans
      ((Nat.min_le_left _ _).trans hAle))
  · have hboundary : (edgeBoundary G M.X M.Y).card < k := by
      simpa [edgeBoundary_eq_edgeMenger] using M.boundary_lt
    have hBle : B.card ≤ (T ∩ M.Y).card := by
      refine Finset.card_le_card ?_
      intro v hv
      exact Finset.mem_inter.2 ⟨hB hv, M.right_subset hv⟩
    exact hboundary.trans_le ((Nat.min_le_left _ _).trans
      ((Nat.min_le_right _ _).trans hBle))

namespace GraphPath

variable {P Q : GraphPath G}

/-- A walk that starts in `X` and uses no edge of the boundary between `X` and
its complement stays in `X`.  This is the connectivity fact used when
Observation 4.13 turns deleted boundary edges into path containment. -/
private theorem walk_support_subset_of_start_mem_and_edge_disjoint_boundary
    [Fintype V] {u v : V} (W : G.Walk u v) {X : Finset V}
    (hu : u ∈ X)
    (hdisj : Disjoint W.edges.toFinset
      (edgeBoundary G X ((Finset.univ : Finset V) \ X))) :
    ∀ x ∈ W.support, x ∈ X := by
  classical
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
      · have hy : y ∈ X := by
          by_contra hyX
          have hboundary :
              s(u, y) ∈ edgeBoundary G X ((Finset.univ : Finset V) \ X) := by
            exact (mem_edgeBoundary (G := G) X ((Finset.univ : Finset V) \ X)
              s(u, y)).2
              ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using h,
                u, hu, y, by simp [hyX], rfl⟩
          have hedge :
              s(u, y) ∈ (_root_.SimpleGraph.Walk.cons h W).edges.toFinset := by
            simp
          exact Finset.disjoint_left.mp hdisj hedge hboundary
        have hdisj_tail :
            Disjoint W.edges.toFinset
              (edgeBoundary G X ((Finset.univ : Finset V) \ X)) := by
          rw [Finset.disjoint_left]
          intro e heW heB
          have heCons :
              e ∈ (_root_.SimpleGraph.Walk.cons h W).edges.toFinset := by
            simp [heW]
          exact Finset.disjoint_left.mp hdisj heCons heB
        exact ih hy hdisj_tail x hx

/-- An initial segment uses only edges from the original path. -/
theorem takeUntil_edgeSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).edgeSet ⊆ P.edgeSet := by
  classical
  intro e he
  have hv' : v ∈ P.walk.support := by simpa [GraphPath.vertexSet] using hv
  have he' : e ∈ (P.walk.takeUntil v hv').edges := by
    simpa [GraphPath.takeUntil, GraphPath.edgeSet] using he
  exact by
    simpa [GraphPath.edgeSet] using P.walk.edges_takeUntil_subset hv' he'

/-- The final edge of a nontrivial graph path belongs to its edge set. -/
theorem penultimate_edge_mem_edgeSet (P : GraphPath G)
    (h : P.source ≠ P.target) :
    s(P.penultimate, P.target) ∈ P.edgeSet := by
  classical
  exact List.mem_toFinset.2 (by
    simpa [GraphPath.penultimate, GraphPath.edgeSet] using
      P.walk.mk_penultimate_end_mem_edges
        (P.walk_not_nil_of_source_ne_target h))

/-- The first edge of a nontrivial graph path belongs to its edge set. -/
theorem snd_edge_mem_edgeSet (P : GraphPath G)
    (h : P.source ≠ P.target) :
    s(P.source, P.walk.snd) ∈ P.edgeSet := by
  classical
  exact List.mem_toFinset.2 (by
    simpa [GraphPath.edgeSet] using
      P.walk.mk_start_snd_mem_edges
        (P.walk_not_nil_of_source_ne_target h))

/-- The second vertex of a nontrivial graph path lies on the path. -/
theorem snd_mem_vertexSet (P : GraphPath G)
    (h : P.source ≠ P.target) :
    P.walk.snd ∈ P.vertexSet := by
  classical
  have hsnd : P.walk.snd ∈ P.walk.support.tail :=
    P.walk.snd_mem_tail_support (P.walk_not_nil_of_source_ne_target h)
  have hsupport : P.walk.snd ∈ P.walk.support :=
    List.mem_of_mem_tail hsnd
  simp [GraphPath.vertexSet, hsupport]

/-- If a graph path has one vertex in `X` and avoids the boundary of `X`, then
the whole path is contained in `X`. -/
theorem vertexSet_subset_of_vertex_mem_and_edgeSet_disjoint_boundary
    [Fintype V] (P : GraphPath G) {X : Finset V} {x : V}
    (hxP : x ∈ P.vertexSet) (hxX : x ∈ X)
    (hdisj : Disjoint P.edgeSet
      (edgeBoundary G X ((Finset.univ : Finset V) \ X))) :
    P.vertexSet ⊆ X := by
  classical
  intro y hy
  by_cases hbefore : y ∈ (P.takeUntil hxP).vertexSet
  · have htake_disj :
        Disjoint (P.takeUntil hxP).edgeSet
          (edgeBoundary G X ((Finset.univ : Finset V) \ X)) := by
      rw [Finset.disjoint_left]
      intro e he heB
      exact Finset.disjoint_left.mp hdisj
        (GraphPath.takeUntil_edgeSet_subset P hxP he) heB
    have htake_rev_disj :
        Disjoint (P.takeUntil hxP).reverse.walk.edges.toFinset
          (edgeBoundary G X ((Finset.univ : Finset V) \ X)) := by
      change Disjoint (P.takeUntil hxP).reverse.edgeSet
        (edgeBoundary G X ((Finset.univ : Finset V) \ X))
      simpa [GraphPath.reverse_edgeSet] using htake_disj
    have hsub :=
      walk_support_subset_of_start_mem_and_edge_disjoint_boundary
        (W := (P.takeUntil hxP).reverse.walk)
        (X := X) hxX htake_rev_disj
    have hyrev : y ∈ (P.takeUntil hxP).reverse.vertexSet := by
      simpa [GraphPath.reverse_vertexSet] using hbefore
    exact hsub y (by simpa [GraphPath.vertexSet] using hyrev)
  · have hyDrop : y ∈ (P.dropUntil hxP).vertexSet := by
      by_contra hnot
      have hsplit :
          (P.takeUntil hxP).walk.append (P.dropUntil hxP).walk = P.walk :=
        P.takeUntil_append_dropUntil_walk hxP
      have hsupport :
          y ∈ ((P.takeUntil hxP).walk.append
            (P.dropUntil hxP).walk).support := by
        have hyWalk : y ∈ P.walk.support := by
          simpa [GraphPath.vertexSet] using hy
        rw [hsplit]
        exact hyWalk
      have hmem :
          y ∈ (P.takeUntil hxP).walk.support ∨
            y ∈ (P.dropUntil hxP).walk.support := by
        have hmemTail :
            y ∈ (P.takeUntil hxP).walk.support ∨
              y ∈ (P.dropUntil hxP).walk.support.tail := by
          simpa [_root_.SimpleGraph.Walk.support_append] using hsupport
        exact hmemTail.elim Or.inl
          (fun htail => Or.inr (List.mem_of_mem_tail htail))
      rcases hmem with hyTake | hyDrop'
      · exact hbefore (by simpa [GraphPath.vertexSet] using hyTake)
      · exact hnot (by simpa [GraphPath.vertexSet] using hyDrop')
    have hdrop_disj :
        Disjoint (P.dropUntil hxP).edgeSet
          (edgeBoundary G X ((Finset.univ : Finset V) \ X)) := by
      rw [Finset.disjoint_left]
      intro e he heB
      exact Finset.disjoint_left.mp hdisj
        (P.dropUntil_edgeSet_subset hxP he) heB
    have hsub :=
      walk_support_subset_of_start_mem_and_edge_disjoint_boundary
        (W := (P.dropUntil hxP).walk) (X := X) hxX hdrop_disj
    exact hsub y (by simpa [GraphPath.vertexSet] using hyDrop)

/-- Node-disjoint paths are edge-disjoint.  This small conversion is used by
the Section 4.4 counting argument: one deleted edge can be charged to at most
one path of a node-disjoint path family. -/
theorem edgeDisjoint_of_nodeDisjoint (h : P.NodeDisjoint Q) :
    P.EdgeDisjoint Q := by
  classical
  rw [GraphPath.EdgeDisjoint, Finset.disjoint_left]
  intro e heP heQ
  have hePwalk : e ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using heP)
  have heQwalk : e ∈ Q.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using heQ)
  have hvP : e.out.1 ∈ P.vertexSet := by
    have hv : e.out.1 ∈ P.walk.support :=
      P.walk.mem_support_of_mem_edges hePwalk (Sym2.out_fst_mem e)
    simpa [GraphPath.vertexSet] using hv
  have hvQ : e.out.1 ∈ Q.vertexSet := by
    have hv : e.out.1 ∈ Q.walk.support :=
      Q.walk.mem_support_of_mem_edges heQwalk (Sym2.out_fst_mem e)
    simpa [GraphPath.vertexSet] using hv
  exact Finset.disjoint_left.mp h hvP hvQ

/-- A path wholly contained in the left side of a disjoint cut uses no
boundary edge of the cut. -/
theorem edgeSet_disjoint_edgeBoundary_of_vertexSet_subset_left [Fintype V]
    {X Y : Finset V} (hXY : Disjoint X Y)
    (hP : P.vertexSet ⊆ X) :
    Disjoint P.edgeSet (edgeBoundary G X Y) := by
  classical
  rw [Finset.disjoint_left]
  intro e heP heB
  rcases ((mem_edgeBoundary (G := G) X Y e).1 heB) with
    ⟨_heG, x, hx, y, hy, rfl⟩
  have heWalk : s(x, y) ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using heP)
  have hyP : y ∈ P.vertexSet := by
    have hySupport : y ∈ P.walk.support :=
      P.walk.mem_support_of_mem_edges heWalk (by simp)
    simpa [GraphPath.vertexSet] using hySupport
  exact Finset.disjoint_left.mp hXY (hP hyP) hy

/-- A path wholly contained in the right side of a disjoint cut uses no
boundary edge of the cut. -/
theorem edgeSet_disjoint_edgeBoundary_of_vertexSet_subset_right [Fintype V]
    {X Y : Finset V} (hXY : Disjoint X Y)
    (hP : P.vertexSet ⊆ Y) :
    Disjoint P.edgeSet (edgeBoundary G X Y) := by
  classical
  rw [edgeBoundary_comm (G := G) X Y]
  exact edgeSet_disjoint_edgeBoundary_of_vertexSet_subset_left
    (P := P) hXY.symm hP

private theorem walk_support_subset_left_of_subset_union_and_edge_disjoint_boundary
    [Fintype V] {u v : V} (W : G.Walk u v) {X Y : Finset V}
    (hsub : W.support.toFinset ⊆ X ∪ Y)
    (hu : u ∈ X)
    (hdisj : Disjoint W.edges.toFinset (edgeBoundary G X Y)) :
    ∀ x ∈ W.support, x ∈ X := by
  classical
  induction W with
  | nil =>
      intro x hx
      simp at hx
      simpa [hx] using hu
  | @cons u z v h W ih =>
      intro x hx
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · have hzUnion : z ∈ X ∪ Y := by
          exact hsub (by simp)
        have hzX : z ∈ X := by
          rcases Finset.mem_union.1 hzUnion with hzX | hzY
          · exact hzX
          · have hboundary : s(u, z) ∈ edgeBoundary G X Y := by
              exact (mem_edgeBoundary (G := G) X Y s(u, z)).2
                ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using h,
                  u, hu, z, hzY, rfl⟩
            have hedge : s(u, z) ∈
                (_root_.SimpleGraph.Walk.cons h W).edges.toFinset := by
              simp
            exact False.elim
              (Finset.disjoint_left.mp hdisj hedge hboundary)
        have hsubTail : W.support.toFinset ⊆ X ∪ Y := by
          intro y hy
          exact hsub (by simp [hy])
        have hdisjTail :
            Disjoint W.edges.toFinset (edgeBoundary G X Y) := by
          rw [Finset.disjoint_left]
          intro e heW heB
          exact Finset.disjoint_left.mp hdisj (by simp [heW]) heB
        exact ih hsubTail hzX hdisjTail x hx

/-- A path contained in a disjoint union and avoiding the cut boundary cannot
move from the left side to the right side. -/
theorem vertexSet_subset_left_of_subset_union_and_edgeSet_disjoint_boundary
    [Fintype V] (P : GraphPath G) {X Y : Finset V}
    (hsub : P.vertexSet ⊆ X ∪ Y) {x : V}
    (hxP : x ∈ P.vertexSet) (hxX : x ∈ X)
    (hdisj : Disjoint P.edgeSet (edgeBoundary G X Y)) :
    P.vertexSet ⊆ X := by
  classical
  intro y hy
  by_cases hbefore : y ∈ (P.takeUntil hxP).vertexSet
  · have htakeSub :
        (P.takeUntil hxP).walk.support.toFinset ⊆ X ∪ Y := by
      intro z hz
      have hzPath : z ∈ P.vertexSet :=
        P.takeUntil_vertexSet_subset hxP (by
          simpa [GraphPath.vertexSet] using hz)
      exact hsub hzPath
    have htakeDisj :
        Disjoint (P.takeUntil hxP).edgeSet (edgeBoundary G X Y) := by
      rw [Finset.disjoint_left]
      intro e he heB
      exact Finset.disjoint_left.mp hdisj
        (GraphPath.takeUntil_edgeSet_subset P hxP he) heB
    have htakeRevSub :
        (P.takeUntil hxP).reverse.walk.support.toFinset ⊆ X ∪ Y := by
      intro z hz
      have hzRev : z ∈ (P.takeUntil hxP).reverse.vertexSet := by
        simpa [GraphPath.vertexSet] using hz
      have hzTake : z ∈ (P.takeUntil hxP).vertexSet := by
        simpa [GraphPath.reverse_vertexSet] using hzRev
      have hzPath : z ∈ P.vertexSet :=
        P.takeUntil_vertexSet_subset hxP hzTake
      exact hsub hzPath
    have htakeRevDisj :
        Disjoint (P.takeUntil hxP).reverse.walk.edges.toFinset
          (edgeBoundary G X Y) := by
      change Disjoint (P.takeUntil hxP).reverse.edgeSet
        (edgeBoundary G X Y)
      simpa [GraphPath.reverse_edgeSet] using htakeDisj
    have hsubWalk :=
      walk_support_subset_left_of_subset_union_and_edge_disjoint_boundary
        (W := (P.takeUntil hxP).reverse.walk) htakeRevSub hxX htakeRevDisj
    have hyRev : y ∈ (P.takeUntil hxP).reverse.vertexSet := by
      simpa [GraphPath.reverse_vertexSet] using hbefore
    exact hsubWalk y (by simpa [GraphPath.vertexSet] using hyRev)
  · have hyDrop : y ∈ (P.dropUntil hxP).vertexSet := by
      by_contra hnot
      have hsplit :
          (P.takeUntil hxP).walk.append (P.dropUntil hxP).walk = P.walk :=
        P.takeUntil_append_dropUntil_walk hxP
      have hsupport :
          y ∈ ((P.takeUntil hxP).walk.append
            (P.dropUntil hxP).walk).support := by
        have hyWalk : y ∈ P.walk.support := by
          simpa [GraphPath.vertexSet] using hy
        rw [hsplit]
        exact hyWalk
      have hmem :
          y ∈ (P.takeUntil hxP).walk.support ∨
            y ∈ (P.dropUntil hxP).walk.support := by
        have hmemTail :
            y ∈ (P.takeUntil hxP).walk.support ∨
              y ∈ (P.dropUntil hxP).walk.support.tail := by
          simpa [_root_.SimpleGraph.Walk.support_append] using hsupport
        exact hmemTail.elim Or.inl
          (fun htail => Or.inr (List.mem_of_mem_tail htail))
      rcases hmem with hyTake | hyDrop'
      · exact hbefore (by simpa [GraphPath.vertexSet] using hyTake)
      · exact hnot (by simpa [GraphPath.vertexSet] using hyDrop')
    have hdropSub :
        (P.dropUntil hxP).walk.support.toFinset ⊆ X ∪ Y := by
      intro z hz
      have hzPath : z ∈ P.vertexSet :=
        P.dropUntil_vertexSet_subset hxP (by
          simpa [GraphPath.vertexSet] using hz)
      exact hsub hzPath
    have hdropDisj :
        Disjoint (P.dropUntil hxP).edgeSet (edgeBoundary G X Y) := by
      rw [Finset.disjoint_left]
      intro e he heB
      exact Finset.disjoint_left.mp hdisj
        (P.dropUntil_edgeSet_subset hxP he) heB
    have hsubWalk :=
      walk_support_subset_left_of_subset_union_and_edge_disjoint_boundary
        (W := (P.dropUntil hxP).walk) hdropSub hxX hdropDisj
    exact hsubWalk y (by simpa [GraphPath.vertexSet] using hyDrop)

/-- Right-side version of
`vertexSet_subset_left_of_subset_union_and_edgeSet_disjoint_boundary`. -/
theorem vertexSet_subset_right_of_subset_union_and_edgeSet_disjoint_boundary
    [Fintype V] (P : GraphPath G) {X Y : Finset V}
    (hsub : P.vertexSet ⊆ X ∪ Y) {x : V}
    (hxP : x ∈ P.vertexSet) (hxY : x ∈ Y)
    (hdisj : Disjoint P.edgeSet (edgeBoundary G X Y)) :
    P.vertexSet ⊆ Y := by
  classical
  rw [edgeBoundary_comm (G := G) X Y] at hdisj
  have hsub' : P.vertexSet ⊆ Y ∪ X := by
    intro v hv
    rcases Finset.mem_union.1 (hsub hv) with hvX | hvY
    · exact Finset.mem_union_right _ hvX
    · exact Finset.mem_union_left _ hvY
  exact vertexSet_subset_left_of_subset_union_and_edgeSet_disjoint_boundary
    (P := P) hsub' hxP hxY hdisj

/-- If a path has no vertex on the left side of a cut, it uses no cut edge. -/
theorem edgeSet_disjoint_edgeBoundary_of_vertexSet_disjoint_left [Fintype V]
    {X Y : Finset V}
    (hP : Disjoint P.vertexSet X) :
    Disjoint P.edgeSet (edgeBoundary G X Y) := by
  classical
  rw [Finset.disjoint_left]
  intro e heP heB
  rcases ((mem_edgeBoundary (G := G) X Y e).1 heB) with
    ⟨_heG, x, hxX, y, _hyY, rfl⟩
  have heWalk : s(x, y) ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using heP)
  have hxP : x ∈ P.vertexSet := by
    have hxSupport : x ∈ P.walk.support :=
      P.walk.mem_support_of_mem_edges heWalk (by simp)
    simpa [GraphPath.vertexSet] using hxSupport
  exact Finset.disjoint_left.mp hP hxP hxX

/-- If a path has no vertex on the right side of a cut, it uses no cut edge. -/
theorem edgeSet_disjoint_edgeBoundary_of_vertexSet_disjoint_right [Fintype V]
    {X Y : Finset V}
    (hP : Disjoint P.vertexSet Y) :
    Disjoint P.edgeSet (edgeBoundary G X Y) := by
  classical
  rw [edgeBoundary_comm (G := G) X Y]
  exact edgeSet_disjoint_edgeBoundary_of_vertexSet_disjoint_left
    (P := P) hP

/-- If a path starts on the left side, stays in the union of the two sides,
and is not wholly contained in the left side, then it crosses the cut. -/
theorem exists_edgeBoundary_of_source_mem_left_of_not_subset_left
    [Fintype V] (P : GraphPath G) {X Y : Finset V}
    (hsub : P.vertexSet ⊆ X ∪ Y)
    (hsource : P.source ∈ X)
    (hnot : ¬ P.vertexSet ⊆ X) :
    ∃ e ∈ P.edgeSet, e ∈ edgeBoundary G X Y := by
  classical
  by_contra hnone
  push Not at hnone
  have hdisj : Disjoint P.edgeSet (edgeBoundary G X Y) := by
    rw [Finset.disjoint_left]
    intro e heP heB
    exact hnone e heP heB
  exact hnot
    (vertexSet_subset_left_of_subset_union_and_edgeSet_disjoint_boundary
      (P := P) hsub (GraphPath.source_mem_vertexSet P) hsource hdisj)

/-- Target-end version of
`exists_edgeBoundary_of_source_mem_left_of_not_subset_left`. -/
theorem exists_edgeBoundary_of_target_mem_left_of_not_subset_left
    [Fintype V] (P : GraphPath G) {X Y : Finset V}
    (hsub : P.vertexSet ⊆ X ∪ Y)
    (htarget : P.target ∈ X)
    (hnot : ¬ P.vertexSet ⊆ X) :
    ∃ e ∈ P.edgeSet, e ∈ edgeBoundary G X Y := by
  classical
  rcases exists_edgeBoundary_of_source_mem_left_of_not_subset_left
      (P := P.reverse)
      (X := X) (Y := Y)
      (by simpa [GraphPath.reverse_vertexSet] using hsub)
      (by simpa using htarget)
      (by
        intro hrev
        exact hnot (by simpa [GraphPath.reverse_vertexSet] using hrev)) with
    ⟨e, heRev, heB⟩
  exact ⟨e, by simpa [GraphPath.reverse_edgeSet] using heRev, heB⟩

/-- The endpoints of a graph path that lie on the left side of a disjoint cut
can be charged to distinct cut edges, provided the path stays in the union of
the two sides and is not wholly contained in the left side.  The two-endpoint
case is the formal version of the paper's sentence that a path with both
endpoints in `X` and not contained in `X` contributes at least two edges to
`E(X,Y)`. -/
theorem endpoint_left_card_le_boundary_edges_of_not_subset_left
    [Fintype V] (P : GraphPath G) {X Y : Finset V}
    (hXY : Disjoint X Y)
    (hsub : P.vertexSet ⊆ X ∪ Y)
    (hnot : ¬ P.vertexSet ⊆ X) :
    ((({P.source, P.target} : Finset V) ∩ X).card) ≤
      (P.edgeSet ∩ edgeBoundary G X Y).card := by
  classical
  by_cases hsourceX : P.source ∈ X
  · by_cases htargetX : P.target ∈ X
    · have hYnonempty : (P.vertexSet ∩ Y).Nonempty := by
        by_contra hnoY
        have hsubX : P.vertexSet ⊆ X := by
          intro v hv
          rcases Finset.mem_union.1 (hsub hv) with hvX | hvY
          · exact hvX
          · have : v ∈ P.vertexSet ∩ Y := Finset.mem_inter.2 ⟨hv, hvY⟩
            exact False.elim (hnoY ⟨v, this⟩)
        exact hnot hsubX
      let Q := P.cleanPrefixToSet Y hYnonempty
      have hQsourceX : Q.source ∈ X := by
        simpa [Q]
      have hQtargetY : Q.target ∈ Y := by
        simpa [Q] using P.cleanPrefixToSet_target_mem Y hYnonempty
      have hQne : Q.source ≠ Q.target := by
        intro h
        exact Finset.disjoint_left.mp hXY hQsourceX (by simpa [h] using hQtargetY)
      have hQpen_ne_target : Q.penultimate ≠ Q.target := by
        exact (Q.penultimate_adj_target hQne).ne
      have hQpen_mem : Q.penultimate ∈ Q.vertexSet :=
        Q.penultimate_mem_vertexSet hQne
      have hQpenX : Q.penultimate ∈ X := by
        have hpenP : Q.penultimate ∈ P.vertexSet :=
          P.cleanPrefixToSet_vertexSet_subset Y hYnonempty hQpen_mem
        rcases Finset.mem_union.1 (hsub hpenP) with hpenX | hpenY
        · exact hpenX
        · exact False.elim (by
            rcases (P.cleanPrefixToSet_internallyDisjointFromSet Y hYnonempty)
                hQpen_mem hpenY with hsrc | htgt
            · exact Finset.disjoint_left.mp hXY hQsourceX
                (by simpa [hsrc] using hpenY)
            · exact hQpen_ne_target htgt)
      let e₁ : Sym2 V := s(Q.penultimate, Q.target)
      have he₁Q : e₁ ∈ Q.edgeSet := by
        simpa [e₁] using
          GraphPath.penultimate_edge_mem_edgeSet (P := Q) hQne
      have he₁P : e₁ ∈ P.edgeSet := by
        simpa [Q, GraphPath.cleanPrefixToSet, e₁] using
          GraphPath.takeUntil_edgeSet_subset (P := P)
            (P.firstHitVertex_mem_vertexSet Y hYnonempty) he₁Q
      have he₁B : e₁ ∈ edgeBoundary G X Y := by
        exact (mem_edgeBoundary (G := G) X Y e₁).2
          ⟨by
              simpa [_root_.SimpleGraph.mem_edgeSet, e₁] using
                Q.penultimate_adj_target hQne,
            Q.penultimate, hQpenX, Q.target, hQtargetY, by simp [e₁]⟩
      have hbefore₁ : P.Before Q.penultimate Q.target := by
        simpa [Q, GraphPath.cleanPrefixToSet] using
          P.before_of_mem_takeUntil
            (P.firstHitVertex_mem_vertexSet Y hYnonempty) hQpen_mem
      let R := P.cleanSuffixFromSet Y hYnonempty
      have hRsourceY : R.source ∈ Y := by
        simpa [R] using P.cleanSuffixFromSet_source_mem Y hYnonempty
      have hRtargetX : R.target ∈ X := by
        simpa [R]
      have hRne : R.source ≠ R.target := by
        intro h
        exact Finset.disjoint_left.mp hXY hRtargetX (by simpa [h] using hRsourceY)
      have hRsnd_ne_source : R.walk.snd ≠ R.source := by
        exact (R.walk.adj_snd (R.walk_not_nil_of_source_ne_target hRne)).ne.symm
      have hRsnd_mem : R.walk.snd ∈ R.vertexSet :=
        GraphPath.snd_mem_vertexSet (P := R) hRne
      have hRsndX : R.walk.snd ∈ X := by
        have hsndP : R.walk.snd ∈ P.vertexSet :=
          P.cleanSuffixFromSet_vertexSet_subset Y hYnonempty hRsnd_mem
        rcases Finset.mem_union.1 (hsub hsndP) with hsndX | hsndY
        · exact hsndX
        · rcases (P.cleanSuffixFromSet_internallyDisjointFromSet Y hYnonempty)
            hRsnd_mem hsndY with hsrc | htgt
          · exact False.elim (hRsnd_ne_source hsrc)
          · exact False.elim
              (Finset.disjoint_left.mp hXY hRtargetX (by simpa [htgt] using hsndY))
      let e₂ : Sym2 V := s(R.walk.snd, R.source)
      have he₂R : e₂ ∈ R.edgeSet := by
        have hfirst : s(R.source, R.walk.snd) ∈ R.edgeSet :=
          GraphPath.snd_edge_mem_edgeSet (P := R) hRne
        simpa [e₂, Sym2.eq_swap] using hfirst
      have he₂P : e₂ ∈ P.edgeSet :=
        P.cleanSuffixFromSet_edgeSet_subset Y hYnonempty he₂R
      have he₂B : e₂ ∈ edgeBoundary G X Y := by
        exact (mem_edgeBoundary (G := G) X Y e₂).2
          ⟨by
              have hadj : G.Adj R.source R.walk.snd :=
                R.walk.adj_snd (R.walk_not_nil_of_source_ne_target hRne)
              simpa [_root_.SimpleGraph.mem_edgeSet, e₂, Sym2.eq_swap] using hadj,
            R.walk.snd, hRsndX, R.source, hRsourceY, by simp [e₂]⟩
      have hbefore₂ : P.Before R.source R.walk.snd := by
        refine ⟨P.lastHitVertex_mem_vertexSet Y hYnonempty, ?_⟩
        simpa [R, GraphPath.cleanSuffixFromSet] using hRsnd_mem
      have he_ne : e₁ ≠ e₂ := by
        intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with heq | heq
        · rcases heq with ⟨hpen_snd, htarget_source⟩
          have hback : P.Before Q.target Q.penultimate := by
            simpa [hpen_snd, htarget_source] using hbefore₂
          exact hQpen_ne_target (P.before_antisymm hbefore₁ hback)
        · rcases heq with ⟨hpen_source, htarget_snd⟩
          exact Finset.disjoint_left.mp hXY hQpenX
            (by simpa [hpen_source] using hRsourceY)
      have hpair_subset :
          ({e₁, e₂} : Finset (Sym2 V)) ⊆
            P.edgeSet ∩ edgeBoundary G X Y := by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact Finset.mem_inter.2 ⟨he₁P, he₁B⟩
        · exact Finset.mem_inter.2 ⟨he₂P, he₂B⟩
      have htwo_boundary :
          2 ≤ (P.edgeSet ∩ edgeBoundary G X Y).card := by
        have hcard_pair :
            ({e₁, e₂} : Finset (Sym2 V)).card = 2 := by
          exact Finset.card_pair he_ne
        rw [← hcard_pair]
        exact Finset.card_le_card hpair_subset
      have hend_le_two :
          ((({P.source, P.target} : Finset V) ∩ X).card) ≤ 2 := by
        exact (Finset.card_le_card (Finset.inter_subset_left)).trans
          (Finset.card_le_two (a := P.source) (b := P.target))
      exact hend_le_two.trans htwo_boundary
    · have hboundary_pos :
          0 < (P.edgeSet ∩ edgeBoundary G X Y).card := by
        rcases GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
            (P := P) hsub hsourceX hnot with ⟨e, heP, heB⟩
        exact Finset.card_pos.2 ⟨e, Finset.mem_inter.2 ⟨heP, heB⟩⟩
      have hend_le_one :
          ((({P.source, P.target} : Finset V) ∩ X).card) ≤ 1 := by
        have hsubEnd :
            (({P.source, P.target} : Finset V) ∩ X) ⊆
              ({P.source} : Finset V) := by
          intro v hv
          rcases Finset.mem_inter.1 hv with ⟨hvEnd, hvX⟩
          rw [Finset.mem_insert, Finset.mem_singleton] at hvEnd
          simp
          rcases hvEnd with rfl | rfl
          · rfl
          · exact False.elim (htargetX hvX)
        exact (Finset.card_le_card hsubEnd).trans (by simp)
      exact hend_le_one.trans (Nat.succ_le_iff.2 hboundary_pos)
  · by_cases htargetX : P.target ∈ X
    · have hboundary_pos :
          0 < (P.edgeSet ∩ edgeBoundary G X Y).card := by
        rcases GraphPath.exists_edgeBoundary_of_target_mem_left_of_not_subset_left
            (P := P) hsub htargetX hnot with ⟨e, heP, heB⟩
        exact Finset.card_pos.2 ⟨e, Finset.mem_inter.2 ⟨heP, heB⟩⟩
      have hend_le_one :
          ((({P.source, P.target} : Finset V) ∩ X).card) ≤ 1 := by
        have hsubEnd :
            (({P.source, P.target} : Finset V) ∩ X) ⊆
              ({P.target} : Finset V) := by
          intro v hv
          rcases Finset.mem_inter.1 hv with ⟨hvEnd, hvX⟩
          rw [Finset.mem_insert, Finset.mem_singleton] at hvEnd
          simp
          rcases hvEnd with rfl | rfl
          · exact False.elim (hsourceX hvX)
          · rfl
        exact (Finset.card_le_card hsubEnd).trans (by simp)
      exact hend_le_one.trans (Nat.succ_le_iff.2 hboundary_pos)
    · have hend_empty :
          (({P.source, P.target} : Finset V) ∩ X) = ∅ := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_inter.1 hv with ⟨hvEnd, hvX⟩
          rw [Finset.mem_insert, Finset.mem_singleton] at hvEnd
          rcases hvEnd with rfl | rfl
          · exact False.elim (hsourceX hvX)
          · exact False.elim (htargetX hvX)
        · intro hv
          simp at hv
      simp [hend_empty]

/-- The two endpoints of a path, restricted to a side of a cut. -/
noncomputable def endpointSetIn (P : GraphPath G) (X : Finset V) :
    Finset V :=
  ({P.source, P.target} : Finset V) ∩ X

end GraphPath

namespace PathPacking

variable {S T : Finset V}

/-- A selected subfamily of paths from a path packing. -/
abbrev Subfamily (P : PathPacking G S T) := Finset P.Index

/-- The selected paths from `P` whose vertices are contained in a finite
cluster `C`. -/
noncomputable def containedInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V) :
    Finset P.Index := by
  classical
  exact I.filter fun i => (P.path i).vertexSet ⊆ C

theorem mem_containedInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V)
    (i : P.Index) :
    i ∈ containedInCluster P I C ↔
      i ∈ I ∧ (P.path i).vertexSet ⊆ C := by
  classical
  simp [containedInCluster]

/-- The endpoints of the selected paths contained in `C`.  This is the formal
`Γ(C)` from Section 4.4. -/
noncomputable def endpointSetInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V) :
    Finset V := by
  classical
  let J := containedInCluster P I C
  exact (J.image fun i => (P.path i).source) ∪
    (J.image fun i => (P.path i).target)

/-- Source endpoints of the selected paths contained in `C`. -/
noncomputable def sourceEndpointSetInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V) :
    Finset V := by
  classical
  exact (containedInCluster P I C).image fun i => (P.path i).source

/-- Target endpoints of the selected paths contained in `C`. -/
noncomputable def targetEndpointSetInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V) :
    Finset V := by
  classical
  exact (containedInCluster P I C).image fun i => (P.path i).target

theorem endpointSetInCluster_eq_source_union_target
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V) :
    endpointSetInCluster P I C =
      sourceEndpointSetInCluster P I C ∪
        targetEndpointSetInCluster P I C := by
  classical
  rfl

theorem endpointSetInCluster_subset_cluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V) :
    endpointSetInCluster P I C ⊆ C := by
  classical
  intro v hv
  rw [endpointSetInCluster] at hv
  rcases Finset.mem_union.1 hv with hv | hv
  · rcases Finset.mem_image.1 hv with ⟨i, hi, rfl⟩
    exact ((mem_containedInCluster P I C i).1 hi).2
      (GraphPath.source_mem_vertexSet (P.path i))
  · rcases Finset.mem_image.1 hv with ⟨i, hi, rfl⟩
    exact ((mem_containedInCluster P I C i).1 hi).2
      (GraphPath.target_mem_vertexSet (P.path i))

theorem mem_endpointSetInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V)
    (v : V) :
    v ∈ endpointSetInCluster P I C ↔
      (∃ i ∈ containedInCluster P I C, (P.path i).source = v) ∨
        (∃ i ∈ containedInCluster P I C, (P.path i).target = v) := by
  classical
  rw [endpointSetInCluster]
  constructor
  · intro hv
    rcases Finset.mem_union.1 hv with hv | hv
    · rcases Finset.mem_image.1 hv with ⟨i, hi, hsrc⟩
      exact Or.inl ⟨i, hi, hsrc⟩
    · rcases Finset.mem_image.1 hv with ⟨i, hi, htgt⟩
      exact Or.inr ⟨i, hi, htgt⟩
  · rintro (⟨i, hi, hsrc⟩ | ⟨i, hi, htgt⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_image.2 ⟨i, hi, hsrc⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨i, hi, htgt⟩)

theorem mem_sourceEndpointSetInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V)
    (v : V) :
    v ∈ sourceEndpointSetInCluster P I C ↔
      ∃ i ∈ containedInCluster P I C, (P.path i).source = v := by
  classical
  simp [sourceEndpointSetInCluster]

theorem mem_targetEndpointSetInCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V)
    (v : V) :
    v ∈ targetEndpointSetInCluster P I C ↔
      ∃ i ∈ containedInCluster P I C, (P.path i).target = v := by
  classical
  simp [targetEndpointSetInCluster]

/-- The endpoint set of a cluster, restricted to `X`, is the union over the
contained selected paths of their two endpoints restricted to `X`. -/
theorem endpointSetInCluster_inter_eq_biUnion_endpointSetIn
    (P : PathPacking G S T) (I : Subfamily P) (C X : Finset V) :
    endpointSetInCluster P I C ∩ X =
      (containedInCluster P I C).biUnion
        (fun i => GraphPath.endpointSetIn (P.path i) X) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.1 hv with ⟨hvEnd, hvX⟩
    rcases (mem_endpointSetInCluster P I C v).1 hvEnd with
      ⟨i, hi, hsrc⟩ | ⟨i, hi, htgt⟩
    · exact Finset.mem_biUnion.2
        ⟨i, hi, by
          rw [GraphPath.endpointSetIn, Finset.mem_inter]
          exact ⟨by simp [hsrc], hvX⟩⟩
    · exact Finset.mem_biUnion.2
        ⟨i, hi, by
          rw [GraphPath.endpointSetIn, Finset.mem_inter]
          exact ⟨by simp [htgt], hvX⟩⟩
  · intro hv
    rcases Finset.mem_biUnion.1 hv with ⟨i, hi, hvi⟩
    change v ∈ ({(P.path i).source, (P.path i).target} : Finset V) ∩ X at hvi
    rcases Finset.mem_inter.1 hvi with ⟨hvPair, hvX⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hvPair
    refine Finset.mem_inter.2 ⟨?_, hvX⟩
    rcases hvPair with hsrc | htgt
    · exact (mem_endpointSetInCluster P I C v).2
        (Or.inl ⟨i, hi, hsrc.symm⟩)
    · exact (mem_endpointSetInCluster P I C v).2
        (Or.inr ⟨i, hi, htgt.symm⟩)

/-- Endpoint sets of distinct paths in a node-disjoint packing are disjoint. -/
theorem pairwiseDisjoint_endpointSetIn
    (P : PathPacking G S T) (J : Finset P.Index) (X : Finset V) :
    (↑J : Set P.Index).PairwiseDisjoint
      (fun i => GraphPath.endpointSetIn (P.path i) X) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hnonempty
  rcases hnonempty with ⟨v, hv⟩
  rcases Finset.mem_inter.1 hv with ⟨hvi, hvj⟩
  have hviPath : v ∈ (P.path i).vertexSet := by
    change v ∈ ({(P.path i).source, (P.path i).target} : Finset V) ∩ X at hvi
    rcases Finset.mem_inter.1 hvi with ⟨hvEnd, _hvX⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hvEnd
    rcases hvEnd with rfl | rfl
    · exact GraphPath.source_mem_vertexSet (P.path i)
    · exact GraphPath.target_mem_vertexSet (P.path i)
  have hvjPath : v ∈ (P.path j).vertexSet := by
    change v ∈ ({(P.path j).source, (P.path j).target} : Finset V) ∩ X at hvj
    rcases Finset.mem_inter.1 hvj with ⟨hvEnd, _hvX⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hvEnd
    rcases hvEnd with rfl | rfl
    · exact GraphPath.source_mem_vertexSet (P.path j)
    · exact GraphPath.target_mem_vertexSet (P.path j)
  by_contra hne
  exact Finset.disjoint_left.mp (P.node_disjoint hne) hviPath hvjPath

/-- Edge sets of distinct paths in a node-disjoint packing are disjoint, even
after intersecting with a common finite edge set. -/
theorem pairwiseDisjoint_edgeSet_inter
    (P : PathPacking G S T) (J : Finset P.Index) (F : Finset (Sym2 V)) :
    (↑J : Set P.Index).PairwiseDisjoint
      (fun i => (P.path i).edgeSet ∩ F) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hnonempty
  rcases hnonempty with ⟨e, he⟩
  rcases Finset.mem_inter.1 he with ⟨hei, hej⟩
  have heiPath : e ∈ (P.path i).edgeSet := (Finset.mem_inter.1 hei).1
  have hejPath : e ∈ (P.path j).edgeSet := (Finset.mem_inter.1 hej).1
  by_contra hne
  have hEdgeDisj :
      GraphPath.EdgeDisjoint (P.path i) (P.path j) :=
    GraphPath.edgeDisjoint_of_nodeDisjoint (P.node_disjoint hne)
  exact Finset.disjoint_left.mp hEdgeDisj heiPath hejPath

@[simp] theorem containedInCluster_univ [Fintype V]
    (P : PathPacking G S T) (I : Subfamily P) :
    containedInCluster P I (Finset.univ : Finset V) = I := by
  classical
  ext i
  simp [containedInCluster]

@[simp] theorem containedInCluster_univ_card [Fintype V]
    (P : PathPacking G S T) (I : Subfamily P) :
    (containedInCluster P I (Finset.univ : Finset V)).card = I.card := by
  simp

/-- The selected paths whose edge sets meet a finite deleted-edge set.  These
are the paths destroyed by the deletions in the proof of Theorem 4.11. -/
noncomputable def hitEdges
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    Finset P.Index := by
  classical
  exact I.filter fun i => ¬ Disjoint (P.path i).edgeSet F

theorem mem_hitEdges
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V))
    (i : P.Index) :
    i ∈ hitEdges P I F ↔
      i ∈ I ∧ ¬ Disjoint (P.path i).edgeSet F := by
  classical
  simp [hitEdges]

/-- The selected paths that avoid all deleted edges. -/
noncomputable def surviving
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    Finset P.Index := by
  classical
  exact I \ hitEdges P I F

theorem mem_surviving
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V))
    (i : P.Index) :
    i ∈ surviving P I F ↔
      i ∈ I ∧ Disjoint (P.path i).edgeSet F := by
  classical
  rw [surviving, Finset.mem_sdiff, mem_hitEdges]
  constructor
  · intro h
    exact ⟨h.1, by
      by_contra hdisj
      exact h.2 ⟨h.1, hdisj⟩⟩
  · intro h
    exact ⟨h.1, by
      intro hhit
      exact hhit.2 h.2⟩

theorem hitEdges_subset
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    hitEdges P I F ⊆ I := by
  intro i hi
  exact ((mem_hitEdges P I F i).1 hi).1

theorem surviving_subset
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    surviving P I F ⊆ I := by
  intro i hi
  exact ((mem_surviving P I F i).1 hi).1

/-- Surviving and destroyed selected paths partition the selected family. -/
theorem surviving_union_hitEdges
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    surviving P I F ∪ hitEdges P I F = I := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.1 hi with hsurv | hhit
    · exact surviving_subset P I F hsurv
    · exact hitEdges_subset P I F hhit
  · intro hi
    by_cases hhit : i ∈ hitEdges P I F
    · exact Finset.mem_union_right _ hhit
    · exact Finset.mem_union_left _
        (by
          change i ∈ I \ hitEdges P I F
          exact Finset.mem_sdiff.2 ⟨hi, hhit⟩)

theorem disjoint_surviving_hitEdges
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    Disjoint (surviving P I F) (hitEdges P I F) := by
  classical
  rw [Finset.disjoint_left]
  intro i hsurv hhit
  exact (Finset.mem_sdiff.1 (by simpa [surviving] using hsurv)).2 hhit

/-- Cardinal form of the destroyed/surviving partition. -/
theorem surviving_card_add_hitEdges_card
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    (surviving P I F).card + (hitEdges P I F).card = I.card := by
  classical
  rw [← Finset.card_union_of_disjoint
    (disjoint_surviving_hitEdges P I F)]
  rw [surviving_union_hitEdges]

/-- A finite set of deleted edges destroys at most that many paths from a
node-disjoint path family.  The proof injects every destroyed path into a
deleted edge lying on it; node-disjointness makes this choice injective. -/
theorem hitEdges_card_le
    (P : PathPacking G S T) (I : Subfamily P) (F : Finset (Sym2 V)) :
    (hitEdges P I F).card ≤ F.card := by
  classical
  let chooseHit :
      (i : {i : P.Index // i ∈ hitEdges P I F}) →
        {e : Sym2 V // e ∈ F} := by
    intro i
    have hnot : ¬ Disjoint (P.path i.1).edgeSet F :=
      ((mem_hitEdges P I F i.1).1 i.2).2
    let e := Classical.choose (Finset.not_disjoint_iff.1 hnot)
    have heF : e ∈ F :=
      (Classical.choose_spec (Finset.not_disjoint_iff.1 hnot)).2
    exact ⟨e, heF⟩
  have hchoose_path :
      ∀ i : {i : P.Index // i ∈ hitEdges P I F},
        (chooseHit i).1 ∈ (P.path i.1).edgeSet := by
    intro i
    dsimp [chooseHit]
    have hnot : ¬ Disjoint (P.path i.1).edgeSet F :=
      ((mem_hitEdges P I F i.1).1 i.2).2
    simpa using (Classical.choose_spec
      (Finset.not_disjoint_iff.1 hnot)).1
  have hinj : Function.Injective chooseHit := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hEdgeDisj :
        GraphPath.EdgeDisjoint (P.path i.1) (P.path j.1) :=
      GraphPath.edgeDisjoint_of_nodeDisjoint (P.node_disjoint hne)
    have heq : (chooseHit i).1 = (chooseHit j).1 :=
      congrArg Subtype.val hij
    have hej : (chooseHit i).1 ∈ (P.path j.1).edgeSet := by
      simpa [heq] using hchoose_path j
    exact Finset.disjoint_left.mp hEdgeDisj (hchoose_path i) hej
  have hcard := Fintype.card_le_of_injective chooseHit hinj
  simpa using hcard

/-- If a selected path is contained in the left side of a cut, then it
survives deletion of the cut boundary. -/
theorem mem_surviving_edgeBoundary_of_vertexSet_subset_left [Fintype V]
    (P : PathPacking G S T) (I : Subfamily P)
    {X Y : Finset V} (hXY : Disjoint X Y)
    {i : P.Index} (hi : i ∈ I) (hsub : (P.path i).vertexSet ⊆ X) :
    i ∈ surviving P I (edgeBoundary G X Y) := by
  rw [mem_surviving]
  exact ⟨hi,
    GraphPath.edgeSet_disjoint_edgeBoundary_of_vertexSet_subset_left
      (P := P.path i) hXY hsub⟩

/-- If a selected path is contained in the right side of a cut, then it
survives deletion of the cut boundary. -/
theorem mem_surviving_edgeBoundary_of_vertexSet_subset_right [Fintype V]
    (P : PathPacking G S T) (I : Subfamily P)
    {X Y : Finset V} (hXY : Disjoint X Y)
    {i : P.Index} (hi : i ∈ I) (hsub : (P.path i).vertexSet ⊆ Y) :
    i ∈ surviving P I (edgeBoundary G X Y) := by
  rw [mem_surviving]
  exact ⟨hi,
    GraphPath.edgeSet_disjoint_edgeBoundary_of_vertexSet_subset_right
      (P := P.path i) hXY hsub⟩

/-- A cluster is good when its endpoint set is weakly edge-well-linked inside
the cluster. -/
def GoodCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V) (w : ℕ) :
    Prop :=
  WeakEdgeWellLinkedIn G C (endpointSetInCluster P I C) w

/-- A cluster is happy when it is good and contains at least `D` selected
`Σ`-paths. -/
def HappyCluster
    (P : PathPacking G S T) (I : Subfamily P) (C : Finset V)
    (w D : ℕ) : Prop :=
  GoodCluster P I C w ∧ D ≤ (containedInCluster P I C).card

theorem intersectingRightIndices_subset
    {S T S' T' : Finset V} [Fintype V]
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Qset : Finset Q.Index) (r : R.Index) :
    R.intersectingRightIndices Q Qset r ⊆ Qset := by
  classical
  intro q hq
  exact (Finset.mem_filter.1 (by
    change q ∈ Qset.filter (fun q => PathPacking.PathsIntersect (R.path r) (Q.path q))
    simpa [PathPacking.intersectingRightIndices] using hq)).1

theorem intersectingLeftIndices_subset
    {S T S' T' : Finset V} [Fintype V]
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (q : Q.Index) :
    R.intersectingLeftIndices Q Rset q ⊆ Rset := by
  classical
  intro r hr
  exact (Finset.mem_filter.1 (by
    change r ∈ Rset.filter (fun r => PathPacking.PathsIntersect (R.path r) (Q.path q))
    simpa [PathPacking.intersectingLeftIndices] using hr)).1

/-- A formal state of the Section 4.4 splitting algorithm.

The paper starts with one cluster, repeatedly splits a bad cluster by a sparse
cut, and accumulates the cut edges in `deletedEdges`.  This structure records
the invariant needed for the counting argument: clusters are disjoint,
surviving selected `Σ`-paths are assigned to clusters, each cluster contains a
surviving path, and the number of deleted edges is at most
`(|C|-1) * w`. -/
structure DecompositionState [Fintype V]
    (P : PathPacking G S T) (I : Subfamily P) (w : ℕ) where
  /-- The finite index type for the current clusters. -/
  ClusterIndex : Type u
  /-- The cluster index type is finite. -/
  [clusterFintype : Fintype ClusterIndex]
  /-- The cluster index type has decidable equality. -/
  [clusterDecidableEq : DecidableEq ClusterIndex]
  /-- The vertex set of each current cluster. -/
  cluster : ClusterIndex → Finset V
  /-- Current clusters are pairwise vertex-disjoint. -/
  cluster_disjoint :
    Pairwise fun c d => Disjoint (cluster c) (cluster d)
  /-- The set of all edges deleted by previous sparse cuts. -/
  deletedEdges : Finset (Sym2 V)
  /-- Every edge leaving a current cluster has already been deleted. -/
  boundary_deleted :
    ∀ c : ClusterIndex, clusterBoundary G (cluster c) ⊆ deletedEdges
  /-- A selected `Σ`-path contained in a current cluster uses none of the
  deleted edges.  In the splitting algorithm, deleted edges are always cut
  edges between sibling clusters, never internal edges of a descendant. -/
  contained_path_disjoint_deleted :
    ∀ (c : ClusterIndex) (i : P.Index), i ∈ I →
      (P.path i).vertexSet ⊆ cluster c →
        Disjoint (P.path i).edgeSet deletedEdges
  /-- Every surviving selected path is contained in one current cluster. -/
  surviving_contained :
    ∀ i ∈ surviving P I deletedEdges,
      ∃ c : ClusterIndex, (P.path i).vertexSet ⊆ cluster c
  /-- Every current cluster still contains at least one surviving selected
  path.  This is the formal version of the paragraph after Observation 4.10
  showing both children of every split are nonempty for `Σ`. -/
  cluster_has_survivor :
    ∀ c : ClusterIndex,
      ∃ i ∈ surviving P I deletedEdges, (P.path i).vertexSet ⊆ cluster c
  /-- At most `w` edges are deleted per split.  Since a state with `r`
  clusters is reached after `r-1` splits, the paper's budget is
  `|E'| ≤ (r-1)w`. -/
  deleted_budget :
    deletedEdges.card ≤ (@Fintype.card ClusterIndex clusterFintype - 1) * w

attribute [instance] DecompositionState.clusterFintype
attribute [instance] DecompositionState.clusterDecidableEq

namespace DecompositionState

variable [Fintype V]

/-- Number of clusters in a decomposition state. -/
noncomputable def clusterCount
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) : ℕ := by
  exact @Fintype.card D.ClusterIndex D.clusterFintype

/-- The initial decomposition state: one cluster containing all vertices and
no deleted edges.  This is the first line of the proof of Theorem 4.11. -/
noncomputable def initial
    (P : PathPacking G S T) (I : Subfamily P) (w : ℕ)
    (hI : I.Nonempty) : DecompositionState (V := V) (G := G) P I w where
  ClusterIndex := PUnit
  cluster := fun _ => Finset.univ
  cluster_disjoint := by
    intro a b hne
    cases a
    cases b
    exact (hne rfl).elim
  deletedEdges := ∅
  boundary_deleted := by
    intro c e he
    cases c
    simp [clusterBoundary] at he
  contained_path_disjoint_deleted := by
    intro c i hi hsub
    rw [Finset.disjoint_left]
    intro e he hdel
    simp at hdel
  surviving_contained := by
    intro i hi
    refine ⟨PUnit.unit, ?_⟩
    intro v hv
    simp
  cluster_has_survivor := by
    intro c
    rcases hI with ⟨i, hiI⟩
    refine ⟨i, ?_, ?_⟩
    · rw [mem_surviving]
      exact ⟨hiI, by simp⟩
    · intro v hv
      simp
  deleted_budget := by
    simp

/-- Cluster indices after splitting one cluster `c`: all old clusters except
`c`, plus two new children.  `false` denotes the left child and `true` the
right child. -/
abbrev SplitIndex
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex) : Type u :=
  Sum {d : D.ClusterIndex // d ≠ c} Bool

/-- The cluster map after splitting `c` by a sparse cut. -/
noncomputable def splitCluster
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    D.SplitIndex c → Finset V
  | Sum.inl d => D.cluster d.1
  | Sum.inr false => Cut.X
  | Sum.inr true => Cut.Y

private theorem left_subset_of_sparse_cut
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    Cut.X ⊆ D.cluster c := by
  intro v hv
  have hvUnion : v ∈ Cut.X ∪ Cut.Y := Finset.mem_union_left _ hv
  simpa [Cut.cover] using hvUnion

private theorem right_subset_of_sparse_cut
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    Cut.Y ⊆ D.cluster c := by
  intro v hv
  have hvUnion : v ∈ Cut.X ∪ Cut.Y := Finset.mem_union_right _ hv
  simpa [Cut.cover] using hvUnion

theorem splitCluster_disjoint
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    Pairwise fun a b : D.SplitIndex c =>
      Disjoint (D.splitCluster c Cut a) (D.splitCluster c Cut b) := by
  classical
  intro a b hab
  cases a with
  | inl aold =>
      cases b with
      | inl bold =>
          exact D.cluster_disjoint (by
            intro hval
            exact hab (by
              apply congrArg Sum.inl
              exact Subtype.ext hval))
      | inr bchild =>
          cases bchild
          · rw [Finset.disjoint_left]
            intro v hvOld hvX
            exact Finset.disjoint_left.mp (D.cluster_disjoint aold.2)
              hvOld (left_subset_of_sparse_cut D c Cut hvX)
          · rw [Finset.disjoint_left]
            intro v hvOld hvY
            exact Finset.disjoint_left.mp (D.cluster_disjoint aold.2)
              hvOld (right_subset_of_sparse_cut D c Cut hvY)
  | inr achild =>
      cases b with
      | inl bold =>
          cases achild
          · rw [Finset.disjoint_left]
            intro v hvX hvOld
            exact Finset.disjoint_left.mp (D.cluster_disjoint bold.2).symm
              (left_subset_of_sparse_cut D c Cut hvX) hvOld
          · rw [Finset.disjoint_left]
            intro v hvY hvOld
            exact Finset.disjoint_left.mp (D.cluster_disjoint bold.2).symm
              (right_subset_of_sparse_cut D c Cut hvY) hvOld
      | inr bchild =>
          cases achild <;> cases bchild
          · exact (hab rfl).elim
          · exact Cut.disjoint
          · exact Cut.disjoint.symm
          · exact (hab rfl).elim

theorem clusterBoundary_left_subset_deleted_union_cut
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    clusterBoundary G Cut.X ⊆
      D.deletedEdges ∪ edgeBoundary G Cut.X Cut.Y := by
  classical
  intro e he
  rcases ((mem_edgeBoundary (G := G) Cut.X
      ((Finset.univ : Finset V) \ Cut.X) e).1
      (by simpa [clusterBoundary] using he)) with
    ⟨heG, x, hxX, y, hyNotX, rfl⟩
  by_cases hyY : y ∈ Cut.Y
  · exact Finset.mem_union_right _
      ((mem_edgeBoundary (G := G) Cut.X Cut.Y s(x, y)).2
        ⟨heG, x, hxX, y, hyY, rfl⟩)
  · have hxC : x ∈ D.cluster c :=
      left_subset_of_sparse_cut D c Cut hxX
    have hyNotC : y ∉ D.cluster c := by
      intro hyC
      have hyUnion : y ∈ Cut.X ∪ Cut.Y := by
        simpa [Cut.cover] using hyC
      rcases Finset.mem_union.1 hyUnion with hyX | hyY'
      · exact (Finset.mem_sdiff.1 hyNotX).2 hyX
      · exact hyY hyY'
    have hparent :
        s(x, y) ∈ clusterBoundary G (D.cluster c) := by
      exact (mem_edgeBoundary (G := G) (D.cluster c)
        ((Finset.univ : Finset V) \ D.cluster c) s(x, y)).2
        ⟨heG, x, hxC, y, by simp [hyNotC], rfl⟩
    exact Finset.mem_union_left _
      (D.boundary_deleted c (by simpa [clusterBoundary] using hparent))

theorem clusterBoundary_right_subset_deleted_union_cut
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    clusterBoundary G Cut.Y ⊆
      D.deletedEdges ∪ edgeBoundary G Cut.X Cut.Y := by
  classical
  intro e he
  rcases ((mem_edgeBoundary (G := G) Cut.Y
      ((Finset.univ : Finset V) \ Cut.Y) e).1
      (by simpa [clusterBoundary] using he)) with
    ⟨heG, y, hyY, x, hxNotY, hxy⟩
  subst hxy
  by_cases hxX : x ∈ Cut.X
  · have hcutYX :
        s(y, x) ∈ edgeBoundary G Cut.Y Cut.X :=
      (mem_edgeBoundary (G := G) Cut.Y Cut.X s(y, x)).2
        ⟨heG, y, hyY, x, hxX, rfl⟩
    exact Finset.mem_union_right _ (by
      rw [edgeBoundary_comm (G := G) Cut.X Cut.Y]
      simpa using hcutYX)
  · have hyC : y ∈ D.cluster c :=
      right_subset_of_sparse_cut D c Cut hyY
    have hxNotC : x ∉ D.cluster c := by
      intro hxC
      have hxUnion : x ∈ Cut.X ∪ Cut.Y := by
        simpa [Cut.cover] using hxC
      rcases Finset.mem_union.1 hxUnion with hxX' | hxY
      · exact hxX hxX'
      · exact (Finset.mem_sdiff.1 hxNotY).2 hxY
    have hparent :
        s(y, x) ∈ clusterBoundary G (D.cluster c) := by
      exact (mem_edgeBoundary (G := G) (D.cluster c)
        ((Finset.univ : Finset V) \ D.cluster c) s(y, x)).2
        ⟨heG, y, hyC, x, by simp [hxNotC], rfl⟩
    exact Finset.mem_union_left _
      (D.boundary_deleted c (by simpa [clusterBoundary] using hparent))

/-- Deleted edges after one split: old deleted edges plus the new cut. -/
noncomputable def splitDeletedEdges
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    Finset (Sym2 V) :=
  D.deletedEdges ∪ edgeBoundary G Cut.X Cut.Y

theorem split_boundary_deleted
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    ∀ a : D.SplitIndex c,
      clusterBoundary G (D.splitCluster c Cut a) ⊆
        D.splitDeletedEdges c Cut := by
  classical
  intro a e he
  cases a with
  | inl old =>
      exact Finset.mem_union_left _
        (D.boundary_deleted old.1 he)
  | inr child =>
      cases child
      · exact clusterBoundary_left_subset_deleted_union_cut D c Cut he
      · exact clusterBoundary_right_subset_deleted_union_cut D c Cut he

theorem split_contained_path_disjoint_deleted
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    ∀ (a : D.SplitIndex c) (i : P.Index), i ∈ I →
      (P.path i).vertexSet ⊆ D.splitCluster c Cut a →
        Disjoint (P.path i).edgeSet (D.splitDeletedEdges c Cut) := by
  classical
  intro a i hiI hsub
  rw [Finset.disjoint_left]
  intro e hePath heDel
  rcases Finset.mem_union.1 heDel with heOld | heCut
  · cases a with
    | inl old =>
        exact Finset.disjoint_left.mp
          (D.contained_path_disjoint_deleted old.1 i hiI hsub)
          hePath heOld
    | inr child =>
        cases child
        · have hsubParent : (P.path i).vertexSet ⊆ D.cluster c :=
            fun v hv => left_subset_of_sparse_cut D c Cut (hsub hv)
          exact Finset.disjoint_left.mp
            (D.contained_path_disjoint_deleted c i hiI hsubParent)
            hePath heOld
        · have hsubParent : (P.path i).vertexSet ⊆ D.cluster c :=
            fun v hv => right_subset_of_sparse_cut D c Cut (hsub hv)
          exact Finset.disjoint_left.mp
            (D.contained_path_disjoint_deleted c i hiI hsubParent)
            hePath heOld
  · cases a with
    | inl old =>
        have hdisjX : Disjoint (P.path i).vertexSet Cut.X := by
          rw [Finset.disjoint_left]
          intro v hvPath hvX
          exact Finset.disjoint_left.mp (D.cluster_disjoint old.2)
            (hsub hvPath) (left_subset_of_sparse_cut D c Cut hvX)
        exact Finset.disjoint_left.mp
          (GraphPath.edgeSet_disjoint_edgeBoundary_of_vertexSet_disjoint_left
            (P := P.path i) hdisjX)
          hePath heCut
    | inr child =>
        cases child
        · exact Finset.disjoint_left.mp
            (GraphPath.edgeSet_disjoint_edgeBoundary_of_vertexSet_subset_left
              (P := P.path i) Cut.disjoint hsub)
            hePath heCut
        · exact Finset.disjoint_left.mp
            (GraphPath.edgeSet_disjoint_edgeBoundary_of_vertexSet_subset_right
              (P := P.path i) Cut.disjoint hsub)
            hePath heCut

theorem split_surviving_contained
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    ∀ i ∈ surviving P I (D.splitDeletedEdges c Cut),
      ∃ a : D.SplitIndex c,
        (P.path i).vertexSet ⊆ D.splitCluster c Cut a := by
  classical
  intro i hiSurv
  have hiData := (mem_surviving P I (D.splitDeletedEdges c Cut) i).1 hiSurv
  have hdisjOld : Disjoint (P.path i).edgeSet D.deletedEdges := by
    rw [Finset.disjoint_left]
    intro e hePath heOld
    exact Finset.disjoint_left.mp hiData.2 hePath
      (Finset.mem_union_left _ heOld)
  have hiOldSurv : i ∈ surviving P I D.deletedEdges :=
    (mem_surviving P I D.deletedEdges i).2 ⟨hiData.1, hdisjOld⟩
  rcases D.surviving_contained i hiOldSurv with ⟨d, hsubD⟩
  by_cases hdc : d = c
  · subst d
    have hsubUnion : (P.path i).vertexSet ⊆ Cut.X ∪ Cut.Y := by
      intro v hv
      have hvC : v ∈ D.cluster c := hsubD hv
      simpa [Cut.cover] using hvC
    have hdisjCut :
        Disjoint (P.path i).edgeSet (edgeBoundary G Cut.X Cut.Y) := by
      rw [Finset.disjoint_left]
      intro e hePath heCut
      exact Finset.disjoint_left.mp hiData.2 hePath
        (Finset.mem_union_right _ heCut)
    have hsourceUnion :
        (P.path i).source ∈ Cut.X ∪ Cut.Y :=
      hsubUnion (GraphPath.source_mem_vertexSet (P.path i))
    rcases Finset.mem_union.1 hsourceUnion with hsourceX | hsourceY
    · refine ⟨Sum.inr false, ?_⟩
      exact GraphPath.vertexSet_subset_left_of_subset_union_and_edgeSet_disjoint_boundary
        (P := P.path i) hsubUnion
        (GraphPath.source_mem_vertexSet (P.path i)) hsourceX hdisjCut
    · refine ⟨Sum.inr true, ?_⟩
      exact GraphPath.vertexSet_subset_right_of_subset_union_and_edgeSet_disjoint_boundary
        (P := P.path i) hsubUnion
        (GraphPath.source_mem_vertexSet (P.path i)) hsourceY hdisjCut
  · exact ⟨Sum.inl ⟨d, hdc⟩, hsubD⟩

@[simp] theorem splitIndex_card
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex) :
    Fintype.card (D.SplitIndex c) = D.clusterCount + 1 := by
  classical
  change Fintype.card (Sum {d : D.ClusterIndex // d ≠ c} Bool) =
    D.clusterCount + 1
  rw [Fintype.card_sum, Fintype.card_bool]
  have hsub :
      Fintype.card {d : D.ClusterIndex // d ≠ c} =
        D.clusterCount - 1 := by
    let f : {d : D.ClusterIndex // d ≠ c} → D.ClusterIndex := fun d => d.1
    have hinj : Function.Injective f := by
      intro a b h
      exact Subtype.ext h
    have hcardImage :
        Fintype.card {d : D.ClusterIndex // d ≠ c} =
          ((Finset.univ : Finset {d : D.ClusterIndex // d ≠ c}).image
            f).card := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have himage :
        ((Finset.univ : Finset {d : D.ClusterIndex // d ≠ c}).image
          f) =
          (Finset.univ : Finset D.ClusterIndex).erase c := by
      ext d
      constructor
      · intro hd
        rcases Finset.mem_image.1 hd with ⟨x, _hx, rfl⟩
        simpa [f] using x.2
      · intro hd
        have hdc : d ≠ c := by
          exact (Finset.mem_erase.1 hd).1
        exact Finset.mem_image.2 ⟨⟨d, hdc⟩, by simp, rfl⟩
    rw [hcardImage, himage, Finset.card_erase_of_mem (by simp)]
    simp [DecompositionState.clusterCount]
  rw [hsub]
  have hpos : 0 < D.clusterCount := by
    change 0 < Fintype.card D.ClusterIndex
    exact Fintype.card_pos_iff.2 ⟨c⟩
  omega

theorem split_deleted_budget
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    (D.splitDeletedEdges c Cut).card ≤
      (Fintype.card (D.SplitIndex c) - 1) * w := by
  classical
  have hnew :
      (D.splitDeletedEdges c Cut).card ≤
        D.deletedEdges.card + (edgeBoundary G Cut.X Cut.Y).card := by
    simpa [splitDeletedEdges] using
      Finset.card_union_le D.deletedEdges (edgeBoundary G Cut.X Cut.Y)
  have hcut : (edgeBoundary G Cut.X Cut.Y).card ≤ w :=
    Nat.le_of_lt Cut.boundary_lt_w
  have hsum :
      (D.splitDeletedEdges c Cut).card ≤
        (D.clusterCount - 1) * w + w := by
    exact hnew.trans (Nat.add_le_add D.deleted_budget hcut)
  have hpos : 0 < D.clusterCount := by
    change 0 < Fintype.card D.ClusterIndex
    exact Fintype.card_pos_iff.2 ⟨c⟩
  have hbudget_eq :
      (D.clusterCount - 1) * w + w = D.clusterCount * w := by
    calc
      (D.clusterCount - 1) * w + w =
          ((D.clusterCount - 1) + 1) * w := by ring
      _ = D.clusterCount * w := by
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
  have htarget :
      (Fintype.card (D.SplitIndex c) - 1) * w =
        D.clusterCount * w := by
    rw [splitIndex_card]
    simp
  rwa [htarget, ← hbudget_eq]

/-- One step of the Section 4.4 splitting algorithm, assuming the two child
survivor witnesses supplied by the sparse-cut counting argument. -/
noncomputable def splitState
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w)
    (hleft :
      ∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
        (P.path i).vertexSet ⊆ Cut.X)
    (hright :
      ∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
        (P.path i).vertexSet ⊆ Cut.Y) :
    DecompositionState (V := V) (G := G) P I w where
  ClusterIndex := D.SplitIndex c
  cluster := D.splitCluster c Cut
  cluster_disjoint := D.splitCluster_disjoint c Cut
  deletedEdges := D.splitDeletedEdges c Cut
  boundary_deleted := D.split_boundary_deleted c Cut
  contained_path_disjoint_deleted :=
    D.split_contained_path_disjoint_deleted c Cut
  surviving_contained := D.split_surviving_contained c Cut
  cluster_has_survivor := by
    intro a
    cases a with
    | inl old =>
        rcases D.cluster_has_survivor old.1 with ⟨i, hiSurv, hsub⟩
        have hiI : i ∈ I :=
          (mem_surviving P I D.deletedEdges i).1 hiSurv |>.1
        have hnewDisj :
            Disjoint (P.path i).edgeSet (D.splitDeletedEdges c Cut) :=
          D.split_contained_path_disjoint_deleted c Cut
            (Sum.inl old) i hiI hsub
        have hiNew :
            i ∈ surviving P I (D.splitDeletedEdges c Cut) :=
          (mem_surviving P I (D.splitDeletedEdges c Cut) i).2
            ⟨hiI, hnewDisj⟩
        exact ⟨i, hiNew, hsub⟩
    | inr child =>
        cases child
        · rcases hleft with ⟨i, hiSurv, hsub⟩
          exact ⟨i, hiSurv, hsub⟩
        · rcases hright with ⟨i, hiSurv, hsub⟩
          exact ⟨i, hiSurv, hsub⟩
  deleted_budget := D.split_deleted_budget c Cut

/-- The two survivor witnesses needed to perform a split.  The crossing-count
part of the proof of Theorem 4.11 is exactly the construction of these
witnesses from `boundary_lt_left` and `boundary_lt_right`. -/
def ChildSurvivors
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) : Prop :=
  (∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
      (P.path i).vertexSet ⊆ Cut.X) ∧
    (∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
      (P.path i).vertexSet ⊆ Cut.Y)

theorem sourceEndpoint_left_card_le_boundary_of_no_left_survivor
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w)
    (hno :
      ¬ ∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
        (P.path i).vertexSet ⊆ Cut.X) :
    ((sourceEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card ≤
      (edgeBoundary G Cut.X Cut.Y).card := by
  classical
  let Domain :=
    {v : V // v ∈ (sourceEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X}
  let idx : Domain → P.Index := fun v =>
    Classical.choose
      ((mem_sourceEndpointSetInCluster P I (D.cluster c) v.1).1
        (Finset.mem_inter.1 v.2).1)
  have idx_contained :
      ∀ v : Domain, idx v ∈ containedInCluster P I (D.cluster c) := by
    intro v
    exact (Classical.choose_spec
      ((mem_sourceEndpointSetInCluster P I (D.cluster c) v.1).1
        (Finset.mem_inter.1 v.2).1)).1
  have idx_source :
      ∀ v : Domain, (P.path (idx v)).source = v.1 := by
    intro v
    exact (Classical.choose_spec
      ((mem_sourceEndpointSetInCluster P I (D.cluster c) v.1).1
        (Finset.mem_inter.1 v.2).1)).2
  have idx_mem_I :
      ∀ v : Domain, idx v ∈ I := by
    intro v
    exact ((mem_containedInCluster P I (D.cluster c) (idx v)).1
      (idx_contained v)).1
  have idx_subset_parent :
      ∀ v : Domain, (P.path (idx v)).vertexSet ⊆ D.cluster c := by
    intro v
    exact ((mem_containedInCluster P I (D.cluster c) (idx v)).1
      (idx_contained v)).2
  have idx_not_subset_left :
      ∀ v : Domain, ¬ (P.path (idx v)).vertexSet ⊆ Cut.X := by
    intro v hsubX
    have hnewDisj :
        Disjoint (P.path (idx v)).edgeSet (D.splitDeletedEdges c Cut) :=
      D.split_contained_path_disjoint_deleted c Cut
        (Sum.inr false) (idx v) (idx_mem_I v) hsubX
    have hsurv :
        idx v ∈ surviving P I (D.splitDeletedEdges c Cut) :=
      (mem_surviving P I (D.splitDeletedEdges c Cut) (idx v)).2
        ⟨idx_mem_I v, hnewDisj⟩
    exact hno ⟨idx v, hsurv, hsubX⟩
  have idx_boundary :
      ∀ v : Domain,
        ∃ e ∈ (P.path (idx v)).edgeSet, e ∈ edgeBoundary G Cut.X Cut.Y := by
    intro v
    have hsubUnion : (P.path (idx v)).vertexSet ⊆ Cut.X ∪ Cut.Y := by
      intro x hx
      have hxC : x ∈ D.cluster c := idx_subset_parent v hx
      simpa [Cut.cover] using hxC
    have hsourceX : (P.path (idx v)).source ∈ Cut.X := by
      simpa [idx_source v] using (Finset.mem_inter.1 v.2).2
    exact GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
      (P := P.path (idx v)) hsubUnion hsourceX (idx_not_subset_left v)
  let charge : Domain → {e : Sym2 V // e ∈ edgeBoundary G Cut.X Cut.Y} :=
    fun v => ⟨Classical.choose (idx_boundary v),
      (Classical.choose_spec (idx_boundary v)).2⟩
  have charge_mem_path :
      ∀ v : Domain, (charge v).1 ∈ (P.path (idx v)).edgeSet := by
    intro v
    exact (Classical.choose_spec (idx_boundary v)).1
  have hcharge_inj : Function.Injective charge := by
    intro a b hab
    have hedge : (charge a).1 = (charge b).1 :=
      congrArg Subtype.val hab
    have hidx : idx a = idx b := by
      by_contra hne
      have hEdgeDisj :
          GraphPath.EdgeDisjoint (P.path (idx a)) (P.path (idx b)) :=
        GraphPath.edgeDisjoint_of_nodeDisjoint (P.node_disjoint hne)
      have hbmem : (charge a).1 ∈ (P.path (idx b)).edgeSet := by
        simpa [hedge] using charge_mem_path b
      exact Finset.disjoint_left.mp hEdgeDisj
        (charge_mem_path a) hbmem
    apply Subtype.ext
    calc
      a.1 = (P.path (idx a)).source := (idx_source a).symm
      _ = (P.path (idx b)).source := by rw [hidx]
      _ = b.1 := idx_source b
  have hcard := Fintype.card_le_of_injective charge hcharge_inj
  have hDomain :
      Fintype.card Domain =
        ((sourceEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card := by
    change Fintype.card
        (↥((sourceEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X)) =
      ((sourceEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card
    exact Fintype.card_coe _
  have hCodomain :
      Fintype.card {e : Sym2 V // e ∈ edgeBoundary G Cut.X Cut.Y} =
        (edgeBoundary G Cut.X Cut.Y).card := by
    change Fintype.card (↥(edgeBoundary G Cut.X Cut.Y)) =
      (edgeBoundary G Cut.X Cut.Y).card
    exact Fintype.card_coe _
  simpa [hDomain, hCodomain] using hcard

theorem targetEndpoint_left_card_le_boundary_of_no_left_survivor
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w)
    (hno :
      ¬ ∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
        (P.path i).vertexSet ⊆ Cut.X) :
    ((targetEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card ≤
      (edgeBoundary G Cut.X Cut.Y).card := by
  classical
  let Domain :=
    {v : V // v ∈ (targetEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X}
  let idx : Domain → P.Index := fun v =>
    Classical.choose
      ((mem_targetEndpointSetInCluster P I (D.cluster c) v.1).1
        (Finset.mem_inter.1 v.2).1)
  have idx_contained :
      ∀ v : Domain, idx v ∈ containedInCluster P I (D.cluster c) := by
    intro v
    exact (Classical.choose_spec
      ((mem_targetEndpointSetInCluster P I (D.cluster c) v.1).1
        (Finset.mem_inter.1 v.2).1)).1
  have idx_target :
      ∀ v : Domain, (P.path (idx v)).target = v.1 := by
    intro v
    exact (Classical.choose_spec
      ((mem_targetEndpointSetInCluster P I (D.cluster c) v.1).1
        (Finset.mem_inter.1 v.2).1)).2
  have idx_mem_I :
      ∀ v : Domain, idx v ∈ I := by
    intro v
    exact ((mem_containedInCluster P I (D.cluster c) (idx v)).1
      (idx_contained v)).1
  have idx_subset_parent :
      ∀ v : Domain, (P.path (idx v)).vertexSet ⊆ D.cluster c := by
    intro v
    exact ((mem_containedInCluster P I (D.cluster c) (idx v)).1
      (idx_contained v)).2
  have idx_not_subset_left :
      ∀ v : Domain, ¬ (P.path (idx v)).vertexSet ⊆ Cut.X := by
    intro v hsubX
    have hnewDisj :
        Disjoint (P.path (idx v)).edgeSet (D.splitDeletedEdges c Cut) :=
      D.split_contained_path_disjoint_deleted c Cut
        (Sum.inr false) (idx v) (idx_mem_I v) hsubX
    have hsurv :
        idx v ∈ surviving P I (D.splitDeletedEdges c Cut) :=
      (mem_surviving P I (D.splitDeletedEdges c Cut) (idx v)).2
        ⟨idx_mem_I v, hnewDisj⟩
    exact hno ⟨idx v, hsurv, hsubX⟩
  have idx_boundary :
      ∀ v : Domain,
        ∃ e ∈ (P.path (idx v)).edgeSet, e ∈ edgeBoundary G Cut.X Cut.Y := by
    intro v
    have hsubUnion : (P.path (idx v)).vertexSet ⊆ Cut.X ∪ Cut.Y := by
      intro x hx
      have hxC : x ∈ D.cluster c := idx_subset_parent v hx
      simpa [Cut.cover] using hxC
    have htargetX : (P.path (idx v)).target ∈ Cut.X := by
      simpa [idx_target v] using (Finset.mem_inter.1 v.2).2
    exact GraphPath.exists_edgeBoundary_of_target_mem_left_of_not_subset_left
      (P := P.path (idx v)) hsubUnion htargetX (idx_not_subset_left v)
  let charge : Domain → {e : Sym2 V // e ∈ edgeBoundary G Cut.X Cut.Y} :=
    fun v => ⟨Classical.choose (idx_boundary v),
      (Classical.choose_spec (idx_boundary v)).2⟩
  have charge_mem_path :
      ∀ v : Domain, (charge v).1 ∈ (P.path (idx v)).edgeSet := by
    intro v
    exact (Classical.choose_spec (idx_boundary v)).1
  have hcharge_inj : Function.Injective charge := by
    intro a b hab
    have hedge : (charge a).1 = (charge b).1 :=
      congrArg Subtype.val hab
    have hidx : idx a = idx b := by
      by_contra hne
      have hEdgeDisj :
          GraphPath.EdgeDisjoint (P.path (idx a)) (P.path (idx b)) :=
        GraphPath.edgeDisjoint_of_nodeDisjoint (P.node_disjoint hne)
      have hbmem : (charge a).1 ∈ (P.path (idx b)).edgeSet := by
        simpa [hedge] using charge_mem_path b
      exact Finset.disjoint_left.mp hEdgeDisj
        (charge_mem_path a) hbmem
    apply Subtype.ext
    calc
      a.1 = (P.path (idx a)).target := (idx_target a).symm
      _ = (P.path (idx b)).target := by rw [hidx]
      _ = b.1 := idx_target b
  have hcard := Fintype.card_le_of_injective charge hcharge_inj
  have hDomain :
      Fintype.card Domain =
        ((targetEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card := by
    change Fintype.card
        (↥((targetEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X)) =
      ((targetEndpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card
    exact Fintype.card_coe _
  have hCodomain :
      Fintype.card {e : Sym2 V // e ∈ edgeBoundary G Cut.X Cut.Y} =
        (edgeBoundary G Cut.X Cut.Y).card := by
    change Fintype.card (↥(edgeBoundary G Cut.X Cut.Y)) =
      (edgeBoundary G Cut.X Cut.Y).card
    exact Fintype.card_coe _
  simpa [hDomain, hCodomain] using hcard

/-- If the left child of a sparse split had no surviving contained selected
path, then every terminal endpoint on the left can be charged to a distinct
edge of the sparse cut. -/
theorem endpoint_left_card_le_boundary_of_no_left_survivor
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w)
    (hno :
      ¬ ∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
        (P.path i).vertexSet ⊆ Cut.X) :
    ((endpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card ≤
      (edgeBoundary G Cut.X Cut.Y).card := by
  classical
  let J := containedInCluster P I (D.cluster c)
  let B := edgeBoundary G Cut.X Cut.Y
  have hendpoint_eq :
      (endpointSetInCluster P I (D.cluster c)) ∩ Cut.X =
        J.biUnion (fun i => GraphPath.endpointSetIn (P.path i) Cut.X) := by
    simpa [J] using
      endpointSetInCluster_inter_eq_biUnion_endpointSetIn
        P I (D.cluster c) Cut.X
  have hendpoint_card :
      ((endpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card =
        ∑ i ∈ J, (GraphPath.endpointSetIn (P.path i) Cut.X).card := by
    rw [hendpoint_eq]
    exact Finset.card_biUnion (pairwiseDisjoint_endpointSetIn P J Cut.X)
  have hpath_le :
      ∀ i ∈ J,
        (GraphPath.endpointSetIn (P.path i) Cut.X).card ≤
          ((P.path i).edgeSet ∩ B).card := by
    intro i hiJ
    have hiData := (mem_containedInCluster P I (D.cluster c) i).1 (by simpa [J] using hiJ)
    have hsubUnion : (P.path i).vertexSet ⊆ Cut.X ∪ Cut.Y := by
      intro v hv
      have hvC : v ∈ D.cluster c := hiData.2 hv
      simpa [Cut.cover] using hvC
    have hnotSubset : ¬ (P.path i).vertexSet ⊆ Cut.X := by
      intro hsubX
      have hnewDisj :
          Disjoint (P.path i).edgeSet (D.splitDeletedEdges c Cut) :=
        D.split_contained_path_disjoint_deleted c Cut
          (Sum.inr false) i hiData.1 hsubX
      have hsurv :
          i ∈ surviving P I (D.splitDeletedEdges c Cut) :=
        (mem_surviving P I (D.splitDeletedEdges c Cut) i).2
          ⟨hiData.1, hnewDisj⟩
      exact hno ⟨i, hsurv, hsubX⟩
    simpa [GraphPath.endpointSetIn, B] using
      GraphPath.endpoint_left_card_le_boundary_edges_of_not_subset_left
        (P := P.path i) Cut.disjoint hsubUnion hnotSubset
  have hsum_le :
      (∑ i ∈ J, (GraphPath.endpointSetIn (P.path i) Cut.X).card) ≤
        ∑ i ∈ J, ((P.path i).edgeSet ∩ B).card := by
    exact Finset.sum_le_sum hpath_le
  have hedge_union_subset :
      J.biUnion (fun i => (P.path i).edgeSet ∩ B) ⊆ B := by
    intro e he
    rcases Finset.mem_biUnion.1 he with ⟨i, _hi, hei⟩
    exact (Finset.mem_inter.1 hei).2
  have hedge_sum_le :
      (∑ i ∈ J, ((P.path i).edgeSet ∩ B).card) ≤ B.card := by
    have hcard_union :
        (J.biUnion (fun i => (P.path i).edgeSet ∩ B)).card =
          ∑ i ∈ J, ((P.path i).edgeSet ∩ B).card :=
      Finset.card_biUnion (pairwiseDisjoint_edgeSet_inter P J B)
    rw [← hcard_union]
    exact Finset.card_le_card hedge_union_subset
  calc
    ((endpointSetInCluster P I (D.cluster c)) ∩ Cut.X).card
        = ∑ i ∈ J, (GraphPath.endpointSetIn (P.path i) Cut.X).card :=
      hendpoint_card
    _ ≤ ∑ i ∈ J, ((P.path i).edgeSet ∩ B).card := hsum_le
    _ ≤ B.card := hedge_sum_le

/-- Right-side version of
`endpoint_left_card_le_boundary_of_no_left_survivor`. -/
theorem endpoint_right_card_le_boundary_of_no_right_survivor
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w)
    (hno :
      ¬ ∃ i ∈ surviving P I (D.splitDeletedEdges c Cut),
        (P.path i).vertexSet ⊆ Cut.Y) :
    ((endpointSetInCluster P I (D.cluster c)) ∩ Cut.Y).card ≤
      (edgeBoundary G Cut.X Cut.Y).card := by
  classical
  let J := containedInCluster P I (D.cluster c)
  let B := edgeBoundary G Cut.Y Cut.X
  have hendpoint_eq :
      (endpointSetInCluster P I (D.cluster c)) ∩ Cut.Y =
        J.biUnion (fun i => GraphPath.endpointSetIn (P.path i) Cut.Y) := by
    simpa [J] using
      endpointSetInCluster_inter_eq_biUnion_endpointSetIn
        P I (D.cluster c) Cut.Y
  have hendpoint_card :
      ((endpointSetInCluster P I (D.cluster c)) ∩ Cut.Y).card =
        ∑ i ∈ J, (GraphPath.endpointSetIn (P.path i) Cut.Y).card := by
    rw [hendpoint_eq]
    exact Finset.card_biUnion (pairwiseDisjoint_endpointSetIn P J Cut.Y)
  have hpath_le :
      ∀ i ∈ J,
        (GraphPath.endpointSetIn (P.path i) Cut.Y).card ≤
          ((P.path i).edgeSet ∩ B).card := by
    intro i hiJ
    have hiData := (mem_containedInCluster P I (D.cluster c) i).1 (by simpa [J] using hiJ)
    have hsubUnion : (P.path i).vertexSet ⊆ Cut.Y ∪ Cut.X := by
      intro v hv
      have hvC : v ∈ D.cluster c := hiData.2 hv
      have hvXY : v ∈ Cut.X ∪ Cut.Y := by
        simpa [Cut.cover] using hvC
      rcases Finset.mem_union.1 hvXY with hvX | hvY
      · exact Finset.mem_union_right _ hvX
      · exact Finset.mem_union_left _ hvY
    have hnotSubset : ¬ (P.path i).vertexSet ⊆ Cut.Y := by
      intro hsubY
      have hnewDisj :
          Disjoint (P.path i).edgeSet (D.splitDeletedEdges c Cut) :=
        D.split_contained_path_disjoint_deleted c Cut
          (Sum.inr true) i hiData.1 hsubY
      have hsurv :
          i ∈ surviving P I (D.splitDeletedEdges c Cut) :=
        (mem_surviving P I (D.splitDeletedEdges c Cut) i).2
          ⟨hiData.1, hnewDisj⟩
      exact hno ⟨i, hsurv, hsubY⟩
    simpa [GraphPath.endpointSetIn, B] using
      GraphPath.endpoint_left_card_le_boundary_edges_of_not_subset_left
        (P := P.path i) Cut.disjoint.symm hsubUnion hnotSubset
  have hsum_le :
      (∑ i ∈ J, (GraphPath.endpointSetIn (P.path i) Cut.Y).card) ≤
        ∑ i ∈ J, ((P.path i).edgeSet ∩ B).card := by
    exact Finset.sum_le_sum hpath_le
  have hedge_union_subset :
      J.biUnion (fun i => (P.path i).edgeSet ∩ B) ⊆ B := by
    intro e he
    rcases Finset.mem_biUnion.1 he with ⟨i, _hi, hei⟩
    exact (Finset.mem_inter.1 hei).2
  have hedge_sum_le :
      (∑ i ∈ J, ((P.path i).edgeSet ∩ B).card) ≤ B.card := by
    have hcard_union :
        (J.biUnion (fun i => (P.path i).edgeSet ∩ B)).card =
          ∑ i ∈ J, ((P.path i).edgeSet ∩ B).card :=
      Finset.card_biUnion (pairwiseDisjoint_edgeSet_inter P J B)
    rw [← hcard_union]
    exact Finset.card_le_card hedge_union_subset
  have hleB :
      ((endpointSetInCluster P I (D.cluster c)) ∩ Cut.Y).card ≤
        (edgeBoundary G Cut.Y Cut.X).card := by
    calc
      ((endpointSetInCluster P I (D.cluster c)) ∩ Cut.Y).card
          = ∑ i ∈ J, (GraphPath.endpointSetIn (P.path i) Cut.Y).card :=
        hendpoint_card
      _ ≤ ∑ i ∈ J, ((P.path i).edgeSet ∩ B).card := hsum_le
      _ ≤ B.card := hedge_sum_le
  simpa [B, edgeBoundary_comm (G := G) Cut.X Cut.Y] using hleB

/-- A sparse cut of a bad cluster leaves at least one surviving selected path
inside each child. -/
theorem childSurvivors_of_sparse_cut
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) :
    ChildSurvivors D c Cut := by
  classical
  constructor
  · by_contra hno
    have hle :=
      D.endpoint_left_card_le_boundary_of_no_left_survivor c Cut hno
    exact (not_lt_of_ge hle) Cut.boundary_lt_left
  · by_contra hno
    have hle :=
      D.endpoint_right_card_le_boundary_of_no_right_survivor c Cut hno
    exact (not_lt_of_ge hle) Cut.boundary_lt_right

theorem exists_sparse_cut_of_not_good
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (hbad : ¬ GoodCluster P I (D.cluster c) w) :
    Nonempty (SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w) := by
  classical
  exact observation410 G (D.cluster c)
    (endpointSetInCluster P I (D.cluster c)) w
    (endpointSetInCluster_subset_cluster P I (D.cluster c)) hbad

/-- A decomposition state has no more clusters than vertices: choose a vertex
from a surviving path in each cluster and use cluster disjointness. -/
theorem clusterCount_le_card_vertices
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) :
    D.clusterCount ≤ Fintype.card V := by
  classical
  let chosenIndex : D.ClusterIndex → P.Index := fun c =>
    Classical.choose (D.cluster_has_survivor c)
  have chosen_mem :
      ∀ c : D.ClusterIndex,
        chosenIndex c ∈ surviving P I D.deletedEdges := by
    intro c
    exact (Classical.choose_spec (D.cluster_has_survivor c)).1
  have chosen_subset :
      ∀ c : D.ClusterIndex,
        (P.path (chosenIndex c)).vertexSet ⊆ D.cluster c := by
    intro c
    exact (Classical.choose_spec (D.cluster_has_survivor c)).2
  let rep : D.ClusterIndex → V := fun c => (P.path (chosenIndex c)).source
  have hrep_mem : ∀ c : D.ClusterIndex, rep c ∈ D.cluster c := by
    intro c
    exact chosen_subset c (GraphPath.source_mem_vertexSet (P.path (chosenIndex c)))
  have hinj : Function.Injective rep := by
    intro c d hrep
    by_contra hne
    have hc : rep c ∈ D.cluster c := hrep_mem c
    have hd : rep c ∈ D.cluster d := by
      simpa [hrep] using hrep_mem d
    exact Finset.disjoint_left.mp (D.cluster_disjoint hne) hc hd
  change Fintype.card D.ClusterIndex ≤ Fintype.card V
  exact Fintype.card_le_of_injective rep hinj

/-- The selected paths destroyed in a decomposition state are bounded by the
same edge budget as the deleted-edge set. -/
theorem hitEdges_card_le_budget
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) :
    (hitEdges P I D.deletedEdges).card ≤
      (D.clusterCount - 1) * w := by
  change (hitEdges P I D.deletedEdges).card ≤
      (@Fintype.card D.ClusterIndex D.clusterFintype - 1) * w
  exact (hitEdges_card_le P I D.deletedEdges).trans D.deleted_budget

/-- Any graph path that meets a cluster and avoids all deleted edges is
contained in that cluster.  This is the formal version of the paper's repeated
use of the deleted cut set `E'`: a path can leave a cluster only through a
previously deleted boundary edge. -/
theorem graphPath_vertexSet_subset_cluster_of_meets_and_disjoint_deleted
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (R : GraphPath G) (c : D.ClusterIndex) {x : V}
    (hxR : x ∈ R.vertexSet) (hxC : x ∈ D.cluster c)
    (hdisj : Disjoint R.edgeSet D.deletedEdges) :
    R.vertexSet ⊆ D.cluster c := by
  classical
  refine
    GraphPath.vertexSet_subset_of_vertex_mem_and_edgeSet_disjoint_boundary
      (P := R) hxR hxC ?_
  rw [Finset.disjoint_left]
  intro e heR heB
  exact Finset.disjoint_left.mp hdisj heR
    (D.boundary_deleted c (by simpa [clusterBoundary] using heB))

/-- Every selected path contained in a state cluster is one of the surviving
paths. -/
theorem containedInCluster_subset_surviving
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex) :
    containedInCluster P I (D.cluster c) ⊆ surviving P I D.deletedEdges := by
  intro i hi
  rcases (mem_containedInCluster P I (D.cluster c) i).1 hi with ⟨hiI, hiC⟩
  exact (mem_surviving P I D.deletedEdges i).2
    ⟨hiI, D.contained_path_disjoint_deleted c i hiI hiC⟩

/-- The selected-path sets contained in two distinct state clusters are
disjoint. -/
theorem disjoint_containedInCluster_of_ne
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    {c d : D.ClusterIndex} (hcd : c ≠ d) :
    Disjoint (containedInCluster P I (D.cluster c))
      (containedInCluster P I (D.cluster d)) := by
  classical
  rw [Finset.disjoint_left]
  intro i hic hid
  have hic' := (mem_containedInCluster P I (D.cluster c) i).1 hic
  have hid' := (mem_containedInCluster P I (D.cluster d) i).1 hid
  have hsrcC : (P.path i).source ∈ D.cluster c :=
    hic'.2 (GraphPath.source_mem_vertexSet (P.path i))
  have hsrcD : (P.path i).source ∈ D.cluster d :=
    hid'.2 (GraphPath.source_mem_vertexSet (P.path i))
  exact Finset.disjoint_left.mp (D.cluster_disjoint hcd) hsrcC hsrcD

private theorem exists_inside_vertex_of_mem_clusterBoundary
    {C : Finset V} {e : Sym2 V}
    (he : e ∈ clusterBoundary G C) :
    ∃ x : V, x ∈ C ∧ x ∈ e := by
  classical
  rcases ((mem_edgeBoundary (G := G) C ((Finset.univ : Finset V) \ C) e).1
      (by simpa [clusterBoundary] using he)) with
    ⟨_heG, x, hxC, y, _hy, hexy⟩
  exact ⟨x, hxC, by rw [hexy]; simp⟩

private noncomputable def insideVertexOfBoundary
    {C : Finset V} {e : Sym2 V}
    (he : e ∈ clusterBoundary G C) : V :=
  Classical.choose (exists_inside_vertex_of_mem_clusterBoundary (G := G) he)

private theorem insideVertexOfBoundary_mem_cluster
    {C : Finset V} {e : Sym2 V}
    (he : e ∈ clusterBoundary G C) :
    insideVertexOfBoundary (G := G) he ∈ C :=
  (Classical.choose_spec
    (exists_inside_vertex_of_mem_clusterBoundary (G := G) he)).1

private theorem insideVertexOfBoundary_mem_edge
    {C : Finset V} {e : Sym2 V}
    (he : e ∈ clusterBoundary G C) :
    insideVertexOfBoundary (G := G) he ∈ e :=
  (Classical.choose_spec
    (exists_inside_vertex_of_mem_clusterBoundary (G := G) he)).2

private theorem sym2_endpoint_subtype_card_le_two (e : Sym2 V) :
    Fintype.card {v : V // v ∈ e} ≤ 2 := by
  classical
  rw [Fintype.card_subtype (fun v : V => v ∈ e)]
  have hfin :
      (Finset.univ.filter (fun v : V => v ∈ e)) = e.toFinset := by
    ext v
    simp [Sym2.mem_toFinset]
  rw [hfin]
  rw [Sym2.card_toFinset]
  by_cases hdiag : e.IsDiag <;> simp [hdiag]

/-- Every current boundary incidence can be charged injectively to a deleted
edge together with one of its endpoints.  Since a simple edge has at most two
endpoints, the total current boundary size is at most twice the number of
deleted edges. -/
theorem sum_clusterBoundary_card_le_two_deletedEdges_card
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) :
    (∑ c : D.ClusterIndex, (clusterBoundary G (D.cluster c)).card) ≤
      2 * D.deletedEdges.card := by
  classical
  let Domain :=
    Σ c : D.ClusterIndex, {e : Sym2 V // e ∈ clusterBoundary G (D.cluster c)}
  let Codomain :=
    Σ e : {e : Sym2 V // e ∈ D.deletedEdges}, {v : V // v ∈ (e.1 : Sym2 V)}
  let charge : Domain → Codomain := fun x =>
    ⟨⟨x.2.1, D.boundary_deleted x.1 x.2.2⟩,
      ⟨insideVertexOfBoundary (G := G) x.2.2,
        insideVertexOfBoundary_mem_edge (G := G) x.2.2⟩⟩
  have hcharge_inj : Function.Injective charge := by
    intro x y hxy
    rcases x with ⟨c, e⟩
    rcases y with ⟨d, f⟩
    have hedge : e.1 = f.1 := by
      exact congrArg (fun z : Codomain => (z.1.1 : Sym2 V)) hxy
    have hvertex :
        insideVertexOfBoundary (G := G) e.2 =
          insideVertexOfBoundary (G := G) f.2 := by
      exact congrArg (fun z : Codomain => (z.2.1 : V)) hxy
    by_cases hcd : c = d
    · subst d
      have hef : e = f := Subtype.ext hedge
      subst f
      rfl
    · have hvC :
          insideVertexOfBoundary (G := G) e.2 ∈ D.cluster c :=
        insideVertexOfBoundary_mem_cluster (G := G) e.2
      have hvD :
          insideVertexOfBoundary (G := G) e.2 ∈ D.cluster d := by
        simpa [hvertex] using
          insideVertexOfBoundary_mem_cluster (G := G) f.2
      exact (Finset.disjoint_left.mp (D.cluster_disjoint hcd) hvC hvD).elim
  have hcard_inj : Fintype.card Domain ≤ Fintype.card Codomain :=
    Fintype.card_le_of_injective charge hcharge_inj
  have hDomain :
      Fintype.card Domain =
        ∑ c : D.ClusterIndex, (clusterBoundary G (D.cluster c)).card := by
    simp [Domain]
  have hCodomain :
      Fintype.card Codomain ≤ D.deletedEdges.card * 2 := by
    calc
      Fintype.card Codomain =
          ∑ e : {e : Sym2 V // e ∈ D.deletedEdges},
            Fintype.card {v : V // v ∈ (e.1 : Sym2 V)} := by
        simp [Codomain]
      _ ≤ ∑ _e : {e : Sym2 V // e ∈ D.deletedEdges}, 2 := by
        refine Finset.sum_le_sum ?_
        intro e _he
        exact sym2_endpoint_subtype_card_le_two (V := V) e.1
      _ = D.deletedEdges.card * 2 := by
        simp
  calc
    (∑ c : D.ClusterIndex, (clusterBoundary G (D.cluster c)).card)
        = Fintype.card Domain := hDomain.symm
    _ ≤ Fintype.card Codomain := hcard_inj
    _ ≤ D.deletedEdges.card * 2 := hCodomain
    _ = 2 * D.deletedEdges.card := by ring

/-- The paper's collection `C₁`: clusters whose current boundary has size
strictly smaller than `4w`. -/
noncomputable def smallBoundaryClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) :
    Finset D.ClusterIndex := by
  classical
  exact Finset.univ.filter fun c =>
    (clusterBoundary G (D.cluster c)).card < 4 * w

theorem mem_smallBoundaryClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex) :
    c ∈ D.smallBoundaryClusters ↔
      (clusterBoundary G (D.cluster c)).card < 4 * w := by
  classical
  simp [smallBoundaryClusters]

/-- Observation 4.12 in decomposition-state form.  If `w > 0`, then at least
half of the clusters have current boundary size `< 4w`. -/
theorem halfSmallBoundary_of_pos
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (hw : 0 < w) :
    D.clusterCount ≤ 2 * D.smallBoundaryClusters.card := by
  classical
  let small := D.smallBoundaryClusters
  let large : Finset D.ClusterIndex := Finset.univ \ small
  have hlarge_lower :
      large.card * (4 * w) ≤
        ∑ c ∈ large, (clusterBoundary G (D.cluster c)).card := by
    calc
      large.card * (4 * w) = ∑ c ∈ large, 4 * w := by
        simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ c ∈ large, (clusterBoundary G (D.cluster c)).card := by
        refine Finset.sum_le_sum ?_
        intro c hc
        have hcnot : c ∉ small := by
          simpa [large] using hc
        have hnotSmall :
            ¬ (clusterBoundary G (D.cluster c)).card < 4 * w := by
          intro hlt
          exact hcnot ((D.mem_smallBoundaryClusters c).2 hlt)
        exact Nat.le_of_not_gt hnotSmall
  have hlarge_sum_le_total :
      (∑ c ∈ large, (clusterBoundary G (D.cluster c)).card) ≤
        ∑ c : D.ClusterIndex, (clusterBoundary G (D.cluster c)).card := by
    exact Finset.sum_le_univ_sum_of_nonneg (s := large)
      (f := fun c => (clusterBoundary G (D.cluster c)).card)
      (by intro c; exact Nat.zero_le _)
  have htotal_budget :
      (∑ c : D.ClusterIndex, (clusterBoundary G (D.cluster c)).card) ≤
        2 * ((D.clusterCount - 1) * w) := by
    have hsum := D.sum_clusterBoundary_card_le_two_deletedEdges_card
    have hdel := D.deleted_budget
    have hmul : 2 * D.deletedEdges.card ≤ 2 * ((D.clusterCount - 1) * w) := by
      exact Nat.mul_le_mul_left 2 hdel
    exact hsum.trans hmul
  have hlarge_budget :
      large.card * (4 * w) ≤ 2 * ((D.clusterCount - 1) * w) :=
    hlarge_lower.trans (hlarge_sum_le_total.trans htotal_budget)
  have hpart : small.card + large.card = D.clusterCount := by
    have hsub : small ⊆ (Finset.univ : Finset D.ClusterIndex) := by
      intro c hc
      simp
    have h := Finset.card_sdiff_add_card_eq_card hsub
    have h' : large.card + small.card = D.clusterCount := by
      simpa [large, small, DecompositionState.clusterCount] using h
    omega
  by_contra hnot
  have hlt : 2 * small.card < D.clusterCount := Nat.lt_of_not_ge hnot
  have hlarge_gt_small : small.card < large.card := by omega
  have hcontr : 2 * ((D.clusterCount - 1) * w) < large.card * (4 * w) := by
    have hrlt : D.clusterCount - 1 < 2 * large.card := by omega
    have hmul :
        (D.clusterCount - 1) * w < (2 * large.card) * w :=
      Nat.mul_lt_mul_of_pos_right hrlt hw
    calc
      2 * ((D.clusterCount - 1) * w) <
          2 * ((2 * large.card) * w) :=
        Nat.mul_lt_mul_of_pos_left hmul (by norm_num)
      _ = large.card * (4 * w) := by ring
  exact (not_lt_of_ge hlarge_budget) hcontr

/-- The splitting algorithm has stopped: every current cluster is good. -/
def Final
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) : Prop :=
  ∀ c : D.ClusterIndex, GoodCluster P I (D.cluster c) w

/-- Observation 4.12 for a state: at least half of the clusters are in `C₁`,
written without division as `r ≤ 2 |C₁|`. -/
def HalfSmallBoundary
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) : Prop :=
  D.clusterCount ≤ 2 * D.smallBoundaryClusters.card

/-- A final state is exactly a state with no bad cluster. -/
theorem final_iff_no_bad_cluster
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) :
    Final D ↔ ¬ ∃ c : D.ClusterIndex,
      ¬ GoodCluster P I (D.cluster c) w := by
  classical
  constructor
  · intro hfinal hbad
    rcases hbad with ⟨c, hbadc⟩
    exact hbadc (hfinal c)
  · intro hno c
    by_contra hbadc
    exact hno ⟨c, hbadc⟩

/-- Any decomposition state is either final or has a concrete bad cluster to
split. -/
theorem final_or_bad_cluster
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) :
    Final D ∨ ∃ c : D.ClusterIndex,
      ¬ GoodCluster P I (D.cluster c) w := by
  classical
  by_cases hbad : ∃ c : D.ClusterIndex,
      ¬ GoodCluster P I (D.cluster c) w
  · exact Or.inr hbad
  · exact Or.inl ((D.final_iff_no_bad_cluster).2 hbad)

/-- The remaining split measure: the number of vertices not yet accounted for
by the current number of clusters. -/
noncomputable def splitMeasure
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w) : ℕ :=
  Fintype.card V - D.clusterCount

theorem split_measure_lt
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (D : DecompositionState (V := V) (G := G) P I w)
    (c : D.ClusterIndex)
    (Cut : SparseTerminalCut G (D.cluster c)
      (endpointSetInCluster P I (D.cluster c)) w)
    (hchild : ChildSurvivors D c Cut) :
    (D.splitState c Cut hchild.1 hchild.2).splitMeasure < D.splitMeasure := by
  classical
  let D' := D.splitState c Cut hchild.1 hchild.2
  have hcount : D'.clusterCount = D.clusterCount + 1 := by
    change Fintype.card (D.SplitIndex c) = D.clusterCount + 1
    exact D.splitIndex_card c
  have hleVertices : D.clusterCount + 1 ≤ Fintype.card V := by
    rw [← hcount]
    exact clusterCount_le_card_vertices D'
  have hlt :
      Fintype.card V - (D.clusterCount + 1) <
        Fintype.card V - D.clusterCount := by
    omega
  simpa [splitMeasure, D', hcount] using hlt

/-- If every bad cluster admits a sparse cut with child survivors, then the
splitting process terminates in a final decomposition state. -/
theorem exists_final_state_of_splitter
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (hsplit :
      ∀ (D : DecompositionState (V := V) (G := G) P I w)
        (c : D.ClusterIndex),
        ¬ GoodCluster P I (D.cluster c) w →
          ∃ Cut : SparseTerminalCut G (D.cluster c)
              (endpointSetInCluster P I (D.cluster c)) w,
            ChildSurvivors D c Cut)
    (D₀ : DecompositionState (V := V) (G := G) P I w) :
    ∃ Df : DecompositionState (V := V) (G := G) P I w, Final Df := by
  classical
  let measure :=
    fun D : DecompositionState (V := V) (G := G) P I w => D.splitMeasure
  have hmain :
      ∀ n : ℕ,
        ∀ D : DecompositionState (V := V) (G := G) P I w,
          measure D ≤ n →
            ∃ Df : DecompositionState (V := V) (G := G) P I w, Final Df := by
    intro n
    induction n with
    | zero =>
        intro D hD
        rcases D.final_or_bad_cluster with hfinal | ⟨c, hbad⟩
        · exact ⟨D, hfinal⟩
        · rcases hsplit D c hbad with ⟨Cut, hchild⟩
          have hlt := D.split_measure_lt c Cut hchild
          have hzero : measure D = 0 := Nat.eq_zero_of_le_zero hD
          have : measure (D.splitState c Cut hchild.1 hchild.2) < 0 := by
            simp [measure, hzero] at hlt
          exact False.elim (Nat.not_lt_zero _ this)
    | succ n ih =>
        intro D hD
        rcases D.final_or_bad_cluster with hfinal | ⟨c, hbad⟩
        · exact ⟨D, hfinal⟩
        · rcases hsplit D c hbad with ⟨Cut, hchild⟩
          let D' := D.splitState c Cut hchild.1 hchild.2
          have hlt : measure D' < measure D := by
            simpa [measure, D'] using D.split_measure_lt c Cut hchild
          have hD' : measure D' ≤ n := by
            omega
          exact ih D' hD'
  exact hmain (measure D₀) D₀ le_rfl

/-- Observation 4.13, in decomposition-state form.  Once the splitting process
has stopped, a cluster whose boundary has size `< 4w` is happy: it is good by
finality, and the `(4w,2D)` intersection hypotheses force at least `D`
surviving `Σ`-paths to be contained in it. -/
theorem happy_of_final_good_of_boundary_lt
    {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    {I : Subfamily P} {J : Finset Q.Index} {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hint : P.IntersectingPathSetPair Q I J (4 * w) (2 * Dhat))
    (hD : 8 * w ≤ Dhat)
    (c : State.ClusterIndex)
    (hsmall :
      (clusterBoundary G (State.cluster c)).card < 4 * w) :
    HappyCluster P I (State.cluster c) w Dhat := by
  classical
  constructor
  · exact hfinal c
  · rcases State.cluster_has_survivor c with ⟨i, hiSurv, hiC⟩
    have hiI : i ∈ I := (mem_surviving P I State.deletedEdges i).1 hiSurv |>.1
    let B : Finset (Sym2 V) := clusterBoundary G (State.cluster c)
    let A : Finset Q.Index := P.intersectingRightIndices Q J i
    let HQ : Finset Q.Index := hitEdges Q J B
    have hAcard : 4 * w ≤ A.card := by
      simpa [A] using hint.1 i hiI
    have hHQcard : HQ.card < A.card := by
      have hHQleB : HQ.card ≤ B.card := hitEdges_card_le Q J B
      have hBlt : B.card < 4 * w := by simpa [B] using hsmall
      exact lt_of_le_of_lt hHQleB (hBlt.trans_le hAcard)
    have hq_exists : ∃ q ∈ A, q ∉ HQ := by
      by_contra hno
      push Not at hno
      have hAsub : A ⊆ HQ := by
        intro q hq
        exact hno q hq
      have hAle : A.card ≤ HQ.card := Finset.card_le_card hAsub
      omega
    rcases hq_exists with ⟨q, hqA, hqNotHit⟩
    have hqJ : q ∈ J :=
      intersectingRightIndices_subset P Q J i hqA
    have hqInter :
        PathPacking.PathsIntersect (P.path i) (Q.path q) := by
      have hqA' :
          q ∈ J ∧ PathPacking.PathsIntersect (P.path i) (Q.path q) := by
        exact Finset.mem_filter.1 (by
          change q ∈ J.filter
            (fun q => PathPacking.PathsIntersect (P.path i) (Q.path q))
          simpa [A, PathPacking.intersectingRightIndices] using hqA)
      exact hqA'.2
    have hqDisjB : Disjoint (Q.path q).edgeSet B := by
      by_contra hnot
      exact hqNotHit ((mem_hitEdges Q J B q).2 ⟨hqJ, hnot⟩)
    rcases Finset.not_disjoint_iff.1 hqInter with ⟨x, hxSigma, hxQ⟩
    have hxC : x ∈ State.cluster c := hiC hxSigma
    have hqC : (Q.path q).vertexSet ⊆ State.cluster c := by
      refine
        GraphPath.vertexSet_subset_of_vertex_mem_and_edgeSet_disjoint_boundary
          (P := Q.path q) hxQ hxC ?_
      simpa [B, clusterBoundary] using hqDisjB
    let L : Finset P.Index := P.intersectingLeftIndices Q I q
    let HP : Finset P.Index := hitEdges P I B
    let K : Finset P.Index := L \ HP
    have hLcard : 2 * Dhat ≤ L.card := by
      simpa [L] using hint.2 q hqJ
    have hHPcard : HP.card < Dhat := by
      have hHPleB : HP.card ≤ B.card := hitEdges_card_le P I B
      have hBlt : B.card < 4 * w := by simpa [B] using hsmall
      have h4leD : 4 * w ≤ Dhat := by omega
      exact lt_of_le_of_lt hHPleB (hBlt.trans_le h4leD)
    have hL_le_K_add_HP : L.card ≤ K.card + HP.card := by
      have hsub : L ∩ HP ⊆ L := Finset.inter_subset_left
      have hpart := Finset.card_sdiff_add_card_eq_card hsub
      have hsdiff_eq : L \ (L ∩ HP) = K := by
        ext r
        simp [K]
      have hinter_le : (L ∩ HP).card ≤ HP.card :=
        Finset.card_le_card Finset.inter_subset_right
      rw [hsdiff_eq] at hpart
      omega
    have hDleK : Dhat ≤ K.card := by
      omega
    have hKsubset :
        K ⊆ containedInCluster P I (State.cluster c) := by
      intro r hrK
      have hrL : r ∈ L := (Finset.mem_sdiff.1 hrK).1
      have hrNotHit : r ∉ HP := (Finset.mem_sdiff.1 hrK).2
      have hrI : r ∈ I :=
        intersectingLeftIndices_subset P Q I q (by simpa [L] using hrL)
      have hrInter :
          PathPacking.PathsIntersect (P.path r) (Q.path q) := by
        have hrL' :
            r ∈ I ∧ PathPacking.PathsIntersect (P.path r) (Q.path q) := by
          exact Finset.mem_filter.1 (by
            change r ∈ I.filter
              (fun r => PathPacking.PathsIntersect (P.path r) (Q.path q))
            simpa [L, PathPacking.intersectingLeftIndices] using hrL)
        exact hrL'.2
      have hrDisjB : Disjoint (P.path r).edgeSet B := by
        by_contra hnot
        exact hrNotHit ((mem_hitEdges P I B r).2 ⟨hrI, hnot⟩)
      rcases Finset.not_disjoint_iff.1 hrInter with ⟨y, hyP, hyQ⟩
      have hyC : y ∈ State.cluster c := hqC hyQ
      have hrC : (P.path r).vertexSet ⊆ State.cluster c := by
        refine
          GraphPath.vertexSet_subset_of_vertex_mem_and_edgeSet_disjoint_boundary
            (P := P.path r) hyP hyC ?_
        simpa [B, clusterBoundary] using hrDisjB
      exact (mem_containedInCluster P I (State.cluster c) r).2
        ⟨hrI, hrC⟩
    exact hDleK.trans (Finset.card_le_card hKsubset)

/-- Observation 4.13 stated with the paper's `C₁` notation. -/
theorem happy_of_mem_smallBoundaryClusters
    {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    {I : Subfamily P} {J : Finset Q.Index} {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hint : P.IntersectingPathSetPair Q I J (4 * w) (2 * Dhat))
    (hD : 8 * w ≤ Dhat)
    {c : State.ClusterIndex}
    (hc : c ∈ State.smallBoundaryClusters) :
    HappyCluster P I (State.cluster c) w Dhat :=
  State.happy_of_final_good_of_boundary_lt hfinal hint hD c
    ((State.mem_smallBoundaryClusters c).1 hc)

/-- The counting half of Observation 4.14, conditional on Observation 4.12.
If at least half of the final clusters lie in `C₁`, then the number of
clusters times `D` is at most twice the number of selected `Σ`-paths. -/
theorem clusterCount_mul_D_le_two_card_of_half_small
    {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    {I : Subfamily P} {J : Finset Q.Index} {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hint : P.IntersectingPathSetPair Q I J (4 * w) (2 * Dhat))
    (hD : 8 * w ≤ Dhat)
    (hhalf : State.clusterCount ≤ 2 * State.smallBoundaryClusters.card) :
    State.clusterCount * Dhat ≤ 2 * I.card := by
  classical
  let small := State.smallBoundaryClusters
  let contained : State.ClusterIndex → Finset P.Index :=
    fun c => containedInCluster P I (State.cluster c)
  have hsmall_lower :
      small.card * Dhat ≤ ∑ c ∈ small, (contained c).card := by
    calc
      small.card * Dhat = ∑ c ∈ small, Dhat := by
        simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ c ∈ small, (contained c).card := by
        refine Finset.sum_le_sum ?_
        intro c hc
        exact (State.happy_of_mem_smallBoundaryClusters hfinal hint hD hc).2
  have hpairwise :
      ∀ c ∈ small, ∀ d ∈ small, c ≠ d →
        Disjoint (contained c) (contained d) := by
    intro c hc d hd hne
    exact State.disjoint_containedInCluster_of_ne hne
  let U : Finset P.Index := small.disjiUnion contained hpairwise
  have hUsub : U ⊆ I := by
    intro i hi
    rcases Finset.mem_disjiUnion.1 hi with ⟨c, hc, hiC⟩
    exact ((mem_containedInCluster P I (State.cluster c) i).1 hiC).1
  have hsum_le_I :
      (∑ c ∈ small, (contained c).card) ≤ I.card := by
    have hcardU : U.card = ∑ c ∈ small, (contained c).card := by
      dsimp [U]
      rw [Finset.card_disjiUnion]
    exact hcardU.ge.trans (Finset.card_le_card hUsub)
  have hsmallD_le_I : small.card * Dhat ≤ I.card :=
    hsmall_lower.trans hsum_le_I
  calc
    State.clusterCount * Dhat ≤ (2 * small.card) * Dhat := by
      exact Nat.mul_le_mul_right Dhat hhalf
    _ = 2 * (small.card * Dhat) := by ring
    _ ≤ 2 * I.card := by
      exact Nat.mul_le_mul_left 2 hsmallD_le_I

/-- Final-paragraph deleted-path bound.  Once Observation 4.14 gives
`r * D ≤ 2 |Σ|`, the deleted-edge budget and `D ≥ 8w` imply that at most a
quarter of the selected paths are destroyed. -/
theorem four_mul_hitEdges_card_le_of_clusterCount_mul_D_le_two_card
    {P : PathPacking G S T} {I : Subfamily P} {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hcount : State.clusterCount * Dhat ≤ 2 * I.card)
    (hD : 8 * w ≤ Dhat) :
    4 * (hitEdges P I State.deletedEdges).card ≤ I.card := by
  classical
  have hhit_budget :
      (hitEdges P I State.deletedEdges).card ≤ State.clusterCount * w := by
    have hhit := State.hitEdges_card_le_budget
    have hbudget :
        (State.clusterCount - 1) * w ≤ State.clusterCount * w :=
      Nat.mul_le_mul_right w (Nat.sub_le _ _)
    exact hhit.trans hbudget
  have hfour_cluster : 4 * (State.clusterCount * w) ≤ I.card := by
    nlinarith
  exact (Nat.mul_le_mul_left 4 hhit_budget).trans hfour_cluster

/-- Surviving selected paths assigned to one of the small-boundary clusters.
These are the retained paths in the final assembly of Theorem 4.11. -/
noncomputable def retainedInSmallBoundaryClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w) :
    Finset P.Index := by
  classical
  exact (surviving P I State.deletedEdges).filter fun i =>
    ∃ c ∈ State.smallBoundaryClusters, (P.path i).vertexSet ⊆ State.cluster c

theorem mem_retainedInSmallBoundaryClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (i : P.Index) :
    i ∈ State.retainedInSmallBoundaryClusters ↔
      i ∈ surviving P I State.deletedEdges ∧
        ∃ c ∈ State.smallBoundaryClusters,
          (P.path i).vertexSet ⊆ State.cluster c := by
  classical
  simp [retainedInSmallBoundaryClusters]

/-- The final collection of happy clusters.  The paper retains paths contained
in happy clusters, not just in the small-boundary subcollection `C₁`. -/
noncomputable def happyClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w) (Dhat : ℕ) :
    Finset State.ClusterIndex := by
  classical
  exact Finset.univ.filter fun c => HappyCluster P I (State.cluster c) w Dhat

theorem mem_happyClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (Dhat : ℕ) (c : State.ClusterIndex) :
    c ∈ State.happyClusters Dhat ↔
      HappyCluster P I (State.cluster c) w Dhat := by
  classical
  simp [happyClusters]

/-- Observation 4.13 implies that every small-boundary cluster belongs to the
final happy-cluster collection. -/
theorem smallBoundaryClusters_subset_happyClusters
    {S' T' : Finset V}
    {P : PathPacking G S T} {Q : PathPacking G S' T'}
    {I : Subfamily P} {J : Finset Q.Index} {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hint : P.IntersectingPathSetPair Q I J (4 * w) (2 * Dhat))
    (hD : 8 * w ≤ Dhat) :
    State.smallBoundaryClusters ⊆ State.happyClusters Dhat := by
  intro c hc
  exact (State.mem_happyClusters Dhat c).2
    (State.happy_of_mem_smallBoundaryClusters hfinal hint hD hc)

/-- Surviving selected paths assigned to a happy cluster. -/
noncomputable def retainedInHappyClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w) (Dhat : ℕ) :
    Finset P.Index := by
  classical
  exact (surviving P I State.deletedEdges).filter fun i =>
    ∃ c ∈ State.happyClusters Dhat, (P.path i).vertexSet ⊆ State.cluster c

theorem mem_retainedInHappyClusters
    {P : PathPacking G S T} {I : Subfamily P} {w : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (Dhat : ℕ) (i : P.Index) :
    i ∈ State.retainedInHappyClusters Dhat ↔
      i ∈ surviving P I State.deletedEdges ∧
        ∃ c ∈ State.happyClusters Dhat,
          (P.path i).vertexSet ⊆ State.cluster c := by
  classical
  simp [retainedInHappyClusters]

/-- If at least half of the clusters are happy, then the happy clusters contain
at least half of the surviving selected paths.  This formalizes the paragraph
after Observation 4.14. -/
theorem surviving_card_le_two_retainedInHappyClusters_card
    {P : PathPacking G S T} {I : Subfamily P} {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hhalfHappy : State.clusterCount ≤ 2 * (State.happyClusters Dhat).card) :
    (surviving P I State.deletedEdges).card ≤
      2 * (State.retainedInHappyClusters Dhat).card := by
  classical
  let happy := State.happyClusters Dhat
  let unhappy : Finset State.ClusterIndex := Finset.univ \ happy
  let contained : State.ClusterIndex → Finset P.Index :=
    fun c => containedInCluster P I (State.cluster c)
  have hpairwise :
      ∀ c ∈ (Finset.univ : Finset State.ClusterIndex),
        ∀ d ∈ (Finset.univ : Finset State.ClusterIndex), c ≠ d →
          Disjoint (contained c) (contained d) := by
    intro c hc d hd hne
    exact State.disjoint_containedInCluster_of_ne hne
  have hpairwise_happy :
      ∀ c ∈ happy, ∀ d ∈ happy, c ≠ d →
        Disjoint (contained c) (contained d) := by
    intro c hc d hd hne
    exact hpairwise c (by simp) d (by simp) hne
  have hpairwise_unhappy :
      ∀ c ∈ unhappy, ∀ d ∈ unhappy, c ≠ d →
        Disjoint (contained c) (contained d) := by
    intro c hc d hd hne
    exact hpairwise c (by simp) d (by simp) hne
  let Uhappy : Finset P.Index := happy.disjiUnion contained hpairwise_happy
  let Uunhappy : Finset P.Index := unhappy.disjiUnion contained hpairwise_unhappy
  have hretained_eq : State.retainedInHappyClusters Dhat = Uhappy := by
    ext i
    constructor
    · intro hi
      rcases (State.mem_retainedInHappyClusters Dhat i).1 hi with
        ⟨hsurv, c, hchappy, hiC⟩
      have hiI : i ∈ I :=
        (mem_surviving P I State.deletedEdges i).1 hsurv |>.1
      exact Finset.mem_disjiUnion.2
        ⟨c, hchappy,
          (mem_containedInCluster P I (State.cluster c) i).2 ⟨hiI, hiC⟩⟩
    · intro hi
      rcases Finset.mem_disjiUnion.1 hi with ⟨c, hchappy, hiC⟩
      have hsurv : i ∈ surviving P I State.deletedEdges :=
        State.containedInCluster_subset_surviving c hiC
      exact (State.mem_retainedInHappyClusters Dhat i).2
        ⟨hsurv, c, hchappy,
          ((mem_containedInCluster P I (State.cluster c) i).1 hiC).2⟩
  have hsurv_subset_union :
      surviving P I State.deletedEdges ⊆ Uhappy ∪ Uunhappy := by
    intro i hi
    rcases State.surviving_contained i hi with ⟨c, hiC⟩
    by_cases hchappy : c ∈ happy
    · exact Finset.mem_union_left _ (Finset.mem_disjiUnion.2
        ⟨c, hchappy,
          (mem_containedInCluster P I (State.cluster c) i).2
            ⟨(mem_surviving P I State.deletedEdges i).1 hi |>.1, hiC⟩⟩)
    · have hcunhappy : c ∈ unhappy := by
        simp [unhappy, hchappy]
      exact Finset.mem_union_right _ (Finset.mem_disjiUnion.2
        ⟨c, hcunhappy,
          (mem_containedInCluster P I (State.cluster c) i).2
            ⟨(mem_surviving P I State.deletedEdges i).1 hi |>.1, hiC⟩⟩)
  have hsurv_card_le :
      (surviving P I State.deletedEdges).card ≤ Uhappy.card + Uunhappy.card := by
    exact (Finset.card_le_card hsurv_subset_union).trans
      (Finset.card_union_le Uhappy Uunhappy)
  have hUhappy_card :
      Uhappy.card = ∑ c ∈ happy, (contained c).card := by
    dsimp [Uhappy]
    rw [Finset.card_disjiUnion]
  have hUunhappy_card :
      Uunhappy.card = ∑ c ∈ unhappy, (contained c).card := by
    dsimp [Uunhappy]
    rw [Finset.card_disjiUnion]
  have hhappy_lower :
      happy.card * Dhat ≤ Uhappy.card := by
    rw [hUhappy_card]
    calc
      happy.card * Dhat = ∑ c ∈ happy, Dhat := by
        simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ c ∈ happy, (contained c).card := by
        refine Finset.sum_le_sum ?_
        intro c hc
        exact ((State.mem_happyClusters Dhat c).1 hc).2
  have hunhappy_upper :
      Uunhappy.card ≤ unhappy.card * Dhat := by
    rw [hUunhappy_card]
    calc
      (∑ c ∈ unhappy, (contained c).card) ≤ ∑ c ∈ unhappy, Dhat := by
        refine Finset.sum_le_sum ?_
        intro c hc
        have hcnot : c ∉ happy := by
          simpa [unhappy] using hc
        have hnotHappy :
            ¬ HappyCluster P I (State.cluster c) w Dhat := by
          intro hhappy
          exact hcnot ((State.mem_happyClusters Dhat c).2 hhappy)
        have hlt : (contained c).card < Dhat := by
          exact Nat.lt_of_not_ge (by
            intro hDle
            exact hnotHappy ⟨hfinal c, hDle⟩)
        exact Nat.le_of_lt hlt
      _ = unhappy.card * Dhat := by
        simp [Finset.sum_const, Nat.mul_comm]
  have hunhappy_card_le_happy : unhappy.card ≤ happy.card := by
    have hsub : happy ⊆ (Finset.univ : Finset State.ClusterIndex) := by
      intro c hc
      simp
    have hpart := Finset.card_sdiff_add_card_eq_card hsub
    have hpart' : unhappy.card + happy.card = State.clusterCount := by
      simpa [unhappy, DecompositionState.clusterCount] using hpart
    have hhalfHappy' : State.clusterCount ≤ 2 * happy.card := by
      simpa [happy] using hhalfHappy
    omega
  have hUunhappy_le_Uhappy : Uunhappy.card ≤ Uhappy.card := by
    exact hunhappy_upper.trans
      ((Nat.mul_le_mul_right Dhat hunhappy_card_le_happy).trans hhappy_lower)
  calc
    (surviving P I State.deletedEdges).card ≤ Uhappy.card + Uunhappy.card :=
      hsurv_card_le
    _ ≤ Uhappy.card + Uhappy.card := Nat.add_le_add_left hUunhappy_le_Uhappy _
    _ = 2 * Uhappy.card := by ring
    _ = 2 * (State.retainedInHappyClusters Dhat).card := by
      rw [hretained_eq]

end DecompositionState

/-- The output object promised by Theorem 4.11.  Clusters are represented by
their vertex sets; disjointness is vertex-disjointness. -/
structure Theorem411Output
    (P : PathPacking G S T) (I : Subfamily P) (w D : ℕ) where
  /-- The finite index type for the cluster collection. -/
  ClusterIndex : Type u
  /-- The cluster index type is finite. -/
  [clusterFintype : Fintype ClusterIndex]
  /-- The cluster index type has decidable equality. -/
  [clusterDecidableEq : DecidableEq ClusterIndex]
  /-- The vertex set of each cluster. -/
  cluster : ClusterIndex → Finset V
  /-- Distinct clusters are vertex-disjoint. -/
  cluster_disjoint :
    Pairwise fun c d => Disjoint (cluster c) (cluster d)
  /-- Every cluster in the collection is happy. -/
  happy : ∀ c : ClusterIndex, HappyCluster P I (cluster c) w D
  /-- The retained subset `Σ'`. -/
  retained : Finset P.Index
  /-- Retained paths were selected from the original `Σ`. -/
  retained_subset : retained ⊆ I
  /-- At least a quarter of the original selected paths are retained.  This
  avoids division by using the equivalent natural-number inequality
  `|Σ| ≤ 4 |Σ'|`. -/
  quarter_retained : I.card ≤ 4 * retained.card
  /-- Every retained path belongs to one of the happy clusters. -/
  retained_contained :
    ∀ i ∈ retained, ∃ c : ClusterIndex,
      i ∈ containedInCluster P I (cluster c)

attribute [instance] Theorem411Output.clusterFintype
attribute [instance] Theorem411Output.clusterDecidableEq

namespace Theorem411Output

variable [Fintype V]

/-- Empty input needs no clusters and retains the empty family. -/
noncomputable def empty
    (P : PathPacking G S T) (w D : ℕ) :
    Theorem411Output P (∅ : Finset P.Index) w D where
  ClusterIndex := PEmpty.{u+1}
  cluster := fun c => nomatch c
  cluster_disjoint := by
    intro c
    cases c
  happy := by
    intro c
    cases c
  retained := ∅
  retained_subset := by
    intro i hi
    simp at hi
  quarter_retained := by
    simp
  retained_contained := by
    intro i hi
    simp at hi

/-- If the whole ambient vertex set is already a happy cluster, then Theorem
4.11 is witnessed by the singleton cluster collection and retaining all
selected `Σ` paths. -/
noncomputable def singletonUniv
    (P : PathPacking G S T) (I : Subfamily P) {w D : ℕ}
    (hweak :
      WeakEdgeWellLinkedIn G (Finset.univ : Finset V)
        (endpointSetInCluster P I (Finset.univ : Finset V)) w)
    (hD : D ≤ I.card) :
    Theorem411Output P I w D where
  ClusterIndex := PUnit
  cluster := fun _ => Finset.univ
  cluster_disjoint := by
    intro a b hne
    cases a
    cases b
    exact (hne rfl).elim
  happy := by
    intro c
    constructor
    · simpa [GoodCluster] using hweak
    · simpa using hD
  retained := I
  retained_subset := by
    intro i hi
    exact hi
  quarter_retained := by
    nlinarith
  retained_contained := by
    intro i hi
    refine ⟨PUnit.unit, ?_⟩
    simp [containedInCluster, hi]

/-- Assemble the output of Theorem 4.11 from a final decomposition state,
assuming the two global counting estimates later supplied by the state
invariants:

* `r * D ≤ 2 |Σ|` (Observation 4.14), and
* at least half of the surviving paths lie in small-boundary clusters.

All cluster happiness, retained-subset, containment, and destroyed-path
bookkeeping is discharged here. -/
noncomputable def ofFinalState
    {S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking G S' T')
    (I : Subfamily P) (J : Finset Q.Index) {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hint : P.IntersectingPathSetPair Q I J (4 * w) (2 * Dhat))
    (hD : 8 * w ≤ Dhat)
    (hcount : State.clusterCount * Dhat ≤ 2 * I.card)
    (hretained_half :
      (surviving P I State.deletedEdges).card ≤
        2 * State.retainedInSmallBoundaryClusters.card) :
    Theorem411Output P I w Dhat where
  ClusterIndex := {c : State.ClusterIndex // c ∈ State.smallBoundaryClusters}
  cluster := fun c => State.cluster c.1
  cluster_disjoint := by
    intro c d hne
    exact State.cluster_disjoint (fun h => hne (Subtype.ext h))
  happy := by
    intro c
    exact State.happy_of_mem_smallBoundaryClusters hfinal hint hD c.2
  retained := State.retainedInSmallBoundaryClusters
  retained_subset := by
    intro i hi
    have hsurv :=
      (State.mem_retainedInSmallBoundaryClusters i).1 hi |>.1
    exact (mem_surviving P I State.deletedEdges i).1 hsurv |>.1
  quarter_retained := by
    have hpart :
        (surviving P I State.deletedEdges).card +
          (hitEdges P I State.deletedEdges).card = I.card :=
      surviving_card_add_hitEdges_card P I State.deletedEdges
    have hhit :
        4 * (hitEdges P I State.deletedEdges).card ≤ I.card :=
      State.four_mul_hitEdges_card_le_of_clusterCount_mul_D_le_two_card
        hcount hD
    omega
  retained_contained := by
    intro i hi
    rcases (State.mem_retainedInSmallBoundaryClusters i).1 hi with
      ⟨hsurv, c, hcsmall, hiC⟩
    have hiI : i ∈ I :=
      (mem_surviving P I State.deletedEdges i).1 hsurv |>.1
    refine ⟨⟨c, hcsmall⟩, ?_⟩
    exact (mem_containedInCluster P I (State.cluster c) i).2
      ⟨hiI, hiC⟩

/-- Assemble the output of Theorem 4.11 from the exact final happy-cluster
collection used in the paper, given the counting fact that happy clusters
contain at least half of the surviving selected paths. -/
noncomputable def ofFinalHappyState
    (P : PathPacking G S T) (I : Subfamily P) {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hD : 8 * w ≤ Dhat)
    (hcount : State.clusterCount * Dhat ≤ 2 * I.card)
    (hretained_half :
      (surviving P I State.deletedEdges).card ≤
        2 * (State.retainedInHappyClusters Dhat).card) :
    Theorem411Output P I w Dhat where
  ClusterIndex := {c : State.ClusterIndex // c ∈ State.happyClusters Dhat}
  cluster := fun c => State.cluster c.1
  cluster_disjoint := by
    intro c d hne
    exact State.cluster_disjoint (fun h => hne (Subtype.ext h))
  happy := by
    intro c
    exact (State.mem_happyClusters Dhat c.1).1 c.2
  retained := State.retainedInHappyClusters Dhat
  retained_subset := by
    intro i hi
    have hsurv :=
      (State.mem_retainedInHappyClusters Dhat i).1 hi |>.1
    exact (mem_surviving P I State.deletedEdges i).1 hsurv |>.1
  quarter_retained := by
    have hpart :
        (surviving P I State.deletedEdges).card +
          (hitEdges P I State.deletedEdges).card = I.card :=
      surviving_card_add_hitEdges_card P I State.deletedEdges
    have hhit :
        4 * (hitEdges P I State.deletedEdges).card ≤ I.card :=
      State.four_mul_hitEdges_card_le_of_clusterCount_mul_D_le_two_card
        hcount hD
    omega
  retained_contained := by
    intro i hi
    rcases (State.mem_retainedInHappyClusters Dhat i).1 hi with
      ⟨hsurv, c, hchappy, hiC⟩
    have hiI : i ∈ I :=
      (mem_surviving P I State.deletedEdges i).1 hsurv |>.1
    refine ⟨⟨c, hchappy⟩, ?_⟩
    exact (mem_containedInCluster P I (State.cluster c) i).2
      ⟨hiI, hiC⟩

/-- Theorem 4.11 from a final decomposition state and Observation 4.12
(`|C₁| ≥ r/2`).  The next lemma supplies Observation 4.12 from the state
invariants. -/
theorem ofFinalDecompositionState
    {S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking G S' T')
    (I : Subfamily P) (J : Finset Q.Index) {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hint : P.IntersectingPathSetPair Q I J (4 * w) (2 * Dhat))
    (hD : 8 * w ≤ Dhat)
    (hhalfSmall :
      State.clusterCount ≤ 2 * State.smallBoundaryClusters.card) :
    Nonempty (Theorem411Output P I w Dhat) := by
  classical
  have hcount :
      State.clusterCount * Dhat ≤ 2 * I.card :=
    State.clusterCount_mul_D_le_two_card_of_half_small
      hfinal hint hD hhalfSmall
  have hsmall_happy :
      State.smallBoundaryClusters ⊆ State.happyClusters Dhat :=
    State.smallBoundaryClusters_subset_happyClusters hfinal hint hD
  have hhalfHappy :
      State.clusterCount ≤ 2 * (State.happyClusters Dhat).card := by
    exact hhalfSmall.trans
      (Nat.mul_le_mul_left 2 (Finset.card_le_card hsmall_happy))
  have hretained_half :
      (surviving P I State.deletedEdges).card ≤
        2 * (State.retainedInHappyClusters Dhat).card :=
    State.surviving_card_le_two_retainedInHappyClusters_card hfinal hhalfHappy
  exact ⟨Theorem411Output.ofFinalHappyState
    P I State hD hcount hretained_half⟩

/-- Theorem 4.11 from a final decomposition state, with Observation 4.12 now
proved from the state invariants. -/
theorem ofFinalDecompositionState_of_pos
    {S' T' : Finset V}
    (P : PathPacking G S T) (Q : PathPacking G S' T')
    (I : Subfamily P) (J : Finset Q.Index) {w Dhat : ℕ}
    (State : DecompositionState (V := V) (G := G) P I w)
    (hw : 0 < w)
    (hfinal : ∀ c : State.ClusterIndex,
      GoodCluster P I (State.cluster c) w)
    (hint : P.IntersectingPathSetPair Q I J (4 * w) (2 * Dhat))
    (hD : 8 * w ≤ Dhat) :
    Nonempty (Theorem411Output P I w Dhat) :=
  ofFinalDecompositionState P Q I J State hfinal hint hD
    (State.halfSmallBoundary_of_pos hw)

end Theorem411Output

theorem card_le_of_intersectingPathSetPair_nonempty_right
    {S T S' T' : Finset V} [Fintype V]
    (Sigma : PathPacking G S T) (Q : PathPacking G S' T')
    {I : Finset Sigma.Index} {J : Finset Q.Index} {w D : ℕ}
    (hw : 0 < w)
    (hI : I.Nonempty)
    (hint : Sigma.IntersectingPathSetPair Q I J (4 * w) (2 * D)) :
    2 * D ≤ I.card := by
  classical
  rcases hI with ⟨i, hi⟩
  have hright :
      4 * w ≤ (Sigma.intersectingRightIndices Q J i).card :=
    hint.1 i hi
  have hright_pos :
      0 < (Sigma.intersectingRightIndices Q J i).card := by
    exact lt_of_lt_of_le (by nlinarith) hright
  rcases Finset.card_pos.1 hright_pos with ⟨q, hqright⟩
  have hqJ : q ∈ J :=
    intersectingRightIndices_subset Sigma Q J i hqright
  have hleft :
      2 * D ≤ (Sigma.intersectingLeftIndices Q I q).card :=
    hint.2 q hqJ
  exact hleft.trans (Finset.card_le_card
    (intersectingLeftIndices_subset Sigma Q I q))

theorem card_le_of_intersectingPathSetPair_nonempty
    {S T S' T' : Finset V} [Fintype V]
    (Sigma : PathPacking G S T) (Q : PathPacking G S' T')
    {I : Finset Sigma.Index} {J : Finset Q.Index} {w D : ℕ}
    (hw : 0 < w)
    (hI : I.Nonempty)
    (hint : Sigma.IntersectingPathSetPair Q I J (4 * w) (2 * D)) :
    D ≤ I.card := by
  have htwo :
      2 * D ≤ I.card :=
    card_le_of_intersectingPathSetPair_nonempty_right
      Sigma Q hw hI hint
  omega

/-- The easy one-cluster branch of Theorem 4.11. -/
theorem theorem411_of_global_weak
    {S T S' T' : Finset V} [Fintype V]
    (Sigma : PathPacking G S T) (Q : PathPacking G S' T')
    (I : Finset Sigma.Index) (J : Finset Q.Index) {w D : ℕ}
    (hw : 0 < w)
    (hint : Sigma.IntersectingPathSetPair Q I J (4 * w) (2 * D))
    (hweak :
      WeakEdgeWellLinkedIn G (Finset.univ : Finset V)
        (endpointSetInCluster Sigma I (Finset.univ : Finset V)) w) :
    Nonempty (Theorem411Output Sigma I w D) := by
  classical
  by_cases hI : I.Nonempty
  · have hD : D ≤ I.card :=
      card_le_of_intersectingPathSetPair_nonempty
        Sigma Q hw hI hint
    exact ⟨Theorem411Output.singletonUniv Sigma I hweak hD⟩
  · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.1 hI
    cases hIempty
    exact ⟨Theorem411Output.empty Sigma w D⟩

/-- Theorem 4.11 from the local splitting lemma: every bad cluster has a
sparse cut whose two sides each retain a surviving selected `Σ` path.  The
final theorem supplies this splitter from Observation 4.10 and the child
survivor counting lemma. -/
theorem theorem411_of_splitter
    {S T S' T' : Finset V} [Fintype V]
    (Sigma : PathPacking G S T) (Q : PathPacking G S' T')
    (I : Finset Sigma.Index) (J : Finset Q.Index) {w D : ℕ}
    (hw : 0 < w)
    (hint : Sigma.IntersectingPathSetPair Q I J (4 * w) (2 * D))
    (hD : 8 * w ≤ D)
    (hsplit :
      ∀ (State : DecompositionState (V := V) (G := G) Sigma I w)
        (c : State.ClusterIndex),
        ¬ GoodCluster Sigma I (State.cluster c) w →
          ∃ Cut : SparseTerminalCut G (State.cluster c)
              (endpointSetInCluster Sigma I (State.cluster c)) w,
            DecompositionState.ChildSurvivors State c Cut) :
    Nonempty (Theorem411Output Sigma I w D) := by
  classical
  by_cases hI : I.Nonempty
  · let State₀ := DecompositionState.initial Sigma I w hI
    rcases DecompositionState.exists_final_state_of_splitter
        (P := Sigma) (I := I) (w := w) hsplit State₀ with
      ⟨State, hfinal⟩
    exact Theorem411Output.ofFinalDecompositionState_of_pos
      Sigma Q I J State hw hfinal hint hD
  · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.1 hI
    cases hIempty
    exact ⟨Theorem411Output.empty Sigma w D⟩

/-- The paper-shaped statement of Chuzhoy--Tan Theorem 4.11 for finite path
packings.  The two input families are `Σ` and `Q`; `I` and `J` select the
subfamilies under discussion. -/
def Theorem411Statement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {S T S' T' : Finset V}
    (Sigma : PathPacking G S T) (Q : PathPacking G S' T')
    (I : Finset Sigma.Index) (J : Finset Q.Index) {w D : ℕ},
      0 < w →
        0 < D →
          Sigma.IntersectingPathSetPair Q I J (4 * w) (2 * D) →
            8 * w ≤ D →
              Nonempty (Theorem411Output Sigma I w D)

/-- Chuzhoy--Tan Theorem 4.11.  The splitting algorithm terminates in a final
decomposition, and the retained surviving paths in happy clusters form the
required quarter-size subfamily. -/
theorem theorem411 : Theorem411Statement.{u} := by
  intro V _instFintype _instDecidableEq G S T S' T'
    Sigma Q I J w D hw _hDpos hint hD
  classical
  refine theorem411_of_splitter Sigma Q I J hw hint hD ?_
  intro State c hbad
  rcases State.exists_sparse_cut_of_not_good c hbad with ⟨Cut⟩
  exact ⟨Cut, State.childSurvivors_of_sparse_cut c Cut⟩

end PathPacking

end Section44

end SimpleGraph

end Lax17Proofs
