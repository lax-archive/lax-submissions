import Lax17Proofs.Source.Paths
import Mathlib.Data.Finset.Lattice.Fold

namespace Lax17Proofs

universe u v w

/-!
# Degree bounds for unions of path-packing support graphs

This file packages the degree bounds for graphs spanned by node-disjoint path
packings, together with additive bounds for finite graph unions.
-/

namespace SimpleGraph


namespace GraphPath

variable {V : Type u} [DecidableEq V]

private theorem eq_of_vertexIndex_eq
    {G : _root_.SimpleGraph V} (P : GraphPath G) {x y : V}
    (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet)
    (hindex : P.vertexIndex x = P.vertexIndex y) :
    x = y := by
  have hxy : P.Before x y :=
    (P.before_iff_vertexIndex_le).2 ⟨hx, hy, hindex.le⟩
  have hyx : P.Before y x :=
    (P.before_iff_vertexIndex_le).2 ⟨hy, hx, hindex.ge⟩
  exact P.before_antisymm hxy hyx

private noncomputable def pathNeighborFinset
    {G : _root_.SimpleGraph V} (P : GraphPath G) (x : V) : Finset V :=
  P.vertexSet.filter fun y => s(x, y) ∈ P.edgeSet

private theorem mem_pathNeighborFinset
    {G : _root_.SimpleGraph V} (P : GraphPath G) {x y : V} :
    y ∈ pathNeighborFinset P x ↔
      y ∈ P.vertexSet ∧ s(x, y) ∈ P.edgeSet := by
  classical
  simp [pathNeighborFinset]

private theorem pathNeighborFinset_card_le_two
    {G : _root_.SimpleGraph V} (P : GraphPath G) (x : V) :
    (pathNeighborFinset P x).card ≤ 2 := by
  classical
  let N := pathNeighborFinset P x
  have hcard_image : (N.image P.vertexIndex).card = N.card := by
    apply Finset.card_image_of_injOn
    intro y hy z hz hyz
    exact eq_of_vertexIndex_eq P
      ((mem_pathNeighborFinset P).1 hy).1
      ((mem_pathNeighborFinset P).1 hz).1 hyz
  have hsubset :
      N.image P.vertexIndex ⊆
        ({P.vertexIndex x - 1, P.vertexIndex x + 1} : Finset ℕ) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨y, hyN, rfl⟩
    have hyV : y ∈ P.vertexSet := (mem_pathNeighborFinset P).1 hyN |>.1
    have he : s(x, y) ∈ P.edgeSet := (mem_pathNeighborFinset P).1 hyN |>.2
    have hxV : x ∈ P.vertexSet :=
      (endpoints_mem_vertexSet_of_edgeSet P he).1
    have hyx : y ≠ x := by
      intro h
      subst y
      have hxx : G.Adj x x := by
        simpa using P.edgeSet_subset_edgeSet he
      exact hxx.ne rfl
    have hindex_ne : P.vertexIndex y ≠ P.vertexIndex x := by
      intro h
      exact hyx (eq_of_vertexIndex_eq P hyV hxV h)
    have hright : P.vertexIndex y ≤ P.vertexIndex x + 1 :=
      P.edge_vertexIndex_le_succ he
    have he' : s(y, x) ∈ P.edgeSet := by
      simpa [Sym2.eq_swap] using he
    have hleft : P.vertexIndex x ≤ P.vertexIndex y + 1 :=
      P.edge_vertexIndex_le_succ he'
    have hcases :
        P.vertexIndex y + 1 = P.vertexIndex x ∨
          P.vertexIndex y = P.vertexIndex x + 1 := by
      omega
    rcases hcases with hprev | hnext
    · have : P.vertexIndex y = P.vertexIndex x - 1 := by omega
      simp [this]
    · simp [hnext]
  calc
    N.card = (N.image P.vertexIndex).card := hcard_image.symm
    _ ≤ ({P.vertexIndex x - 1, P.vertexIndex x + 1} : Finset ℕ).card :=
      Finset.card_le_card hsubset
    _ ≤ 2 := by simp

/-- Two path edges incident with the source of a simple path have the same
other endpoint. -/
private theorem edge_neighbor_eq_of_source
    {G : _root_.SimpleGraph V} (P : GraphPath G) {y z : V}
    (hy : s(P.source, y) ∈ P.edgeSet)
    (hz : s(P.source, z) ∈ P.edgeSet) :
    y = z := by
  classical
  have hyV := (endpoints_mem_vertexSet_of_edgeSet P hy).2
  have hzV := (endpoints_mem_vertexSet_of_edgeSet P hz).2
  have hyNe : y ≠ P.source := by
    intro h
    subst y
    exact (P.edgeSet_subset_edgeSet hy).ne rfl
  have hzNe : z ≠ P.source := by
    intro h
    subst z
    exact (P.edgeSet_subset_edgeSet hz).ne rfl
  have hyIndex : P.vertexIndex y = 1 := by
    have hle : P.vertexIndex y ≤ 1 := by
      simpa using P.edge_vertexIndex_le_succ hy
    have hne : P.vertexIndex y ≠ 0 := by
      intro hzero
      exact hyNe (eq_of_vertexIndex_eq P hyV P.source_mem_vertexSet
        (by simpa using hzero))
    omega
  have hzIndex : P.vertexIndex z = 1 := by
    have hle : P.vertexIndex z ≤ 1 := by
      simpa using P.edge_vertexIndex_le_succ hz
    have hne : P.vertexIndex z ≠ 0 := by
      intro hzero
      exact hzNe (eq_of_vertexIndex_eq P hzV P.source_mem_vertexSet
        (by simpa using hzero))
    omega
  exact eq_of_vertexIndex_eq P hyV hzV (hyIndex.trans hzIndex.symm)

/-- Two path edges incident with the same endpoint of a simple path have the
same other endpoint. -/
private theorem edge_neighbor_eq_of_isEndpoint
    {G : _root_.SimpleGraph V} (P : GraphPath G) {x y z : V}
    (hx : P.IsEndpoint x)
    (hy : s(x, y) ∈ P.edgeSet) (hz : s(x, z) ∈ P.edgeSet) :
    y = z := by
  rcases hx with rfl | rfl
  · exact edge_neighbor_eq_of_source P hy hz
  · have hy' : s(P.reverse.source, y) ∈ P.reverse.edgeSet := by
      simpa [Sym2.eq_swap] using hy
    have hz' : s(P.reverse.source, z) ∈ P.reverse.edgeSet := by
      simpa [Sym2.eq_swap] using hz
    exact edge_neighbor_eq_of_source P.reverse hy' hz'

end GraphPath

namespace PathPacking

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T : Finset V}

private theorem degreeAtMost_spanningGraph_of_mem_path
    (P : PathPacking G S T) {x : V} (i : P.Index)
    (hxi : x ∈ (P.path i).vertexSet) :
    DegreeAtMost P.spanningGraph x 2 := by
  classical
  let N := GraphPath.pathNeighborFinset (P.path i) x
  refine ⟨N, ?_, GraphPath.pathNeighborFinset_card_le_two (P.path i) x⟩
  intro y
  constructor
  · intro hy
    have he : s(x, y) ∈ (P.path i).edgeSet :=
      (GraphPath.mem_pathNeighborFinset (P.path i)).1 hy |>.2
    have hne : x ≠ y := by
      have hxy : G.Adj x y := by
        simpa using GraphPath.edgeSet_subset_edgeSet (P.path i) he
      exact hxy.ne
    exact (P.spanningGraph_adj_iff_exists_path_edge).2
      ⟨⟨i, he⟩, hne⟩
  · intro hxy
    rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hxy with
      ⟨⟨j, hej⟩, _⟩
    have hxj : x ∈ (P.path j).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path j) hej).1
    have hyj : y ∈ (P.path j).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path j) hej).2
    have hji : j = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.node_disjoint hne) hxj hxi
    subst j
    exact (GraphPath.mem_pathNeighborFinset (P.path i)).2 ⟨hyj, hej⟩

private theorem degreeAtMost_spanningGraph_of_not_mem
    (P : PathPacking G S T) {x : V} (hx : x ∉ P.vertexSet) :
    DegreeAtMost P.spanningGraph x 2 := by
  classical
  refine ⟨∅, ?_, by simp⟩
  intro y
  constructor
  · simp
  · intro hxy
    rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hxy with
      ⟨⟨i, hei⟩, _⟩
    have hxi : x ∈ (P.path i).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hei).1
    exact False.elim (hx ((P.mem_vertexSet).2 ⟨i, hxi⟩))

/-- The graph spanned by a node-disjoint path packing has maximum degree at
most two. -/
theorem maxDegreeAtMost_spanningGraph (P : PathPacking G S T) :
    MaxDegreeAtMost P.spanningGraph 2 := by
  classical
  intro x
  by_cases hx : x ∈ P.vertexSet
  · rcases (P.mem_vertexSet).1 hx with ⟨i, hxi⟩
    exact degreeAtMost_spanningGraph_of_mem_path P i hxi
  · exact degreeAtMost_spanningGraph_of_not_mem P hx

/-- If a vertex can occur in a node-disjoint packing only as a path endpoint,
then it has degree at most one in the graph spanned by the packing. -/
theorem degreeAtMost_one_spanningGraph_of_endpoint_only
    (P : PathPacking G S T) {x : V}
    (hendpoint :
      ∀ i : P.Index, x ∈ (P.path i).vertexSet →
        (P.path i).IsEndpoint x) :
    DegreeAtMost P.spanningGraph x 1 := by
  classical
  let N := P.vertexSet.filter fun y => P.spanningGraph.Adj x y
  refine ⟨N, ?_, ?_⟩
  · intro y
    constructor
    · exact fun hy => (Finset.mem_filter.mp hy).2
    · intro hxy
      rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hxy with
        ⟨⟨i, hei⟩, _⟩
      have hyi : y ∈ (P.path i).vertexSet :=
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hei).2
      exact Finset.mem_filter.mpr
        ⟨(P.mem_vertexSet).2 ⟨i, hyi⟩, hxy⟩
  · rw [Finset.card_le_one]
    intro y hy z hz
    have hxy : P.spanningGraph.Adj x y := (Finset.mem_filter.mp hy).2
    have hxz : P.spanningGraph.Adj x z := (Finset.mem_filter.mp hz).2
    rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hxy with
      ⟨⟨i, hei⟩, _⟩
    rcases (P.spanningGraph_adj_iff_exists_path_edge).1 hxz with
      ⟨⟨j, hej⟩, _⟩
    have hxi : x ∈ (P.path i).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path i) hei).1
    have hxj : x ∈ (P.path j).vertexSet :=
      (GraphPath.endpoints_mem_vertexSet_of_edgeSet (P.path j) hej).1
    have hji : j = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (P.node_disjoint hne) hxj hxi
    subst j
    exact GraphPath.edge_neighbor_eq_of_isEndpoint
      (P.path i) (hendpoint i hxi) hei hej

end PathPacking

/-- Maximum-degree bounds add under graph union. -/
theorem maxDegreeAtMost_sup
    {V : Type u} {G H : _root_.SimpleGraph V} {d e : ℕ}
    (hG : MaxDegreeAtMost G d) (hH : MaxDegreeAtMost H e) :
    MaxDegreeAtMost (G ⊔ H) (d + e) := by
  classical
  intro x
  rcases hG x with ⟨NG, hNG, hcardG⟩
  rcases hH x with ⟨NH, hNH, hcardH⟩
  refine ⟨NG ∪ NH, ?_, ?_⟩
  · intro y
    simp [hNG y, hNH y]
  · exact (Finset.card_union_le NG NH).trans
      (Nat.add_le_add hcardG hcardH)

/-- A weighted maximum-degree bound for a finite supremum of graphs. -/
theorem maxDegreeAtMost_finset_sup
    {V : Type u} {ι : Type v} (I : Finset ι)
    (F : ι → _root_.SimpleGraph V) (d : ι → ℕ)
    (hF : ∀ i ∈ I, MaxDegreeAtMost (F i) (d i)) :
    MaxDegreeAtMost (I.sup F) (∑ i ∈ I, d i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simp only [Finset.sup_empty, Finset.sum_empty]
      intro x
      refine ⟨∅, ?_, by simp⟩
      simp [IsNeighborFinset]
  | @insert i I hi ih =>
      rw [Finset.sup_insert, Finset.sum_insert hi]
      apply maxDegreeAtMost_sup
      · exact hF i (Finset.mem_insert_self i I)
      · apply ih
        intro j hj
        exact hF j (Finset.mem_insert_of_mem hj)

namespace PathPacking

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ι : Type v}
variable {S T : ι → Finset V}

/-- The union of the support graphs of a finite family of path packings has
maximum degree at most twice the number of packings. -/
theorem maxDegreeAtMost_finset_sup_spanningGraph
    (I : Finset ι) (P : (i : ι) → PathPacking G (S i) (T i)) :
    MaxDegreeAtMost (I.sup fun i => (P i).spanningGraph) (2 * I.card) := by
  have h := maxDegreeAtMost_finset_sup I
    (fun i => (P i).spanningGraph) (fun _ => 2)
    (fun i hi => (P i).maxDegreeAtMost_spanningGraph)
  simpa [Nat.mul_comm] using h

/-- The union of all support graphs in a finite indexed family of path
packings has maximum degree at most twice the cardinality of the index type. -/
theorem maxDegreeAtMost_univ_sup_spanningGraph
    [Fintype ι] (P : (i : ι) → PathPacking G (S i) (T i)) :
    MaxDegreeAtMost
      (Finset.univ.sup fun i => (P i).spanningGraph)
      (2 * Fintype.card ι) := by
  simpa using maxDegreeAtMost_finset_sup_spanningGraph
    (I := (Finset.univ : Finset ι)) P

end PathPacking

end SimpleGraph

end Lax17Proofs
