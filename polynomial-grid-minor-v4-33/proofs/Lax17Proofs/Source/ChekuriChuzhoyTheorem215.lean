import Mathlib.Tactic
import Mathlib.Order.Preorder.Finite
import Lax17Proofs.Source.ChekuriChuzhoyStructural

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Theorem 2.15

This file starts the self-contained formal proof of Chekuri--Chuzhoy
Theorem 2.15: a connected graph either has a spanning tree with many leaves or
has a long path all of whose vertices have ambient degree two.

The proof follows Appendix A.2 of `chekuri-chuzhoy.pdf`.  We first set up the
finite optimization step used by the paper: among all spanning trees of the
input connected graph, choose one with the maximum number of leaves.  The rest
of the proof uses the two local edge-swap improvements to show that long
maximal degree-two paths in such a tree are genuine 2-paths in the ambient
graph.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The repository's finset-neighborhood degree predicate agrees with
mathlib's `degree` whenever the adjacency relation is decidable. -/
theorem degreeEquals_iff_degree_eq (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (d : ℕ) :
    DegreeEquals G v d ↔ G.degree v = d := by
  classical
  constructor
  · rintro ⟨N, hN, hcard⟩
    have hN_eq : N = G.neighborFinset v := by
      ext u
      exact (hN u).trans (by simp)
    simpa [hN_eq] using hcard
  · intro hdeg
    refine ⟨G.neighborFinset v, ?_, hdeg⟩
    intro u
    simp

/-- Three distinct neighbors force degree at least three. -/
theorem three_le_degree_of_three_neighbors
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ G.degree v := by
  classical
  have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl
    · simp [ha]
    · simp [hb]
    · simp [hc]
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  have hle := Finset.card_le_card hsub
  simpa [hcard] using hle

/-- The leaves of a graph, expressed with the repository's finset-degree
predicate. -/
noncomputable def leafSet (G : _root_.SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v : V => DegreeEquals G v 1

omit [DecidableEq V] in
@[simp] theorem mem_leafSet (G : _root_.SimpleGraph V) (v : V) :
    v ∈ leafSet G ↔ DegreeEquals G v 1 := by
  classical
  simp [leafSet]

/-- The number of leaves of a graph. -/
noncomputable def leafCount (G : _root_.SimpleGraph V) : ℕ :=
  (leafSet G).card

/-- Vertices of a fixed mathlib degree. -/
noncomputable def degreeSet (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v : V => G.degree v = d

/-- Vertices of degree at least three.  These are the branch vertices in the
tree-counting part of the proof. -/
noncomputable def branchVertexSet (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := by
  classical
  exact Finset.univ.filter fun v : V => 3 ≤ G.degree v

omit [DecidableEq V] in
@[simp] theorem mem_degreeSet (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (v : V) :
    v ∈ degreeSet G d ↔ G.degree v = d := by
  classical
  simp [degreeSet]

omit [DecidableEq V] in
@[simp] theorem mem_branchVertexSet (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    v ∈ branchVertexSet G ↔ 3 ≤ G.degree v := by
  classical
  simp [branchVertexSet]

omit [DecidableEq V] in
/-- In decidable graphs, `leafSet` is the ordinary set of degree-one vertices. -/
theorem leafSet_eq_degreeSet (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    leafSet G = degreeSet G 1 := by
  classical
  ext v
  simp [degreeEquals_iff_degree_eq]

omit [DecidableEq V] in
theorem leafCount_eq_degreeSet_card (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] :
    leafCount G = (degreeSet G 1).card := by
  classical
  simp [leafCount, leafSet_eq_degreeSet]

/-- The non-degree-two skeleton vertices of a nontrivial tree: leaves and
branch vertices. -/
noncomputable def treeSkeletonVertexSet (T : _root_.SimpleGraph V)
    [DecidableRel T.Adj] : Finset V :=
  degreeSet T 1 ∪ branchVertexSet T

/-- Vertices of degree exactly two in a tree. -/
noncomputable def treeDegreeTwoVertexSet (T : _root_.SimpleGraph V)
    [DecidableRel T.Adj] : Finset V :=
  degreeSet T 2

@[simp] theorem mem_treeSkeletonVertexSet (T : _root_.SimpleGraph V)
    [DecidableRel T.Adj] (v : V) :
    v ∈ treeSkeletonVertexSet T ↔ T.degree v = 1 ∨ 3 ≤ T.degree v := by
  classical
  simp [treeSkeletonVertexSet]

omit [DecidableEq V] in
@[simp] theorem mem_treeDegreeTwoVertexSet (T : _root_.SimpleGraph V)
    [DecidableRel T.Adj] (v : V) :
    v ∈ treeDegreeTwoVertexSet T ↔ T.degree v = 2 := by
  classical
  simp [treeDegreeTwoVertexSet]

omit [DecidableEq V] in
/-- In a nontrivial tree, every vertex has positive degree. -/
theorem one_le_tree_degree_of_nontrivial (T : _root_.SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) [Nontrivial V] (v : V) :
    1 ≤ T.degree v := by
  exact Nat.succ_le_of_lt (hT.connected.preconnected.degree_pos_of_nontrivial v)

omit [DecidableEq V] in
/-- The degree-sum identity for a tree, written as an integer excess formula.

The total excess `∑ (deg(v) - 2)` is `-2`.  This is the counting invariant
used in Appendix A.2 to bound the number of branch vertices by the number of
leaves. -/
theorem tree_degree_excess_sum_eq_neg_two (T : _root_.SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) :
    (∑ v : V, ((T.degree v : ℤ) - 2)) = -2 := by
  classical
  have hsumNat : ∑ v : V, T.degree v = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hsumInt : (∑ v : V, (T.degree v : ℤ)) =
      (2 * T.edgeFinset.card : ℤ) := by
    exact_mod_cast hsumNat
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hedgeInt : (T.edgeFinset.card : ℤ) + 1 = (Fintype.card V : ℤ) := by
    exact_mod_cast hedge
  calc
    (∑ v : V, ((T.degree v : ℤ) - 2))
        = (∑ v : V, (T.degree v : ℤ)) - ∑ _v : V, (2 : ℤ) := by
          rw [Finset.sum_sub_distrib]
    _ = (2 * T.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * 2 := by
          simp [hsumInt, Finset.sum_const]
    _ = -2 := by
          omega

omit [DecidableEq V] in
/-- A tree with at least two vertices has no more branch vertices
(degree at least three) than leaves. -/
theorem branchVertexSet_card_le_leafCount_of_tree
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    (branchVertexSet T).card ≤ leafCount T := by
  classical
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos : ∀ v : V, 1 ≤ T.degree v :=
    one_le_tree_degree_of_nontrivial T hT
  have hpoint :
      ∀ v : V,
        (if 3 ≤ T.degree v then (1 : ℤ) else 0) ≤
          (if T.degree v = 1 then (1 : ℤ) else 0) +
            ((T.degree v : ℤ) - 2) := by
    intro v
    by_cases hb : 3 ≤ T.degree v
    · simp [hb]
      omega
    · simp [hb]
      by_cases hleaf : T.degree v = 1
      · simp [hleaf]
      · have hvpos : 1 ≤ T.degree v := hpos v
        have hdeg2 : 2 ≤ T.degree v := by omega
        have hdeg_le_two : T.degree v ≤ 2 := by omega
        have hdeg : T.degree v = 2 := by omega
        simp [hdeg]
  have hsum :=
    Finset.sum_le_sum (fun v _hv => hpoint v)
      (s := (Finset.univ : Finset V))
  have hexcess := tree_degree_excess_sum_eq_neg_two T hT
  have hbranchPlusTwoInt :
      ((branchVertexSet T).card : ℤ) + 2 ≤
        ((degreeSet T 1).card : ℤ) := by
    simpa [branchVertexSet, degreeSet, Finset.sum_add_distrib, hexcess]
      using hsum
  have hbranchLeafInt :
      ((branchVertexSet T).card : ℤ) ≤ ((degreeSet T 1).card : ℤ) := by
    linarith
  have hbranchLeaf : (branchVertexSet T).card ≤ (degreeSet T 1).card := by
    exact_mod_cast hbranchLeafInt
  simpa [leafCount_eq_degreeSet_card] using hbranchLeaf

/-- If a nontrivial tree has fewer than `L` leaves, then its leaf-or-branch
skeleton has at most `2 * L` vertices. -/
theorem treeSkeletonVertexSet_card_le_two_mul
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) {L : ℕ}
    (hleaves : leafCount T < L) :
    (treeSkeletonVertexSet T).card ≤ 2 * L := by
  classical
  have hbranch :
      (branchVertexSet T).card ≤ leafCount T :=
    branchVertexSet_card_le_leafCount_of_tree T hT hcard
  have hleafCard : (degreeSet T 1).card = leafCount T := by
    simp [leafCount_eq_degreeSet_card]
  have hskeleton :
      (treeSkeletonVertexSet T).card ≤
        (degreeSet T 1).card + (branchVertexSet T).card := by
    simpa [treeSkeletonVertexSet] using
      Finset.card_union_le (degreeSet T 1) (branchVertexSet T)
  calc
    (treeSkeletonVertexSet T).card
        ≤ (degreeSet T 1).card + (branchVertexSet T).card := hskeleton
    _ ≤ leafCount T + leafCount T := by
          omega
    _ ≤ L + L := by
          omega
    _ = 2 * L := by
          omega

/-- The strict leaf bound gives the slightly sharper successor form needed
when the component count is bounded by `|skeleton| + 1`. -/
theorem treeSkeletonVertexSet_card_succ_le_two_mul
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) {L : ℕ}
    (hleaves : leafCount T < L) :
    (treeSkeletonVertexSet T).card + 1 ≤ 2 * L := by
  classical
  have hbranch :
      (branchVertexSet T).card ≤ leafCount T :=
    branchVertexSet_card_le_leafCount_of_tree T hT hcard
  have hleafCard : (degreeSet T 1).card = leafCount T := by
    simp [leafCount_eq_degreeSet_card]
  have hskeleton :
      (treeSkeletonVertexSet T).card ≤
        (degreeSet T 1).card + (branchVertexSet T).card := by
    simpa [treeSkeletonVertexSet] using
      Finset.card_union_le (degreeSet T 1) (branchVertexSet T)
  omega

/-- In a nontrivial tree, the degree-two vertices and the leaf-or-branch
skeleton partition the vertex set. -/
theorem treeDegreeTwoVertexSet_card_add_skeleton_card
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    (treeDegreeTwoVertexSet T).card + (treeSkeletonVertexSet T).card =
      Fintype.card V := by
  classical
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hdisj :
      Disjoint (treeDegreeTwoVertexSet T) (treeSkeletonVertexSet T) := by
    rw [Finset.disjoint_left]
    intro v hv2 hvs
    have hv2' : T.degree v = 2 := (mem_treeDegreeTwoVertexSet T v).1 hv2
    rcases (mem_treeSkeletonVertexSet T v).1 hvs with hv1 | hv3
    · omega
    · omega
  have hcover :
      treeDegreeTwoVertexSet T ∪ treeSkeletonVertexSet T =
        (Finset.univ : Finset V) := by
    ext v
    have hpos : 1 ≤ T.degree v := one_le_tree_degree_of_nontrivial T hT v
    by_cases h2 : T.degree v = 2
    · simp [h2]
    · by_cases h1 : T.degree v = 1
      · simp [h1]
      · have h3 : 3 ≤ T.degree v := by omega
        simp [h2, h1, h3]
  have hcardUnion :
      (treeDegreeTwoVertexSet T ∪ treeSkeletonVertexSet T).card =
        (treeDegreeTwoVertexSet T).card + (treeSkeletonVertexSet T).card :=
    Finset.card_union_of_disjoint hdisj
  calc
    (treeDegreeTwoVertexSet T).card + (treeSkeletonVertexSet T).card
        = (treeDegreeTwoVertexSet T ∪ treeSkeletonVertexSet T).card := hcardUnion.symm
    _ = Fintype.card V := by simp [hcover]

/-- If a nontrivial tree has fewer than `L` leaves, then many vertices have
degree exactly two. -/
theorem treeDegreeTwoVertexSet_card_ge_card_sub_two_mul
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) {L : ℕ}
    (hleaves : leafCount T < L) :
    Fintype.card V - 2 * L ≤ (treeDegreeTwoVertexSet T).card := by
  classical
  have hpartition :=
    treeDegreeTwoVertexSet_card_add_skeleton_card T hT hcard
  have hskeleton :=
    treeSkeletonVertexSet_card_le_two_mul T hT hcard hleaves
  omega

/-- A finite union has cardinal at most the sum of the cardinalities of the
pieces. -/
theorem finset_card_biUnion_le_sum_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ x ∈ s, (f x).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (Finset.card_union_le (f a) (s.biUnion f)).trans
        (Nat.add_le_add_left ih _)

/-- In a nontrivial tree, the degree-two vertices and the skeleton vertices
cover all vertices. -/
theorem treeDegreeTwoVertexSet_union_skeleton_eq_univ
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    treeDegreeTwoVertexSet T ∪ treeSkeletonVertexSet T =
      (Finset.univ : Finset V) := by
  classical
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  ext v
  have hpos : 1 ≤ T.degree v := one_le_tree_degree_of_nontrivial T hT v
  by_cases h2 : T.degree v = 2
  · simp [h2]
  · by_cases h1 : T.degree v = 1
    · simp [h1]
    · have h3 : 3 ≤ T.degree v := by omega
      simp [h2, h1, h3]

/-- In a nontrivial tree, the skeleton degree sum is at most twice the number
of skeleton vertices. -/
theorem treeSkeletonVertexSet_degree_sum_le_two_mul_card
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    (∑ v ∈ treeSkeletonVertexSet T, T.degree v) ≤
      2 * (treeSkeletonVertexSet T).card := by
  classical
  let D := treeDegreeTwoVertexSet T
  let S := treeSkeletonVertexSet T
  have hdisj : Disjoint D S := by
    rw [Finset.disjoint_left]
    intro v hvD hvS
    have hv2 : T.degree v = 2 := by simpa [D] using (mem_treeDegreeTwoVertexSet T v).1 hvD
    rcases (mem_treeSkeletonVertexSet T v).1 (by simpa [S] using hvS) with hv1 | hv3
    · omega
    · omega
  have hcover : D ∪ S = (Finset.univ : Finset V) := by
    simpa [D, S] using treeDegreeTwoVertexSet_union_skeleton_eq_univ T hT hcard
  have hsumSplit :
      (∑ v : V, T.degree v) =
        (∑ v ∈ D, T.degree v) + (∑ v ∈ S, T.degree v) := by
    rw [← hcover, Finset.sum_union hdisj]
  have hsumD : (∑ v ∈ D, T.degree v) = 2 * D.card := by
    calc
      (∑ v ∈ D, T.degree v) = ∑ _v ∈ D, 2 := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        exact (by simpa [D] using (mem_treeDegreeTwoVertexSet T v).1 hv)
      _ = 2 * D.card := by simp [Nat.mul_comm]
  have htotal : ∑ v : V, T.degree v = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hpartition :
      D.card + S.card = Fintype.card V := by
    simpa [D, S] using treeDegreeTwoVertexSet_card_add_skeleton_card T hT hcard
  have hgoal : (∑ v ∈ S, T.degree v) ≤ 2 * S.card := by
    omega
  simpa [S] using hgoal

/-- Every tree edge that is not internal to the degree-two set is incident with
a skeleton vertex, so these edges are charged to skeleton incidences. -/
theorem tree_edgeFinset_sdiff_degreeTwo_sym2_card_le_skeleton_degree_sum
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    (T.edgeFinset \ (treeDegreeTwoVertexSet T).sym2).card ≤
      ∑ v ∈ treeSkeletonVertexSet T, T.degree v := by
  classical
  let D := treeDegreeTwoVertexSet T
  let S := treeSkeletonVertexSet T
  let U : Finset (Sym2 V) := S.biUnion fun v => T.incidenceFinset v
  have hcover : D ∪ S = (Finset.univ : Finset V) := by
    simpa [D, S] using treeDegreeTwoVertexSet_union_skeleton_eq_univ T hT hcard
  have hsub : T.edgeFinset \ D.sym2 ⊆ U := by
    intro e he
    rcases Finset.mem_sdiff.mp he with ⟨heT, heNotD⟩
    have heout : s(e.out.1, e.out.2) = e := by
      rw [Sym2.mk, e.out_eq]
    by_cases hfstD : e.out.1 ∈ D
    · have hsndNotD : e.out.2 ∉ D := by
        intro hsndD
        exact heNotD (by
          rw [← heout]
          exact Finset.mk_mem_sym2_iff.2 ⟨hfstD, hsndD⟩)
      have hsndS : e.out.2 ∈ S := by
        have hmem : e.out.2 ∈ D ∪ S := by simp [hcover]
        simpa [hsndNotD] using hmem
      refine Finset.mem_biUnion.2 ⟨e.out.2, hsndS, ?_⟩
      rw [T.incidenceFinset_eq_filter]
      exact Finset.mem_filter.2 ⟨heT, Sym2.out_snd_mem e⟩
    · have hfstS : e.out.1 ∈ S := by
        have hmem : e.out.1 ∈ D ∪ S := by simp [hcover]
        simpa [hfstD] using hmem
      refine Finset.mem_biUnion.2 ⟨e.out.1, hfstS, ?_⟩
      rw [T.incidenceFinset_eq_filter]
      exact Finset.mem_filter.2 ⟨heT, Sym2.out_fst_mem e⟩
  calc
    (T.edgeFinset \ D.sym2).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (T.incidenceFinset v).card :=
        finset_card_biUnion_le_sum_card S (fun v => T.incidenceFinset v)
    _ = ∑ v ∈ S, T.degree v := by simp

omit [Fintype V] in
/-- A simple graph path has one more vertex than its walk length. -/
theorem graphPath_vertexSet_card_eq_walk_length_add_one
    {G : _root_.SimpleGraph V} (P : GraphPath G) :
    P.vertexSet.card = P.walk.length + 1 := by
  classical
  rw [GraphPath.vertexSet]
  calc
    P.walk.support.toFinset.card = P.walk.support.length :=
      List.toFinset_card_of_nodup P.isPath.support_nodup
    _ = P.walk.length + 1 := by
      rw [P.walk.length_support]

/-- A connected finite graph of maximum degree at most two has a path through
all vertices.  This is the standard longest-path argument: a longest path can
not be extended at an endpoint, and if an outside path first hits it at an
internal vertex then that hit has three distinct neighbors. -/
theorem exists_spanning_path_of_connected_degree_le_two
    (H : _root_.SimpleGraph V) [DecidableRel H.Adj]
    (hH : H.Connected) (hdeg : ∀ v : V, H.degree v ≤ 2) :
    ∃ P : GraphPath H, P.vertexSet = (Finset.univ : Finset V) := by
  classical
  haveI : Nonempty V := hH.nonempty
  rcases _root_.SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H with
    ⟨s, t, W, hWpath, hmax⟩
  let P : GraphPath H :=
    { source := s, target := t, walk := W, isPath := hWpath }
  refine ⟨P, ?_⟩
  ext z
  constructor
  · intro _hz
    simp
  · intro _hz
    by_contra hzP
    rcases hH.exists_isPath z P.source with ⟨Wz, hWz⟩
    let Q : GraphPath H :=
      { source := z, target := P.source, walk := Wz, isPath := hWz }
    have hmeet : (Q.vertexSet ∩ P.vertexSet).Nonempty := by
      refine ⟨P.source, ?_⟩
      exact Finset.mem_inter.2
        ⟨by simpa [Q] using GraphPath.target_mem_vertexSet Q,
          GraphPath.source_mem_vertexSet P⟩
    let R : GraphPath H := Q.cleanPrefixToSet P.vertexSet hmeet
    have hR_target_mem : R.target ∈ P.vertexSet := by
      simpa [R] using Q.cleanPrefixToSet_target_mem P.vertexSet hmeet
    have hR_source_not : R.source ∉ P.vertexSet := by
      simpa [R, Q] using hzP
    have hRne : R.source ≠ R.target := by
      intro h
      exact hR_source_not (by simpa [h] using hR_target_mem)
    have hRpos : 0 < R.walk.length :=
      _root_.SimpleGraph.Walk.not_nil_iff_lt_length.mp
        (R.walk_not_nil_of_source_ne_target hRne)
    have hRinternal : R.InternallyDisjointFromSet P.vertexSet := by
      simpa [R] using Q.cleanPrefixToSet_internallyDisjointFromSet P.vertexSet hmeet
    have hinter :
        ∀ ⦃v : V⦄, v ∈ R.vertexSet → v ∈ P.vertexSet → v = R.target := by
      intro v hvR hvP
      rcases hRinternal hvR hvP with hsrc | htgt
      · exact False.elim (hR_source_not (by simpa [hsrc] using hvP))
      · exact htgt
    by_cases hx_source : R.target = P.source
    · let S : GraphPath H :=
        R.appendWithEqOfInterSubsetTarget P hx_source (by
          intro v hvR hvP
          exact hinter hvR hvP)
      have hle : S.walk.length ≤ P.walk.length :=
        hmax S.source S.target S.walk S.isPath
      have hlen : S.walk.length = R.walk.length + P.walk.length := by
        simp [S, GraphPath.appendWithEqOfInterSubsetTarget, GraphPath.appendWithEq]
      omega
    by_cases hx_target : R.target = P.target
    · let S : GraphPath H :=
        R.appendWithEqOfInterSubsetTarget P.reverse (by simpa using hx_target) (by
          intro v hvR hvP
          exact hinter hvR (by simpa using hvP))
      have hle : S.walk.length ≤ P.walk.length :=
        hmax S.source S.target S.walk S.isPath
      have hlen : S.walk.length = R.walk.length + P.walk.length := by
        have hrev : P.reverse.walk.length = P.walk.length := by
          simp [GraphPath.reverse]
        rw [show S.walk.length = R.walk.length + P.reverse.walk.length by
          simp [S, GraphPath.appendWithEqOfInterSubsetTarget, GraphPath.appendWithEq]]
        rw [hrev]
      omega
    let Apath : GraphPath H := P.takeUntil hR_target_mem
    have hApath_ne : Apath.source ≠ Apath.target := by
      intro h
      exact hx_source (by simpa [Apath] using h.symm)
    let A : V := Apath.penultimate
    have hA_adj : H.Adj A R.target := by
      simpa [A, Apath] using Apath.penultimate_adj_target hApath_ne
    have hA_mem_Apath : A ∈ Apath.vertexSet := by
      simpa [A] using Apath.penultimate_mem_vertexSet hApath_ne
    have hA_mem_P : A ∈ P.vertexSet := by
      simpa [Apath] using P.takeUntil_vertexSet_subset hR_target_mem hA_mem_Apath
    have hA_before : P.Before A R.target := by
      simpa [Apath] using P.before_of_mem_takeUntil hR_target_mem hA_mem_Apath
    let Bpath : GraphPath H := P.dropUntil hR_target_mem
    have hBpath_ne : Bpath.source ≠ Bpath.target := by
      intro h
      exact hx_target (by simpa [Bpath] using h)
    have hBpath_not_nil : ¬ Bpath.walk.Nil :=
      Bpath.walk_not_nil_of_source_ne_target hBpath_ne
    let B : V := Bpath.walk.snd
    have hB_adj : H.Adj R.target B := by
      simpa [B, Bpath] using Bpath.walk.adj_snd hBpath_not_nil
    have hB_mem_Bpath : B ∈ Bpath.vertexSet := by
      have htail : B ∈ Bpath.walk.support.tail := by
        simpa [B] using
          (_root_.SimpleGraph.Walk.snd_mem_tail_support hBpath_not_nil)
      have hsupp : B ∈ Bpath.walk.support := List.mem_of_mem_tail htail
      simp [B, GraphPath.vertexSet, hsupp]
    have hB_mem_P : B ∈ P.vertexSet := by
      simpa [Bpath] using P.dropUntil_vertexSet_subset hR_target_mem hB_mem_Bpath
    have htarget_before_B : P.Before R.target B := by
      exact ⟨hR_target_mem, by simpa [Bpath] using hB_mem_Bpath⟩
    have hA_ne_target : A ≠ R.target := hA_adj.ne
    have hB_ne_target : B ≠ R.target := hB_adj.ne.symm
    have hA_ne_B : A ≠ B := by
      intro hAB
      have htarget_before_A : P.Before R.target A := by
        simpa [hAB] using htarget_before_B
      exact hA_ne_target (P.before_antisymm hA_before htarget_before_A)
    let C : V := R.penultimate
    have hC_adj : H.Adj C R.target := by
      simpa [C] using R.penultimate_adj_target hRne
    have hC_mem_R : C ∈ R.vertexSet := by
      simpa [C] using R.penultimate_mem_vertexSet hRne
    have hC_ne_target : C ≠ R.target := hC_adj.ne
    have hC_not_mem_P : C ∉ P.vertexSet := by
      intro hCP
      rcases hRinternal hC_mem_R hCP with hsrc | htgt
      · exact hR_source_not (by simpa [hsrc] using hCP)
      · exact hC_ne_target htgt
    have hA_ne_C : A ≠ C := by
      intro h
      exact hC_not_mem_P (by simpa [h] using hA_mem_P)
    have hB_ne_C : B ≠ C := by
      intro h
      exact hC_not_mem_P (by simpa [h] using hB_mem_P)
    have hthree : 3 ≤ H.degree R.target :=
      three_le_degree_of_three_neighbors H hA_adj.symm hB_adj hC_adj.symm
        hA_ne_B hA_ne_C hB_ne_C
    have htwo := hdeg R.target
    omega

end ChekuriChuzhoy

namespace GraphPath

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}

/-- Map a bundled graph path along a graph embedding. -/
def mapEmbedding (P : GraphPath G) (φ : G ↪g H) : GraphPath H where
  source := φ P.source
  target := φ P.target
  walk := P.walk.map φ.toHom
  isPath := _root_.SimpleGraph.Walk.map_isPath_of_injective φ.injective P.isPath

@[simp] theorem mapEmbedding_vertexSet (P : GraphPath G) (φ : G ↪g H) :
    (P.mapEmbedding φ).vertexSet = P.vertexSet.image φ.toEmbedding := by
  classical
  ext y
  simp [mapEmbedding, vertexSet, _root_.SimpleGraph.Walk.support_map]

@[simp] theorem mapEmbedding_vertexSet_card (P : GraphPath G) (φ : G ↪g H) :
    (P.mapEmbedding φ).vertexSet.card = P.vertexSet.card := by
  classical
  rw [mapEmbedding_vertexSet]
  exact Finset.card_image_of_injective P.vertexSet φ.injective

theorem mem_vertexSet_of_mem_edgeSet {P : GraphPath G} {e : Sym2 V} {v : V}
    (he : e ∈ P.edgeSet) (hv : v ∈ e) :
    v ∈ P.vertexSet := by
  classical
  have heWalk : e ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [edgeSet] using he)
  exact by
    simpa [vertexSet] using P.walk.mem_support_of_mem_edges heWalk hv

theorem reachable_deleteEdge_of_not_mem_edgeSet {P : GraphPath G} (e : Sym2 V)
    (havoid : e ∉ P.edgeSet) :
    (G.deleteEdges {e}).Reachable P.source P.target := by
  classical
  have havoidWalk : e ∉ P.walk.edges := by
    intro he
    exact havoid (List.mem_toFinset.mpr (by simpa [edgeSet] using he))
  exact (P.walk.toDeleteEdge e havoidWalk).reachable

theorem dropLast_not_mem_edgeSet_of_incident_target (P : GraphPath G)
    (hne : P.source ≠ P.target) {x : V} :
    s(P.target, x) ∉ P.dropLast.edgeSet := by
  classical
  intro he
  have htarget_mem :
      P.target ∈ P.dropLast.vertexSet :=
    mem_vertexSet_of_mem_edgeSet (P := P.dropLast) he (by simp)
  exact P.target_not_mem_dropLast_vertexSet hne htarget_mem

theorem mem_vertexSet_getVert (P : GraphPath G) {i : ℕ}
    (_hi : i ≤ P.walk.length) :
    P.walk.getVert i ∈ P.vertexSet := by
  classical
  simp [vertexSet]

theorem vertexIndex_getVert (P : GraphPath G) {i : ℕ}
    (hi : i ≤ P.walk.length) :
    P.vertexIndex (P.walk.getVert i) = i := by
  classical
  have hi' : i < P.walk.support.length := by
    rw [_root_.SimpleGraph.Walk.length_support]
    omega
  have hidx := P.isPath.support_nodup.idxOf_getElem i hi'
  have hget :
      P.walk.support[i]'hi' = P.walk.getVert i :=
    _root_.SimpleGraph.Walk.support_getElem_eq_getVert P.walk hi'
  simpa [vertexIndex, hget] using hidx

theorem getVert_vertexIndex_eq (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    P.walk.getVert (P.vertexIndex v) = v := by
  classical
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv
  simpa [vertexIndex] using P.walk.getVert_support_idxOf hvSupport

theorem before_getVert_of_le (P : GraphPath G) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.walk.length) :
    P.Before (P.walk.getVert i) (P.walk.getVert j) := by
  classical
  have hi : i ≤ P.walk.length := hij.trans hj
  refine (P.before_iff_vertexIndex_le).2 ?_
  refine ⟨P.mem_vertexSet_getVert hi, P.mem_vertexSet_getVert hj, ?_⟩
  rw [P.vertexIndex_getVert hi, P.vertexIndex_getVert hj]
  exact hij

theorem segmentOfBefore_getVert_card (P : GraphPath G) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.walk.length) :
    let hbefore := P.before_getVert_of_le hij hj
    (P.segmentOfBefore hbefore).vertexSet.card = j - i + 1 := by
  classical
  dsimp
  let a : V := P.walk.getVert i
  let b : V := P.walk.getVert j
  have hi : i ≤ P.walk.length := hij.trans hj
  let hbefore : P.Before a b := by
    simpa [a, b] using P.before_getVert_of_le hij hj
  let Q : GraphPath G := P.dropUntil hbefore.choose
  have hbQ : b ∈ Q.vertexSet := by
    simpa [Q] using hbefore.choose_spec
  have hidxQ : Q.vertexIndex b = j - i := by
    have hidxAdd :
        P.vertexIndex b = P.vertexIndex a + Q.vertexIndex b := by
      simpa [Q, a, b] using
        P.vertexIndex_eq_add_vertexIndex_dropUntil hbefore.choose
          hbefore.choose_spec
    have hia : P.vertexIndex a = i := by
      simpa [a] using P.vertexIndex_getVert hi
    have hjb : P.vertexIndex b = j := by
      simpa [b] using P.vertexIndex_getVert hj
    omega
  have hlen :
      (P.segmentOfBefore hbefore).walk.length = j - i := by
    change (Q.takeUntil hbQ).walk.length = j - i
    have hlen' : (Q.takeUntil hbQ).walk.length = Q.vertexIndex b := by
      simp [GraphPath.takeUntil, GraphPath.vertexIndex,
        _root_.SimpleGraph.Walk.length_takeUntil]
    rw [hlen', hidxQ]
  have hcard :=
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.graphPath_vertexSet_card_eq_walk_length_add_one
      (P.segmentOfBefore hbefore)
  omega

end GraphPath

namespace ChekuriChuzhoy

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The subgraph of a tree induced by its degree-two vertices, as a graph on
the corresponding subtype.  Its connected components are the maximal
degree-two paths used in Appendix A.2. -/
noncomputable def degreeTwoInducedGraph (T : _root_.SimpleGraph V)
    [DecidableRel T.Adj] :
    _root_.SimpleGraph {v : V // v ∈ treeDegreeTwoVertexSet T} :=
  T.induce {v : V | v ∈ treeDegreeTwoVertexSet T}

omit [DecidableEq V] in
@[simp] theorem degreeTwoInducedGraph_adj
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    {x y : {v : V // v ∈ treeDegreeTwoVertexSet T}} :
    (degreeTwoInducedGraph T).Adj x y ↔ T.Adj x.1 y.1 := by
  rfl

/-- Restricting to the degree-two vertices leaves maximum degree at most two. -/
theorem degreeTwoInducedGraph_degree_le_two
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    [DecidableRel (degreeTwoInducedGraph T).Adj]
    (x : {v : V // v ∈ treeDegreeTwoVertexSet T}) :
    (degreeTwoInducedGraph T).degree x ≤ 2 := by
  classical
  let emb : {v : V // v ∈ treeDegreeTwoVertexSet T} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsub :
      ((degreeTwoInducedGraph T).neighborFinset x).image emb ⊆
        T.neighborFinset x.1 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    have hxz : (degreeTwoInducedGraph T).Adj x z := by
      simpa using hz
    simpa [emb] using hxz
  have hcard :=
    Finset.card_le_card hsub
  have himage :
      (((degreeTwoInducedGraph T).neighborFinset x).image emb).card =
        (degreeTwoInducedGraph T).degree x := by
    calc
      (((degreeTwoInducedGraph T).neighborFinset x).image emb).card =
          ((degreeTwoInducedGraph T).neighborFinset x).card :=
        Finset.card_image_of_injective _ emb.injective
      _ = (degreeTwoInducedGraph T).degree x := rfl
  have hle :
      (degreeTwoInducedGraph T).degree x ≤ T.degree x.1 := by
    simpa [himage] using hcard
  have hxdeg : T.degree x.1 = 2 :=
    (mem_treeDegreeTwoVertexSet T x.1).1 x.2
  omega

/-- The finite support of a connected component. -/
noncomputable def connectedComponentVertexFinset
    (H : _root_.SimpleGraph V) (C : H.ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter fun v : V => v ∈ C.supp

omit [DecidableEq V] in
@[simp] theorem mem_connectedComponentVertexFinset
    (H : _root_.SimpleGraph V) (C : H.ConnectedComponent) (v : V) :
    v ∈ connectedComponentVertexFinset H C ↔ v ∈ C.supp := by
  classical
  simp [connectedComponentVertexFinset]

omit [DecidableEq V] in
/-- The vertex finsets of the connected components partition the vertex set. -/
theorem card_eq_sum_connectedComponentVertexFinset
    (H : _root_.SimpleGraph V) :
    Fintype.card V =
      ∑ C : H.ConnectedComponent, (connectedComponentVertexFinset H C).card := by
  classical
  let comps : Finset H.ConnectedComponent := Finset.univ
  have hmaps :
      ((Finset.univ : Finset V) : Set V).MapsTo H.connectedComponentMk comps := by
    intro v _hv
    simp [comps]
  have hcard :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset V)) (t := comps)
      (f := H.connectedComponentMk) hmaps
  have hfiber :
      ∀ C : H.ConnectedComponent,
        ({v ∈ (Finset.univ : Finset V) | H.connectedComponentMk v = C}).card =
          (connectedComponentVertexFinset H C).card := by
    intro C
    have hset :
        {v ∈ (Finset.univ : Finset V) | H.connectedComponentMk v = C} =
          connectedComponentVertexFinset H C := by
      ext v
      simp [connectedComponentVertexFinset,
        _root_.SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hset]
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ = ∑ C ∈ comps,
          ({v ∈ (Finset.univ : Finset V) | H.connectedComponentMk v = C}).card := hcard
    _ = ∑ C : H.ConnectedComponent,
          (connectedComponentVertexFinset H C).card := by
            simp [comps, hfiber]

omit [DecidableEq V] in
/-- A connected component finset has the same cardinality as its subtype of
vertices. -/
theorem connectedComponentVertexFinset_card_eq_nat_card
    (H : _root_.SimpleGraph V) (C : H.ConnectedComponent) :
    (connectedComponentVertexFinset H C).card = Nat.card C := by
  classical
  change (Finset.univ.filter (fun v : V => v ∈ C.supp)).card =
    Nat.card {v : V // v ∈ C.supp}
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype (fun v : V => v ∈ C.supp)).symm

/-- The component containing the first endpoint of an edge.  For actual edges
the choice of endpoint is irrelevant, because adjacent vertices lie in the same
connected component. -/
noncomputable def edgeComponent (H : _root_.SimpleGraph V) (e : Sym2 V) :
    H.ConnectedComponent :=
  H.connectedComponentMk e.out.1

/-- The edges of a graph whose two endpoints lie in a fixed connected
component. -/
noncomputable def componentEdgeFinset
    (H : _root_.SimpleGraph V) [Fintype H.edgeSet]
    (C : H.ConnectedComponent) :
    Finset (Sym2 V) :=
  H.edgeFinset ∩ (connectedComponentVertexFinset H C).sym2

omit [Fintype V] [DecidableEq V] in
/-- The endpoint selected by `Sym2.out` really is adjacent to the other
selected endpoint when the unordered pair is an edge. -/
theorem adj_out_of_mem_edgeFinset
    (H : _root_.SimpleGraph V) {e : Sym2 V} [Fintype H.edgeSet]
    (he : e ∈ H.edgeFinset) :
    H.Adj e.out.1 e.out.2 := by
  classical
  have heSet : e ∈ H.edgeSet := (_root_.SimpleGraph.mem_edgeFinset).1 he
  have heout : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  rw [← heout] at heSet
  simpa using heSet

/-- Edges whose selected endpoint lies in a component are exactly the edges
inside that component. -/
theorem edgeFinset_filter_edgeComponent_eq
    (H : _root_.SimpleGraph V) [Fintype H.edgeSet] [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (C : H.ConnectedComponent) :
    {e ∈ H.edgeFinset | edgeComponent H e = C} =
      componentEdgeFinset H C := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_filter.mp he with ⟨heH, hcomp⟩
    have hadj : H.Adj e.out.1 e.out.2 := adj_out_of_mem_edgeFinset H heH
    have hfst : e.out.1 ∈ C.supp := by
      simpa [edgeComponent] using hcomp
    have hsnd : e.out.2 ∈ C.supp :=
      (_root_.SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hadj).1 hfst
    refine Finset.mem_inter.2 ⟨?_, ?_⟩
    · have heSet : e ∈ H.edgeSet := by
        have h := heH
        unfold _root_.SimpleGraph.edgeFinset at h
        exact Set.mem_toFinset.mp h
      unfold _root_.SimpleGraph.edgeFinset
      exact Set.mem_toFinset.mpr heSet
    have heout : s(e.out.1, e.out.2) = e := by
      rw [Sym2.mk, e.out_eq]
    rw [← heout]
    exact Finset.mk_mem_sym2_iff.2
      ⟨by
        simpa [connectedComponentVertexFinset,
          _root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using hfst,
       by
        simpa [connectedComponentVertexFinset,
          _root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using hsnd⟩
  · intro he
    rcases Finset.mem_inter.mp he with ⟨heH, heC⟩
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · have heSet : e ∈ H.edgeSet := by
        have h := heH
        unfold _root_.SimpleGraph.edgeFinset at h
        exact Set.mem_toFinset.mp h
      unfold _root_.SimpleGraph.edgeFinset
      exact Set.mem_toFinset.mpr heSet
    have hfstFin : e.out.1 ∈ connectedComponentVertexFinset H C :=
      (Finset.mem_sym2_iff.1 heC) e.out.1 (Sym2.out_fst_mem e)
    have hfst : e.out.1 ∈ C.supp := by
      simpa [connectedComponentVertexFinset] using hfstFin
    simpa [componentEdgeFinset, edgeComponent,
      _root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using hfst

/-- The edge sets of the connected components partition the edge set. -/
theorem edgeFinset_card_eq_sum_connectedComponent_edgeFinset
    (H : _root_.SimpleGraph V) [Fintype H.edgeSet] [DecidableRel H.Adj] :
    H.edgeFinset.card =
      ∑ C : H.ConnectedComponent, (componentEdgeFinset H C).card := by
  classical
  let comps : Finset H.ConnectedComponent := Finset.univ
  have hmaps :
      ((H.edgeFinset : Finset (Sym2 V)) : Set (Sym2 V)).MapsTo
        (edgeComponent H) comps := by
    intro e _he
    simp [comps]
  have hcard :=
    Finset.card_eq_sum_card_fiberwise
      (s := H.edgeFinset) (t := comps) (f := edgeComponent H) hmaps
  have hfiber :
      ∀ C : H.ConnectedComponent,
        ({e ∈ H.edgeFinset | edgeComponent H e = C}).card =
          (componentEdgeFinset H C).card := by
    intro C
    have hfilter := edgeFinset_filter_edgeComponent_eq H C
    rw [hfilter]
  have hsumFiber :
      (∑ C ∈ comps, ({e ∈ H.edgeFinset | edgeComponent H e = C}).card) =
        ∑ C ∈ comps, (componentEdgeFinset H C).card := by
    exact Finset.sum_congr rfl (fun C _hC => hfiber C)
  calc
    H.edgeFinset.card
        = ∑ C ∈ comps, ({e ∈ H.edgeFinset | edgeComponent H e = C}).card := hcard
    _ = ∑ C : H.ConnectedComponent, (componentEdgeFinset H C).card := by
          exact hsumFiber.trans (by simp [comps])

/-- In a finite forest, the number of connected components plus the number of
edges is the number of vertices. -/
theorem isAcyclic_connectedComponent_card_add_edgeFinset_card
    (H : _root_.SimpleGraph V) [Fintype H.edgeSet] [DecidableRel H.Adj]
    (hH : H.IsAcyclic) :
    Fintype.card H.ConnectedComponent + H.edgeFinset.card = Fintype.card V := by
  classical
  have hvertices := card_eq_sum_connectedComponentVertexFinset H
  have hedges := edgeFinset_card_eq_sum_connectedComponent_edgeFinset H
  have hcomponent :
      ∀ C : H.ConnectedComponent,
        (componentEdgeFinset H C).card + 1 =
          (connectedComponentVertexFinset H C).card := by
    intro C
    letI : Fintype C := Subtype.fintype (fun v : V => v ∈ C.supp)
    have hCfinset :
        connectedComponentVertexFinset H C = C.supp.toFinset := by
      ext v
      simp [connectedComponentVertexFinset]
    let φ : C ≃ {v : V // v ∈ C.supp} := {
      toFun := fun x => ⟨(x : V), x.2⟩
      invFun := fun x => ⟨(x : V), x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl }
    let iso : C.toSimpleGraph ≃g H.induce C.supp := {
      toEquiv := φ
      map_rel_iff' := by
        intro x y
        rfl }
    have hisoCard :
        C.toSimpleGraph.edgeFinset.card =
          (H.induce C.supp).edgeFinset.card := by
      simpa [iso] using iso.card_edgeFinset_eq
    have hmap :
        (H.induce C.supp).edgeFinset.card =
          (H.edgeFinset ∩ C.supp.toFinset.sym2).card := by
      have hmapSet :=
        _root_.SimpleGraph.map_edgeFinset_induce (G := H) (s := C.supp)
      have hedgeEq :
          (@_root_.SimpleGraph.edgeFinset V H H.fintypeEdgeSet ∩
              C.supp.toFinset.sym2) =
            (H.edgeFinset ∩ C.supp.toFinset.sym2) := by
        ext e
        simp [_root_.SimpleGraph.mem_edgeFinset]
      calc
        (H.induce C.supp).edgeFinset.card =
            ((H.induce C.supp).edgeFinset.map
              (Function.Embedding.subtype (fun v : V => v ∈ C.supp)).sym2Map).card := by
              rw [Finset.card_map]
        _ = (H.edgeFinset ∩ C.supp.toFinset.sym2).card := by
              exact congrArg Finset.card (hmapSet.trans hedgeEq)
    have hcompEdgeCard :
        (componentEdgeFinset H C).card = C.toSimpleGraph.edgeFinset.card := by
      calc
        (componentEdgeFinset H C).card =
            (H.edgeFinset ∩ C.supp.toFinset.sym2).card := by
              apply congrArg Finset.card
              ext e
              simp [componentEdgeFinset, hCfinset,
                _root_.SimpleGraph.mem_edgeFinset]
        _ = (H.induce C.supp).edgeFinset.card := hmap.symm
        _ = C.toSimpleGraph.edgeFinset.card := hisoCard.symm
    have htree : C.toSimpleGraph.IsTree := hH.isTree_connectedComponent C
    have hcard := htree.card_edgeFinset
    have hvertsNat :=
      connectedComponentVertexFinset_card_eq_nat_card H C
    have hverts :
        (connectedComponentVertexFinset H C).card = Fintype.card C := by
      simpa [Nat.card_eq_fintype_card] using hvertsNat
    rw [hcompEdgeCard]
    exact hcard.trans hverts.symm
  have hsum :
      (∑ C : H.ConnectedComponent, (componentEdgeFinset H C).card) +
          Fintype.card H.ConnectedComponent =
        ∑ C : H.ConnectedComponent,
          (connectedComponentVertexFinset H C).card := by
    have hsum' :
        ∑ C : H.ConnectedComponent, ((componentEdgeFinset H C).card + 1) =
          ∑ C : H.ConnectedComponent,
            (connectedComponentVertexFinset H C).card := by
      exact Finset.sum_congr rfl (fun C _hC => hcomponent C)
    simpa [Finset.sum_add_distrib, Finset.sum_const] using hsum'
  calc
    Fintype.card H.ConnectedComponent + H.edgeFinset.card
        = (∑ C : H.ConnectedComponent, (componentEdgeFinset H C).card) +
            Fintype.card H.ConnectedComponent := by
          rw [hedges]
          exact Nat.add_comm (Fintype.card H.ConnectedComponent)
            (∑ C : H.ConnectedComponent, (componentEdgeFinset H C).card)
    _ = ∑ C : H.ConnectedComponent,
          (connectedComponentVertexFinset H C).card := hsum
    _ = Fintype.card V := hvertices.symm

/-- Every connected component of a finite graph of maximum degree at most two
has a simple path containing exactly the vertices of that component. -/
theorem exists_path_spanning_connectedComponent_of_degree_le_two
    (H : _root_.SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v : V, H.degree v ≤ 2)
    (C : H.ConnectedComponent) :
    ∃ P : GraphPath H, P.vertexSet = connectedComponentVertexFinset H C := by
  classical
  have hdegC : ∀ x : C, C.toSimpleGraph.degree x ≤ 2 := by
    intro x
    let emb : C ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    have hsub :
        (C.toSimpleGraph.neighborFinset x).image emb ⊆
          H.neighborFinset x.1 := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      have hxz : C.toSimpleGraph.Adj x z := by
        simpa using hz
      have hxzH : H.Adj x.1 z.1 := by
        simpa [_root_.SimpleGraph.ConnectedComponent.toSimpleGraph] using hxz
      simpa [emb] using hxzH
    have hcard := Finset.card_le_card hsub
    have himage :
        ((C.toSimpleGraph.neighborFinset x).image emb).card =
          C.toSimpleGraph.degree x := by
      calc
        ((C.toSimpleGraph.neighborFinset x).image emb).card =
            (C.toSimpleGraph.neighborFinset x).card :=
          Finset.card_image_of_injective _ emb.injective
        _ = C.toSimpleGraph.degree x := rfl
    have hle : C.toSimpleGraph.degree x ≤ H.degree x.1 := by
      simpa [himage] using hcard
    exact hle.trans (hdeg x.1)
  rcases exists_spanning_path_of_connected_degree_le_two
      C.toSimpleGraph
      (_root_.SimpleGraph.ConnectedComponent.connected_toSimpleGraph C)
      hdegC with
    ⟨Psub, hPsub⟩
  let φ : C.toSimpleGraph ↪g H :=
    _root_.SimpleGraph.Embedding.induce C.supp
  let P : GraphPath H := Psub.mapEmbedding φ
  refine ⟨P, ?_⟩
  ext v
  constructor
  · intro hv
    have hvImage : v ∈ Psub.vertexSet.image φ.toEmbedding := by
      simpa [P] using hv
    rcases Finset.mem_image.mp hvImage with ⟨x, _hx, hxv⟩
    subst hxv
    rw [mem_connectedComponentVertexFinset]
    change H.connectedComponentMk x.1 = C
    exact x.2
  · intro hv
    have hvC : v ∈ C.supp :=
      (mem_connectedComponentVertexFinset H C v).1 hv
    have hx : (⟨v, hvC⟩ : C) ∈ Psub.vertexSet := by
      rw [hPsub]
      simp
    have hvImage : v ∈ Psub.vertexSet.image φ.toEmbedding := by
      exact Finset.mem_image.2 ⟨⟨v, hvC⟩, hx, rfl⟩
    simpa [P] using hvImage

omit [DecidableEq V] in
/-- If every connected component has at most `m` vertices, then the whole
finite vertex set has size at most `m` times the number of connected
components. -/
theorem card_le_components_mul_of_component_card_le
    (H : _root_.SimpleGraph V) (m : ℕ)
    (h : ∀ C : H.ConnectedComponent,
      (connectedComponentVertexFinset H C).card ≤ m) :
    Fintype.card V ≤ Fintype.card H.ConnectedComponent * m := by
  classical
  let comps : Finset H.ConnectedComponent := Finset.univ
  have hmaps :
      ((Finset.univ : Finset V) : Set V).MapsTo H.connectedComponentMk comps := by
    intro v _hv
    simp [comps]
  have hcard :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset V)) (t := comps)
      (f := H.connectedComponentMk) hmaps
  have hfiber :
      ∀ C : H.ConnectedComponent,
        ({v ∈ (Finset.univ : Finset V) | H.connectedComponentMk v = C}).card =
          (connectedComponentVertexFinset H C).card := by
    intro C
    have hset :
        {v ∈ (Finset.univ : Finset V) | H.connectedComponentMk v = C} =
          connectedComponentVertexFinset H C := by
      ext v
      simp [connectedComponentVertexFinset,
        _root_.SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hset]
  have hsum_le :
      (∑ C ∈ comps,
        ({v ∈ (Finset.univ : Finset V) | H.connectedComponentMk v = C}).card) ≤
        ∑ _C ∈ comps, m := by
    refine Finset.sum_le_sum ?_
    intro C _hC
    rw [hfiber C]
    exact h C
  have hsum_le' :
      (∑ C ∈ comps,
        ({v ∈ (Finset.univ : Finset V) | H.connectedComponentMk v = C}).card) ≤
        Fintype.card H.ConnectedComponent * m := by
    simpa [comps, Finset.sum_const] using hsum_le
  have huniv_le :
      (Finset.univ : Finset V).card ≤
        Fintype.card H.ConnectedComponent * m := by
    rw [hcard]
    exact hsum_le'
  simpa using huniv_le

/-- A connected component of the degree-two induced subgraph gives a genuine
tree path of the same cardinality, all of whose vertices have tree degree
two. -/
theorem exists_tree_path_of_degreeTwo_component
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    [DecidableRel (degreeTwoInducedGraph T).Adj]
    (C : (degreeTwoInducedGraph T).ConnectedComponent) :
    ∃ P : GraphPath T,
      P.vertexSet.card =
        (connectedComponentVertexFinset (degreeTwoInducedGraph T) C).card ∧
      ∀ v ∈ P.vertexSet, DegreeEquals T v 2 := by
  classical
  let H : _root_.SimpleGraph {v : V // v ∈ treeDegreeTwoVertexSet T} :=
    degreeTwoInducedGraph T
  have hdegH : ∀ x : {v : V // v ∈ treeDegreeTwoVertexSet T},
      H.degree x ≤ 2 := by
    intro x
    simpa [H] using degreeTwoInducedGraph_degree_le_two T x
  rcases exists_path_spanning_connectedComponent_of_degree_le_two
      H hdegH C with
    ⟨PH, hPH⟩
  let φ : H ↪g T :=
    _root_.SimpleGraph.Embedding.induce {v : V | v ∈ treeDegreeTwoVertexSet T}
  let P : GraphPath T := PH.mapEmbedding φ
  refine ⟨P, ?_, ?_⟩
  · calc
      P.vertexSet.card = PH.vertexSet.card := by
        simpa [P] using GraphPath.mapEmbedding_vertexSet_card PH φ
      _ = (connectedComponentVertexFinset H C).card := by
        rw [hPH]
      _ = (connectedComponentVertexFinset (degreeTwoInducedGraph T) C).card := by
        simp [H]
  · intro v hv
    have hvImage : v ∈ PH.vertexSet.image φ.toEmbedding := by
      simpa [P] using hv
    rcases Finset.mem_image.mp hvImage with ⟨x, _hx, hxv⟩
    subst hxv
    have hxdeg : T.degree x.1 = 2 :=
      (mem_treeDegreeTwoVertexSet T x.1).1 x.2
    exact (degreeEquals_iff_degree_eq T x.1 2).2 hxdeg

omit [Fintype V] in
/-- A path found in a spanning subgraph is also a path in the ambient graph,
with the same vertex set.  This is the final conversion needed after the
maximal-spanning-tree argument has identified a long degree-two tree path whose
vertices also have ambient degree two. -/
theorem containsTwoPath_of_subgraph_path
    {G T : _root_.SimpleGraph V} {p : ℕ}
    (hTG : T ≤ G) (P : GraphPath T)
    (hcard : p ≤ P.vertexSet.card)
    (hdeg : ∀ v ∈ P.vertexSet, DegreeEquals G v 2) :
    ContainsTwoPath G p := by
  refine ⟨P.mapLe hTG, ?_, ?_⟩
  · simpa using hcard
  · intro v hv
    exact hdeg v (by simpa using hv)

/-- The local tree-exchange graph obtained by deleting one edge and adding
another.  Appendix A.2 uses two instances of this operation to contradict
leaf-maximality. -/
def edgeSwap (T : _root_.SimpleGraph V) (deleteLeft deleteRight addLeft addRight : V) :
    _root_.SimpleGraph V :=
  T.deleteEdges {s(deleteLeft, deleteRight)} ⊔ _root_.SimpleGraph.edge addLeft addRight

omit [Fintype V] [DecidableEq V] in
/-- If `T` is a subgraph of `G` and the added edge is present in `G`, then the
edge-swap graph is also a subgraph of `G`. -/
theorem edgeSwap_le_of_le_of_adj
    {G T : _root_.SimpleGraph V}
    {deleteLeft deleteRight addLeft addRight : V}
    (hTG : T ≤ G) (hadd : G.Adj addLeft addRight) :
    edgeSwap T deleteLeft deleteRight addLeft addRight ≤ G := by
  classical
  unfold edgeSwap
  refine sup_le ?_ ?_
  · exact (T.deleteEdges_le {s(deleteLeft, deleteRight)}).trans hTG
  · exact (_root_.SimpleGraph.edge_le_iff (G := G)).2 (Or.inr hadd)

omit [Fintype V] in
/-- A general connectedness criterion for an edge swap in a tree.  If after
deleting `x-y`, the new edge `a-b` joins the two components in such a way that
`x` can still reach `a` and `b` can still reach `y`, then every old tree edge
can be simulated in the swapped graph. -/
theorem edgeSwap_connected_of_replacement
    {T : _root_.SimpleGraph V} {x y a b : V}
    (hT : T.IsTree)
    (hxa : (T.deleteEdges {s(x, y)}).Reachable x a)
    (hby : (T.deleteEdges {s(x, y)}).Reachable b y)
    (hab : a ≠ b) :
    (edgeSwap T x y a b).Connected := by
  classical
  let D : _root_.SimpleGraph V := T.deleteEdges {s(x, y)}
  let S : _root_.SimpleGraph V := edgeSwap T x y a b
  have hDS : D ≤ S := by
    dsimp [D, S, edgeSwap]
    exact le_sup_left
  have hS_ab : S.Adj a b := by
    dsimp [S, edgeSwap]
    right
    rw [_root_.SimpleGraph.edge_adj]
    exact ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
  have hxy : S.Reachable x y :=
    (hxa.mono hDS).trans
      ((_root_.SimpleGraph.Adj.reachable hS_ab).trans (hby.mono hDS))
  change S.Connected
  haveI : Nonempty V := hT.connected.nonempty
  refine ⟨?_⟩
  intro u v
  have htransfer :
      ∀ ⦃r s : V⦄, T.Reachable r s → S.Reachable r s := by
    intro r s hrs
    rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at hrs ⊢
    refine Relation.ReflTransGen.trans_induction_on hrs ?hrefl ?hsingle ?htrans
    · intro r
      exact Relation.ReflTransGen.refl
    · intro r s hrs
      have hS_reach : S.Reachable r s := by
        by_cases hdel : s(r, s) = s(x, y)
        · rw [Sym2.eq_iff] at hdel
          rcases hdel with h | h
          · rcases h with ⟨rfl, rfl⟩
            exact hxy
          · rcases h with ⟨rfl, rfl⟩
            exact hxy.symm
        · have hSrs : S.Adj r s := by
            dsimp [S, D, edgeSwap]
            left
            rw [_root_.SimpleGraph.deleteEdges_adj]
            exact ⟨hrs, by simp [hdel]⟩
          exact _root_.SimpleGraph.Adj.reachable hSrs
      exact (_root_.SimpleGraph.reachable_iff_reflTransGen (G := S) r s).1 hS_reach
    · intro r s t _ _ hrs hst
      exact hrs.trans hst
  exact htransfer (hT.connected u v)

omit [Fintype V] [DecidableEq V] in
/-- The acyclicity criterion for an edge swap in a tree.  Once the deleted
edge is removed, adding an edge between two vertices in different components
preserves acyclicity. -/
theorem edgeSwap_acyclic_of_not_reachable
    {T : _root_.SimpleGraph V} {x y a b : V}
    (hT : T.IsTree)
    (hnot : ¬ (T.deleteEdges {s(x, y)}).Reachable a b) :
    (edgeSwap T x y a b).IsAcyclic := by
  classical
  let D : _root_.SimpleGraph V := T.deleteEdges {s(x, y)}
  have hD_acyc : D.IsAcyclic :=
    hT.isAcyclic.anti (T.deleteEdges_le {s(x, y)})
  change (D ⊔ _root_.SimpleGraph.edge a b).IsAcyclic
  exact hD_acyc.sup_edge_of_not_reachable hnot

omit [Fintype V] in
/-- A general tree criterion for an edge swap. -/
theorem edgeSwap_isTree_of_replacement
    {T : _root_.SimpleGraph V} {x y a b : V}
    (hT : T.IsTree)
    (hxa : (T.deleteEdges {s(x, y)}).Reachable x a)
    (hby : (T.deleteEdges {s(x, y)}).Reachable b y)
    (hnot : ¬ (T.deleteEdges {s(x, y)}).Reachable a b) :
    (edgeSwap T x y a b).IsTree := by
  have hab : a ≠ b := by
    intro h
    exact hnot (by simp [h])
  exact
    ⟨edgeSwap_connected_of_replacement hT hxa hby hab,
      edgeSwap_acyclic_of_not_reachable hT hnot⟩

omit [Fintype V] [DecidableEq V] in
/-- In a tree, deleting an edge separates the two sides.  If `a` is reachable
from `x` and `b` from `y` after deleting the tree edge `x-y`, then `a` and `b`
are not reachable after the deletion. -/
theorem delete_tree_edge_not_reachable_of_sides
    {T : _root_.SimpleGraph V} {x y a b : V}
    (hT : T.IsTree) (hxy : T.Adj x y)
    (hax : (T.deleteEdges {s(x, y)}).Reachable a x)
    (hby : (T.deleteEdges {s(x, y)}).Reachable b y) :
    ¬ (T.deleteEdges {s(x, y)}).Reachable a b := by
  let D : _root_.SimpleGraph V := T.deleteEdges {s(x, y)}
  have hxy_bridge : T.IsBridge s(x, y) :=
    (_root_.SimpleGraph.isAcyclic_iff_forall_adj_isBridge (G := T)).1
      hT.isAcyclic hxy
  have hxy_not_reach : ¬ D.Reachable x y := by
    simpa [D] using
      ((_root_.SimpleGraph.isBridge_iff (G := T) (u := x) (v := y)).1
        hxy_bridge).2
  intro hab
  exact hxy_not_reach (hax.symm.trans (hab.trans hby))

omit [Fintype V] [DecidableEq V] in
/-- If every edge of `G` can be replaced by a walk in `H`, then reachability in
`G` implies reachability in `H`. -/
theorem reachable_of_forall_adj_reachable
    {G H : _root_.SimpleGraph V} {x y : V}
    (h : ∀ u v : V, G.Adj u v → H.Reachable u v)
    (hxy : G.Reachable x y) :
    H.Reachable x y := by
  rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at hxy ⊢
  refine Relation.ReflTransGen.trans_induction_on hxy ?hrefl ?hsingle ?htrans
  · intro u
    exact Relation.ReflTransGen.refl
  · intro u v huv
    exact (_root_.SimpleGraph.reachable_iff_reflTransGen (G := H) u v).1
      (h u v huv)
  · intro u v w _ _ huv hvw
    exact huv.trans hvw

/-- A vertex has exactly the two listed neighbors.  This explicit form is often
more convenient than first unpacking `DegreeEquals _ _ 2`. -/
structure HasExactlyTwoNeighbors (G : _root_.SimpleGraph V) (v x y : V) : Prop where
  ne_neighbors : x ≠ y
  adj_left : G.Adj v x
  adj_right : G.Adj v y
  eq_left_or_right : ∀ z : V, G.Adj v z → z = x ∨ z = y

namespace HasExactlyTwoNeighbors

omit [Fintype V] in
theorem degreeEquals {G : _root_.SimpleGraph V} {v x y : V}
    (h : HasExactlyTwoNeighbors G v x y) :
    DegreeEquals G v 2 := by
  classical
  refine ⟨{x, y}, ?_, by simp [h.ne_neighbors]⟩
  intro z
  constructor
  · intro hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h.adj_left
    · have hzy : z = y := by simpa using hz
      simpa [hzy] using h.adj_right
  · intro hz
    rcases h.eq_left_or_right z hz with rfl | rfl
    · simp
    · simp

omit [Fintype V] in
theorem of_degreeEquals_two_of_adj {G : _root_.SimpleGraph V} {v x y : V}
    (hdeg : DegreeEquals G v 2) (hx : G.Adj v x) (hy : G.Adj v y)
    (hxy : x ≠ y) :
    HasExactlyTwoNeighbors G v x y := by
  classical
  refine ⟨hxy, hx, hy, ?_⟩
  intro z hz
  rcases hdeg with ⟨N, hN, hcard⟩
  have hxN : x ∈ N := (hN x).2 hx
  have hyN : y ∈ N := (hN y).2 hy
  have hzN : z ∈ N := (hN z).2 hz
  have hxySet : ({x, y} : Finset V) ⊆ N := by
    intro w hw
    simp at hw
    rcases hw with rfl | rfl
    · exact hxN
    · exact hyN
  have hcardPair : ({x, y} : Finset V).card = 2 := by
    simp [hxy]
  have hpairEq : ({x, y} : Finset V) = N :=
    Finset.eq_of_subset_of_card_le hxySet (by simp [hcardPair, hcard])
  have hzPair : z ∈ ({x, y} : Finset V) := by
    simpa [hpairEq] using hzN
  simpa using hzPair

end HasExactlyTwoNeighbors

omit [Fintype V] in
/-- Deleting one of the two tree-neighbor edges at `b` makes `b` a leaf after
the edge swap, provided the inserted edge is not incident with `b`.  This is
the degree calculation in the first local improvement in Appendix A.2. -/
theorem edgeSwap_degreeEquals_one_delete_right
    {T : _root_.SimpleGraph V} {a b c : V}
    (hb : HasExactlyTwoNeighbors T b a c) :
    DegreeEquals (edgeSwap T b c a c) b 1 := by
  classical
  rcases hb with ⟨hac, hba, hbc, huniq⟩
  have hba_ne : b ≠ a := hba.ne
  have hbc_ne : b ≠ c := hbc.ne
  have hsym_ne : s(b, a) ≠ s(b, c) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hac h.2
    · exact hbc_ne h.1
  refine degreeEquals_one_of_unique_neighbor (v := b) (u := a) ?_ ?_
  · unfold edgeSwap
    left
    exact ⟨hba, by simp [hsym_ne]⟩
  · intro w hbw
    unfold edgeSwap at hbw
    rcases hbw with hbw | hbw
    · rcases hbw with ⟨hTbw, hnot_deleted⟩
      rcases huniq w hTbw with rfl | rfl
      · rfl
      · exfalso
        exact hnot_deleted (by simp [hbc.ne])
    · rw [_root_.SimpleGraph.edge_adj] at hbw
      rcases hbw.1 with h | h
      · exact False.elim (hba_ne h.1)
      · exact False.elim (hbc_ne h.1)

omit [Fintype V] in
/-- Deleting any one incident edge of a degree-two vertex and adding an edge
not incident with that vertex makes it a leaf.  The deleted edge may be given
in either orientation. -/
theorem edgeSwap_degreeEquals_one_delete_adj_of_degree_two
    {T : _root_.SimpleGraph V}
    {deleteLeft deleteRight addLeft addRight v drop : V}
    (hdeg : DegreeEquals T v 2) (hvd : T.Adj v drop)
    (hdel : s(deleteLeft, deleteRight) = s(v, drop))
    (haddLeft : v ≠ addLeft) (haddRight : v ≠ addRight) :
    DegreeEquals (edgeSwap T deleteLeft deleteRight addLeft addRight) v 1 := by
  classical
  rcases hdeg with ⟨N, hN, hcard⟩
  have hdropN : drop ∈ N := (hN drop).2 hvd
  have hcardErase : (N.erase drop).card = 1 := by
    rw [Finset.card_erase_of_mem hdropN]
    omega
  rcases Finset.card_eq_one.mp hcardErase with ⟨keep, hkeep⟩
  have hkeepMemErase : keep ∈ N.erase drop := by
    simp [hkeep]
  have hkeepN : keep ∈ N := Finset.mem_of_mem_erase hkeepMemErase
  have hkeep_ne_drop : keep ≠ drop := by
    exact (Finset.mem_erase.mp hkeepMemErase).1
  have hvkeep : T.Adj v keep := (hN keep).1 hkeepN
  have hsym_keep_drop : s(v, keep) ≠ s(v, drop) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hkeep_ne_drop h.2
    · exact hvd.ne h.1
  have hsym_not_deleted : s(v, keep) ≠ s(deleteLeft, deleteRight) := by
    intro h
    exact hsym_keep_drop (h.trans hdel)
  refine degreeEquals_one_of_unique_neighbor (v := v) (u := keep) ?_ ?_
  · unfold edgeSwap
    left
    exact ⟨hvkeep, by simp [hsym_not_deleted]⟩
  · intro w hvw
    unfold edgeSwap at hvw
    rcases hvw with hvw | hvw
    · rw [_root_.SimpleGraph.deleteEdges_adj] at hvw
      rcases hvw with ⟨hTvw, hnot_deleted⟩
      have hwN : w ∈ N := (hN w).2 hTvw
      have hw_ne_drop : w ≠ drop := by
        intro hwd
        have hpair : s(v, w) = s(deleteLeft, deleteRight) := by
          simp [hwd, hdel]
        exact hnot_deleted (by simp [hpair])
      have hwErase : w ∈ N.erase drop := Finset.mem_erase.2 ⟨hw_ne_drop, hwN⟩
      simpa [hkeep] using hwErase
    · rw [_root_.SimpleGraph.edge_adj] at hvw
      rcases hvw.1 with h | h
      · exact False.elim (haddLeft h.1)
      · exact False.elim (haddRight h.1)

omit [Fintype V] in
/-- A leaf not incident with either the deleted edge or the inserted edge
remains a leaf after an edge swap. -/
theorem edgeSwap_preserves_leaf_of_not_incident
    {T : _root_.SimpleGraph V}
    {deleteLeft deleteRight addLeft addRight v : V}
    (hleaf : DegreeEquals T v 1)
    (hv_deleteLeft : v ≠ deleteLeft) (hv_deleteRight : v ≠ deleteRight)
    (hv_addLeft : v ≠ addLeft) (hv_addRight : v ≠ addRight) :
    DegreeEquals (edgeSwap T deleteLeft deleteRight addLeft addRight) v 1 := by
  classical
  rcases hleaf with ⟨N, hN, hcard⟩
  rcases Finset.card_eq_one.mp hcard with ⟨u, hN_eq⟩
  have huN : u ∈ N := by simp [hN_eq]
  have hvu : T.Adj v u := (hN u).1 huN
  have hdeleted_ne : s(v, u) ≠ s(deleteLeft, deleteRight) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hv_deleteLeft h.1
    · exact hv_deleteRight h.1
  refine degreeEquals_one_of_unique_neighbor (v := v) (u := u) ?_ ?_
  · unfold edgeSwap
    left
    exact ⟨hvu, by simp [hdeleted_ne]⟩
  · intro w hvw
    unfold edgeSwap at hvw
    rcases hvw with hvw | hvw
    · exact DegreeEquals.one_adj_eq ⟨N, hN, hcard⟩ hvw.1 hvu
    · rw [_root_.SimpleGraph.edge_adj] at hvw
      rcases hvw.1 with h | h
      · exact False.elim (hv_addLeft h.1)
      · exact False.elim (hv_addRight h.1)

omit [Fintype V] in
/-- The first shortcut exchange preserves connectedness of the tree: the
removed edge `b-c` is replaced by the route `b-a-c`. -/
theorem edgeSwap_connected_firstShortcut
    {T : _root_.SimpleGraph V} {a b c : V}
    (hT : T.IsTree) (hb : HasExactlyTwoNeighbors T b a c) :
    (edgeSwap T b c a c).Connected := by
  classical
  let S : _root_.SimpleGraph V := edgeSwap T b c a c
  rcases hb with ⟨hac, hba, hbc, huniq⟩
  have hba_ne : b ≠ a := hba.ne
  have hbc_ne : b ≠ c := hbc.ne
  have hsym_ne : s(b, a) ≠ s(b, c) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hac h.2
    · exact hbc_ne h.1
  have hS_ba : S.Adj b a := by
    dsimp [S, edgeSwap]
    left
    exact ⟨hba, by simp [hsym_ne]⟩
  have hS_ac : S.Adj a c := by
    dsimp [S, edgeSwap]
    right
    rw [_root_.SimpleGraph.edge_adj]
    exact ⟨Or.inl ⟨rfl, rfl⟩, hac⟩
  have hS_bc : S.Reachable b c :=
    (_root_.SimpleGraph.Adj.reachable hS_ba).trans
      (_root_.SimpleGraph.Adj.reachable hS_ac)
  change S.Connected
  haveI : Nonempty V := hT.connected.nonempty
  refine ⟨?_⟩
  intro x y
  refine reachable_of_forall_adj_reachable (G := T) (H := S) ?_ (hT.connected x y)
  intro u v huv
  by_cases hdel : s(u, v) = s(b, c)
  · rw [Sym2.eq_iff] at hdel
    rcases hdel with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hS_bc
    · rcases h with ⟨rfl, rfl⟩
      exact hS_bc.symm
  · have hSuv : S.Adj u v := by
      dsimp [S, edgeSwap]
      left
      rw [_root_.SimpleGraph.deleteEdges_adj]
      exact ⟨huv, by simp [hdel]⟩
    exact _root_.SimpleGraph.Adj.reachable hSuv

omit [Fintype V] [DecidableEq V] in
/-- The first shortcut exchange preserves acyclicity.  In a tree every edge is
a bridge; after deleting `b-c`, the retained edge `b-a` puts `a` on the `b`
side, so `a` and `c` are not reachable before the new edge is inserted. -/
theorem edgeSwap_acyclic_firstShortcut
    {T : _root_.SimpleGraph V} {a b c : V}
    (hT : T.IsTree) (hb : HasExactlyTwoNeighbors T b a c) :
    (edgeSwap T b c a c).IsAcyclic := by
  classical
  let D : _root_.SimpleGraph V := T.deleteEdges {s(b, c)}
  rcases hb with ⟨hac, hba, hbc, huniq⟩
  have hbc_bridge : T.IsBridge s(b, c) :=
    (_root_.SimpleGraph.isAcyclic_iff_forall_adj_isBridge (G := T)).1
      hT.isAcyclic hbc
  have hbc_not_reach : ¬ D.Reachable b c := by
    simpa [D] using
      ((_root_.SimpleGraph.isBridge_iff (G := T) (u := b) (v := c)).1
        hbc_bridge).2
  have hsym_ne : s(b, a) ≠ s(b, c) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hac h.2
    · exact hbc.ne h.1
  have hba_D : D.Adj b a := by
    dsimp [D]
    exact ⟨hba, by simp [hsym_ne]⟩
  have hac_not_reach : ¬ D.Reachable a c := by
    intro hac_reach
    exact hbc_not_reach
      ((_root_.SimpleGraph.Adj.reachable hba_D).trans hac_reach)
  have hD_acyc : D.IsAcyclic :=
    hT.isAcyclic.anti (T.deleteEdges_le {s(b, c)})
  change (D ⊔ _root_.SimpleGraph.edge a c).IsAcyclic
  exact hD_acyc.sup_edge_of_not_reachable hac_not_reach

omit [Fintype V] in
/-- The first shortcut exchange is again a tree. -/
theorem edgeSwap_isTree_firstShortcut
    {T : _root_.SimpleGraph V} {a b c : V}
    (hT : T.IsTree) (hb : HasExactlyTwoNeighbors T b a c) :
    (edgeSwap T b c a c).IsTree where
  connected := edgeSwap_connected_firstShortcut hT hb
  isAcyclic := edgeSwap_acyclic_firstShortcut hT hb

/-- If the three vertices touched by the first shortcut exchange are not old
leaves, then every old leaf remains a leaf. -/
theorem leafSet_subset_edgeSwap_firstShortcut
    {T : _root_.SimpleGraph V} {a b c : V}
    (ha : ¬ DegreeEquals T a 1)
    (hb : ¬ DegreeEquals T b 1)
    (hc : ¬ DegreeEquals T c 1) :
    leafSet T ⊆ leafSet (edgeSwap T b c a c) := by
  classical
  intro v hv
  have hvleaf : DegreeEquals T v 1 := (mem_leafSet T v).1 hv
  have hva : v ≠ a := by
    intro h
    exact ha (by simpa [h] using hvleaf)
  have hvb : v ≠ b := by
    intro h
    exact hb (by simpa [h] using hvleaf)
  have hvc : v ≠ c := by
    intro h
    exact hc (by simpa [h] using hvleaf)
  exact (mem_leafSet (edgeSwap T b c a c) v).2 <|
    edgeSwap_preserves_leaf_of_not_incident hvleaf hvb hvc hva hvc

omit [Fintype V] in
/-- Degree two vertices are not leaves. -/
theorem not_degreeEquals_one_of_hasExactlyTwoNeighbors
    {G : _root_.SimpleGraph V} {v x y : V}
    (h : HasExactlyTwoNeighbors G v x y) :
    ¬ DegreeEquals G v 1 := by
  intro hleaf
  exact h.ne_neighbors <|
    DegreeEquals.one_adj_eq hleaf h.adj_left h.adj_right

omit [Fintype V] [DecidableEq V] in
/-- A degree-two vertex is not a leaf, stated directly for the finset-degree
definition. -/
theorem not_degreeEquals_one_of_degreeEquals_two
    {G : _root_.SimpleGraph V} {v : V}
    (h : DegreeEquals G v 2) :
    ¬ DegreeEquals G v 1 := by
  intro hleaf
  rcases h with ⟨N, hN, hNcard⟩
  rcases hleaf with ⟨M, hM, hMcard⟩
  have hNM : N = M := by
    ext u
    exact (hN u).trans ((hM u).symm)
  have hcardEq : N.card = M.card := congrArg Finset.card hNM
  omega

omit [DecidableEq V] in
/-- If the leaf set of one graph is a proper subset of the leaf set of another,
then its leaf count is strictly smaller. -/
theorem leafCount_lt_of_leafSet_subset_of_new_leaf
    {T S : _root_.SimpleGraph V} {v : V}
    (hsub : leafSet T ⊆ leafSet S)
    (hvS : v ∈ leafSet S) (hvT : v ∉ leafSet T) :
    leafCount T < leafCount S := by
  classical
  have hssub : leafSet T ⊂ leafSet S := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨v, hvS, hvT⟩
  exact Finset.card_lt_card hssub

/-- If all old leaves except possibly `lost` remain leaves, and two distinct
non-leaves become leaves, then the number of leaves strictly increases. -/
theorem leafCount_lt_of_preserve_except_and_two_new
    {T S : _root_.SimpleGraph V} {new₁ new₂ lost : V}
    (hpres :
      ∀ v : V, v ∈ leafSet T → v ≠ lost → v ∈ leafSet S)
    (hnew₁S : new₁ ∈ leafSet S) (hnew₂S : new₂ ∈ leafSet S)
    (hnew₁T : new₁ ∉ leafSet T) (hnew₂T : new₂ ∉ leafSet T)
    (hnew_ne : new₁ ≠ new₂) :
    leafCount T < leafCount S := by
  classical
  let A : Finset V := leafSet T
  let B : Finset V := leafSet S
  by_cases hlostA : lost ∈ A
  · let C : Finset V := insert new₁ (insert new₂ (A.erase lost))
    have hCsub : C ⊆ B := by
      intro v hv
      simp [C] at hv
      rcases hv with rfl | rfl | hv
      · simpa [B] using hnew₁S
      · simpa [B] using hnew₂S
      · rcases hv with ⟨hv_ne_lost, hvA⟩
        exact hpres v (by simpa [A] using hvA) hv_ne_lost
    have hnew₂_not_erase : new₂ ∉ A.erase lost := by
      intro h
      exact hnew₂T (by simpa [A] using Finset.mem_of_mem_erase h)
    have hnew₁_not_erase : new₁ ∉ A.erase lost := by
      intro h
      exact hnew₁T (by simpa [A] using Finset.mem_of_mem_erase h)
    have hnew₁_not_insert : new₁ ∉ insert new₂ (A.erase lost) := by
      simp [hnew_ne, hnew₁_not_erase]
    have hcardEraseAdd : (A.erase lost).card + 1 = A.card :=
      Finset.card_erase_add_one hlostA
    have hcardInsert₂ :
        (insert new₂ (A.erase lost)).card = (A.erase lost).card + 1 :=
      Finset.card_insert_of_notMem hnew₂_not_erase
    have hcardC : C.card = A.card + 1 := by
      calc
        C.card = (insert new₂ (A.erase lost)).card + 1 :=
          Finset.card_insert_of_notMem hnew₁_not_insert
        _ = (A.erase lost).card + 1 + 1 := by rw [hcardInsert₂]
        _ = A.card + 1 := by omega
    have hle : C.card ≤ B.card := Finset.card_le_card hCsub
    have hlt : A.card < B.card := by omega
    simpa [leafCount, A, B] using hlt
  · have hsub : leafSet T ⊆ leafSet S := by
      intro v hv
      exact hpres v hv (by
        intro hv_lost
        exact hlostA (by simpa [A, hv_lost] using hv))
    exact leafCount_lt_of_leafSet_subset_of_new_leaf hsub hnew₁S hnew₁T

/-- The leaf-count core of the second improvement step.  Deleting a tree edge
whose endpoints both have degree two makes both endpoints leaves.  If the
inserted edge is incident with a non-leaf `addLeft`, then at worst the other
inserted endpoint `addRight` was an old leaf, so the leaf count increases. -/
theorem leafCount_lt_edgeSwap_delete_between_degree_two
    {T : _root_.SimpleGraph V} {x y addLeft addRight : V}
    (hxdeg : DegreeEquals T x 2) (hydeg : DegreeEquals T y 2)
    (hxy : T.Adj x y)
    (hx_addLeft : x ≠ addLeft) (hx_addRight : x ≠ addRight)
    (hy_addLeft : y ≠ addLeft) (hy_addRight : y ≠ addRight)
    (haddLeft_not_leaf : ¬ DegreeEquals T addLeft 1) :
    leafCount T < leafCount (edgeSwap T x y addLeft addRight) := by
  classical
  let S : _root_.SimpleGraph V := edgeSwap T x y addLeft addRight
  have hx_new : x ∈ leafSet S := by
    exact (mem_leafSet S x).2 <|
      edgeSwap_degreeEquals_one_delete_adj_of_degree_two
        (T := T) (deleteLeft := x) (deleteRight := y)
        (addLeft := addLeft) (addRight := addRight)
        (v := x) (drop := y) hxdeg hxy rfl hx_addLeft hx_addRight
  have hy_new : y ∈ leafSet S := by
    exact (mem_leafSet S y).2 <|
      edgeSwap_degreeEquals_one_delete_adj_of_degree_two
        (T := T) (deleteLeft := x) (deleteRight := y)
        (addLeft := addLeft) (addRight := addRight)
        (v := y) (drop := x) hydeg hxy.symm
        (by exact Sym2.eq_swap) hy_addLeft hy_addRight
  have hx_old : x ∉ leafSet T := by
    intro hxleaf
    exact not_degreeEquals_one_of_degreeEquals_two hxdeg
      ((mem_leafSet T x).1 hxleaf)
  have hy_old : y ∉ leafSet T := by
    intro hyleaf
    exact not_degreeEquals_one_of_degreeEquals_two hydeg
      ((mem_leafSet T y).1 hyleaf)
  have hpres :
      ∀ v : V, v ∈ leafSet T → v ≠ addRight → v ∈ leafSet S := by
    intro v hvleaf hv_ne_addRight
    have hvdeg : DegreeEquals T v 1 := (mem_leafSet T v).1 hvleaf
    have hv_ne_x : v ≠ x := by
      intro h
      exact not_degreeEquals_one_of_degreeEquals_two hxdeg (by simpa [h] using hvdeg)
    have hv_ne_y : v ≠ y := by
      intro h
      exact not_degreeEquals_one_of_degreeEquals_two hydeg (by simpa [h] using hvdeg)
    have hv_ne_addLeft : v ≠ addLeft := by
      intro h
      exact haddLeft_not_leaf (by simpa [h] using hvdeg)
    exact (mem_leafSet S v).2 <|
      edgeSwap_preserves_leaf_of_not_incident hvdeg
        hv_ne_x hv_ne_y hv_ne_addLeft hv_ne_addRight
  exact leafCount_lt_of_preserve_except_and_two_new
    (T := T) (S := S) (new₁ := x) (new₂ := y) (lost := addRight)
    hpres hx_new hy_new hx_old hy_old hxy.ne

/-- The leaf-count part of the first shortcut improvement: under the local
degree-two configuration, the edge swap creates a new leaf and preserves all
old leaves. -/
theorem leafCount_lt_edgeSwap_firstShortcut
    {T : _root_.SimpleGraph V} {a b c : V}
    (ha : DegreeEquals T a 2)
    (hb : HasExactlyTwoNeighbors T b a c)
    (hc : DegreeEquals T c 2) :
    leafCount T < leafCount (edgeSwap T b c a c) := by
  classical
  have ha_not : ¬ DegreeEquals T a 1 :=
    not_degreeEquals_one_of_degreeEquals_two ha
  have hb_not : ¬ DegreeEquals T b 1 :=
    not_degreeEquals_one_of_hasExactlyTwoNeighbors hb
  have hc_not : ¬ DegreeEquals T c 1 :=
    not_degreeEquals_one_of_degreeEquals_two hc
  have hsub :
      leafSet T ⊆ leafSet (edgeSwap T b c a c) :=
    leafSet_subset_edgeSwap_firstShortcut ha_not hb_not hc_not
  have hb_new : b ∈ leafSet (edgeSwap T b c a c) :=
    (mem_leafSet (edgeSwap T b c a c) b).2
      (edgeSwap_degreeEquals_one_delete_right hb)
  have hb_old : b ∉ leafSet T := by
    intro hb_leaf
    exact hb_not ((mem_leafSet T b).1 hb_leaf)
  exact leafCount_lt_of_leafSet_subset_of_new_leaf hsub hb_new hb_old

omit [Fintype V] in
/-- The tree part of the second shortcut when the new edge reconnects the
component above `v`.  The hypotheses `hu_side` and `hnot` record exactly that,
after deleting `v₁-v₂`, the endpoint `u` is on the `v₂` side while `v` is on
the other side. -/
theorem edgeSwap_isTree_secondShortcut_delete_parent
    {T : _root_.SimpleGraph V} {v₂ v₁ v u : V}
    (hT : T.IsTree)
    (hv₁ : HasExactlyTwoNeighbors T v₁ v₂ v)
    (hu_side : (T.deleteEdges {s(v₁, v₂)}).Reachable u v₂)
    (hnot : ¬ (T.deleteEdges {s(v₁, v₂)}).Reachable v u) :
    (edgeSwap T v₁ v₂ v u).IsTree := by
  classical
  have hv₁v_not_deleted : s(v₁, v) ≠ s(v₁, v₂) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hv₁.ne_neighbors.symm h.2
    · exact hv₁.adj_left.ne h.1
  have hv₁v_D : (T.deleteEdges {s(v₁, v₂)}).Adj v₁ v := by
    rw [_root_.SimpleGraph.deleteEdges_adj]
    exact ⟨hv₁.adj_right, by simp [hv₁v_not_deleted]⟩
  exact edgeSwap_isTree_of_replacement
    (T := T) (x := v₁) (y := v₂) (a := v) (b := u)
    hT (_root_.SimpleGraph.Adj.reachable hv₁v_D) hu_side hnot

omit [Fintype V] in
/-- The tree part of the second shortcut when the new edge reconnects the
component below `v`. -/
theorem edgeSwap_isTree_secondShortcut_delete_child
    {T : _root_.SimpleGraph V} {v v₁' v₂' u : V}
    (hT : T.IsTree)
    (hv₁' : HasExactlyTwoNeighbors T v₁' v v₂')
    (hu_side : (T.deleteEdges {s(v₁', v₂')}).Reachable u v₂')
    (hnot : ¬ (T.deleteEdges {s(v₁', v₂')}).Reachable v u) :
    (edgeSwap T v₁' v₂' v u).IsTree := by
  classical
  have hv₁v_not_deleted : s(v₁', v) ≠ s(v₁', v₂') := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact hv₁'.ne_neighbors h.2
    · exact hv₁'.adj_right.ne h.1
  have hv₁v_D : (T.deleteEdges {s(v₁', v₂')}).Adj v₁' v := by
    rw [_root_.SimpleGraph.deleteEdges_adj]
    exact ⟨hv₁'.adj_left, by simp [hv₁v_not_deleted]⟩
  exact edgeSwap_isTree_of_replacement
    (T := T) (x := v₁') (y := v₂') (a := v) (b := u)
    hT (_root_.SimpleGraph.Adj.reachable hv₁v_D) hu_side hnot

/-- A spanning tree with sufficiently many leaves gives the structural
`HasSpanningTreeWithAtLeastLeaves` certificate. -/
theorem hasSpanningTreeWithAtLeastLeaves_of_leafCount
    {G T : _root_.SimpleGraph V} {L : ℕ}
    (hTG : T ≤ G) (hT : T.IsTree) (hL : L ≤ leafCount T) :
    HasSpanningTreeWithAtLeastLeaves G L := by
  refine ⟨T, hTG, hT, leafSet T, ?_, hL⟩
  intro v
  exact mem_leafSet T v

/-- The finite set of all spanning trees of `G`, represented as same-vertex
subgraphs. -/
noncomputable def spanningTreeSet (G : _root_.SimpleGraph V) :
    Finset (_root_.SimpleGraph V) := by
  classical
  exact Finset.univ.filter fun T : _root_.SimpleGraph V => T ≤ G ∧ T.IsTree

@[simp] theorem mem_spanningTreeSet (G T : _root_.SimpleGraph V) :
    T ∈ spanningTreeSet G ↔ T ≤ G ∧ T.IsTree := by
  classical
  simp [spanningTreeSet]

/-- A connected graph has at least one spanning tree in `spanningTreeSet`. -/
theorem spanningTreeSet_nonempty {G : _root_.SimpleGraph V}
    (hG : G.Connected) : (spanningTreeSet G).Nonempty := by
  classical
  rcases hG.exists_isTree_le with ⟨T, hTG, hT⟩
  exact ⟨T, by simp [hTG, hT]⟩

/-- A spanning tree of `G` with maximum possible leaf count. -/
noncomputable def maxLeafSpanningTree (G : _root_.SimpleGraph V)
    (hG : G.Connected) : _root_.SimpleGraph V :=
  Classical.choose
    (Finset.exists_max_image (spanningTreeSet G) leafCount
      (spanningTreeSet_nonempty hG))

/-- The chosen maximum-leaf spanning tree belongs to `spanningTreeSet`. -/
theorem maxLeafSpanningTree_mem {G : _root_.SimpleGraph V}
    (hG : G.Connected) :
    maxLeafSpanningTree G hG ∈ spanningTreeSet G :=
  (Classical.choose_spec
    (Finset.exists_max_image (spanningTreeSet G) leafCount
      (spanningTreeSet_nonempty hG))).1

/-- The chosen maximum-leaf spanning tree is a subgraph of `G`. -/
theorem maxLeafSpanningTree_le {G : _root_.SimpleGraph V}
  (hG : G.Connected) :
    maxLeafSpanningTree G hG ≤ G :=
  ((mem_spanningTreeSet G (maxLeafSpanningTree G hG)).1
    (maxLeafSpanningTree_mem hG)).1

/-- The chosen maximum-leaf spanning tree is a tree. -/
theorem maxLeafSpanningTree_isTree {G : _root_.SimpleGraph V}
    (hG : G.Connected) :
    (maxLeafSpanningTree G hG).IsTree :=
  (mem_spanningTreeSet G (maxLeafSpanningTree G hG)).1
    (maxLeafSpanningTree_mem hG) |>.2

/-- The chosen spanning tree has at least as many leaves as any other spanning
tree of `G`. -/
theorem leafCount_le_maxLeafSpanningTree {G T : _root_.SimpleGraph V}
    (hG : G.Connected) (hT : T ≤ G ∧ T.IsTree) :
    leafCount T ≤ leafCount (maxLeafSpanningTree G hG) := by
  exact
    (Classical.choose_spec
      (Finset.exists_max_image (spanningTreeSet G) leafCount
        (spanningTreeSet_nonempty hG))).2 T
      ((mem_spanningTreeSet G T).2 hT)

/-- A spanning tree that is optimal for the number of leaves.  The paper
chooses such a tree before applying the local exchange argument. -/
def IsLeafMaximalSpanningTree
    (G T : _root_.SimpleGraph V) : Prop :=
  T ≤ G ∧ T.IsTree ∧
    ∀ T' : _root_.SimpleGraph V, T' ≤ G → T'.IsTree →
      leafCount T' ≤ leafCount T

theorem maxLeafSpanningTree_isLeafMaximal
    {G : _root_.SimpleGraph V} (hG : G.Connected) :
    IsLeafMaximalSpanningTree G (maxLeafSpanningTree G hG) := by
  refine ⟨maxLeafSpanningTree_le hG, maxLeafSpanningTree_isTree hG, ?_⟩
  intro T' hT'G hT'
  exact leafCount_le_maxLeafSpanningTree hG ⟨hT'G, hT'⟩

omit [DecidableEq V] in
theorem IsLeafMaximalSpanningTree.no_better_tree
    {G T T' : _root_.SimpleGraph V}
    (hT : IsLeafMaximalSpanningTree G T)
    (hT'G : T' ≤ G) (hT' : T'.IsTree) :
    leafCount T' ≤ leafCount T :=
  hT.2.2 T' hT'G hT'

/-- Leaf-maximality rules out the second shortcut in the case where the edge
`v-u` reconnects to the component above `v`. -/
theorem IsLeafMaximalSpanningTree.not_secondShortcut_delete_parent
    {G T : _root_.SimpleGraph V} {v₂ v₁ v u : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (hv₂ : DegreeEquals T v₂ 2)
    (hv₁ : HasExactlyTwoNeighbors T v₁ v₂ v)
    (hv : DegreeEquals T v 2)
    (hadd : G.Adj v u)
    (hu_ne_v₁ : u ≠ v₁) (hu_ne_v₂ : u ≠ v₂)
    (hu_side : (T.deleteEdges {s(v₁, v₂)}).Reachable u v₂)
    (hnot : ¬ (T.deleteEdges {s(v₁, v₂)}).Reachable v u) :
    False := by
  have hswapTree :
      (edgeSwap T v₁ v₂ v u).IsTree :=
    edgeSwap_isTree_secondShortcut_delete_parent hT.2.1 hv₁ hu_side hnot
  have hle :=
    hT.no_better_tree
      (edgeSwap_le_of_le_of_adj hT.1 hadd) hswapTree
  have hlt :
      leafCount T < leafCount (edgeSwap T v₁ v₂ v u) := by
    exact leafCount_lt_edgeSwap_delete_between_degree_two
      (x := v₁) (y := v₂) (addLeft := v) (addRight := u)
      (HasExactlyTwoNeighbors.degreeEquals hv₁) hv₂ hv₁.adj_left
      hv₁.adj_right.ne hu_ne_v₁.symm hv₁.ne_neighbors hu_ne_v₂.symm
      (not_degreeEquals_one_of_degreeEquals_two hv)
  exact (not_lt_of_ge hle) hlt

/-- Leaf-maximality rules out the second shortcut in the case where the edge
`v-u` reconnects to the component below `v`. -/
theorem IsLeafMaximalSpanningTree.not_secondShortcut_delete_child
    {G T : _root_.SimpleGraph V} {v v₁' v₂' u : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (hv : DegreeEquals T v 2)
    (hv₁' : HasExactlyTwoNeighbors T v₁' v v₂')
    (hv₂' : DegreeEquals T v₂' 2)
    (hadd : G.Adj v u)
    (hu_ne_v₁' : u ≠ v₁') (hu_ne_v₂' : u ≠ v₂')
    (hu_side : (T.deleteEdges {s(v₁', v₂')}).Reachable u v₂')
    (hnot : ¬ (T.deleteEdges {s(v₁', v₂')}).Reachable v u) :
    False := by
  have hswapTree :
      (edgeSwap T v₁' v₂' v u).IsTree :=
    edgeSwap_isTree_secondShortcut_delete_child hT.2.1 hv₁' hu_side hnot
  have hle :=
    hT.no_better_tree
      (edgeSwap_le_of_le_of_adj hT.1 hadd) hswapTree
  have hlt :
      leafCount T < leafCount (edgeSwap T v₁' v₂' v u) := by
    exact leafCount_lt_edgeSwap_delete_between_degree_two
      (x := v₁') (y := v₂') (addLeft := v) (addRight := u)
      (HasExactlyTwoNeighbors.degreeEquals hv₁') hv₂' hv₁'.adj_right
      hv₁'.adj_left.ne hu_ne_v₁'.symm hv₁'.ne_neighbors.symm hu_ne_v₂'.symm
      (not_degreeEquals_one_of_degreeEquals_two hv)
  exact (not_lt_of_ge hle) hlt

/-- The second shortcut, stated in the paper's degree-two path language for the
case where deleting the parent edge reconnects the upper component. -/
theorem IsLeafMaximalSpanningTree.not_secondShortcut_delete_parent_of_degreeTwo_path
    {G T : _root_.SimpleGraph V} {v₂ v₁ v u : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (hv₂ : DegreeEquals T v₂ 2)
    (hv₁ : DegreeEquals T v₁ 2)
    (hv : DegreeEquals T v 2)
    (hv₁v₂ : T.Adj v₁ v₂)
    (hv₁v : T.Adj v₁ v)
    (hv₂_ne_v : v₂ ≠ v)
    (hadd : G.Adj v u)
    (hu_ne_v₁ : u ≠ v₁)
    (hu_ne_v₂ : u ≠ v₂)
    (hu_side : (T.deleteEdges {s(v₁, v₂)}).Reachable u v₂)
    (hnot : ¬ (T.deleteEdges {s(v₁, v₂)}).Reachable v u) :
    False := by
  have hv₁_exact : HasExactlyTwoNeighbors T v₁ v₂ v :=
    HasExactlyTwoNeighbors.of_degreeEquals_two_of_adj hv₁ hv₁v₂ hv₁v hv₂_ne_v
  exact hT.not_secondShortcut_delete_parent
    hv₂ hv₁_exact hv hadd hu_ne_v₁ hu_ne_v₂ hu_side hnot

/-- The second shortcut, stated in the paper's degree-two path language for the
case where deleting the child edge reconnects the lower component. -/
theorem IsLeafMaximalSpanningTree.not_secondShortcut_delete_child_of_degreeTwo_path
    {G T : _root_.SimpleGraph V} {v v₁' v₂' u : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (hv : DegreeEquals T v 2)
    (hv₁' : DegreeEquals T v₁' 2)
    (hv₂' : DegreeEquals T v₂' 2)
    (hv₁'v : T.Adj v₁' v)
    (hv₁'v₂' : T.Adj v₁' v₂')
    (hv_ne_v₂' : v ≠ v₂')
    (hadd : G.Adj v u)
    (hu_ne_v₁' : u ≠ v₁')
    (hu_ne_v₂' : u ≠ v₂')
    (hu_side : (T.deleteEdges {s(v₁', v₂')}).Reachable u v₂')
    (hnot : ¬ (T.deleteEdges {s(v₁', v₂')}).Reachable v u) :
    False := by
  have hv₁'_exact : HasExactlyTwoNeighbors T v₁' v v₂' :=
    HasExactlyTwoNeighbors.of_degreeEquals_two_of_adj
      hv₁' hv₁'v hv₁'v₂' hv_ne_v₂'
  exact hT.not_secondShortcut_delete_child
    hv hv₁'_exact hv₂' hadd hu_ne_v₁' hu_ne_v₂' hu_side hnot

/-- A leaf-maximal spanning tree cannot contain the first shortcut exchange once
the exchanged graph is known to still be a spanning tree.  The remaining
tree-specific work in Appendix A.2 is to prove `hSwapTree` from the rooted-tree
configuration. -/
theorem IsLeafMaximalSpanningTree.not_firstShortcut
    {G T : _root_.SimpleGraph V} {a b c : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (ha : DegreeEquals T a 2)
    (hb : HasExactlyTwoNeighbors T b a c)
    (hc : DegreeEquals T c 2)
    (hadd : G.Adj a c)
    (hSwapTree : (edgeSwap T b c a c).IsTree) :
    False := by
  have hle :=
    hT.no_better_tree
      (edgeSwap_le_of_le_of_adj hT.1 hadd) hSwapTree
  have hlt := leafCount_lt_edgeSwap_firstShortcut ha hb hc
  exact (not_lt_of_ge hle) hlt

/-- Fully discharged first local improvement: a leaf-maximal spanning tree
cannot contain the shortcut configuration from Appendix A.2. -/
theorem IsLeafMaximalSpanningTree.not_firstShortcut_of_adj
    {G T : _root_.SimpleGraph V} {a b c : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (ha : DegreeEquals T a 2)
    (hb : HasExactlyTwoNeighbors T b a c)
    (hc : DegreeEquals T c 2)
    (hadd : G.Adj a c) :
    False :=
  hT.not_firstShortcut ha hb hc hadd
    (edgeSwap_isTree_firstShortcut hT.2.1 hb)

/-- The paper's first improvement step in its natural path form: if
`a-b-c` is a tree path of degree-two vertices and `a-c` is an ambient edge,
then a leaf-maximal spanning tree is contradicted. -/
theorem IsLeafMaximalSpanningTree.not_firstShortcut_of_degreeTwo_path
    {G T : _root_.SimpleGraph V} {a b c : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (ha : DegreeEquals T a 2) (hb : DegreeEquals T b 2)
    (hc : DegreeEquals T c 2)
    (hba : T.Adj b a) (hbc : T.Adj b c) (hac : a ≠ c)
    (hadd : G.Adj a c) :
    False := by
  have hb_exact : HasExactlyTwoNeighbors T b a c :=
    HasExactlyTwoNeighbors.of_degreeEquals_two_of_adj hb hba hbc hac
  exact hT.not_firstShortcut_of_adj ha hb_exact hc hadd

omit [Fintype V] in
/-- In a tree, a vertex outside the five displayed vertices of a degree-two
path `v₂-v₁-v-v₁'-v₂'` lies on one of the two outer sides relative to `v`.

This is the rooted-tree case distinction used implicitly in Appendix A.2:
the unique tree path from `u` to `v` enters `v` through either `v₁` or `v₁'`;
one more step along that path must then be through `v₂` or `v₂'`, respectively,
because `v₁` and `v₁'` have tree degree two. -/
theorem tree_five_path_side_dichotomy
    {T : _root_.SimpleGraph V} {v₂ v₁ v v₁' v₂' u : V}
    (hT : T.IsTree)
    (hv₁ : DegreeEquals T v₁ 2)
    (hv : DegreeEquals T v 2)
    (hv₁' : DegreeEquals T v₁' 2)
    (hv₁v₂ : T.Adj v₁ v₂)
    (hv₁v : T.Adj v₁ v)
    (hv₁'v : T.Adj v₁' v)
    (hv₁'v₂' : T.Adj v₁' v₂')
    (hv₁_ne_v₁' : v₁ ≠ v₁')
    (hv₂_ne_v : v₂ ≠ v)
    (hv_ne_v₂' : v ≠ v₂')
    (hu_ne_v : u ≠ v)
    (hu_ne_v₁ : u ≠ v₁)
    (hu_ne_v₁' : u ≠ v₁') :
    ((T.deleteEdges {s(v₁, v₂)}).Reachable u v₂ ∧
      ¬ (T.deleteEdges {s(v₁, v₂)}).Reachable v u) ∨
    ((T.deleteEdges {s(v₁', v₂')}).Reachable u v₂' ∧
      ¬ (T.deleteEdges {s(v₁', v₂')}).Reachable v u) := by
  classical
  have hv_exact : HasExactlyTwoNeighbors T v v₁ v₁' :=
    HasExactlyTwoNeighbors.of_degreeEquals_two_of_adj
      hv hv₁v.symm hv₁'v.symm hv₁_ne_v₁'
  have hv₁_exact : HasExactlyTwoNeighbors T v₁ v₂ v :=
    HasExactlyTwoNeighbors.of_degreeEquals_two_of_adj
      hv₁ hv₁v₂ hv₁v hv₂_ne_v
  have hv₁'_exact : HasExactlyTwoNeighbors T v₁' v v₂' :=
    HasExactlyTwoNeighbors.of_degreeEquals_two_of_adj
      hv₁' hv₁'v hv₁'v₂' hv_ne_v₂'
  rcases hT.connected.exists_isPath u v with ⟨W, hW⟩
  let P : GraphPath T :=
    { source := u, target := v, walk := W, isPath := hW }
  have hPne : P.source ≠ P.target := by
    simpa [P] using hu_ne_v
  let w : V := P.penultimate
  have hw_adj : T.Adj v w := by
    simpa [w] using (P.penultimate_adj_target hPne).symm
  have hw_cases : w = v₁ ∨ w = v₁' :=
    hv_exact.eq_left_or_right w hw_adj
  rcases hw_cases with hw | hw
  · let Q : GraphPath T := P.dropLast
    have hQne : Q.source ≠ Q.target := by
      intro h
      exact hu_ne_v₁ (by simpa [Q, w, hw] using h)
    let z : V := Q.penultimate
    have hz_adj : T.Adj v₁ z := by
      have hQadj := Q.penultimate_adj_target hQne
      simpa [Q, z, w, hw] using hQadj.symm
    have hz_cases : z = v₂ ∨ z = v :=
      hv₁_exact.eq_left_or_right z hz_adj
    have hz_ne_v : z ≠ v := by
      intro hzv
      have hz_mem_Q : z ∈ Q.vertexSet :=
        Q.penultimate_mem_vertexSet hQne
      have hv_mem_Q : v ∈ Q.vertexSet := by
        simpa [z, hzv] using hz_mem_Q
      exact P.target_not_mem_dropLast_vertexSet hPne
        (by simpa [Q] using hv_mem_Q)
    have hz : z = v₂ := by
      rcases hz_cases with hz | hz
      · exact hz
      · exact False.elim (hz_ne_v hz)
    have havoid :
        s(v₁, v₂) ∉ Q.dropLast.edgeSet := by
      simpa [Q, w, hw] using
        (GraphPath.dropLast_not_mem_edgeSet_of_incident_target
          (P := Q) hQne (x := v₂))
    have hu_reach_v₂ :
        (T.deleteEdges {s(v₁, v₂)}).Reachable u v₂ := by
      have hreach :=
        GraphPath.reachable_deleteEdge_of_not_mem_edgeSet
          (P := Q.dropLast) (e := s(v₁, v₂)) havoid
      simpa [Q, z, hz] using hreach
    have hsym_v_v₁ : s(v, v₁) ≠ s(v₁, v₂) := by
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with h | h
      · exact hv₁v.ne h.1.symm
      · exact hv₂_ne_v h.1.symm
    have hv_reach_v₁ :
        (T.deleteEdges {s(v₁, v₂)}).Reachable v v₁ := by
      exact _root_.SimpleGraph.Adj.reachable (by
        rw [_root_.SimpleGraph.deleteEdges_adj]
        exact ⟨hv₁v.symm, by simp [hsym_v_v₁]⟩)
    have hnot :
        ¬ (T.deleteEdges {s(v₁, v₂)}).Reachable v u :=
      delete_tree_edge_not_reachable_of_sides
        (T := T) (x := v₁) (y := v₂) (a := v) (b := u)
        hT hv₁v₂ hv_reach_v₁ hu_reach_v₂
    exact Or.inl ⟨hu_reach_v₂, hnot⟩
  · let Q : GraphPath T := P.dropLast
    have hQne : Q.source ≠ Q.target := by
      intro h
      exact hu_ne_v₁' (by simpa [Q, w, hw] using h)
    let z : V := Q.penultimate
    have hz_adj : T.Adj v₁' z := by
      have hQadj := Q.penultimate_adj_target hQne
      simpa [Q, z, w, hw] using hQadj.symm
    have hz_cases : z = v ∨ z = v₂' :=
      hv₁'_exact.eq_left_or_right z hz_adj
    have hz_ne_v : z ≠ v := by
      intro hzv
      have hz_mem_Q : z ∈ Q.vertexSet :=
        Q.penultimate_mem_vertexSet hQne
      have hv_mem_Q : v ∈ Q.vertexSet := by
        simpa [z, hzv] using hz_mem_Q
      exact P.target_not_mem_dropLast_vertexSet hPne
        (by simpa [Q] using hv_mem_Q)
    have hz : z = v₂' := by
      rcases hz_cases with hz | hz
      · exact False.elim (hz_ne_v hz)
      · exact hz
    have havoid :
        s(v₁', v₂') ∉ Q.dropLast.edgeSet := by
      simpa [Q, w, hw] using
        (GraphPath.dropLast_not_mem_edgeSet_of_incident_target
          (P := Q) hQne (x := v₂'))
    have hu_reach_v₂' :
        (T.deleteEdges {s(v₁', v₂')}).Reachable u v₂' := by
      have hreach :=
        GraphPath.reachable_deleteEdge_of_not_mem_edgeSet
          (P := Q.dropLast) (e := s(v₁', v₂')) havoid
      simpa [Q, z, hz] using hreach
    have hsym_v_v₁' : s(v, v₁') ≠ s(v₁', v₂') := by
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with h | h
      · exact hv₁'v.ne h.1.symm
      · exact hv_ne_v₂' h.1
    have hv_reach_v₁' :
        (T.deleteEdges {s(v₁', v₂')}).Reachable v v₁' := by
      exact _root_.SimpleGraph.Adj.reachable (by
        rw [_root_.SimpleGraph.deleteEdges_adj]
        exact ⟨hv₁'v.symm, by simp [hsym_v_v₁']⟩)
    have hnot :
        ¬ (T.deleteEdges {s(v₁', v₂')}).Reachable v u :=
      delete_tree_edge_not_reachable_of_sides
        (T := T) (x := v₁') (y := v₂') (a := v) (b := u)
        hT hv₁'v₂' hv_reach_v₁' hu_reach_v₂'
    exact Or.inr ⟨hu_reach_v₂', hnot⟩

/-- Local five-vertex consequence of the two shortcut exclusions.  If
`v₂-v₁-v-v₁'-v₂'` is a degree-two path in the leaf-maximal tree, then the
middle vertex `v` has ambient degree two as soon as every other ambient
neighbor lies on one of the two sides certified by the tree-deletion
reachability hypotheses. -/
theorem IsLeafMaximalSpanningTree.degreeEquals_ambient_of_five_path
    {G T : _root_.SimpleGraph V} {v₂ v₁ v v₁' v₂' : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (hv₂ : DegreeEquals T v₂ 2)
    (hv₁ : DegreeEquals T v₁ 2)
    (hv : DegreeEquals T v 2)
    (hv₁' : DegreeEquals T v₁' 2)
    (hv₂' : DegreeEquals T v₂' 2)
    (hv₁v₂ : T.Adj v₁ v₂)
    (hv₁v : T.Adj v₁ v)
    (hv₁'v : T.Adj v₁' v)
    (hv₁'v₂' : T.Adj v₁' v₂')
    (hv₁_ne_v₁' : v₁ ≠ v₁')
    (hv₂_ne_v : v₂ ≠ v)
    (hv_ne_v₂' : v ≠ v₂')
    (hside :
      ∀ u : V, G.Adj v u → u ≠ v₁ → u ≠ v₁' → u ≠ v₂ → u ≠ v₂' →
        ((T.deleteEdges {s(v₁, v₂)}).Reachable u v₂ ∧
          ¬ (T.deleteEdges {s(v₁, v₂)}).Reachable v u) ∨
        ((T.deleteEdges {s(v₁', v₂')}).Reachable u v₂' ∧
          ¬ (T.deleteEdges {s(v₁', v₂')}).Reachable v u)) :
    DegreeEquals G v 2 := by
  classical
  have hvv₁G : G.Adj v v₁ := hT.1 hv₁v.symm
  have hvv₁'G : G.Adj v v₁' := hT.1 hv₁'v.symm
  refine HasExactlyTwoNeighbors.degreeEquals
    (G := G) (v := v) (x := v₁) (y := v₁') ?_
  refine ⟨hv₁_ne_v₁', hvv₁G, hvv₁'G, ?_⟩
  intro u huv
  by_cases hu₁ : u = v₁
  · exact Or.inl hu₁
  by_cases hu₁' : u = v₁'
  · exact Or.inr hu₁'
  exfalso
  by_cases hu₂ : u = v₂
  · subst hu₂
    exact hT.not_firstShortcut_of_degreeTwo_path
      hv₂ hv₁ hv hv₁v₂ hv₁v hv₂_ne_v
      huv.symm
  by_cases hu₂' : u = v₂'
  · subst hu₂'
    exact hT.not_firstShortcut_of_degreeTwo_path
      hv hv₁' hv₂' hv₁'v hv₁'v₂' hv_ne_v₂'
      huv
  rcases hside u huv hu₁ hu₁' hu₂ hu₂' with hparent | hchild
  · exact hT.not_secondShortcut_delete_parent_of_degreeTwo_path
      hv₂ hv₁ hv hv₁v₂ hv₁v
      hv₂_ne_v
      huv hu₁ hu₂ hparent.1 hparent.2
  · exact hT.not_secondShortcut_delete_child_of_degreeTwo_path
      hv hv₁' hv₂' hv₁'v hv₁'v₂'
      hv_ne_v₂'
      huv hu₁' hu₂' hchild.1 hchild.2

/-- Self-contained five-vertex consequence of leaf-maximality.  The side
dichotomy needed by `degreeEquals_ambient_of_five_path` is supplied by the
unique tree path from the external neighbor to the middle vertex. -/
theorem IsLeafMaximalSpanningTree.degreeEquals_ambient_of_five_path'
    {G T : _root_.SimpleGraph V} {v₂ v₁ v v₁' v₂' : V}
    (hT : IsLeafMaximalSpanningTree G T)
    (hv₂ : DegreeEquals T v₂ 2)
    (hv₁ : DegreeEquals T v₁ 2)
    (hv : DegreeEquals T v 2)
    (hv₁' : DegreeEquals T v₁' 2)
    (hv₂' : DegreeEquals T v₂' 2)
    (hv₁v₂ : T.Adj v₁ v₂)
    (hv₁v : T.Adj v₁ v)
    (hv₁'v : T.Adj v₁' v)
    (hv₁'v₂' : T.Adj v₁' v₂')
    (hv₁_ne_v₁' : v₁ ≠ v₁')
    (hv₂_ne_v : v₂ ≠ v)
    (hv_ne_v₂' : v ≠ v₂') :
    DegreeEquals G v 2 := by
  exact hT.degreeEquals_ambient_of_five_path
    hv₂ hv₁ hv hv₁' hv₂' hv₁v₂ hv₁v hv₁'v hv₁'v₂'
    hv₁_ne_v₁' hv₂_ne_v hv_ne_v₂'
    (by
      intro u huv hu₁ hu₁' _hu₂ _hu₂'
      exact tree_five_path_side_dichotomy
        hT.2.1 hv₁ hv hv₁' hv₁v₂ hv₁v hv₁'v hv₁'v₂'
        hv₁_ne_v₁' hv₂_ne_v hv_ne_v₂'
        huv.ne.symm hu₁ hu₁')

/-- A long tree path whose vertices all have tree degree two contains, after
discarding two vertices from each end, a 2-path in the ambient graph. -/
theorem containsTwoPath_of_leafMaximal_tree_path
    {G T : _root_.SimpleGraph V} {p : ℕ}
    (hMax : IsLeafMaximalSpanningTree G T)
    (hp : 1 ≤ p)
    (P : GraphPath T)
    (hcard : p + 4 ≤ P.vertexSet.card)
    (hdeg : ∀ v ∈ P.vertexSet, DegreeEquals T v 2) :
    ContainsTwoPath G p := by
  classical
  let n : ℕ := P.walk.length
  have hPcard :
      P.vertexSet.card = n + 1 := by
    simpa [n] using graphPath_vertexSet_card_eq_walk_length_add_one P
  have hn_lower : p + 3 ≤ n := by
    omega
  have hn4 : 4 ≤ n := by
    omega
  have h2_le_nsub2 : 2 ≤ n - 2 := by
    omega
  have hnsub2_le : n - 2 ≤ P.walk.length := by
    simp [n]
  let hcoreBefore :
      P.Before (P.walk.getVert 2) (P.walk.getVert (n - 2)) := by
    simpa [n] using
      P.before_getVert_of_le (i := 2) (j := n - 2)
        h2_le_nsub2 hnsub2_le
  let Core : GraphPath T := P.segmentOfBefore hcoreBefore
  have hCoreCard : p ≤ Core.vertexSet.card := by
    have hseg :=
      P.segmentOfBefore_getVert_card (i := 2) (j := n - 2)
        h2_le_nsub2 hnsub2_le
    have hcardCoreRaw : Core.vertexSet.card = (n - 2) - 2 + 1 := by
      simpa [Core, hcoreBefore, n] using hseg
    have hcardCore : Core.vertexSet.card = n - 3 := by
      omega
    omega
  refine containsTwoPath_of_subgraph_path hMax.1 Core hCoreCard ?_
  intro x hxCore
  have hxP : x ∈ P.vertexSet := by
    simpa [Core] using P.segmentOfBefore_vertexSet_subset hcoreBefore hxCore
  let k : ℕ := P.vertexIndex x
  have hk_get : P.walk.getVert k = x := by
    simpa [k] using P.getVert_vertexIndex_eq hxP
  have hleft := P.before_of_mem_segmentOfBefore_left hcoreBefore (by
    simpa [Core] using hxCore)
  have hright := P.before_of_mem_segmentOfBefore_right hcoreBefore (by
    simpa [Core] using hxCore)
  have hk_ge_two : 2 ≤ k := by
    have hleft' := (P.before_iff_vertexIndex_le).1 hleft
    have hidx2 : P.vertexIndex (P.walk.getVert 2) = 2 := by
      exact P.vertexIndex_getVert (by omega : 2 ≤ P.walk.length)
    simpa [k, hidx2] using hleft'.2.2
  have hk_le_nsub2 : k ≤ n - 2 := by
    have hright' := (P.before_iff_vertexIndex_le).1 hright
    have hidxn : P.vertexIndex (P.walk.getVert (n - 2)) = n - 2 := by
      exact P.vertexIndex_getVert hnsub2_le
    simpa [k, hidxn] using hright'.2.2
  have hk_le_n : k ≤ P.walk.length := by
    have hklt : k < P.walk.support.length := by
      simpa [k, GraphPath.vertexIndex] using
        (List.idxOf_lt_length_iff.2
          (by simpa [GraphPath.vertexSet] using hxP :
            x ∈ P.walk.support))
    rw [_root_.SimpleGraph.Walk.length_support] at hklt
    omega
  let v₂ : V := P.walk.getVert (k - 2)
  let v₁ : V := P.walk.getVert (k - 1)
  let v₁' : V := P.walk.getVert (k + 1)
  let v₂' : V := P.walk.getVert (k + 2)
  have hkm2_le : k - 2 ≤ P.walk.length := by omega
  have hkm1_le : k - 1 ≤ P.walk.length := by omega
  have hkp1_le : k + 1 ≤ P.walk.length := by omega
  have hkp2_le : k + 2 ≤ P.walk.length := by omega
  have hv₂deg : DegreeEquals T v₂ 2 :=
    hdeg v₂ (P.mem_vertexSet_getVert hkm2_le)
  have hv₁deg : DegreeEquals T v₁ 2 :=
    hdeg v₁ (P.mem_vertexSet_getVert hkm1_le)
  have hxdeg : DegreeEquals T x 2 := hdeg x hxP
  have hv₁'deg : DegreeEquals T v₁' 2 :=
    hdeg v₁' (P.mem_vertexSet_getVert hkp1_le)
  have hv₂'deg : DegreeEquals T v₂' 2 :=
    hdeg v₂' (P.mem_vertexSet_getVert hkp2_le)
  have hv₁v₂ : T.Adj v₁ v₂ := by
    have hadj := P.walk.adj_getVert_succ (i := k - 2) (by omega)
    have hsucc : k - 2 + 1 = k - 1 := by omega
    simpa [v₁, v₂, hsucc] using hadj.symm
  have hv₁x : T.Adj v₁ x := by
    have hadj := P.walk.adj_getVert_succ (i := k - 1) (by omega)
    have hsucc : k - 1 + 1 = k := by omega
    simpa [v₁, hk_get, hsucc] using hadj
  have hv₁'x : T.Adj v₁' x := by
    have hadj := P.walk.adj_getVert_succ (i := k) (by omega)
    simpa [v₁', hk_get] using hadj.symm
  have hv₁'v₂' : T.Adj v₁' v₂' := by
    have hadj := P.walk.adj_getVert_succ (i := k + 1) (by omega)
    simpa [v₁', v₂', Nat.add_assoc] using hadj
  have hv₁_ne_v₁' : v₁ ≠ v₁' := by
    intro h
    have hinj := P.isPath.getVert_injOn
      (by simp; omega : k - 1 ∈ {i : ℕ | i ≤ P.walk.length})
      (by simp; omega : k + 1 ∈ {i : ℕ | i ≤ P.walk.length})
      (by simpa [v₁, v₁'] using h)
    omega
  have hv₂_ne_x : v₂ ≠ x := by
    intro h
    have hinj := P.isPath.getVert_injOn
      (by simp; omega : k - 2 ∈ {i : ℕ | i ≤ P.walk.length})
      (by simp; exact hk_le_n : k ∈ {i : ℕ | i ≤ P.walk.length})
      (by simpa [v₂, hk_get] using h)
    omega
  have hx_ne_v₂' : x ≠ v₂' := by
    intro h
    have hinj := P.isPath.getVert_injOn
      (by simp; exact hk_le_n : k ∈ {i : ℕ | i ≤ P.walk.length})
      (by simp; omega : k + 2 ∈ {i : ℕ | i ≤ P.walk.length})
      (by simpa [v₂', hk_get] using h)
    omega
  exact hMax.degreeEquals_ambient_of_five_path'
    hv₂deg hv₁deg hxdeg hv₁'deg hv₂'deg
    hv₁v₂ hv₁x hv₁'x hv₁'v₂'
    hv₁_ne_v₁' hv₂_ne_x hx_ne_v₂'

theorem degreeTwoSubtype_card_eq
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj] :
    Fintype.card {v : V // v ∈ treeDegreeTwoVertexSet T} =
      (treeDegreeTwoVertexSet T).card := by
  classical
  simpa [treeDegreeTwoVertexSet] using
    (Fintype.card_subtype (fun v : V => v ∈ treeDegreeTwoVertexSet T))

/-- Mapping the edges of the degree-two induced graph back to the ambient
vertex type gives exactly the ambient tree edges with both endpoints of tree
degree two. -/
theorem degreeTwoInducedGraph_map_edgeFinset_eq_inter
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    [Fintype (degreeTwoInducedGraph T).edgeSet] :
    (degreeTwoInducedGraph T).edgeFinset.map
        (Function.Embedding.subtype
          (fun v : V => v ∈ treeDegreeTwoVertexSet T)).sym2Map =
      (T.edgeFinset ∩ (treeDegreeTwoVertexSet T).sym2) := by
  classical
  aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall,
    degreeTwoInducedGraph, _root_.SimpleGraph.mem_edgeFinset,
    _root_.SimpleGraph.adj_comm])

/-- The edges of the graph induced by the degree-two vertices are exactly the
tree edges whose endpoints both have tree degree two. -/
theorem degreeTwoInducedGraph_edgeFinset_card_eq_inter
    (T : _root_.SimpleGraph V) [DecidableRel T.Adj]
    [Fintype (degreeTwoInducedGraph T).edgeSet] :
    (degreeTwoInducedGraph T).edgeFinset.card =
      (T.edgeFinset ∩ (treeDegreeTwoVertexSet T).sym2).card := by
  classical
  rw [← degreeTwoInducedGraph_map_edgeFinset_eq_inter T, Finset.card_map]

/-- If a nontrivial tree has fewer than `L` leaves, then the induced forest on
its degree-two vertices has at most `2L` connected components.  This is the
component-count estimate for maximal degree-two paths used in Appendix A.2. -/
theorem degreeTwoInducedGraph_component_count_le_two_mul_of_few_leaves
    {T : _root_.SimpleGraph V} [DecidableRel T.Adj]
    [DecidableRel (degreeTwoInducedGraph T).Adj]
    {L : ℕ}
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V)
    (hleaves : leafCount T < L) :
    Fintype.card (degreeTwoInducedGraph T).ConnectedComponent ≤ 2 * L := by
  classical
  let D := treeDegreeTwoVertexSet T
  let S := treeSkeletonVertexSet T
  let H : _root_.SimpleGraph {v : V // v ∈ D} := degreeTwoInducedGraph T
  have hacyc : H.IsAcyclic := by
    simpa [H, degreeTwoInducedGraph, D] using
      hT.isAcyclic.induce {v : V | v ∈ D}
  have hforest := isAcyclic_connectedComponent_card_add_edgeFinset_card H hacyc
  have hDcard : Fintype.card {v : V // v ∈ D} = D.card := by
    simpa [D] using degreeTwoSubtype_card_eq T
  have hforestD :
      Fintype.card H.ConnectedComponent + H.edgeFinset.card = D.card := by
    simpa [H, hDcard] using hforest
  have hedgeH :
      H.edgeFinset.card = (T.edgeFinset ∩ D.sym2).card := by
    simpa [H, D] using degreeTwoInducedGraph_edgeFinset_card_eq_inter T
  have hsplit :
      (T.edgeFinset ∩ D.sym2).card + (T.edgeFinset \ D.sym2).card =
        T.edgeFinset.card := by
    simp [D]
  have hnonD :
      (T.edgeFinset \ D.sym2).card ≤ 2 * S.card := by
    have h1 :=
      tree_edgeFinset_sdiff_degreeTwo_sym2_card_le_skeleton_degree_sum
        T hT hcard
    have h2 := treeSkeletonVertexSet_degree_sum_le_two_mul_card T hT hcard
    simpa [D, S] using h1.trans h2
  have hpartition :
      D.card + S.card = Fintype.card V := by
    simpa [D, S] using treeDegreeTwoVertexSet_card_add_skeleton_card T hT hcard
  have hedgeTree : T.edgeFinset.card + 1 = Fintype.card V :=
    hT.card_edgeFinset
  have hcomp_le_succ :
      Fintype.card H.ConnectedComponent ≤ S.card + 1 := by
    omega
  have hSsucc : S.card + 1 ≤ 2 * L := by
    simpa [S] using
      treeSkeletonVertexSet_card_succ_le_two_mul T hT hcard hleaves
  exact hcomp_le_succ.trans hSsucc

omit [DecidableEq V] in
/-- Pigeonhole principle for connected components: if a finite graph has at
most `N` components and at least `N * (m + 1)` vertices, then one component has
at least `m + 1` vertices. -/
theorem exists_component_card_ge_of_component_count_le
    (H : _root_.SimpleGraph V) [DecidableRel H.Adj]
    {N m : ℕ}
    (hNpos : 0 < N)
    (hcomponents : Fintype.card H.ConnectedComponent ≤ N)
    (htotal : N * (m + 1) ≤ Fintype.card V) :
    ∃ C : H.ConnectedComponent,
      m + 1 ≤ (connectedComponentVertexFinset H C).card := by
  classical
  by_contra h
  have hall : ∀ C : H.ConnectedComponent,
      (connectedComponentVertexFinset H C).card ≤ m := by
    intro C
    have hnot : ¬ m + 1 ≤ (connectedComponentVertexFinset H C).card := by
      intro hC
      exact h ⟨C, hC⟩
    omega
  have htotal_le :=
    card_le_components_mul_of_component_card_le H m hall
  have hmul : Fintype.card H.ConnectedComponent * m ≤ N * m := by
    exact Nat.mul_le_mul_right m hcomponents
  have hlt : N * m < N * (m + 1) := by
    nlinarith
  omega

/-- Conditional long degree-two tree path extraction.  The only global
counting input is the standard bound that the degree-two induced forest has at
most `2 * L` connected components. -/
theorem exists_long_degreeTwo_tree_path_of_component_bound
    {T : _root_.SimpleGraph V} [DecidableRel T.Adj]
    [DecidableRel (degreeTwoInducedGraph T).Adj]
    {L p : ℕ}
    (hT : T.IsTree)
    (hL : 1 ≤ L)
    (hcard : 2 * L * (p + 5) ≤ Fintype.card V)
    (hleaves : leafCount T < L)
    (hcomponents :
      Fintype.card (degreeTwoInducedGraph T).ConnectedComponent ≤ 2 * L) :
    ∃ P : GraphPath T,
      p + 4 ≤ P.vertexSet.card ∧
        ∀ v ∈ P.vertexSet, DegreeEquals T v 2 := by
  classical
  have hVcard : 2 ≤ Fintype.card V := by
    nlinarith
  have hD_lower₀ :
      Fintype.card V - 2 * L ≤ (treeDegreeTwoVertexSet T).card :=
    treeDegreeTwoVertexSet_card_ge_card_sub_two_mul T hT hVcard hleaves
  have hD_lower :
      2 * L * (p + 4) ≤ (treeDegreeTwoVertexSet T).card := by
    have : 2 * L * (p + 4) ≤ Fintype.card V - 2 * L := by
      apply Nat.le_sub_of_add_le
      nlinarith [hcard]
    exact this.trans hD_lower₀
  let H : _root_.SimpleGraph {v : V // v ∈ treeDegreeTwoVertexSet T} :=
    degreeTwoInducedGraph T
  have hHtotal :
      2 * L * (p + 4) ≤ Fintype.card {v : V // v ∈ treeDegreeTwoVertexSet T} := by
    rw [degreeTwoSubtype_card_eq T]
    exact hD_lower
  have hNpos : 0 < 2 * L := by
    omega
  rcases exists_component_card_ge_of_component_count_le
      (H := H) (N := 2 * L) (m := p + 3)
      hNpos (by simpa [H] using hcomponents)
      (by
        simpa [H, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hHtotal) with
    ⟨C, hC⟩
  rcases exists_tree_path_of_degreeTwo_component T C with ⟨P, hPcard, hPdeg⟩
  refine ⟨P, ?_, hPdeg⟩
  have hC' : p + 4 ≤
      (connectedComponentVertexFinset (degreeTwoInducedGraph T) C).card := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hC
  simpa [hPcard] using hC'

/-- Conditional hard branch of Theorem 2.15 once the global component count for
maximal degree-two paths in a tree is available. -/
theorem theorem215_of_maxLeafSpanningTree_few_leaves_of_component_bound
    {G : _root_.SimpleGraph V} {L p : ℕ} (hG : G.Connected)
    [DecidableRel (maxLeafSpanningTree G hG).Adj]
    [DecidableRel (degreeTwoInducedGraph (maxLeafSpanningTree G hG)).Adj]
    (hL : 1 ≤ L) (hp : 1 ≤ p)
    (hcard : 2 * L * (p + 5) ≤ Fintype.card V)
    (hleaves : leafCount (maxLeafSpanningTree G hG) < L)
    (hcomponents :
      Fintype.card
        (degreeTwoInducedGraph (maxLeafSpanningTree G hG)).ConnectedComponent ≤
          2 * L) :
    HasSpanningTreeWithAtLeastLeaves G L ∨ ContainsTwoPath G p := by
  classical
  let T : _root_.SimpleGraph V := maxLeafSpanningTree G hG
  have hMax : IsLeafMaximalSpanningTree G T := by
    simpa [T] using maxLeafSpanningTree_isLeafMaximal hG
  rcases exists_long_degreeTwo_tree_path_of_component_bound
      (T := T) hMax.2.1 hL hcard (by simpa [T] using hleaves)
      (by simpa [T] using hcomponents) with
    ⟨P, hPcard, hPdeg⟩
  exact Or.inr <|
    containsTwoPath_of_leafMaximal_tree_path hMax hp P hPcard hPdeg

/-- The easy branch of Theorem 2.15: if the leaf-maximal spanning tree has at
least `L` leaves, then the theorem is already proved. -/
theorem theorem215_of_maxLeafSpanningTree_many_leaves
    {G : _root_.SimpleGraph V} {L p : ℕ} (hG : G.Connected)
    (hL : L ≤ leafCount (maxLeafSpanningTree G hG)) :
    HasSpanningTreeWithAtLeastLeaves G L ∨ ContainsTwoPath G p := by
  exact Or.inl <|
    hasSpanningTreeWithAtLeastLeaves_of_leafCount
      (maxLeafSpanningTree_le hG) (maxLeafSpanningTree_isTree hG) hL

/-- Chekuri--Chuzhoy Theorem 2.15, structural form.

If `Z` is connected and has at least `2 * L * (p + 5)` vertices, then either
`Z` has a spanning tree with at least `L` leaves or it contains a 2-path on at
least `p` vertices.  This is the non-algorithmic statement used later in the
path-of-sets to grid-minor conversion. -/
theorem theorem215_tree_with_many_leaves_or_long_twoPath
    (Z : _root_.SimpleGraph V) {L p : ℕ}
    (hZ : Z.Connected) (hL : 1 ≤ L) (hp : 1 ≤ p)
    (hcard : 2 * L * (p + 5) ≤ Fintype.card V) :
    HasSpanningTreeWithAtLeastLeaves Z L ∨ ContainsTwoPath Z p := by
  classical
  by_cases hmany : L ≤ leafCount (maxLeafSpanningTree Z hZ)
  · exact theorem215_of_maxLeafSpanningTree_many_leaves hZ hmany
  · have hfew : leafCount (maxLeafSpanningTree Z hZ) < L := by
      omega
    let T : _root_.SimpleGraph V := maxLeafSpanningTree Z hZ
    have hTtree : T.IsTree := by
      simpa [T] using maxLeafSpanningTree_isTree hZ
    have hVcard : 2 ≤ Fintype.card V := by
      nlinarith
    have hcomponents :
        Fintype.card
          (degreeTwoInducedGraph (maxLeafSpanningTree Z hZ)).ConnectedComponent ≤
            2 * L := by
      simpa [T] using
        degreeTwoInducedGraph_component_count_le_two_mul_of_few_leaves
          (T := T) hTtree hVcard (by simpa [T] using hfew)
    exact theorem215_of_maxLeafSpanningTree_few_leaves_of_component_bound
      hZ hL hp hcard hfew hcomponents

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
