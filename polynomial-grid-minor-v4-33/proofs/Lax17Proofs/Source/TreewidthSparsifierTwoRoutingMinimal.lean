import Lax17Proofs.Source.TreewidthSparsifierSection2

namespace Lax17Proofs

universe u v w

/-!
# Edge-minimal two-routing supports

Step 1 of Theorem 5.1 replaces each pair of red/blue routings by an
edge-minimal subgraph in which both terminal pairs remain routable.  The
minimality is used in Claim 5.4 after the segment contraction.  This file
supplies the finite choice and its exact one-edge deletion consequence.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A same-vertex edge-minimal support for two simultaneous perfect
routings. -/
structure EdgeMinimalTwoRoutingSubgraph
    (G : _root_.SimpleGraph V)
    (S₁ T₁ S₂ T₂ : Finset V) where
  graph : _root_.SimpleGraph V
  le_original : graph ≤ G
  red : PerfectPathPacking graph S₁ T₁
  blue : PerfectPathPacking graph S₂ T₂
  deleteEdge_failure :
    ∀ ⦃a b : V⦄, graph.Adj a b →
      ¬ (RoutableIn
          (graph.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₁ T₁ ∧
        RoutableIn
          (graph.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₂ T₂)

namespace EdgeMinimalTwoRoutingSubgraph

omit [DecidableEq V] in
private theorem edgeSet_deleteEdges_singleton_ncard_lt
    (H : _root_.SimpleGraph V) {a b : V} (hab : H.Adj a b) :
    ((H.deleteEdges ({s(a, b)} : Set (Sym2 V))).edgeSet).ncard <
      H.edgeSet.ncard := by
  classical
  let e : Sym2 V := s(a, b)
  have heH : e ∈ H.edgeSet := by
    simpa [_root_.SimpleGraph.mem_edgeSet, e] using hab
  rw [_root_.SimpleGraph.edgeSet_deleteEdges]
  have hcard :
      (H.edgeSet \ ({e} : Set (Sym2 V))).ncard + 1 =
        H.edgeSet.ncard :=
    Set.ncard_diff_singleton_add_one heH (Set.toFinite H.edgeSet)
  exact (Nat.lt_succ_self _).trans_eq hcard

/-- Finite minimization of the number of retained edges. -/
theorem exists_of_routable
    {G : _root_.SimpleGraph V} {S₁ T₁ S₂ T₂ : Finset V}
    (hred : RoutableIn G S₁ T₁)
    (hblue : RoutableIn G S₂ T₂) :
    Nonempty (EdgeMinimalTwoRoutingSubgraph G S₁ T₁ S₂ T₂) := by
  classical
  let Candidate :=
    {H : _root_.SimpleGraph V //
      H ≤ G ∧ RoutableIn H S₁ T₁ ∧ RoutableIn H S₂ T₂}
  let HasEdgeCount : ℕ → Prop := fun n =>
    ∃ H : Candidate, H.1.edgeSet.ncard = n
  have hexists : ∃ n, HasEdgeCount n :=
    ⟨G.edgeSet.ncard, ⟨G, le_rfl, hred, hblue⟩, rfl⟩
  let edgeMin := Nat.find hexists
  rcases Nat.find_spec hexists with ⟨Hmin, hHcard⟩
  let red : PerfectPathPacking Hmin.1 S₁ T₁ :=
    Classical.choice Hmin.2.2.1
  let blue : PerfectPathPacking Hmin.1 S₂ T₂ :=
    Classical.choice Hmin.2.2.2
  refine ⟨{
    graph := Hmin.1
    le_original := Hmin.2.1
    red := red
    blue := blue
    deleteEdge_failure := ?_
  }⟩
  intro a b hab hdelete
  let Hdel : Candidate :=
    ⟨Hmin.1.deleteEdges ({s(a, b)} : Set (Sym2 V)),
      (_root_.SimpleGraph.deleteEdges_le
        ({s(a, b)} : Set (Sym2 V))).trans Hmin.2.1,
      hdelete.1, hdelete.2⟩
  have hcandidate : HasEdgeCount Hdel.1.edgeSet.ncard :=
    ⟨Hdel, rfl⟩
  have hminle : edgeMin ≤ Hdel.1.edgeSet.ncard :=
    Nat.find_min' (H := hexists) hcandidate
  have hdellt :
      Hdel.1.edgeSet.ncard < Hmin.1.edgeSet.ncard := by
    simpa [Hdel] using
      edgeSet_deleteEdges_singleton_ncard_lt Hmin.1 hab
  omega

/-- Edge minimization does not create new branch vertices. -/
theorem branchVertexCount_le
    {G : _root_.SimpleGraph V} {S₁ T₁ S₂ T₂ : Finset V}
    (M : EdgeMinimalTwoRoutingSubgraph G S₁ T₁ S₂ T₂) :
    branchVertexCount M.graph ≤ branchVertexCount G :=
  branchVertexCount_le_of_injective_adj
    (fun v : V => v) Function.injective_id
    (fun {_ _} huv => M.le_original huv)

/-- Every retained edge is used by one of the two selected routings.  An
unused edge could be deleted without affecting either routing, contrary to
minimality. -/
theorem graph_eq_twoPackingUnion
    {G : _root_.SimpleGraph V} {S₁ T₁ S₂ T₂ : Finset V}
    (M : EdgeMinimalTwoRoutingSubgraph G S₁ T₁ S₂ T₂) :
    M.graph = twoPackingUnionGraph M.red M.blue := by
  classical
  apply le_antisymm
  · intro a b hab
    by_contra hnot
    have hnotRed :
        ¬ M.red.toPathPacking.spanningGraph.Adj a b := by
      intro h
      exact hnot (Or.inl h)
    have hnotBlue :
        ¬ M.blue.toPathPacking.spanningGraph.Adj a b := by
      intro h
      exact hnot (Or.inr h)
    let Hdel :=
      M.graph.deleteEdges ({s(a, b)} : Set (Sym2 V))
    have redEdges :
        ∀ i : M.red.Index, ∀ e,
          e ∈ (M.red.path i).walk.edges → e ∈ Hdel.edgeSet := by
      intro i e he
      rw [_root_.SimpleGraph.edgeSet_deleteEdges]
      constructor
      · exact (M.red.path i).walk.edges_subset_edgeSet he
      · intro heq
        have heq' : e = s(a, b) := by simpa using heq
        subst e
        have hedge : s(a, b) ∈ (M.red.path i).edgeSet := by
          simpa [GraphPath.edgeSet] using he
        apply hnotRed
        exact
          (M.red.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
            ⟨⟨i, hedge⟩, M.graph.ne_of_adj hab⟩
    have blueEdges :
        ∀ i : M.blue.Index, ∀ e,
          e ∈ (M.blue.path i).walk.edges → e ∈ Hdel.edgeSet := by
      intro i e he
      rw [_root_.SimpleGraph.edgeSet_deleteEdges]
      constructor
      · exact (M.blue.path i).walk.edges_subset_edgeSet he
      · intro heq
        have heq' : e = s(a, b) := by simpa using heq
        subst e
        have hedge : s(a, b) ∈ (M.blue.path i).edgeSet := by
          simpa [GraphPath.edgeSet] using he
        apply hnotBlue
        exact
          (M.blue.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
            ⟨⟨i, hedge⟩, M.graph.ne_of_adj hab⟩
    exact M.deleteEdge_failure hab
      ⟨⟨M.red.transfer Hdel redEdges⟩,
        ⟨M.blue.transfer Hdel blueEdges⟩⟩
  · exact twoPackingUnionGraph_le M.red M.blue

end EdgeMinimalTwoRoutingSubgraph

/-- The edge-deletion consequence of Theorem 1.3 used in the proof of
`treewidth-sparsifier.pdf`, Claim 5.4.

If a graph supporting two routing pairs has more branch vertices than the
Theorem 1.3 bound, reroute both pairs with a smaller union.  Some ambient edge
is then absent from both new routings, so deleting that edge preserves both
routing pairs. -/
theorem exists_edge_deletable_for_two_routings_of_branchVertexCount_gt
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {k₁ k₂ : ℕ}
    (hS₁ : S₁.card = k₁) (hT₁ : T₁.card = k₁)
    (hS₂ : S₂.card = k₂) (hT₂ : T₂.card = k₂)
    (hk₂ : k₂ ≤ k₁)
    (hred : RoutableIn G S₁ T₁)
    (hblue : RoutableIn G S₂ T₂)
    (hlarge : 8 * k₁ ^ 4 + 8 * k₁ < branchVertexCount G) :
    ∃ a b : V, G.Adj a b ∧
      RoutableIn
        (G.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₁ T₁ ∧
      RoutableIn
        (G.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₂ T₂ := by
  classical
  rcases theorem13_two_pair_routability_sparsifier
      G S₁ T₁ S₂ T₂ hS₁ hT₁ hS₂ hT₂ hk₂ hred hblue with
    ⟨R, B, hsmall⟩
  let K := twoPackingUnionGraph R B
  have hKG : K ≤ G := twoPackingUnionGraph_le R B
  have hnotle : ¬ G ≤ K := by
    intro hGK
    have hEq : G = K := le_antisymm hGK hKG
    have hbranchEq : branchVertexCount G = branchVertexCount K :=
      congrArg branchVertexCount hEq
    dsimp [K] at hbranchEq
    omega
  change ¬ ∀ ⦃a b : V⦄, G.Adj a b → K.Adj a b at hnotle
  simp only [not_forall, Classical.not_imp] at hnotle
  rcases hnotle with ⟨a, b, hab, habK⟩
  have hne : a ≠ b := G.ne_of_adj hab
  have hrunused :
      s(a, b) ∉ R.toPathPacking.edgeSet := by
    intro he
    apply habK
    left
    exact
      (R.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨R.toPathPacking.mem_edgeSet.mp he, hne⟩
  have hbunused :
      s(a, b) ∉ B.toPathPacking.edgeSet := by
    intro he
    apply habK
    right
    exact
      (B.toPathPacking.spanningGraph_adj_iff_exists_path_edge).2
        ⟨B.toPathPacking.mem_edgeSet.mp he, hne⟩
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact ⟨perfectPathPacking_deleteUnusedEdge R hrunused⟩
  · exact ⟨perfectPathPacking_deleteUnusedEdge B hbunused⟩

/-- A symmetric bounded-cardinality form of the deletion lemma.

This is the form used in Theorem 5.1, Claim 5.4.  The two regional routing
families may have different cardinalities and either one may be larger; a
common upper bound `K` is enough for the Theorem 1.3 branch estimate. -/
theorem exists_edge_deletable_for_two_routings_of_card_le
    {G : _root_.SimpleGraph V}
    {S₁ T₁ S₂ T₂ : Finset V} {K : ℕ}
    (hS₁T₁ : S₁.card = T₁.card)
    (hS₂T₂ : S₂.card = T₂.card)
    (hS₁ : S₁.card ≤ K)
    (hS₂ : S₂.card ≤ K)
    (hred : RoutableIn G S₁ T₁)
    (hblue : RoutableIn G S₂ T₂)
    (hlarge : 8 * K ^ 4 + 8 * K < branchVertexCount G) :
    ∃ a b : V, G.Adj a b ∧
      RoutableIn
        (G.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₁ T₁ ∧
      RoutableIn
        (G.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₂ T₂ := by
  have bound_mono :
      ∀ {k : ℕ}, k ≤ K →
        8 * k ^ 4 + 8 * k ≤ 8 * K ^ 4 + 8 * K := by
    intro k hk
    exact Nat.add_le_add
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hk 4))
      (Nat.mul_le_mul_left 8 hk)
  by_cases hcard : S₂.card ≤ S₁.card
  · apply exists_edge_deletable_for_two_routings_of_branchVertexCount_gt
      (k₁ := S₁.card) (k₂ := S₂.card)
      rfl hS₁T₁.symm rfl hS₂T₂.symm hcard hred hblue
    exact (bound_mono hS₁).trans_lt hlarge
  · have hreverse : S₁.card ≤ S₂.card := Nat.le_of_not_ge hcard
    rcases
        exists_edge_deletable_for_two_routings_of_branchVertexCount_gt
          (k₁ := S₂.card) (k₂ := S₁.card)
          rfl hS₂T₂.symm rfl hS₁T₁.symm hreverse hblue hred
          ((bound_mono hS₂).trans_lt hlarge) with
      ⟨a, b, hab, hblue', hred'⟩
    exact ⟨a, b, hab, hred', hblue'⟩

end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
