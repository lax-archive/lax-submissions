import Lax17Proofs.Source.Menger
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Lemma 2.19

This module develops the rerouting lemma used twice in Step 2 of the
many-leaves branch of Theorem 4.6 (journal Section 4.2).

The first result below is Claim A.5 from the paper's Appendix A.3, expressed
without the artificial common sink.  Endpoint-clean path packings are the
uncontracted form of nearly-disjoint paths to that sink.  The proof is a
finite-gammoid basis extension: the smaller family is augmented while keeping
all of its origins, and the larger family certifies the required separator
rank.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T : Finset V}

/-- Appendix A.3, Claim A.5: a smaller endpoint-clean family can be extended
to the cardinality of any larger family while retaining all of its origins
and destinations.

In the application, the retained origins are the `U₂` origins.  Since the
ambient source set is `U₁ ∪ U₂` and the two origin sets are disjoint, the
output therefore has exactly the prescribed number of `U₂` paths. -/
theorem exists_endpointClean_rerouting_retaining_sources
    (large small : EndpointCleanPathPacking G S T)
    (hcard : small.card ≤ large.card) :
    ∃ rerouted : EndpointCleanPathPacking G S T,
      rerouted.card = large.card ∧
        small.sourceSet ⊆ rerouted.sourceSet ∧
          small.targetSet ⊆ rerouted.targetSet := by
  have hrank : large.card ≤ Menger.minSeparatorSize G S T := by
    rw [← Menger.minSeparator_card (G := G) (S := S) (T := T)]
    exact Menger.PathPacking.card_le_of_blocks
      large.toPathPacking Menger.minSeparator_blocks
  exact Menger.EndpointCleanPathPacking.exists_extension_card
    small hcard hrank

/-- Strict-cardinality form matching the hypotheses `ℓ₁ > ℓ₂ ≥ 1` printed in
Lemma 2.19. -/
theorem exists_endpointClean_rerouting_retaining_sources_of_lt
    (large small : EndpointCleanPathPacking G S T)
    (hcard : small.card < large.card) :
    ∃ rerouted : EndpointCleanPathPacking G S T,
      rerouted.card = large.card ∧
        small.sourceSet ⊆ rerouted.sourceSet ∧
          small.targetSet ⊆ rerouted.targetSet :=
  exists_endpointClean_rerouting_retaining_sources large small hcard.le

/-- Claim A.5 with the two origin classes made explicit.  If the smaller
family uses every `U₂` origin and every output origin lies in the disjoint
union `U₁ ∪ U₂`, then the rerouted family contains exactly `|U₂|` paths
originating in `U₂`. -/
theorem exists_endpointClean_rerouting_with_exact_second_origin_class
    {U₁ U₂ : Finset V}
    (large small : EndpointCleanPathPacking G (U₁ ∪ U₂) T)
    (hsmallSources : small.sourceSet = U₂)
    (hcard : small.card ≤ large.card) :
    ∃ rerouted : EndpointCleanPathPacking G (U₁ ∪ U₂) T,
      rerouted.card = large.card ∧
        U₂ ⊆ rerouted.sourceSet ∧
          (rerouted.sourceSet ∩ U₂).card = small.card := by
  rcases exists_endpointClean_rerouting_retaining_sources
      large small hcard with
    ⟨rerouted, hreroutedCard, hsource, _htarget⟩
  have hU₂sub : U₂ ⊆ rerouted.sourceSet := by
    simpa [hsmallSources] using hsource
  have hinter : rerouted.sourceSet ∩ U₂ = U₂ := by
    exact Finset.inter_eq_right.mpr hU₂sub
  refine ⟨rerouted, hreroutedCard, hU₂sub, ?_⟩
  rw [hinter]
  calc
    U₂.card = small.sourceSet.card := congrArg Finset.card hsmallSources.symm
    _ = small.card := EndpointCleanPathPacking.sourceSet_card small

/-! ## The source-minimal graph in Appendix A.3 -/

/-- The graph obtained after the edge-deletion loop in the proof of
Lemma 2.19.  It keeps the whole large family, still admits a copy of the small
family with the same endpoint sets, and every remaining edge outside the
large-family support is essential for that endpoint prescription. -/
structure Lemma219MinimalSupport
    (large small : EndpointCleanPathPacking G S T) where
  H : _root_.SimpleGraph V
  le_original : H ≤ G
  support_le :
    H ≤
      large.toPathPacking.spanningGraph ⊔
        small.toPathPacking.spanningGraph
  large_support_le : large.toPathPacking.spanningGraph ≤ H
  smallPacking : EndpointCleanPathPacking H S T
  small_sourceSet : smallPacking.sourceSet = small.sourceSet
  delete_nonlarge_edge_forbids_small :
    ∀ ⦃e : Sym2 V⦄, e ∈ H.edgeSet →
      e ∉ large.toPathPacking.edgeSet →
        ¬ ∃ P : EndpointCleanPathPacking
            (H.deleteEdges ({e} : Set (Sym2 V))) S T,
          P.sourceSet = small.sourceSet

omit [DecidableEq V] in
private theorem edgeSet_deleteEdges_singleton_ncard_lt
    (H : _root_.SimpleGraph V) {e : Sym2 V} (heH : e ∈ H.edgeSet) :
    ((H.deleteEdges ({e} : Set (Sym2 V))).edgeSet).ncard <
      H.edgeSet.ncard := by
  classical
  rw [_root_.SimpleGraph.edgeSet_deleteEdges]
  have hcard :
      (H.edgeSet \ ({e} : Set (Sym2 V))).ncard + 1 = H.edgeSet.ncard :=
    Set.ncard_diff_singleton_add_one heH (Set.toFinite H.edgeSet)
  exact (Nat.lt_succ_self _).trans_eq hcard

/-- The Appendix A.3 edge-deletion loop terminates because a finite graph has
only finitely many edges. -/
theorem exists_lemma219MinimalSupport
    (large small : EndpointCleanPathPacking G S T) :
    Nonempty (Lemma219MinimalSupport large small) := by
  classical
  let supportGraph :=
    large.toPathPacking.spanningGraph ⊔
      small.toPathPacking.spanningGraph
  have hsupportG : supportGraph ≤ G := by
    exact sup_le large.toPathPacking.spanningGraph_le
      small.toPathPacking.spanningGraph_le
  let smallSupport :
      EndpointCleanPathPacking supportGraph S T :=
    small.transfer supportGraph (by
      intro i e he
      apply _root_.SimpleGraph.edgeSet_mono
        (le_sup_right :
          small.toPathPacking.spanningGraph ≤ supportGraph)
      rw [PathPacking.spanningGraph,
        _root_.SimpleGraph.edgeSet_fromEdgeSet]
      constructor
      · have hePath : e ∈ (small.path i).edgeSet := by
          simpa [GraphPath.edgeSet] using he
        exact small.toPathPacking.path_edgeSet_subset_edgeSet i hePath
      · exact G.not_isDiag_of_mem_edgeSet
          ((small.path i).walk.edges_subset_edgeSet he))
  let Candidate :=
    {H : _root_.SimpleGraph V //
      H ≤ supportGraph ∧
        large.toPathPacking.spanningGraph ≤ H ∧
          ∃ P : EndpointCleanPathPacking H S T,
            P.sourceSet = small.sourceSet}
  let HasEdgeCount : ℕ → Prop := fun n =>
    ∃ H : Candidate, H.1.edgeSet.ncard = n
  have hExists : ∃ n : ℕ, HasEdgeCount n := by
    refine ⟨supportGraph.edgeSet.ncard,
      ⟨supportGraph, le_rfl, le_sup_left,
        smallSupport, ?_⟩, rfl⟩
    simp [smallSupport]
  let edgeMin := Nat.find hExists
  rcases Nat.find_spec hExists with ⟨Hmin, hHminCard⟩
  rcases Hmin.2.2.2 with ⟨Pmin, hPminSource⟩
  refine ⟨{
    H := Hmin.1
    le_original := Hmin.2.1.trans hsupportG
    support_le := Hmin.2.1
    large_support_le := Hmin.2.2.1
    smallPacking := Pmin
    small_sourceSet := hPminSource
    delete_nonlarge_edge_forbids_small := ?_ }⟩
  intro e heH hnotLarge hdelete
  rcases hdelete with ⟨Pdel, hPdelSource⟩
  let Hdel := Hmin.1.deleteEdges ({e} : Set (Sym2 V))
  have hlargeDel : large.toPathPacking.spanningGraph ≤ Hdel := by
    intro x y hxy
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨Hmin.2.2.1 hxy, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hxyEdge
    apply hnotLarge
    have hmemAnd :
        s(x, y) ∈ large.toPathPacking.edgeSet ∧ x ≠ y := by
      simpa [PathPacking.spanningGraph] using hxy
    have hmem : s(x, y) ∈ large.toPathPacking.edgeSet := hmemAnd.1
    simpa [hxyEdge] using hmem
  let HdelCandidate : Candidate :=
    ⟨Hdel,
      (_root_.SimpleGraph.deleteEdges_le
        ({e} : Set (Sym2 V))).trans Hmin.2.1,
      hlargeDel, Pdel, hPdelSource⟩
  have hDelCandidate : HasEdgeCount Hdel.edgeSet.ncard :=
    ⟨HdelCandidate, rfl⟩
  have hMinLe : edgeMin ≤ Hdel.edgeSet.ncard :=
    Nat.find_min' (H := hExists) hDelCandidate
  have hDelLt : Hdel.edgeSet.ncard < Hmin.1.edgeSet.ncard := by
    simpa [Hdel] using
      edgeSet_deleteEdges_singleton_ncard_lt Hmin.1 heH
  have hHminEdgeMin : Hmin.1.edgeSet.ncard = edgeMin := by
    simpa [edgeMin] using hHminCard
  rw [hHminEdgeMin] at hDelLt
  omega

/-- The original large family, transferred to the selected minimal support. -/
noncomputable def Lemma219MinimalSupport.largePacking
    {large small : EndpointCleanPathPacking G S T}
    (M : Lemma219MinimalSupport large small) :
    EndpointCleanPathPacking M.H S T :=
  large.transfer M.H (by
    classical
    intro i e he
    apply _root_.SimpleGraph.edgeSet_mono M.large_support_le
    rw [PathPacking.spanningGraph,
      _root_.SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · have hePath : e ∈ (large.path i).edgeSet := by
        simpa [GraphPath.edgeSet] using he
      exact large.toPathPacking.path_edgeSet_subset_edgeSet i hePath
    · exact G.not_isDiag_of_mem_edgeSet
        ((large.path i).walk.edges_subset_edgeSet he))

@[simp] theorem Lemma219MinimalSupport.largePacking_card
    {large small : EndpointCleanPathPacking G S T}
    (M : Lemma219MinimalSupport large small) :
    M.largePacking.card = large.card := rfl

@[simp] theorem Lemma219MinimalSupport.largePacking_sourceSet
    {large small : EndpointCleanPathPacking G S T}
    (M : Lemma219MinimalSupport large small) :
    M.largePacking.sourceSet = large.sourceSet := by
  simp [Lemma219MinimalSupport.largePacking]

/-- The decisive consequence of the Appendix A.3 deletion loop.  After
extending the small family inside the minimal support, every path whose origin
is not one of the retained small-family origins uses only edges of the
original large family.

Indeed, if such a path used a non-large edge `e`, all paths with retained
origins avoid `e` by node-disjointness.  They would survive in `H - e`,
contradicting the minimal-support property. -/
theorem Lemma219MinimalSupport.exists_rerouting_large_supported
    {large small : EndpointCleanPathPacking G S T}
    (M : Lemma219MinimalSupport large small)
    (hcard : small.card ≤ large.card) :
    ∃ rerouted : EndpointCleanPathPacking M.H S T,
      rerouted.card = large.card ∧
        small.sourceSet ⊆ rerouted.sourceSet ∧
          ∀ i : rerouted.Index,
            (rerouted.path i).source ∉ small.sourceSet →
              (rerouted.path i).edgeSet ⊆
                large.toPathPacking.edgeSet := by
  have hsmallCard : M.smallPacking.card = small.card := by
    calc
      M.smallPacking.card = M.smallPacking.sourceSet.card :=
        (EndpointCleanPathPacking.sourceSet_card M.smallPacking).symm
      _ = small.sourceSet.card := congrArg Finset.card M.small_sourceSet
      _ = small.card := EndpointCleanPathPacking.sourceSet_card small
  have hcardH : M.smallPacking.card ≤ M.largePacking.card := by
    simpa [hsmallCard] using hcard
  rcases exists_endpointClean_rerouting_retaining_sources
      M.largePacking M.smallPacking hcardH with
    ⟨rerouted, hreroutedCard, hretained, _htarget⟩
  have hsmallSub : small.sourceSet ⊆ rerouted.sourceSet := by
    rw [← M.small_sourceSet]
    exact hretained
  refine ⟨rerouted, by simpa using hreroutedCard, hsmallSub, ?_⟩
  intro i hiSource e he
  by_contra heLarge
  have heH : e ∈ M.H.edgeSet :=
    GraphPath.edgeSet_subset_edgeSet (rerouted.path i)
      (by simpa using he)
  apply M.delete_nonlarge_edge_forbids_small heH heLarge
  let retained :=
    rerouted.restrictSources small.sourceSet
  have hretainedSource : retained.sourceSet = small.sourceSet :=
    rerouted.restrictSources_sourceSet_eq small.sourceSet hsmallSub
  let retainedDeleted :
      EndpointCleanPathPacking
        (M.H.deleteEdges ({e} : Set (Sym2 V))) S T :=
    retained.transfer
      (M.H.deleteEdges ({e} : Set (Sym2 V))) (by
        intro j f hf
        rw [_root_.SimpleGraph.edgeSet_deleteEdges]
        constructor
        · exact (retained.path j).walk.edges_subset_edgeSet hf
        · simp only [Set.mem_singleton_iff]
          intro hfe
          have hfEdge : f ∈ (retained.path j).edgeSet := by
            simpa [GraphPath.edgeSet] using hf
          have hjSource :
              (rerouted.path j.1).source ∈ small.sourceSet :=
            (Finset.mem_filter.mp j.2).2
          have hji : j.1 ≠ i := by
            intro hji
            apply hiSource
            simpa [hji] using hjSource
          have heout : s(e.out.1, e.out.2) = e := by
            rw [Sym2.mk, e.out_eq]
          have hiVertex :
              e.out.1 ∈ (rerouted.path i).vertexSet := by
            have he' :
                s(e.out.1, e.out.2) ∈
                  (rerouted.path i).edgeSet := by
              rw [heout]
              exact he
            exact
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (rerouted.path i) he').1
          have hjVertex :
              e.out.1 ∈ (rerouted.path j.1).vertexSet := by
            have hfEq : f = e := hfe
            have :
                s(e.out.1, e.out.2) ∈
                  (rerouted.path j.1).edgeSet := by
              simpa [retained, EndpointCleanPathPacking.restrictSources,
                hfEq, heout] using hfEdge
            exact
              (GraphPath.endpoints_mem_vertexSet_of_edgeSet
                (rerouted.path j.1) this).1
          exact Finset.disjoint_left.mp
            (rerouted.node_disjoint hji.symm) hiVertex hjVertex)
  exact ⟨retainedDeleted, by
    simpa [retainedDeleted] using hretainedSource⟩

/-- A large-supported path in the rerouted family whose origin is outside the
small origin class is one of the original large paths.

This is the last step in Appendix A.3: node-disjointness prevents a supported
path from moving between members of the large family, endpoint cleanliness
identifies its far endpoint, and uniqueness of a subpath between the two
endpoints identifies the whole original path. -/
theorem Lemma219MinimalSupport.rerouted_path_eq_large_path
    {U₁ U₂ : Finset V}
    {large small :
      EndpointCleanPathPacking G (U₁ ∪ U₂) T}
    (M : Lemma219MinimalSupport large small)
    (hlargeSources : large.sourceSet = U₁)
    (hsmallSources : small.sourceSet = U₂)
    (rerouted :
      EndpointCleanPathPacking M.H (U₁ ∪ U₂) T)
    (hsupported :
      ∀ i : rerouted.Index,
        (rerouted.path i).source ∉ small.sourceSet →
          (rerouted.path i).edgeSet ⊆
            large.toPathPacking.edgeSet)
    (i : rerouted.Index)
    (hi : (rerouted.path i).source ∉ U₂) :
    ∃ r : large.Index,
      (rerouted.path i).vertexSet =
        (M.largePacking.path r).vertexSet := by
  classical
  have hiUnion :
      (rerouted.path i).source ∈ U₁ ∪ U₂ :=
    (rerouted.endpoint_clean i).source_mem
  have hiU₁ : (rerouted.path i).source ∈ U₁ := by
    rcases Finset.mem_union.mp hiUnion with hiU₁ | hiU₂
    · exact hiU₁
    · exact False.elim (hi hiU₂)
  have hiLarge :
      (rerouted.path i).source ∈ M.largePacking.sourceSet := by
    simpa [M.largePacking_sourceSet, hlargeSources] using hiU₁
  rcases M.largePacking.exists_index_source_eq_of_mem_sourceSet
      hiLarge with ⟨r, hrSource⟩
  have hiNotSmall :
      (rerouted.path i).source ∉ small.sourceSet := by
    simpa [hsmallSources] using hi
  have hQedgeUnion :
      (rerouted.path i).edgeSet ⊆
        M.largePacking.toPathPacking.edgeSet := by
    simpa [Lemma219MinimalSupport.largePacking] using
      hsupported i hiNotSmall
  have hsourceMem :
      (rerouted.path i).source ∈
        (M.largePacking.path r).vertexSet := by
    rw [← hrSource]
    exact GraphPath.source_mem_vertexSet (M.largePacking.path r)
  have hQvertex :
      (rerouted.path i).vertexSet ⊆
        (M.largePacking.path r).vertexSet :=
    M.largePacking.toPathPacking
      |>.path_vertexSet_subset_of_edgeSet_subset_of_source_mem
        (rerouted.path i) r hQedgeUnion hsourceMem
  have hQedge :
      (rerouted.path i).edgeSet ⊆
        (M.largePacking.path r).edgeSet :=
    M.largePacking.toPathPacking
      |>.path_edgeSet_subset_of_edgeSet_subset_of_source_mem
        (rerouted.path i) r hQedgeUnion hsourceMem
  have hrTarget :
      (rerouted.path i).target =
        (M.largePacking.path r).target := by
    exact (M.largePacking.endpoint_clean r).right_eq_target
      (hQvertex (GraphPath.target_mem_vertexSet (rerouted.path i)))
      ((rerouted.endpoint_clean i).target_mem)
  have hreverse :
      (M.largePacking.path r).vertexSet ⊆
        (rerouted.path i).vertexSet := by
    exact AppendixB1.GraphPath.vertexSet_subset_of_edgeSet_subset_same_endpoints
      (M.largePacking.path r)
      (M.largePacking.path r)
      (rerouted.path i)
      (by exact fun _ h => h)
      (by exact fun _ h => h)
      hQvertex
      hQedge
      hrSource
      hrTarget.symm
  exact ⟨r, Finset.Subset.antisymm hQvertex hreverse⟩

/-- Chekuri--Chuzhoy Lemma 2.19, in the uncontracted endpoint-clean form used
by the many-leaves induction.

The rerouted family keeps every small-family origin.  Its other paths are
literal members of the original large family.  The displayed cardinality
identity is the reserve accounting needed in Step 2. -/
theorem exists_lemma219_rerouting
    {U₁ U₂ : Finset V}
    (large small :
      EndpointCleanPathPacking G (U₁ ∪ U₂) T)
    (hlargeSources : large.sourceSet = U₁)
    (hsmallSources : small.sourceSet = U₂)
    (hdisjoint : Disjoint U₁ U₂)
    (hcard : small.card ≤ large.card) :
    ∃ rerouted :
        EndpointCleanPathPacking G (U₁ ∪ U₂) T,
      rerouted.card = large.card ∧
        U₂ ⊆ rerouted.sourceSet ∧
          (rerouted.sourceSet ∩ U₁).card + small.card =
            large.card ∧
            rerouted.toPathPacking.edgeSet ⊆
              large.toPathPacking.edgeSet ∪
                small.toPathPacking.edgeSet ∧
            ∀ i : rerouted.Index,
              (rerouted.path i).source ∈ U₁ →
                ∃ r : large.Index,
                  (rerouted.path i).vertexSet =
                    (large.path r).vertexSet := by
  classical
  rcases exists_lemma219MinimalSupport large small with ⟨M⟩
  rcases M.exists_rerouting_large_supported hcard with
    ⟨R, hRcard, hU₂R, hsupported⟩
  let R' : EndpointCleanPathPacking G (U₁ ∪ U₂) T :=
    R.transfer G (by
      intro i e he
      exact _root_.SimpleGraph.edgeSet_mono M.le_original
        ((R.path i).walk.edges_subset_edgeSet he))
  have hR'card : R'.card = large.card := by
    simpa [R'] using hRcard
  have hU₂R' : U₂ ⊆ R'.sourceSet := by
    intro v hv
    have hvSmall : v ∈ small.sourceSet := by
      simpa [hsmallSources] using hv
    simpa [R'] using hU₂R hvSmall
  have hsourceSub : R'.sourceSet ⊆ U₁ ∪ U₂ :=
    R'.sourceSet_subset_left
  have hsplit :
      R'.sourceSet =
        (R'.sourceSet ∩ U₁) ∪ (R'.sourceSet ∩ U₂) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp (hsourceSub hv) with hv₁ | hv₂
      · exact Finset.mem_union_left _
          (Finset.mem_inter.2 ⟨hv, hv₁⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.2 ⟨hv, hv₂⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).1
      · exact (Finset.mem_inter.mp hv).1
  have hinterDisj :
      Disjoint (R'.sourceSet ∩ U₁)
        (R'.sourceSet ∩ U₂) := by
    exact Finset.disjoint_left.2 (by
      intro v hv₁ hv₂
      exact Finset.disjoint_left.mp hdisjoint
        (Finset.mem_inter.mp hv₁).2
        (Finset.mem_inter.mp hv₂).2)
  have hinterU₂ : R'.sourceSet ∩ U₂ = U₂ :=
    Finset.inter_eq_right.mpr hU₂R'
  have hcount :
      (R'.sourceSet ∩ U₁).card + small.card =
        large.card := by
    have hcardSplit :
        R'.sourceSet.card =
          (R'.sourceSet ∩ U₁).card +
            (R'.sourceSet ∩ U₂).card := by
      calc
        R'.sourceSet.card =
            ((R'.sourceSet ∩ U₁) ∪
              (R'.sourceSet ∩ U₂)).card :=
          congrArg Finset.card hsplit
        _ = (R'.sourceSet ∩ U₁).card +
              (R'.sourceSet ∩ U₂).card :=
          Finset.card_union_of_disjoint hinterDisj
    have hsmallCard : U₂.card = small.card := by
      calc
        U₂.card = small.sourceSet.card :=
          congrArg Finset.card hsmallSources.symm
        _ = small.card := EndpointCleanPathPacking.sourceSet_card small
    have hRsourceCard : R'.sourceSet.card = large.card := by
      rw [EndpointCleanPathPacking.sourceSet_card, hR'card]
    calc
      (R'.sourceSet ∩ U₁).card + small.card =
          (R'.sourceSet ∩ U₁).card + U₂.card := by
            rw [hsmallCard]
      _ = (R'.sourceSet ∩ U₁).card +
          (R'.sourceSet ∩ U₂).card := by
            rw [hinterU₂]
      _ = R'.sourceSet.card := hcardSplit.symm
      _ = large.card := hRsourceCard
  have hsupport :
      R'.toPathPacking.edgeSet ⊆
        large.toPathPacking.edgeSet ∪
          small.toPathPacking.edgeSet := by
    intro e he
    rcases R'.toPathPacking.mem_edgeSet.mp he with ⟨i, hie⟩
    have hieR : e ∈ (R.path i).edgeSet := by
      change e ∈ ((R.path i).transfer G _).edgeSet at hie
      simpa using hie
    have heH : e ∈ M.H.edgeSet := by
      exact GraphPath.edgeSet_subset_edgeSet (R.path i)
        (by simpa [GraphPath.edgeSet] using hieR)
    have heSupport :=
      _root_.SimpleGraph.edgeSet_mono M.support_le heH
    simp only [_root_.SimpleGraph.edgeSet_sup,
      PathPacking.spanningGraph,
      _root_.SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_union] at heSupport
    rcases heSupport with heLarge | heSmall
    · exact Finset.mem_union_left _ heLarge.1
    · exact Finset.mem_union_right _ heSmall.1
  refine ⟨R', hR'card, hU₂R', hcount, hsupport, ?_⟩
  intro i hiU₁
  have hiNotU₂ : (R.path i).source ∉ U₂ := by
    intro hiU₂
    exact Finset.disjoint_left.mp hdisjoint hiU₁ hiU₂
  rcases M.rerouted_path_eq_large_path
      hlargeSources hsmallSources R hsupported i hiNotU₂ with
    ⟨r, hr⟩
  refine ⟨r, ?_⟩
  calc
    (R'.path i).vertexSet = (R.path i).vertexSet := by
      simp [R']
    _ = (M.largePacking.path r).vertexSet := hr
    _ = (large.path r).vertexSet := by
      simp [Lemma219MinimalSupport.largePacking]

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
