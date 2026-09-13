import Lax17Proofs.Source.ChekuriChuzhoySection5DensePartition
import Lax17Proofs.Source.ChekuriChuzhoySection5Routers
import Lax17Proofs.Source.ChekuriChuzhoySection5Descent
import Lax17Proofs.Source.HindOellermann

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 router production

This module begins the concrete production chain behind journal Section 5.
It constructs the legal contracted named multigraph of a vertex clustering
without losing the original edge copy.  The named-edge presentation is the
bridge from the clustering descent to Claim 5.9 and to the split/delete/
contract arguments used in failed-router elimination.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RouterProduction


open Finset
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A vertex of the legal contracted graph is one block of the clustering. -/
abbrev ContractedVertex (P : VertexClustering V) :=
  {C : Finset V // C ∈ P.parts}

/-- The contracted vertex containing an original vertex. -/
def contractedVertex (P : VertexClustering V) (v : V) : ContractedVertex P :=
  ⟨P.block v, P.block_mem_parts v⟩

@[simp] theorem contractedVertex_val (P : VertexClustering V) (v : V) :
    (contractedVertex P v).1 = P.block v := rfl

/-- Choose an endpoint ordering for an unordered edge.  The choice is used
only as bookkeeping; `sym2_mk_chosenEndpoints` proves that it represents the
original unordered edge. -/
noncomputable def chosenLeft (e : Sym2 V) : V := (Quot.out e).1

noncomputable def chosenRight (e : Sym2 V) : V := (Quot.out e).2

theorem sym2_mk_chosenEndpoints (e : Sym2 V) :
    s(chosenLeft e, chosenRight e) = e := by
  exact Quot.out_eq e

/-- A universe-zero name for each cross-block original edge.  The underlying
`FiniteEdgeIndexedGraph` intentionally requires edge names in `Type 0`, so a
finite ordinal is used even when the original vertex type is universe
polymorphic. -/
abbrev LegalContractedEdgeIndex (G : _root_.SimpleGraph V)
    (P : VertexClustering V) :=
  Fin (crossBlockOriginalEdges G P).card

/-- Recover the original edge represented by a legal contracted edge name. -/
noncomputable def indexedOriginalEdge
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (e : LegalContractedEdgeIndex G P) : Sym2 V :=
  ((Finset.equivFin (crossBlockOriginalEdges G P)).symm e).val

theorem indexedOriginalEdge_mem_crossBlock
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (e : LegalContractedEdgeIndex G P) :
    indexedOriginalEdge G P e ∈ crossBlockOriginalEdges G P :=
  ((Finset.equivFin (crossBlockOriginalEdges G P)).symm e).property

theorem indexedOriginalEdge_injective
    (G : _root_.SimpleGraph V) (P : VertexClustering V) :
    Function.Injective (indexedOriginalEdge G P) := by
  intro e f hef
  apply (Finset.equivFin (crossBlockOriginalEdges G P)).symm.injective
  exact Subtype.ext hef

theorem indexedOriginalEdge_surjective_crossBlock
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    {e : Sym2 V} (he : e ∈ crossBlockOriginalEdges G P) :
    ∃ i : LegalContractedEdgeIndex G P, indexedOriginalEdge G P i = e := by
  let x : {e // e ∈ crossBlockOriginalEdges G P} := ⟨e, he⟩
  refine ⟨Finset.equivFin (crossBlockOriginalEdges G P) x, ?_⟩
  exact congrArg Subtype.val
    ((Finset.equivFin (crossBlockOriginalEdges G P)).symm_apply_apply x)

noncomputable def legalContractedEdgeLeft
    (P : VertexClustering V) (e : LegalContractedEdgeIndex G P) :
    ContractedVertex P := contractedVertex P (chosenLeft (indexedOriginalEdge G P e))

noncomputable def legalContractedEdgeRight
    (P : VertexClustering V) (e : LegalContractedEdgeIndex G P) :
    ContractedVertex P := contractedVertex P (chosenRight (indexedOriginalEdge G P e))

theorem legalContractedEdge_end_ne
    (P : VertexClustering V) (e : LegalContractedEdgeIndex G P) :
    legalContractedEdgeLeft P e ≠ legalContractedEdgeRight P e := by
  have hcross := ((mem_crossBlockOriginalEdges (G := G) P
    (indexedOriginalEdge G P e)).1 (indexedOriginalEdge_mem_crossBlock G P e)).2
  have hout := sym2_mk_chosenEndpoints (indexedOriginalEdge G P e)
  rw [← hout, crossesBlocks_mk] at hcross
  intro heq
  exact hcross (congrArg Subtype.val heq)

/-- The legal contracted multigraph.  Parallel copies arise when distinct
original edges join the same two blocks, and remain distinct through the
subtype edge index. -/
noncomputable def legalContractedGraph
    (G : _root_.SimpleGraph V) (P : VertexClustering V) :
    FiniteEdgeIndexedGraph (ContractedVertex P) where
  Edge := LegalContractedEdgeIndex G P
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  left := legalContractedEdgeLeft P
  right := legalContractedEdgeRight P
  end_ne := legalContractedEdge_end_ne P

/-- Forgetting the contracted edge subtype returns its unique original edge
copy. -/
noncomputable def legalContractedOrigin
    (G : _root_.SimpleGraph V) (P : VertexClustering V) :
    (legalContractedGraph G P).Edge → Sym2 V := indexedOriginalEdge G P

theorem legalContractedOrigin_injective
    (G : _root_.SimpleGraph V) (P : VertexClustering V) :
    Function.Injective (legalContractedOrigin G P) := by
  exact indexedOriginalEdge_injective G P

theorem legalContractedOrigin_mem_edgeFinset
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (e : (legalContractedGraph G P).Edge) :
    legalContractedOrigin G P e ∈ G.edgeFinset := by
  exact crossBlockOriginalEdges_subset_edgeFinset (G := G) P
    (indexedOriginalEdge_mem_crossBlock G P e)

@[simp] theorem legalContracted_left
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (e : (legalContractedGraph G P).Edge) :
    (legalContractedGraph G P).left e =
      contractedVertex P (chosenLeft (legalContractedOrigin G P e)) := rfl

@[simp] theorem legalContracted_right
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (e : (legalContractedGraph G P).Edge) :
    (legalContractedGraph G P).right e =
      contractedVertex P (chosenRight (legalContractedOrigin G P e)) := rfl

/-- Complete original-edge provenance for one legal contracted edge. -/
theorem legalContractedEdge_provenance
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (e : (legalContractedGraph G P).Edge) :
    legalContractedOrigin G P e ∈ G.edgeFinset ∧
      s(chosenLeft (legalContractedOrigin G P e),
        chosenRight (legalContractedOrigin G P e)) = legalContractedOrigin G P e ∧
      chosenLeft (legalContractedOrigin G P e) ∈
        ((legalContractedGraph G P).left e).1 ∧
      chosenRight (legalContractedOrigin G P e) ∈
        ((legalContractedGraph G P).right e).1 := by
  refine ⟨legalContractedOrigin_mem_edgeFinset G P e,
    sym2_mk_chosenEndpoints (legalContractedOrigin G P e), ?_, ?_⟩
  · exact P.mem_block _
  · exact P.mem_block _

/-- Incidence in the contracted multigraph is exactly membership of the
original edge copy in the original boundary of the corresponding block. -/
theorem mem_legalContracted_incidentEdges_iff
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (C : ContractedVertex P) (e : (legalContractedGraph G P).Edge) :
    e ∈ (legalContractedGraph G P).incidentEdges C ↔
      legalContractedOrigin G P e ∈ originalBoundary G C.1 := by
  let a := chosenLeft (legalContractedOrigin G P e)
  let b := chosenRight (legalContractedOrigin G P e)
  have horigin : legalContractedOrigin G P e = s(a, b) :=
    (sym2_mk_chosenEndpoints (legalContractedOrigin G P e)).symm
  have hedge : legalContractedOrigin G P e ∈ G.edgeSet := by
    simpa [_root_.SimpleGraph.mem_edgeFinset] using
      legalContractedOrigin_mem_edgeFinset G P e
  have hblocks : P.block a ≠ P.block b := by
    have hcross := ((mem_crossBlockOriginalEdges (G := G) P
      (indexedOriginalEdge G P e)).1
        (indexedOriginalEdge_mem_crossBlock G P e)).2
    rw [← sym2_mk_chosenEndpoints (indexedOriginalEdge G P e)] at hcross
    simpa [a, b, legalContractedOrigin] using hcross
  constructor
  · intro hinc
    rcases ((legalContractedGraph G P).mem_incidentEdges C e).1 hinc with hleft | hright
    · have haC : a ∈ C.1 := by
        have : P.block a = C.1 := congrArg Subtype.val hleft
        exact this ▸ P.mem_block a
      have hbC : b ∉ C.1 := by
        intro hb
        have hbBlock : P.block b = C.1 := P.block_eq_of_mem C.2 hb
        exact hblocks ((P.block_eq_of_mem C.2 haC).trans hbBlock.symm)
      exact mem_originalBoundary_iff.mpr
        ⟨hedge, a, haC, b, hbC, horigin⟩
    · have hbC : b ∈ C.1 := by
        have : P.block b = C.1 := congrArg Subtype.val hright
        exact this ▸ P.mem_block b
      have haC : a ∉ C.1 := by
        intro ha
        have haBlock : P.block a = C.1 := P.block_eq_of_mem C.2 ha
        exact hblocks (haBlock.trans (P.block_eq_of_mem C.2 hbC).symm)
      exact mem_originalBoundary_iff.mpr
        ⟨hedge, b, hbC, a, haC, by simpa [Sym2.eq_swap] using horigin⟩
  · intro hboundary
    rcases mem_originalBoundary_iff.mp hboundary with
      ⟨_, u, huC, v, hvC, heuv⟩
    have habuv : s(a, b) = s(u, v) := horigin.symm.trans heuv
    rcases Sym2.eq_iff.mp habuv with hab | hab
    · have haC : a ∈ C.1 := hab.1 ▸ huC
      apply ((legalContractedGraph G P).mem_incidentEdges C e).2
      left
      apply Subtype.ext
      exact P.block_eq_of_mem C.2 haC
    · have hbC : b ∈ C.1 := hab.2 ▸ huC
      apply ((legalContractedGraph G P).mem_incidentEdges C e).2
      right
      apply Subtype.ext
      exact P.block_eq_of_mem C.2 hbC

/-- The provenance map identifies the contracted incidence set with the
original boundary, including every parallel edge copy separately. -/
theorem image_legalContracted_incidentEdges
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (C : ContractedVertex P) :
    ((legalContractedGraph G P).incidentEdges C).image
        (legalContractedOrigin G P) = originalBoundary G C.1 := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    exact (mem_legalContracted_incidentEdges_iff G P C i).1 hi
  · intro he
    have hcross := originalBoundary_subset_crossBlockOriginalEdges
      (G := G) P C.2 he
    obtain ⟨i, hi⟩ := indexedOriginalEdge_surjective_crossBlock G P hcross
    apply Finset.mem_image.mpr
    refine ⟨i, (mem_legalContracted_incidentEdges_iff G P C i).2 ?_, hi⟩
    simpa [legalContractedOrigin, hi] using he

/-- Contracted degree is exactly the number of original boundary edges of
the represented cluster. -/
theorem legalContracted_degree_eq_originalBoundary_card
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (C : ContractedVertex P) :
    (legalContractedGraph G P).degree C = (originalBoundary G C.1).card := by
  classical
  rw [← image_legalContracted_incidentEdges G P C,
    Finset.card_image_of_injective _ (legalContractedOrigin_injective G P)]
  rfl

/-! ## Good-clustering degree bridge and Claim 5.9 -/

/-- The terminal vertices of the legal contracted graph.  Under an acceptable
clustering, every original terminal has its own singleton contracted vertex. -/
noncomputable def contractedTerminals
    (P : VertexClustering V) (terminals : Finset V) :
    Finset (ContractedVertex P) :=
  terminals.image (contractedVertex P)

theorem mem_contractedTerminals
    (P : VertexClustering V) (terminals : Finset V)
    (C : ContractedVertex P) :
    C ∈ contractedTerminals P terminals ↔
      ∃ t ∈ terminals, contractedVertex P t = C := by
  classical
  simp [contractedTerminals]

/-- Distinct original terminals remain distinct after contraction because an
acceptable clustering isolates each terminal in its own singleton block. -/
theorem contractedVertex_injective_on_terminals_of_isAcceptable
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hacceptable : IsAcceptable G terminals threshold cap alphaNum alphaDen P)
    {s t : V} (hs : s ∈ terminals) (ht : t ∈ terminals)
    (hcontracted : contractedVertex P s = contractedVertex P t) :
    s = t := by
  have hblocks : P.block s = P.block t := congrArg Subtype.val hcontracted
  rw [hacceptable.terminal_block_eq_singleton hs,
    hacceptable.terminal_block_eq_singleton ht] at hblocks
  exact Finset.singleton_inj.mp hblocks

/-- Contracting the singleton terminal blocks preserves the terminal count. -/
theorem contractedTerminals_card_eq_of_isGood
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hgood : IsGood G terminals threshold cap alphaNum alphaDen P) :
    (contractedTerminals P terminals).card = terminals.card := by
  classical
  rw [contractedTerminals]
  apply Finset.card_image_of_injOn
  intro s hs t ht hcontracted
  exact contractedVertex_injective_on_terminals_of_isAcceptable hgood.1
    (by simpa using hs) (by simpa using ht) hcontracted

/-- Every cluster in a good clustering has contracted degree strictly below
the large-cluster threshold. -/
theorem legalContracted_degree_lt_of_isGood
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hgood : IsGood G terminals threshold cap alphaNum alphaDen P)
    (C : ContractedVertex P) :
    (legalContractedGraph G P).degree C < threshold := by
  rw [legalContracted_degree_eq_originalBoundary_card]
  exact hgood.2 C.1 C.2

/-- The weak maximum-degree form used by Claim 5.9 follows immediately from
the strict good-clustering boundary invariant. -/
theorem legalContracted_degree_le_of_isGood
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hgood : IsGood G terminals threshold cap alphaNum alphaDen P)
    (C : ContractedVertex P) :
    (legalContractedGraph G P).degree C ≤ threshold := by
  exact Nat.le_of_lt (legalContracted_degree_lt_of_isGood hgood C)

/-- The legal contracted graph satisfies the Claim 5.9 nonterminal
maximum-degree hypothesis whenever the clustering is good. -/
theorem legalContracted_claim59_maxDegree_of_isGood
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hgood : IsGood G terminals threshold cap alphaNum alphaDen P) :
    ∀ C ∈ nonterminalVertices (contractedTerminals P terminals),
      (legalContractedGraph G P).degree C ≤ threshold := by
  intro C _hC
  exact legalContracted_degree_le_of_isGood hgood C

/-- A pendant original terminal remains degree one in the legal contracted
graph once acceptability has made its cluster a singleton. -/
theorem legalContracted_pendant_degree_of_isGood
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hgood : IsGood G terminals threshold cap alphaNum alphaDen P)
    {t : V} (ht : t ∈ terminals)
    (hpendant : (originalBoundary G ({t} : Finset V)).card = 1) :
    (legalContractedGraph G P).degree (contractedVertex P t) = 1 := by
  rw [legalContracted_degree_eq_originalBoundary_card]
  simpa [hgood.1.terminal_block_eq_singleton ht] using hpendant

/-- The contracted image of pendant terminals has degree one. -/
theorem legalContracted_pendantTerminals_of_isGood
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hgood : IsGood G terminals threshold cap alphaNum alphaDen P)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary G ({t} : Finset V)).card = 1) :
    ∀ C ∈ contractedTerminals P terminals,
      (legalContractedGraph G P).degree C = 1 := by
  intro C hC
  rcases (mem_contractedTerminals P terminals C).mp hC with ⟨t, ht, rfl⟩
  exact legalContracted_pendant_degree_of_isGood hgood ht (hpendant t ht)

/-- Claim 5.9's deterministic moment hypotheses for the legal contracted
graph.  The good-clustering bridge supplies its degree field; the terminal
degree-one and `k <= 3m` inputs are the separate source invariants. -/
theorem legalContracted_claim59MomentHypotheses_of_isGood
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (hgood : IsGood G terminals threshold cap alphaNum alphaDen P)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary G ({t} : Finset V)).card = 1)
    (hterminalCard : (contractedTerminals P terminals).card ≤
      3 * (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card) :
    Claim59MomentHypotheses (legalContractedGraph G P)
      (contractedTerminals P terminals) threshold := by
  exact claim59MomentHypotheses_of_pendantTerminals
    (legalContractedGraph G P) (contractedTerminals P terminals) threshold
    (legalContracted_claim59_maxDegree_of_isGood hgood)
    (legalContracted_pendantTerminals_of_isGood hgood hpendant)
    hterminalCard

/-- Concrete journal Claim 5.9 for a legal contracted graph from a good
clustering.  This is the source-parameter form: its degree cap is exactly
`w0 = floor (k / (192 ell0^3 log k))`. -/
theorem exists_densePartition_of_goodClustering_source_parameters
    {terminals : Finset V} {cap alphaNum alphaDen ell0 : ℕ}
    {P : VertexClustering V}
    (hell0 : 0 < ell0)
    (hgood : IsGood G terminals
      (claim59SourceDegreeCap (contractedTerminals P terminals).card ell0)
      cap alphaNum alphaDen P)
    (hterminalTwo : 2 ≤ terminals.card)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary G ({t} : Finset V)).card = 1)
    (hterminalCard : terminals.card ≤
      3 * (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card) :
    ∃ blocks : Fin ell0 -> Finset (ContractedVertex P),
      (forall j, blocks j ⊆ Finset.univ \ contractedTerminals P terminals) ∧
      (forall C, C ∉ contractedTerminals P terminals -> ∃! j, C ∈ blocks j) ∧
      (forall i j, i ≠ j -> Disjoint (blocks i) (blocks j)) ∧
      (forall j, ell0 * ((legalContractedGraph G P).boundary (blocks j)).card <
        10 * (nonterminalEdges (legalContractedGraph G P)
          (contractedTerminals P terminals)).card) ∧
      (forall j, (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card ≤
        2 * ell0 ^ 2 * (internalEdges (legalContractedGraph G P)
          (blocks j)).card) := by
  have hterminalCard' : (contractedTerminals P terminals).card ≤
      3 * (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card := by
    rw [contractedTerminals_card_eq_of_isGood hgood]
    exact hterminalCard
  have hterminalTwo' : 2 ≤ (contractedTerminals P terminals).card := by
    rw [contractedTerminals_card_eq_of_isGood hgood]
    exact hterminalTwo
  exact exists_densePartition_of_pendant_source_parameters
    (legalContractedGraph G P) (contractedTerminals P terminals) ell0 hell0
    hterminalTwo'
    (legalContracted_claim59_maxDegree_of_isGood hgood)
    (legalContracted_pendantTerminals_of_isGood hgood hpendant)
    hterminalCard'

end ChekuriChuzhoySection5RouterProduction
end SimpleGraph

end Lax17Proofs
