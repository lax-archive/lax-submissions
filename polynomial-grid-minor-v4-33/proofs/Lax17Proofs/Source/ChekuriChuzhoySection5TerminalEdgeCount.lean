import Lax17Proofs.Source.ChekuriChuzhoySection5DenseBlockReplacement
import Lax17Proofs.Source.MaderEvenCore

namespace Lax17Proofs

universe u v w

/-!
# Terminal edge count in a legal contracted graph

This module formalizes preprint Claim 5.1, which is journal Claim 5.3 in
Chekuri--Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*.

The paper groups pendant terminals by their common neighbor in the legal
contracted multigraph, takes two balanced unions of whole groups, and routes
between them using node-well-linkedness.  Here the routing argument is phrased
as a cut count.  A union of whole neighbor groups, together with their
neighbors, has no terminal edge in its boundary.  Node-well-linkedness forces
the corresponding original cut to contain at least `ceil (k / 3)` edges, all
of which therefore come from nonterminal named edges of the legal contracted
graph.

The explicit terminal-independence premise is part of the pendant
normalization: fresh pendant leaves have old vertices as their unique
neighbors.  Degree one alone would not exclude an isolated edge joining two
terminals when there are only two terminals.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalEdgeCount


open Finset
open ChekuriChuzhoySection5BandwidthDecomposition
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5DenseBlockReplacement
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5RouterProduction
open ChekuriChuzhoySection5Routers
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

/-! ## The finite balancing step -/

/-- A finite family whose fibers have size at most `r` has a union of whole
fibers with at least `q` elements on each side, provided
`2 * q + r <= |T| + 1`.

The proof chooses a cardinality-minimal set of labels covering at least `q`
elements.  Removing one represented label leaves fewer than `q` elements,
while putting that one fiber back adds at most `r`. -/
private theorem exists_balanced_fiber_labels
    {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]
    (T : Finset A) (label : A → B) (q r : Nat)
    (hq : 0 < q) (hbalance : 2 * q + r ≤ T.card + 1)
    (hfiber : ∀ b ∈ T.image label,
      (T.filter fun a => label a = b).card ≤ r) :
    ∃ labels : Finset B,
      labels ⊆ T.image label ∧
      q ≤ (T.filter fun a => label a ∈ labels).card ∧
      q ≤ (T.filter fun a => label a ∉ labels).card := by
  classical
  let covered : Finset B → Finset A :=
    fun labels => T.filter fun a => label a ∈ labels
  let candidates : Finset (Finset B) :=
    (T.image label).powerset.filter fun labels =>
      q ≤ (covered labels).card
  have hfull : covered (T.image label) = T := by
    ext a
    constructor
    · intro ha
      exact (mem_filter.mp ha).1
    · intro ha
      apply mem_filter.mpr
      exact ⟨ha, mem_image.mpr ⟨a, ha, rfl⟩⟩
  have hcandidates : candidates.Nonempty := by
    refine ⟨T.image label, ?_⟩
    simp only [candidates, mem_filter, mem_powerset, subset_rfl, true_and]
    rw [hfull]
    omega
  rcases candidates.exists_min_image Finset.card hcandidates with
    ⟨labels, hlabelsCandidate, hminimal⟩
  have hlabelsSubset : labels ⊆ T.image label := by
    exact mem_powerset.mp (mem_filter.mp hlabelsCandidate).1
  have hcoveredLower : q ≤ (covered labels).card := by
    exact (mem_filter.mp hlabelsCandidate).2
  have hlabelsNonempty : labels.Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    subst labels
    simp [covered] at hcoveredLower
    omega
  rcases hlabelsNonempty with ⟨b, hb⟩
  have heraseUpper : (covered (labels.erase b)).card < q := by
    by_contra hnot
    have heraseLower : q ≤ (covered (labels.erase b)).card :=
      Nat.le_of_not_gt hnot
    have heraseCandidate : labels.erase b ∈ candidates := by
      apply mem_filter.mpr
      exact ⟨mem_powerset.mpr
        ((erase_subset b labels).trans hlabelsSubset), heraseLower⟩
    have hcard := hminimal (labels.erase b) heraseCandidate
    have heraseCard : (labels.erase b).card < labels.card :=
      card_erase_lt_of_mem hb
    omega
  have hcoveredSubset :
      covered labels ⊆
        covered (labels.erase b) ∪
          T.filter fun a => label a = b := by
    intro a ha
    have ha' := mem_filter.mp ha
    by_cases hab : label a = b
    · exact mem_union_right _ (mem_filter.mpr ⟨ha'.1, hab⟩)
    · apply mem_union_left
      apply mem_filter.mpr
      exact ⟨ha'.1, mem_erase.mpr ⟨hab, ha'.2⟩⟩
  have hcoveredUpper : (covered labels).card < q + r := by
    calc
      (covered labels).card
          ≤ (covered (labels.erase b) ∪
              T.filter fun a => label a = b).card :=
        card_le_card hcoveredSubset
      _ ≤ (covered (labels.erase b)).card +
            (T.filter fun a => label a = b).card :=
        card_union_le _ _
      _ < q + r := Nat.add_lt_add_of_lt_of_le heraseUpper
        (hfiber b (hlabelsSubset hb))
  have hcoveredSubsetT : covered labels ⊆ T := by
    intro a ha
    exact (mem_filter.mp ha).1
  have hcomplementLower : q ≤ (T \ covered labels).card := by
    rw [card_sdiff, inter_eq_left.mpr hcoveredSubsetT]
    omega
  refine ⟨labels, hlabelsSubset, ?_, ?_⟩
  · simpa [covered] using hcoveredLower
  · have hfilter :
        T.filter (fun a => label a ∉ labels) = T \ covered labels := by
      ext a
      constructor
      · intro ha
        have ha' := mem_filter.mp ha
        apply mem_sdiff.mpr
        refine ⟨ha'.1, ?_⟩
        intro hacovered
        exact ha'.2 (mem_filter.mp hacovered).2
      · intro ha
        have ha' := mem_sdiff.mp ha
        apply mem_filter.mpr
        refine ⟨ha'.1, ?_⟩
        intro halabel
        exact ha'.2 (mem_filter.mpr ⟨ha'.1, halabel⟩)
    rw [hfilter]
    exact hcomplementLower

/-! ## Pendant edges in a named multigraph -/

section Pendant

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The unique named edge incident with a degree-one terminal. -/
private noncomputable def pendantEdge
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (t : {w : W // w ∈ terminals}) : H.Edge :=
  Classical.choose (by
    have hcard : (H.incidentEdges t.1).card = 1 := by
      simpa [FiniteEdgeIndexedGraph.degree] using hpendant t.1 t.2
    exact Finset.card_pos.mp (by omega : 0 < (H.incidentEdges t.1).card))

private theorem pendantEdge_mem
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (t : {w : W // w ∈ terminals}) :
    pendantEdge H terminals hpendant t ∈ H.incidentEdges t.1 := by
  exact Classical.choose_spec (by
    have hcard : (H.incidentEdges t.1).card = 1 := by
      simpa [FiniteEdgeIndexedGraph.degree] using hpendant t.1 t.2
    exact Finset.card_pos.mp (by omega : 0 < (H.incidentEdges t.1).card))

private theorem eq_pendantEdge_of_incident
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (t : {w : W // w ∈ terminals}) {e : H.Edge}
    (he : e ∈ H.incidentEdges t.1) :
    e = pendantEdge H terminals hpendant t := by
  have hcard : (H.incidentEdges t.1).card = 1 := by
    simpa [FiniteEdgeIndexedGraph.degree] using hpendant t.1 t.2
  rcases card_eq_one.mp hcard with ⟨f, hf⟩
  have heq : e = f := by simpa [hf] using he
  have hp : pendantEdge H terminals hpendant t = f := by
    simpa [hf] using pendantEdge_mem H terminals hpendant t
  exact heq.trans hp.symm

/-- The common-neighbor label used in Claim 5.3. -/
private noncomputable def terminalNeighbor
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (t : {w : W // w ∈ terminals}) : W :=
  H.otherEndpointAt t.1 (pendantEdge H terminals hpendant t)

private theorem terminalNeighbor_ne_center
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (t : {w : W // w ∈ terminals}) :
    terminalNeighbor H terminals hpendant t ≠ t.1 := by
  exact H.otherEndpointAt_ne_center
    (pendantEdge_mem H terminals hpendant t)

private theorem terminalNeighbor_not_mem
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (hnoTerminalEdge :
      ∀ e : H.Edge, ¬ (H.left e ∈ terminals ∧ H.right e ∈ terminals))
    (t : {w : W // w ∈ terminals}) :
    terminalNeighbor H terminals hpendant t ∉ terminals := by
  intro hneighbor
  let e := pendantEdge H terminals hpendant t
  have hends := H.otherEndpointAt_ends
    (pendantEdge_mem H terminals hpendant t)
  rcases hends with hends | hends
  · exact hnoTerminalEdge e
      ⟨hends.1 ▸ t.2, hends.2 ▸ hneighbor⟩
  · exact hnoTerminalEdge e
      ⟨hends.2 ▸ hneighbor, hends.1 ▸ t.2⟩

private theorem pendantEdge_injective_on_neighbor_fiber
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    {s t : {w : W // w ∈ terminals}}
    (hneighbors :
      terminalNeighbor H terminals hpendant s =
        terminalNeighbor H terminals hpendant t)
    (hedges :
      pendantEdge H terminals hpendant s =
        pendantEdge H terminals hpendant t) :
    s = t := by
  have hsEnds := H.otherEndpointAt_ends
    (pendantEdge_mem H terminals hpendant s)
  have htEnds := H.otherEndpointAt_ends
    (pendantEdge_mem H terminals hpendant t)
  have hsPair :
      s(H.left (pendantEdge H terminals hpendant s),
          H.right (pendantEdge H terminals hpendant s)) =
        s(s.1, terminalNeighbor H terminals hpendant s) := by
    rcases hsEnds with hs | hs
    · rw [hs.1, hs.2]
      rfl
    · rw [hs.1, hs.2]
      change
        s(terminalNeighbor H terminals hpendant s, s.1) =
          s(s.1, terminalNeighbor H terminals hpendant s)
      exact Sym2.eq_swap
  have htPair :
      s(H.left (pendantEdge H terminals hpendant t),
          H.right (pendantEdge H terminals hpendant t)) =
        s(t.1, terminalNeighbor H terminals hpendant t) := by
    rcases htEnds with ht | ht
    · rw [ht.1, ht.2]
      rfl
    · rw [ht.1, ht.2]
      change
        s(terminalNeighbor H terminals hpendant t, t.1) =
          s(t.1, terminalNeighbor H terminals hpendant t)
      exact Sym2.eq_swap
  have hpairs :
      s(s.1, terminalNeighbor H terminals hpendant s) =
        s(t.1, terminalNeighbor H terminals hpendant t) := by
    calc
      s(s.1, terminalNeighbor H terminals hpendant s) =
          s(H.left (pendantEdge H terminals hpendant s),
            H.right (pendantEdge H terminals hpendant s)) := hsPair.symm
      _ = s(H.left (pendantEdge H terminals hpendant t),
            H.right (pendantEdge H terminals hpendant t)) := by rw [hedges]
      _ = s(t.1, terminalNeighbor H terminals hpendant t) := htPair
  rcases Sym2.eq_iff.mp hpairs with hst | hswap
  · exact Subtype.ext hst.1
  · exact False.elim
      (terminalNeighbor_ne_center H terminals hpendant s
        (hneighbors.trans hswap.1.symm))

/-- A terminal-neighbor fiber injects into the named edges incident with that
neighbor.  This is the exact multigraph version of the paper's assertion that
every group has size at most the maximum degree. -/
private theorem terminalNeighbor_fiber_card_le_degree
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (z : W) :
    ((Finset.univ : Finset {w : W // w ∈ terminals}).filter fun t =>
        terminalNeighbor H terminals hpendant t = z).card ≤ H.degree z := by
  classical
  let fiber :=
    (Finset.univ : Finset {w : W // w ∈ terminals}).filter fun t =>
      terminalNeighbor H terminals hpendant t = z
  let charge : {t // t ∈ fiber} → H.incidentEdges z := fun t =>
    ⟨pendantEdge H terminals hpendant t.1, by
      have hcenter :=
        pendantEdge_mem H terminals hpendant t.1
      have hends := H.otherEndpointAt_ends hcenter
      have hneighbor :
          terminalNeighbor H terminals hpendant t.1 = z :=
        (mem_filter.mp t.2).2
      apply (H.mem_incidentEdges z _).2
      rcases hends with hends | hends
      · exact Or.inr (hends.2.trans hneighbor)
      · exact Or.inl (hends.2.trans hneighbor)⟩
  have hcharge : Function.Injective charge := by
    intro s t hst
    apply Subtype.ext
    apply pendantEdge_injective_on_neighbor_fiber H terminals hpendant
    · exact ((mem_filter.mp s.2).2).trans (mem_filter.mp t.2).2.symm
    · exact congrArg Subtype.val hst
  have hcard := Fintype.card_le_of_injective charge hcharge
  change fiber.card ≤ (H.incidentEdges z).card
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact hcard

/-- The cut formed by a union of whole neighbor fibers and by all their
neighbors has no terminal edge in its boundary. -/
private theorem boundary_groupSide_subset_nonterminalEdges
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (hnoTerminalEdge :
      ∀ e : H.Edge, ¬ (H.left e ∈ terminals ∧ H.right e ∈ terminals))
    (labels : Finset W) :
    let selectedTerminals :
        Finset {w : W // w ∈ terminals} :=
      Finset.univ.filter fun t =>
        terminalNeighbor H terminals hpendant t ∈ labels
    let side : Finset W :=
      selectedTerminals.image Subtype.val ∪
        selectedTerminals.image
          (terminalNeighbor H terminals hpendant)
    H.boundary side ⊆ nonterminalEdges H terminals := by
  classical
  dsimp only
  let selectedTerminals :
      Finset {w : W // w ∈ terminals} :=
    Finset.univ.filter fun t =>
      terminalNeighbor H terminals hpendant t ∈ labels
  let side : Finset W :=
    selectedTerminals.image Subtype.val ∪
      selectedTerminals.image
        (terminalNeighbor H terminals hpendant)
  have hterminal_mem_side_iff
      (t : {w : W // w ∈ terminals}) :
      t.1 ∈ side ↔ t ∈ selectedTerminals := by
    constructor
    · intro ht
      rcases mem_union.mp ht with ht | ht
      · rcases mem_image.mp ht with ⟨s, hs, hst⟩
        have : s = t := Subtype.ext hst
        simpa [this] using hs
      · rcases mem_image.mp ht with ⟨s, _hs, hst⟩
        exact False.elim
          (terminalNeighbor_not_mem H terminals hpendant
            hnoTerminalEdge s (hst ▸ t.2))
    · intro ht
      exact mem_union_left _ (mem_image.mpr ⟨t, ht, rfl⟩)
  have hneighbor_mem_side_iff
      (t : {w : W // w ∈ terminals}) :
      terminalNeighbor H terminals hpendant t ∈ side ↔
        t ∈ selectedTerminals := by
    constructor
    · intro ht
      rcases mem_union.mp ht with ht | ht
      · rcases mem_image.mp ht with ⟨s, _hs, hst⟩
        exact False.elim
          (terminalNeighbor_not_mem H terminals hpendant
            hnoTerminalEdge t (hst.symm ▸ s.2))
      · rcases mem_image.mp ht with ⟨s, hs, hst⟩
        apply mem_filter.mpr
        exact ⟨mem_univ _, hst ▸ (mem_filter.mp hs).2⟩
    · intro ht
      exact mem_union_right _
        (mem_image.mpr ⟨t, ht, rfl⟩)
  have hincident_same_side
      (t : {w : W // w ∈ terminals}) {e : H.Edge}
      (he : e ∈ H.incidentEdges t.1) :
      H.left e ∈ side ↔ H.right e ∈ side := by
    have heq := eq_pendantEdge_of_incident H terminals hpendant t he
    have hends := H.otherEndpointAt_ends
      (pendantEdge_mem H terminals hpendant t)
    have hsame :
        t.1 ∈ side ↔
          terminalNeighbor H terminals hpendant t ∈ side :=
      (hterminal_mem_side_iff t).trans
        (hneighbor_mem_side_iff t).symm
    rcases hends with hends | hends
    · simpa [heq, hends.1, hends.2] using hsame
    · simpa [heq, hends.1, hends.2] using hsame.symm
  intro e he
  have hcross := (H.mem_boundary side e).1 he
  have hleft : H.left e ∉ terminals := by
    intro hleft
    let t : {w : W // w ∈ terminals} := ⟨H.left e, hleft⟩
    have hsame := hincident_same_side t
      ((H.mem_incidentEdges t.1 e).2 (Or.inl rfl))
    rcases hcross with hcross | hcross
    · exact hcross.2 (hsame.mp hcross.1)
    · exact hcross.2 (hsame.mpr hcross.1)
  have hright : H.right e ∉ terminals := by
    intro hright
    let t : {w : W // w ∈ terminals} := ⟨H.right e, hright⟩
    have hsame := hincident_same_side t
      ((H.mem_incidentEdges t.1 e).2 (Or.inr rfl))
    rcases hcross with hcross | hcross
    · exact hcross.2 (hsame.mp hcross.1)
    · exact hcross.2 (hsame.mpr hcross.1)
  simp [nonterminalEdges, hleft, hright]

end Pendant

/-! ## Legal contraction and the host routing cut -/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Independent original terminals cannot become the two ends of a legal
contracted named edge, because a good clustering keeps every terminal in its
singleton block. -/
theorem no_terminal_terminal_edge_of_isGood
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen : Nat) (P : VertexClustering V)
    (hgood :
      IsGood G terminals threshold cap alphaNum alphaDen P)
    (hindependent :
      ∀ ⦃s⦄, s ∈ terminals → ∀ ⦃t⦄, t ∈ terminals →
        s ≠ t → ¬ G.Adj s t) :
    ∀ e : (legalContractedGraph G P).Edge,
      ¬ ((legalContractedGraph G P).left e ∈
            contractedTerminals P terminals ∧
          (legalContractedGraph G P).right e ∈
            contractedTerminals P terminals) := by
  classical
  intro e he
  rcases (mem_contractedTerminals P terminals _).1 he.1 with
    ⟨s, hs, hleft⟩
  rcases (mem_contractedTerminals P terminals _).1 he.2 with
    ⟨t, ht, hright⟩
  obtain ⟨hedge, horigin, ha, hb⟩ :=
    legalContractedEdge_provenance G P e
  have ha' :
      chosenLeft (legalContractedOrigin G P e) = s := by
    have hblock :
        ((legalContractedGraph G P).left e).1 = P.block s :=
      congrArg Subtype.val hleft.symm
    rw [hblock, hgood.1.terminal_block_eq_singleton hs] at ha
    simpa using ha
  have hb' :
      chosenRight (legalContractedOrigin G P e) = t := by
    have hblock :
        ((legalContractedGraph G P).right e).1 = P.block t :=
      congrArg Subtype.val hright.symm
    rw [hblock, hgood.1.terminal_block_eq_singleton ht] at hb
    simpa using hb
  have hadj : G.Adj s t := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    rw [← ha', ← hb', horigin]
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hedge
  exact hindependent hs ht hadj.ne hadj

/-- Pull a set of contracted terminal vertices back to the original terminal
set. -/
private noncomputable def originalTerminalsOver
    (P : VertexClustering V) (terminals : Finset V)
    (A : Finset (ContractedVertex P)) : Finset V :=
  terminals.filter fun t => contractedVertex P t ∈ A

private theorem originalTerminalsOver_subset
    (P : VertexClustering V) (terminals : Finset V)
    (A : Finset (ContractedVertex P)) :
    originalTerminalsOver P terminals A ⊆ terminals := by
  intro t ht
  exact (mem_filter.mp ht).1

private theorem image_originalTerminalsOver
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    {threshold cap alphaNum alphaDen : Nat} (P : VertexClustering V)
    (hgood :
      IsGood G terminals threshold cap alphaNum alphaDen P)
    {A : Finset (ContractedVertex P)}
    (hA : A ⊆ contractedTerminals P terminals) :
    (originalTerminalsOver P terminals A).image (contractedVertex P) = A := by
  classical
  ext C
  constructor
  · intro hC
    rcases mem_image.mp hC with ⟨t, ht, rfl⟩
    exact (mem_filter.mp ht).2
  · intro hC
    rcases (mem_contractedTerminals P terminals C).1 (hA hC) with
      ⟨t, ht, hCt⟩
    apply mem_image.mpr
    refine ⟨t, mem_filter.mpr ⟨ht, ?_⟩, hCt⟩
    exact hCt ▸ hC

private theorem originalTerminalsOver_card
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    {threshold cap alphaNum alphaDen : Nat} (P : VertexClustering V)
    (hgood :
      IsGood G terminals threshold cap alphaNum alphaDen P)
    {A : Finset (ContractedVertex P)}
    (hA : A ⊆ contractedTerminals P terminals) :
    (originalTerminalsOver P terminals A).card = A.card := by
  classical
  have hinjective :
      Set.InjOn (contractedVertex P)
        (originalTerminalsOver P terminals A) := by
    intro s hs t ht hst
    exact contractedVertex_injective_on_terminals_of_isAcceptable hgood.1
      (originalTerminalsOver_subset P terminals A hs)
      (originalTerminalsOver_subset P terminals A ht) hst
  calc
    (originalTerminalsOver P terminals A).card =
        ((originalTerminalsOver P terminals A).image
          (contractedVertex P)).card :=
      (card_image_iff.mpr hinjective).symm
    _ = A.card := congrArg Finset.card
      (image_originalTerminalsOver G terminals P hgood hA)

/-- Source-parameter form of preprint Claim 5.1 / journal Claim 5.3.

The conclusion is exactly the terminal-cardinality premise consumed by
`ChekuriChuzhoySection5DenseRouterFamily.exists_denseRouterFamily`.
`hthreshold` is already a source hypothesis of the downstream router-candidate
producer. -/
theorem terminal_card_le_three_mul_nonterminalEdges
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (cap alphaNum alphaDen ell0 : Nat) (hell0 : 0 < ell0)
    (P : VertexClustering V)
    (hgood :
      IsGood G terminals
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap alphaNum alphaDen P)
    (hthreshold :
      0 < claim59SourceDegreeCap
        (contractedTerminals P terminals).card ell0)
    (hnode : NodeWellLinkedIn G Finset.univ terminals)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary G ({t} : Finset V)).card = 1)
    (hindependent :
      ∀ ⦃s⦄, s ∈ terminals → ∀ ⦃t⦄, t ∈ terminals →
        s ≠ t → ¬ G.Adj s t) :
    terminals.card ≤
      3 * (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card := by
  classical
  let H := legalContractedGraph G P
  let T := contractedTerminals P terminals
  let k := T.card
  let threshold := claim59SourceDegreeCap k ell0
  let q := (k + 2) / 3
  let r := k / 3
  have hk : k = terminals.card := by
    simpa [k, T] using contractedTerminals_card_eq_of_isGood hgood
  have hthreshold' : 0 < threshold := by
    simpa [threshold, k, T] using hthreshold
  have hpendantH : ∀ t ∈ T, H.degree t = 1 := by
    simpa [H, T] using
      legalContracted_pendantTerminals_of_isGood hgood hpendant
  have hnoTerminalEdge :
      ∀ e : H.Edge, ¬ (H.left e ∈ T ∧ H.right e ∈ T) := by
    simpa [H, T, threshold, k] using
      no_terminal_terminal_edge_of_isGood
        G terminals
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap alphaNum alphaDen P hgood hindependent
  have hthreshold_le_third : threshold ≤ r := by
    let D := 192 * ell0 ^ 3 * Nat.log 2 k
    have hDpos : 0 < D := by
      by_contra hnot
      have hDzero : D = 0 := Nat.eq_zero_of_not_pos hnot
      have : threshold = 0 := by
        simp [threshold, claim59SourceDegreeCap, D, hDzero]
      omega
    have hellCube : 0 < ell0 ^ 3 := pow_pos hell0 _
    have hlog : 0 < Nat.log 2 k := by
      by_contra hnot
      have hlogZero : Nat.log 2 k = 0 := Nat.eq_zero_of_not_pos hnot
      simp [D, hlogZero] at hDpos
    have hone : 1 ≤ ell0 ^ 3 * Nat.log 2 k :=
      Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.mul_pos hellCube hlog))
    have hDthree : 3 ≤ D := by
      calc
        3 ≤ 192 := by omega
        _ = 192 * 1 := by omega
        _ ≤ 192 * (ell0 ^ 3 * Nat.log 2 k) :=
          Nat.mul_le_mul_left 192 hone
        _ = D := by simp [D, Nat.mul_assoc]
    have hmul : threshold * D ≤ k := by
      simpa [threshold, claim59SourceDegreeCap, D] using
        Nat.div_mul_le_self k D
    have hthreeMul : threshold * 3 ≤ k := by
      calc
        threshold * 3 ≤ threshold * D :=
          Nat.mul_le_mul_left threshold hDthree
        _ ≤ k := hmul
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 3)).2 hthreeMul
  have hqpos : 0 < q := by
    have hkpos : 0 < k := by
      by_contra hnot
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hnot
      simp [threshold, claim59SourceDegreeCap, hkzero] at hthreshold'
    dsimp [q]
    omega
  have hbalance : 2 * q + r ≤
      (Finset.univ : Finset {w : ContractedVertex P // w ∈ T}).card + 1 := by
    simp only [card_univ, Fintype.card_coe, card_attach]
    dsimp [q, r]
    omega
  have hfiber :
      ∀ z ∈ (Finset.univ :
          Finset {w : ContractedVertex P // w ∈ T}).image
            (terminalNeighbor H T hpendantH),
        ((Finset.univ :
            Finset {w : ContractedVertex P // w ∈ T}).filter fun t =>
              terminalNeighbor H T hpendantH t = z).card ≤ r := by
    intro z _hz
    calc
      ((Finset.univ :
          Finset {w : ContractedVertex P // w ∈ T}).filter fun t =>
            terminalNeighbor H T hpendantH t = z).card
          ≤ H.degree z :=
        terminalNeighbor_fiber_card_le_degree H T hpendantH z
      _ ≤ threshold := Nat.le_of_lt (by
        simpa [H, T, threshold, k] using
          legalContracted_degree_lt_of_isGood hgood z)
      _ ≤ r := hthreshold_le_third
  obtain ⟨labels, _hlabels, hselectedLower, hunselectedLower⟩ :=
    exists_balanced_fiber_labels
      (Finset.univ :
        Finset {w : ContractedVertex P // w ∈ T})
      (terminalNeighbor H T hpendantH) q r hqpos hbalance hfiber
  let selected :
      Finset {w : ContractedVertex P // w ∈ T} :=
    Finset.univ.filter fun t =>
      terminalNeighbor H T hpendantH t ∈ labels
  let unselected :
      Finset {w : ContractedVertex P // w ∈ T} :=
    Finset.univ.filter fun t =>
      terminalNeighbor H T hpendantH t ∉ labels
  have hselected : q ≤ selected.card := by
    simpa [selected] using hselectedLower
  have hunselected : q ≤ unselected.card := by
    simpa [unselected] using hunselectedLower
  obtain ⟨selectedQ, hselectedQ, hselectedQcard⟩ :=
    Finset.exists_subset_card_eq hselected
  obtain ⟨unselectedQ, hunselectedQ, hunselectedQcard⟩ :=
    Finset.exists_subset_card_eq hunselected
  let selectedCenters : Finset (ContractedVertex P) :=
    selected.image Subtype.val
  let unselectedCenters : Finset (ContractedVertex P) :=
    unselected.image Subtype.val
  let A : Finset (ContractedVertex P) :=
    selectedQ.image Subtype.val
  let B : Finset (ContractedVertex P) :=
    unselectedQ.image Subtype.val
  let side : Finset (ContractedVertex P) :=
    selectedCenters ∪
      selected.image (terminalNeighbor H T hpendantH)
  have hselectedCentersT : selectedCenters ⊆ T := by
    intro C hC
    rcases mem_image.mp hC with ⟨t, _ht, rfl⟩
    exact t.2
  have hunselectedCentersT : unselectedCenters ⊆ T := by
    intro C hC
    rcases mem_image.mp hC with ⟨t, _ht, rfl⟩
    exact t.2
  have hAT : A ⊆ T := by
    intro C hC
    rcases mem_image.mp hC with ⟨t, ht, rfl⟩
    exact t.2
  have hBT : B ⊆ T := by
    intro C hC
    rcases mem_image.mp hC with ⟨t, ht, rfl⟩
    exact t.2
  have hAside : A ⊆ side := by
    intro C hC
    rcases mem_image.mp hC with ⟨t, ht, rfl⟩
    exact mem_union_left _
      (mem_image.mpr ⟨t, hselectedQ ht, rfl⟩)
  have hBside : Disjoint B side := by
    rw [Finset.disjoint_left]
    intro C hCB hCside
    rcases mem_image.mp hCB with ⟨t, htUnselectedQ, rfl⟩
    have htUnselected : t ∈ unselected :=
      hunselectedQ htUnselectedQ
    rcases mem_union.mp hCside with hCselected | hCneighbor
    · rcases mem_image.mp hCselected with ⟨s, hsSelected, hst⟩
      have hst' : s = t := Subtype.ext hst
      subst s
      exact (mem_filter.mp htUnselected).2
        (mem_filter.mp hsSelected).2
    · rcases mem_image.mp hCneighbor with ⟨s, _hs, hneighbor⟩
      exact terminalNeighbor_not_mem H T hpendantH hnoTerminalEdge s
        (hneighbor ▸ t.2)
  have hAcard : A.card = q := by
    change (selectedQ.image Subtype.val).card = q
    rw [card_image_of_injective]
    · exact hselectedQcard
    · exact Subtype.val_injective
  have hBcard : B.card = q := by
    change (unselectedQ.image Subtype.val).card = q
    rw [card_image_of_injective]
    · exact hunselectedQcard
    · exact Subtype.val_injective
  let X := originalTerminalsOver P terminals A
  let Y := originalTerminalsOver P terminals B
  have hXterminals : X ⊆ terminals :=
    originalTerminalsOver_subset P terminals A
  have hYterminals : Y ⊆ terminals :=
    originalTerminalsOver_subset P terminals B
  have hXcard : X.card = q := by
    calc
      X.card = A.card :=
        originalTerminalsOver_card G terminals P hgood hAT
      _ = q := hAcard
  have hYcard : Y.card = q := by
    calc
      Y.card = B.card :=
        originalTerminalsOver_card G terminals P hgood hBT
      _ = q := hBcard
  have hXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro t htX htY
    have hctA : contractedVertex P t ∈ A :=
      (mem_filter.mp htX).2
    have hctB : contractedVertex P t ∈ B :=
      (mem_filter.mp htY).2
    exact Finset.disjoint_left.mp (hBside.mono_right hAside)
      hctB hctA
  obtain ⟨packing, hpackingCard, hpackingStay⟩ :=
    hnode.2 hXterminals hYterminals hXY
  have hpackingCard' : packing.card = q := by
    simpa [hXcard, hYcard] using hpackingCard
  let hostSide := selectedUnion side
  let hostOther := Finset.univ \ hostSide
  have hXhostSide : X ⊆ hostSide := by
    intro t ht
    apply (mem_selectedUnion_iff side t).2
    exact hAside (mem_filter.mp ht).2
  have hYhostOther : Y ⊆ hostOther := by
    intro t ht
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    intro htSide
    exact Finset.disjoint_left.mp hBside (mem_filter.mp ht).2
      ((mem_selectedUnion_iff side t).1 htSide)
  have hcutPacking :
      q ≤ (EdgeMenger.edgeBoundary G hostSide hostOther).card := by
    let edgePacking : EdgePathPacking G X Y := {
      Index := packing.Index
      path := packing.path
      connects := packing.connects
      edge_disjoint := fun _i _j hij =>
        GraphPath.edgeDisjoint_of_nodeDisjoint
          (packing.node_disjoint hij) }
    have hedgePackingCard : edgePacking.card = q := by
      change Fintype.card packing.Index = q
      simpa [PathPacking.card] using hpackingCard'
    have hle :=
      edgePathPacking_card_le_edgeBoundary_of_partition
        edgePacking
        (by ext v; simp [hostOther])
        (by
          rw [Finset.disjoint_left]
          intro v hvSide hvOther
          exact (mem_sdiff.mp hvOther).2 hvSide)
        hXhostSide hYhostOther
    exact hedgePackingCard ▸ hle
  have hboundaryHost :
      q ≤ (Section44.clusterBoundary G hostSide).card := by
    calc
      q ≤ (EdgeMenger.edgeBoundary G hostSide hostOther).card :=
        hcutPacking
      _ = (Section44.edgeBoundary G hostSide hostOther).card := by
        rw [Section44.edgeBoundary_eq_edgeMenger]
      _ ≤ (Section44.clusterBoundary G hostSide).card :=
        card_le_card
          (edgeBoundary_subset_clusterBoundary_left (G := G) (by
            rw [Finset.disjoint_left]
            intro v hvSide hvOther
            exact (mem_sdiff.mp hvOther).2 hvSide))
  have hboundaryNamed :
      q ≤ (H.boundary side).card := by
    rw [legalContracted_boundary_card_eq_clusterBoundary_card
      G P side]
    simpa [hostSide] using hboundaryHost
  have hboundarySubset :
      H.boundary side ⊆ nonterminalEdges H T := by
    simpa [side, selected] using
      boundary_groupSide_subset_nonterminalEdges
        H T hpendantH hnoTerminalEdge labels
  have hqm :
      q ≤ (nonterminalEdges H T).card :=
    hboundaryNamed.trans (card_le_card hboundarySubset)
  rw [← hk]
  change k ≤ 3 * (nonterminalEdges H T).card
  have hkq : k ≤ 3 * q := by
    dsimp [q]
    omega
  exact hkq.trans (Nat.mul_le_mul_left 3 hqm)

end ChekuriChuzhoySection5TerminalEdgeCount
end SimpleGraph

end Lax17Proofs
