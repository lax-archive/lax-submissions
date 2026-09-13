import Lax17Proofs.Source.ChekuriChuzhoySection5Separate
import Lax17Proofs.Source.ChekuriChuzhoySection5DensePartition

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Claim 5.10

This module formalizes the deterministic conclusion of journal Claim 5.10.
For a dense contracted block `B`, its uncontracted union is replaced by the
connected components of its induced graph; old clustering blocks outside
that union are retained unchanged.  The dense internal edges pay for the
small increase on the outer boundary, and Theorem 5.5 then completes every
small component without increasing the source potential.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Claim510


open Finset
open ChekuriChuzhoySection5BandwidthDecomposition
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5DenseBlockReplacement
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5LabelPartition
open ChekuriChuzhoySection5Partition
open ChekuriChuzhoySection5Rho
open ChekuriChuzhoySection5RouterProduction
open ChekuriChuzhoySection5SourcePotential

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Auxiliary graph for the preliminary clustering in Claim 5.10.  Inside
`A` it is exactly `G[A]`; outside `A`, each old clustering block is made a
clique so that it remains one part even when a small bandwidth block is not
known to be connected. -/
def denseReplacementGraph
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (A : Finset V) : _root_.SimpleGraph V where
  Adj u v :=
    (G.Adj u v ∧ u ∈ A ∧ v ∈ A) ∨
      (u ∉ A ∧ v ∉ A ∧ P.block u = P.block v ∧ u ≠ v)
  symm := by
    intro u v h
    rcases h with hin | hout
    · exact Or.inl ⟨G.symm hin.1, hin.2.2, hin.2.1⟩
    · exact Or.inr
        ⟨hout.2.1, hout.1, hout.2.2.1.symm, hout.2.2.2.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with hin | hout
    · exact G.loopless.irrefl v hin.1
    · exact hout.2.2.2 rfl⟩

/-- The preliminary clustering of Claim 5.10. -/
noncomputable def denseReplacementClustering
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (A : Finset V) : VertexClustering V := by
  classical
  exact partition (denseReplacementGraph G P A).connectedComponentMk

@[simp] theorem denseReplacementClustering_block_eq_iff
    (P : VertexClustering V) (A : Finset V) (u v : V) :
    (denseReplacementClustering G P A).block u =
        (denseReplacementClustering G P A).block v ↔
      (denseReplacementGraph G P A).connectedComponentMk u =
        (denseReplacementGraph G P A).connectedComponentMk v := by
  classical
  change
    partOf (denseReplacementGraph G P A).connectedComponentMk u =
        partOf (denseReplacementGraph G P A).connectedComponentMk v ↔ _
  exact partOf_eq_partOf_iff

private theorem denseWalk_mem_side
    {P : VertexClustering V} {A : Finset V} {u v : V}
    (p : (denseReplacementGraph G P A).Walk u v) :
    u ∈ A ↔ v ∈ A := by
  induction p with
  | nil => exact Iff.rfl
  | @cons u w v huw p ih =>
      have huwSide : u ∈ A ↔ w ∈ A := by
        rcases huw with hin | hout
        · exact ⟨fun _ => hin.2.2, fun _ => hin.2.1⟩
        · exact ⟨fun hu => (hout.1 hu).elim,
            fun hw => (hout.2.1 hw).elim⟩
      exact huwSide.trans ih

private theorem denseWalk_oldBlock_eq_outside
    {P : VertexClustering V} {A : Finset V} {u v : V}
    (p : (denseReplacementGraph G P A).Walk u v)
    (hu : u ∉ A) :
    P.block u = P.block v := by
  induction p with
  | nil => rfl
  | @cons u w v huw p ih =>
      rcases huw with hin | hout
      · exact (hu hin.2.1).elim
      · have hw : w ∉ A := hout.2.1
        exact hout.2.2.1.trans (ih hw)

theorem mem_A_iff_of_dense_same_block
    (P : VertexClustering V) (A : Finset V) {u v : V}
    (h :
      (denseReplacementClustering G P A).block u =
        (denseReplacementClustering G P A).block v) :
    u ∈ A ↔ v ∈ A := by
  have hc :=
    (denseReplacementClustering_block_eq_iff
      (G := G) P A u v).mp h
  rcases _root_.SimpleGraph.ConnectedComponent.eq.mp hc with ⟨p⟩
  exact denseWalk_mem_side p

theorem denseReplacement_block_eq_old_of_not_mem
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    {v : V} (hv : v ∉ selectedUnion B) :
    (denseReplacementClustering G P (selectedUnion B)).block v =
      P.block v := by
  classical
  ext x
  change
    x ∈ (denseReplacementClustering G P (selectedUnion B)).part v ↔
      x ∈ P.part v
  rw [(denseReplacementClustering G P
      (selectedUnion B)).mem_part_iff_part_eq_part (by simp) (by simp),
    P.mem_part_iff_part_eq_part (by simp) (by simp)]
  constructor
  · intro h
    have hc :=
      (denseReplacementClustering_block_eq_iff
        (G := G) P (selectedUnion B) x v).mp h
    rcases _root_.SimpleGraph.ConnectedComponent.eq.mp hc with ⟨p⟩
    change P.block x = P.block v
    exact denseWalk_oldBlock_eq_outside p
      ((denseWalk_mem_side p).not.mpr hv)
  · intro h
    change
      (denseReplacementClustering G P (selectedUnion B)).block x =
        (denseReplacementClustering G P (selectedUnion B)).block v
    rw [denseReplacementClustering_block_eq_iff]
    by_cases hxv : x = v
    · subst x
      rfl
    · apply _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      have hx : x ∉ selectedUnion B := by
        intro hxB
        apply hv
        apply (mem_selectedUnion_iff B v).2
        have hxContracted :=
          (mem_selectedUnion_iff B x).1 hxB
        have heq : contractedVertex P x = contractedVertex P v := by
          apply Subtype.ext
          exact h
        rw [← heq]
        exact hxContracted
      exact Or.inr
        ⟨hx, hv, h, hxv⟩

theorem denseReplacement_same_block_of_adj_inside
    (P : VertexClustering V) (A : Finset V) {u v : V}
    (huv : G.Adj u v) (hu : u ∈ A) (hv : v ∈ A) :
    (denseReplacementClustering G P A).block u =
      (denseReplacementClustering G P A).block v := by
  rw [denseReplacementClustering_block_eq_iff]
  exact _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (Or.inl ⟨huv, hu, hv⟩)

/-- A preliminary block meeting the selected union is a connected component
of the original induced graph on that union. -/
theorem denseReplacement_inside_block_connected
    (P : VertexClustering V) (A : Finset V)
    {v : V} (hv : v ∈ A) :
    (G.induce
      {x : V | x ∈ (denseReplacementClustering G P A).block v}).Connected := by
  classical
  let H := denseReplacementGraph G P A
  let K := H.connectedComponentMk v
  have hset :
      {x : V | x ∈ (denseReplacementClustering G P A).block v} =
        K.supp := by
    ext x
    change x ∈ partOf H.connectedComponentMk v ↔ x ∈ K.supp
    rw [mem_partOf_iff]
    simp only [K, _root_.SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact eq_comm
  rw [hset]
  apply K.connected_toSimpleGraph.mono
  intro x y hxy
  have hxA : x.1 ∈ A := by
    have hcomp : H.connectedComponentMk x.1 =
        H.connectedComponentMk v := x.2
    rcases _root_.SimpleGraph.ConnectedComponent.eq.mp hcomp with ⟨p⟩
    exact (denseWalk_mem_side p).mpr hv
  rcases hxy with hin | hout
  · exact hin.1
  · exact (hout.1 hxA).elim

theorem selectedUnion_disjoint_terminals
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    (terminals : Finset V)
    (hB : Disjoint B (contractedTerminals P terminals)) :
    Disjoint (selectedUnion B) terminals := by
  rw [Finset.disjoint_left]
  intro v hvB hvT
  have hcB := (mem_selectedUnion_iff B v).1 hvB
  have hcT : contractedVertex P v ∈ contractedTerminals P terminals := by
    apply (mem_contractedTerminals P terminals _).2
    exact ⟨v, hvT, rfl⟩
  exact Finset.disjoint_left.mp hB hcB hcT

/-- The preliminary Claim 5.10 clustering has terminal singleton blocks and
all of its large blocks are connected.  Outside the selected union the old
good clustering is unchanged, so a large new block must meet the union. -/
theorem denseReplacement_preAcceptable
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    (terminals : Finset V) {threshold cap D : Nat}
    (hgood : IsGood G terminals threshold cap 1 D P)
    (hB : Disjoint B (contractedTerminals P terminals)) :
    PreAcceptable G terminals threshold
      (denseReplacementClustering G P (selectedUnion B)) := by
  let Q := denseReplacementClustering G P (selectedUnion B)
  have hAT : Disjoint (selectedUnion B) terminals :=
    selectedUnion_disjoint_terminals P B terminals hB
  refine ⟨?_, ?_⟩
  · intro t ht
    have htA : t ∉ selectedUnion B :=
      fun htA => Finset.disjoint_left.mp hAT htA ht
    have hblock :
        Q.block t = ({t} : Finset V) := by
      rw [denseReplacement_block_eq_old_of_not_mem
        (G := G) P B htA]
      exact hgood.1.terminal_block_eq_singleton ht
    rw [← hblock]
    exact Q.block_mem_parts t
  · intro C hCQ hClarge
    rcases Q.nonempty_of_mem_parts hCQ with ⟨v, hvC⟩
    have hblock : Q.block v = C :=
      Q.block_eq_of_mem hCQ hvC
    by_cases hvA : v ∈ selectedUnion B
    · rw [← hblock]
      exact denseReplacement_inside_block_connected
        (G := G) P (selectedUnion B) hvA
    · have hold :
          P.block v = C := by
        rw [← hblock,
          denseReplacement_block_eq_old_of_not_mem
            (G := G) P B hvA]
      have hCP : C ∈ P.parts := by
        rw [← hold]
        exact P.block_mem_parts v
      exact False.elim
        ((smallCluster_iff_not_largeCluster G threshold C).mp
          (hgood.2 C hCP) hClarge)

theorem denseReplacement_large_part_subset_selectedUnion
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    (terminals : Finset V) {threshold cap D : Nat}
    (hgood : IsGood G terminals threshold cap 1 D P)
    {C : Finset V}
    (hC :
      C ∈ (denseReplacementClustering
        G P (selectedUnion B)).parts)
    (hClarge : IsLargeCluster G threshold C) :
    C ⊆ selectedUnion B := by
  let Q := denseReplacementClustering G P (selectedUnion B)
  rcases Q.nonempty_of_mem_parts hC with ⟨v, hvC⟩
  have hblock : Q.block v = C :=
    Q.block_eq_of_mem hC hvC
  by_cases hvA : v ∈ selectedUnion B
  · intro x hxC
    have hsame : Q.block x = Q.block v :=
      (Q.block_eq_of_mem hC hxC).trans hblock.symm
    exact (mem_A_iff_of_dense_same_block
      (G := G) P (selectedUnion B)
      (u := x) (v := v) hsame).mpr hvA
  · have hold : P.block v = C := by
      rw [← hblock,
        denseReplacement_block_eq_old_of_not_mem
          (G := G) P B hvA]
    have hCP : C ∈ P.parts := by
      rw [← hold]
      exact P.block_mem_parts v
    exact False.elim
      ((smallCluster_iff_not_largeCluster G threshold C).mp
        (hgood.2 C hCP) hClarge)

theorem selectedUnion_mem_iff_of_oldBlock_eq
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    {u v : V} (h : P.block u = P.block v) :
    u ∈ selectedUnion B ↔ v ∈ selectedUnion B := by
  rw [mem_selectedUnion_iff, mem_selectedUnion_iff]
  have heq : contractedVertex P u = contractedVertex P v := by
    apply Subtype.ext
    exact h
  rw [heq]

/-- Away from the outer boundary of the selected union, the preliminary
replacement cannot increase an edge potential.  An inside edge becomes
internal; an outside edge sees exactly the same old endpoint blocks. -/
theorem denseReplacement_edgePotential_le_of_not_boundary
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    (schedule : BoundedContribution) {e : Sym2 V}
    (heG : e ∈ G.edgeSet)
    (heA : e ∉ originalBoundary G (selectedUnion B)) :
    edgePotential G
        (denseReplacementClustering G P (selectedUnion B))
        schedule e ≤
      edgePotential G P schedule e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using heG
      have hsameSide :
          u ∈ selectedUnion B ↔ v ∈ selectedUnion B := by
        constructor
        · intro hu
          by_contra hv
          apply heA
          exact mem_originalBoundary_iff.mpr
            ⟨heG, u, hu, v, hv, rfl⟩
        · intro hv
          by_contra hu
          apply heA
          exact mem_originalBoundary_iff.mpr
            ⟨heG, v, hv, u, hu, Sym2.eq_swap⟩
      by_cases hu : u ∈ selectedUnion B
      · have hv := hsameSide.mp hu
        have hnew :=
          denseReplacement_same_block_of_adj_inside
            (G := G) P (selectedUnion B) huv hu hv
        rw [edgePotential_eq_zero_of_same_block
          (G := G) _ schedule hnew]
        exact edgePotential_nonnegative (G := G) P schedule s(u, v)
      · have hv : v ∉ selectedUnion B := by
          simpa [hu] using hsameSide
        have huBlock :=
          denseReplacement_block_eq_old_of_not_mem
            (G := G) P B hu
        have hvBlock :=
          denseReplacement_block_eq_old_of_not_mem
            (G := G) P B hv
        have huSize :
            endpointBoundarySize G
                (denseReplacementClustering G P (selectedUnion B)) u =
              endpointBoundarySize G P u := by
          simp only [endpointBoundarySize, huBlock]
        have hvSize :
            endpointBoundarySize G
                (denseReplacementClustering G P (selectedUnion B)) v =
              endpointBoundarySize G P v := by
          simp only [endpointBoundarySize, hvBlock]
        simp only
          [ChekuriChuzhoySection5SourcePotential.edgePotential_mk]
        rw [huBlock, hvBlock, huSize, hvSize]

/-- An edge leaving the selected union gains at most the new endpoint
contribution on its inside endpoint. -/
theorem denseReplacement_boundary_edgePotential_le
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    {w0 cap ell0 : Nat}
    (hw0 : 0 < w0) (hcap : 1 < cap) (hw0cap : w0 ≤ cap)
    (hell0 : 0 < ell0)
    {e : Sym2 V} (he : e ∈ originalBoundary G (selectedUnion B)) :
    edgePotential G
        (denseReplacementClustering G P (selectedUnion B))
        (sourceBoundedContribution w0 cap ell0
          hw0 hcap hw0cap hell0) e ≤
      edgePotential G P
        (sourceBoundedContribution w0 cap ell0
          hw0 hcap hw0cap hell0) e +
        (1 : Rat) / (28 * ell0) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have he' :
          s(u, v) ∈ Section44.clusterBoundary G
            (selectedUnion B) := he
      rcases (mk_mem_clusterBoundary_iff
        G (selectedUnion B) u v).1 he' with
        ⟨huv, hends⟩
      have heG : s(u, v) ∈ G.edgeSet := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using huv
      have horient :
          ∀ a b : V, G.Adj a b →
            a ∈ selectedUnion B → b ∉ selectedUnion B →
            edgePotential G
                (denseReplacementClustering G P (selectedUnion B))
                (sourceBoundedContribution w0 cap ell0
                  hw0 hcap hw0cap hell0) s(a, b) ≤
              edgePotential G P
                  (sourceBoundedContribution w0 cap ell0
                    hw0 hcap hw0cap hell0) s(a, b) +
                (1 : Rat) / (28 * ell0) := by
        intro a b hab ha hb
        let Q := denseReplacementClustering G P (selectedUnion B)
        have hOldCross : P.block a ≠ P.block b := by
          intro hold
          exact hb
            ((selectedUnion_mem_iff_of_oldBlock_eq P B hold).mp ha)
        have hNewCross : Q.block a ≠ Q.block b := by
          intro hnew
          exact hb
            ((mem_A_iff_of_dense_same_block
              (G := G) P (selectedUnion B) hnew).mp ha)
        have hvBlock :
            Q.block b = P.block b :=
          denseReplacement_block_eq_old_of_not_mem
            (G := G) P B hb
        have hinside :=
          rho_le_one_div_twentyEight_mul
            hw0 hcap hw0cap hell0
              (endpointBoundarySize G Q a)
        have holdNonnegative :=
          rho_nonnegative
            (w0 := w0)
            (show 0 <
                16 * (20 * ell0) * (Nat.log 2 cap + 1) by
              positivity)
            (endpointBoundarySize G P a)
        rw [edgePotential_eq_of_crosses
            (G := G) Q _ hNewCross,
          edgePotential_eq_of_crosses
            (G := G) P _ hOldCross]
        change
          1 +
              rho w0
                (16 * (20 * ell0) * (Nat.log 2 cap + 1))
                (endpointBoundarySize G Q a) +
              rho w0
                (16 * (20 * ell0) * (Nat.log 2 cap + 1))
                (endpointBoundarySize G Q b) ≤
            1 +
                rho w0
                  (16 * (20 * ell0) * (Nat.log 2 cap + 1))
                  (endpointBoundarySize G P a) +
                rho w0
                  (16 * (20 * ell0) * (Nat.log 2 cap + 1))
                  (endpointBoundarySize G P b) +
              1 / (28 * ↑ell0)
        rw [show endpointBoundarySize G Q b =
            endpointBoundarySize G P b by
          simp only [endpointBoundarySize, hvBlock]]
        linarith
      rcases hends with hends | hends
      · exact horient u v huv hends.1 hends.2
      · simpa only [Sym2.eq_swap] using
          horient v u (G.symm huv) hends.1 hends.2

theorem oldInternalCrossBlockEdges_internal_denseReplacement
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    {e : Sym2 V} (he : e ∈ oldInternalCrossBlockEdges G P B) :
    ¬ crossesBlocks
      (denseReplacementClustering G P (selectedUnion B)) e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rcases Finset.mem_inter.mp he with ⟨hcross, hinternal⟩
      rcases (mk_mem_edgeBoundary_iff
        G (selectedUnion B) (selectedUnion B) u v).1 hinternal with
        ⟨huv, hends⟩
      rcases hends with hends | hends
      · simpa only [crossesBlocks_mk, not_ne_iff] using
          denseReplacement_same_block_of_adj_inside
            (G := G) P (selectedUnion B) huv hends.1 hends.2
      · simpa only [crossesBlocks_mk, not_ne_iff] using
          denseReplacement_same_block_of_adj_inside
            (G := G) P (selectedUnion B) huv hends.2 hends.1

theorem oldInternalCrossBlockEdges_disjoint_boundary
    (P : VertexClustering V) (B : Finset (ContractedVertex P)) :
    Disjoint (oldInternalCrossBlockEdges G P B)
      (originalBoundary G (selectedUnion B)) := by
  rw [Finset.disjoint_left]
  intro e heInternal heBoundary
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hi :=
        (mk_mem_edgeBoundary_iff
          G (selectedUnion B) (selectedUnion B) u v).1
          (Finset.mem_inter.mp heInternal).2
      have hb :=
        (mk_mem_clusterBoundary_iff
          G (selectedUnion B) u v).1 heBoundary
      rcases hi.2 with hi | hi <;>
        rcases hb.2 with hb | hb <;> simp_all

/-- Claim 5.10's source edge classification, before the dense cardinal
inequality is applied. -/
theorem denseReplacement_dropsByOne_of_card
    (P : VertexClustering V) (B : Finset (ContractedVertex P))
    {w0 cap ell0 : Nat}
    (hw0 : 0 < w0) (hcap : 1 < cap) (hw0cap : w0 ≤ cap)
    (hell0 : 0 < ell0)
    (hcard :
      (1 : Rat) / (28 * ell0) *
            (originalBoundary G (selectedUnion B)).card + 1 ≤
        ((oldInternalCrossBlockEdges G P B).card : Rat)) :
    DropsByOne G
      (sourceBoundedContribution w0 cap ell0
        hw0 hcap hw0cap hell0)
      P (denseReplacementClustering G P (selectedUnion B)) := by
  let Q := denseReplacementClustering G P (selectedUnion B)
  let schedule :=
    sourceBoundedContribution w0 cap ell0
      hw0 hcap hw0cap hell0
  let removed := oldInternalCrossBlockEdges G P B
  let added := originalBoundary G (selectedUnion B)
  apply dropsByOne_of_removed_added_accounting
    (G := G) P Q schedule removed added
      ((1 : Rat) / (28 * ell0))
  · intro e he
    exact mem_sourceEdgeFinset.mpr
      ((mem_crossBlockOriginalEdges (G := G) P e).1
        (Finset.mem_inter.mp he).1).1
  · exact
      ChekuriChuzhoySection5Separate.originalBoundary_subset_sourceEdgeFinset
        (G := G) (selectedUnion B)
  · simpa [removed, added] using hcard
  · intro e heG
    by_cases heRemoved : e ∈ removed
    · have heAdded : e ∉ added :=
        fun heAdded =>
          Finset.disjoint_left.mp
            (oldInternalCrossBlockEdges_disjoint_boundary
              (G := G) P B) heRemoved heAdded
      have hQzero : edgePotential G Q schedule e = 0 := by
        induction e using Sym2.inductionOn with
        | _ u v =>
            apply
              ChekuriChuzhoySection5SourcePotential.edgePotential_eq_zero_of_same_block
            simpa only [crossesBlocks_mk, not_ne_iff] using
              oldInternalCrossBlockEdges_internal_denseReplacement
                (G := G) P B heRemoved
      have hPone : (1 : Rat) ≤ edgePotential G P schedule e :=
        one_le_edgePotential_of_crosses
          (G := G) P schedule
          ((mem_crossBlockOriginalEdges (G := G) P e).1
            (Finset.mem_inter.mp heRemoved).1).2
      simp only [if_pos heRemoved, if_neg heAdded]
      rw [hQzero]
      linarith
    · by_cases heAdded : e ∈ added
      · have hbound :=
          denseReplacement_boundary_edgePotential_le
            (G := G) P B hw0 hcap hw0cap hell0 heAdded
        simpa [Q, schedule, removed, added,
          heRemoved, heAdded] using hbound
      · have hstable :=
          denseReplacement_edgePotential_le_of_not_boundary
            (G := G) P B schedule heG heAdded
        simpa [removed, added, heRemoved, heAdded] using hstable

/-- The numerical heart of Claim 5.10.  Claim 5.9 gives
`ell0 * boundary < 10m` and `m ≤ 2 ell0^2 * internal`.  Four internal
edges already suffice for the `1/(28 ell0)` boundary charge to leave a full
unit of decrease. -/
theorem claim510_card_accounting
    {ell0 boundary internal m : Nat}
    (hell0 : 0 < ell0)
    (hboundary : ell0 * boundary < 10 * m)
    (hinternal : m ≤ 2 * ell0 ^ 2 * internal)
    (hfour : 4 ≤ internal) :
    (1 : Rat) / (28 * ell0) * boundary + 1 ≤
      (internal : Rat) := by
  have hscaled :
      ell0 * boundary <
        ell0 * (20 * ell0 * internal) := by
    calc
      ell0 * boundary < 10 * m := hboundary
      _ ≤ 10 * (2 * ell0 ^ 2 * internal) :=
        Nat.mul_le_mul_left 10 hinternal
      _ = ell0 * (20 * ell0 * internal) := by ring
  have hb : boundary < 20 * ell0 * internal :=
    Nat.lt_of_mul_lt_mul_left hscaled
  have hnat :
      boundary + 28 * ell0 ≤ 28 * ell0 * internal := by
    nlinarith
  have hnatRat :
      (boundary : Rat) + 28 * ell0 ≤
        28 * ell0 * internal := by
    exact_mod_cast hnat
  have hden : (0 : Rat) < 28 * ell0 := by positivity
  rw [div_mul_eq_mul_div]
  simp only [one_mul]
  rw [show (boundary : Rat) / (28 * ell0) + 1 =
      ((boundary : Rat) + 28 * ell0) / (28 * ell0) by
        field_simp]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Journal Claim 5.10 for one block of the Claim 5.9 dense partition.
The theorem constructs the acceptable clustering, rather than exposing the
preliminary component partition or the later bandwidth completions as
inputs. -/
theorem exists_claim510_clustering
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (cap ell0 : Nat) (hell0 : 0 < ell0)
    (hcap : 1 < cap)
    (P : VertexClustering V)
    (hgoodSource :
      let k := (contractedTerminals P terminals).card
      let w0 := claim59SourceDegreeCap k ell0
      let D := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
      IsGood G terminals w0 cap 1 D P)
    (hthreshold :
      0 < claim59SourceDegreeCap
        (contractedTerminals P terminals).card ell0)
    (hthresholdCap :
      claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0 ≤ cap)
    (hterminalCard :
      (contractedTerminals P terminals).card ≤
        3 * (nonterminalEdges (legalContractedGraph G P)
          (contractedTerminals P terminals)).card)
    (B : Finset (ContractedVertex P))
    (hBterm : Disjoint B (contractedTerminals P terminals))
    (hBboundary :
      ell0 * ((legalContractedGraph G P).boundary B).card <
        10 * (nonterminalEdges (legalContractedGraph G P)
          (contractedTerminals P terminals)).card)
    (hBinternal :
      (nonterminalEdges (legalContractedGraph G P)
          (contractedTerminals P terminals)).card ≤
        2 * ell0 ^ 2 *
          (internalEdges (legalContractedGraph G P) B).card) :
    ∃ Q : VertexClustering V,
      (let k := (contractedTerminals P terminals).card
       let w0 := claim59SourceDegreeCap k ell0
       let D := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
       IsAcceptable G terminals w0 cap 1 D Q) ∧
      DropsByOne G
        (sourceBoundedContribution
          (claim59SourceDegreeCap
            (contractedTerminals P terminals).card ell0)
          cap ell0 hthreshold hcap hthresholdCap hell0)
        P Q ∧
      (∀ C ∈ Q.parts,
        IsLargeCluster G
          (claim59SourceDegreeCap
            (contractedTerminals P terminals).card ell0) C →
        C ⊆ selectedUnion B) := by
  classical
  let k := (contractedTerminals P terminals).card
  let w0 := claim59SourceDegreeCap k ell0
  let D := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
  let H := legalContractedGraph G P
  let T := contractedTerminals P terminals
  let m := (nonterminalEdges H T).card
  let internal := (internalEdges H B).card
  let boundary := (H.boundary B).card
  have hgood :
      IsGood G terminals w0 cap 1 D P := by
    simpa [k, w0, D] using hgoodSource
  have hw0pos : 0 < w0 := by
    simpa [w0, k] using hthreshold
  have hsourceDenPos :
      0 < 192 * ell0 ^ 3 * Nat.log 2 k := by
    by_contra hzero
    have hz :
        192 * ell0 ^ 3 * Nat.log 2 k = 0 := Nat.eq_zero_of_not_pos hzero
    have : w0 = 0 := by
      simp [w0, claim59SourceDegreeCap, hz]
    omega
  have hsourceDenLe :
      192 * ell0 ^ 3 * Nat.log 2 k ≤ k := by
    by_contra hnot
    have hlt :
        k < 192 * ell0 ^ 3 * Nat.log 2 k := Nat.lt_of_not_ge hnot
    have hwzero : w0 = 0 := by
      simp [w0, claim59SourceDegreeCap,
        Nat.div_eq_of_lt hlt]
    omega
  have hlog : 0 < Nat.log 2 k := by
    by_contra hzero
    have hz : Nat.log 2 k = 0 := Nat.eq_zero_of_not_pos hzero
    simp [hz] at hsourceDenPos
  have hfour : 4 ≤ internal := by
    have hk : k ≤ 3 * m := by
      simpa [k, m, H, T] using hterminalCard
    have hm : m ≤ 2 * ell0 ^ 2 * internal := by
      simpa [m, internal, H, T] using hBinternal
    have hscaled :
        ell0 ^ 2 * (192 * ell0 * Nat.log 2 k) ≤
          ell0 ^ 2 * (6 * internal) := by
      calc
        ell0 ^ 2 * (192 * ell0 * Nat.log 2 k) =
            192 * ell0 ^ 3 * Nat.log 2 k := by ring
        _ ≤ k := hsourceDenLe
        _ ≤ 3 * m := hk
        _ ≤ 3 * (2 * ell0 ^ 2 * internal) :=
          Nat.mul_le_mul_left 3 hm
        _ = ell0 ^ 2 * (6 * internal) := by ring
    have hcancel :
        192 * ell0 * Nat.log 2 k ≤ 6 * internal :=
      Nat.le_of_mul_le_mul_left hscaled (by positivity)
    nlinarith
  have hboundary' :
      ell0 *
          (originalBoundary G (selectedUnion B)).card <
        10 * m := by
    change ell0 *
        (Section44.clusterBoundary G (selectedUnion B)).card <
      10 * m
    rw [← legalContracted_boundary_card_eq_clusterBoundary_card
      G P B]
    simpa [boundary, m, H, T] using hBboundary
  have hinternal' :
      m ≤
        2 * ell0 ^ 2 *
          (oldInternalCrossBlockEdges G P B).card := by
    rw [← card_legalContracted_internalEdges_eq_oldInternalCrossBlockEdges
      G P B]
    simpa [m, internal, H, T] using hBinternal
  have hcard :
      (1 : Rat) / (28 * ell0) *
            (originalBoundary G (selectedUnion B)).card + 1 ≤
        ((oldInternalCrossBlockEdges G P B).card : Rat) := by
    apply claim510_card_accounting hell0 hboundary' hinternal'
    rw [← card_legalContracted_internalEdges_eq_oldInternalCrossBlockEdges
      G P B]
    simpa [internal, H] using hfour
  let Q0 := denseReplacementClustering G P (selectedUnion B)
  have hdrop0 :
      DropsByOne G
        (sourceBoundedContribution w0 cap ell0
          hthreshold hcap hthresholdCap hell0) P Q0 := by
    exact denseReplacement_dropsByOne_of_card
      (G := G) P B hthreshold hcap hthresholdCap hell0 hcard
  have hpre : PreAcceptable G terminals w0 Q0 :=
    denseReplacement_preAcceptable
      (G := G) P B terminals hgood hBterm
  have hsize :
      (80 : Rat) * (harmonic w0 + 2) ≤ D := by
    simpa [D] using source_denominator_size
      hthreshold hcap hthresholdCap hell0
  have hupper :
      ∀ z, rho w0 D z ≤ (1 : Rat) / 20 :=
    rho_le_one_twentieth (by
      dsimp [D]
      positivity) hsize
  obtain ⟨Q, hQacceptable, hQle, hQlargeQ0, _hQrefines⟩ :=
    exists_acceptableCompletion
      (G := G) Q0 terminals
      (threshold := w0) (cap := cap) (D := D)
      (by
        dsimp [D]
        nlinarith)
      hupper hpre
  refine ⟨Q, ?_, ?_, ?_⟩
  · simpa [k, w0, D] using hQacceptable
  · unfold DropsByOne at hdrop0 ⊢
    have hQle' :
        clusteringPotential G Q
            (sourceBoundedContribution w0 cap ell0
              hthreshold hcap hthresholdCap hell0) ≤
          clusteringPotential G Q0
            (sourceBoundedContribution w0 cap ell0
              hthreshold hcap hthresholdCap hell0) := by
      simpa [sourceBoundedContribution, boundedContribution,
        hsize, D, w0] using hQle
    change
      clusteringPotential G Q
          (sourceBoundedContribution w0 cap ell0
            hthreshold hcap hthresholdCap hell0) + 1 ≤
        clusteringPotential G P
          (sourceBoundedContribution w0 cap ell0
            hthreshold hcap hthresholdCap hell0)
    linarith
  · intro C hCQ hClarge
    exact denseReplacement_large_part_subset_selectedUnion
      (G := G) P B terminals hgood
      (hQlargeQ0 C hCQ hClarge) hClarge

end ChekuriChuzhoySection5Claim510
end SimpleGraph

end Lax17Proofs
