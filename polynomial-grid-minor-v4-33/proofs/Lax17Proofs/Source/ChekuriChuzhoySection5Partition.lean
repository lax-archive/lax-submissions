import Lax17Proofs.Source.ChekuriChuzhoySection5DenseBlockReplacement
import Lax17Proofs.Source.ChekuriChuzhoySection5Rho

namespace Lax17Proofs

universe u v w

/-!
# PARTITION and bandwidth-decomposition potential accounting

This file formalizes Theorem 5.5 and the potential part of journal
Claim 5.6.  A split replaces one block by the two sides of a sparse cut.
The inherited old boundary pays for the newly crossing cut edges.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Partition


open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5BandwidthDecomposition
open ChekuriChuzhoySection5DenseBlockReplacement
open ChekuriChuzhoySection5SourcePotential
open ChekuriChuzhoySection5Rho

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Replace one clustering block by the two sides of a violating cut. -/
noncomputable def splitClustering
    (P : VertexClustering V) {C : Finset V}
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    VertexClustering V :=
  replacementClustering P C
    (ScaledViolatingPartition.pairFinpartition cut)

theorem splitClustering_block_eq_left
    (P : VertexClustering V) {C : Finset V}
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    {v : V} (hv : v ∈ cut.X) :
    (splitClustering P cut).block v = cut.X := by
  rw [splitClustering,
    replacementClustering_block_eq_qc_part P C
      (ScaledViolatingPartition.pairFinpartition cut)
      (cut.left_subset hv)]
  apply (ScaledViolatingPartition.pairFinpartition cut).part_eq_of_mem
  · simp [ScaledViolatingPartition.pairFinpartition]
  · exact hv

theorem splitClustering_block_eq_right
    (P : VertexClustering V) {C : Finset V}
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    {v : V} (hv : v ∈ cut.Y) :
    (splitClustering P cut).block v = cut.Y := by
  rw [splitClustering,
    replacementClustering_block_eq_qc_part P C
      (ScaledViolatingPartition.pairFinpartition cut)
      (cut.right_subset hv)]
  apply (ScaledViolatingPartition.pairFinpartition cut).part_eq_of_mem
  · simp [ScaledViolatingPartition.pairFinpartition]
  · exact hv

theorem splitClustering_block_eq_old_of_not_mem
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    {v : V} (hv : v ∉ C) :
    (splitClustering P cut).block v = P.block v := by
  have hne : P.block v ≠ C := by
    intro h
    exact hv (h ▸ P.mem_block v)
  have hdisjoint : Disjoint (P.block v) C :=
    P.disjoint (P.block_mem_parts v) hC hne
  apply (splitClustering P cut).block_eq_of_mem
  · rw [splitClustering, replacementClustering_parts]
    apply Finset.mem_union_left
    rw [Finpartition.mem_avoid]
    exact ⟨P.block v, P.block_mem_parts v,
      fun hsub => hv (hsub (P.mem_block v)),
      Finset.sdiff_eq_self_of_disjoint hdisjoint⟩
  · exact P.mem_block v

/-- Replacing a part by the two sides of a partition refines the original
clustering. -/
theorem splitClustering_le
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    splitClustering P cut ≤ P := by
  intro R hR
  rcases (splitClustering P cut).nonempty_of_mem_parts hR with
    ⟨v, hvR⟩
  by_cases hvC : v ∈ C
  · refine ⟨C, hC, ?_⟩
    intro x hx
    have hblock :
        (splitClustering P cut).block x =
          (splitClustering P cut).block v :=
      ((splitClustering P cut).block_eq_of_mem hR hx).trans
        ((splitClustering P cut).block_eq_of_mem hR hvR).symm
    have hvSides : v ∈ cut.X ∨ v ∈ cut.Y := by
      have : v ∈ cut.X ∪ cut.Y := cut.cover.symm ▸ hvC
      exact Finset.mem_union.mp this
    rcases hvSides with hvX | hvY
    · have hvBlock :
          (splitClustering P cut).block v = cut.X :=
        splitClustering_block_eq_left P cut hvX
      have hxX : x ∈ cut.X := by
        rw [← hvBlock, ← hblock]
        exact (splitClustering P cut).mem_block x
      exact cut.left_subset hxX
    · have hvBlock :
          (splitClustering P cut).block v = cut.Y :=
        splitClustering_block_eq_right P cut hvY
      have hxY : x ∈ cut.Y := by
        rw [← hvBlock, ← hblock]
        exact (splitClustering P cut).mem_block x
      exact cut.right_subset hxY
  · refine ⟨P.block v, P.block_mem_parts v, ?_⟩
    intro x hx
    have hblock :
        (splitClustering P cut).block x =
          (splitClustering P cut).block v :=
      ((splitClustering P cut).block_eq_of_mem hR hx).trans
        ((splitClustering P cut).block_eq_of_mem hR hvR).symm
    have hvBlock :
        (splitClustering P cut).block v = P.block v :=
      splitClustering_block_eq_old_of_not_mem P hC cut hvC
    rw [← hvBlock, ← hblock]
    exact (splitClustering P cut).mem_block x

theorem splitClustering_boundarySize_left
    (P : VertexClustering V) {C : Finset V}
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    {v : V} (hv : v ∈ cut.X) :
    endpointBoundarySize G (splitClustering P cut) v =
      (inheritedBoundary G cut.X cut.Y).card +
        (Section44.edgeBoundary G cut.X cut.Y).card := by
  rw [endpointBoundarySize, splitClustering_block_eq_left P cut hv]
  exact (inheritedBoundary_card_add_cut
    (G := G) cut.disjoint).symm

theorem splitClustering_boundarySize_right
    (P : VertexClustering V) {C : Finset V}
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    {v : V} (hv : v ∈ cut.Y) :
    endpointBoundarySize G (splitClustering P cut) v =
      (inheritedBoundary G cut.Y cut.X).card +
        (Section44.edgeBoundary G cut.X cut.Y).card := by
  rw [endpointBoundarySize, splitClustering_block_eq_right P cut hv]
  have h := inheritedBoundary_card_add_cut
    (G := G) cut.disjoint.symm
  rw [Section44.edgeBoundary_comm] at h
  exact h.symm

/-- Swapping the two names of a cut does not change the resulting
two-block replacement. -/
theorem splitClustering_swap
    (P : VertexClustering V) {C : Finset V}
    {cap alphaNum alphaDen : Nat}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    splitClustering P cut.swap = splitClustering P cut := by
  unfold splitClustering
  congr 1
  apply Finpartition.ext
  ext A
  simp [ScaledViolatingPartition.pairFinpartition,
    ScaledViolatingPartition.swap, or_comm]

theorem old_boundarySize_eq
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {v : V} (hv : v ∈ C) :
    endpointBoundarySize G P v =
      (Section44.clusterBoundary G C).card := by
  rw [endpointBoundarySize, P.block_eq_of_mem hC hv]
  rfl

/-- The sparse inequality for ratio `1/D` implies the three cleared
inequalities used by the local charge lemmas. -/
theorem violating_cut_numerics
    {C : Finset V} {cap D : Nat}
    (cut : ScaledViolatingPartition G C cap 1 D) :
    D * (Section44.edgeBoundary G cut.X cut.Y).card <
        (inheritedBoundary G cut.X cut.Y).card ∧
      D * (Section44.edgeBoundary G cut.X cut.Y).card <
        (inheritedBoundary G cut.Y cut.X).card ∧
      D * (Section44.edgeBoundary G cut.X cut.Y).card < cap := by
  have hleft :=
    truncatedInterfaceDemand_le_inheritedBoundary_left
      (G := G) cut.cover cut.disjoint cap
  have hright :=
    truncatedInterfaceDemand_le_inheritedBoundary_right
      (G := G) cut.cover cut.disjoint cap
  have hcap :=
    truncatedInterfaceDemand_le_cap G C cut.X cut.Y cap
  have hsparse := cut.sparse
  simp only [one_mul] at hsparse
  exact ⟨hsparse.trans_le hleft,
    hsparse.trans_le hright,
    hsparse.trans_le hcap⟩

/-- Either child of a ratio-`1/D` violating split has no larger outer
boundary than its parent. -/
theorem violating_left_boundary_le
    {C : Finset V} {cap D : Nat} (hD : 1 ≤ D)
    (cut : ScaledViolatingPartition G C cap 1 D) :
    (Section44.clusterBoundary G cut.X).card ≤
      (Section44.clusterBoundary G C).card := by
  let a := (inheritedBoundary G cut.X cut.Y).card
  let b := (inheritedBoundary G cut.Y cut.X).card
  let c := (Section44.edgeBoundary G cut.X cut.Y).card
  have hz := inheritedBoundary_card_add
    (G := G) cut.cover cut.disjoint
  have hn := violating_cut_numerics (G := G) cut
  have hc_le_b : c ≤ b := by
    have hcD : c ≤ D * c := by
      calc
        c = 1 * c := by simp
        _ ≤ D * c := Nat.mul_le_mul_right c hD
    exact hcD.trans hn.2.1.le
  have hx := inheritedBoundary_card_add_cut
    (G := G) cut.disjoint
  dsimp [a, b, c] at hz hc_le_b
  omega

theorem violating_right_boundary_le
    {C : Finset V} {cap D : Nat} (hD : 1 ≤ D)
    (cut : ScaledViolatingPartition G C cap 1 D) :
    (Section44.clusterBoundary G cut.Y).card ≤
      (Section44.clusterBoundary G C).card := by
  have h := violating_left_boundary_le
    (G := G) hD cut.swap
  simpa [Section44.edgeBoundary_comm] using h

/-- Edgewise core of the source-potential split calculation, oriented so
that the left inherited boundary pays the cut charge. -/
theorem splitClustering_potential_le_of_left_charge
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {w0 D cap : Nat} (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (cut : ScaledViolatingPartition G C cap 1 D)
    (hcharge :
      (11 : Rat) / 10 *
          (Section44.edgeBoundary G cut.X cut.Y).card ≤
        (rho w0 D (Section44.clusterBoundary G C).card -
            rho w0 D
              ((inheritedBoundary G cut.X cut.Y).card +
                (Section44.edgeBoundary G cut.X cut.Y).card)) *
          (inheritedBoundary G cut.X cut.Y).card)
    (hcut_lt :
      (Section44.edgeBoundary G cut.X cut.Y).card <
        (inheritedBoundary G cut.X cut.Y).card) :
    clusteringPotential G (splitClustering P cut)
        (boundedContributionOfUpper w0 D (by omega) hupper) ≤
      clusteringPotential G P
        (boundedContributionOfUpper w0 D (by omega) hupper) := by
  classical
  let schedule := boundedContributionOfUpper w0 D (by omega) hupper
  let a := (inheritedBoundary G cut.X cut.Y).card
  let b := (inheritedBoundary G cut.Y cut.X).card
  let c := (Section44.edgeBoundary G cut.X cut.Y).card
  let z := (Section44.clusterBoundary G C).card
  let gap := rho w0 D z - rho w0 D (a + c)
  have hz : z = a + b := by
    dsimp [z, a, b]
    exact (inheritedBoundary_card_add
      (G := G) cut.cover cut.disjoint).symm
  have hcharge' : (11 : Rat) / 10 * c ≤ gap * a := by
    simpa [gap, a, c, z] using hcharge
  apply clusteringPotential_le_of_split_edge_accounting
    (G := G) P (splitClustering P cut) schedule
    (inheritedBoundary G cut.X cut.Y)
    (Section44.edgeBoundary G cut.X cut.Y) gap
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        exact mem_sourceEdgeFinset.mpr <| by
          have hboundary := (Finset.mem_sdiff.mp he).1
          simpa [_root_.SimpleGraph.mem_edgeSet] using
            ((mk_mem_clusterBoundary_iff G cut.X u v).1 hboundary).1
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        exact mem_sourceEdgeFinset.mpr <| by
          simpa [_root_.SimpleGraph.mem_edgeSet] using
            ((mk_mem_edgeBoundary_iff G cut.X cut.Y u v).1 he).1
  · simpa [a, c] using hcharge'
  · intro e heG
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using heG
      have hside (x : V) : x ∈ cut.X ∨ x ∈ cut.Y ∨ x ∉ C := by
        by_cases hxC : x ∈ C
        · have : x ∈ cut.X ∪ cut.Y := cut.cover.symm ▸ hxC
          exact (Finset.mem_union.mp this).elim Or.inl
            (fun h => Or.inr (Or.inl h))
        · exact Or.inr (Or.inr hxC)
      have hXnotY {x : V} (hx : x ∈ cut.X) : x ∉ cut.Y :=
        fun hy => Finset.disjoint_left.mp cut.disjoint hx hy
      have hYnotX {x : V} (hy : x ∈ cut.Y) : x ∉ cut.X :=
        fun hx => Finset.disjoint_left.mp cut.disjoint hx hy
      have hXC : cut.X ⊆ C := cut.left_subset
      have hYC : cut.Y ⊆ C := cut.right_subset
      have hXY : cut.X ≠ cut.Y := by
        intro h
        rcases ScaledViolatingPartition.left_nonempty cut with ⟨x, hx⟩
        exact hXnotY hx (h ▸ hx)
      have holdOut {x : V} (hx : x ∉ C) : P.block x ≠ C := by
        intro h
        exact hx (h ▸ P.mem_block x)
      have hnewXOut {x y : V} (hx : x ∈ cut.X) (hy : y ∉ C) :
          (splitClustering P cut).block x ≠
            (splitClustering P cut).block y := by
        rw [splitClustering_block_eq_left P cut hx,
          splitClustering_block_eq_old_of_not_mem P hC cut hy]
        intro h
        exact hy (h ▸ P.mem_block y |> hXC)
      have hnewYOut {x y : V} (hx : x ∈ cut.Y) (hy : y ∉ C) :
          (splitClustering P cut).block x ≠
            (splitClustering P cut).block y := by
        rw [splitClustering_block_eq_right P cut hx,
          splitClustering_block_eq_old_of_not_mem P hC cut hy]
        intro h
        exact hy (h ▸ P.mem_block y |> hYC)
      have houtSize {x : V} (hx : x ∉ C) :
          endpointBoundarySize G (splitClustering P cut) x =
            endpointBoundarySize G P x := by
        rw [endpointBoundarySize,
          splitClustering_block_eq_old_of_not_mem P hC cut hx]
        rfl
      have hrightBoundary :
          b + c ≤ z := by
        have hc_lt_a : c < a := by simpa [a, c] using hcut_lt
        omega
      have hnotRel_bothC {x y : V} (hx : x ∈ C) (hy : y ∈ C) :
          s(x, y) ∉ inheritedBoundary G cut.X cut.Y := by
        intro he
        rcases (mk_mem_inheritedBoundary_iff
          (G := G) cut.cover cut.disjoint x y).1 he with
          ⟨_, h | h⟩
        · exact h.2 hy
        · exact h.2 hx
      have hnotRel_neX {x y : V} (hx : x ∉ cut.X) (hy : y ∉ cut.X) :
          s(x, y) ∉ inheritedBoundary G cut.X cut.Y := by
        intro he
        rcases (mk_mem_inheritedBoundary_iff
          (G := G) cut.cover cut.disjoint x y).1 he with
          ⟨_, h | h⟩
        · exact hx h.1
        · exact hy h.1
      have hnotCut_sameX {x y : V} (hx : x ∈ cut.X) (hy : y ∈ cut.X) :
          s(x, y) ∉ Section44.edgeBoundary G cut.X cut.Y := by
        intro he
        rcases (mk_mem_edgeBoundary_iff G cut.X cut.Y x y).1 he with
          ⟨_, h | h⟩
        · exact hXnotY hy h.2
        · exact hXnotY hx h.2
      have hnotCut_sameY {x y : V} (hx : x ∈ cut.Y) (hy : y ∈ cut.Y) :
          s(x, y) ∉ Section44.edgeBoundary G cut.X cut.Y := by
        intro he
        rcases (mk_mem_edgeBoundary_iff G cut.X cut.Y x y).1 he with
          ⟨_, h | h⟩
        · exact hYnotX hx h.1
        · exact hYnotX hy h.1
      have hnotCut_out_left {x y : V} (hx : x ∉ C) :
          s(x, y) ∉ Section44.edgeBoundary G cut.X cut.Y := by
        intro he
        rcases (mk_mem_edgeBoundary_iff G cut.X cut.Y x y).1 he with
          ⟨_, h | h⟩
        · exact hx (hXC h.1)
        · exact hx (hYC h.2)
      have hnotCut_out_right {x y : V} (hy : y ∉ C) :
          s(x, y) ∉ Section44.edgeBoundary G cut.X cut.Y := by
        intro he
        rcases (mk_mem_edgeBoundary_iff G cut.X cut.Y x y).1 he with
          ⟨_, h | h⟩
        · exact hy (hYC h.2)
        · exact hy (hXC h.1)
      rcases hside u with huX | huY | huO <;>
        rcases hside v with hvX | hvY | hvO
      · have hP : P.block u = P.block v := by
          rw [P.block_eq_of_mem hC (hXC huX),
            P.block_eq_of_mem hC (hXC hvX)]
        have hQ : (splitClustering P cut).block u =
            (splitClustering P cut).block v := by
          rw [splitClustering_block_eq_left P cut huX,
            splitClustering_block_eq_left P cut hvX]
        have hrel := hnotRel_bothC (hXC huX) (hXC hvX)
        have hadd := hnotCut_sameX huX hvX
        simp [ChekuriChuzhoySection5SourcePotential.edgePotential_mk,
          hP, hQ, hrel, hadd]
      · have hP : P.block u = P.block v := by
          rw [P.block_eq_of_mem hC (hXC huX),
            P.block_eq_of_mem hC (hYC hvY)]
        have hQ : (splitClustering P cut).block u ≠
            (splitClustering P cut).block v := by
          rw [splitClustering_block_eq_left P cut huX,
            splitClustering_block_eq_right P cut hvY]
          exact hXY
        have hrel := hnotRel_bothC (hXC huX) (hYC hvY)
        have hadd : s(u, v) ∈ Section44.edgeBoundary G cut.X cut.Y :=
          (mk_mem_edgeBoundary_iff G cut.X cut.Y u v).2
            ⟨huv, Or.inl ⟨huX, hvY⟩⟩
        simp only [if_neg hQ, if_pos hP, if_neg hrel, if_pos hadd,
          add_zero, zero_add]
        have hupperEdge := edgePotential_le_eleven_tenths_of_crosses
          (G := G) (splitClustering P cut) schedule
          (e := s(u, v)) (by simpa only [crossesBlocks_mk] using hQ)
        have holdNonnegative :=
          edgePotential_nonnegative (G := G) P schedule s(u, v)
        linarith
      · have hP : P.block u ≠ P.block v := by
          rw [P.block_eq_of_mem hC (hXC huX)]
          exact (holdOut hvO).symm
        have hQ := hnewXOut huX hvO
        have hrel : s(u, v) ∈ inheritedBoundary G cut.X cut.Y :=
          (mk_mem_inheritedBoundary_iff
            (G := G) cut.cover cut.disjoint u v).2
              ⟨huv, Or.inl ⟨huX, hvO⟩⟩
        have hadd := hnotCut_out_right (x := u) hvO
        rw [edgePotential_eq_of_crosses
            (G := G) (splitClustering P cut) schedule hQ,
          edgePotential_eq_of_crosses (G := G) P schedule hP,
          if_pos hrel, if_neg hadd,
          splitClustering_boundarySize_left P cut huX,
          old_boundarySize_eq P hC (hXC huX), houtSize hvO]
        simp only [schedule, boundedContributionOfUpper, gap, a, c, z]
        ring_nf
        exact le_rfl
      · have hP : P.block u = P.block v := by
          rw [P.block_eq_of_mem hC (hYC huY),
            P.block_eq_of_mem hC (hXC hvX)]
        have hQ : (splitClustering P cut).block u ≠
            (splitClustering P cut).block v := by
          rw [splitClustering_block_eq_right P cut huY,
            splitClustering_block_eq_left P cut hvX]
          exact hXY.symm
        have hrel := hnotRel_bothC (hYC huY) (hXC hvX)
        have hadd : s(u, v) ∈ Section44.edgeBoundary G cut.X cut.Y :=
          (mk_mem_edgeBoundary_iff G cut.X cut.Y u v).2
            ⟨huv, Or.inr ⟨hvX, huY⟩⟩
        simp only [if_neg hQ, if_pos hP, if_neg hrel, if_pos hadd,
          add_zero, zero_add]
        have hupperEdge := edgePotential_le_eleven_tenths_of_crosses
          (G := G) (splitClustering P cut) schedule
          (e := s(u, v)) (by simpa only [crossesBlocks_mk] using hQ)
        have holdNonnegative :=
          edgePotential_nonnegative (G := G) P schedule s(u, v)
        linarith
      · have hP : P.block u = P.block v := by
          rw [P.block_eq_of_mem hC (hYC huY),
            P.block_eq_of_mem hC (hYC hvY)]
        have hQ : (splitClustering P cut).block u =
            (splitClustering P cut).block v := by
          rw [splitClustering_block_eq_right P cut huY,
            splitClustering_block_eq_right P cut hvY]
        have hrel := hnotRel_neX (hYnotX huY) (hYnotX hvY)
        have hadd := hnotCut_sameY huY hvY
        simp [ChekuriChuzhoySection5SourcePotential.edgePotential_mk,
          hP, hQ, hrel, hadd]
      · have hP : P.block u ≠ P.block v := by
          rw [P.block_eq_of_mem hC (hYC huY)]
          exact (holdOut hvO).symm
        have hQ := hnewYOut huY hvO
        have hrel := hnotRel_neX (hYnotX huY)
          (fun hvX => hvO (hXC hvX))
        have hadd := hnotCut_out_right (x := u) hvO
        rw [edgePotential_eq_of_crosses
            (G := G) (splitClustering P cut) schedule hQ,
          edgePotential_eq_of_crosses (G := G) P schedule hP,
          if_neg hrel, if_neg hadd,
          splitClustering_boundarySize_right P cut huY,
          old_boundarySize_eq P hC (hYC huY), houtSize hvO]
        simp only [schedule, boundedContributionOfUpper, b, c, z]
        have hmono := rho_mono (w0 := w0) (D := D) (by omega)
          hrightBoundary
        linarith
      · have hP : P.block u ≠ P.block v := by
          exact ne_comm.mp <| by
            rw [P.block_eq_of_mem hC (hXC hvX)]
            exact (holdOut huO).symm
        have hQ : (splitClustering P cut).block u ≠
            (splitClustering P cut).block v :=
          ne_comm.mp (hnewXOut hvX huO)
        have hrel : s(u, v) ∈ inheritedBoundary G cut.X cut.Y :=
          (mk_mem_inheritedBoundary_iff
            (G := G) cut.cover cut.disjoint u v).2
              ⟨huv, Or.inr ⟨hvX, huO⟩⟩
        have hadd := hnotCut_out_left (y := v) huO
        rw [edgePotential_eq_of_crosses
            (G := G) (splitClustering P cut) schedule hQ,
          edgePotential_eq_of_crosses (G := G) P schedule hP,
          if_pos hrel, if_neg hadd,
          splitClustering_boundarySize_left P cut hvX,
          old_boundarySize_eq P hC (hXC hvX), houtSize huO]
        simp only [schedule, boundedContributionOfUpper, gap, a, c, z]
        ring_nf
        exact le_rfl
      · have hP : P.block u ≠ P.block v := by
          exact ne_comm.mp <| by
            rw [P.block_eq_of_mem hC (hYC hvY)]
            exact (holdOut huO).symm
        have hQ : (splitClustering P cut).block u ≠
            (splitClustering P cut).block v :=
          ne_comm.mp (hnewYOut hvY huO)
        have hrel := hnotRel_neX
          (fun huX => huO (hXC huX)) (hYnotX hvY)
        have hadd := hnotCut_out_left (y := v) huO
        rw [edgePotential_eq_of_crosses
            (G := G) (splitClustering P cut) schedule hQ,
          edgePotential_eq_of_crosses (G := G) P schedule hP,
          if_neg hrel, if_neg hadd,
          splitClustering_boundarySize_right P cut hvY,
          old_boundarySize_eq P hC (hYC hvY), houtSize huO]
        simp only [schedule, boundedContributionOfUpper, b, c, z]
        have hmono := rho_mono (w0 := w0) (D := D) (by omega)
          hrightBoundary
        linarith
      · have hblocksU :=
          splitClustering_block_eq_old_of_not_mem P hC cut huO
        have hblocksV :=
          splitClustering_block_eq_old_of_not_mem P hC cut hvO
        have hrel := hnotRel_neX
          (fun huX => huO (hXC huX)) (fun hvX => hvO (hXC hvX))
        have hadd := hnotCut_out_left (y := v) huO
        rw [ChekuriChuzhoySection5SourcePotential.edgePotential_mk,
          ChekuriChuzhoySection5SourcePotential.edgePotential_mk,
          hblocksU, hblocksV, houtSize huO, houtSize hvO,
          if_neg hrel, if_neg hadd]

/-- The oriented single-iteration calculation in Theorem 5.5. -/
theorem splitClustering_potential_le_of_left_small
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {w0 D cap : Nat} (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (cut : ScaledViolatingPartition G C cap 1 D)
    (hleft :
      (inheritedBoundary G cut.X cut.Y).card ≤
        (inheritedBoundary G cut.Y cut.X).card)
    (hsmall : (Section44.clusterBoundary G C).card < w0) :
    clusteringPotential G (splitClustering P cut)
        (boundedContributionOfUpper w0 D (by omega) hupper) ≤
      clusteringPotential G P
        (boundedContributionOfUpper w0 D (by omega) hupper) := by
  let a := (inheritedBoundary G cut.X cut.Y).card
  let b := (inheritedBoundary G cut.Y cut.X).card
  let c := (Section44.edgeBoundary G cut.X cut.Y).card
  let z := (Section44.clusterBoundary G C).card
  have hz : z = a + b := by
    dsimp [z, a, b]
    exact (inheritedBoundary_card_add
      (G := G) cut.cover cut.disjoint).symm
  have hsparse : D * c < a :=
    (violating_cut_numerics (G := G) cut).1
  have hcut_lt : c < a := by
    have hc_le : c ≤ D * c := by
      calc
        c = 1 * c := by simp
        _ ≤ D * c := Nat.mul_le_mul_right c (by omega)
    exact hc_le.trans_lt hsparse
  apply splitClustering_potential_le_of_left_charge
    (G := G) P hC hD hupper cut
  · have h := small_split_charge hD hz
      (by simpa [a, b] using hleft) hsparse
      (by simpa [z] using hsmall)
    simpa [a, c, z, mul_comm] using h
  · simpa [a, c] using hcut_lt

/-- One arbitrary sparse split of a small cluster does not increase the
source potential. -/
theorem splitClustering_potential_le_small
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {w0 D cap : Nat} (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (cut : ScaledViolatingPartition G C cap 1 D)
    (hsmall : (Section44.clusterBoundary G C).card < w0) :
    clusteringPotential G (splitClustering P cut)
        (boundedContributionOfUpper w0 D (by omega) hupper) ≤
      clusteringPotential G P
        (boundedContributionOfUpper w0 D (by omega) hupper) := by
  by_cases hleft :
      (inheritedBoundary G cut.X cut.Y).card ≤
        (inheritedBoundary G cut.Y cut.X).card
  · exact splitClustering_potential_le_of_left_small
      (G := G) P hC hD hupper cut hleft hsmall
  · have hright :
        (inheritedBoundary G cut.Y cut.X).card ≤
          (inheritedBoundary G cut.X cut.Y).card := by omega
    have h :=
      splitClustering_potential_le_of_left_small
        (G := G) P hC hD hupper cut.swap (by simpa using hright) hsmall
    simpa [splitClustering_swap (G := G) P cut] using h

/-- The oriented potential calculation for PARTITION in Claim 5.6. -/
theorem splitClustering_potential_le_of_left_large
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {w0 D : Nat} (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (cut : ScaledViolatingPartition G C (w0 / 2) 1 D)
    (hleft :
      (inheritedBoundary G cut.X cut.Y).card ≤
        (inheritedBoundary G cut.Y cut.X).card)
    (hlarge : w0 ≤ (Section44.clusterBoundary G C).card) :
    clusteringPotential G (splitClustering P cut)
        (boundedContributionOfUpper w0 D (by omega) hupper) ≤
      clusteringPotential G P
        (boundedContributionOfUpper w0 D (by omega) hupper) := by
  let a := (inheritedBoundary G cut.X cut.Y).card
  let b := (inheritedBoundary G cut.Y cut.X).card
  let c := (Section44.edgeBoundary G cut.X cut.Y).card
  let z := (Section44.clusterBoundary G C).card
  have hz : z = a + b := by
    dsimp [z, a, b]
    exact (inheritedBoundary_card_add
      (G := G) cut.cover cut.disjoint).symm
  have hn := violating_cut_numerics (G := G) cut
  have hsparse : D * c < a := hn.1
  have hcap : 2 * D * c < w0 := by
    have : D * c < w0 / 2 := hn.2.2
    rw [Nat.mul_assoc]
    omega
  have hcut_lt : c < a := by
    have hc_le : c ≤ D * c := by
      calc
        c = 1 * c := by simp
        _ ≤ D * c := Nat.mul_le_mul_right c (by omega)
    exact hc_le.trans_lt hsparse
  apply splitClustering_potential_le_of_left_charge
    (G := G) P hC hD hupper cut
  · by_cases hchild : w0 ≤ a + c
    · have h := large_split_charge hD hz
        (by simpa [a, b] using hleft) hsparse hcap
        (by simpa [z] using hlarge) hchild
      simpa [a, c, z, mul_comm] using h
    · have hchild' : a + c < w0 := by omega
      have h := large_to_small_split_charge hD hsparse
        (by simpa [z] using hlarge) hchild'
      simpa [a, c, z, mul_comm] using h
  · simpa [a, c] using hcut_lt

/-- Claim 5.6's potential comparison for an arbitrary orientation of the
large-cluster violating partition. -/
theorem splitClustering_potential_le_large
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {w0 D : Nat} (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (cut : ScaledViolatingPartition G C (w0 / 2) 1 D)
    (hlarge : w0 ≤ (Section44.clusterBoundary G C).card) :
    clusteringPotential G (splitClustering P cut)
        (boundedContributionOfUpper w0 D (by omega) hupper) ≤
      clusteringPotential G P
        (boundedContributionOfUpper w0 D (by omega) hupper) := by
  by_cases hleft :
      (inheritedBoundary G cut.X cut.Y).card ≤
        (inheritedBoundary G cut.Y cut.X).card
  · exact splitClustering_potential_le_of_left_large
      (G := G) P hC hD hupper cut hleft hlarge
  · have hright :
        (inheritedBoundary G cut.Y cut.X).card ≤
          (inheritedBoundary G cut.X cut.Y).card := by omega
    have h :=
      splitClustering_potential_le_of_left_large
        (G := G) P hC hD hupper cut.swap
          (by simpa using hright) hlarge
    simpa [splitClustering_swap (G := G) P cut] using h

/-! ## Recursive completion of Theorem 5.5 -/

/-- The proof data produced by recursively decomposing one old block. -/
structure BandwidthRefinement
    (G : _root_.SimpleGraph V) (P Q : VertexClustering V)
    (C : Finset V) (w0 D cap : Nat)
    (schedule : BoundedContribution) : Prop where
  refines : Q ≤ P
  potential_le :
    clusteringPotential G Q schedule ≤
      clusteringPotential G P schedule
  outside_block :
    ∀ ⦃v⦄, v ∉ C → Q.block v = P.block v
  inside_subset :
    ∀ ⦃v⦄, v ∈ C → Q.block v ⊆ C
  inside_bandwidth :
    ∀ ⦃v⦄, v ∈ C →
      TruncatedScaledBandwidth G (Q.block v) cap 1 D
  inside_boundary :
    ∀ ⦃v⦄, v ∈ C →
      (Section44.clusterBoundary G (Q.block v)).card ≤
        (Section44.clusterBoundary G C).card

/-- Theorem 5.5, in the form consumed by PARTITION and SEPARATE: a small
block can be completely decomposed to bandwidth blocks without increasing
the source potential.  The recursion is on strict subsets furnished by the
two sides of each violating partition. -/
theorem exists_bandwidthRefinement
    (P : VertexClustering V) (C : Finset V) (hC : C ∈ P.parts)
    {w0 D cap : Nat} (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (hsmall : (Section44.clusterBoundary G C).card < w0) :
    ∃ Q : VertexClustering V,
      BandwidthRefinement G P Q C w0 D cap
        (boundedContributionOfUpper w0 D (by omega) hupper) := by
  classical
  let schedule := boundedContributionOfUpper w0 D (by omega) hupper
  let motive : Finset V → Prop := fun C =>
    ∀ (P : VertexClustering V), C ∈ P.parts →
      (Section44.clusterBoundary G C).card < w0 →
      ∃ Q : VertexClustering V,
        BandwidthRefinement G P Q C w0 D cap schedule
  refine Finset.strongInductionOn (p := motive) C ?_ P hC hsmall
  intro C ih P hC hsmall
  by_cases hband : TruncatedScaledBandwidth G C cap 1 D
  · refine ⟨P, ?_⟩
    refine {
      refines := le_rfl
      potential_le := le_rfl
      outside_block := by
        intro v _
        rfl
      inside_subset := ?_
      inside_bandwidth := ?_
      inside_boundary := ?_ }
    · intro v hv
      rw [P.block_eq_of_mem hC hv]
    · intro v hv
      simpa [P.block_eq_of_mem hC hv] using hband
    · intro v hv
      rw [P.block_eq_of_mem hC hv]
  · let cut : ScaledViolatingPartition G C cap 1 D :=
      Classical.choice <|
        (not_truncatedScaledBandwidth_iff_exists_violating
          (G := G) (C := C) (cap := cap)
          (by decide) (by omega)).mp hband
    let Q0 := splitClustering P cut
    have hQ0potential :
        clusteringPotential G Q0 schedule ≤
          clusteringPotential G P schedule := by
      simpa [Q0, schedule] using
        splitClustering_potential_le_small
          (G := G) P hC hD hupper cut hsmall
    have hXsmall :
        (Section44.clusterBoundary G cut.X).card < w0 :=
      lt_of_le_of_lt
        (violating_left_boundary_le (G := G) (by omega) cut) hsmall
    have hYsmall :
        (Section44.clusterBoundary G cut.Y).card < w0 :=
      lt_of_le_of_lt
        (violating_right_boundary_le (G := G) (by omega) cut) hsmall
    have hXssub : cut.X ⊂ C := by
      exact Finset.ssubset_iff_subset_ne.mpr
        ⟨cut.left_subset, fun h =>
          (ScaledViolatingPartition.left_card_lt cut).ne
            (congrArg Finset.card h)⟩
    have hYssub : cut.Y ⊂ C := by
      exact Finset.ssubset_iff_subset_ne.mpr
        ⟨cut.right_subset, fun h =>
          (ScaledViolatingPartition.right_card_lt cut).ne
            (congrArg Finset.card h)⟩
    rcases ScaledViolatingPartition.left_nonempty cut with ⟨x, hx⟩
    have hXpart : cut.X ∈ Q0.parts := by
      have hxBlock : Q0.block x = cut.X := by
        simpa [Q0] using splitClustering_block_eq_left P cut hx
      rw [← hxBlock]
      exact Q0.block_mem_parts x
    obtain ⟨Q1, hQ1⟩ := ih cut.X hXssub Q0 hXpart hXsmall
    rcases ScaledViolatingPartition.right_nonempty cut with ⟨y, hy⟩
    have hyNotX : y ∉ cut.X :=
      fun hyX => Finset.disjoint_left.mp cut.disjoint hyX hy
    have hYpart : cut.Y ∈ Q1.parts := by
      have hyQ1 : Q1.block y = Q0.block y :=
        hQ1.outside_block hyNotX
      have hyQ0 : Q0.block y = cut.Y := by
        simpa [Q0] using splitClustering_block_eq_right P cut hy
      have hmem := Q1.block_mem_parts y
      rw [hyQ1, hyQ0] at hmem
      exact hmem
    obtain ⟨Q2, hQ2⟩ := ih cut.Y hYssub Q1 hYpart hYsmall
    refine ⟨Q2, ?_⟩
    refine {
      refines := hQ2.refines.trans (hQ1.refines.trans ?_)
      potential_le := hQ2.potential_le.trans
        (hQ1.potential_le.trans hQ0potential)
      outside_block := ?_
      inside_subset := ?_
      inside_bandwidth := ?_
      inside_boundary := ?_ }
    · intro R hR
      rcases Q0.nonempty_of_mem_parts hR with ⟨v, hvR⟩
      by_cases hvC : v ∈ C
      · have hvSides : v ∈ cut.X ∨ v ∈ cut.Y := by
          have : v ∈ cut.X ∪ cut.Y := cut.cover.symm ▸ hvC
          exact Finset.mem_union.mp this
        refine ⟨C, hC, ?_⟩
        intro x hx
        have hblock :
            Q0.block x = Q0.block v :=
          (Q0.block_eq_of_mem hR hx).trans
            (Q0.block_eq_of_mem hR hvR).symm
        rcases hvSides with hvX | hvY
        · have hQv : Q0.block v = cut.X := by
            simpa [Q0] using splitClustering_block_eq_left P cut hvX
          have hxX : x ∈ cut.X := by
            rw [← hQv, ← hblock]
            exact Q0.mem_block x
          exact cut.left_subset hxX
        · have hQv : Q0.block v = cut.Y := by
            simpa [Q0] using splitClustering_block_eq_right P cut hvY
          have hxY : x ∈ cut.Y := by
            rw [← hQv, ← hblock]
            exact Q0.mem_block x
          exact cut.right_subset hxY
      · refine ⟨P.block v, P.block_mem_parts v, ?_⟩
        intro x hx
        have hQv :
            Q0.block v = P.block v := by
          simpa [Q0] using
            splitClustering_block_eq_old_of_not_mem P hC cut hvC
        have hblock :
            Q0.block x = Q0.block v :=
          (Q0.block_eq_of_mem hR hx).trans
            (Q0.block_eq_of_mem hR hvR).symm
        rw [← hQv, ← hblock]
        exact Q0.mem_block x
    · intro v hvC
      have hvX : v ∉ cut.X := fun h => hvC (cut.left_subset h)
      have hvY : v ∉ cut.Y := fun h => hvC (cut.right_subset h)
      rw [hQ2.outside_block hvY, hQ1.outside_block hvX]
      simpa [Q0] using
        splitClustering_block_eq_old_of_not_mem P hC cut hvC
    · intro v hvC
      have hvSides : v ∈ cut.X ∨ v ∈ cut.Y := by
        have : v ∈ cut.X ∪ cut.Y := cut.cover.symm ▸ hvC
        exact Finset.mem_union.mp this
      rcases hvSides with hvX | hvY
      · have hvNotY : v ∉ cut.Y :=
          fun h => Finset.disjoint_left.mp cut.disjoint hvX h
        rw [hQ2.outside_block hvNotY]
        exact (hQ1.inside_subset hvX).trans cut.left_subset
      · exact (hQ2.inside_subset hvY).trans cut.right_subset
    · intro v hvC
      have hvSides : v ∈ cut.X ∨ v ∈ cut.Y := by
        have : v ∈ cut.X ∪ cut.Y := cut.cover.symm ▸ hvC
        exact Finset.mem_union.mp this
      rcases hvSides with hvX | hvY
      · have hvNotY : v ∉ cut.Y :=
          fun h => Finset.disjoint_left.mp cut.disjoint hvX h
        rw [hQ2.outside_block hvNotY]
        exact hQ1.inside_bandwidth hvX
      · exact hQ2.inside_bandwidth hvY
    · intro v hvC
      have hvSides : v ∈ cut.X ∨ v ∈ cut.Y := by
        have : v ∈ cut.X ∪ cut.Y := cut.cover.symm ▸ hvC
        exact Finset.mem_union.mp this
      rcases hvSides with hvX | hvY
      · have hvNotY : v ∉ cut.Y :=
          fun h => Finset.disjoint_left.mp cut.disjoint hvX h
        rw [hQ2.outside_block hvNotY]
        exact (hQ1.inside_boundary hvX).trans
          (violating_left_boundary_le (G := G) (by omega) cut)
      · exact (hQ2.inside_boundary hvY).trans
          (violating_right_boundary_le (G := G) (by omega) cut)

/-! ## Completing every small block -/

/-- Small blocks that still require Theorem 5.5. -/
noncomputable def badBlocks
    (G : _root_.SimpleGraph V) (threshold cap D : Nat)
    (P : VertexClustering V) : Finset (Finset V) := by
  classical
  exact P.parts.filter fun C =>
    IsSmallCluster G threshold C ∧
      ¬ TruncatedScaledBandwidth G C cap 1 D

theorem mem_badBlocks
    (threshold cap D : Nat) (P : VertexClustering V)
    {C : Finset V} :
    C ∈ badBlocks G threshold cap D P ↔
      C ∈ P.parts ∧ IsSmallCluster G threshold C ∧
        ¬ TruncatedScaledBandwidth G C cap 1 D := by
  classical
  simp [badBlocks]

/-- Refining one bad block removes it and creates no new bad block. -/
theorem badBlocks_subset_erase_of_refinement
    {threshold cap D : Nat} {P Q : VertexClustering V}
    {C : Finset V}
    (hCbad : C ∈ badBlocks G threshold cap D P)
    {schedule : BoundedContribution}
    (h : BandwidthRefinement G P Q C threshold D cap schedule) :
    badBlocks G threshold cap D Q ⊆
      (badBlocks G threshold cap D P).erase C := by
  classical
  intro R hRbad
  rcases (mem_badBlocks (G := G) threshold cap D Q).1 hRbad with
    ⟨hRQ, hRsmall, hRnotBand⟩
  rcases Q.nonempty_of_mem_parts hRQ with ⟨v, hvR⟩
  have hQblock : Q.block v = R := Q.block_eq_of_mem hRQ hvR
  have hvNotC : v ∉ C := by
    intro hvC
    exact hRnotBand <| by
      rw [← hQblock]
      exact h.inside_bandwidth hvC
  have hPblock : P.block v = R := by
    rw [← hQblock, h.outside_block hvNotC]
  have hRP : R ∈ P.parts := by
    rw [← hPblock]
    exact P.block_mem_parts v
  have hRneC : R ≠ C := by
    intro hRC
    exact hvNotC (hRC ▸ hvR)
  exact Finset.mem_erase.mpr
    ⟨hRneC, (mem_badBlocks (G := G) threshold cap D P).2
      ⟨hRP, hRsmall, hRnotBand⟩⟩

theorem badBlocks_card_lt_of_refinement
    {threshold cap D : Nat} {P Q : VertexClustering V}
    {C : Finset V}
    (hCbad : C ∈ badBlocks G threshold cap D P)
    {schedule : BoundedContribution}
    (h : BandwidthRefinement G P Q C threshold D cap schedule) :
    (badBlocks G threshold cap D Q).card <
      (badBlocks G threshold cap D P).card := by
  have hcard := Finset.card_le_card
    (badBlocks_subset_erase_of_refinement (G := G) hCbad h)
  exact hcard.trans_lt (Finset.card_erase_lt_of_mem hCbad)

/-- The two acceptability fields unaffected by decomposing small blocks. -/
structure PreAcceptable
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold : Nat) (P : VertexClustering V) : Prop where
  terminal_singleton :
    ∀ t ∈ terminals, ({t} : Finset V) ∈ P.parts
  large_connected :
    ∀ C ∈ P.parts, IsLargeCluster G threshold C →
      (G.induce {v : V | v ∈ C}).Connected

theorem PreAcceptable.ofAcceptable
    {terminals : Finset V} {threshold cap alphaNum alphaDen : Nat}
    {P : VertexClustering V}
    (h : IsAcceptable G terminals threshold cap alphaNum alphaDen P) :
    PreAcceptable G terminals threshold P :=
  ⟨h.terminal_singleton, h.large_connected⟩

/-- Theorem 5.5 preserves terminal singleton blocks and all old large
connected blocks. -/
theorem PreAcceptable.refine_bad
    {terminals : Finset V} {threshold cap D : Nat}
    (hD : 1 ≤ D) {P Q : VertexClustering V} {C : Finset V}
    (hpre : PreAcceptable G terminals threshold P)
    (hCbad : C ∈ badBlocks G threshold cap D P)
    {schedule : BoundedContribution}
    (href : BandwidthRefinement G P Q C threshold D cap schedule) :
    PreAcceptable G terminals threshold Q := by
  classical
  rcases (mem_badBlocks (G := G) threshold cap D P).1 hCbad with
    ⟨hCP, hCsmall, hCnotBand⟩
  refine ⟨?_, ?_⟩
  · intro t ht
    have htBlock : P.block t = ({t} : Finset V) :=
      P.block_eq_of_mem (hpre.terminal_singleton t ht) (by simp)
    have htNotC : t ∉ C := by
      intro htC
      have hCeq : C = ({t} : Finset V) := by
        rw [← htBlock]
        exact (P.block_eq_of_mem hCP htC).symm
      apply hCnotBand
      subst C
      exact truncatedScaledBandwidth_singleton
        G t cap 1 D (by decide) hD
    have hQblock : Q.block t = ({t} : Finset V) := by
      rw [href.outside_block htNotC, htBlock]
    rw [← hQblock]
    exact Q.block_mem_parts t
  · intro R hRQ hRlarge
    rcases Q.nonempty_of_mem_parts hRQ with ⟨v, hvR⟩
    have hQblock : Q.block v = R := Q.block_eq_of_mem hRQ hvR
    have hvNotC : v ∉ C := by
      intro hvC
      have hboundary := href.inside_boundary hvC
      rw [hQblock] at hboundary
      have hRsmall : IsSmallCluster G threshold R :=
        lt_of_le_of_lt hboundary hCsmall
      exact (smallCluster_iff_not_largeCluster G threshold R).mp
        hRsmall hRlarge
    have hPblock : P.block v = R := by
      rw [← hQblock, href.outside_block hvNotC]
    have hRP : R ∈ P.parts := by
      rw [← hPblock]
      exact P.block_mem_parts v
    exact hpre.large_connected R hRP hRlarge

/-- A refinement of a small block cannot create a large block.  Consequently
every large block after one Theorem 5.5 refinement is literally an old
clustering block. -/
theorem BandwidthRefinement.large_part_mem_old
    {threshold cap D : Nat} {P Q : VertexClustering V} {C R : Finset V}
    (hCbad : C ∈ badBlocks G threshold cap D P)
    {schedule : BoundedContribution}
    (href : BandwidthRefinement G P Q C threshold D cap schedule)
    (hRQ : R ∈ Q.parts) (hRlarge : IsLargeCluster G threshold R) :
    R ∈ P.parts := by
  rcases Q.nonempty_of_mem_parts hRQ with ⟨v, hvR⟩
  have hQblock : Q.block v = R := Q.block_eq_of_mem hRQ hvR
  have hvNotC : v ∉ C := by
    intro hvC
    have hboundary := href.inside_boundary hvC
    rw [hQblock] at hboundary
    have hCsmall :=
      ((mem_badBlocks (G := G) threshold cap D P).1 hCbad).2.1
    have hRsmall : IsSmallCluster G threshold R :=
      lt_of_le_of_lt hboundary hCsmall
    exact (smallCluster_iff_not_largeCluster G threshold R).mp
      hRsmall hRlarge
  have hPblock : P.block v = R := by
    rw [← hQblock, href.outside_block hvNotC]
  rw [← hPblock]
  exact P.block_mem_parts v

/-- Simultaneously complete all small blocks.  The proof chooses, among
pre-acceptable clusterings below the initial source potential, one with the
fewest bad blocks.  A remaining bad block could be refined by Theorem 5.5,
contradicting that minimum. -/
theorem exists_acceptableCompletion
    (P : VertexClustering V) (terminals : Finset V)
    {threshold cap D : Nat} (hD : 4 ≤ D)
    (hupper : ∀ z, rho threshold D z ≤ (1 : Rat) / 20)
    (hpre : PreAcceptable G terminals threshold P) :
    ∃ Q : VertexClustering V,
      IsAcceptable G terminals threshold cap 1 D Q ∧
      clusteringPotential G Q
          (boundedContributionOfUpper threshold D (by omega) hupper) ≤
        clusteringPotential G P
          (boundedContributionOfUpper threshold D (by omega) hupper) ∧
      (∀ C ∈ Q.parts, IsLargeCluster G threshold C → C ∈ P.parts) ∧
      Q ≤ P := by
  classical
  let schedule :=
    boundedContributionOfUpper threshold D (by omega) hupper
  let Candidate : VertexClustering V → Prop := fun Q =>
    PreAcceptable G terminals threshold Q ∧
      clusteringPotential G Q schedule ≤
        clusteringPotential G P schedule ∧
      (∀ C ∈ Q.parts, IsLargeCluster G threshold C → C ∈ P.parts) ∧
      Q ≤ P
  have hex :
      ∃ n : Nat, ∃ Q : VertexClustering V,
        Candidate Q ∧ (badBlocks G threshold cap D Q).card = n :=
    ⟨(badBlocks G threshold cap D P).card, P,
      ⟨hpre, le_rfl, (fun C hC _ => hC), le_rfl⟩, rfl⟩
  let n := Nat.find hex
  obtain ⟨Q, hQcandidate, hQcard⟩ := Nat.find_spec hex
  have hQbad : badBlocks G threshold cap D Q = ∅ := by
    by_contra hne
    rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨C, hCbad⟩
    have hCsmall :=
      ((mem_badBlocks (G := G) threshold cap D Q).1 hCbad).2.1
    obtain ⟨R, hRref⟩ :=
      exists_bandwidthRefinement
        (G := G) Q C
        ((mem_badBlocks (G := G) threshold cap D Q).1 hCbad).1
        hD hupper hCsmall
    have hRpre :
        PreAcceptable G terminals threshold R :=
      hQcandidate.1.refine_bad (by omega) hCbad hRref
    have hRcandidate : Candidate R :=
      ⟨hRpre, hRref.potential_le.trans hQcandidate.2.1,
        fun U hUR hUlarge =>
          hQcandidate.2.2.1 U
            (hRref.large_part_mem_old hCbad hUR hUlarge) hUlarge,
        hRref.refines.trans hQcandidate.2.2.2⟩
    have hRlt :
        (badBlocks G threshold cap D R).card < n := by
      change (badBlocks G threshold cap D R).card < Nat.find hex
      rw [← hQcard]
      exact badBlocks_card_lt_of_refinement
        (G := G) hCbad hRref
    have hnle :
        n ≤ (badBlocks G threshold cap D R).card :=
      Nat.find_min' hex
        ⟨R, hRcandidate, rfl⟩
    omega
  refine ⟨Q, ?_, ?_, hQcandidate.2.2.1, hQcandidate.2.2.2⟩
  · refine {
      terminal_singleton := hQcandidate.1.terminal_singleton
      small_bandwidth := ?_
      large_connected := hQcandidate.1.large_connected }
    intro C hCQ hCsmall
    by_contra hnot
    have hmem :
        C ∈ badBlocks G threshold cap D Q :=
      (mem_badBlocks (G := G) threshold cap D Q).2
        ⟨hCQ, hCsmall, hnot⟩
    rw [hQbad] at hmem
    simp at hmem
  · simpa [schedule] using hQcandidate.2.1

end ChekuriChuzhoySection5Partition
end SimpleGraph

end Lax17Proofs
