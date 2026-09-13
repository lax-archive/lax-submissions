import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 clustering foundations

This module formalizes the finite combinatorial substrate of journal
Definitions 5.1--5.2, Theorem 5.5, and Claims 5.3--5.7 from
Chekuri--Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*, JACM 63(5),
2016.  It deliberately stops before the analytic estimates for the paper's
real-valued function `rho`: the potential below is natural-valued and generic
over any bounded contribution schedule.  This is enough to support a later
finite-descent proof once source-specific decrease estimates are supplied.

The graph is always the original simple graph.  A clustering is a Mathlib
`Finpartition` of `Finset.univ`, so coverage, nonempty blocks, and pairwise
disjointness are carried by the type rather than repeated as hypotheses.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Clustering


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-! ## Vertex clusterings and their original-graph boundaries -/

/-- A finite partition of all vertices into nonempty clusters. -/
abbrev VertexClustering (V : Type u) [Fintype V] [DecidableEq V] :=
  Finpartition (Finset.univ : Finset V)

/-- The unique cluster containing a vertex. -/
def VertexClustering.block (P : VertexClustering V) (v : V) : Finset V :=
  P.part v

@[simp] theorem VertexClustering.mem_block (P : VertexClustering V) (v : V) :
    v ∈ P.block v := by
  simp [VertexClustering.block]

@[simp] theorem VertexClustering.block_mem_parts (P : VertexClustering V) (v : V) :
    P.block v ∈ P.parts := by
  simp [VertexClustering.block]

theorem VertexClustering.block_nonempty (P : VertexClustering V) (v : V) :
    (P.block v).Nonempty :=
  P.nonempty_of_mem_parts (P.block_mem_parts v)

theorem VertexClustering.block_eq_of_mem
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts)
    {v : V} (hv : v ∈ C) :
    P.block v = C := by
  exact P.part_eq_of_mem hC hv

/-- Vertices of `C` incident with an original edge leaving `C` (Definition 4.1). -/
noncomputable def interfaceVertices
    (G : _root_.SimpleGraph V) (C : Finset V) : Finset V := by
  classical
  exact C.filter fun v => ∃ w, w ∉ C ∧ G.Adj v w

@[simp] theorem mem_interfaceVertices {C : Finset V} {v : V} :
    v ∈ interfaceVertices G C ↔ v ∈ C ∧ ∃ w, w ∉ C ∧ G.Adj v w := by
  simp [interfaceVertices]

theorem interfaceVertices_subset (G : _root_.SimpleGraph V) (C : Finset V) :
    interfaceVertices G C ⊆ C := by
  intro v hv
  exact (mem_interfaceVertices.mp hv).1

/-- Original graph edges with endpoints in different blocks of `P`. -/
def crossesBlocks (P : VertexClustering V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun u v => P.block u ≠ P.block v, fun u v =>
    propext (ne_comm : P.block u ≠ P.block v ↔ P.block v ≠ P.block u)⟩

@[simp] theorem crossesBlocks_mk (P : VertexClustering V) (u v : V) :
    crossesBlocks P s(u, v) ↔ P.block u ≠ P.block v := by
  simp [crossesBlocks]

/-- The original edges crossing the clustering.  Parallel edges only arise
after contraction in the paper; this foundation counts the original simple
edges before contraction. -/
noncomputable def crossBlockOriginalEdges
    (G : _root_.SimpleGraph V) (P : VertexClustering V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (crossesBlocks P)

theorem mem_crossBlockOriginalEdges
    (P : VertexClustering V) (e : Sym2 V) :
    e ∈ crossBlockOriginalEdges G P ↔ e ∈ G.edgeSet ∧ crossesBlocks P e := by
  classical
  simp [crossBlockOriginalEdges, _root_.SimpleGraph.mem_edgeFinset]

@[simp] theorem mk_mem_crossBlockOriginalEdges
    (P : VertexClustering V) (u v : V) :
    s(u, v) ∈ crossBlockOriginalEdges G P ↔
      G.Adj u v ∧ P.block u ≠ P.block v := by
  classical
  simp [mem_crossBlockOriginalEdges, _root_.SimpleGraph.mem_edgeSet]

theorem crossBlockOriginalEdges_subset_edgeFinset (P : VertexClustering V) :
    crossBlockOriginalEdges G P ⊆ G.edgeFinset := by
  classical
  intro e he
  have heG := ((mem_crossBlockOriginalEdges (G := G) P e).1 he).1
  simpa [_root_.SimpleGraph.mem_edgeFinset] using heG

/-- The boundary of a cluster, always measured in the original graph. -/
noncomputable def originalBoundary
    (G : _root_.SimpleGraph V) (C : Finset V) : Finset (Sym2 V) :=
  Section44.clusterBoundary G C

@[simp] theorem originalBoundary_empty (G : _root_.SimpleGraph V) :
    originalBoundary G (∅ : Finset V) = ∅ := by
  classical
  simp [originalBoundary, Section44.clusterBoundary]

@[simp] theorem originalBoundary_univ (G : _root_.SimpleGraph V) :
    originalBoundary G (Finset.univ : Finset V) = ∅ := by
  classical
  simp [originalBoundary, Section44.clusterBoundary]

theorem mem_originalBoundary_iff {C : Finset V} {e : Sym2 V} :
    e ∈ originalBoundary G C ↔
      e ∈ G.edgeSet ∧
        ∃ u ∈ C, ∃ v ∉ C, e = s(u, v) := by
  classical
  simp [originalBoundary, Section44.clusterBoundary, Section44.mem_edgeBoundary]

/-- Every original boundary edge of a cluster in `P` is a cross-block edge. -/
theorem originalBoundary_subset_crossBlockOriginalEdges
    (P : VertexClustering V) {C : Finset V} (hC : C ∈ P.parts) :
    originalBoundary G C ⊆ crossBlockOriginalEdges G P := by
  classical
  intro e he
  rcases mem_originalBoundary_iff.mp he with ⟨heG, u, huC, v, hvC, rfl⟩
  refine (mk_mem_crossBlockOriginalEdges (G := G) P u v).2 ⟨?_, ?_⟩
  · simpa [_root_.SimpleGraph.mem_edgeSet] using heG
  · intro hsame
    have huBlock : P.block u = C := P.block_eq_of_mem hC huC
    have hvBlock : P.block v = C := hsame.symm.trans huBlock
    exact hvC (hvBlock ▸ P.mem_block v)

/-- A crossing edge lies on the original boundary of either endpoint block. -/
theorem crossBlock_edge_mem_originalBoundary_left
    (P : VertexClustering V) {u v : V}
    (h : s(u, v) ∈ crossBlockOriginalEdges G P) :
    s(u, v) ∈ originalBoundary G (P.block u) := by
  classical
  rcases (mk_mem_crossBlockOriginalEdges (G := G) P u v).1 h with ⟨huv, hblocks⟩
  apply mem_originalBoundary_iff.mpr
  refine ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using huv, u, P.mem_block u, v, ?_, rfl⟩
  intro hv
  exact hblocks (P.block_eq_of_mem (P.block_mem_parts u) hv).symm

/-! ## Refinement and crossing-edge monotonicity -/

theorem VertexClustering.block_subset_of_refines
    {P Q : VertexClustering V} (hPQ : P ≤ Q) (v : V) :
    P.block v ⊆ Q.block v := by
  obtain ⟨C, hC, hsub⟩ := hPQ (P.block_mem_parts v)
  have hCv : v ∈ C := hsub (P.mem_block v)
  simpa [Q.block_eq_of_mem hC hCv] using hsub

theorem crossesBlocks_of_refines
    {P Q : VertexClustering V} (hPQ : P ≤ Q) {e : Sym2 V}
    (he : crossesBlocks Q e) :
    crossesBlocks P e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [crossesBlocks_mk] at he ⊢
      intro hP
      have huv : u ∈ P.block v := hP ▸ P.mem_block u
      have huQ : u ∈ Q.block v := P.block_subset_of_refines hPQ v huv
      exact he (Q.block_eq_of_mem (Q.block_mem_parts v) huQ)

theorem crossBlockOriginalEdges_mono_refinement
    {P Q : VertexClustering V} (hPQ : P ≤ Q) :
    crossBlockOriginalEdges G Q ⊆ crossBlockOriginalEdges G P := by
  classical
  intro e he
  rcases (mem_crossBlockOriginalEdges (G := G) Q e).1 he with ⟨heG, hcross⟩
  exact (mem_crossBlockOriginalEdges (G := G) P e).2
    ⟨heG, crossesBlocks_of_refines hPQ hcross⟩

theorem crossBlockOriginalEdges_card_mono_refinement
    {P Q : VertexClustering V} (hPQ : P ≤ Q) :
    (crossBlockOriginalEdges G Q).card ≤
      (crossBlockOriginalEdges G P).card :=
  Finset.card_le_card (crossBlockOriginalEdges_mono_refinement (G := G) hPQ)

/-! ## Truncated scaled bandwidth and violating partitions -/

/-- The amount of interface demand tested across `X,Y`, truncated at `cap`.
Taking `cap = w0 / 2` gives the equivalent form of the paper's
`(w0, alpha)` violating-partition definition in Action 1. -/
noncomputable def truncatedInterfaceDemand
    (G : _root_.SimpleGraph V) (C X Y : Finset V) (cap : ℕ) : ℕ :=
  min (min (X ∩ interfaceVertices G C).card
    (Y ∩ interfaceVertices G C).card) cap

theorem truncatedInterfaceDemand_le_cap
    (G : _root_.SimpleGraph V) (C X Y : Finset V) (cap : ℕ) :
    truncatedInterfaceDemand G C X Y cap ≤ cap :=
  Nat.min_le_right _ _

theorem truncatedInterfaceDemand_comm
    (G : _root_.SimpleGraph V) (C X Y : Finset V) (cap : ℕ) :
    truncatedInterfaceDemand G C X Y cap =
      truncatedInterfaceDemand G C Y X cap := by
  simp [truncatedInterfaceDemand, Nat.min_comm]

/-- Cut form of the truncated bandwidth property.  The ratio
`alphaNum / alphaDen` is cleared over naturals. -/
def TruncatedScaledBandwidth
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : ℕ) : Prop :=
  0 < alphaNum ∧ alphaNum ≤ alphaDen ∧
    ∀ X Y : Finset V,
      X ⊆ C → Y ⊆ C → X ∪ Y = C → Disjoint X Y →
        alphaNum * truncatedInterfaceDemand G C X Y cap ≤
          alphaDen * (Section44.edgeBoundary G X Y).card

/-- A partition of `C` that strictly violates truncated scaled bandwidth. -/
structure ScaledViolatingPartition
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : ℕ) where
  X : Finset V
  Y : Finset V
  left_subset : X ⊆ C
  right_subset : Y ⊆ C
  cover : X ∪ Y = C
  disjoint : Disjoint X Y
  sparse :
    alphaDen * (Section44.edgeBoundary G X Y).card <
      alphaNum * truncatedInterfaceDemand G C X Y cap

def ScaledViolatingPartition.swap
    {C : Finset V} {cap alphaNum alphaDen : ℕ}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    ScaledViolatingPartition G C cap alphaNum alphaDen where
  X := cut.Y
  Y := cut.X
  left_subset := cut.right_subset
  right_subset := cut.left_subset
  cover := by simpa [Finset.union_comm] using cut.cover
  disjoint := cut.disjoint.symm
  sparse := by
    simpa [truncatedInterfaceDemand_comm,
      Section44.edgeBoundary_comm (G := G) cut.Y cut.X] using cut.sparse

/-- With valid ratio parameters, failure of bandwidth is exactly the existence
of a violating vertex partition. -/
theorem not_truncatedScaledBandwidth_iff_exists_violating
    {C : Finset V} {cap alphaNum alphaDen : ℕ}
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    ¬ TruncatedScaledBandwidth G C cap alphaNum alphaDen ↔
      Nonempty (ScaledViolatingPartition G C cap alphaNum alphaDen) := by
  constructor
  · intro hbad
    simp only [TruncatedScaledBandwidth, hnum, hratio, true_and] at hbad
    push Not at hbad
    rcases hbad with ⟨X, Y, hXC, hYC, hcover, hdisj, hsparse⟩
    exact ⟨⟨X, Y, hXC, hYC, hcover, hdisj, hsparse⟩⟩
  · rintro ⟨cut⟩ hband
    exact (Nat.not_le_of_lt cut.sparse)
      (hband.2.2 cut.X cut.Y cut.left_subset cut.right_subset cut.cover cut.disjoint)

theorem truncatedScaledBandwidth_iff_no_violating
    {C : Finset V} {cap alphaNum alphaDen : ℕ}
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    TruncatedScaledBandwidth G C cap alphaNum alphaDen ↔
      IsEmpty (ScaledViolatingPartition G C cap alphaNum alphaDen) := by
  rw [← not_iff_not]
  simpa using not_truncatedScaledBandwidth_iff_exists_violating
    (G := G) (C := C) (cap := cap) hnum hratio

/-! ## Acceptable and good clusterings (Definition 5.1) -/

def IsLargeCluster (G : _root_.SimpleGraph V) (threshold : ℕ) (C : Finset V) : Prop :=
  threshold ≤ (originalBoundary G C).card

def IsSmallCluster (G : _root_.SimpleGraph V) (threshold : ℕ) (C : Finset V) : Prop :=
  (originalBoundary G C).card < threshold

theorem smallCluster_iff_not_largeCluster
    (G : _root_.SimpleGraph V) (threshold : ℕ) (C : Finset V) :
    IsSmallCluster G threshold C ↔ ¬ IsLargeCluster G threshold C := by
  simp [IsSmallCluster, IsLargeCluster]

/-- Journal Definition 5.1, with bandwidth represented by the exact finite
cut predicate above. -/
structure IsAcceptable
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen : ℕ) (P : VertexClustering V) : Prop where
  terminal_singleton : ∀ t ∈ terminals, ({t} : Finset V) ∈ P.parts
  small_bandwidth : ∀ C ∈ P.parts, IsSmallCluster G threshold C →
    TruncatedScaledBandwidth G C cap alphaNum alphaDen
  large_connected : ∀ C ∈ P.parts, IsLargeCluster G threshold C →
    (G.induce {v : V | v ∈ C}).Connected

/-- An acceptable clustering with no large cluster. -/
def IsGood
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen : ℕ) (P : VertexClustering V) : Prop :=
  IsAcceptable G terminals threshold cap alphaNum alphaDen P ∧
    ∀ C ∈ P.parts, IsSmallCluster G threshold C

theorem IsAcceptable.terminal_block_eq_singleton
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (h : IsAcceptable G terminals threshold cap alphaNum alphaDen P)
    {t : V} (ht : t ∈ terminals) :
    P.block t = {t} := by
  exact P.block_eq_of_mem (h.terminal_singleton t ht) (by simp)

theorem IsGood.no_large
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (h : IsGood G terminals threshold cap alphaNum alphaDen P)
    {C : Finset V} (hC : C ∈ P.parts) :
    ¬ IsLargeCluster G threshold C :=
  (smallCluster_iff_not_largeCluster G threshold C).mp (h.2 C hC)

theorem IsGood.all_bandwidth
    {terminals : Finset V} {threshold cap alphaNum alphaDen : ℕ}
    {P : VertexClustering V}
    (h : IsGood G terminals threshold cap alphaNum alphaDen P)
    {C : Finset V} (hC : C ∈ P.parts) :
    TruncatedScaledBandwidth G C cap alphaNum alphaDen :=
  h.1.small_bandwidth C hC (h.2 C hC)

/-! ## A finite natural-valued potential -/

/-- A bounded natural analogue of the paper's endpoint contribution `rho`.
Monotonicity is recorded for later source-specific split estimates; boundedness
is enough for the generic potential estimates in this module. -/
structure ContributionSchedule where
  rho : ℕ → ℕ
  monotone : Monotone rho
  bound : ℕ
  rho_le_bound : ∀ z, rho z ≤ bound

namespace ContributionSchedule

/-- The zero endpoint-contribution schedule. -/
def zero : ContributionSchedule where
  rho := fun _ => 0
  monotone := fun _ _ _ => le_rfl
  bound := 0
  rho_le_bound := fun _ => le_rfl

/-- A constant endpoint-contribution schedule. -/
def constant (c : ℕ) : ContributionSchedule where
  rho := fun _ => c
  monotone := fun _ _ _ => le_rfl
  bound := c
  rho_le_bound := fun _ => le_rfl

end ContributionSchedule

/-- Original boundary size of the block containing `v`. -/
noncomputable def endpointBoundarySize
    (G : _root_.SimpleGraph V) (P : VertexClustering V) (v : V) : ℕ :=
  (originalBoundary G (P.block v)).card

/-- Natural edge potential: zero inside a block, and a base charge plus the
two bounded endpoint contributions across blocks. -/
noncomputable def edgePotential
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (base : ℕ) (schedule : ContributionSchedule) : Sym2 V → ℕ := by
  classical
  exact Sym2.lift ⟨fun u v =>
    if P.block u = P.block v then 0
    else base + schedule.rho (endpointBoundarySize G P u) +
      schedule.rho (endpointBoundarySize G P v), by
        intro u v
        by_cases h : P.block u = P.block v
        · simp only [if_pos h, if_pos h.symm]
        · have h' : P.block v ≠ P.block u := ne_comm.mp h
          simp only [if_neg h, if_neg h']
          ac_rfl⟩

@[simp] theorem edgePotential_mk
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule)
    (u v : V) :
    edgePotential G P base schedule s(u, v) =
      if P.block u = P.block v then 0
      else base + schedule.rho (endpointBoundarySize G P u) +
        schedule.rho (endpointBoundarySize G P v) := by
  classical
  simp only [edgePotential, Sym2.lift_mk]

theorem edgePotential_eq_zero_of_same_block
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule)
    {u v : V} (h : P.block u = P.block v) :
    edgePotential G P base schedule s(u, v) = 0 := by
  simp [edgePotential_mk, h]

theorem edgePotential_eq_of_crosses
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule)
    {u v : V} (h : P.block u ≠ P.block v) :
    edgePotential G P base schedule s(u, v) =
      base + schedule.rho (endpointBoundarySize G P u) +
        schedule.rho (endpointBoundarySize G P v) := by
  simp [edgePotential_mk, h]

theorem base_le_edgePotential_of_crosses
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule)
    {e : Sym2 V} (h : crossesBlocks P e) :
    base ≤ edgePotential G P base schedule e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [edgePotential_eq_of_crosses]
      · omega
      · simpa using h

theorem edgePotential_le_of_crosses
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule)
    {e : Sym2 V} (h : crossesBlocks P e) :
    edgePotential G P base schedule e ≤ base + 2 * schedule.bound := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [edgePotential_eq_of_crosses]
      · have hu := schedule.rho_le_bound (endpointBoundarySize G P u)
        have hv := schedule.rho_le_bound (endpointBoundarySize G P v)
        omega
      · simpa using h

/-- Sum of edge potentials over the finite original edge set. -/
noncomputable def clusteringPotential
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (base : ℕ) (schedule : ContributionSchedule) : ℕ :=
  ∑ e ∈ G.edgeFinset, edgePotential G P base schedule e

theorem clusteringPotential_eq_sum_crossBlockOriginalEdges
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule) :
    clusteringPotential G P base schedule =
      ∑ e ∈ crossBlockOriginalEdges G P, edgePotential G P base schedule e := by
  classical
  symm
  apply Finset.sum_subset (crossBlockOriginalEdges_subset_edgeFinset (G := G) P)
  intro e heG heNot
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hsame : P.block u = P.block v := by
        by_contra hne
        exact heNot ((mk_mem_crossBlockOriginalEdges (G := G) P u v).2
          ⟨by simpa [_root_.SimpleGraph.mem_edgeFinset] using heG, hne⟩)
      exact edgePotential_eq_zero_of_same_block (G := G) P base schedule hsame

theorem base_mul_crossBlockOriginalEdges_card_le_potential
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule) :
    base * (crossBlockOriginalEdges G P).card ≤
      clusteringPotential G P base schedule := by
  classical
  rw [clusteringPotential_eq_sum_crossBlockOriginalEdges]
  calc
    base * (crossBlockOriginalEdges G P).card =
        ∑ _e ∈ crossBlockOriginalEdges G P, base := by
          simp [Nat.mul_comm]
    _ ≤ ∑ e ∈ crossBlockOriginalEdges G P,
        edgePotential G P base schedule e := by
      apply Finset.sum_le_sum
      intro e he
      exact base_le_edgePotential_of_crosses (G := G) P base schedule
        ((mem_crossBlockOriginalEdges (G := G) P e).1 he).2

theorem clusteringPotential_le_crossBlockOriginalEdges_card_mul
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule) :
    clusteringPotential G P base schedule ≤
      (crossBlockOriginalEdges G P).card * (base + 2 * schedule.bound) := by
  classical
  rw [clusteringPotential_eq_sum_crossBlockOriginalEdges]
  calc
    ∑ e ∈ crossBlockOriginalEdges G P, edgePotential G P base schedule e ≤
        ∑ _e ∈ crossBlockOriginalEdges G P,
          (base + 2 * schedule.bound) := by
      apply Finset.sum_le_sum
      intro e he
      exact edgePotential_le_of_crosses (G := G) P base schedule
        ((mem_crossBlockOriginalEdges (G := G) P e).1 he).2
    _ = (crossBlockOriginalEdges G P).card *
        (base + 2 * schedule.bound) := by simp

theorem clusteringPotential_le_edgeFinset_card_mul
    (P : VertexClustering V) (base : ℕ) (schedule : ContributionSchedule) :
    clusteringPotential G P base schedule ≤
      G.edgeFinset.card * (base + 2 * schedule.bound) := by
  exact (clusteringPotential_le_crossBlockOriginalEdges_card_mul
    (G := G) P base schedule).trans
      (Nat.mul_le_mul_right _
        (Finset.card_le_card (crossBlockOriginalEdges_subset_edgeFinset (G := G) P)))

theorem clusteringPotential_eq_zero_iff
    (P : VertexClustering V) {base : ℕ} (hbase : 0 < base)
    (schedule : ContributionSchedule) :
    clusteringPotential G P base schedule = 0 ↔
      crossBlockOriginalEdges G P = ∅ := by
  constructor
  · intro hzero
    have hle := base_mul_crossBlockOriginalEdges_card_le_potential
      (G := G) P base schedule
    rw [hzero] at hle
    have hmul : base * (crossBlockOriginalEdges G P).card = 0 :=
      Nat.eq_zero_of_le_zero hle
    have hcard : (crossBlockOriginalEdges G P).card = 0 :=
      (Nat.mul_eq_zero.mp hmul).resolve_left (Nat.ne_of_gt hbase)
    exact Finset.card_eq_zero.mp hcard
  · intro hempty
    rw [clusteringPotential_eq_sum_crossBlockOriginalEdges, hempty]
    simp

/-! ## Natural potential descent -/

/-- `Q` lowers a natural potential from `P` by at least `amount`. -/
def PotentialDropsBy {State : Type*}
    (potential : State → ℕ) (amount : ℕ) (P Q : State) : Prop :=
  potential Q + amount ≤ potential P

theorem PotentialDropsBy.zero {State : Type*}
    (potential : State → ℕ) (P Q : State)
    (h : potential Q ≤ potential P) :
    PotentialDropsBy potential 0 P Q := by
  simpa [PotentialDropsBy] using h

theorem PotentialDropsBy.trans {State : Type*}
    {potential : State → ℕ} {a b : ℕ} {P Q R : State}
    (hPQ : PotentialDropsBy potential a P Q)
    (hQR : PotentialDropsBy potential b Q R) :
    PotentialDropsBy potential (a + b) P R := by
  unfold PotentialDropsBy at *
  omega

theorem PotentialDropsBy.lt_of_pos {State : Type*}
    {potential : State → ℕ} {amount : ℕ} {P Q : State}
    (h : PotentialDropsBy potential amount P Q) (hamount : 0 < amount) :
    potential Q < potential P := by
  unfold PotentialDropsBy at h
  omega

/-- Minimum-potential descent.  No finiteness assumption on `State` is needed:
well-ordering of the attained natural potentials supplies a terminal state. -/
theorem exists_good_of_potential_descent
    {State : Type*} (potential : State → ℕ)
    (Valid Good : State → Prop) (initial : State)
    (hinitial : Valid initial)
    (hstep : ∀ state, Valid state → ¬ Good state →
      ∃ next, Valid next ∧ potential next < potential state) :
    ∃ state, Valid state ∧ Good state := by
  classical
  let Attained : ℕ → Prop := fun n => ∃ state, Valid state ∧ potential state = n
  have hex : ∃ n, Attained n := ⟨potential initial, initial, hinitial, rfl⟩
  rcases Nat.find_spec hex with ⟨state, hvalid, hpotential⟩
  refine ⟨state, hvalid, ?_⟩
  by_contra hbad
  rcases hstep state hvalid hbad with ⟨next, hnext, hlt⟩
  have hattained : Attained (potential next) := ⟨next, hnext, rfl⟩
  have hminimal := Nat.find_min' (H := hex) hattained
  omega

/-- A sequence dropping by at least one per step can have at most its initial
potential many strict steps. -/
theorem descent_chain_add_index_le
    (potential : ℕ → ℕ)
    (hstep : ∀ i, potential (i + 1) + 1 ≤ potential i) :
    ∀ i, potential i + i ≤ potential 0 := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      have hs := hstep i
      omega

theorem descent_chain_index_le_initial
    (potential : ℕ → ℕ)
    (hstep : ∀ i, potential (i + 1) + 1 ≤ potential i) (i : ℕ) :
    i ≤ potential 0 := by
  have h := descent_chain_add_index_le potential hstep i
  omega

end ChekuriChuzhoySection5Clustering
end SimpleGraph

end Lax17Proofs
