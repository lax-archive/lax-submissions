import Lax17Proofs.Source.ChekuriChuzhoySection5LabelPartition
import Lax17Proofs.Source.ChekuriChuzhoySection5SourcePotential
import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthDecomposition
import Lax17Proofs.Source.AppendixA3CutSubmodularity
import Lax17Proofs.Source.ChekuriChuzhoySection5Partition

namespace Lax17Proofs

universe u v w

/-!
# The SEPARATE component partition

This file formalizes the preliminary partition in Chekuri--Chuzhoy, journal
Section 5.2, Action 2 and Claim 5.7.  Given an old clustering `P` and a cut
side `A`, the auxiliary graph permits:

* every original edge with both endpoints in `A`; and
* an original edge outside `A` only when its endpoints lie in the same old
  cluster.

Its connected components are exactly the components of `G[A]` together with
the components of `G[S \ A]` for old clusters `S`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Separate


open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5LabelPartition
open ChekuriChuzhoySection5SourcePotential
open ChekuriChuzhoySection5BandwidthDecomposition
open ChekuriChuzhoySection5Partition

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The graph whose connected components form the preliminary result of
`SEPARATE(P,A)`. -/
def separateGraph
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (A : Finset V) : _root_.SimpleGraph V where
  Adj u v :=
    G.Adj u v ∧
      ((u ∈ A ∧ v ∈ A) ∨
        (u ∉ A ∧ v ∉ A ∧ P.block u = P.block v))
  symm := by
    intro u v h
    refine ⟨G.symm h.1, ?_⟩
    rcases h.2 with hA | hout
    · exact Or.inl ⟨hA.2, hA.1⟩
    · exact Or.inr ⟨hout.2.1, hout.1, hout.2.2.symm⟩
  loopless := ⟨by
    intro v h
    exact G.loopless.irrefl v h.1⟩

@[simp] theorem separateGraph_adj
    (P : VertexClustering V) (A : Finset V) (u v : V) :
    (separateGraph G P A).Adj u v ↔
      G.Adj u v ∧
        ((u ∈ A ∧ v ∈ A) ∨
          (u ∉ A ∧ v ∉ A ∧ P.block u = P.block v)) :=
  Iff.rfl

/-- The preliminary SEPARATE clustering. -/
noncomputable def componentClustering
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (A : Finset V) : VertexClustering V := by
  classical
  exact partition (separateGraph G P A).connectedComponentMk

@[simp] theorem componentClustering_block_eq_iff
    (P : VertexClustering V) (A : Finset V) (u v : V) :
    (componentClustering G P A).block u =
        (componentClustering G P A).block v ↔
      (separateGraph G P A).connectedComponentMk u =
        (separateGraph G P A).connectedComponentMk v := by
  classical
  change
    partOf (separateGraph G P A).connectedComponentMk u =
        partOf (separateGraph G P A).connectedComponentMk v ↔ _
  exact partOf_eq_partOf_iff

private theorem separateWalk_target_mem_of_source_mem
    {P : VertexClustering V} {A : Finset V} {u v : V}
    (p : (separateGraph G P A).Walk u v) (hu : u ∈ A) :
    v ∈ A := by
  induction p with
  | nil => exact hu
  | @cons u w v huw p ih =>
      have hw : w ∈ A := by
        rcases huw.2 with hin | hout
        · exact hin.2
        · exact (hout.1 hu).elim
      exact ih hw

private theorem separateWalk_target_not_mem_of_source_not_mem
    {P : VertexClustering V} {A : Finset V} {u v : V}
    (p : (separateGraph G P A).Walk u v) (hu : u ∉ A) :
    v ∉ A := by
  induction p with
  | nil => exact hu
  | @cons u w v huw p ih =>
      have hw : w ∉ A := by
        rcases huw.2 with hin | hout
        · exact (hu hin.1).elim
        · exact hout.2.1
      exact ih hw

private theorem separateWalk_target_oldBlock_eq_of_source_not_mem
    {P : VertexClustering V} {A : Finset V} {u v : V}
    (p : (separateGraph G P A).Walk u v) (hu : u ∉ A) :
    P.block v = P.block u := by
  induction p with
  | nil => rfl
  | @cons u w v huw p ih =>
      rcases huw.2 with hin | hout
      · exact (hu hin.1).elim
      · have htail : P.block v = P.block w := ih hout.2.1
        exact htail.trans hout.2.2.symm

theorem mem_A_iff_of_same_componentBlock
    (P : VertexClustering V) (A : Finset V) {u v : V}
    (hblock :
      (componentClustering G P A).block u =
        (componentClustering G P A).block v) :
    u ∈ A ↔ v ∈ A := by
  have hcomponent :=
    (componentClustering_block_eq_iff
      (G := G) P A u v).mp hblock
  rcases _root_.SimpleGraph.ConnectedComponent.eq.mp hcomponent with ⟨p⟩
  constructor
  · exact separateWalk_target_mem_of_source_mem p
  · intro hv
    have hreverse :
        (separateGraph G P A).connectedComponentMk v =
          (separateGraph G P A).connectedComponentMk u :=
      hcomponent.symm
    rcases _root_.SimpleGraph.ConnectedComponent.eq.mp hreverse with ⟨q⟩
    exact separateWalk_target_mem_of_source_mem q hv

theorem oldBlock_eq_of_same_componentBlock_of_not_mem
    (P : VertexClustering V) (A : Finset V) {u v : V}
    (hu : u ∉ A)
    (hblock :
      (componentClustering G P A).block u =
        (componentClustering G P A).block v) :
    P.block u = P.block v := by
  have hcomponent :=
    (componentClustering_block_eq_iff
      (G := G) P A u v).mp hblock
  rcases _root_.SimpleGraph.ConnectedComponent.eq.mp hcomponent with ⟨p⟩
  exact (separateWalk_target_oldBlock_eq_of_source_not_mem p hu).symm

/-- Every original edge lying entirely in `A` becomes internal to the
preliminary SEPARATE clustering. -/
theorem same_componentBlock_of_adj_of_mem
    (P : VertexClustering V) (A : Finset V) {u v : V}
    (huv : G.Adj u v) (hu : u ∈ A) (hv : v ∈ A) :
    (componentClustering G P A).block u =
      (componentClustering G P A).block v := by
  rw [componentClustering_block_eq_iff]
  exact _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    ⟨huv, Or.inl ⟨hu, hv⟩⟩

/-- Outside `A`, an original edge inside one old cluster also becomes
internal to the corresponding old-cluster remainder component. -/
theorem same_componentBlock_of_adj_of_not_mem_of_oldBlock_eq
    (P : VertexClustering V) (A : Finset V) {u v : V}
    (huv : G.Adj u v) (hu : u ∉ A) (hv : v ∉ A)
    (hblock : P.block u = P.block v) :
    (componentClustering G P A).block u =
      (componentClustering G P A).block v := by
  rw [componentClustering_block_eq_iff]
  exact _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    ⟨huv, Or.inr ⟨hu, hv, hblock⟩⟩

/-- Every preliminary SEPARATE block is connected in the original graph. -/
theorem componentBlock_connected
    (P : VertexClustering V) (A : Finset V) (v : V) :
    (G.induce
      {x : V | x ∈ (componentClustering G P A).block v}).Connected := by
  classical
  let H := separateGraph G P A
  let K := H.connectedComponentMk v
  have hset :
      {x : V | x ∈ (componentClustering G P A).block v} =
        K.supp := by
    ext x
    change
      x ∈ partOf H.connectedComponentMk v ↔ x ∈ K.supp
    rw [mem_partOf_iff]
    simp only [K, _root_.SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact eq_comm
  rw [hset]
  apply K.connected_toSimpleGraph.mono
  intro x y hxy
  exact hxy.1

/-- A component on the distinguished side is contained in that side. -/
theorem componentBlock_subset_of_mem
    (P : VertexClustering V) (A : Finset V) {v : V}
    (hvA : v ∈ A) :
    (componentClustering G P A).block v ⊆ A := by
  intro x hx
  have hxBlock :
      (componentClustering G P A).block x =
        (componentClustering G P A).block v :=
    (componentClustering G P A).block_eq_of_mem
      ((componentClustering G P A).block_mem_parts v) hx
  exact (mem_A_iff_of_same_componentBlock P A hxBlock).mpr hvA

/-- The boundary of a component on the distinguished side is contained in
the boundary of that side. -/
theorem componentBoundary_subset_cutBoundary
    (P : VertexClustering V) (A : Finset V) {v : V}
    (hvA : v ∈ A) :
    originalBoundary G ((componentClustering G P A).block v) ⊆
      originalBoundary G A := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rcases (mk_mem_clusterBoundary_iff G
          ((componentClustering G P A).block v) x y).1 he with
        ⟨hxy, hends⟩
      rcases hends with ⟨hxD, hyD⟩ | ⟨hyD, hxD⟩
      · have hxA : x ∈ A :=
          componentBlock_subset_of_mem P A hvA hxD
        have hyA : y ∉ A := by
          intro hyA
          have hsame :=
            same_componentBlock_of_adj_of_mem P A hxy hxA hyA
          have hxBlock :
              (componentClustering G P A).block x =
                (componentClustering G P A).block v :=
            (componentClustering G P A).block_eq_of_mem
              ((componentClustering G P A).block_mem_parts v) hxD
          have hyIn :
              y ∈ (componentClustering G P A).block v := by
            rw [← hxBlock, hsame]
            exact (componentClustering G P A).mem_block y
          exact hyD hyIn
        exact mem_originalBoundary_iff.mpr
          ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using hxy,
            x, hxA, y, hyA, rfl⟩
      · have hyA : y ∈ A :=
          componentBlock_subset_of_mem P A hvA hyD
        have hxA : x ∉ A := by
          intro hxA
          have hsame :=
            same_componentBlock_of_adj_of_mem P A hxy hxA hyA
          have hyBlock :
              (componentClustering G P A).block y =
                (componentClustering G P A).block v :=
            (componentClustering G P A).block_eq_of_mem
              ((componentClustering G P A).block_mem_parts v) hyD
          have hxIn :
              x ∈ (componentClustering G P A).block v := by
            rw [← hyBlock, ← hsame]
            exact (componentClustering G P A).mem_block x
          exact hxD hxIn
        exact mem_originalBoundary_iff.mpr
          ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using hxy,
            y, hyA, x, hxA, Sym2.eq_swap⟩

/-- An edge crossing the preliminary clustering but not the cut `A` already
crossed the old clustering. -/
theorem old_crosses_of_new_crosses_of_not_cut
    (P : VertexClustering V) (A : Finset V) {u v : V}
    (huv : G.Adj u v)
    (hnew :
      (componentClustering G P A).block u ≠
        (componentClustering G P A).block v)
    (hnotCut : ¬((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A))) :
    P.block u ≠ P.block v := by
  intro hold
  by_cases hu : u ∈ A
  · have hv : v ∈ A := by
      by_contra hv
      exact hnotCut (Or.inl ⟨hu, hv⟩)
    exact hnew (same_componentBlock_of_adj_of_mem P A huv hu hv)
  · have hv : v ∉ A := by
      intro hv
      exact hnotCut (Or.inr ⟨hv, hu⟩)
    exact hnew
      (same_componentBlock_of_adj_of_not_mem_of_oldBlock_eq
        P A huv hu hv hold)

theorem originalBoundary_subset_sourceEdgeFinset
    (C : Finset V) :
    originalBoundary G C ⊆ sourceEdgeFinset G := by
  intro e he
  exact mem_sourceEdgeFinset.mpr
    (mem_originalBoundary_iff.mp he).1

/-- The old boundary of a block contained in `A` either lies on the new cut,
or becomes internal to the preliminary component clustering. -/
theorem oldBoundary_internal_unless_newCut
    (P : VertexClustering V) (A C : Finset V)
    (hCA : C ⊆ A) {e : Sym2 V}
    (heC : e ∈ originalBoundary G C)
    (heA : e ∉ originalBoundary G A) :
    ¬ crossesBlocks (componentClustering G P A) e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have heC' :
          s(u, v) ∈ Section44.clusterBoundary G C := heC
      rcases (mk_mem_clusterBoundary_iff G C u v).1 heC' with
        ⟨huv, hends⟩
      rcases hends with ⟨huC, hvC⟩ | ⟨hvC, huC⟩
      · have huA : u ∈ A := hCA huC
        have hvA : v ∈ A := by
          by_contra hvA
          apply heA
          exact mem_originalBoundary_iff.mpr
            ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using huv,
              u, huA, v, hvA, rfl⟩
        simpa only [crossesBlocks_mk, not_ne_iff] using
          same_componentBlock_of_adj_of_mem P A huv huA hvA
      · have hvA : v ∈ A := hCA hvC
        have huA : u ∈ A := by
          by_contra huA
          apply heA
          exact mem_originalBoundary_iff.mpr
            ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using huv,
              v, hvA, u, huA, Sym2.eq_swap⟩
        simpa only [crossesBlocks_mk, not_ne_iff] using
          (same_componentBlock_of_adj_of_mem
            P A huv huA hvA)

/-- Outside the two cuts, the preliminary component operation cannot
increase an edge potential, provided the boundary of every outside component
is no larger than the boundary of its old cluster.  This is the invariant
established by the cut-adjustment loop immediately preceding Action 2 in the
paper. -/
theorem stable_edgePotential_outside_cuts
    (P : VertexClustering V) (A : Finset V)
    (schedule : BoundedContribution)
    (hcontrolled : ∀ v, v ∉ A →
      (originalBoundary G
          ((componentClustering G P A).block v)).card ≤
        (originalBoundary G (P.block v)).card)
    {e : Sym2 V} (heG : e ∈ G.edgeSet)
    (heA : e ∉ originalBoundary G A) :
    edgePotential G (componentClustering G P A) schedule e ≤
      edgePotential G P schedule e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using heG
      by_cases hnew :
          (componentClustering G P A).block u =
            (componentClustering G P A).block v
      · rw [edgePotential_eq_zero_of_same_block
          (G := G) _ schedule hnew]
        exact edgePotential_nonnegative (G := G) P schedule s(u, v)
      · have hnotCut :
          ¬((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) := by
          intro hcut
          apply heA
          rcases hcut with hcut | hcut
          · exact mem_originalBoundary_iff.mpr
              ⟨heG, u, hcut.1, v, hcut.2, rfl⟩
          · exact mem_originalBoundary_iff.mpr
              ⟨heG, v, hcut.1, u, hcut.2,
                Sym2.eq_swap⟩
        have hold : P.block u ≠ P.block v :=
          old_crosses_of_new_crosses_of_not_cut
            P A huv hnew hnotCut
        have huA : u ∉ A := by
          intro hu
          have hv : v ∈ A := by
            by_contra hv
            exact hnotCut (Or.inl ⟨hu, hv⟩)
          exact hnew
            (same_componentBlock_of_adj_of_mem P A huv hu hv)
        have hvA : v ∉ A := by
          intro hv
          have hu : u ∈ A := by
            by_contra hu
            exact hnotCut (Or.inr ⟨hv, hu⟩)
          exact hnew
            (same_componentBlock_of_adj_of_mem P A huv hu hv)
        rw [edgePotential_eq_of_crosses
            (G := G) _ schedule hnew,
          edgePotential_eq_of_crosses (G := G) P schedule hold]
        have huRho :
            schedule.rho
                (endpointBoundarySize G
                  (componentClustering G P A) u) ≤
              schedule.rho (endpointBoundarySize G P u) := by
          apply schedule.monotone
          exact hcontrolled u huA
        have hvRho :
            schedule.rho
                (endpointBoundarySize G
                  (componentClustering G P A) v) ≤
              schedule.rho (endpointBoundarySize G P v) := by
          apply schedule.monotone
          exact hcontrolled v hvA
        linarith

/-- Claim 5.7 for the preliminary component partition, before applying the
bandwidth decompositions from Theorem 5.5. -/
theorem componentClustering_dropsByOne
    (P : VertexClustering V) (A C : Finset V)
    (schedule : BoundedContribution) (w0 : Nat)
    (hCpart : C ∈ P.parts)
    (hCA : C ⊆ A)
    (hlarge : IsLargeCluster G w0 C)
    (hcut : (originalBoundary G A).card < w0 / 2)
    (hcontrolled : ∀ v, v ∉ A →
      (originalBoundary G
          ((componentClustering G P A).block v)).card ≤
        (originalBoundary G (P.block v)).card) :
    DropsByOne G schedule P (componentClustering G P A) := by
  let removed := originalBoundary G C
  let added := originalBoundary G A
  apply dropsByOne_of_separate_classification
    (G := G) P (componentClustering G P A) schedule
      removed added
  · exact originalBoundary_subset_sourceEdgeFinset C
  · exact originalBoundary_subset_sourceEdgeFinset A
  · apply separate_card_accounting hlarge hcut
  · intro e he
    exact
      crossesBlocks_of_refines
        (P := P) (Q := P) (le_refl P)
        ((mem_crossBlockOriginalEdges (G := G) P e).1
          (originalBoundary_subset_crossBlockOriginalEdges
            (G := G) P hCpart he)).2
  · intro e heC heA
    exact oldBoundary_internal_unless_newCut P A C hCA heC heA
  · intro e heG _heC heA
    exact stable_edgePotential_outside_cuts
      P A schedule hcontrolled heG heA

/-! ## The cut-adjustment loop preceding Action 2 -/

/-- Removing a set `S` whose outside remainder has larger boundary than `S`
strictly decreases the boundary of `A`.  This is the one-line
posimodularity calculation used by the paper's adjustment loop. -/
theorem boundary_sdiff_lt_of_remainder_boundary_gt
    (A S : Finset V)
    (hbad :
      (originalBoundary G S).card <
        (originalBoundary G (S \ A)).card) :
    (originalBoundary G (A \ S)).card <
      (originalBoundary G A).card := by
  have hposi :=
    Section44.clusterBoundary_sdiff_add_sdiff_card_le G A S
  change
    (originalBoundary G (A \ S)).card +
        (originalBoundary G (S \ A)).card ≤
      (originalBoundary G A).card +
        (originalBoundary G S).card at hposi
  omega

/-- A minimum-boundary admissible subset of the initial cut side realizes
the terminating state of the paper's cut-adjustment loop. -/
theorem exists_adjustedSide
    (P : VertexClustering V) (C terminals initial : Finset V)
    (hCpart : C ∈ P.parts)
    (hCinitial : C ⊆ initial)
    (hterminal : Disjoint initial terminals) :
    ∃ A : Finset V,
      A ⊆ initial ∧
      C ⊆ A ∧
      Disjoint A terminals ∧
      (originalBoundary G A).card ≤
        (originalBoundary G initial).card ∧
      ∀ S ∈ P.parts, (S \ A).Nonempty →
        (originalBoundary G (S \ A)).card ≤
          (originalBoundary G S).card := by
  classical
  let Admissible : Finset V → Prop := fun A =>
    A ⊆ initial ∧ C ⊆ A ∧ Disjoint A terminals
  let Attained : Nat → Prop := fun n =>
    ∃ A, Admissible A ∧ (originalBoundary G A).card = n
  have hex : ∃ n, Attained n :=
    ⟨(originalBoundary G initial).card, initial,
      ⟨Finset.Subset.rfl, hCinitial, hterminal⟩, rfl⟩
  let n := Nat.find hex
  obtain ⟨A, hA, hboundary⟩ := Nat.find_spec hex
  refine ⟨A, hA.1, hA.2.1, hA.2.2, ?_, ?_⟩
  · have hinitialAttained :
        Attained (originalBoundary G initial).card :=
      ⟨initial, ⟨Finset.Subset.rfl, hCinitial, hterminal⟩, rfl⟩
    simpa [n, hboundary] using Nat.find_min' hex hinitialAttained
  · intro S hSpart hSrem
    by_contra hnot
    have hbad :
        (originalBoundary G S).card <
          (originalBoundary G (S \ A)).card := by
      omega
    have hSC : S ≠ C := by
      intro h
      subst S
      rcases hSrem with ⟨v, hv⟩
      rcases Finset.mem_sdiff.mp hv with ⟨hvC, hvA⟩
      exact hvA (hA.2.1 hvC)
    have hdisjointCS : Disjoint C S :=
      P.disjoint hCpart hSpart hSC.symm
    let A' := A \ S
    have hA'admissible : Admissible A' := by
      refine ⟨?_, ?_, ?_⟩
      · exact (Finset.sdiff_subset.trans hA.1)
      · intro v hvC
        exact Finset.mem_sdiff.mpr
          ⟨hA.2.1 hvC,
            fun hvS =>
              Finset.disjoint_left.mp hdisjointCS hvC hvS⟩
      · exact hA.2.2.mono Finset.sdiff_subset Finset.Subset.rfl
    have hA'lt :
        (originalBoundary G A').card <
          (originalBoundary G A).card :=
      boundary_sdiff_lt_of_remainder_boundary_gt A S hbad
    have hA'attained : Attained (originalBoundary G A').card :=
      ⟨A', hA'admissible, rfl⟩
    have hminimal := Nat.find_min' hex hA'attained
    rw [hboundary] at hA'lt
    exact (Nat.not_lt_of_ge hminimal hA'lt)

/-- An outside component of the preliminary clustering is contained in the
remainder of its old cluster. -/
theorem componentBlock_subset_oldBlock_sdiff
    (P : VertexClustering V) (A : Finset V) {v : V}
    (hvA : v ∉ A) :
    (componentClustering G P A).block v ⊆ P.block v \ A := by
  intro x hx
  have hxBlock :
      (componentClustering G P A).block x =
        (componentClustering G P A).block v :=
    (componentClustering G P A).block_eq_of_mem
      ((componentClustering G P A).block_mem_parts v) hx
  have hxA : x ∉ A := by
    intro hxA
    exact hvA
      ((mem_A_iff_of_same_componentBlock P A hxBlock).mp hxA)
  have hOld : P.block x = P.block v :=
    oldBlock_eq_of_same_componentBlock_of_not_mem
      P A hxA hxBlock
  exact Finset.mem_sdiff.mpr
    ⟨by
      rw [← hOld]
      exact P.mem_block x,
      hxA⟩

/-- No original edge joins one outside component to another vertex of the
same old-cluster remainder. -/
theorem componentBoundary_subset_remainderBoundary
    (P : VertexClustering V) (A : Finset V) {v : V}
    (hvA : v ∉ A) :
    originalBoundary G ((componentClustering G P A).block v) ⊆
      originalBoundary G (P.block v \ A) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have he' :
          s(x, y) ∈
            Section44.clusterBoundary G
              ((componentClustering G P A).block v) := he
      rcases
          (mk_mem_clusterBoundary_iff G
            ((componentClustering G P A).block v) x y).1 he' with
        ⟨hxy, hends⟩
      rcases hends with ⟨hxD, hyD⟩ | ⟨hyD, hxD⟩
      · have hxR :
            x ∈ P.block v \ A :=
          componentBlock_subset_oldBlock_sdiff P A hvA hxD
        have hyR : y ∉ P.block v \ A := by
          intro hyR
          rcases Finset.mem_sdiff.mp hyR with ⟨hyOld, hyA⟩
          have hxA : x ∉ A :=
            (Finset.mem_sdiff.mp hxR).2
          have hxOld : P.block x = P.block v := by
            have hxBlock :
                (componentClustering G P A).block x =
                  (componentClustering G P A).block v :=
              (componentClustering G P A).block_eq_of_mem
                ((componentClustering G P A).block_mem_parts v) hxD
            exact oldBlock_eq_of_same_componentBlock_of_not_mem
              P A hxA hxBlock
          have hyOldBlock : P.block y = P.block v :=
            P.block_eq_of_mem (P.block_mem_parts v) hyOld
          have hsame :=
            same_componentBlock_of_adj_of_not_mem_of_oldBlock_eq
              P A hxy hxA hyA (hxOld.trans hyOldBlock.symm)
          have hxBlock :
              (componentClustering G P A).block x =
                (componentClustering G P A).block v :=
            (componentClustering G P A).block_eq_of_mem
              ((componentClustering G P A).block_mem_parts v) hxD
          have hyIn :
              y ∈ (componentClustering G P A).block v := by
            have :
                y ∈ (componentClustering G P A).block x := by
              rw [hsame]
              exact (componentClustering G P A).mem_block y
            simpa [hxBlock] using this
          exact hyD hyIn
        exact mem_originalBoundary_iff.mpr
          ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using hxy,
            x, hxR, y, hyR, rfl⟩
      · have hyR :
            y ∈ P.block v \ A :=
          componentBlock_subset_oldBlock_sdiff P A hvA hyD
        have hxR : x ∉ P.block v \ A := by
          intro hxR
          rcases Finset.mem_sdiff.mp hxR with ⟨hxOld, hxA⟩
          have hyA : y ∉ A :=
            (Finset.mem_sdiff.mp hyR).2
          have hyOldBlock : P.block y = P.block v := by
            have hyBlock :
                (componentClustering G P A).block y =
                  (componentClustering G P A).block v :=
              (componentClustering G P A).block_eq_of_mem
                ((componentClustering G P A).block_mem_parts v) hyD
            exact oldBlock_eq_of_same_componentBlock_of_not_mem
              P A hyA hyBlock
          have hxOldBlock : P.block x = P.block v :=
            P.block_eq_of_mem (P.block_mem_parts v) hxOld
          have hsame :=
            same_componentBlock_of_adj_of_not_mem_of_oldBlock_eq
              P A hxy hxA hyA (hxOldBlock.trans hyOldBlock.symm)
          have hyBlock :
              (componentClustering G P A).block y =
                (componentClustering G P A).block v :=
            (componentClustering G P A).block_eq_of_mem
              ((componentClustering G P A).block_mem_parts v) hyD
          have hxIn :
              x ∈ (componentClustering G P A).block v := by
            have :
                x ∈ (componentClustering G P A).block y := by
              rw [← hsame]
              exact (componentClustering G P A).mem_block x
            simpa [hyBlock] using this
          exact hxD hxIn
        exact mem_originalBoundary_iff.mpr
          ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using hxy,
            y, hyR, x, hxR, Sym2.eq_swap⟩

/-- When the distinguished side is one old part, taking the component
clustering is a genuine refinement of the old clustering. -/
theorem componentClustering_le_of_mem_parts
    (P : VertexClustering V) (A : Finset V) (hA : A ∈ P.parts) :
    componentClustering G P A ≤ P := by
  intro R hR
  rcases (componentClustering G P A).nonempty_of_mem_parts hR with
    ⟨v, hvR⟩
  by_cases hvA : v ∈ A
  · refine ⟨A, hA, ?_⟩
    intro x hx
    have hblock :
        (componentClustering G P A).block x =
          (componentClustering G P A).block v :=
      ((componentClustering G P A).block_eq_of_mem hR hx).trans
        ((componentClustering G P A).block_eq_of_mem hR hvR).symm
    exact (mem_A_iff_of_same_componentBlock P A hblock).mpr hvA
  · refine ⟨P.block v, P.block_mem_parts v, ?_⟩
    intro x hx
    have hblock :
        (componentClustering G P A).block x =
          (componentClustering G P A).block v :=
      ((componentClustering G P A).block_eq_of_mem hR hx).trans
        ((componentClustering G P A).block_eq_of_mem hR hvR).symm
    have hxA : x ∉ A :=
      (mem_A_iff_of_same_componentBlock P A hblock).not.mpr hvA
    rw [← oldBlock_eq_of_same_componentBlock_of_not_mem
      P A hxA hblock]
    exact P.mem_block x

/-- Componentizing one old part does not enlarge the boundary seen at any
endpoint. -/
theorem componentClustering_boundary_le_of_mem_parts
    (P : VertexClustering V) (A : Finset V) (hA : A ∈ P.parts)
    (v : V) :
    (originalBoundary G ((componentClustering G P A).block v)).card ≤
      (originalBoundary G (P.block v)).card := by
  by_cases hvA : v ∈ A
  · have hblock : P.block v = A :=
      P.block_eq_of_mem hA hvA
    rw [hblock]
    exact Finset.card_le_card
      (componentBoundary_subset_cutBoundary
        (G := G) P A hvA)
  · have hne : P.block v ≠ A := by
      intro h
      exact hvA (h ▸ P.mem_block v)
    have hdisjoint : Disjoint (P.block v) A :=
      P.disjoint (P.block_mem_parts v) hA hne
    have hsubset :=
      componentBoundary_subset_remainderBoundary
        (G := G) P A hvA
    rw [Finset.sdiff_eq_self_of_disjoint hdisjoint] at hsubset
    exact Finset.card_le_card hsubset

/-- Connected-component normalization of one old part does not increase the
source potential. -/
theorem componentClustering_potential_le_of_mem_parts
    (P : VertexClustering V) (A : Finset V) (hA : A ∈ P.parts)
    (schedule : BoundedContribution) :
    clusteringPotential G (componentClustering G P A) schedule ≤
      clusteringPotential G P schedule := by
  classical
  unfold ChekuriChuzhoySection5SourcePotential.clusteringPotential
  apply Finset.sum_le_sum
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by
        exact mem_sourceEdgeFinset.mp he
      by_cases hnew :
          (componentClustering G P A).block u =
            (componentClustering G P A).block v
      · rw [edgePotential_eq_zero_of_same_block
          (G := G) _ schedule hnew]
        exact edgePotential_nonnegative (G := G) P schedule s(u, v)
      · have hold : P.block u ≠ P.block v := by
          intro hold
          by_cases huA : u ∈ A
          · have huBlock : P.block u = A :=
              P.block_eq_of_mem hA huA
            have hvA : v ∈ A := by
              rw [← huBlock]
              simpa [hold] using P.mem_block v
            exact hnew
              (same_componentBlock_of_adj_of_mem P A huv huA hvA)
          · have hvA : v ∉ A := by
              intro hvA
              have hvBlock : P.block v = A :=
                P.block_eq_of_mem hA hvA
              exact huA <| by
                rw [← hvBlock]
                simpa [hold] using P.mem_block u
            exact hnew
              (same_componentBlock_of_adj_of_not_mem_of_oldBlock_eq
                P A huv huA hvA hold)
        rw [edgePotential_eq_of_crosses
            (G := G) _ schedule hnew,
          edgePotential_eq_of_crosses (G := G) P schedule hold]
        have hu :=
          schedule.monotone
            (componentClustering_boundary_le_of_mem_parts
              (G := G) P A hA u)
        have hv :=
          schedule.monotone
            (componentClustering_boundary_le_of_mem_parts
              (G := G) P A hA v)
        have hu' :
            schedule.rho
                (endpointBoundarySize G
                  (componentClustering G P A) u) ≤
              schedule.rho (endpointBoundarySize G P u) := by
          simpa [endpointBoundarySize] using hu
        have hv' :
            schedule.rho
                (endpointBoundarySize G
                  (componentClustering G P A) v) ≤
              schedule.rho (endpointBoundarySize G P v) := by
          simpa [endpointBoundarySize] using hv
        linarith

/-- The complete preliminary part of Action 2 and Claim 5.7: adjust the cut,
take the component partition, and obtain a unit source-potential drop. -/
theorem exists_componentClustering_dropsByOne
    (P : VertexClustering V) (C terminals initial : Finset V)
    (schedule : BoundedContribution) (w0 : Nat)
    (hCpart : C ∈ P.parts)
    (hCinitial : C ⊆ initial)
    (hterminal : Disjoint initial terminals)
    (hlarge : IsLargeCluster G w0 C)
    (hcut : (originalBoundary G initial).card < w0 / 2) :
    ∃ A : Finset V,
      A ⊆ initial ∧ C ⊆ A ∧ Disjoint A terminals ∧
      (originalBoundary G A).card ≤
        (originalBoundary G initial).card ∧
      (∀ v, v ∉ A →
        (originalBoundary G
          ((componentClustering G P A).block v)).card ≤
        (originalBoundary G (P.block v)).card) ∧
      DropsByOne G schedule P (componentClustering G P A) := by
  obtain ⟨A, hAinitial, hCA, hAT, hAboundary, hremainder⟩ :=
    exists_adjustedSide (G := G) P C terminals initial
      hCpart hCinitial hterminal
  have hcontrolled :
      ∀ v, v ∉ A →
        (originalBoundary G
          ((componentClustering G P A).block v)).card ≤
        (originalBoundary G (P.block v)).card := by
    intro v hvA
    have hremNonempty : (P.block v \ A).Nonempty :=
      ⟨v, Finset.mem_sdiff.mpr ⟨P.mem_block v, hvA⟩⟩
    exact
      (Finset.card_le_card
        (componentBoundary_subset_remainderBoundary
          (G := G) P A hvA)).trans
        (hremainder (P.block v) (P.block_mem_parts v) hremNonempty)
  refine ⟨A, hAinitial, hCA, hAT, hAboundary, hcontrolled, ?_⟩
  apply componentClustering_dropsByOne
    (G := G) P A C schedule w0 hCpart hCA hlarge
    (lt_of_le_of_lt hAboundary hcut)
  exact hcontrolled

/-! ## Completing the preliminary partition by Theorem 5.5 -/

/-- Decompose a small preliminary part to the requested bandwidth, and leave
a large part unchanged. -/
noncomputable def completedPartOf
    (G : _root_.SimpleGraph V) (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    (U : Finset V) : Finpartition U := by
  classical
  exact if IsSmallCluster G threshold U then
    (BandwidthSplitTree.build G U cap alphaNum alphaDen
      hnum hratio).partition
  else ⊤

/-- Apply the bandwidth decomposition simultaneously to every small block. -/
noncomputable def bandwidthCompletion
    (G : _root_.SimpleGraph V) (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    (Q : VertexClustering V) : VertexClustering V :=
  Q.bind fun U _ =>
    completedPartOf G threshold cap alphaNum alphaDen hnum hratio U

theorem mem_bandwidthCompletion_iff
    (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    (Q : VertexClustering V) {R : Finset V} :
    R ∈ (bandwidthCompletion G threshold cap alphaNum alphaDen
      hnum hratio Q).parts ↔
      ∃ U : Finset V, ∃ hU : U ∈ Q.parts, R ∈
        (completedPartOf G threshold cap alphaNum alphaDen
          hnum hratio U).parts := by
  exact Finpartition.mem_bind

theorem completedPartOf_eq_decomposition
    (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    {U : Finset V} (hsmall : IsSmallCluster G threshold U) :
    completedPartOf G threshold cap alphaNum alphaDen hnum hratio U =
      (BandwidthSplitTree.build G U cap alphaNum alphaDen
        hnum hratio).partition := by
  simp [completedPartOf, hsmall]

theorem completedPartOf_eq_top
    (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    {U : Finset V} (hlarge : ¬ IsSmallCluster G threshold U) :
    completedPartOf G threshold cap alphaNum alphaDen hnum hratio U =
      ⊤ := by
  simp [completedPartOf, hlarge]

/-- Every small block of the completed clustering has the target bandwidth. -/
theorem bandwidthCompletion_small_bandwidth
    (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    (Q : VertexClustering V) {R : Finset V}
    (hR : R ∈ (bandwidthCompletion G threshold cap alphaNum alphaDen
      hnum hratio Q).parts)
    (hRsmall : IsSmallCluster G threshold R) :
    TruncatedScaledBandwidth G R cap alphaNum alphaDen := by
  rcases (mem_bandwidthCompletion_iff
    (G := G) threshold cap alphaNum alphaDen hnum hratio Q).mp hR with
    ⟨U, hU, hRU⟩
  by_cases hUsmall : IsSmallCluster G threshold U
  · rw [completedPartOf_eq_decomposition
      (G := G) threshold cap alphaNum alphaDen hnum hratio hUsmall] at hRU
    exact
      (BandwidthSplitTree.partition_bandwidth
        (BandwidthSplitTree.build G U cap alphaNum alphaDen
          hnum hratio)) R hRU
  · rw [completedPartOf_eq_top
      (G := G) threshold cap alphaNum alphaDen hnum hratio hUsmall] at hRU
    have hRUeq : R = U :=
      Finset.mem_singleton.mp
        (Finpartition.parts_top_subset U hRU)
    subst R
    exact False.elim (hUsmall hRsmall)

/-- A part produced by decomposing a small root remains small. -/
theorem bandwidthCompletion_part_small_of_root_small
    (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    {U R : Finset V} (hUsmall : IsSmallCluster G threshold U)
    (hRU : R ∈
      (completedPartOf G threshold cap alphaNum alphaDen
        hnum hratio U).parts) :
    IsSmallCluster G threshold R := by
  rw [completedPartOf_eq_decomposition
    (G := G) threshold cap alphaNum alphaDen hnum hratio hUsmall] at hRU
  have hboundary :=
    BandwidthSplitTree.partition_part_boundary_card_le_root
      (BandwidthSplitTree.build G U cap alphaNum alphaDen
        hnum hratio) hnum hratio hRU
  exact lt_of_le_of_lt hboundary hUsmall

/-- A terminal singleton of the preliminary clustering remains a singleton
part after bandwidth completion. -/
theorem singleton_mem_bandwidthCompletion
    (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    (Q : VertexClustering V) {t : V}
    (ht : ({t} : Finset V) ∈ Q.parts) :
    ({t} : Finset V) ∈
      (bandwidthCompletion G threshold cap alphaNum alphaDen
        hnum hratio Q).parts := by
  apply (mem_bandwidthCompletion_iff
    (G := G) threshold cap alphaNum alphaDen hnum hratio Q).2
  let R :=
    completedPartOf G threshold cap alphaNum alphaDen
      hnum hratio ({t} : Finset V)
  have hpart : R.part t ∈ R.parts := R.part_mem.mpr (by simp)
  have hsub : R.part t ⊆ ({t} : Finset V) := R.le hpart
  have htpart : t ∈ R.part t := R.mem_part (by simp)
  have heq : R.part t = ({t} : Finset V) := by
    apply Finset.Subset.antisymm hsub
    intro x hx
    have hxt : x = t := Finset.mem_singleton.mp hx
    subst x
    exact htpart
  exact ⟨{t}, ht, by simpa [R, heq] using hpart⟩

theorem terminal_singleton_mem_componentClustering
    (P : VertexClustering V) (A terminals : Finset V)
    (hterminal :
      ∀ t ∈ terminals, ({t} : Finset V) ∈ P.parts)
    (hAT : Disjoint A terminals)
    {t : V} (ht : t ∈ terminals) :
    ({t} : Finset V) ∈ (componentClustering G P A).parts := by
  have htA : t ∉ A := fun htA =>
    Finset.disjoint_left.mp hAT htA ht
  have hPblock : P.block t = ({t} : Finset V) :=
    P.block_eq_of_mem (hterminal t ht) (by simp)
  have hsub :
      (componentClustering G P A).block t ⊆ ({t} : Finset V) := by
    intro x hx
    have hxRem :=
      componentBlock_subset_oldBlock_sdiff
        (G := G) P A htA hx
    exact by
      rw [hPblock] at hxRem
      exact (Finset.mem_sdiff.mp hxRem).1
  have hsingleton :
      (componentClustering G P A).block t = ({t} : Finset V) := by
    apply Finset.Subset.antisymm hsub
    intro x hx
    have hxt : x = t := Finset.mem_singleton.mp hx
    subst x
    exact (componentClustering G P A).mem_block t
  rw [← hsingleton]
  exact (componentClustering G P A).block_mem_parts t

/-- The final clustering returned by Action 2 is acceptable.  This is the
structural half of Claim 5.7; its potential comparison is supplied by the
Theorem 5.5 compatibility theorem for the source schedule. -/
theorem bandwidthCompletion_component_isAcceptable
    (P : VertexClustering V) (A terminals : Finset V)
    (threshold cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    (hacceptable :
      IsAcceptable G terminals threshold cap alphaNum alphaDen P)
    (hAT : Disjoint A terminals) :
    IsAcceptable G terminals threshold cap alphaNum alphaDen
      (bandwidthCompletion G threshold cap alphaNum alphaDen
        hnum hratio (componentClustering G P A)) := by
  let Q := componentClustering G P A
  refine {
    terminal_singleton := ?_
    small_bandwidth := ?_
    large_connected := ?_ }
  · intro t ht
    apply singleton_mem_bandwidthCompletion
    exact terminal_singleton_mem_componentClustering
      (G := G) P A terminals hacceptable.terminal_singleton hAT ht
  · intro R hR hsmall
    exact bandwidthCompletion_small_bandwidth
      (G := G) threshold cap alphaNum alphaDen hnum hratio Q hR hsmall
  · intro R hR hlarge
    rcases (mem_bandwidthCompletion_iff
      (G := G) threshold cap alphaNum alphaDen
        hnum hratio Q).mp hR with ⟨U, hU, hRU⟩
    by_cases hUsmall : IsSmallCluster G threshold U
    · have hRsmall :=
        bandwidthCompletion_part_small_of_root_small
          (G := G) threshold cap alphaNum alphaDen
            hnum hratio hUsmall hRU
      exact False.elim
        ((smallCluster_iff_not_largeCluster G threshold R).mp
          hRsmall hlarge)
    · rw [completedPartOf_eq_top
        (G := G) threshold cap alphaNum alphaDen
          hnum hratio hUsmall] at hRU
      have hRUeq : R = U :=
        Finset.mem_singleton.mp
          (Finpartition.parts_top_subset U hRU)
      rcases Q.nonempty_of_mem_parts hU with ⟨v, hvU⟩
      have hQblock : Q.block v = U :=
        Q.block_eq_of_mem hU hvU
      subst R
      rw [← hQblock]
      exact componentBlock_connected (G := G) P A v

/-- The preliminary component clustering has the two structural properties
needed before Theorem 5.5 is applied to all of its small blocks. -/
theorem componentClustering_preAcceptable
    (P : VertexClustering V) (A terminals : Finset V)
    (threshold : Nat)
    (hterminal :
      ∀ t ∈ terminals, ({t} : Finset V) ∈ P.parts)
    (hAT : Disjoint A terminals) :
    PreAcceptable G terminals threshold
      (componentClustering G P A) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact terminal_singleton_mem_componentClustering
      (G := G) P A terminals hterminal hAT ht
  · intro R hR _hlarge
    rcases (componentClustering G P A).nonempty_of_mem_parts hR with
      ⟨v, hvR⟩
    have hblock :
        (componentClustering G P A).block v = R :=
      (componentClustering G P A).block_eq_of_mem hR hvR
    rw [← hblock]
    exact componentBlock_connected (G := G) P A v

/-- Complete Action 2 and Claim 5.7: after the preliminary unit drop, all
small component blocks are decomposed by Theorem 5.5.  The completion
preserves that drop and produces an acceptable clustering. -/
theorem exists_separate_acceptable_dropsByOne
    (P : VertexClustering V) (C terminals initial : Finset V)
    (w0 cap D : Nat) (hD : 4 ≤ D)
    (hupper :
      ∀ z, ChekuriChuzhoySection5Rho.rho w0 D z ≤ (1 : Rat) / 20)
    (hacceptable :
      IsAcceptable G terminals w0 cap 1 D P)
    (hCpart : C ∈ P.parts)
    (hCinitial : C ⊆ initial)
    (hterminal : Disjoint initial terminals)
    (hlarge : IsLargeCluster G w0 C)
    (hcut : (originalBoundary G initial).card < w0 / 2) :
    ∃ Q : VertexClustering V,
      IsAcceptable G terminals w0 cap 1 D Q ∧
      DropsByOne G
        (ChekuriChuzhoySection5Rho.boundedContributionOfUpper
          w0 D (by omega) hupper) P Q ∧
      (∀ R ∈ Q.parts, IsLargeCluster G w0 R →
        ∃ S ∈ P.parts, IsLargeCluster G w0 S ∧ R ⊆ S) := by
  let schedule :=
    ChekuriChuzhoySection5Rho.boundedContributionOfUpper
      w0 D (by omega) hupper
  obtain ⟨A, _hAinitial, _hCA, hAT, hAboundary,
      hcontrolled, hdrop⟩ :=
    exists_componentClustering_dropsByOne
      (G := G) P C terminals initial schedule w0
        hCpart hCinitial hterminal hlarge hcut
  let Q0 := componentClustering G P A
  have hpre :
      PreAcceptable G terminals w0 Q0 := by
    exact componentClustering_preAcceptable
      (G := G) P A terminals w0
        hacceptable.terminal_singleton hAT
  obtain ⟨Q, hQacceptable, hQpotential, hQlargeOld, _hQrefines⟩ :=
    exists_acceptableCompletion
      (G := G) Q0 terminals hD hupper hpre
  refine ⟨Q, hQacceptable, ?_, ?_⟩
  · unfold DropsByOne at hdrop ⊢
    change clusteringPotential G Q schedule + 1 ≤
      clusteringPotential G P schedule
    have hQpotential' :
        clusteringPotential G Q schedule ≤
          clusteringPotential G Q0 schedule := by
      simpa [schedule] using hQpotential
    have hdrop' :
        clusteringPotential G Q0 schedule + 1 ≤
          clusteringPotential G P schedule := by
      simpa [Q0] using hdrop
    linarith
  · intro R hRQ hRlarge
    have hRQ0 : R ∈ Q0.parts :=
      hQlargeOld R hRQ hRlarge
    rcases Q0.nonempty_of_mem_parts hRQ0 with ⟨v, hvR⟩
    have hQ0block : Q0.block v = R :=
      Q0.block_eq_of_mem hRQ0 hvR
    have hvA : v ∉ A := by
      intro hvA
      have hboundarySubset :=
        componentBoundary_subset_cutBoundary
          (G := G) P A hvA
      rw [hQ0block] at hboundarySubset
      have hcard :=
        (Finset.card_le_card hboundarySubset).trans hAboundary
      exact (by
        have hltHalf : (originalBoundary G R).card < w0 / 2 :=
          hcard.trans_lt hcut
        have hlt : (originalBoundary G R).card < w0 := by omega
        exact (smallCluster_iff_not_largeCluster G w0 R).mp hlt hRlarge)
    have hsubset :
        R ⊆ P.block v := by
      rw [← hQ0block]
      exact
        (componentBlock_subset_oldBlock_sdiff
          (G := G) P A hvA).trans Finset.sdiff_subset
    have hparentLarge : IsLargeCluster G w0 (P.block v) := by
      exact hRlarge.trans <| by
        rw [← hQ0block]
        exact hcontrolled v hvA
    exact ⟨P.block v, P.block_mem_parts v, hparentLarge, hsubset⟩

end ChekuriChuzhoySection5Separate
end SimpleGraph

end Lax17Proofs
