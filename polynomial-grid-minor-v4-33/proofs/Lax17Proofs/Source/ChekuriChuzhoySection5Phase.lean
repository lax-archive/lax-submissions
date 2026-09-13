import Lax17Proofs.Source.ChekuriChuzhoySection5Claim510

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 phase

This module assembles Claim 5.9 and Claim 5.10.  It produces either the next
good clustering with a one-unit source-potential drop, or the family of
pairwise-disjoint large connected clusters on which journal Theorem 5.11 is
run.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase


open Finset
open ChekuriChuzhoySection5Claim510
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5DenseBlockReplacement
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5Rho
open ChekuriChuzhoySection5RouterProduction
open ChekuriChuzhoySection5SourcePotential

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- State produced immediately before Theorem 5.11 in the journal proof. -/
structure LargeClusterSeedFamily
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (P : VertexClustering V) (w0 cap D ell0 : Nat)
    (schedule : BoundedContribution) : Type u where
  clustering : Fin ell0 → VertexClustering V
  region : Fin ell0 → Finset V
  cluster : Fin ell0 → Finset V
  acceptable : ∀ i,
    IsAcceptable G terminals w0 cap 1 D (clustering i)
  part : ∀ i, cluster i ∈ (clustering i).parts
  large : ∀ i, IsLargeCluster G w0 (cluster i)
  connected : ∀ i, (G.induce {v : V | v ∈ cluster i}).Connected
  terminal_disjoint : ∀ i, Disjoint (cluster i) terminals
  cluster_subset_region : ∀ i, cluster i ⊆ region i
  all_large_inside : ∀ i C, C ∈ (clustering i).parts →
    IsLargeCluster G w0 C → C ⊆ region i
  region_terminal_disjoint : ∀ i, Disjoint (region i) terminals
  pairwise_disjoint :
    Pairwise fun i j => Disjoint (region i) (region j)
  initial_drop : ∀ i, DropsByOne G schedule P (clustering i)

/-- Claims 5.9 and 5.10 assembled exactly as in the first half of Theorem
5.8.  If none of the `ell0` acceptable clusterings is already good, choose
one large block from each.  Property (P1) from Claim 5.10 makes these blocks
pairwise disjoint and terminal-free. -/
theorem good_drop_or_largeClusterSeedFamily
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (cap ell0 : Nat) (hell0 : 0 < ell0) (hcap : 1 < cap)
    (P : VertexClustering V)
    (hgood :
      IsGood G terminals
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap 1 (16 * (20 * ell0) * (Nat.log 2 cap + 1)) P)
    (hthreshold :
      0 < claim59SourceDegreeCap
        (contractedTerminals P terminals).card ell0)
    (hthresholdCap :
      claim59SourceDegreeCap
        (contractedTerminals P terminals).card ell0 ≤ cap)
    (hterminalTwo : 2 ≤ terminals.card)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary G ({t} : Finset V)).card = 1)
    (hterminalCard : terminals.card ≤
      3 * (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card) :
    (∃ Q : VertexClustering V,
      IsGood G terminals
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap 1 (16 * (20 * ell0) * (Nat.log 2 cap + 1)) Q ∧
      DropsByOne G
        (sourceBoundedContribution
          (claim59SourceDegreeCap
            (contractedTerminals P terminals).card ell0)
          cap ell0 hthreshold hcap hthresholdCap hell0)
        P Q) ∨
    Nonempty
      (LargeClusterSeedFamily G terminals P
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap (16 * (20 * ell0) * (Nat.log 2 cap + 1)) ell0
        (sourceBoundedContribution
          (claim59SourceDegreeCap
            (contractedTerminals P terminals).card ell0)
          cap ell0 hthreshold hcap hthresholdCap hell0)) := by
  classical
  let w0 :=
    claim59SourceDegreeCap
      (contractedTerminals P terminals).card ell0
  let D := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
  let schedule :=
    sourceBoundedContribution w0 cap ell0
      hthreshold hcap hthresholdCap hell0
  obtain ⟨blocks, hblocksTerminal, _hpartition, hblocksDisjoint,
      hblockBoundary, hblockInternal⟩ :=
    exists_densePartition_of_goodClustering_source_parameters
      (G := G) (P := P) hell0 hgood hterminalTwo hpendant hterminalCard
  have hblockTerminalDisjoint :
      ∀ i, Disjoint (blocks i)
        (contractedTerminals P terminals) := by
    intro i
    rw [Finset.disjoint_left]
    intro C hCB hCT
    exact (Finset.mem_sdiff.mp (hblocksTerminal i hCB)).2 hCT
  have hterminalCard' :
      (contractedTerminals P terminals).card ≤
        3 * (nonterminalEdges (legalContractedGraph G P)
          (contractedTerminals P terminals)).card := by
    rw [contractedTerminals_card_eq_of_isGood hgood]
    exact hterminalCard
  have hclaim :
      ∀ i : Fin ell0, ∃ Q : VertexClustering V,
        IsAcceptable G terminals w0 cap 1 D Q ∧
        DropsByOne G schedule P Q ∧
        (∀ C ∈ Q.parts, IsLargeCluster G w0 C →
          C ⊆ selectedUnion (blocks i)) := by
    intro i
    obtain ⟨Q, hQacceptable, hQdrop, hQinside⟩ :=
      exists_claim510_clustering
        G terminals cap ell0 hell0 hcap P
        (by simpa [w0, D] using hgood)
        hthreshold hthresholdCap hterminalCard'
        (blocks i) (hblockTerminalDisjoint i)
        (hblockBoundary i) (hblockInternal i)
    exact ⟨Q, by simpa [w0, D] using hQacceptable,
      by simpa [schedule, w0] using hQdrop,
      by simpa [w0] using hQinside⟩
  let clustering : Fin ell0 → VertexClustering V :=
    fun i => Classical.choose (hclaim i)
  have hclustering :
      ∀ i : Fin ell0,
        IsAcceptable G terminals w0 cap 1 D (clustering i) ∧
        DropsByOne G schedule P (clustering i) ∧
        (∀ C ∈ (clustering i).parts, IsLargeCluster G w0 C →
          C ⊆ selectedUnion (blocks i)) :=
    fun i => Classical.choose_spec (hclaim i)
  by_cases hsome :
      ∃ i : Fin ell0,
        IsGood G terminals w0 cap 1 D (clustering i)
  · rcases hsome with ⟨i, hi⟩
    exact Or.inl
      ⟨clustering i, by simpa [w0, D] using hi,
        by simpa [schedule, w0] using (hclustering i).2.1⟩
  · have hlarge :
        ∀ i : Fin ell0, ∃ C ∈ (clustering i).parts,
          IsLargeCluster G w0 C := by
      intro i
      by_contra hnone
      push Not at hnone
      apply hsome
      refine ⟨i, (hclustering i).1, ?_⟩
      intro C hC
      exact (smallCluster_iff_not_largeCluster G w0 C).2
        (hnone C hC)
    let cluster : Fin ell0 → Finset V :=
      fun i => Classical.choose (hlarge i)
    have hcluster :
        ∀ i : Fin ell0,
          cluster i ∈ (clustering i).parts ∧
          IsLargeCluster G w0 (cluster i) :=
      fun i => Classical.choose_spec (hlarge i)
    apply Or.inr
    refine ⟨{
      clustering := clustering
      region := fun i => selectedUnion (blocks i)
      cluster := cluster
      acceptable := fun i => (hclustering i).1
      part := fun i => (hcluster i).1
      large := fun i => (hcluster i).2
      connected := ?_
      terminal_disjoint := ?_
      cluster_subset_region := fun i =>
        (hclustering i).2.2
          (cluster i) (hcluster i).1 (hcluster i).2
      all_large_inside := fun i C hC hlarge =>
        (hclustering i).2.2 C hC hlarge
      region_terminal_disjoint := fun i =>
        selectedUnion_disjoint_terminals
          P (blocks i) terminals (hblockTerminalDisjoint i)
      pairwise_disjoint := ?_
      initial_drop := fun i => (hclustering i).2.1 }⟩
    · intro i
      exact (hclustering i).1.large_connected
        (cluster i) (hcluster i).1 (hcluster i).2
    · intro i
      exact (selectedUnion_disjoint_terminals
        P (blocks i) terminals (hblockTerminalDisjoint i)).mono_left
          ((hclustering i).2.2
            (cluster i) (hcluster i).1 (hcluster i).2)
    · intro i j hij
      rw [Finset.disjoint_left]
      intro v hvi hvj
      have hviB :
          contractedVertex P v ∈ blocks i :=
        (mem_selectedUnion_iff (blocks i) v).1 hvi
      have hvjB :
          contractedVertex P v ∈ blocks j :=
        (mem_selectedUnion_iff (blocks j) v).1 hvj
      exact Finset.disjoint_left.mp
        (hblocksDisjoint i j hij) hviB hvjB

end ChekuriChuzhoySection5Phase
end SimpleGraph

end Lax17Proofs
