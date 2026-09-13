import Lax17Proofs.Source.ChekuriChuzhoySection5Phase
import Lax17Proofs.Source.ChekuriChuzhoySection5PartitionAction
import Lax17Proofs.Source.ChekuriChuzhoySection5Routers

namespace Lax17Proofs

universe u v w

/-!
# Theorem 5.11 inside the Section 5 phase

The journal proof repeatedly applies PARTITION until the currently selected
large cluster has bandwidth, and applies SEPARATE when edge Menger returns a
terminal cut.  The finite minimal-refinement argument below packages the
PARTITION iterations; the source-potential descent packages the SEPARATE
iterations.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Theorem511Phase


open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5PartitionAction
open ChekuriChuzhoySection5Phase
open ChekuriChuzhoySection5Rho
open ChekuriChuzhoySection5RouterProduction
open ChekuriChuzhoySection5Routers
open ChekuriChuzhoySection5Separate
open ChekuriChuzhoySection5SourcePotential

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The finite PARTITION loop from the proof of Theorem 5.8. -/
theorem exists_bandwidth_normalization
    (P : VertexClustering V) (terminals region : Finset V)
    (w0 cap D : Nat) (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (hacceptable : IsAcceptable G terminals w0 cap 1 D P)
    (hterminal : Disjoint region terminals)
    (hlargeInside :
      ∀ C ∈ P.parts, IsLargeCluster G w0 C → C ⊆ region) :
    ∃ Q : VertexClustering V,
      IsAcceptable G terminals w0 cap 1 D Q ∧
      clusteringPotential G Q
          (boundedContributionOfUpper w0 D (by omega) hupper) ≤
        clusteringPotential G P
          (boundedContributionOfUpper w0 D (by omega) hupper) ∧
      (∀ C ∈ Q.parts, IsLargeCluster G w0 C → C ⊆ region) ∧
      (∀ C ∈ Q.parts, IsLargeCluster G w0 C →
        TruncatedScaledBandwidth G C (w0 / 2) 1 D) := by
  classical
  let schedule :=
    boundedContributionOfUpper w0 D (by omega) hupper
  let Candidate : VertexClustering V → Prop := fun Q =>
    IsAcceptable G terminals w0 cap 1 D Q ∧
      clusteringPotential G Q schedule ≤
        clusteringPotential G P schedule ∧
      ∀ C ∈ Q.parts, IsLargeCluster G w0 C → C ⊆ region
  let candidates : Finset (VertexClustering V) :=
    Finset.univ.filter Candidate
  have hcandidates : candidates.Nonempty := by
    refine ⟨P, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hacceptable, le_rfl, hlargeInside⟩
  obtain ⟨Q, hQminimal⟩ := candidates.exists_minimal hcandidates
  have hQcandidate : Candidate Q := by
    simpa [candidates] using hQminimal.1
  have hQband :
      ∀ C ∈ Q.parts, IsLargeCluster G w0 C →
        TruncatedScaledBandwidth G C (w0 / 2) 1 D := by
    intro C hCQ hClarge
    by_contra hnot
    obtain ⟨R, hRacceptable, hRpotential, hRlt, hRinside⟩ :=
      exists_partition_acceptable_strict_refinement
        (G := G) Q C terminals region w0 cap D hD hupper
        hQcandidate.1 hCQ hClarge
        (hQcandidate.2.2 C hCQ hClarge)
        hterminal hQcandidate.2.2 hnot
    have hRcandidate : Candidate R :=
      ⟨hRacceptable, hRpotential.trans hQcandidate.2.1, hRinside⟩
    have hRmem : R ∈ candidates := by
      simp [candidates, hRcandidate]
    exact hRlt.2 (hQminimal.2 hRmem hRlt.1)
  exact ⟨Q, hQcandidate.1, by simpa [schedule] using hQcandidate.2.1,
    hQcandidate.2.2, hQband⟩

/-- Theorem 5.11 for one of the disjoint regions produced by Claims 5.9 and
5.10.  PARTITION is absorbed by `exists_bandwidth_normalization`; a failed
terminal routing invokes SEPARATE and decreases the source potential. -/
theorem good_or_router_in_region
    (P : VertexClustering V) (terminals region : Finset V)
    (w0 cap D : Nat) (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (hacceptable : IsAcceptable G terminals w0 cap 1 D P)
    (hterminal : Disjoint region terminals)
    (hlargeInside :
      ∀ C ∈ P.parts, IsLargeCluster G w0 C → C ⊆ region) :
    (∃ Q : VertexClustering V,
      IsGood G terminals w0 cap 1 D Q ∧
      clusteringPotential G Q
          (boundedContributionOfUpper w0 D (by omega) hupper) ≤
        clusteringPotential G P
          (boundedContributionOfUpper w0 D (by omega) hupper)) ∨
    ∃ router : Finset V,
      router ⊆ region ∧
      GoodRouter G terminals router w0 (w0 / 2) 1 D (w0 / 2) := by
  classical
  let schedule :=
    boundedContributionOfUpper w0 D (by omega) hupper
  let Valid : VertexClustering V → Prop := fun Q =>
    IsAcceptable G terminals w0 cap 1 D Q ∧
      clusteringPotential G Q schedule ≤
        clusteringPotential G P schedule ∧
      ∀ C ∈ Q.parts, IsLargeCluster G w0 C → C ⊆ region
  let Output : Prop :=
    (∃ Q : VertexClustering V,
      IsGood G terminals w0 cap 1 D Q ∧
      clusteringPotential G Q schedule ≤
        clusteringPotential G P schedule) ∨
    ∃ router : Finset V,
      router ⊆ region ∧
      GoodRouter G terminals router w0 (w0 / 2) 1 D (w0 / 2)
  have hinitial : Valid P :=
    ⟨hacceptable, le_rfl, hlargeInside⟩
  have houtput : Output := output_of_sourcePotential_descent
      G schedule Valid Output P hinitial (by
        intro Q hQ
        obtain ⟨R, hRacceptable, hRpotential, hRinside, hRband⟩ :=
          exists_bandwidth_normalization
            (G := G) Q terminals region w0 cap D hD hupper
              hQ.1 hterminal hQ.2.2
        by_cases hgood : IsGood G terminals w0 cap 1 D R
        · exact Or.inl (Or.inl
            ⟨R, hgood, hRpotential.trans hQ.2.1⟩)
        · have hlarge :
              ∃ C ∈ R.parts, IsLargeCluster G w0 C := by
            by_contra hnone
            apply hgood
            refine ⟨hRacceptable, ?_⟩
            intro C hCR
            exact (smallCluster_iff_not_largeCluster G w0 C).2
              (by
                intro hClarge
                apply hnone
                exact ⟨C, hCR, hClarge⟩)
          obtain ⟨C, hCR, hClarge⟩ := hlarge
          have hCregion : C ⊆ region :=
            hRinside C hCR hClarge
          have hCT : Disjoint C terminals :=
            hterminal.mono_left hCregion
          rcases hasEdgeDisjointPaths_or_routerTerminalCut
              (G := G) C terminals (w0 / 2) hCT with hroute | hcutWitness
          · exact Or.inl (Or.inr
              ⟨C, hCregion,
                { terminal_disjoint := hCT
                  connected := hRacceptable.large_connected C hCR hClarge
                  large := hClarge
                  bandwidth := hRband C hCR hClarge
                  routes := hroute }⟩)
          · rcases hcutWitness with ⟨cut⟩
            have hside :
                (Finset.univ : Finset V) \ cut.routerSide =
                  cut.terminalSide :=
              cut.disjoint.sdiff_eq_of_sup_eq cut.cover
            have hboundary :
                originalBoundary G cut.routerSide =
                  EdgeMenger.edgeBoundary G cut.routerSide
                    cut.terminalSide := by
              rw [originalBoundary, Section44.clusterBoundary, hside,
                Section44.edgeBoundary_eq_edgeMenger]
            have hcut :
                (originalBoundary G cut.routerSide).card < w0 / 2 := by
              rw [hboundary]
              exact cut.boundary_lt
            have hCside : C ⊆ cut.routerSide := cut.router_subset
            have hsideT : Disjoint cut.routerSide terminals :=
              cut.disjoint.mono_right cut.terminals_subset
            obtain ⟨S, hSacceptable, hSdrop, hSancestry⟩ :=
              exists_separate_acceptable_dropsByOne
                (G := G) R C terminals cut.routerSide
                  w0 cap D hD hupper hRacceptable hCR hCside
                  hsideT hClarge hcut
            have hSinside :
                ∀ A ∈ S.parts, IsLargeCluster G w0 A →
                  A ⊆ region := by
              intro A hAS hAlarge
              obtain ⟨B, hBR, hBlarge, hAB⟩ :=
                hSancestry A hAS hAlarge
              exact hAB.trans (hRinside B hBR hBlarge)
            have hSP :
                clusteringPotential G S schedule ≤
                  clusteringPotential G P schedule := by
              have hSR :
                  clusteringPotential G S schedule + 1 ≤
                    clusteringPotential G R schedule := by
                simpa [schedule] using hSdrop
              linarith [hRpotential, hQ.2.1]
            have hSQ :
                DropsByOne G schedule Q S := by
              unfold DropsByOne
              have hSR :
                  clusteringPotential G S schedule + 1 ≤
                    clusteringPotential G R schedule := by
                simpa [schedule] using hSdrop
              linarith [hRpotential]
            exact Or.inr ⟨S, ⟨hSacceptable, hSP, hSinside⟩, hSQ⟩)
  simpa [Output, schedule] using houtput

/-- Run Theorem 5.11 independently in the pairwise-disjoint regions supplied
by Claims 5.9 and 5.10.  Either one region yields the next good clustering, or
all regions yield the required disjoint good-router family. -/
theorem seedFamily_good_drop_or_goodRouterFamily
    (P : VertexClustering V) (terminals : Finset V)
    (w0 cap D ell0 : Nat) (hD : 4 ≤ D)
    (hupper : ∀ z, rho w0 D z ≤ (1 : Rat) / 20)
    (seed : LargeClusterSeedFamily G terminals P w0 cap D ell0
      (boundedContributionOfUpper w0 D (by omega) hupper)) :
    (∃ Q : VertexClustering V,
      IsGood G terminals w0 cap 1 D Q ∧
      DropsByOne G
        (boundedContributionOfUpper w0 D (by omega) hupper) P Q) ∨
    Nonempty
      (GoodRouterFamily G terminals ell0
        w0 (w0 / 2) 1 D (w0 / 2)) := by
  classical
  let schedule :=
    boundedContributionOfUpper w0 D (by omega) hupper
  have hchoice :
      ∀ i : Fin ell0,
        (∃ Q : VertexClustering V,
          IsGood G terminals w0 cap 1 D Q ∧
          clusteringPotential G Q schedule ≤
            clusteringPotential G (seed.clustering i) schedule) ∨
        ∃ router : Finset V,
          router ⊆ seed.region i ∧
          GoodRouter G terminals router
            w0 (w0 / 2) 1 D (w0 / 2) := by
    intro i
    simpa [schedule] using
      (good_or_router_in_region
        (G := G) (seed.clustering i) terminals (seed.region i)
          w0 cap D hD hupper (seed.acceptable i)
          (seed.region_terminal_disjoint i) (seed.all_large_inside i))
  by_cases hsome :
      ∃ i : Fin ell0, ∃ Q : VertexClustering V,
        IsGood G terminals w0 cap 1 D Q ∧
        clusteringPotential G Q schedule ≤
          clusteringPotential G (seed.clustering i) schedule
  · obtain ⟨i, Q, hQgood, hQpotential⟩ := hsome
    refine Or.inl ⟨Q, hQgood, ?_⟩
    unfold DropsByOne
    have hseed :
        clusteringPotential G (seed.clustering i) schedule + 1 ≤
          clusteringPotential G P schedule := by
      simpa [schedule] using seed.initial_drop i
    linarith
  · have hrouters :
        ∀ i : Fin ell0, ∃ router : Finset V,
          router ⊆ seed.region i ∧
          GoodRouter G terminals router
            w0 (w0 / 2) 1 D (w0 / 2) := by
      intro i
      rcases hchoice i with hgood | hrouter
      · exact (hsome ⟨i, hgood⟩).elim
      · exact hrouter
    let router : Fin ell0 → Finset V :=
      fun i => Classical.choose (hrouters i)
    have hrouter :
        ∀ i : Fin ell0,
          router i ⊆ seed.region i ∧
          GoodRouter G terminals (router i)
            w0 (w0 / 2) 1 D (w0 / 2) :=
      fun i => Classical.choose_spec (hrouters i)
    refine Or.inr ⟨{
      router := router
      good := fun i => (hrouter i).2
      pairwise_disjoint := ?_
    }⟩
    intro i j hij
    exact (seed.pairwise_disjoint hij).mono
      (hrouter i).1 (hrouter j).1

/-- Claims 5.9, 5.10, and Theorem 5.11 assembled into the complete inner
phase of journal Theorem 5.8. -/
theorem phase_good_drop_or_goodRouterFamily
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
      (GoodRouterFamily G terminals ell0
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0 / 2)
        1 (16 * (20 * ell0) * (Nat.log 2 cap + 1))
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0 / 2)) := by
  classical
  let w0 :=
    claim59SourceDegreeCap
      (contractedTerminals P terminals).card ell0
  let D := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
  let schedule :=
    sourceBoundedContribution w0 cap ell0
      hthreshold hcap hthresholdCap hell0
  rcases good_drop_or_largeClusterSeedFamily
      G terminals cap ell0 hell0 hcap P hgood hthreshold
        hthresholdCap hterminalTwo hpendant hterminalCard with
    hnext | hseedWitness
  · exact Or.inl hnext
  · rcases hseedWitness with ⟨seed⟩
    have hsize :
        (80 : Rat) * (harmonic w0 + 2) ≤ D := by
      simpa [w0, D] using
        source_denominator_size hthreshold hcap hthresholdCap hell0
    have hDpos : 0 < D := by
      dsimp [D]
      positivity
    have hD : 4 ≤ D := by
      calc
        4 ≤ 16 := by omega
        _ ≤ 16 * (20 * ell0) :=
          Nat.le_mul_of_pos_right 16 (by positivity)
        _ ≤ 16 * (20 * ell0) * (Nat.log 2 cap + 1) :=
          Nat.le_mul_of_pos_right _ (by positivity)
    have hupper :
        ∀ z, rho w0 D z ≤ (1 : Rat) / 20 :=
      rho_le_one_twentieth hDpos hsize
    have hseed :
        LargeClusterSeedFamily G terminals P w0 cap D ell0
          (boundedContributionOfUpper w0 D hDpos hupper) := by
      simpa [schedule, sourceBoundedContribution, boundedContribution,
        hsize, w0, D] using seed
    rcases seedFamily_good_drop_or_goodRouterFamily
        (G := G) P terminals w0 cap D ell0 hD hupper hseed with
      hnext | hrouters
    · exact Or.inl (by
        simpa [schedule, sourceBoundedContribution, boundedContribution,
          hsize, w0, D] using hnext)
    · exact Or.inr (by simpa [w0, D] using hrouters)

end ChekuriChuzhoySection5Theorem511Phase
end SimpleGraph

end Lax17Proofs
