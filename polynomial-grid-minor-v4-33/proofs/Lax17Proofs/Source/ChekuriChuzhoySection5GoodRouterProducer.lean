import Lax17Proofs.Source.ChekuriChuzhoySection5HostSetup
import Lax17Proofs.Source.ChekuriChuzhoySection5Theorem511Phase
import Lax17Proofs.Source.ChekuriChuzhoySection5TerminalEdgeCount

namespace Lax17Proofs

universe u v w

/-!
# Source-facing good-router producer for Chekuri--Chuzhoy Section 5

This module composes the pendant-host setup with the source-potential proof of
journal Theorem 5.8.  Each phase uses Claims 5.9 and 5.10 followed by the
PARTITION/SEPARATE proof of Theorem 5.11.  No failed-router deletion axiom is
used.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5GoodRouterProducer


open ChekuriChuzhoyPendantVertex
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5GoodClustering
open ChekuriChuzhoySection5HostSetup
open ChekuriChuzhoySection5MinimalHost
open ChekuriChuzhoySection5RouterProduction
open ChekuriChuzhoySection5Routers
open ChekuriChuzhoySection5Rho
open ChekuriChuzhoySection5SourcePotential
open ChekuriChuzhoySection5TerminalEdgeCount
open ChekuriChuzhoySection5Theorem511Phase

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Chekuri--Chuzhoy Section 5 good-router production from an edge-minimal
host with independent degree-one terminals.

The source degree cap is
`floor (|terminals| / (192 * ell0^3 * log_2 |terminals|))`.  The explicit
strict maximum-degree and positivity hypotheses are exactly what initializes
the discrete good clustering and the connected-router localization. -/
theorem exists_goodRouterFamily_of_edgeMinimalHost
    {G0 : _root_.SimpleGraph V}
    {terminals : Finset V}
    (M : EdgeMinimalNodeWellLinkedHost G0 terminals)
    (Delta cap ell0 : Nat)
    (hdegree : MaxDegreeAtMost M.H Delta)
    (hdegreeCap :
      Delta < claim59SourceDegreeCap terminals.card ell0)
    (hell0 : 0 < ell0)
    (hcap : 1 < cap)
    (hthresholdCap :
      claim59SourceDegreeCap terminals.card ell0 ≤ cap)
    (hterminalTwo : 2 ≤ terminals.card)
    (hterminalDegree :
      ∀ t ∈ terminals, DegreeEquals M.H t 1)
    (hterminalIndependent :
      ∀ ⦃s⦄, s ∈ terminals → ∀ ⦃t⦄, t ∈ terminals →
        s ≠ t → ¬ M.H.Adj s t) :
    Nonempty
      (GoodRouterFamily M.H terminals ell0
        (claim59SourceDegreeCap terminals.card ell0)
        (claim59SourceDegreeCap terminals.card ell0 / 2) 1
        (16 * (20 * ell0) * (Nat.log 2 cap + 1))
        (claim59SourceDegreeCap terminals.card ell0 / 2)) := by
  classical
  let threshold := claim59SourceDegreeCap terminals.card ell0
  let denominator := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    omega
  let schedule :=
    sourceBoundedContribution threshold cap ell0
      hthreshold hcap (by simpa [threshold] using hthresholdCap) hell0
  have hpendant :
      ∀ t ∈ terminals,
        (originalBoundary M.H ({t} : Finset V)).card = 1 :=
    fun t ht =>
      originalBoundary_singleton_card_eq_one_of_degreeEquals
        (hterminalDegree t ht)
  let Valid : VertexClustering V → Prop := fun P =>
    IsGood M.H terminals threshold cap 1 denominator P
  let Output : Prop :=
    Nonempty
      (GoodRouterFamily M.H terminals ell0
        threshold (threshold / 2) 1 denominator (threshold / 2))
  have hinitial : Valid (⊥ : VertexClustering V) := by
    exact discrete_isGood M.H terminals threshold cap 1 denominator Delta
      hdegree (by simpa [threshold] using hdegreeCap)
      (by omega) (by
        have hpos : 0 < denominator := by
          dsimp [denominator]
          positivity
        omega)
  have houtput : Output := output_of_sourcePotential_descent
      M.H schedule Valid Output (⊥ : VertexClustering V) hinitial (by
        intro P hP
        have hcontractedCard :
            (contractedTerminals P terminals).card = terminals.card :=
          contractedTerminals_card_eq_of_isGood hP
        have hgoodPhase :
            IsGood M.H terminals
              (claim59SourceDegreeCap
                (contractedTerminals P terminals).card ell0)
              cap 1 denominator P := by
          simpa [hcontractedCard, threshold] using hP
        have hthresholdPhase :
            0 < claim59SourceDegreeCap
              (contractedTerminals P terminals).card ell0 := by
          simpa [hcontractedCard, threshold] using hthreshold
        have hthresholdCapPhase :
            claim59SourceDegreeCap
              (contractedTerminals P terminals).card ell0 ≤ cap := by
          simpa [hcontractedCard] using hthresholdCap
        have hterminalCard :
            terminals.card ≤
              3 * (nonterminalEdges (legalContractedGraph M.H P)
                (contractedTerminals P terminals)).card :=
          terminal_card_le_three_mul_nonterminalEdges
            M.H terminals cap 1 denominator ell0 hell0 P
            hgoodPhase hthresholdPhase M.nodeWellLinked hpendant
            hterminalIndependent
        rcases phase_good_drop_or_goodRouterFamily
            M.H terminals cap ell0 hell0 hcap P hgoodPhase
              hthresholdPhase hthresholdCapPhase hterminalTwo
              hpendant hterminalCard with hnext | hrouters
        · exact Or.inr (by
            simpa [Valid, schedule, threshold, denominator,
              hcontractedCard] using hnext)
        · exact Or.inl (by
            simpa [Output, threshold, denominator, hcontractedCard]
              using hrouters))
  simpa [Output, threshold, denominator] using houtput

/-- Source-facing pendant normalization followed by good-router production.
The maximum degree rises from `Delta` to `Delta + 1`, which is reflected in
the strict source-cap hypothesis. -/
theorem exists_goodRouterFamily_of_pendantHost
    {G : _root_.SimpleGraph V} {X : Finset V}
    (Delta cap ell0 : Nat)
    (hdegree : MaxDegreeAtMost G Delta)
    (hdegreeCap :
      Delta + 1 < claim59SourceDegreeCap X.card ell0)
    (hell0 : 0 < ell0)
    (hcap : 1 < cap)
    (hthresholdCap :
      claim59SourceDegreeCap X.card ell0 ≤ cap)
    (hXcard : 2 ≤ X.card)
    (hXwell :
      NodeWellLinkedIn G (Finset.univ : Finset V) X) :
    ∃ M : EdgeMinimalNodeWellLinkedHost
        (graph (X := X) G) (leaves (V := V) (X := X)),
      Nonempty
        (GoodRouterFamily M.H (leaves (V := V) (X := X)) ell0
          (claim59SourceDegreeCap X.card ell0)
          (claim59SourceDegreeCap X.card ell0 / 2) 1
          (16 * (20 * ell0) * (Nat.log 2 cap + 1))
          (claim59SourceDegreeCap X.card ell0 / 2)) := by
  obtain ⟨M, hMdegree, hterminalDegree, _hpendant⟩ :=
    exists_edgeMinimalPendantHost hdegree hXcard hXwell
  have hterminalIndependent :
      ∀ ⦃s⦄, s ∈ leaves (V := V) (X := X) →
        ∀ ⦃t⦄, t ∈ leaves (V := V) (X := X) →
          s ≠ t → ¬ M.H.Adj s t := by
    intro s hs t ht _hst hadj
    obtain ⟨x, rfl⟩ := exists_leafValue hs
    obtain ⟨y, rfl⟩ := exists_leafValue ht
    have horiginal := M.le_original hadj
    simp [graph, rel] at horiginal
  refine ⟨M, ?_⟩
  have hfamily :=
    exists_goodRouterFamily_of_edgeMinimalHost
      M (Delta + 1) cap ell0 hMdegree
      (by simpa using hdegreeCap) hell0 hcap
      (by simpa using hthresholdCap)
      (by simpa using hXcard) hterminalDegree hterminalIndependent
  simpa using hfamily

end ChekuriChuzhoySection5GoodRouterProducer
end SimpleGraph

end Lax17Proofs
