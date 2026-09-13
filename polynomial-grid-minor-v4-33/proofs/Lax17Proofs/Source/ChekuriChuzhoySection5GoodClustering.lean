import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthDecomposition
import Lax17Proofs.Source.ChekuriChuzhoySection5RouterProduction

namespace Lax17Proofs

universe u v w

/-!
# Minimum good clusterings for Chekuri--Chuzhoy Section 5

The nonconstructive proof in journal Section 5.1 chooses, after making the
terminal host edge-minimal, a good clustering whose legal contracted graph has
the fewest named edges.  This module constructs that finite minimizer.  It
also records the singleton boundary calculation used to show that the
discrete clustering is a concrete initial candidate.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5GoodClustering


open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5BandwidthDecomposition

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The edge boundary of a singleton is its ordinary incidence finset. -/
theorem clusterBoundary_singleton_eq_incidenceFinset
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Section44.clusterBoundary G ({v} : Finset V) =
      G.incidenceFinset v := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [G.mem_incidenceFinset, mk_mem_clusterBoundary_iff]
      change
        (G.Adj x y ∧
          ((x ∈ ({v} : Finset V) ∧ y ∉ ({v} : Finset V)) ∨
            (y ∈ ({v} : Finset V) ∧ x ∉ ({v} : Finset V)))) ↔
          s(x, y) ∈ G.edgeSet ∧ v ∈ s(x, y)
      simp only [_root_.SimpleGraph.mem_edgeSet, Sym2.mem_iff,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hxy, h | h⟩
        · exact ⟨hxy, Or.inl h.1.symm⟩
        · exact ⟨hxy, Or.inr h.1.symm⟩
      · rintro ⟨hxy, h | h⟩
        · exact ⟨hxy, Or.inl
            ⟨h.symm, fun hy => hxy.ne (h.symm.trans hy.symm)⟩⟩
        · exact ⟨hxy, Or.inr ⟨h.symm,
            fun hx => hxy.ne (hx.trans h)⟩⟩

@[simp] theorem originalBoundary_singleton_card
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (originalBoundary G ({v} : Finset V)).card = G.degree v := by
  classical
  rw [originalBoundary, clusterBoundary_singleton_eq_incidenceFinset,
    G.card_incidenceFinset_eq_degree]

theorem degree_le_of_degreeAtMost
    [DecidableRel G.Adj] {v : V} {d : Nat} (h : DegreeAtMost G v d) :
    G.degree v ≤ d := by
  classical
  rcases h with ⟨N, hN, hcard⟩
  have hN_eq : N = G.neighborFinset v := by
    ext w
    simp only [G.mem_neighborFinset]
    exact hN w
  rw [← G.card_neighborFinset_eq_degree, ← hN_eq]
  exact hcard

/-- If the threshold strictly exceeds the host maximum degree, the discrete
partition is a good clustering. -/
theorem discrete_isGood
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen Delta : Nat)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : Delta < threshold)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    IsGood G terminals threshold cap alphaNum alphaDen
      (⊥ : VertexClustering V) := by
  classical
  letI := Classical.decRel G.Adj
  constructor
  · refine {
      terminal_singleton := ?_
      small_bandwidth := ?_
      large_connected := ?_ }
    · intro t ht
      rw [Finpartition.mem_bot_iff]
      exact ⟨t, Finset.mem_univ t, rfl⟩
    · intro C hC _hsmall
      rw [Finpartition.mem_bot_iff] at hC
      rcases hC with ⟨v, _hv, rfl⟩
      exact truncatedScaledBandwidth_singleton
        G v cap alphaNum alphaDen hnum hratio
    · intro C hC hlarge
      rw [Finpartition.mem_bot_iff] at hC
      rcases hC with ⟨v, _hv, rfl⟩
      have hdeg : G.degree v ≤ Delta :=
        degree_le_of_degreeAtMost (hdegree v)
      have := hlarge
      simp only [IsLargeCluster, originalBoundary_singleton_card] at this
      omega
  · intro C hC
    rw [Finpartition.mem_bot_iff] at hC
    rcases hC with ⟨v, _hv, rfl⟩
    simp only [IsSmallCluster, originalBoundary_singleton_card]
    exact (degree_le_of_degreeAtMost (hdegree v)).trans_lt hDelta

/-- A good clustering minimizing the number of original cross-block edge
copies, equivalently the edge count of its legal contracted multigraph. -/
structure IsMinimumGoodClustering
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen : Nat)
    (P : VertexClustering V) : Prop where
  good : IsGood G terminals threshold cap alphaNum alphaDen P
  minimal :
    ∀ Q : VertexClustering V,
      IsGood G terminals threshold cap alphaNum alphaDen Q →
        (crossBlockOriginalEdges G P).card ≤
          (crossBlockOriginalEdges G Q).card

/-- The finite family of good clusterings has a crossing-edge minimizer. -/
theorem exists_minimumGoodClustering
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (threshold cap alphaNum alphaDen Delta : Nat)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : Delta < threshold)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    ∃ P : VertexClustering V,
      IsMinimumGoodClustering G terminals
        threshold cap alphaNum alphaDen P := by
  classical
  let candidates : Finset (VertexClustering V) :=
    Finset.univ.filter fun P =>
      IsGood G terminals threshold cap alphaNum alphaDen P
  have hcandidates : candidates.Nonempty := by
    refine ⟨(⊥ : VertexClustering V), ?_⟩
    simp [candidates, discrete_isGood G terminals threshold cap
      alphaNum alphaDen Delta hdegree hDelta hnum hratio]
  rcases candidates.exists_min_image
      (fun P => (crossBlockOriginalEdges G P).card) hcandidates with
    ⟨P, hPmem, hPmin⟩
  have hPgood :
      IsGood G terminals threshold cap alphaNum alphaDen P := by
    simpa [candidates] using hPmem
  refine ⟨P, ⟨hPgood, ?_⟩⟩
  intro Q hQ
  apply hPmin
  simp [candidates, hQ]

end ChekuriChuzhoySection5GoodClustering
end SimpleGraph

end Lax17Proofs
