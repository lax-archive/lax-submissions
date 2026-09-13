import Lax17Proofs.Source.AppendixA3Claim73Complete

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Lemma 7.2

This file completes the deletable-edge argument in Section 7.  It first proves
that the minimum Menger-side set contains an edge, then uses Claim 7.3 and edge
minimality to obtain the required edge-disjoint terminal--`Gamma` packing.
-/

namespace SimpleGraph
namespace AppendixA3Lemma72


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Boundary vertices inject into boundary edges by choosing one outgoing edge
at each vertex. -/
theorem boundaryVertices_card_le_clusterBoundary_card (S : Finset V) :
    (AppendixA3ClusterSplit.boundaryVertices G S).card ≤
      (Section44.clusterBoundary G S).card := by
  classical
  let outsideNeighbor :
      {v : V // v ∈ AppendixA3ClusterSplit.boundaryVertices G S} → V :=
    fun v => Classical.choose
      ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1 v.2).2
  have outsideNeighbor_spec
      (v : {v : V // v ∈ AppendixA3ClusterSplit.boundaryVertices G S}) :
      outsideNeighbor v ∉ S ∧ G.Adj v.1 (outsideNeighbor v) :=
    Classical.choose_spec
      ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1 v.2).2
  let toBoundaryEdge :
      {v : V // v ∈ AppendixA3ClusterSplit.boundaryVertices G S} →
        {e : Sym2 V // e ∈ Section44.clusterBoundary G S} :=
    fun v => ⟨s(v.1, outsideNeighbor v), by
      apply (Section44.mem_edgeBoundary (G := G) S
        ((Finset.univ : Finset V) \ S) s(v.1, outsideNeighbor v)).2
      refine ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using
          (outsideNeighbor_spec v).2,
        v.1, ?_, outsideNeighbor v, ?_, rfl⟩
      · exact
          ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1 v.2).1
      · exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, (outsideNeighbor_spec v).1⟩⟩
  have hinjective : Function.Injective toBoundaryEdge := by
    intro v w hvw
    apply Subtype.ext
    have hedge := congrArg Subtype.val hvw
    change s(v.1, outsideNeighbor v) = s(w.1, outsideNeighbor w) at hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with hedge | hedge
    · exact hedge.1
    · exfalso
      have hvS : v.1 ∈ S :=
        ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1 v.2).1
      exact (outsideNeighbor_spec w).1 (by simpa [hedge.1] using hvS)
  have hcard := Fintype.card_le_of_injective toBoundaryEdge hinjective
  calc
    (AppendixA3ClusterSplit.boundaryVertices G S).card =
        Fintype.card
          {v : V // v ∈ AppendixA3ClusterSplit.boundaryVertices G S} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
          {e : Sym2 V // e ∈ Section44.clusterBoundary G S} := hcard
    _ = (Section44.clusterBoundary G S).card := Fintype.card_coe _

private theorem exists_neighbor_of_mem_scaledWellLinked
    {Gamma : Finset V} {gammaNum gammaDen : ℕ} {v : V}
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) Gamma gammaNum gammaDen)
    (hcard : 2 ≤ Gamma.card) (hv : v ∈ Gamma) :
    ∃ w : V, G.Adj v w := by
  classical
  let X : Finset V := {v}
  let Y : Finset V := (Finset.univ : Finset V) \ X
  have hleft : (X ∩ Gamma).card = 1 := by simp [X, hv]
  have hrightSet : Y ∩ Gamma = Gamma.erase v := by
    ext x
    simp [Y, X, and_left_comm, and_assoc]
  have hrightEq : (Y ∩ Gamma).card = (Gamma.erase v).card :=
    congrArg Finset.card hrightSet
  have hright : 1 ≤ (Y ∩ Gamma).card := by
    rw [hrightEq, Finset.card_erase_of_mem hv]
    omega
  have hcut := hGamma.2.2.2 X Y (by simp [X]) (by simp [Y])
    (by simp [X, Y]) (by simp [X, Y, Finset.disjoint_left])
  have hmin : min (X ∩ Gamma).card (Y ∩ Gamma).card = 1 := by
    rw [hleft, Nat.min_eq_left hright]
  rw [hmin] at hcut
  have hboundaryPos :
      0 < (Section44.edgeBoundary G X Y).card := by
    by_contra hnot
    have hzero := Nat.eq_zero_of_not_pos hnot
    rw [hzero, Nat.mul_zero] at hcut
    exact (Nat.not_le_of_lt hGamma.1) (by simpa using hcut)
  rcases Finset.card_pos.mp hboundaryPos with ⟨e, he⟩
  rcases ((Section44.mem_edgeBoundary (G := G) X Y e).1 he) with
    ⟨heG, x, hx, y, _hy, hxy⟩
  have hxv : x = v := by simpa [X] using hx
  subst x
  refine ⟨y, ?_⟩
  simpa [_root_.SimpleGraph.mem_edgeSet, hxy] using heG

/-- Under the strict Menger threshold, the minimum set `M` contains an edge.
Otherwise every retained `Gamma` terminal injects into an outgoing edge, which
contradicts `Gamma.card <= 2 * gamma` and `3 * gamma < Gamma.card`. -/
theorem exists_internal_edge_of_minimumSet
    {T Gamma M : Finset V} {gamma gammaNum gammaDen : ℕ}
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) Gamma gammaNum gammaDen)
    (hM :
      AppendixA3DeletableEdge.Lemma72SetConditions G T Gamma gamma M)
    (hGammaCard : 2 ≤ Gamma.card)
    (hthreshold : 3 * gammaDen * gamma < gammaNum * Gamma.card) :
    ∃ a ∈ M, ∃ b ∈ M, G.Adj a b := by
  classical
  by_contra hnone
  push Not at hnone
  have hsubset :
      M ∩ Gamma ⊆ AppendixA3ClusterSplit.boundaryVertices G M := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvM, hvGamma⟩
    rcases exists_neighbor_of_mem_scaledWellLinked
        hGamma hGammaCard hvGamma with ⟨w, hvw⟩
    have hwNotM : w ∉ M := by
      intro hwM
      exact hnone v hvM w hwM hvw
    exact (AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).2
      ⟨hvM, w, hwNotM, hvw⟩
  have hretainedLe : (M ∩ Gamma).card ≤ gamma := by
    calc
      (M ∩ Gamma).card ≤
          (AppendixA3ClusterSplit.boundaryVertices G M).card :=
        Finset.card_le_card hsubset
      _ ≤ (Section44.clusterBoundary G M).card :=
        boundaryVertices_card_le_clusterBoundary_card M
      _ ≤ gamma := hM.boundary_card_le
  have hGammaLe : Gamma.card ≤ 2 * gamma :=
    hM.half_gamma.trans (Nat.mul_le_mul_left 2 hretainedLe)
  have hratioLe : gammaNum * Gamma.card ≤ gammaDen * Gamma.card :=
    Nat.mul_le_mul_right Gamma.card hGamma.2.1
  have hscaled : gammaDen * (3 * gamma) < gammaDen * Gamma.card := by
    calc
      gammaDen * (3 * gamma) = 3 * gammaDen * gamma := by ring
      _ < gammaNum * Gamma.card := hthreshold
      _ ≤ gammaDen * Gamma.card := hratioLe
  have hthree : 3 * gamma < Gamma.card :=
    Nat.lt_of_mul_lt_mul_left hscaled
  omega

/-- Chuzhoy Lemma 7.2, specialized to finite simple graphs and written with
natural ratios.  The returned packing has exactly
`floor(gammaNum * |Gamma| / (3 * gammaDen))` paths. -/
theorem lemma_7_2_edgePathPacking
    {T Gamma : Finset V}
    {terminalNum terminalDen gammaNum gammaDen : ℕ}
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) T terminalNum terminalDen)
    (hminimal :
      ∀ ⦃a b : V⦄, G.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (G.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) T terminalNum terminalDen)
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) Gamma gammaNum gammaDen)
    (hdisjoint : Disjoint T Gamma) :
    ∃ P : EdgePathPacking G T Gamma,
      P.card = gammaNum * Gamma.card / (3 * gammaDen) ∧
        P.StaysIn (Finset.univ : Finset V) := by
  classical
  let r := gammaNum * Gamma.card / (3 * gammaDen)
  have hdenPos : 0 < gammaDen := hGamma.1.trans_le hGamma.2.1
  have hhas :
      EdgeMenger.HasEdgeDisjointPathsIn
        G (Finset.univ : Finset V) T Gamma r := by
    by_contra hno
    rcases
        AppendixA3DeletableEdge.exists_minimumLemma72Set_of_not_hasEdgeDisjointPathsIn
          (G := G) hdisjoint hno with
      ⟨gamma, hgamma, M, hM⟩
    have hrPos : 0 < r := by omega
    have hfloor : r * (3 * gammaDen) ≤ gammaNum * Gamma.card := by
      simpa [r] using
        Nat.div_mul_le_self (gammaNum * Gamma.card) (3 * gammaDen)
    have honeLe : 1 ≤ r := Nat.succ_le_iff.mpr hrPos
    have hthreeDen : 3 * gammaDen ≤ gammaNum * Gamma.card := by
      calc
        3 * gammaDen = 1 * (3 * gammaDen) := by simp
        _ ≤ r * (3 * gammaDen) := Nat.mul_le_mul_right _ honeLe
        _ ≤ gammaNum * Gamma.card := hfloor
    have hnumLe : gammaNum * Gamma.card ≤ gammaDen * Gamma.card :=
      Nat.mul_le_mul_right Gamma.card hGamma.2.1
    have hthreeCardScaled : gammaDen * 3 ≤ gammaDen * Gamma.card := by
      calc
        gammaDen * 3 = 3 * gammaDen := by ring
        _ ≤ gammaNum * Gamma.card := hthreeDen
        _ ≤ gammaDen * Gamma.card := hnumLe
    have hGammaCard : 2 ≤ Gamma.card := by
      have hthreeCard : 3 ≤ Gamma.card :=
        Nat.le_of_mul_le_mul_left hthreeCardScaled hdenPos
      omega
    have hthreshold :
        3 * gammaDen * gamma < gammaNum * Gamma.card := by
      calc
        3 * gammaDen * gamma < 3 * gammaDen * r :=
          Nat.mul_lt_mul_of_pos_left hgamma (by positivity)
        _ = r * (3 * gammaDen) := by ring
        _ ≤ gammaNum * Gamma.card := hfloor
    rcases exists_internal_edge_of_minimumSet
        hGamma hM.toLemma72SetConditions hGammaCard hthreshold with
      ⟨a, haM, b, hbM, hab⟩
    have hpreserved :=
      AppendixA3Claim73.delete_internal_edge_preserves_scaledEdgeWellLinkedIn
        hTwell hGamma hM hab haM hbM hthreshold
    exact hminimal hab hpreserved
  simpa [r] using
    EdgeMenger.exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn hhas

end AppendixA3Lemma72
end SimpleGraph

end Lax17Proofs
