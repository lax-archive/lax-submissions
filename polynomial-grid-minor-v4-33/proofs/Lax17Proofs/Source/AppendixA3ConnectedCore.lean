import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma75Outer
import Lax17Proofs.Source.WellLinkedComponent

namespace Lax17Proofs

universe u v w

/-!
# Connected cores with unchanged augmented boundary

The pruning arguments return a vertex set whose augmented boundary is
well-linked.  This file replaces that set by the connected component of its
induced graph containing the augmented boundary.  Component closure shows
that the augmented boundary is unchanged.
-/

namespace SimpleGraph
namespace AppendixA3ConnectedCore


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

private theorem scaledEdgeWellLinkedIn_univ_induced
    {S Gamma : Finset V} {alphaNum alphaDen : ℕ}
    (hwell :
      Section46.ScaledEdgeWellLinkedIn G S Gamma alphaNum alphaDen) :
    Section46.ScaledEdgeWellLinkedIn
      (inducedOnFinset G S) (Finset.univ : Finset V)
      Gamma alphaNum alphaDen := by
  have hscaled := hwell.toScaledEdgeWellLinked_induced
  exact ⟨hscaled.1, hscaled.2.1, by simp, fun X Y _ _ hcover hdisj =>
    hscaled.2.2 X Y hcover hdisj⟩

/-- A nonempty well-linked augmented boundary can be localized to a connected
subcluster without changing that augmented boundary. -/
theorem exists_connectedCore_same_augmentedBoundary
    {S T : Finset V} {alphaNum alphaDen : ℕ}
    (hwell :
      Section46.ScaledEdgeWellLinkedIn G S
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T)
        alphaNum alphaDen)
    (hnonempty :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).Nonempty) :
    ∃ C : Finset V,
      C ⊆ S ∧
      IsCluster G C ∧
      AppendixA3ClusterSplit.augmentedBoundaryVertices G C T =
        AppendixA3ClusterSplit.augmentedBoundaryVertices G S T ∧
      Section46.ScaledEdgeWellLinkedIn G C
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G C T)
        alphaNum alphaDen := by
  classical
  let Gamma :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G S T
  let H := inducedOnFinset G S
  have hHwell :
      Section46.ScaledEdgeWellLinkedIn H (Finset.univ : Finset V)
        Gamma alphaNum alphaDen := by
    simpa [H, Gamma] using scaledEdgeWellLinkedIn_univ_induced hwell
  obtain ⟨C, hCclusterH, hGammaC, hCwellH, hCclosed⟩ :=
    Section46.exists_closed_cluster_scaledEdgeWellLinkedIn_of_univ
      (by simpa [Gamma] using hnonempty) hHwell
  obtain ⟨t, htGamma⟩ := hnonempty
  have htC : t ∈ C := hGammaC (by simpa [Gamma] using htGamma)
  have htS : t ∈ S := hwell.2.2.1 htGamma
  have hCS : C ⊆ S := by
    intro v hvC
    by_cases hvt : v = t
    · simpa [hvt] using htS
    · let Cset : Set V := {x : V | x ∈ C}
      have hreachableInduced :
          (H.induce Cset).Reachable
            (⟨v, by simpa [Cset] using hvC⟩ : Cset)
            (⟨t, by simpa [Cset] using htC⟩ : Cset) :=
        hCclusterH.preconnected _ _
      have hreachableH : H.Reachable v t :=
        hreachableInduced.map
          (_root_.SimpleGraph.Embedding.induce Cset).toHom
      have hvSupport : v ∈ H.support :=
        _root_.SimpleGraph.mem_support_of_reachable hvt hreachableH
      rcases (_root_.SimpleGraph.mem_support H).mp hvSupport with ⟨w, hvw⟩
      exact (inducedOnFinset_adj G S v w).mp hvw |>.2.1
  have hcutEmpty :
      AppendixA3AugmentedBoundary.leftCutBoundaryVertices
        G C (S \ C) = ∅ := by
    ext v
    constructor
    · intro hv
      rcases
          (AppendixA3AugmentedBoundary.mem_leftCutBoundaryVertices
            (G := G)).1 hv with
        ⟨hvC, w, hwSC, hvw⟩
      have hvS : v ∈ S := hCS hvC
      have hwS : w ∈ S := (Finset.mem_sdiff.mp hwSC).1
      have hvwH : H.Adj v w := by
        exact ⟨hvw, hvS, hwS⟩
      have hedge :
          s(v, w) ∈ Section44.edgeBoundary H C (Finset.univ \ C) :=
        (Section44.mem_edgeBoundary (G := H) C
          (Finset.univ \ C) s(v, w)).2
          ⟨by simpa using hvwH, v, hvC, w,
            Finset.mem_sdiff.mpr
              ⟨Finset.mem_univ w, (Finset.mem_sdiff.mp hwSC).2⟩, rfl⟩
      rw [hCclosed] at hedge
      simp at hedge
    · simp
  have hGammaEq :
      AppendixA3ClusterSplit.augmentedBoundaryVertices G C T = Gamma := by
    rw [Lax17Proofs.SimpleGraph.AppendixA3AugmentedBoundary.augmentedBoundaryVertices_eq_retained_union_cut
      (G := G) hCS]
    have hinter : C ∩ Gamma = Gamma :=
      Finset.inter_eq_right.mpr hGammaC
    rw [hinter, hcutEmpty, Finset.union_empty]
  have hCcluster : IsCluster G C :=
    IsCluster.mono_graph hCclusterH inducedOnFinset_le
  have hboundaryEq {X Y : Finset V}
      (hXC : X ⊆ C) (hYC : Y ⊆ C) :
      Section44.edgeBoundary H X Y =
        Section44.edgeBoundary G X Y := by
    ext e
    constructor
    · intro he
      rcases ((Section44.mem_edgeBoundary (G := H) X Y e).1 he) with
        ⟨heH, x, hx, y, hy, rfl⟩
      have hAdjH : H.Adj x y := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using heH
      exact (Section44.mem_edgeBoundary (G := G) X Y s(x, y)).2
        ⟨(by simpa [_root_.SimpleGraph.mem_edgeSet] using hAdjH.1),
          x, hx, y, hy, rfl⟩
    · intro he
      rcases ((Section44.mem_edgeBoundary (G := G) X Y e).1 he) with
        ⟨heG, x, hx, y, hy, rfl⟩
      have hAdjG : G.Adj x y := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using heG
      have hxS := hCS (hXC hx)
      have hyS := hCS (hYC hy)
      have hAdjH : H.Adj x y := ⟨hAdjG, hxS, hyS⟩
      exact (Section44.mem_edgeBoundary (G := H) X Y s(x, y)).2
        ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using hAdjH,
          x, hx, y, hy, rfl⟩
  have hCwell :
      Section46.ScaledEdgeWellLinkedIn G C Gamma alphaNum alphaDen := by
    refine ⟨hCwellH.1, hCwellH.2.1, hGammaC, ?_⟩
    intro X Y hXC hYC hcover hdisj
    have hcut := hCwellH.2.2.2 X Y hXC hYC hcover hdisj
    rwa [hboundaryEq hXC hYC] at hcut
  refine ⟨C, hCS, hCcluster, by simpa [Gamma] using hGammaEq, ?_⟩
  simpa [hGammaEq] using hCwell

/-- Connected-cluster form of the completed degree-three Lemma 7.5. -/
theorem exists_lemma75_cluster
    {T : Finset V} {rho kappa terminalNum terminalDen : ℕ}
    (hkappaPos : 0 < kappa)
    (hkappa : kappa = 256 * rho)
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn G (Finset.univ : Finset V)
        T terminalNum terminalDen)
    (hminimal :
      ∀ ⦃a b : V⦄, G.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (G.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) T terminalNum terminalDen)
    (hdegree : MaxDegreeAtMost G 3)
    (hInitial :
      ∃ S0 : Finset V,
        AppendixA3Lemma75.IsMinimumInitialSet G T rho S0) :
    ∃ Y : Finset V,
      IsCluster G Y ∧
      rho ≤ 4 *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ∧
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ≤ rho ∧
      Section46.ScaledEdgeWellLinkedIn G Y
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T)
        1 AppendixA3Lemma75.finalAlphaDen := by
  obtain ⟨S, hlarge, hsmall, hwell⟩ :=
    AppendixA3Lemma75.exists_lemma75_set
      hkappaPos hkappa hTcard hTwell hminimal hdegree hInitial
  have hrhoPos : 0 < rho := by
    rw [hkappa] at hkappaPos
    omega
  have hnonempty :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨Y, _hYS, hYcluster, hGammaEq, hYwell⟩ :=
    exists_connectedCore_same_augmentedBoundary hwell hnonempty
  refine ⟨Y, hYcluster, ?_, ?_, hYwell⟩
  · simpa [hGammaEq] using hlarge
  · simpa [hGammaEq] using hsmall

end
end AppendixA3ConnectedCore
end SimpleGraph

end Lax17Proofs
