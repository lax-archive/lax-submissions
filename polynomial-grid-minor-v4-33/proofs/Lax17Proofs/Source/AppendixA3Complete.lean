import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma710
import Lax17Proofs.Source.HairyPathOfSetsTheorem

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Theorem 6.3, degree-three specialization

This module assembles the completed Section 7 ingredients into the local
cluster-splitting input used by Chuzhoy--Tan Appendix A.4.  The fixed
constants absorb the two endpoint-boosting losses and the explicit
Observation 7.11 / Lemma 7.10 boundary-routing threshold.
-/

namespace SimpleGraph
namespace AppendixA3Complete


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

/-- Connector width before the two endpoint boosts. -/
def connectorScale : ℕ :=
  653400 * AppendixA3Lemma75.finalAlphaDen

/-- Boundary threshold used by Observation 7.11 and Lemma 7.10. -/
def rhoScale : ℕ :=
  72 * (48600 * AppendixA3Lemma75.finalAlphaDen + 2700) *
    connectorScale

/-- The universal degree-three split constant. -/
def cSplit : ℕ := 256 * rhoScale

theorem cSplit_pos : 0 < cSplit := by
  simp [cSplit, rhoScale, connectorScale,
    AppendixA3Lemma75.finalAlphaDen]

private theorem connector_first_boost_floor (w : ℕ) :
    (3 * (connectorScale * w)) / (10 * 3 * 33) =
      1980 * AppendixA3Lemma75.finalAlphaDen * w := by
  have heq :
      3 * (connectorScale * w) =
        (1980 * AppendixA3Lemma75.finalAlphaDen * w) *
          (10 * 3 * 33) := by
    simp [connectorScale]
    ring
  rw [heq]
  exact Nat.mul_div_left _ (by norm_num)

private theorem connector_second_boost_floor (w : ℕ) :
    (3 *
        (1980 * AppendixA3Lemma75.finalAlphaDen * w)) /
        (10 * 3 * AppendixA3Lemma75.finalAlphaDen) =
      198 * w := by
  have hden :
      0 < 10 * 3 * AppendixA3Lemma75.finalAlphaDen := by
    simp [AppendixA3Lemma75.finalAlphaDen]
  have heq :
      3 * (1980 * AppendixA3Lemma75.finalAlphaDen * w) =
        (198 * w) *
          (10 * 3 * AppendixA3Lemma75.finalAlphaDen) := by
    ring
  rw [heq]
  exact Nat.mul_div_left _ hden

private theorem nail_boost_floor (w : ℕ) :
    (3 * (65340 * w)) / (10 * 3 * 33) = 198 * w := by
  have heq :
      3 * (65340 * w) = (198 * w) * (10 * 3 * 33) := by
    ring
  rw [heq]
  exact Nat.mul_div_left _ (by norm_num)

/-- A connected set in a subgraph induced on `C` lies in `C` as soon as it
contains one vertex of `C`. -/
private theorem cluster_subset_of_le_induced
    {H : _root_.SimpleGraph V} {C K : Finset V} {t : V}
    (hHC : H ≤ inducedOnFinset G C)
    (hK : IsCluster H K) (htK : t ∈ K) (htC : t ∈ C) :
    K ⊆ C := by
  intro v hvK
  by_cases hvt : v = t
  · simpa [hvt] using htC
  · let Kset : Set V := {x : V | x ∈ K}
    have hreachableInduced :
        (H.induce Kset).Reachable
          (⟨v, by simpa [Kset] using hvK⟩ : Kset)
          (⟨t, by simpa [Kset] using htK⟩ : Kset) :=
      hK.preconnected _ _
    have hreachableH : H.Reachable v t :=
      hreachableInduced.map
        (_root_.SimpleGraph.Embedding.induce Kset).toHom
    have hvSupport : v ∈ H.support :=
      _root_.SimpleGraph.mem_support_of_reachable hvt hreachableH
    rcases (_root_.SimpleGraph.mem_support H).mp hvSupport with ⟨z, hvz⟩
    exact (inducedOnFinset_adj G C v z).mp (hHC hvz) |>.2.1

/-- The local cluster-splitting theorem proved by the Section 7 assembly. -/
theorem exists_clusterSplitData
    (G : _root_.SimpleGraph V) {C A B : Finset V} {w : ℕ}
    (hw : 0 < w)
    (hdegree : MaxDegreeAtMost G 3)
    (hCcluster : IsCluster G C)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hAcard : A.card = cSplit * w)
    (hBcard : B.card = cSplit * w)
    (hAB : Disjoint A B)
    (hAwl : NodeWellLinkedIn G C A)
    (hBwl : NodeWellLinkedIn G C B)
    (hABlinked : NodeLinkedIn G C A B) :
    Nonempty
      (HairyPathOfSetsTheorem.AppendixA3ClusterSplitData
        G C A B w) := by
  classical
  let T := A ∪ B
  let kappa := cSplit * w
  let rho := rhoScale * w
  let z := connectorScale * w
  have hkappa : kappa = 256 * rho := by
    simp [kappa, rho, cSplit]
    ring
  have hrho :
      rho =
        72 *
          (48600 * AppendixA3Lemma75.finalAlphaDen + 2700) *
            z := by
    dsimp [rho, z]
    rw [rhoScale]
    ring
  have hkappaPos : 0 < kappa := by
    simp [kappa, cSplit_pos, hw]
  have hrhoPos : 0 < rho := by
    rw [hkappa] at hkappaPos
    omega
  have hTcard : T.card = 2 * kappa := by
    simp only [T, kappa]
    rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard]
    omega
  have hTwellLocal :
      Section46.ScaledEdgeWellLinkedIn G C T 1 3 := by
    simpa [T] using
      AppendixA3ClusterSplit.observation_7_1_union_scaledEdgeWellLinkedIn
        hAwl hBwl hABlinked
  let Gind := inducedOnFinset G C
  have hTwellInd :
      Section46.ScaledEdgeWellLinkedIn Gind
        (Finset.univ : Finset V) T 1 3 := by
    have hscaled := hTwellLocal.toScaledEdgeWellLinked_induced
    exact ⟨hscaled.1, hscaled.2.1, by simp,
      fun X Y _ _ hcover hdisj =>
        hscaled.2.2 X Y hcover hdisj⟩
  let M :=
    Classical.choice
      (AppendixA3ClusterSplit.exists_edgeMinimalScaledWellLinkedSubgraph
        (G := Gind) hTwellInd)
  let H := M.H
  have hHGind : H ≤ Gind := M.le_original
  have hHG : H ≤ G := hHGind.trans inducedOnFinset_le
  have hdegreeH : MaxDegreeAtMost H 3 :=
    maxDegreeAtMost_of_le hdegree hHG
  have hTwell :
      Section46.ScaledEdgeWellLinkedIn H
        (Finset.univ : Finset V) T 1 3 :=
    M.wellLinked
  have hminimal :
      ∀ ⦃a b : V⦄, H.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (H.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) T 1 3 :=
    M.deleteEdge_not_wellLinked
  have hInitial :
      ∃ S0 : Finset V,
        AppendixA3Lemma75.IsMinimumInitialSet H T rho S0 := by
    apply AppendixA3Lemma75.exists_minimumInitialSet_of_univ
    · rw [hTcard, hkappa]
      omega
    · exact AppendixA3Lemma75.scaledEdgeWellLinkedIn_weaken_denominator
        hTwell (by norm_num)
  obtain ⟨Y, hYcluster, hYlarge, hYsmall, hYwell⟩ :=
    AppendixA3ConnectedCore.exists_lemma75_cluster
      hkappaPos hkappa hTcard hTwell hminimal hdegreeH hInitial
  obtain ⟨X, hXY, hXcluster, hXmass, hXwell⟩ :=
    AppendixA3Lemma78.exists_lemma78_cluster
      hrhoPos hkappa hTcard hTwell hdegreeH hYsmall
  have hGammaYNonempty :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices H Y T).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨ty, htyGamma⟩ := hGammaYNonempty
  have htyY : ty ∈ Y := hYwell.2.2.1 htyGamma
  have hTC : T ⊆ C := Finset.union_subset hAC hBC
  have htyC' : ty ∈ C := by
    rcases Finset.mem_union.mp htyGamma with htyBoundary | htyTerminal
    · rcases
          ((AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).1
            htyBoundary).2 with
        ⟨q, _hqY, htyq⟩
      exact (inducedOnFinset_adj G C ty q).mp (hHGind htyq) |>.2.1
    · exact hTC (Finset.mem_inter.mp htyTerminal).1
  have hYC : Y ⊆ C :=
    cluster_subset_of_le_induced hHGind hYcluster htyY htyC'
  have hGammaXNonempty :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices H X T).Nonempty := by
    have hXTpos : 0 < (X ∩ T).card := by omega
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le hXTpos
      (Finset.card_le_card (by
        intro v hv
        exact Finset.mem_union_right _
          (Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hv).2,
              (Finset.mem_inter.mp hv).1⟩)))
  obtain ⟨tx, htxGamma⟩ := hGammaXNonempty
  have htxX : tx ∈ X := hXwell.2.2.1 htxGamma
  have htxC : tx ∈ C := by
    rcases Finset.mem_union.mp htxGamma with htxBoundary | htxTerminal
    · rcases
          ((AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).1
            htxBoundary).2 with
        ⟨q, _hqX, htxq⟩
      exact (inducedOnFinset_adj G C tx q).mp (hHGind htxq) |>.2.1
    · exact hTC (Finset.mem_inter.mp htxTerminal).1
  have hXC : X ⊆ C :=
    cluster_subset_of_le_induced hHGind hXcluster htxX htxC
  obtain ⟨x0, y0, P0, hx0Boundary, hy0Boundary,
      hx0card, hy0card, hP0card, hP0stay, hP0X, hP0Y⟩ :=
    AppendixA3Lemma710.exists_lemma710_connector_boundary
      (G := G) (H := H) (C := C) (T := T)
      (kappa := kappa) (rho := rho) (width := z)
      (by simp [z, connectorScale,
        AppendixA3Lemma75.finalAlphaDen, hw])
      hHGind hdegreeH hXC hYC hXY hkappa hrho hTcard hTwell
      hminimal hYlarge hYwell hXmass
  have hx0Aug :
      x0 ⊆
        AppendixA3ClusterSplit.augmentedBoundaryVertices H X T :=
    hx0Boundary.trans Finset.subset_union_left
  have hx0Well :
      Section46.ScaledEdgeWellLinkedIn H X x0 1 33 :=
    hXwell.mono_terminals hx0Aug
  obtain ⟨xRes, hxRes0, hxResLarge, hxResNode⟩ :=
    ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := H) (C := X) (T := x0)
      (alphaNum := 1) (alphaDen := 33) (Δ := 3)
      (κ := z)
      hXcluster hdegreeH (by decide) (by decide) (by decide)
      hx0card hx0Well
  rw [connector_first_boost_floor] at hxResLarge
  obtain ⟨xMid, hxMidRes, hxMidCard⟩ :=
    Finset.exists_subset_card_eq hxResLarge
  have hxMid0 : xMid ⊆ x0 := hxMidRes.trans hxRes0
  have hxMidNode : NodeWellLinkedIn H X xMid :=
    hxResNode.mono_terminals hxMidRes
  let P1 := P0.restrictSourceSet xMid hxMid0
  let yMid :=
    P0.targetSet (P0.sourceIndexSetOfSubset xMid)
  have hP1card :
      P1.card =
        1980 * AppendixA3Lemma75.finalAlphaDen * w := by
    simpa [P1, hxMidCard]
  have hyMidCard :
      yMid.card =
        1980 * AppendixA3Lemma75.finalAlphaDen * w := by
    calc
      yMid.card =
          (P0.sourceIndexSetOfSubset xMid).card := by
        simp [yMid]
      _ = xMid.card :=
        P0.sourceIndexSetOfSubset_card hxMid0
      _ = 1980 * AppendixA3Lemma75.finalAlphaDen * w :=
        hxMidCard
  have hyMid0 : yMid ⊆ y0 := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact P0.target_mem i
  have hyMidAug :
      yMid ⊆
        AppendixA3ClusterSplit.augmentedBoundaryVertices H Y T :=
    hyMid0.trans hy0Boundary |>.trans Finset.subset_union_left
  have hyMidWell :
      Section46.ScaledEdgeWellLinkedIn H Y yMid
        1 AppendixA3Lemma75.finalAlphaDen :=
    hYwell.mono_terminals hyMidAug
  obtain ⟨yRes, hyResMid, hyResLarge, hyResNode⟩ :=
    ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := H) (C := Y) (T := yMid)
      (alphaNum := 1)
      (alphaDen := AppendixA3Lemma75.finalAlphaDen)
      (Δ := 3)
      (κ := 1980 * AppendixA3Lemma75.finalAlphaDen * w)
      hYcluster hdegreeH (by decide) (by decide)
      (by
        simp [AppendixA3Lemma75.finalAlphaDen])
      hyMidCard hyMidWell
  rw [connector_second_boost_floor] at hyResLarge
  obtain ⟨yBig, hyBigRes, hyBigCard⟩ :=
    Finset.exists_subset_card_eq hyResLarge
  have hyBigMid : yBig ⊆ yMid := hyBigRes.trans hyResMid
  have hyBigNode : NodeWellLinkedIn H Y yBig :=
    hyResNode.mono_terminals hyBigRes
  let P2 := P1.restrictTargetSet yBig hyBigMid
  let xBig :=
    P1.sourceSet (P1.targetIndexSetOfSubset yBig)
  have hxBigMid : xBig ⊆ xMid := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact P1.source_mem i
  have hxBigCard : xBig.card = 198 * w := by
    calc
      xBig.card =
          (P1.targetIndexSetOfSubset yBig).card := by
        simp [xBig]
      _ = yBig.card :=
        P1.targetIndexSetOfSubset_card hyBigMid
      _ = 198 * w := hyBigCard
  have hxBigNode : NodeWellLinkedIn H X xBig :=
    hxMidNode.mono_terminals hxBigMid
  have hxBigX : xBig ⊆ X :=
    hxBigMid.trans hxMid0 |>.trans hx0Boundary |>.trans
      (by
        intro v hv
        exact
          ((AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).1 hv).1)
  have hyBigY : yBig ⊆ Y :=
    hyBigMid.trans hyMid0 |>.trans hy0Boundary |>.trans
      (by
        intro v hv
        exact
          ((AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).1 hv).1)
  have hP2stay : P2.toPathPacking.StaysIn C := by
    apply PerfectPathPacking.restrictTargetSet_staysIn
    apply PerfectPathPacking.restrictSourceSet_staysIn
    exact hP0stay
  have hP2X :
      P2.toPathPacking.InternallyDisjointFromSet X := by
    apply PerfectPathPacking.restrictTargetSet_internallyDisjointFromSet
    apply PerfectPathPacking.restrictSourceSet_internallyDisjointFromSet
    exact hP0X
  have hP2Y :
      P2.toPathPacking.InternallyDisjointFromSet Y := by
    apply PerfectPathPacking.restrictTargetSet_internallyDisjointFromSet
    apply PerfectPathPacking.restrictSourceSet_internallyDisjointFromSet
    exact hP0Y
  have hsideMass :
      kappa ≤ 2 * (X ∩ A).card ∧
        kappa ≤ 2 * (X ∩ B).card := by
    apply AppendixA3Lemma710.original_side_mass
      (kappa := kappa)
    · simpa [kappa] using hAcard
    · simpa [kappa] using hBcard
    · exact hAB
    · simpa [T] using hXmass
  have hfreshScale :
      2 * (65340 * w + 198 * w) ≤ kappa := by
    dsimp [kappa]
    rw [cSplit, rhoScale, connectorScale]
    have hD : 0 < AppendixA3Lemma75.finalAlphaDen := by
      simp [AppendixA3Lemma75.finalAlphaDen]
    nlinarith
  have hleftRawLarge :
      65340 * w ≤ ((X ∩ A) \ xBig).card := by
    have hinter :
        ((X ∩ A) ∩ xBig).card ≤ xBig.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hparts :=
      Finset.card_sdiff_add_card_inter (X ∩ A) xBig
    rw [hxBigCard] at hinter
    omega
  have hrightRawLarge :
      65340 * w ≤ ((X ∩ B) \ xBig).card := by
    have hinter :
        ((X ∩ B) ∩ xBig).card ≤ xBig.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hparts :=
      Finset.card_sdiff_add_card_inter (X ∩ B) xBig
    rw [hxBigCard] at hinter
    omega
  obtain ⟨leftRaw, hleftRawSub, hleftRawCard⟩ :=
    Finset.exists_subset_card_eq hleftRawLarge
  obtain ⟨rightRaw, hrightRawSub, hrightRawCard⟩ :=
    Finset.exists_subset_card_eq hrightRawLarge
  have hleftRawX : leftRaw ⊆ X :=
    hleftRawSub.trans Finset.sdiff_subset |>.trans
      Finset.inter_subset_left
  have hrightRawX : rightRaw ⊆ X :=
    hrightRawSub.trans Finset.sdiff_subset |>.trans
      Finset.inter_subset_left
  have hleftRawA : leftRaw ⊆ A :=
    hleftRawSub.trans Finset.sdiff_subset |>.trans
      Finset.inter_subset_right
  have hrightRawB : rightRaw ⊆ B :=
    hrightRawSub.trans Finset.sdiff_subset |>.trans
      Finset.inter_subset_right
  have hleftRawXBig : Disjoint leftRaw xBig := by
    rw [Finset.disjoint_left]
    intro v hvleft hvx
    exact
      (Finset.mem_sdiff.mp (hleftRawSub hvleft)).2 hvx
  have hrightRawXBig : Disjoint rightRaw xBig := by
    rw [Finset.disjoint_left]
    intro v hvright hvx
    exact
      (Finset.mem_sdiff.mp (hrightRawSub hvright)).2 hvx
  have hleftRightRaw : Disjoint leftRaw rightRaw :=
    hAB.mono hleftRawA hrightRawB
  have hleftRawAug :
      leftRaw ⊆
        AppendixA3ClusterSplit.augmentedBoundaryVertices H X T := by
    intro v hv
    exact Finset.mem_union_right _
      (Finset.mem_inter.mpr
        ⟨Finset.mem_union_left B (hleftRawA hv), hleftRawX hv⟩)
  have hrightRawAug :
      rightRaw ⊆
        AppendixA3ClusterSplit.augmentedBoundaryVertices H X T := by
    intro v hv
    exact Finset.mem_union_right _
      (Finset.mem_inter.mpr
        ⟨Finset.mem_union_right A (hrightRawB hv), hrightRawX hv⟩)
  have hleftRawWell :
      Section46.ScaledEdgeWellLinkedIn H X leftRaw 1 33 :=
    hXwell.mono_terminals hleftRawAug
  have hrightRawWell :
      Section46.ScaledEdgeWellLinkedIn H X rightRaw 1 33 :=
    hXwell.mono_terminals hrightRawAug
  obtain ⟨leftRes, hleftResRaw, hleftResLarge, hleftResNode⟩ :=
    ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := H) (C := X) (T := leftRaw)
      (alphaNum := 1) (alphaDen := 33) (Δ := 3)
      (κ := 65340 * w)
      hXcluster hdegreeH (by decide) (by decide) (by decide)
      hleftRawCard hleftRawWell
  obtain ⟨rightRes, hrightResRaw, hrightResLarge, hrightResNode⟩ :=
    ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := H) (C := X) (T := rightRaw)
      (alphaNum := 1) (alphaDen := 33) (Δ := 3)
      (κ := 65340 * w)
      hXcluster hdegreeH (by decide) (by decide) (by decide)
      hrightRawCard hrightRawWell
  rw [nail_boost_floor] at hleftResLarge hrightResLarge
  obtain ⟨leftBig, hleftBigRes, hleftBigCard⟩ :=
    Finset.exists_subset_card_eq hleftResLarge
  obtain ⟨rightBig, hrightBigRes, hrightBigCard⟩ :=
    Finset.exists_subset_card_eq hrightResLarge
  have hleftBigRaw : leftBig ⊆ leftRaw :=
    hleftBigRes.trans hleftResRaw
  have hrightBigRaw : rightBig ⊆ rightRaw :=
    hrightBigRes.trans hrightResRaw
  have hleftBigNode : NodeWellLinkedIn H X leftBig :=
    hleftResNode.mono_terminals hleftBigRes
  have hrightBigNode : NodeWellLinkedIn H X rightBig :=
    hrightResNode.mono_terminals hrightBigRes
  have hleftRightBig : Disjoint leftBig rightBig :=
    hleftRightRaw.mono hleftBigRaw hrightBigRaw
  have hleftXBig : Disjoint leftBig xBig :=
    hleftRawXBig.mono hleftBigRaw Finset.Subset.rfl
  have hrightXBig : Disjoint rightBig xBig :=
    hrightRawXBig.mono hrightBigRaw Finset.Subset.rfl
  have hwBig : w ≤ 198 * w := by omega
  obtain ⟨left, hleftBig, hleftCard⟩ :=
    Finset.exists_subset_card_eq (s := leftBig)
      (by simpa [hleftBigCard] using hwBig)
  obtain ⟨right, hrightBig, hrightCard⟩ :=
    Finset.exists_subset_card_eq (s := rightBig)
      (by simpa [hrightBigCard] using hwBig)
  obtain ⟨x, hxBig, hxCard⟩ :=
    Finset.exists_subset_card_eq (s := xBig)
      (by simpa [hxBigCard] using hwBig)
  have hleftNode : NodeWellLinkedIn H X left :=
    hleftBigNode.mono_terminals hleftBig
  have hrightNode : NodeWellLinkedIn H X right :=
    hrightBigNode.mono_terminals hrightBig
  have hxNode : NodeWellLinkedIn H X x :=
    hxBigNode.mono_terminals hxBig
  have hleftRight : Disjoint left right :=
    hleftRightBig.mono hleftBig hrightBig
  have hleftX : Disjoint left x :=
    hleftXBig.mono hleftBig hxBig
  have hrightX : Disjoint right x :=
    hrightXBig.mono hrightBig hxBig
  have hleftRightWell :
      Section46.ScaledEdgeWellLinkedIn H X
        (leftBig ∪ rightBig) 1 33 :=
    hXwell.mono_terminals (by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hleftRawAug (hleftBigRaw hv)
      · exact hrightRawAug (hrightBigRaw hv))
  have hleftXWell :
      Section46.ScaledEdgeWellLinkedIn H X
        (leftBig ∪ xBig) 1 33 :=
    hXwell.mono_terminals (by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hleftRawAug (hleftBigRaw hv)
      · exact hx0Aug
          (hxMid0 (hxBigMid hv)))
  have hleftRightLinked : NodeLinkedIn H X left right := by
    apply Section46.theorem421_linkedSubsets_scaledEdgeWellLinked_minCard
      (G := H) (C := X)
      (T1 := leftBig) (T2 := rightBig)
      (T1' := left) (T2' := right)
      (Delta := 3) (kappa := 198 * w)
      (alphaNum := 1) (alphaDen := 33)
      hdegreeH (by decide) (by decide) hleftRightBig
      (by rw [hleftBigCard]) (by rw [hrightBigCard])
      hleftRightWell hleftBigNode hrightBigNode
      hleftBig hrightBig
    rw [hleftCard]
    omega
  have hleftXLinked : NodeLinkedIn H X left x := by
    apply Section46.theorem421_linkedSubsets_scaledEdgeWellLinked_minCard
      (G := H) (C := X)
      (T1 := leftBig) (T2 := xBig)
      (T1' := left) (T2' := x)
      (Delta := 3) (kappa := 198 * w)
      (alphaNum := 1) (alphaDen := 33)
      hdegreeH (by decide) (by decide) hleftXBig
      (by rw [hleftBigCard]) (by rw [hxBigCard])
      hleftXWell hleftBigNode hxBigNode hleftBig hxBig
    rw [hleftCard]
    omega
  let P := P2.restrictSourceSet x hxBig
  let y := P2.targetSet (P2.sourceIndexSetOfSubset x)
  have hyBig : y ⊆ yBig := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact P2.target_mem i
  have hyCard : y.card = w := by
    calc
      y.card = (P2.sourceIndexSetOfSubset x).card := by
        simp [y]
      _ = x.card := P2.sourceIndexSetOfSubset_card hxBig
      _ = w := hxCard
  have hyNode : NodeWellLinkedIn H Y y :=
    hyBigNode.mono_terminals hyBig
  have hPcard : P.card = w := by
    simpa [P, hxCard]
  have hPstay : P.toPathPacking.StaysIn C := by
    exact PerfectPathPacking.restrictSourceSet_staysIn
      P2 x hxBig hP2stay
  have hPX :
      P.toPathPacking.InternallyDisjointFromSet X :=
    PerfectPathPacking.restrictSourceSet_internallyDisjointFromSet
      P2 x hxBig hP2X
  have hPY :
      P.toPathPacking.InternallyDisjointFromSet Y :=
    PerfectPathPacking.restrictSourceSet_internallyDisjointFromSet
      P2 x hxBig hP2Y
  have hleftA : left ⊆ A :=
    hleftBig.trans hleftBigRaw |>.trans hleftRawA
  have hrightB : right ⊆ B :=
    hrightBig.trans hrightBigRaw |>.trans hrightRawB
  have hleftXset : left ⊆ X :=
    hleftBig.trans hleftBigRaw |>.trans hleftRawX
  have hrightXset : right ⊆ X :=
    hrightBig.trans hrightBigRaw |>.trans hrightRawX
  have hxXset : x ⊆ X := hxBig.trans hxBigX
  have hyYset : y ⊆ Y := hyBig.trans hyBigY
  refine ⟨{
    baseCluster := X
    hairCluster := Y
    left := left
    right := right
    x := x
    y := y
    base_subset_cluster := hXC
    hair_subset_cluster := hYC
    base_connected := IsCluster.mono_graph hXcluster hHG
    hair_connected := IsCluster.mono_graph hYcluster hHG
    hair_disjoint_base := hXY.symm
    left_subset_base := hleftXset
    right_subset_base := hrightXset
    x_subset_base := hxXset
    y_subset_hair := hyYset
    left_subset_old_left := hleftA
    right_subset_old_right := hrightB
    left_card := hleftCard
    right_card := hrightCard
    x_card := hxCard
    y_card := hyCard
    left_right_disjoint := hleftRight
    x_disjoint_nails := by
      rw [Finset.disjoint_left]
      intro v hvx hvnails
      rcases Finset.mem_union.mp hvnails with hvleft | hvright
      · exact Finset.disjoint_left.mp hleftX hvleft hvx
      · exact Finset.disjoint_left.mp hrightX hvright hvx
    left_nodeWellLinked :=
      NodeWellLinkedIn.mono_graph hleftNode hHG
    right_nodeWellLinked :=
      NodeWellLinkedIn.mono_graph hrightNode hHG
    left_right_nodeLinked :=
      NodeLinkedIn.mono_graph hleftRightLinked hHG
    left_x_nodeLinked :=
      NodeLinkedIn.mono_graph hleftXLinked hHG
    y_nodeWellLinked :=
      NodeWellLinkedIn.mono_graph hyNode hHG
    hairConnector := P
    hairConnector_card := hPcard
    hairConnector_staysIn_cluster := hPstay
    hairConnector_internally_disjoint_base := hPX
    hairConnector_internally_disjoint_hair := hPY }⟩

/-- Axiom-free producer for the Appendix A.3 input used downstream. -/
theorem appendixA3ClusterSplitInput :
    HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit := by
  refine ⟨cSplit_pos, ?_⟩
  intro V _ _ G C A B w hw hdegree hC hAC hBC
    hAcard hBcard hAB hAwl hBwl hABlinked
  exact exists_clusterSplitData G hw hdegree hC hAC hBC
    hAcard hBcard hAB hAwl hBwl hABlinked

/-- The completed local Appendix A.3 theorem supplies the global split input
used by Appendix A.4. -/
theorem appendixA4SplitInput :
    HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit :=
  HairyPathOfSetsTheorem.appendixA4SplitInput_of_appendixA3ClusterSplitInput
    appendixA3ClusterSplitInput

end
end AppendixA3Complete
end SimpleGraph

end Lax17Proofs
