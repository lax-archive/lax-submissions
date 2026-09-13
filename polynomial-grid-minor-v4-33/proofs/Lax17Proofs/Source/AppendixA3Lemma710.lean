import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Observation711
import Lax17Proofs.Source.AppendixA3EndpointMatching
import Lax17Proofs.Source.AppendixA3Corollary74Overlap
import Lax17Proofs.Source.FlowRouting
import Lax17Proofs.Source.ScaledWellLinkedPathFlow
import Lax17Proofs.Source.Theorem214Nonconstructive
import Lax17Proofs.Source.ScaledLinkedSubsets

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Section 7, Lemma 7.10

This module constructs the internally clean connector between the two
clusters.  It uses the two cases of Observation 7.11: terminal boundary
vertices are linked directly through one of the original nail sets; otherwise
Lemma 7.2 supplies many edge-disjoint paths from nonterminal boundary vertices
to the original terminals.  Endpoint thinning, one node-disjoint terminal
linkage, and the bounded-congestion flow lemma then produce node-disjoint
cluster-to-cluster paths.
-/

namespace SimpleGraph
namespace AppendixA3Lemma710


open Finset
open ChekuriChuzhoySection5Phase1Flow

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

/-- Turn a lower bound on disjoint paths in an induced cluster into an exact
perfect ambient packing.  Cleaning at the two terminal regions gives the
internal-disjointness fields needed by Appendix A.3. -/
theorem exists_cleanPerfect_of_hasDisjointSTPaths_induced
    {C X Y : Finset V} {width : ℕ}
    (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hhas :
      HasDisjointSTPaths (inducedOnFinset G C) X Y width) :
    ∃ (x y : Finset V) (P : PerfectPathPacking G x y),
      x ⊆ X ∧ y ⊆ Y ∧
      x.card = width ∧ y.card = width ∧
      P.card = width ∧
      P.toPathPacking.StaysIn C ∧
      P.toPathPacking.InternallyDisjointFromSet X ∧
      P.toPathPacking.InternallyDisjointFromSet Y := by
  classical
  rcases hhas with ⟨Q, hQcard⟩
  obtain ⟨I, hIcard, hrestrictCard⟩ :=
    PathPacking.exists_indexSet_card_eq Q hQcard
  let R := Q.restrictIndexSet I
  let Rclean := R.cleanToTerminals
  let Pind := Rclean.toPerfectUsedTerminals
  let x := Rclean.sourceSet
  let y := Rclean.targetSet
  let P := Pind.mapLe (inducedOnFinset_le (G := G) (C := C))
  have hRcard : R.card = width := by
    simpa [R] using hrestrictCard
  have hRcleanCard : Rclean.card = width := by
    simpa [Rclean] using hRcard
  have hxcard : x.card = width := by
    simpa [x] using hRcleanCard
  have hycard : y.card = width := by
    simpa [y] using hRcleanCard
  have hterminalClean : Rclean.TerminalClean :=
    PathPacking.cleanToTerminals_terminalClean R
  have hPindX :
      Pind.toPathPacking.InternallyDisjointFromSet X := by
    apply PathPacking.toPerfectUsedTerminals_internallyDisjointFromSet
    intro i v hv hvX
    exact hterminalClean i hv
      (Finset.mem_union_left Y hvX)
  have hPindY :
      Pind.toPathPacking.InternallyDisjointFromSet Y := by
    apply PathPacking.toPerfectUsedTerminals_internallyDisjointFromSet
    intro i v hv hvY
    exact hterminalClean i hv
      (Finset.mem_union_right X hvY)
  have hPstay : P.toPathPacking.StaysIn C := by
    simpa [P, Pind] using
      Section46.InducedOnFinset.pathPacking_mapLe_staysIn
        (G := G) (C := C) (A := x) (B := y)
        Pind.toPathPacking
        (Rclean.sourceSet_subset_left.trans hXC)
        (Rclean.targetSet_subset_right.trans hYC)
  refine ⟨x, y, P,
    Rclean.sourceSet_subset_left,
    Rclean.targetSet_subset_right,
    hxcard, hycard, ?_, hPstay, ?_, ?_⟩
  · simpa [P, Pind] using hRcleanCard
  · intro i v hv hvX
    have hv' : v ∈ (Pind.path i).vertexSet := by
      change v ∈ ((Pind.path i).mapLe
        (inducedOnFinset_le (G := G) (C := C))).vertexSet at hv
      simpa using hv
    exact hPindX i hv' hvX
  · intro i v hv hvY
    have hv' : v ∈ (Pind.path i).vertexSet := by
      change v ∈ ((Pind.path i).mapLe
        (inducedOnFinset_le (G := G) (C := C))).vertexSet at hv
      simpa using hv
    exact hPindY i hv' hvY

/-- Exact cleaned connector data when the disjoint paths are constructed in a
subgraph of the induced cluster.  The target of every cleaned path is an
actual boundary vertex of `Y` in that subgraph. -/
theorem exists_cleanPerfect_boundary_of_hasDisjointSTPaths
    {H : _root_.SimpleGraph V} {C X Y : Finset V} {width : ℕ}
    (hHC : H ≤ inducedOnFinset G C)
    (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hXY : Disjoint X Y)
    (hhas : HasDisjointSTPaths H X Y width) :
    ∃ (x y : Finset V) (P : PerfectPathPacking G x y),
      x ⊆ AppendixA3ClusterSplit.boundaryVertices H X ∧
      y ⊆ AppendixA3ClusterSplit.boundaryVertices H Y ∧
      x.card = width ∧ y.card = width ∧
      P.card = width ∧
      P.toPathPacking.StaysIn C ∧
      P.toPathPacking.InternallyDisjointFromSet X ∧
      P.toPathPacking.InternallyDisjointFromSet Y := by
  classical
  rcases hhas with ⟨Q, hQcard⟩
  obtain ⟨I, _hIcard, hrestrictCard⟩ :=
    PathPacking.exists_indexSet_card_eq Q hQcard
  let R := Q.restrictIndexSet I
  let Rclean := R.cleanToTerminals
  let P_H := Rclean.toPerfectUsedTerminals
  let x := Rclean.sourceSet
  let y := Rclean.targetSet
  have hRcard : R.card = width := by
    simpa [R] using hrestrictCard
  have hRcleanCard : Rclean.card = width := by
    simpa [Rclean] using hRcard
  have hxcard : x.card = width := by
    simpa [x] using hRcleanCard
  have hycard : y.card = width := by
    simpa [y] using hRcleanCard
  have hterminalClean : Rclean.TerminalClean :=
    PathPacking.cleanToTerminals_terminalClean R
  have hcleanY :
      Rclean.orient.InternallyDisjointFromSet Y := by
    apply PathPacking.orient_internallyDisjointFromSet
    intro i v hv hvY
    exact hterminalClean i hv (Finset.mem_union_right X hvY)
  have hcleanX :
      Rclean.orient.InternallyDisjointFromSet X := by
    apply PathPacking.orient_internallyDisjointFromSet
    intro i v hv hvX
    exact hterminalClean i hv (Finset.mem_union_left Y hvX)
  have hxBoundary :
      x ⊆ AppendixA3ClusterSplit.boundaryVertices H X := by
    intro v hv
    rcases Rclean.exists_orient_source_eq_of_mem_sourceSet hv with
      ⟨i, hi⟩
    let O := Rclean.orient.path i
    have hsourceX : O.source ∈ X :=
      GraphPath.orient_source_mem
        (Rclean.path i) (Rclean.connects i)
    have htargetY : O.target ∈ Y :=
      GraphPath.orient_target_mem
        (Rclean.path i) (Rclean.connects i)
    have hneO : O.source ≠ O.target := by
      intro heq
      exact Finset.disjoint_left.mp hXY hsourceX
        (by simpa [heq] using htargetY)
    have hne : O.reverse.source ≠ O.reverse.target := by
      simpa [GraphPath.reverse] using hneO.symm
    have hnextNotX : O.reverse.penultimate ∉ X := by
      intro hnextX
      have hnextVertex :
          O.reverse.penultimate ∈ O.vertexSet := by
        simpa using O.reverse.penultimate_mem_vertexSet hne
      rcases hcleanX i hnextVertex hnextX with
        hnextSource | hnextTarget
      · exact (O.reverse.penultimate_adj_target hne).ne
          (by simpa [GraphPath.reverse] using hnextSource)
      · exact Finset.disjoint_left.mp hXY hnextX
          (by simpa [hnextTarget] using htargetY)
    apply (AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).2
    refine ⟨?_, O.reverse.penultimate, hnextNotX, ?_⟩
    · simpa [O, hi] using hsourceX
    · simpa [O, hi] using
        (O.reverse.penultimate_adj_target hne).symm
  have hyBoundary :
      y ⊆ AppendixA3ClusterSplit.boundaryVertices H Y := by
    intro v hv
    rcases Rclean.exists_orient_target_eq_of_mem_targetSet hv with
      ⟨i, hi⟩
    let O := Rclean.orient.path i
    have hsourceX : O.source ∈ X :=
      GraphPath.orient_source_mem
        (Rclean.path i) (Rclean.connects i)
    have htargetY : O.target ∈ Y :=
      GraphPath.orient_target_mem
        (Rclean.path i) (Rclean.connects i)
    have hne : O.source ≠ O.target := by
      intro heq
      exact Finset.disjoint_left.mp hXY hsourceX (heq ▸ htargetY)
    have hpenNotY : O.penultimate ∉ Y := by
      intro hpenY
      rcases hcleanY i (O.penultimate_mem_vertexSet hne) hpenY with
        hpenSource | hpenTarget
      · exact Finset.disjoint_left.mp hXY
          (by simpa [hpenSource] using hsourceX) hpenY
      · exact (O.penultimate_adj_target hne).ne hpenTarget
    apply (AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).2
    refine ⟨?_, O.penultimate, hpenNotY, ?_⟩
    · simpa [O, hi] using htargetY
    · simpa [O, hi] using (O.penultimate_adj_target hne).symm
  let Pind := P_H.mapLe hHC
  let P := Pind.mapLe (inducedOnFinset_le (G := G) (C := C))
  have hPstay : P.toPathPacking.StaysIn C := by
    simpa [P, Pind, P_H] using
      Section46.InducedOnFinset.pathPacking_mapLe_staysIn
        (G := G) (C := C) (A := x) (B := y)
        Pind.toPathPacking
        (Rclean.sourceSet_subset_left.trans hXC)
        (Rclean.targetSet_subset_right.trans hYC)
  have hP_H_X :
      P_H.toPathPacking.InternallyDisjointFromSet X := by
    apply PathPacking.toPerfectUsedTerminals_internallyDisjointFromSet
    intro i v hv hvX
    exact hterminalClean i hv (Finset.mem_union_left Y hvX)
  have hP_H_Y :
      P_H.toPathPacking.InternallyDisjointFromSet Y := by
    apply PathPacking.toPerfectUsedTerminals_internallyDisjointFromSet
    intro i v hv hvY
    exact hterminalClean i hv (Finset.mem_union_right X hvY)
  refine ⟨x, y, P, hxBoundary, hyBoundary,
    hxcard, hycard, ?_, hPstay, ?_, ?_⟩
  · simpa [P, Pind, P_H] using hRcleanCard
  · intro i v hv hvX
    exact hP_H_X i (by
      change v ∈ (((P_H.path i).mapLe hHC).mapLe
        (inducedOnFinset_le (G := G) (C := C))).vertexSet at hv
      simpa using hv) hvX
  · intro i v hv hvY
    exact hP_H_Y i (by
      change v ∈ (((P_H.path i).mapLe hHC).mapLe
        (inducedOnFinset_le (G := G) (C := C))).vertexSet at hv
      simpa using hv) hvY

/-- Claim 7.9's union-mass conclusion implies that at least half of each
original nail set remains in `X`. -/
theorem original_side_mass
    {A B X : Finset V} {kappa : ℕ}
    (hAcard : A.card = kappa)
    (hBcard : B.card = kappa)
    (hAB : Disjoint A B)
    (hmass : 3 * kappa ≤ 2 * (X ∩ (A ∪ B)).card) :
    kappa ≤ 2 * (X ∩ A).card ∧
      kappa ≤ 2 * (X ∩ B).card := by
  classical
  have hsplit :
      X ∩ (A ∪ B) = (X ∩ A) ∪ (X ∩ B) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hdisj :
      Disjoint (X ∩ A) (X ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hcardSplit :
      (X ∩ (A ∪ B)).card =
        (X ∩ A).card + (X ∩ B).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  have hXA : (X ∩ A).card ≤ kappa := by
    rw [← hAcard]
    exact Finset.card_le_card Finset.inter_subset_right
  have hXB : (X ∩ B).card ≤ kappa := by
    rw [← hBcard]
    exact Finset.card_le_card Finset.inter_subset_right
  rw [hcardSplit] at hmass
  omega

private theorem fresh_subset_card
    {U Z : Finset V} {m kappa : ℕ}
    (hU : kappa ≤ 2 * U.card)
    (hZ : Z.card = m)
    (hlarge : 4 * m ≤ kappa) :
    m ≤ (U \ Z).card := by
  have hinter : (U ∩ Z).card ≤ m := by
    rw [← hZ]
    exact Finset.card_le_card Finset.inter_subset_right
  have hparts := Finset.card_sdiff_add_card_inter U Z
  omega

/-- The terminal-boundary case of Lemma 7.10. -/
theorem exists_connector_of_many_terminal_boundary
    {C A B X Y Z : Finset V} {kappa width : ℕ}
    (hAcard : A.card = kappa)
    (hBcard : B.card = kappa)
    (hAB : Disjoint A B)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hXY : Disjoint X Y)
    (hAwl : NodeWellLinkedIn G C A)
    (hBwl : NodeWellLinkedIn G C B)
    (hXmass : 3 * kappa ≤ 2 * (X ∩ (A ∪ B)).card)
    (hZ : Z ⊆ (A ∪ B) ∩ Y)
    (hZlarge : 2 * width ≤ Z.card)
    (hkappaLarge : 4 * width ≤ kappa) :
    ∃ (x y : Finset V) (P : PerfectPathPacking G x y),
      x ⊆ X ∧ y ⊆ Y ∧
      x.card = width ∧ y.card = width ∧
      P.card = width ∧
      P.toPathPacking.StaysIn C ∧
      P.toPathPacking.InternallyDisjointFromSet X ∧
      P.toPathPacking.InternallyDisjointFromSet Y := by
  classical
  have hsideMass :=
    original_side_mass hAcard hBcard hAB hXmass
  have hZcover : Z = (Z ∩ A) ∪ (Z ∩ B) := by
    apply Finset.Subset.antisymm
    · intro v hvZ
      have hvAB := (Finset.mem_inter.mp (hZ hvZ)).1
      rcases Finset.mem_union.mp hvAB with hvA | hvB
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hvZ, hvA⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hvZ, hvB⟩)
    · intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).1
      · exact (Finset.mem_inter.mp hv).1
  have hZdisj : Disjoint (Z ∩ A) (Z ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hZsum :
      Z.card = (Z ∩ A).card + (Z ∩ B).card := by
    calc
      Z.card = ((Z ∩ A) ∪ (Z ∩ B)).card :=
        congrArg Finset.card hZcover
      _ = (Z ∩ A).card + (Z ∩ B).card :=
        Finset.card_union_of_disjoint hZdisj
  have hside :
      width ≤ (Z ∩ A).card ∨ width ≤ (Z ∩ B).card := by
    omega
  rcases hside with hside | hside
  · obtain ⟨y, hyZA, hycard⟩ :=
      Finset.exists_subset_card_eq hside
    have hyA : y ⊆ A :=
      hyZA.trans Finset.inter_subset_right
    have hyY : y ⊆ Y := by
      intro v hv
      exact (Finset.mem_inter.mp (hZ (Finset.inter_subset_left (hyZA hv)))).2
    have hfresh :
        width ≤ ((X ∩ A) \ y).card :=
      fresh_subset_card hsideMass.1 hycard hkappaLarge
    obtain ⟨x, hxfresh, hxcard⟩ :=
      Finset.exists_subset_card_eq hfresh
    have hxX : x ⊆ X :=
      hxfresh.trans Finset.sdiff_subset |>.trans Finset.inter_subset_left
    have hxA : x ⊆ A :=
      hxfresh.trans Finset.sdiff_subset |>.trans Finset.inter_subset_right
    have hxy : Disjoint x y := by
      rw [Finset.disjoint_left]
      intro v hvx hvy
      exact (Finset.mem_sdiff.mp (hxfresh hvx)).2 hvy
    rcases hAwl.2 hyA hxA hxy.symm with ⟨Q, hQcard, hQstay⟩
    have hQexact : Q.card = width := by
      simpa [hycard, hxcard] using hQcard
    have hhas :
        HasDisjointSTPaths (inducedOnFinset G C) X Y width := by
      let Qperfect := Q.toPerfectUsedTerminals
      have hQperfectStay :
          Qperfect.toPathPacking.StaysIn C :=
        PathPacking.toPerfectUsedTerminals_staysIn Q hQstay
      let Qrev := Qperfect.reverse
      have hQrevStay : Qrev.toPathPacking.StaysIn C :=
        PerfectPathPacking.reverse_staysIn Qperfect hQperfectStay
      let QrevInd := Qrev.inInducedOnFinset hQrevStay
      exact ⟨QrevInd.toPathPacking.widenTerminals
          (Q.targetSet_subset_right.trans hxX)
          (Q.sourceSet_subset_left.trans hyY),
        by simpa [QrevInd, Qrev, Qperfect, hQexact]⟩
    exact exists_cleanPerfect_of_hasDisjointSTPaths_induced
      hXC hYC hhas

  · obtain ⟨y, hyZB, hycard⟩ :=
      Finset.exists_subset_card_eq hside
    have hyB : y ⊆ B :=
      hyZB.trans Finset.inter_subset_right
    have hyY : y ⊆ Y := by
      intro v hv
      exact (Finset.mem_inter.mp (hZ (Finset.inter_subset_left (hyZB hv)))).2
    have hfresh :
        width ≤ ((X ∩ B) \ y).card :=
      fresh_subset_card hsideMass.2 hycard hkappaLarge
    obtain ⟨x, hxfresh, hxcard⟩ :=
      Finset.exists_subset_card_eq hfresh
    have hxX : x ⊆ X :=
      hxfresh.trans Finset.sdiff_subset |>.trans Finset.inter_subset_left
    have hxB : x ⊆ B :=
      hxfresh.trans Finset.sdiff_subset |>.trans Finset.inter_subset_right
    have hxy : Disjoint x y := by
      rw [Finset.disjoint_left]
      intro v hvx hvy
      exact (Finset.mem_sdiff.mp (hxfresh hvx)).2 hvy
    rcases hBwl.2 hyB hxB hxy.symm with ⟨Q, hQcard, hQstay⟩
    have hQexact : Q.card = width := by
      simpa [hycard, hxcard] using hQcard
    have hhas :
        HasDisjointSTPaths (inducedOnFinset G C) X Y width := by
      let Qperfect := Q.toPerfectUsedTerminals
      have hQperfectStay :
          Qperfect.toPathPacking.StaysIn C :=
        PathPacking.toPerfectUsedTerminals_staysIn Q hQstay
      let Qrev := Qperfect.reverse
      have hQrevStay : Qrev.toPathPacking.StaysIn C :=
        PerfectPathPacking.reverse_staysIn Qperfect hQperfectStay
      let QrevInd := Qrev.inInducedOnFinset hQrevStay
      exact ⟨QrevInd.toPathPacking.widenTerminals
          (Q.targetSet_subset_right.trans hxX)
          (Q.sourceSet_subset_left.trans hyY),
        by simpa [QrevInd, Qrev, Qperfect, hQexact]⟩
    exact exists_cleanPerfect_of_hasDisjointSTPaths_induced
      hXC hYC hhas

private theorem exists_half_indexSet_in_one_side
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Finset V} (source : ι → V)
    (I : Finset ι) {m : ℕ}
    (hsource :
      ∀ i ∈ I, source i ∈ A ∪ B)
    (hAB : Disjoint A B)
    (hIcard : I.card = 2 * m) :
    ∃ J : Finset ι,
      J ⊆ I ∧ J.card = m ∧
        ((∀ i ∈ J, source i ∈ A) ∨
          (∀ i ∈ J, source i ∈ B)) := by
  classical
  let IA := I.filter fun i => source i ∈ A
  let IB := I.filter fun i => source i ∈ B
  have hcover : I = IA ∪ IB := by
    apply Finset.Subset.antisymm
    · intro i hi
      rcases Finset.mem_union.mp (hsource i hi) with hiA | hiB
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hi, hiA⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hi, hiB⟩)
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact (Finset.mem_filter.mp hi).1
      · exact (Finset.mem_filter.mp hi).1
  have hdisj : Disjoint IA IB := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact Finset.disjoint_left.mp hAB
      (Finset.mem_filter.mp hiA).2
      (Finset.mem_filter.mp hiB).2
  have hsum : I.card = IA.card + IB.card := by
    calc
      I.card = (IA ∪ IB).card := congrArg Finset.card hcover
      _ = IA.card + IB.card :=
        Finset.card_union_of_disjoint hdisj
  by_cases hAm : m ≤ IA.card
  · obtain ⟨J, hJIA, hJcard⟩ :=
      Finset.exists_subset_card_eq hAm
    exact ⟨J, hJIA.trans (Finset.filter_subset _ _), hJcard,
      Or.inl (fun i hi => (Finset.mem_filter.mp (hJIA hi)).2)⟩
  · have hBm : m ≤ IB.card := by
      omega
    obtain ⟨J, hJIB, hJcard⟩ :=
      Finset.exists_subset_card_eq hBm
    exact ⟨J, hJIB.trans (Finset.filter_subset _ _), hJcard,
      Or.inr (fun i hi => (Finset.mem_filter.mp (hJIB hi)).2)⟩

private theorem hasDisjoint_of_synchronized_to_boundary
    {H : _root_.SimpleGraph V}
    {C A X Y S U : Finset V} {kappa m width : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hHC : H ≤ inducedOnFinset G C)
    (hdegree : MaxDegreeAtMost G 3)
    (hAwl : NodeWellLinkedIn G C A)
    (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hXY : Disjoint X Y)
    (hSside : S ⊆ A)
    (hUY : U ⊆ Y)
    (hsideMass : kappa ≤ 2 * (X ∩ A).card)
    (hkappaLarge : 4 * m ≤ kappa)
    (hm : m = 5 * width)
    (R : SynchronizedRouting H S U ι)
    (hSCardM : S.card = m)
    (hScard : S.card = Fintype.card ι)
    (hUcard : U.card = Fintype.card ι)
    (hRcongestion : R.EdgeCongestionAtMost 1) :
    HasDisjointSTPaths (inducedOnFinset G C) X Y width := by
  classical
  have hmcard : m = Fintype.card ι := by
    exact hSCardM.symm.trans hScard
  have hfresh : m ≤ ((X ∩ A) \ S).card :=
    fresh_subset_card hsideMass hSCardM hkappaLarge
  obtain ⟨x, hxfresh, hxcard⟩ :=
    Finset.exists_subset_card_eq hfresh
  have hxX : x ⊆ X :=
    hxfresh.trans Finset.sdiff_subset |>.trans Finset.inter_subset_left
  have hxA : x ⊆ A :=
    hxfresh.trans Finset.sdiff_subset |>.trans Finset.inter_subset_right
  have hxS : Disjoint x S := by
    rw [Finset.disjoint_left]
    intro v hvx hvS
    exact (Finset.mem_sdiff.mp (hxfresh hvx)).2 hvS
  rcases hAwl.2 hSside hxA hxS.symm with ⟨Q, hQcard, hQstay⟩
  have hQexact : Q.card = m := by
    simpa [hSCardM, hxcard] using hQcard
  let Qperfect : PerfectPathPacking G S x :=
    Q.toPerfectOfCardEq
      (by simpa [hSCardM] using hQexact)
      (by simpa [hxcard] using hQexact)
  let Qrev := Qperfect.reverse
  let Qsync :=
    AppendixA3EndpointMatching.synchronizedRoutingOfPerfect Qrev
  let sourceEquiv :
      ι ≃ {v : V // v ∈ S} :=
    AppendixA3EndpointMatching.SynchronizedRouting.sourceEquivOfCard
      R hScard
  let tokenEquiv : ι ≃ Qrev.Index :=
    sourceEquiv.trans Qrev.targetEquiv.symm
  let Qaligned := Qsync.reindex tokenEquiv
  have hmatch :
      ∀ i : ι, (Qaligned.path i).target = (R.path i).source := by
    intro i
    have h :=
      Qrev.targetEquiv.apply_symm_apply (sourceEquiv i)
    exact congrArg Subtype.val h
  have hQcongestion : Qaligned.EdgeCongestionAtMost 1 := by
    apply SynchronizedRouting.reindex_edgeCongestionAtMost
    exact
      AppendixA3EndpointMatching.synchronizedRoutingOfPerfect_edgeCongestionAtMost_one
        Qrev
  have hHG : H ≤ G := hHC.trans inducedOnFinset_le
  let Rg := R.mapLe hHG
  have hRgcongestion : Rg.EdgeCongestionAtMost 1 :=
    R.mapLe_edgeCongestionAtMost hHG hRcongestion
  let combined := Qaligned.concat Rg hmatch
  have hcombinedCongestion :
      combined.EdgeCongestionAtMost 2 := by
    simpa [combined] using
      Qaligned.concat_edgeCongestionAtMost Rg hmatch
        hQcongestion hRgcongestion
  have hQstay' : ∀ i : ι, (Qaligned.path i).vertexSet ⊆ C := by
    intro i
    have hQperfectStay :
        Qperfect.toPathPacking.StaysIn C := by
      simpa [Qperfect] using PathPacking.orient_staysIn hQstay
    have hQrevStay : Qrev.toPathPacking.StaysIn C :=
      PerfectPathPacking.reverse_staysIn Qperfect hQperfectStay
    simpa [Qaligned, Qsync, tokenEquiv] using
      hQrevStay (tokenEquiv i)
  have hRstay : ∀ i : ι, (Rg.path i).vertexSet ⊆ C := by
    intro i
    let PH := (R.path i).mapLe hHC
    have hconnects : PH.Connects S U :=
      Or.inl ⟨R.source_mem i, R.target_mem i⟩
    have hPH :=
      Section46.InducedOnFinset.graphPath_vertexSet_subset_of_connects
        (G := G) (C := C) (A := S) (B := U) PH hconnects
        (hSside.trans hAwl.1) (hUY.trans hYC)
    simpa [Rg, PH] using hPH
  have hcombinedStay :
      ∀ i : ι, (combined.path i).vertexSet ⊆ C := by
    intro i v hv
    have hvUnion :=
      ChekuriChuzhoySection5Phase1Flow.GraphPath.concatErase_vertexSet_subset
        (Qaligned.path i) (Rg.path i) (hmatch i) hv
    rcases Finset.mem_union.mp hvUnion with hvQ | hvR
    · exact hQstay' i hvQ
    · exact hRstay i hvR
  let combinedInd :=
    AppendixA3EndpointMatching.synchronizedRoutingInInducedOnFinset
      combined hcombinedStay
  have hcombinedIndCongestion :
      combinedInd.EdgeCongestionAtMost 2 :=
    AppendixA3EndpointMatching.synchronizedRoutingInInducedOnFinset_edgeCongestionAtMost
      combined hcombinedStay hcombinedCongestion
  have hxCardIndex : x.card = Fintype.card ι := by
    rw [hxcard, hmcard]
  have hunit :
      combinedInd.toOrientedPathFlow.IsUnitFlow :=
    combinedInd.toOrientedPathFlow_isUnitFlow hxCardIndex hUcard
  have hedge :
      combinedInd.toOrientedPathFlow.EdgeCongestionAtMost
        (scaledCongestion 1 2) := by
    have hnat :=
      combinedInd.toOrientedPathFlow_edgeCongestionAtMost
        hcombinedIndCongestion
    simpa [scaledCongestion] using hnat
  have hdisjXU : Disjoint x U :=
    hXY.mono hxX hUY
  have hroute :
      HasDisjointSTPaths (inducedOnFinset G C) x U width := by
    apply OrientedPathFlow.hasDisjointSTPaths_of_unit_edgeCongestedFlow_disjoint
      (G := inducedOnFinset G C) (S := x) (T := U)
      (alphaNum := 1) (alphaDen := 2) (Δ := 3)
      (maxDegreeAtMost_of_le hdegree inducedOnFinset_le)
      (by decide) (by decide) (by decide) hdisjXU
      ⟨combinedInd.toOrientedPathFlow, hunit, hedge⟩
    rw [hxcard, hm]
    omega
  rcases hroute with ⟨P, hPcard⟩
  exact ⟨P.widenTerminals hxX hUY, hPcard⟩

/-- The nonterminal-boundary case of Lemma 7.10. -/
theorem exists_connector_of_many_nonterminal_boundary
    {H : _root_.SimpleGraph V}
    {C A B X Y : Finset V}
    {kappa width alphaDen : ℕ}
    (hHC : H ≤ inducedOnFinset G C)
    (hdegree : MaxDegreeAtMost G 3)
    (hAcard : A.card = kappa)
    (hBcard : B.card = kappa)
    (hAB : Disjoint A B)
    (hAwl : NodeWellLinkedIn G C A)
    (hBwl : NodeWellLinkedIn G C B)
    (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hXY : Disjoint X Y)
    (hXmass : 3 * kappa ≤ 2 * (X ∩ (A ∪ B)).card)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn
        H (Finset.univ : Finset V) (A ∪ B) 1 3)
    (hminimal :
      ∀ ⦃a b : V⦄, H.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (H.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) (A ∪ B) 1 3)
    (hGammaY :
      Section46.ScaledEdgeWellLinkedIn H Y
        (AppendixA3ClusterSplit.augmentedBoundaryVertices
          H Y (A ∪ B)) 1 alphaDen)
    (hGamma0Large :
      180 * alphaDen * width ≤
        ((AppendixA3ClusterSplit.boundaryVertices H Y) \
          (A ∪ B)).card)
    (hkappaLarge : 20 * width ≤ kappa) :
    ∃ (x y : Finset V) (P : PerfectPathPacking G x y),
      x ⊆ X ∧ y ⊆ Y ∧
      x.card = width ∧ y.card = width ∧
      P.card = width ∧
      P.toPathPacking.StaysIn C ∧
      P.toPathPacking.InternallyDisjointFromSet X ∧
      P.toPathPacking.InternallyDisjointFromSet Y := by
  classical
  let T := A ∪ B
  let Gamma0 :=
    (AppendixA3ClusterSplit.boundaryVertices H Y) \ T
  have hGamma0Aug :
      Gamma0 ⊆
        AppendixA3ClusterSplit.augmentedBoundaryVertices H Y T := by
    intro v hv
    exact Finset.mem_union_left _
      (Finset.mem_sdiff.mp hv).1
  have hGamma0Local :
      Section46.ScaledEdgeWellLinkedIn H Y Gamma0 1 alphaDen :=
    hGammaY.mono_terminals (by
      simpa [T, Gamma0] using hGamma0Aug)
  have hGamma0 :
      Section46.ScaledEdgeWellLinkedIn H
        (Finset.univ : Finset V) Gamma0 1 alphaDen :=
    AppendixA3Corollary74.scaledEdgeWellLinkedIn_univ_of_region
      hGamma0Local
  have hdisjoint : Disjoint T Gamma0 := by
    rw [Finset.disjoint_left]
    intro v hvT hvGamma
    exact (Finset.mem_sdiff.mp hvGamma).2 hvT
  obtain ⟨Pedge, hPedgeCard, _hPedgeStay⟩ :=
    AppendixA3Lemma72.lemma_7_2_edgePathPacking
      (by simpa [T] using hTwell) hminimal hGamma0 hdisjoint
  have hdenPos : 0 < 3 * alphaDen := by
    have : 0 < alphaDen := hGammaY.1.trans_le hGammaY.2.1
    positivity
  have hPedgeLarge : 60 * width ≤ Pedge.card := by
    rw [hPedgeCard]
    simp only [one_mul]
    apply (Nat.le_div_iff_mul_le hdenPos).2
    simpa only [Gamma0, T, show
        60 * width * (3 * alphaDen) =
          180 * alphaDen * width by ring] using hGamma0Large
  have hdegreeH : MaxDegreeAtMost H 3 :=
    maxDegreeAtMost_of_le hdegree (hHC.trans inducedOnFinset_le)
  obtain ⟨S0, U0, I, hsourceI, htargetI, hIcard,
      _hS0T, _hU0Gamma, hS0eq, hU0eq, _hIcongestion⟩ :=
    AppendixA3EndpointMatching.exists_synchronizedRouting_of_edgePathPacking
        (Delta := 3) (width := 10 * width)
        Pedge hdisjoint hdegreeH (by decide)
        (by
          simpa only [show 2 * 3 * (10 * width) = 60 * width by ring]
            using hPedgeLarge)
  let source := fun i : Pedge.Index =>
    ((Pedge.path i).orient (Pedge.connects i)).source
  let target := fun i : Pedge.Index =>
    ((Pedge.path i).orient (Pedge.connects i)).target
  have hsourceT :
      ∀ i ∈ I, source i ∈ A ∪ B := by
    intro i hi
    simpa [source, T] using
      GraphPath.orient_source_mem (Pedge.path i) (Pedge.connects i)
  obtain ⟨J, hJI, hJcard, hJside⟩ :=
    exists_half_indexSet_in_one_side (m := 5 * width)
      source I hsourceT hAB
      (by simpa only [show 2 * (5 * width) = 10 * width by ring]
        using hIcard)
  have hsourceJ : Set.InjOn source J :=
    hsourceI.mono hJI
  have htargetJ : Set.InjOn target J :=
    htargetI.mono hJI
  let S := J.image source
  let U := J.image target
  let R :=
    AppendixA3EndpointMatching.toSynchronizedRouting
      Pedge J hsourceJ htargetJ
  have hSCard : S.card = 5 * width := by
    change (J.image source).card = 5 * width
    exact (Finset.card_image_of_injOn hsourceJ).trans hJcard
  have hUCard : U.card = 5 * width := by
    change (J.image target).card = 5 * width
    exact (Finset.card_image_of_injOn htargetJ).trans hJcard
  have hSIndex :
      S.card = Fintype.card {i : Pedge.Index // i ∈ J} := by
    rw [hSCard, Fintype.card_coe]
    exact hJcard.symm
  have hUIndex :
      U.card = Fintype.card {i : Pedge.Index // i ∈ J} := by
    rw [hUCard, Fintype.card_coe]
    exact hJcard.symm
  have hUY : U ⊆ Y := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    have hvGamma0 :
        target i ∈ Gamma0 := by
      simpa [target] using
        GraphPath.orient_target_mem (Pedge.path i) (Pedge.connects i)
    exact
      ((AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).1
        (Finset.mem_sdiff.mp hvGamma0).1).1
  have hRcongestion : R.EdgeCongestionAtMost 1 :=
    AppendixA3EndpointMatching.toSynchronizedRouting_edgeCongestionAtMost_one
      Pedge J hsourceJ htargetJ
  have hsideMass :=
    original_side_mass hAcard hBcard hAB hXmass
  have hhas :
      HasDisjointSTPaths (inducedOnFinset G C) X Y width := by
    rcases hJside with hJA | hJB
    · apply hasDisjoint_of_synchronized_to_boundary
        hHC hdegree hAwl hXC hYC hXY
        (by
          intro v hv
          rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
          exact hJA i hi)
        hUY hsideMass.1 (by simpa only [show
          4 * (5 * width) = 20 * width by ring] using hkappaLarge)
        rfl R hSCard hSIndex hUIndex hRcongestion
    · apply hasDisjoint_of_synchronized_to_boundary
        hHC hdegree hBwl hXC hYC hXY
        (by
          intro v hv
          rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
          exact hJB i hi)
        hUY hsideMass.2 (by simpa only [show
          4 * (5 * width) = 20 * width by ring] using hkappaLarge)
        rfl R hSCard hSIndex hUIndex hRcongestion
  exact exists_cleanPerfect_of_hasDisjointSTPaths_induced
    hXC hYC hhas

/-- Chuzhoy Lemma 7.10, specialized to degree three and with one explicit
constant.  The ambient graph `G` supplies the original node linkages; `H` is
the edge-minimal subgraph in which Lemmas 7.2, 7.5, and 7.8 are run. -/
theorem exists_lemma710_connector
    {H : _root_.SimpleGraph V}
    {C A B X Y : Finset V}
    {kappa rho width : ℕ}
    (hwidth : 0 < width)
    (hHC : H ≤ inducedOnFinset G C)
    (hdegree : MaxDegreeAtMost G 3)
    (hAcard : A.card = kappa)
    (hBcard : B.card = kappa)
    (hAB : Disjoint A B)
    (hAwl : NodeWellLinkedIn G C A)
    (hBwl : NodeWellLinkedIn G C B)
    (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hXY : Disjoint X Y)
    (hkappa : kappa = 256 * rho)
    (hrho :
      rho =
        72 * (180 * AppendixA3Lemma75.finalAlphaDen + 2) * width)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn H
        (Finset.univ : Finset V) (A ∪ B) 1 3)
    (hminimal :
      ∀ ⦃a b : V⦄, H.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (H.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) (A ∪ B) 1 3)
    (hYlarge :
      rho ≤ 4 *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices
          H Y (A ∪ B)).card)
    (hYwell :
      Section46.ScaledEdgeWellLinkedIn H Y
        (AppendixA3ClusterSplit.augmentedBoundaryVertices
          H Y (A ∪ B))
        1 AppendixA3Lemma75.finalAlphaDen)
    (hXmass :
      3 * kappa ≤ 2 * (X ∩ (A ∪ B)).card) :
    ∃ (x y : Finset V) (P : PerfectPathPacking G x y),
      x ⊆ X ∧ y ⊆ Y ∧
      x.card = width ∧ y.card = width ∧
      P.card = width ∧
      P.toPathPacking.StaysIn C ∧
      P.toPathPacking.InternallyDisjointFromSet X ∧
      P.toPathPacking.InternallyDisjointFromSet Y := by
  classical
  let T := A ∪ B
  let boundary := AppendixA3ClusterSplit.boundaryVertices H Y
  have hTcard : T.card = 2 * kappa := by
    change (A ∪ B).card = 2 * kappa
    rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard]
    omega
  have hdegreeH : MaxDegreeAtMost H 3 :=
    maxDegreeAtMost_of_le hdegree (hHC.trans inducedOnFinset_le)
  have hboundaryLower :
      rho ≤ 72 * boundary.card := by
    simpa [T, boundary] using
      AppendixA3Observation711.rho_le_seventy_two_mul_boundaryVertices_card
        (G := H) hkappa hTcard hTwell hdegreeH hXY hXmass hYlarge
  let terminalBoundary := boundary ∩ T
  by_cases hterminal :
      2 * width ≤ terminalBoundary.card
  · have hZ :
        terminalBoundary ⊆ T ∩ Y := by
      intro v hv
      have hvBoundary := (Finset.mem_inter.mp hv).1
      have hvT := (Finset.mem_inter.mp hv).2
      have hvY :=
        ((AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).1
          hvBoundary).1
      exact Finset.mem_inter.mpr ⟨hvT, hvY⟩
    have hkappaLarge : 4 * width ≤ kappa := by
      rw [hkappa, hrho]
      have hD : 0 < AppendixA3Lemma75.finalAlphaDen := by
        simp [AppendixA3Lemma75.finalAlphaDen]
      nlinarith
    exact exists_connector_of_many_terminal_boundary
      hAcard hBcard hAB hAwl.1 hBwl.1 hXC hYC hXY
      hAwl hBwl hXmass (by simpa [T, terminalBoundary] using hZ)
      hterminal hkappaLarge
  · have hterminalSmall :
        terminalBoundary.card < 2 * width :=
      Nat.lt_of_not_ge hterminal
    have hscaledBoundary :
        (180 * AppendixA3Lemma75.finalAlphaDen + 2) * width ≤
          boundary.card := by
      have hscaled :
          72 *
              ((180 * AppendixA3Lemma75.finalAlphaDen + 2) * width) ≤
            72 * boundary.card := by
        simpa [hrho, Nat.mul_assoc] using hboundaryLower
      exact Nat.le_of_mul_le_mul_left hscaled (by decide)
    have hparts :=
      Finset.card_sdiff_add_card_inter boundary T
    have hparts' :
        (boundary \ T).card + terminalBoundary.card =
          boundary.card := by
      simpa [terminalBoundary] using hparts
    have hGamma0Large :
        180 * AppendixA3Lemma75.finalAlphaDen * width ≤
          (boundary \ T).card := by
      change terminalBoundary.card < 2 * width at hterminalSmall
      have hdecomp :
          (180 * AppendixA3Lemma75.finalAlphaDen + 2) * width =
            180 * AppendixA3Lemma75.finalAlphaDen * width +
              2 * width := by ring
      rw [hdecomp] at hscaledBoundary
      omega
    exact exists_connector_of_many_nonterminal_boundary
      hHC hdegree hAcard hBcard hAB hAwl hBwl
      hXC hYC hXY hXmass hTwell hminimal hYwell
      (by simpa [boundary, T] using hGamma0Large)
      (by
        rw [hkappa, hrho]
        have hD : 0 < AppendixA3Lemma75.finalAlphaDen := by
          simp [AppendixA3Lemma75.finalAlphaDen]
        nlinarith)

/-! ## Source-faithful all-minimal-graph connector -/

private theorem hasDisjoint_of_large_synchronized_boundary_routing
    {H : _root_.SimpleGraph V}
    {C T X Y S U : Finset V}
    {kappa width : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hwidth : 0 < width)
    (hHC : H ≤ inducedOnFinset G C)
    (hdegreeH : MaxDegreeAtMost H 3)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn H
        (Finset.univ : Finset V) T 1 3)
    (hTnonempty : T.Nonempty)
    (hST : S ⊆ T)
    (hUY :
      U ⊆ AppendixA3ClusterSplit.boundaryVertices H Y)
    (hXY : Disjoint X Y)
    (hXmass : 3 * kappa ≤ 2 * (X ∩ T).card)
    (hkappaLarge : 4 * (2700 * width) ≤ 3 * kappa)
    (R : SynchronizedRouting H S U ι)
    (hScard : S.card = 2700 * width)
    (hSindex : S.card = Fintype.card ι)
    (hUindex : U.card = Fintype.card ι)
    (hRcongestion : R.EdgeCongestionAtMost 1) :
    HasDisjointSTPaths H X Y width := by
  classical
  obtain ⟨K, hKcluster, hTK, hTwellK⟩ :=
    Section46.exists_cluster_scaledEdgeWellLinkedIn_of_univ
      hTnonempty hTwell
  have hXrawLarge :
      2700 * width ≤ ((X ∩ T) \ S).card := by
    have hinter : ((X ∩ T) ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hparts := Finset.card_sdiff_add_card_inter (X ∩ T) S
    rw [hScard] at hinter
    omega
  obtain ⟨Xraw, hXrawSub, hXrawCard⟩ :=
    Finset.exists_subset_card_eq hXrawLarge
  have hXrawX : Xraw ⊆ X :=
    hXrawSub.trans Finset.sdiff_subset |>.trans Finset.inter_subset_left
  have hXrawT : Xraw ⊆ T :=
    hXrawSub.trans Finset.sdiff_subset |>.trans Finset.inter_subset_right
  have hSXraw : Disjoint S Xraw := by
    rw [Finset.disjoint_left]
    intro v hvS hvXraw
    exact (Finset.mem_sdiff.mp (hXrawSub hvXraw)).2 hvS
  have hSwell :
      Section46.ScaledEdgeWellLinkedIn H K S 1 3 :=
    hTwellK.mono_terminals hST
  have hXrawWell :
      Section46.ScaledEdgeWellLinkedIn H K Xraw 1 3 :=
    hTwellK.mono_terminals hXrawT
  obtain ⟨Sres, hSresS, hSresLarge, hSresNode⟩ :=
    ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := H) (C := K) (T := S)
      (alphaNum := 1) (alphaDen := 3) (Δ := 3)
      (κ := 2700 * width)
      hKcluster hdegreeH (by decide) (by decide) (by decide)
      hScard hSwell
  obtain ⟨Xres, hXresRaw, hXresLarge, hXresNode⟩ :=
    ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := H) (C := K) (T := Xraw)
      (alphaNum := 1) (alphaDen := 3) (Δ := 3)
      (κ := 2700 * width)
      hKcluster hdegreeH (by decide) (by decide) (by decide)
      hXrawCard hXrawWell
  have hfloor :
      (3 * 1 * (2700 * width)) / (10 * 3 * 3) =
        90 * width := by
    have : 10 * 3 * 3 = 90 := by decide
    rw [this]
    omega
  rw [hfloor] at hSresLarge hXresLarge
  obtain ⟨Sbig, hSbigRes, hSbigCard⟩ :=
    Finset.exists_subset_card_eq hSresLarge
  obtain ⟨Xbig, hXbigRes, hXbigCard⟩ :=
    Finset.exists_subset_card_eq hXresLarge
  have hSbigNode : NodeWellLinkedIn H K Sbig :=
    hSresNode.mono_terminals hSbigRes
  have hXbigNode : NodeWellLinkedIn H K Xbig :=
    hXresNode.mono_terminals hXbigRes
  have hSbigS : Sbig ⊆ S := hSbigRes.trans hSresS
  have hXbigXraw : Xbig ⊆ Xraw :=
    hXbigRes.trans hXresRaw
  have hSbigXbig : Disjoint Sbig Xbig :=
    hSXraw.mono hSbigS hXbigXraw
  have hUnionWell :
      Section46.ScaledEdgeWellLinkedIn H K (Sbig ∪ Xbig) 1 3 :=
    hTwellK.mono_terminals (by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hST (hSbigS hv)
      · exact hXrawT (hXbigXraw hv))
  have hmLarge : 5 * width ≤ Sbig.card := by
    rw [hSbigCard]
    omega
  have hmLargeX : 5 * width ≤ Xbig.card := by
    rw [hXbigCard]
    omega
  obtain ⟨Ssmall, hSsmallBig, hSsmallCard⟩ :=
    Finset.exists_subset_card_eq hmLarge
  obtain ⟨Xsmall, hXsmallBig, hXsmallCard⟩ :=
    Finset.exists_subset_card_eq hmLargeX
  have hlinked :
      NodeLinkedIn H K Ssmall Xsmall := by
    apply Section46.theorem421_linkedSubsets_scaledEdgeWellLinked_minCard
      (G := H) (C := K) (T1 := Sbig) (T2 := Xbig)
      (T1' := Ssmall) (T2' := Xsmall)
      (Delta := 3) (kappa := 90 * width)
      (alphaNum := 1) (alphaDen := 3)
      hdegreeH (by decide) (by decide) hSbigXbig
      (by rw [hSbigCard]) (by rw [hXbigCard])
      hUnionWell hSbigNode hXbigNode
      hSsmallBig hXsmallBig
    rw [hSsmallCard]
    omega
  obtain ⟨L, hLcard, hLstay⟩ :=
    hlinked.exists_perfectPathPacking_of_card_eq
      (by rw [hSsmallCard, hXsmallCard])
  let sourceEquiv :
      ι ≃ {v : V // v ∈ S} :=
    AppendixA3EndpointMatching.SynchronizedRouting.sourceEquivOfCard
      R hSindex
  let source := fun i : ι => (R.path i).source
  let J :=
    (Finset.univ : Finset ι).filter fun i => source i ∈ Ssmall
  let token := {i : ι // i ∈ J}
  let sourceSmallEquiv : token ≃ {v : V // v ∈ Ssmall} := by
    apply Equiv.ofBijective
      (fun i =>
        ⟨(R.path i.1).source, (Finset.mem_filter.mp i.2).2⟩)
    constructor
    · intro i j hij
      apply Subtype.ext
      exact R.source_injective (congrArg Subtype.val hij)
    · intro v
      let sv : {x : V // x ∈ S} :=
        ⟨v.1, hSbigS (hSsmallBig v.2)⟩
      let i : ι := sourceEquiv.symm sv
      have hi : (R.path i).source = v.1 := by
        have h := sourceEquiv.apply_symm_apply sv
        exact congrArg Subtype.val h
      refine ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩, ?_⟩
      · simpa [source, hi] using v.2
      · exact Subtype.ext hi
  let Usmall :=
    J.image fun i => (R.path i).target
  let Rsmall : SynchronizedRouting H Ssmall Usmall token :=
    { path := fun i => R.path i.1
      source_mem := by
        intro i
        exact (Finset.mem_filter.mp i.2).2
      target_mem := by
        intro i
        exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
      source_injective := by
        intro i j hij
        apply Subtype.ext
        exact R.source_injective hij
      target_injective := by
        intro i j hij
        apply Subtype.ext
        exact R.target_injective hij }
  have hUsmallU : Usmall ⊆ U := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact R.target_mem i
  have hRsmallCongestion :
      Rsmall.EdgeCongestionAtMost 1 := by
    intro e he
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hiOld :
        i.1 ∈
          (Finset.univ.filter fun a : ι =>
            e ∈ (R.path a).edgeSet) :=
      Finset.mem_filter.mpr
        ⟨by simp, (Finset.mem_filter.mp hi).2⟩
    have hjOld :
        j.1 ∈
          (Finset.univ.filter fun a : ι =>
            e ∈ (R.path a).edgeSet) :=
      Finset.mem_filter.mpr
        ⟨by simp, (Finset.mem_filter.mp hj).2⟩
    have holdEq :
        i.1 = j.1 :=
      Finset.card_le_one.mp (hRcongestion e he)
        i.1 hiOld j.1 hjOld
    exact Subtype.ext holdEq
  let Lrev := L.reverse
  let Lsync :=
    AppendixA3EndpointMatching.synchronizedRoutingOfPerfect Lrev
  let align : token ≃ Lrev.Index :=
    sourceSmallEquiv.trans Lrev.targetEquiv.symm
  let Laligned := Lsync.reindex align
  have hmatch :
      ∀ i : token,
        (Laligned.path i).target = (Rsmall.path i).source := by
    intro i
    have h :=
      Lrev.targetEquiv.apply_symm_apply (sourceSmallEquiv i)
    exact congrArg Subtype.val h
  have hLcongestion : Laligned.EdgeCongestionAtMost 1 := by
    apply SynchronizedRouting.reindex_edgeCongestionAtMost
    exact
      AppendixA3EndpointMatching.synchronizedRoutingOfPerfect_edgeCongestionAtMost_one
        Lrev
  let combined := Laligned.concat Rsmall hmatch
  have hcombinedCongestion :
      combined.EdgeCongestionAtMost 2 := by
    simpa [combined] using
      Laligned.concat_edgeCongestionAtMost Rsmall hmatch
        hLcongestion hRsmallCongestion
  have hXsmallX : Xsmall ⊆ X :=
    hXsmallBig.trans hXbigXraw |>.trans hXrawX
  have hUsmallY : Usmall ⊆ Y :=
    hUsmallU.trans (hUY.trans
      (fun v hv =>
        ((AppendixA3ClusterSplit.mem_boundaryVertices (G := H)).1 hv).1))
  have hdisjSmall : Disjoint Xsmall Usmall :=
    hXY.mono hXsmallX hUsmallY
  have hXsmallIndex :
      Xsmall.card = Fintype.card token := by
    calc
      Xsmall.card = Ssmall.card := by
        rw [hXsmallCard, hSsmallCard]
      _ = Fintype.card token := by
        simpa using Fintype.card_congr sourceSmallEquiv.symm
  have hUsmallIndex :
      Usmall.card = Fintype.card token := by
    change
      (J.image fun i => (R.path i).target).card =
        Fintype.card token
    rw [Finset.card_image_of_injective]
    · simp [token]
    · exact R.target_injective
  have hunit :
      combined.toOrientedPathFlow.IsUnitFlow :=
    combined.toOrientedPathFlow_isUnitFlow
      hXsmallIndex hUsmallIndex
  have hedge :
      combined.toOrientedPathFlow.EdgeCongestionAtMost
        (scaledCongestion 1 2) := by
    have hnat :=
      combined.toOrientedPathFlow_edgeCongestionAtMost
        hcombinedCongestion
    simpa [scaledCongestion] using hnat
  have hroute :
      HasDisjointSTPaths H Xsmall Usmall width := by
    apply OrientedPathFlow.hasDisjointSTPaths_of_unit_edgeCongestedFlow_disjoint
      (G := H) (S := Xsmall) (T := Usmall)
      (alphaNum := 1) (alphaDen := 2) (Δ := 3)
      hdegreeH (by decide) (by decide) (by decide) hdisjSmall
      ⟨combined.toOrientedPathFlow, hunit, hedge⟩
    rw [hXsmallCard]
    omega
  rcases hroute with ⟨P, hPcard⟩
  exact ⟨P.widenTerminals hXsmallX hUsmallY, hPcard⟩

/-- Chuzhoy Lemma 7.10 in the form consumed by the final Appendix A.3
assembly.  All linkage work takes place in the edge-minimal graph `H`.
Cleaning the resulting paths records that their endpoints belong to the
ordinary boundaries of both clusters. -/
theorem exists_lemma710_connector_boundary
    {H : _root_.SimpleGraph V}
    {C T X Y : Finset V}
    {kappa rho width : ℕ}
    (hwidth : 0 < width)
    (hHC : H ≤ inducedOnFinset G C)
    (hdegreeH : MaxDegreeAtMost H 3)
    (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hXY : Disjoint X Y)
    (hkappa : kappa = 256 * rho)
    (hrho :
      rho =
        72 *
          (48600 * AppendixA3Lemma75.finalAlphaDen + 2700) *
            width)
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn H
        (Finset.univ : Finset V) T 1 3)
    (hminimal :
      ∀ ⦃a b : V⦄, H.Adj a b →
        ¬ Section46.ScaledEdgeWellLinkedIn
          (H.deleteEdges ({s(a, b)} : Set (Sym2 V)))
          (Finset.univ : Finset V) T 1 3)
    (hYlarge :
      rho ≤ 4 *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices
          H Y T).card)
    (hYwell :
      Section46.ScaledEdgeWellLinkedIn H Y
        (AppendixA3ClusterSplit.augmentedBoundaryVertices
          H Y T)
        1 AppendixA3Lemma75.finalAlphaDen)
    (hXmass :
      3 * kappa ≤ 2 * (X ∩ T).card) :
    ∃ (x y : Finset V) (P : PerfectPathPacking G x y),
      x ⊆ AppendixA3ClusterSplit.boundaryVertices H X ∧
      y ⊆ AppendixA3ClusterSplit.boundaryVertices H Y ∧
      x.card = width ∧ y.card = width ∧
      P.card = width ∧
      P.toPathPacking.StaysIn C ∧
      P.toPathPacking.InternallyDisjointFromSet X ∧
      P.toPathPacking.InternallyDisjointFromSet Y := by
  classical
  let boundary := AppendixA3ClusterSplit.boundaryVertices H Y
  have hrhoPos : 0 < rho := by
    rw [hrho]
    positivity
  have hkappaPos : 0 < kappa := by
    rw [hkappa]
    positivity
  have hTnonempty : T.Nonempty := by
    apply Finset.card_pos.mp
    rw [hTcard]
    omega
  have hboundaryLower :
      rho ≤ 72 * boundary.card := by
    simpa [boundary] using
      AppendixA3Observation711.rho_le_seventy_two_mul_boundaryVertices_card
        (G := H) hkappa hTcard hTwell hdegreeH hXY hXmass hYlarge
  have hkappaLarge :
      4 * (2700 * width) ≤ 3 * kappa := by
    rw [hkappa, hrho]
    nlinarith
  let terminalBoundary := boundary ∩ T
  by_cases hterminal :
      2700 * width ≤ terminalBoundary.card
  · obtain ⟨Z, hZterminal, hZcard⟩ :=
      Finset.exists_subset_card_eq hterminal
    have hZT : Z ⊆ T :=
      hZterminal.trans Finset.inter_subset_right
    have hZboundary : Z ⊆ boundary :=
      hZterminal.trans Finset.inter_subset_left
    let P0 := PerfectPathPacking.refl H Z
    let R :=
      AppendixA3EndpointMatching.synchronizedRoutingOfPerfect P0
    have hZindex :
        Z.card = Fintype.card P0.Index := by
      simpa [PerfectPathPacking.card] using
        (PerfectPathPacking.refl_card H Z).symm
    have hRcongestion : R.EdgeCongestionAtMost 1 :=
      AppendixA3EndpointMatching.synchronizedRoutingOfPerfect_edgeCongestionAtMost_one
        P0
    have hhas :
        HasDisjointSTPaths H X Y width :=
      hasDisjoint_of_large_synchronized_boundary_routing
        hwidth hHC hdegreeH hTwell hTnonempty hZT hZboundary
        hXY hXmass hkappaLarge R hZcard hZindex hZindex
        hRcongestion
    exact exists_cleanPerfect_boundary_of_hasDisjointSTPaths
      hHC hXC hYC hXY hhas
  · have hterminalSmall :
        terminalBoundary.card < 2700 * width :=
      Nat.lt_of_not_ge hterminal
    have hscaledBoundary :
        (48600 * AppendixA3Lemma75.finalAlphaDen + 2700) *
            width ≤ boundary.card := by
      have hscaled :
          72 *
              ((48600 * AppendixA3Lemma75.finalAlphaDen + 2700) *
                width) ≤
            72 * boundary.card := by
        simpa [hrho, Nat.mul_assoc] using hboundaryLower
      exact Nat.le_of_mul_le_mul_left hscaled (by decide)
    have hparts :=
      Finset.card_sdiff_add_card_inter boundary T
    have hparts' :
        (boundary \ T).card + terminalBoundary.card =
          boundary.card := by
      simpa [terminalBoundary] using hparts
    have hGamma0Large :
        48600 * AppendixA3Lemma75.finalAlphaDen * width ≤
          (boundary \ T).card := by
      have hdecomp :
          (48600 * AppendixA3Lemma75.finalAlphaDen + 2700) *
              width =
            48600 * AppendixA3Lemma75.finalAlphaDen * width +
              2700 * width := by ring
      rw [hdecomp] at hscaledBoundary
      omega
    let Gamma0 := boundary \ T
    have hGamma0Aug :
        Gamma0 ⊆
          AppendixA3ClusterSplit.augmentedBoundaryVertices H Y T := by
      intro v hv
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hv).1
    have hGamma0Local :
        Section46.ScaledEdgeWellLinkedIn H Y Gamma0
          1 AppendixA3Lemma75.finalAlphaDen :=
      hYwell.mono_terminals hGamma0Aug
    have hGamma0 :
        Section46.ScaledEdgeWellLinkedIn H
          (Finset.univ : Finset V) Gamma0
          1 AppendixA3Lemma75.finalAlphaDen :=
      AppendixA3Corollary74.scaledEdgeWellLinkedIn_univ_of_region
        hGamma0Local
    have hdisjoint : Disjoint T Gamma0 := by
      rw [Finset.disjoint_left]
      intro v hvT hvGamma
      exact (Finset.mem_sdiff.mp hvGamma).2 hvT
    obtain ⟨Pedge, hPedgeCard, _hPedgeStay⟩ :=
      AppendixA3Lemma72.lemma_7_2_edgePathPacking
        hTwell hminimal hGamma0 hdisjoint
    have hdenPos :
        0 < 3 * AppendixA3Lemma75.finalAlphaDen := by
      simp [AppendixA3Lemma75.finalAlphaDen]
    have hPedgeLarge : 16200 * width ≤ Pedge.card := by
      rw [hPedgeCard]
      simp only [one_mul]
      apply (Nat.le_div_iff_mul_le hdenPos).2
      simpa only [Gamma0, boundary, show
          16200 * width *
              (3 * AppendixA3Lemma75.finalAlphaDen) =
            48600 * AppendixA3Lemma75.finalAlphaDen * width by ring]
        using hGamma0Large
    obtain ⟨S, U, I, hsourceI, htargetI, hIcard,
        hST, hUGamma, hSeq, hUeq, hIcongestion⟩ :=
      AppendixA3EndpointMatching.exists_synchronizedRouting_of_edgePathPacking
        (Delta := 3) (width := 2700 * width)
        Pedge hdisjoint hdegreeH (by decide)
        (by
          simpa only [show
              2 * 3 * (2700 * width) = 16200 * width by ring]
            using hPedgeLarge)
    subst S
    subst U
    let R :=
      AppendixA3EndpointMatching.toSynchronizedRouting
        Pedge I hsourceI htargetI
    have hScard :
        (I.image fun i =>
            ((Pedge.path i).orient (Pedge.connects i)).source).card =
          2700 * width := by
      rw [Finset.card_image_of_injOn hsourceI, hIcard]
    have hUcard :
        (I.image fun i =>
            ((Pedge.path i).orient (Pedge.connects i)).target).card =
          2700 * width := by
      rw [Finset.card_image_of_injOn htargetI, hIcard]
    have hSindex :
        (I.image fun i =>
            ((Pedge.path i).orient (Pedge.connects i)).source).card =
          Fintype.card {i : Pedge.Index // i ∈ I} := by
      rw [hScard, Fintype.card_coe, hIcard]
    have hUindex :
        (I.image fun i =>
            ((Pedge.path i).orient (Pedge.connects i)).target).card =
          Fintype.card {i : Pedge.Index // i ∈ I} := by
      rw [hUcard, Fintype.card_coe, hIcard]
    have hUboundary :
        (I.image fun i =>
            ((Pedge.path i).orient (Pedge.connects i)).target) ⊆
          boundary :=
      hUGamma.trans Finset.sdiff_subset
    have hhas :
        HasDisjointSTPaths H X Y width :=
      hasDisjoint_of_large_synchronized_boundary_routing
        hwidth hHC hdegreeH hTwell hTnonempty hST hUboundary
        hXY hXmass hkappaLarge R hScard hSindex hUindex
        hIcongestion
    exact exists_cleanPerfect_boundary_of_hasDisjointSTPaths
      hHC hXC hYC hXY hhas

end
end AppendixA3Lemma710
end SimpleGraph

end Lax17Proofs
