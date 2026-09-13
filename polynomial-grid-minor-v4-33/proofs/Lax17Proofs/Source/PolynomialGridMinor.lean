import Lax17Proofs.Source.PolynomialGridMinorBound
import Lax17Proofs.Source.ChekuriChuzhoyTheoremA2Inputs
import Lax17Proofs.Source.HairyPathOfSetsTheorem
import Lax17Proofs.Source.HairyCrossbar
import Lax17Proofs.Source.HairyCrossbarExpander
import Lax17Proofs.Source.CutMatchingGame
import Lax17Proofs.Source.GridMinor
import Lax17Proofs.Source.GridMinorArithmetic

namespace Lax17Proofs

universe u v w

/-!
# Polynomial grid-minor theorem

This file packages the polynomial grid-minor theorem in proof-facing form and
formalizes the main composition of the Chuzhoy--Tan proof.

The broad public wrappers near the end keep the older contract-backed theorem
available.  The long `*_of_A1omega_ChekuriChuzhoy_*` wrappers expose the
current source-route inputs and avoid the broad hairy path-of-sets, crossbar,
and strong-minor contracts when those inputs are supplied.
-/

namespace SimpleGraph
namespace PolynomialGridMinor


/-- If constants satisfy the polynomial grid-minor theorem, then the theorem can
be applied to any graph meeting the corresponding threshold. -/
theorem containsGridMinor_of_constants_spec
    {c1 c2 : ℕ}
    (hconstants :
      0 < c1 ∧ 0 < c2 ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {g : ℕ},
            2 ≤ g →
              polynomialGridMinorTreewidthBound c1 c2 g ≤
                treewidth G →
                  ContainsGridMinor G g)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ}
    (hg : 2 ≤ g)
    (htw :
      polynomialGridMinorTreewidthBound c1 c2 g ≤
        treewidth G) :
    ContainsGridMinor G g :=
  hconstants.2.2 (V := V) G hg htw

/-- The degree-nine threshold is bounded by the degree-ten threshold for
targets at least two. -/
theorem polynomialGridMinorTreewidthBound_le_degree10
    {c1 c2 target : ℕ} (htarget : 2 ≤ target) :
    polynomialGridMinorTreewidthBound c1 c2 target ≤
      polynomialGridMinorTreewidthBound10 c1 c2 target := by
  have htarget_pos : 0 < target :=
    lt_of_lt_of_le (by decide : 0 < 2) htarget
  have hpow : target ^ 9 ≤ target ^ 10 :=
    Nat.pow_le_pow_right htarget_pos (by decide : 9 ≤ 10)
  calc
    polynomialGridMinorTreewidthBound c1 c2 target
        = c1 * target ^ 9 * (Nat.log 2 target) ^ c2 := rfl
    _ ≤ c1 * target ^ 10 * (Nat.log 2 target) ^ c2 :=
        Nat.mul_le_mul_right ((Nat.log 2 target) ^ c2)
          (Nat.mul_le_mul_left c1 hpow)
    _ = polynomialGridMinorTreewidthBound10 c1 c2 target := rfl

/-- Any degree-nine polynomial grid-minor theorem immediately gives the
weaker degree-ten formulation with the same constants. -/
theorem polynomial_grid_minor_theorem_degree10_of_degree9
    (hdegree9 :
      ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {target : ℕ},
            2 ≤ target →
              polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
                ContainsGridMinor G target) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases hdegree9 with ⟨c1, c2, hc1, hc2, hmain⟩
  refine ⟨c1, c2, hc1, hc2, ?_⟩
  intro V _ _ G target htarget htw
  exact hmain G htarget
    (le_trans (polynomialGridMinorTreewidthBound_le_degree10 htarget) htw)

/-- Treewidth-to-hairy-path-of-sets theorem as an explicit input to the
composition proof. -/
def HairyPathOfSetsInput (cHair cHairLog : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w k : ℕ},
      1 < ell →
        1 < w →
          1 < k →
            k ≤ treewidth G →
              cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧
                    MaxDegreeAtMost H 3 ∧
                      Nonempty (HairyPathOfSetsSystem H ell w)

/-- Strong-path-of-sets-minor-to-grid theorem as an explicit input to the
composition proof. -/
def StrongMinorGridInput (cStrong : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w g : ℕ},
      2 ≤ g →
        g ^ 2 ≤ ell →
          g ^ 2 ≤ w →
            CrossbarContract.HasStrongPathOfSetsMinor G ell w →
              ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g'

/-- Chekuri--Chuzhoy Corollary 3.2 supplies the strong-minor-to-grid input
used by the polynomial grid-minor composition. -/
theorem strongMinorGridInput_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ cStrong : ℕ, 0 < cStrong ∧ StrongMinorGridInput.{u} cStrong := by
  rcases
    CrossbarContract.HasStrongPathOfSetsMinor.exists_gridMinor_of_large_of_corollary32Input
      hinput with
    ⟨cStrong, hcStrong, hgrid⟩
  refine ⟨cStrong, hcStrong, ?_⟩
  intro V _ _ G ell w g hg hell hw hminor
  exact hgrid hg hell hw hminor

/-- The split Chekuri--Chuzhoy inputs supply the strong-minor-to-grid input
used by the polynomial grid-minor composition. -/
theorem strongMinorGridInput_of_localRoutingInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ cStrong : ℕ, 0 < cStrong ∧ StrongMinorGridInput.{u} cStrong :=
  strongMinorGridInput_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)


/-- Appendix A.2 plus the formal Appendix A.4 assembly supply the
treewidth-to-hairy input once the degree-three strong path-of-sets ingredient
is provided. -/
theorem exists_hairyPathOfSetsInput_of_appendixA2PaperInputs
    (hinputs :
      ∃ cStrong cStrongLog cSplit : ℕ,
        0 < cStrong ∧
          0 < cStrongLog ∧
            0 < cSplit ∧
              HairyPathOfSetsTheorem.DegreeThreeStrongPathOfSetsInput.{u}
                cStrong cStrongLog cSplit ∧
                HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog := by
  rcases hinputs with
    ⟨cStrong, cStrongLog, cSplit,
      hcStrong, hcStrongLog, hcSplit, hdegree, hsplit⟩
  exact
    HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_paper_inputs
      ⟨cStrong, cStrongLog, cSplit,
        hcStrong, hcStrongLog, hcSplit, hdegree,
          HairyPathOfSetsTheorem.strongPathOfSetsToHairyInput_of_appendixA4SplitInput
            hsplit⟩


/-- Hairy path-of-sets input from the degree-three sparsifier, the reduced
Chekuri--Chuzhoy A.2 route, and the Appendix A.4 split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_sparsifier_ChekuriChuzhoy_cutCore_route_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_cutCore_route_and_appendixA4
    hsparseInput hcut hroute hsplit

/-- Hairy path-of-sets input from the degree-three sparsifier, the
cut-well-linked Theorem 2.21 boundary, the faithful direct Section 4 path
route, and the Appendix A.4 split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_sparsifier_ChekuriChuzhoy_cutCore_pathRoute_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_cutCore_pathRoute_and_appendixA4
    hsparseInput hcut hroute hsplit

/-- Hairy path-of-sets input from the degree-three sparsifier, Lemma 2.17
routability, the cut-matching/AARV embedding source, the Section 4 tree route,
and the Appendix A.4 split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_route_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_route_and_appendixA4
    hsparseInput hroutable hcutMatching hroute hsplit

/-- Hairy path-of-sets input from the degree-three sparsifier, Lemma 2.17
routability, the cut-matching/AARV embedding source, the faithful direct
Section 4 path route, and the Appendix A.4 split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
    (hsparseInput :
      ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {k t : ℕ},
            1 < k →
              k ≤ treewidth G →
                cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_sparsifier_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
    hsparseInput hroutable hcutMatching hroute hsplit

/-- Hairy path-of-sets input from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the faithful
direct Section 4 path route, and the Appendix A.4 split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
    hsparseOmega hroutable hcutMatching hroute hsplit

/-- Hairy path-of-sets input from Theorem A.1 in its paper-shaped Omega form,
the bundled explicit Chekuri--Chuzhoy A.2 source inputs, and the Appendix A.4
split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_theoremA2SourceInputs_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2SourceInputs.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_theoremA2SourceInputs_and_appendixA4
    hsparseOmega hA2 hsplit

/-- Hairy path-of-sets input from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, Theorem 4.6 extraction, and the Appendix A.4
split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_extraction_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_extraction_and_appendixA4
    hsparseOmega hroutable hcutMatching hbuild hextract hsplit

/-- Hairy path-of-sets input from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, the split proof of Theorem 4.6, and the Appendix
A.4 split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_leafExtraction_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_leafExtraction_and_appendixA4
    hsparseOmega hroutable hcutMatching hbuild hdichotomy hleaf hsplit

/-- Hairy path-of-sets input from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, the proved finite-tree dichotomy, the DFS/many-leaves
branch of Theorem 4.6, and the Appendix A.4 split-cluster input. -/
theorem exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_and_appendixA4
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit) :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      HairyPathOfSetsInput.{u} cHair cHairLog :=
  HairyPathOfSetsTheorem.exists_subgraph_hairy_pathOfSets_of_treewidth_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_and_appendixA4
    hsparseOmega hroutable hcutMatching hbuild hleaf hsplit



/-- Section 4 weak crossbar input from the formal Theorem 4.1 proof and the
explicit pseudo-grid branch for Sections 4.2--4.6. -/
theorem exists_crossbarDichotomyInput10_of_section4PseudoGridBranchInput
    {cCross : ℕ} (hcCross : 0 < cCross)
    (hbranch :
      CrossbarTheorem.Section4PseudoGridBranchInput10.{u} cCross) :
    ∃ cCross : ℕ, 0 < cCross ∧
      HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross :=
  HairyPathOfSetsSystem.exists_crossbarDichotomyInput10_of_section4PseudoGridBranchInput
    hcCross hbranch

/-- Section 4 weak crossbar input from the formal Theorem 4.1 proof, the
Section 4.5 weak path-of-sets assembly data, and Section 4.6 strongification
data. -/
theorem exists_crossbarDichotomyInput10_of_section4WeakToStrongAssemblyInput
    {cCross : ℕ} (hcCross : 0 < cCross)
    (hbranch :
      CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross) :
    ∃ cCross : ℕ, 0 < cCross ∧
      HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross :=
  HairyPathOfSetsSystem.exists_crossbarDichotomyInput10_of_section4WeakToStrongAssemblyInput
    hcCross hbranch


/-- Axiom-free graph-theoretic composition from explicit hard inputs.

The assumptions are exactly the pieces supplied elsewhere by contracts:
treewidth-to-hairy, the local crossbar dichotomy, the strong-minor-to-grid
conversion, and the large-case cut-matching/separator provider.  The proof
itself is only the Lean composition of those inputs. -/
theorem gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      (∃ g' : ℕ,
                                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                          ContainsGridMinor G g') ∨
                                        ∃ r' : ℕ,
                                          r ≤ cStrong * r' ∧
                                            ContainsGridMinor G r' := by
  rcases hhairyInput with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases
    HairyPathOfSetsSystem.gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs
      hcrossInput hstrongGrid hlargeData with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hcrossbar⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r hell hw hk htw hhairyLarge hg hr hpow hellGrid
    hwGrid hlarge hscaled
  rcases hhairy G hell hw hk htw hhairyLarge with
    ⟨H, hHG, hmaxDegree, ⟨Hsys⟩⟩
  exact hcrossbar G H Hsys hHG hg hr hpow hmaxDegree hellGrid hwGrid hlarge
    hscaled

/-- Axiom-free graph-theoretic composition from explicit hard inputs, using
the Section 4 `g^10 log g` crossbar input. -/
theorem gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs10
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      (∃ g' : ℕ,
                                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                          ContainsGridMinor G g') ∨
                                        ∃ r' : ℕ,
                                          r ≤ cStrong * r' ∧
                                            ContainsGridMinor G r' := by
  rcases hhairyInput with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases
    HairyPathOfSetsSystem.gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs10
      hcrossInput hstrongGrid hlargeData with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hcrossbar⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r hell hw hk htw hhairyLarge hg hr hpow hellGrid
    hwGrid hlarge hscaled
  rcases hhairy G hell hw hk htw hhairyLarge with
    ⟨H, hHG, hmaxDegree, ⟨Hsys⟩⟩
  exact hcrossbar G H Hsys hHG hg hr hpow hmaxDegree hellGrid hwGrid hlarge
    hscaled

/-- Axiom-free graph-theoretic composition from explicit hard inputs, using
the target-provider large-case route.  This is the explicit-input analogue of
`gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders`. -/
theorem gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      (∃ g' : ℕ,
                                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                          ContainsGridMinor G g') ∨
                                        ∃ r' : ℕ,
                                          r ≤ cStrong * r' ∧
                                            ContainsGridMinor G r' := by
  rcases hhairyInput with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases
    HairyPathOfSetsSystem.gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
      hcrossInput hstrongGrid hproviders with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hcrossbar⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r hell hw hk htw hhairyLarge hg hr hpow hellGrid
    hwGrid hlarge hscaled
  rcases hhairy G hell hw hk htw hhairyLarge with
    ⟨H, hHG, hmaxDegree, ⟨Hsys⟩⟩
  exact hcrossbar G H Hsys hHG hg hr hpow hmaxDegree hellGrid hwGrid hlarge
    hscaled

/-- Explicit-input composition after internalizing the Theorem 8.1 target-size
arithmetic. -/
theorem gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      (∃ g' : ℕ,
                                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                          ContainsGridMinor G g') ∨
                                        ∃ r' : ℕ,
                                          r ≤ cStrong * r' ∧
                                            ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput hstrongGrid
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact ⟨cRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound,
        hcRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos cRound,
        hunbundled, HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
          cRound⟩)

/-- Axiom-free graph-theoretic composition where the strong-minor branch is
supplied directly by Chekuri--Chuzhoy Corollary 3.2. -/
theorem gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_chekuriInput
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      (∃ g' : ℕ,
                                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                          ContainsGridMinor G g') ∨
                                        ∃ r' : ℕ,
                                          r ≤ cStrong * r' ∧
                                            ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs
    hhairyInput hcrossInput
    (strongMinorGridInput_of_corollary32Input hchekuri) hlargeData










/-- Cancel a positive multiplicative constant from both sides of a natural
number inequality. -/
theorem le_of_const_mul_le_const_mul {c a b : ℕ}
    (hc : 0 < c) (h : c * a ≤ c * b) : a ≤ b :=
  Nat.le_of_mul_le_mul_left h hc

/-- If a target grid order satisfies the direct crossbar-assembly lower bound,
then it is no larger than the grid order produced by that branch. -/
theorem le_gridOrder_of_direct_branch_bound {c g target g' : ℕ}
    (hc : 0 < c) (hg : 2 ≤ g)
    (htarget : c * target * (Nat.log 2 g) ^ 2 ≤ g)
    (hproduced : g ≤ c * g' * (Nat.log 2 g) ^ 2) :
    target ≤ g' := by
  have hlog : 0 < (Nat.log 2 g) ^ 2 :=
    Nat.pow_pos (Nat.log_pos (by decide : 1 < 2) hg)
  have hfactor : 0 < c * (Nat.log 2 g) ^ 2 := Nat.mul_pos hc hlog
  have hscaled :
      (c * (Nat.log 2 g) ^ 2) * target ≤
        (c * (Nat.log 2 g) ^ 2) * g' := by
    calc
      (c * (Nat.log 2 g) ^ 2) * target = c * target * (Nat.log 2 g) ^ 2 := by
        ac_rfl
      _ ≤ g := htarget
      _ ≤ c * g' * (Nat.log 2 g) ^ 2 := hproduced
      _ = (c * (Nat.log 2 g) ^ 2) * g' := by
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled hfactor

/-- Numerical parameter package for the proof skeleton of the polynomial
grid-minor theorem.

For fixed constants and target grid order, this records the choices of the
hairy path-of-sets parameters (`ell`, `w`, `k`) and the crossbar parameters
(`g`, `r`) together with exactly the inequalities consumed by
`containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter`.
-/
structure ParameterChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Hairy path-of-sets length. -/
  ell : ℕ
  /-- Hairy path-of-sets width. -/
  w : ℕ
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Crossbar parameter, required to be a power of two. -/
  g : ℕ
  /-- Strong path-of-sets parameter used in the second branch. -/
  r : ℕ
  /-- The hairy-system length is nontrivial. -/
  ell_gt_one : 1 < ell
  /-- The hairy-system width is nontrivial. -/
  w_gt_one : 1 < w
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The Chuzhoy--Tan Theorem 2.3 numerical hypothesis. -/
  hairy_large :
    cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k
  /-- The crossbar parameter is at least two. -/
  g_ge_two : 2 ≤ g
  /-- The strong-branch parameter is at least two. -/
  r_ge_two : 2 ≤ r
  /-- The crossbar parameter is a power of two. -/
  g_powerOfTwo : CrossbarContract.IsPowerOfTwo g
  /-- There are enough clusters for the crossbar-grid assembly theorem. -/
  grid_length : cGrid * Nat.log 2 g ≤ ell
  /-- The system is wide enough for `g^2` crossbar paths. -/
  grid_width : g ^ 2 ≤ w
  /-- The local crossbar theorem's width lower bound. -/
  crossbar_width : 2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w
  /-- The strong branch can be thinned to parameter `r`. -/
  strong_scale : cCross * r ^ 2 ≤ g ^ 2
  /-- The direct branch produces a grid at least as large as `target`. -/
  target_direct : cGrid * target * (Nat.log 2 g) ^ 2 ≤ g
  /-- The strong branch produces a grid at least as large as `target`. -/
  target_strong : cStrong * target ≤ r

namespace ParameterChoice

/-- A numerical parameter choice remains valid when the available treewidth
bound is increased. -/
def mono_treewidth {cHair cHairLog cCross cGrid cStrong target tw tw' : ℕ}
    (P : ParameterChoice cHair cHairLog cCross cGrid cStrong target tw)
    (htw : tw ≤ tw') :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw' where
  ell := P.ell
  w := P.w
  k := P.k
  g := P.g
  r := P.r
  ell_gt_one := P.ell_gt_one
  w_gt_one := P.w_gt_one
  k_gt_one := P.k_gt_one
  k_le_treewidth := le_trans P.k_le_treewidth htw
  hairy_large := P.hairy_large
  g_ge_two := P.g_ge_two
  r_ge_two := P.r_ge_two
  g_powerOfTwo := P.g_powerOfTwo
  grid_length := P.grid_length
  grid_width := P.grid_width
  crossbar_width := P.crossbar_width
  strong_scale := P.strong_scale
  target_direct := P.target_direct
  target_strong := P.target_strong

end ParameterChoice

/-- Canonical path-of-sets length used by the numerical skeleton for a rounded
crossbar scale. -/
def lengthScale (cGrid n : ℕ) : ℕ :=
  max 2 (cGrid * Nat.log 2 (GridMinorArithmetic.powTwoFloor n))

/-- A simpler upper bound for `lengthScale`, using the unrounded scale. -/
def coarseLengthScale (cGrid n : ℕ) : ℕ :=
  max 2 (cGrid * Nat.log 2 n)

/-- A polynomial upper bound for `coarseLengthScale`. -/
def polynomialLengthScale (cGrid n : ℕ) : ℕ :=
  max 2 (cGrid * n)

/-- The canonical length is nontrivial. -/
theorem lengthScale_gt_one (cGrid n : ℕ) :
    1 < lengthScale cGrid n :=
  lt_of_lt_of_le (by decide : 1 < 2) (le_max_left 2 _)

/-- The canonical length satisfies the crossbar-grid length requirement. -/
theorem lengthScale_grid_length (cGrid n : ℕ) :
    cGrid * Nat.log 2 (GridMinorArithmetic.powTwoFloor n) ≤
      lengthScale cGrid n :=
  le_max_right 2 _

/-- The canonical length is bounded by the same expression using the unrounded
scale's logarithm. -/
theorem lengthScale_le_unrounded (cGrid n : ℕ) (hn : 2 ≤ n) :
    lengthScale cGrid n ≤ coarseLengthScale cGrid n := by
  apply max_le
  · exact le_max_left _ _
  · exact le_trans
      (Nat.mul_le_mul_left cGrid (GridMinorArithmetic.log_powTwoFloor_le_log hn))
      (le_max_right 2 _)

/-- The coarse length is bounded by a linear expression in the unrounded
scale. -/
theorem coarseLengthScale_le_linear (cGrid n : ℕ) :
    coarseLengthScale cGrid n ≤ polynomialLengthScale cGrid n := by
  apply max_le
  · exact le_max_left _ _
  · exact le_trans (Nat.mul_le_mul_left cGrid (Nat.log_le_self 2 n))
      (le_max_right 2 _)

/-- The polynomial length scale is bounded by `(max 2 cGrid) * n` once
`n >= 1`. -/
theorem polynomialLengthScale_le_const_mul
    {cGrid n : ℕ} (hn : 1 ≤ n) :
    polynomialLengthScale cGrid n ≤ max 2 cGrid * n := by
  apply max_le
  · calc
      2 = 2 * 1 := by simp
      _ ≤ max 2 cGrid * n :=
        Nat.mul_le_mul (le_max_left 2 cGrid) hn
  · exact Nat.mul_le_mul_right n (le_max_right 2 cGrid)

/-- Canonical path-of-sets width used by the numerical skeleton for a rounded
crossbar scale. -/
def widthScale (n : ℕ) : ℕ :=
  max 2
    (max ((GridMinorArithmetic.powTwoFloor n) ^ 2)
      (2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 9 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n)))

/-- A simpler upper bound for `widthScale`, using the unrounded scale. -/
def coarseWidthScale (n : ℕ) : ℕ :=
  max 2 (max (n ^ 2) (2 ^ 22 * n ^ 9 * Nat.log 2 n))

/-- A polynomial upper bound for `coarseWidthScale`. -/
def polynomialWidthScale (n : ℕ) : ℕ :=
  max 2 (max (n ^ 2) (2 ^ 22 * n ^ 10))

/-- The canonical width is nontrivial. -/
theorem widthScale_gt_one (n : ℕ) :
    1 < widthScale n :=
  lt_of_lt_of_le (by decide : 1 < 2) (le_max_left 2 _)

/-- The canonical width contains the square of the rounded crossbar scale. -/
theorem widthScale_grid_width (n : ℕ) :
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ widthScale n :=
  le_trans (le_max_left _ _ ) (le_max_right 2 _)

/-- The canonical width satisfies the local crossbar theorem's width lower
bound. -/
theorem widthScale_crossbar_width (n : ℕ) :
    2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 9 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n) ≤
      widthScale n :=
  le_trans (le_max_right _ _) (le_max_right 2 _)

/-- The rounded crossbar width term is bounded by the corresponding unrounded
term. -/
theorem rounded_crossbar_width_le_unrounded (n : ℕ) (hn : 2 ≤ n) :
    2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 9 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n) ≤
      2 ^ 22 * n ^ 9 * Nat.log 2 n := by
  calc
    2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 9 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n)
        =
      2 ^ 22 * ((GridMinorArithmetic.powTwoFloor n) ^ 9 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n)) := by
        ac_rfl
    _ ≤ 2 ^ 22 * (n ^ 9 * Nat.log 2 n) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul
        (GridMinorArithmetic.pow_powTwoFloor_le_pow hn)
        (GridMinorArithmetic.log_powTwoFloor_le_log hn))
    _ = 2 ^ 22 * n ^ 9 * Nat.log 2 n := by
      ac_rfl

/-- The canonical width is bounded by the simpler unrounded width expression. -/
theorem widthScale_le_unrounded (n : ℕ) (hn : 2 ≤ n) :
    widthScale n ≤ coarseWidthScale n := by
  apply max_le
  · exact le_max_left _ _
  · apply max_le
    · exact le_trans (GridMinorArithmetic.pow_powTwoFloor_le_pow hn)
        (le_trans (le_max_left _ _) (le_max_right 2 _))
    · exact le_trans (rounded_crossbar_width_le_unrounded n hn)
        (le_trans (le_max_right _ _) (le_max_right 2 _))

/-- The coarse width is bounded by a fixed degree-ten expression in the
unrounded scale. -/
theorem coarseWidthScale_le_polynomial (n : ℕ) :
    coarseWidthScale n ≤ polynomialWidthScale n := by
  have hterm :
      2 ^ 22 * n ^ 9 * Nat.log 2 n ≤ 2 ^ 22 * n ^ 10 := by
    calc
      2 ^ 22 * n ^ 9 * Nat.log 2 n =
          2 ^ 22 * (n ^ 9 * Nat.log 2 n) := by
        ac_rfl
      _ ≤ 2 ^ 22 * (n ^ 9 * n) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_le_self 2 n))
      _ = 2 ^ 22 * n ^ 10 := by
        rw [← Nat.pow_succ n 9]
  rw [coarseWidthScale, polynomialWidthScale]
  apply max_le
  · exact le_max_left _ _
  · apply max_le
    · exact le_trans (le_max_left (n ^ 2) (2 ^ 22 * n ^ 10))
        (le_max_right 2 _)
    · exact le_trans hterm
        (le_trans (le_max_right (n ^ 2) (2 ^ 22 * n ^ 10))
          (le_max_right 2 _))

/-- For `n >= 1`, the polynomial width scale is bounded by the degree-ten
monomial `2^22 * n^10`. -/
theorem polynomialWidthScale_le_monomial {n : ℕ} (hn : 1 ≤ n) :
    polynomialWidthScale n ≤ 2 ^ 22 * n ^ 10 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
  have hn2_le_hn10 : n ^ 2 ≤ n ^ 10 :=
    Nat.pow_le_pow_right hnpos (by decide : 2 ≤ 10)
  have hconst : 2 ≤ 2 ^ 22 := by decide
  have hn10_pos : 1 ≤ n ^ 10 := Nat.succ_le_of_lt (Nat.pow_pos hnpos)
  rw [polynomialWidthScale]
  apply max_le
  · calc
      2 = 2 * 1 := by simp
      _ ≤ 2 ^ 22 * n ^ 10 := Nat.mul_le_mul hconst hn10_pos
  · apply max_le
    · exact le_trans hn2_le_hn10
        (by
          calc
            n ^ 10 = 1 * n ^ 10 := by simp
            _ ≤ 2 ^ 22 * n ^ 10 :=
              Nat.mul_le_mul_right (n ^ 10) (by decide : 1 ≤ 2 ^ 22))
    · exact le_rfl

/-- The exact hairy-system size expression is bounded by the coarser
unrounded expression. -/
theorem hairy_size_le_coarse
    (cHair cHairLog cGrid k n : ℕ) (hn : 2 ≤ n) :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      cHair * coarseWidthScale n * (coarseLengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
  have hw := widthScale_le_unrounded n hn
  have hell := lengthScale_le_unrounded cGrid n hn
  gcongr

/-- A coarse hairy-system inequality implies the exact one used by the
parameter package. -/
theorem hairy_large_of_coarse
    {cHair cHairLog cGrid k n : ℕ} (hn : 2 ≤ n)
    (h :
      cHair * coarseWidthScale n * (coarseLengthScale cGrid n) ^ 50 *
          (Nat.log 2 k) ^ cHairLog < k) :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k :=
  lt_of_le_of_lt (hairy_size_le_coarse cHair cHairLog cGrid k n hn) h

/-- The coarse hairy-system size expression is bounded by the polynomial
length/width expression. -/
theorem coarse_hairy_size_le_polynomial
    (cHair cHairLog cGrid k n : ℕ) :
    cHair * coarseWidthScale n * (coarseLengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      cHair * polynomialWidthScale n * (polynomialLengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
  have hw := coarseWidthScale_le_polynomial n
  have hell := coarseLengthScale_le_linear cGrid n
  gcongr

/-- A polynomial upper-bound hairy-system inequality implies the exact
hairy-system inequality used by the proof skeleton. -/
theorem hairy_large_of_polynomial
    {cHair cHairLog cGrid k n : ℕ} (hn : 2 ≤ n)
    (h :
      cHair * polynomialWidthScale n * (polynomialLengthScale cGrid n) ^ 50 *
          (Nat.log 2 k) ^ cHairLog < k) :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k :=
  hairy_large_of_coarse hn
    (lt_of_le_of_lt (coarse_hairy_size_le_polynomial cHair cHairLog cGrid k n) h)

/-- The coarse length scale is bounded by a constant times `log n`, once
`n >= 2`. -/
theorem coarseLengthScale_le_logarithmic
    (cGrid : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    coarseLengthScale cGrid n ≤ max 2 cGrid * Nat.log 2 n := by
  have hlog_pos : 0 < Nat.log 2 n :=
    Nat.log_pos (by decide : 1 < 2) hn
  have hlog_one : 1 ≤ Nat.log 2 n := Nat.succ_le_of_lt hlog_pos
  rw [coarseLengthScale]
  apply max_le
  · calc
      2 = 2 * 1 := by simp
      _ ≤ max 2 cGrid * Nat.log 2 n :=
        Nat.mul_le_mul (le_max_left 2 cGrid) hlog_one
  · exact Nat.mul_le_mul_right (Nat.log 2 n) (le_max_right 2 cGrid)

/-- The coarse width scale is bounded by the logarithmic width term
`2^22 * n^9 * log n`, once `n >= 2`. -/
theorem coarseWidthScale_le_logarithmic {n : ℕ} (hn : 2 ≤ n) :
    coarseWidthScale n ≤ 2 ^ 22 * n ^ 9 * Nat.log 2 n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hlog_pos : 0 < Nat.log 2 n :=
    Nat.log_pos (by decide : 1 < 2) hn
  have hlog_one : 1 ≤ Nat.log 2 n := Nat.succ_le_of_lt hlog_pos
  have hn9_log_one : 1 ≤ n ^ 9 * Nat.log 2 n :=
    Nat.mul_le_mul (Nat.succ_le_of_lt (Nat.pow_pos hnpos)) hlog_one
  have htwo_le_const : 2 ≤ 2 ^ 22 := by decide
  have htwo_le_term : 2 ≤ 2 ^ 22 * n ^ 9 * Nat.log 2 n := by
    calc
      2 = 2 * 1 := by simp
      _ ≤ 2 ^ 22 * (n ^ 9 * Nat.log 2 n) :=
        Nat.mul_le_mul htwo_le_const hn9_log_one
      _ = 2 ^ 22 * n ^ 9 * Nat.log 2 n := by
        ac_rfl
  have hn2_le_term : n ^ 2 ≤ 2 ^ 22 * n ^ 9 * Nat.log 2 n := by
    calc
      n ^ 2 ≤ n ^ 9 :=
        Nat.pow_le_pow_right hnpos (by decide : 2 ≤ 9)
      _ = n ^ 9 * 1 := by simp
      _ ≤ n ^ 9 * Nat.log 2 n := Nat.mul_le_mul_left _ hlog_one
      _ = 1 * (n ^ 9 * Nat.log 2 n) := by simp
      _ ≤ 2 ^ 22 * (n ^ 9 * Nat.log 2 n) :=
        Nat.mul_le_mul_right _ (by decide : 1 ≤ 2 ^ 22)
      _ = 2 ^ 22 * n ^ 9 * Nat.log 2 n := by
        ac_rfl
  rw [coarseWidthScale]
  apply max_le
  · exact htwo_le_term
  · apply max_le
    · exact hn2_le_term
    · exact le_rfl

/-- The exact hairy-system size expression is bounded by the logarithmic
width/length expression that preserves the `n^9` exponent. -/
theorem hairy_size_le_logarithmic
    (cHair cHairLog cGrid k n : ℕ) (hn : 2 ≤ n) :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      cHair * (2 ^ 22 * n ^ 9 * Nat.log 2 n) *
        (max 2 cGrid * Nat.log 2 n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
  have hw : widthScale n ≤ 2 ^ 22 * n ^ 9 * Nat.log 2 n :=
    le_trans (widthScale_le_unrounded n hn) (coarseWidthScale_le_logarithmic hn)
  have hell :
      lengthScale cGrid n ≤ max 2 cGrid * Nat.log 2 n :=
    le_trans (lengthScale_le_unrounded cGrid n hn)
      (coarseLengthScale_le_logarithmic cGrid hn)
  gcongr

/-- A logarithmic upper-bound hairy-system inequality implies the exact
hairy-system inequality used by the proof skeleton. -/
theorem hairy_large_of_logarithmic
    {cHair cHairLog cGrid k n : ℕ} (hn : 2 ≤ n)
    (h :
      cHair * (2 ^ 22 * n ^ 9 * Nat.log 2 n) *
        (max 2 cGrid * Nat.log 2 n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k) :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k :=
  lt_of_le_of_lt (hairy_size_le_logarithmic cHair cHairLog cGrid k n hn) h

/-- The constant factor left after normalizing the logarithmic and monomial
hairy-system size bounds. -/
def exponentHairyConstant (cHair cGrid : ℕ) : ℕ :=
  cHair * 2 ^ 22 * (max 2 cGrid) ^ 50

/-- The logarithmic hairy-size upper bound can be written as one constant
times `n^9 * (log n)^51`. -/
theorem logarithmic_hairy_size_eq_normalized
    (cHair cHairLog cGrid k n : ℕ) :
    cHair * (2 ^ 22 * n ^ 9 * Nat.log 2 n) *
        (max 2 cGrid * Nat.log 2 n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog =
      exponentHairyConstant cHair cGrid * n ^ 9 *
        (Nat.log 2 n) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
  rw [mul_pow]
  have hlog :
      Nat.log 2 n * (Nat.log 2 n) ^ 50 =
        (Nat.log 2 n) ^ 51 := by
    rw [show (51 : ℕ) = 1 + 50 by decide, pow_add]
    simp
  calc
    cHair * (2 ^ 22 * n ^ 9 * Nat.log 2 n) *
        ((max 2 cGrid) ^ 50 * (Nat.log 2 n) ^ 50) *
        (Nat.log 2 k) ^ cHairLog
        =
      cHair * 2 ^ 22 * (max 2 cGrid) ^ 50 * n ^ 9 *
        (Nat.log 2 n * (Nat.log 2 n) ^ 50) *
        (Nat.log 2 k) ^ cHairLog := by
        ac_rfl
    _ =
      exponentHairyConstant cHair cGrid * n ^ 9 *
        (Nat.log 2 n) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
        rw [hlog, exponentHairyConstant]

/-- A normalized logarithmic hairy-system inequality implies the exact
hairy-system inequality used by the proof skeleton. -/
theorem hairy_large_of_logarithmic_normalized
    {cHair cHairLog cGrid k n : ℕ} (hn : 2 ≤ n)
    (h :
      exponentHairyConstant cHair cGrid * n ^ 9 *
        (Nat.log 2 n) ^ 51 *
        (Nat.log 2 k) ^ cHairLog < k) :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k := by
  apply hairy_large_of_logarithmic hn
  rwa [logarithmic_hairy_size_eq_normalized]

/-- The polynomial hairy-size expression is bounded by a monomial in the
unrounded scale `n`, up to the remaining logarithmic factor in `k`. -/
theorem polynomial_hairy_size_le_monomial
    (cHair cHairLog cGrid k n : ℕ) (hn : 1 ≤ n) :
    cHair * polynomialWidthScale n * (polynomialLengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      cHair * (2 ^ 22 * n ^ 10) * ((max 2 cGrid * n) ^ 50) *
        (Nat.log 2 k) ^ cHairLog := by
  have hw := polynomialWidthScale_le_monomial hn
  have hell := polynomialLengthScale_le_const_mul (cGrid := cGrid) hn
  gcongr

/-- A monomial upper-bound hairy-system inequality implies the exact
hairy-system inequality used by the proof skeleton. -/
theorem hairy_large_of_monomial
    {cHair cHairLog cGrid k n : ℕ} (hn : 2 ≤ n)
    (h :
      cHair * (2 ^ 22 * n ^ 10) * ((max 2 cGrid * n) ^ 50) *
          (Nat.log 2 k) ^ cHairLog < k) :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k :=
  hairy_large_of_polynomial hn
    (lt_of_le_of_lt
      (polynomial_hairy_size_le_monomial cHair cHairLog cGrid k n
        (le_trans (by decide : 1 ≤ 2) hn))
      h)

/-- At the power-of-two scale `2^m`, the monomial hairy-system size has a
single exponential factor `2^(60*m)`. -/
theorem monomial_hairy_size_eq_exponent
    (cHair cHairLog cGrid k m : ℕ) :
    cHair * (2 ^ 22 * (2 ^ m) ^ 10) *
        ((max 2 cGrid * (2 ^ m)) ^ 50) *
      (Nat.log 2 k) ^ cHairLog =
        exponentHairyConstant cHair cGrid * 2 ^ (m * 60) *
          (Nat.log 2 k) ^ cHairLog := by
  rw [GridMinorArithmetic.two_pow_pow m 10]
  rw [mul_pow]
  rw [GridMinorArithmetic.two_pow_pow m 50]
  calc
    cHair * (2 ^ 22 * 2 ^ (m * 10)) *
        ((max 2 cGrid) ^ 50 * 2 ^ (m * 50)) *
      (Nat.log 2 k) ^ cHairLog
        =
      cHair * 2 ^ 22 * (max 2 cGrid) ^ 50 *
        (2 ^ (m * 10) * 2 ^ (m * 50)) *
      (Nat.log 2 k) ^ cHairLog := by
        ac_rfl
    _ =
      cHair * 2 ^ 22 * (max 2 cGrid) ^ 50 *
        2 ^ (m * 10 + m * 50) *
      (Nat.log 2 k) ^ cHairLog := by
        rw [← pow_add]
    _ =
      exponentHairyConstant cHair cGrid * 2 ^ (m * 60) *
        (Nat.log 2 k) ^ cHairLog := by
        have hmul : m * 10 + m * 50 = m * 60 := by omega
        rw [hmul, exponentHairyConstant]

/-- An exponent-normalized hairy-system inequality implies the monomial
hairy-system inequality. -/
theorem hairy_large_of_exponent
    {cHair cHairLog cGrid k m : ℕ}
    (h :
      exponentHairyConstant cHair cGrid * 2 ^ (m * 60) *
          (Nat.log 2 k) ^ cHairLog < k) :
    cHair * (2 ^ 22 * (2 ^ m) ^ 10) *
        ((max 2 cGrid * (2 ^ m)) ^ 50) *
      (Nat.log 2 k) ^ cHairLog < k := by
  rwa [monomial_hairy_size_eq_exponent]

/-- Parameter package where the crossbar scale is given by an arbitrary natural
number `n`; it is converted to the required power of two by taking
`GridMinorArithmetic.powTwoFloor n`.

The raw direct and strong-branch inequalities are stated with an extra factor
of two.  The rounding lemmas in `GridMinorArithmetic` remove this factor when
passing from `n` to the largest power of two below `n`.
-/
structure RoundedParameterChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Hairy path-of-sets length. -/
  ell : ℕ
  /-- Hairy path-of-sets width. -/
  w : ℕ
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- Strong path-of-sets parameter used in the second branch. -/
  r : ℕ
  /-- The hairy-system length is nontrivial. -/
  ell_gt_one : 1 < ell
  /-- The hairy-system width is nontrivial. -/
  w_gt_one : 1 < w
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The Chuzhoy--Tan Theorem 2.3 numerical hypothesis. -/
  hairy_large :
    cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The strong-branch parameter is at least two. -/
  r_ge_two : 2 ≤ r
  /-- There are enough clusters for the rounded crossbar-grid assembly theorem. -/
  grid_length :
    cGrid * Nat.log 2 (GridMinorArithmetic.powTwoFloor n) ≤ ell
  /-- The system is wide enough for the rounded crossbar paths. -/
  grid_width : (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ w
  /-- The local crossbar theorem's width lower bound after rounding. -/
  crossbar_width :
    2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 9 *
      Nat.log 2 (GridMinorArithmetic.powTwoFloor n) ≤ w
  /-- The rounded strong branch can be thinned to parameter `r`. -/
  strong_scale_raw : 2 * (cCross * r ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n
  /-- The strong branch produces a grid at least as large as `target`. -/
  target_strong : cStrong * target ≤ r

namespace RoundedParameterChoice

/-- Convert an unrounded parameter package into the exact parameter package
consumed by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : RoundedParameterChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw where
  ell := P.ell
  w := P.w
  k := P.k
  g := GridMinorArithmetic.powTwoFloor P.n
  r := P.r
  ell_gt_one := P.ell_gt_one
  w_gt_one := P.w_gt_one
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large := P.hairy_large
  g_ge_two := GridMinorArithmetic.two_le_powTwoFloor P.n_ge_two
  r_ge_two := P.r_ge_two
  g_powerOfTwo := GridMinorArithmetic.isPowerOfTwo_powTwoFloor P.n
  grid_length := P.grid_length
  grid_width := P.grid_width
  crossbar_width := P.crossbar_width
  strong_scale :=
    GridMinorArithmetic.le_powTwoFloor_sq_of_two_mul_le
      P.n_ge_two P.strong_scale_raw
  target_direct :=
    GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
      P.n_ge_two P.target_direct_raw
  target_strong := P.target_strong

end RoundedParameterChoice

/-- Parameter package where the length and width are the canonical scales
derived from the unrounded crossbar scale `n`. -/
structure ScaleParameterChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- Strong path-of-sets parameter used in the second branch. -/
  r : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The Chuzhoy--Tan Theorem 2.3 numerical hypothesis with canonical
  `ell` and `w`. -/
  hairy_large :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The strong-branch parameter is at least two. -/
  r_ge_two : 2 ≤ r
  /-- The rounded strong branch can be thinned to parameter `r`. -/
  strong_scale_raw : 2 * (cCross * r ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n
  /-- The strong branch produces a grid at least as large as `target`. -/
  target_strong : cStrong * target ≤ r

namespace ScaleParameterChoice

/-- Expand a scale-only parameter package to the rounded parameter package. -/
def toRoundedParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : ScaleParameterChoice cHair cHairLog cCross cGrid cStrong target tw) :
    RoundedParameterChoice cHair cHairLog cCross cGrid cStrong target tw where
  ell := lengthScale cGrid P.n
  w := widthScale P.n
  k := P.k
  n := P.n
  r := P.r
  ell_gt_one := lengthScale_gt_one cGrid P.n
  w_gt_one := widthScale_gt_one P.n
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large := P.hairy_large
  n_ge_two := P.n_ge_two
  r_ge_two := P.r_ge_two
  grid_length := lengthScale_grid_length cGrid P.n
  grid_width := widthScale_grid_width P.n
  crossbar_width := widthScale_crossbar_width P.n
  strong_scale_raw := P.strong_scale_raw
  target_direct_raw := P.target_direct_raw
  target_strong := P.target_strong

end ScaleParameterChoice

/-- Scale-only parameter package using the sharp square-form rounding condition
for the strong branch.  This avoids the overly strong sufficient condition
`cCross * r^2 <= O(n)` and instead uses `cCross * r^2 <= O(n^2)`, which is the
condition compatible with a crossbar scale linear in the target grid order. -/
structure SharpScaleParameterChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- Strong path-of-sets parameter used in the second branch. -/
  r : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The Chuzhoy--Tan Theorem 2.3 numerical hypothesis with canonical
  `ell` and `w`. -/
  hairy_large :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The strong-branch parameter is at least two. -/
  r_ge_two : 2 ≤ r
  /-- The rounded strong branch can be thinned to parameter `r`, using the
  square-form rounding lemma. -/
  strong_scale_raw_sq : 4 * (cCross * r ^ 2) ≤ n ^ 2
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n
  /-- The strong branch produces a grid at least as large as `target`. -/
  target_strong : cStrong * target ≤ r

namespace SharpScaleParameterChoice

/-- Sharp scale choices imply the exact parameter package consumed by the
graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : SharpScaleParameterChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw where
  ell := lengthScale cGrid P.n
  w := widthScale P.n
  k := P.k
  g := GridMinorArithmetic.powTwoFloor P.n
  r := P.r
  ell_gt_one := lengthScale_gt_one cGrid P.n
  w_gt_one := widthScale_gt_one P.n
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large := P.hairy_large
  g_ge_two := GridMinorArithmetic.two_le_powTwoFloor P.n_ge_two
  r_ge_two := P.r_ge_two
  g_powerOfTwo := GridMinorArithmetic.isPowerOfTwo_powTwoFloor P.n
  grid_length := lengthScale_grid_length cGrid P.n
  grid_width := widthScale_grid_width P.n
  crossbar_width := widthScale_crossbar_width P.n
  strong_scale :=
    GridMinorArithmetic.le_powTwoFloor_sq_of_four_mul_le_sq
      P.strong_scale_raw_sq
  target_direct :=
    GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
      P.n_ge_two P.target_direct_raw
  target_strong := P.target_strong

end SharpScaleParameterChoice

/-- Scale-only parameter package whose hairy-system inequality uses the sharp
logarithmic width/length bound `n^9 * (log n)^51`, instead of the coarse
monomial `n^60`. -/
structure LogarithmicScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- Strong path-of-sets parameter used in the second branch. -/
  r : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Logarithmic upper-bound version of the Chuzhoy--Tan Theorem 2.3
  numerical hypothesis. -/
  hairy_large_logarithmic :
    cHair * (2 ^ 22 * n ^ 9 * Nat.log 2 n) *
      (max 2 cGrid * Nat.log 2 n) ^ 50 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The strong-branch parameter is at least two. -/
  r_ge_two : 2 ≤ r
  /-- The rounded strong branch can be thinned to parameter `r`. -/
  strong_scale_raw : 2 * (cCross * r ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n
  /-- The strong branch produces a grid at least as large as `target`. -/
  target_strong : cStrong * target ≤ r

namespace LogarithmicScaleChoice

/-- Logarithmic scale choices imply ordinary scale-only choices. -/
def toScaleParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : LogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ScaleParameterChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  n := P.n
  r := P.r
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large :=
    hairy_large_of_logarithmic P.n_ge_two P.hairy_large_logarithmic
  n_ge_two := P.n_ge_two
  r_ge_two := P.r_ge_two
  strong_scale_raw := P.strong_scale_raw
  target_direct_raw := P.target_direct_raw
  target_strong := P.target_strong

/-- Logarithmic scale choices imply the exact parameter package consumed by
the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : LogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toScaleParameterChoice.toRoundedParameterChoice.toParameterChoice

end LogarithmicScaleChoice

/-- Scale-only parameter package whose hairy-system inequality is stated in
the normalized logarithmic form
`constant * n^9 * (log n)^51 * (log k)^cHairLog < k`. -/
structure NormalizedLogarithmicScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- Strong path-of-sets parameter used in the second branch. -/
  r : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Normalized logarithmic version of the Chuzhoy--Tan Theorem 2.3
  numerical hypothesis. -/
  hairy_large_logarithmic_normalized :
    exponentHairyConstant cHair cGrid * n ^ 9 *
      (Nat.log 2 n) ^ 51 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The strong-branch parameter is at least two. -/
  r_ge_two : 2 ≤ r
  /-- The rounded strong branch can be thinned to parameter `r`. -/
  strong_scale_raw : 2 * (cCross * r ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n
  /-- The strong branch produces a grid at least as large as `target`. -/
  target_strong : cStrong * target ≤ r

namespace NormalizedLogarithmicScaleChoice

/-- Normalized logarithmic choices imply the expanded logarithmic choices. -/
def toLogarithmicScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      NormalizedLogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    LogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  n := P.n
  r := P.r
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_logarithmic := by
    rw [logarithmic_hairy_size_eq_normalized]
    exact P.hairy_large_logarithmic_normalized
  n_ge_two := P.n_ge_two
  r_ge_two := P.r_ge_two
  strong_scale_raw := P.strong_scale_raw
  target_direct_raw := P.target_direct_raw
  target_strong := P.target_strong

/-- Normalized logarithmic choices imply ordinary scale-only choices. -/
def toScaleParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      NormalizedLogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    ScaleParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toLogarithmicScaleChoice.toScaleParameterChoice

/-- Normalized logarithmic choices imply the exact parameter package consumed
by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      NormalizedLogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toLogarithmicScaleChoice.toParameterChoice

end NormalizedLogarithmicScaleChoice

/-- Canonical strong-branch scale for a target grid order. -/
def strongScale (cStrong target : ℕ) : ℕ :=
  max 2 (cStrong * target)

/-- The canonical strong scale is at least two. -/
theorem strongScale_ge_two (cStrong target : ℕ) :
    2 ≤ strongScale cStrong target :=
  le_max_left 2 _

/-- The canonical strong scale dominates `cStrong * target`. -/
theorem target_le_strongScale (cStrong target : ℕ) :
    cStrong * target ≤ strongScale cStrong target :=
  le_max_right 2 _

/-- For nonzero target order, the canonical strong scale is at most a constant
multiple of the target. -/
theorem strongScale_le_const_mul
    {cStrong target : ℕ} (htarget : 1 ≤ target) :
    strongScale cStrong target ≤ max 2 cStrong * target := by
  rw [strongScale]
  apply max_le
  · calc
      2 = 2 * 1 := by simp
      _ ≤ max 2 cStrong * target :=
        Nat.mul_le_mul (le_max_left 2 cStrong) htarget
  · exact Nat.mul_le_mul_right target (le_max_right 2 cStrong)

/-- Canonical-strong scale package whose hairy-system inequality is stated in
normalized logarithmic form.  This is the sharp analogue of
`UnroundedScaleChoice`: the strong branch uses `strongScale cStrong target`,
and the remaining numerical work is concentrated in choosing `k` and `n`. -/
structure NormalizedUnroundedScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Normalized logarithmic Chuzhoy--Tan Theorem 2.3 numerical hypothesis. -/
  hairy_large_logarithmic_normalized :
    exponentHairyConstant cHair cGrid * n ^ 9 *
      (Nat.log 2 n) ^ 51 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_raw : 2 * (cCross * (strongScale cStrong target) ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n

namespace NormalizedUnroundedScaleChoice

/-- Canonical normalized scale choices imply normalized logarithmic choices. -/
def toNormalizedLogarithmicScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      NormalizedUnroundedScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    NormalizedLogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw where
  k := P.k
  n := P.n
  r := strongScale cStrong target
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_logarithmic_normalized := P.hairy_large_logarithmic_normalized
  n_ge_two := P.n_ge_two
  r_ge_two := strongScale_ge_two cStrong target
  strong_scale_raw := P.strong_scale_raw
  target_direct_raw := P.target_direct_raw
  target_strong := target_le_strongScale cStrong target

/-- Canonical normalized scale choices imply ordinary scale-only choices. -/
def toScaleParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      NormalizedUnroundedScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    ScaleParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toNormalizedLogarithmicScaleChoice.toScaleParameterChoice

/-- Canonical normalized scale choices imply the exact parameter package
consumed by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      NormalizedUnroundedScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toNormalizedLogarithmicScaleChoice.toParameterChoice

end NormalizedUnroundedScaleChoice

/-- A polynomial-logarithmic crossbar scale of the expected grid-minor shape:
`C * target * (log target)^p`. -/
def logProductScale (C p target : ℕ) : ℕ :=
  C * target * (Nat.log 2 target) ^ p

/-- The logarithm of the log-product scale is controlled by a constant
multiple of `log target`.  The coefficient is intentionally simple rather than
tight; later numerical packages can enlarge it freely. -/
theorem log_logProductScale_le_const_mul_log
    (C p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (logProductScale C p target) ≤
      (C + p + 2) * Nat.log 2 target := by
  set L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
  have hC : C ≤ 2 ^ C := GridMinorArithmetic.self_le_two_pow C
  have htarget_pow : target ≤ 2 ^ Nat.clog 2 target :=
    Nat.le_pow_clog (by decide : 1 < 2) target
  have hL_pow : L ^ p ≤ (2 ^ Nat.clog 2 L) ^ p :=
    Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) L) p
  have hscale_le_pow :
      logProductScale C p target ≤
        2 ^ (C + Nat.clog 2 target + Nat.clog 2 L * p) := by
    calc
      logProductScale C p target = C * target * L ^ p := by
        simp [logProductScale, L]
      _ ≤ 2 ^ C * 2 ^ Nat.clog 2 target *
          (2 ^ Nat.clog 2 L) ^ p :=
        Nat.mul_le_mul (Nat.mul_le_mul hC htarget_pow) hL_pow
      _ = 2 ^ C * 2 ^ Nat.clog 2 target *
          2 ^ (Nat.clog 2 L * p) := by
        rw [GridMinorArithmetic.two_pow_pow]
      _ = 2 ^ (C + Nat.clog 2 target) *
          2 ^ (Nat.clog 2 L * p) := by
        rw [← pow_add]
      _ = 2 ^ (C + Nat.clog 2 target + Nat.clog 2 L * p) := by
        rw [← pow_add]
  have hlog_scale :
      Nat.log 2 (logProductScale C p target) ≤
        C + Nat.clog 2 target + Nat.clog 2 L * p :=
    le_trans (Nat.log_le_clog 2 (logProductScale C p target))
      (Nat.clog_le_of_le_pow hscale_le_pow)
  have hclog_target : Nat.clog 2 target ≤ L + 1 := by
    simpa [L] using GridMinorArithmetic.clog_le_log_succ target
  have hclog_L : Nat.clog 2 L ≤ L := by
    simpa [L] using GridMinorArithmetic.clog_log_le_log target
  have hmul : Nat.clog 2 L * p ≤ L * p :=
    Nat.mul_le_mul_right p hclog_L
  have hto_linear :
      C + Nat.clog 2 target + Nat.clog 2 L * p ≤
        C + (L + 1) + L * p :=
    Nat.add_le_add (Nat.add_le_add_left hclog_target C) hmul
  have hlinear :
      C + (L + 1) + L * p ≤ (C + p + 2) * L := by
    have hCmul : C ≤ C * L := by
      simpa using Nat.mul_le_mul_left C hLone
    calc
      C + (L + 1) + L * p
          ≤ C * L + (L + 1) + L * p := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right hCmul (L + 1)) (L * p)
      _ ≤ C * L + (L + L) + L * p := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_left (Nat.add_le_add_left hLone L) (C * L))
              (L * p)
      _ = (C + p + 2) * L := by
            rw [Nat.add_mul, Nat.add_mul]
            rw [Nat.mul_comm L p, two_mul]
            ac_rfl
  exact le_trans hlog_scale (le_trans hto_linear hlinear)

/-- A general monomial-logarithmic scale
`C * target^a * (log target)^p`.  The polynomial grid-minor threshold is the
case `a = 9`. -/
def monomialLogScale (C a p target : ℕ) : ℕ :=
  C * target ^ a * (Nat.log 2 target) ^ p

/-- The public polynomial grid-minor threshold is the degree-nine
monomial-logarithmic scale. -/
theorem polynomialGridMinorTreewidthBound_eq_monomialLogScale
    (K b target : ℕ) :
    polynomialGridMinorTreewidthBound K b target =
      monomialLogScale K 9 b target :=
  rfl

/-- The logarithm of a monomial-logarithmic scale is controlled by a constant
multiple of `log target`.  The coefficient `C + 2*a + p` absorbs the one-bit
rounding loss from replacing `clog target` by `log target + 1`. -/
theorem log_monomialLogScale_le_const_mul_log
    (C a p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (monomialLogScale C a p target) ≤
      (C + 2 * a + p) * Nat.log 2 target := by
  set L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
  have hC : C ≤ 2 ^ C := GridMinorArithmetic.self_le_two_pow C
  have htarget_pow :
      target ^ a ≤ (2 ^ Nat.clog 2 target) ^ a :=
    Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) target) a
  have hL_pow : L ^ p ≤ (2 ^ Nat.clog 2 L) ^ p :=
    Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) L) p
  have hscale_le_pow :
      monomialLogScale C a p target ≤
        2 ^ (C + Nat.clog 2 target * a + Nat.clog 2 L * p) := by
    calc
      monomialLogScale C a p target = C * target ^ a * L ^ p := by
        simp [monomialLogScale, L]
      _ ≤ 2 ^ C * (2 ^ Nat.clog 2 target) ^ a *
          (2 ^ Nat.clog 2 L) ^ p :=
        Nat.mul_le_mul (Nat.mul_le_mul hC htarget_pow) hL_pow
      _ = 2 ^ C * 2 ^ (Nat.clog 2 target * a) *
          2 ^ (Nat.clog 2 L * p) := by
        rw [GridMinorArithmetic.two_pow_pow]
        rw [GridMinorArithmetic.two_pow_pow]
      _ = 2 ^ (C + Nat.clog 2 target * a) *
          2 ^ (Nat.clog 2 L * p) := by
        rw [← pow_add]
      _ = 2 ^ (C + Nat.clog 2 target * a + Nat.clog 2 L * p) := by
        rw [← pow_add]
  have hlog_scale :
      Nat.log 2 (monomialLogScale C a p target) ≤
        C + Nat.clog 2 target * a + Nat.clog 2 L * p :=
    le_trans (Nat.log_le_clog 2 (monomialLogScale C a p target))
      (Nat.clog_le_of_le_pow hscale_le_pow)
  have hclog_target : Nat.clog 2 target ≤ L + 1 := by
    simpa [L] using GridMinorArithmetic.clog_le_log_succ target
  have hclog_L : Nat.clog 2 L ≤ L := by
    simpa [L] using GridMinorArithmetic.clog_log_le_log target
  have htarget_part : Nat.clog 2 target * a ≤ (L + 1) * a :=
    Nat.mul_le_mul_right a hclog_target
  have hlog_part : Nat.clog 2 L * p ≤ L * p :=
    Nat.mul_le_mul_right p hclog_L
  have hto_linear :
      C + Nat.clog 2 target * a + Nat.clog 2 L * p ≤
        C + (L + 1) * a + L * p :=
    Nat.add_le_add (Nat.add_le_add_left htarget_part C) hlog_part
  have hlinear :
      C + (L + 1) * a + L * p ≤ (C + 2 * a + p) * L := by
    have hCmul : C ≤ C * L := by
      simpa using Nat.mul_le_mul_left C hLone
    have hamul : a ≤ a * L := by
      simpa using Nat.mul_le_mul_left a hLone
    calc
      C + (L + 1) * a + L * p
          = C + (L * a + a) + L * p := by
            rw [Nat.add_mul, one_mul]
      _ ≤ C * L + (L * a + a) + L * p := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right hCmul (L * a + a)) (L * p)
      _ ≤ C * L + (L * a + a * L) + L * p := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_left (Nat.add_le_add_left hamul (L * a))
                (C * L)) (L * p)
      _ = (C + 2 * a + p) * L := by
            rw [two_mul, Nat.mul_comm L a, Nat.mul_comm L p]
            rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  exact le_trans hlog_scale (le_trans hto_linear hlinear)

/-- Sharper version of `log_monomialLogScale_le_const_mul_log` using
`clog C` rather than `C` for the fixed coefficient. -/
theorem log_monomialLogScale_le_clog_const_mul_log
    (C a p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (monomialLogScale C a p target) ≤
      (Nat.clog 2 C + 2 * a + p) * Nat.log 2 target := by
  set L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
  have hC : C ≤ 2 ^ Nat.clog 2 C :=
    Nat.le_pow_clog (by decide : 1 < 2) C
  have htarget_pow :
      target ^ a ≤ (2 ^ Nat.clog 2 target) ^ a :=
    Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) target) a
  have hL_pow : L ^ p ≤ (2 ^ Nat.clog 2 L) ^ p :=
    Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) L) p
  have hscale_le_pow :
      monomialLogScale C a p target ≤
        2 ^ (Nat.clog 2 C + Nat.clog 2 target * a +
          Nat.clog 2 L * p) := by
    calc
      monomialLogScale C a p target = C * target ^ a * L ^ p := by
        simp [monomialLogScale, L]
      _ ≤ 2 ^ Nat.clog 2 C * (2 ^ Nat.clog 2 target) ^ a *
          (2 ^ Nat.clog 2 L) ^ p :=
        Nat.mul_le_mul (Nat.mul_le_mul hC htarget_pow) hL_pow
      _ = 2 ^ Nat.clog 2 C * 2 ^ (Nat.clog 2 target * a) *
          2 ^ (Nat.clog 2 L * p) := by
        rw [GridMinorArithmetic.two_pow_pow]
        rw [GridMinorArithmetic.two_pow_pow]
      _ = 2 ^ (Nat.clog 2 C + Nat.clog 2 target * a) *
          2 ^ (Nat.clog 2 L * p) := by
        rw [← pow_add]
      _ = 2 ^ (Nat.clog 2 C + Nat.clog 2 target * a +
          Nat.clog 2 L * p) := by
        rw [← pow_add]
  have hlog_scale :
      Nat.log 2 (monomialLogScale C a p target) ≤
        Nat.clog 2 C + Nat.clog 2 target * a + Nat.clog 2 L * p :=
    le_trans (Nat.log_le_clog 2 (monomialLogScale C a p target))
      (Nat.clog_le_of_le_pow hscale_le_pow)
  have hclog_target : Nat.clog 2 target ≤ L + 1 := by
    simpa [L] using GridMinorArithmetic.clog_le_log_succ target
  have hclog_L : Nat.clog 2 L ≤ L := by
    simpa [L] using GridMinorArithmetic.clog_log_le_log target
  have htarget_part : Nat.clog 2 target * a ≤ (L + 1) * a :=
    Nat.mul_le_mul_right a hclog_target
  have hlog_part : Nat.clog 2 L * p ≤ L * p :=
    Nat.mul_le_mul_right p hclog_L
  have hto_linear :
      Nat.clog 2 C + Nat.clog 2 target * a + Nat.clog 2 L * p ≤
        Nat.clog 2 C + (L + 1) * a + L * p :=
    Nat.add_le_add (Nat.add_le_add_left htarget_part (Nat.clog 2 C))
      hlog_part
  have hlinear :
      Nat.clog 2 C + (L + 1) * a + L * p ≤
        (Nat.clog 2 C + 2 * a + p) * L := by
    have hCmul : Nat.clog 2 C ≤ Nat.clog 2 C * L := by
      simpa using Nat.mul_le_mul_left (Nat.clog 2 C) hLone
    have hamul : a ≤ a * L := by
      simpa using Nat.mul_le_mul_left a hLone
    calc
      Nat.clog 2 C + (L + 1) * a + L * p
          = Nat.clog 2 C + (L * a + a) + L * p := by
            rw [Nat.add_mul, one_mul]
      _ ≤ Nat.clog 2 C * L + (L * a + a) + L * p := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right hCmul (L * a + a)) (L * p)
      _ ≤ Nat.clog 2 C * L + (L * a + a * L) + L * p := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_left (Nat.add_le_add_left hamul (L * a))
                (Nat.clog 2 C * L)) (L * p)
      _ = (Nat.clog 2 C + 2 * a + p) * L := by
            rw [two_mul, Nat.mul_comm L a, Nat.mul_comm L p]
            rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  exact le_trans hlog_scale (le_trans hto_linear hlinear)

/-- Sharper logarithm bound for the log-product scale. -/
theorem log_logProductScale_le_clog_const_mul_log
    (C p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (logProductScale C p target) ≤
      (Nat.clog 2 C + p + 2) * Nat.log 2 target := by
  simpa [logProductScale, monomialLogScale, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    (log_monomialLogScale_le_clog_const_mul_log C 1 p htarget)

/-- A log-product scale is at least two when its constant coefficient is
positive and the target grid order is at least two. -/
theorem two_le_logProductScale
    {C p target : ℕ} (hC : 1 ≤ C) (htarget : 2 ≤ target) :
    2 ≤ logProductScale C p target := by
  have hlog_pos : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have hlog_pow : 1 ≤ (Nat.log 2 target) ^ p :=
    Nat.succ_le_of_lt (Nat.pow_pos hlog_pos)
  calc
    2 ≤ C * target := by
      calc
        2 = 1 * 2 := by simp
        _ ≤ C * target := Nat.mul_le_mul hC htarget
    _ = C * target * 1 := by simp
    _ ≤ C * target * (Nat.log 2 target) ^ p :=
      Nat.mul_le_mul_left _ hlog_pow
    _ = logProductScale C p target := by
      rw [logProductScale]

/-- The public polynomial grid-minor threshold is nontrivial when its
coefficient is positive and the target grid order is at least two. -/
theorem polynomialGridMinorTreewidthBound_gt_one
    {K b target : ℕ} (hK : 1 ≤ K) (htarget : 2 ≤ target) :
    1 < polynomialGridMinorTreewidthBound K b target := by
  have hlog_pos : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have hlog_pow : 1 ≤ (Nat.log 2 target) ^ b :=
    Nat.succ_le_of_lt (Nat.pow_pos hlog_pos)
  have htarget_pow : 2 ≤ target ^ 9 := by
    calc
      2 ≤ 2 ^ 9 := by decide
      _ ≤ target ^ 9 := Nat.pow_le_pow_left htarget 9
  have htwo :
      2 ≤ polynomialGridMinorTreewidthBound K b target := by
    calc
      2 ≤ K * target ^ 9 := by
        calc
          2 = 1 * 2 := by simp
          _ ≤ K * target ^ 9 :=
            Nat.mul_le_mul hK htarget_pow
      _ = K * target ^ 9 * 1 := by simp
      _ ≤ K * target ^ 9 * (Nat.log 2 target) ^ b :=
        Nat.mul_le_mul_left _ hlog_pow
      _ = polynomialGridMinorTreewidthBound K b target := by
        rw [polynomialGridMinorTreewidthBound]
  exact lt_of_lt_of_le (by decide : 1 < 2) htwo

/-- A coefficient inequality that implies the direct-branch condition for a
log-product crossbar scale. -/
theorem target_direct_logProduct_of_coeff
    {cGrid C Dn p target : ℕ} (htarget : 2 ≤ target) (hp : 2 ≤ p)
    (hcoeff : 2 * cGrid * Dn ^ 2 ≤ C) :
    2 * (cGrid * target * (Dn * Nat.log 2 target) ^ 2) ≤
      logProductScale C p target := by
  set L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hLpow : L ^ 2 ≤ L ^ p :=
    Nat.pow_le_pow_right hLpos hp
  calc
    2 * (cGrid * target * (Dn * Nat.log 2 target) ^ 2)
        =
      (2 * cGrid * Dn ^ 2) * (target * L ^ 2) := by
        rw [mul_pow]
        simp [L]
        ac_rfl
    _ ≤ C * (target * L ^ 2) :=
      Nat.mul_le_mul_right _ hcoeff
    _ = C * target * L ^ 2 := by
      ac_rfl
    _ ≤ C * target * L ^ p :=
      Nat.mul_le_mul_left (C * target) hLpow
    _ = logProductScale C p target := by
      simp [logProductScale, L]

/-- If a coefficient is below `2^q`, then `2^(2^q)` dominates that coefficient
times `(2^q + 4)^2`. -/
theorem coeff_mul_two_pow_add_four_sq_le_two_pow_two_pow
    {A q : ℕ} (hA : A ≤ 2 ^ q) (hq : 5 ≤ q) :
    A * (2 ^ q + 4) ^ 2 ≤ 2 ^ (2 ^ q) := by
  let M := 2 ^ q
  have hq_two : 2 ≤ q := le_trans (by decide : 2 ≤ 5) hq
  have hM_ge_four : 4 ≤ M := by
    simpa [M] using
      Nat.pow_le_pow_right (by decide : 0 < 2) hq_two
  have hadd : M + 4 ≤ 2 * M := by
    calc
      M + 4 ≤ M + M := Nat.add_le_add_left hM_ge_four M
      _ = 2 * M := by omega
  have hsquare : (M + 4) ^ 2 ≤ (2 * M) ^ 2 :=
    Nat.pow_le_pow_left hadd 2
  calc
    A * (2 ^ q + 4) ^ 2 = A * (M + 4) ^ 2 := by
      simp [M]
    _ ≤ M * (M + 4) ^ 2 := Nat.mul_le_mul_right _ (by simpa [M] using hA)
    _ ≤ M * (2 * M) ^ 2 := Nat.mul_le_mul_left _ hsquare
    _ = 4 * M ^ 3 := by
      rw [mul_pow]
      change M * (4 * M ^ 2) = 4 * M ^ 3
      rw [show (3 : ℕ) = 1 + 2 by decide, pow_add]
      simp
      ac_rfl
    _ = 4 * (2 ^ q) ^ 3 := by
      simp [M]
    _ ≤ 2 ^ (2 ^ q) :=
      GridMinorArithmetic.four_mul_two_pow_cube_le_two_pow_two_pow_of_five_le
        hq

/-- Direct-branch coefficient budget for the canonical choice
`C = 2^(2^q)` and `p = 2`. -/
theorem direct_coeff_two_pow_two_pow
    {cGrid q : ℕ} (hcoeff : 2 * cGrid ≤ 2 ^ q) (hq : 5 ≤ q) :
    2 * cGrid * (Nat.clog 2 (2 ^ (2 ^ q)) + 2 + 2) ^ 2 ≤
      2 ^ (2 ^ q) := by
  simpa [Nat.clog_pow 2 (2 ^ q) (by decide : 1 < 2), Nat.add_assoc] using
    coeff_mul_two_pow_add_four_sq_le_two_pow_two_pow
      (A := 2 * cGrid) hcoeff hq

/-- A coefficient inequality that implies the sharp strong-branch condition
for a log-product crossbar scale. -/
theorem strong_scale_logProduct_sq_of_coeff
    {cCross cStrong C p target : ℕ} (htarget : 2 ≤ target)
    (hcoeff : 4 * cCross * (max 2 cStrong) ^ 2 ≤ C ^ 2) :
    4 * (cCross * (strongScale cStrong target) ^ 2) ≤
      (logProductScale C p target) ^ 2 := by
  set L := Nat.log 2 target
  have htarget_one : 1 ≤ target :=
    le_trans (by decide : 1 ≤ 2) htarget
  have hlog_pos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hlog_pow_pos : 0 < L ^ p := Nat.pow_pos hlog_pos
  have hlog_pow_sq : 1 ≤ (L ^ p) ^ 2 :=
    Nat.succ_le_of_lt (Nat.pow_pos hlog_pow_pos)
  have hstrong_sq :
      (strongScale cStrong target) ^ 2 ≤
        (max 2 cStrong * target) ^ 2 :=
    Nat.pow_le_pow_left (strongScale_le_const_mul htarget_one) 2
  have htarget_sq_pos : 1 ≤ target ^ 2 :=
    Nat.succ_le_of_lt
      (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) htarget))
  calc
    4 * (cCross * (strongScale cStrong target) ^ 2)
        =
      (4 * cCross) * (strongScale cStrong target) ^ 2 := by
        ac_rfl
    _ ≤ (4 * cCross) * (max 2 cStrong * target) ^ 2 :=
      Nat.mul_le_mul_left _ hstrong_sq
    _ = (4 * cCross * (max 2 cStrong) ^ 2) * target ^ 2 := by
      rw [mul_pow]
      ac_rfl
    _ ≤ C ^ 2 * target ^ 2 :=
      Nat.mul_le_mul_right _ hcoeff
    _ = C ^ 2 * target ^ 2 * 1 := by
      simp
    _ ≤ C ^ 2 * target ^ 2 * (L ^ p) ^ 2 :=
      Nat.mul_le_mul_left _ hlog_pow_sq
    _ = (logProductScale C p target) ^ 2 := by
      rw [logProductScale, mul_pow, mul_pow]

/-- Strong-branch coefficient budget for the canonical choice
`C = 2^(2^q)`. -/
theorem strong_coeff_two_pow_two_pow
    {A q : ℕ} (hA : A ≤ 2 ^ q) :
    A ≤ (2 ^ (2 ^ q)) ^ 2 := by
  calc
    A ≤ 2 ^ q := hA
    _ ≤ 2 ^ (2 ^ q) :=
      Nat.pow_le_pow_right (by decide : 0 < 2)
        (GridMinorArithmetic.self_le_two_pow q)
    _ ≤ (2 ^ (2 ^ q)) ^ 2 :=
      Nat.le_self_pow (a := 2 ^ (2 ^ q)) (by decide : (2 : ℕ) ≠ 0)

/-- Canonical exponent large enough for the two crossbar coefficient budgets. -/
def crossbarCoefficientExponent
    (cCross cGrid cStrong : ℕ) : ℕ :=
  max 5 (max (2 * cGrid) (4 * cCross * (max 2 cStrong) ^ 2))

/-- Canonical crossbar-scale coefficient used by the coefficient template. -/
def crossbarCoefficient
    (cCross cGrid cStrong : ℕ) : ℕ :=
  2 ^ (2 ^ crossbarCoefficientExponent cCross cGrid cStrong)

/-- The canonical crossbar exponent is at least five. -/
theorem five_le_crossbarCoefficientExponent
    (cCross cGrid cStrong : ℕ) :
    5 ≤ crossbarCoefficientExponent cCross cGrid cStrong :=
  le_max_left _ _

/-- The direct-branch coefficient is bounded by the canonical crossbar
coefficient. -/
theorem direct_coeff_crossbarCoefficient
    (cCross cGrid cStrong : ℕ) :
    2 * cGrid *
        (Nat.clog 2 (crossbarCoefficient cCross cGrid cStrong) + 2 + 2) ^ 2
      ≤ crossbarCoefficient cCross cGrid cStrong := by
  let q := crossbarCoefficientExponent cCross cGrid cStrong
  have hq : 5 ≤ q := five_le_crossbarCoefficientExponent cCross cGrid cStrong
  have hcoeff_linear : 2 * cGrid ≤ q := by
    exact le_trans (le_max_left _ _)
      (le_max_right 5 (max (2 * cGrid)
        (4 * cCross * (max 2 cStrong) ^ 2)))
  have hcoeff : 2 * cGrid ≤ 2 ^ q :=
    le_trans hcoeff_linear (GridMinorArithmetic.self_le_two_pow q)
  simpa [crossbarCoefficient, q] using
    direct_coeff_two_pow_two_pow (cGrid := cGrid) hcoeff hq

/-- The sharp strong-branch coefficient is bounded by the canonical crossbar
coefficient squared. -/
theorem strong_coeff_crossbarCoefficient
    (cCross cGrid cStrong : ℕ) :
    4 * cCross * (max 2 cStrong) ^ 2 ≤
      (crossbarCoefficient cCross cGrid cStrong) ^ 2 := by
  let q := crossbarCoefficientExponent cCross cGrid cStrong
  have hcoeff_linear :
      4 * cCross * (max 2 cStrong) ^ 2 ≤ q := by
    exact le_trans (le_max_right _ _)
      (le_max_right 5 (max (2 * cGrid)
        (4 * cCross * (max 2 cStrong) ^ 2)))
  have hcoeff :
      4 * cCross * (max 2 cStrong) ^ 2 ≤ 2 ^ q :=
    le_trans hcoeff_linear (GridMinorArithmetic.self_le_two_pow q)
  simpa [crossbarCoefficient, q] using
    strong_coeff_two_pow_two_pow (A := 4 * cCross * (max 2 cStrong) ^ 2)
      hcoeff

/-- A coefficient and exponent budget that imply the normalized hairy-system
inequality at the public polynomial threshold. -/
theorem hairy_large_threshold_of_coeff
    {cHair cHairLog cGrid C p Dn Dk K b target : ℕ}
    (htarget : 2 ≤ target)
    (hexponent : p * 9 + 51 + cHairLog ≤ b)
    (hcoeff :
      exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
        Dk ^ cHairLog < K) :
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 9 *
      (Dn * Nat.log 2 target) ^ 51 *
      (Dk * Nat.log 2 target) ^ cHairLog <
        polynomialGridMinorTreewidthBound K b target := by
  set L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have htarget_pos : 0 < target :=
    lt_of_lt_of_le (by decide : 0 < 2) htarget
  have htarget_pow_pos : 0 < target ^ 9 := Nat.pow_pos htarget_pos
  have hLpow_b_pos : 0 < L ^ b := Nat.pow_pos hLpos
  have hmult_pos : 0 < target ^ 9 * L ^ b :=
    Nat.mul_pos htarget_pow_pos hLpow_b_pos
  have hLp :
      (L ^ p) ^ 9 = L ^ (p * 9) := by
    simpa using (Nat.pow_mul L p 9).symm
  have hleft_eq :
      exponentHairyConstant cHair cGrid *
          (logProductScale C p target) ^ 9 *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog =
      (exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
          Dk ^ cHairLog) *
        target ^ 9 * L ^ (p * 9 + 51 + cHairLog) := by
    calc
      exponentHairyConstant cHair cGrid *
          (logProductScale C p target) ^ 9 *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog
          =
        exponentHairyConstant cHair cGrid *
          (C ^ 9 * target ^ 9 * (L ^ p) ^ 9) *
          (Dn ^ 51 * L ^ 51) *
          (Dk ^ cHairLog * L ^ cHairLog) := by
          rw [logProductScale]
          repeat rw [mul_pow]
      _ =
        exponentHairyConstant cHair cGrid *
          (C ^ 9 * target ^ 9 * L ^ (p * 9)) *
          (Dn ^ 51 * L ^ 51) *
          (Dk ^ cHairLog * L ^ cHairLog) := by
          rw [hLp]
      _ =
        (exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
            Dk ^ cHairLog) *
          target ^ 9 *
          (L ^ (p * 9) * L ^ 51 * L ^ cHairLog) := by
          ac_rfl
      _ =
        (exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
            Dk ^ cHairLog) *
          target ^ 9 * L ^ (p * 9 + 51 + cHairLog) := by
          rw [← pow_add, ← pow_add]
  have hpow :
      L ^ (p * 9 + 51 + cHairLog) ≤ L ^ b :=
    Nat.pow_le_pow_right hLpos hexponent
  calc
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 9 *
      (Dn * Nat.log 2 target) ^ 51 *
      (Dk * Nat.log 2 target) ^ cHairLog
        =
      (exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
          Dk ^ cHairLog) *
        target ^ 9 * L ^ (p * 9 + 51 + cHairLog) := hleft_eq
    _ ≤ (exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
          Dk ^ cHairLog) *
        target ^ 9 * L ^ b :=
      Nat.mul_le_mul_left
        ((exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
          Dk ^ cHairLog) * target ^ 9) hpow
    _ < K * target ^ 9 * L ^ b := by
      calc
        (exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
            Dk ^ cHairLog) *
          target ^ 9 * L ^ b
            =
          (exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
            Dk ^ cHairLog) * (target ^ 9 * L ^ b) := by
            ac_rfl
        _ < K * (target ^ 9 * L ^ b) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hmult_pos
        _ = K * target ^ 9 * L ^ b := by
          ac_rfl
    _ = polynomialGridMinorTreewidthBound K b target := by
      simp [polynomialGridMinorTreewidthBound, L]

/-- A triple-power coefficient `K = 2^(2^(2^q))` dominates
`A * (clog K + E)^h` once `q` dominates the fixed parameters. -/
theorem coeff_mul_clog_triplePower_add_pow_lt_triplePower
    {A h E q : ℕ} (hA : A ≤ q) (hh : h ≤ q) (hE : E ≤ q)
    (hq : 5 ≤ q) :
    A * (Nat.clog 2 (2 ^ (2 ^ (2 ^ q))) + E) ^ h <
      2 ^ (2 ^ (2 ^ q)) := by
  let S := 2 ^ q
  have hq_le_S : q ≤ S := GridMinorArithmetic.self_le_two_pow q
  have hA_S : A ≤ S := le_trans hA hq_le_S
  have hhS : h ≤ S := le_trans hh hq_le_S
  have hE_S : E ≤ S := le_trans hE hq_le_S
  have hA_pow : A ≤ 2 ^ S :=
    le_trans hA_S (GridMinorArithmetic.self_le_two_pow S)
  have hE_pow : E ≤ 2 ^ S :=
    le_trans hE_S (GridMinorArithmetic.self_le_two_pow S)
  have hD :
      Nat.clog 2 (2 ^ (2 ^ (2 ^ q))) + E ≤ 2 ^ (S + 1) := by
    calc
      Nat.clog 2 (2 ^ (2 ^ (2 ^ q))) + E
          = 2 ^ S + E := by
            rw [Nat.clog_pow 2 (2 ^ S) (by decide : 1 < 2)]
      _ ≤ 2 ^ S + 2 ^ S := Nat.add_le_add_left hE_pow (2 ^ S)
      _ = 2 ^ (S + 1) := by
            rw [Nat.pow_succ]
            omega
  have hDpow :
      (Nat.clog 2 (2 ^ (2 ^ (2 ^ q))) + E) ^ h ≤
        (2 ^ (S + 1)) ^ h :=
    Nat.pow_le_pow_left hD h
  have hS_ge_two : 2 ≤ S := by
    exact CrossbarContract.two_le_two_pow
      (lt_of_lt_of_le (by decide : 0 < 5) hq)
  have hexp_le :
      S + (S + 1) * h ≤ S ^ 3 := by
    calc
      S + (S + 1) * h ≤ S + (S + 1) * S :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (S + 1) hhS) S
      _ ≤ S ^ 3 := GridMinorArithmetic.add_succ_mul_self_le_cube hS_ge_two
  have hexp_lt : S + (S + 1) * h < 2 ^ S :=
    lt_of_le_of_lt hexp_le (by
      simpa [S] using
        GridMinorArithmetic.two_pow_cube_lt_two_pow_two_pow_of_five_le hq)
  calc
    A * (Nat.clog 2 (2 ^ (2 ^ (2 ^ q))) + E) ^ h
        ≤ 2 ^ S * (2 ^ (S + 1)) ^ h :=
      Nat.mul_le_mul hA_pow hDpow
    _ = 2 ^ S * 2 ^ ((S + 1) * h) := by
      rw [GridMinorArithmetic.two_pow_pow]
    _ = 2 ^ (S + (S + 1) * h) := by
      rw [← pow_add]
    _ < 2 ^ (2 ^ S) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) hexp_lt
    _ = 2 ^ (2 ^ (2 ^ q)) := by
      simp [S]

/-- Canonical exponent large enough for the threshold coefficient budget. -/
def thresholdCoefficientExponent (A h E : ℕ) : ℕ :=
  max 5 (max A (max h E))

/-- Canonical threshold coefficient dominating `A * (clog K + E)^h`. -/
def thresholdCoefficient (A h E : ℕ) : ℕ :=
  2 ^ (2 ^ (2 ^ thresholdCoefficientExponent A h E))

/-- The canonical threshold exponent is at least five. -/
theorem five_le_thresholdCoefficientExponent (A h E : ℕ) :
    5 ≤ thresholdCoefficientExponent A h E :=
  le_max_left _ _

/-- The canonical threshold coefficient dominates the corresponding
coefficient-logarithm expression. -/
theorem coeff_mul_clog_thresholdCoefficient_add_pow_lt
    (A h E : ℕ) :
    A * (Nat.clog 2 (thresholdCoefficient A h E) + E) ^ h <
      thresholdCoefficient A h E := by
  let q := thresholdCoefficientExponent A h E
  have hA : A ≤ q := by
    exact le_trans (le_max_left _ _)
      (le_max_right 5 (max A (max h E)))
  have hh : h ≤ q := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right A (max h E))
        (le_max_right 5 (max A (max h E))))
  have hE : E ≤ q := by
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right A (max h E))
        (le_max_right 5 (max A (max h E))))
  have hq : 5 ≤ q := five_le_thresholdCoefficientExponent A h E
  simpa [thresholdCoefficient, q] using
    coeff_mul_clog_triplePower_add_pow_lt_triplePower hA hh hE hq

/-- Canonical normalized scale package where the unrounded crossbar scale is
specified as `C * target * (log target)^p`.

The field `log_scale_bound` is the remaining logarithmic estimate needed to
replace `log n` by a controlled multiple of `log target`.  Keeping it explicit
lets later arithmetic files choose the coefficient `D` in the most convenient
way. -/
structure LogProductScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- Coefficient controlling `log n` by `D * log target`. -/
  D : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The unrounded crossbar scale is at least two. -/
  scale_ge_two : 2 ≤ logProductScale C p target
  /-- The logarithm of the crossbar scale is controlled by `D * log target`. -/
  log_scale_bound :
    Nat.log 2 (logProductScale C p target) ≤ D * Nat.log 2 target
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_logProduct :
    2 * (cCross * (strongScale cStrong target) ^ 2) ≤
      logProductScale C p target
  /-- The rounded direct branch produces a grid at least as large as `target`
  after replacing `log n` by `D * log target`. -/
  target_direct_logProduct :
    2 * (cGrid * target * (D * Nat.log 2 target) ^ 2) ≤
      logProductScale C p target
  /-- Normalized hairy-system inequality for the log-product scale after
  replacing `log n` by `D * log target`. -/
  hairy_large_logProduct :
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 9 *
      (D * Nat.log 2 target) ^ 51 *
      (Nat.log 2 k) ^ cHairLog < k

namespace LogProductScaleChoice

/-- Log-product scale choices imply canonical normalized scale choices. -/
def toNormalizedUnroundedScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : LogProductScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    NormalizedUnroundedScaleChoice cHair cHairLog cCross cGrid cStrong target
        tw where
  k := P.k
  n := logProductScale P.C P.p target
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_logarithmic_normalized := by
    have hlog_pow :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 ≤
          (P.D * Nat.log 2 target) ^ 51 :=
      Nat.pow_le_pow_left P.log_scale_bound 51
    have hle :
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 P.k) ^ cHairLog ≤
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (P.D * Nat.log 2 target) ^ 51 *
          (Nat.log 2 P.k) ^ cHairLog := by
      calc
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 P.k) ^ cHairLog
            =
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9) *
            ((Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
              (Nat.log 2 P.k) ^ cHairLog) := by
            ac_rfl
        _ ≤
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9) *
            ((P.D * Nat.log 2 target) ^ 51 *
              (Nat.log 2 P.k) ^ cHairLog) :=
            Nat.mul_le_mul_left _
              (Nat.mul_le_mul_right _ hlog_pow)
        _ =
          exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9 *
            (P.D * Nat.log 2 target) ^ 51 *
            (Nat.log 2 P.k) ^ cHairLog := by
            ac_rfl
    exact lt_of_le_of_lt hle P.hairy_large_logProduct
  n_ge_two := P.scale_ge_two
  strong_scale_raw := P.strong_scale_logProduct
  target_direct_raw := by
    have hlog_sq :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 2 ≤
          (P.D * Nat.log 2 target) ^ 2 :=
      Nat.pow_le_pow_left P.log_scale_bound 2
    calc
      2 * (cGrid * target *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 2)
          ≤
        2 * (cGrid * target * (P.D * Nat.log 2 target) ^ 2) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left (cGrid * target) hlog_sq)
      _ ≤ logProductScale P.C P.p target :=
        P.target_direct_logProduct

/-- Log-product scale choices imply the exact parameter package consumed by
the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : LogProductScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toNormalizedUnroundedScaleChoice.toParameterChoice

end LogProductScaleChoice

/-- Log-product scale package using the built-in estimate
`log (C * target * (log target)^p) <= (C+p+2) * log target`.

This is the main proof-facing interface for the expected polynomial
grid-minor threshold shape before the final choice of constants. -/
structure ExplicitLogProductScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The unrounded crossbar scale is at least two. -/
  scale_ge_two : 2 ≤ logProductScale C p target
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_logProduct :
    2 * (cCross * (strongScale cStrong target) ^ 2) ≤
      logProductScale C p target
  /-- The rounded direct branch produces a grid at least as large as `target`
  with the built-in logarithm estimate. -/
  target_direct_explicit :
    2 * (cGrid * target * ((C + p + 2) * Nat.log 2 target) ^ 2) ≤
      logProductScale C p target
  /-- Normalized hairy-system inequality for the log-product scale with the
  built-in logarithm estimate. -/
  hairy_large_explicit :
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 9 *
      ((C + p + 2) * Nat.log 2 target) ^ 51 *
      (Nat.log 2 k) ^ cHairLog < k

namespace ExplicitLogProductScaleChoice

/-- Explicit log-product choices imply log-product choices. -/
def toLogProductScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      ExplicitLogProductScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    LogProductScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  C := P.C
  p := P.p
  D := P.C + P.p + 2
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  target_ge_two := P.target_ge_two
  scale_ge_two := P.scale_ge_two
  log_scale_bound :=
    log_logProductScale_le_const_mul_log P.C P.p P.target_ge_two
  strong_scale_logProduct := P.strong_scale_logProduct
  target_direct_logProduct := P.target_direct_explicit
  hairy_large_logProduct := P.hairy_large_explicit

/-- Explicit log-product choices imply canonical normalized scale choices. -/
def toNormalizedUnroundedScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      ExplicitLogProductScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    NormalizedUnroundedScaleChoice cHair cHairLog cCross cGrid cStrong target
        tw :=
  P.toLogProductScaleChoice.toNormalizedUnroundedScaleChoice

/-- Explicit log-product choices imply the exact parameter package consumed by
the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      ExplicitLogProductScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toLogProductScaleChoice.toParameterChoice

end ExplicitLogProductScaleChoice

/-- Explicit log-product scale package at the public polynomial treewidth
threshold `K * target^9 * (log target)^b`.

This wrapper packages the last logarithmic substitution needed for the
proof-facing polynomial-grid-minor statement: the threshold's own logarithm is
bounded by `(K + 18 + b) * log target`. -/
structure ExplicitLogProductPolynomialThresholdChoice
    (cHair cHairLog cCross cGrid cStrong target K b : ℕ) where
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- The public polynomial threshold is nontrivial. -/
  threshold_gt_one :
    1 < polynomialGridMinorTreewidthBound K b target
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The unrounded crossbar scale is at least two. -/
  scale_ge_two : 2 ≤ logProductScale C p target
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_logProduct :
    2 * (cCross * (strongScale cStrong target) ^ 2) ≤
      logProductScale C p target
  /-- The rounded direct branch produces a grid at least as large as `target`
  with the built-in logarithm estimate for the crossbar scale. -/
  target_direct_explicit :
    2 * (cGrid * target * ((C + p + 2) * Nat.log 2 target) ^ 2) ≤
      logProductScale C p target
  /-- Normalized hairy-system inequality after also bounding the logarithm of
  the public polynomial threshold. -/
  hairy_large_threshold :
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 9 *
      ((C + p + 2) * Nat.log 2 target) ^ 51 *
      ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog <
        polynomialGridMinorTreewidthBound K b target

namespace ExplicitLogProductPolynomialThresholdChoice

/-- Polynomial-threshold log-product choices imply explicit log-product
choices at the public treewidth threshold. -/
def toExplicitLogProductScaleChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      ExplicitLogProductPolynomialThresholdChoice cHair cHairLog cCross cGrid
        cStrong target K b) :
    ExplicitLogProductScaleChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) where
  k := polynomialGridMinorTreewidthBound K b target
  C := P.C
  p := P.p
  k_gt_one := P.threshold_gt_one
  k_le_treewidth := le_rfl
  target_ge_two := P.target_ge_two
  scale_ge_two := P.scale_ge_two
  strong_scale_logProduct := P.strong_scale_logProduct
  target_direct_explicit := P.target_direct_explicit
  hairy_large_explicit := by
    have hlog_threshold :
        Nat.log 2 (polynomialGridMinorTreewidthBound K b target) ≤
          (K + 2 * 9 + b) * Nat.log 2 target := by
      simpa [polynomialGridMinorTreewidthBound_eq_monomialLogScale,
        monomialLogScale] using
        log_monomialLogScale_le_const_mul_log K 9 b P.target_ge_two
    have hlog_pow :
        (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog ≤
          ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog :=
      Nat.pow_le_pow_left hlog_threshold cHairLog
    have hle :
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          ((P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog ≤
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          ((P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
          ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog := by
      calc
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          ((P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog
            =
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9 *
            ((P.C + P.p + 2) * Nat.log 2 target) ^ 51) *
          (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog := by
            ac_rfl
        _ ≤
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9 *
            ((P.C + P.p + 2) * Nat.log 2 target) ^ 51) *
          ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog :=
            Nat.mul_le_mul_left _ hlog_pow
        _ =
          exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9 *
            ((P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
            ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog := by
            ac_rfl
    exact lt_of_le_of_lt hle P.hairy_large_threshold

/-- Polynomial-threshold log-product choices imply the exact parameter package
consumed by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      ExplicitLogProductPolynomialThresholdChoice cHair cHairLog cCross cGrid
        cStrong target K b) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) :=
  P.toExplicitLogProductScaleChoice.toParameterChoice

end ExplicitLogProductPolynomialThresholdChoice

/-- Sharp log-product scale package at the public polynomial treewidth
threshold.  Compared with `ExplicitLogProductPolynomialThresholdChoice`, the
strong branch is stated in the square form
`4 * cCross * r^2 <= n^2`, which preserves a crossbar scale linear in the
target grid order. -/
structure SharpExplicitLogProductPolynomialThresholdChoice
    (cHair cHairLog cCross cGrid cStrong target K b : ℕ) where
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- The public polynomial threshold is nontrivial. -/
  threshold_gt_one :
    1 < polynomialGridMinorTreewidthBound K b target
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The unrounded crossbar scale is at least two. -/
  scale_ge_two : 2 ≤ logProductScale C p target
  /-- The rounded strong branch can be thinned to the canonical strong scale
  using the square-form rounding condition. -/
  strong_scale_logProduct_sq :
    4 * (cCross * (strongScale cStrong target) ^ 2) ≤
      (logProductScale C p target) ^ 2
  /-- The rounded direct branch produces a grid at least as large as `target`
  with the built-in logarithm estimate for the crossbar scale. -/
  target_direct_explicit :
    2 * (cGrid * target * ((C + p + 2) * Nat.log 2 target) ^ 2) ≤
      logProductScale C p target
  /-- Normalized hairy-system inequality after bounding the logarithms of both
  the crossbar scale and the public polynomial threshold. -/
  hairy_large_threshold :
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 9 *
      ((C + p + 2) * Nat.log 2 target) ^ 51 *
      ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog <
        polynomialGridMinorTreewidthBound K b target

namespace SharpExplicitLogProductPolynomialThresholdChoice

/-- Sharp polynomial-threshold log-product choices imply sharp scale choices. -/
def toSharpScaleParameterChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpExplicitLogProductPolynomialThresholdChoice cHair cHairLog cCross
        cGrid cStrong target K b) :
    SharpScaleParameterChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) where
  k := polynomialGridMinorTreewidthBound K b target
  n := logProductScale P.C P.p target
  r := strongScale cStrong target
  k_gt_one := P.threshold_gt_one
  k_le_treewidth := le_rfl
  hairy_large := by
    apply hairy_large_of_logarithmic_normalized P.scale_ge_two
    have hlog_n :
        Nat.log 2 (logProductScale P.C P.p target) ≤
          (P.C + P.p + 2) * Nat.log 2 target :=
      log_logProductScale_le_const_mul_log P.C P.p P.target_ge_two
    have hlog_k :
        Nat.log 2 (polynomialGridMinorTreewidthBound K b target) ≤
          (K + 2 * 9 + b) * Nat.log 2 target := by
      simpa [polynomialGridMinorTreewidthBound_eq_monomialLogScale,
        monomialLogScale] using
        log_monomialLogScale_le_const_mul_log K 9 b P.target_ge_two
    have hlog_n_pow :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 ≤
          ((P.C + P.p + 2) * Nat.log 2 target) ^ 51 :=
      Nat.pow_le_pow_left hlog_n 51
    have hlog_k_pow :
        (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog ≤
          ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog :=
      Nat.pow_le_pow_left hlog_k cHairLog
    have hle :
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog ≤
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          ((P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
          ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog := by
      calc
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog
            =
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9) *
            ((Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
              (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
                cHairLog) := by
            ac_rfl
        _ ≤
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9) *
            (((P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
              ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog) :=
            Nat.mul_le_mul_left _
              (Nat.mul_le_mul hlog_n_pow hlog_k_pow)
        _ =
          exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9 *
            ((P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
            ((K + 2 * 9 + b) * Nat.log 2 target) ^ cHairLog := by
            ac_rfl
    exact lt_of_le_of_lt hle P.hairy_large_threshold
  n_ge_two := P.scale_ge_two
  r_ge_two := strongScale_ge_two cStrong target
  strong_scale_raw_sq := P.strong_scale_logProduct_sq
  target_direct_raw := by
    have hlog_n :
        Nat.log 2 (logProductScale P.C P.p target) ≤
          (P.C + P.p + 2) * Nat.log 2 target :=
      log_logProductScale_le_const_mul_log P.C P.p P.target_ge_two
    have hlog_sq :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 2 ≤
          ((P.C + P.p + 2) * Nat.log 2 target) ^ 2 :=
      Nat.pow_le_pow_left hlog_n 2
    calc
      2 * (cGrid * target *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 2)
          ≤
        2 * (cGrid * target *
          ((P.C + P.p + 2) * Nat.log 2 target) ^ 2) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left (cGrid * target) hlog_sq)
      _ ≤ logProductScale P.C P.p target :=
        P.target_direct_explicit
  target_strong := target_le_strongScale cStrong target

/-- Sharp polynomial-threshold choices imply the exact parameter package
consumed by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpExplicitLogProductPolynomialThresholdChoice cHair cHairLog cCross
        cGrid cStrong target K b) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) :=
  P.toSharpScaleParameterChoice.toParameterChoice

end SharpExplicitLogProductPolynomialThresholdChoice

/-- Flexible sharp log-product scale package at the public polynomial
treewidth threshold.  The logarithm coefficients `Dn` and `Dk` are supplied
explicitly, allowing later arithmetic to use sharper bounds than the coarse
`C+p+2` and `K+18+b` estimates. -/
structure SharpLogProductPolynomialThresholdChoice
    (cHair cHairLog cCross cGrid cStrong target K b : ℕ) where
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- Coefficient controlling the logarithm of the crossbar scale. -/
  Dn : ℕ
  /-- Coefficient controlling the logarithm of the treewidth threshold. -/
  Dk : ℕ
  /-- The public polynomial threshold is nontrivial. -/
  threshold_gt_one :
    1 < polynomialGridMinorTreewidthBound K b target
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The unrounded crossbar scale is at least two. -/
  scale_ge_two : 2 ≤ logProductScale C p target
  /-- Logarithm bound for the crossbar scale. -/
  log_scale_bound :
    Nat.log 2 (logProductScale C p target) ≤ Dn * Nat.log 2 target
  /-- Logarithm bound for the public treewidth threshold. -/
  threshold_log_bound :
    Nat.log 2 (polynomialGridMinorTreewidthBound K b target) ≤
      Dk * Nat.log 2 target
  /-- The rounded strong branch can be thinned to the canonical strong scale
  using the square-form rounding condition. -/
  strong_scale_logProduct_sq :
    4 * (cCross * (strongScale cStrong target) ^ 2) ≤
      (logProductScale C p target) ^ 2
  /-- The rounded direct branch produces a grid at least as large as `target`
  using the supplied crossbar logarithm coefficient. -/
  target_direct_logProduct :
    2 * (cGrid * target * (Dn * Nat.log 2 target) ^ 2) ≤
      logProductScale C p target
  /-- Normalized hairy-system inequality using the supplied logarithm
  coefficients. -/
  hairy_large_threshold :
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 9 *
      (Dn * Nat.log 2 target) ^ 51 *
      (Dk * Nat.log 2 target) ^ cHairLog <
        polynomialGridMinorTreewidthBound K b target

namespace SharpLogProductPolynomialThresholdChoice

/-- Flexible sharp polynomial-threshold choices imply sharp scale choices. -/
def toSharpScaleParameterChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpLogProductPolynomialThresholdChoice cHair cHairLog cCross cGrid
        cStrong target K b) :
    SharpScaleParameterChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) where
  k := polynomialGridMinorTreewidthBound K b target
  n := logProductScale P.C P.p target
  r := strongScale cStrong target
  k_gt_one := P.threshold_gt_one
  k_le_treewidth := le_rfl
  hairy_large := by
    apply hairy_large_of_logarithmic_normalized P.scale_ge_two
    have hlog_n_pow :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 ≤
          (P.Dn * Nat.log 2 target) ^ 51 :=
      Nat.pow_le_pow_left P.log_scale_bound 51
    have hlog_k_pow :
        (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog ≤
          (P.Dk * Nat.log 2 target) ^ cHairLog :=
      Nat.pow_le_pow_left P.threshold_log_bound cHairLog
    have hle :
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog ≤
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (P.Dn * Nat.log 2 target) ^ 51 *
          (P.Dk * Nat.log 2 target) ^ cHairLog := by
      calc
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 9 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
            cHairLog
            =
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9) *
            ((Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
              (Nat.log 2 (polynomialGridMinorTreewidthBound K b target)) ^
                cHairLog) := by
            ac_rfl
        _ ≤
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9) *
            ((P.Dn * Nat.log 2 target) ^ 51 *
              (P.Dk * Nat.log 2 target) ^ cHairLog) :=
            Nat.mul_le_mul_left _
              (Nat.mul_le_mul hlog_n_pow hlog_k_pow)
        _ =
          exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 9 *
            (P.Dn * Nat.log 2 target) ^ 51 *
            (P.Dk * Nat.log 2 target) ^ cHairLog := by
            ac_rfl
    exact lt_of_le_of_lt hle P.hairy_large_threshold
  n_ge_two := P.scale_ge_two
  r_ge_two := strongScale_ge_two cStrong target
  strong_scale_raw_sq := P.strong_scale_logProduct_sq
  target_direct_raw := by
    have hlog_sq :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 2 ≤
          (P.Dn * Nat.log 2 target) ^ 2 :=
      Nat.pow_le_pow_left P.log_scale_bound 2
    calc
      2 * (cGrid * target *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 2)
          ≤
        2 * (cGrid * target * (P.Dn * Nat.log 2 target) ^ 2) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left (cGrid * target) hlog_sq)
      _ ≤ logProductScale P.C P.p target :=
        P.target_direct_logProduct
  target_strong := target_le_strongScale cStrong target

/-- Flexible sharp polynomial-threshold choices imply the exact parameter
package consumed by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpLogProductPolynomialThresholdChoice cHair cHairLog cCross cGrid
        cStrong target K b) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) :=
  P.toSharpScaleParameterChoice.toParameterChoice

end SharpLogProductPolynomialThresholdChoice

/-- Coefficient-budget package for the sharp polynomial-threshold log-product
choice.  This collects the numerical inequalities that are independent of the
graph-theoretic composition and mostly independent of the target. -/
structure SharpCoefficientPolynomialThresholdChoice
    (cHair cHairLog cCross cGrid cStrong target K b : ℕ) where
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- Coefficient controlling the logarithm of the crossbar scale. -/
  Dn : ℕ
  /-- Coefficient controlling the logarithm of the treewidth threshold. -/
  Dk : ℕ
  /-- The crossbar-scale coefficient is positive. -/
  C_pos : 1 ≤ C
  /-- The threshold coefficient is positive. -/
  K_pos : 1 ≤ K
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The log-product exponent is large enough for the direct branch. -/
  p_ge_two : 2 ≤ p
  /-- Logarithm bound for the crossbar scale. -/
  log_scale_bound :
    Nat.log 2 (logProductScale C p target) ≤ Dn * Nat.log 2 target
  /-- Logarithm bound for the public treewidth threshold. -/
  threshold_log_bound :
    Nat.log 2 (polynomialGridMinorTreewidthBound K b target) ≤
      Dk * Nat.log 2 target
  /-- Coefficient budget for the sharp strong-branch inequality. -/
  strong_coeff :
    4 * cCross * (max 2 cStrong) ^ 2 ≤ C ^ 2
  /-- Coefficient budget for the direct-branch inequality. -/
  direct_coeff : 2 * cGrid * Dn ^ 2 ≤ C
  /-- Logarithmic exponent budget for the hairy-system inequality. -/
  hairy_exponent : p * 9 + 51 + cHairLog ≤ b
  /-- Strict coefficient budget for the hairy-system inequality. -/
  hairy_coeff :
    exponentHairyConstant cHair cGrid * C ^ 9 * Dn ^ 51 *
      Dk ^ cHairLog < K

namespace SharpCoefficientPolynomialThresholdChoice

/-- Coefficient-budget choices imply flexible sharp polynomial-threshold
choices. -/
def toSharpLogProductPolynomialThresholdChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpCoefficientPolynomialThresholdChoice cHair cHairLog cCross cGrid
        cStrong target K b) :
    SharpLogProductPolynomialThresholdChoice cHair cHairLog cCross cGrid
      cStrong target K b where
  C := P.C
  p := P.p
  Dn := P.Dn
  Dk := P.Dk
  threshold_gt_one :=
    polynomialGridMinorTreewidthBound_gt_one P.K_pos P.target_ge_two
  target_ge_two := P.target_ge_two
  scale_ge_two := two_le_logProductScale P.C_pos P.target_ge_two
  log_scale_bound := P.log_scale_bound
  threshold_log_bound := P.threshold_log_bound
  strong_scale_logProduct_sq :=
    strong_scale_logProduct_sq_of_coeff P.target_ge_two P.strong_coeff
  target_direct_logProduct :=
    target_direct_logProduct_of_coeff P.target_ge_two P.p_ge_two
      P.direct_coeff
  hairy_large_threshold :=
    hairy_large_threshold_of_coeff P.target_ge_two P.hairy_exponent
      P.hairy_coeff

/-- Coefficient-budget choices imply the exact parameter package consumed by
the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpCoefficientPolynomialThresholdChoice cHair cHairLog cCross cGrid
        cStrong target K b) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) :=
  P.toSharpLogProductPolynomialThresholdChoice.toParameterChoice

end SharpCoefficientPolynomialThresholdChoice

/-- Coefficient-budget package using the built-in `clog`-based logarithm
estimates for both the crossbar scale coefficient and the treewidth-threshold
coefficient. -/
structure SharpClogCoefficientPolynomialThresholdChoice
    (cHair cHairLog cCross cGrid cStrong target K b : ℕ) where
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- The crossbar-scale coefficient is positive. -/
  C_pos : 1 ≤ C
  /-- The threshold coefficient is positive. -/
  K_pos : 1 ≤ K
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The log-product exponent is large enough for the direct branch. -/
  p_ge_two : 2 ≤ p
  /-- Coefficient budget for the sharp strong-branch inequality. -/
  strong_coeff :
    4 * cCross * (max 2 cStrong) ^ 2 ≤ C ^ 2
  /-- Coefficient budget for the direct-branch inequality. -/
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  /-- Logarithmic exponent budget for the hairy-system inequality. -/
  hairy_exponent : p * 9 + 51 + cHairLog ≤ b
  /-- Strict coefficient budget for the hairy-system inequality. -/
  hairy_coeff :
    exponentHairyConstant cHair cGrid * C ^ 9 *
        (Nat.clog 2 C + p + 2) ^ 51 *
      (Nat.clog 2 K + 2 * 9 + b) ^ cHairLog < K

namespace SharpClogCoefficientPolynomialThresholdChoice

/-- Clog-coefficient choices imply coefficient-budget choices. -/
def toSharpCoefficientPolynomialThresholdChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpClogCoefficientPolynomialThresholdChoice cHair cHairLog cCross
        cGrid cStrong target K b) :
    SharpCoefficientPolynomialThresholdChoice cHair cHairLog cCross cGrid
      cStrong target K b where
  C := P.C
  p := P.p
  Dn := Nat.clog 2 P.C + P.p + 2
  Dk := Nat.clog 2 K + 2 * 9 + b
  C_pos := P.C_pos
  K_pos := P.K_pos
  target_ge_two := P.target_ge_two
  p_ge_two := P.p_ge_two
  log_scale_bound :=
    log_logProductScale_le_clog_const_mul_log P.C P.p P.target_ge_two
  threshold_log_bound := by
    simpa [polynomialGridMinorTreewidthBound_eq_monomialLogScale,
      monomialLogScale] using
      log_monomialLogScale_le_clog_const_mul_log K 9 b P.target_ge_two
  strong_coeff := P.strong_coeff
  direct_coeff := P.direct_coeff
  hairy_exponent := P.hairy_exponent
  hairy_coeff := P.hairy_coeff

/-- Clog-coefficient choices imply the exact parameter package consumed by the
graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpClogCoefficientPolynomialThresholdChoice cHair cHairLog cCross
        cGrid cStrong target K b) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound K b target) :=
  P.toSharpCoefficientPolynomialThresholdChoice.toParameterChoice

end SharpClogCoefficientPolynomialThresholdChoice

/-- Target-independent constants satisfying the clog-coefficient budgets.  A
template generates `SharpClogCoefficientPolynomialThresholdChoice`s for every
target `>= 2`. -/
structure SharpClogCoefficientPolynomialThresholdTemplate
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  /-- Coefficient in the public polynomial treewidth threshold. -/
  K : ℕ
  /-- Logarithmic exponent in the public polynomial treewidth threshold. -/
  b : ℕ
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- The threshold coefficient is positive. -/
  K_pos : 0 < K
  /-- The logarithmic exponent is positive. -/
  b_pos : 0 < b
  /-- The crossbar-scale coefficient is positive. -/
  C_pos : 1 ≤ C
  /-- The log-product exponent is large enough for the direct branch. -/
  p_ge_two : 2 ≤ p
  /-- Coefficient budget for the sharp strong-branch inequality. -/
  strong_coeff :
    4 * cCross * (max 2 cStrong) ^ 2 ≤ C ^ 2
  /-- Coefficient budget for the direct-branch inequality. -/
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  /-- Logarithmic exponent budget for the hairy-system inequality. -/
  hairy_exponent : p * 9 + 51 + cHairLog ≤ b
  /-- Strict coefficient budget for the hairy-system inequality. -/
  hairy_coeff :
    exponentHairyConstant cHair cGrid * C ^ 9 *
        (Nat.clog 2 C + p + 2) ^ 51 *
      (Nat.clog 2 K + 2 * 9 + b) ^ cHairLog < K

namespace SharpClogCoefficientPolynomialThresholdTemplate

/-- A target-independent template supplies clog-coefficient choices for every
target at least two. -/
def choiceAt
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (T :
      SharpClogCoefficientPolynomialThresholdTemplate cHair cHairLog cCross
        cGrid cStrong)
    (target : ℕ) (htarget : 2 ≤ target) :
    SharpClogCoefficientPolynomialThresholdChoice cHair cHairLog cCross cGrid
      cStrong target T.K T.b where
  C := T.C
  p := T.p
  C_pos := T.C_pos
  K_pos := Nat.succ_le_of_lt T.K_pos
  target_ge_two := htarget
  p_ge_two := T.p_ge_two
  strong_coeff := T.strong_coeff
  direct_coeff := T.direct_coeff
  hairy_exponent := T.hairy_exponent
  hairy_coeff := T.hairy_coeff

/-- A canonical target-independent template satisfying all clog-coefficient
budgets.  The constants are intentionally enormous but explicit; this closes
the remaining numerical side conditions without using asymptotic notation. -/
def canonical
    (cHair cHairLog cCross cGrid cStrong : ℕ) :
    SharpClogCoefficientPolynomialThresholdTemplate cHair cHairLog cCross
      cGrid cStrong := by
  let C := crossbarCoefficient cCross cGrid cStrong
  let b := 2 * 9 + 51 + cHairLog
  let A :=
    exponentHairyConstant cHair cGrid * C ^ 9 *
      (Nat.clog 2 C + 2 + 2) ^ 51
  let E := 2 * 9 + b
  refine
    { K := thresholdCoefficient A cHairLog E
      b := b
      C := C
      p := 2
      K_pos := ?_
      b_pos := ?_
      C_pos := ?_
      p_ge_two := le_rfl
      strong_coeff := ?_
      direct_coeff := ?_
      hairy_exponent := ?_
      hairy_coeff := ?_ }
  · dsimp [thresholdCoefficient]
    exact Nat.pow_pos (by decide : 0 < 2)
  · omega
  · dsimp [C, crossbarCoefficient]
    exact Nat.succ_le_of_lt
      (Nat.pow_pos (by decide : 0 < 2))
  · simpa [C] using
      strong_coeff_crossbarCoefficient cCross cGrid cStrong
  · simpa [C] using
      direct_coeff_crossbarCoefficient cCross cGrid cStrong
  · omega
  · simpa [A, E, Nat.add_assoc] using
      coeff_mul_clog_thresholdCoefficient_add_pow_lt A cHairLog E

end SharpClogCoefficientPolynomialThresholdTemplate

/-- Scale-only parameter package with the strong-branch scale fixed to the
canonical value `strongScale cStrong target`. -/
structure UnroundedScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The Chuzhoy--Tan Theorem 2.3 numerical hypothesis with canonical
  `ell`, `w`, and `r`. -/
  hairy_large :
    cHair * widthScale n * (lengthScale cGrid n) ^ 50 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_raw : 2 * (cCross * (strongScale cStrong target) ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n

namespace UnroundedScaleChoice

/-- Expand the two-choice package to the scale-only package. -/
def toScaleParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : UnroundedScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ScaleParameterChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  n := P.n
  r := strongScale cStrong target
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large := P.hairy_large
  n_ge_two := P.n_ge_two
  r_ge_two := strongScale_ge_two cStrong target
  strong_scale_raw := P.strong_scale_raw
  target_direct_raw := P.target_direct_raw
  target_strong := target_le_strongScale cStrong target

end UnroundedScaleChoice

/-- Unrounded scale package whose hairy-system inequality is stated with the
coarser unrounded upper bounds for length and width. -/
structure CoarseScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Coarse Chuzhoy--Tan Theorem 2.3 numerical hypothesis. -/
  hairy_large_coarse :
    cHair * coarseWidthScale n * (coarseLengthScale cGrid n) ^ 50 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_raw : 2 * (cCross * (strongScale cStrong target) ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n

namespace CoarseScaleChoice

/-- Coarse scale choices imply unrounded scale choices. -/
def toUnroundedScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : CoarseScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    UnroundedScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  n := P.n
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large :=
    hairy_large_of_coarse P.n_ge_two P.hairy_large_coarse
  n_ge_two := P.n_ge_two
  strong_scale_raw := P.strong_scale_raw
  target_direct_raw := P.target_direct_raw

end CoarseScaleChoice

/-- Scale package whose hairy-system inequality uses polynomial upper bounds
for the canonical length and width scales. -/
structure PolynomialScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Unrounded crossbar scale. -/
  n : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Polynomial upper-bound version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis. -/
  hairy_large_polynomial :
    cHair * polynomialWidthScale n * (polynomialLengthScale cGrid n) ^ 50 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The unrounded crossbar scale is at least two. -/
  n_ge_two : 2 ≤ n
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_raw : 2 * (cCross * (strongScale cStrong target) ^ 2) ≤ n
  /-- The rounded direct branch produces a grid at least as large as `target`. -/
  target_direct_raw : 2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤ n

namespace PolynomialScaleChoice

/-- Polynomial scale choices imply coarse scale choices. -/
def toCoarseScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : PolynomialScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    CoarseScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  n := P.n
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_coarse :=
    lt_of_le_of_lt
      (coarse_hairy_size_le_polynomial cHair cHairLog cGrid P.k P.n)
      P.hairy_large_polynomial
  n_ge_two := P.n_ge_two
  strong_scale_raw := P.strong_scale_raw
  target_direct_raw := P.target_direct_raw

end PolynomialScaleChoice

/-- Polynomial scale package where the unrounded crossbar scale is itself a
power of two, `n = 2^m`. -/
structure PowerScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Exponent of the power-of-two crossbar scale. -/
  m : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Polynomial upper-bound version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis with `n = 2^m`. -/
  hairy_large_power :
    cHair * polynomialWidthScale (2 ^ m) *
        (polynomialLengthScale cGrid (2 ^ m)) ^ 50 *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The exponent is positive, so `2^m >= 2`. -/
  m_pos : 0 < m
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_power : 2 * (cCross * (strongScale cStrong target) ^ 2) ≤ 2 ^ m
  /-- The direct branch produces a grid at least as large as `target`. -/
  target_direct_power : 2 * (cGrid * target * m ^ 2) ≤ 2 ^ m

namespace PowerScaleChoice

/-- Power-scale choices imply polynomial scale choices. -/
def toPolynomialScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : PowerScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    PolynomialScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  n := 2 ^ P.m
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_polynomial := P.hairy_large_power
  n_ge_two := CrossbarContract.two_le_two_pow P.m_pos
  strong_scale_raw := P.strong_scale_power
  target_direct_raw := by
    simpa [Nat.log_pow (by decide : 1 < 2)] using P.target_direct_power

end PowerScaleChoice

/-- Power-scale package whose hairy-system inequality is stated using the
monomial upper bound for the length and width scales. -/
structure MonomialScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Exponent of the power-of-two crossbar scale. -/
  m : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Monomial upper-bound version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis. -/
  hairy_large_monomial :
    cHair * (2 ^ 22 * (2 ^ m) ^ 10) *
        ((max 2 cGrid * (2 ^ m)) ^ 50) *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The exponent is positive, so `2^m >= 2`. -/
  m_pos : 0 < m
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_power : 2 * (cCross * (strongScale cStrong target) ^ 2) ≤ 2 ^ m
  /-- The direct branch produces a grid at least as large as `target`. -/
  target_direct_power : 2 * (cGrid * target * m ^ 2) ≤ 2 ^ m

namespace MonomialScaleChoice

/-- Monomial scale choices imply power-scale choices. -/
def toPowerScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : MonomialScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    PowerScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  m := P.m
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_power :=
    lt_of_le_of_lt
      (polynomial_hairy_size_le_monomial cHair cHairLog cGrid P.k (2 ^ P.m)
        (Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))))
      P.hairy_large_monomial
  m_pos := P.m_pos
  strong_scale_power := P.strong_scale_power
  target_direct_power := P.target_direct_power

end MonomialScaleChoice

/-- Power-scale package whose hairy-system inequality has been normalized to
one exponential factor in the power-of-two exponent. -/
structure ExponentScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Exponent of the power-of-two crossbar scale. -/
  m : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Exponent-normalized version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis. -/
  hairy_large_exponent :
    exponentHairyConstant cHair cGrid * 2 ^ (m * 60) *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The exponent is positive, so `2^m >= 2`. -/
  m_pos : 0 < m
  /-- The rounded strong branch can be thinned to the canonical strong scale. -/
  strong_scale_power : 2 * (cCross * (strongScale cStrong target) ^ 2) ≤ 2 ^ m
  /-- The direct branch produces a grid at least as large as `target`. -/
  target_direct_power : 2 * (cGrid * target * m ^ 2) ≤ 2 ^ m

namespace ExponentScaleChoice

/-- Exponent-normalized scale choices imply monomial scale choices. -/
def toMonomialScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : ExponentScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    MonomialScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  m := P.m
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_monomial :=
    hairy_large_of_exponent P.hairy_large_exponent
  m_pos := P.m_pos
  strong_scale_power := P.strong_scale_power
  target_direct_power := P.target_direct_power

end ExponentScaleChoice

/-- The single power-of-two domination requirement that implies both branch
size inequalities for the exponent-normalized parameter package. -/
def branchPowerRequirement
    (cCross cGrid cStrong target m : ℕ) : ℕ :=
  max (2 * (cCross * (strongScale cStrong target) ^ 2))
    (2 * (cGrid * target * m ^ 2))

/-- The branch requirement dominates the strong-branch size condition. -/
theorem strong_scale_power_le_branchPowerRequirement
    (cCross cGrid cStrong target m : ℕ) :
    2 * (cCross * (strongScale cStrong target) ^ 2) ≤
      branchPowerRequirement cCross cGrid cStrong target m :=
  le_max_left _ _

/-- The branch requirement dominates the direct-branch size condition. -/
theorem target_direct_power_le_branchPowerRequirement
    (cCross cGrid cStrong target m : ℕ) :
    2 * (cGrid * target * m ^ 2) ≤
      branchPowerRequirement cCross cGrid cStrong target m :=
  le_max_right _ _

/-- A branch-size package where the crossbar exponent is chosen as
`clog_2 B`.  This keeps the crossbar scale polynomial in a later parameter
`B`, instead of replacing `B` by a tower. -/
structure ClogBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Polynomial-sized upper scale for the branch requirements. -/
  B : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The branch scale is at least two, so `clog_2 B` is positive and
  `2^clog_2 B` is within a factor of two of `B`. -/
  B_ge_two : 2 ≤ B
  /-- The actual branch requirements fit below `B` once `m = clog_2 B`. -/
  branch_bound :
    branchPowerRequirement cCross cGrid cStrong target (Nat.clog 2 B) ≤ B
  /-- Hairy-system inequality after replacing `2^(60 * clog_2 B)` by
  `(2 * B)^60`. -/
  hairy_large_clog :
    exponentHairyConstant cHair cGrid * (2 * B) ^ 60 *
      (Nat.log 2 k) ^ cHairLog < k

namespace ClogBranchScaleChoice

/-- Clog branch choices imply exponent-normalized choices. -/
def toExponentScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : ClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ExponentScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  m := Nat.clog 2 P.B
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_exponent := by
    have hpow :
        2 ^ (Nat.clog 2 P.B * 60) =
          (2 ^ Nat.clog 2 P.B) ^ 60 := by
      rw [GridMinorArithmetic.two_pow_pow]
    have hle :
        exponentHairyConstant cHair cGrid *
            2 ^ (Nat.clog 2 P.B * 60) *
          (Nat.log 2 P.k) ^ cHairLog ≤
        exponentHairyConstant cHair cGrid * (2 * P.B) ^ 60 *
          (Nat.log 2 P.k) ^ cHairLog := by
      have hpow_le :
          (2 ^ Nat.clog 2 P.B) ^ 60 ≤ (2 * P.B) ^ 60 :=
        GridMinorArithmetic.two_pow_clog_pow_le_two_mul_pow
          (lt_of_lt_of_le (by decide : 1 < 2) P.B_ge_two)
      rw [hpow]
      calc
        exponentHairyConstant cHair cGrid *
            (2 ^ Nat.clog 2 P.B) ^ 60 *
          (Nat.log 2 P.k) ^ cHairLog
            =
          exponentHairyConstant cHair cGrid *
            ((2 ^ Nat.clog 2 P.B) ^ 60 *
              (Nat.log 2 P.k) ^ cHairLog) := by
            ac_rfl
        _ ≤ exponentHairyConstant cHair cGrid *
            ((2 * P.B) ^ 60 * (Nat.log 2 P.k) ^ cHairLog) :=
          Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right _ hpow_le)
        _ = exponentHairyConstant cHair cGrid * (2 * P.B) ^ 60 *
            (Nat.log 2 P.k) ^ cHairLog := by
          ac_rfl
    exact lt_of_le_of_lt hle P.hairy_large_clog
  m_pos := GridMinorArithmetic.clog_pos_of_two_le P.B_ge_two
  strong_scale_power :=
    le_trans
      (strong_scale_power_le_branchPowerRequirement cCross cGrid cStrong
        target (Nat.clog 2 P.B))
      (le_trans P.branch_bound (Nat.le_pow_clog (by decide : 1 < 2) P.B))
  target_direct_power :=
    le_trans
      (target_direct_power_le_branchPowerRequirement cCross cGrid cStrong
        target (Nat.clog 2 P.B))
      (le_trans P.branch_bound (Nat.le_pow_clog (by decide : 1 < 2) P.B))

/-- Clog branch choices imply the exact parameter package consumed by the
graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : ClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw := by
  let pExponent := P.toExponentScaleChoice
  let pMonomial := pExponent.toMonomialScaleChoice
  let pPower := pMonomial.toPowerScaleChoice
  let pPolynomial := pPower.toPolynomialScaleChoice
  let pCoarse := pPolynomial.toCoarseScaleChoice
  let pUnrounded := pCoarse.toUnroundedScaleChoice
  let pScale := pUnrounded.toScaleParameterChoice
  let pRounded := pScale.toRoundedParameterChoice
  exact pRounded.toParameterChoice

end ClogBranchScaleChoice

/-- Clog-rounded branch package where the branch upper scale is a monomial
`C * target^a`.  This is the polynomial-shaped interface used before choosing
large enough constants and exponent. -/
structure PolynomialClogBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Coefficient of the monomial branch scale. -/
  C : ℕ
  /-- Exponent of the monomial branch scale. -/
  a : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The target grid order is nonzero; later applications use `target >= 2`. -/
  target_pos : 1 ≤ target
  /-- The monomial branch scale is at least two. -/
  branch_scale_ge_two : 2 ≤ C * target ^ a
  /-- The strong branch requirement is bounded by the monomial scale. -/
  strong_branch_polynomial :
    2 * (cCross * (strongScale cStrong target) ^ 2) ≤ C * target ^ a
  /-- The direct branch requirement is bounded using the linear logarithm
  estimate for `clog_2 (C * target^a)`. -/
  direct_branch_polynomial :
    2 * (cGrid * target * ((C + a) * target) ^ 2) ≤ C * target ^ a
  /-- Hairy-system inequality after replacing the rounded exponent by the
  monomial branch scale. -/
  hairy_large_polynomial_clog :
    exponentHairyConstant cHair cGrid * (2 * (C * target ^ a)) ^ 60 *
      (Nat.log 2 k) ^ cHairLog < k

namespace PolynomialClogBranchScaleChoice

/-- Polynomial clog branch choices imply clog-rounded branch choices. -/
def toClogBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      PolynomialClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    ClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  B := P.C * target ^ P.a
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  B_ge_two := P.branch_scale_ge_two
  branch_bound := by
    rw [branchPowerRequirement]
    apply max_le
    · exact P.strong_branch_polynomial
    · have hclog :
          Nat.clog 2 (P.C * target ^ P.a) ≤ (P.C + P.a) * target :=
        GridMinorArithmetic.clog_mul_pow_le_linear P.target_pos
      have hclog_sq :
          (Nat.clog 2 (P.C * target ^ P.a)) ^ 2 ≤
            ((P.C + P.a) * target) ^ 2 :=
        Nat.pow_le_pow_left hclog 2
      calc
        2 * (cGrid * target *
            (Nat.clog 2 (P.C * target ^ P.a)) ^ 2)
            ≤
          2 * (cGrid * target * ((P.C + P.a) * target) ^ 2) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (cGrid * target) hclog_sq)
        _ ≤ P.C * target ^ P.a := P.direct_branch_polynomial
  hairy_large_clog := P.hairy_large_polynomial_clog

/-- Polynomial clog branch choices imply the exact parameter package consumed
by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P :
      PolynomialClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong
        target tw) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target tw :=
  P.toClogBranchScaleChoice.toParameterChoice

end PolynomialClogBranchScaleChoice

/-- Polynomial clog branch package with a monomial treewidth threshold
`K * target^b`.  The logarithmic factor `log k` is bounded by the linear
quantity `(K + b) * target`. -/
structure MonomialThresholdClogBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target threshold : ℕ) where
  /-- Coefficient of the monomial branch scale. -/
  C : ℕ
  /-- Exponent of the monomial branch scale. -/
  a : ℕ
  /-- Coefficient of the monomial treewidth threshold. -/
  K : ℕ
  /-- Exponent of the monomial treewidth threshold. -/
  b : ℕ
  /-- The threshold is the monomial `K * target^b`. -/
  threshold_eq : threshold = K * target ^ b
  /-- The threshold is nontrivial. -/
  threshold_gt_one : 1 < threshold
  /-- The target grid order is nonzero; later applications use `target >= 2`. -/
  target_pos : 1 ≤ target
  /-- The monomial branch scale is at least two. -/
  branch_scale_ge_two : 2 ≤ C * target ^ a
  /-- The strong branch requirement is bounded by the monomial branch scale. -/
  strong_branch_polynomial :
    2 * (cCross * (strongScale cStrong target) ^ 2) ≤ C * target ^ a
  /-- The direct branch requirement is bounded by the monomial branch scale. -/
  direct_branch_polynomial :
    2 * (cGrid * target * ((C + a) * target) ^ 2) ≤ C * target ^ a
  /-- The hairy-system inequality after bounding `log_2 threshold` by
  `(K + b) * target`. -/
  hairy_large_monomial_threshold :
    exponentHairyConstant cHair cGrid * (2 * (C * target ^ a)) ^ 60 *
        ((K + b) * target) ^ cHairLog < K * target ^ b

namespace MonomialThresholdClogBranchScaleChoice

/-- Monomial-threshold choices imply polynomial clog branch choices. -/
def toPolynomialClogBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      MonomialThresholdClogBranchScaleChoice cHair cHairLog cCross cGrid
        cStrong target threshold) :
    PolynomialClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong
        target threshold where
  k := threshold
  C := P.C
  a := P.a
  k_gt_one := P.threshold_gt_one
  k_le_treewidth := le_rfl
  target_pos := P.target_pos
  branch_scale_ge_two := P.branch_scale_ge_two
  strong_branch_polynomial := P.strong_branch_polynomial
  direct_branch_polynomial := P.direct_branch_polynomial
  hairy_large_polynomial_clog := by
    have hclog :
        Nat.clog 2 (P.K * target ^ P.b) ≤ (P.K + P.b) * target :=
      GridMinorArithmetic.clog_mul_pow_le_linear P.target_pos
    have hlog_poly :
        Nat.log 2 (P.K * target ^ P.b) ≤ (P.K + P.b) * target :=
      le_trans (Nat.log_le_clog 2 (P.K * target ^ P.b)) hclog
    have hlog :
        Nat.log 2 threshold ≤ (P.K + P.b) * target := by
      simpa [P.threshold_eq] using hlog_poly
    have hlog_pow :
        (Nat.log 2 threshold) ^ cHairLog ≤
          ((P.K + P.b) * target) ^ cHairLog :=
      Nat.pow_le_pow_left hlog cHairLog
    have hle :
        exponentHairyConstant cHair cGrid *
            (2 * (P.C * target ^ P.a)) ^ 60 *
          (Nat.log 2 threshold) ^ cHairLog ≤
        exponentHairyConstant cHair cGrid *
            (2 * (P.C * target ^ P.a)) ^ 60 *
          ((P.K + P.b) * target) ^ cHairLog := by
      calc
        exponentHairyConstant cHair cGrid *
            (2 * (P.C * target ^ P.a)) ^ 60 *
          (Nat.log 2 threshold) ^ cHairLog
            =
          (exponentHairyConstant cHair cGrid *
            (2 * (P.C * target ^ P.a)) ^ 60) *
          (Nat.log 2 threshold) ^ cHairLog := by
            ac_rfl
        _ ≤ (exponentHairyConstant cHair cGrid *
            (2 * (P.C * target ^ P.a)) ^ 60) *
          ((P.K + P.b) * target) ^ cHairLog :=
            Nat.mul_le_mul_left _ hlog_pow
        _ =
          exponentHairyConstant cHair cGrid *
            (2 * (P.C * target ^ P.a)) ^ 60 *
          ((P.K + P.b) * target) ^ cHairLog := by
            ac_rfl
    exact lt_of_le_of_lt hle (by
      simpa [P.threshold_eq] using P.hairy_large_monomial_threshold)

/-- Monomial-threshold choices imply the exact parameter package consumed by
the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      MonomialThresholdClogBranchScaleChoice cHair cHairLog cCross cGrid
        cStrong target threshold) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target threshold :=
  P.toPolynomialClogBranchScaleChoice.toParameterChoice

end MonomialThresholdClogBranchScaleChoice

/-- A constant that dominates both coefficients in the branch power
requirement after bounding the canonical strong scale linearly in the target. -/
def branchRequirementConstant
    (cCross cGrid cStrong : ℕ) : ℕ :=
  max (2 * cCross * (max 2 cStrong) ^ 2) (2 * cGrid)

/-- The branch power requirement is bounded by a quadratic expression in the
target and the exponent. -/
theorem branchPowerRequirement_le_quadratic
    {cCross cGrid cStrong target m : ℕ}
    (htarget : 1 ≤ target) (hm : 1 ≤ m) :
    branchPowerRequirement cCross cGrid cStrong target m ≤
      branchRequirementConstant cCross cGrid cStrong * target ^ 2 * m ^ 2 := by
  have htarget_sq : target ≤ target ^ 2 :=
    Nat.le_self_pow (a := target) (by decide : (2 : ℕ) ≠ 0)
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 1) hm
  have hm_sq : 1 ≤ m ^ 2 :=
    Nat.succ_le_of_lt (Nat.pow_pos hm_pos)
  rw [branchPowerRequirement]
  apply max_le
  · have hstrong_sq :
        (strongScale cStrong target) ^ 2 ≤
          (max 2 cStrong * target) ^ 2 :=
      Nat.pow_le_pow_left (strongScale_le_const_mul htarget) 2
    calc
      2 * (cCross * (strongScale cStrong target) ^ 2)
          =
        (2 * cCross) * (strongScale cStrong target) ^ 2 := by
          ac_rfl
      _ ≤ (2 * cCross) * (max 2 cStrong * target) ^ 2 :=
        Nat.mul_le_mul_left _ hstrong_sq
      _ = (2 * cCross) * ((max 2 cStrong) ^ 2 * target ^ 2) := by
        rw [mul_pow]
      _ = (2 * cCross * (max 2 cStrong) ^ 2) * target ^ 2 := by
        ac_rfl
      _ ≤ branchRequirementConstant cCross cGrid cStrong * target ^ 2 :=
        Nat.mul_le_mul_right _ (le_max_left _ _)
      _ ≤ branchRequirementConstant cCross cGrid cStrong * target ^ 2 *
          m ^ 2 := by
        calc
          branchRequirementConstant cCross cGrid cStrong * target ^ 2 =
              branchRequirementConstant cCross cGrid cStrong * target ^ 2 *
                1 := by simp
          _ ≤ branchRequirementConstant cCross cGrid cStrong * target ^ 2 *
              m ^ 2 :=
            Nat.mul_le_mul_left _ hm_sq
  · calc
      2 * (cGrid * target * m ^ 2)
          =
        (2 * cGrid) * (target * m ^ 2) := by
          ac_rfl
      _ ≤ branchRequirementConstant cCross cGrid cStrong * (target * m ^ 2) :=
        Nat.mul_le_mul_right _ (le_max_right _ _)
      _ ≤ branchRequirementConstant cCross cGrid cStrong *
          (target ^ 2 * m ^ 2) :=
        Nat.mul_le_mul_left _
          (Nat.mul_le_mul_right (m ^ 2) htarget_sq)
      _ = branchRequirementConstant cCross cGrid cStrong * target ^ 2 *
          m ^ 2 := by
        ac_rfl

/-- If the branch coefficient is at most `2^q`, then choosing `m = 2^q`
discharges the quadratic branch power condition. -/
theorem quadratic_branch_power_of_two_pow_exponent
    {cCross cGrid cStrong target q : ℕ}
    (hcoeff :
      branchRequirementConstant cCross cGrid cStrong * target ^ 2 ≤ 2 ^ q)
    (hq : 4 ≤ q) :
    branchRequirementConstant cCross cGrid cStrong * target ^ 2 *
        (2 ^ q) ^ 2 ≤
      2 ^ (2 ^ q) := by
  calc
    branchRequirementConstant cCross cGrid cStrong * target ^ 2 *
        (2 ^ q) ^ 2
        ≤ 2 ^ q * (2 ^ q) ^ 2 := Nat.mul_le_mul_right _ hcoeff
    _ = (2 ^ q) ^ 3 := by
      rw [show (2 ^ q) ^ 3 = (2 ^ q) ^ 2 * 2 ^ q by
        rw [Nat.pow_succ]]
      ac_rfl
    _ ≤ 2 ^ (2 ^ q) :=
      GridMinorArithmetic.two_pow_cube_le_two_pow_two_pow_of_four_le hq

/-- For a double-power threshold `2^(2^r)`, the hairy-system inequality
follows from an exponent budget. -/
theorem hairy_large_powerThreshold_of_exponent_budget
    {cHair cHairLog cGrid q r a : ℕ}
    (hconstant : exponentHairyConstant cHair cGrid ≤ 2 ^ a)
    (hbudget : a + (2 ^ q) * 60 + r * cHairLog < 2 ^ r) :
    exponentHairyConstant cHair cGrid * 2 ^ ((2 ^ q) * 60) *
        (2 ^ r) ^ cHairLog <
      2 ^ (2 ^ r) := by
  have hpow :
      (2 ^ r) ^ cHairLog = 2 ^ (r * cHairLog) :=
    GridMinorArithmetic.two_pow_pow r cHairLog
  calc
    exponentHairyConstant cHair cGrid * 2 ^ ((2 ^ q) * 60) *
        (2 ^ r) ^ cHairLog
        =
      exponentHairyConstant cHair cGrid *
        (2 ^ ((2 ^ q) * 60) * 2 ^ (r * cHairLog)) := by
        rw [hpow]
        ac_rfl
    _ ≤ 2 ^ a * (2 ^ ((2 ^ q) * 60) * 2 ^ (r * cHairLog)) :=
      Nat.mul_le_mul_right _ hconstant
    _ = 2 ^ a * 2 ^ ((2 ^ q) * 60) * 2 ^ (r * cHairLog) := by
      ac_rfl
    _ = 2 ^ (a + (2 ^ q) * 60 + r * cHairLog) := by
      rw [← pow_add, ← pow_add]
    _ < 2 ^ (2 ^ r) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) hbudget

/-- A convenient way to satisfy the double-power exponent budget: choose
`r = 2^p` and make the remaining coefficient fit below `2^p`. -/
theorem double_power_budget_of_coefficient_power
    {a b c p : ℕ}
    (hcoeff : a + b + c ≤ 2 ^ p) (hp : 4 ≤ p) :
    a + b + (2 ^ p) * c < 2 ^ (2 ^ p) := by
  let X := 2 ^ p
  have hX_ge_one : 1 ≤ X :=
    Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
  have hX_gt_one : 1 < X := by
    exact lt_of_lt_of_le (by decide : 1 < 2)
      (CrossbarContract.two_le_two_pow
        (lt_of_lt_of_le (by decide : 0 < 4) hp))
  have hsquare_lt_cube : X * X < X ^ 3 := by
    calc
      X * X = X ^ 2 := by rw [Nat.pow_two]
      _ < X ^ 3 := Nat.pow_lt_pow_right hX_gt_one (by decide : 2 < 3)
  calc
    a + b + X * c
        ≤ X * (a + b) + X * c := by
          exact Nat.add_le_add_right
            (by
              calc
                a + b = 1 * (a + b) := by simp
                _ ≤ X * (a + b) :=
                  Nat.mul_le_mul_right (a + b) hX_ge_one)
            (X * c)
    _ = X * ((a + b) + c) := by
      simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = X * (a + b + c) := rfl
    _ ≤ X * X := Nat.mul_le_mul_left X hcoeff
    _ < X ^ 3 := hsquare_lt_cube
    _ ≤ 2 ^ (2 ^ p) := by
      simpa [X] using
        GridMinorArithmetic.two_pow_cube_le_two_pow_two_pow_of_four_le hp

/-- Exponent-normalized scale package where both branch inequalities are
compressed into one power-of-two lower bound. -/
structure BranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Exponent of the power-of-two crossbar scale. -/
  m : ℕ
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- Exponent-normalized version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis. -/
  hairy_large_exponent :
    exponentHairyConstant cHair cGrid * 2 ^ (m * 60) *
      (Nat.log 2 k) ^ cHairLog < k
  /-- The exponent is positive, so `2^m >= 2`. -/
  m_pos : 0 < m
  /-- One bound implying both branch-size requirements. -/
  branch_power :
    branchPowerRequirement cCross cGrid cStrong target m ≤ 2 ^ m

namespace BranchScaleChoice

/-- Branch-compressed scale choices imply exponent-normalized scale choices. -/
def toExponentScaleChoice
    {cHair cHairLog cCross cGrid cStrong target tw : ℕ}
    (P : BranchScaleChoice cHair cHairLog cCross cGrid cStrong target tw) :
    ExponentScaleChoice cHair cHairLog cCross cGrid cStrong target tw where
  k := P.k
  m := P.m
  k_gt_one := P.k_gt_one
  k_le_treewidth := P.k_le_treewidth
  hairy_large_exponent := P.hairy_large_exponent
  m_pos := P.m_pos
  strong_scale_power :=
    le_trans
      (strong_scale_power_le_branchPowerRequirement cCross cGrid cStrong
        target P.m)
      P.branch_power
  target_direct_power :=
    le_trans
      (target_direct_power_le_branchPowerRequirement cCross cGrid cStrong
        target P.m)
      P.branch_power

end BranchScaleChoice

/-- Branch-compressed scale package with the treewidth scale fixed to the
threshold value itself.  This is the final proof-facing arithmetic interface:
one chooses only the exponent `m` for each target order. -/
structure ThresholdBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target threshold : ℕ) where
  /-- Exponent of the power-of-two crossbar scale. -/
  m : ℕ
  /-- The threshold is nontrivial, so it can serve as the `k` parameter. -/
  threshold_gt_one : 1 < threshold
  /-- Exponent-normalized version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis with `k = threshold`. -/
  hairy_large_exponent :
    exponentHairyConstant cHair cGrid * 2 ^ (m * 60) *
      (Nat.log 2 threshold) ^ cHairLog < threshold
  /-- The exponent is positive, so `2^m >= 2`. -/
  m_pos : 0 < m
  /-- One bound implying both branch-size requirements. -/
  branch_power :
    branchPowerRequirement cCross cGrid cStrong target m ≤ 2 ^ m

namespace ThresholdBranchScaleChoice

/-- A threshold-fixed branch choice is a branch-compressed choice at that
threshold. -/
def toBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      ThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold) :
    BranchScaleChoice cHair cHairLog cCross cGrid cStrong target threshold where
  k := threshold
  m := P.m
  k_gt_one := P.threshold_gt_one
  k_le_treewidth := le_rfl
  hairy_large_exponent := P.hairy_large_exponent
  m_pos := P.m_pos
  branch_power := P.branch_power

end ThresholdBranchScaleChoice

/-- Threshold-fixed scale package where the branch power requirement has been
replaced by a single quadratic upper bound. -/
structure QuadraticBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target threshold : ℕ) where
  /-- Exponent of the power-of-two crossbar scale. -/
  m : ℕ
  /-- The threshold is nontrivial, so it can serve as the `k` parameter. -/
  threshold_gt_one : 1 < threshold
  /-- Exponent-normalized version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis with `k = threshold`. -/
  hairy_large_exponent :
    exponentHairyConstant cHair cGrid * 2 ^ (m * 60) *
      (Nat.log 2 threshold) ^ cHairLog < threshold
  /-- The exponent is positive, so `2^m >= 2`. -/
  m_pos : 0 < m
  /-- A quadratic upper bound dominates both branch-size requirements. -/
  quadratic_branch_power :
    branchRequirementConstant cCross cGrid cStrong * target ^ 2 * m ^ 2 ≤
      2 ^ m

namespace QuadraticBranchScaleChoice

/-- Quadratic branch choices imply threshold-fixed branch choices. -/
def toThresholdBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      QuadraticBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold)
    (htarget : 2 ≤ target) :
    ThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold where
  m := P.m
  threshold_gt_one := P.threshold_gt_one
  hairy_large_exponent := P.hairy_large_exponent
  m_pos := P.m_pos
  branch_power :=
    le_trans
      (branchPowerRequirement_le_quadratic
        (le_trans (by decide : 1 ≤ 2) htarget)
        (Nat.succ_le_of_lt P.m_pos))
      P.quadratic_branch_power

/-- Quadratic branch choices imply the exact parameter package consumed by the
graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      QuadraticBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold)
    (htarget : 2 ≤ target) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target threshold := by
  let pThreshold := P.toThresholdBranchScaleChoice htarget
  let pBranch := pThreshold.toBranchScaleChoice
  let pExponent := pBranch.toExponentScaleChoice
  let pMonomial := pExponent.toMonomialScaleChoice
  let pPower := pMonomial.toPowerScaleChoice
  let pPolynomial := pPower.toPolynomialScaleChoice
  let pCoarse := pPolynomial.toCoarseScaleChoice
  let pUnrounded := pCoarse.toUnroundedScaleChoice
  let pScale := pUnrounded.toScaleParameterChoice
  let pRounded := pScale.toRoundedParameterChoice
  exact pRounded.toParameterChoice

end QuadraticBranchScaleChoice

/-- Threshold-fixed scale package where the branch exponent is itself chosen
as a power of two, `m = 2^q`. -/
structure PowerBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target threshold : ℕ) where
  /-- Exponent used to define `m = 2^q`. -/
  q : ℕ
  /-- The threshold is nontrivial, so it can serve as the `k` parameter. -/
  threshold_gt_one : 1 < threshold
  /-- Exponent-normalized version of the Chuzhoy--Tan Theorem 2.3 numerical
  hypothesis with `m = 2^q` and `k = threshold`. -/
  hairy_large_exponent :
    exponentHairyConstant cHair cGrid * 2 ^ ((2 ^ q) * 60) *
      (Nat.log 2 threshold) ^ cHairLog < threshold
  /-- The exponent `q` is large enough for the cubic domination lemma. -/
  q_ge_four : 4 ≤ q
  /-- The non-`m` coefficient in the quadratic branch condition is at most
  `2^q`. -/
  branch_coefficient_power :
    branchRequirementConstant cCross cGrid cStrong * target ^ 2 ≤ 2 ^ q

namespace PowerBranchScaleChoice

/-- Power-branch choices imply quadratic branch choices. -/
def toQuadraticBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      PowerBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold) :
    QuadraticBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold where
  m := 2 ^ P.q
  threshold_gt_one := P.threshold_gt_one
  hairy_large_exponent := P.hairy_large_exponent
  m_pos := Nat.pow_pos (by decide : 0 < 2)
  quadratic_branch_power :=
    quadratic_branch_power_of_two_pow_exponent P.branch_coefficient_power
      P.q_ge_four

/-- Power-branch choices imply the exact parameter package consumed by the
graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      PowerBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold)
    (htarget : 2 ≤ target) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target threshold :=
  (P.toQuadraticBranchScaleChoice).toParameterChoice htarget

end PowerBranchScaleChoice

/-- Power-branch scale package where the threshold itself is a power of two,
so the logarithmic factor in the hairy-system inequality is explicit. -/
structure PowerThresholdBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target threshold : ℕ) where
  /-- Exponent used to define `m = 2^q`. -/
  q : ℕ
  /-- Exponent used to define the threshold `2^s`. -/
  s : ℕ
  /-- The threshold is exactly `2^s`. -/
  threshold_eq : threshold = 2 ^ s
  /-- The threshold exponent is positive. -/
  s_pos : 0 < s
  /-- Exponent-normalized hairy-system inequality after rewriting
  `log_2 threshold = s`. -/
  hairy_large_powerThreshold :
    exponentHairyConstant cHair cGrid * 2 ^ ((2 ^ q) * 60) *
      s ^ cHairLog < 2 ^ s
  /-- The exponent `q` is large enough for the cubic domination lemma. -/
  q_ge_four : 4 ≤ q
  /-- The non-`m` coefficient in the quadratic branch condition is at most
  `2^q`. -/
  branch_coefficient_power :
    branchRequirementConstant cCross cGrid cStrong * target ^ 2 ≤ 2 ^ q

namespace PowerThresholdBranchScaleChoice

/-- Power-threshold branch choices imply power-branch choices. -/
def toPowerBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      PowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong
        target threshold) :
    PowerBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold where
  q := P.q
  threshold_gt_one := by
    simpa [P.threshold_eq] using
      (lt_of_lt_of_le (by decide : 1 < 2)
        (CrossbarContract.two_le_two_pow P.s_pos))
  hairy_large_exponent := by
    simpa [P.threshold_eq, Nat.log_pow (by decide : 1 < 2)] using
      P.hairy_large_powerThreshold
  q_ge_four := P.q_ge_four
  branch_coefficient_power := P.branch_coefficient_power

/-- Power-threshold branch choices imply the exact parameter package consumed
by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      PowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong
        target threshold)
    (htarget : 2 ≤ target) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target threshold :=
  P.toPowerBranchScaleChoice.toParameterChoice htarget

end PowerThresholdBranchScaleChoice

/-- Power-threshold branch package with threshold `2^(2^r)` and the hairy
inequality reduced to an exponent budget below `2^r`. -/
structure DoublePowerThresholdBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target threshold : ℕ) where
  /-- Exponent used to define `m = 2^q`. -/
  q : ℕ
  /-- Exponent used to define the threshold `2^(2^r)`. -/
  r : ℕ
  /-- Exponent bounding the constant in the hairy-system inequality. -/
  a : ℕ
  /-- The threshold is exactly `2^(2^r)`. -/
  threshold_eq : threshold = 2 ^ (2 ^ r)
  /-- The constant in the hairy-system inequality is at most `2^a`. -/
  exponent_constant_power :
    exponentHairyConstant cHair cGrid ≤ 2 ^ a
  /-- The remaining exponent budget fits below `2^r`. -/
  hairy_exponent_budget :
    a + (2 ^ q) * 60 + r * cHairLog < 2 ^ r
  /-- The exponent `q` is large enough for the cubic domination lemma. -/
  q_ge_four : 4 ≤ q
  /-- The non-`m` coefficient in the quadratic branch condition is at most
  `2^q`. -/
  branch_coefficient_power :
    branchRequirementConstant cCross cGrid cStrong * target ^ 2 ≤ 2 ^ q

namespace DoublePowerThresholdBranchScaleChoice

/-- Double-power threshold branch choices imply power-threshold branch
choices. -/
def toPowerThresholdBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      DoublePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid
        cStrong target threshold) :
    PowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
        threshold where
  q := P.q
  s := 2 ^ P.r
  threshold_eq := P.threshold_eq
  s_pos := Nat.pow_pos (by decide : 0 < 2)
  hairy_large_powerThreshold :=
    hairy_large_powerThreshold_of_exponent_budget P.exponent_constant_power
      P.hairy_exponent_budget
  q_ge_four := P.q_ge_four
  branch_coefficient_power := P.branch_coefficient_power

/-- Double-power threshold branch choices imply the exact parameter package
consumed by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      DoublePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid
        cStrong target threshold)
    (htarget : 2 ≤ target) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target threshold :=
  P.toPowerThresholdBranchScaleChoice.toParameterChoice htarget

end DoublePowerThresholdBranchScaleChoice

/-- Double-power threshold branch package where `r = 2^p`, so the hairy
exponent budget is reduced to one coefficient bound below `2^p`. -/
structure TriplePowerThresholdBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target threshold : ℕ) where
  /-- Exponent used to define `m = 2^q`. -/
  q : ℕ
  /-- Exponent used to define `r = 2^p`. -/
  p : ℕ
  /-- Exponent bounding the constant in the hairy-system inequality. -/
  a : ℕ
  /-- The threshold is exactly `2^(2^(2^p))`. -/
  threshold_eq : threshold = 2 ^ (2 ^ (2 ^ p))
  /-- The constant in the hairy-system inequality is at most `2^a`. -/
  exponent_constant_power :
    exponentHairyConstant cHair cGrid ≤ 2 ^ a
  /-- The non-`r` coefficient in the hairy exponent budget is at most `2^p`. -/
  hairy_coefficient_power :
    a + (2 ^ q) * 60 + cHairLog ≤ 2 ^ p
  /-- The exponent `p` is large enough for the cubic domination lemma. -/
  p_ge_four : 4 ≤ p
  /-- The exponent `q` is large enough for the cubic domination lemma. -/
  q_ge_four : 4 ≤ q
  /-- The non-`m` coefficient in the quadratic branch condition is at most
  `2^q`. -/
  branch_coefficient_power :
    branchRequirementConstant cCross cGrid cStrong * target ^ 2 ≤ 2 ^ q

namespace TriplePowerThresholdBranchScaleChoice

/-- Triple-power threshold branch choices imply double-power threshold branch
choices. -/
def toDoublePowerThresholdBranchScaleChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      TriplePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid
        cStrong target threshold) :
    DoublePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong
        target threshold where
  q := P.q
  r := 2 ^ P.p
  a := P.a
  threshold_eq := P.threshold_eq
  exponent_constant_power := P.exponent_constant_power
  hairy_exponent_budget :=
    double_power_budget_of_coefficient_power P.hairy_coefficient_power
      P.p_ge_four
  q_ge_four := P.q_ge_four
  branch_coefficient_power := P.branch_coefficient_power

/-- Triple-power threshold branch choices imply the exact parameter package
consumed by the graph-theoretic proof skeleton. -/
def toParameterChoice
    {cHair cHairLog cCross cGrid cStrong target threshold : ℕ}
    (P :
      TriplePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid
        cStrong target threshold)
    (htarget : 2 ≤ target) :
    ParameterChoice cHair cHairLog cCross cGrid cStrong target threshold :=
  P.toDoublePowerThresholdBranchScaleChoice.toParameterChoice htarget

end TriplePowerThresholdBranchScaleChoice

/-- Exponent `q` used by the explicit tower-threshold fallback.  It is chosen
large enough that the branch coefficient is at most `2^q`. -/
def towerBranchExponent
    (cCross cGrid cStrong target : ℕ) : ℕ :=
  max 4 (branchRequirementConstant cCross cGrid cStrong * target ^ 2)

/-- Exponent `a` bounding the constant in the hairy-system inequality for the
explicit tower-threshold fallback. -/
def towerHairyConstantExponent (cHair cGrid : ℕ) : ℕ :=
  exponentHairyConstant cHair cGrid

/-- Exponent `p` used by the explicit tower-threshold fallback.  It is chosen
large enough that the hairy exponent budget fits below `2^p`. -/
def towerHairyBudgetExponent
    (cHair cHairLog cCross cGrid cStrong target : ℕ) : ℕ :=
  max 4
    (towerHairyConstantExponent cHair cGrid +
      2 ^ (towerBranchExponent cCross cGrid cStrong target) * 60 +
        cHairLog)

/-- Explicit tower-type threshold obtained from the formalized proof skeleton.

This threshold is intentionally much larger than the Chuzhoy--Tan polynomial
bound.  Its role is to close the currently formalized composition without using
the final polynomial theorem contract. -/
def towerGridMinorThreshold
    (cHair cHairLog cCross cGrid cStrong target : ℕ) : ℕ :=
  2 ^ (2 ^ (2 ^ (towerHairyBudgetExponent cHair cHairLog cCross cGrid
    cStrong target)))

/-- The explicit tower threshold supplies the triple-power numerical package. -/
def towerTriplePowerThresholdBranchScaleChoice
    (cHair cHairLog cCross cGrid cStrong target : ℕ) :
    TriplePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong
      target
      (towerGridMinorThreshold cHair cHairLog cCross cGrid cStrong target) where
  q := towerBranchExponent cCross cGrid cStrong target
  p := towerHairyBudgetExponent cHair cHairLog cCross cGrid cStrong target
  a := towerHairyConstantExponent cHair cGrid
  threshold_eq := rfl
  exponent_constant_power :=
    GridMinorArithmetic.self_le_two_pow (towerHairyConstantExponent cHair cGrid)
  hairy_coefficient_power := by
    exact le_trans
      (le_max_right 4
        (towerHairyConstantExponent cHair cGrid +
          2 ^ (towerBranchExponent cCross cGrid cStrong target) * 60 +
            cHairLog))
      (GridMinorArithmetic.self_le_two_pow
        (towerHairyBudgetExponent cHair cHairLog cCross cGrid cStrong target))
  p_ge_four := le_max_left 4 _
  q_ge_four := le_max_left 4 _
  branch_coefficient_power := by
    exact le_trans
      (le_max_right 4
        (branchRequirementConstant cCross cGrid cStrong * target ^ 2))
      (GridMinorArithmetic.self_le_two_pow
        (towerBranchExponent cCross cGrid cStrong target))









/-- Axiom-free parameterized proof after both branch lower bounds, from
explicit hard inputs instead of contract wrappers. -/
theorem containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target := by
  rcases
    gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs
      hhairyInput hcrossInput hstrongGrid hlargeData with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r target hell hw hk htw hhairyLarge hg hr hpow
    hellGrid hwGrid hlarge hscaled htargetDirect htargetStrong
  rcases hmain G hell hw hk htw hhairyLarge hg hr hpow hellGrid hwGrid hlarge
      hscaled with hdirect | hstrong
  · rcases hdirect with ⟨g', hproduced, hgrid⟩
    exact hgrid.of_order_le
      (le_gridOrder_of_direct_branch_bound hcGrid hg htargetDirect hproduced)
  · rcases hstrong with ⟨r', hproduced, hgrid⟩
    have htarget_le : target ≤ r' :=
      le_of_const_mul_le_const_mul hcStrong (le_trans htargetStrong hproduced)
    exact hgrid.of_order_le htarget_le

/-- Axiom-free parameterized proof after both branch lower bounds, using the
Section 4 weak `g^10 log g` crossbar input. -/
theorem containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs10
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target := by
  rcases
    gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs10
      hhairyInput hcrossInput hstrongGrid hlargeData with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r target hell hw hk htw hhairyLarge hg hr hpow
    hellGrid hwGrid hlarge hscaled htargetDirect htargetStrong
  rcases hmain G hell hw hk htw hhairyLarge hg hr hpow hellGrid hwGrid hlarge
      hscaled with hdirect | hstrong
  · rcases hdirect with ⟨g', hproduced, hgrid⟩
    exact hgrid.of_order_le
      (le_gridOrder_of_direct_branch_bound hcGrid hg htargetDirect hproduced)
  · rcases hstrong with ⟨r', hproduced, hgrid⟩
    have htarget_le : target ≤ r' :=
      le_of_const_mul_le_const_mul hcStrong (le_trans htargetStrong hproduced)
    exact hgrid.of_order_le htarget_le

/-- Parameterized proof using the formal Appendix A.2/A.4 hairy route and
the Section 4 weak crossbar route.  The remaining hypotheses are the
degree-three strong path-of-sets input, the pseudo-grid branch of
Sections 4.2--4.6, the strong-minor-to-grid input, and the large-case
cut-matching data provider. -/
theorem containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_appendixA2_and_section4_inputs
    (hhairyPaper :
      ∃ cStrong cStrongLog cSplit : ℕ,
        0 < cStrong ∧
          0 < cStrongLog ∧
            0 < cSplit ∧
              HairyPathOfSetsTheorem.DegreeThreeStrongPathOfSetsInput.{u}
                cStrong cStrongLog cSplit ∧
                HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4PseudoGridBranchInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target := by
  rcases hsection4 with ⟨cCross, hcCross, hbranch⟩
  exact containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs10
    (exists_hairyPathOfSetsInput_of_appendixA2PaperInputs hhairyPaper)
    (exists_crossbarDichotomyInput10_of_section4PseudoGridBranchInput
      hcCross hbranch)
    hstrongGrid
    hlargeData

/-- Parameterized proof using the formal Appendix A.2/A.4 hairy route and the
Section 4 route reduced to Section 4.5 weak path-of-sets assembly plus
Section 4.6 strongification data. -/
theorem containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_appendixA2_and_section4_weakToStrong_inputs
    (hhairyPaper :
      ∃ cStrong cStrongLog cSplit : ℕ,
        0 < cStrong ∧
          0 < cStrongLog ∧
            0 < cSplit ∧
              HairyPathOfSetsTheorem.DegreeThreeStrongPathOfSetsInput.{u}
                cStrong cStrongLog cSplit ∧
                HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target := by
  rcases hsection4 with ⟨cCross, hcCross, hbranch⟩
  exact
    containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_appendixA2_and_section4_inputs
      hhairyPaper
      ⟨cCross, hcCross,
        CrossbarTheorem.section4PseudoGridBranchInput10_of_weakToStrongAssemblyInput10
          hbranch⟩
      hstrongGrid
      hlargeData


/-- Axiom-free parameterized proof after both branch lower bounds, using the
target-provider large-case route. -/
theorem containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target := by
  rcases
    gridMinor_or_gridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
      hhairyInput hcrossInput hstrongGrid hproviders with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r target hell hw hk htw hhairyLarge hg hr hpow
    hellGrid hwGrid hlarge hscaled htargetDirect htargetStrong
  rcases hmain G hell hw hk htw hhairyLarge hg hr hpow hellGrid hwGrid hlarge
      hscaled with hdirect | hstrong
  · rcases hdirect with ⟨g', hproduced, hgrid⟩
    exact hgrid.of_order_le
      (le_gridOrder_of_direct_branch_bound hcGrid hg htargetDirect hproduced)
  · rcases hstrong with ⟨r', hproduced, hgrid⟩
    have htarget_le : target ≤ r' :=
      le_of_const_mul_le_const_mul hcStrong (le_trans htargetStrong hproduced)
    exact hgrid.of_order_le htarget_le

/-- Axiom-free parameterized proof after internalizing the Theorem 8.1
target-size arithmetic. -/
theorem containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target :=
  containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput hstrongGrid
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact ⟨cRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound,
        hcRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos cRound,
        hunbundled, HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
          cRound⟩)

/-- Parameterized proof after both branch lower bounds, with the strong-minor
branch supplied directly by Chekuri--Chuzhoy Corollary 3.2. -/
theorem containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_chekuriInput
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target :=
  containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs
    hhairyInput hcrossInput
    (strongMinorGridInput_of_corollary32Input hchekuri) hlargeData












/-- Bundled-parameter proof from explicit hard inputs.  This is the
contract-free composition theorem: any later formal proof of the hard paper
ingredients can be passed here without changing the numerical endgame. -/
theorem containsGridMinor_of_parameterChoice_of_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) (target : ℕ),
              ParameterChoice cHair cHairLog cCross cGrid cStrong target
                (treewidth G) →
                ContainsGridMinor G target := by
  rcases
    containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs
      hhairyInput hcrossInput hstrongGrid hlargeData with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G target P
  exact hmain G P.ell_gt_one P.w_gt_one P.k_gt_one P.k_le_treewidth
    P.hairy_large P.g_ge_two P.r_ge_two P.g_powerOfTwo P.grid_length
    P.grid_width P.crossbar_width P.strong_scale P.target_direct
    P.target_strong

/-- Bundled-parameter explicit-input proof using the target-provider large-case
route. -/
theorem containsGridMinor_of_parameterChoice_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) (target : ℕ),
              ParameterChoice cHair cHairLog cCross cGrid cStrong target
                (treewidth G) →
                ContainsGridMinor G target := by
  rcases
    containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
      hhairyInput hcrossInput hstrongGrid hproviders with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G target P
  exact hmain G P.ell_gt_one P.w_gt_one P.k_gt_one P.k_le_treewidth
    P.hairy_large P.g_ge_two P.r_ge_two P.g_powerOfTwo P.grid_length
    P.grid_width P.crossbar_width P.strong_scale P.target_direct
    P.target_strong

/-- Bundled-parameter explicit-input proof after internalizing the Theorem 8.1
target-size arithmetic. -/
theorem containsGridMinor_of_parameterChoice_of_inputs_and_unbundledCutMatching
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) (target : ℕ),
              ParameterChoice cHair cHairLog cCross cGrid cStrong target
                (treewidth G) →
                ContainsGridMinor G target :=
  containsGridMinor_of_parameterChoice_of_inputs_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput hstrongGrid
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact ⟨cRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound,
        hcRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos cRound,
        hunbundled, HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
          cRound⟩)

/-- Bundled-parameter proof with the strong-minor branch supplied directly by
Chekuri--Chuzhoy Corollary 3.2. -/
theorem containsGridMinor_of_parameterChoice_of_chekuriInput
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) (target : ℕ),
              ParameterChoice cHair cHairLog cCross cGrid cStrong target
                (treewidth G) →
                ContainsGridMinor G target :=
  containsGridMinor_of_parameterChoice_of_inputs
    hhairyInput hcrossInput
    (strongMinorGridInput_of_corollary32Input hchekuri) hlargeData





















/-- A family of numerical parameter choices at a threshold function.  This is
the remaining arithmetic interface needed to turn the proof skeleton into a
closed excluded-grid theorem. -/
abbrev HasParameterChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    ParameterChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of rounded numerical parameter choices at a threshold function. -/
abbrev HasRoundedParameterChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    RoundedParameterChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of scale-only numerical parameter choices at a threshold
function. -/
abbrev HasScaleParameterChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    ScaleParameterChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of logarithmic scale choices at a threshold function. -/
abbrev HasLogarithmicScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    LogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of normalized logarithmic scale choices at a threshold function. -/
abbrev HasNormalizedLogarithmicScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    NormalizedLogarithmicScaleChoice cHair cHairLog cCross cGrid cStrong
      target (threshold target)

/-- A family of canonical normalized logarithmic scale choices at a threshold
function. -/
abbrev HasNormalizedUnroundedScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    NormalizedUnroundedScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of log-product scale choices at a threshold function. -/
abbrev HasLogProductScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    LogProductScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of explicit log-product scale choices at a threshold function. -/
abbrev HasExplicitLogProductScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    ExplicitLogProductScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of log-product choices at a fixed public polynomial threshold. -/
abbrev HasExplicitLogProductPolynomialThresholdChoicesAt
    (K b : ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    ExplicitLogProductPolynomialThresholdChoice cHair cHairLog cCross cGrid
      cStrong target K b

/-- Data choosing the public polynomial threshold constants and the
corresponding log-product scale choices for all target grid orders. -/
structure ExplicitLogProductPolynomialThresholdFamily
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  /-- Coefficient in the public polynomial treewidth threshold. -/
  K : ℕ
  /-- Logarithmic exponent in the public polynomial treewidth threshold. -/
  b : ℕ
  /-- The threshold coefficient is positive. -/
  K_pos : 0 < K
  /-- The logarithmic exponent is positive. -/
  b_pos : 0 < b
  /-- Choices for every target grid order at least two. -/
  choices :
    HasExplicitLogProductPolynomialThresholdChoicesAt K b cHair cHairLog
      cCross cGrid cStrong

/-- A family of sharp log-product choices at a fixed public polynomial
threshold. -/
abbrev HasSharpExplicitLogProductPolynomialThresholdChoicesAt
    (K b : ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    SharpExplicitLogProductPolynomialThresholdChoice cHair cHairLog cCross
      cGrid cStrong target K b

/-- Data choosing public polynomial threshold constants and sharp log-product
scale choices for all target grid orders. -/
structure SharpExplicitLogProductPolynomialThresholdFamily
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  /-- Coefficient in the public polynomial treewidth threshold. -/
  K : ℕ
  /-- Logarithmic exponent in the public polynomial treewidth threshold. -/
  b : ℕ
  /-- The threshold coefficient is positive. -/
  K_pos : 0 < K
  /-- The logarithmic exponent is positive. -/
  b_pos : 0 < b
  /-- Sharp choices for every target grid order at least two. -/
  choices :
    HasSharpExplicitLogProductPolynomialThresholdChoicesAt K b cHair cHairLog
      cCross cGrid cStrong

/-- A family of flexible sharp log-product choices at a fixed public
polynomial threshold. -/
abbrev HasSharpLogProductPolynomialThresholdChoicesAt
    (K b : ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    SharpLogProductPolynomialThresholdChoice cHair cHairLog cCross cGrid
      cStrong target K b

/-- Data choosing public polynomial threshold constants and flexible sharp
log-product scale choices for all target grid orders. -/
structure SharpLogProductPolynomialThresholdFamily
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  /-- Coefficient in the public polynomial treewidth threshold. -/
  K : ℕ
  /-- Logarithmic exponent in the public polynomial treewidth threshold. -/
  b : ℕ
  /-- The threshold coefficient is positive. -/
  K_pos : 0 < K
  /-- The logarithmic exponent is positive. -/
  b_pos : 0 < b
  /-- Flexible sharp choices for every target grid order at least two. -/
  choices :
    HasSharpLogProductPolynomialThresholdChoicesAt K b cHair cHairLog cCross
      cGrid cStrong

/-- A family of coefficient-budget choices at a fixed public polynomial
threshold. -/
abbrev HasSharpCoefficientPolynomialThresholdChoicesAt
    (K b : ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    SharpCoefficientPolynomialThresholdChoice cHair cHairLog cCross cGrid
      cStrong target K b

/-- Data choosing public polynomial threshold constants and coefficient-budget
choices for all target grid orders. -/
structure SharpCoefficientPolynomialThresholdFamily
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  /-- Coefficient in the public polynomial treewidth threshold. -/
  K : ℕ
  /-- Logarithmic exponent in the public polynomial treewidth threshold. -/
  b : ℕ
  /-- The threshold coefficient is positive. -/
  K_pos : 0 < K
  /-- The logarithmic exponent is positive. -/
  b_pos : 0 < b
  /-- Coefficient-budget choices for every target grid order at least two. -/
  choices :
    HasSharpCoefficientPolynomialThresholdChoicesAt K b cHair cHairLog cCross
      cGrid cStrong

/-- A family of clog-coefficient choices at a fixed public polynomial
threshold. -/
abbrev HasSharpClogCoefficientPolynomialThresholdChoicesAt
    (K b : ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    SharpClogCoefficientPolynomialThresholdChoice cHair cHairLog cCross cGrid
      cStrong target K b

/-- Data choosing public polynomial threshold constants and clog-coefficient
choices for all target grid orders. -/
structure SharpClogCoefficientPolynomialThresholdFamily
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  /-- Coefficient in the public polynomial treewidth threshold. -/
  K : ℕ
  /-- Logarithmic exponent in the public polynomial treewidth threshold. -/
  b : ℕ
  /-- The threshold coefficient is positive. -/
  K_pos : 0 < K
  /-- The logarithmic exponent is positive. -/
  b_pos : 0 < b
  /-- Clog-coefficient choices for every target grid order at least two. -/
  choices :
    HasSharpClogCoefficientPolynomialThresholdChoicesAt K b cHair cHairLog
      cCross cGrid cStrong

namespace SharpClogCoefficientPolynomialThresholdTemplate

/-- A target-independent template supplies the family data used by the
polynomial-threshold finalizer. -/
def toFamily
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (T :
      SharpClogCoefficientPolynomialThresholdTemplate cHair cHairLog cCross
        cGrid cStrong) :
    SharpClogCoefficientPolynomialThresholdFamily cHair cHairLog cCross cGrid
      cStrong where
  K := T.K
  b := T.b
  K_pos := T.K_pos
  b_pos := T.b_pos
  choices := T.choiceAt

end SharpClogCoefficientPolynomialThresholdTemplate

/-- A family of unrounded scale choices at a threshold function. -/
abbrev HasUnroundedScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    UnroundedScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of coarse scale choices at a threshold function. -/
abbrev HasCoarseScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    CoarseScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of polynomial scale choices at a threshold function. -/
abbrev HasPolynomialScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    PolynomialScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of power-scale choices at a threshold function. -/
abbrev HasPowerScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    PowerScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of monomial scale choices at a threshold function. -/
abbrev HasMonomialScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    MonomialScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of exponent-normalized scale choices at a threshold function. -/
abbrev HasExponentScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    ExponentScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of clog-rounded branch scale choices at a threshold function. -/
abbrev HasClogBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    ClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of polynomial-shaped clog branch choices at a threshold
function. -/
abbrev HasPolynomialClogBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    PolynomialClogBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of monomial-threshold clog branch choices at a threshold
function. -/
abbrev HasMonomialThresholdClogBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    MonomialThresholdClogBranchScaleChoice cHair cHairLog cCross cGrid
      cStrong target (threshold target)

/-- A family of branch-compressed scale choices at a threshold function. -/
abbrev HasBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    BranchScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of threshold-fixed branch-compressed scale choices. -/
abbrev HasThresholdBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    ThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of threshold-fixed quadratic branch scale choices. -/
abbrev HasQuadraticBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    QuadraticBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of threshold-fixed power-branch scale choices. -/
abbrev HasPowerBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    PowerBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of power-threshold branch scale choices. -/
abbrev HasPowerThresholdBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    PowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong target
      (threshold target)

/-- A family of double-power-threshold branch scale choices. -/
abbrev HasDoublePowerThresholdBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    DoublePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong
      target (threshold target)

/-- A family of triple-power-threshold branch scale choices. -/
abbrev HasTriplePowerThresholdBranchScaleChoicesAt
    (threshold : ℕ → ℕ)
    (cHair cHairLog cCross cGrid cStrong : ℕ) : Type :=
  ∀ target : ℕ, 2 ≤ target →
    TriplePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid cStrong
      target (threshold target)

/-- The explicit tower threshold supplies triple-power choices for every
target. -/
def hasTriplePowerThresholdBranchScaleChoicesAt_tower
    (cHair cHairLog cCross cGrid cStrong : ℕ) :
    HasTriplePowerThresholdBranchScaleChoicesAt
      (towerGridMinorThreshold cHair cHairLog cCross cGrid cStrong)
      cHair cHairLog cCross cGrid cStrong :=
  fun target _htarget =>
    towerTriplePowerThresholdBranchScaleChoice cHair cHairLog cCross cGrid
      cStrong target

/-- Rounded parameter choices imply exact parameter choices. -/
def parameterChoicesAt_of_rounded
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasRoundedParameterChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasParameterChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toParameterChoice

/-- Scale-only parameter choices imply rounded parameter choices. -/
def roundedParameterChoicesAt_of_scale
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasScaleParameterChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasRoundedParameterChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toRoundedParameterChoice

/-- Unrounded scale choices imply scale-only parameter choices. -/
def scaleParameterChoicesAt_of_unrounded
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasUnroundedScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasScaleParameterChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toScaleParameterChoice

/-- Logarithmic scale choices imply scale-only parameter choices. -/
def scaleParameterChoicesAt_of_logarithmic
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasLogarithmicScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong) :
    HasScaleParameterChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toScaleParameterChoice

/-- Normalized logarithmic scale choices imply logarithmic scale choices. -/
def logarithmicScaleChoicesAt_of_normalizedLogarithmic
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasNormalizedLogarithmicScaleChoicesAt threshold cHair cHairLog cCross
        cGrid cStrong) :
    HasLogarithmicScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget => (hchoices target htarget).toLogarithmicScaleChoice

/-- Canonical normalized logarithmic choices imply normalized logarithmic
choices. -/
def normalizedLogarithmicScaleChoicesAt_of_normalizedUnrounded
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasNormalizedUnroundedScaleChoicesAt threshold cHair cHairLog cCross
        cGrid cStrong) :
    HasNormalizedLogarithmicScaleChoicesAt threshold cHair cHairLog cCross
        cGrid cStrong :=
  fun target htarget =>
    (hchoices target htarget).toNormalizedLogarithmicScaleChoice

/-- Log-product scale choices imply canonical normalized logarithmic choices. -/
def normalizedUnroundedScaleChoicesAt_of_logProduct
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasLogProductScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong) :
    HasNormalizedUnroundedScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget =>
    (hchoices target htarget).toNormalizedUnroundedScaleChoice

/-- Explicit log-product scale choices imply log-product scale choices. -/
def logProductScaleChoicesAt_of_explicitLogProduct
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasExplicitLogProductScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong) :
    HasLogProductScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget => (hchoices target htarget).toLogProductScaleChoice

/-- Coarse scale choices imply unrounded scale choices. -/
def unroundedScaleChoicesAt_of_coarse
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasCoarseScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasUnroundedScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toUnroundedScaleChoice

/-- Polynomial scale choices imply coarse scale choices. -/
def coarseScaleChoicesAt_of_polynomial
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasPolynomialScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasCoarseScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toCoarseScaleChoice

/-- Power-scale choices imply polynomial scale choices. -/
def polynomialScaleChoicesAt_of_power
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasPowerScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasPolynomialScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toPolynomialScaleChoice

/-- Monomial scale choices imply power-scale choices. -/
def powerScaleChoicesAt_of_monomial
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasMonomialScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasPowerScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toPowerScaleChoice

/-- Exponent-normalized scale choices imply monomial scale choices. -/
def monomialScaleChoicesAt_of_exponent
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasExponentScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasMonomialScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toMonomialScaleChoice

/-- Clog-rounded branch choices imply exponent-normalized choices. -/
def exponentScaleChoicesAt_of_clogBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasClogBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong) :
    HasExponentScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toExponentScaleChoice

/-- Polynomial-shaped clog branch choices imply clog-rounded branch choices. -/
def clogBranchScaleChoicesAt_of_polynomialClogBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasPolynomialClogBranchScaleChoicesAt threshold cHair cHairLog cCross
        cGrid cStrong) :
    HasClogBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget => (hchoices target htarget).toClogBranchScaleChoice

/-- Monomial-threshold clog branch choices imply polynomial-shaped clog branch
choices. -/
def polynomialClogBranchScaleChoicesAt_of_monomialThresholdClogBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasMonomialThresholdClogBranchScaleChoicesAt threshold cHair cHairLog
        cCross cGrid cStrong) :
    HasPolynomialClogBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget =>
    (hchoices target htarget).toPolynomialClogBranchScaleChoice

/-- Branch-compressed scale choices imply exponent-normalized scale choices. -/
def exponentScaleChoicesAt_of_branch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong) :
    HasExponentScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toExponentScaleChoice

/-- Threshold-fixed branch-compressed scale choices imply branch-compressed
scale choices. -/
def branchScaleChoicesAt_of_thresholdBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasThresholdBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong) :
    HasBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid cStrong :=
  fun target htarget => (hchoices target htarget).toBranchScaleChoice

/-- Quadratic branch choices imply threshold-fixed branch-compressed choices. -/
def thresholdBranchScaleChoicesAt_of_quadraticBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasQuadraticBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong) :
    HasThresholdBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget =>
    (hchoices target htarget).toThresholdBranchScaleChoice htarget

/-- Power-branch choices imply quadratic branch choices. -/
def quadraticBranchScaleChoicesAt_of_powerBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasPowerBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong) :
    HasQuadraticBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget => (hchoices target htarget).toQuadraticBranchScaleChoice

/-- Power-threshold branch choices imply power-branch choices. -/
def powerBranchScaleChoicesAt_of_powerThresholdBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasPowerThresholdBranchScaleChoicesAt threshold cHair cHairLog cCross
        cGrid cStrong) :
    HasPowerBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget => (hchoices target htarget).toPowerBranchScaleChoice

/-- Double-power-threshold branch choices imply power-threshold branch
choices. -/
def powerThresholdBranchScaleChoicesAt_of_doublePowerThresholdBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasDoublePowerThresholdBranchScaleChoicesAt threshold cHair cHairLog
        cCross cGrid cStrong) :
    HasPowerThresholdBranchScaleChoicesAt threshold cHair cHairLog cCross cGrid
        cStrong :=
  fun target htarget =>
    (hchoices target htarget).toPowerThresholdBranchScaleChoice

/-- Triple-power-threshold branch choices imply double-power-threshold branch
choices. -/
def doublePowerThresholdBranchScaleChoicesAt_of_triplePowerThresholdBranch
    {threshold : ℕ → ℕ}
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (hchoices :
      HasTriplePowerThresholdBranchScaleChoicesAt threshold cHair cHairLog
        cCross cGrid cStrong) :
    HasDoublePowerThresholdBranchScaleChoicesAt threshold cHair cHairLog cCross
        cGrid cStrong :=
  fun target htarget =>
    (hchoices target htarget).toDoublePowerThresholdBranchScaleChoice















/-- Finalization from a supplied bundled graph-theoretic proof skeleton and
target-independent clog-coefficient templates.

This is the reusable endpoint for conditional proof skeletons: once the
graph-theoretic part has been reduced to `ParameterChoice`, the same explicit
polynomial arithmetic closes the public excluded-grid statement. -/
theorem exists_constants_containsGridMinor_of_sharpClogCoefficientPolynomialThresholdTemplate_of_parameterChoice
    (hparam :
      ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
        0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
          0 < cGrid ∧ 0 < cStrong ∧
            ∀ {V : Type u} [Fintype V] [DecidableEq V]
              (G : _root_.SimpleGraph V) (target : ℕ),
                ParameterChoice cHair cHairLog cCross cGrid cStrong target
                  (treewidth G) →
                  ContainsGridMinor G target)
    (hchoices :
      ∀ {cHair cHairLog cCross cGrid cStrong : ℕ},
        0 < cHair → 0 < cHairLog → 0 < cCross → 0 < cGrid →
          0 < cStrong →
            SharpClogCoefficientPolynomialThresholdTemplate
              cHair cHairLog cCross cGrid cStrong) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases hparam with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  let F :=
    (hchoices hcHair hcHairLog hcCross hcGrid hcStrong).toFamily
  refine ⟨F.K, F.b, F.K_pos, F.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  exact hmain G target
    ((F.choices target htarget).toParameterChoice.mono_treewidth htw)











/-- Polynomial excluded-grid theorem from explicit hard inputs, with no
project-contract calls in the composition proof. -/
theorem polynomial_grid_minor_theorem_of_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target := by
  exact
    exists_constants_containsGridMinor_of_sharpClogCoefficientPolynomialThresholdTemplate_of_parameterChoice
      (containsGridMinor_of_parameterChoice_of_inputs
        hhairyInput hcrossInput hstrongGrid hlargeData)
      (hchoices := by
        intro cHair cHairLog cCross cGrid cStrong _hcHair _hcHairLog _hcCross
          _hcGrid _hcStrong
        exact
          SharpClogCoefficientPolynomialThresholdTemplate.canonical
            cHair cHairLog cCross cGrid cStrong)

/-- Polynomial excluded-grid theorem from explicit hard inputs, using the
unbundled cut-matching provider and explicit Theorem 8.1 target-size provider
for the direct branch. -/
theorem polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target := by
  exact
    exists_constants_containsGridMinor_of_sharpClogCoefficientPolynomialThresholdTemplate_of_parameterChoice
      (containsGridMinor_of_parameterChoice_of_inputs_and_unbundledCutMatching_and_targetProviders
        hhairyInput hcrossInput hstrongGrid hproviders)
      (hchoices := by
        intro cHair cHairLog cCross cGrid cStrong _hcHair _hcHairLog _hcCross
          _hcGrid _hcStrong
        exact
          SharpClogCoefficientPolynomialThresholdTemplate.canonical
            cHair cHairLog cCross cGrid cStrong)

/-- Polynomial excluded-grid theorem from explicit hard inputs after
internalizing the Theorem 8.1 target-size arithmetic. -/
theorem polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput hstrongGrid
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact ⟨cRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound,
        hcRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos cRound,
        hunbundled, HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
          cRound⟩)

/-- Polynomial excluded-grid theorem from explicit hairy/crossbar inputs, with
Chekuri--Chuzhoy Corollary 3.2 and the target-provider large-case route. -/
theorem polynomial_grid_minor_theorem_of_chekuri_and_unbundledTarget_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput
    (strongMinorGridInput_of_corollary32Input hchekuri) hproviders

/-- Polynomial excluded-grid theorem from explicit hairy/crossbar inputs, with
Chekuri--Chuzhoy split into local routing and stitching and with the
target-provider large-case route. -/
theorem polynomial_grid_minor_theorem_of_localRouting_and_stitching_and_unbundledTarget_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput
    (strongMinorGridInput_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)
    hproviders

/-- Polynomial excluded-grid theorem from explicit hard inputs, with the
strong-minor branch supplied directly by Chekuri--Chuzhoy Corollary 3.2. -/
theorem polynomial_grid_minor_theorem_of_chekuri_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_inputs hhairyInput hcrossInput
    (strongMinorGridInput_of_corollary32Input hchekuri) hlargeData

/-- Polynomial excluded-grid theorem from explicit hard inputs, with the
Chekuri--Chuzhoy branch split into local routing and row stitching. -/
theorem polynomial_grid_minor_theorem_of_localRouting_and_stitching_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_inputs hhairyInput hcrossInput
    (strongMinorGridInput_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)
    hlargeData

/-- Polynomial excluded-grid theorem from explicit hard inputs, with the
large crossbar-grid branch expressed at the paper-level cut-matching and
separator-grid interfaces. -/
theorem polynomial_grid_minor_theorem_of_unbundled_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_inputs hhairyInput hcrossInput hstrongGrid
    (HairyCrossbarGrid.exists_largeCaseCutMatchingDataProvider_of_unbundled_and_separator
      hproviders)

/-- Polynomial excluded-grid theorem from explicit hard inputs, with the
strong-minor branch supplied directly by Chekuri--Chuzhoy Corollary 3.2.

This removes the opaque `StrongMinorGridInput` from the public composition
interface: downstream formalization only has to prove the paper's Corollary
3.2 dichotomy, the Chuzhoy--Tan hairy and crossbar inputs, and the large-case
cut-matching/separator providers. -/
theorem polynomial_grid_minor_theorem_of_chekuri_and_unbundled_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_unbundled_inputs hhairyInput hcrossInput
    (strongMinorGridInput_of_corollary32Input hchekuri) hproviders

/-- Polynomial excluded-grid theorem with the Chekuri--Chuzhoy branch split
into local routing and row stitching, and the large crossbar-grid branch
expressed by unbundled cut-matching/separator providers. -/
theorem polynomial_grid_minor_theorem_of_localRouting_and_stitching_and_unbundled_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_unbundled_inputs hhairyInput hcrossInput
    (strongMinorGridInput_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)
    hproviders




/-- Degree-ten corollary of the explicit-input composition theorem.

This does not reprove the theorem with weaker arithmetic; it reuses the
degree-nine composition and relaxes the public threshold. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_inputs
      hhairyInput hcrossInput hstrongGrid hlargeData)

/-- Degree-ten corollary of the explicit-input composition theorem using the
unbundled cut-matching provider and explicit Theorem 8.1 target-size provider. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching_and_targetProviders
      hhairyInput hcrossInput hstrongGrid hproviders)

/-- Degree-ten corollary of the explicit-input composition theorem after
internalizing the Theorem 8.1 target-size arithmetic. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs_and_unbundledCutMatching
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching
      hhairyInput hcrossInput hstrongGrid hprovider)





/-!
## Direct degree-ten numerical endpoint

The preceding degree-ten public statements reuse the stronger degree-nine
crossbar-width route.  Section 4 of Chuzhoy--Tan only supplies the weaker
`g^10 log g` local crossbar input, so we also keep a parallel endpoint whose
parameter package asks for exactly that weaker width inequality.
-/

/-- Numerical parameter package for the proof skeleton using the Section 4
`g^10 log g` crossbar-width requirement. -/
structure ParameterChoice10
    (cHair cHairLog cCross cGrid cStrong target tw : ℕ) where
  /-- Hairy path-of-sets length. -/
  ell : ℕ
  /-- Hairy path-of-sets width. -/
  w : ℕ
  /-- Treewidth scale passed to the hairy path-of-sets theorem. -/
  k : ℕ
  /-- Crossbar parameter, required to be a power of two. -/
  g : ℕ
  /-- Strong path-of-sets parameter used in the second branch. -/
  r : ℕ
  /-- The hairy-system length is nontrivial. -/
  ell_gt_one : 1 < ell
  /-- The hairy-system width is nontrivial. -/
  w_gt_one : 1 < w
  /-- The treewidth scale is nontrivial. -/
  k_gt_one : 1 < k
  /-- The chosen scale is bounded by the graph treewidth. -/
  k_le_treewidth : k ≤ tw
  /-- The Chuzhoy--Tan Theorem 2.3 numerical hypothesis. -/
  hairy_large :
    cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k
  /-- The crossbar parameter is at least two. -/
  g_ge_two : 2 ≤ g
  /-- The strong-branch parameter is at least two. -/
  r_ge_two : 2 ≤ r
  /-- The crossbar parameter is a power of two. -/
  g_powerOfTwo : CrossbarContract.IsPowerOfTwo g
  /-- There are enough clusters for the crossbar-grid assembly theorem. -/
  grid_length : cGrid * Nat.log 2 g ≤ ell
  /-- The system is wide enough for `g^2` crossbar paths. -/
  grid_width : g ^ 2 ≤ w
  /-- The Section 4 local crossbar theorem's weaker width lower bound. -/
  crossbar_width10 : 2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w
  /-- The strong branch can be thinned to parameter `r`. -/
  strong_scale : cCross * r ^ 2 ≤ g ^ 2
  /-- The direct branch produces a grid at least as large as `target`. -/
  target_direct : cGrid * target * (Nat.log 2 g) ^ 2 ≤ g
  /-- The strong branch produces a grid at least as large as `target`. -/
  target_strong : cStrong * target ≤ r

namespace ParameterChoice10

/-- A degree-ten numerical parameter choice remains valid when the available
treewidth bound is increased. -/
def mono_treewidth {cHair cHairLog cCross cGrid cStrong target tw tw' : ℕ}
    (P : ParameterChoice10 cHair cHairLog cCross cGrid cStrong target tw)
    (htw : tw ≤ tw') :
    ParameterChoice10 cHair cHairLog cCross cGrid cStrong target tw' where
  ell := P.ell
  w := P.w
  k := P.k
  g := P.g
  r := P.r
  ell_gt_one := P.ell_gt_one
  w_gt_one := P.w_gt_one
  k_gt_one := P.k_gt_one
  k_le_treewidth := le_trans P.k_le_treewidth htw
  hairy_large := P.hairy_large
  g_ge_two := P.g_ge_two
  r_ge_two := P.r_ge_two
  g_powerOfTwo := P.g_powerOfTwo
  grid_length := P.grid_length
  grid_width := P.grid_width
  crossbar_width10 := P.crossbar_width10
  strong_scale := P.strong_scale
  target_direct := P.target_direct
  target_strong := P.target_strong

end ParameterChoice10

/-- Canonical path-of-sets width for the rounded crossbar scale, using the
Section 4 `g^10 log g` local threshold. -/
def widthScale10 (n : ℕ) : ℕ :=
  max 2
    (max ((GridMinorArithmetic.powTwoFloor n) ^ 2)
      (2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 10 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n)))

/-- A simpler upper bound for `widthScale10`, using the unrounded scale. -/
def coarseWidthScale10 (n : ℕ) : ℕ :=
  max 2 (max (n ^ 2) (2 ^ 22 * n ^ 10 * Nat.log 2 n))

/-- The degree-ten canonical width is nontrivial. -/
theorem widthScale10_gt_one (n : ℕ) :
    1 < widthScale10 n :=
  lt_of_lt_of_le (by decide : 1 < 2) (le_max_left 2 _)

/-- The degree-ten canonical width contains the square of the rounded
crossbar scale. -/
theorem widthScale10_grid_width (n : ℕ) :
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤ widthScale10 n :=
  le_trans (le_max_left _ _) (le_max_right 2 _)

/-- The degree-ten canonical width satisfies the Section 4 local crossbar
threshold. -/
theorem widthScale10_crossbar_width (n : ℕ) :
    2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 10 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n) ≤
      widthScale10 n :=
  le_trans (le_max_right _ _) (le_max_right 2 _)

/-- The rounded degree-ten crossbar-width term is bounded by the corresponding
unrounded term. -/
theorem rounded_crossbar_width10_le_unrounded (n : ℕ) (hn : 2 ≤ n) :
    2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 10 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n) ≤
      2 ^ 22 * n ^ 10 * Nat.log 2 n := by
  calc
    2 ^ 22 * (GridMinorArithmetic.powTwoFloor n) ^ 10 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n)
        =
      2 ^ 22 * ((GridMinorArithmetic.powTwoFloor n) ^ 10 *
        Nat.log 2 (GridMinorArithmetic.powTwoFloor n)) := by
        ac_rfl
    _ ≤ 2 ^ 22 * (n ^ 10 * Nat.log 2 n) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul
        (GridMinorArithmetic.pow_powTwoFloor_le_pow hn)
        (GridMinorArithmetic.log_powTwoFloor_le_log hn))
    _ = 2 ^ 22 * n ^ 10 * Nat.log 2 n := by
      ac_rfl

/-- The degree-ten canonical width is bounded by the simpler unrounded width
expression. -/
theorem widthScale10_le_unrounded (n : ℕ) (hn : 2 ≤ n) :
    widthScale10 n ≤ coarseWidthScale10 n := by
  apply max_le
  · exact le_max_left _ _
  · apply max_le
    · exact le_trans (GridMinorArithmetic.pow_powTwoFloor_le_pow hn)
        (le_trans (le_max_left _ _) (le_max_right 2 _))
    · exact le_trans (rounded_crossbar_width10_le_unrounded n hn)
        (le_trans (le_max_right _ _) (le_max_right 2 _))

/-- The degree-ten coarse width is bounded by the logarithmic width term
`2^22 * n^10 * log n`, once `n >= 2`. -/
theorem coarseWidthScale10_le_logarithmic {n : ℕ} (hn : 2 ≤ n) :
    coarseWidthScale10 n ≤ 2 ^ 22 * n ^ 10 * Nat.log 2 n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hlog_pos : 0 < Nat.log 2 n :=
    Nat.log_pos (by decide : 1 < 2) hn
  have hlog_one : 1 ≤ Nat.log 2 n := Nat.succ_le_of_lt hlog_pos
  have hn10_log_one : 1 ≤ n ^ 10 * Nat.log 2 n :=
    Nat.mul_le_mul (Nat.succ_le_of_lt (Nat.pow_pos hnpos)) hlog_one
  have htwo_le_const : 2 ≤ 2 ^ 22 := by decide
  have htwo_le_term : 2 ≤ 2 ^ 22 * n ^ 10 * Nat.log 2 n := by
    calc
      2 = 2 * 1 := by simp
      _ ≤ 2 ^ 22 * (n ^ 10 * Nat.log 2 n) :=
        Nat.mul_le_mul htwo_le_const hn10_log_one
      _ = 2 ^ 22 * n ^ 10 * Nat.log 2 n := by
        ac_rfl
  have hn2_le_term : n ^ 2 ≤ 2 ^ 22 * n ^ 10 * Nat.log 2 n := by
    calc
      n ^ 2 ≤ n ^ 10 :=
        Nat.pow_le_pow_right hnpos (by decide : 2 ≤ 10)
      _ = n ^ 10 * 1 := by simp
      _ ≤ n ^ 10 * Nat.log 2 n := Nat.mul_le_mul_left _ hlog_one
      _ = 1 * (n ^ 10 * Nat.log 2 n) := by simp
      _ ≤ 2 ^ 22 * (n ^ 10 * Nat.log 2 n) :=
        Nat.mul_le_mul_right _ (by decide : 1 ≤ 2 ^ 22)
      _ = 2 ^ 22 * n ^ 10 * Nat.log 2 n := by
        ac_rfl
  rw [coarseWidthScale10]
  apply max_le
  · exact htwo_le_term
  · apply max_le
    · exact hn2_le_term
    · exact le_rfl

/-- The exact degree-ten hairy-system size expression is bounded by the
logarithmic width/length expression preserving the `n^10` exponent. -/
theorem hairy_size10_le_logarithmic
    (cHair cHairLog cGrid k n : ℕ) (hn : 2 ≤ n) :
    cHair * widthScale10 n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      cHair * (2 ^ 22 * n ^ 10 * Nat.log 2 n) *
        (max 2 cGrid * Nat.log 2 n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
  have hw : widthScale10 n ≤ 2 ^ 22 * n ^ 10 * Nat.log 2 n :=
    le_trans (widthScale10_le_unrounded n hn)
      (coarseWidthScale10_le_logarithmic hn)
  have hell :
      lengthScale cGrid n ≤ max 2 cGrid * Nat.log 2 n :=
    le_trans (lengthScale_le_unrounded cGrid n hn)
      (coarseLengthScale_le_logarithmic cGrid hn)
  gcongr

/-- The degree-ten logarithmic hairy-size upper bound can be written as one
constant times `n^10 * (log n)^51`. -/
theorem logarithmic_hairy_size10_eq_normalized
    (cHair cHairLog cGrid k n : ℕ) :
    cHair * (2 ^ 22 * n ^ 10 * Nat.log 2 n) *
        (max 2 cGrid * Nat.log 2 n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog =
      exponentHairyConstant cHair cGrid * n ^ 10 *
        (Nat.log 2 n) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
  rw [mul_pow]
  have hlog :
      Nat.log 2 n * (Nat.log 2 n) ^ 50 =
        (Nat.log 2 n) ^ 51 := by
    rw [show (51 : ℕ) = 1 + 50 by decide, pow_add]
    simp
  calc
    cHair * (2 ^ 22 * n ^ 10 * Nat.log 2 n) *
        ((max 2 cGrid) ^ 50 * (Nat.log 2 n) ^ 50) *
        (Nat.log 2 k) ^ cHairLog
        =
      cHair * 2 ^ 22 * (max 2 cGrid) ^ 50 * n ^ 10 *
        (Nat.log 2 n * (Nat.log 2 n) ^ 50) *
        (Nat.log 2 k) ^ cHairLog := by
        ac_rfl
    _ =
      exponentHairyConstant cHair cGrid * n ^ 10 *
        (Nat.log 2 n) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
        rw [hlog, exponentHairyConstant]

/-- A normalized logarithmic degree-ten hairy-system inequality implies the
exact hairy-system inequality used by the Section 4 proof skeleton. -/
theorem hairy_large10_of_logarithmic_normalized
    {cHair cHairLog cGrid k n : ℕ} (hn : 2 ≤ n)
    (h :
      exponentHairyConstant cHair cGrid * n ^ 10 *
        (Nat.log 2 n) ^ 51 *
        (Nat.log 2 k) ^ cHairLog < k) :
    cHair * widthScale10 n * (lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k := by
  apply lt_of_le_of_lt (hairy_size10_le_logarithmic cHair cHairLog cGrid k n hn)
  rwa [logarithmic_hairy_size10_eq_normalized]

/-- The public degree-ten polynomial grid-minor threshold is the degree-ten
monomial-logarithmic scale. -/
theorem polynomialGridMinorTreewidthBound10_eq_monomialLogScale
    (K b target : ℕ) :
    polynomialGridMinorTreewidthBound10 K b target =
      monomialLogScale K 10 b target :=
  rfl

/-- The public degree-ten polynomial grid-minor threshold is nontrivial when
its coefficient is positive and the target grid order is at least two. -/
theorem polynomialGridMinorTreewidthBound10_gt_one
    {K b target : ℕ} (hK : 1 ≤ K) (htarget : 2 ≤ target) :
    1 < polynomialGridMinorTreewidthBound10 K b target := by
  have hlog_pos : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have hlog_pow : 1 ≤ (Nat.log 2 target) ^ b :=
    Nat.succ_le_of_lt (Nat.pow_pos hlog_pos)
  have htarget_pow : 2 ≤ target ^ 10 := by
    calc
      2 ≤ 2 ^ 10 := by decide
      _ ≤ target ^ 10 := Nat.pow_le_pow_left htarget 10
  have htwo :
      2 ≤ polynomialGridMinorTreewidthBound10 K b target := by
    calc
      2 ≤ K * target ^ 10 := by
        calc
          2 = 1 * 2 := by simp
          _ ≤ K * target ^ 10 :=
            Nat.mul_le_mul hK htarget_pow
      _ = K * target ^ 10 * 1 := by simp
      _ ≤ K * target ^ 10 * (Nat.log 2 target) ^ b :=
        Nat.mul_le_mul_left _ hlog_pow
      _ = polynomialGridMinorTreewidthBound10 K b target := by
        rw [polynomialGridMinorTreewidthBound10]
  exact lt_of_lt_of_le (by decide : 1 < 2) htwo

/-- A coefficient and exponent budget that imply the normalized degree-ten
hairy-system inequality at the public degree-ten polynomial threshold. -/
theorem hairy_large_threshold10_of_coeff
    {cHair cHairLog cGrid C p Dn Dk K b target : ℕ}
    (htarget : 2 ≤ target)
    (hexponent : p * 10 + 51 + cHairLog ≤ b)
    (hcoeff :
      exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
        Dk ^ cHairLog < K) :
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 10 *
      (Dn * Nat.log 2 target) ^ 51 *
      (Dk * Nat.log 2 target) ^ cHairLog <
        polynomialGridMinorTreewidthBound10 K b target := by
  set L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have htarget_pos : 0 < target :=
    lt_of_lt_of_le (by decide : 0 < 2) htarget
  have htarget_pow_pos : 0 < target ^ 10 := Nat.pow_pos htarget_pos
  have hLpow_b_pos : 0 < L ^ b := Nat.pow_pos hLpos
  have hmult_pos : 0 < target ^ 10 * L ^ b :=
    Nat.mul_pos htarget_pow_pos hLpow_b_pos
  have hLp :
      (L ^ p) ^ 10 = L ^ (p * 10) := by
    simpa using (Nat.pow_mul L p 10).symm
  have hleft_eq :
      exponentHairyConstant cHair cGrid *
          (logProductScale C p target) ^ 10 *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog =
      (exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
          Dk ^ cHairLog) *
        target ^ 10 * L ^ (p * 10 + 51 + cHairLog) := by
    calc
      exponentHairyConstant cHair cGrid *
          (logProductScale C p target) ^ 10 *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog
          =
        exponentHairyConstant cHair cGrid *
          (C ^ 10 * target ^ 10 * (L ^ p) ^ 10) *
          (Dn ^ 51 * L ^ 51) *
          (Dk ^ cHairLog * L ^ cHairLog) := by
          rw [logProductScale]
          repeat rw [mul_pow]
      _ =
        exponentHairyConstant cHair cGrid *
          (C ^ 10 * target ^ 10 * L ^ (p * 10)) *
          (Dn ^ 51 * L ^ 51) *
          (Dk ^ cHairLog * L ^ cHairLog) := by
          rw [hLp]
      _ =
        (exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
            Dk ^ cHairLog) *
          target ^ 10 *
          (L ^ (p * 10) * L ^ 51 * L ^ cHairLog) := by
          ac_rfl
      _ =
        (exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
            Dk ^ cHairLog) *
          target ^ 10 * L ^ (p * 10 + 51 + cHairLog) := by
          rw [← pow_add, ← pow_add]
  have hpow :
      L ^ (p * 10 + 51 + cHairLog) ≤ L ^ b :=
    Nat.pow_le_pow_right hLpos hexponent
  calc
    exponentHairyConstant cHair cGrid *
        (logProductScale C p target) ^ 10 *
      (Dn * Nat.log 2 target) ^ 51 *
      (Dk * Nat.log 2 target) ^ cHairLog
        =
      (exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
          Dk ^ cHairLog) *
        target ^ 10 * L ^ (p * 10 + 51 + cHairLog) := hleft_eq
    _ ≤ (exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
          Dk ^ cHairLog) *
        target ^ 10 * L ^ b :=
      Nat.mul_le_mul_left
        ((exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
          Dk ^ cHairLog) * target ^ 10) hpow
    _ < K * target ^ 10 * L ^ b := by
      calc
        (exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
            Dk ^ cHairLog) *
          target ^ 10 * L ^ b
            =
          (exponentHairyConstant cHair cGrid * C ^ 10 * Dn ^ 51 *
            Dk ^ cHairLog) * (target ^ 10 * L ^ b) := by
            ac_rfl
        _ < K * (target ^ 10 * L ^ b) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hmult_pos
        _ = K * target ^ 10 * L ^ b := by
          ac_rfl
    _ = polynomialGridMinorTreewidthBound10 K b target := by
      simp [polynomialGridMinorTreewidthBound10, L]

/-- Degree-ten scale choice at the public `k^10 polylog k` threshold, using
the same sharp square-form strong-branch rounding as the degree-nine endpoint. -/
structure SharpClogCoefficientPolynomialThresholdChoice10
    (cHair cHairLog cCross cGrid cStrong target K b : ℕ) where
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- The crossbar-scale coefficient is positive. -/
  C_pos : 1 ≤ C
  /-- The threshold coefficient is positive. -/
  K_pos : 1 ≤ K
  /-- The target grid order is at least two. -/
  target_ge_two : 2 ≤ target
  /-- The log-product exponent is large enough for the direct branch. -/
  p_ge_two : 2 ≤ p
  /-- Coefficient budget for the sharp strong-branch inequality. -/
  strong_coeff :
    4 * cCross * (max 2 cStrong) ^ 2 ≤ C ^ 2
  /-- Coefficient budget for the direct-branch inequality. -/
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  /-- Logarithmic exponent budget for the degree-ten hairy-system inequality. -/
  hairy_exponent : p * 10 + 51 + cHairLog ≤ b
  /-- Strict coefficient budget for the degree-ten hairy-system inequality. -/
  hairy_coeff :
    exponentHairyConstant cHair cGrid * C ^ 10 *
        (Nat.clog 2 C + p + 2) ^ 51 *
      (Nat.clog 2 K + 2 * 10 + b) ^ cHairLog < K

namespace SharpClogCoefficientPolynomialThresholdChoice10

/-- Degree-ten coefficient choices imply the exact parameter package consumed
by the Section 4 graph-theoretic proof skeleton. -/
def toParameterChoice10
    {cHair cHairLog cCross cGrid cStrong target K b : ℕ}
    (P :
      SharpClogCoefficientPolynomialThresholdChoice10 cHair cHairLog cCross
        cGrid cStrong target K b) :
    ParameterChoice10 cHair cHairLog cCross cGrid cStrong target
      (polynomialGridMinorTreewidthBound10 K b target) where
  ell := lengthScale cGrid (logProductScale P.C P.p target)
  w := widthScale10 (logProductScale P.C P.p target)
  k := polynomialGridMinorTreewidthBound10 K b target
  g := GridMinorArithmetic.powTwoFloor (logProductScale P.C P.p target)
  r := strongScale cStrong target
  ell_gt_one := lengthScale_gt_one cGrid (logProductScale P.C P.p target)
  w_gt_one := widthScale10_gt_one (logProductScale P.C P.p target)
  k_gt_one :=
    polynomialGridMinorTreewidthBound10_gt_one P.K_pos P.target_ge_two
  k_le_treewidth := le_rfl
  hairy_large := by
    apply hairy_large10_of_logarithmic_normalized
      (two_le_logProductScale P.C_pos P.target_ge_two)
    have hlog_n :
        Nat.log 2 (logProductScale P.C P.p target) ≤
          (Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target :=
      log_logProductScale_le_clog_const_mul_log P.C P.p P.target_ge_two
    have hlog_k :
        Nat.log 2 (polynomialGridMinorTreewidthBound10 K b target) ≤
          (Nat.clog 2 K + 2 * 10 + b) * Nat.log 2 target := by
      simpa [polynomialGridMinorTreewidthBound10_eq_monomialLogScale,
        monomialLogScale] using
        log_monomialLogScale_le_clog_const_mul_log K 10 b P.target_ge_two
    have hlog_n_pow :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 ≤
          ((Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target) ^ 51 :=
      Nat.pow_le_pow_left hlog_n 51
    have hlog_k_pow :
        (Nat.log 2 (polynomialGridMinorTreewidthBound10 K b target)) ^
            cHairLog ≤
          ((Nat.clog 2 K + 2 * 10 + b) * Nat.log 2 target) ^
            cHairLog :=
      Nat.pow_le_pow_left hlog_k cHairLog
    have hthreshold :
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 10 *
          ((Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
          ((Nat.clog 2 K + 2 * 10 + b) * Nat.log 2 target) ^ cHairLog <
            polynomialGridMinorTreewidthBound10 K b target :=
      hairy_large_threshold10_of_coeff P.target_ge_two P.hairy_exponent
        P.hairy_coeff
    have hle :
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 10 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound10 K b target)) ^
            cHairLog ≤
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 10 *
          ((Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
          ((Nat.clog 2 K + 2 * 10 + b) * Nat.log 2 target) ^
            cHairLog := by
      calc
        exponentHairyConstant cHair cGrid *
            (logProductScale P.C P.p target) ^ 10 *
          (Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
          (Nat.log 2 (polynomialGridMinorTreewidthBound10 K b target)) ^
            cHairLog
            =
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 10) *
            ((Nat.log 2 (logProductScale P.C P.p target)) ^ 51 *
              (Nat.log 2 (polynomialGridMinorTreewidthBound10 K b target)) ^
                cHairLog) := by
            ac_rfl
        _ ≤
          (exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 10) *
            (((Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
              ((Nat.clog 2 K + 2 * 10 + b) * Nat.log 2 target) ^
                cHairLog) :=
            Nat.mul_le_mul_left _
              (Nat.mul_le_mul hlog_n_pow hlog_k_pow)
        _ =
          exponentHairyConstant cHair cGrid *
              (logProductScale P.C P.p target) ^ 10 *
            ((Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target) ^ 51 *
            ((Nat.clog 2 K + 2 * 10 + b) * Nat.log 2 target) ^
              cHairLog := by
            ac_rfl
    exact lt_of_le_of_lt hle hthreshold
  g_ge_two :=
    GridMinorArithmetic.two_le_powTwoFloor
      (two_le_logProductScale P.C_pos P.target_ge_two)
  r_ge_two := strongScale_ge_two cStrong target
  g_powerOfTwo :=
    GridMinorArithmetic.isPowerOfTwo_powTwoFloor
      (logProductScale P.C P.p target)
  grid_length :=
    lengthScale_grid_length cGrid (logProductScale P.C P.p target)
  grid_width :=
    widthScale10_grid_width (logProductScale P.C P.p target)
  crossbar_width10 :=
    widthScale10_crossbar_width (logProductScale P.C P.p target)
  strong_scale :=
    GridMinorArithmetic.le_powTwoFloor_sq_of_four_mul_le_sq
      (strong_scale_logProduct_sq_of_coeff P.target_ge_two P.strong_coeff)
  target_direct := by
    have hlog_n :
        Nat.log 2 (logProductScale P.C P.p target) ≤
          (Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target :=
      log_logProductScale_le_clog_const_mul_log P.C P.p P.target_ge_two
    have hlog_sq :
        (Nat.log 2 (logProductScale P.C P.p target)) ^ 2 ≤
          ((Nat.clog 2 P.C + P.p + 2) * Nat.log 2 target) ^ 2 :=
      Nat.pow_le_pow_left hlog_n 2
    exact
      GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
        (two_le_logProductScale P.C_pos P.target_ge_two)
        (by
          calc
            2 * (cGrid * target *
                (Nat.log 2 (logProductScale P.C P.p target)) ^ 2)
                ≤
              2 * (cGrid * target *
                ((Nat.clog 2 P.C + P.p + 2) *
                  Nat.log 2 target) ^ 2) :=
                Nat.mul_le_mul_left 2
                  (Nat.mul_le_mul_left (cGrid * target) hlog_sq)
            _ ≤ logProductScale P.C P.p target :=
              target_direct_logProduct_of_coeff P.target_ge_two P.p_ge_two
                P.direct_coeff)
  target_strong := target_le_strongScale cStrong target

end SharpClogCoefficientPolynomialThresholdChoice10

/-- Target-independent constants satisfying the degree-ten clog-coefficient
budgets. -/
structure SharpClogCoefficientPolynomialThresholdTemplate10
    (cHair cHairLog cCross cGrid cStrong : ℕ) where
  /-- Coefficient in the public degree-ten treewidth threshold. -/
  K : ℕ
  /-- Logarithmic exponent in the public degree-ten treewidth threshold. -/
  b : ℕ
  /-- Constant multiplier in the crossbar scale. -/
  C : ℕ
  /-- Exponent of `log target` in the crossbar scale. -/
  p : ℕ
  /-- The threshold coefficient is positive. -/
  K_pos : 0 < K
  /-- The logarithmic exponent is positive. -/
  b_pos : 0 < b
  /-- The crossbar-scale coefficient is positive. -/
  C_pos : 1 ≤ C
  /-- The log-product exponent is large enough for the direct branch. -/
  p_ge_two : 2 ≤ p
  /-- Coefficient budget for the sharp strong-branch inequality. -/
  strong_coeff :
    4 * cCross * (max 2 cStrong) ^ 2 ≤ C ^ 2
  /-- Coefficient budget for the direct-branch inequality. -/
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  /-- Logarithmic exponent budget for the degree-ten hairy-system inequality. -/
  hairy_exponent : p * 10 + 51 + cHairLog ≤ b
  /-- Strict coefficient budget for the degree-ten hairy-system inequality. -/
  hairy_coeff :
    exponentHairyConstant cHair cGrid * C ^ 10 *
        (Nat.clog 2 C + p + 2) ^ 51 *
      (Nat.clog 2 K + 2 * 10 + b) ^ cHairLog < K

namespace SharpClogCoefficientPolynomialThresholdTemplate10

/-- A target-independent degree-ten template supplies choices for every target
at least two. -/
def choiceAt
    {cHair cHairLog cCross cGrid cStrong : ℕ}
    (T :
      SharpClogCoefficientPolynomialThresholdTemplate10 cHair cHairLog
        cCross cGrid cStrong)
    (target : ℕ) (htarget : 2 ≤ target) :
    SharpClogCoefficientPolynomialThresholdChoice10 cHair cHairLog cCross
      cGrid cStrong target T.K T.b where
  C := T.C
  p := T.p
  C_pos := T.C_pos
  K_pos := Nat.succ_le_of_lt T.K_pos
  target_ge_two := htarget
  p_ge_two := T.p_ge_two
  strong_coeff := T.strong_coeff
  direct_coeff := T.direct_coeff
  hairy_exponent := T.hairy_exponent
  hairy_coeff := T.hairy_coeff

/-- A canonical target-independent degree-ten template satisfying all
coefficient budgets. -/
def canonical
    (cHair cHairLog cCross cGrid cStrong : ℕ) :
    SharpClogCoefficientPolynomialThresholdTemplate10 cHair cHairLog cCross
      cGrid cStrong := by
  let C := crossbarCoefficient cCross cGrid cStrong
  let b := 2 * 10 + 51 + cHairLog
  let A :=
    exponentHairyConstant cHair cGrid * C ^ 10 *
      (Nat.clog 2 C + 2 + 2) ^ 51
  let E := 2 * 10 + b
  refine
    { K := thresholdCoefficient A cHairLog E
      b := b
      C := C
      p := 2
      K_pos := ?_
      b_pos := ?_
      C_pos := ?_
      p_ge_two := le_rfl
      strong_coeff := ?_
      direct_coeff := ?_
      hairy_exponent := ?_
      hairy_coeff := ?_ }
  · dsimp [thresholdCoefficient]
    exact Nat.pow_pos (by decide : 0 < 2)
  · omega
  · dsimp [C, crossbarCoefficient]
    exact Nat.succ_le_of_lt
      (Nat.pow_pos (by decide : 0 < 2))
  · simpa [C] using
      strong_coeff_crossbarCoefficient cCross cGrid cStrong
  · simpa [C] using
      direct_coeff_crossbarCoefficient cCross cGrid cStrong
  · omega
  · simpa [A, E, Nat.add_assoc] using
      coeff_mul_clog_thresholdCoefficient_add_pow_lt A cHairLog E

end SharpClogCoefficientPolynomialThresholdTemplate10

/-- Bundled degree-ten parameter proof from explicit hard inputs and the
Section 4 `g^10 log g` crossbar input. -/
theorem containsGridMinor_of_parameterChoice10_of_inputs10
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) (target : ℕ),
              ParameterChoice10 cHair cHairLog cCross cGrid cStrong target
                (treewidth G) →
                ContainsGridMinor G target := by
  rcases
    containsGridMinor_of_treewidth_parameters_with_scaled_strong_parameter_of_inputs10
      hhairyInput hcrossInput hstrongGrid hlargeData with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G target P
  exact hmain G P.ell_gt_one P.w_gt_one P.k_gt_one P.k_le_treewidth
    P.hairy_large P.g_ge_two P.r_ge_two P.g_powerOfTwo P.grid_length
    P.grid_width P.crossbar_width10 P.strong_scale P.target_direct
    P.target_strong

/-- Bundled degree-ten parameter proof from explicit hard inputs, using the
unbundled cut-matching provider and explicit Theorem 8.1 target-size provider
for the direct branch. -/
theorem containsGridMinor_of_parameterChoice10_of_inputs10_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) (target : ℕ),
              ParameterChoice10 cHair cHairLog cCross cGrid cStrong target
                (treewidth G) →
                ContainsGridMinor G target := by
  rcases hhairyInput with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases
    HairyPathOfSetsSystem.gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs10_and_unbundledCutMatching_and_targetProviders
      hcrossInput hstrongGrid hproviders with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hcrossbar⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G target P
  rcases hhairy G P.ell_gt_one P.w_gt_one P.k_gt_one P.k_le_treewidth
      P.hairy_large with
    ⟨H, hHG, hmaxDegree, ⟨Hsys⟩⟩
  rcases hcrossbar G H Hsys hHG P.g_ge_two P.r_ge_two P.g_powerOfTwo
      hmaxDegree P.grid_length P.grid_width P.crossbar_width10
      P.strong_scale with hdirect | hstrong
  · rcases hdirect with ⟨g', hproduced, hgrid⟩
    exact hgrid.of_order_le
      (le_gridOrder_of_direct_branch_bound hcGrid P.g_ge_two
        P.target_direct hproduced)
  · rcases hstrong with ⟨r', hproduced, hgrid⟩
    have htarget_le : target ≤ r' :=
      le_of_const_mul_le_const_mul hcStrong
        (le_trans P.target_strong hproduced)
    exact hgrid.of_order_le htarget_le

/-- Finalization from a supplied degree-ten bundled graph-theoretic proof
skeleton and target-independent degree-ten clog-coefficient templates. -/
theorem exists_constants_containsGridMinor10_of_template_of_parameterChoice10
    (hparam :
      ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
        0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
          0 < cGrid ∧ 0 < cStrong ∧
            ∀ {V : Type u} [Fintype V] [DecidableEq V]
              (G : _root_.SimpleGraph V) (target : ℕ),
                ParameterChoice10 cHair cHairLog cCross cGrid cStrong target
                  (treewidth G) →
                  ContainsGridMinor G target)
    (hchoices :
      ∀ {cHair cHairLog cCross cGrid cStrong : ℕ},
        0 < cHair → 0 < cHairLog → 0 < cCross → 0 < cGrid →
          0 < cStrong →
            SharpClogCoefficientPolynomialThresholdTemplate10
              cHair cHairLog cCross cGrid cStrong) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases hparam with
    ⟨cHair, cHairLog, cCross, cGrid, cStrong,
      hcHair, hcHairLog, hcCross, hcGrid, hcStrong, hmain⟩
  let T := hchoices hcHair hcHairLog hcCross hcGrid hcStrong
  refine ⟨T.K, T.b, T.K_pos, T.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  exact hmain G target
    ((T.choiceAt target htarget).toParameterChoice10.mono_treewidth htw)

/-- Polynomial excluded-grid theorem at the direct `k^10 polylog k` endpoint,
using the Section 4 `g^10 log g` crossbar input. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs10
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  exists_constants_containsGridMinor10_of_template_of_parameterChoice10
    (containsGridMinor_of_parameterChoice10_of_inputs10
      hhairyInput hcrossInput hstrongGrid hlargeData)
    (hchoices := by
      intro cHair cHairLog cCross cGrid cStrong _hcHair _hcHairLog _hcCross
        _hcGrid _hcStrong
      exact
        SharpClogCoefficientPolynomialThresholdTemplate10.canonical
          cHair cHairLog cCross cGrid cStrong)

/-- Direct degree-ten endpoint using the unbundled cut-matching provider and
explicit Theorem 8.1 target-size provider. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs10_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  exists_constants_containsGridMinor10_of_template_of_parameterChoice10
    (containsGridMinor_of_parameterChoice10_of_inputs10_and_unbundledCutMatching_and_targetProviders
      hhairyInput hcrossInput hstrongGrid hproviders)
    (hchoices := by
      intro cHair cHairLog cCross cGrid cStrong _hcHair _hcHairLog _hcCross
        _hcGrid _hcStrong
      exact
        SharpClogCoefficientPolynomialThresholdTemplate10.canonical
          cHair cHairLog cCross cGrid cStrong)

/-- Direct degree-ten endpoint after internalizing the Theorem 8.1 target-size
arithmetic. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs10_and_unbundledCutMatching
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong)
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_inputs10_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput hstrongGrid
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact ⟨cRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound,
        hcRound, HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos cRound,
        hunbundled, HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
          cRound⟩)

/-- Direct degree-ten endpoint with the proved fixed-round cut-matching game
internalized. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs10_and_cutMatchingGame
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        StrongMinorGridInput.{u} cStrong) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_inputs10_and_unbundledCutMatching
    hhairyInput hcrossInput hstrongGrid
    HairyCrossbarGrid.exists_fixedRoundCutMatchingUnbundledProvider

















end PolynomialGridMinor










/-- Public axiom-free composition theorem with the strong-minor branch supplied
by Chekuri--Chuzhoy Corollary 3.2 and the direct branch supplied by a
large-case cut-matching data provider. -/
theorem polynomial_grid_minor_theorem_of_chekuri_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        PolynomialGridMinor.HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_of_chekuri_inputs
    hhairyInput hcrossInput hchekuri hlargeData

/-- Public composition theorem with the Chekuri--Chuzhoy branch split into
local routing and row stitching. -/
theorem polynomial_grid_minor_theorem_of_localRouting_and_stitching_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        PolynomialGridMinor.HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_of_localRouting_and_stitching_inputs
    hhairyInput hcrossInput hlocal hstitch hlargeData

/-- Public axiom-free composition theorem from explicit hard inputs.  This is
the self-contained proof skeleton for the polynomial excluded-grid theorem:
the paper inputs are hypotheses, not contract axioms. -/
theorem polynomial_grid_minor_theorem_of_unbundled_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        PolynomialGridMinor.HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_of_unbundled_inputs
    hhairyInput hcrossInput hstrongGrid hproviders

/-- Public composition theorem whose hairy-side input is supplied directly by
the paper-shaped A.1 Omega sparsifier source, the lower-level
Chekuri--Chuzhoy Theorem 2.21 sources, the faithful Section 4 path route, and
the Appendix A.4 split-cluster source.

The remaining hypotheses are the non-hairy-side grid-minor inputs: the
crossbar dichotomy, the strong-minor grid branch, and the large-case
cut-matching/separator providers. -/
theorem polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_unbundled_inputs
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_unbundled_inputs
    (PolynomialGridMinor.exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
      hsparseOmega hroutable hcutMatching hpathRoute hsplit)
    hcrossInput hstrongGrid hproviders

/-- Degree-ten corollary of
`polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_unbundled_inputs`.

This reuses the stronger degree-nine theorem and only relaxes the public
threshold to the `k^10 polylog k` shape. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_unbundled_inputs
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_unbundled_inputs
      hsparseOmega hroutable hcutMatching hpathRoute hsplit
      hcrossInput hstrongGrid hproviders)

/-- Public composition theorem whose hairy-side input is supplied by the
paper-shaped A.1 Omega sparsifier source, the lower-level Chekuri--Chuzhoy
Theorem 2.21 sources, the faithful Section 4 path route, and the Appendix A.4
split-cluster source, with the large-case fixed-round cut-matching game
internalized.

Compared with
`polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_unbundled_inputs`,
this theorem uses the proved cut-matching-game theorem and the explicit
Theorem 8.1 target-size arithmetic, so no cut-matching or separator provider is
left as a hypothesis. -/
theorem polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_cutMatchingGame
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_of_inputs_and_unbundledCutMatching
    (PolynomialGridMinor.exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
      hsparseOmega hroutable hcutMatching hpathRoute hsplit)
    hcrossInput hstrongGrid
    HairyCrossbarGrid.exists_fixedRoundCutMatchingUnbundledProvider

/-- Degree-ten corollary of
`polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_cutMatchingGame`.

This reuses the stronger degree-nine theorem and only relaxes the public
threshold to the `k^10 polylog k` shape. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_cutMatchingGame
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_cutMatchingGame
      hsparseOmega hroutable hcutMatching hpathRoute hsplit
      hcrossInput hstrongGrid)

/-- A.1/A.2-shaped composition with the large-case cut-matching game
internalized and the strong-minor branch supplied by Chekuri--Chuzhoy
Corollary 3.2. -/
theorem polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_corollary32Input
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_cutMatchingGame
    hsparseOmega hroutable hcutMatching hpathRoute hsplit hcrossInput
    (PolynomialGridMinor.strongMinorGridInput_of_corollary32Input hchekuri)

/-- Degree-ten corollary of
`polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_corollary32Input`. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_corollary32Input
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_corollary32Input
      hsparseOmega hroutable hcutMatching hpathRoute hsplit
      hcrossInput hchekuri)

/-- A.1/A.2-shaped composition with the large-case cut-matching game
internalized and Chekuri--Chuzhoy Corollary 3.2 split into local routing and
row stitching inputs. -/
theorem polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_localRouting_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_corollary32Input
    hsparseOmega hroutable hcutMatching hpathRoute hsplit hcrossInput
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)

/-- Degree-ten corollary of the local-routing/stitching A.1/A.2-shaped
composition with the large-case cut-matching game internalized. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_localRouting_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hsplit :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA4SplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_localRouting_stitching
      hsparseOmega hroutable hcutMatching hpathRoute hsplit
      hcrossInput hlocal hstitch)

/-- A.1/A.2-shaped composition with Appendix A.4 derived from the local
Appendix A.3 split-cluster theorem, with the large-case cut-matching game
internalized and Chekuri--Chuzhoy Corollary 3.2 split into local routing and
row stitching inputs. -/
theorem polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_cutMatchingGame_and_localRouting_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_cutMatchingGame_and_localRouting_stitching
    hsparseOmega hroutable hcutMatching hpathRoute
    (by
      rcases hA3 with ⟨cSplit, hcSplit, hsplit⟩
      exact ⟨cSplit, hcSplit,
        HairyPathOfSetsTheorem.appendixA4SplitInput_of_appendixA3ClusterSplitInput
          hsplit⟩)
    hcrossInput hlocal hstitch

/-- Degree-ten corollary with Appendix A.4 derived from the local Appendix A.3
split-cluster theorem, the large-case cut-matching game internalized, and
Chekuri--Chuzhoy Corollary 3.2 split into local routing and row stitching
inputs. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_cutMatchingGame_and_localRouting_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_degree9
    (polynomial_grid_minor_theorem_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_cutMatchingGame_and_localRouting_stitching
      hsparseOmega hroutable hcutMatching hpathRoute hA3
      hcrossInput hlocal hstitch)

/-- Direct degree-ten A.1/A.2-shaped composition using the Section 4 weak
`g^10 log g` crossbar input, Appendix A.4 derived from the local Appendix A.3
split-cluster theorem, the proved large-case cut-matching game, and the split
Chekuri--Chuzhoy Corollary 3.2 inputs. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_crossbar10_cutMatchingGame_and_localRouting_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_inputs10_and_cutMatchingGame
    (PolynomialGridMinor.exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
      hsparseOmega hroutable hcutMatching hpathRoute
      (by
        rcases hA3 with ⟨cSplit, hcSplit, hsplit⟩
        exact ⟨cSplit, hcSplit,
          HairyPathOfSetsTheorem.appendixA4SplitInput_of_appendixA3ClusterSplitInput
            hsplit⟩))
    hcrossInput
    (PolynomialGridMinor.strongMinorGridInput_of_corollary32Input
      (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
        hlocal hstitch))

/-- Direct degree-ten A.1/A.2-shaped composition using the Section 4 weak
`g^10 log g` crossbar input, Appendix A.4 derived from the local Appendix A.3
split-cluster theorem, the proved large-case cut-matching game, and the
cluster-faithful split Chekuri--Chuzhoy Corollary 3.2 inputs. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_crossbar10_cutMatchingGame_and_localRoutingCluster_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_inputs10_and_cutMatchingGame
    (PolynomialGridMinor.exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_and_appendixA4
      hsparseOmega hroutable hcutMatching hpathRoute
      (by
        rcases hA3 with ⟨cSplit, hcSplit, hsplit⟩
        exact ⟨cSplit, hcSplit,
          HairyPathOfSetsTheorem.appendixA4SplitInput_of_appendixA3ClusterSplitInput
            hsplit⟩))
    hcrossInput
    (PolynomialGridMinor.strongMinorGridInput_of_corollary32Input
      (ChekuriChuzhoy.corollary32Input_of_localRoutingClusterInput_and_stitchingInput
        hlocal hstitch))

/-- Direct degree-ten A.1/A.2-shaped composition with the Section 4 crossbar
branch reduced to the formal Theorem 4.1 proof plus Section 4.5 weak assembly
and Section 4.6 strongification data. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_section4WeakToStrong_cutMatchingGame_and_localRouting_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_crossbar10_cutMatchingGame_and_localRouting_stitching
    hsparseOmega hroutable hcutMatching hpathRoute hA3
    (by
      rcases hsection4 with ⟨cCross, hcCross, hbranch⟩
      exact
        PolynomialGridMinor.exists_crossbarDichotomyInput10_of_section4WeakToStrongAssemblyInput
          hcCross hbranch)
    hlocal hstitch

/-- Direct degree-ten A.1/A.2-shaped composition with the Section 4 crossbar
branch reduced to the formal Theorem 4.1 proof plus Section 4.5 weak assembly
and Section 4.6 strongification data, using the cluster-faithful local-routing
input for the Chekuri--Chuzhoy branch. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hpathRoute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow)
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_crossbar10_cutMatchingGame_and_localRoutingCluster_stitching
    hsparseOmega hroutable hcutMatching hpathRoute hA3
    (by
      rcases hsection4 with ⟨cCross, hcCross, hbranch⟩
      exact
        PolynomialGridMinor.exists_crossbarDichotomyInput10_of_section4WeakToStrongAssemblyInput
          hcCross hbranch)
    hlocal hstitch

/-- Direct degree-ten composition with Theorem A.1 in Omega form and the
Chekuri--Chuzhoy A.2 route bundled as its explicit source-input boundary.

This is the preferred public theorem for auditing the remaining A.1/A.2 closure
for the `k^10 polylog k` route: `hA2` is exactly the three-paper-input
semantic closure recorded by `ChekuriChuzhoy.TheoremA2SourceInputs`, not the
broad A.2 contract axiom. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_theoremA2SourceInputs_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2SourceInputs.{u})
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases hA2 with ⟨hroutable, hcutMatching, hpathRoute⟩
  exact
    polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
      hsparseOmega hroutable hcutMatching hpathRoute hA3 hsection4 hlocal hstitch

/-- Direct degree-ten A.1/A.2-shaped composition where the Chekuri--Chuzhoy
A.2 route is split into the Section 4 strong-tree construction and Theorem 4.6
extraction.  This is the same public `k^10 polylog k` bound as the path-route
variant, but it exposes the currently relevant paper-internal dependencies
instead of bundling them as `StrongPathOfSetsFromNodeWellLinkedCore`. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_extraction_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u})
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_pathRoute_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    hsparseOmega hroutable hcutMatching
    (ChekuriChuzhoy.strongPathOfSetsFromNodeWellLinkedCore_of_strongTreeCore_and_extraction
      hbuild hextract)
    hA3 hsection4 hlocal hstitch

/-- Direct degree-ten A.1/A.2-shaped composition where the
Chekuri--Chuzhoy A.2 route is split down to the strong-tree construction, the
pure meta-tree dichotomy, and the DFS/many-leaves branch of Theorem 4.6.

The buffered-path branch of Theorem 4.6 is proved by `TreeOfSets.lean` and is
composed here, so the theorem exposes only the remaining leaf-side construction
instead of the monolithic extraction hypothesis. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_leafExtraction_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_extraction_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    hsparseOmega hroutable hcutMatching hbuild
    (ChekuriChuzhoy.strongPathOfSetsFromStrongTreeOfSets_of_metaDichotomy_and_leafExtraction
      hdichotomy hleaf)
    hA3 hsection4 hlocal hstitch

/-- Direct degree-ten A.1/A.2-shaped composition where the
Chekuri--Chuzhoy A.2 route is split down to the strong-tree construction and
the DFS/many-leaves branch of Theorem 4.6.  The finite meta-tree dichotomy is
proved internally. -/
theorem polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        ChekuriChuzhoy.RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        ChekuriChuzhoy.CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u})
    (hA3 :
      ∃ cSplit : ℕ, 0 < cSplit ∧
        HairyPathOfSetsTheorem.AppendixA3ClusterSplitInput.{u} cSplit)
    (hsection4 :
      ∃ cCross : ℕ, 0 < cCross ∧
        CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} cCross)
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_extraction_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    hsparseOmega hroutable hcutMatching hbuild
    (ChekuriChuzhoy.strongPathOfSetsFromStrongTreeOfSets_of_leafExtraction
      hleaf)
    hA3 hsection4 hlocal hstitch

/-- Public axiom-free composition theorem with the strong-minor branch supplied
by the paper-level Chekuri--Chuzhoy Corollary 3.2 dichotomy. -/
theorem polynomial_grid_minor_theorem_of_chekuri_and_unbundled_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        PolynomialGridMinor.HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hchekuri : ChekuriChuzhoy.Corollary32Input.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_of_chekuri_and_unbundled_inputs
    hhairyInput hcrossInput hchekuri hproviders




/-- Public degree-ten corollary of the explicit-input composition theorem. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        PolynomialGridMinor.HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u} cGrid) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_inputs
    hhairyInput hcrossInput hstrongGrid hlargeData

/-- Public degree-ten corollary using explicit hard inputs, the unbundled
fixed-round cut-matching provider, and the explicit Theorem 8.1 target-size
provider. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        PolynomialGridMinor.HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong)
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          HairyCrossbarGrid.FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_inputs_and_unbundledCutMatching_and_targetProviders
    hhairyInput hcrossInput hstrongGrid hproviders

/-- Public degree-ten corollary from explicit hard inputs after internalizing
the explicit Theorem 8.1 target-size arithmetic. -/
theorem polynomial_grid_minor_theorem_degree10_of_inputs_and_unbundledCutMatching
    (hhairyInput :
      ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
        PolynomialGridMinor.HairyPathOfSetsInput.{u} cHair cHairLog)
    (hcrossInput :
      ∃ cCross : ℕ, 0 < cCross ∧
        HairyPathOfSetsSystem.CrossbarDichotomyInput.{u} cCross)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        PolynomialGridMinor.StrongMinorGridInput.{u} cStrong)
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_inputs_and_unbundledCutMatching
    hhairyInput hcrossInput hstrongGrid hprovider





end SimpleGraph

end Lax17Proofs
