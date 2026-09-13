import Lax17Proofs.Source.DegreeThreeStrongPathOfSetsContract

namespace Lax17Proofs

universe u v w

/-!
# Degree-three strong path-of-sets input

This module contains the proof-facing Appendix A.2 degree-three/strong
path-of-sets compositions.

The broad contract-backed theorem is kept available only as a legacy
conditional route.  It is not a self-contained proof.  The Chekuri--Chuzhoy
source-route theorems below do not use the broad A.2 contract
`DegreeThreeStrongPathOfSetsContract.exists_strongPathOfSets_of_treewidth`.
They route that part through the formalized Chekuri--Chuzhoy Theorem 2.21 and
Section 4 interfaces.

Theorem A.1 remains an explicit input in the `A1omega` variants.  The source
paper `treewidth-sparsifier.pdf` is present in the repository, and Section 2
has a substantial formalized proof route, but the full Theorem 1.1 route and
the topological-minor-to-same-vertex-subgraph bridge are not yet closed.  Do not
treat A.1 as self-contained until those pieces are proved.

The A.2 source-route variants expose the Chekuri--Chuzhoy semantic closure
instead of using the broad A.2 axiom.  They are still conditional until the
exposed Lemma 2.17, cut-matching/AARV, Section 4 strong-tree construction, and
leafy extraction inputs are fully proved.
-/

namespace SimpleGraph
namespace DegreeThreeStrongPathOfSets


/-- The doubled-length and scaled-width strong path-of-sets input used by
Appendix A.2 before the strong-to-hairy conversion. -/
def DoubledScaledInput (cStrong cStrongLog cSplit : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w k : ℕ},
      1 < ell →
        1 < w →
          1 < k →
            k ≤ treewidth G →
              cStrong * (cSplit * w) * (2 * ell) ^ 50 *
                  (Nat.log 2 k) ^ cStrongLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧
                    MaxDegreeAtMost H 3 ∧
                      Nonempty (StrongPathOfSetsSystem H (2 * ell) (cSplit * w))

/-- The paper-shaped Omega form of Theorem A.1 implies the threshold form used
in the Appendix A.2 parameter composition. -/
theorem degreeThreeTreewidthSparsifier_of_omega
    (homega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog) :
    ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {k t : ℕ},
          1 < k →
            k ≤ treewidth G →
              cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
                ∃ H : _root_.SimpleGraph V,
                  H ≤ G ∧ MaxDegreeAtMost H 3 ∧ t ≤ treewidth H :=
  DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifier_of_omega
    homega

/-- A degree-three strong path-of-sets theorem implies the doubled/scaled input
needed by Appendix A.2 for any positive split constant. -/
theorem exists_doubledScaledInput_of_degreeThreeStrongPathOfSets
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hstrong :
      ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w k : ℕ},
            1 < ell →
              1 < w →
                1 < k →
                  k ≤ treewidth G →
                    cStrong * w * ell ^ 50 *
                        (Nat.log 2 k) ^ cStrongLog < k →
                      ∃ H : _root_.SimpleGraph V,
                        H ≤ G ∧
                          MaxDegreeAtMost H 3 ∧
                            Nonempty (StrongPathOfSetsSystem H ell w)) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit := by
  rcases hstrong with ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, hinput⟩
  refine ⟨cStrong, cStrongLog, hcStrong, hcStrongLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htw hlarge
  have hell_doubled : 1 < 2 * ell := by
    have hle : ell ≤ 2 * ell := by
      simpa using Nat.mul_le_mul_right ell (by decide : 1 ≤ 2)
    exact lt_of_lt_of_le hell hle
  have hw_scaled : 1 < cSplit * w := by
    have hcSplit_one : 1 ≤ cSplit := Nat.succ_le_of_lt hcSplit
    have hle : w ≤ cSplit * w := by
      simpa using Nat.mul_le_mul_right w hcSplit_one
    exact lt_of_lt_of_le hw hle
  exact hinput (V := V) G hell_doubled hw_scaled hk htw hlarge


/-- Appendix A.2 source route from a sparsifier, the cut-well-linked Theorem
2.21 boundary, and the Section 4 tree-of-sets route. -/
theorem exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_route
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_route
      hsparseInput hcut hroute)

/-- Appendix A.2 source route from a sparsifier, the cut-well-linked Theorem
2.21 boundary, and the faithful direct Section 4 path route. -/
theorem exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_pathRoute
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_cutCore_and_pathRoute
      hsparseInput hcut hroute)

/-- Appendix A.2 source route from a sparsifier, Lemma 2.17 routability, the
cut-matching/AARV embedding source, and the Section 4 tree-of-sets route. -/
theorem exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_route
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_route
      hsparseInput hroutable hcutMatching hroute)

/-- Appendix A.2 source route from a sparsifier, Lemma 2.17 routability, the
cut-matching/AARV embedding source, and the faithful direct Section 4 path
route. -/
theorem exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      hsparseInput hroutable hcutMatching hroute)

/-- Appendix A.2 source route from a sparsifier, Lemma 2.17 routability, the
cut-matching/AARV embedding source, the Section 4 strong-tree construction,
and Theorem 4.6 extraction. -/
theorem exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      hsparseInput hroutable hcutMatching hbuild hextract)

/-- Appendix A.2 source route from a sparsifier, Lemma 2.17 routability, the
cut-matching/AARV embedding source, the Section 4 strong-tree construction,
and the split proof of Theorem 4.6. -/
theorem exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : ChekuriChuzhoy.StrongTreeMetaDichotomy.{u})
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
      hsparseInput hroutable hcutMatching hbuild hdichotomy hleaf)

/-- Appendix A.2 source route from a sparsifier, Lemma 2.17 routability, the
cut-matching/AARV embedding source, the Section 4 strong-tree construction,
the proved finite-tree dichotomy, and the DFS/many-leaves branch of Theorem
4.6. -/
theorem exists_doubledScaledInput_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        ChekuriChuzhoy.StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_sparsifier_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
      hsparseInput hroutable hcutMatching hbuild hleaf)

/-- Appendix A.2 source route from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, and the
faithful direct Section 4 path route. -/
theorem exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
          cRoute cRouteLog cDeltaPow) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      hsparseOmega hroutable hcutMatching hroute)

/-- Appendix A.2 source route from Theorem A.1 in its paper-shaped Omega form
and the bundled explicit Chekuri--Chuzhoy A.2 source inputs.

This is the theorem-shaped audit point for the degree-three strong
path-of-sets input once the proof is no longer allowed to use the broad A.2
contract axiom.  It remains conditional exactly on the A.1 sparsifier and the
three lower-level A.2 inputs bundled by
`ChekuriChuzhoy.TheoremA2SourceInputs`. -/
theorem exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_theoremA2SourceInputs
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2SourceInputs.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit := by
  rcases hA2 with ⟨hroutable, hcutMatching, hroute⟩
  exact
    exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_and_pathRoute
      hcSplit hsparseOmega hroutable hcutMatching hroute

/-- Appendix A.2 source route from Theorem A.1 in its paper-shaped Omega form
and the expanded Chekuri--Chuzhoy A.2 leaf-source inputs.

This is the preferred audit point when closing A.2 against the papers in the
repository.  It does not use the broad A.2 contract axiom and it does not bundle
Section 4 into the direct `StrongPathOfSetsFromNodeWellLinkedCore` interface:
the finite-tree dichotomy is already proved, while the remaining Section 4
strong-tree construction and leafy extraction branch are exposed separately. -/
theorem exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_theoremA2LeafSourceInputs
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2LeafSourceInputs.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit := by
  rcases hA2 with ⟨hroutable, hcutMatching, hbuild, hleaf⟩
  exact
    exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
      (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
        hsparseOmega hroutable hcutMatching hbuild hleaf)

/-- Appendix A.2 source route from Theorem A.1 in its paper-facing
topological-minor form and the bundled explicit Chekuri--Chuzhoy A.2 source
inputs.

This is the theorem-shaped audit point matching the two external statements
quoted in Chuzhoy--Tan Appendix A.2: Theorem A.1 is supplied as Theorem 1.1 of
`treewidth-sparsifier.pdf`, and the same-vertex degree-three sparsifier needed
for the parameter calculation is obtained by taking the support graph of the
topological-minor model. -/
theorem exists_doubledScaledInput_of_treewidthSparsifierTheorem11_and_ChekuriChuzhoy_theoremA2SourceInputs
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (h11 :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          TreewidthSparsifier.DegreeThreeTopologicalTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2SourceInputs.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit := by
  have hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog :=
    DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifierOmega_of_treewidthSparsifierTheorem11_and_supportGraphDegree
      (fun M hdegree =>
        M.supportGraph_maxDegreeAtMost_of_maxDegreeAtMost hdegree)
      h11
  exact
    exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_theoremA2SourceInputs
      hcSplit hsparseOmega hA2

/-- Appendix A.2 source route from Theorem A.1 in its paper-facing
topological-minor form and the expanded Chekuri--Chuzhoy A.2 leaf-source
inputs.

Compared with
`exists_doubledScaledInput_of_treewidthSparsifierTheorem11_and_ChekuriChuzhoy_theoremA2SourceInputs`,
this version exposes the Section 4 strong-tree construction and leafy
extraction branch separately. -/
theorem exists_doubledScaledInput_of_treewidthSparsifierTheorem11_and_ChekuriChuzhoy_theoremA2LeafSourceInputs
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
    (h11 :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          TreewidthSparsifier.DegreeThreeTopologicalTreewidthSparsifierOmega.{u}
            cSparse cSparseLog)
    (hA2 : ChekuriChuzhoy.TheoremA2LeafSourceInputs.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit := by
  have hsparseOmega :
      ∃ cSparse cSparseLog : ℕ,
        0 < cSparse ∧ 0 < cSparseLog ∧
          DegreeThreeStrongPathOfSetsContract.DegreeThreeTreewidthSparsifierOmega.{u}
            cSparse cSparseLog :=
    DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifierOmega_of_treewidthSparsifierTheorem11_and_supportGraphDegree
      (fun M hdegree =>
        M.supportGraph_maxDegreeAtMost_of_maxDegreeAtMost hdegree)
      h11
  exact
    exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_theoremA2LeafSourceInputs
      hcSplit hsparseOmega hA2

/-- Appendix A.2 source route from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, and Theorem 4.6 extraction. -/
theorem exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
    (hextract : ChekuriChuzhoy.StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_and_extraction
      hsparseOmega hroutable hcutMatching hbuild hextract)

/-- Appendix A.2 source route from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, and the split proof of Theorem 4.6. -/
theorem exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
      hsparseOmega hroutable hcutMatching hbuild hdichotomy hleaf)

/-- Appendix A.2 source route from Theorem A.1 in its paper-shaped Omega form,
Lemma 2.17 routability, the cut-matching/AARV embedding source, the Section 4
strong-tree construction, the proved finite-tree dichotomy, and the
DFS/many-leaves branch of Theorem 4.6. -/
theorem exists_doubledScaledInput_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
    {cSplit : ℕ} (hcSplit : 0 < cSplit)
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
    (hleaf : ChekuriChuzhoy.StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cStrong cStrongLog : ℕ, 0 < cStrong ∧ 0 < cStrongLog ∧
      DoubledScaledInput.{u} cStrong cStrongLog cSplit :=
  exists_doubledScaledInput_of_degreeThreeStrongPathOfSets hcSplit
    (DegreeThreeStrongPathOfSetsContract.exists_degreeThreeStrongPathOfSets_of_A1omega_and_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction
      hsparseOmega hroutable hcutMatching hbuild hleaf)

end DegreeThreeStrongPathOfSets
end SimpleGraph

end Lax17Proofs
