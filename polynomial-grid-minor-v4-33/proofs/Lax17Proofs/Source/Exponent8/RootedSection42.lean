import Lax17Proofs.Source.Theorem46
import Lax17Proofs.Source.Exponent8.Observation44RootProvenance
import Lax17Proofs.Source.Exponent8.RecursiveSlicing

namespace Lax17Proofs

/-!
# A rooted Section 4.2 producer for recursive slicing

The existing source-faithful Section 4.2 theorem existentially hides the
Observation 4.4 contraction state.  That is sufficient for the degree-ten
argument, but Section 5 must return selected contracted paths to their fixed
`X`-ending pseudo-grid paths.

This module runs Theorem 4.6 over a rooted reduced state, applies the additive
Lemma 4.8 producer in every slice, and packages the result as an initial
`RecursiveSliceLayer`.  Exact source-path localization is supplied by
`RootedObservation44State.toSliceLocalizationInvariant_fullRows`.
-/

namespace SimpleGraph
namespace Exponent8

open Section4Reduction

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D M w wHat Dhat : ℕ}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}

/-- Persistent recursive-slicing data exported by one rooted reduced
Observation 4.4 state.  Exact incidence provenance is reused for every future
slicing; no later layer is asked to reconstruct it from containment alone. -/
noncomputable def RootedObservation44State.recursiveSlicingContext
    {Gamma : PseudoGrid G A B X g D P Q}
    (Root : RootedObservation44State Gamma)
    (hReduced : Root.state.IsReduced)
    (hN : 0 < Gamma.rowPacking.card)
    (hDhat : 0 < Dhat)
    (hDscale : 2 * Dhat ≤ D)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet) :
    RecursiveSlicingContext
      G (Root.state.reducedGraph hReduced) A B X P Q
      (Root.state.reducedRow hReduced)
      (Root.state.reducedRetained hReduced) Dhat where
  Dhat_pos := hDhat
  unique_linkage := by
    exact Root.state.reducedRow_isUniqueLinkage hReduced hN
  slice_density := by
    intro m sigma i q hq
    apply hDscale.trans
    apply (Root.state.reducedRetained_metRows_card hReduced q).trans_eq
    congr 1
    ext r
    rw [sigma.mem_segmentIntersectingLeftIndices]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hmeet
      apply
        (sigma.sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
          (Root.state.reducedRetained hReduced) hq).2
      intro hdisjoint
      exact hmeet hdisjoint.symm
    · intro hsegment
      have hmeet :
          PathPacking.PathsIntersect
            ((Root.state.reducedRow hReduced).path r)
            ((Root.state.reducedRetained hReduced).path q) :=
        (sigma.sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
          (Root.state.reducedRetained hReduced) hq).1 hsegment
      intro hdisjoint
      exact hmeet hdisjoint.symm
  mkLocalization := by
    intro m sigma i I hI
    exact
      Root.toSliceLocalizationInvariant_fullRows
        hReduced sigma i I hI hXdisjoint
  mkLocalization_localizedQ := by
    intro m sigma i I hI
    rfl

/-- Rooted Observation 4.4, Theorem 4.6, and the additive one-slice cleanup,
assembled into the initial recursive layer.

The two division-free scale hypotheses are exactly what the cleanup producer
uses: every localized auxiliary path has at least `2 * Dhat` row neighbours,
and the width lower bound supplies enough total incidence mass in every
slice. -/
theorem exists_initialRecursiveSliceLayer_of_pseudoGrid
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hD : 0 < D) (hM : 0 < M) (hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card ≤
        Gamma.goodQSet.card)
    (hDhat : 0 < Dhat)
    (hDscale : 2 * Dhat ≤ D)
    (hmass :
      2 * Gamma.rowPacking.card * wHat ≤ Dhat * w)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet) :
    ∃ Root : RootedObservation44State Gamma,
      ∃ hReduced : Root.state.IsReduced,
        Nonempty
          (RecursiveSliceLayer
            G (Root.state.reducedGraph hReduced) A B X P Q
            (Root.state.reducedRow hReduced)
            (Root.state.reducedRetained hReduced)
            M w wHat Dhat) := by
  classical
  have hgoodPos : 0 < Gamma.goodQSet.card := by
    have hMw : 0 < M * w := Nat.mul_pos hM hw
    exact hMw.trans_le
      ((Nat.le_add_right (M * w)
        ((M + 1) * Gamma.rowPacking.card)).trans hcard)
  have hgood : Gamma.goodQSet.Nonempty := Finset.card_pos.mp hgoodPos
  have hN : 0 < Gamma.rowPacking.card := by
    have hDle :=
      Gamma.depth_le_reservedUnion_card_of_goodQSet_nonempty hgood
    have hrowCard :
        Gamma.rowPacking.card = Gamma.reservedUnion.card :=
      Gamma.rowPacking_card
    omega
  rcases
      RootedObservation44State.exists_reduced_of_pseudoGrid
        Gamma hminimal hD with
    ⟨Root, hReduced⟩
  let R := Root.state.reducedRow hReduced
  let Qpack := Root.state.reducedRetained hReduced
  have hunique : R.IsUniqueLinkage := by
    simpa [R] using
      Root.state.reducedRow_isUniqueLinkage hReduced hN
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage R Qpack := by
    simpa [R, Qpack] using
      Root.state.reducedRetained_intersects_reducedRow hReduced hD
  have hRcard : R.card = Gamma.rowPacking.card := by
    simp [R]
  have hQcard : Qpack.card = Gamma.goodQSet.card := by
    calc
      Qpack.card = Gamma.goodQPathPacking.card := by
        exact Root.state.reducedRetained_card hReduced
      _ = Gamma.goodQSet.card := Gamma.goodQPathPacking_card
  have hcard' : M * w + (M + 1) * R.card ≤ Qpack.card := by
    calc
      M * w + (M + 1) * R.card =
          M * w + (M + 1) * Gamma.rowPacking.card := by
            rw [hRcard]
      _ ≤ Gamma.goodQSet.card := hcard
      _ = Qpack.card := hQcard.symm
  rcases
      PathSlicing.theorem46 R Qpack M w hM hw hunique hintersects hcard' with
    ⟨sigma, hwidth⟩
  have hdense :
      ∀ (i : Fin M) (q : Qpack.Index),
        q ∈ sigma.pathsInSlice Qpack i →
          2 * Dhat ≤
            (sigma.segmentIntersectingLeftIndices Qpack i
              (Finset.univ : Finset R.Index) q).card := by
    intro i q hq
    apply hDscale.trans
    apply (Root.state.reducedRetained_metRows_card hReduced q).trans_eq
    congr 1
    ext r
    rw [sigma.mem_segmentIntersectingLeftIndices]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hmeet
      apply
        (sigma.sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
          Qpack hq).2
      intro hdisjoint
      exact hmeet hdisjoint.symm
    · intro hsegment
      have hmeet :
          PathPacking.PathsIntersect (R.path r) (Qpack.path q) :=
        (sigma.sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
          Qpack hq).1 hsegment
      intro hdisjoint
      exact hmeet hdisjoint.symm
  have hsliceMass :
      ∀ i : Fin M,
        2 * R.card * wHat ≤
          Dhat * (sigma.pathsInSlice Qpack i).card := by
    intro i
    calc
      2 * R.card * wHat =
          2 * Gamma.rowPacking.card * wHat := by rw [hRcard]
      _ ≤ Dhat * w := hmass
      _ ≤ Dhat * (sigma.pathsInSlice Qpack i).card :=
        Nat.mul_le_mul_left Dhat (hwidth i)
  let cleanup :
      ∀ i : Fin M, AdditiveSliceCleanup sigma i wHat Dhat :=
    fun i =>
      exists_additiveSliceCleanup R Qpack sigma i hDhat
        (hdense i) (hsliceMass i)
  let localization :
      ∀ i : Fin M,
        SliceLocalizationInvariant
          G (Root.state.reducedGraph hReduced) A B X P Q
          (Root.state.reducedRow hReduced)
          (Root.state.reducedRetained hReduced) sigma i :=
    fun i =>
      Root.toSliceLocalizationInvariant_fullRows hReduced sigma i
        (cleanup i).paths (cleanup i).paths_subset hXdisjoint
  refine ⟨Root, hReduced, ⟨?_⟩⟩
  refine
    { sigma := sigma
      width_at_least := hwidth
      unique_linkage := hunique
      cleanup := cleanup
      localization := localization
      localized_eq := ?_ }
  intro i
  rfl

/-- Source-level wrapper: the Theorem 4.1 setup supplies both minimality and
the fact that every main path is disjoint from the leaf-terminal set `X`. -/
theorem Theorem41Setup.exists_initialRecursiveSliceLayer_of_pseudoGrid
    {kappa : ℕ}
    (Setup : Theorem41Setup G A B X g kappa D P Q)
    (Gamma : PseudoGrid G A B X g D P Q)
    (hM : 0 < M) (hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card ≤
        Gamma.goodQSet.card)
    (hDhat : 0 < Dhat)
    (hDscale : 2 * Dhat ≤ D)
    (hmass :
      2 * Gamma.rowPacking.card * wHat ≤ Dhat * w) :
    ∃ Root : RootedObservation44State Gamma,
      ∃ hReduced : Root.state.IsReduced,
        Nonempty
          (RecursiveSliceLayer
            G (Root.state.reducedGraph hReduced) A B X P Q
            (Root.state.reducedRow hReduced)
            (Root.state.reducedRetained hReduced)
            M w wHat Dhat) := by
  apply
    SimpleGraph.Exponent8.exists_initialRecursiveSliceLayer_of_pseudoGrid
      Gamma Setup.minimal_pair Setup.D_pos_strict hM hw hcard
      hDhat hDscale hmass
  intro p
  exact (Setup.P_path_disjoint_X p).symm

end Exponent8
end SimpleGraph

end Lax17Proofs
