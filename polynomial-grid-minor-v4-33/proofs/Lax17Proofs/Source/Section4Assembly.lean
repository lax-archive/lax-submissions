import Lax17Proofs.Source.CrossbarTheorem
import Lax17Proofs.Source.PathPackingSupportDegree
import Lax17Proofs.Source.Theorem214Nonconstructive

namespace Lax17Proofs

/-!
# Chuzhoy--Tan Section 4: paper-specific assembly

This module closes the two paper-specific joins left after formalizing the
individual results in Chuzhoy--Tan Section 4.

The strongification theorem below is Step 6 (Section 4.6), specialized to the
maximum-degree-four weak Path-of-Sets System constructed in Step 5.  The two
applications of the boosting theorem are synchronized through the connector
path indices, and Theorem 4.21 supplies the within-cluster linkedness.
-/

namespace SimpleGraph

universe u

namespace Section4Assembly

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The exact parameters used in Chuzhoy--Tan Sections 4.2--4.5.

Keeping these quantities in one record makes the natural-number rounding and
the three hypotheses of Theorem 4.15 explicit. -/
structure Section4Parameters (g N : ℕ) where
  depth : ℕ := 64 * g ^ 4
  sliceCount : ℕ := 8 * g ^ 4 * Nat.log 2 g
  sliceWidth : ℕ := 2 ^ 11 * g ^ 6
  retainedDepth : ℕ := (64 * g ^ 4) / 4
  weakWidth : ℕ := g ^ 2
  depth_eq : depth = 64 * g ^ 4 := by rfl
  sliceCount_eq : sliceCount = 8 * g ^ 4 * Nat.log 2 g := by rfl
  sliceWidth_eq : sliceWidth = 2 ^ 11 * g ^ 6 := by rfl
  retainedDepth_eq : retainedDepth = 16 * g ^ 4 := by omega
  weakWidth_eq : weakWidth = g ^ 2 := by rfl
  depth_le_rows : depth ≤ N
  rows_le : N ≤ depth * g ^ 2
  weakWidth_pos : 0 < weakWidth
  sliceCount_pos : 0 < sliceCount
  sliceWidth_pos : 0 < sliceWidth
  theorem415_rows : 3 * weakWidth ≤ N
  theorem415_square : 4 * N * weakWidth ≤ retainedDepth ^ 2
  theorem415_large :
    2 * N * weakWidth ≤ retainedDepth * sliceCount

/-- The paper's inequalities
`D ≤ N ≤ D g^2`, with `D = 64 g^4`, imply all numerical hypotheses used in
Sections 4.2--4.5. -/
def section4Parameters
    {g N : ℕ} (hg : 2 ≤ g)
    (hNlower : 64 * g ^ 4 ≤ N)
    (hNupper : N ≤ (64 * g ^ 4) * g ^ 2) :
    Section4Parameters g N := by
  have hlog : 0 < Nat.log 2 g := by
    exact Nat.log_pos (by norm_num) hg
  refine
    { depth_le_rows := hNlower
      rows_le := hNupper
      weakWidth_pos := by positivity
      sliceCount_pos := by positivity
      sliceWidth_pos := by positivity
      theorem415_rows := ?_
      theorem415_square := ?_
      theorem415_large := ?_ }
  · have hg4 : 3 * g ^ 2 ≤ 64 * g ^ 4 := by nlinarith [sq_nonneg (g ^ 2)]
    exact hg4.trans hNlower
  · dsimp
    rw [show 64 * g ^ 4 / 4 = 16 * g ^ 4 by omega]
    have hg4pos : 0 < g ^ 4 := by positivity
    calc
      4 * N * g ^ 2
          ≤ 4 * ((64 * g ^ 4) * g ^ 2) * g ^ 2 :=
            Nat.mul_le_mul_right (g ^ 2)
              (Nat.mul_le_mul_left 4 hNupper)
      _ ≤ (16 * g ^ 4) ^ 2 := by
        nlinarith [sq_nonneg (g ^ 4)]
  · dsimp
    rw [show 64 * g ^ 4 / 4 = 16 * g ^ 4 by omega]
    have hM : 8 * g ^ 4 ≤ 8 * g ^ 4 * Nat.log 2 g := by
      calc
        8 * g ^ 4 = 8 * g ^ 4 * 1 := by simp
        _ ≤ 8 * g ^ 4 * Nat.log 2 g :=
          Nat.mul_le_mul_left (8 * g ^ 4) hlog
    calc
      2 * N * g ^ 2
          ≤ 2 * ((64 * g ^ 4) * g ^ 2) * g ^ 2 :=
            Nat.mul_le_mul_right (g ^ 2)
              (Nat.mul_le_mul_left 2 hNupper)
      _ ≤ (16 * g ^ 4) * (8 * g ^ 4) := by
        nlinarith [sq_nonneg (g ^ 4)]
      _ ≤ (16 * g ^ 4) * (8 * g ^ 4 * Nat.log 2 g) :=
        Nat.mul_le_mul_left (16 * g ^ 4) hM

/-- The support graph `H'`, the union of one node-disjoint row packing and one
node-disjoint auxiliary packing, has maximum degree at most four. -/
theorem PseudoGrid.hPrimeGraph_maxDegreeAtMost_four
    {A B X : Finset V} {g D : ℕ}
    {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}
    (Gamma : PseudoGrid G A B X g D P Q) :
    MaxDegreeAtMost Gamma.hPrimeGraph 4 := by
  simpa [PseudoGrid.hPrimeGraph] using
    maxDegreeAtMost_sup
      Gamma.rowPacking.maxDegreeAtMost_spanningGraph
      Gamma.goodQPathPacking.maxDegreeAtMost_spanningGraph

/-- The exponent-ten threshold pays simultaneously for the paths discarded in
Section 4.2 and for the exact Theorem 4.6 slicing budget
`M * w + (M + 1) * N`. -/
theorem PseudoGrid.section42_slicing_budget_depth64
    {A B X : Finset V} {g kappa : ℕ}
    {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q)
    (hg : 2 ≤ g)
    (hlarge : 2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa)
    (hPcard : P.card = kappa) :
    (8 * g ^ 4 * Nat.log 2 g) * (2 ^ 11 * g ^ 6) +
          (8 * g ^ 4 * Nat.log 2 g + 1) * Gamma.rowPacking.card ≤
      Gamma.goodQSet.card := by
  have hlog : 0 < Nat.log 2 g :=
    Nat.log_pos (by norm_num) hg
  have hN :
      Gamma.rowPacking.card ≤ (64 * g ^ 4) * g ^ 2 := by
    simpa using Gamma.reservedUnion_card_le
  have hgpow : g ^ 6 ≤ g ^ 10 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hglog : g ^ 6 ≤ g ^ 10 * Nat.log 2 g := by
    calc
      g ^ 6 ≤ g ^ 10 := hgpow
      _ ≤ g ^ 10 * Nat.log 2 g :=
        Nat.le_mul_of_pos_right _ hlog
  have hN' :
      Gamma.rowPacking.card ≤ 64 * g ^ 6 := by
    calc
      Gamma.rowPacking.card ≤ (64 * g ^ 4) * g ^ 2 := hN
      _ = 64 * g ^ 6 := by ring
  have hNlog :
      Gamma.rowPacking.card ≤ 64 * (g ^ 10 * Nat.log 2 g) :=
    hN'.trans (Nat.mul_le_mul_left 64 hglog)
  have hdiscard :
      (64 * g ^ 4) * (2 * g ^ 2) ≤
        128 * (g ^ 10 * Nat.log 2 g) := by
    calc
      (64 * g ^ 4) * (2 * g ^ 2) = 128 * g ^ 6 := by ring
      _ ≤ 128 * (g ^ 10 * Nat.log 2 g) :=
        Nat.mul_le_mul_left 128 hglog
  have hmain :
      (8 * g ^ 4 * Nat.log 2 g) * (2 ^ 11 * g ^ 6) =
        16384 * (g ^ 10 * Nat.log 2 g) := by
    ring
  have hrows :
      (8 * g ^ 4 * Nat.log 2 g + 1) * Gamma.rowPacking.card ≤
        576 * (g ^ 10 * Nat.log 2 g) := by
    calc
      (8 * g ^ 4 * Nat.log 2 g + 1) * Gamma.rowPacking.card =
          (8 * g ^ 4 * Nat.log 2 g) * Gamma.rowPacking.card +
            Gamma.rowPacking.card := by ring
      _ ≤ (8 * g ^ 4 * Nat.log 2 g) * (64 * g ^ 6) +
            64 * (g ^ 10 * Nat.log 2 g) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left (8 * g ^ 4 * Nat.log 2 g) hN')
          hNlog
      _ = 576 * (g ^ 10 * Nat.log 2 g) := by ring
  apply Gamma.goodQSet_card_lower_bound_of_packing_bound
  rw [hPcard]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  have hsum :
      (64 * g ^ 4) * (2 * g ^ 2) +
          ((8 * g ^ 4 * Nat.log 2 g) * (2 ^ 11 * g ^ 6) +
            (8 * g ^ 4 * Nat.log 2 g + 1) *
              Gamma.rowPacking.card) ≤
        (128 + 16384 + 576) * (g ^ 10 * Nat.log 2 g) := by
    calc
      (64 * g ^ 4) * (2 * g ^ 2) +
            ((8 * g ^ 4 * Nat.log 2 g) * (2 ^ 11 * g ^ 6) +
              (8 * g ^ 4 * Nat.log 2 g + 1) *
                Gamma.rowPacking.card)
          ≤ 128 * (g ^ 10 * Nat.log 2 g) +
              (16384 * (g ^ 10 * Nat.log 2 g) +
                576 * (g ^ 10 * Nat.log 2 g)) :=
        Nat.add_le_add hdiscard
          (Nat.add_le_add (le_of_eq hmain) hrows)
      _ = (128 + 16384 + 576) * (g ^ 10 * Nat.log 2 g) := by ring
  calc
    ((64 * g ^ 4) * (2 * g ^ 2) +
        ((8 * g ^ 4 * Nat.log 2 g) * (2 ^ 11 * g ^ 6) +
          (8 * g ^ 4 * Nat.log 2 g + 1) *
            Gamma.rowPacking.card)) * 4
        ≤ ((128 + 16384 + 576) *
            (g ^ 10 * Nat.log 2 g)) * 4 :=
          Nat.mul_le_mul_right 4 hsum
    _ ≤ 2 ^ 22 * g ^ 10 * Nat.log 2 g := by
      nlinarith
    _ ≤ kappa := hlarge

/-- Data retained across one gap of a weak Path-of-Sets System during the
Section 4.6 strongification. -/
structure GapStrongData {ell w w' : ℕ}
    (P : PathOfSetsSystem G ell w)
    (i : Fin ell) (hi : i.1 + 1 < ell) where
  sourceEnvelope : Finset V
  targetEnvelope : Finset V
  indexSet : Finset (P.connector i hi).Index
  card_indexSet : indexSet.card = w'
  sourceEnvelope_subset : sourceEnvelope ⊆ P.right i
  targetEnvelope_subset : targetEnvelope ⊆ P.left ⟨i.1 + 1, hi⟩
  source_subset_envelope :
    (P.connector i hi).sourceSet indexSet ⊆ sourceEnvelope
  target_subset_envelope :
    (P.connector i hi).targetSet indexSet ⊆ targetEnvelope
  sourceEnvelope_large : 8 * w' ≤ sourceEnvelope.card
  targetEnvelope_large : 8 * w' ≤ targetEnvelope.card
  sourceEnvelope_nodeWellLinked :
    NodeWellLinkedIn G (P.cluster i) sourceEnvelope
  targetEnvelope_nodeWellLinked :
    NodeWellLinkedIn G (P.cluster ⟨i.1 + 1, hi⟩) targetEnvelope

namespace GapStrongData

variable {ell w w' : ℕ} {P : PathOfSetsSystem G ell w}

@[simp] theorem source_card
    {i : Fin ell} {hi : i.1 + 1 < ell}
    (D : GapStrongData (G := G) (w' := w') P i hi) :
    ((P.connector i hi).sourceSet D.indexSet).card = w' := by
  rw [PerfectPathPacking.sourceSet_card, D.card_indexSet]

@[simp] theorem target_card
    {i : Fin ell} {hi : i.1 + 1 < ell}
    (D : GapStrongData (G := G) (w' := w') P i hi) :
    ((P.connector i hi).targetSet D.indexSet).card = w' := by
  rw [PerfectPathPacking.targetSet_card, D.card_indexSet]

theorem source_subset
    {i : Fin ell} {hi : i.1 + 1 < ell}
    (D : GapStrongData (G := G) (w' := w') P i hi) :
    (P.connector i hi).sourceSet D.indexSet ⊆ P.right i :=
  subset_trans D.source_subset_envelope D.sourceEnvelope_subset

theorem target_subset
    {i : Fin ell} {hi : i.1 + 1 < ell}
    (D : GapStrongData (G := G) (w' := w') P i hi) :
    (P.connector i hi).targetSet D.indexSet ⊆ P.left ⟨i.1 + 1, hi⟩ :=
  subset_trans D.target_subset_envelope D.targetEnvelope_subset

theorem source_nodeWellLinked
    {i : Fin ell} {hi : i.1 + 1 < ell}
    (D : GapStrongData (G := G) (w' := w') P i hi) :
    NodeWellLinkedIn G (P.cluster i)
      ((P.connector i hi).sourceSet D.indexSet) :=
  NodeWellLinkedIn.mono_terminals
    D.sourceEnvelope_nodeWellLinked D.source_subset_envelope

theorem target_nodeWellLinked
    {i : Fin ell} {hi : i.1 + 1 < ell}
    (D : GapStrongData (G := G) (w' := w') P i hi) :
    NodeWellLinkedIn G (P.cluster ⟨i.1 + 1, hi⟩)
      ((P.connector i hi).targetSet D.indexSet) :=
  NodeWellLinkedIn.mono_terminals
    D.targetEnvelope_nodeWellLinked D.target_subset_envelope

end GapStrongData

/-- The exact integer width retained by the formal Section 4.6 proof.

For systems shorter than `20000` we retain one connector.  Above that
threshold, two applications of the `3/(10*4)` boosting bound and the
one-eighth thinning in Theorem 4.21 leave at least `ell / 20000` terminals.
The slightly relaxed universal constant absorbs the unavoidable natural-number
rounding that is suppressed in the paper's `Omega(w)` notation. -/
def strongifiedWidth (ell : ℕ) : ℕ :=
  if ell < 20000 then 1 else ell / 20000 + 1

theorem strongifiedWidth_pos {ell : ℕ} (hell : 0 < ell) :
    0 < strongifiedWidth ell := by
  unfold strongifiedWidth
  split_ifs with h
  · omega
  · omega

theorem le_twentyThousand_mul_strongifiedWidth {ell : ℕ} (hell : 0 < ell) :
    ell ≤ 20000 * strongifiedWidth ell := by
  unfold strongifiedWidth
  split_ifs with h
  · omega
  · have hle : ell / 20000 * 20000 ≤ ell :=
      Nat.div_mul_le_self ell 20000
    omega

private theorem strongifiedWidth_le_secondBoost {ell : ℕ}
    (hlarge : ¬ ell < 20000) :
    strongifiedWidth ell ≤
      (3 * ((3 * ell) / 40)) / 40 := by
  unfold strongifiedWidth
  simp only [if_neg hlarge]
  omega

private theorem eight_mul_strongifiedWidth_le {ell : ℕ}
    (hlarge : ¬ ell < 20000) :
    2 * 4 * strongifiedWidth ell ≤ ell := by
  unfold strongifiedWidth
  simp only [if_neg hlarge]
  have hle : ell / 20000 * 20000 ≤ ell :=
    Nat.div_mul_le_self ell 20000
  have hdivpos : 0 < ell / 20000 :=
    Nat.div_pos (by omega) (by norm_num)
  omega

/-- A one-element terminal subset of a nonempty finite terminal set. -/
noncomputable def singletonSubset {T : Finset V} (hT : T.Nonempty) : Finset V :=
  {Classical.choose hT}

theorem singletonSubset_subset {T : Finset V} (hT : T.Nonempty) :
    singletonSubset hT ⊆ T := by
  intro v hv
  have hv' : v = Classical.choose hT := by
    simpa [singletonSubset] using hv
  simpa [hv'] using Classical.choose_spec hT

@[simp] theorem singletonSubset_card {T : Finset V} (hT : T.Nonempty) :
    (singletonSubset hT).card = 1 := by
  simp [singletonSubset]

/-- The low-width branch of Section 4.6.  One connector is retained in every
gap.  Connectedness of the clusters makes singleton nail sets node-well-linked,
and edge-well-linkedness of the old nail union links the two retained
singletons. -/
noncomputable def singletonStrongificationData
    {ell w : ℕ} (P : WeakPathOfSetsSystem G ell w) :
    Section46.StrongificationData
      (G := G) (P := P.toPathOfSetsSystem) (w' := 1) := by
  let P0 := P.toPathOfSetsSystem
  have hell : 0 < ell := P0.length_pos
  let first : Fin ell := ⟨0, hell⟩
  let last : Fin ell := ⟨ell - 1, by omega⟩
  let gapIndex :
      (i : Fin ell) → (hi : i.1 + 1 < ell) →
        (P0.connector i hi).Index :=
    fun i hi => Classical.choice
      (Fintype.card_pos_iff.mp (by
        have hc : 0 < (P0.connector i hi).card := by
          rw [P0.connector_card i hi]
          exact P0.width_pos
        simpa [PerfectPathPacking.card] using hc))
  let gapSet :
      (i : Fin ell) → (hi : i.1 + 1 < ell) →
        Finset (P0.connector i hi).Index :=
    fun i hi => {gapIndex i hi}
  let firstLeft : Finset V :=
    singletonSubset (Finset.card_pos.mp (by
      rw [P0.left_card first]
      exact P0.width_pos))
  let lastRight : Finset V :=
    singletonSubset (Finset.card_pos.mp (by
      rw [P0.right_card last]
      exact P0.width_pos))
  let left : Fin ell → Finset V := fun i =>
    if h0 : i.1 = 0 then firstLeft
    else
      let j : Fin ell := ⟨i.1 - 1, by omega⟩
      let hj : j.1 + 1 < ell := by
        dsimp [j]
        omega
      (P0.connector j hj).targetSet (gapSet j hj)
  let right : Fin ell → Finset V := fun i =>
    if hi : i.1 + 1 < ell then
      (P0.connector i hi).sourceSet (gapSet i hi)
    else lastRight
  have hfirstLeft :
      firstLeft ⊆ P0.left first := by
    exact singletonSubset_subset (Finset.card_pos.mp (by
      rw [P0.left_card first]
      exact P0.width_pos))
  have hlastRight :
      lastRight ⊆ P0.right last := by
    exact singletonSubset_subset (Finset.card_pos.mp (by
      rw [P0.right_card last]
      exact P0.width_pos))
  have hleft_subset : ∀ i : Fin ell, left i ⊆ P0.left i := by
    intro i
    dsimp [left]
    split_ifs with h0
    · have hi : i = first := Fin.ext h0
      simpa [hi] using hfirstLeft
    · intro v hv
      let j : Fin ell := ⟨i.1 - 1, by omega⟩
      let hj : j.1 + 1 < ell := by
        dsimp [j]
        omega
      have hnext : (⟨j.1 + 1, hj⟩ : Fin ell) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      rw [← hnext]
      exact (P0.connector j hj).targetSet_subset_right (gapSet j hj) hv
  have hright_subset : ∀ i : Fin ell, right i ⊆ P0.right i := by
    intro i
    dsimp [right]
    split_ifs with hi
    · exact (P0.connector i hi).sourceSet_subset_left (gapSet i hi)
    · have hilast : i = last := by
        apply Fin.ext
        dsimp [last]
        omega
      simpa [hilast] using hlastRight
  have hleft_card : ∀ i : Fin ell, (left i).card = 1 := by
    intro i
    dsimp [left]
    split_ifs <;> simp [firstLeft, gapSet]
  have hright_card : ∀ i : Fin ell, (right i).card = 1 := by
    intro i
    dsimp [right]
    split_ifs <;> simp [lastRight, gapSet]
  refine
    { width_pos := by norm_num
      left := left
      right := right
      left_subset_left := ?_
      right_subset_right := ?_
      left_card := ?_
      right_card := ?_
      connectorIndexSet := gapSet
      connectorIndexSet_card := ?_
      sourceSet_eq_right := ?_
      targetSet_eq_left_next := ?_
      left_nodeWellLinked := ?_
      right_nodeWellLinked := ?_
      left_right_nodeLinked := ?_ }
  · exact hleft_subset
  · exact hright_subset
  · exact hleft_card
  · exact hright_card
  · intro i hi
    simp [gapSet]
  · intro i hi
    change (P0.connector i hi).sourceSet (gapSet i hi) = right i
    simp [right, hi]
  · intro i hi
    change (P0.connector i hi).targetSet (gapSet i hi) =
      left ⟨i.1 + 1, hi⟩
    dsimp [left]
  · intro i
    apply Section46.nodeWellLinkedIn_of_card_le_three_of_isCluster
      (P0.cluster_connected i)
    · exact subset_trans (hleft_subset i) (P0.left_subset_cluster i)
    · rw [hleft_card i]
      omega
  · intro i
    apply Section46.nodeWellLinkedIn_of_card_le_three_of_isCluster
      (P0.cluster_connected i)
    · exact subset_trans (hright_subset i) (P0.right_subset_cluster i)
    · rw [hright_card i]
      omega
  · intro i
    apply Section46.nodeLinkedIn_of_edgeWellLinked_card_le_one
    · exact subset_trans (hleft_subset i) (P0.left_subset_cluster i)
    · exact subset_trans (hright_subset i) (P0.right_subset_cluster i)
    · exact (P0.left_right_disjoint i).mono
        (hleft_subset i) (hright_subset i)
    · simpa [hleft_card i]
    · simpa [hright_card i]
    · apply EdgeWellLinkedIn.mono_terminals (P.nails_edgeWellLinked i)
      exact Finset.union_subset_union
        (hleft_subset i) (hright_subset i)

private theorem eight_mul_strongifiedWidth_le_secondBoost {ell : ℕ}
    (hlarge : ¬ ell < 20000) :
    8 * strongifiedWidth ell ≤
      (3 * ((3 * ell) / 40)) / 40 := by
  unfold strongifiedWidth
  simp only [if_neg hlarge]
  omega

/-- A boosted node-well-linked envelope together with an exact-size retained
subset.  Keeping the envelope is essential: Theorem 4.21 links the final
subsets by using the larger boosted sets. -/
structure BoostedSetData (C T : Finset V) (w' : ℕ) where
  envelope : Finset V
  selected : Finset V
  envelope_subset : envelope ⊆ T
  selected_subset_envelope : selected ⊆ envelope
  selected_card : selected.card = w'
  envelope_large : 8 * w' ≤ envelope.card
  boost_lower : (3 * T.card) / 40 ≤ envelope.card
  envelope_nodeWellLinked : NodeWellLinkedIn G C envelope

/-- Chekuri--Chuzhoy Theorem 2.14 specialized to degree four, retaining both
the boosted set and an exact-size subset for Theorem 4.21. -/
theorem exists_boostedSetData_maxDegreeFour
    {C T : Finset V} {κ w' : ℕ}
    (hcluster : IsCluster G C)
    (hdegree : MaxDegreeAtMost G 4)
    (hcard : T.card = κ)
    (hwell : EdgeWellLinkedIn G C T)
    (hscale : 8 * w' ≤ (3 * κ) / 40) :
    Nonempty (BoostedSetData (G := G) C T w') := by
  classical
  rcases ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_floor
      (G := G) (C := C) (T := T)
      (alphaNum := 1) (alphaDen := 1) (Δ := 4) (κ := κ)
      hcluster hdegree (by norm_num) (by norm_num) (by norm_num)
      hcard (Section46.scaledEdgeWellLinkedIn_one_of_edgeWellLinkedIn hwell) with
    ⟨Tbig, hTbigT, hbig, hbigNode⟩
  have hlargeBig : 8 * w' ≤ Tbig.card :=
    hscale.trans (by simpa using hbig)
  have hwBig : w' ≤ Tbig.card := by omega
  rcases Finset.exists_subset_card_eq hwBig with ⟨T', hT'Tbig, hT'card⟩
  exact
    ⟨{ envelope := Tbig
       selected := T'
       envelope_subset := hTbigT
       selected_subset_envelope := hT'Tbig
       selected_card := hT'card
       envelope_large := hlargeBig
       boost_lower := by simpa [hcard] using hbig
       envelope_nodeWellLinked := hbigNode }⟩

/-- The two boosts across one connector family in Step 6.  The first boost is
performed on the right nails of cluster `i`; its path indices transport the
chosen nails to cluster `i+1`, where the second boost is performed. -/
theorem exists_boostedGapStrongData
    {ell w : ℕ} (P : WeakPathOfSetsSystem G ell w)
    (hdegree : MaxDegreeAtMost G 4)
    (hlarge : ¬ w < 20000)
    (i : Fin ell) (hi : i.1 + 1 < ell) :
    Nonempty (GapStrongData (G := G) (w' := strongifiedWidth w)
      P.toPathOfSetsSystem i hi) := by
  let P0 := P.toPathOfSetsSystem
  let a := (3 * w) / 40
  have hfirstScale : 8 * strongifiedWidth w ≤ (3 * w) / 40 := by
    have hsecond := eight_mul_strongifiedWidth_le_secondBoost hlarge
    omega
  rcases exists_boostedSetData_maxDegreeFour
      (G := G) (C := P0.cluster i) (T := P0.right i)
      (κ := w) (w' := strongifiedWidth w)
      (P0.cluster_connected i) hdegree (P0.right_card i)
      (EdgeWellLinkedIn.mono_terminals (P.nails_edgeWellLinked i)
        (Finset.subset_union_right (s₁ := P0.left i) (s₂ := P0.right i)))
      hfirstScale with ⟨Bdata⟩
  let I₁ := (P0.connector i hi).sourceIndexSetOfSubset Bdata.envelope
  let Atemp := (P0.connector i hi).targetSet I₁
  have hAtempCard : Atemp.card = Bdata.envelope.card := by
    calc
      Atemp.card = I₁.card := (P0.connector i hi).targetSet_card I₁
      _ = Bdata.envelope.card := by
        exact (P0.connector i hi).sourceIndexSetOfSubset_card
          Bdata.envelope_subset
  have hAtempSubset : Atemp ⊆ P0.left ⟨i.1 + 1, hi⟩ :=
    (P0.connector i hi).targetSet_subset_right I₁
  have hAtempWell :
      EdgeWellLinkedIn G (P0.cluster ⟨i.1 + 1, hi⟩) Atemp := by
    apply EdgeWellLinkedIn.mono_terminals
      (P.nails_edgeWellLinked ⟨i.1 + 1, hi⟩)
    exact subset_trans hAtempSubset
      (Finset.subset_union_left
        (s₁ := P0.left ⟨i.1 + 1, hi⟩)
        (s₂ := P0.right ⟨i.1 + 1, hi⟩))
  have hsecondScale :
      8 * strongifiedWidth w ≤ (3 * Atemp.card) / 40 := by
    have hbase :
        8 * strongifiedWidth w ≤ (3 * a) / 40 := by
      simpa [a] using eight_mul_strongifiedWidth_le_secondBoost hlarge
    have ha : a ≤ Atemp.card := by
      rw [hAtempCard]
      simpa [a, P0.right_card i] using Bdata.boost_lower
    omega
  rcases exists_boostedSetData_maxDegreeFour
      (G := G) (C := P0.cluster ⟨i.1 + 1, hi⟩) (T := Atemp)
      (κ := Atemp.card) (w' := strongifiedWidth w)
      (P0.cluster_connected ⟨i.1 + 1, hi⟩) hdegree rfl
      hAtempWell hsecondScale with ⟨Adata⟩
  let Ifinal :=
    (P0.connector i hi).targetIndexSetOfSubset Adata.selected
  have hAfinalTemp : Adata.selected ⊆ Atemp :=
    subset_trans Adata.selected_subset_envelope Adata.envelope_subset
  have hAfinalRight : Adata.selected ⊆ P0.left ⟨i.1 + 1, hi⟩ :=
    subset_trans hAfinalTemp hAtempSubset
  have hIfinalI₁ : Ifinal ⊆ I₁ := by
    exact (P0.connector i hi).targetIndexSetOfSubset_subset_indexSet
      (by simpa [Atemp] using hAfinalTemp)
  have hsourceEnvelope :
      (P0.connector i hi).sourceSet Ifinal ⊆ Bdata.envelope := by
    calc
      (P0.connector i hi).sourceSet Ifinal
          ⊆ (P0.connector i hi).sourceSet I₁ :=
        (P0.connector i hi).sourceSet_mono hIfinalI₁
      _ = Bdata.envelope :=
        (P0.connector i hi).sourceSet_sourceIndexSetOfSubset
          Bdata.envelope_subset
  have htargetAfinal :
      (P0.connector i hi).targetSet Ifinal = Adata.selected :=
    (P0.connector i hi).targetSet_targetIndexSetOfSubset hAfinalRight
  refine
    ⟨{ sourceEnvelope := Bdata.envelope
       targetEnvelope := Adata.envelope
       indexSet := Ifinal
       card_indexSet := ?_
       sourceEnvelope_subset := Bdata.envelope_subset
       targetEnvelope_subset :=
         subset_trans Adata.envelope_subset hAtempSubset
       source_subset_envelope := hsourceEnvelope
       target_subset_envelope := by
         rw [htargetAfinal]
         exact Adata.selected_subset_envelope
       sourceEnvelope_large := Bdata.envelope_large
       targetEnvelope_large := Adata.envelope_large
       sourceEnvelope_nodeWellLinked := Bdata.envelope_nodeWellLinked
       targetEnvelope_nodeWellLinked := Adata.envelope_nodeWellLinked }⟩
  calc
    Ifinal.card = Adata.selected.card :=
      (P0.connector i hi).targetIndexSetOfSubset_card hAfinalRight
    _ = strongifiedWidth w := Adata.selected_card

/-- Boost an endpoint nail set and retain the envelope used by Theorem 4.21. -/
theorem exists_boostedEndpointSet
    {ell w : ℕ} (P : WeakPathOfSetsSystem G ell w)
    (hdegree : MaxDegreeAtMost G 4)
    (hlarge : ¬ w < 20000)
    (i : Fin ell) (T : Finset V)
    (hTcard : T.card = w)
    (hTwell : EdgeWellLinkedIn G (P.cluster i) T) :
    Nonempty (BoostedSetData (G := G) (P.cluster i) T
      (strongifiedWidth w)) := by
  have hw : 8 * strongifiedWidth w ≤ (3 * w) / 40 := by
    have hsecond := eight_mul_strongifiedWidth_le_secondBoost hlarge
    omega
  exact exists_boostedSetData_maxDegreeFour
      (G := G) (C := P.cluster i) (T := T)
      (κ := w) (w' := strongifiedWidth w)
      (P.cluster_connected i) hdegree hTcard hTwell hw

/-- Chuzhoy--Tan Section 4.6 for a maximum-degree-four weak
Path-of-Sets System.  The output has the same length and width within the
universal factor `20000`. -/
noncomputable def strongificationData_of_weakPathOfSetsSystem_maxDegreeFour
    {ell w : ℕ} (P : WeakPathOfSetsSystem G ell w)
    (hdegree : MaxDegreeAtMost G 4) :
    Section46.StrongificationData
      (G := G) (P := P.toPathOfSetsSystem)
      (w' := strongifiedWidth w) := by
  classical
  by_cases hlarge : w < 20000
  · have hwidth : strongifiedWidth w = 1 := by
      simp [strongifiedWidth, hlarge]
    simpa [hwidth] using singletonStrongificationData P
  · let P0 := P.toPathOfSetsSystem
    have hell : 0 < ell := P0.length_pos
    let first : Fin ell := ⟨0, hell⟩
    let last : Fin ell := ⟨ell - 1, by omega⟩
    let Gap :
        (i : Fin ell) → (hi : i.1 + 1 < ell) →
          GapStrongData (G := G) (w' := strongifiedWidth w) P0 i hi :=
      fun i hi => Classical.choice
        (exists_boostedGapStrongData P hdegree hlarge i hi)
    let LeftEnd :=
      Classical.choice <| exists_boostedEndpointSet
        P hdegree hlarge first (P0.left first) (P0.left_card first)
          (EdgeWellLinkedIn.mono_terminals (P.nails_edgeWellLinked first)
            (Finset.subset_union_left
              (s₁ := P0.left first) (s₂ := P0.right first)))
    let RightEnd :=
      Classical.choice <| exists_boostedEndpointSet
        P hdegree hlarge last (P0.right last) (P0.right_card last)
          (EdgeWellLinkedIn.mono_terminals (P.nails_edgeWellLinked last)
            (Finset.subset_union_right
              (s₁ := P0.left last) (s₂ := P0.right last)))
    let left : Fin ell → Finset V := fun i =>
      if h0 : i.1 = 0 then LeftEnd.selected
      else
        let j : Fin ell := ⟨i.1 - 1, by omega⟩
        let hj : j.1 + 1 < ell := by
          dsimp [j]
          omega
        (P0.connector j hj).targetSet (Gap j hj).indexSet
    let right : Fin ell → Finset V := fun i =>
      if hi : i.1 + 1 < ell then
        (P0.connector i hi).sourceSet (Gap i hi).indexSet
      else RightEnd.selected
    let leftEnvelope : Fin ell → Finset V := fun i =>
      if h0 : i.1 = 0 then LeftEnd.envelope
      else
        let j : Fin ell := ⟨i.1 - 1, by omega⟩
        let hj : j.1 + 1 < ell := by
          dsimp [j]
          omega
        (Gap j hj).targetEnvelope
    let rightEnvelope : Fin ell → Finset V := fun i =>
      if hi : i.1 + 1 < ell then (Gap i hi).sourceEnvelope
      else RightEnd.envelope
    have hleft_subset : ∀ i : Fin ell, left i ⊆ P0.left i := by
      intro i
      dsimp [left]
      split_ifs with h0
      · have hi : i = first := Fin.ext h0
        simpa [hi] using
          (subset_trans LeftEnd.selected_subset_envelope
            LeftEnd.envelope_subset)
      · let j : Fin ell := ⟨i.1 - 1, by omega⟩
        let hj : j.1 + 1 < ell := by dsimp [j]; omega
        have hnext : (⟨j.1 + 1, hj⟩ : Fin ell) = i := by
          apply Fin.ext
          dsimp [j]
          omega
        simpa only [hnext] using (Gap j hj).target_subset
    have hright_subset : ∀ i : Fin ell, right i ⊆ P0.right i := by
      intro i
      dsimp [right]
      split_ifs with hi
      · exact (Gap i hi).source_subset
      · have hilast : i = last := by
          apply Fin.ext
          dsimp [last]
          omega
        simpa [hilast] using
          (subset_trans RightEnd.selected_subset_envelope
            RightEnd.envelope_subset)
    have hleft_card :
        ∀ i : Fin ell, (left i).card = strongifiedWidth w := by
      intro i
      dsimp [left]
      split_ifs with h0
      · exact LeftEnd.selected_card
      · exact (Gap _ _).target_card
    have hright_card :
        ∀ i : Fin ell, (right i).card = strongifiedWidth w := by
      intro i
      dsimp [right]
      split_ifs with hi
      · exact (Gap i hi).source_card
      · exact RightEnd.selected_card
    have hleft_node :
        ∀ i : Fin ell, NodeWellLinkedIn G (P0.cluster i) (left i) := by
      intro i
      dsimp [left]
      split_ifs with h0
      · have hi : i = first := Fin.ext h0
        simpa [hi] using NodeWellLinkedIn.mono_terminals
          LeftEnd.envelope_nodeWellLinked LeftEnd.selected_subset_envelope
      · let j : Fin ell := ⟨i.1 - 1, by omega⟩
        let hj : j.1 + 1 < ell := by dsimp [j]; omega
        have hnext : (⟨j.1 + 1, hj⟩ : Fin ell) = i := by
          apply Fin.ext
          dsimp [j]
          omega
        simpa [hnext] using (Gap j hj).target_nodeWellLinked
    have hright_node :
        ∀ i : Fin ell, NodeWellLinkedIn G (P0.cluster i) (right i) := by
      intro i
      dsimp [right]
      split_ifs with hi
      · exact (Gap i hi).source_nodeWellLinked
      · have hilast : i = last := by
          apply Fin.ext
          dsimp [last]
          omega
        simpa [hilast] using NodeWellLinkedIn.mono_terminals
          RightEnd.envelope_nodeWellLinked RightEnd.selected_subset_envelope
    have hleftEnvelope_subset :
        ∀ i : Fin ell, leftEnvelope i ⊆ P0.left i := by
      intro i
      dsimp [leftEnvelope]
      split_ifs with h0
      · have hi : i = first := Fin.ext h0
        simpa [hi] using LeftEnd.envelope_subset
      · let j : Fin ell := ⟨i.1 - 1, by omega⟩
        let hj : j.1 + 1 < ell := by dsimp [j]; omega
        have hnext : (⟨j.1 + 1, hj⟩ : Fin ell) = i := by
          apply Fin.ext
          dsimp [j]
          omega
        simpa only [hnext] using (Gap j hj).targetEnvelope_subset
    have hrightEnvelope_subset :
        ∀ i : Fin ell, rightEnvelope i ⊆ P0.right i := by
      intro i
      dsimp [rightEnvelope]
      split_ifs with hi
      · exact (Gap i hi).sourceEnvelope_subset
      · have hilast : i = last := by
          apply Fin.ext
          dsimp [last]
          omega
        simpa [hilast] using RightEnd.envelope_subset
    have hleft_subset_envelope :
        ∀ i : Fin ell, left i ⊆ leftEnvelope i := by
      intro i
      dsimp [left, leftEnvelope]
      split_ifs with h0
      · exact LeftEnd.selected_subset_envelope
      · exact (Gap _ _).target_subset_envelope
    have hright_subset_envelope :
        ∀ i : Fin ell, right i ⊆ rightEnvelope i := by
      intro i
      dsimp [right, rightEnvelope]
      split_ifs with hi
      · exact (Gap i hi).source_subset_envelope
      · exact RightEnd.selected_subset_envelope
    have hleftEnvelope_large :
        ∀ i : Fin ell,
          8 * strongifiedWidth w ≤ (leftEnvelope i).card := by
      intro i
      dsimp [leftEnvelope]
      split_ifs
      · exact LeftEnd.envelope_large
      · exact (Gap _ _).targetEnvelope_large
    have hrightEnvelope_large :
        ∀ i : Fin ell,
          8 * strongifiedWidth w ≤ (rightEnvelope i).card := by
      intro i
      dsimp [rightEnvelope]
      split_ifs with hi
      · exact (Gap i hi).sourceEnvelope_large
      · exact RightEnd.envelope_large
    have hleftEnvelope_node :
        ∀ i : Fin ell,
          NodeWellLinkedIn G (P0.cluster i) (leftEnvelope i) := by
      intro i
      dsimp [leftEnvelope]
      split_ifs with h0
      · have hi : i = first := Fin.ext h0
        simpa [hi] using LeftEnd.envelope_nodeWellLinked
      · let j : Fin ell := ⟨i.1 - 1, by omega⟩
        let hj : j.1 + 1 < ell := by dsimp [j]; omega
        have hnext : (⟨j.1 + 1, hj⟩ : Fin ell) = i := by
          apply Fin.ext
          dsimp [j]
          omega
        simpa [hnext] using (Gap j hj).targetEnvelope_nodeWellLinked
    have hrightEnvelope_node :
        ∀ i : Fin ell,
          NodeWellLinkedIn G (P0.cluster i) (rightEnvelope i) := by
      intro i
      dsimp [rightEnvelope]
      split_ifs with hi
      · exact (Gap i hi).sourceEnvelope_nodeWellLinked
      · have hilast : i = last := by
          apply Fin.ext
          dsimp [last]
          omega
        simpa [hilast] using RightEnd.envelope_nodeWellLinked
    refine
      { width_pos := strongifiedWidth_pos P0.width_pos
        left := left
        right := right
        left_subset_left := hleft_subset
        right_subset_right := hright_subset
        left_card := hleft_card
        right_card := hright_card
        connectorIndexSet := fun i hi => (Gap i hi).indexSet
        connectorIndexSet_card := fun i hi => (Gap i hi).card_indexSet
        sourceSet_eq_right := ?_
        targetSet_eq_left_next := ?_
        left_nodeWellLinked := hleft_node
        right_nodeWellLinked := hright_node
        left_right_nodeLinked := ?_ }
    · intro i hi
      change (P0.connector i hi).sourceSet (Gap i hi).indexSet = right i
      simp [right, hi]
    · intro i hi
      change (P0.connector i hi).targetSet (Gap i hi).indexSet =
        left ⟨i.1 + 1, hi⟩
      dsimp [left]
    · intro i
      apply Section46.theorem421_linkedSubsets_edgeWellLinked
        (G := G) (C := P0.cluster i)
        (T1 := leftEnvelope i) (T2 := rightEnvelope i)
        (T1' := left i) (T2' := right i)
        (κ := 8 * strongifiedWidth w)
        hdegree (by norm_num)
        ((P0.left_right_disjoint i).mono
          (hleftEnvelope_subset i) (hrightEnvelope_subset i))
        (hleftEnvelope_large i) (hrightEnvelope_large i)
        (EdgeWellLinkedIn.mono_terminals (P.nails_edgeWellLinked i)
          (Finset.union_subset_union
            (hleftEnvelope_subset i) (hrightEnvelope_subset i)))
        (hleftEnvelope_node i) (hrightEnvelope_node i)
        (hleft_subset_envelope i) (hright_subset_envelope i)
        (by rw [hleft_card i, hright_card i])
        (by rw [hleft_card i])

theorem strongification_width_bound
    {ell w : ℕ} (P : WeakPathOfSetsSystem G ell w) :
    w ≤ 20000 * strongifiedWidth w :=
  le_twentyThousand_mul_strongifiedWidth P.toPathOfSetsSystem.width_pos

end Section4Assembly

end SimpleGraph

end Lax17Proofs
