import Lax17Proofs.Source.HairyPathOfSets
import Lax17Proofs.Source.CrossbarTheorem
import Lax17Proofs.Source.HairyCrossbarGrid

namespace Lax17Proofs

universe u v w

/-!
# Crossbar dichotomy inside a hairy path-of-sets cluster

This file proves the local application of the Chuzhoy--Tan crossbar dichotomy
to one cluster of a hairy Path-of-Sets System.  The hairy-system API supplies
the two required path packings: one from left nails to right nails and one from
left nails to the hair endpoints.
-/

namespace SimpleGraph
namespace HairyPathOfSetsSystem


/-- The crossbar dichotomy as an explicit input rather than as a contract
axiom.  Parameterized composition theorems use this interface to keep their
proof terms independent of `CrossbarContract.crossbar_or_strong_pathOfSets_minor`. -/
def CrossbarDichotomyInput (c : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {g kappa : ℕ}
    {A B X : Finset V},
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          A.card = kappa →
            B.card = kappa →
              X.card = kappa →
                Disjoint A B →
                  Disjoint A X →
                    Disjoint B X →
                      2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ kappa →
                        (∀ x ∈ X, DegreeEquals H x 1) →
                          (Pab : PathPacking H A B) →
                            Pab.card = kappa →
                              (Pax : PathPacking H A X) →
                                Pax.card = kappa →
                                  Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                    ∃ ell' w' : ℕ,
                                      g ^ 2 ≤ c * ell' ∧
                                        g ^ 2 ≤ c * w' ∧
                                          CrossbarContract.HasStrongPathOfSetsMinor
                                            H ell' w'

/-- Section 4 weaker crossbar dichotomy input.  It has the same conclusion as
`CrossbarDichotomyInput`, but assumes the larger `g^10 log g` terminal-set
threshold. -/
def CrossbarDichotomyInput10 (c : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {g kappa : ℕ}
    {A B X : Finset V},
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          A.card = kappa →
            B.card = kappa →
              X.card = kappa →
                Disjoint A B →
                  Disjoint A X →
                    Disjoint B X →
                      2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa →
                        (∀ x ∈ X, DegreeEquals H x 1) →
                          (Pab : PathPacking H A B) →
                            Pab.card = kappa →
                              (Pax : PathPacking H A X) →
                                Pax.card = kappa →
                                  Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                    ∃ ell' w' : ℕ,
                                      g ^ 2 ≤ c * ell' ∧
                                        g ^ 2 ≤ c * w' ∧
                                          CrossbarContract.HasStrongPathOfSetsMinor
                                            H ell' w'

/-- A stronger `g^9 log g` crossbar input supplies the Section 4
`g^10 log g` input. -/
theorem crossbarDichotomyInput10_of_crossbarDichotomyInput
    {c : ℕ} (hinput : CrossbarDichotomyInput.{u} c) :
    CrossbarDichotomyInput10.{u} c := by
  intro V _ _ H g kappa A B X hg hpow hA hB hX hAB hAX hBX hlarge10
    hdeg Pab hPab Pax hPax
  exact hinput H hg hpow hA hB hX hAB hAX hBX
    (le_trans (CrossbarTheorem.crossbar_threshold_degree9_le_degree10 hg)
      hlarge10)
    hdeg Pab hPab Pax hPax


/-- Section 4 supplies the `g^10 log g` input once the pseudo-grid branch
(Sections 4.2--4.6) is available, without appealing to the stronger
Theorem 3.1 crossbar contract. -/
theorem exists_crossbarDichotomyInput10_of_section4PseudoGridBranchInput
    {c : ℕ} (hc : 0 < c)
    (hbranch : CrossbarTheorem.Section4PseudoGridBranchInput10.{u} c) :
    ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c :=
  CrossbarTheorem.crossbar_or_strong_pathOfSets_minor_degree10_of_section4PseudoGridBranchInput
    hc hbranch

/-- Section 4 supplies the `g^10 log g` input from the formal Theorem 4.1
proof, the Section 4.5 weak path-of-sets assembly data, and Section 4.6
strongification data. -/
theorem exists_crossbarDichotomyInput10_of_section4WeakToStrongAssemblyInput
    {c : ℕ} (hc : 0 < c)
    (hbranch :
      CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} c) :
    ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c :=
  exists_crossbarDichotomyInput10_of_section4PseudoGridBranchInput hc
    (CrossbarTheorem.section4PseudoGridBranchInput10_of_weakToStrongAssemblyInput10
      hbranch)

/-- Input form of the local crossbar dichotomy in a hair-local graph. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph_of_crossbarDichotomy
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          (Hsys.hairLocalGraph i) ell' w' := by
  rcases hinput with ⟨c, hc, hcrossbar⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPab_card, _hPab_stays⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPax_card⟩
  have hleft_card : (Hsys.base.left i).card = w := Hsys.base.left_card i
  have hright_card : (Hsys.base.right i).card = w := Hsys.base.right_card i
  have hy_card : (Hsys.y i).card = w := Hsys.y_card i
  have hleft_y_disjoint : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvleft hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.left_subset_cluster i hvleft)
  have hright_y_disjoint : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvright hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.right_subset_cluster i hvright)
  exact hcrossbar (Hsys.hairLocalGraph i) hg hpow hleft_card hright_card
    hy_card (Hsys.base.left_right_disjoint i) hleft_y_disjoint hright_y_disjoint
    hlarge (fun x hx => Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPab_card Pax.toPathPacking (by simpa using hPax_card)

/-- Section 4 input form of the local crossbar dichotomy in a hair-local
graph, using the weaker `g^10 log g` terminal threshold. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph_of_crossbarDichotomy10
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          (Hsys.hairLocalGraph i) ell' w' := by
  rcases hinput with ⟨c, hc, hcrossbar⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPab_card, _hPab_stays⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPax_card⟩
  have hleft_card : (Hsys.base.left i).card = w := Hsys.base.left_card i
  have hright_card : (Hsys.base.right i).card = w := Hsys.base.right_card i
  have hy_card : (Hsys.y i).card = w := Hsys.y_card i
  have hleft_y_disjoint : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvleft hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.left_subset_cluster i hvleft)
  have hright_y_disjoint : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvright hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.right_subset_cluster i hvright)
  exact hcrossbar (Hsys.hairLocalGraph i) hg hpow hleft_card hright_card
    hy_card (Hsys.base.left_right_disjoint i) hleft_y_disjoint hright_y_disjoint
    hlarge (fun x hx => Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPab_card Pax.toPathPacking (by simpa using hPax_card)



/-- Input form of the ambient hair-cluster crossbar dichotomy. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairyCluster_of_crossbarDichotomy
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph_of_crossbarDichotomy
      hinput with
    ⟨c, hc, hlocal⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases hlocal Hsys i hg hpow hlarge with hcrossbar | hstrong
  · exact Or.inl hcrossbar
  · rcases hstrong with ⟨ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw,
      hminor.mono (Hsys.hairLocalGraph_le i)⟩

/-- Section 4 input form of the ambient hair-cluster crossbar dichotomy. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairyCluster_of_crossbarDichotomy10
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph_of_crossbarDichotomy10
      hinput with
    ⟨c, hc, hlocal⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases hlocal Hsys i hg hpow hlarge with hcrossbar | hstrong
  · exact Or.inl hcrossbar
  · rcases hstrong with ⟨ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw,
      hminor.mono (Hsys.hairLocalGraph_le i)⟩


/-- Section 4 input form of the odd-cluster crossbar dichotomy. -/
theorem local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy10
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                (∀ i : Fin ell,
                  Lax17Proofs.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i →
                  Nonempty (Crossbar (Hsys.hairLocalGraph i)
                    (Hsys.base.left i) (Hsys.base.right i)
                    (Hsys.y i) (g ^ 2))) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairyCluster_of_crossbarDichotomy10
      hinput with
    ⟨c, hc, hcluster⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hlarge
  by_cases hstrong :
      ∃ i : Fin ell,
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i ∧
        ∃ ell' w' : ℕ,
          g ^ 2 ≤ c * ell' ∧
            g ^ 2 ≤ c * w' ∧
              CrossbarContract.HasStrongPathOfSetsMinor G ell' w'
  · rcases hstrong with ⟨_i, _hi, ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw, hminor⟩
  · refine Or.inl ?_
    intro i hi
    rcases hcluster Hsys i hg hpow hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hstrong ⟨i, hi, hminor⟩)

/-- Input form of the odd-cluster crossbar dichotomy. -/
theorem local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                (∀ i : Fin ell,
                  Lax17Proofs.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i →
                  Nonempty (Crossbar (Hsys.hairLocalGraph i)
                    (Hsys.base.left i) (Hsys.base.right i)
                    (Hsys.y i) (g ^ 2))) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairyCluster_of_crossbarDichotomy
      hinput with
    ⟨c, hc, hcluster⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hlarge
  by_cases hstrong :
      ∃ i : Fin ell,
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i ∧
        ∃ ell' w' : ℕ,
          g ^ 2 ≤ c * ell' ∧
            g ^ 2 ≤ c * w' ∧
              CrossbarContract.HasStrongPathOfSetsMinor G ell' w'
  · rcases hstrong with ⟨_i, _hi, ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw, hminor⟩
  · refine Or.inl ?_
    intro i hi
    rcases hcluster Hsys i hg hpow hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hstrong ⟨i, hi, hminor⟩)




/-- Input form of
`gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider`,
with the crossbar dichotomy supplied as an explicit hypothesis. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_crossbarDichotomy_and_largeCaseCutMatchingDataProvider
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy
      hinput with
    ⟨cCross, hcCross, hodd⟩
  rcases
    HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingDataProvider
      hlargeData with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars)
  · exact Or.inr hstrong

/-- Section 4 input form of the hairy-system dichotomy, with the weak
`g^10 log g` crossbar threshold and the same large-case grid assembly. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_crossbarDichotomy10_and_largeCaseCutMatchingDataProvider
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy10
      hinput with
    ⟨cCross, hcCross, hodd⟩
  rcases
    HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingDataProvider
      hlargeData with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars)
  · exact Or.inr hstrong






/-- Cancel the crossbar constant from a scaled square lower bound. -/
theorem square_le_of_scaled_square_le {c g r n : ℕ}
    (hc : 0 < c) (hscaled : c * r ^ 2 ≤ g ^ 2)
    (hn : g ^ 2 ≤ c * n) :
    r ^ 2 ≤ n :=
  Nat.le_of_mul_le_mul_left (le_trans hscaled hn) hc



/-- Input form of the scaled strong-parameter dichotomy: both the crossbar
dichotomy and the strong-path-of-sets-minor-to-grid theorem are explicit
hypotheses, so this composition theorem has no project-contract dependency. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
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
  rcases
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_crossbarDichotomy_and_largeCaseCutMatchingDataProvider
      hcrossInput hlargeData with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases hstrongGrid with ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le hcCross hscaled hell')
      (square_le_of_scaled_square_le hcCross hscaled hw')
      hminor)

/-- Section 4 input form of the scaled strong-parameter dichotomy.  The
crossbar input is the weaker `g^10 log g` theorem, while the direct grid branch
and strong-minor branch use the same downstream providers. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs10
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
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
  rcases
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_crossbarDichotomy10_and_largeCaseCutMatchingDataProvider
      hcrossInput hlargeData with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases hstrongGrid with ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le hcCross hscaled hell')
      (square_le_of_scaled_square_le hcCross hscaled hw')
      hminor)




/-- Input form of the supergraph scaled-strong-parameter theorem. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
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
  rcases
    gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs
      hcrossInput hstrongGrid hlargeData with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain H Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled with
    hgrid | hgrid
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hgrid with ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Section 4 input form of the supergraph scaled-strong-parameter theorem,
using the weak `g^10 log g` crossbar threshold. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs10
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
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
  rcases
    gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs10
      hcrossInput hstrongGrid hlargeData with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain H Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled with
    hgrid | hgrid
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hgrid with ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩



end HairyPathOfSetsSystem
end SimpleGraph

end Lax17Proofs
