import Lax17Proofs.Source.ReedTreeDecompositionGlue
import Lax17Proofs.Source.ReedTreeDecompositionConvert
import Lax17Proofs.Source.ReedSeparatorArithmetic

namespace Lax17Proofs

universe u v w

/-!
# Recursive Reed tree decomposition

This file turns a balanced-separator oracle into a bounded-width tree
decomposition.  At every non-base recursive call the current root set is
extended to exactly `8 * k` terminals before the oracle is invoked.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace ReedTreeDecomposition

/-- An oracle producing an order-at-most-`k` balanced separation whenever its
terminal set has cardinality in the range required by Reed's recursion. -/
def SeparatorOracle (G : _root_.SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C R : Finset V), R ⊆ C → 4 * k < R.card → R.card ≤ 8 * k →
    ∃ Y Z : Finset V,
      BalancedSeparation G C R R.card Y Z ∧ (Y ∩ Z).card ≤ k

namespace RegionDecomposition

variable {G : _root_.SimpleGraph V} {k : ℕ}

/-- A separator oracle gives a region decomposition whose root contains the
prescribed set and whose bags all have cardinality at most `9 * k`. -/
theorem exists_bounded_of_separatorOracle
    (hOracle : SeparatorOracle G k) (hk : 0 < k) (C R : Finset V)
    (hRC : R ⊆ C) (hRcard : R.card ≤ 8 * k) :
    ∃ D : RegionDecomposition G C,
      R ⊆ D.bag D.root ∧ ∀ i, (D.bag i).card ≤ 9 * k := by
  classical
  induction hn : C.card using Nat.strong_induction_on generalizing C R with
  | h n ih =>
      subst hn
      by_cases hsmall : C.card ≤ 9 * k
      · refine ⟨oneBag G C, ?_, ?_⟩
        · simpa [oneBag] using hRC
        · intro i
          simpa [oneBag] using hsmall
      · have hCcard : 8 * k ≤ C.card := by omega
        have hmissing : 8 * k - R.card ≤ (C \ R).card := by
          rw [Finset.card_sdiff_of_subset hRC]
          omega
        obtain ⟨S, hSsub, hScard⟩ :=
          Finset.exists_subset_card_eq hmissing
        have hRS : Disjoint R S := by
          rw [Finset.disjoint_left]
          intro v hvR hvS
          exact (Finset.mem_sdiff.mp (hSsub hvS)).2 hvR
        let T : Finset V := R ∪ S
        have hRT : R ⊆ T := Finset.subset_union_left
        have hTC : T ⊆ C := by
          apply Finset.union_subset hRC
          exact hSsub.trans Finset.sdiff_subset
        have hTcard : T.card = 8 * k := by
          dsimp [T]
          rw [Finset.card_union_of_disjoint hRS, hScard]
          omega
        have hTlarge : 4 * k < T.card := by omega
        have hTupper : T.card ≤ 8 * k := by omega
        obtain ⟨Y, Z, hYZ, hoverlap⟩ :=
          hOracle C T hTC hTlarge hTupper
        let O : Finset V := Y ∩ Z
        let K : Finset V := T ∪ O
        have hstep :=
          ReedSeparatorArithmetic.recursive_step_cardinality_bounds
            (G := G) (C := C) (T := T) (Y := Y) (Z := Z) (k := k)
            hTC hTlarge hTupper hYZ hoverlap
        have hKY : K ∩ Y = O ∪ (Y ∩ T) := by
          ext v
          simp only [K, O, Finset.mem_inter, Finset.mem_union]
          aesop
        have hKZ : K ∩ Z = O ∪ (Z ∩ T) := by
          ext v
          simp only [K, O, Finset.mem_inter, Finset.mem_union]
          aesop
        have hKYcard : (K ∩ Y).card ≤ 8 * k := by
          rw [hKY]
          exact hstep.2.2.1
        have hKZcard : (K ∩ Z).card ≤ 8 * k := by
          rw [hKZ]
          exact hstep.2.2.2
        have hKYsub : K ∩ Y ⊆ Y := Finset.inter_subset_right
        have hKZsub : K ∩ Z ⊆ Z := Finset.inter_subset_right
        obtain ⟨DY, hrootY, hboundY⟩ :=
          ih _ hstep.1 Y (K ∩ Y) hKYsub hKYcard rfl
        obtain ⟨DZ, hrootZ, hboundZ⟩ :=
          ih _ hstep.2.1 Z (K ∩ Z) hKZsub hKZcard rfl
        have hOsubK : Y ∩ Z ⊆ K := by
          intro v hv
          exact Finset.mem_union_right T hv
        have hKsubC : K ⊆ C := by
          apply Finset.union_subset hTC
          exact Finset.inter_subset_left.trans hYZ.toVertexSeparation.left_subset
        have hKcard : K.card ≤ 9 * k := by
          change (T ∪ O).card ≤ 9 * k
          calc
            (T ∪ O).card ≤ T.card + O.card := Finset.card_union_le T O
            _ ≤ 9 * k := by
              dsimp [O]
              omega
        obtain ⟨D, hDroot, hDbound⟩ :=
          glue DY DZ hYZ.toVertexSeparation hOsubK hKsubC
            hrootY hrootZ hboundY hboundZ
        refine ⟨D, ?_, ?_⟩
        · rw [hDroot]
          exact hRT.trans Finset.subset_union_left
        · intro i
          exact (hDbound i).trans (by simp [hKcard])

end RegionDecomposition

/-- A positive-parameter separator oracle bounds the treewidth of the full
graph by `9 * k`. -/
theorem hasTreewidthAtMost_of_separatorOracle
    (G : _root_.SimpleGraph V) (k : ℕ) (hk : 0 < k)
    (hOracle : SeparatorOracle G k) :
    HasTreewidthAtMost G (9 * k) := by
  classical
  by_cases hsmall : (Finset.univ : Finset V).card ≤ 9 * k
  · let D := RegionDecomposition.oneBag G (Finset.univ : Finset V)
    refine ⟨D.toTreeDecomposition, ?_⟩
    exact (RegionDecomposition.toTreeDecomposition_width_le D (9 * k)
      (by intro i; simpa [D, RegionDecomposition.oneBag] using hsmall)).trans
      (Nat.sub_le _ _)
  · have htarget : 8 * k ≤ (Finset.univ : Finset V).card := by omega
    obtain ⟨R, hRuniv, hRcard⟩ :=
      Finset.exists_subset_card_eq htarget
    obtain ⟨D, _hroot, hbag⟩ :=
      RegionDecomposition.exists_bounded_of_separatorOracle
        hOracle hk (Finset.univ : Finset V) R hRuniv (by omega)
    refine ⟨D.toTreeDecomposition, ?_⟩
    exact (RegionDecomposition.toTreeDecomposition_width_le D (9 * k) hbag).trans
      (Nat.sub_le _ _)

end ReedTreeDecomposition

end SimpleGraph

end Lax17Proofs
