import Lax17Proofs.Source.ChekuriChuzhoySection5AuxiliaryTree

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5.4.1 Phase 1 support graph

This file formalizes the deterministic support-graph step in
Chekuri--Chuzhoy preprint Section 5.4.1. Given an `h`-edge-connected named
multigraph on `n` terminals, the simple support retains the distinct endpoint
pairs carrying at least `h / n^2` parallel copies.

Every nontrivial cut has at most `n^2` endpoint pairs. If no retained pair
crossed such a cut, all its bundles would be light and their total capacity
would be strictly less than `h`, contradicting edge connectivity. Thus the
support is connected and has a spanning tree.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Phase1Support

open Finset
open ChekuriChuzhoySection5AuxiliaryTree
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {n h : Nat}

/-- The Phase 1 threshold `h / n^2`, interpreted in `Rat`. -/
def phase1Threshold (n h : Nat) : Rat :=
  (h : Rat) / (n : Rat) ^ 2

theorem phase1Threshold_pos (hn : 0 < n) (hh : 0 < h) :
    0 < phase1Threshold n h := by
  unfold phase1Threshold
  positivity

theorem phase1Threshold_nonnegative (n h : Nat) :
    0 ≤ phase1Threshold n h := by
  unfold phase1Threshold
  positivity

/-- The deterministic simple support used in Phase 1. Two terminals are
adjacent exactly when they are distinct and their parallel bundle has
capacity at least `h / n^2`. -/
noncomputable def phase1Support
    (H : FiniteEdgeIndexedGraph (Fin n)) (h : Nat) :
    _root_.SimpleGraph (Fin n) where
  Adj i j :=
    i ≠ j ∧ phase1Threshold n h ≤ H.bundleCapacity s(i, j)
  symm := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    simpa [FiniteEdgeIndexedGraph.bundleCapacity, Sym2.eq_swap] using hij.2
  loopless := ⟨by
    intro i hii
    exact hii.1 rfl⟩

@[simp] theorem phase1Support_adj
    (H : FiniteEdgeIndexedGraph (Fin n)) (h : Nat) (i j : Fin n) :
    (phase1Support H h).Adj i j ↔
      i ≠ j ∧ phase1Threshold n h ≤ H.bundleCapacity s(i, j) :=
  Iff.rfl

private theorem cast_sq_mul_phase1Threshold (hn : 0 < n) :
    (((n ^ 2 : Nat) : Rat) * phase1Threshold n h) = (h : Rat) := by
  unfold phase1Threshold
  norm_num [Nat.cast_pow]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

/-- The cut-counting core of Phase 1: every nonempty proper terminal cut has
a retained support edge crossing it. -/
theorem exists_phase1Support_adj_crossing
    (H : FiniteEdgeIndexedGraph (Fin n))
    (hn : 0 < n) (hh : 0 < h)
    (hconnected : H.IsEdgeConnected h)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSproper : S ≠ Finset.univ) :
    ∃ i ∈ S, ∃ j ∉ S, (phase1Support H h).Adj i j := by
  classical
  by_contra hcross
  push Not at hcross
  let A := allCutPairs S
  have htotal :
      (h : Rat) ≤ ∑ p ∈ A, H.bundleCapacity p := by
    rw [← H.copiesOver_card_eq_sum_bundleCapacity A]
    rw [show H.copiesOver A = H.boundary S by
      simpa [A] using copiesOver_allCutPairs H S]
    exact_mod_cast hconnected S hS hSproper
  have hA : A.Nonempty := by
    by_contra hA
    have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    rw [hAempty] at htotal
    simp only [Finset.sum_empty] at htotal
    have hhRat : (0 : Rat) < h := by
      exact_mod_cast hh
    exact (not_lt_of_ge htotal) hhRat
  have hlight :
      ∀ p ∈ A, H.bundleCapacity p < phase1Threshold n h := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨ij, hij, hp⟩
    have hi : ij.1 ∈ S := (Finset.mem_product.mp hij).1
    have hj : ij.2 ∉ S := by
      simpa using (Finset.mem_product.mp hij).2
    have hne : ij.1 ≠ ij.2 := by
      intro heq
      exact hj (heq ▸ hi)
    subst p
    apply lt_of_not_ge
    intro hlarge
    exact hcross ij.1 hi ij.2 hj
      ((phase1Support_adj H h ij.1 ij.2).2 ⟨hne, hlarge⟩)
  have hsumLight :
      (∑ p ∈ A, H.bundleCapacity p) <
        ∑ _p ∈ A, phase1Threshold n h :=
    Finset.sum_lt_sum_of_nonempty hA hlight
  have hcardRat :
      (A.card : Rat) ≤ ((n ^ 2 : Nat) : Rat) := by
    exact_mod_cast (by
      simpa [A] using allCutPairs_card_le_sq S)
  have hsum_lt_h :
      (∑ p ∈ A, H.bundleCapacity p) < (h : Rat) := by
    calc
      (∑ p ∈ A, H.bundleCapacity p) <
          ∑ _p ∈ A, phase1Threshold n h :=
        hsumLight
      _ = (A.card : Rat) * phase1Threshold n h := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n ^ 2 : Nat) : Rat) * phase1Threshold n h :=
        mul_le_mul_of_nonneg_right hcardRat
          (phase1Threshold_nonnegative n h)
      _ = (h : Rat) := cast_sq_mul_phase1Threshold (h := h) hn
  exact (not_lt_of_ge htotal) hsum_lt_h

/-- The Phase 1 support is preconnected, by applying the crossing theorem to
the set of vertices reachable from an arbitrary starting vertex. -/
theorem phase1Support_preconnected
    (H : FiniteEdgeIndexedGraph (Fin n))
    (hn : 0 < n) (hh : 0 < h)
    (hconnected : H.IsEdgeConnected h) :
    (phase1Support H h).Preconnected := by
  classical
  intro a b
  by_cases hab : (phase1Support H h).Reachable a b
  · exact hab
  · let S : Finset (Fin n) :=
      Finset.univ.filter fun z => (phase1Support H h).Reachable a z
    have haS : a ∈ S := by
      simp [S]
    have hbNotS : b ∉ S := by
      simpa [S] using hab
    have hSproper : S ≠ Finset.univ := by
      intro hSuniv
      apply hbNotS
      rw [hSuniv]
      simp
    rcases exists_phase1Support_adj_crossing
        H hn hh hconnected S ⟨a, haS⟩ hSproper with
      ⟨i, hiS, j, hjNotS, hij⟩
    have hai : (phase1Support H h).Reachable a i := by
      simpa [S] using hiS
    have haj : (phase1Support H h).Reachable a j :=
      hai.trans hij.reachable
    have hjS : j ∈ S := by
      simp [S, haj]
    exact (hjNotS hjS).elim

/-- The deterministic Phase 1 support graph is connected. -/
theorem phase1Support_connected
    (H : FiniteEdgeIndexedGraph (Fin n))
    (hn : 0 < n) (hh : 0 < h)
    (hconnected : H.IsEdgeConnected h) :
    (phase1Support H h).Connected where
  preconnected := phase1Support_preconnected H hn hh hconnected
  nonempty := Fin.pos_iff_nonempty.mp hn

/-- A same-vertex subgraph of the Phase 1 support that is a tree. Since the
vertex type is unchanged, this is a spanning tree of the support. -/
theorem exists_phase1Support_spanningTree
    (H : FiniteEdgeIndexedGraph (Fin n))
    (hn : 0 < n) (hh : 0 < h)
    (hconnected : H.IsEdgeConnected h) :
    ∃ T : _root_.SimpleGraph (Fin n),
      T ≤ phase1Support H h ∧ T.IsTree :=
  (phase1Support_connected H hn hh hconnected).exists_isTree_le

/-- The natural-number bundle bridge used after selecting a Phase 1 support
edge. The threshold loses exactly the factor `n^2`. -/
theorem width_le_edgeBundle_card_of_phase1Support_adj
    (H : FiniteEdgeIndexedGraph (Fin n))
    {i j : Fin n} {w : Nat}
    (hn : 0 < n) (hwidth : n ^ 2 * w ≤ h)
    (hij : (phase1Support H h).Adj i j) :
    w ≤ (H.edgeBundle s(i, j)).card := by
  have hden : (0 : Rat) < (n : Rat) ^ 2 := by
    positivity
  have hcapacityRat :
      (h : Rat) ≤ ((H.edgeBundle s(i, j)).card : Rat) * (n : Rat) ^ 2 := by
    exact (div_le_iff₀ hden).mp (by
      simpa [phase1Threshold, FiniteEdgeIndexedGraph.bundleCapacity] using
        (phase1Support_adj H h i j).mp hij |>.2)
  have hcapacity :
      h ≤ (H.edgeBundle s(i, j)).card * n ^ 2 := by
    exact_mod_cast hcapacityRat
  have hscaled :
      n ^ 2 * w ≤ n ^ 2 * (H.edgeBundle s(i, j)).card := by
    calc
      n ^ 2 * w ≤ h := hwidth
      _ ≤ (H.edgeBundle s(i, j)).card * n ^ 2 := hcapacity
      _ = n ^ 2 * (H.edgeBundle s(i, j)).card := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos hn)

/-- Source-facing combined Phase 1 output: a spanning tree whose every edge
has at least `w` named copies whenever `n^2 * w <= h`. -/
theorem exists_phase1Support_spanningTree_with_bundle_lower_bound
    (H : FiniteEdgeIndexedGraph (Fin n))
    {w : Nat}
    (hn : 0 < n) (hh : 0 < h)
    (hconnected : H.IsEdgeConnected h)
    (hwidth : n ^ 2 * w ≤ h) :
    ∃ T : _root_.SimpleGraph (Fin n),
      T ≤ phase1Support H h ∧
      T.IsTree ∧
      ∀ i j, T.Adj i j → w ≤ (H.edgeBundle s(i, j)).card := by
  rcases exists_phase1Support_spanningTree H hn hh hconnected with
    ⟨T, hTsupport, hTtree⟩
  refine ⟨T, hTsupport, hTtree, ?_⟩
  intro i j hij
  exact width_le_edgeBundle_card_of_phase1Support_adj
    H hn hwidth (hTsupport hij)

end ChekuriChuzhoySection5Phase1Support
end SimpleGraph

end Lax17Proofs
