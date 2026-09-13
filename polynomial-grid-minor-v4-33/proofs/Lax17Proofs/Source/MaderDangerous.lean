import Lax17Proofs.Source.MaderBridge
import Lax17Proofs.Source.MaderConnectivity
import Lax17Proofs.Source.MaderCutIdentities

namespace Lax17Proofs

universe u v w

/-!
# Dangerous cuts for Mader splitting

This file proves the dangerous-set characterization of non-admissible split
pairs.  All connectivity statements remain in the cut-threshold language used
by `MaderAdmissible`; no path version of edge Menger is assumed.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A nonempty proper center-avoiding cut whose boundary exceeds its maximum
local-connectivity requirement by at most one. -/
def MaderDangerous (H : FiniteEdgeIndexedGraph W) (s : W)
    (X : Finset W) : Prop :=
  X.Nonempty ∧ X ⊂ Finset.univ.erase s ∧
    (H.boundary X).card ≤ H.centerAvoidingRequirement s X + 1

/-- A nonempty center-avoiding cut with zero surplus. -/
def MaderTight (H : FiniteEdgeIndexedGraph W) (s : W)
    (X : Finset W) : Prop :=
  X.Nonempty ∧ X ⊆ Finset.univ.erase s ∧
    (H.boundary X).card = H.centerAvoidingRequirement s X

theorem MaderDangerous.nonempty {H : FiniteEdgeIndexedGraph W} {s : W}
    {X : Finset W} (h : H.MaderDangerous s X) : X.Nonempty := h.1

theorem MaderDangerous.ssubset_ground
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (h : H.MaderDangerous s X) : X ⊂ Finset.univ.erase s := h.2.1

theorem MaderDangerous.subset_ground
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (h : H.MaderDangerous s X) : X ⊆ Finset.univ.erase s := h.2.1.subset

theorem MaderDangerous.center_not_mem
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (h : H.MaderDangerous s X) : s ∉ X := by
  intro hs
  exact (Finset.mem_erase.mp (h.subset_ground hs)).1 rfl

theorem MaderDangerous.boundary_le
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (h : H.MaderDangerous s X) :
    (H.boundary X).card ≤ H.centerAvoidingRequirement s X + 1 := h.2.2

theorem MaderTight.dangerous_of_ssubset
    {H : FiniteEdgeIndexedGraph W} {s : W} {X : Finset W}
    (h : H.MaderTight s X) (hproper : X ⊂ Finset.univ.erase s) :
    H.MaderDangerous s X := by
  refine ⟨h.1, hproper, ?_⟩
  rw [h.2.2]
  omega

/-- Splitting never increases a center-avoiding cut cardinality. -/
theorem maderSplit_boundary_card_le
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) (hs : s ∉ X) :
    ((H.maderSplit p).boundary X).card ≤ (H.boundary X).card := by
  have h := boundary_card_maderSplit_add_two_iff H p X hs
  omega

/-- Every post-split threshold also held before the split. -/
theorem PairwiseEdgeConnectedAtLeast.of_maderSplit
    {H : FiniteEdgeIndexedGraph W} {s x y : W} (p : H.MaderSplitPair s)
    (hxs : x ≠ s) (hys : y ≠ s) {k : Nat}
    (h : (H.maderSplit p).PairwiseEdgeConnectedAtLeast x y k) :
    H.PairwiseEdgeConnectedAtLeast x y k := by
  intro X hx hy
  by_cases hs : s ∈ X
  · have hyc : y ∈ Xᶜ := by simpa using hy
    have hxc : x ∉ Xᶜ := by simpa using hx
    have hscompl : s ∉ Xᶜ := by simp [hs]
    have hcomm : (H.maderSplit p).PairwiseEdgeConnectedAtLeast y x k :=
      ((H.maderSplit p).pairwiseEdgeConnectedAtLeast_comm x y k).mp h
    have hpost := hcomm Xᶜ hyc hxc
    have hle := H.maderSplit_boundary_card_le p Xᶜ hscompl
    simpa using hpost.trans hle
  · exact (h X hx hy).trans (H.maderSplit_boundary_card_le p X hs)

/-- In the absence of a dangerous set covering both other endpoints, a split
preserves every local edge-connectivity away from the center. -/
theorem maderAdmissible_of_no_dangerous
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (hno : ∀ X : Finset W, H.MaderDangerous s X →
      ¬ (p.firstOther ∈ X ∧ p.secondOther ∈ X)) :
    H.MaderAdmissible p := by
  intro x y hxs hys hxy k
  constructor
  · intro hpre X hx hy
    by_cases hs : s ∈ X
    · have hyc : y ∈ Xᶜ := by simpa using hy
      have hxc : x ∉ Xᶜ := by simpa using hx
      have hscompl : s ∉ Xᶜ := by simp [hs]
      have hcut : k ≤ ((H.maderSplit p).boundary Xᶜ).card := by
        by_cases hboth : p.firstOther ∈ Xᶜ ∧ p.secondOther ∈ Xᶜ
        · have hnonempty : (Xᶜ : Finset W).Nonempty := ⟨y, hyc⟩
          have hproper : Xᶜ ⊂ Finset.univ.erase s := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · intro z hz
              exact Finset.mem_erase.mpr ⟨by
                intro hzs
                subst z
                exact hscompl hz, Finset.mem_univ _⟩
            · intro heq
              have hxground : x ∈ Finset.univ.erase s := by simp [hxs]
              have : x ∈ Xᶜ := heq ▸ hxground
              exact hxc this
          have hconn : k ≤ H.localEdgeConnectivity y x := by
            rw [H.localEdgeConnectivity_comm y x]
            exact (H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
              hxy k).mp hpre
          have hreq : k ≤ H.centerAvoidingRequirement s Xᶜ :=
            hconn.trans (H.localEdgeConnectivity_le_centerAvoidingRequirement
              hyc hxc hxs)
          have hnDanger : ¬ H.MaderDangerous s Xᶜ := fun hd => hno Xᶜ hd hboth
          have hlarge : H.centerAvoidingRequirement s Xᶜ + 2 ≤
              (H.boundary Xᶜ).card := by
            have hreqCut := H.centerAvoidingRequirement_le_boundary s Xᶜ
            simp only [MaderDangerous, hnonempty, hproper, true_and] at hnDanger
            omega
          rw [H.maderSplit_boundary_card_of_both_mem p Xᶜ hscompl hboth.1 hboth.2]
          omega
        · rw [H.maderSplit_boundary_card_of_not_both_mem p Xᶜ hscompl hboth]
          exact (H.pairwiseEdgeConnectedAtLeast_comm x y k).mp hpre Xᶜ hyc hxc
      simpa using hcut
    · by_cases hboth : p.firstOther ∈ X ∧ p.secondOther ∈ X
      · have hnonempty : X.Nonempty := ⟨x, hx⟩
        have hproper : X ⊂ Finset.univ.erase s := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro z hz
            exact Finset.mem_erase.mpr ⟨by
              intro hzs
              subst z
              exact hs hz, Finset.mem_univ _⟩
          · intro heq
            have hyground : y ∈ Finset.univ.erase s := by simp [hys]
            exact hy (heq ▸ hyground)
        have hreq : k ≤ H.centerAvoidingRequirement s X :=
          ((H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity hxy k).mp hpre).trans
            (H.localEdgeConnectivity_le_centerAvoidingRequirement hx hy hys)
        have hnDanger : ¬ H.MaderDangerous s X := fun hd => hno X hd hboth
        have hlarge : H.centerAvoidingRequirement s X + 2 ≤
            (H.boundary X).card := by
          have hreqCut := H.centerAvoidingRequirement_le_boundary s X
          simp only [MaderDangerous, hnonempty, hproper, true_and] at hnDanger
          omega
        rw [H.maderSplit_boundary_card_of_both_mem p X hs hboth.1 hboth.2]
        omega
      · rw [H.maderSplit_boundary_card_of_not_both_mem p X hs hboth]
        exact hpre X hx hy
  · exact fun hpost => hpost.of_maderSplit p hxs hys

/-- A dangerous set containing both other endpoints witnesses failure of
admissibility. -/
theorem not_maderAdmissible_of_exists_dangerous
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (hbad : ∃ X : Finset W, H.MaderDangerous s X ∧
      p.firstOther ∈ X ∧ p.secondOther ∈ X) :
    ¬ H.MaderAdmissible p := by
  rcases hbad with ⟨X, hX, hfirst, hsecond⟩
  rcases H.exists_centerAvoidingRequirement_pair hX.nonempty hX.ssubset_ground with
    ⟨x, hx, y, hy, hys, hconn⟩
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  intro hadm
  let k := H.centerAvoidingRequirement s X
  have hpre : H.PairwiseEdgeConnectedAtLeast x y k :=
    (H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity hxy k).2
      (by simp [k, hconn])
  have hpost := (hadm x y
    (fun h => hX.center_not_mem (h ▸ hx)) hys hxy k).1 hpre
  have hcut := hpost X hx hy
  have hcard := H.boundary_card_maderSplit_add_two_iff p X hX.center_not_mem
  simp [hfirst, hsecond] at hcard
  have hbound := hX.boundary_le
  dsimp [k] at hcut
  exact (by omega)

/-- Exact dangerous-set criterion for a named split pair. -/
theorem not_maderAdmissible_iff_exists_dangerous
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s) :
    ¬ H.MaderAdmissible p ↔
      ∃ X : Finset W, H.MaderDangerous s X ∧
        p.firstOther ∈ X ∧ p.secondOther ∈ X := by
  constructor
  · intro hnot
    by_contra hnone
    push_neg at hnone
    exact hnot (H.maderAdmissible_of_no_dangerous p (fun X hX hboth =>
      hnone X hX hboth.1 hboth.2))
  · exact H.not_maderAdmissible_of_exists_dangerous p

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
