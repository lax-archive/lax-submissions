import Lax17Proofs.Source.ChekuriChuzhoySection5SplitOff

namespace Lax17Proofs

universe u v w

/-!
# Finite local connectivity for Mader's theorem

This module turns the cut-threshold formulation used by the split-off
bookkeeping into an actual finite minimum-cut value.  It also defines the
center-avoiding cut requirement on `univ.erase s` and proves the uncrossing
properties used in the finite proof of Mader's admissible-pair theorem.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-! ## Finite local edge connectivity -/

/-- All vertex sets whose cut separates `x` from `y`, oriented with `x` on
the inside. -/
noncomputable def separatingCuts (x y : W) : Finset (Finset W) := by
  classical
  exact Finset.univ.filter fun X => x ∈ X ∧ y ∉ X

@[simp] theorem mem_separatingCuts {x y : W} {X : Finset W} :
    X ∈ separatingCuts x y ↔ x ∈ X ∧ y ∉ X := by
  classical
  simp [separatingCuts]

/-- Distinct vertices have at least the singleton cut separating them. -/
theorem separatingCuts_nonempty {x y : W} (hxy : x ≠ y) :
    (separatingCuts x y).Nonempty := by
  classical
  refine ⟨{x}, ?_⟩
  simp [Ne.symm hxy]

/-- Boundary cardinalities of the oriented cuts separating `x` from `y`. -/
noncomputable def separatingCutSizes
    (H : FiniteEdgeIndexedGraph W) (x y : W) : Finset Nat :=
  (separatingCuts x y).image fun X => (H.boundary X).card

theorem separatingCutSizes_nonempty (H : FiniteEdgeIndexedGraph W)
    {x y : W} (hxy : x ≠ y) :
    (H.separatingCutSizes x y).Nonempty := by
  classical
  exact (separatingCuts_nonempty hxy).image _

/-- The minimum number of named edge copies in a cut separating two distinct
vertices.  The diagonal is assigned the harmless default value `0`. -/
noncomputable def localEdgeConnectivity
    (H : FiniteEdgeIndexedGraph W) (x y : W) : Nat :=
  if hxy : x = y then 0
  else (H.separatingCutSizes x y).min'
    (H.separatingCutSizes_nonempty hxy)

theorem localEdgeConnectivity_eq_min' (H : FiniteEdgeIndexedGraph W)
    {x y : W} (hxy : x ≠ y) :
    H.localEdgeConnectivity x y =
      (H.separatingCutSizes x y).min'
        (H.separatingCutSizes_nonempty hxy) := by
  simp [localEdgeConnectivity, hxy]

@[simp] theorem localEdgeConnectivity_self
    (H : FiniteEdgeIndexedGraph W) (x : W) :
    H.localEdgeConnectivity x x = 0 := by
  simp [localEdgeConnectivity]

/-- The cut-threshold predicate is exactly comparison with the finite
minimum-cut value. -/
theorem pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
    (H : FiniteEdgeIndexedGraph W) {x y : W} (hxy : x ≠ y) (k : Nat) :
    H.PairwiseEdgeConnectedAtLeast x y k ↔
      k ≤ H.localEdgeConnectivity x y := by
  classical
  rw [H.localEdgeConnectivity_eq_min' hxy]
  constructor
  · intro h
    apply Finset.le_min'
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨X, hX, rfl⟩
    exact h X (mem_separatingCuts.mp hX).1
      (mem_separatingCuts.mp hX).2
  · intro hk X hx hy
    exact hk.trans (Finset.min'_le _ _ (Finset.mem_image.mpr
      ⟨X, mem_separatingCuts.mpr ⟨hx, hy⟩, rfl⟩))

/-- Local edge connectivity is symmetric. -/
theorem localEdgeConnectivity_comm
    (H : FiniteEdgeIndexedGraph W) (x y : W) :
    H.localEdgeConnectivity x y = H.localEdgeConnectivity y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  apply Nat.le_antisymm
  · apply (H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
      (Ne.symm hxy) _).mp
    exact (H.pairwiseEdgeConnectedAtLeast_comm x y _).mp
      ((H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
        hxy _).mpr le_rfl)
  · apply (H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
      hxy _).mp
    exact (H.pairwiseEdgeConnectedAtLeast_comm y x _).mp
      ((H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
        (Ne.symm hxy) _).mpr le_rfl)

/-- A minimum separating cut realizes local edge connectivity. -/
theorem exists_minimum_separatingCut
    (H : FiniteEdgeIndexedGraph W) {x y : W} (hxy : x ≠ y) :
    ∃ X : Finset W, x ∈ X ∧ y ∉ X ∧
      (H.boundary X).card = H.localEdgeConnectivity x y := by
  classical
  have hmem := Finset.min'_mem (H.separatingCutSizes x y)
    (H.separatingCutSizes_nonempty hxy)
  rcases Finset.mem_image.mp hmem with ⟨X, hX, hcard⟩
  refine ⟨X, (mem_separatingCuts.mp hX).1,
    (mem_separatingCuts.mp hX).2, ?_⟩
  rw [H.localEdgeConnectivity_eq_min' hxy]
  exact hcard

/-- Every oriented separating cut bounds local edge connectivity from above. -/
theorem localEdgeConnectivity_le_boundary
    (H : FiniteEdgeIndexedGraph W) {x y : W} {X : Finset W}
    (hx : x ∈ X) (hy : y ∉ X) :
    H.localEdgeConnectivity x y ≤ (H.boundary X).card := by
  have hxy : x ≠ y := by
    intro h
    exact hy (h ▸ hx)
  rw [H.localEdgeConnectivity_eq_min' hxy]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨X, mem_separatingCuts.mpr ⟨hx, hy⟩, rfl⟩)

/-! ## Center-avoiding requirements -/

/-- Ordered pairs crossing `X` inside the ground set with center `s` removed.
The first endpoint is in `X`; the second is outside `X` and is not `s`. -/
def centerAvoidingPairs (s : W) (X : Finset W) : Finset (W × W) :=
  X ×ˢ ((Finset.univ.erase s) \ X)

@[simp] theorem mem_centerAvoidingPairs {s : W} {X : Finset W} {p : W × W} :
    p ∈ centerAvoidingPairs s X ↔
      p.1 ∈ X ∧ p.2 ∉ X ∧ p.2 ≠ s := by
  simp [centerAvoidingPairs]
  tauto

/-- The largest local edge connectivity demanded across `X` while avoiding
the distinguished center on the outside.  `Finset.sup` makes the value `0`
when there is no eligible pair. -/
noncomputable def centerAvoidingRequirement
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset W) : Nat :=
  (centerAvoidingPairs s X).sup fun p =>
    H.localEdgeConnectivity p.1 p.2

@[simp] theorem centerAvoidingRequirement_empty
    (H : FiniteEdgeIndexedGraph W) (s : W) :
    H.centerAvoidingRequirement s ∅ = 0 := by
  simp [centerAvoidingRequirement, centerAvoidingPairs]

theorem localEdgeConnectivity_le_centerAvoidingRequirement
    (H : FiniteEdgeIndexedGraph W) {s x y : W} {X : Finset W}
    (hx : x ∈ X) (hy : y ∉ X) (hys : y ≠ s) :
    H.localEdgeConnectivity x y ≤ H.centerAvoidingRequirement s X := by
  unfold centerAvoidingRequirement
  simpa using (Finset.le_sup
    (f := fun p : W × W => H.localEdgeConnectivity p.1 p.2)
    (b := (x, y)) (mem_centerAvoidingPairs.mpr ⟨hx, hy, hys⟩))

/-- Pointwise bounds on all eligible pairs bound the requirement. -/
theorem centerAvoidingRequirement_le
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W} {k : Nat}
    (h : ∀ x ∈ X, ∀ y, y ∉ X -> y ≠ s ->
      H.localEdgeConnectivity x y ≤ k) :
    H.centerAvoidingRequirement s X ≤ k := by
  apply Finset.sup_le
  intro p hp
  have hmem := mem_centerAvoidingPairs.mp hp
  exact h p.1 hmem.1 p.2 hmem.2.1 hmem.2.2

/-- Every center-avoiding requirement is at most the size of its own cut. -/
theorem centerAvoidingRequirement_le_boundary
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset W) :
    H.centerAvoidingRequirement s X ≤ (H.boundary X).card := by
  apply H.centerAvoidingRequirement_le
  intro x hx y hy _
  exact H.localEdgeConnectivity_le_boundary hx hy

/-- If no noncenter vertex lies outside `X`, there is no eligible pair and the
requirement is zero. -/
theorem centerAvoidingRequirement_eq_zero_of_ground_subset
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hground : Finset.univ.erase s ⊆ X) :
    H.centerAvoidingRequirement s X = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply H.centerAvoidingRequirement_le
  intro x hx y hy hys
  exact (hy (hground (by simp [hys]))).elim

/-- A nonempty proper subset of the center-deleted ground set has a pair that
realizes its requirement. -/
theorem exists_centerAvoidingRequirement_pair
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hX : X.Nonempty) (hproper : X ⊂ Finset.univ.erase s) :
    ∃ x ∈ X, ∃ y, y ∉ X ∧ y ≠ s ∧
      H.localEdgeConnectivity x y = H.centerAvoidingRequirement s X := by
  classical
  rcases Finset.exists_of_ssubset hproper with ⟨y, hyGround, hyX⟩
  have houtside : ((Finset.univ.erase s) \ X).Nonempty :=
    ⟨y, Finset.mem_sdiff.mpr ⟨hyGround, hyX⟩⟩
  have hpairs : (centerAvoidingPairs s X).Nonempty :=
    hX.product houtside
  rcases Finset.exists_mem_eq_sup (centerAvoidingPairs s X) hpairs
      (fun p => H.localEdgeConnectivity p.1 p.2) with ⟨p, hp, heq⟩
  have hmem := mem_centerAvoidingPairs.mp hp
  exact ⟨p.1, hmem.1, p.2, hmem.2.1, hmem.2.2, heq.symm⟩

/-- Reversing every eligible pair can only increase the requirement of the
center-deleted complement. -/
theorem centerAvoidingRequirement_le_complement
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hX : X ⊆ Finset.univ.erase s) :
    H.centerAvoidingRequirement s X ≤
      H.centerAvoidingRequirement s ((Finset.univ.erase s) \ X) := by
  apply H.centerAvoidingRequirement_le
  intro x hx y hy hys
  rw [H.localEdgeConnectivity_comm x y]
  apply H.localEdgeConnectivity_le_centerAvoidingRequirement
  · exact Finset.mem_sdiff.mpr ⟨by simp [hys], hy⟩
  · simp only [Finset.mem_sdiff]
    intro h
    exact h.2 hx
  · exact fun h => by
      subst x
      exact (Finset.mem_erase.mp (hX hx)).1 rfl

/-- The requirement is symmetric under complement in `univ.erase s`. -/
theorem centerAvoidingRequirement_complement
    (H : FiniteEdgeIndexedGraph W) {s : W} {X : Finset W}
    (hX : X ⊆ Finset.univ.erase s) :
    H.centerAvoidingRequirement s ((Finset.univ.erase s) \ X) =
      H.centerAvoidingRequirement s X := by
  apply Nat.le_antisymm
  · have hle := H.centerAvoidingRequirement_le_complement
      (X := (Finset.univ.erase s) \ X) (Finset.sdiff_subset)
    have hdouble :
        (Finset.univ.erase s) \ ((Finset.univ.erase s) \ X) = X := by
      ext z
      simp only [Finset.mem_sdiff]
      constructor
      · intro h
        by_contra hzX
        exact h.2 ⟨h.1, hzX⟩
      · intro hzX
        exact ⟨hX hzX, fun hz => hz.2 hzX⟩
    simpa [hdouble] using hle
  · exact H.centerAvoidingRequirement_le_complement hX

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
