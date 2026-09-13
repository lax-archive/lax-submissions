import Lax17Proofs.Source.MaderBridge
import Lax17Proofs.Source.MaderCutIdentities
import Lax17Proofs.Source.MaderConnectivity

namespace Lax17Proofs

universe u v w

/-!
# Three-edge augmentation for Mader splitting

This module adds a fresh vertex joined to the old center by three separately
named parallel edge copies.  Projecting an augmented cut to the old vertices
preserves all old boundary copies; the only additional contribution is either
zero or all three new copies.  This gives exact preservation of every old
local edge-connectivity value, both before and after splitting a lifted old
pair.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The three separately named parallel copies in the augmentation. -/
inductive ThreeAugmentationEdge
  | first
  | second
  | third
  deriving DecidableEq, Fintype

@[simp] theorem card_threeAugmentationEdge :
    Fintype.card ThreeAugmentationEdge = 3 := by
  decide

/-- Add a fresh vertex and three named parallel copies from `s` to it. -/
def threeEdgeAugmentation (H : FiniteEdgeIndexedGraph W) (s : W) :
    FiniteEdgeIndexedGraph (W ⊕ Unit) where
  Edge := H.Edge ⊕ ThreeAugmentationEdge
  left
    | Sum.inl e => Sum.inl (H.left e)
    | Sum.inr _ => Sum.inl s
  right
    | Sum.inl e => Sum.inl (H.right e)
    | Sum.inr _ => Sum.inr ()
  end_ne
    | Sum.inl e => fun h => H.end_ne e (Sum.inl.inj h)
    | Sum.inr _ => by simp

/-- The old-center embedding into the augmented vertex type. -/
def threeEdgeAugmentationCenter (s : W) : W ⊕ Unit := Sum.inl s

/-- The fresh vertex of the augmentation. -/
def threeEdgeAugmentationFresh (W : Type u) : W ⊕ Unit := Sum.inr ()

/-- Embed an old named edge copy in the augmented graph. -/
def threeEdgeAugmentationOldEdge (H : FiniteEdgeIndexedGraph W) (s : W)
    (e : H.Edge) : (H.threeEdgeAugmentation s).Edge := Sum.inl e

/-- The first new parallel edge copy. -/
def threeEdgeAugmentationFirstEdge (H : FiniteEdgeIndexedGraph W) (s : W) :
    (H.threeEdgeAugmentation s).Edge :=
  Sum.inr ThreeAugmentationEdge.first

/-- The second new parallel edge copy. -/
def threeEdgeAugmentationSecondEdge (H : FiniteEdgeIndexedGraph W) (s : W) :
    (H.threeEdgeAugmentation s).Edge :=
  Sum.inr ThreeAugmentationEdge.second

/-- The third new parallel edge copy. -/
def threeEdgeAugmentationThirdEdge (H : FiniteEdgeIndexedGraph W) (s : W) :
    (H.threeEdgeAugmentation s).Edge :=
  Sum.inr ThreeAugmentationEdge.third

/-- The augmentation adds exactly three named edge copies. -/
theorem threeEdgeAugmentation_edgeCard
    (H : FiniteEdgeIndexedGraph W) (s : W) :
    Fintype.card (H.threeEdgeAugmentation s).Edge =
      Fintype.card H.Edge + 3 := by
  rw [show Fintype.card (H.threeEdgeAugmentation s).Edge =
      Fintype.card (H.Edge ⊕ ThreeAugmentationEdge) by rfl,
    Fintype.card_sum, card_threeAugmentationEdge]

@[simp] theorem threeEdgeAugmentation_old_left
    (H : FiniteEdgeIndexedGraph W) (s : W) (e : H.Edge) :
    (H.threeEdgeAugmentation s).left (Sum.inl e) = Sum.inl (H.left e) := rfl

@[simp] theorem threeEdgeAugmentation_old_right
    (H : FiniteEdgeIndexedGraph W) (s : W) (e : H.Edge) :
    (H.threeEdgeAugmentation s).right (Sum.inl e) = Sum.inl (H.right e) := rfl

@[simp] theorem threeEdgeAugmentation_new_left
    (H : FiniteEdgeIndexedGraph W) (s : W) (e : ThreeAugmentationEdge) :
    (H.threeEdgeAugmentation s).left (Sum.inr e) = Sum.inl s := rfl

@[simp] theorem threeEdgeAugmentation_new_right
    (H : FiniteEdgeIndexedGraph W) (s : W) (e : ThreeAugmentationEdge) :
    (H.threeEdgeAugmentation s).right (Sum.inr e) = Sum.inr () := rfl

/-- The old vertices occurring in an augmented vertex set. -/
noncomputable def oldVertexSet (X : Finset (W ⊕ Unit)) : Finset W := by
  classical
  exact Finset.univ.filter fun w => Sum.inl w ∈ X

@[simp] theorem mem_oldVertexSet {X : Finset (W ⊕ Unit)} {w : W} :
    w ∈ oldVertexSet X ↔ Sum.inl w ∈ X := by
  classical
  simp [oldVertexSet]

/-- Whether a cut separates the old center from the fresh vertex. -/
def SeparatesAugmentationFresh (s : W) (X : Finset (W ⊕ Unit)) : Prop :=
  (Sum.inl s ∈ X ∧ Sum.inr () ∉ X) ∨
    (Sum.inr () ∈ X ∧ Sum.inl s ∉ X)

instance (s : W) (X : Finset (W ⊕ Unit)) :
    Decidable (SeparatesAugmentationFresh s X) := by
  unfold SeparatesAugmentationFresh
  infer_instance

@[simp] theorem threeEdgeAugmentation_old_crosses
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset (W ⊕ Unit))
    (e : H.Edge) :
    (H.threeEdgeAugmentation s).Crosses X (Sum.inl e) ↔
      H.Crosses (oldVertexSet X) e := by
  simp [Crosses]

@[simp] theorem threeEdgeAugmentation_new_crosses
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset (W ⊕ Unit))
    (e : ThreeAugmentationEdge) :
    (H.threeEdgeAugmentation s).Crosses X (Sum.inr e) ↔
      SeparatesAugmentationFresh s X := by
  rfl

/-- Every augmented cut consists of its projected old boundary and either
none or all three new parallel copies. -/
theorem threeEdgeAugmentation_boundary_card
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset (W ⊕ Unit)) :
    ((H.threeEdgeAugmentation s).boundary X).card =
      (H.boundary (oldVertexSet X)).card +
        if SeparatesAugmentationFresh s X then 3 else 0 := by
  classical
  rw [boundary, Finset.card_filter]
  change (∑ e : H.Edge ⊕ ThreeAugmentationEdge,
      if (H.threeEdgeAugmentation s).Crosses X e then 1 else 0) = _
  rw [Fintype.sum_sum_type]
  have hold :
      (∑ e : H.Edge,
          if (H.threeEdgeAugmentation s).Crosses X (Sum.inl e) then 1 else 0) =
        (H.boundary (oldVertexSet X)).card := by
    rw [boundary, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro e _
    simp
  rw [hold]
  congr 1
  by_cases hsep : SeparatesAugmentationFresh s X
  · simp [hsep]
  · simp [hsep]

/-- Embed an old cut and put the fresh vertex on the same side as the center. -/
noncomputable def alignedOldCut (s : W) (X : Finset W) :
    Finset (W ⊕ Unit) := by
  classical
  exact X.image Sum.inl ∪ if s ∈ X then {Sum.inr ()} else ∅

@[simp] theorem inl_mem_alignedOldCut (s : W) (X : Finset W) (w : W) :
    Sum.inl w ∈ alignedOldCut s X ↔ w ∈ X := by
  classical
  by_cases hs : s ∈ X <;> simp [alignedOldCut, hs]

@[simp] theorem fresh_mem_alignedOldCut (s : W) (X : Finset W) :
    Sum.inr () ∈ alignedOldCut s X ↔ s ∈ X := by
  classical
  by_cases hs : s ∈ X <;> simp [alignedOldCut, hs]

@[simp] theorem oldVertexSet_alignedOldCut (s : W) (X : Finset W) :
    oldVertexSet (alignedOldCut s X) = X := by
  classical
  ext w
  simp

@[simp] theorem not_separatesAugmentationFresh_alignedOldCut
    (s : W) (X : Finset W) :
    ¬ SeparatesAugmentationFresh s (alignedOldCut s X) := by
  simp [SeparatesAugmentationFresh]

/-- Aligned old cuts have exactly their old boundary cardinality. -/
theorem threeEdgeAugmentation_boundary_card_alignedOldCut
    (H : FiniteEdgeIndexedGraph W) (s : W) (X : Finset W) :
    ((H.threeEdgeAugmentation s).boundary (alignedOldCut s X)).card =
      (H.boundary X).card := by
  simp [H.threeEdgeAugmentation_boundary_card]

/-- The old center gains exactly the three new parallel copies. -/
theorem threeEdgeAugmentation_degree_center
    (H : FiniteEdgeIndexedGraph W) (s : W) :
    (H.threeEdgeAugmentation s).degree (Sum.inl s) = H.degree s + 3 := by
  classical
  calc
    (H.threeEdgeAugmentation s).degree (Sum.inl s) =
        ((H.threeEdgeAugmentation s).boundary {Sum.inl s}).card := by
      rw [(H.threeEdgeAugmentation s).boundary_singleton]
      rfl
    _ = (H.boundary {s}).card + 3 := by
      have hold : oldVertexSet ({Sum.inl s} : Finset (W ⊕ Unit)) = {s} := by
        ext w
        simp
      rw [H.threeEdgeAugmentation_boundary_card]
      simp [hold, SeparatesAugmentationFresh]
    _ = H.degree s + 3 := by
      rw [H.boundary_singleton]
      rfl

/-- If no old edge at `s` is a cut edge, then none of the old or new copies
incident with the augmented center is a cut edge. -/
theorem NoIncidentCutEdge.threeEdgeAugmentation
    {H : FiniteEdgeIndexedGraph W} {s : W} (h : H.NoIncidentCutEdge s) :
    (H.threeEdgeAugmentation s).NoIncidentCutEdge (Sum.inl s) := by
  classical
  intro e heInc heCut
  rcases heCut with ⟨X, hboundary⟩
  have heBoundary : e ∈ (H.threeEdgeAugmentation s).boundary X := by
    simp [hboundary]
  have hcard : ((H.threeEdgeAugmentation s).boundary X).card = 1 := by
    simp [hboundary]
  have hformula := H.threeEdgeAugmentation_boundary_card s X
  cases e with
  | inl old =>
      have holdInc : old ∈ H.incidentEdges s := by
        rw [H.mem_incidentEdges]
        simpa using ((H.threeEdgeAugmentation s).mem_incidentEdges
          (Sum.inl s) (Sum.inl old)).mp heInc
      have holdBoundary : old ∈ H.boundary (oldVertexSet X) := by
        rw [H.mem_boundary]
        simpa using ((H.threeEdgeAugmentation s).mem_boundary X
          (Sum.inl old)).mp heBoundary
      have holdCard : (H.boundary (oldVertexSet X)).card = 1 := by
        by_cases hsep : SeparatesAugmentationFresh s X <;>
          simp [hsep] at hformula <;> omega
      exact h old holdInc ((isNamedCutEdge_iff_boundary_card_one_mem H old).2
        ⟨oldVertexSet X, holdCard, holdBoundary⟩)
  | inr new =>
      have hsep : SeparatesAugmentationFresh s X := by
        simpa using ((H.threeEdgeAugmentation s).mem_boundary X
          (Sum.inr new)).mp heBoundary
      simp [hsep] at hformula
      omega

/-! ## Lifting old split pairs -/

/-- Lift an old Mader pair through the vertex and edge embeddings. -/
def MaderSplitPair.liftThreeEdgeAugmentation
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s) :
    (H.threeEdgeAugmentation s).MaderSplitPair (Sum.inl s) where
  first := Sum.inl p.first
  second := Sum.inl p.second
  edge_ne h := p.edge_ne (Sum.inl.inj h)
  firstOther := Sum.inl p.firstOther
  secondOther := Sum.inl p.secondOther
  first_ends := by
    rcases p.first_ends with h | h
    · exact Or.inl ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩
    · exact Or.inr ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩
  second_ends := by
    rcases p.second_ends with h | h
    · exact Or.inl ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩
    · exact Or.inr ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩

@[simp] theorem MaderSplitPair.liftThreeEdgeAugmentation_first
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s) :
    p.liftThreeEdgeAugmentation.first = Sum.inl p.first := rfl

@[simp] theorem MaderSplitPair.liftThreeEdgeAugmentation_second
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s) :
    p.liftThreeEdgeAugmentation.second = Sum.inl p.second := rfl

@[simp] theorem MaderSplitPair.liftThreeEdgeAugmentation_firstOther
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s) :
    p.liftThreeEdgeAugmentation.firstOther = Sum.inl p.firstOther := rfl

@[simp] theorem MaderSplitPair.liftThreeEdgeAugmentation_secondOther
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s) :
    p.liftThreeEdgeAugmentation.secondOther = Sum.inl p.secondOther := rfl

/-! ## Exact preservation before splitting -/

/-- Every old cut-threshold predicate is unchanged by the augmentation. -/
theorem pairwiseEdgeConnectedAtLeast_threeEdgeAugmentation_iff
    (H : FiniteEdgeIndexedGraph W) (s x y : W) (k : Nat) :
    (H.threeEdgeAugmentation s).PairwiseEdgeConnectedAtLeast
        (Sum.inl x) (Sum.inl y) k ↔
      H.PairwiseEdgeConnectedAtLeast x y k := by
  constructor
  · intro h X hx hy
    have hcut := h (alignedOldCut s X) (by simpa) (by simpa)
    simpa [H.threeEdgeAugmentation_boundary_card_alignedOldCut] using hcut
  · intro h X hx hy
    have hold : k ≤ (H.boundary (oldVertexSet X)).card :=
      h (oldVertexSet X) (by simpa using hx) (by simpa using hy)
    rw [H.threeEdgeAugmentation_boundary_card]
    omega

/-- In particular, this is the exact center-avoiding threshold equality for
old vertices distinct from the center. -/
theorem pairwiseEdgeConnectedAtLeast_threeEdgeAugmentation_iff_of_ne_center
    (H : FiniteEdgeIndexedGraph W) (s x y : W) (_ : x ≠ s) (_ : y ≠ s)
    (k : Nat) :
    (H.threeEdgeAugmentation s).PairwiseEdgeConnectedAtLeast
        (Sum.inl x) (Sum.inl y) k ↔
      H.PairwiseEdgeConnectedAtLeast x y k :=
  H.pairwiseEdgeConnectedAtLeast_threeEdgeAugmentation_iff s x y k

/-- Every local edge-connectivity value between old vertices is unchanged. -/
theorem localEdgeConnectivity_threeEdgeAugmentation
    (H : FiniteEdgeIndexedGraph W) (s x y : W) :
    (H.threeEdgeAugmentation s).localEdgeConnectivity
        (Sum.inl x) (Sum.inl y) = H.localEdgeConnectivity x y := by
  by_cases hxy : x = y
  · subst y
    simp
  have hAugNe : Sum.inl x ≠ (Sum.inl y : W ⊕ Unit) :=
    fun h => hxy (Sum.inl.inj h)
  apply Nat.le_antisymm
  · apply (H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity hxy _).mp
    exact (H.pairwiseEdgeConnectedAtLeast_threeEdgeAugmentation_iff s x y _).1
      ((pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
        (H.threeEdgeAugmentation s) hAugNe _).2 le_rfl)
  · apply (pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
      (H.threeEdgeAugmentation s) hAugNe _).mp
    exact (H.pairwiseEdgeConnectedAtLeast_threeEdgeAugmentation_iff s x y _).2
      ((H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity hxy _).2 le_rfl)

/-- Center-avoiding old local connectivity is unchanged by augmentation. -/
theorem localEdgeConnectivity_threeEdgeAugmentation_of_ne_center
    (H : FiniteEdgeIndexedGraph W) (s x y : W) (_ : x ≠ s) (_ : y ≠ s) :
    (H.threeEdgeAugmentation s).localEdgeConnectivity
        (Sum.inl x) (Sum.inl y) = H.localEdgeConnectivity x y :=
  H.localEdgeConnectivity_threeEdgeAugmentation s x y

/-! ## Exact preservation after splitting a lifted old pair -/

private theorem oldVertexSet_compl (X : Finset (W ⊕ Unit)) :
    oldVertexSet Xᶜ = (oldVertexSet X)ᶜ := by
  classical
  ext w
  simp

private theorem separatesAugmentationFresh_compl (s : W)
    (X : Finset (W ⊕ Unit)) :
    SeparatesAugmentationFresh s Xᶜ ↔ SeparatesAugmentationFresh s X := by
  simp only [SeparatesAugmentationFresh, Finset.mem_compl]
  tauto

private theorem maderSplit_liftThreeEdgeAugmentation_boundary_card_of_center_not_mem
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset (W ⊕ Unit)) (hs : Sum.inl s ∉ X) :
    (((H.threeEdgeAugmentation s).maderSplit
        p.liftThreeEdgeAugmentation).boundary X).card =
      ((H.maderSplit p).boundary (oldVertexSet X)).card +
        if SeparatesAugmentationFresh s X then 3 else 0 := by
  have hOldCenter : s ∉ oldVertexSet X := by simpa
  have hAug := boundary_card_maderSplit_add_two_iff
    (H.threeEdgeAugmentation s) p.liftThreeEdgeAugmentation X hs
  have hOld := boundary_card_maderSplit_add_two_iff
    H p (oldVertexSet X) hOldCenter
  have hBase := H.threeEdgeAugmentation_boundary_card s X
  have hFirstMem : Sum.inl p.firstOther ∈ X ↔
      p.firstOther ∈ oldVertexSet X := mem_oldVertexSet.symm
  have hSecondMem : Sum.inl p.secondOther ∈ X ↔
      p.secondOther ∈ oldVertexSet X := mem_oldVertexSet.symm
  simp only [MaderSplitPair.liftThreeEdgeAugmentation_firstOther,
    MaderSplitPair.liftThreeEdgeAugmentation_secondOther,
    hFirstMem, hSecondMem] at hAug
  omega

/-- Splitting a lifted old pair still leaves exactly the projected split cut,
plus either zero or all three augmentation edges. -/
theorem maderSplit_liftThreeEdgeAugmentation_boundary_card
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset (W ⊕ Unit)) :
    (((H.threeEdgeAugmentation s).maderSplit
        p.liftThreeEdgeAugmentation).boundary X).card =
      ((H.maderSplit p).boundary (oldVertexSet X)).card +
        if SeparatesAugmentationFresh s X then 3 else 0 := by
  by_cases hs : Sum.inl s ∈ X
  · have h := maderSplit_liftThreeEdgeAugmentation_boundary_card_of_center_not_mem
      H p Xᶜ (by simp [hs])
    simpa [oldVertexSet_compl, separatesAugmentationFresh_compl] using h
  · exact maderSplit_liftThreeEdgeAugmentation_boundary_card_of_center_not_mem
      H p X hs

/-- Aligned old cuts remain exactly equal after splitting the old pair. -/
theorem maderSplit_liftThreeEdgeAugmentation_boundary_card_alignedOldCut
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (X : Finset W) :
    (((H.threeEdgeAugmentation s).maderSplit
        p.liftThreeEdgeAugmentation).boundary (alignedOldCut s X)).card =
      ((H.maderSplit p).boundary X).card := by
  simp [maderSplit_liftThreeEdgeAugmentation_boundary_card]

/-- Every old cut-threshold predicate is unchanged after splitting the old
pair and its lift. -/
theorem pairwiseEdgeConnectedAtLeast_maderSplit_liftThreeEdgeAugmentation_iff
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (x y : W) (k : Nat) :
    PairwiseEdgeConnectedAtLeast
        ((H.threeEdgeAugmentation s).maderSplit p.liftThreeEdgeAugmentation)
        (Sum.inl x) (Sum.inl y) k ↔
      (H.maderSplit p).PairwiseEdgeConnectedAtLeast x y k := by
  constructor
  · intro h X hx hy
    have hcut := h (alignedOldCut s X) (by simpa) (by simpa)
    simpa [maderSplit_liftThreeEdgeAugmentation_boundary_card_alignedOldCut]
      using hcut
  · intro h X hx hy
    have hold : k ≤ ((H.maderSplit p).boundary (oldVertexSet X)).card :=
      h (oldVertexSet X) (by simpa using hx) (by simpa using hy)
    rw [maderSplit_liftThreeEdgeAugmentation_boundary_card]
    omega

/-- This is the center-avoiding old threshold equality after splitting. -/
theorem pairwiseEdgeConnectedAtLeast_maderSplit_liftThreeEdgeAugmentation_iff_of_ne_center
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (x y : W) (_ : x ≠ s) (_ : y ≠ s) (k : Nat) :
    PairwiseEdgeConnectedAtLeast
        ((H.threeEdgeAugmentation s).maderSplit p.liftThreeEdgeAugmentation)
        (Sum.inl x) (Sum.inl y) k ↔
      (H.maderSplit p).PairwiseEdgeConnectedAtLeast x y k :=
  H.pairwiseEdgeConnectedAtLeast_maderSplit_liftThreeEdgeAugmentation_iff
    p x y k

/-- Thus all old local edge-connectivity values agree after the corresponding
splits. -/
theorem localEdgeConnectivity_maderSplit_liftThreeEdgeAugmentation
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (x y : W) :
    localEdgeConnectivity
        ((H.threeEdgeAugmentation s).maderSplit p.liftThreeEdgeAugmentation)
        (Sum.inl x) (Sum.inl y) =
      (H.maderSplit p).localEdgeConnectivity x y := by
  by_cases hxy : x = y
  · subst y
    simp
  have hAugNe : Sum.inl x ≠ (Sum.inl y : W ⊕ Unit) :=
    fun h => hxy (Sum.inl.inj h)
  apply Nat.le_antisymm
  · apply (pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
      (H.maderSplit p) hxy _).mp
    exact (H.pairwiseEdgeConnectedAtLeast_maderSplit_liftThreeEdgeAugmentation_iff
      p x y _).1
      ((pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
        ((H.threeEdgeAugmentation s).maderSplit p.liftThreeEdgeAugmentation)
        hAugNe _).2 le_rfl)
  · apply (pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
      ((H.threeEdgeAugmentation s).maderSplit p.liftThreeEdgeAugmentation)
      hAugNe _).mp
    exact (H.pairwiseEdgeConnectedAtLeast_maderSplit_liftThreeEdgeAugmentation_iff
      p x y _).2
      (((H.maderSplit p).pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
        hxy _).2 le_rfl)

/-- Center-avoiding old local connectivity remains equal after splitting. -/
theorem localEdgeConnectivity_maderSplit_liftThreeEdgeAugmentation_of_ne_center
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (x y : W) (_ : x ≠ s) (_ : y ≠ s) :
    localEdgeConnectivity
        ((H.threeEdgeAugmentation s).maderSplit p.liftThreeEdgeAugmentation)
        (Sum.inl x) (Sum.inl y) =
      (H.maderSplit p).localEdgeConnectivity x y :=
  H.localEdgeConnectivity_maderSplit_liftThreeEdgeAugmentation p x y

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
