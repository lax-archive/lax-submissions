import Lax17Proofs.Source.MaderEvenDecomposition
import Lax17Proofs.Source.MaderThreeEdgeAugmentation

namespace Lax17Proofs

universe u v w

/-!
# Odd-degree reduction for Mader splitting

This file carries out the standard reduction from odd center degree to the
even theorem.  Three parallel copies from the center to a fresh vertex make
the degree even.  An avoiding run consumes any selected augmentation copies;
its final pair therefore consists of two surviving old copies.  The pair is
transported back through the preceding splits, and then projected to the
original graph.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Admissibility preserves the numerical center-avoiding requirement. -/
private theorem centerAvoidingRequirement_maderSplit_eq
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (hadm : H.MaderAdmissible p) (X : Finset W)
    (hX : X ⊆ Finset.univ.erase s) :
    (H.maderSplit p).centerAvoidingRequirement s X =
      H.centerAvoidingRequirement s X := by
  have hlocal : ∀ x y : W, x ≠ s → y ≠ s → x ≠ y →
      (H.maderSplit p).localEdgeConnectivity x y =
        H.localEdgeConnectivity x y := by
    intro x y hxs hys hxy
    apply Nat.le_antisymm
    · apply (H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
        hxy _).mp
      exact (hadm x y hxs hys hxy _).2
        (((H.maderSplit p).pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
          hxy _).2 le_rfl)
    · apply ((H.maderSplit p).pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
        hxy _).mp
      exact (hadm x y hxs hys hxy _).1
        ((H.pairwiseEdgeConnectedAtLeast_iff_le_localEdgeConnectivity
          hxy _).2 le_rfl)
  apply Nat.le_antisymm
  · apply (H.maderSplit p).centerAvoidingRequirement_le
    intro x hx y hy hys
    have hxs : x ≠ s := by
      intro h
      subst x
      exact (Finset.mem_erase.mp (hX hx)).1 rfl
    have hxy : x ≠ y := fun h => hy (h ▸ hx)
    rw [hlocal x y hxs hys hxy]
    exact H.localEdgeConnectivity_le_centerAvoidingRequirement hx hy hys
  · apply H.centerAvoidingRequirement_le
    intro x hx y hy hys
    have hxs : x ≠ s := by
      intro h
      subst x
      exact (Finset.mem_erase.mp (hX hx)).1 rfl
    have hxy : x ≠ y := fun h => hy (h ▸ hx)
    rw [← hlocal x y hxs hys hxy]
    exact (H.maderSplit p).localEdgeConnectivity_le_centerAvoidingRequirement
      hx hy hys

/-- A pair in the split graph with the same two other endpoints as a pair in
the parent graph pulls admissibility back through an admissible earlier
split. -/
private theorem admissible_of_admissible_maderSplit
    (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) (hp : H.MaderAdmissible p)
    (r : H.MaderSplitPair s) (q : (H.maderSplit p).MaderSplitPair s)
    (hfirst : r.firstOther = q.firstOther)
    (hsecond : r.secondOther = q.secondOther)
    (hq : (H.maderSplit p).MaderAdmissible q) :
    H.MaderAdmissible r := by
  by_contra hr
  rcases (H.not_maderAdmissible_iff_exists_dangerous r).mp hr with
    ⟨X, hX, hrFirst, hrSecond⟩
  exact ((H.maderSplit p).not_maderAdmissible_of_exists_dangerous q
    ⟨X,
      ⟨hX.nonempty, hX.ssubset_ground, by
        have hboundary := H.maderSplit_boundary_card_le p X hX.center_not_mem
        have hrequirement := H.centerAvoidingRequirement_maderSplit_eq
          p hp X hX.subset_ground
        rw [hrequirement]
        exact hboundary.trans hX.boundary_le⟩,
      by simpa [← hfirst] using hrFirst,
      by simpa [← hsecond] using hrSecond⟩) hq

/-- Membership of a surviving old copy is exactly membership of its parent
copy among the distinguished edges. -/
private theorem mem_survivingDistinguished_old
    {H : FiniteEdgeIndexedGraph W} {s : W}
    (p : H.MaderSplitPair s) (D : Finset H.Edge)
    (e : {g : H.Edge // g ≠ p.first ∧ g ≠ p.second}) :
    (Sum.inl e : (H.maderSplit p).Edge) ∈ survivingDistinguished p D ↔
      e.1 ∈ D := by
  classical
  unfold survivingDistinguished
  dsimp only
  refine Finset.mem_map.trans ?_
  constructor
  · rintro ⟨a, ha, hmap⟩
    have hae : a = e.1 := by
      have hsub := Sum.inl.inj hmap
      exact congrArg Subtype.val hsub
    have haD : a.1 ∈ D :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase a.2)
    exact hae ▸ haD
  · intro he
    let a : {g : H.Edge // g ∈ (D.erase p.first).erase p.second} :=
      ⟨e.1, by simp [he, e.2.1, e.2.2]⟩
    refine ⟨a, by simp, ?_⟩
    exact congrArg Sum.inl (Subtype.ext rfl)

/-- Pull a center pair in a split graph back to its two surviving named copies
in the parent graph. -/
private theorem exists_parent_pair
    (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s)
    (q : (H.maderSplit p).MaderSplitPair s) :
    ∃ (r : H.MaderSplitPair s)
      (firstOld : {g : H.Edge // g ≠ p.first ∧ g ≠ p.second})
      (secondOld : {g : H.Edge // g ≠ p.first ∧ g ≠ p.second}),
      q.first = Sum.inl firstOld ∧ q.second = Sum.inl secondOld ∧
        r.first = firstOld.1 ∧ r.second = secondOld.1 ∧
        r.firstOther = q.firstOther ∧ r.secondOther = q.secondOther := by
  classical
  rcases H.maderSplit_incidentEdge_is_old p q.first
      q.first_mem_incidentEdges with ⟨firstOld, hfirst⟩
  rcases H.maderSplit_incidentEdge_is_old p q.second
      q.second_mem_incidentEdges with ⟨secondOld, hsecond⟩
  let r : H.MaderSplitPair s :=
    { first := firstOld.1
      second := secondOld.1
      edge_ne := by
        intro heq
        apply q.edge_ne
        rw [hfirst, hsecond]
        exact congrArg Sum.inl (Subtype.ext heq)
      firstOther := q.firstOther
      secondOther := q.secondOther
      first_ends := by
        rcases q.first_ends with h | h
        · exact Or.inl ⟨by simpa [hfirst] using h.1,
            by simpa [hfirst] using h.2⟩
        · exact Or.inr ⟨by simpa [hfirst] using h.1,
            by simpa [hfirst] using h.2⟩
      second_ends := by
        rcases q.second_ends with h | h
        · exact Or.inl ⟨by simpa [hsecond] using h.1,
            by simpa [hsecond] using h.2⟩
        · exact Or.inr ⟨by simpa [hsecond] using h.1,
            by simpa [hsecond] using h.2⟩ }
  exact ⟨r, firstOld, secondOld, hfirst, hsecond, rfl, rfl, rfl, rfl⟩

/-- Any avoiding run yields an admissible pair in its initial graph which
avoids every initially distinguished copy. -/
theorem MaderAvoidingRun.exists_initial_avoiding_pair
    {H : FiniteEdgeIndexedGraph W} {s : W} {D : Finset H.Edge}
    (R : MaderAvoidingRun s H D) :
    ∃ p : H.MaderSplitPair s,
      H.MaderAdmissible p ∧ p.first ∉ D ∧ p.second ∉ D := by
  induction R with
  | here H D p hp hfirst hsecond =>
      exact ⟨p, hp, hfirst, hsecond⟩
  | later H D p hp hhit tail ih =>
      rcases ih with ⟨q, hq, hqFirst, hqSecond⟩
      rcases H.exists_parent_pair p q with
        ⟨r, firstOld, secondOld, qFirst, qSecond,
          rFirst, rSecond, rFirstOther, rSecondOther⟩
      have hr : H.MaderAdmissible r :=
        H.admissible_of_admissible_maderSplit p hp r q
          rFirstOther rSecondOther hq
      have hrFirst : r.first ∉ D := by
        intro hmem
        apply hqFirst
        rw [qFirst]
        apply (mem_survivingDistinguished_old p D firstOld).2
        simpa [rFirst] using hmem
      have hrSecond : r.second ∉ D := by
        intro hmem
        apply hqSecond
        rw [qSecond]
        apply (mem_survivingDistinguished_old p D secondOld).2
        simpa [rSecond] using hmem
      exact ⟨r, hr, hrFirst, hrSecond⟩

/-- The three named augmentation copies used as the distinguished set. -/
private def threeAugmentationEdges (H : FiniteEdgeIndexedGraph W) (s : W) :
    Finset (H.threeEdgeAugmentation s).Edge :=
  {H.threeEdgeAugmentationFirstEdge s,
    H.threeEdgeAugmentationSecondEdge s,
    H.threeEdgeAugmentationThirdEdge s}

@[simp] private theorem card_threeAugmentationEdges
    (H : FiniteEdgeIndexedGraph W) (s : W) :
    (threeAugmentationEdges H s).card = 3 := by
  simp only [threeAugmentationEdges, threeEdgeAugmentationFirstEdge,
    threeEdgeAugmentationSecondEdge, threeEdgeAugmentationThirdEdge]
  have hfirst :
      (Sum.inr ThreeAugmentationEdge.first : H.Edge ⊕ ThreeAugmentationEdge) ∉
        ({Sum.inr ThreeAugmentationEdge.second,
          Sum.inr ThreeAugmentationEdge.third} :
          Finset (H.Edge ⊕ ThreeAugmentationEdge)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq, not_or]
    decide
  have hsecond :
      (Sum.inr ThreeAugmentationEdge.second : H.Edge ⊕ ThreeAugmentationEdge) ∉
        ({Sum.inr ThreeAugmentationEdge.third} :
          Finset (H.Edge ⊕ ThreeAugmentationEdge)) := by
    simp only [Finset.mem_singleton, Sum.inr.injEq]
    decide
  calc
    ({Sum.inr ThreeAugmentationEdge.first,
        Sum.inr ThreeAugmentationEdge.second,
        Sum.inr ThreeAugmentationEdge.third} :
        Finset (H.Edge ⊕ ThreeAugmentationEdge)).card =
        ({Sum.inr ThreeAugmentationEdge.second,
          Sum.inr ThreeAugmentationEdge.third} :
          Finset (H.Edge ⊕ ThreeAugmentationEdge)).card + 1 :=
      Finset.card_insert_of_notMem hfirst
    _ = ({Sum.inr ThreeAugmentationEdge.third} :
          Finset (H.Edge ⊕ ThreeAugmentationEdge)).card + 1 + 1 := by
      rw [Finset.card_insert_of_notMem hsecond]
    _ = 3 := by simp

/-- An augmented edge outside the three distinguished copies is an old edge. -/
private theorem augmentation_edge_is_old_of_not_mem
    (H : FiniteEdgeIndexedGraph W) (s : W)
    (e : (H.threeEdgeAugmentation s).Edge)
    (he : e ∉ threeAugmentationEdges H s) :
    ∃ old : H.Edge, e = Sum.inl old := by
  rcases e with old | new
  · exact ⟨old, rfl⟩
  · cases new <;> simp [threeAugmentationEdges,
      threeEdgeAugmentationFirstEdge, threeEdgeAugmentationSecondEdge,
      threeEdgeAugmentationThirdEdge] at he

/-- The actual odd-degree reduction.  The even theorem is required only on
the augmented vertex type. -/
theorem exists_maderAdmissible_of_odd
    (hexists : EvenMaderPairExistence (W := W ⊕ Unit))
    (H : FiniteEdgeIndexedGraph W) (s : W)
    (hdegree : 5 ≤ H.degree s) (hodd : Odd (H.degree s))
    (hno : H.NoIncidentCutEdge s) :
    ∃ p : H.MaderSplitPair s, H.MaderAdmissible p := by
  classical
  let K := H.threeEdgeAugmentation s
  let center : W ⊕ Unit := Sum.inl s
  let D := threeAugmentationEdges H s
  have hdegreeK : K.degree center = H.degree s + 3 := by
    simpa [K, center] using H.threeEdgeAugmentation_degree_center s
  have hevenK : Even (K.degree center) := by
    rw [hdegreeK]
    exact Odd.add_odd hodd (by decide : Odd 3)
  have hnoK : K.NoIncidentCutEdge center := by
    simpa [K, center] using hno.threeEdgeAugmentation
  have hDcard : D.card ≤ 3 := by simp [D]
  have hdegreeEight : 8 ≤ K.degree center := by omega
  rcases exists_maderAvoidingRun_of_card_le_three hexists K center D
      hevenK hnoK hDcard hdegreeEight with ⟨R⟩
  rcases R.exists_initial_avoiding_pair with
    ⟨q, hq, hqFirst, hqSecond⟩
  rcases H.augmentation_edge_is_old_of_not_mem s q.first hqFirst with
    ⟨first, qFirst⟩
  rcases H.augmentation_edge_is_old_of_not_mem s q.second hqSecond with
    ⟨second, qSecond⟩
  have qFirstOtherOld : ∃ other : W, q.firstOther = Sum.inl other := by
    rcases q.first_ends with h | h
    · exact ⟨H.right first, by simpa [K, qFirst] using h.2.symm⟩
    · exact ⟨H.left first, by simpa [K, qFirst] using h.2.symm⟩
  have qSecondOtherOld : ∃ other : W, q.secondOther = Sum.inl other := by
    rcases q.second_ends with h | h
    · exact ⟨H.right second, by simpa [K, qSecond] using h.2.symm⟩
    · exact ⟨H.left second, by simpa [K, qSecond] using h.2.symm⟩
  rcases qFirstOtherOld with ⟨firstOther, qFirstOther⟩
  rcases qSecondOtherOld with ⟨secondOther, qSecondOther⟩
  let p : H.MaderSplitPair s :=
    { first := first
      second := second
      edge_ne := by
        intro heq
        apply q.edge_ne
        rw [qFirst, qSecond, heq]
      firstOther := firstOther
      secondOther := secondOther
      first_ends := by
        rcases q.first_ends with h | h
        · exact Or.inl ⟨by simpa [K, center, qFirst] using h.1,
            by simpa [K, qFirst, qFirstOther] using h.2⟩
        · exact Or.inr ⟨by simpa [K, center, qFirst] using h.1,
            by simpa [K, qFirst, qFirstOther] using h.2⟩
      second_ends := by
        rcases q.second_ends with h | h
        · exact Or.inl ⟨by simpa [K, center, qSecond] using h.1,
            by simpa [K, qSecond, qSecondOther] using h.2⟩
        · exact Or.inr ⟨by simpa [K, center, qSecond] using h.1,
            by simpa [K, qSecond, qSecondOther] using h.2⟩ }
  refine ⟨p, ?_⟩
  intro x y hxs hys hxy k
  have hAug := hq (Sum.inl x) (Sum.inl y)
    (fun h => hxs (Sum.inl.inj h)) (fun h => hys (Sum.inl.inj h))
    (fun h => hxy (Sum.inl.inj h)) k
  rw [H.pairwiseEdgeConnectedAtLeast_threeEdgeAugmentation_iff s x y k] at hAug
  have hpLift : p.liftThreeEdgeAugmentation = q := by
    cases q with
    | mk qf qs qne qfo qso qfe qse =>
        dsimp only at qFirst qSecond qFirstOther qSecondOther
        subst qf
        subst qs
        subst qfo
        subst qso
        rfl
  rw [← hpLift] at hAug
  rw [H.pairwiseEdgeConnectedAtLeast_maderSplit_liftThreeEdgeAugmentation_iff
    p x y k] at hAug
  exact hAug

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
