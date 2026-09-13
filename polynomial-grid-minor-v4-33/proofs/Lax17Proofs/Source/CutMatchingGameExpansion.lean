import Lax17Proofs.Source.CutMatchingGameEntropy

namespace Lax17Proofs

universe u v w

/-!
# Expansion predicates for abstract cut-matching histories

The cut-matching game builds a multigraph as the union of the matching edges
chosen over the rounds.  This file defines the edge boundary of a vertex set
in that multigraph when the history is represented as a list of lazy rounds.
-/

namespace SimpleGraph
namespace CutMatchingGame


namespace LazyRound

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- A matching edge of one round crosses a vertex set when exactly one endpoint
lies in the set. -/
def edgeCrosses (R : LazyRound X) (S : Finset X)
    (x : {x : X // x ∈ R.cut.left}) : Prop :=
  (x.1 ∈ S ∧ R.matching.rightEndpoint x ∉ S) ∨
    (R.matching.rightEndpoint x ∈ S ∧ x.1 ∉ S)

instance edgeCrossesDecidable (R : LazyRound X) (S : Finset X) :
    DecidablePred (R.edgeCrosses S) := by
  intro x
  unfold edgeCrosses
  infer_instance

/-- Boundary edge instances contributed by one matching round. -/
def edgeBoundary (R : LazyRound X) (S : Finset X) :
    Finset {x : X // x ∈ R.cut.left} :=
  Finset.univ.filter (R.edgeCrosses S)

@[simp]
theorem mem_edgeBoundary {R : LazyRound X} {S : Finset X}
    {x : {x : X // x ∈ R.cut.left}} :
    x ∈ R.edgeBoundary S ↔ R.edgeCrosses S x := by
  simp [edgeBoundary]

@[simp]
theorem edgeBoundary_empty (R : LazyRound X) :
    R.edgeBoundary (∅ : Finset X) = ∅ := by
  ext x
  simp [edgeCrosses]

@[simp]
theorem edgeBoundary_univ (R : LazyRound X) :
    R.edgeBoundary (Finset.univ : Finset X) = ∅ := by
  ext x
  simp [edgeCrosses]

/-- Vertices of `S` whose matching mate lies outside `S`. -/
noncomputable def insideWithMateOutside (R : LazyRound X) (S : Finset X) :
    Finset X :=
  S.filter fun x => R.matching.mate x ∉ S

theorem mem_insideWithMateOutside {R : LazyRound X} {S : Finset X} {x : X} :
    x ∈ R.insideWithMateOutside S ↔ x ∈ S ∧ R.matching.mate x ∉ S := by
  simp [insideWithMateOutside]

/-- The boundary edge whose endpoint inside `S` is `x`. -/
noncomputable def boundarySourceOfInside
    (R : LazyRound X) (S : Finset X)
    (x : {x : X // x ∈ R.insideWithMateOutside S}) :
    {x : X // x ∈ R.cut.left} :=
  if hxleft : x.1 ∈ R.cut.left then
    ⟨x.1, hxleft⟩
  else
    let hxright : x.1 ∈ R.cut.right :=
      (R.cut.mem_right_iff_not_mem_left x.1).2 hxleft
    ⟨R.matching.leftEndpoint ⟨x.1, hxright⟩,
      R.matching.leftEndpoint_mem ⟨x.1, hxright⟩⟩

theorem boundarySourceOfInside_mem_edgeBoundary
    (R : LazyRound X) (S : Finset X)
    (x : {x : X // x ∈ R.insideWithMateOutside S}) :
    R.boundarySourceOfInside S x ∈ R.edgeBoundary S := by
  classical
  rw [LazyRound.mem_edgeBoundary]
  have hxS : x.1 ∈ S := (R.mem_insideWithMateOutside.mp x.2).1
  have hxmate : R.matching.mate x.1 ∉ S :=
    (R.mem_insideWithMateOutside.mp x.2).2
  by_cases hxleft : x.1 ∈ R.cut.left
  · have hmate :
        R.matching.mate x.1 =
          R.matching.rightEndpoint ⟨x.1, hxleft⟩ :=
      R.matching.mate_of_mem_left hxleft
    have htarget_not :
        R.matching.rightEndpoint ⟨x.1, hxleft⟩ ∉ S := by
      intro htarget
      exact hxmate (by simpa [hmate] using htarget)
    have hcross : R.edgeCrosses S (⟨x.1, hxleft⟩ : {z : X // z ∈ R.cut.left}) :=
      Or.inl ⟨hxS, htarget_not⟩
    simpa [boundarySourceOfInside, hxleft] using hcross
  · have hxright : x.1 ∈ R.cut.right :=
      (R.cut.mem_right_iff_not_mem_left x.1).2 hxleft
    have hmate :
        R.matching.mate x.1 =
          R.matching.leftEndpoint ⟨x.1, hxright⟩ :=
      R.matching.mate_of_mem_right hxright
    have hright :
        R.matching.rightEndpoint
          ⟨R.matching.leftEndpoint ⟨x.1, hxright⟩,
            R.matching.leftEndpoint_mem ⟨x.1, hxright⟩⟩ = x.1 :=
      R.matching.rightEndpoint_leftEndpoint ⟨x.1, hxright⟩
    have hsource_not :
        R.matching.leftEndpoint ⟨x.1, hxright⟩ ∉ S := by
      intro hsource
      exact hxmate (by simpa [hmate] using hsource)
    have hcross :
        R.edgeCrosses S
          (⟨R.matching.leftEndpoint ⟨x.1, hxright⟩,
            R.matching.leftEndpoint_mem ⟨x.1, hxright⟩⟩ :
              {z : X // z ∈ R.cut.left}) :=
      Or.inr ⟨by simpa [hright] using hxS, hsource_not⟩
    simpa [boundarySourceOfInside, hxleft] using hcross

theorem boundarySourceOfInside_injective
    (R : LazyRound X) (S : Finset X) :
    Function.Injective (R.boundarySourceOfInside S) := by
  classical
  intro x y hxy
  apply Subtype.ext
  have hxS : x.1 ∈ S := (R.mem_insideWithMateOutside.mp x.2).1
  have hxmate : R.matching.mate x.1 ∉ S :=
    (R.mem_insideWithMateOutside.mp x.2).2
  have hyS : y.1 ∈ S := (R.mem_insideWithMateOutside.mp y.2).1
  have hymate : R.matching.mate y.1 ∉ S :=
    (R.mem_insideWithMateOutside.mp y.2).2
  unfold boundarySourceOfInside at hxy
  by_cases hxleft : x.1 ∈ R.cut.left
  · by_cases hyleft : y.1 ∈ R.cut.left
    · simpa [hxleft, hyleft] using congrArg Subtype.val hxy
    · have hyright : y.1 ∈ R.cut.right :=
        (R.cut.mem_right_iff_not_mem_left y.1).2 hyleft
      have hsource :
          x.1 = R.matching.leftEndpoint ⟨y.1, hyright⟩ := by
        simpa [hxleft, hyleft] using congrArg Subtype.val hxy
      have hy_eq :
          R.matching.rightEndpoint ⟨x.1, hxleft⟩ = y.1 := by
        have hsub :
            (⟨x.1, hxleft⟩ : {z : X // z ∈ R.cut.left}) =
              R.matching.toEquiv.symm ⟨y.1, hyright⟩ := by
          apply Subtype.ext
          exact hsource
        have happ := congrArg R.matching.toEquiv hsub
        simpa [MatchingAcross.rightEndpoint] using congrArg Subtype.val happ
      have hxmate_eq :
          R.matching.mate x.1 = y.1 := by
        rw [R.matching.mate_of_mem_left hxleft, hy_eq]
      exact False.elim (hxmate (by simpa [hxmate_eq] using hyS))
  · have hxright : x.1 ∈ R.cut.right :=
      (R.cut.mem_right_iff_not_mem_left x.1).2 hxleft
    by_cases hyleft : y.1 ∈ R.cut.left
    · have hsource :
          R.matching.leftEndpoint ⟨x.1, hxright⟩ = y.1 := by
        simpa [hxleft, hyleft] using congrArg Subtype.val hxy
      have hx_eq :
          R.matching.rightEndpoint ⟨y.1, hyleft⟩ = x.1 := by
        have hsub :
            R.matching.toEquiv.symm ⟨x.1, hxright⟩ =
              (⟨y.1, hyleft⟩ : {z : X // z ∈ R.cut.left}) := by
          apply Subtype.ext
          exact hsource
        have happ := congrArg R.matching.toEquiv hsub
        simpa [MatchingAcross.rightEndpoint] using congrArg Subtype.val happ.symm
      have hymate_eq :
          R.matching.mate y.1 = x.1 := by
        rw [R.matching.mate_of_mem_left hyleft, hx_eq]
      exact False.elim (hymate (by simpa [hymate_eq] using hxS))
    · have hyright : y.1 ∈ R.cut.right :=
        (R.cut.mem_right_iff_not_mem_left y.1).2 hyleft
      have hleft :
          R.matching.leftEndpoint ⟨x.1, hxright⟩ =
            R.matching.leftEndpoint ⟨y.1, hyright⟩ := by
        simpa [hxleft, hyleft] using congrArg Subtype.val hxy
      have hright :
          R.matching.rightEndpoint
              ⟨R.matching.leftEndpoint ⟨x.1, hxright⟩,
                R.matching.leftEndpoint_mem ⟨x.1, hxright⟩⟩ =
            R.matching.rightEndpoint
              ⟨R.matching.leftEndpoint ⟨y.1, hyright⟩,
                R.matching.leftEndpoint_mem ⟨y.1, hyright⟩⟩ := by
        have hsub :
            R.matching.toEquiv.symm ⟨x.1, hxright⟩ =
              R.matching.toEquiv.symm ⟨y.1, hyright⟩ := by
          apply Subtype.ext
          exact hleft
        have happ := congrArg R.matching.toEquiv hsub
        exact congrArg Subtype.val happ
      simpa [R.matching.rightEndpoint_leftEndpoint] using hright

/-- The boundary edge associated to an inside endpoint, bundled as an element
of the boundary finset. -/
noncomputable def boundaryEdgeOfInside
    (R : LazyRound X) (S : Finset X) :
    {x : X // x ∈ R.insideWithMateOutside S} →
      {e : {x : X // x ∈ R.cut.left} // e ∈ R.edgeBoundary S} :=
  fun x => ⟨R.boundarySourceOfInside S x,
    R.boundarySourceOfInside_mem_edgeBoundary S x⟩

theorem boundaryEdgeOfInside_injective
    (R : LazyRound X) (S : Finset X) :
    Function.Injective (R.boundaryEdgeOfInside S) := by
  intro x y hxy
  apply R.boundarySourceOfInside_injective S
  exact congrArg Subtype.val hxy

/-- The inside endpoints of crossing matching edges inject into the boundary
edge set, so there are no more of them than boundary edges. -/
theorem insideWithMateOutside_card_le_edgeBoundary_card
    (R : LazyRound X) (S : Finset X) :
    (R.insideWithMateOutside S).card ≤ (R.edgeBoundary S).card := by
  classical
  have hle :=
    Fintype.card_le_of_injective (R.boundaryEdgeOfInside S)
      (R.boundaryEdgeOfInside_injective S)
  have hdomain :
      Fintype.card {x : X // x ∈ R.insideWithMateOutside S} =
        (R.insideWithMateOutside S).card :=
    Fintype.card_coe (R.insideWithMateOutside S)
  have hcodomain :
      Fintype.card {e : {x : X // x ∈ R.cut.left} // e ∈ R.edgeBoundary S} =
        (R.edgeBoundary S).card :=
    Fintype.card_coe (R.edgeBoundary S)
  exact hdomain.symm ▸ hcodomain.symm ▸ hle

end LazyRound

namespace RoundFamily

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- View one indexed round of a `RoundFamily` as a lazy random-walk round. -/
def lazyRound {ι : Type*} (F : RoundFamily X ι) (i : ι) : LazyRound X where
  cut := F.cut i
  matching := F.matching i

/-- Convert a `Fin n`-indexed round family to the ordered list of its lazy
rounds. -/
def toFinList {n : ℕ} (F : RoundFamily X (Fin n)) : List (LazyRound X) :=
  List.ofFn fun i : Fin n => F.lazyRound i

@[simp]
theorem length_toFinList {n : ℕ} (F : RoundFamily X (Fin n)) :
    (F.toFinList).length = n := by
  simp [toFinList]

/-- Turn an ordered list of lazy rounds into the corresponding finite
round family. -/
def ofLazyRoundList (rounds : List (LazyRound X)) :
    RoundFamily X (Fin rounds.length) where
  cut := fun i => (rounds.get i).cut
  matching := fun i => (rounds.get i).matching

@[simp]
theorem lazyRound_ofLazyRoundList
    (rounds : List (LazyRound X)) (i : Fin rounds.length) :
    (ofLazyRoundList rounds).lazyRound i = rounds.get i := by
  rfl

@[simp]
theorem toFinList_ofLazyRoundList
    (rounds : List (LazyRound X)) :
    (ofLazyRoundList rounds).toFinList = rounds := by
  rw [toFinList]
  exact List.ofFn_get (l := rounds)

/-- The boundary of a finite round family is the sigma-type union of the
round-by-round lazy boundaries. -/
theorem edgeBoundary_eq_sigma_lazyRound_edgeBoundary
    {n : ℕ} (F : RoundFamily X (Fin n)) (S : Finset X) :
    F.edgeBoundary S =
      (Finset.univ : Finset (Fin n)).sigma
        (fun i => (F.lazyRound i).edgeBoundary S) := by
  ext e
  simp [RoundFamily.edgeBoundary, RoundFamily.edgeCrosses,
    RoundFamily.edgeSource, RoundFamily.edgeTarget,
    LazyRound.edgeBoundary, LazyRound.edgeCrosses, lazyRound]

/-- Cardinal version of `edgeBoundary_eq_sigma_lazyRound_edgeBoundary`. -/
theorem edgeBoundary_card_eq_sum_lazyRound_edgeBoundary
    {n : ℕ} (F : RoundFamily X (Fin n)) (S : Finset X) :
    (F.edgeBoundary S).card =
      (List.ofFn fun i : Fin n => ((F.lazyRound i).edgeBoundary S).card).sum := by
  classical
  rw [F.edgeBoundary_eq_sigma_lazyRound_edgeBoundary S]
  change
    ((Finset.univ : Finset (Fin n)).sigma
      (fun i => (F.lazyRound i).edgeBoundary S)).val.card =
        (List.ofFn fun i : Fin n => ((F.lazyRound i).edgeBoundary S).card).sum
  rw [Finset.sigma]
  rw [Multiset.card_sigma]
  simp

end RoundFamily

/-- Number of matching-edge instances crossing `S` in a list history.  Parallel
edges from different rounds are counted with multiplicity, as in the
cut-matching game multigraph. -/
def edgeBoundaryCount {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (S : Finset X) : ℕ :=
  (rounds.map fun R => (R.edgeBoundary S).card).sum

@[simp]
theorem edgeBoundaryCount_nil {X : Type u} [Fintype X] [DecidableEq X]
    (S : Finset X) :
    edgeBoundaryCount ([] : List (LazyRound X)) S = 0 := rfl

@[simp]
theorem edgeBoundaryCount_cons {X : Type u} [Fintype X] [DecidableEq X]
    (R : LazyRound X) (rounds : List (LazyRound X)) (S : Finset X) :
    edgeBoundaryCount (R :: rounds) S =
      (R.edgeBoundary S).card + edgeBoundaryCount rounds S := by
  rfl

theorem edgeBoundaryCount_append {X : Type u} [Fintype X] [DecidableEq X]
    (rounds₁ rounds₂ : List (LazyRound X)) (S : Finset X) :
    edgeBoundaryCount (rounds₁ ++ rounds₂) S =
      edgeBoundaryCount rounds₁ S + edgeBoundaryCount rounds₂ S := by
  induction rounds₁ with
  | nil =>
      simp [edgeBoundaryCount]
  | cons R rest ih =>
      simp [edgeBoundaryCount, Nat.add_assoc]

theorem edgeBoundaryCount_le_append {X : Type u} [Fintype X] [DecidableEq X]
    (rounds extra : List (LazyRound X)) (S : Finset X) :
    edgeBoundaryCount rounds S ≤ edgeBoundaryCount (rounds ++ extra) S := by
  rw [edgeBoundaryCount_append]
  omega

theorem edgeBoundaryCount_append_singleton {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (R : LazyRound X) (S : Finset X) :
    edgeBoundaryCount (rounds ++ [R]) S =
      edgeBoundaryCount rounds S + (R.edgeBoundary S).card := by
  simpa using edgeBoundaryCount_append rounds [R] S

/-- Rational edge expansion for a list-history multigraph. -/
def IsEdgeExpanderWith {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) (numerator denominator : ℕ) : Prop :=
  0 < denominator ∧
    ∀ S : Finset X, 0 < S.card →
      2 * S.card ≤ Fintype.card X →
        numerator * S.card ≤ denominator * edgeBoundaryCount rounds S

/-- The half-expansion conclusion used by the grid-minor assembly. -/
def IsHalfEdgeExpander {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) : Prop :=
  IsEdgeExpanderWith rounds 1 2

theorem isHalfEdgeExpander_iff {X : Type u} [Fintype X] [DecidableEq X]
    (rounds : List (LazyRound X)) :
    IsHalfEdgeExpander rounds ↔
      ∀ S : Finset X, 0 < S.card →
        2 * S.card ≤ Fintype.card X →
          S.card ≤ 2 * edgeBoundaryCount rounds S := by
  constructor
  · intro h S hS hhalf
    have hbound := h.2 S hS hhalf
    simpa [IsHalfEdgeExpander, IsEdgeExpanderWith] using hbound
  · intro h
    refine ⟨by decide, ?_⟩
    intro S hS hhalf
    simpa [IsHalfEdgeExpander, IsEdgeExpanderWith] using h S hS hhalf

/-- Appending more matching rounds cannot destroy half-expansion. -/
theorem IsHalfEdgeExpander.append
    {X : Type u} [Fintype X] [DecidableEq X]
    {rounds extra : List (LazyRound X)}
    (h : IsHalfEdgeExpander rounds) :
    IsHalfEdgeExpander (rounds ++ extra) := by
  rw [isHalfEdgeExpander_iff] at h ⊢
  intro S hS hhalf
  have hbase := h S hS hhalf
  have hmono := edgeBoundaryCount_le_append rounds extra S
  omega

namespace RoundFamily

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The edge-boundary count of the ordered lazy-round list agrees with the
edge boundary of the corresponding finite round family. -/
theorem edgeBoundaryCount_toFinList
    {n : ℕ} (F : RoundFamily X (Fin n)) (S : Finset X) :
    edgeBoundaryCount F.toFinList S = (F.edgeBoundary S).card := by
  classical
  rw [F.edgeBoundary_card_eq_sum_lazyRound_edgeBoundary S]
  simp [RoundFamily.toFinList, edgeBoundaryCount, Function.comp_def]

/-- Half expansion for the ordered lazy-round list transfers to the
edge-indexed finite round family. -/
theorem isHalfEdgeExpander_of_toFinList
    {n : ℕ} (F : RoundFamily X (Fin n))
    (h : Lax17Proofs.SimpleGraph.CutMatchingGame.IsHalfEdgeExpander F.toFinList) :
    F.IsHalfEdgeExpander := by
  intro S hS hhalf
  rw [← F.edgeBoundaryCount_toFinList S]
  exact (isHalfEdgeExpander_iff F.toFinList).mp h S hS hhalf

end RoundFamily

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
