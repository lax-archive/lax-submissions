import Lax17Proofs.Source.CutMatchingGameStrategy

namespace Lax17Proofs

universe u v w

/-!
# Peeling step for the cut-matching game

Section 4.2 of the cut-matching-game paper turns expansion on balanced cuts
into expansion on every cut.  This file formalizes the final deterministic
part of that argument in an abstract list-history model: after a peeling phase
has produced a small removed set `T` and the residual graph expands, one last
matching across a bisection containing `T` gives a half-edge-expander.
-/

namespace SimpleGraph
namespace CutMatchingGame


variable {X : Type u} [Fintype X] [DecidableEq X]

namespace LazyRound

/-- A round edge crossing `S`, with both endpoints still inside the residual
vertex set `A`. -/
def inducedEdgeCrosses (R : LazyRound X) (A S : Finset X)
    (x : {x : X // x ∈ R.cut.left}) : Prop :=
  x.1 ∈ A ∧ R.matching.rightEndpoint x ∈ A ∧ R.edgeCrosses S x

instance inducedEdgeCrossesDecidable (R : LazyRound X) (A S : Finset X) :
    DecidablePred (R.inducedEdgeCrosses A S) := by
  intro x
  unfold inducedEdgeCrosses
  infer_instance

/-- Boundary edges of `S` in the subgraph induced by a residual vertex set
`A`, for one matching round. -/
def inducedEdgeBoundary (R : LazyRound X) (A S : Finset X) :
    Finset {x : X // x ∈ R.cut.left} :=
  Finset.univ.filter (R.inducedEdgeCrosses A S)

@[simp]
theorem mem_inducedEdgeBoundary {R : LazyRound X} {A S : Finset X}
    {x : {x : X // x ∈ R.cut.left}} :
    x ∈ R.inducedEdgeBoundary A S ↔ R.inducedEdgeCrosses A S x := by
  simp [inducedEdgeBoundary]

theorem inducedEdgeBoundary_subset_edgeBoundary
    (R : LazyRound X) (A S : Finset X) :
    R.inducedEdgeBoundary A S ⊆ R.edgeBoundary S := by
  intro e he
  rw [mem_edgeBoundary]
  exact (mem_inducedEdgeBoundary.mp he).2.2

theorem inducedEdgeBoundary_card_le_edgeBoundary
    (R : LazyRound X) (A S : Finset X) :
    (R.inducedEdgeBoundary A S).card ≤ (R.edgeBoundary S).card :=
  Finset.card_le_card (R.inducedEdgeBoundary_subset_edgeBoundary A S)

/-- Inside an induced vertex set `A`, the boundary of `S` is the same as the
boundary of its complement in `A`. -/
theorem inducedEdgeBoundary_sdiff
    (R : LazyRound X) (A S : Finset X) :
    R.inducedEdgeBoundary A (A \ S) = R.inducedEdgeBoundary A S := by
  ext e
  rw [mem_inducedEdgeBoundary, mem_inducedEdgeBoundary]
  constructor
  · intro h
    rcases h with ⟨hsrcA, htgtA, hcross⟩
    refine ⟨hsrcA, htgtA, ?_⟩
    rcases hcross with hcross | hcross
    · have hsrcNotS : e.1 ∉ S := (Finset.mem_sdiff.mp hcross.1).2
      have htgtS : R.matching.rightEndpoint e ∈ S := by
        by_contra htgtNotS
        exact hcross.2 (Finset.mem_sdiff.mpr ⟨htgtA, htgtNotS⟩)
      exact Or.inr ⟨htgtS, hsrcNotS⟩
    · have htgtNotS : R.matching.rightEndpoint e ∉ S :=
        (Finset.mem_sdiff.mp hcross.1).2
      have hsrcS : e.1 ∈ S := by
        by_contra hsrcNotS
        exact hcross.2 (Finset.mem_sdiff.mpr ⟨hsrcA, hsrcNotS⟩)
      exact Or.inl ⟨hsrcS, htgtNotS⟩
  · intro h
    rcases h with ⟨hsrcA, htgtA, hcross⟩
    refine ⟨hsrcA, htgtA, ?_⟩
    rcases hcross with hcross | hcross
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨htgtA, hcross.2⟩, by
        intro hsrcComp
        exact (Finset.mem_sdiff.mp hsrcComp).2 hcross.1⟩
    · exact Or.inl ⟨Finset.mem_sdiff.mpr ⟨hsrcA, hcross.2⟩, by
        intro htgtComp
        exact (Finset.mem_sdiff.mp htgtComp).2 hcross.1⟩

end LazyRound

/-- Boundary count inside a residual vertex set `A`. -/
def inducedBoundaryCount (rounds : List (LazyRound X))
    (A S : Finset X) : ℕ :=
  (rounds.map fun R => (R.inducedEdgeBoundary A S).card).sum

@[simp]
theorem inducedBoundaryCount_nil (A S : Finset X) :
    inducedBoundaryCount ([] : List (LazyRound X)) A S = 0 := rfl

@[simp]
theorem inducedBoundaryCount_cons
    (R : LazyRound X) (rounds : List (LazyRound X)) (A S : Finset X) :
    inducedBoundaryCount (R :: rounds) A S =
      (R.inducedEdgeBoundary A S).card + inducedBoundaryCount rounds A S := by
  rfl

theorem inducedBoundaryCount_le_edgeBoundaryCount
    (rounds : List (LazyRound X)) (A S : Finset X) :
    inducedBoundaryCount rounds A S ≤ edgeBoundaryCount rounds S := by
  induction rounds with
  | nil =>
      simp
  | cons R rest ih =>
      simp [inducedBoundaryCount, edgeBoundaryCount]
      exact Nat.add_le_add (R.inducedEdgeBoundary_card_le_edgeBoundary A S) ih

theorem inducedBoundaryCount_le_edgeBoundaryCount_append
    (rounds : List (LazyRound X)) (Final : LazyRound X)
    (A S : Finset X) :
    inducedBoundaryCount rounds A S ≤
      edgeBoundaryCount (rounds ++ [Final]) S := by
  exact (inducedBoundaryCount_le_edgeBoundaryCount rounds A S).trans
    (edgeBoundaryCount_le_append rounds [Final] S)

/-- Induced boundary count is unchanged by complementing inside the induced
vertex set. -/
theorem inducedBoundaryCount_sdiff
    (rounds : List (LazyRound X)) (A S : Finset X) :
    inducedBoundaryCount rounds A (A \ S) =
      inducedBoundaryCount rounds A S := by
  induction rounds with
  | nil =>
      simp
  | cons R rest ih =>
      simp [inducedBoundaryCount, LazyRound.inducedEdgeBoundary_sdiff]

/-- The residual vertices after removing `T`. -/
def residualVertices (T : Finset X) : Finset X :=
  vertexComplement T

@[simp]
theorem mem_residualVertices {T : Finset X} {x : X} :
    x ∈ residualVertices T ↔ x ∉ T := by
  simp [residualVertices]

/-- The part of `W` that remains after removing `T`. -/
def residualPart (T W : Finset X) : Finset X :=
  W ∩ residualVertices T

theorem residualPart_subset_residualVertices (T W : Finset X) :
    residualPart T W ⊆ residualVertices T := by
  intro x hx
  exact (Finset.mem_inter.mp hx).2

theorem residualPart_card_le_card (T W : Finset X) :
    (residualPart T W).card ≤ W.card := by
  exact Finset.card_le_card (by
    intro x hx
    exact (Finset.mem_inter.mp hx).1)

theorem inter_removed_add_residualPart_card
    (T W : Finset X) :
    (W ∩ T).card + (residualPart T W).card = W.card := by
  classical
  have hdisj : Disjoint (W ∩ T) (residualPart T W) := by
    rw [Finset.disjoint_left]
    intro x hxT hxR
    exact (mem_residualVertices.mp (Finset.mem_inter.mp hxR).2)
      (Finset.mem_inter.mp hxT).2
  have hunion : (W ∩ T) ∪ residualPart T W = W := by
    ext x
    by_cases hxW : x ∈ W <;> by_cases hxT : x ∈ T <;>
      simp [residualPart, residualVertices, vertexComplement, hxW, hxT]
  calc
    (W ∩ T).card + (residualPart T W).card =
        ((W ∩ T) ∪ residualPart T W).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = W.card := by rw [hunion]

theorem residualVertices_card (T : Finset X) :
    (residualVertices T).card = Fintype.card X - T.card := by
  unfold residualVertices vertexComplement
  rw [Finset.card_sdiff_of_subset]
  · rw [Finset.card_univ]
  · intro x _; exact Finset.mem_univ x

theorem residual_complement_four_mul_lower
    {T W : Finset X}
    (hTsmall : 4 * T.card < Fintype.card X)
    (hWhalf : 2 * W.card ≤ Fintype.card X) :
    W.card ≤
      4 * ((residualVertices T).card - (residualPart T W).card) := by
  have hpart := residualPart_card_le_card T W
  rw [residualVertices_card]
  omega

/-- Residual expansion at threshold `2`: every nontrivial residual cut has at
least twice the smaller side in induced boundary. -/
def ResidualExpandsByTwo
    (rounds : List (LazyRound X)) (T : Finset X) : Prop :=
  ∀ S : Finset X,
    S ⊆ residualVertices T →
      2 * Nat.min S.card ((residualVertices T).card - S.card) ≤
        inducedBoundaryCount rounds (residualVertices T) S

theorem inducedBoundaryCount_residualPart_le_edgeBoundaryCount
    (rounds : List (LazyRound X)) (T W : Finset X) :
    inducedBoundaryCount rounds (residualVertices T) (residualPart T W) ≤
      edgeBoundaryCount rounds W := by
  induction rounds with
  | nil =>
      simp
  | cons R rest ih =>
      have hround :
          (R.inducedEdgeBoundary (residualVertices T) (residualPart T W)).card ≤
            (R.edgeBoundary W).card := by
        refine Finset.card_le_card ?_
        intro e he
        rw [LazyRound.mem_edgeBoundary]
        have hc := LazyRound.mem_inducedEdgeBoundary.mp he
        rcases hc with ⟨hsrcRes, htgtRes, hcross⟩
        rcases hcross with hcross | hcross
        · exact Or.inl ⟨(Finset.mem_inter.mp hcross.1).1, by
            intro htgtW
            exact hcross.2 (Finset.mem_inter.mpr ⟨htgtW, htgtRes⟩)⟩
        · exact Or.inr ⟨(Finset.mem_inter.mp hcross.1).1, by
            intro hsrcW
            exact hcross.2 (Finset.mem_inter.mpr ⟨hsrcW, hsrcRes⟩)⟩
      change
        (R.inducedEdgeBoundary (residualVertices T) (residualPart T W)).card +
            inducedBoundaryCount rest (residualVertices T) (residualPart T W) ≤
          (R.edgeBoundary W).card + edgeBoundaryCount rest W
      exact Nat.add_le_add hround ih

namespace LazyRound

/-- If `U` is a residual set outside `T`, every boundary edge of `T ∪ U`
either was already a boundary edge of `T`, or is an induced residual boundary
edge of `U`. -/
theorem edgeBoundary_union_subset_boundary_union_induced
    (R : LazyRound X) (T U : Finset X) :
    R.edgeBoundary (T ∪ U) ⊆
      R.edgeBoundary T ∪ R.inducedEdgeBoundary (residualVertices T) U := by
  intro e he
  rw [Finset.mem_union]
  have hcross := LazyRound.mem_edgeBoundary.mp he
  by_cases hcrossT : R.edgeCrosses T e
  · exact Or.inl (LazyRound.mem_edgeBoundary.mpr hcrossT)
  · right
    rw [LazyRound.mem_inducedEdgeBoundary]
    have hsrcRes : e.1 ∈ residualVertices T := by
      rw [mem_residualVertices]
      intro hsrcT
      rcases hcross with hcross | hcross
      · exact hcrossT (Or.inl ⟨hsrcT, by
          intro htgtT
          exact hcross.2 (Finset.mem_union.mpr (Or.inl htgtT))⟩)
      · exact hcross.2 (Finset.mem_union.mpr (Or.inl hsrcT))
    have htgtRes : R.matching.rightEndpoint e ∈ residualVertices T := by
      rw [mem_residualVertices]
      intro htgtT
      rcases hcross with hcross | hcross
      · exact hcross.2 (Finset.mem_union.mpr (Or.inl htgtT))
      · exact hcrossT (Or.inr ⟨htgtT, by
          intro hsrcT
          exact hcross.2 (Finset.mem_union.mpr (Or.inl hsrcT))⟩)
    refine ⟨hsrcRes, htgtRes, ?_⟩
    rcases hcross with hcross | hcross
    · rcases Finset.mem_union.mp hcross.1 with hsrcT | hsrcU
      · exact False.elim (mem_residualVertices.mp hsrcRes hsrcT)
      · refine Or.inl ⟨hsrcU, ?_⟩
        intro htgtU
        exact hcross.2 (Finset.mem_union.mpr (Or.inr htgtU))
    · rcases Finset.mem_union.mp hcross.1 with htgtT | htgtU
      · exact False.elim (mem_residualVertices.mp htgtRes htgtT)
      · refine Or.inr ⟨htgtU, ?_⟩
        intro hsrcU
        exact hcross.2 (Finset.mem_union.mpr (Or.inr hsrcU))

/-- Cardinal form of `edgeBoundary_union_subset_boundary_union_induced`. -/
theorem edgeBoundary_union_card_le_boundary_add_induced
    (R : LazyRound X) (T U : Finset X) :
    (R.edgeBoundary (T ∪ U)).card ≤
      (R.edgeBoundary T).card +
        (R.inducedEdgeBoundary (residualVertices T) U).card := by
  exact
    (Finset.card_le_card (R.edgeBoundary_union_subset_boundary_union_induced T U)).trans
      (Finset.card_union_le (R.edgeBoundary T)
        (R.inducedEdgeBoundary (residualVertices T) U))

/-- If `U` lies in the residual outside `T`, every boundary edge of `U`
either is induced inside the residual graph or crosses the already removed set
`T`. -/
theorem edgeBoundary_residual_subset_boundary_union_induced
    (R : LazyRound X) {T U : Finset X}
    (hU : U ⊆ residualVertices T) :
    R.edgeBoundary U ⊆
      R.edgeBoundary T ∪ R.inducedEdgeBoundary (residualVertices T) U := by
  intro e he
  rw [Finset.mem_union]
  have hcross := LazyRound.mem_edgeBoundary.mp he
  by_cases hsrcRes : e.1 ∈ residualVertices T
  · by_cases htgtRes : R.matching.rightEndpoint e ∈ residualVertices T
    · right
      rw [LazyRound.mem_inducedEdgeBoundary]
      exact ⟨hsrcRes, htgtRes, hcross⟩
    · left
      rw [LazyRound.mem_edgeBoundary]
      have hsrcNotT : e.1 ∉ T := mem_residualVertices.mp hsrcRes
      have htgtT : R.matching.rightEndpoint e ∈ T := by
        by_contra htgtNotT
        exact htgtRes (mem_residualVertices.mpr htgtNotT)
      rcases hcross with hcross | hcross
      · exact Or.inr ⟨htgtT, hsrcNotT⟩
      · exact False.elim (htgtRes (hU hcross.1))
  · left
    rw [LazyRound.mem_edgeBoundary]
    have hsrcT : e.1 ∈ T := by
      by_contra hsrcNotT
      exact hsrcRes (mem_residualVertices.mpr hsrcNotT)
    rcases hcross with hcross | hcross
    · exact False.elim (hsrcRes (hU hcross.1))
    · exact Or.inl ⟨hsrcT, mem_residualVertices.mp (hU hcross.1)⟩

/-- Cardinal form of `edgeBoundary_residual_subset_boundary_union_induced`. -/
theorem edgeBoundary_residual_card_le_boundary_add_induced
    (R : LazyRound X) {T U : Finset X}
    (hU : U ⊆ residualVertices T) :
    (R.edgeBoundary U).card ≤
      (R.edgeBoundary T).card +
        (R.inducedEdgeBoundary (residualVertices T) U).card := by
  exact
    (Finset.card_le_card (R.edgeBoundary_residual_subset_boundary_union_induced hU)).trans
      (Finset.card_union_le (R.edgeBoundary T)
        (R.inducedEdgeBoundary (residualVertices T) U))

end LazyRound

/-- Boundary accounting for appending one peeled residual set. -/
theorem edgeBoundaryCount_union_le_boundary_add_induced
    (rounds : List (LazyRound X)) (T U : Finset X) :
    edgeBoundaryCount rounds (T ∪ U) ≤
      edgeBoundaryCount rounds T +
        inducedBoundaryCount rounds (residualVertices T) U := by
  induction rounds with
  | nil =>
      simp
  | cons R rest ih =>
      change
        (R.edgeBoundary (T ∪ U)).card +
            edgeBoundaryCount rest (T ∪ U) ≤
          (R.edgeBoundary T).card + edgeBoundaryCount rest T +
            ((R.inducedEdgeBoundary (residualVertices T) U).card +
              inducedBoundaryCount rest (residualVertices T) U)
      have hround := R.edgeBoundary_union_card_le_boundary_add_induced T U
      omega

/-- Boundary accounting for a peeled residual set itself. -/
theorem edgeBoundaryCount_residual_le_boundary_add_induced
    (rounds : List (LazyRound X)) {T U : Finset X}
    (hU : U ⊆ residualVertices T) :
    edgeBoundaryCount rounds U ≤
      edgeBoundaryCount rounds T +
        inducedBoundaryCount rounds (residualVertices T) U := by
  induction rounds with
  | nil =>
      simp
  | cons R rest ih =>
      change
        (R.edgeBoundary U).card + edgeBoundaryCount rest U ≤
          (R.edgeBoundary T).card + edgeBoundaryCount rest T +
            ((R.inducedEdgeBoundary (residualVertices T) U).card +
              inducedBoundaryCount rest (residualVertices T) U)
      have hround := R.edgeBoundary_residual_card_le_boundary_add_induced hU
      omega

/-- The boundary count of the empty set is zero for every history. -/
@[simp]
theorem edgeBoundaryCount_empty_set (rounds : List (LazyRound X)) :
    edgeBoundaryCount rounds (∅ : Finset X) = 0 := by
  induction rounds with
  | nil =>
      simp
  | cons R rest ih =>
      simp [edgeBoundaryCount]

/-- A set with boundary at most half the `4`-expansion lower bound cannot be
`1/4`-balanced. -/
theorem low_boundary_set_card_lt_quarter_of_balancedExpander_four
    {rounds : List (LazyRound X)} {T : Finset X}
    (hbal : IsBalancedEdgeExpanderWith (X := X) rounds 1 4 4 1)
    (hboundary : edgeBoundaryCount rounds T ≤ 2 * T.card)
    (hhalf : 2 * T.card ≤ Fintype.card X)
    (hpos : 0 < T.card) :
    4 * T.card < Fintype.card X := by
  by_contra hnot
  have hlarge : 1 * Fintype.card X ≤ 4 * T.card := by
    simpa using Nat.le_of_not_gt hnot
  have hb := hbal.2 T hlarge hhalf
  omega

/-- A residual cut eligible for the deterministic peeling process at
threshold `2`.  The set is nonempty, lies in the current residual vertex set,
uses at most half of that residual set, and has induced residual boundary at
most `2 |U|`. -/
structure ResidualSparseCut
    (rounds : List (LazyRound X)) (T U : Finset X) : Prop where
  subset_residual : U ⊆ residualVertices T
  nonempty : 0 < U.card
  half_residual : 2 * U.card ≤ (residualVertices T).card
  boundary_le : inducedBoundaryCount rounds (residualVertices T) U ≤ 2 * U.card

/-- Finset disjointness of the current removed set and a residual sparse cut. -/
theorem ResidualSparseCut.disjoint_removed
    {rounds : List (LazyRound X)} {T U : Finset X}
    (h : ResidualSparseCut rounds T U) :
    Disjoint T U := by
  rw [Finset.disjoint_left]
  intro x hxT hxU
  exact mem_residualVertices.mp (h.subset_residual hxU) hxT

/-- Cardinal additivity when adjoining a residual sparse cut. -/
theorem ResidualSparseCut.card_union
    {rounds : List (LazyRound X)} {T U : Finset X}
    (h : ResidualSparseCut rounds T U) :
    (T ∪ U).card = T.card + U.card := by
  rw [Finset.card_union_of_disjoint (h.disjoint_removed)]

/-- A possible history of the Figure 4 peeling loop, represented only by the
accumulated removed vertex set. -/
inductive PeelingHistory (rounds : List (LazyRound X)) : Finset X → Prop where
  | empty : PeelingHistory rounds ∅
  | step {T U : Finset X}
      (hist : PeelingHistory rounds T)
      (sparse : ResidualSparseCut rounds T U) :
      PeelingHistory rounds (T ∪ U)

namespace PeelingHistory

/-- Every nonempty accumulated removed set in a peeling history has original
boundary at most twice its cardinality. -/
theorem boundary_le_two_card
    {rounds : List (LazyRound X)} {T : Finset X}
    (hist : PeelingHistory rounds T) :
    edgeBoundaryCount rounds T ≤ 2 * T.card := by
  induction hist with
  | empty =>
      simp
  | @step T U hist sparse ih =>
      have hboundary :=
        edgeBoundaryCount_union_le_boundary_add_induced rounds T U
      have hcard := sparse.card_union
      have hsparse := sparse.boundary_le
      rw [hcard]
      omega

/-- Under balanced expansion `4` on all `1/4`-balanced cuts, every nonempty
peeled union of size at most half the ground set is smaller than `n/4`. -/
theorem card_lt_quarter_of_half
    {rounds : List (LazyRound X)} {T : Finset X}
    (hbal : IsBalancedEdgeExpanderWith (X := X) rounds 1 4 4 1)
    (hist : PeelingHistory rounds T)
    (hhalf : 2 * T.card ≤ Fintype.card X)
    (hpos : 0 < T.card) :
    4 * T.card < Fintype.card X :=
  low_boundary_set_card_lt_quarter_of_balancedExpander_four
    hbal hist.boundary_le_two_card hhalf hpos

/-- Lemma 4.7 in strengthened constants: if all `1/4`-balanced cuts in the
original matching union have expansion at least `4`, then every finite peeling
history at residual threshold `2` removes fewer than one quarter of the
vertices. -/
theorem card_lt_quarter
    {rounds : List (LazyRound X)} {T : Finset X}
    (hbal : IsBalancedEdgeExpanderWith (X := X) rounds 1 4 4 1)
    (hist : PeelingHistory rounds T)
    (hn : 0 < Fintype.card X) :
    4 * T.card < Fintype.card X := by
  induction hist with
  | empty =>
      simp
      exact hn
  | @step T U hist sparse ih =>
      have hcard := sparse.card_union
      have hposUnion : 0 < (T ∪ U).card := by
        have hUpos := sparse.nonempty
        rw [hcard]
        omega
      by_cases hhalfUnion : 2 * (T ∪ U).card ≤ Fintype.card X
      · exact
          card_lt_quarter_of_half (X := X) hbal
            (PeelingHistory.step hist sparse) hhalfUnion hposUnion
      · have hgtHalf : Fintype.card X < 2 * (T ∪ U).card :=
          Nat.lt_of_not_ge hhalfUnion
        have hUhalf : 2 * U.card ≤ Fintype.card X := by
          have hrescard := residualVertices_card T
          have hsparseHalf := sparse.half_residual
          omega
        have hUlarge : 1 * Fintype.card X ≤ 4 * U.card := by
          omega
        have hTltU : T.card < U.card := by
          omega
        have hboundaryU_base :=
          edgeBoundaryCount_residual_le_boundary_add_induced
            rounds sparse.subset_residual
        have hboundaryT := hist.boundary_le_two_card
        have hboundaryU_sparse := sparse.boundary_le
        have hboundaryU :
            edgeBoundaryCount rounds U ≤ 2 * T.card + 2 * U.card := by
          omega
        have hbalancedU := hbal.2 U hUlarge hUhalf
        omega

end PeelingHistory

/-- All removed sets obtainable by a peeling history. -/
noncomputable def peelingHistorySets
    (rounds : List (LazyRound X)) : Finset (Finset X) :=
  by
    classical
    exact (Finset.univ : Finset (Finset X)).filter
      (fun T => PeelingHistory rounds T)

theorem mem_peelingHistorySets
    {rounds : List (LazyRound X)} {T : Finset X} :
    T ∈ peelingHistorySets (X := X) rounds ↔ PeelingHistory rounds T := by
  classical
  simp [peelingHistorySets]

/-- A maximal finite peeling history exists.  This is the nonconstructive
formal version of running the Figure 4 while-loop until no eligible residual
sparse cut remains. -/
theorem exists_maximal_peelingHistory
    (rounds : List (LazyRound X)) :
    ∃ T : Finset X,
      PeelingHistory rounds T ∧
        ∀ U : Finset X, ¬ ResidualSparseCut rounds T U := by
  classical
  have hnonempty :
      (peelingHistorySets (X := X) rounds).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [mem_peelingHistorySets]
    exact PeelingHistory.empty
  rcases Finset.exists_max_image
      (peelingHistorySets (X := X) rounds)
      (fun T : Finset X => T.card) hnonempty with
    ⟨T, hTmem, hmax⟩
  have hhist : PeelingHistory rounds T :=
    mem_peelingHistorySets.mp hTmem
  refine ⟨T, hhist, ?_⟩
  intro U hsparse
  have hnext : T ∪ U ∈ peelingHistorySets (X := X) rounds := by
    rw [mem_peelingHistorySets]
    exact PeelingHistory.step hhist hsparse
  have hle := hmax (T ∪ U) hnext
  have hcard := hsparse.card_union
  have hpos := hsparse.nonempty
  omega

/-- If the maximal peeling loop has no eligible residual sparse cut left,
then the remaining residual graph expands at threshold `2`. -/
theorem residualExpandsByTwo_of_no_residualSparseCut
    {rounds : List (LazyRound X)} {T : Finset X}
    (hmax : ∀ U : Finset X, ¬ ResidualSparseCut rounds T U) :
    ResidualExpandsByTwo rounds T := by
  intro S hS
  by_contra hnot
  have hbad :
      inducedBoundaryCount rounds (residualVertices T) S <
        2 * Nat.min S.card ((residualVertices T).card - S.card) :=
    Nat.lt_of_not_ge hnot
  have hSleA : S.card ≤ (residualVertices T).card :=
    Finset.card_le_card hS
  by_cases hle :
      S.card ≤ (residualVertices T).card - S.card
  · have hmin :
        Nat.min S.card ((residualVertices T).card - S.card) = S.card :=
      Nat.min_eq_left hle
    have hpos : 0 < S.card := by
      by_contra hzero
      have hScard : S.card = 0 := Nat.eq_zero_of_not_pos hzero
      omega
    have hhalf : 2 * S.card ≤ (residualVertices T).card := by
      omega
    have hsparse : ResidualSparseCut rounds T S := {
      subset_residual := hS
      nonempty := hpos
      half_residual := hhalf
      boundary_le := by
        rw [hmin] at hbad
        omega }
    exact hmax S hsparse
  · let U := residualVertices T \ S
    have hUcard : U.card = (residualVertices T).card - S.card := by
      exact Finset.card_sdiff_of_subset hS
    have hle' :
        (residualVertices T).card - S.card ≤ S.card :=
      Nat.le_of_not_ge hle
    have hmin :
        Nat.min S.card ((residualVertices T).card - S.card) =
          (residualVertices T).card - S.card :=
      Nat.min_eq_right hle'
    have hpos : 0 < U.card := by
      by_contra hzero
      have hUzero : U.card = 0 := Nat.eq_zero_of_not_pos hzero
      omega
    have hhalf : 2 * U.card ≤ (residualVertices T).card := by
      omega
    have hsparse : ResidualSparseCut rounds T U := {
      subset_residual := by
        intro x hx
        exact (Finset.mem_sdiff.mp hx).1
      nonempty := hpos
      half_residual := hhalf
      boundary_le := by
        change inducedBoundaryCount rounds (residualVertices T)
            (residualVertices T \ S) ≤ 2 * U.card
        rw [inducedBoundaryCount_sdiff rounds (residualVertices T) S]
        rw [hmin] at hbad
        omega }
    exact hmax U hsparse

/-- The deterministic peeling loop produces a small removed set whose
residual graph expands at threshold `2`, provided the starting history has
expansion at least `4` on every `1/4`-balanced cut. -/
theorem exists_small_residualExpandsByTwo_of_balancedExpander_four
    {rounds : List (LazyRound X)}
    (hbal : IsBalancedEdgeExpanderWith (X := X) rounds 1 4 4 1)
    (hn : 0 < Fintype.card X) :
    ∃ T : Finset X,
      4 * T.card < Fintype.card X ∧ ResidualExpandsByTwo rounds T := by
  rcases exists_maximal_peelingHistory (X := X) rounds with
    ⟨T, hhist, hmax⟩
  exact ⟨T, PeelingHistory.card_lt_quarter (X := X) hbal hhist hn,
    residualExpandsByTwo_of_no_residualSparseCut hmax⟩

theorem residual_expansion_gives_boundary_for_large_residual_part
    {rounds : List (LazyRound X)} {Final : LazyRound X}
    {T W : Finset X}
    (hres : ResidualExpandsByTwo rounds T)
    (hTsmall : 4 * T.card < Fintype.card X)
    (hWhalf : 2 * W.card ≤ Fintype.card X)
    (hlargePart : W.card ≤ 4 * (residualPart T W).card) :
    W.card ≤
      2 * edgeBoundaryCount (rounds ++ [Final]) W := by
  have hresBound :=
    hres (residualPart T W) (residualPart_subset_residualVertices T W)
  have hcomp :
      W.card ≤
        4 * ((residualVertices T).card - (residualPart T W).card) :=
    residual_complement_four_mul_lower hTsmall hWhalf
  have hpartLower : W.card ≤ 4 * (residualPart T W).card := hlargePart
  have hminLower :
      W.card ≤ 4 *
        Nat.min (residualPart T W).card
          ((residualVertices T).card - (residualPart T W).card) := by
    by_cases hle :
        (residualPart T W).card ≤
          (residualVertices T).card - (residualPart T W).card
    · simpa [Nat.min_eq_left hle] using hpartLower
    · simpa [Nat.min_eq_right (Nat.le_of_not_ge hle)] using hcomp
  have hinduced_le :
      inducedBoundaryCount rounds (residualVertices T) (residualPart T W) ≤
        edgeBoundaryCount (rounds ++ [Final]) W := by
    have hle_rounds :=
      inducedBoundaryCount_residualPart_le_edgeBoundaryCount rounds T W
    exact hle_rounds.trans (edgeBoundaryCount_le_append rounds [Final] W)
  omega

namespace LazyRound

/-- Vertices of `W ∩ T` whose mate lies outside `W`. -/
noncomputable def removedInsideWithMateOutside
    (R : LazyRound X) (T W : Finset X) : Finset X :=
  (W ∩ T).filter fun x => R.matching.mate x ∉ W

theorem mem_removedInsideWithMateOutside
    {R : LazyRound X} {T W : Finset X} {x : X} :
    x ∈ R.removedInsideWithMateOutside T W ↔
      x ∈ W ∧ x ∈ T ∧ R.matching.mate x ∉ W := by
  constructor
  · intro hx
    have h := Finset.mem_filter.mp hx
    exact ⟨(Finset.mem_inter.mp h.1).1, (Finset.mem_inter.mp h.1).2, h.2⟩
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr ⟨hx.1, hx.2.1⟩, hx.2.2⟩

theorem removedInsideWithMateOutside_subset_insideWithMateOutside
    (R : LazyRound X) (T W : Finset X) :
    R.removedInsideWithMateOutside T W ⊆ R.insideWithMateOutside W := by
  intro x hx
  rw [mem_insideWithMateOutside]
  exact ⟨(R.mem_removedInsideWithMateOutside.mp hx).1,
    (R.mem_removedInsideWithMateOutside.mp hx).2.2⟩

theorem removedInsideWithMateOutside_card_le_edgeBoundary
    (R : LazyRound X) (T W : Finset X) :
    (R.removedInsideWithMateOutside T W).card ≤ (R.edgeBoundary W).card :=
  (Finset.card_le_card (R.removedInsideWithMateOutside_subset_insideWithMateOutside T W)).trans
    (R.insideWithMateOutside_card_le_edgeBoundary_card W)

end LazyRound

theorem final_matching_gives_boundary_for_large_removed_part
    {Final : LazyRound X} {T W : Finset X}
    (hTleft : T ⊆ Final.cut.left)
    (hsmallPart : 4 * (residualPart T W).card < W.card) :
    W.card ≤ 2 * (Final.edgeBoundary W).card := by
  classical
  let Bad : Finset X :=
    (W ∩ T).filter fun x => Final.matching.mate x ∈ W
  have hbad_subset_residual : Bad.image Final.matching.mate ⊆ residualPart T W := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxBad, hxy⟩
    have hxWT : x ∈ W ∩ T := (Finset.mem_filter.mp hxBad).1
    have hyW : y ∈ W := by
      rw [← hxy]
      exact (Finset.mem_filter.mp hxBad).2
    have hxT : x ∈ T := (Finset.mem_inter.mp hxWT).2
    have hxleft : x ∈ Final.cut.left := hTleft hxT
    have hymateRight : Final.matching.mate x ∈ Final.cut.right :=
      Final.matching.mate_mem_right_of_mem_left hxleft
    have hynotT : y ∉ T := by
      intro hyT
      have hyleft : y ∈ Final.cut.left := hTleft hyT
      exact Final.cut.not_mem_left_of_mem_right (by simpa [hxy] using hymateRight) hyleft
    exact Finset.mem_inter.mpr ⟨hyW, mem_residualVertices.mpr hynotT⟩
  have hbad_card_le :
      Bad.card ≤ (residualPart T W).card := by
    have himage_card : (Bad.image Final.matching.mate).card = Bad.card := by
      rw [Finset.card_image_iff]
      intro x hx y hy hxy
      exact Final.matching.mate_injective hxy
    rw [← himage_card]
    exact Finset.card_le_card hbad_subset_residual
  have hgood_card :
      W.card ≤ 2 * (Final.removedInsideWithMateOutside T W).card := by
    have hsplit :
        (Final.removedInsideWithMateOutside T W).card + Bad.card =
          (W ∩ T).card := by
      have h :=
        Finset.card_filter_add_card_filter_not
          (s := W ∩ T) (p := fun x => Final.matching.mate x ∉ W)
      simpa [LazyRound.removedInsideWithMateOutside, Bad] using h
    have hpart := inter_removed_add_residualPart_card T W
    omega
  exact hgood_card.trans
    (Nat.mul_le_mul_left 2
      (Final.removedInsideWithMateOutside_card_le_edgeBoundary T W))

/-- Final deterministic step for the half-expander variant of Section 4.2.
If the removed set is smaller than one quarter of the ground set and the
residual graph expands by `2`, then one final matching across a bisection
containing the removed set makes every cut expand by at least `1/2`. -/
theorem isHalfEdgeExpander_of_residualExpandsByTwo_and_final_matching
    {rounds : List (LazyRound X)} {Final : LazyRound X} {T : Finset X}
    (hTsmall : 4 * T.card < Fintype.card X)
    (hres : ResidualExpandsByTwo rounds T)
    (hTleft : T ⊆ Final.cut.left) :
    IsHalfEdgeExpander (rounds ++ [Final]) := by
  rw [isHalfEdgeExpander_iff]
  intro W hWpos hWhalf
  by_cases hlargePart : W.card ≤ 4 * (residualPart T W).card
  · exact residual_expansion_gives_boundary_for_large_residual_part
      (Final := Final) hres hTsmall hWhalf hlargePart
  · have hsmallPart : 4 * (residualPart T W).card < W.card :=
      Nat.lt_of_not_ge hlargePart
    have hfinal :=
      final_matching_gives_boundary_for_large_removed_part
        (Final := Final) hTleft hsmallPart
    have hmono : (Final.edgeBoundary W).card ≤
        edgeBoundaryCount (rounds ++ [Final]) W := by
      rw [edgeBoundaryCount_append_singleton]
      omega
    omega

/-- After the balanced-expander phases and peeling, one final matching across
a bisection containing the removed set gives a half-expander. -/
theorem exists_final_bisection_halfExpander_of_balancedExpander_four
    {rounds : List (LazyRound X)} {m : ℕ}
    (hm : 2 * m = Fintype.card X)
    (hbal : IsBalancedEdgeExpanderWith (X := X) rounds 1 4 4 1)
    (hn : 0 < Fintype.card X)
    (responder : SequentialResponder X) (finalIndex : ℕ) :
    ∃ B : Bisection X,
      IsHalfEdgeExpander
        (rounds ++ [LazyRound.ofResponder responder finalIndex B]) := by
  rcases exists_small_residualExpandsByTwo_of_balancedExpander_four
      (X := X) hbal hn with
    ⟨T, hTsmall, hres⟩
  have hTle : T.card ≤ m := by
    omega
  rcases Bisection.exists_leftHalf_superset
      (X := X) (T := T) (m := m) hTle hm with
    ⟨B, hTleft, _hBcard⟩
  refine ⟨B, ?_⟩
  exact
    isHalfEdgeExpander_of_residualExpandsByTwo_and_final_matching
      (X := X) (rounds := rounds)
      (Final := LazyRound.ofResponder responder finalIndex B)
      (T := T) hTsmall hres hTleft

/-- Abstract Section 4 cut-player theorem with explicit constants at the list
level: sixteen `c = 1/4` entropy phases, followed by the deterministic peeling
round, produce a half-edge-expander.  The only quantitative hypothesis is the
single-phase entropy budget. -/
theorem exists_list_halfExpander_of_sixteen_phases_and_peeling
    {m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ)
    (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (k : ℝ)) :
    ∃ rounds : List (LazyRound X),
      rounds.length = 16 * k + 1 ∧ IsHalfEdgeExpander rounds := by
  let phaseRounds :=
    sparseCutPlayMany (X := X) 1 4 m hm responder k 16
  have hbal :
      IsBalancedEdgeExpanderWith (X := X) phaseRounds 1 4 4 1 := by
    simpa [phaseRounds] using
      sparseCutPlayMany_balancedExpander_four_of_potential_budget
        (X := X) hm responder k hn hbudget
  rcases exists_final_bisection_halfExpander_of_balancedExpander_four
      (X := X) (rounds := phaseRounds) hm hbal hn responder (16 * k) with
    ⟨B, hhalf⟩
  refine ⟨phaseRounds ++ [LazyRound.ofResponder responder (16 * k) B],
    ?_, hhalf⟩
  have hlen :
      phaseRounds.length = 16 * k := by
    simpa [phaseRounds] using
      sparseCutPlayMany_length (X := X) 1 4 m hm responder k 16
  simp [hlen]

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
