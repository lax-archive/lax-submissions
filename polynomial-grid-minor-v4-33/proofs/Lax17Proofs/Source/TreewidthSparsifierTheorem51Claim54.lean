import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentQuotient
import Lax17Proofs.Source.TreewidthSparsifierTwoRoutingMinimal
import Lax17Proofs.Source.TreewidthSparsifierTheorem51PhysicalCuts
import Lax17Proofs.Source.TreewidthSparsifierBlockSupport
import Lax17Proofs.Source.PathPackingSplice

namespace Lax17Proofs

universe u v w

/-!
# Theorem 5.1, Claim 5.4

This module proves the deterministic connectivity statement for the graph
obtained by contracting the heavy red-rail segments.  The proof follows
Claim 5.4 of Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*.

The first lemmas below isolate the heavy-side reduction used after orienting a
putative small cut: if that side contains no complete rail, then every one of
its segments is heavy in a genuine recorded layer.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open ChekuriChuzhoySection5TerminalSkeleton
open HeavySegments
open PathRuns


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

theorem exactRailSegmentation_length_pos
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) (B : ℕ) (hB : 0 < B) :
    0 <
      (E.exactRailSegmentation hbudget hrecords x B hB).segments.length :=
  List.length_pos_iff_ne_nil.mpr
    (E.exactRailSegmentation hbudget hrecords x B hB).segments_nonempty

/-- All contracted segments of rail `x` lie on the chosen quotient side. -/
def RailContainedIn
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (x : Fin h) : Prop :=
  ∀ i :
      Fin
        (E.exactRailSegmentation
          hbudget hrecords x B hB).segments.length,
    (⟨x, i⟩ : ExactRailSegmentIndex E hbudget hrecords B hB) ∈ S

/-- No complete red rail lies on the chosen quotient side. -/
def NoCompleteRail
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) : Prop :=
  ∀ x : Fin h,
    ¬ E.RailContainedIn hbudget hrecords B hB S x

theorem segmentation_length_gt_one_of_mem_of_noCompleteRail
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (hno : E.NoCompleteRail hbudget hrecords B hB S)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (hi : i ∈ S) :
    1 <
      (E.exactRailSegmentation
        hbudget hrecords i.1 B hB).segments.length := by
  have hpos :=
    E.exactRailSegmentation_length_pos
      hbudget hrecords i.1 B hB
  by_contra hnot
  have hone :
      (E.exactRailSegmentation
        hbudget hrecords i.1 B hB).segments.length = 1 := by
    omega
  apply hno i.1
  intro j
  have hji : j = i.2 := by
    apply Fin.ext
    have hj0 : j.1 = 0 := by omega
    have hi0 : i.2.1 = 0 := by omega
    omega
  subst j
  exact hi

private theorem count_eq_filter_card_of_nodup
    {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (colour : α → κ) (c : κ) (xs : List α)
    (hxs : xs.Nodup) :
    colourCount colour c xs =
      (xs.toFinset.filter fun x => colour x = c).card := by
  induction xs with
  | nil => simp [colourCount]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hxs).1
      have htail : xs.Nodup := (List.nodup_cons.mp hxs).2
      have ih' :
          (List.map colour xs).count c =
            (xs.toFinset.filter fun y => colour y = c).card := by
        simpa [colourCount] using ih htail
      by_cases hc : colour x = c
      · simp only [colourCount, List.map_cons, List.count_cons]
        rw [ih']
        rw [show (x :: xs).toFinset = insert x xs.toFinset by simp]
        rw [Finset.filter_insert]
        simp [hc, hx, Nat.add_comm]
      · simp only [colourCount, List.map_cons, List.count_cons]
        rw [ih']
        rw [show (x :: xs).toFinset = insert x xs.toFinset by simp]
        rw [Finset.filter_insert]
        simp [hc, hx]

theorem exactRailSegment_record_colourCount_eq_branch_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (i : ExactRailSegmentIndex E hbudget hrecords B hB)
    (j : Fin E.finalState.records.length) :
    colourCount E.exactRailColour (Sum.inl j)
        (E.exactRailSegmentList hbudget hrecords B hB i) =
      ((E.exactRailSegmentPathAt
          hbudget hrecords B hB i).vertexSet ∩
        branchVertexFinset (E.recordAt j).layer.localGraph).card := by
  classical
  let xs := E.exactRailSegmentList hbudget hrecords B hB i
  have hnodup : xs.Nodup := by
    have hinfix :=
      E.exactRailSegment_isInfix
        hbudget hrecords i.1 B hB xs
        (E.exactRailSegmentList_mem hbudget hrecords B hB i)
    exact hinfix.nodup
      (E.exactRailPath hbudget hrecords i.1).isPath.support_nodup
  rw [count_eq_filter_card_of_nodup E.exactRailColour
    (Sum.inl j) xs hnodup]
  rw [E.exactRailSegmentPathAt_vertexSet]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hv, hcolour⟩
    exact ⟨hv,
      E.branch_of_exactRailColour_eq_record j hcolour⟩
  · rintro ⟨hv, hbranch⟩
    exact ⟨hv,
      E.exactRailColour_eq_record_of_branch hbudget j hbranch⟩

/-- The heavy segment promised by the source proof, stated directly as a
large set of local branch vertices. -/
theorem exists_heavy_record_of_mem_of_noCompleteRail
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hBpos : 0 < B) (hB : 1 < B)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hBpos))
    (hno : E.NoCompleteRail hbudget hrecords B hBpos S)
    (i : ExactRailSegmentIndex E hbudget hrecords B hBpos)
    (hi : i ∈ S) :
    ∃ j : Fin E.finalState.records.length,
      B ≤
        ((E.exactRailSegmentPathAt
            hbudget hrecords B hBpos i).vertexSet ∩
          branchVertexFinset (E.recordAt j).layer.localGraph).card := by
  have hmany :=
      E.segmentation_length_gt_one_of_mem_of_noCompleteRail
      hbudget hrecords B hBpos S hno i hi
  rcases
      E.exactRailSegment_heavy_record_of_split
        hbudget hrecords i.1 B hB hmany
        (E.exactRailSegmentList hbudget hrecords B hBpos i)
        (E.exactRailSegmentList_mem
          hbudget hrecords B hBpos i) with
    ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [← E.exactRailSegment_record_colourCount_eq_branch_card
    hbudget hrecords B hBpos i j]
  exact hj

/-! ## Rails meeting a side of a segment cut

The next statements are the first counting step in the second case of source
Claim 5.4.  A rail which meets the chosen side but is not wholly contained in
it must contribute a physical red edge to the segment boundary.  Distinct
rails contribute distinct edges because the exact rails are node-disjoint.
-/

/-- If two segments of one exact rail lie on opposite sides of a quotient
cut, an actual edge of that rail belongs to the represented physical
boundary. -/
theorem exists_segmentBoundaryEdge_of_same_rail_opposite
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (i j : ExactRailSegmentIndex E hbudget hrecords B hB)
    (hrail : i.1 = j.1) (hi : i ∈ S) (hj : j ∉ S) :
    ∃ e : Sym2 V,
      e ∈ (E.exactRailPath hbudget hrecords i.1).edgeSet ∧
        e ∈ E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S := by
  classical
  let X :=
    E.segmentOwnerSide hbudget hrecords B hB fallback S
  let Y :=
    E.segmentOwnerSide hbudget hrecords B hB fallback Sᶜ
  let Qi :=
    E.exactRailSegmentPathAt hbudget hrecords B hB i
  let Qj :=
    E.exactRailSegmentPathAt hbudget hrecords B hB j
  have hsourceI :
      Qi.source ∈
        (E.exactRailSegmentPathAt
          hbudget hrecords B hB i).vertexSet := by
    exact GraphPath.source_mem_vertexSet _
  have hsourceJ :
      Qj.source ∈
        (E.exactRailSegmentPathAt
          hbudget hrecords B hB j).vertexSet := by
    exact GraphPath.source_mem_vertexSet _
  have hownerI :
      E.segmentOwner hbudget hrecords B hB fallback Qi.source = i := by
    exact E.segmentOwner_eq_of_mem
      hbudget hrecords B hB fallback i hsourceI
  have hownerJ :
      E.segmentOwner hbudget hrecords B hB fallback Qj.source = j := by
    exact E.segmentOwner_eq_of_mem
      hbudget hrecords B hB fallback j hsourceJ
  have hQiRail :
      Qi.source ∈
        (E.exactRailPath hbudget hrecords i.1).vertexSet := by
    exact
      E.exactRailSegmentPathAt_vertexSet_subset_rail
        hbudget hrecords B hB i hsourceI
  have hQjRail :
      Qj.source ∈
        (E.exactRailPath hbudget hrecords i.1).vertexSet := by
    have hmem :
        Qj.source ∈
          (E.exactRailPath hbudget hrecords j.1).vertexSet :=
      E.exactRailSegmentPathAt_vertexSet_subset_rail
        hbudget hrecords B hB j hsourceJ
    simpa [hrail] using hmem
  have hcover : X ∪ Y = Finset.univ := by
    ext v
    by_cases hv :
        E.segmentOwner hbudget hrecords B hB fallback v ∈ S
    · simp [X, Y, hv]
    · simp [X, Y, hv]
  have hdisjoint : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro v hvX hvY
    have hvS :
        E.segmentOwner hbudget hrecords B hB fallback v ∈ S := by
      exact
        (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback S v).1 (by simpa [X] using hvX)
    have hvNot :
        E.segmentOwner hbudget hrecords B hB fallback v ∉ S := by
      have :=
        (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback Sᶜ v).1 (by simpa [Y] using hvY)
      simpa using this
    exact hvNot hvS
  have hleft : Qi.source ∈ X := by
    apply
      (E.mem_segmentOwnerSide
        hbudget hrecords B hB fallback S Qi.source).2
    simpa [hownerI] using hi
  have hright : Qj.source ∈ Y := by
    apply
      (E.mem_segmentOwnerSide
        hbudget hrecords B hB fallback Sᶜ Qj.source).2
    simpa [hownerJ] using hj
  let R := E.exactRailPath hbudget hrecords i.1
  have hbefore : R.Before Qi.source Qj.source ∨
      R.Before Qj.source Qi.source := by
    by_cases hidx :
        R.vertexIndex Qi.source ≤ R.vertexIndex Qj.source
    · exact Or.inl
        ((R.before_iff_vertexIndex_le).2 ⟨hQiRail, hQjRail, hidx⟩)
    · exact Or.inr
        ((R.before_iff_vertexIndex_le).2
          ⟨hQjRail, hQiRail, Nat.le_of_not_ge hidx⟩)
  rcases hbefore with hbefore | hbefore
  · let Q := R.segmentOfBefore hbefore
    obtain ⟨e, heQ, heCut⟩ :=
      path_exists_edgeBoundary_of_endpoints_opposite
        Q hcover hdisjoint (by simpa [Q] using hleft)
          (by simpa [Q] using hright)
    refine ⟨e, R.segmentOfBefore_edgeSet_subset hbefore heQ, ?_⟩
    rw [E.segmentBoundaryEdges_eq_edgeBoundary_ownerSides]
    exact edgeBoundary_mono
      (le_sup_left :
        E.redSupport hbudget ≤ E.assembledSupport hbudget) X Y heCut
  · let Q := R.segmentOfBefore hbefore
    obtain ⟨e, heQ, heCut⟩ :=
      path_exists_edgeBoundary_of_endpoints_opposite
        Q.reverse hcover hdisjoint (by simpa [Q] using hleft)
          (by simpa [Q] using hright)
    have heQ' : e ∈ Q.edgeSet := by
      simpa using heQ
    refine ⟨e, R.segmentOfBefore_edgeSet_subset hbefore heQ', ?_⟩
    rw [E.segmentBoundaryEdges_eq_edgeBoundary_ownerSides]
    exact edgeBoundary_mono
      (le_sup_left :
        E.redSupport hbudget ≤ E.assembledSupport hbudget) X Y heCut

/-- Rails having at least one contracted segment on `S`. -/
noncomputable def ActiveRails
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ i :
        Fin
          (E.exactRailSegmentation
            hbudget hrecords x B hB).segments.length,
      (⟨x, i⟩ : ExactRailSegmentIndex E hbudget hrecords B hB) ∈ S

@[simp] theorem mem_activeRails
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (x : Fin h) :
    x ∈ E.ActiveRails hbudget hrecords B hB S ↔
      ∃ i :
          Fin
            (E.exactRailSegmentation
              hbudget hrecords x B hB).segments.length,
        (⟨x, i⟩ : ExactRailSegmentIndex E hbudget hrecords B hB) ∈ S := by
  classical
  simp [ActiveRails]

/-- On a side containing no complete rail, the number of rails represented
there is at most the number of physical segment-boundary edges. -/
theorem activeRails_card_le_segmentBoundaryEdges_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (hno : E.NoCompleteRail hbudget hrecords B hB S) :
    (E.ActiveRails hbudget hrecords B hB S).card ≤
      (E.segmentBoundaryEdges
        hbudget hrecords B hB fallback S).card := by
  classical
  let A := E.ActiveRails hbudget hrecords B hB S
  let D :=
    E.segmentBoundaryEdges hbudget hrecords B hB fallback S
  have hedge :
      ∀ x : {x : Fin h // x ∈ A},
        ∃ e : Sym2 V,
          e ∈ (E.exactRailPath hbudget hrecords x.1).edgeSet ∧ e ∈ D := by
    intro x
    have hxA :
        x.1 ∈ E.ActiveRails hbudget hrecords B hB S := by
      simpa [A] using x.2
    rcases (E.mem_activeRails hbudget hrecords B hB S x.1).1 hxA with
      ⟨i, hi⟩
    have hnotAll :
        ¬ E.RailContainedIn hbudget hrecords B hB S x.1 :=
      hno x.1
    simp only [RailContainedIn, not_forall] at hnotAll
    rcases hnotAll with ⟨j, hj⟩
    have hj' :
        (⟨x.1, j⟩ :
          ExactRailSegmentIndex E hbudget hrecords B hB) ∉ S := by
      simpa using hj
    rcases
        E.exists_segmentBoundaryEdge_of_same_rail_opposite
          hbudget hrecords B hB fallback S
          (⟨x.1, i⟩ :
            ExactRailSegmentIndex E hbudget hrecords B hB)
          (⟨x.1, j⟩ :
            ExactRailSegmentIndex E hbudget hrecords B hB)
          rfl hi hj' with
      ⟨e, heRail, heD⟩
    exact ⟨e, heRail, by simpa [D] using heD⟩
  let f : {x : Fin h // x ∈ A} → {e : Sym2 V // e ∈ D} :=
    fun x => ⟨Classical.choose (hedge x),
      (Classical.choose_spec (hedge x)).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have heX :
        (f x).1 ∈
          (E.exactRailPath hbudget hrecords x.1).edgeSet :=
      (Classical.choose_spec (hedge x)).1
    have heY :
        (f y).1 ∈
          (E.exactRailPath hbudget hrecords y.1).edgeSet :=
      (Classical.choose_spec (hedge y)).1
    have heEq : (f x).1 = (f y).1 :=
      congrArg Subtype.val hxy
    rw [heEq] at heX
    have hvX :
        (f y).1.out.1 ∈
          (E.exactRailPath hbudget hrecords x.1).vertexSet := by
      have :
          s((f y).1.out.1, (f y).1.out.2) ∈
            (E.exactRailPath hbudget hrecords x.1).edgeSet := by
        simpa [Sym2.mk, (f y).1.out_eq] using heX
      exact
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.exactRailPath hbudget hrecords x.1) this).1
    have hvY :
        (f y).1.out.1 ∈
          (E.exactRailPath hbudget hrecords y.1).vertexSet := by
      have :
          s((f y).1.out.1, (f y).1.out.2) ∈
            (E.exactRailPath hbudget hrecords y.1).edgeSet := by
        simpa [Sym2.mk, (f y).1.out_eq] using heY
      exact
        (GraphPath.endpoints_mem_vertexSet_of_edgeSet
          (E.exactRailPath hbudget hrecords y.1) this).1
    exact Finset.disjoint_left.mp
      (E.exactRailPath_nodeDisjoint hbudget hrecords hne) hvX hvY
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, A, D] using hcard

/-! ## Regional path pieces -/

/-- If the source of every path is carried by an injectively assigned rail,
then the paths lying wholly on one segment side inject into the active rails
of that side. -/
theorem wholeIndices_card_le_activeRails_of_source_carrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    {K : _root_.SimpleGraph V} {U W : Finset V}
    (R : PathPacking K U W)
    (rail : R.Index → Fin h)
    (hrail : Function.Injective rail)
    (hcarrier :
      ∀ r : R.Index,
        E.RedCarrier hbudget (R.path r).source (rail r)) :
    (wholeIndices R
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)).card ≤
      (E.ActiveRails hbudget hrecords B hB S).card := by
  classical
  let X := E.segmentOwnerSide hbudget hrecords B hB fallback S
  let f :
      {r : R.Index // r ∈ wholeIndices R X} →
        {x : Fin h // x ∈ E.ActiveRails hbudget hrecords B hB S} :=
    fun r =>
      ⟨(E.segmentOwner hbudget hrecords B hB fallback
          (R.path r.1).source).1, by
      have hwhole : (R.path r.1).vertexSet ⊆ X :=
        (mem_wholeIndices R X r.1).mp r.2
      have hsourceX : (R.path r.1).source ∈ X :=
        hwhole (GraphPath.source_mem_vertexSet _)
      have hownerS :
          E.segmentOwner hbudget hrecords B hB fallback
              (R.path r.1).source ∈ S :=
        (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback S _).mp hsourceX
      exact
        (E.mem_activeRails hbudget hrecords B hB S _).2
          ⟨(E.segmentOwner hbudget hrecords B hB fallback
              (R.path r.1).source).2, hownerS⟩⟩
  have hf : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply hrail
    have hr :=
      E.segmentOwner_rail hbudget hrecords B hB fallback
        (hcarrier r.1)
    have hs :=
      E.segmentOwner_rail hbudget hrecords B hB fallback
        (hcarrier s.1)
    rw [← hr, ← hs]
    exact congrArg Subtype.val hrs
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, X] using hcard

/-- Whole red paths of one recorded layer are charged injectively to the
active global red rails. -/
theorem red_wholeIndices_card_le_activeRails
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (j : Fin E.finalState.records.length) :
    (wholeIndices (E.recordAt j).layer.red.toPathPacking
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)).card ≤
      (E.ActiveRails hbudget hrecords B hB S).card := by
  classical
  let L := (E.recordAt j).layer
  let rail : L.red.Index → Fin h :=
    fun r =>
      (E.recordAt j).label.symm
        ⟨(L.red.path r).source, L.red.source_mem r⟩
  have hrail : Function.Injective rail := by
    intro r s hrs
    apply L.red.source_bijective.1
    have hrs' := congrArg (E.recordAt j).label hrs
    simpa [rail] using hrs'
  have hcarrier :
      ∀ r : L.red.Index,
        E.RedCarrier hbudget (L.red.path r).source (rail r) := by
    intro r
    left
    refine ⟨j, ?_⟩
    let named :
        {v : V // v ∈ P.left (E.recordAt j).index} :=
      ⟨(L.red.path r).source, L.red.source_mem r⟩
    have hlabel : (E.recordAt j).label (rail r) = named := by
      exact (E.recordAt j).label.apply_symm_apply named
    have hindex :
        L.red.indexOfSource ((E.recordAt j).label (rail r)) = r := by
      rw [hlabel]
      exact L.red.indexOfSource_source r
    simpa [localRedPath, L, hindex] using
      GraphPath.source_mem_vertexSet (L.red.path r)
  exact
    E.wholeIndices_card_le_activeRails_of_source_carrier
      hbudget hrecords B hB fallback S
      L.red.toPathPacking rail hrail hcarrier

/-- Whole blue paths of one recorded layer are likewise charged to the red
rail carrying their source. -/
theorem blue_wholeIndices_card_le_activeRails
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (j : Fin E.finalState.records.length) :
    (wholeIndices (E.recordAt j).layer.blue.toPathPacking
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)).card ≤
      (E.ActiveRails hbudget hrecords B hB S).card := by
  classical
  let L := (E.recordAt j).layer
  let sourceEquiv :=
    labelledImageEquiv
      (E.recordAt j).label (E.recordAt j).cut.left
  let rail : L.blue.Index → Fin h :=
    fun r =>
      (sourceEquiv.symm
        ⟨(L.blue.path r).source, L.blue.source_mem r⟩).1
  have hrail : Function.Injective rail := by
    intro r s hrs
    apply L.blue.source_bijective.1
    have hrs' :
        sourceEquiv.symm
            ⟨(L.blue.path r).source, L.blue.source_mem r⟩ =
          sourceEquiv.symm
            ⟨(L.blue.path s).source, L.blue.source_mem s⟩ := by
      apply Subtype.ext
      exact hrs
    exact sourceEquiv.symm.injective hrs'
  have hcarrier :
      ∀ r : L.blue.Index,
        E.RedCarrier hbudget (L.blue.path r).source (rail r) := by
    intro r
    let named :
        {v : V //
          v ∈ labelledImage
            (E.recordAt j).label (E.recordAt j).cut.left} :=
      ⟨(L.blue.path r).source, L.blue.source_mem r⟩
    let x :
        {x : Fin h // x ∈ (E.recordAt j).cut.left} :=
      sourceEquiv.symm named
    have hsource : sourceEquiv x = named :=
      sourceEquiv.apply_symm_apply named
    have hindex :
        L.blue.indexOfSource (sourceEquiv x) = r := by
      rw [hsource]
      exact L.blue.indexOfSource_source r
    have hpath :
        E.localBluePath j x = L.blue.path r := by
      simp only [localBluePath]
      rw [hindex]
    have hx :=
      E.localBluePath_source_redCarrier hbudget j x
    rw [hpath] at hx
    simpa [rail, x, named, sourceEquiv, L] using hx
  exact
    E.wholeIndices_card_le_activeRails_of_source_carrier
      hbudget hrecords B hB fallback S
      L.blue.toPathPacking rail hrail hcarrier

/-- A recorded layer contributes no more cut edges than the assembled
support, whose owner cut is exactly the segment-quotient cut. -/
theorem layer_edgeBoundary_card_le_segmentBoundaryEdges_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (j : Fin E.finalState.records.length) :
    (Section44.edgeBoundary
        (E.recordAt j).layer.localGraph
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)ᶜ).card ≤
      (E.segmentBoundaryEdges
        hbudget hrecords B hB fallback S).card := by
  classical
  let X := E.segmentOwnerSide hbudget hrecords B hB fallback S
  let Y := E.segmentOwnerSide hbudget hrecords B hB fallback Sᶜ
  have hcompl : Xᶜ = Y := by
    ext v
    simp [X, Y]
  apply Finset.card_le_card
  rw [E.segmentBoundaryEdges_eq_edgeBoundary_ownerSides
    hbudget hrecords B hB fallback S]
  rw [hcompl]
  exact
    edgeBoundary_mono
      (E.recordAt_localGraph_le_assembledSupport hbudget j) X Y

/-- Deleting the owner cut splits the red routing of a layer into at most
twice as many pieces as there are quotient cut edges. -/
theorem red_packingInside_card_le_two_segmentBoundaryEdges
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (hno : E.NoCompleteRail hbudget hrecords B hB S)
    (j : Fin E.finalState.records.length) :
    (packingInside (E.recordAt j).layer.red.toPathPacking
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)).card ≤
      2 * (E.segmentBoundaryEdges
        hbudget hrecords B hB fallback S).card := by
  let X := E.segmentOwnerSide hbudget hrecords B hB fallback S
  let D := E.segmentBoundaryEdges hbudget hrecords B hB fallback S
  have hpieces :=
    packingInside_card_le
      (E.recordAt j).layer.red.toPathPacking X
  have hwhole :=
    E.red_wholeIndices_card_le_activeRails
      hbudget hrecords B hB fallback S j
  have hactive :=
    E.activeRails_card_le_segmentBoundaryEdges_card
      hbudget hrecords B hB fallback S hno
  have hlocal :=
    E.layer_edgeBoundary_card_le_segmentBoundaryEdges_card
      hbudget hrecords B hB fallback S j
  dsimp only [X, D] at hpieces hwhole hactive hlocal ⊢
  omega

/-- The same component count holds for the blue routing. -/
theorem blue_packingInside_card_le_two_segmentBoundaryEdges
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (hno : E.NoCompleteRail hbudget hrecords B hB S)
    (j : Fin E.finalState.records.length) :
    (packingInside (E.recordAt j).layer.blue.toPathPacking
        (E.segmentOwnerSide hbudget hrecords B hB fallback S)).card ≤
      2 * (E.segmentBoundaryEdges
        hbudget hrecords B hB fallback S).card := by
  let X := E.segmentOwnerSide hbudget hrecords B hB fallback S
  let D := E.segmentBoundaryEdges hbudget hrecords B hB fallback S
  have hpieces :=
    packingInside_card_le
      (E.recordAt j).layer.blue.toPathPacking X
  have hwhole :=
    E.blue_wholeIndices_card_le_activeRails
      hbudget hrecords B hB fallback S j
  have hactive :=
    E.activeRails_card_le_segmentBoundaryEdges_card
      hbudget hrecords B hB fallback S hno
  have hlocal :=
    E.layer_edgeBoundary_card_le_segmentBoundaryEdges_card
      hbudget hrecords B hB fallback S j
  dsimp only [X, D] at hpieces hwhole hactive hlocal ⊢
  omega

/-- A local branch vertex in the selected side remains a branch vertex after
both routings are cut into their maximal regional pieces, unless it is one of
the four oriented regional endpoint types. -/
theorem branch_mem_regional_union_of_not_endpoints
    (E : ExpanderBlocks P count)
    (j : Fin E.finalState.records.length)
    (X : Finset V) {v : V}
    (hvX : v ∈ X)
    (hvRedSource :
      v ∉ (packingInside
        (E.recordAt j).layer.red.toPathPacking X).sourceSet)
    (hvRedTarget :
      v ∉ (packingInside
        (E.recordAt j).layer.red.toPathPacking X).targetSet)
    (hvBlueSource :
      v ∉ (packingInside
        (E.recordAt j).layer.blue.toPathPacking X).sourceSet)
    (hvBlueTarget :
      v ∉ (packingInside
        (E.recordAt j).layer.blue.toPathPacking X).targetSet)
    (hvBranch :
      v ∈ branchVertexFinset (E.recordAt j).layer.localGraph) :
    v ∈ branchVertexFinset
      (twoPackingUnionGraph
        (packingInsidePerfect
          (E.recordAt j).layer.red.toPathPacking X)
        (packingInsidePerfect
          (E.recordAt j).layer.blue.toPathPacking X)) := by
  classical
  let L := (E.recordAt j).layer
  let R := packingInsidePerfect L.red.toPathPacking X
  let Q := packingInsidePerfect L.blue.toPathPacking X
  let J := twoPackingUnionGraph R Q
  have hlocalToJ :
      ∀ ⦃w : V⦄, L.localGraph.Adj v w → J.Adj v w := by
    intro w hvw
    rw [L.support_eq] at hvw
    rcases hvw with hvwRed | hvwBlue
    · exact Or.inl
        (PackingSplice.insidePerfect_spanningGraph_adj_of_original
          L.red X hvX hvRedSource hvRedTarget hvwRed)
    · exact Or.inr
        (PackingSplice.insidePerfect_spanningGraph_adj_of_original
          L.blue X hvX hvBlueSource hvBlueTarget hvwBlue)
  have hJle : J ≤ L.localGraph := by
    exact
      (twoPackingUnionGraph_le R Q).trans (by
        intro a b hab
        exact L.support_eq.symm ▸ hab)
  have hvNot : ¬ DegreeAtMost L.localGraph v 2 := by
    simpa [branchVertexFinset, L] using hvBranch
  have hvJNot : ¬ DegreeAtMost J v 2 := by
    intro hvJ
    apply hvNot
    rcases hvJ with ⟨N, hN, hcard⟩
    refine ⟨N, ?_, hcard⟩
    intro w
    constructor
    · intro hw
      exact hJle ((hN w).mp hw)
    · intro hvw
      exact (hN w).mpr (hlocalToJ hvw)
  simpa [branchVertexFinset, J, R, Q, L] using hvJNot

/-! ## Theorem 1.3 arithmetic

The source takes at most `N` red pieces and at most `2N` blue pieces.  Their
four endpoint sets remove at most `6N` vertices from the heavy segment.  The
remaining `200N^4 - 6N` branch vertices strictly exceed the exact Theorem 1.3
bound with `k₁ = 2N`.
-/

theorem claim54_branch_arithmetic {N : ℕ} (hN : 0 < N) :
    8 * (2 * N) ^ 4 + 8 * (2 * N) <
      200 * N ^ 4 - 6 * N := by
  have hN4 : N ≤ N ^ 4 := by
    calc
      N = N * 1 := by simp
      _ ≤ N * N ^ 3 := by
        exact Nat.mul_le_mul_left N (by
          have hpow : 0 < N ^ 3 := Nat.pow_pos hN
          omega)
      _ = N ^ 4 := by ring
  have hmain :
      8 * (2 * N) ^ 4 + 8 * (2 * N) + 6 * N <
        200 * N ^ 4 := by
    calc
      8 * (2 * N) ^ 4 + 8 * (2 * N) + 6 * N =
          128 * N ^ 4 + 22 * N := by ring
      _ ≤ 128 * N ^ 4 + 22 * N ^ 4 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 22 hN4) _
      _ = 150 * N ^ 4 := by ring
      _ < 200 * N ^ 4 := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos hN)
  omega

/-- Symmetric version used with the formal component count, which bounds both
regional routings by `2N`. -/
theorem claim54_branch_arithmetic_symmetric {N : ℕ} (hN : 0 < N) :
    8 * (2 * N) ^ 4 + 8 * (2 * N) <
      200 * N ^ 4 - 8 * N := by
  have hN4 : N ≤ N ^ 4 := by
    calc
      N = N * 1 := by simp
      _ ≤ N * N ^ 3 := by
        exact Nat.mul_le_mul_left N (by
          have hpow : 0 < N ^ 3 := Nat.pow_pos hN
          omega)
      _ = N ^ 4 := by ring
  have hmain :
      8 * (2 * N) ^ 4 + 8 * (2 * N) + 8 * N <
        200 * N ^ 4 := by
    calc
      8 * (2 * N) ^ 4 + 8 * (2 * N) + 8 * N =
          128 * N ^ 4 + 24 * N := by ring
      _ ≤ 128 * N ^ 4 + 24 * N ^ 4 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 24 hN4) _
      _ = 152 * N ^ 4 := by ring
      _ < 200 * N ^ 4 := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos hN)
  omega

/-- Removing a finite exceptional endpoint set from a known family of branch
vertices gives the corresponding lower bound on the branch count. -/
theorem branchVertexCount_ge_card_sub_of_diff_subset
    (J : _root_.SimpleGraph V) (A Z : Finset V)
    (hbranch : A \ Z ⊆ branchVertexFinset J) :
    A.card - Z.card ≤ branchVertexCount J := by
  have hdiff :
      (A \ Z).card ≤ (branchVertexFinset J).card :=
    Finset.card_le_card hbranch
  have hinter : (A ∩ Z).card ≤ Z.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplit :
      (A \ Z).card + (A ∩ Z).card = A.card := by
    exact Finset.card_sdiff_add_card_inter A Z
  rw [branchVertexFinset_card] at hdiff
  omega

/-- The numerical branch lower bound used immediately before invoking
Theorem 1.3 in Claim 5.4. -/
theorem claim54_branchVertexCount_lower
    (J : _root_.SimpleGraph V) (A Z : Finset V) {N : ℕ}
    (hA : 200 * N ^ 4 ≤ A.card)
    (hZ : Z.card ≤ 6 * N)
    (hbranch : A \ Z ⊆ branchVertexFinset J) :
    200 * N ^ 4 - 6 * N ≤ branchVertexCount J := by
  have hcore :=
    branchVertexCount_ge_card_sub_of_diff_subset J A Z hbranch
  omega

/-- The local deletion conclusion at the heart of Claim 5.4.

The caller supplies the red and blue component endpoint sets, their routings
inside the regional union graph `J`, and the source degree observation saying
that every heavy-segment branch vertex away from the four endpoint sets is
still a branch vertex of `J`.  The conclusion is the exact deletable edge
needed for the final splicing contradiction. -/
theorem claim54_exists_local_deletable_edge
    (J : _root_.SimpleGraph V)
    (S₁ T₁ S₂ T₂ A : Finset V) {N : ℕ}
    (hN : 0 < N)
    (hS₁T₁ : S₁.card = T₁.card)
    (hS₂T₂ : S₂.card = T₂.card)
    (hS₁ : S₁.card ≤ N)
    (hS₂ : S₂.card ≤ 2 * N)
    (hred : RoutableIn J S₁ T₁)
    (hblue : RoutableIn J S₂ T₂)
    (hA : 200 * N ^ 4 ≤ A.card)
    (hbranch :
      A \ (S₁ ∪ T₁ ∪ S₂ ∪ T₂) ⊆ branchVertexFinset J) :
    ∃ a b : V, J.Adj a b ∧
      RoutableIn
        (J.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₁ T₁ ∧
      RoutableIn
        (J.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₂ T₂ := by
  let Z := S₁ ∪ T₁ ∪ S₂ ∪ T₂
  have hT₁ : T₁.card ≤ N := by simpa [← hS₁T₁] using hS₁
  have hT₂ : T₂.card ≤ 2 * N := by simpa [← hS₂T₂] using hS₂
  have hZ : Z.card ≤ 6 * N := by
    dsimp [Z]
    calc
      (S₁ ∪ T₁ ∪ S₂ ∪ T₂).card ≤
          S₁.card + T₁.card + S₂.card + T₂.card := by
        exact
          (Finset.card_union_le (S₁ ∪ T₁ ∪ S₂) T₂).trans
            (Nat.add_le_add_right
              ((Finset.card_union_le (S₁ ∪ T₁) S₂).trans
                (Nat.add_le_add_right
                  (Finset.card_union_le S₁ T₁) S₂.card))
              T₂.card)
      _ ≤ N + N + (2 * N) + (2 * N) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS₁ hT₁) hS₂) hT₂
      _ = 6 * N := by ring
  have hbranchLower :
      200 * N ^ 4 - 6 * N ≤ branchVertexCount J :=
    claim54_branchVertexCount_lower J A Z hA hZ (by
      simpa [Z] using hbranch)
  have hlarge :
      8 * (2 * N) ^ 4 + 8 * (2 * N) < branchVertexCount J :=
    (claim54_branch_arithmetic hN).trans_le hbranchLower
  exact
    exists_edge_deletable_for_two_routings_of_card_le
      hS₁T₁ hS₂T₂
      (hS₁.trans (by omega))
      hS₂ hred hblue hlarge

/-- Symmetric local deletion conclusion matching the component bounds proved
above. -/
theorem claim54_exists_local_deletable_edge_symmetric
    (J : _root_.SimpleGraph V)
    (S₁ T₁ S₂ T₂ A : Finset V) {N : ℕ}
    (hN : 0 < N)
    (hS₁T₁ : S₁.card = T₁.card)
    (hS₂T₂ : S₂.card = T₂.card)
    (hS₁ : S₁.card ≤ 2 * N)
    (hS₂ : S₂.card ≤ 2 * N)
    (hred : RoutableIn J S₁ T₁)
    (hblue : RoutableIn J S₂ T₂)
    (hA : 200 * N ^ 4 ≤ A.card)
    (hbranch :
      A \ (S₁ ∪ T₁ ∪ S₂ ∪ T₂) ⊆ branchVertexFinset J) :
    ∃ a b : V, J.Adj a b ∧
      RoutableIn
        (J.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₁ T₁ ∧
      RoutableIn
        (J.deleteEdges ({s(a, b)} : Set (Sym2 V))) S₂ T₂ := by
  let Z := S₁ ∪ T₁ ∪ S₂ ∪ T₂
  have hT₁ : T₁.card ≤ 2 * N := by simpa [← hS₁T₁] using hS₁
  have hT₂ : T₂.card ≤ 2 * N := by simpa [← hS₂T₂] using hS₂
  have hZ : Z.card ≤ 8 * N := by
    dsimp [Z]
    calc
      (S₁ ∪ T₁ ∪ S₂ ∪ T₂).card ≤
          S₁.card + T₁.card + S₂.card + T₂.card := by
        exact
          (Finset.card_union_le (S₁ ∪ T₁ ∪ S₂) T₂).trans
            (Nat.add_le_add_right
              ((Finset.card_union_le (S₁ ∪ T₁) S₂).trans
                (Nat.add_le_add_right
                  (Finset.card_union_le S₁ T₁) S₂.card))
              T₂.card)
      _ ≤ (2 * N) + (2 * N) + (2 * N) + (2 * N) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS₁ hT₁) hS₂) hT₂
      _ = 8 * N := by ring
  have hbranchLower :
      200 * N ^ 4 - 8 * N ≤ branchVertexCount J :=
    by
      have hcore :=
        branchVertexCount_ge_card_sub_of_diff_subset J A Z (by
          simpa [Z] using hbranch)
      omega
  have hlarge :
      8 * (2 * N) ^ 4 + 8 * (2 * N) < branchVertexCount J :=
    (claim54_branch_arithmetic_symmetric hN).trans_le hbranchLower
  exact
    exists_edge_deletable_for_two_routings_of_card_le
      hS₁T₁ hS₂T₂ hS₁ hS₂ hred hblue hlarge

/-! ## The heavy-side contradiction

This is the second case of source Claim 5.4.  If one side of a segment cut
contains no complete red rail, then a boundary smaller than `N` would expose
a `200 * N^4`-heavy segment.  The regional red and blue path pieces can then
be sparsified, one edge deleted, and the replacement pieces spliced back into
the original layer routings, contradicting the defining minimality of that
layer. -/

/-- The first case of source Claim 5.4.  If opposite sides of a segment cut
contain complete rails, every independently restarted expander block supplies
one physical crossing edge.  The block supports are edge-disjoint, so these
crossings are distinct. -/
theorem segmentBoundary_card_ge_of_completeRails
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB))
    (x y : Fin h)
    (hx : E.RailContainedIn hbudget hrecords B hB S x)
    (hy : E.RailContainedIn hbudget hrecords B hB Sᶜ y) :
    count ≤
      (E.segmentBoundaryEdges
        hbudget hrecords B hB fallback S).card := by
  classical
  let X :=
    E.segmentOwnerSide hbudget hrecords B hB fallback S
  let Y :=
    E.segmentOwnerSide hbudget hrecords B hB fallback Sᶜ
  have hcover : X ∪ Y = Finset.univ := by
    ext v
    by_cases hv :
        E.segmentOwner hbudget hrecords B hB fallback v ∈ S
    · simp [X, Y, hv]
    · simp [X, Y, hv]
  have hdisjoint : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro v hvX hvY
    have hvS :
        E.segmentOwner hbudget hrecords B hB fallback v ∈ S :=
      (E.mem_segmentOwnerSide
        hbudget hrecords B hB fallback S v).1
        (by simpa [X] using hvX)
    have hvNot :
        E.segmentOwner hbudget hrecords B hB fallback v ∉ S := by
      have :=
        (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback Sᶜ v).1
          (by simpa [Y] using hvY)
      simpa using this
    exact hvNot hvS
  have hrailCarrier :
      ∀ (i : Fin count) (z : Fin h),
        E.RedCarrier hbudget (E.blockRailVertex hheight i z) z := by
    intro i z
    let r0 : Fin (E.rounds i).length :=
      ⟨0, E.rounds_nonempty hheight i⟩
    left
    refine ⟨E.blockRecordIndex i r0, ?_⟩
    simpa [blockRailVertex, r0] using
        GraphPath.source_mem_vertexSet
          (E.localRedPath (E.blockRecordIndex i r0) z)
  have hxAll :
      ∀ q : ExactRailSegmentIndex E hbudget hrecords B hB,
        q.1 = x → q ∈ S := by
    rintro ⟨z, k⟩ hz
    change z = x at hz
    subst z
    exact hx k
  have hyAll :
      ∀ q : ExactRailSegmentIndex E hbudget hrecords B hB,
        q.1 = y → q ∈ Sᶜ := by
    rintro ⟨z, k⟩ hz
    change z = y at hz
    subst z
    exact hy k
  have hxSide :
      ∀ i : Fin count, E.blockRailVertex hheight i x ∈ X := by
    intro i
    apply
      (E.mem_segmentOwnerSide
        hbudget hrecords B hB fallback S _).2
    apply hxAll
    exact
      E.segmentOwner_rail hbudget hrecords B hB fallback
        (hrailCarrier i x)
  have hySide :
      ∀ i : Fin count, E.blockRailVertex hheight i y ∈ Y := by
    intro i
    apply
      (E.mem_segmentOwnerSide
        hbudget hrecords B hB fallback Sᶜ _).2
    apply hyAll
    exact
      E.segmentOwner_rail hbudget hrecords B hB fallback
        (hrailCarrier i y)
  have hpaths :
      ∀ i : Fin count,
        ∃ Q : GraphPath (E.blockSupport hbudget i),
          Q.source = E.blockRailVertex hheight i x ∧
            Q.target = E.blockRailVertex hheight i y := by
    intro i
    apply
      (E.blockRailVertex_reachable
        hbudget hheight i x y).elim_path
    intro q
    exact
      ⟨{
        source := E.blockRailVertex hheight i x
        target := E.blockRailVertex hheight i y
        walk := q.1
        isPath := q.2
      }, rfl, rfl⟩
  let Q (i : Fin count) : GraphPath (E.blockSupport hbudget i) :=
    Classical.choose (hpaths i)
  have hQsource :
      ∀ i : Fin count,
        (Q i).source = E.blockRailVertex hheight i x :=
    fun i => (Classical.choose_spec (hpaths i)).1
  have hQtarget :
      ∀ i : Fin count,
        (Q i).target = E.blockRailVertex hheight i y :=
    fun i => (Classical.choose_spec (hpaths i)).2
  have hcross :
      ∀ i : Fin count,
        ∃ e ∈ (Q i).edgeSet,
          e ∈ E.segmentBoundaryEdges
            hbudget hrecords B hB fallback S := by
    intro i
    obtain ⟨e, heQ, heCut⟩ :=
      path_exists_edgeBoundary_of_endpoints_opposite
        (Q i) hcover hdisjoint
        (by simpa [hQsource i] using hxSide i)
        (by simpa [hQtarget i] using hySide i)
    refine ⟨e, heQ, ?_⟩
    rw [E.segmentBoundaryEdges_eq_edgeBoundary_ownerSides]
    exact
      edgeBoundary_mono
        (E.blockSupport_le_assembledSupport hbudget i) X Y heCut
  let edge (i : Fin count) : Sym2 V :=
    Classical.choose (hcross i)
  have hedgePath :
      ∀ i : Fin count, edge i ∈ (Q i).edgeSet :=
    fun i => (Classical.choose_spec (hcross i)).1
  have hedgeBoundary :
      ∀ i : Fin count,
        edge i ∈ E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S :=
    fun i => (Classical.choose_spec (hcross i)).2
  let f :
      Fin count →
        {e : Sym2 V //
          e ∈ E.segmentBoundaryEdges
            hbudget hrecords B hB fallback S} :=
    fun i => ⟨edge i, hedgeBoundary i⟩
  have hf : Function.Injective f := by
    intro i k hik
    have hedgeEq : edge i = edge k :=
      congrArg Subtype.val hik
    have hiAdj :
        (E.blockSupport hbudget i).Adj
          (edge i).out.1 (edge i).out.2 := by
      rw [← _root_.SimpleGraph.mem_edgeSet]
      simpa [Sym2.mk, (edge i).out_eq] using
        GraphPath.edgeSet_subset_edgeSet (Q i) (hedgePath i)
    have hkAdj :
        (E.blockSupport hbudget k).Adj
          (edge i).out.1 (edge i).out.2 := by
      rw [← _root_.SimpleGraph.mem_edgeSet]
      simpa [hedgeEq, Sym2.mk, (edge k).out_eq] using
        GraphPath.edgeSet_subset_edgeSet (Q k) (hedgePath k)
    exact E.blockSupport_common_adj_block_unique
      hbudget hheight hiAdj hkAdj
  calc
    count = Fintype.card (Fin count) := by simp
    _ ≤ Fintype.card
        {e : Sym2 V //
          e ∈ E.segmentBoundaryEdges
            hbudget hrecords B hB fallback S} :=
      Fintype.card_le_of_injective f hf
    _ = (E.segmentBoundaryEdges
          hbudget hrecords B hB fallback S).card := by
      rw [Fintype.card_coe]

theorem segmentBoundary_card_ge_of_noCompleteRail
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (N : ℕ) (hN : 0 < N)
    (hB : 0 < 200 * N ^ 4)
    (fallback :
      ExactRailSegmentIndex E hbudget hrecords (200 * N ^ 4) hB)
    (S :
      Finset
        (ExactRailSegmentIndex E hbudget hrecords (200 * N ^ 4) hB))
    (hS : S.Nonempty)
    (hno :
      E.NoCompleteRail hbudget hrecords (200 * N ^ 4) hB S) :
    N ≤
      (E.segmentBoundaryEdges
        hbudget hrecords (200 * N ^ 4) hB fallback S).card := by
  classical
  by_contra hsmallNot
  have hsmall :
      (E.segmentBoundaryEdges
        hbudget hrecords (200 * N ^ 4) hB fallback S).card < N := by
    omega
  obtain ⟨i, hi⟩ := hS
  have hBlarge : 1 < 200 * N ^ 4 := by
    have hN4 : 0 < N ^ 4 := Nat.pow_pos hN
    nlinarith
  obtain ⟨j, hj⟩ :=
    E.exists_heavy_record_of_mem_of_noCompleteRail
      hbudget hrecords (200 * N ^ 4) hB hBlarge
      S hno i hi
  let L := (E.recordAt j).layer
  let X :=
    E.segmentOwnerSide
      hbudget hrecords (200 * N ^ 4) hB fallback S
  let R := packingInsidePerfect L.red.toPathPacking X
  let Q := packingInsidePerfect L.blue.toPathPacking X
  let J := twoPackingUnionGraph R Q
  let S₁ := (packingInside L.red.toPathPacking X).sourceSet
  let T₁ := (packingInside L.red.toPathPacking X).targetSet
  let S₂ := (packingInside L.blue.toPathPacking X).sourceSet
  let T₂ := (packingInside L.blue.toPathPacking X).targetSet
  let A :=
    (E.exactRailSegmentPathAt
        hbudget hrecords (200 * N ^ 4) hB i).vertexSet ∩
      branchVertexFinset L.localGraph
  have hS₁T₁ : S₁.card = T₁.card := by
    simp [S₁, T₁]
  have hS₂T₂ : S₂.card = T₂.card := by
    simp [S₂, T₂]
  have hS₁ :
      S₁.card ≤ 2 * N := by
    have hpieces :=
      E.red_packingInside_card_le_two_segmentBoundaryEdges
        hbudget hrecords (200 * N ^ 4) hB fallback S hno j
    have hsource :
        S₁.card =
          (packingInside L.red.toPathPacking X).card := by
      simp [S₁]
    rw [hsource]
    simpa [L, X] using hpieces.trans (Nat.mul_le_mul_left 2 hsmall.le)
  have hS₂ :
      S₂.card ≤ 2 * N := by
    have hpieces :=
      E.blue_packingInside_card_le_two_segmentBoundaryEdges
        hbudget hrecords (200 * N ^ 4) hB fallback S hno j
    have hsource :
        S₂.card =
          (packingInside L.blue.toPathPacking X).card := by
      simp [S₂]
    rw [hsource]
    simpa [L, X] using hpieces.trans (Nat.mul_le_mul_left 2 hsmall.le)
  have hred : RoutableIn J S₁ T₁ := by
    exact ⟨R.inSpanningGraph.mapLe le_sup_left⟩
  have hblue : RoutableIn J S₂ T₂ := by
    exact ⟨Q.inSpanningGraph.mapLe le_sup_right⟩
  have hA : 200 * N ^ 4 ≤ A.card := by
    simpa [A, L] using hj
  have hbranch :
      A \ (S₁ ∪ T₁ ∪ S₂ ∪ T₂) ⊆ branchVertexFinset J := by
    intro v hv
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    have hvNot : v ∉ S₁ ∪ T₁ ∪ S₂ ∪ T₂ :=
      (Finset.mem_sdiff.mp hv).2
    have hvSegment :
        v ∈
          (E.exactRailSegmentPathAt
            hbudget hrecords (200 * N ^ 4) hB i).vertexSet := by
      change
        v ∈
          (E.exactRailSegmentPathAt
              hbudget hrecords (200 * N ^ 4) hB i).vertexSet ∩
            branchVertexFinset L.localGraph at hvA
      exact (Finset.mem_inter.mp hvA).1
    have hvLocal :
        v ∈ branchVertexFinset L.localGraph := by
      exact (Finset.mem_inter.mp hvA).2
    have howner :
        E.segmentOwner
            hbudget hrecords (200 * N ^ 4) hB fallback v = i :=
      E.segmentOwner_eq_of_mem
        hbudget hrecords (200 * N ^ 4) hB fallback i hvSegment
    have hvX : v ∈ X := by
      apply
        (E.mem_segmentOwnerSide
          hbudget hrecords (200 * N ^ 4) hB fallback S v).2
      simpa [howner] using hi
    have hvS₁ : v ∉ S₁ := by
      intro hvS₁
      exact hvNot (by simp [hvS₁])
    have hvT₁ : v ∉ T₁ := by
      intro hvT₁
      exact hvNot (by simp [hvT₁])
    have hvS₂ : v ∉ S₂ := by
      intro hvS₂
      exact hvNot (by simp [hvS₂])
    have hvT₂ : v ∉ T₂ := by
      intro hvT₂
      exact hvNot (by simp [hvT₂])
    simpa [J, R, Q, S₁, T₁, S₂, T₂, L, X] using
      E.branch_mem_regional_union_of_not_endpoints
        j X hvX
        (by simpa [S₁, L, X] using hvS₁)
        (by simpa [T₁, L, X] using hvT₁)
        (by simpa [S₂, L, X] using hvS₂)
        (by simpa [T₂, L, X] using hvT₂)
        (by simpa [L] using hvLocal)
  obtain ⟨a, b, habJ, hredDelete, hblueDelete⟩ :=
    claim54_exists_local_deletable_edge_symmetric
      J S₁ T₁ S₂ T₂ A hN hS₁T₁ hS₂T₂
      hS₁ hS₂ hred hblue hA hbranch
  have hJle : J ≤ L.localGraph := by
    exact twoPackingUnionGraph_le R Q
  have habLocal : L.localGraph.Adj a b := hJle habJ
  have habX : a ∈ X ∧ b ∈ X := by
    exact
      SimpleGraph.TreewidthSparsifier.PackingSplice.twoPackingUnionGraph_adj_endpoints_mem
        R Q
        (packingInsidePerfect_staysIn L.red.toPathPacking X)
        (packingInsidePerfect_staysIn L.blue.toPathPacking X)
        habJ
  rcases hredDelete with ⟨Rdelete⟩
  rcases hblueDelete with ⟨Qdelete⟩
  let RdeleteLocal :=
    Rdelete.mapLe (_root_.SimpleGraph.deleteEdges_mono hJle)
  let QdeleteLocal :=
    Qdelete.mapLe (_root_.SimpleGraph.deleteEdges_mono hJle)
  have hRdeleteStay :
      RdeleteLocal.toPathPacking.StaysIn X := by
    have hstay :
        Rdelete.toPathPacking.StaysIn X := by
      apply
        SimpleGraph.TreewidthSparsifier.PackingSplice.staysIn_of_source_subset_of_adj_endpoints
          Rdelete
      · exact
          PathRuns.packingInside_sourceSet_subset L.red.toPathPacking X
      · intro u v huv
        exact
          SimpleGraph.TreewidthSparsifier.PackingSplice.twoPackingUnionGraph_adj_endpoints_mem
            R Q
            (packingInsidePerfect_staysIn L.red.toPathPacking X)
            (packingInsidePerfect_staysIn L.blue.toPathPacking X)
            (_root_.SimpleGraph.deleteEdges_le _ huv)
    intro q
    simpa [RdeleteLocal, PerfectPathPacking.mapLe, PathPacking.mapLe] using
      hstay q
  have hQdeleteStay :
      QdeleteLocal.toPathPacking.StaysIn X := by
    have hstay :
        Qdelete.toPathPacking.StaysIn X := by
      apply
        SimpleGraph.TreewidthSparsifier.PackingSplice.staysIn_of_source_subset_of_adj_endpoints
          Qdelete
      · exact
          PathRuns.packingInside_sourceSet_subset L.blue.toPathPacking X
      · intro u v huv
        exact
          SimpleGraph.TreewidthSparsifier.PackingSplice.twoPackingUnionGraph_adj_endpoints_mem
            R Q
            (packingInsidePerfect_staysIn L.red.toPathPacking X)
            (packingInsidePerfect_staysIn L.blue.toPathPacking X)
            (_root_.SimpleGraph.deleteEdges_le _ huv)
    intro q
    simpa [QdeleteLocal, PerfectPathPacking.mapLe, PathPacking.mapLe] using
      hstay q
  have hkeepRed :
      ∀ ⦃u v : V⦄,
        PerfectPathPacking.ForwardStep L.red u v →
          ¬(u ∈ X ∧ v ∈ X) →
            (L.localGraph.deleteEdges
              ({s(a, b)} : Set (Sym2 V))).Adj u v := by
    intro u v huv huvNot
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨PerfectPathPacking.forwardStep_adj L.red huv, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · exact huvNot ⟨heq.1 ▸ habX.1, heq.2 ▸ habX.2⟩
    · exact huvNot ⟨heq.1 ▸ habX.2, heq.2 ▸ habX.1⟩
  have hkeepBlue :
      ∀ ⦃u v : V⦄,
        PerfectPathPacking.ForwardStep L.blue u v →
          ¬(u ∈ X ∧ v ∈ X) →
            (L.localGraph.deleteEdges
              ({s(a, b)} : Set (Sym2 V))).Adj u v := by
    intro u v huv huvNot
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨PerfectPathPacking.forwardStep_adj L.blue huv, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · exact huvNot ⟨heq.1 ▸ habX.1, heq.2 ▸ habX.2⟩
    · exact huvNot ⟨heq.1 ▸ habX.2, heq.2 ▸ habX.1⟩
  have hredOriginal :
      RoutableIn
        (L.localGraph.deleteEdges ({s(a, b)} : Set (Sym2 V)))
        (P.left (E.recordAt j).index)
        (P.right (E.recordAt j).index) := by
    exact
      ⟨PackingSplice.perfectPacking
        L.red X RdeleteLocal
        (P.left_right_disjoint (E.recordAt j).index)
        hRdeleteStay hkeepRed⟩
  have hblueOriginal :
      RoutableIn
        (L.localGraph.deleteEdges ({s(a, b)} : Set (Sym2 V)))
        (physicalLeft (E.recordAt j).label (E.recordAt j).cut)
        (physicalRight (E.recordAt j).label (E.recordAt j).cut) := by
    exact
      ⟨PackingSplice.perfectPacking
        L.blue X QdeleteLocal
        (labelledImage_disjoint
          (E.recordAt j).label (E.recordAt j).cut.disjoint)
        hQdeleteStay hkeepBlue⟩
  exact
    (L.deleteEdge_failure habLocal)
      ⟨by simpa [L] using hredOriginal,
        by simpa [L] using hblueOriginal⟩

/-- Source Claim 5.4: after contracting every maximal
`200 * N^4`-bounded red segment, the resulting finite edge-indexed graph has
edge connectivity at least `N`. -/
theorem segmentQuotient_isEdgeConnected
    {N : ℕ}
    (E : ExpanderBlocks P N)
    (hbudget :
      N *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hheight : 2 ≤ h)
    (hrecords : 0 < E.finalState.records.length)
    (hN : 0 < N)
    (hB : 0 < 200 * N ^ 4)
    (fallback :
      ExactRailSegmentIndex E hbudget hrecords (200 * N ^ 4) hB) :
    (E.segmentQuotient
      hbudget hrecords (200 * N ^ 4) hB fallback).IsEdgeConnected N := by
  classical
  intro S hS hproper
  by_cases hno :
      E.NoCompleteRail hbudget hrecords (200 * N ^ 4) hB S
  · have hphysical :=
      E.segmentBoundary_card_ge_of_noCompleteRail
        hbudget hrecords N hN hB fallback S hS hno
    rw [E.segmentQuotient_boundary_card]
    exact hphysical
  · have hx :
        ∃ x : Fin h,
          E.RailContainedIn
            hbudget hrecords (200 * N ^ 4) hB S x := by
      simpa only [NoCompleteRail, not_forall, not_not] using hno
    obtain ⟨x, hx⟩ := hx
    by_cases hnoComp :
        E.NoCompleteRail
          hbudget hrecords (200 * N ^ 4) hB Sᶜ
    · have hcomp : (Sᶜ :
          Finset
            (ExactRailSegmentIndex
              E hbudget hrecords (200 * N ^ 4) hB)).Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro hempty
        apply hproper
        have := congrArg
          (fun T :
            Finset
              (ExactRailSegmentIndex
                E hbudget hrecords (200 * N ^ 4) hB) => Tᶜ)
          hempty
        simpa using this
      have hphysical :=
        E.segmentBoundary_card_ge_of_noCompleteRail
          hbudget hrecords N hN hB fallback Sᶜ hcomp hnoComp
      have hquotient :
          N ≤
            ((E.segmentQuotient
              hbudget hrecords (200 * N ^ 4) hB fallback).boundary
                Sᶜ).card := by
        rw [E.segmentQuotient_boundary_card]
        exact hphysical
      rw [FiniteEdgeIndexedGraph.boundary_compl] at hquotient
      exact hquotient
    · have hy :
          ∃ y : Fin h,
            E.RailContainedIn
              hbudget hrecords (200 * N ^ 4) hB Sᶜ y := by
        simpa only [NoCompleteRail, not_forall, not_not] using hnoComp
      obtain ⟨y, hy⟩ := hy
      have hphysical :=
        E.segmentBoundary_card_ge_of_completeRails
          hbudget hheight hrecords (200 * N ^ 4) hB
          fallback S x y hx hy
      rw [E.segmentQuotient_boundary_card]
      exact hphysical

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
