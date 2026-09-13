import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax17Proofs.Source.Crossbar
import Lax17Proofs.Source.CrossbarPower

namespace Lax17Proofs

universe u v w

/-!
# Pseudo-grids

This file formalizes the pseudo-grid object introduced in Section 4.1 of
Chuzhoy--Tan.  A pseudo-grid is defined relative to the two path families
`P` and `Q` used in Theorem 4.1: `P` is the family of disjoint `A`-to-`B`
paths, and `Q` is the family of disjoint `A`-to-`X` paths.

The theorem at the end of the file proves the final assembly step of
Theorem 4.1 from the iteration data produced by the contraction/Menger
argument.  The self-contained Section 4.1 proof is completed in
`Theorem41.lean`, which constructs those separator choices and lifts successful
contracted linkages to crossbars.
-/

namespace SimpleGraph


namespace GraphPath

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- A path segment has an endpoint in a terminal set and is internally
disjoint from that set.

This is the endpoint convention used for the `Q'`-segments in the pseudo-grid
construction.  It deliberately allows a trivial one-vertex segment at a
terminal in `X`: in the Section 4.1 iteration a separator trace may already
contain the `X` endpoint of a matched `Q`-path, and then the last-hit suffix is
such a trivial segment. -/
def ExactlyOneEndpointIn (P : GraphPath G) (X : Finset V) : Prop :=
  (P.source ∈ X ∨ P.target ∈ X) ∧ P.InternallyDisjointFromSet X

theorem exactlyOneEndpointIn_of_target_mem_of_internal
    (P : GraphPath G) {X : Finset V}
    (htarget : P.target ∈ X)
    (hinternal : P.InternallyDisjointFromSet X) :
    P.ExactlyOneEndpointIn X :=
  ⟨Or.inr htarget, hinternal⟩

/-- If every vertex of `X` has degree one, a path ending in `X` satisfies the
pseudo-grid endpoint convention. -/
theorem exactlyOneEndpointIn_of_target_mem_of_degree_one
    (P : GraphPath G) {X : Finset V}
    (htarget : P.target ∈ X)
    (hdegree : ∀ x ∈ X, DegreeEquals G x 1) :
    P.ExactlyOneEndpointIn X := by
  refine P.exactlyOneEndpointIn_of_target_mem_of_internal htarget ?_
  intro v hvPath hvX
  exact GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
    P (hdegree v hvX) hvPath

/-- A last-hit suffix of a path ending in `X` again satisfies the pseudo-grid
endpoint convention, provided vertices of `X` have degree one. -/
theorem cleanSuffixFromSet_exactlyOneEndpointIn_of_target_mem_of_degree_one
    (P : GraphPath G) (U : Finset V) (hne : (P.vertexSet ∩ U).Nonempty)
    {X : Finset V}
    (htarget : P.target ∈ X)
    (hdegree : ∀ x ∈ X, DegreeEquals G x 1) :
    (P.cleanSuffixFromSet U hne).ExactlyOneEndpointIn X := by
  exact (P.cleanSuffixFromSet U hne).exactlyOneEndpointIn_of_target_mem_of_degree_one
    (by simpa using htarget) hdegree

end GraphPath

/-- The index of the `Q`-path whose `A`-endpoint is the `A`-endpoint of the
`P`-path indexed by `i`.

Both path packings are perfect and oriented out of `A`, so this is the formal
version of the paper's notation `Q_P`. -/
noncomputable def PerfectPathPacking.matchedSourceIndex
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B X : Finset V}
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X)
    (i : P.Index) : Q.Index :=
  Q.indexOfSource ⟨(P.path i).source, P.source_mem i⟩

namespace PerfectPathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B X : Finset V}

@[simp] theorem source_matchedSourceIndex
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X)
    (i : P.Index) :
    (Q.path (P.matchedSourceIndex Q i)).source = (P.path i).source := by
  have h :=
    congrArg Subtype.val
      (Q.source_indexOfSource ⟨(P.path i).source, P.source_mem i⟩)
  simpa [matchedSourceIndex] using h

theorem matchedSourceIndex_injective
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X) :
    Function.Injective (P.matchedSourceIndex Q) := by
  intro i j hij
  apply P.source_bijective.1
  apply Subtype.ext
  calc
    (P.path i).source = (Q.path (P.matchedSourceIndex Q i)).source :=
      (P.source_matchedSourceIndex Q i).symm
    _ = (Q.path (P.matchedSourceIndex Q j)).source := by rw [hij]
    _ = (P.path j).source := P.source_matchedSourceIndex Q j

end PerfectPathPacking

/-- The union of the `P`-indices selected by the rows of a pseudo-grid. -/
noncomputable def pseudoGridReservedUnion
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) : Finset ι :=
  Finset.univ.biUnion R

/-- The `P`-indices not selected by any row of a pseudo-grid. -/
noncomputable def pseudoGridRemaining
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) : Finset ι :=
  Finset.univ \ pseudoGridReservedUnion R

/-- The row indices strictly before `i`. -/
noncomputable def pseudoGridPrefixRows {D : ℕ} (i : Fin D) : Finset (Fin D) :=
  Finset.univ.filter fun j : Fin D => j.val < i.val

/-- The union of all rows before iteration `i`. -/
noncomputable def pseudoGridPrefixReservedUnion
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i : Fin D) : Finset ι :=
  (pseudoGridPrefixRows i).biUnion R

/-- The `P`-paths still remaining just before row `i` is selected. -/
noncomputable def pseudoGridRemainingBefore
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i : Fin D) : Finset ι :=
  Finset.univ \ pseudoGridPrefixReservedUnion R i

/-- If every pseudo-grid row has size at most `b`, then their union has size
at most `D * b`. -/
theorem pseudoGridReservedUnion_card_le
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D b : ℕ}
    (R : Fin D → Finset ι) (hR : ∀ i : Fin D, (R i).card ≤ b) :
    (pseudoGridReservedUnion R).card ≤ D * b := by
  classical
  simpa [pseudoGridReservedUnion, Nat.mul_comm] using
    (Finset.card_biUnion_le_card_mul
      (Finset.univ : Finset (Fin D)) R b (by
        intro i _hi
        exact hR i))

theorem subset_prefixReservedUnion_of_lt
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) {i j : Fin D} (hij : i.val < j.val) :
    R i ⊆ pseudoGridPrefixReservedUnion R j := by
  classical
  intro x hx
  exact Finset.mem_biUnion.2
    ⟨i, by
      simp [pseudoGridPrefixRows]
      exact hij, hx⟩

theorem pseudoGridPrefixReservedUnion_subset_reservedUnion
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i : Fin D) :
    pseudoGridPrefixReservedUnion R i ⊆ pseudoGridReservedUnion R := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.1 hx with ⟨j, _hjPrefix, hxj⟩
  exact Finset.mem_biUnion.2 ⟨j, by simp, hxj⟩

theorem pseudoGridRemaining_subset_remainingBefore
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i : Fin D) :
    pseudoGridRemaining R ⊆ pseudoGridRemainingBefore R i := by
  classical
  intro x hx
  rcases Finset.mem_sdiff.1 hx with ⟨hxuniv, hxnot⟩
  exact Finset.mem_sdiff.2
    ⟨hxuniv, fun hxprefix =>
      hxnot (pseudoGridPrefixReservedUnion_subset_reservedUnion R i hxprefix)⟩

theorem not_mem_reserved_of_mem_remaining
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i : Fin D) {x : ι}
    (hx : x ∈ pseudoGridRemaining R) :
    x ∉ R i := by
  classical
  intro hxi
  exact (Finset.mem_sdiff.1 hx).2
    (Finset.mem_biUnion.2 ⟨i, by simp, hxi⟩)

/-- Updating row `i` does not change the prefix union before row `j` when
`i` is not strictly before `j`. -/
theorem pseudoGridPrefixReservedUnion_update_eq_of_not_lt
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i j : Fin D) (S : Finset ι)
    (hij : ¬ i.val < j.val) :
    pseudoGridPrefixReservedUnion (Function.update R i S) j =
      pseudoGridPrefixReservedUnion R j := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_biUnion.1 hx with ⟨r, hr, hxr⟩
    have hri : r ≠ i := by
      intro h
      have hlt : i.val < j.val := by
        simpa [h] using (by
          simpa [pseudoGridPrefixRows] using hr : r.val < j.val)
      exact hij hlt
    exact Finset.mem_biUnion.2
      ⟨r, hr, by simpa [Function.update, hri] using hxr⟩
  · intro hx
    rcases Finset.mem_biUnion.1 hx with ⟨r, hr, hxr⟩
    have hri : r ≠ i := by
      intro h
      have hlt : i.val < j.val := by
        simpa [h] using (by
          simpa [pseudoGridPrefixRows] using hr : r.val < j.val)
      exact hij hlt
    exact Finset.mem_biUnion.2
      ⟨r, hr, by simpa [Function.update, hri] using hxr⟩

/-- Updating row `i` does not change the remaining set before row `j` when
`i` is not strictly before `j`. -/
theorem pseudoGridRemainingBefore_update_eq_of_not_lt
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i j : Fin D) (S : Finset ι)
    (hij : ¬ i.val < j.val) :
    pseudoGridRemainingBefore (Function.update R i S) j =
      pseudoGridRemainingBefore R j := by
  simp [pseudoGridRemainingBefore,
    pseudoGridPrefixReservedUnion_update_eq_of_not_lt R i j S hij]

/-- Updating a row does not change the remaining set before that same row. -/
theorem pseudoGridRemainingBefore_update_self
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) (i : Fin D) (S : Finset ι) :
    pseudoGridRemainingBefore (Function.update R i S) i =
      pseudoGridRemainingBefore R i :=
  pseudoGridRemainingBefore_update_eq_of_not_lt R i i S (Nat.lt_irrefl i.val)

/-- Updating a later row does not change the remaining set before an earlier
row. -/
theorem pseudoGridRemainingBefore_update_later
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι) {i j : Fin D} (S : Finset ι)
    (hji : j.val < i.val) :
    pseudoGridRemainingBefore (Function.update R i S) j =
      pseudoGridRemainingBefore R j :=
  pseudoGridRemainingBefore_update_eq_of_not_lt R i j S (by omega)

/-- If every row is selected from the paths remaining before that row, then
the rows are pairwise disjoint. -/
theorem pseudoGridReserved_disjoint_of_subset_remainingBefore
    {ι : Type u} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (R : Fin D → Finset ι)
    (hR : ∀ i : Fin D, R i ⊆ pseudoGridRemainingBefore R i) :
    ∀ ⦃i j : Fin D⦄, i ≠ j → Disjoint (R i) (R j) := by
  classical
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne (show i.val ≠ j.val by
    intro hval
    exact hij (Fin.ext hval)) with hijlt | hjilt
  · have hxPrefix : x ∈ pseudoGridPrefixReservedUnion R j :=
      subset_prefixReservedUnion_of_lt R hijlt hxi
    have hxRemaining := hR j hxj
    exact (Finset.mem_sdiff.mp hxRemaining).2 hxPrefix
  · have hxPrefix : x ∈ pseudoGridPrefixReservedUnion R i :=
      subset_prefixReservedUnion_of_lt R hjilt hxj
    have hxRemaining := hR i hxi
    exact (Finset.mem_sdiff.mp hxRemaining).2 hxPrefix

/-- A selected `Q`-segment intersects one of the `P`-paths in a row. -/
def pseudoGridIntersectsRow
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B : Finset V} {D : ℕ}
    (P : PerfectPathPacking G A B) {J : Type*}
    (R : Fin D → Finset P.Index) (Qseg : J → GraphPath G)
    (i : Fin D) (j : J) : Prop :=
  ∃ p ∈ R i, ¬ Disjoint (P.path p).vertexSet (Qseg j).vertexSet

/-- Chuzhoy--Tan pseudo-grid of depth `D`, relative to the fixed path families
`P` and `Q`.

The family `reserved i` is the row `R_i`.  The selected paths `qPath` are the
subpaths forming `Q'`; each one is attached to a distinct remaining path of
`P`, and it is required to lie on the corresponding matched `Q_P` path.  The
two fields `remaining_disjoint_qPath` and `few_qPath_miss_reserved` are the
paper's properties P1 and P2.
-/
structure PseudoGrid {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (A B X : Finset V) (g D : ℕ)
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X) where
  /-- The depth is positive, matching the paper's `D > 0`. -/
  depth_pos : 0 < D
  /-- The row sets `R_i` of selected `P`-paths. -/
  reserved : Fin D → Finset P.Index
  /-- Each row has size at most `g^2`. -/
  reserved_card_le : ∀ i : Fin D, (reserved i).card ≤ g ^ 2
  /-- Distinct rows select disjoint sets of `P`-paths. -/
  reserved_disjoint :
    ∀ ⦃i j : Fin D⦄, i ≠ j → Disjoint (reserved i) (reserved j)
  /-- Index type for the selected subpaths `Q'`. -/
  QIndex : Type
  /-- The selected subpaths form a finite family. -/
  [qFintype : Fintype QIndex]
  /-- The selected subpath index type has decidable equality. -/
  [qDecidableEq : DecidableEq QIndex]
  /-- The paper keeps exactly `⌊κ/4⌋` selected subpaths.  Since `P.card = κ`,
  this is represented as natural-number division by `4`. -/
  q_card : Fintype.card QIndex = P.card / 4
  /-- The remaining `P`-path to which a selected `Q`-segment belongs. -/
  parent : QIndex → P.Index
  /-- Every parent path lies outside the reserved rows. -/
  parent_remaining :
    ∀ j : QIndex, parent j ∈ pseudoGridRemaining reserved
  /-- Distinct selected `Q`-segments come from distinct matched `Q_P` paths. -/
  parent_injective : Function.Injective parent
  /-- The selected `Q'` segments. -/
  qPath : QIndex → GraphPath G
  /-- Each selected segment is contained in the corresponding original `Q_P`
  path.  This records the “sub-path of a distinct path of `{Q_P}`” part of the
  definition at the vertex-set level. -/
  qPath_subset_matched :
    ∀ j : QIndex,
      (qPath j).vertexSet ⊆
        (Q.path (P.matchedSourceIndex Q (parent j))).vertexSet
  /-- Each selected segment is an actual subpath of the corresponding original
  `Q_P` path, at the edge-set level.  This is needed in Section 4.2 when
  replacing part of `P` by a linkage in `H'`: edges contributed by retained
  `Q''` segments must already be edges of the original `Q` family. -/
  qPath_edgeSet_subset_matched :
    ∀ j : QIndex,
      (qPath j).edgeSet ⊆
        (Q.path (P.matchedSourceIndex Q (parent j))).edgeSet
  /-- Each selected segment has exactly one endpoint in `X`. -/
  qPath_exactly_one_endpoint_in_X :
    ∀ j : QIndex, (qPath j).ExactlyOneEndpointIn X
  /-- The selected `Q'` segments are node-disjoint. -/
  qPath_nodeDisjoint :
    Pairwise fun i j : QIndex => GraphPath.NodeDisjoint (qPath i) (qPath j)
  /-- Property P1: every remaining `P`-path is disjoint from every selected
  `Q'` segment. -/
  remaining_disjoint_qPath :
    ∀ (p : P.Index), p ∈ pseudoGridRemaining reserved →
      ∀ j : QIndex, GraphPath.NodeDisjoint (P.path p) (qPath j)
  /-- Property P2: for each row `R_i`, all but at most `2g^2` selected
  `Q'` segments intersect a path of `R_i`. -/
  few_qPath_miss_reserved :
    ∀ i : Fin D,
      ∃ miss : Finset QIndex,
        miss.card ≤ 2 * g ^ 2 ∧
          ∀ j : QIndex,
            ¬ pseudoGridIntersectsRow P reserved qPath i j → j ∈ miss

namespace PseudoGrid

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

instance (Γ : PseudoGrid G A B X g D P Q) : Fintype Γ.QIndex :=
  Γ.qFintype

instance (Γ : PseudoGrid G A B X g D P Q) : DecidableEq Γ.QIndex :=
  Γ.qDecidableEq

/-- The selected row indices as a single finite set. -/
noncomputable def reservedUnion (Γ : PseudoGrid G A B X g D P Q) :
    Finset P.Index :=
  pseudoGridReservedUnion Γ.reserved

/-- The paths of `P` left after removing the rows of the pseudo-grid. -/
noncomputable def remaining (Γ : PseudoGrid G A B X g D P Q) :
    Finset P.Index :=
  pseudoGridRemaining Γ.reserved

@[simp] theorem q_card_eq (Γ : PseudoGrid G A B X g D P Q) :
    Fintype.card Γ.QIndex = P.card / 4 :=
  Γ.q_card

theorem parent_mem_remaining (Γ : PseudoGrid G A B X g D P Q)
    (j : Γ.QIndex) :
    Γ.parent j ∈ Γ.remaining :=
  Γ.parent_remaining j

/-- The union of all row path indices has the expected `D * g^2` upper bound. -/
theorem reservedUnion_card_le (Γ : PseudoGrid G A B X g D P Q) :
    Γ.reservedUnion.card ≤ D * g ^ 2 := by
  simpa [reservedUnion] using
    pseudoGridReservedUnion_card_le Γ.reserved Γ.reserved_card_le

theorem qPath_intersects_row_iff
    (Γ : PseudoGrid G A B X g D P Q) (i : Fin D) (j : Γ.QIndex) :
    pseudoGridIntersectsRow P Γ.reserved Γ.qPath i j ↔
      ∃ p ∈ Γ.reserved i,
        ¬ Disjoint (P.path p).vertexSet (Γ.qPath j).vertexSet :=
  Iff.rfl

end PseudoGrid

/-- The data produced when the iterative proof of Theorem 4.1 never returns a
crossbar.

For each row `i`, the set `bad i` contains the paths that are not `i`-good,
and `terminalBad` contains the paths that are not good in the final iteration.
The field `good_intersects_reserved` is exactly the final comparison of
segments in the paper: a path that is both `i`-good and final-good intersects
some path of `R_i`.
-/
structure PseudoGridIterationData {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (A B X : Finset V) (g D : ℕ)
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X) where
  depth_pos : 0 < D
  reserved : Fin D → Finset P.Index
  reserved_card_le : ∀ i : Fin D, (reserved i).card ≤ g ^ 2
  reserved_disjoint :
    ∀ ⦃i j : Fin D⦄, i ≠ j → Disjoint (reserved i) (reserved j)
  QIndex : Type
  [qFintype : Fintype QIndex]
  [qDecidableEq : DecidableEq QIndex]
  q_card : Fintype.card QIndex = P.card / 4
  parent : QIndex → P.Index
  parent_remaining :
    ∀ j : QIndex, parent j ∈ pseudoGridRemaining reserved
  parent_injective : Function.Injective parent
  qPath : QIndex → GraphPath G
  qPath_subset_matched :
    ∀ j : QIndex,
      (qPath j).vertexSet ⊆
        (Q.path (P.matchedSourceIndex Q (parent j))).vertexSet
  qPath_edgeSet_subset_matched :
    ∀ j : QIndex,
      (qPath j).edgeSet ⊆
        (Q.path (P.matchedSourceIndex Q (parent j))).edgeSet
  qPath_exactly_one_endpoint_in_X :
    ∀ j : QIndex, (qPath j).ExactlyOneEndpointIn X
  qPath_nodeDisjoint :
    Pairwise fun i j : QIndex => GraphPath.NodeDisjoint (qPath i) (qPath j)
  remaining_disjoint_qPath :
    ∀ (p : P.Index), p ∈ pseudoGridRemaining reserved →
      ∀ j : QIndex, GraphPath.NodeDisjoint (P.path p) (qPath j)
  bad : Fin D → Finset QIndex
  bad_card_le : ∀ i : Fin D, (bad i).card ≤ g ^ 2
  terminalBad : Finset QIndex
  terminalBad_card_le : terminalBad.card ≤ g ^ 2
  good_intersects_reserved :
    ∀ (i : Fin D) (j : QIndex),
      j ∉ bad i →
        j ∉ terminalBad →
          pseudoGridIntersectsRow P reserved qPath i j

namespace PseudoGridIterationData

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

instance (I : PseudoGridIterationData G A B X g D P Q) : Fintype I.QIndex :=
  I.qFintype

instance (I : PseudoGridIterationData G A B X g D P Q) : DecidableEq I.QIndex :=
  I.qDecidableEq

/-- A selected segment that misses row `i` must lie in one of the two bad
sets used in the paper's final counting argument. -/
theorem miss_reserved_mem_bad_union
    (I : PseudoGridIterationData G A B X g D P Q)
    (i : Fin D) {j : I.QIndex}
    (hmiss : ¬ pseudoGridIntersectsRow P I.reserved I.qPath i j) :
    j ∈ I.bad i ∪ I.terminalBad := by
  classical
  by_cases hb : j ∈ I.bad i
  · exact Finset.mem_union_left _ hb
  · by_cases ht : j ∈ I.terminalBad
    · exact Finset.mem_union_right _ ht
    · exact False.elim (hmiss (I.good_intersects_reserved i j hb ht))

/-- The paper's final `g^2 + g^2` counting step proving property P2. -/
theorem bad_union_card_le
    (I : PseudoGridIterationData G A B X g D P Q)
    (i : Fin D) :
    (I.bad i ∪ I.terminalBad).card ≤ 2 * g ^ 2 := by
  classical
  calc
    (I.bad i ∪ I.terminalBad).card
        ≤ (I.bad i).card + I.terminalBad.card := Finset.card_union_le _ _
    _ ≤ g ^ 2 + g ^ 2 := Nat.add_le_add (I.bad_card_le i) I.terminalBad_card_le
    _ = 2 * g ^ 2 := by omega

/-- The witness form of property P2 for a row. -/
theorem few_qPath_miss_reserved
    (I : PseudoGridIterationData G A B X g D P Q)
    (i : Fin D) :
    ∃ miss : Finset I.QIndex,
      miss.card ≤ 2 * g ^ 2 ∧
        ∀ j : I.QIndex,
          ¬ pseudoGridIntersectsRow P I.reserved I.qPath i j → j ∈ miss := by
  exact ⟨I.bad i ∪ I.terminalBad, I.bad_union_card_le i,
    fun j hmiss => I.miss_reserved_mem_bad_union i hmiss⟩

/-- The union of all rows produced by the iteration has size at most
`D * g^2`. -/
theorem reservedUnion_card_le
    (I : PseudoGridIterationData G A B X g D P Q) :
    (pseudoGridReservedUnion I.reserved).card ≤ D * g ^ 2 := by
  exact pseudoGridReservedUnion_card_le I.reserved I.reserved_card_le

/-- Convert the no-crossbar iteration data into a pseudo-grid. -/
noncomputable def toPseudoGrid
    (I : PseudoGridIterationData G A B X g D P Q) :
    PseudoGrid G A B X g D P Q where
  depth_pos := I.depth_pos
  reserved := I.reserved
  reserved_card_le := I.reserved_card_le
  reserved_disjoint := I.reserved_disjoint
  QIndex := I.QIndex
  q_card := I.q_card
  parent := I.parent
  parent_remaining := I.parent_remaining
  parent_injective := I.parent_injective
  qPath := I.qPath
  qPath_subset_matched := I.qPath_subset_matched
  qPath_edgeSet_subset_matched := I.qPath_edgeSet_subset_matched
  qPath_exactly_one_endpoint_in_X := I.qPath_exactly_one_endpoint_in_X
  qPath_nodeDisjoint := I.qPath_nodeDisjoint
  remaining_disjoint_qPath := I.remaining_disjoint_qPath
  few_qPath_miss_reserved := I.few_qPath_miss_reserved

end PseudoGridIterationData

/-- The number of edges in the union of two perfect path packings.

This is the quantity minimized in the hypothesis of Theorem 4.1.  The paper
counts edges in the union of all paths in `P ∪ Q`; using the union of the two
formal edge sets removes duplicate edges automatically. -/
noncomputable def PerfectPathPacking.pairUnionEdgeCount
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B X : Finset V}
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X) : ℕ :=
  (P.toPathPacking.edgeSet ∪ Q.toPathPacking.edgeSet).card

/-- The chosen pair `(P,Q)` minimizes the number of edges in the union of the
two path families among all perfect `A`-to-`B` and `A`-to-`X` path families.
-/
def PerfectPathPacking.IsMinimumTheorem41Pair
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B X : Finset V}
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X) : Prop :=
  ∀ (P' : PerfectPathPacking G A B) (Q' : PerfectPathPacking G A X),
    P.pairUnionEdgeCount Q ≤ P'.pairUnionEdgeCount Q'

/-- Among all perfect `A`-to-`B` and `A`-to-`X` path-packing pairs, one
minimizes the edge count used in Theorem 4.1.

The proof only uses well-foundedness of `Nat`: once one admissible pair exists,
the set of possible edge-union counts has a least element. -/
theorem PerfectPathPacking.exists_minimumTheorem41Pair
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B X : Finset V}
    (P₀ : PerfectPathPacking G A B) (Q₀ : PerfectPathPacking G A X) :
    ∃ (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X),
      P.IsMinimumTheorem41Pair Q := by
  classical
  let HasCount : ℕ → Prop := fun n =>
    ∃ (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X),
      P.pairUnionEdgeCount Q = n
  have hExists : ∃ n : ℕ, HasCount n :=
    ⟨P₀.pairUnionEdgeCount Q₀, P₀, Q₀, rfl⟩
  rcases Nat.find_spec hExists with ⟨P, Q, hPQ⟩
  refine ⟨P, Q, ?_⟩
  intro P' Q'
  have hP' : HasCount (P'.pairUnionEdgeCount Q') := ⟨P', Q', rfl⟩
  have hmin : Nat.find hExists ≤ P'.pairUnionEdgeCount Q' :=
    Nat.find_min' (H := hExists) hP'
  simpa [hPQ] using hmin

/-- The explicit hypotheses of Chuzhoy--Tan Theorem 4.1, with the two path
families represented as perfect oriented packings.

This is the internal bundled form used by the proof in `Theorem41.lean`.
The paper's minimum-pair hypothesis is retained as data, even though the
Section 4.1 dichotomy itself is proved in a slightly stronger form that does
not consume it. -/
structure Theorem41Setup {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (A B X : Finset V) (g kappa D : ℕ)
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X) where
  /-- The grid parameter satisfies `g >= 2`. -/
  two_le_g : 2 ≤ g
  /-- In the paper, `g` is an integral power of two. -/
  g_power_two : CrossbarContract.IsPowerOfTwo g
  /-- The three terminal sets have the common size `κ`. -/
  A_card : A.card = kappa
  B_card : B.card = kappa
  X_card : X.card = kappa
  /-- The terminal sets are pairwise disjoint. -/
  disjoint_A_B : Disjoint A B
  /-- The terminal sets are pairwise disjoint. -/
  disjoint_A_X : Disjoint A X
  /-- The terminal sets are pairwise disjoint. -/
  disjoint_B_X : Disjoint B X
  /-- Every `X` terminal has degree one in `H`. -/
  degree_X : ∀ x ∈ X, DegreeEquals G x 1
  /-- The `A`-to-`B` path family has size `κ`. -/
  P_card : P.card = kappa
  /-- The `A`-to-`X` path family has size `κ`. -/
  Q_card : Q.card = kappa
  /-- The path-pair is chosen with minimum total edge-union size. -/
  minimal_pair : P.IsMinimumTheorem41Pair Q
  /-- The depth parameter is positive. -/
  D_pos : 1 ≤ D
  /-- The depth parameter is at most `κ/(2g^2)`. -/
  D_le : D ≤ kappa / (2 * g ^ 2)

namespace Theorem41Setup

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B X : Finset V}
variable {g kappa D : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

/-- In the setup of Theorem 4.1, no `P`-path contains a vertex of `X`.

The paper says this can be assumed because every vertex of `X` has degree one.
With perfect packings, it follows directly: a degree-one vertex on a simple
path is an endpoint, while `P`-path endpoints lie in `A` and `B`, both
disjoint from `X`. -/
theorem P_path_disjoint_X
    (S : Theorem41Setup G A B X g kappa D P Q) (i : P.Index) :
    Disjoint (P.path i).vertexSet X := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvX
  have hend :
      (P.path i).IsEndpoint v :=
    GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
      (P.path i) (S.degree_X v hvX) hvP
  rcases hend with hsource | htarget
  · have hvA : v ∈ A := by
      simpa [hsource.symm] using P.source_mem i
    exact Finset.disjoint_left.mp S.disjoint_A_X hvA hvX
  · have hvB : v ∈ B := by
      simpa [htarget.symm] using P.target_mem i
    exact Finset.disjoint_left.mp S.disjoint_B_X hvB hvX

/-- In the setup of Theorem 4.1, every `Q`-path has an `X` endpoint and is
internally disjoint from `X`: its target endpoint lies in `X`, and any `X`
vertex on the path has degree one, hence is an endpoint of the simple path. -/
theorem Q_path_exactlyOneEndpointIn_X
    (S : Theorem41Setup G A B X g kappa D P Q) (i : Q.Index) :
    (Q.path i).ExactlyOneEndpointIn X := by
  exact (Q.path i).exactlyOneEndpointIn_of_target_mem_of_degree_one
    (Q.target_mem i) S.degree_X

/-- The theorem's positive-depth hypothesis as a strict inequality. -/
theorem D_pos_strict (S : Theorem41Setup G A B X g kappa D P Q) : 0 < D :=
  S.D_pos

end Theorem41Setup

/-- The conclusion of Chuzhoy--Tan Theorem 4.1 in pseudo-grid language. -/
def Theorem41Conclusion {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (A B X : Finset V) (g D : ℕ)
    (P : PerfectPathPacking G A B) (Q : PerfectPathPacking G A X) : Prop :=
  Nonempty (Crossbar G A B X (g ^ 2)) ∨
    Nonempty (PseudoGrid G A B X g D P Q)

/-- Theorem 4.1 outcome produced from the explicit iteration data.

This is the proved, contract-free part of Section 4.1: after the Menger
iterations have either supplied a crossbar or supplied the no-crossbar data,
the second outcome is a pseudo-grid satisfying properties P1 and P2. -/
theorem crossbar_or_pseudoGrid_of_theorem41_iterationData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B X : Finset V} {g D : ℕ}
    {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}
    (h :
      Nonempty (Crossbar G A B X (g ^ 2)) ∨
        Nonempty (PseudoGridIterationData G A B X g D P Q)) :
    Nonempty (Crossbar G A B X (g ^ 2)) ∨
      Nonempty (PseudoGrid G A B X g D P Q) := by
  rcases h with hcross | hiter
  · exact Or.inl hcross
  · rcases hiter with ⟨I⟩
    exact Or.inr ⟨I.toPseudoGrid⟩

/-- Named Section 4.1 form of
`crossbar_or_pseudoGrid_of_theorem41_iterationData`.

The hypotheses bundled in `PseudoGridIterationData` are exactly the data left
after the proof of Chuzhoy--Tan Theorem 4.1 has run the contraction/Menger
iterations and has not found a crossbar. -/
theorem theorem_four_one_of_iterationData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B X : Finset V} {g D : ℕ}
    {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}
    (h :
      Nonempty (Crossbar G A B X (g ^ 2)) ∨
        Nonempty (PseudoGridIterationData G A B X g D P Q)) :
    Nonempty (Crossbar G A B X (g ^ 2)) ∨
      Nonempty (PseudoGrid G A B X g D P Q) :=
  crossbar_or_pseudoGrid_of_theorem41_iterationData h

/-- Theorem 4.1 with its paper hypotheses exposed, conditional on the
iteration data produced by the contracted-graph/Menger part of the proof.

This is kept as a small compatibility wrapper for modules that work directly
with already-constructed iteration data.  The unconditional Section 4.1 theorem
is `Theorem41Setup.theorem_four_one` in `Theorem41.lean`. -/
theorem theorem_four_one_of_setup_and_iterationData
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B X : Finset V} {g kappa D : ℕ}
    {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}
    (_setup : Theorem41Setup G A B X g kappa D P Q)
    (h :
      Nonempty (Crossbar G A B X (g ^ 2)) ∨
        Nonempty (PseudoGridIterationData G A B X g D P Q)) :
    Theorem41Conclusion G A B X g D P Q :=
  theorem_four_one_of_iterationData h

end SimpleGraph

end Lax17Proofs
