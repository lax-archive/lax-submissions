import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1Valley
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1PathGridGeometry

namespace Lax17Proofs

universe u v w

/-!
# Appendix B.1: the terminal sparse grid

This module turns the terminal full-column geometry from Claim B.3 into the
ordered path-grid geometry consumed by the concrete grid-minor assembly.

The first `h` active rows are used.  Columns are not assumed to arrive in
left-to-right order: they are canonically sorted by the vertex index of their
chosen contact on the first active row.  The active-strip no-cross theorem
transports that order to every retained row.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

open IndexedAuxiliaryPrefix

/-- Position of the `i`-th retained active row. -/
def terminalRowPosition (h : ℕ) (i : Fin h) : Fin (z h + 2) :=
  ⟨i.1 + 1, by
    dsimp [z]
    omega⟩

/-- The first active row, used to sort the columns. -/
def terminalLowerPosition (h : ℕ) : Fin (z h + 2) :=
  ⟨1, by
    dsimp [z]
    omega⟩

/-- A wrapper separating the lifted column order from the standard order on
the target `Fin h`. -/
@[ext] structure TerminalColumnLabel (h : ℕ) where
  index : Fin h
deriving DecidableEq, Fintype

namespace TerminalColumnLabel

def equivFin (h : ℕ) : TerminalColumnLabel h ≃ Fin h where
  toFun := TerminalColumnLabel.index
  invFun := fun i => ⟨i⟩
  left_inv := by
    intro i
    cases i
    rfl
  right_inv := by
    intro i
    rfl

theorem card (h : ℕ) :
    Fintype.card (TerminalColumnLabel h) = h := by
  rw [Fintype.card_congr (equivFin h)]
  simp

end TerminalColumnLabel

namespace FullBoundaryColumnFamily.TerminalGeometry

variable {h : ℕ}
variable {L : PerfectPathPacking G A B}
variable {C : AuxiliaryCorridor L (z h)}
variable {F : FullBoundaryColumnFamily L (z h) (Fin h) C}

/-- Numerical key of a column: its chosen contact on the first active row. -/
noncomputable def lowerContactKey
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (j : Fin h) : ℕ :=
  (C.rowPath (terminalLowerPosition h)).vertexIndex
    ((F.trace j).contactAtRow (terminalLowerPosition h))

/-- Distinct full columns have distinct first-active-row contacts, hence
distinct sorting keys. -/
theorem lowerContactKey_injective
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C) :
    Function.Injective (lowerContactKey F) := by
  classical
  intro i j hkey
  let Row := C.rowPath (terminalLowerPosition h)
  let xi := (F.trace i).contactAtRow (terminalLowerPosition h)
  let xj := (F.trace j).contactAtRow (terminalLowerPosition h)
  have hxiRow : xi ∈ Row.vertexSet := by
    simpa [Row, xi] using
      (F.trace i).contactAtRow_mem_row (terminalLowerPosition h)
  have hxjRow : xj ∈ Row.vertexSet := by
    simpa [Row, xj] using
      (F.trace j).contactAtRow_mem_row (terminalLowerPosition h)
  have hindices : Row.vertexIndex xi = Row.vertexIndex xj := by
    simpa [lowerContactKey, Row, xi, xj] using hkey
  have hxixj : xi = xj := by
    apply Row.before_antisymm
    · exact Row.before_iff_vertexIndex_le.2
        ⟨hxiRow, hxjRow, hindices.le⟩
    · exact Row.before_iff_vertexIndex_le.2
        ⟨hxjRow, hxiRow, hindices.ge⟩
  by_contra hij
  have hxiColumn : xi ∈ (F.column i).vertexSet := by
    simpa [xi] using
      (F.trace i).contactAtRow_mem_column (terminalLowerPosition h)
  have hxjColumn : xj ∈ (F.column j).vertexSet := by
    simpa [xj] using
      (F.trace j).contactAtRow_mem_column (terminalLowerPosition h)
  exact Finset.disjoint_left.mp (F.column_vertexSet_disjoint hij)
    hxiColumn (by simpa [hxixj] using hxjColumn)

/-- The data of the canonical left-to-right enumeration of columns. -/
structure ColumnOrdering
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C) where
  columnIndex : Fin h → Fin h
  columnIndex_bijective : Function.Bijective columnIndex
  key_strictMono :
    ∀ ⦃i j : Fin h⦄, i.1 < j.1 →
      lowerContactKey F (columnIndex i) <
        lowerContactKey F (columnIndex j)

/-- Sort all columns by the lifted lower-contact key and enumerate the sorted
finite order by `Fin h`. -/
noncomputable def columnOrdering
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C) :
    ColumnOrdering F := by
  classical
  let key : TerminalColumnLabel h → ℕ :=
    fun j => lowerContactKey F j.index
  have hkey : Function.Injective key := by
    intro i j hij
    apply TerminalColumnLabel.ext
    exact lowerContactKey_injective F hij
  letI : LinearOrder (TerminalColumnLabel h) :=
    LinearOrder.lift' key hkey
  let e : Fin h ≃o TerminalColumnLabel h :=
    Fintype.orderIsoFinOfCardEq
      (TerminalColumnLabel h) (TerminalColumnLabel.card h)
  refine
    { columnIndex := fun i => (e i).index
      columnIndex_bijective := ?_
      key_strictMono := ?_ }
  · constructor
    · intro i j hij
      apply e.injective
      apply TerminalColumnLabel.ext
      exact hij
    · intro j
      rcases e.surjective (TerminalColumnLabel.mk j) with ⟨i, hi⟩
      exact ⟨i, congrArg TerminalColumnLabel.index hi⟩
  · intro i j hij
    have hlt : e i < e j := e.lt_iff_lt.2 hij
    change key (e i) < key (e j) at hlt
    exact hlt

theorem columnOrdering_injective
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C) :
    Function.Injective (columnOrdering F).columnIndex :=
  (columnOrdering F).columnIndex_bijective.1

theorem columnOrdering_surjective
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C) :
    Function.Surjective (columnOrdering F).columnIndex :=
  (columnOrdering F).columnIndex_bijective.2

/-- Original column label occupying sorted position `j`. -/
noncomputable def orderedColumnIndex
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (j : Fin h) : Fin h :=
  (columnOrdering F).columnIndex j

/-- The `i`-th retained row. -/
def terminalRow
    (_F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (i : Fin h) : GraphPath G :=
  C.rowPath (terminalRowPosition h i)

/-- The `j`-th column in canonical left-to-right order. -/
noncomputable def terminalColumn
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (j : Fin h) : GraphPath G :=
  F.column (orderedColumnIndex F j)

/-- The row-column intersection used as the grid branch set. -/
noncomputable def terminalBlock
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (i j : Fin h) : Finset V :=
  (terminalRow F i).vertexSet ∩ (terminalColumn F j).vertexSet

theorem terminalRowPosition_injective :
    Function.Injective (terminalRowPosition h) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp [terminalRowPosition] at hval
  omega

theorem orderedColumnIndex_injective
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C) :
    Function.Injective (orderedColumnIndex F) :=
  columnOrdering_injective F

theorem terminalRow_nodeDisjoint
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    {i k : Fin h} (hik : i ≠ k) :
    (terminalRow F i).NodeDisjoint (terminalRow F k) := by
  exact C.rowPath_nodeDisjoint
    (by
      intro heq
      exact hik (terminalRowPosition_injective heq))

theorem terminalColumn_nodeDisjoint
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    {j l : Fin h} (hjl : j ≠ l) :
    (terminalColumn F j).NodeDisjoint (terminalColumn F l) := by
  exact F.pairwise_nodeDisjoint
    (by
      intro heq
      exact hjl (orderedColumnIndex_injective F heq))

theorem terminalBlock_nonempty
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (i j : Fin h) :
    (terminalBlock F i j).Nonempty := by
  let q := terminalRowPosition h i
  let c := orderedColumnIndex F j
  let x := (F.trace c).contactAtRow q
  refine ⟨x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simpa [terminalBlock, terminalRow, q, x] using
      (F.trace c).contactAtRow_mem_row q
  · simpa [terminalBlock, terminalColumn, c, x] using
      (F.trace c).contactAtRow_mem_column q

theorem terminalBlock_subset_row
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (i j : Fin h) :
    terminalBlock F i j ⊆ (terminalRow F i).vertexSet :=
  Finset.inter_subset_left

theorem terminalBlock_subset_column
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (i j : Fin h) :
    terminalBlock F i j ⊆ (terminalColumn F j).vertexSet :=
  Finset.inter_subset_right

theorem terminalBlock_disjoint_same_row
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    {i j l : Fin h} (hjl : j ≠ l) :
    Disjoint (terminalBlock F i j) (terminalBlock F i l) := by
  exact Disjoint.mono
    (terminalBlock_subset_column F i j)
    (terminalBlock_subset_column F i l)
    (by simpa [GraphPath.NodeDisjoint] using
      terminalColumn_nodeDisjoint F hjl)

theorem terminalBlock_disjoint_same_column
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    {i k j : Fin h} (hik : i ≠ k) :
    Disjoint (terminalBlock F i j) (terminalBlock F k j) := by
  exact Disjoint.mono
    (terminalBlock_subset_row F i j)
    (terminalBlock_subset_row F k j)
    (by simpa [GraphPath.NodeDisjoint] using
      terminalRow_nodeDisjoint F hik)

/-- The lifted first-active-row sort gives the corresponding strict contact
order on that row. -/
theorem lower_contact_before_of_lt
    (D : F.TerminalGeometry)
    {j l : Fin h} (hjl : j.1 < l.1) :
    (C.rowPath (terminalLowerPosition h)).Before
      ((F.trace (orderedColumnIndex F j)).contactAtRow
        (terminalLowerPosition h))
      ((F.trace (orderedColumnIndex F l)).contactAtRow
        (terminalLowerPosition h)) := by
  apply
    (C.rowPath (terminalLowerPosition h)).before_iff_vertexIndex_le.2
  refine
    ⟨(F.trace (orderedColumnIndex F j)).contactAtRow_mem_row _,
      (F.trace (orderedColumnIndex F l)).contactAtRow_mem_row _, ?_⟩
  exact Nat.le_of_lt ((columnOrdering F).key_strictMono hjl)

/-- No-cross transports the sorted first-active-row order to every corridor
row. -/
theorem ordered_contact_before
    (D : F.TerminalGeometry)
    {j l : Fin h} (hjl : j.1 < l.1)
    (q : Fin (z h + 2)) :
    (C.rowPath q).Before
      ((F.trace (orderedColumnIndex F j)).contactAtRow q)
      ((F.trace (orderedColumnIndex F l)).contactAtRow q) := by
  have hjlne : j ≠ l := by
    intro heq
    have := congrArg Fin.val heq
    omega
  have hcolumns :
      orderedColumnIndex F j ≠ orderedColumnIndex F l :=
    fun heq => hjlne (orderedColumnIndex_injective F heq)
  exact
    (D.commonOrder hcolumns (terminalLowerPosition h) q).mp
      (D.lower_contact_before_of_lt hjl)

/-- Along a monotone full column, contacts with strictly increasing rows occur
in the same order on the column. -/
theorem column_contact_before_of_row_lt
    (D : F.TerminalGeometry)
    (c : Fin h)
    {q r : Fin (z h + 2)} (hqr : q.1 < r.1) :
    (F.column c).Before
      ((F.trace c).contactAtRow q)
      ((F.trace c).contactAtRow r) := by
  let T := F.trace c
  have hindex :
      (T.contactAtRowIndex q).1 ≤ (T.contactAtRowIndex r).1 := by
    by_contra hnot
    have hreverse :
        (T.contactAtRowIndex r).1 ≤
          (T.contactAtRowIndex q).1 := by
      omega
    have hrows :=
      D.monotoneRows c
        (T.contactAtRowIndex r) (T.contactAtRowIndex q) hreverse
    rw [T.row_contactAtRowIndex, T.row_contactAtRowIndex] at hrows
    omega
  exact (T.contact_before_iff_le
    (T.contactAtRowIndex q) (T.contactAtRowIndex r)).2 hindex

/-- Each terminal block meets its host row. -/
theorem terminalBlock_meets_row
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (i j : Fin h) :
    ((terminalRow F i).vertexSet ∩ terminalBlock F i j).Nonempty := by
  rcases terminalBlock_nonempty F i j with ⟨x, hx⟩
  exact ⟨x, Finset.mem_inter.mpr
    ⟨terminalBlock_subset_row F i j hx, hx⟩⟩

/-- Each terminal block meets its host column. -/
theorem terminalBlock_meets_column
    (F : FullBoundaryColumnFamily L (z h) (Fin h) C)
    (i j : Fin h) :
    ((terminalColumn F j).vertexSet ∩ terminalBlock F i j).Nonempty := by
  rcases terminalBlock_nonempty F i j with ⟨x, hx⟩
  exact ⟨x, Finset.mem_inter.mpr
    ⟨terminalBlock_subset_column F i j hx, hx⟩⟩

/-- Intersection blocks occur in sorted-column order on each retained row. -/
noncomputable def rowBlockFamily
    (D : F.TerminalGeometry) (i : Fin h) :
    OrderedPathBlockFamily (terminalRow F i) h where
  block := terminalBlock F i
  meets := terminalBlock_meets_row F i
  block_subset := terminalBlock_subset_row F i
  pairwise_disjoint := by
    intro j l hjl
    exact terminalBlock_disjoint_same_row F hjl
  ordered := by
    intro j l hjl
    let q := terminalRowPosition h i
    let cj := orderedColumnIndex F j
    let cl := orderedColumnIndex F l
    have hjlne : j ≠ l := by
      intro heq
      have := congrArg Fin.val heq
      omega
    have hcols : cj ≠ cl :=
      fun heq => hjlne (orderedColumnIndex_injective F heq)
    apply graphPath_before_of_disjoint_traceConvex
      (F.column_vertexSet_disjoint hcols)
      (D.rowTraceConvex cj q)
      (D.rowTraceConvex cl q)
      (u0 := (F.trace cj).contactAtRow q)
      (w0 := (F.trace cl).contactAtRow q)
    · exact Finset.mem_inter.mpr
        ⟨(F.trace cj).contactAtRow_mem_row q,
          (F.trace cj).contactAtRow_mem_column q⟩
    · exact Finset.mem_inter.mpr
        ⟨(F.trace cl).contactAtRow_mem_row q,
          (F.trace cl).contactAtRow_mem_column q⟩
    · simpa [terminalBlock, terminalRow, terminalColumn, q, cj] using
        (terminalRow F i).lastHitVertex_mem_set
          (terminalBlock F i j) (terminalBlock_meets_row F i j)
    · simpa [terminalBlock, terminalRow, terminalColumn, q, cl] using
        (terminalRow F i).firstHitVertex_mem_set
          (terminalBlock F i l) (terminalBlock_meets_row F i l)
    · simpa [terminalRow, q, cj, cl] using
        D.ordered_contact_before hjl q

/-- Intersection blocks occur in active-row order on each sorted column. -/
noncomputable def columnBlockFamily
    (D : F.TerminalGeometry) (j : Fin h) :
    OrderedPathBlockFamily (terminalColumn F j) h where
  block := fun i => terminalBlock F i j
  meets := fun i => terminalBlock_meets_column F i j
  block_subset := fun i => terminalBlock_subset_column F i j
  pairwise_disjoint := by
    intro i k hik
    exact terminalBlock_disjoint_same_column F hik
  ordered := by
    intro i k hik
    let q := terminalRowPosition h i
    let r := terminalRowPosition h k
    let c := orderedColumnIndex F j
    have hikne : i ≠ k := by
      intro heq
      have := congrArg Fin.val heq
      omega
    have hrows : q ≠ r :=
      fun heq => hikne (terminalRowPosition_injective heq)
    apply graphPath_before_of_disjoint_traceConvex
      (C.rowPath_nodeDisjoint hrows)
      (D.columnTraceConvex c q)
      (D.columnTraceConvex c r)
      (u0 := (F.trace c).contactAtRow q)
      (w0 := (F.trace c).contactAtRow r)
    · exact Finset.mem_inter.mpr
        ⟨(F.trace c).contactAtRow_mem_column q,
          (F.trace c).contactAtRow_mem_row q⟩
    · exact Finset.mem_inter.mpr
        ⟨(F.trace c).contactAtRow_mem_column r,
          (F.trace c).contactAtRow_mem_row r⟩
    · simpa [terminalBlock, terminalRow, terminalColumn, q, c,
        Finset.inter_comm] using
        (terminalColumn F j).lastHitVertex_mem_set
          (terminalBlock F i j) (terminalBlock_meets_column F i j)
    · simpa [terminalBlock, terminalRow, terminalColumn, r, c,
        Finset.inter_comm] using
        (terminalColumn F j).firstHitVertex_mem_set
          (terminalBlock F k j) (terminalBlock_meets_column F k j)
    · apply D.column_contact_before_of_row_lt c
      dsimp [q, r, terminalRowPosition]
      omega

/-- The source-faithful terminal sparse-grid certificate. -/
noncomputable def toOrderedPathGridGeometry
    (D : F.TerminalGeometry) :
    OrderedPathGridGeometry G h where
  row := terminalRow F
  column := terminalColumn F
  row_nodeDisjoint := by
    intro i k hik
    exact terminalRow_nodeDisjoint F hik
  column_nodeDisjoint := by
    intro j l hjl
    exact terminalColumn_nodeDisjoint F hjl
  intersectionPath := fun i j =>
    D.rowIntersectionPath
      (orderedColumnIndex F j) (terminalRowPosition h i)
  intersectionPath_vertexSet := by
    intro i j
    simpa [terminalRow, terminalColumn] using
      D.rowIntersectionPath_vertexSet
        (orderedColumnIndex F j) (terminalRowPosition h i)
  rowBlocks := D.rowBlockFamily
  rowBlocks_block := by
    intro i j
    rfl
  columnBlocks := D.columnBlockFamily
  columnBlocks_block := by
    intro j i
    rfl

/-- Terminal bump/cross/hill-free geometry contains the requested grid
minor. -/
theorem containsGridMinor
    (D : F.TerminalGeometry) :
    ContainsGridMinor G h :=
  OrderedPathGridGeometry.containsGridMinor
    D.toOrderedPathGridGeometry

end FullBoundaryColumnFamily.TerminalGeometry

namespace FullBoundaryColumnFamily

/-- The terminal geometry actually produced by the active-row switching
argument.  Boundary rows are retained as anchors but are never switched, so
only crossings between two active rows are ruled out. -/
structure ActiveTerminalGeometry
    {activeCount : ℕ} {ι : Type*}
    {L : PerfectPathPacking G A B}
    {C : AuxiliaryCorridor L activeCount}
    (F : FullBoundaryColumnFamily L activeCount ι C) where
  monotoneRows : ∀ i, (F.trace i).MonotoneRows
  noBump : ∀ i, (F.trace i).NoBump
  noActiveCross : F.NoActiveCross

namespace ActiveTerminalGeometry

open TerminalGeometry

variable {h : ℕ}
variable {L : PerfectPathPacking G A B}
variable {C : AuxiliaryCorridor L (z h)}
variable {F : FullBoundaryColumnFamily L (z h) (Fin h) C}

/-- Finish Claim B.3 using the concrete active-strip blocker theorem.  This is
the active-scope counterpart of `TerminalGeometry.of_noHill_of_higherValleyBlocker`;
there is no additional proof-data parameter. -/
noncomputable def of_noHill
    (hnoBump : ∀ i, (F.trace i).NoBump)
    (hnoActiveCross : F.NoActiveCross)
    (hnoHill : F.NoHill) :
    F.ActiveTerminalGeometry := by
  have hraise :
      ∀ i : Fin h, ∀ D : (F.trace i).Valley,
        ∃ j : Fin h, ∃ E : (F.trace j).Valley,
          D.rowTop.1 < E.rowTop.1 := by
    intro i D
    rcases F.exists_blocking_column_of_noHill hnoHill i D with
      ⟨j, hji, hblocked⟩
    rcases F.higher_valley_of_blocker hnoBump hnoActiveCross
        (i := i) (j := j) hji.symm D hblocked with
      ⟨E, hlower⟩
    refine ⟨j, E, ?_⟩
    have hs := E.lower_succ
    rw [hlower] at hs
    omega
  have hnoValley :
      ∀ i : Fin h, ¬ Nonempty (F.trace i).Valley :=
    F.noValley_of_strictly_higher hraise
  exact {
    monotoneRows := fun i =>
      (F.trace i).monotoneRows_of_noValley (hnoValley i)
    noBump := hnoBump
    noActiveCross := hnoActiveCross
  }

theorem columnTraceConvex
    (D : F.ActiveTerminalGeometry) (i : Fin h)
    (q : Fin (z h + 2)) :
    GraphPathTraceConvex (F.column i) (C.rowPath q).vertexSet :=
  (F.trace i).rowTraceConvex_of_monotoneRows_of_noBump
    (D.monotoneRows i) (D.noBump i) q

theorem rowTraceConvex
    (D : F.ActiveTerminalGeometry) (i : Fin h)
    (q : Fin (z h + 2)) :
    GraphPathTraceConvex (C.rowPath q) (F.column i).vertexSet :=
  (F.trace i).rowTraceConvexColumn_of_monotoneRows_of_noBump
    (D.monotoneRows i) (D.noBump i) q

/-- Row-oriented intersection path, used for horizontal connectors. -/
noncomputable def rowIntersectionPath
    (D : F.ActiveTerminalGeometry) (i : Fin h)
    (q : Fin (z h + 2)) : GraphPath G :=
  (F.trace i).rowIntersectionPath (D.monotoneRows i) (D.noBump i) q

@[simp] theorem rowIntersectionPath_vertexSet
    (D : F.ActiveTerminalGeometry) (i : Fin h)
    (q : Fin (z h + 2)) :
    (D.rowIntersectionPath i q).vertexSet =
      (C.rowPath q).vertexSet ∩ (F.column i).vertexSet :=
  (F.trace i).rowIntersectionPath_vertexSet
    (D.monotoneRows i) (D.noBump i) q

/-- In an active strip, lower-row contact order propagates to the upper row.
This is the one direction needed after sorting on the first active row. -/
theorem adjacent_contactAtRow_order_up
    (D : F.ActiveTerminalGeometry)
    {i j : Fin h} (hij : i ≠ j)
    (q : Fin (z h + 1))
    (hqPos : 0 < q.1) (hqLt : q.1 < z h) :
    (C.rowPath ⟨q.1, by omega⟩).Before
        ((F.trace i).contactAtRow ⟨q.1, by omega⟩)
        ((F.trace j).contactAtRow ⟨q.1, by omega⟩) →
      (C.rowPath ⟨q.1 + 1, by omega⟩).Before
        ((F.trace i).contactAtRow ⟨q.1 + 1, by omega⟩)
        ((F.trace j).contactAtRow ⟨q.1 + 1, by omega⟩) := by
  classical
  let lower : Fin (z h + 2) := ⟨q.1, by omega⟩
  let upper : Fin (z h + 2) := ⟨q.1 + 1, by omega⟩
  let Ti := F.trace i
  let Tj := F.trace j
  let Bi := Ti.stripBridge (D.monotoneRows i) q
  let Bj := Tj.stripBridge (D.monotoneRows j) q
  have hdisj := F.column_vertexSet_disjoint hij
  have hconvIL :
      GraphPathTraceConvex (C.rowPath lower) (F.column i).vertexSet :=
    Ti.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (D.monotoneRows i) (D.noBump i) lower
  have hconvJL :
      GraphPathTraceConvex (C.rowPath lower) (F.column j).vertexSet :=
    Tj.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (D.monotoneRows j) (D.noBump j) lower
  have hconvIU :
      GraphPathTraceConvex (C.rowPath upper) (F.column i).vertexSet :=
    Ti.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (D.monotoneRows i) (D.noBump i) upper
  have hconvJU :
      GraphPathTraceConvex (C.rowPath upper) (F.column j).vertexSet :=
    Tj.rowTraceConvexColumn_of_monotoneRows_of_noBump
      (D.monotoneRows j) (D.noBump j) upper
  have hrepIL :
      Ti.contactAtRow lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column i).vertexSet :=
    Finset.mem_inter.2
      ⟨Ti.contactAtRow_mem_row lower, Ti.contactAtRow_mem_column lower⟩
  have hrepJL :
      Tj.contactAtRow lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column j).vertexSet :=
    Finset.mem_inter.2
      ⟨Tj.contactAtRow_mem_row lower, Tj.contactAtRow_mem_column lower⟩
  have hrepIU :
      Ti.contactAtRow upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column i).vertexSet :=
    Finset.mem_inter.2
      ⟨Ti.contactAtRow_mem_row upper, Ti.contactAtRow_mem_column upper⟩
  have hrepJU :
      Tj.contactAtRow upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column j).vertexSet :=
    Finset.mem_inter.2
      ⟨Tj.contactAtRow_mem_row upper, Tj.contactAtRow_mem_column upper⟩
  have hbridgeIL :
      Bi.lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column i).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bi, lower] using Bi.lower_mem,
       by simpa [Ti, Bi] using Bi.lower_mem_column⟩
  have hbridgeJL :
      Bj.lower ∈
        (C.rowPath lower).vertexSet ∩ (F.column j).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bj, lower] using Bj.lower_mem,
       by simpa [Tj, Bj] using Bj.lower_mem_column⟩
  have hbridgeIU :
      Bi.upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column i).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bi, upper] using Bi.upper_mem,
       by simpa [Ti, Bi] using Bi.upper_mem_column⟩
  have hbridgeJU :
      Bj.upper ∈
        (C.rowPath upper).vertexSet ∩ (F.column j).vertexSet := by
    exact Finset.mem_inter.2
      ⟨by simpa [Bj, upper] using Bj.upper_mem,
       by simpa [Tj, Bj] using Bj.upper_mem_column⟩
  intro hLower
  have hBridgeLower :
      (C.rowPath lower).Before Bi.lower Bj.lower :=
    graphPath_before_of_disjoint_traceConvex hdisj hconvIL hconvJL
      hrepIL hrepJL hbridgeIL hbridgeJL (by simpa [lower] using hLower)
  rcases ClaimB2Atom.graphPath_before_or_before_of_mem
      (C.rowPath upper)
      (Finset.mem_inter.1 hrepIU).1
      (Finset.mem_inter.1 hrepJU).1 with hUpper | hUpperRev
  · simpa [upper] using hUpper
  · have hBridgeUpperRev :
        (C.rowPath upper).Before Bj.upper Bi.upper :=
      graphPath_before_of_disjoint_traceConvex hdisj.symm hconvJU hconvIU
        hrepJU hrepIU hbridgeJU hbridgeIU hUpperRev
    exact False.elim (D.noActiveCross {
      strip := q
      first := i
      second := j
      first_ne_second := hij
      firstBridge := Bi
      secondBridge := Bj
      lower_reversed := by simpa [lower] using hBridgeLower
      upper_reversed := by simpa [upper] using hBridgeUpperRev
    } hqPos hqLt)

/-- The first-active-row sorting key gives strict order on that row. -/
theorem lower_contact_before_of_lt
    (D : F.ActiveTerminalGeometry)
    {j l : Fin h} (hjl : j.1 < l.1) :
    (C.rowPath (terminalLowerPosition h)).Before
      ((F.trace (orderedColumnIndex F j)).contactAtRow
        (terminalLowerPosition h))
      ((F.trace (orderedColumnIndex F l)).contactAtRow
        (terminalLowerPosition h)) := by
  apply
    (C.rowPath (terminalLowerPosition h)).before_iff_vertexIndex_le.2
  refine
    ⟨(F.trace (orderedColumnIndex F j)).contactAtRow_mem_row _,
      (F.trace (orderedColumnIndex F l)).contactAtRow_mem_row _, ?_⟩
  exact Nat.le_of_lt ((columnOrdering F).key_strictMono hjl)

/-- Active-strip no-cross transports the sorted order from the first active
row to every retained active row. -/
theorem ordered_contact_before
    (D : F.ActiveTerminalGeometry)
    {j l : Fin h} (hjl : j.1 < l.1)
    (i : Fin h) :
    (C.rowPath (terminalRowPosition h i)).Before
      ((F.trace (orderedColumnIndex F j)).contactAtRow
        (terminalRowPosition h i))
      ((F.trace (orderedColumnIndex F l)).contactAtRow
        (terminalRowPosition h i)) := by
  have hjlne : j ≠ l := by
    intro heq
    have := congrArg Fin.val heq
    omega
  have hcolumns :
      orderedColumnIndex F j ≠ orderedColumnIndex F l :=
    fun heq => hjlne (orderedColumnIndex_injective F heq)
  have H :
      ∀ n : ℕ, ∀ r : Fin h, r.1 = n →
        (C.rowPath (terminalRowPosition h r)).Before
          ((F.trace (orderedColumnIndex F j)).contactAtRow
            (terminalRowPosition h r))
          ((F.trace (orderedColumnIndex F l)).contactAtRow
            (terminalRowPosition h r)) := by
    intro n
    induction n with
    | zero =>
        intro r hr
        have hrzero : r = ⟨0, by omega⟩ := Fin.ext hr
        simpa [terminalRowPosition, terminalLowerPosition, hrzero] using
          D.lower_contact_before_of_lt hjl
    | succ n ih =>
        intro r hr
        let prev : Fin h := ⟨n, by omega⟩
        let strip : Fin (z h + 1) := ⟨n + 1, by
          dsimp [z]
          omega⟩
        have hrFin : r = ⟨n + 1, by omega⟩ := Fin.ext hr
        have hprev := ih prev rfl
        have hstep :=
          D.adjacent_contactAtRow_order_up hcolumns strip
            (by simp [strip]) (by
              dsimp [strip, z]
              omega) (by
                simpa [terminalRowPosition, prev, strip] using hprev)
        simpa [terminalRowPosition, strip, hrFin] using hstep
  exact H i.1 i rfl

/-- Along a monotone full column, contacts with strictly increasing rows occur
in the same order on the column. -/
theorem column_contact_before_of_row_lt
    (D : F.ActiveTerminalGeometry)
    (c : Fin h)
    {q r : Fin (z h + 2)} (hqr : q.1 < r.1) :
    (F.column c).Before
      ((F.trace c).contactAtRow q)
      ((F.trace c).contactAtRow r) := by
  let T := F.trace c
  have hindex :
      (T.contactAtRowIndex q).1 ≤ (T.contactAtRowIndex r).1 := by
    by_contra hnot
    have hreverse :
        (T.contactAtRowIndex r).1 ≤
          (T.contactAtRowIndex q).1 := by
      omega
    have hrows :=
      D.monotoneRows c
        (T.contactAtRowIndex r) (T.contactAtRowIndex q) hreverse
    rw [T.row_contactAtRowIndex, T.row_contactAtRowIndex] at hrows
    omega
  exact (T.contact_before_iff_le
    (T.contactAtRowIndex q) (T.contactAtRowIndex r)).2 hindex

/-- Intersection blocks occur in sorted-column order on each retained row. -/
noncomputable def rowBlockFamily
    (D : F.ActiveTerminalGeometry) (i : Fin h) :
    OrderedPathBlockFamily (terminalRow F i) h where
  block := terminalBlock F i
  meets := terminalBlock_meets_row F i
  block_subset := terminalBlock_subset_row F i
  pairwise_disjoint := by
    intro j l hjl
    exact terminalBlock_disjoint_same_row F hjl
  ordered := by
    intro j l hjl
    let q := terminalRowPosition h i
    let cj := orderedColumnIndex F j
    let cl := orderedColumnIndex F l
    have hjlne : j ≠ l := by
      intro heq
      have := congrArg Fin.val heq
      omega
    have hcols : cj ≠ cl :=
      fun heq => hjlne (orderedColumnIndex_injective F heq)
    apply graphPath_before_of_disjoint_traceConvex
      (F.column_vertexSet_disjoint hcols)
      (D.rowTraceConvex cj q)
      (D.rowTraceConvex cl q)
      (u0 := (F.trace cj).contactAtRow q)
      (w0 := (F.trace cl).contactAtRow q)
    · exact Finset.mem_inter.mpr
        ⟨(F.trace cj).contactAtRow_mem_row q,
          (F.trace cj).contactAtRow_mem_column q⟩
    · exact Finset.mem_inter.mpr
        ⟨(F.trace cl).contactAtRow_mem_row q,
          (F.trace cl).contactAtRow_mem_column q⟩
    · simpa [terminalBlock, terminalRow, terminalColumn, q, cj] using
        (terminalRow F i).lastHitVertex_mem_set
          (terminalBlock F i j) (terminalBlock_meets_row F i j)
    · simpa [terminalBlock, terminalRow, terminalColumn, q, cl] using
        (terminalRow F i).firstHitVertex_mem_set
          (terminalBlock F i l) (terminalBlock_meets_row F i l)
    · simpa [terminalRow, q, cj, cl] using
        D.ordered_contact_before hjl i

/-- Intersection blocks occur in active-row order on each sorted column. -/
noncomputable def columnBlockFamily
    (D : F.ActiveTerminalGeometry) (j : Fin h) :
    OrderedPathBlockFamily (terminalColumn F j) h where
  block := fun i => terminalBlock F i j
  meets := fun i => terminalBlock_meets_column F i j
  block_subset := fun i => terminalBlock_subset_column F i j
  pairwise_disjoint := by
    intro i k hik
    exact terminalBlock_disjoint_same_column F hik
  ordered := by
    intro i k hik
    let q := terminalRowPosition h i
    let r := terminalRowPosition h k
    let c := orderedColumnIndex F j
    have hikne : i ≠ k := by
      intro heq
      have := congrArg Fin.val heq
      omega
    have hrows : q ≠ r :=
      fun heq => hikne (terminalRowPosition_injective heq)
    apply graphPath_before_of_disjoint_traceConvex
      (C.rowPath_nodeDisjoint hrows)
      (D.columnTraceConvex c q)
      (D.columnTraceConvex c r)
      (u0 := (F.trace c).contactAtRow q)
      (w0 := (F.trace c).contactAtRow r)
    · exact Finset.mem_inter.mpr
        ⟨(F.trace c).contactAtRow_mem_column q,
          (F.trace c).contactAtRow_mem_row q⟩
    · exact Finset.mem_inter.mpr
        ⟨(F.trace c).contactAtRow_mem_column r,
          (F.trace c).contactAtRow_mem_row r⟩
    · simpa [terminalBlock, terminalRow, terminalColumn, q, c,
        Finset.inter_comm] using
        (terminalColumn F j).lastHitVertex_mem_set
          (terminalBlock F i j) (terminalBlock_meets_column F i j)
    · simpa [terminalBlock, terminalRow, terminalColumn, r, c,
        Finset.inter_comm] using
        (terminalColumn F j).firstHitVertex_mem_set
          (terminalBlock F k j) (terminalBlock_meets_column F k j)
    · apply D.column_contact_before_of_row_lt c
      dsimp [q, r, terminalRowPosition]
      omega

/-- Active-row terminal geometry gives the concrete ordered path-grid
geometry without any no-cross assumption on either boundary strip. -/
noncomputable def toOrderedPathGridGeometry
    (D : F.ActiveTerminalGeometry) :
    OrderedPathGridGeometry G h where
  row := terminalRow F
  column := terminalColumn F
  row_nodeDisjoint := by
    intro i k hik
    exact terminalRow_nodeDisjoint F hik
  column_nodeDisjoint := by
    intro j l hjl
    exact terminalColumn_nodeDisjoint F hjl
  intersectionPath := fun i j =>
    D.rowIntersectionPath
      (orderedColumnIndex F j) (terminalRowPosition h i)
  intersectionPath_vertexSet := by
    intro i j
    simpa [terminalRow, terminalColumn] using
      D.rowIntersectionPath_vertexSet
        (orderedColumnIndex F j) (terminalRowPosition h i)
  rowBlocks := D.rowBlockFamily
  rowBlocks_block := by
    intro i j
    rfl
  columnBlocks := D.columnBlockFamily
  columnBlocks_block := by
    intro j i
    rfl

/-- Terminal geometry with active-strip no-cross contains the requested grid
minor. -/
theorem containsGridMinor
    (D : F.ActiveTerminalGeometry) :
    ContainsGridMinor G h :=
  OrderedPathGridGeometry.containsGridMinor
    D.toOrderedPathGridGeometry

/-- Direct terminal sparse-grid theorem in the invariants delivered by the
row and hill descents. -/
theorem containsGridMinor_of_noHill
    (hnoBump : ∀ i, (F.trace i).NoBump)
    (hnoActiveCross : F.NoActiveCross)
    (hnoHill : F.NoHill) :
    ContainsGridMinor G h :=
  (of_noHill hnoBump hnoActiveCross hnoHill).containsGridMinor

end ActiveTerminalGeometry
end FullBoundaryColumnFamily

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
