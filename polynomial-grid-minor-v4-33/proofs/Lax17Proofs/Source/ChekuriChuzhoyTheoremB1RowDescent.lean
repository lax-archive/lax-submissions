import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorBump
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorCross
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1Valley

namespace Lax17Proofs

universe u v w

/-!
# Appendix B.1: finite descent through bump and cross switches

This module connects the contact-trace configurations to the generic
corridor rerouting steps.  Only configurations wholly between active rows are
switched; boundary-strip configurations are irrelevant to the terminal grid
and are deliberately left untouched.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}
variable {original : PerfectPathPacking G A B}
variable {activeCount : ℕ} {ι : Type w}
variable {fixedColumn : ι → GraphPath G}

open IndexedAuxiliaryPrefix

/-- Convert an internal corridor position into its active-row index. -/
def activeRowOfPosition
    (q : Fin (activeCount + 2))
    (hlower : 0 < q.1) (hupper : q.1 < activeCount + 1) :
    Fin activeCount :=
  ⟨q.1 - 1, by omega⟩

@[simp] theorem activePosition_activeRowOfPosition
    (C : AuxiliaryCorridor original activeCount)
    (q : Fin (activeCount + 2))
    (hlower : 0 < q.1) (hupper : q.1 < activeCount + 1) :
    C.activePosition (activeRowOfPosition q hlower hupper) = q := by
  apply Fin.ext
  simp [AuxiliaryCorridor.activePosition, activeRowOfPosition]
  omega

namespace CorridorBumpWitness

variable {S : CorridorRowState original activeCount ι fixedColumn}

/-- A trace bump whose common row is active gives the exact generic bump
witness consumed by the row switch. -/
noncomputable def ofActiveTraceBump
    (i : ι) (b : (S.columns.trace i).Bump)
    (hactive :
      0 <
          ((S.columns.trace i).row
            ⟨b.step.1, by omega⟩).1 ∧
        ((S.columns.trace i).row
            ⟨b.step.1, by omega⟩).1 <
          activeCount + 1) :
    CorridorBumpWitness S := by
  classical
  let T := S.columns.trace i
  let q : Fin (activeCount + 2) :=
    T.row ⟨b.step.1, by omega⟩
  let row : Fin activeCount :=
    activeRowOfPosition q hactive.1 hactive.2
  let x : V := T.contact ⟨b.step.1, by omega⟩
  let y : V := T.contact ⟨b.step.1 + 1, by omega⟩
  have hrowPosition : S.corridor.activePosition row = q := by
    exact activePosition_activeRowOfPosition
      S.corridor q hactive.1 hactive.2
  have hrowPath :
      S.corridor.activePath row = S.corridor.rowPath q := by
    change
      S.linkage.path
          (S.corridor.index (S.corridor.activePosition row)) =
        S.linkage.path (S.corridor.index q)
    rw [hrowPosition]
  have hxRow : x ∈ (S.corridor.activePath row).vertexSet := by
    rw [hrowPath]
    simpa [T, q, x] using
      T.contact_mem_row ⟨b.step.1, by omega⟩
  have hyRow : y ∈ (S.corridor.activePath row).vertexSet := by
    rw [hrowPath]
    have hy :=
      T.contact_mem_row ⟨b.step.1 + 1, by omega⟩
    simpa [T, q, y, b.same_row] using hy
  have hxy : x ≠ y := by
    intro h
    have hindices :=
      T.contact_injective h
    have hvals := congrArg Fin.val hindices
    simp at hvals
  by_cases hxyBefore :
      (S.corridor.activePath row).Before x y
  · exact
      { row := row
        column := i
        left := x
        right := y
        left_mem_row := hxRow
        right_mem_row := hyRow
        left_before_right := hxyBefore
        left_ne_right := hxy
        segment := T.atom b.step
        segment_connects :=
          Or.inl ⟨by simp [T, x], by simp [T, y]⟩
        segment_vertexSet_subset_column := by
          simpa [T, S.column_eq_fixed i] using
            T.atom_vertexSet_subset_column b.step
        segment_edgeSet_subset_column := by
          simpa [T, S.column_eq_fixed i] using
            T.atom_edgeSet_subset_column b.step
        segment_clean_linkage := T.atom_internallyDisjoint_linkage b.step
        not_row_contained := by
          right
          intro hsub
          exact b.off_row_edge_not_mem (by
            rw [← hrowPath]
            exact hsub b.off_row_edge_mem) }
  · have hyxBefore :
        (S.corridor.activePath row).Before y x :=
      (ClaimB2Atom.graphPath_before_or_before_of_mem
        (S.corridor.activePath row) hxRow hyRow).resolve_left hxyBefore
    exact
      { row := row
        column := i
        left := y
        right := x
        left_mem_row := hyRow
        right_mem_row := hxRow
        left_before_right := hyxBefore
        left_ne_right := hxy.symm
        segment := T.atom b.step
        segment_connects :=
          Or.inr ⟨by simp [T, x], by simp [T, y]⟩
        segment_vertexSet_subset_column := by
          simpa [T, S.column_eq_fixed i] using
            T.atom_vertexSet_subset_column b.step
        segment_edgeSet_subset_column := by
          simpa [T, S.column_eq_fixed i] using
            T.atom_edgeSet_subset_column b.step
        segment_clean_linkage := T.atom_internallyDisjoint_linkage b.step
        not_row_contained := by
          right
          intro hsub
          exact b.off_row_edge_not_mem (by
            rw [← hrowPath]
            exact hsub b.off_row_edge_mem) }

end CorridorBumpWitness

/-- A strip-bridge atom connects its stored lower and upper endpoints in the
unoriented `GraphPath.Connects` convention. -/
theorem CorridorColumnTrace.StripBridge.atom_connects
    {L : PerfectPathPacking G A B}
    {C : AuxiliaryCorridor L activeCount}
    {P : GraphPath G}
    {T : CorridorColumnTrace L activeCount C P}
    {q : Fin (activeCount + 1)}
    (D : T.StripBridge q) :
    (T.atom D.step).Connects {D.lower} {D.upper} := by
  rcases D.connects with h | h
  · exact Or.inl ⟨by simpa using h.1, by simpa using h.2⟩
  · exact Or.inr ⟨by simpa using h.1, by simpa using h.2⟩

namespace CorridorCross

variable {S : CorridorRowState original activeCount ι fixedColumn}

/-- A trace cross in a strip between two active rows gives the exact generic
Figure-8 witness consumed by the two-row switch. -/
noncomputable def ofActiveFamilyCross
    (X : S.columns.Cross)
    (hactive : 0 < X.strip.1 ∧ X.strip.1 < activeCount) :
    CorridorCross S := by
  classical
  let lowerPosition : Fin (activeCount + 2) :=
    ⟨X.strip.1, by omega⟩
  let upperPosition : Fin (activeCount + 2) :=
    ⟨X.strip.1 + 1, by omega⟩
  have hlowerPositive : 0 < lowerPosition.1 := by
    simpa [lowerPosition] using hactive.1
  have hlowerUpper : lowerPosition.1 < activeCount + 1 := by
    simp only [lowerPosition]
    omega
  have hupperPositive : 0 < upperPosition.1 := by
    simp only [upperPosition]
    omega
  have hupperUpper : upperPosition.1 < activeCount + 1 := by
    simp only [upperPosition]
    omega
  let lowerRow : Fin activeCount :=
    activeRowOfPosition lowerPosition hlowerPositive hlowerUpper
  let upperRow : Fin activeCount :=
    activeRowOfPosition upperPosition hupperPositive hupperUpper
  have hlowerPosition :
      S.corridor.activePosition lowerRow = lowerPosition := by
    exact activePosition_activeRowOfPosition
      S.corridor lowerPosition hlowerPositive hlowerUpper
  have hupperPosition :
      S.corridor.activePosition upperRow = upperPosition := by
    exact activePosition_activeRowOfPosition
      S.corridor upperPosition hupperPositive hupperUpper
  have hlowerPath :
      S.corridor.activePath lowerRow =
        S.corridor.rowPath lowerPosition := by
    change
      S.linkage.path
          (S.corridor.index (S.corridor.activePosition lowerRow)) =
        S.linkage.path (S.corridor.index lowerPosition)
    rw [hlowerPosition]
  have hupperPath :
      S.corridor.activePath upperRow =
        S.corridor.rowPath upperPosition := by
    change
      S.linkage.path
          (S.corridor.index (S.corridor.activePosition upperRow)) =
        S.linkage.path (S.corridor.index upperPosition)
    rw [hupperPosition]
  have hs₁ne :
      X.firstBridge.lower ≠ X.secondBridge.lower := by
    intro heq
    exact Finset.disjoint_left.mp
      (S.columns.column_vertexSet_disjoint X.first_ne_second)
      X.firstBridge.lower_mem_column
      (by simpa [heq] using X.secondBridge.lower_mem_column)
  have ht₂ne :
      X.secondBridge.upper ≠ X.firstBridge.upper := by
    intro heq
    exact Finset.disjoint_left.mp
      (S.columns.column_vertexSet_disjoint X.first_ne_second).symm
      X.secondBridge.upper_mem_column
      (by simpa [heq] using X.firstBridge.upper_mem_column)
  refine
    { lowerRow := lowerRow
      upperRow := upperRow
      consecutive := by
        dsimp [lowerRow, upperRow, activeRowOfPosition,
          lowerPosition, upperPosition]
        omega
      column₁ := X.first
      column₂ := X.second
      s₁ := X.firstBridge.lower
      s₂ := X.secondBridge.lower
      t₁ := X.firstBridge.upper
      t₂ := X.secondBridge.upper
      s₁_mem_lower := by
        rw [hlowerPath]
        simpa [lowerPosition] using X.firstBridge.lower_mem
      s₂_mem_lower := by
        rw [hlowerPath]
        simpa [lowerPosition] using X.secondBridge.lower_mem
      t₁_mem_upper := by
        rw [hupperPath]
        simpa [upperPosition] using X.firstBridge.upper_mem
      t₂_mem_upper := by
        rw [hupperPath]
        simpa [upperPosition] using X.secondBridge.upper_mem
      s₁_before_s₂ := by
        rw [hlowerPath]
        simpa [lowerPosition] using X.lower_reversed
      t₂_before_t₁ := by
        rw [hupperPath]
        simpa [upperPosition] using X.upper_reversed
      s₁_ne_s₂ := hs₁ne
      t₂_ne_t₁ := ht₂ne
      segment₁ := (S.columns.trace X.first).atom X.firstBridge.step
      segment₂ := (S.columns.trace X.second).atom X.secondBridge.step
      segment₁_connects := X.firstBridge.atom_connects
      segment₂_connects := X.secondBridge.atom_connects
      segment₁_subset_column := by
        simpa [S.column_eq_fixed X.first] using
          (S.columns.trace X.first).atom_vertexSet_subset_column
            X.firstBridge.step
      segment₂_subset_column := by
        simpa [S.column_eq_fixed X.second] using
          (S.columns.trace X.second).atom_vertexSet_subset_column
            X.secondBridge.step
      segment₁_edges_subset_column := by
        simpa [S.column_eq_fixed X.first] using
          (S.columns.trace X.first).atom_edgeSet_subset_column
            X.firstBridge.step
      segment₂_edges_subset_column := by
        simpa [S.column_eq_fixed X.second] using
          (S.columns.trace X.second).atom_edgeSet_subset_column
            X.secondBridge.step
      segment₁_clean_linkage :=
        (S.columns.trace X.first).atom_internallyDisjoint_linkage
          X.firstBridge.step
      segment₂_clean_linkage :=
        (S.columns.trace X.second).atom_internallyDisjoint_linkage
          X.secondBridge.step
      segments_nodeDisjoint := ?_ }
  exact Disjoint.mono
    ((S.columns.trace X.first).atom_vertexSet_subset_column
      X.firstBridge.step)
    ((S.columns.trace X.second).atom_vertexSet_subset_column
      X.secondBridge.step)
    (S.columns.column_vertexSet_disjoint X.first_ne_second)

end CorridorCross

namespace CorridorRowState

variable (S : CorridorRowState original activeCount ι fixedColumn)

/-- The terminal predicate for the first finite descent: no bump remains on
an active row and no cross remains between two active rows. -/
def RowNormal : Prop :=
  (∀ i : ι, (S.columns.trace i).NoActiveBump) ∧
    S.columns.NoActiveCross

theorem RowNormal.noActiveBump
    (h : S.RowNormal) (i : ι) :
    (S.columns.trace i).NoActiveBump :=
  h.1 i

theorem RowNormal.noActiveCross
    (h : S.RowNormal) :
    S.columns.NoActiveCross :=
  h.2

/-- Logical extraction of a concrete active bump. -/
theorem exists_active_bump_of_not_all_noActiveBump
    (h : ¬ ∀ i : ι, (S.columns.trace i).NoActiveBump) :
    ∃ i : ι, ∃ b : (S.columns.trace i).Bump,
      0 <
          ((S.columns.trace i).row
            ⟨b.step.1, by omega⟩).1 ∧
        ((S.columns.trace i).row
            ⟨b.step.1, by omega⟩).1 <
          activeCount + 1 := by
  classical
  by_contra hex
  apply h
  intro i b hlower hupper
  exact hex ⟨i, b, hlower, hupper⟩

/-- Logical extraction of a concrete cross in an active strip. -/
theorem exists_active_cross_of_not_noActiveCross
    (h : ¬ S.columns.NoActiveCross) :
    ∃ X : S.columns.Cross,
      0 < X.strip.1 ∧ X.strip.1 < activeCount := by
  classical
  by_contra hex
  apply h
  intro X hlower hupper
  exact hex ⟨X, hlower, hupper⟩

/-- One row-normalization step.  A concrete active bump or cross either
already lowers the auxiliary degree-two count below the branch's original
linkage, or supplies a new row state with strictly smaller `rowMeasure`. -/
theorem step_degree_drop_or_smaller_state
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (hnot : ¬ S.RowNormal) :
    (∃ L' : PerfectPathPacking G A B,
        linkageAuxDegreeTwoCount L' <
          linkageAuxDegreeTwoCount original) ∨
      ∃ S' : CorridorRowState original activeCount ι fixedColumn,
        S'.rowMeasure < S.rowMeasure := by
  classical
  by_cases hnoBump :
      ∀ i : ι, (S.columns.trace i).NoActiveBump
  · have hnotCross : ¬ S.columns.NoActiveCross := by
      intro hnoCross
      exact hnot ⟨hnoBump, hnoCross⟩
    rcases S.exists_active_cross_of_not_noActiveCross hnotCross with
      ⟨X, hlower, hupper⟩
    let cross : CorridorCross S :=
      CorridorCross.ofActiveFamilyCross X ⟨hlower, hupper⟩
    rcases cross.step_degree_drop_or_smaller_state with
      hdrop | ⟨S', hmeasure⟩
    · exact Or.inl
        ⟨cross.replacementLinkage,
          S.degree_drop_lt_original hdrop⟩
    · exact Or.inr ⟨S', hmeasure⟩
  · rcases S.exists_active_bump_of_not_all_noActiveBump hnoBump with
      ⟨i, b, hlower, hupper⟩
    let bump : CorridorBumpWitness S :=
      CorridorBumpWitness.ofActiveTraceBump i b ⟨hlower, hupper⟩
    rcases bump.step_degree_drop_or_smaller_state with
      hdrop | ⟨S', hmeasure⟩
    · exact Or.inl
        ⟨bump.replacementLinkage,
          S.degree_drop_lt_original hdrop⟩
    · exact Or.inr ⟨S', hmeasure⟩

/-- Strong induction on the explicit row-edge measure terminates the
bump/cross loop.  The terminal state contains no active trace bump and no
cross whose two rows are active. -/
theorem degree_drop_or_exists_rowNormal
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S₀ : CorridorRowState original activeCount ι fixedColumn) :
    (∃ L' : PerfectPathPacking G A B,
        linkageAuxDegreeTwoCount L' <
          linkageAuxDegreeTwoCount original) ∨
      ∃ S' : CorridorRowState original activeCount ι fixedColumn,
        S'.RowNormal := by
  classical
  exact
    output_or_exists_terminal_of_nat_descent
      (fun S' : CorridorRowState original activeCount ι fixedColumn =>
        S'.rowMeasure)
      (fun S' : CorridorRowState original activeCount ι fixedColumn =>
        S'.RowNormal)
      (fun S' hnot =>
        S'.step_degree_drop_or_smaller_state hnot)
      S₀

end CorridorRowState

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
