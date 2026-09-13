import Lax17.Minor
import Lax17.PathOfSets
import Lax17.Paths

/-!
---
title: Crossbars and pseudo-grids
type: definition
---
An \((A,B,X)\)-crossbar consists of disjoint main paths from \(A\) to \(B\)
and one disjoint spoke from every main path to \(X\).  Each spoke meets its own
main path exactly once and avoids all other main paths.

A pseudo-grid records the alternative produced by Theorem 4.1: disjoint
\(A\)-to-\(B\) rows, disjoint selected columns reaching \(X\), and disjoint
small blocks of rows.  Property P1 says that every unreserved row avoids all
selected columns; property P2 says that, for each reserved block, all but at
most \(2g^2\) columns meet a row in that block.
-/

namespace Lax17.Crossbar

universe u

open Lax17.Paths

/-- The parameter is an integral power of two. -/
def IsPowerOfTwo (g : ℕ) : Prop :=
  ∃ exponent : ℕ, g = 2 ^ exponent

/-- The graph has a minor carrying a strong path-of-sets system of the
specified length and width. -/
def HasStrongPathOfSetsMinor {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (length width : ℕ) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
    (H : SimpleGraph W),
      Lax17.Minor.IsMinor H G ∧
        Nonempty (Lax17.PathOfSets.StrongSystem H length width)

/-- A crossbar of width `ρ`. -/
structure System {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V) (ρ : ℕ) where
  mainPath : Fin ρ → Path G
  main_connects : ∀ i : Fin ρ, (mainPath i).Connects A B
  main_disjoint :
    Pairwise fun i j => Disjoint (mainPath i).vertices (mainPath j).vertices
  spokePath : Fin ρ → Path G
  spoke_disjoint :
    Pairwise fun i j => Disjoint (spokePath i).vertices (spokePath j).vertices
  attachment : Fin ρ → V
  attachment_on_main :
    ∀ i : Fin ρ, attachment i ∈ (mainPath i).vertices
  attachment_on_spoke :
    ∀ i : Fin ρ, attachment i ∈ (spokePath i).vertices
  exact_attachment :
    ∀ i : Fin ρ,
      (mainPath i).vertices ∩ (spokePath i).vertices = {attachment i}
  exit : Fin ρ → V
  attachment_is_endpoint :
    ∀ i : Fin ρ,
      attachment i = (spokePath i).source ∨
        attachment i = (spokePath i).target
  exit_is_other_endpoint :
    ∀ i : Fin ρ,
      exit i =
        if (spokePath i).source = attachment i then
          (spokePath i).target
        else
          (spokePath i).source
  exit_in_X : ∀ i : Fin ρ, exit i ∈ X
  exit_off_main :
    ∀ i : Fin ρ, exit i ∉ (mainPath i).vertices
  spoke_avoids_other_main :
    ∀ ⦃i j : Fin ρ⦄, i ≠ j →
      Disjoint (spokePath i).vertices (mainPath j).vertices

/-- A depth-`D` pseudo-grid with `κ` main rows at scale `g`. -/
structure PseudoGrid {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V)
    (g D κ : ℕ) where
  RowIndex : Type
  [rowFintype : Fintype RowIndex]
  [rowDecidableEq : DecidableEq RowIndex]
  row_count : Fintype.card RowIndex = κ
  row : RowIndex → Path G
  row_connects : ∀ i : RowIndex, (row i).Connects A B
  rows_disjoint :
    Pairwise fun i j => Disjoint (row i).vertices (row j).vertices
  depth_pos : 0 < D
  reserved : Fin D → Finset RowIndex
  reserved_card_le :
    ∀ i : Fin D, (reserved i).card ≤ g ^ 2
  reserved_disjoint :
    ∀ ⦃i j : Fin D⦄, i ≠ j →
      Disjoint (reserved i) (reserved j)
  ColumnIndex : Type
  [columnFintype : Fintype ColumnIndex]
  [columnDecidableEq : DecidableEq ColumnIndex]
  column_count : Fintype.card ColumnIndex = κ / 4
  column : ColumnIndex → Path G
  columns_disjoint :
    Pairwise fun i j => Disjoint (column i).vertices (column j).vertices
  column_reaches_X_cleanly :
    ∀ j : ColumnIndex,
      ((column j).source ∈ X ∨ (column j).target ∈ X) ∧
        (column j).InternallyAvoids X
  unreserved_row_avoids_columns :
    ∀ p : RowIndex,
      (∀ i : Fin D, p ∉ reserved i) →
        ∀ j : ColumnIndex,
          Disjoint (row p).vertices (column j).vertices
  few_columns_miss_reserved :
    ∀ i : Fin D,
      ∃ miss : Finset ColumnIndex,
        miss.card ≤ 2 * g ^ 2 ∧
          ∀ j : ColumnIndex, j ∉ miss →
            ∃ p ∈ reserved i,
              ¬ Disjoint (row p).vertices (column j).vertices

end Lax17.Crossbar
