import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin

namespace Lax17Proofs

/-!
# Finite selection for the last-hit crossbar argument

This module isolates the only counting and choice step in the last-hit
construction.  A finite family of auxiliary paths is sent to the row
containing its last bad-segment contact.  If every row receives at most `d`
paths and there are at least `d * r` paths, then at least `r` rows occur.

The output does not merely assert the cardinality bound.  It chooses `r`
distinct row values and, for each one, a distinct path in the corresponding
fiber.  The `Fin r` indexing is the form consumed directly by `Crossbar`.
-/

namespace SimpleGraph
namespace Exponent8

open Finset

universe u v

variable {PathIndex : Type u} {RowIndex : Type v}
variable [DecidableEq RowIndex]

/-- Explicit representatives of `r` distinct fibers of `lastRow`.

`row` lists the selected last-hit rows and `preimage` lists one bad auxiliary
path assigned to each row.  Both maps are injective; the latter fact also
follows from `maps_to` and `row_injective`, but is recorded because it is the
property used to reindex the selected spokes. -/
structure LastHitSelection
    (Qbad : Finset PathIndex) (lastRow : PathIndex → RowIndex) (r : ℕ) where
  row : Fin r → RowIndex
  preimage : Fin r → PathIndex
  row_mem_image : ∀ i, row i ∈ Qbad.image lastRow
  preimage_mem : ∀ i, preimage i ∈ Qbad
  maps_to : ∀ i, lastRow (preimage i) = row i
  row_injective : Function.Injective row
  preimage_injective : Function.Injective preimage

/-- The bounded-fiber count used by the last-hit argument. -/
theorem card_le_mul_card_lastRow_image
    (Qbad : Finset PathIndex) (lastRow : PathIndex → RowIndex) (d : ℕ)
    (hfiber :
      ∀ row ∈ Qbad.image lastRow,
        (Qbad.filter fun q => lastRow q = row).card ≤ d) :
    Qbad.card ≤ d * (Qbad.image lastRow).card :=
  Finset.card_le_mul_card_image Qbad d hfiber

/-- If `d > 0` and `d * r` bad paths are distributed among fibers of size at
most `d`, then the image of the last-row map has at least `r` elements. -/
theorem le_card_lastRow_image
    (Qbad : Finset PathIndex) (lastRow : PathIndex → RowIndex) (d r : ℕ)
    (hd : 0 < d)
    (hfiber :
      ∀ row ∈ Qbad.image lastRow,
        (Qbad.filter fun q => lastRow q = row).card ≤ d)
    (hmany : d * r ≤ Qbad.card) :
    r ≤ (Qbad.image lastRow).card := by
  have hmul :
      d * r ≤ d * (Qbad.image lastRow).card :=
    hmany.trans
      (card_le_mul_card_lastRow_image Qbad lastRow d hfiber)
  exact Nat.le_of_mul_le_mul_left hmul hd

/-- Select exactly `r` represented rows.  This set-level form is useful when
the downstream argument wants to stay in the `Finset` API. -/
theorem exists_lastRow_subset_card_eq
    (Qbad : Finset PathIndex) (lastRow : PathIndex → RowIndex) (d r : ℕ)
    (hd : 0 < d)
    (hfiber :
      ∀ row ∈ Qbad.image lastRow,
        (Qbad.filter fun q => lastRow q = row).card ≤ d)
    (hmany : d * r ≤ Qbad.card) :
    ∃ rows : Finset RowIndex,
      rows ⊆ Qbad.image lastRow ∧ rows.card = r :=
  Finset.exists_subset_card_eq
    (le_card_lastRow_image Qbad lastRow d r hd hfiber hmany)

/-- Choose `r` distinct last-hit rows and a distinct bad path attaining each
row.  This is the selection package needed to construct a width-`r`
crossbar. -/
theorem exists_lastHitSelection
    (Qbad : Finset PathIndex) (lastRow : PathIndex → RowIndex) (d r : ℕ)
    (hd : 0 < d)
    (hfiber :
      ∀ row ∈ Qbad.image lastRow,
        (Qbad.filter fun q => lastRow q = row).card ≤ d)
    (hmany : d * r ≤ Qbad.card) :
    Nonempty (LastHitSelection Qbad lastRow r) := by
  classical
  rcases exists_lastRow_subset_card_eq
      Qbad lastRow d r hd hfiber hmany with
    ⟨rows, hrows_sub, hrows_card⟩
  have hrow_witness :
      ∀ row : {row // row ∈ rows},
        ∃ q ∈ Qbad, lastRow q = row.1 := by
    intro row
    exact Finset.mem_image.mp (hrows_sub row.property)
  let chosen : {row // row ∈ rows} → PathIndex :=
    fun row => Classical.choose (hrow_witness row)
  have chosen_mem :
      ∀ row : {row // row ∈ rows}, chosen row ∈ Qbad := by
    intro row
    exact (Classical.choose_spec (hrow_witness row)).1
  have chosen_maps :
      ∀ row : {row // row ∈ rows},
        lastRow (chosen row) = row.1 := by
    intro row
    exact (Classical.choose_spec (hrow_witness row)).2
  have hindex_card :
      Fintype.card {row // row ∈ rows} = r := by
    simpa only [Fintype.card_coe] using hrows_card
  let enumerate : Fin r ≃ {row // row ∈ rows} :=
    (Fintype.equivFinOfCardEq hindex_card).symm
  let selectedRow : Fin r → RowIndex :=
    fun i => (enumerate i).1
  let selectedPath : Fin r → PathIndex :=
    fun i => chosen (enumerate i)
  have hrow_injective : Function.Injective selectedRow := by
    intro i j hij
    apply enumerate.injective
    exact Subtype.ext hij
  have hpath_injective : Function.Injective selectedPath := by
    intro i j hij
    apply hrow_injective
    change (enumerate i).1 = (enumerate j).1
    rw [← chosen_maps (enumerate i), ← chosen_maps (enumerate j)]
    exact congrArg lastRow (by simpa [selectedPath] using hij)
  exact ⟨{
    row := selectedRow
    preimage := selectedPath
    row_mem_image := by
      intro i
      exact hrows_sub (enumerate i).property
    preimage_mem := by
      intro i
      exact chosen_mem (enumerate i)
    maps_to := by
      intro i
      exact chosen_maps (enumerate i)
    row_injective := hrow_injective
    preimage_injective := hpath_injective
  }⟩

end Exponent8
end SimpleGraph

end Lax17Proofs
