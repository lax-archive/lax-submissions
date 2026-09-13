import Lax17Proofs.Source.Exponent7.RectangularSection45Input

namespace Lax17Proofs

/-!
# Rectangular row selection for Section 4.5

The square form of Section 4.5 uses one parameter for both the selected chain
length and every overlap row set. Here these parameters are independent.
This module proves the finite-set selection; the graph realization is in
`RectangularCase1Assembly`.
-/

namespace SimpleGraph
namespace Exponent7

open Finset

/-- Consecutive entries of a rectangular selected chain satisfy the
large-overlap relation with threshold `W`. -/
theorem selectedIndex_chain_succ_rectangular
    {N M L W : ℕ}
    {sliceRows : Fin M → Finset (Fin N)}
    {l : List (Fin M)} (hlen : l.length = L)
    (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
    (i : Fin L) (hi : i.1 + 1 < L) :
    Section45.LargeOverlapRel sliceRows W
      (Section45.selectedIndex l hlen i)
      (Section45.selectedIndex l hlen ⟨i.1 + 1, hi⟩) := by
  have hrel := List.IsChain.getElem hchain i.1 (by simpa [hlen] using hi)
  simpa [Section45.selectedIndex] using hrel

/-- Selected indices are strictly increasing; the proof only uses the order
component of the large-overlap relation, not equality of `L` and `W`. -/
theorem selectedIndex_lt_of_lt_rectangular
    {N M L W : ℕ}
    {sliceRows : Fin M → Finset (Fin N)}
    {l : List (Fin M)} (hlen : l.length = L)
    (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
    {i j : Fin L} (hij : i < j) :
    Section45.selectedIndex l hlen i <
      Section45.selectedIndex l hlen j := by
  have hltChain : l.IsChain (fun a b : Fin M => a < b) :=
    hchain.imp (fun _ _ h => h.1)
  have hp : l.Pairwise (fun a b : Fin M => a < b) :=
    hltChain.pairwise
  exact hp.rel_get_of_lt (by
    change
      (⟨i.1, by simp [hlen, i.2]⟩ : Fin l.length) <
        ⟨j.1, by simp [hlen, j.2]⟩
    exact hij)

theorem selectedIndex_le_of_le_rectangular
    {N M L W : ℕ}
    {sliceRows : Fin M → Finset (Fin N)}
    {l : List (Fin M)} (hlen : l.length = L)
    (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
    {i j : Fin L} (hij : i ≤ j) :
    Section45.selectedIndex l hlen i ≤
      Section45.selectedIndex l hlen j := by
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact
      (selectedIndex_lt_of_lt_rectangular
        hlen hchain hij).le
  · exact le_rfl

/-- Left row set at a selected cluster.  The first selected cluster uses the
chosen initial set; later clusters use the preceding overlap set. -/
def rectangularPaperLeftRows
    {N M L W : ℕ} {sliceRows : Fin M → Finset (Fin N)}
    (firstRows :
      (l : List (Fin M)) → (hlen : l.length = L) →
        l.IsChain (Section45.LargeOverlapRel sliceRows W) →
          Finset (Fin N))
    (gapRows :
      (l : List (Fin M)) → (hlen : l.length = L) →
        l.IsChain (Section45.LargeOverlapRel sliceRows W) →
          (i : Fin L) → i.1 + 1 < L → Finset (Fin N))
    (l : List (Fin M)) (hlen : l.length = L)
    (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
    (i : Fin L) : Finset (Fin N) :=
  if h0 : i.1 = 0 then
    firstRows l hlen hchain
  else
    let k : Fin L := ⟨i.1 - 1, by omega⟩
    gapRows l hlen hchain k (by
      dsimp [k]
      omega)

/-- Right row set at a selected cluster.  Except at the final cluster it is
the following overlap set; at the final cluster it equals the left set. -/
def rectangularPaperRightRows
    {N M L W : ℕ} {sliceRows : Fin M → Finset (Fin N)}
    (firstRows :
      (l : List (Fin M)) → (hlen : l.length = L) →
        l.IsChain (Section45.LargeOverlapRel sliceRows W) →
          Finset (Fin N))
    (gapRows :
      (l : List (Fin M)) → (hlen : l.length = L) →
        l.IsChain (Section45.LargeOverlapRel sliceRows W) →
          (i : Fin L) → i.1 + 1 < L → Finset (Fin N))
    (l : List (Fin M)) (hlen : l.length = L)
    (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
    (i : Fin L) : Finset (Fin N) :=
  if hi : i.1 + 1 < L then
    gapRows l hlen hchain i hi
  else
    rectangularPaperLeftRows firstRows gapRows l hlen hchain i

/-- Choose `W` initial rows and `W` rows in every consecutive overlap of a
chain of length `L`. -/
theorem exists_rectangularPaperRows
    {N M D L W : ℕ} (sliceRows : Fin M → Finset (Fin N))
    (hL : 0 < L) (hW : 0 < W)
    (hDW : W ≤ D)
    (hcard : ∀ i : Fin M, D ≤ (sliceRows i).card) :
    ∃ (firstRows :
        (l : List (Fin M)) → (hlen : l.length = L) →
          l.IsChain (Section45.LargeOverlapRel sliceRows W) →
            Finset (Fin N)),
      ∃ (gapRows :
        (l : List (Fin M)) → (hlen : l.length = L) →
          l.IsChain (Section45.LargeOverlapRel sliceRows W) →
            (i : Fin L) → i.1 + 1 < L → Finset (Fin N)),
        (∀ (l : List (Fin M)) (hlen : l.length = L)
          (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W)),
            firstRows l hlen hchain ⊆
              sliceRows
                (Section45.selectedIndex l hlen ⟨0, hL⟩)) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = L)
          (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W)),
            (firstRows l hlen hchain).card = W) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = L)
          (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
          (i : Fin L) (hi : i.1 + 1 < L),
            gapRows l hlen hchain i hi ⊆
              sliceRows (Section45.selectedIndex l hlen i)) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = L)
          (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
          (i : Fin L) (hi : i.1 + 1 < L),
            gapRows l hlen hchain i hi ⊆
              sliceRows
                (Section45.selectedIndex l hlen
                  ⟨i.1 + 1, hi⟩)) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = L)
          (hchain : l.IsChain (Section45.LargeOverlapRel sliceRows W))
          (i : Fin L) (hi : i.1 + 1 < L),
            (gapRows l hlen hchain i hi).card = W) := by
  classical
  let firstRows :
      (l : List (Fin M)) → (hlen : l.length = L) →
        l.IsChain (Section45.LargeOverlapRel sliceRows W) →
          Finset (Fin N) :=
    fun l hlen _ =>
      Classical.choose <| Finset.exists_subset_card_eq
        (hDW.trans
          (hcard (Section45.selectedIndex l hlen ⟨0, hL⟩)))
  let gapRows :
      (l : List (Fin M)) → (hlen : l.length = L) →
        l.IsChain (Section45.LargeOverlapRel sliceRows W) →
          (i : Fin L) → i.1 + 1 < L → Finset (Fin N) :=
    fun l hlen hchain i hi =>
      Classical.choose <| Finset.exists_subset_card_eq
        ((selectedIndex_chain_succ_rectangular
          (sliceRows := sliceRows) hlen hchain i hi).2)
  refine ⟨firstRows, gapRows, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hlen hchain
    exact (Classical.choose_spec <| Finset.exists_subset_card_eq
      (hDW.trans
        (hcard (Section45.selectedIndex l hlen ⟨0, hL⟩)))).1
  · intro l hlen hchain
    exact (Classical.choose_spec <| Finset.exists_subset_card_eq
      (hDW.trans
        (hcard (Section45.selectedIndex l hlen ⟨0, hL⟩)))).2
  · intro l hlen hchain i hi r hr
    have hsub :
        gapRows l hlen hchain i hi ⊆
          sliceRows (Section45.selectedIndex l hlen i) ∩
            sliceRows
              (Section45.selectedIndex l hlen
                ⟨i.1 + 1, hi⟩) :=
      (Classical.choose_spec <| Finset.exists_subset_card_eq
        ((selectedIndex_chain_succ_rectangular
          (sliceRows := sliceRows) hlen hchain i hi).2)).1
    exact (Finset.mem_inter.mp (hsub hr)).1
  · intro l hlen hchain i hi r hr
    have hsub :
        gapRows l hlen hchain i hi ⊆
          sliceRows (Section45.selectedIndex l hlen i) ∩
            sliceRows
              (Section45.selectedIndex l hlen
                ⟨i.1 + 1, hi⟩) :=
      (Classical.choose_spec <| Finset.exists_subset_card_eq
        ((selectedIndex_chain_succ_rectangular
          (sliceRows := sliceRows) hlen hchain i hi).2)).1
    exact (Finset.mem_inter.mp (hsub hr)).2
  · intro l hlen hchain i hi
    exact (Classical.choose_spec <| Finset.exists_subset_card_eq
      ((selectedIndex_chain_succ_rectangular
        (sliceRows := sliceRows) hlen hchain i hi).2)).2

end Exponent7
end SimpleGraph

end Lax17Proofs
