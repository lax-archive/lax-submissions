import Lax185574Proofs.ResolveRam.Glue.FarW
import Lax185574Proofs.ResolveRam.CallList

/-!
The query of the children of an item on words.

The glue program keeps the parents and guards of the items of the next
level and the words of their outputs. The children of item `i` with
their guards are the outputs whose parent is `i`. A child of depth `q`
and arity `ℓ + 1` with a guard below `ℓ` gives the word of an extension,
the guard followed by the root of the output, which is the output word
without its header of three entries (`kidW_eq`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.ResolveRam
open Lax185574Proofs.Words

/-- The extension word of a child with guard `g` and output word `ow`. -/
def kidSel (q ℓ i : ℕ) (pg : ℕ × ℕ) (ow : List ℕ) : Option (List ℕ) :=
  if pg.1 = i ∧ pg.2 < ℓ ∧ ow.getD 1 0 = q ∧ ow.getD 2 0 = ℓ + 1 then some (pg.2 :: ow.drop 3)
  else none

/-- **The children of item `i` on words**, from the parents and guards `PG`
of the next level and the words `OW` of its outputs. -/
def kidW (q ℓ i : ℕ) (PG : List (ℕ × ℕ)) (OW : List (List ℕ)) : List (List ℕ) :=
  (PG.zip OW).filterMap fun y => kidSel q ℓ i y.1 y.2

theorem kidSel_eq (q ℓ i : ℕ) (y : Item × TypeTree) :
    kidSel q ℓ i y.1.1 (toWord y.2) =
      if y.1.1.1 = i then
        (if h : y.1.1.2 < ℓ then (TypeTree.rootAs y.2 q (ℓ + 1)).map fun r =>
          toWord (((⟨y.1.1.2, h⟩ : Fin ℓ), r)) else none)
      else none := by
  obtain ⟨⟨⟨p, g⟩, τ⟩, ⟨ck, cq, cℓ, cr⟩⟩ := y
  simp only [kidSel, FarRam.toWord_typeTree]
  show (if p = i ∧ g < ℓ ∧ cq = q ∧ cℓ = ℓ + 1 then some (g :: toWord cr) else none) = _
  by_cases hp : p = i
  · simp only [hp, true_and, if_true]
    by_cases hg : g < ℓ
    · simp only [hg, true_and, dif_pos]
      by_cases hc : cq = q ∧ cℓ = ℓ + 1
      · obtain ⟨rfl, rfl⟩ := hc
        rw [if_pos ⟨rfl, rfl⟩, TypeTree.rootAs_mk]
        rfl
      · rw [if_neg hc]
        have : TypeTree.rootAs ⟨ck, cq, cℓ, cr⟩ q (ℓ + 1) = none := by
          simp only [TypeTree.rootAs]; rw [dif_neg hc]
        rw [this]; rfl
    · simp [hg]
  · simp [hp]

/-- **The query of the children on words.** -/
theorem kidW_eq (q ℓ i : ℕ) (Ln : List Item) (On : List TypeTree) :
    (kidL q ℓ (kidsOf Ln On i)).map toWord = kidW q ℓ i (Ln.map (·.1)) (On.map toWord) := by
  unfold kidL kidsOf kidW
  rw [List.zip_map, List.filterMap_map, List.map_filterMap, List.filterMap_map, List.filterMap_filter]
  congr 1
  funext y
  simp only [Function.comp, Prod.map]
  rw [kidSel_eq]
  by_cases hp : y.1.1.1 = i
  · simp only [hp, decide_true, if_true]
    by_cases hg : y.1.1.2 < ℓ
    · simp only [hg, dif_pos]
      cases TypeTree.rootAs y.2 q (ℓ + 1) <;> rfl
    · simp [hg]
  · simp [hp]

/-- **The output word of an item of positive depth**: the header, the
answer of the canonical form on the atom words and its answer on the
children words. -/
theorem asm_words_succ (D : ResolveData) {cs : List ℕ} (hcs : ∀ Y, Y ∈ cs ↔ Y ∈ D.cols)
    (k q ℓ : ℕ) (t : Node (q + 1) ℓ) (kids : List (ℕ × TypeTree)) :
    toWord (asm D ⟨k, q + 1, ℓ, t⟩ kids) = [k, q + 1, ℓ] ++
      canonW ((atomL D k (q + 1) cs t).map toWord) ++ canonW ((kidL q ℓ kids).map toWord) := by
  rw [toWord_asm_succ D hcs, toWord_finsetOf_list, toWord_finsetOf_list]
  rfl

/-- **The output word of an item of depth `0`.** -/
theorem asm_words_zero (D : ResolveData) {cs : List ℕ} (hcs : ∀ Y, Y ∈ cs ↔ Y ∈ D.cols)
    (k ℓ : ℕ) (t : Node 0 ℓ) (kids : List (ℕ × TypeTree)) :
    toWord (asm D ⟨k, 0, ℓ, t⟩ kids) = [k, 0, ℓ] ++ canonW ((atomL D k 0 cs t).map toWord) := by
  rw [toWord_asm_zero D hcs, toWord_finsetOf_list]
  rfl

end Lax185574Proofs.ResolveRam.Glue
