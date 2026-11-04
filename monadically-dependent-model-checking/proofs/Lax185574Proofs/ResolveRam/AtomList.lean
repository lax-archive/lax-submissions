import Lax185574Proofs.ResolveRam.Script

/-!
The assembly of an output from two answers of the canonical form.

The program enumerates the atoms of rank `(k, q)` in a fixed order (pairs
of positions, then colors, then radii), tests each by `newAtomTest` on the
root word, and gives the list of the words that pass to the canonical
form (`atomL`). It gives the list of the words of the children with their
guards to the canonical form a second time (`kidL`). The canonical form
returns the words of the finite sets, so the word of the output of an
item is its header followed by the two answers (`toWord_asm_succ`,
`toWord_asm_zero`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.WordEncoding Lax185574.DistanceLogic Lax185574.TypeTrees
open Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The pairs of positions, row by row. -/
def pairsL (ℓ : ℕ) : List (Fin ℓ × Fin ℓ) :=
  (List.finRange ℓ).flatMap fun i => (List.finRange ℓ).map fun j => (i, j)

/-- The atoms of rank `(k, q)` with colors from the list `cs`, in the
order of the program. -/
def candL (k q ℓ : ℕ) (cs : List ℕ) : List (DistFO ℓ) :=
  (pairsL ℓ).map (fun p => DistFO.eq p.1 p.2) ++ (pairsL ℓ).map (fun p => DistFO.edge p.1 p.2) ++
    (pairsL ℓ).map (fun p => DistFO.nonEdge p.1 p.2) ++
    cs.flatMap (fun Y => (List.finRange ℓ).map fun i => DistFO.color Y i) ++
    (List.range (rhoMinus k q + 1)).flatMap (fun s => (pairsL ℓ).map fun p => DistFO.distLe s p.1 p.2) ++
    (List.range (rhoPlus k q + 1)).flatMap fun s =>
      cs.flatMap fun Y => (List.finRange ℓ).map fun i => DistFO.distColorLt s Y i

/-- The atoms of the new root, in the order of the program. -/
def atomL (D : ResolveData) (k q : ℕ) (cs : List ℕ) {q' ℓ : ℕ} (t : Node q' ℓ) : List (DistFO ℓ) :=
  (candL k q ℓ cs).filter fun φ => decide (newAtomTest D t φ)

theorem mem_pairsL {ℓ : ℕ} (p : Fin ℓ × Fin ℓ) : p ∈ pairsL ℓ := by
  simp [pairsL]

theorem mem_candL {k q ℓ : ℕ} {cs : List ℕ} {cols : Finset ℕ} (hcs : ∀ Y, Y ∈ cs ↔ Y ∈ cols)
    (φ : DistFO ℓ) : φ ∈ candL k q ℓ cs ↔ φ ∈ candidates k q ℓ cols := by
  simp only [candL, candidates, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_finRange, Finset.mem_union, Finset.mem_image, Finset.mem_univ, Finset.mem_product,
    Finset.mem_range, hcs, mem_pairsL, true_and, and_true, Prod.exists, and_assoc, exists_and_left]

theorem mem_atomL (D : ResolveData) (k q : ℕ) {cs : List ℕ} (hcs : ∀ Y, Y ∈ cs ↔ Y ∈ D.cols)
    {q' ℓ : ℕ} (t : Node q' ℓ) (φ : DistFO ℓ) : φ ∈ atomL D k q cs t ↔ φ ∈ newAtoms D k q t := by
  simp only [atomL, List.mem_filter, mem_candL hcs, decide_eq_true_eq, newAtoms, Finset.mem_filter]

theorem finsetOf_list {α : Type*} [DecidableEq α] (l : List α) :
    finsetOf {x | x ∈ l} = l.toFinset := by
  ext x
  rw [mem_finsetOf l.finite_toSet, List.mem_toFinset]
  rfl

/-- The children as extensions. -/
def kidL (q ℓ : ℕ) (kids : List (ℕ × TypeTree)) : List (Fin ℓ × Node q (ℓ + 1)) :=
  kids.filterMap fun p =>
    if h : p.1 < ℓ then (TypeTree.rootAs p.2 q (ℓ + 1)).map fun r => ((⟨p.1, h⟩ : Fin ℓ), r)
    else none

theorem kidSet_eq (q ℓ : ℕ) (kids : List (ℕ × TypeTree)) :
    kidSet q ℓ kids = finsetOf {x | x ∈ kidL q ℓ kids} := by
  rw [finsetOf_list]; rfl

theorem newAtoms_eq (D : ResolveData) (k q : ℕ) {cs : List ℕ} (hcs : ∀ Y, Y ∈ cs ↔ Y ∈ D.cols)
    {q' ℓ : ℕ} (t : Node q' ℓ) : newAtoms D k q t = finsetOf {x | x ∈ atomL D k q cs t} := by
  rw [finsetOf_list]
  ext φ
  rw [List.mem_toFinset, mem_atomL D k q hcs]

/-- **The word of an output of positive depth.** -/
theorem toWord_asm_succ (D : ResolveData) {cs : List ℕ} (hcs : ∀ Y, Y ∈ cs ↔ Y ∈ D.cols)
    (k q ℓ : ℕ) (t : Node (q + 1) ℓ) (kids : List (ℕ × TypeTree)) :
    toWord (asm D ⟨k, q + 1, ℓ, t⟩ kids) = toWord (k, q + 1, ℓ) ++
      toWord (finsetOf {x | x ∈ atomL D k (q + 1) cs t}) ++
        toWord (finsetOf {x | x ∈ kidL q ℓ kids}) := by
  rw [← newAtoms_eq D k (q + 1) hcs, ← kidSet_eq, List.append_assoc]
  rfl

/-- **The word of an output of depth `0`.** -/
theorem toWord_asm_zero (D : ResolveData) {cs : List ℕ} (hcs : ∀ Y, Y ∈ cs ↔ Y ∈ D.cols)
    (k ℓ : ℕ) (t : Node 0 ℓ) (kids : List (ℕ × TypeTree)) :
    toWord (asm D ⟨k, 0, ℓ, t⟩ kids) = toWord (k, 0, ℓ) ++
      toWord (finsetOf {x | x ∈ atomL D k 0 cs t}) := by
  rw [← newAtoms_eq D k 0 hcs]
  rfl

end Lax185574Proofs.ResolveRam
