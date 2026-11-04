import Lax185574Proofs.ResolveRam.Glue.Sched
import Lax185574Proofs.ResolveRam.Glue.ExpW
import Lax185574Proofs.ResolveRam.Glue.KidW
import Lax185574Proofs.ResolveRam.Answers
import Lax185574Proofs.ResolveRam.Glue.Input

/-!
The bookkeeping of the glue program of lem:resolve-lift on words.

The glue program keeps the levels as lists of item words `itemW` (the
parent, the guard and the word of the tree). On the way down, after the
items `0, …, i - 1` of level `d`, the next level holds their expansions
(`nxL d i`), and after the last item it is level `d + 1` (`nxL_full`).
Finishing item `i` appends the words `i :: w` for the words `w` of
`exW` on the root of its tree and the answers of the compositions with
the members of the filtered far tree (`nxW_succ`). On the way up, the
output of item `i` of level `d` is its header followed by the answers of
the canonical form on the atom words and on the children words
(`outW_succ`, `outW_top`), and the children words are `kidW` on the
parents, guards and output words of level `d + 1` (`kidQ_words`). The
outputs of level `0` are the trees of the vertices after the resolve, so
the output of the program is the word of `H`, `n` and the output words of
level `0` (`zOut_outs`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ResolveRam Lax185574Proofs.Words
open Lax185574.DistanceMatrix

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The word of an item: the parent, the guard and the word of the tree. -/
def itemW (x : Item) : List ℕ := x.1.1 :: x.1.2 :: toWord x.2

/-- The members of the expansion of an item with index `i`, as items. -/
def asItems (i : ℕ) (ex : List (ℕ × TypeTree)) : List Item := ex.map fun gc => ((i, gc.1), gc.2)

/-- The expansions of the first `i` items of level `d`. -/
noncomputable def nxL (d i : ℕ) : List Item :=
  ((lvR G P Q s k₀ q₀ d).zipIdx.take i).flatMap fun x => asItems x.2 (exR G P Q s k₀ q₀ x.1.2)

theorem nxL_zero (d : ℕ) : nxL G P Q s k₀ q₀ d 0 = [] := by simp [nxL]

theorem nxL_full (d : ℕ) : nxL G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length = lvR G P Q s k₀ q₀ (d + 1) := by
  rw [lvR_succ, nxL, List.take_of_length_le (by simp)]
  rfl

theorem nxL_succ {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    nxL G P Q s k₀ q₀ d (i + 1) = nxL G P Q s k₀ q₀ d i ++
      asItems i (exR G P Q s k₀ q₀ (lvR G P Q s k₀ q₀ d)[i].2) := by
  have hz : i < (lvR G P Q s k₀ q₀ d).zipIdx.length := by simpa using hi
  rw [nxL, nxL, List.take_add_one, List.getElem?_eq_getElem hz, List.flatMap_append]
  simp [List.getElem_zipIdx]

/-- The items of a level above the last are trees of depth `q₀ - d`. -/
theorem lvR_shape (hk₀ : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    ∃ (ℓ : ℕ) (t : Node (q₀ - d) ℓ), (lvR G P Q s k₀ q₀ d)[i].2 = ⟨k₀ + d, q₀ - d, ℓ, t⟩ := by
  obtain ⟨ℓ, u, hu, -⟩ := lvR_good G P Q s k₀ q₀ hk₀ hd (List.getElem_mem hi)
  exact ⟨ℓ, _, hu⟩

/-- The words of the expansion of an item. -/
theorem exR_words {Dw : DW} (h : Dw.OK (dataOf G P Q s k₀ q₀)) (i k q ℓ : ℕ) (t : Node (q + 1) ℓ) :
    (asItems i (exR G P Q s k₀ q₀ ⟨k, q + 1, ℓ, t⟩)).map itemW =
      (exW Dw k q ℓ (toWord t) ((faP G (dataOf G P Q s k₀ q₀) ⟨k, q + 1, ℓ, t⟩).map
        fun ν => toWord (coOf G (shOf G ⟨k, q + 1, ℓ, t⟩) ν))).map (i :: ·) := by
  have := exW_eq h (shOf G) (faP G (dataOf G P Q s k₀ q₀)) (coOf G) k q ℓ t
  rw [← this, List.map_map, asItems, List.map_map]
  rfl

/-- The words of the partial next level. -/
noncomputable def nxW (d i : ℕ) : List (List ℕ) := (nxL G P Q s k₀ q₀ d i).map itemW

/-- **Finishing an item on the way down.** -/
theorem nxW_succ {Dw : DW} (h : Dw.OK (dataOf G P Q s k₀ q₀)) {d i k q ℓ : ℕ} {t : Node (q + 1) ℓ}
    (hi : i < (lvR G P Q s k₀ q₀ d).length) (hx : (lvR G P Q s k₀ q₀ d)[i].2 = ⟨k, q + 1, ℓ, t⟩) :
    nxW G P Q s k₀ q₀ d (i + 1) = nxW G P Q s k₀ q₀ d i ++
      (exW Dw k q ℓ (toWord t) ((faP G (dataOf G P Q s k₀ q₀) ⟨k, q + 1, ℓ, t⟩).map
        fun ν => toWord (coOf G (shOf G ⟨k, q + 1, ℓ, t⟩) ν))).map (i :: ·) := by
  rw [nxW, nxL_succ G P Q s k₀ q₀ hi, List.map_append, hx, exR_words G P Q s k₀ q₀ h]
  rfl

/-- The word of the tree of an item. -/
theorem itemW_tree (x : Item) : (itemW x).drop 2 = toWord x.2 := rfl

theorem itemW_root (x : Item) : (itemW x).drop 5 = toWord x.2.root := rfl

/-! ### The outputs -/

theorem length_outR (m d : ℕ) : (outR G P Q s k₀ q₀ m d).length = (lvR G P Q s k₀ q₀ d).length := by
  cases m <;> simp [outR, outsAt, outLevel, lvR]

/-- The output of item `i` of a level above the last. -/
theorem outR_get {d i : ℕ} (hd : d < q₀) (hi : i < (outR G P Q s k₀ q₀ (q₀ - d) d).length) :
    (outR G P Q s k₀ q₀ (q₀ - d) d)[i] = asm (dataOf G P Q s k₀ q₀)
      ((lvR G P Q s k₀ q₀ d)[i]'(by rwa [length_outR] at hi)).2
      (kidsOf (lvR G P Q s k₀ q₀ (d + 1)) (outR G P Q s k₀ q₀ (q₀ - (d + 1)) (d + 1)) i) := by
  obtain ⟨m, hm⟩ : ∃ m, q₀ - d = m + 1 := ⟨q₀ - d - 1, by omega⟩
  have hm' : q₀ - (d + 1) = m := by omega
  simp only [outR, hm, hm', outsAt, outLevel, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rfl

/-- The output of item `i` of the last level. -/
theorem outR_get_top {i : ℕ} (hi : i < (outR G P Q s k₀ q₀ 0 q₀).length) :
    (outR G P Q s k₀ q₀ 0 q₀)[i] =
      asm (dataOf G P Q s k₀ q₀) ((lvR G P Q s k₀ q₀ q₀)[i]'(by rwa [length_outR] at hi)).2 [] := by
  simp only [outR, outsAt, List.getElem_map]
  rfl

/-- The output words of level `d`. -/
noncomputable def outW (d : ℕ) : List (List ℕ) := (outR G P Q s k₀ q₀ (q₀ - d) d).map toWord

theorem length_outW (d : ℕ) : (outW G P Q s k₀ q₀ d).length = (lvR G P Q s k₀ q₀ d).length := by
  rw [outW, List.length_map, length_outR]

theorem hcs_colsL : ∀ Y, Y ∈ colsL G ↔ Y ∈ (dataOf G P Q s k₀ q₀).cols :=
  fun Y => mem_colsL G P Q s k₀ q₀ Y

/-- **The children words of an item.** -/
theorem kidQ_words (d i k q ℓ : ℕ) (t : Node (q + 1) ℓ) :
    kidQ G P Q s k₀ q₀ d i ⟨k, q + 1, ℓ, t⟩ =
      kidW q ℓ i ((lvR G P Q s k₀ q₀ (d + 1)).map (·.1)) (outW G P Q s k₀ q₀ (d + 1)) := by
  rw [kidQ, kidW_eq]
  rfl

/-- **The output word of an item of a level above the last.** -/
theorem outW_get {d i k q ℓ : ℕ} {t : Node (q + 1) ℓ} (hd : d < q₀)
    (hi : i < (lvR G P Q s k₀ q₀ d).length) (hx : (lvR G P Q s k₀ q₀ d)[i].2 = ⟨k, q + 1, ℓ, t⟩) :
    (outW G P Q s k₀ q₀ d)[i]'(by rwa [length_outW]) = [k, q + 1, ℓ] ++
      canonW (atomQ G P Q s k₀ q₀ ⟨k, q + 1, ℓ, t⟩) ++
      canonW (kidQ G P Q s k₀ q₀ d i ⟨k, q + 1, ℓ, t⟩) := by
  simp only [outW, List.getElem_map]
  rw [outR_get G P Q s k₀ q₀ hd (by rwa [length_outR])]
  simp only [hx]
  rw [asm_words_succ _ (hcs_colsL G P Q s k₀ q₀)]
  rfl

/-- **The output word of an item of the last level.** -/
theorem outW_top {i k ℓ : ℕ} {t : Node 0 ℓ} (hi : i < (lvR G P Q s k₀ q₀ q₀).length)
    (hx : (lvR G P Q s k₀ q₀ q₀)[i].2 = ⟨k, 0, ℓ, t⟩) :
    (outW G P Q s k₀ q₀ q₀)[i]'(by rwa [length_outW]) = [k, 0, ℓ] ++
      canonW (atomQ G P Q s k₀ q₀ ⟨k, 0, ℓ, t⟩) := by
  have h0 : outW G P Q s k₀ q₀ q₀ = (outR G P Q s k₀ q₀ 0 q₀).map toWord := by
    rw [outW, Nat.sub_self]
  simp only [h0, List.getElem_map]
  rw [outR_get_top G P Q s k₀ q₀ (by rwa [length_outR])]
  simp only [hx]
  rw [asm_words_zero _ (hcs_colsL G P Q s k₀ q₀)]
  rfl

/-- The first `i` output words of level `d`. -/
noncomputable def outP (d i : ℕ) : List (List ℕ) := (outW G P Q s k₀ q₀ d).take i

theorem outP_succ {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    outP G P Q s k₀ q₀ d (i + 1) =
      outP G P Q s k₀ q₀ d i ++ [(outW G P Q s k₀ q₀ d)[i]'(by rwa [length_outW])] := by
  rw [outP, outP, List.take_add_one, List.getElem?_eq_getElem]
  rfl

theorem outP_full (d : ℕ) : outP G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length = outW G P Q s k₀ q₀ d := by
  rw [outP, List.take_of_length_le (by rw [length_outW])]

/-! ### The output of the program -/

/-- **The output.** The word of the output is the word of `H`, the word
of its distance matrix, then `n` and the output words of level `0`. -/
theorem zOut_outs (hk : 1 ≤ k₀) :
    zOut G k₀ q₀ P Q s = toWord (resolveBy G s P Q) ++ toWord (distMatrix (resolveBy G s P Q)) ++
      (n :: (outW G P Q s k₀ q₀ 0).flatten) := by
  have hs := script_family (dataOf G P Q s k₀ q₀) (farMapOf G) hk (dataOf_spec G P Q s k₀ q₀)
    (farSpec_farMapOf G) (expandOK_exR G P Q s k₀ q₀)
  have ho : outR G P Q s k₀ q₀ q₀ 0 =
      (List.finRange n).map fun b => family (resolveBy G s P Q) k₀ q₀ b := hs
  simp only [zOut]
  change toWord (resolveBy G s P Q) ++ (toWord (distMatrix (resolveBy G s P Q)) ++
    toWord (family (resolveBy G s P Q) k₀ q₀)) = _
  rw [toWord_family, List.append_assoc]
  congr 3
  rw [outW, Nat.sub_zero, ho, List.map_map, List.ofFn_eq_map]
  rfl

end Lax185574Proofs.ResolveRam.Glue
