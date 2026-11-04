import Lax185574Proofs.ResolveRam.Glue.CaseDn

/-!
The lengths of the levels after an item on the way down.

The round that finishes item `i` of level `d` writes the new word of the
lengths of the levels as `llNew LL d e z`: the first `d + 1` lengths,
the length of the part of level `d + 1` built so far plus the number `e`
of new items, and `z` zeros (`ll_next_item`, `ll_next_level`,
`ll_down_end`, `ll_down_empty`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.Words

variable {n : ℕ} {G : PartialGraph (Fin n)} {P Q : ℕ} {s : Bool} {k₀ q₀ : ℕ}

/-- The new lengths of the levels. -/
def llNew (LL : List ℕ) (d e z : ℕ) : List ℕ := LL.take (d + 1) ++ [LL.getD (d + 1) 0 + e] ++ List.replicate z 0

theorem length_llW (d : ℕ) : (llW G P Q s k₀ q₀ d).length = d + 1 := by simp [llW]

theorem llNew_eq (d x e z : ℕ) :
    llNew (llW G P Q s k₀ q₀ d ++ [x]) d e z = llW G P Q s k₀ q₀ d ++ [x + e] ++ List.replicate z 0 := by
  have hl := length_llW (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) d
  simp only [llNew]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hl]

theorem ll_dn (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn d i m)).LL = llW G P Q s k₀ q₀ d ++ [(nxW G P Q s k₀ q₀ d i).length] := by
  simp [swAt, nxW]

/-- **Next item.** -/
theorem ll_next_item {d i : ℕ} (e : ℕ)
    (he : (nxW G P Q s k₀ q₀ d (i + 1)).length = (nxW G P Q s k₀ q₀ d i).length + e) (m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn d (i + 1) 0)).LL = llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d e 0 := by
  rw [ll_dn, ll_dn, llNew_eq, he]; simp

/-- **Next level.** -/
theorem ll_next_level {d i : ℕ} (e : ℕ) (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length)
    (he : (nxW G P Q s k₀ q₀ d (i + 1)).length = (nxW G P Q s k₀ q₀ d i).length + e) (m : ℕ) :
    (swAt G P Q s k₀ q₀ (.dn (d + 1) 0 0)).LL = llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d e 1 := by
  rw [sw_next_level, ll_dn, llNew_eq, ← hi, he]; simp

/-- **The last level of the way down.** -/
theorem ll_down_end {d i : ℕ} (e : ℕ) (hd : d + 1 = q₀) (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length)
    (he : (nxW G P Q s k₀ q₀ d (i + 1)).length = (nxW G P Q s k₀ q₀ d i).length + e) (m : ℕ) :
    (swAt G P Q s k₀ q₀ (.up (d + 1) 0 0)).LL = llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d e 0 := by
  rw [sw_down_end hd, ll_dn, llNew_eq, ← hi, he]; simp

/-- **The next level is empty.** -/
theorem ll_down_empty {d i : ℕ} (e : ℕ) (hd : d < q₀) (hi : i + 1 = (lvR G P Q s k₀ q₀ d).length)
    (h0 : (lvR G P Q s k₀ q₀ (d + 1)).length = 0)
    (he : (nxW G P Q s k₀ q₀ d (i + 1)).length = (nxW G P Q s k₀ q₀ d i).length + e) (m : ℕ) :
    (swAt G P Q s k₀ q₀ (.up d 0 0)).LL = llNew (swAt G P Q s k₀ q₀ (.dn d i m)).LL d e (q₀ - d - 1) := by
  rw [sw_down_empty hd h0, ll_dn, llNew_eq]
  have h1 : (nxW G P Q s k₀ q₀ d (i + 1)).length = 0 := by
    rw [hi, nxW_full, lvW_nil _ _ _ _ _ _ h0]; rfl
  rw [show (nxW G P Q s k₀ q₀ d i).length + e = 0 by omega, List.append_assoc, List.singleton_append,
    ← List.replicate_succ, show q₀ - d - 1 + 1 = q₀ - d by omega]

end Lax185574Proofs.ResolveRam.Glue
