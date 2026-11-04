import Lax185574Proofs.ResolveRam.Glue.State

/-!
The state of the glue program on the way up, after the scatter type, and
the queries of the calls on words.

On the way up the round that receives the answer of the canonical form on
the atom words of item `i` keeps it (`sw_atoms`) if the item has
children. The round that receives the last answer of the item appends
the output word `[k, q, ℓ] ++ AT ++ answer` (`outWord_succ`) or
`[k, 0, ℓ] ++ answer` (`outWord_top`) to the outputs (`sw_up_item`), and
after the last item of a level drops the outputs of the level below it
(`sw_up_level`). After the last item of level `0` the outputs are the
output words of level `0` (`outs_final`).

The queries: the rank shift and the far tree send the word of the tree
of the item, the far tree also the entries of the scatter type whose
tree has first rank at least `k + 1`, a composition the answer of the
rank shift followed by a word of the filtered far tree, and the canonical
forms the words of `atomQ` and of `kidQ` (`realQ_*`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.DistanceLogic
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ResolveRam Lax185574Proofs.Words

variable {n : ℕ} {G : PartialGraph (Fin n)} {P Q : ℕ} {s : Bool} {k₀ q₀ : ℕ}

/-! ### After the scatter type -/

theorem sw_stp_up (hq : q₀ = 0) :
    swAt G P Q s k₀ q₀ (.up 0 0 0) =
      ⟨ctW G P Q, (stp G k₀ q₀).words, [], [], [n], [], [], lvW G P Q s k₀ q₀ 0, []⟩ := by
  subst hq
  simp only [swAt, lt_irrefl, if_false, List.nil_append, outP, List.take_zero,
    show (0 : ℕ) ≠ 1 by omega]
  simp [llW, lvsW, lvR_zero_length]

theorem sw_stp_dn :
    swAt G P Q s k₀ q₀ (.dn 0 0 0) =
      ⟨ctW G P Q, (stp G k₀ q₀).words, [], [], [n, 0], [], [], lvW G P Q s k₀ q₀ 0, []⟩ := by
  simp [swAt, llW, lvsW, lvR_zero_length, nxL_zero, nxW]

/-! ### The way up -/

theorem callOf_up' {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m < nUp q₀ d) :
    callOf G P Q s k₀ q₀ (.up d i m) =
      if m = 0 then .canon (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2)
      else .canon (kidQ G P Q s k₀ q₀ d i (itm G P Q s k₀ q₀ d i).2) := by
  have hm' : m < (upCalls G P Q s k₀ q₀ d ((lvR G P Q s k₀ q₀ d)[i], i)).length := by
    rw [length_upCalls]; exact hm
  rw [itm_eq G P Q s k₀ q₀ hi, callOf_up G P Q s k₀ q₀ hi hm']
  unfold nUp at hm
  rcases m with _ | _ | m
  · rfl
  · split_ifs at hm with h
    · simp [upCalls, h]
    · omega
  · split_ifs at hm <;> omega

/-- **After the atom words.** -/
theorem sw_atoms {d i : ℕ} :
    swAt G P Q s k₀ q₀ (.up d i 1) =
      { swAt G P Q s k₀ q₀ (.up d i 0) with
        AT := canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) } := by
  simp [swAt]

/-- The prefix of the outputs on the way up: those of the level below. -/
noncomputable def ouPre (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ d : ℕ) :
    List (List ℕ) := if d < q₀ then outW G P Q s k₀ q₀ (d + 1) else []

theorem swAt_up_OU (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.up d i m)).OU = ouPre G P Q s k₀ q₀ d ++
      outP G P Q s k₀ q₀ d i := rfl

theorem length_ouPre (d : ℕ) :
    (ouPre G P Q s k₀ q₀ d).length =
      if d < q₀ then (lvR G P Q s k₀ q₀ (d + 1)).length else 0 := by
  unfold ouPre; split_ifs <;> simp [length_outW]

/-- **The output word of an item with children.** -/
theorem outWord_succ {d i : ℕ} (hk : 1 ≤ k₀) (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    (outW G P Q s k₀ q₀ d)[i]'(by rwa [length_outW]) =
      (toWord (itm G P Q s k₀ q₀ d i).2).take 3 ++
        (swAt G P Q s k₀ q₀ (.up d i 1)).AT ++
        canonW (kidQ G P Q s k₀ q₀ d i (itm G P Q s k₀ q₀ d i).2) := by
  obtain ⟨ℓ, t, hx⟩ := lvR_shape G P Q s k₀ q₀ hk hd.le hi
  obtain ⟨m, hm⟩ : ∃ m, q₀ - d = m + 1 := ⟨q₀ - d - 1, by omega⟩
  revert t
  rw [hm]
  intro t hx
  rw [outW_get G P Q s k₀ q₀ hd hi hx]
  simp only [swAt, itm_eq G P Q s k₀ q₀ hi, hx]
  rfl

theorem outWord_top {i : ℕ} (hk : 1 ≤ k₀) (hi : i < (lvR G P Q s k₀ q₀ q₀).length) :
    (outW G P Q s k₀ q₀ q₀)[i]'(by rwa [length_outW]) =
      (toWord (itm G P Q s k₀ q₀ q₀ i).2).take 3 ++
        canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ q₀ i).2) := by
  obtain ⟨ℓ, t, hx⟩ := lvR_shape G P Q s k₀ q₀ hk le_rfl hi
  revert t
  rw [Nat.sub_self]
  intro t hx
  rw [outW_top G P Q s k₀ q₀ hi hx, itm_eq G P Q s k₀ q₀ hi, hx]
  rfl

/-- **After the last call of an item, next item.** -/
theorem sw_up_item {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    swAt G P Q s k₀ q₀ (.up d (i + 1) 0) =
      { swAt G P Q s k₀ q₀ (.up d i m) with
        AT := []
        OU := (swAt G P Q s k₀ q₀ (.up d i m)).OU ++ [(outW G P Q s k₀ q₀ d)[i]'(by rwa [length_outW])] } := by
  simp only [swAt, show (0 : ℕ) ≠ 1 by omega, if_false]
  rw [outP_succ G P Q s k₀ q₀ hi, List.append_assoc]

/-- **After the last item of a level, the level above.** -/
theorem sw_up_level {d m : ℕ} (hd : d + 1 ≤ q₀) :
    swAt G P Q s k₀ q₀ (.up d 0 0) =
      { swAt G P Q s k₀ q₀ (.up (d + 1) 0 m) with
        AT := []
        OU := ((swAt G P Q s k₀ q₀ (.up (d + 1) 0 m)).OU ++
          outW G P Q s k₀ q₀ (d + 1)).drop
            (ouPre G P Q s k₀ q₀ (d + 1)).length } := by
  simp only [swAt, show (0 : ℕ) ≠ 1 by omega, if_false, show d < q₀ by omega, if_true, outP,
    List.take_zero, List.append_nil]
  rw [show ((if d + 1 < q₀ then outW G P Q s k₀ q₀ (d + 1 + 1) else []) ++ outW G P Q s k₀ q₀ (d + 1)) =
    ouPre G P Q s k₀ q₀ (d + 1) ++ outW G P Q s k₀ q₀ (d + 1)
    from rfl, List.drop_left]

/-- **The outputs at the end.** -/
theorem outs_final :
    ((swAt G P Q s k₀ q₀ (.up 0 0 0)).OU ++ outW G P Q s k₀ q₀ 0).drop
      (ouPre G P Q s k₀ q₀ 0).length =
        outW G P Q s k₀ q₀ 0 := by
  rw [swAt_up_OU, outP, List.take_zero, List.append_nil, List.drop_left]

/-! ### The queries -/

theorem realQ_shift (τ : TypeTree) : realQ G k₀ q₀ (.shift τ) = toWord τ := rfl

theorem realQ_ftree (τ : TypeTree) :
    realQ G k₀ q₀ (.ftree τ) = toWord τ ++ toWord ((stp G k₀ q₀).words.filter (cutSel (τ.k + 1))) := by
  show toWord τ ++ toWord (stpCut (τ.k + 1) (stp G k₀ q₀)).words = _
  rw [stpCut_words]

theorem realQ_compose (σ ν : TypeTree) : realQ G k₀ q₀ (.compose σ ν) = toWord σ ++ toWord ν := rfl

theorem realQ_canon (ws : List (List ℕ)) : realQ G k₀ q₀ (.canon ws) = toWord ws := rfl

/-- The tree of an item from its word. -/
theorem toWord_itm (d i : ℕ) : toWord (itm G P Q s k₀ q₀ d i).2 = (itemW (itm G P Q s k₀ q₀ d i)).drop 2 :=
  rfl

/-- **The atom words on words.** -/
theorem atomQ_words (τ : TypeTree) :
    atomQ G P Q s k₀ q₀ τ = (candW τ.k τ.q τ.ℓ (colsL G)).filter
      (newAtomW (dW G P Q s) (listWords (toWord τ) 3)) := by
  rw [atomQ, atomL_words (dW_ok G P Q s k₀ q₀), listWords_tree_root]

end Lax185574Proofs.ResolveRam.Glue
