import Lax185574Proofs.ResolveRam.Glue.CFE

/-!
The output of the last round of the glue program of lem:resolve-lift.

The last call is at the position `up 0 i m` of the last step of the last
item of level `0` (`fe_last`). There the library of the round is the
state at that position, and `feOut` with the scalars of that state is
`0` followed by the output of lem:resolve-lift (`fe_out`): the last `i`
words of the state are the output words of the first `i` items of level
`0`, the word with index `4 + |SG| + i` is the word of item `i`, and the
output word of item `i` is the head `k, q, ℓ` of its tree, the answer on
its atom words and the answer of the last call. `fECmd_run`: the end
command writes it after the start of the last round.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- **The last position.** The position whose next position is the end is
the last step of the last item of level `0`. -/
theorem fe_last {c : Cur} (hv : Valid G P Q s k₀ q₀ c) (hf : next G P Q s k₀ q₀ c = .fin) :
    ∃ i m, c = .up 0 i m ∧ i + 1 = (lvR G P Q s k₀ q₀ 0).length ∧ m + 1 = nUp q₀ 0 := by
  cases c with
  | stp => simp only [next] at hf; split_ifs at hf
  | dn d i m => simp only [next] at hf; split_ifs at hf
  | fin => exact hv.elim
  | up d i m =>
    obtain ⟨-, hi, hm⟩ := hv
    simp only [next] at hf
    split_ifs at hf with h1 h2 h3
    subst h3
    exact ⟨i, m, rfl, by omega, by omega⟩

/-- The last round: the position of the last call. -/
theorem fe_cur (hn : 1 ≤ n) {j : ℕ} (hj : j + 1 = (rcalls G P Q s k₀ q₀).length) :
    Valid G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) ∧ next G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) = .fin ∧
      (rcalls G P Q s k₀ q₀)[j]? = some (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) := by
  obtain ⟨hv, hc⟩ := rcalls_get G P Q s k₀ q₀ hn (j := j) (by omega)
  refine ⟨hv, ?_, hc⟩
  rw [← cur_succ, hj]
  exact cur_length G P Q s k₀ q₀ hn

theorem fe_winOf {c : Cur} (hf : next G P Q s k₀ q₀ c = .fin) :
    winOf G P Q s k₀ q₀ c = (xIn G k₀ q₀ P Q s).length := by
  simp [winOf, hf]

section facts

variable {G P Q s k₀ q₀}

theorem fe_ws (i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.up 0 i m)).ws =
      (([ctW G P Q, [], (swAt G P Q s k₀ q₀ (.up 0 i m)).AT, llW G P Q s k₀ q₀ q₀] ++
        (stp G k₀ q₀).words) ++ (lvsW G P Q s k₀ q₀ q₀ ++ ouPre G P Q s k₀ q₀ 0)) ++
          outP G P Q s k₀ q₀ 0 i := by
  simp [SW.ws, swAt, ouPre]

theorem fe_len_outP {i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ 0).length) :
    (outP G P Q s k₀ q₀ 0 i).length = i := by
  simp [outP, length_outW]; omega

/-- The output words of the first `i` items are the last `i` words. -/
theorem fe_drop {i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ 0).length) :
    (swAt G P Q s k₀ q₀ (.up 0 i m)).ws.drop ((swAt G P Q s k₀ q₀ (.up 0 i m)).ws.length - i) =
      outP G P Q s k₀ q₀ 0 i := by
  rw [fe_ws, List.length_append, fe_len_outP hi, Nat.add_sub_cancel, List.drop_left]

/-- The word of item `i` of level `0`. -/
theorem fe_item {i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ 0).length) :
    (swAt G P Q s k₀ q₀ (.up 0 i m)).ws[4 + (swAt G P Q s k₀ q₀ (.up 0 i m)).SG.length +
      (swAt G P Q s k₀ q₀ (.up 0 i m)).FA.length + (swAt G P Q s k₀ q₀ (.up 0 i m)).CO.length + i]? =
      some (itemW (lvR G P Q s k₀ q₀ 0)[i]) := by
  have h := lvsW_get G P Q s k₀ q₀ (d := 0) (e := q₀) (Nat.zero_le _) hi
    ((if 0 < q₀ then outW G P Q s k₀ q₀ 1 else []) ++ outP G P Q s k₀ q₀ 0 i)
  simp only [offL, List.range_zero, List.map_nil, List.sum_nil, Nat.zero_add] at h
  have e : (swAt G P Q s k₀ q₀ (.up 0 i m)).ws =
      ([ctW G P Q, [], (swAt G P Q s k₀ q₀ (.up 0 i m)).AT, llW G P Q s k₀ q₀ q₀] ++ (stp G k₀ q₀).words) ++
        (lvsW G P Q s k₀ q₀ q₀ ++ ((if 0 < q₀ then outW G P Q s k₀ q₀ 1 else []) ++
          outP G P Q s k₀ q₀ 0 i)) := by
    simp [SW.ws, swAt]
  rw [e, List.getElem?_append_right (by simp [swAt]; omega)]
  convert h using 2
  simp [swAt]
  omega

theorem fe_len_item (x : Item) : 5 ≤ (itemW x).length := by
  simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree]

theorem fe_dl (ws : List (List ℕ)) : feDl ≤ (rY G k₀ q₀ (.canon ws)).length := by
  simp [feDl, dLen, rY, yA, yB, yC, yE, yF]; omega

theorem fe_ans (ws : List (List ℕ)) :
    ((rY G k₀ q₀ (.canon ws)).drop fePl).take ((rY G k₀ q₀ (.canon ws)).length - feDl) = canonW ws :=
  realY_seg G k₀ q₀ (.canon ws)

end facts

/-- **The output of the last round.** -/
theorem fe_out (hk : 1 ≤ k₀) {i m : ℕ} (hi : i + 1 = (lvR G P Q s k₀ q₀ 0).length)
    (hm : m + 1 = nUp q₀ 0) :
    feOut (hWord G s P Q) n i
        (4 + (swAt G P Q s k₀ q₀ (.up 0 i m)).SG.length + (swAt G P Q s k₀ q₀ (.up 0 i m)).FA.length +
          (swAt G P Q s k₀ q₀ (.up 0 i m)).CO.length + i)
        (swAt G P Q s k₀ q₀ (.up 0 i m)).ws (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.up 0 i m))) =
      0 :: zOut G k₀ q₀ P Q s := by
  have hi' : i < (lvR G P Q s k₀ q₀ 0).length := by omega
  have hm' : m < nUp q₀ 0 := by omega
  rw [zOut_outs G P Q s k₀ q₀ hk, feOut, hWord, fe_drop hi', List.getD_eq_getElem?_getD, fe_item hi',
    Option.getD_some, callOf_up' hi' hm']
  have hw2 : (swAt G P Q s k₀ q₀ (.up 0 i m)).ws.getD 2 [] = (swAt G P Q s k₀ q₀ (.up 0 i m)).AT := by
    simp [SW.ws]
  rw [hw2, ← outP_full G P Q s k₀ q₀ 0, ← hi, outP_succ G P Q s k₀ q₀ hi', List.flatten_append,
    List.flatten_singleton, show (itemW (lvR G P Q s k₀ q₀ 0)[i]).drop 2 =
      toWord (itm G P Q s k₀ q₀ 0 i).2 by rw [itm_eq G P Q s k₀ q₀ hi']; rfl]
  by_cases hq : q₀ = 0
  · subst hq
    have hm0 : m = 0 := by simp [nUp] at hm; omega
    subst hm0
    rw [if_pos rfl, fe_ans]
    have hAT : (swAt G P Q s k₀ 0 (.up 0 i 0)).AT = [] := by simp [swAt]
    rw [hAT, outWord_top hk hi']
    simp
  · have hm1 : m = 1 := by simp [nUp, show 0 < q₀ by omega] at hm; omega
    subst hm1
    rw [if_neg (by omega), fe_ans, outWord_succ hk (by omega) hi']
    simp

end Lax185574Proofs.ResolveRam.Glue
