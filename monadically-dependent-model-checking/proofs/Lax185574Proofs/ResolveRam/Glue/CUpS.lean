import Lax185574Proofs.ResolveRam.Glue.CFinS
import Lax185574Proofs.ResolveRam.Glue.StateUp

/-!
Facts on the state on the way up: the parts of the state, the item words,
the item words of the level below and the output words of the level
below as ranges of the library.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.Words

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem SH_up (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.up d i m)).SH = [] := rfl
theorem FA_up (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.up d i m)).FA = [] := rfl
theorem CO_up (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.up d i m)).CO = [] := rfl
theorem LL_up (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.up d i m)).LL = llW G P Q s k₀ q₀ q₀ := rfl
theorem LV_up (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.up d i m)).LV = lvsW G P Q s k₀ q₀ q₀ := rfl
theorem SG_up (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.up d i m)).SG = (Lax185574.ScatterTypes.stp G k₀ q₀).words :=
  rfl
theorem CT_up (d i m : ℕ) : (swAt G P Q s k₀ q₀ (.up d i m)).CT = ctW G P Q := rfl
theorem AT_up0 (d i : ℕ) : (swAt G P Q s k₀ q₀ (.up d i 0)).AT = [] := by simp [swAt]

theorem offL_mono {d e : ℕ} (h : d ≤ e) : offL G P Q s k₀ q₀ d ≤ offL G P Q s k₀ q₀ e := by
  induction e, h using Nat.le_induction with
  | base => exact le_rfl
  | succ e _ ih => rw [offL_succ]; omega

theorem llW_get {d e : ℕ} (hde : e ≤ d) :
    (llW G P Q s k₀ q₀ d)[e]'(by simp [llW]; omega) = (lvR G P Q s k₀ q₀ e).length := by
  simp [llW]

theorem llW_getD (d e : ℕ) :
    (llW G P Q s k₀ q₀ d).getD e 0 = if e ≤ d then (lvR G P Q s k₀ q₀ e).length else 0 := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simp [llW]; omega), llW_get G P Q s k₀ q₀ h]
  · rw [List.getD_eq_default _ _ (by simp [llW]; omega)]

theorem sum_llW {d e : ℕ} (hde : e ≤ d + 1) : ((llW G P Q s k₀ q₀ d).take e).sum = offL G P Q s k₀ q₀ e := by
  simp only [llW, offL]
  rw [← List.map_take, List.take_range, min_eq_left hde]

theorem ws_eq_LV (w : SW) (hF : w.FA = []) (hC : w.CO = []) :
    w.ws = (w.CT :: w.SH :: w.AT :: w.LL :: w.SG) ++ (w.LV ++ w.OU) := by
  rw [SW.ws_eq, hF, hC]; simp

theorem ws_get_LV (w : SW) (hF : w.FA = []) (hC : w.CO = []) (j : ℕ) :
    w.ws[4 + w.SG.length + j]? = (w.LV ++ w.OU)[j]? := by
  rw [ws_eq_LV w hF hC, List.getElem?_append_right (by simp; omega)]
  congr 1; simp; omega

theorem rng_LV (w : SW) (hF : w.FA = []) (hC : w.CO = []) (M : List (List ℕ)) {lo N : ℕ}
    (h : lo + N ≤ (w.LV ++ w.OU).length) :
    rng (w.ws ++ M) (4 + w.SG.length + lo) N = rng (w.LV ++ w.OU) lo N := by
  have hl : (w.CT :: w.SH :: w.AT :: w.LL :: w.SG).length = 4 + w.SG.length := by simp; omega
  rw [ws_eq_LV w hF hC, List.append_assoc, ← hl, rng_append_right, rng_append_left h]

/-- **Item `i` of level `d` among the words of the state on the way up.** -/
theorem ws_up_item {d e i i' m : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    (swAt G P Q s k₀ q₀ (.up e i' m)).ws[4 + (swAt G P Q s k₀ q₀ (.up e i' m)).SG.length +
        offL G P Q s k₀ q₀ d + i]? = some (itemW (lvR G P Q s k₀ q₀ d)[i]) := by
  rw [Nat.add_assoc, ws_get_LV _ (FA_up G P Q s k₀ q₀ e i' m) (CO_up G P Q s k₀ q₀ e i' m), LV_up]
  exact lvsW_get G P Q s k₀ q₀ hd hi _

theorem length_OU_up (d i m : ℕ) :
    (swAt G P Q s k₀ q₀ (.up d i m)).OU.length = (ouPre G P Q s k₀ q₀ d).length + min i (lvR G P Q s k₀ q₀ d).length := by
  rw [swAt_up_OU, List.length_append, outP, List.length_take, length_outW]

/-- **The item words of a level as a range of the state on the way up.** -/
theorem rng_up_lv {d e i' m : ℕ} (hd : d ≤ q₀) (M : List (List ℕ)) :
    rng ((swAt G P Q s k₀ q₀ (.up e i' m)).ws ++ M)
        (4 + (swAt G P Q s k₀ q₀ (.up e i' m)).SG.length + offL G P Q s k₀ q₀ d)
        (lvR G P Q s k₀ q₀ d).length = lvW G P Q s k₀ q₀ d := by
  obtain ⟨Z, hZ⟩ := lvsW_prefix G P Q s k₀ q₀ hd
  have hlen : offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length ≤
      ((swAt G P Q s k₀ q₀ (.up e i' m)).LV ++ (swAt G P Q s k₀ q₀ (.up e i' m)).OU).length := by
    rw [LV_up, hZ, lvsW_eq, List.length_append, List.length_append, List.length_append, length_pre]
    simp only [lvW, List.length_map]; omega
  rw [rng_LV _ (FA_up G P Q s k₀ q₀ e i' m) (CO_up G P Q s k₀ q₀ e i' m) M hlen, LV_up, hZ, lvsW_eq]
  rw [List.append_assoc, List.append_assoc, show offL G P Q s k₀ q₀ d =
    ((List.range d).flatMap (lvW G P Q s k₀ q₀)).length + 0 by rw [length_pre, Nat.add_zero], rng_append_right,
    rng_append_left (by simp [lvW])]
  simp [rng, lvW]

/-- **The output words of the level below as a range of the state on the way up.** -/
theorem rng_up_out {d i m : ℕ} (hd : d < q₀) (M : List (List ℕ)) :
    rng ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++ M)
        (4 + (swAt G P Q s k₀ q₀ (.up d i m)).SG.length + (swAt G P Q s k₀ q₀ (.up d i m)).LV.length)
        (lvR G P Q s k₀ q₀ (d + 1)).length = outW G P Q s k₀ q₀ (d + 1) := by
  have hOU : (swAt G P Q s k₀ q₀ (.up d i m)).OU = outW G P Q s k₀ q₀ (d + 1) ++ outP G P Q s k₀ q₀ d i := by
    rw [swAt_up_OU]; simp [ouPre, hd]
  have hlen : (swAt G P Q s k₀ q₀ (.up d i m)).LV.length + (lvR G P Q s k₀ q₀ (d + 1)).length ≤
      ((swAt G P Q s k₀ q₀ (.up d i m)).LV ++ (swAt G P Q s k₀ q₀ (.up d i m)).OU).length := by
    rw [hOU]; simp [length_outW]
  rw [rng_LV _ (FA_up G P Q s k₀ q₀ d i m) (CO_up G P Q s k₀ q₀ d i m) M hlen, hOU,
    show (swAt G P Q s k₀ q₀ (.up d i m)).LV.length = (swAt G P Q s k₀ q₀ (.up d i m)).LV.length + 0 from rfl,
    rng_append_right, rng_append_left (by simp [length_outW])]
  simp [rng, length_outW]

/-- The parents of the item words. -/
theorem lvW_parents (d : ℕ) :
    (lvW G P Q s k₀ q₀ d).map (fun w => (w.getD 0 0, w.getD 1 0)) = (lvR G P Q s k₀ q₀ d).map (·.1) := by
  simp [lvW, itemW]

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.MC Lax185574Proofs.MC.Glue
  Lax185574Proofs.Simulate in
/-- Entry `e` of the word `3` of the library. -/
theorem ev_LLe {W : ℕ} {L : List (List ℕ)} {τ : Env} {e : Expr} {j : ℕ} (hw : WordsAt L τ)
    (hi : 3 < L.length) (he : e.evalB (W + 1) τ = some j) (hj : j < L[3].length) (hl : EnvLt (W + 1) τ)
    (harr : ArrW W τ) (hW3 : 3 ≤ W) :
    (Expr.get "a" (.add (.get "st" (.lit 3)) e)).evalB (W + 1) τ = some L[3][j] := by
  have hst := hw.st 3 hi
  have hoff : off L 3 < W + 1 := hl.arrs "st" _ (List.mem_of_getElem? hst)
  have ha := hw.a 3 hi j hj
  have hval : L[3][j] < W + 1 := hl.arrs "a" _ (List.mem_of_getElem? ha)
  have hidx : off L 3 + j < W + 1 := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rw [harr "a"] at this; exact this
  exact evalB_get (ev_add (evalB_get (evalB_lit (by omega)) hst hoff) he hidx) ha hval

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.MC Lax185574Proofs.MC.Glue
  Lax185574Proofs.Simulate in
/-- An entry of the word `3` of the library, given the word. -/
theorem ev_LL3 {W : ℕ} {L : List (List ℕ)} {LL : List ℕ} {τ : Env} {e : Expr} {j : ℕ} (hw : WordsAt L τ)
    (hi : 3 < L.length) (h3 : L[3] = LL) (he : e.evalB (W + 1) τ = some j) (hj : j < LL.length)
    (hl : EnvLt (W + 1) τ) (harr : ArrW W τ) (hW3 : 3 ≤ W) :
    (Expr.get "a" (.add (.get "st" (.lit 3)) e)).evalB (W + 1) τ = some LL[j] := by
  have := ev_LLe hw hi he (by rw [h3]; exact hj) hl harr hW3
  rw [this]; congr 1
  exact List.getElem_of_eq h3 _

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning in
/-- A test of equality, as a decision. -/
theorem ev_condEq {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ} (he : e.evalB B σ = some m)
    (hf : f.evalB B σ = some n) : (Cond.eq e f).evalB B σ = some (decide (m = n)) := by
  rw [evalB_condEq he hf]; by_cases h : m = n <;> simp [h]

open Lax808846Proofs.Imp in
/-- The head of a round whose next call is the last one: the window is the
whole input. -/
def winC (c1 c2 : Cond) : Com :=
  .ite c1 (.ite c2 (asgs [("Nt", .add (.var "nx") (.lit 1)), ("Nw", .var "nx")]) .skip) .skip

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.MC Lax185574Proofs.MC.Glue
  Lax185574Proofs.Simulate in
theorem winC_run {W X : ℕ} {c1 c2 : Cond} {b1 b2 : Bool} {τ : Env} (h1 : c1.evalB (W + 1) τ = some b1)
    (h2 : c2.evalB (W + 1) τ = some b2) (hX : τ.vars "nx" = X) (hXW : X + 1 < W + 1) :
    ∃ τ' K, Run (W + 1) (winC c1 c2) τ τ' K ∧ K ≤ c1.size + c2.size + 20 ∧
      τ'.vars "Nt" = (if b1 && b2 then X + 1 else τ.vars "Nt") ∧
      τ'.vars "Nw" = (if b1 && b2 then X else τ.vars "Nw") ∧
      (∀ y, y ≠ "Nt" → y ≠ "Nw" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  cases b1 with
  | false =>
    exact ⟨τ, _, Run.ite_false h1 Run.skip, by omega, by simp, by simp, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | true =>
    cases b2 with
    | false =>
      exact ⟨τ, _, Run.ite_true h1 (Run.ite_false h2 Run.skip), by omega, by simp, by simp, fun _ _ _ => rfl,
        rfl, rfl, rfl⟩
    | true =>
      obtain ⟨τ', r, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ)
        (l := [("Nt", .add (.var "nx") (.lit 1)), ("Nw", .var "nx")])
        (f := fun y => if y = "Nt" then X + 1 else X)
        (by
          intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl
          · simp only [if_true]; exact ev_add (ev_var hX (by omega)) (evalB_lit (by omega)) hXW
          · simp only [show ("Nw" : String) ≠ "Nt" by decide, if_false]; exact ev_var hX (by omega))
        (by decide)
      refine ⟨τ', _, Run.ite_true h1 (Run.ite_true h2 r), ?_, by simp [s1 "Nt" (by simp)],
        by simp [s1 "Nw" (by simp)], fun y a b => g1 y (by simp [a, b]), a1, o1, i1⟩
      simp [asgK, Expr.size]; omega

end Lax185574Proofs.ResolveRam.Glue
