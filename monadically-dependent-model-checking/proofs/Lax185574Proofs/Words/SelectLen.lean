import Lax185574Proofs.Words.Select

/-!
The cost of `collect` (`Lax185574Proofs.Words.Select`) with the
comparisons charged by the longest word.

The theorems of `Lax185574Proofs.Words.Select` charge every comparison
`36 · total ws + 56`, which makes `collect` cubic in the number of words.
A comparison costs at most `36 · ℓ + 56` for the longest length `ℓ`, so
the same proofs with `Kc` redefined give a bound that is quadratic in
the number of words and linear in `ℓ`. The commands are those of
`Lax185574Proofs.Words.Select`.
-/

namespace Lax185574Proofs.Words.Fast

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574Proofs.Words

/-- The length of the longest word. -/
def maxLen (ws : List (List ℕ)) : ℕ := (ws.map List.length).foldr max 0

theorem length_le_maxLen {ws : List (List ℕ)} {u : List ℕ} (h : u ∈ ws) : u.length ≤ maxLen ws := by
  induction ws with
  | nil => simp at h
  | cons v ws ih =>
    simp only [maxLen, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem maxLen_le {ws : List (List ℕ)} {L : ℕ} (h : ∀ u ∈ ws, u.length ≤ L) : maxLen ws ≤ L := by
  induction ws with
  | nil => simp [maxLen]
  | cons v ws ih =>
    simp only [maxLen, List.map_cons, List.foldr_cons] at ih ⊢
    exact max_le (h v (by simp)) (ih fun u hu => h u (by simp [hu]))

theorem length_wd_le_maxLen (ws : List (List ℕ)) (i : ℕ) : (wd ws i).length ≤ maxLen ws := by
  by_cases h : i < ws.length
  · rw [wd_eq h]; exact length_le_maxLen (List.getElem_mem h)
  · simp [wd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ i)]

/-- The cost bound of one comparison. -/
def Kc (ws : List (List ℕ)) : ℕ := 36 * maxLen ws + 56

theorem cmpWords_run' {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) {i j : ℕ} (hi : σ.vars "ci" = i) (hj : σ.vars "cj" = j)
    (hil : i < ws.length) (hjl : j < ws.length) :
    ∃ σ', Run B cmpWords σ σ' (Kc ws) ∧ σ'.vars "c" = cmpCode (wd ws i) (wd ws j) := by
  obtain ⟨σ', hr, hc⟩ := cmpWords_run hw hb hi hj hil hjl
  refine ⟨σ', hr.mono ?_, by rw [hc, wd_eq hil, wd_eq hjl]⟩
  have := length_wd_le_maxLen ws i
  rw [wd_eq hil] at this
  simp only [Kc]; omega

theorem candTest_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) (hs : σ.vars "s" < ws.length) (hhp : σ.vars "hp" ≤ 1)
    (hprev : σ.vars "hp" = 1 → σ.vars "prev" < ws.length) :
    ∃ σ', Run B candTest σ σ' (Kc ws + 30) ∧
      σ'.vars "ok" = (if Cand ws (σ.vars "hp") (σ.vars "prev") (σ.vars "s") then 1 else 0) := by
  have hlen := hb.len
  have h3 := hb.three
  set σ1 := σ.setVar "ok" 1 with hσ1
  by_cases hp1 : σ.vars "hp" = 1
  · set σ2 := (σ1.setVar "ci" (σ.vars "s")).setVar "cj" (σ.vars "prev") with hσ2
    obtain ⟨σ3, hr3, hc3⟩ := cmpWords_run' (σ := σ2) (hw.of_arrs (by simp [hσ2, hσ1])
      (by simp [hσ2, hσ1]) (by simp [hσ2, hσ1])) hb (by simp [hσ2]) (by simp [hσ2]) hs (hprev hp1)
    have hok3 : σ3.vars "ok" = 1 := by
      rw [hr3.frame_var "ok" (by decide)]; simp [hσ2, hσ1]
    have hc3B : σ3.vars "c" < B := by
      have := cmpCode_le_two (wd ws (σ.vars "s")) (wd ws (σ.vars "prev")); omega
    have hcand : Cand ws (σ.vars "hp") (σ.vars "prev") (σ.vars "s") ↔ σ3.vars "c" = 2 := by
      rw [hc3, cmpCode_eq_two, Cand, hp1]; simp
    by_cases hc2 : σ3.vars "c" = 2
    · refine ⟨σ3, ?_, by rw [if_pos (hcand.mpr hc2), hok3]⟩
      unfold candTest
      refine (Run.seq (Run.assign (v := 1) (by simp; omega)) (Run.ite_true ?_
        (Run.seq (Run.assign (v := σ.vars "s") (by simp; omega))
          (Run.seq (Run.assign (v := σ.vars "prev") ?_) (Run.seq hr3
            (Run.ite_true ?_ Run.skip)))))).mono (by simp; omega)
      · rw [eq_true_iff' (by simp; omega) (by omega)]; simp [hp1]
      · have := hprev hp1; simp; omega
      · rw [eq_true_iff' hc3B (by omega)]; simp [hc2]
    · refine ⟨σ3.setVar "ok" 0, ?_, by rw [if_neg (fun h => hc2 (hcand.mp h))]; simp⟩
      unfold candTest
      refine (Run.seq (Run.assign (v := 1) (by simp; omega)) (Run.ite_true ?_
        (Run.seq (Run.assign (v := σ.vars "s") (by simp; omega))
          (Run.seq (Run.assign (v := σ.vars "prev") ?_) (Run.seq hr3
            (Run.ite_false ?_ (Run.assign (v := 0) (by simp; omega)))))))).mono (by simp; omega)
      · rw [eq_true_iff' (by simp; omega) (by omega)]; simp [hp1]
      · have := hprev hp1; simp; omega
      · rw [eq_true_iff' hc3B (by omega)]; simp [hc2]
  · have hp0 : σ.vars "hp" = 0 := by omega
    refine ⟨σ1, ?_, by simp [hσ1, Cand, hp0]⟩
    unfold candTest
    refine (Run.seq (Run.assign (v := 1) (by simp; omega)) (Run.ite_false ?_ Run.skip)).mono
      (by simp)
    rw [eq_true_iff' (by simp; omega) (by omega)]; simp [hp1]


theorem candTake_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) (hs : σ.vars "s" < ws.length) (hok : σ.vars "ok" ≤ 1)
    (hfnd : σ.vars "fnd" ≤ 1) (hbest : σ.vars "fnd" = 1 → σ.vars "best" < ws.length) :
    ∃ σ', Run B candTake σ σ' (Kc ws + 30) ∧
      (σ.vars "ok" = 1 → σ.vars "fnd" = 0 → σ'.vars "fnd" = 1 ∧ σ'.vars "best" = σ.vars "s") ∧
      (σ.vars "ok" = 1 → σ.vars "fnd" = 1 → σ'.vars "fnd" = 1 ∧
        σ'.vars "best" = if wd ws (σ.vars "s") < wd ws (σ.vars "best") then σ.vars "s"
          else σ.vars "best") ∧
      (σ.vars "ok" = 0 → σ'.vars "fnd" = σ.vars "fnd" ∧ σ'.vars "best" = σ.vars "best") := by
  have hlen := hb.len
  have h3 := hb.three
  by_cases hok1 : σ.vars "ok" = 1
  · by_cases hf0 : σ.vars "fnd" = 0
    · refine ⟨(σ.setVar "fnd" 1).setVar "best" (σ.vars "s"), ?_, fun _ _ => by simp,
        fun _ h => by omega, fun h => by omega⟩
      unfold candTake
      refine (Run.ite_true ?_ (Run.ite_true ?_ (Run.seq (Run.assign (v := 1) (by simp; omega))
        (Run.assign (v := σ.vars "s") (by simp; omega))))).mono (by simp)
      · rw [eq_true_iff' (by omega) (by omega)]; simp [hok1]
      · rw [eq_true_iff' (by omega) (by omega)]; simp [hf0]
    · have hf1 : σ.vars "fnd" = 1 := by omega
      have hbl := hbest hf1
      set σ2 := (σ.setVar "ci" (σ.vars "s")).setVar "cj" (σ.vars "best") with hσ2
      obtain ⟨σ3, hr3, hc3⟩ := cmpWords_run' (σ := σ2) (hw.of_arrs (by simp [hσ2])
        (by simp [hσ2]) (by simp [hσ2])) hb (by simp [hσ2]) (by simp [hσ2]) hs hbl
      have hc3B : σ3.vars "c" < B := by
        have := cmpCode_le_two (wd ws (σ.vars "s")) (wd ws (σ.vars "best")); omega
      have hfr : ∀ y, y ∉ cmpWords.wvars → σ3.vars y = σ2.vars y := fun y hy => hr3.frame_var y hy
      have hf3 : σ3.vars "fnd" = 1 := by rw [hfr "fnd" (by decide)]; simp [hσ2, hf1]
      have hs3 : σ3.vars "s" = σ.vars "s" := by rw [hfr "s" (by decide)]; simp [hσ2]
      have hb3 : σ3.vars "best" = σ.vars "best" := by rw [hfr "best" (by decide)]; simp [hσ2]
      by_cases hc0 : σ3.vars "c" = 0
      · have hlt : wd ws (σ.vars "s") < wd ws (σ.vars "best") := by
          rw [← cmpCode_eq_zero, ← hc3, hc0]
        refine ⟨σ3.setVar "best" (σ3.vars "s"), ?_, fun _ h => by omega,
          fun _ _ => ⟨by simp [hf3], by simp [hs3, hlt]⟩, fun h => by omega⟩
        unfold candTake
        refine (Run.ite_true ?_ (Run.ite_false ?_ (Run.seq (Run.assign (v := σ.vars "s")
          (by simp; omega)) (Run.seq (Run.assign (v := σ.vars "best") (by simp; omega))
          (Run.seq hr3 (Run.ite_true ?_ (Run.assign (by simp [hs3]; omega)))))))).mono
          (by simp; omega)
        · rw [eq_true_iff' (by omega) (by omega)]; simp [hok1]
        · rw [eq_true_iff' (by omega) (by omega)]; simp [hf0]
        · rw [eq_true_iff' hc3B (by omega)]; simp [hc0]
      · have hnlt : ¬ wd ws (σ.vars "s") < wd ws (σ.vars "best") := by
          rw [← cmpCode_eq_zero, ← hc3]; exact hc0
        refine ⟨σ3, ?_, fun _ h => by omega,
          fun _ _ => ⟨hf3, by simp [hb3, hnlt]⟩, fun h => by omega⟩
        unfold candTake
        refine (Run.ite_true ?_ (Run.ite_false ?_ (Run.seq (Run.assign (v := σ.vars "s")
          (by simp; omega)) (Run.seq (Run.assign (v := σ.vars "best") (by simp; omega))
          (Run.seq hr3 (Run.ite_false ?_ Run.skip)))))).mono (by simp; omega)
        · rw [eq_true_iff' (by omega) (by omega)]; simp [hok1]
        · rw [eq_true_iff' (by omega) (by omega)]; simp [hf0]
        · rw [eq_true_iff' hc3B (by omega)]; simp [hc0]
  · have hok0 : σ.vars "ok" = 0 := by omega
    refine ⟨σ, ?_, fun h => by omega, fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
    unfold candTake
    refine (Run.ite_false ?_ Run.skip).mono (by simp)
    rw [eq_true_iff' (by omega) (by omega)]; simp [hok0]


theorem selBody_step {B : ℕ} {ws : List (List ℕ)} {hp p : ℕ} (hb : WordsBound B ws)
    (hhp : hp ≤ 1) (hprev : hp = 1 → p < ws.length) {τ : Env} (hI : SelInv ws hp p τ)
    (hc : (Cond.lt (.var "s") (.var "m")).evalB B τ = some true) :
    ∃ τ', Run B selBody τ τ' (2 * Kc ws + 64) ∧ SelInv ws hp p τ' ∧
      ws.length - τ'.vars "s" < ws.length - τ.vars "s" := by
  obtain ⟨hsle, hm, hhpv, hpv, hw, hfnd, h0, h1⟩ := hI
  have hs : τ.vars "s" < ws.length := by
    have := lt_of_condLt_true hc; rwa [hm] at this
  have hlen := hb.len
  obtain ⟨τ1, hr1, hok1⟩ := candTest_run hw hb hs (by omega) (by rw [hhpv, hpv]; exact hprev)
  rw [hhpv, hpv] at hok1
  have hfr1 : ∀ y, y ∉ candTest.wvars → τ1.vars y = τ.vars y := fun y hy => hr1.frame_var y hy
  have hw1 : WordsAt ws τ1 := hw.of_arrs (hr1.frame_arr "a" (by decide))
    (hr1.frame_arr "st" (by decide)) (hr1.frame_arr "ln" (by decide))
  have hs1 : τ1.vars "s" = τ.vars "s" := hfr1 "s" (by decide)
  have hf1 : τ1.vars "fnd" = τ.vars "fnd" := hfr1 "fnd" (by decide)
  have hb1 : τ1.vars "best" = τ.vars "best" := hfr1 "best" (by decide)
  obtain ⟨τ2, hr2, hA, hB, hC⟩ := candTake_run hw1 hb (by omega)
    (by rw [hok1]; split <;> omega) (by omega)
    (fun h => by have := (h1 (by omega)).1; omega)
  simp only [hs1, hf1, hb1, hok1] at hA hB hC
  have hfr2 : ∀ y, y ∉ candTake.wvars → τ2.vars y = τ1.vars y := fun y hy => hr2.frame_var y hy
  have hw2 : WordsAt ws τ2 := hw1.of_arrs (hr2.frame_arr "a" (by decide))
    (hr2.frame_arr "st" (by decide)) (hr2.frame_arr "ln" (by decide))
  have hs2 : τ2.vars "s" = τ.vars "s" := by rw [hfr2 "s" (by decide), hs1]
  have hr : Run B selBody τ (τ2.setVar "s" (τ.vars "s" + 1)) (2 * Kc ws + 64) := by
    unfold selBody
    exact (Run.seq hr1 (Run.seq hr2 (Run.assign (by simp [hs2]; omega)))).mono (by simp; omega)
  refine ⟨_, hr, ⟨by simp; omega, ?_, ?_, ?_, hw2.of_arrs (by simp) (by simp) (by simp), ?_, ?_,
    ?_⟩, by simp; omega⟩
  · simp only [vars_setVar]; simp only [show ("m" : String) = "s" ↔ False by decide, if_false]
    rw [hfr2 "m" (by decide), hfr1 "m" (by decide), hm]
  · simp only [vars_setVar]; simp only [show ("hp" : String) = "s" ↔ False by decide, if_false]
    rw [hfr2 "hp" (by decide), hfr1 "hp" (by decide), hhpv]
  · simp only [vars_setVar]; simp only [show ("prev" : String) = "s" ↔ False by decide, if_false]
    rw [hfr2 "prev" (by decide), hfr1 "prev" (by decide), hpv]
  all_goals simp only [vars_setVar, show ("fnd" : String) = "s" ↔ False by decide,
    show ("best" : String) = "s" ↔ False by decide, if_false, if_true]
  all_goals by_cases hcs : Cand ws hp p (τ.vars "s")
  all_goals simp only [hcs, if_true, if_false] at hA hB hC
  · rcases Nat.lt_or_ge 0 (τ.vars "fnd") with h | h
    · rw [(hB (by simp) (by omega)).1]
    · rw [(hA (by simp) (by omega)).1]
  · rw [(hC (by simp)).1]; exact hfnd
  · intro hf
    rcases Nat.lt_or_ge 0 (τ.vars "fnd") with h | h
    · rw [(hB (by simp) (by omega)).1] at hf; omega
    · rw [(hA (by simp) (by omega)).1] at hf; omega
  · intro hf i hi hci
    rw [(hC (by simp)).1] at hf
    rcases Nat.lt_or_ge i (τ.vars "s") with h | h
    · exact h0 hf i h hci
    · have : i = τ.vars "s" := by omega
      subst this; exact hcs hci
  · intro _
    rcases Nat.lt_or_ge 0 (τ.vars "fnd") with h | h
    · obtain ⟨hf2, hb2⟩ := hB (by simp) (by omega)
      obtain ⟨hbs, hcb, hmin⟩ := h1 (by omega)
      rw [hb2]
      by_cases hlt : wd ws (τ.vars "s") < wd ws (τ.vars "best")
      · simp only [hlt, if_true]
        refine ⟨by omega, hcs, fun i hi hci => ?_⟩
        rcases Nat.lt_or_ge i (τ.vars "s") with h' | h'
        · exact le_trans (le_of_lt hlt) (hmin i h' hci)
        · have : i = τ.vars "s" := by omega
          subst this; exact le_rfl
      · simp only [hlt, if_false]
        refine ⟨by omega, hcb, fun i hi hci => ?_⟩
        rcases Nat.lt_or_ge i (τ.vars "s") with h' | h'
        · exact hmin i h' hci
        · have : i = τ.vars "s" := by omega
          subst this; exact not_lt.mp hlt
    · obtain ⟨hf2, hb2⟩ := hA (by simp) (by omega)
      rw [hb2]
      refine ⟨by omega, hcs, fun i hi hci => ?_⟩
      rcases Nat.lt_or_ge i (τ.vars "s") with h' | h'
      · exact absurd hci (h0 (by omega) i h')
      · have : i = τ.vars "s" := by omega
        subst this; exact le_rfl
  · intro hf
    obtain ⟨hf2, hb2⟩ := hC (by simp)
    rw [hf2] at hf
    obtain ⟨hbs, hcb, hmin⟩ := h1 hf
    rw [hb2]
    refine ⟨by omega, hcb, fun i hi hci => ?_⟩
    rcases Nat.lt_or_ge i (τ.vars "s") with h' | h'
    · exact hmin i h' hci
    · have : i = τ.vars "s" := by omega
      subst this; exact absurd hci hcs


/-- The cost bound of the selection. -/
def Ks (ws : List (List ℕ)) : ℕ := (2 * Kc ws + 68) * ws.length + 8

theorem select_run {B : ℕ} {ws : List (List ℕ)} {hp p : ℕ} (hb : WordsBound B ws)
    (hhp : hp ≤ 1) (hprev : hp = 1 → p < ws.length) {σ : Env} (hw : WordsAt ws σ)
    (hm : σ.vars "m" = ws.length) (hhpv : σ.vars "hp" = hp) (hpv : σ.vars "prev" = p) :
    ∃ σ', Run B select σ σ' (Ks ws) ∧ SelInv ws hp p σ' ∧ σ'.vars "s" = ws.length := by
  have hlen := hb.len
  set σ0 := (σ.setVar "fnd" 0).setVar "s" 0 with hσ0
  have hI0 : SelInv ws hp p σ0 :=
    ⟨by simp [hσ0], by simp [hσ0, hm], by simp [hσ0, hhpv], by simp [hσ0, hpv],
      hw.of_arrs (by simp [hσ0]) (by simp [hσ0]) (by simp [hσ0]), by simp [hσ0],
      fun _ i hi => by simp [hσ0] at hi, fun h => by simp [hσ0] at h⟩
  obtain ⟨σ', hr, hI, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "s") (.var "m")) (c := selBody) (SelInv ws hp p)
      (fun τ => ws.length - τ.vars "s") (2 * Kc ws + 64)
      (fun τ hI => evalB_condLt_vars (by have := hI.1; omega) (by rw [hI.2.1]; omega))
      (fun τ hI hc => selBody_step hb hhp hprev hI hc) hI0
  have hsm : σ'.vars "s" = ws.length := by
    have := le_of_condLt_false hfalse; rw [hI.2.1] at this; have := hI.1; omega
  refine ⟨σ', ?_, hI, hsm⟩
  unfold select
  refine (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq (Run.assign (v := 0)
    (by simp; omega)) hr)).mono ?_
  have : σ0.vars "s" = 0 := by simp [hσ0]
  simp only [this, Ks, size_condLt, size_var, size_lit, Nat.sub_zero]
  ring_nf; omega


theorem collectBody_step {B : ℕ} {ws : List (List ℕ)} (hb : WordsBound B ws) {τ : Env}
    (hI : CollectInv ws τ) (hc : (Cond.eq (.var "fnd") (.lit 1)).evalB B τ = some true) :
    ∃ τ', Run B collectBody τ τ' (Ks ws + 11) ∧ CollectInv ws τ' ∧
      (sortedDistinct ws).length - τ'.vars "cnt" < (sortedDistinct ws).length - τ.vars "cnt" := by
  obtain ⟨hR, hm, hw, hol, hord, hfnd, hfi, hfb⟩ := hI
  have hlen := hb.len
  have h3 := hb.three
  have hf1 : τ.vars "fnd" = 1 := by
    simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at hc
    obtain ⟨m, n, ⟨rfl, -⟩, ⟨rfl, -⟩, h⟩ := hc
    simpa using h.symm
  have ht := hfi.mp hf1
  obtain ⟨hbl, hwb⟩ := hfb hf1
  have hLle := length_sortedDistinct_le ws
  generalize htdef : τ.vars "cnt" = t at ht hwb hord
  set σ1 : Env := (((τ.setArr "ord" t (τ.vars "best")).setVar "cnt" (t + 1)).setVar "prev"
    (τ.vars "best")).setVar "hp" 1 with hσ1
  have hR1 : RoundParams ws (t + 1) 1 (τ.vars "best") :=
    ⟨by omega, by simp, fun _ => ⟨hbl, by simpa using hwb⟩⟩
  obtain ⟨σ2, hr2, hsel, hs2⟩ := select_run (σ := σ1) (hp := 1) (p := τ.vars "best") hb
    (by omega) (fun _ => hbl)
    (hw.of_arrs (by simp [hσ1]) (by simp [hσ1]) (by simp [hσ1])) (by simp [hσ1, hm])
    (by simp [hσ1]) (by simp [hσ1])
  obtain ⟨hf2, hfi2, hfb2⟩ := sel_result hR1 hsel hs2
  have hfr : ∀ y, y ∉ select.wvars → σ2.vars y = σ1.vars y := fun y hy => hr2.frame_var y hy
  have hfa : ∀ b, b ∉ select.warrs → σ2.arrs b = σ1.arrs b := fun b hb => hr2.frame_arr b hb
  have hc2 : σ2.vars "cnt" = t + 1 := by rw [hfr "cnt" (by decide)]; simp [hσ1]
  have hhp2 : σ2.vars "hp" = 1 := by rw [hfr "hp" (by decide)]; simp [hσ1]
  have hp2 : σ2.vars "prev" = τ.vars "best" := by rw [hfr "prev" (by decide)]; simp [hσ1]
  have hord2 : σ2.arrs "ord" = (τ.arrs "ord").set t (τ.vars "best") := by
    rw [hfa "ord" (by decide)]; simp [hσ1]
  refine ⟨σ2, ?_, ⟨by rw [hc2, hhp2, hp2]; exact hR1, by rw [hfr "m" (by decide)]; simp [hσ1, hm],
    hsel.2.2.2.2.1, by rw [hord2]; simp [hol], ?_, hf2,
    by rw [hc2]; exact hfi2, by rw [hc2]; exact hfb2⟩, by rw [hc2]; omega⟩
  · unfold collectBody
    refine (Run.seq (Run.store (idx := t) (v := τ.vars "best") (by simp [htdef]; omega)
      (by simp; omega) (by omega)) (Run.seq (Run.assign (v := t + 1) (by simp [htdef]; omega))
        (Run.seq (Run.assign (v := τ.vars "best") (by simp; omega))
          (Run.seq (Run.assign (v := 1) (by simp; omega)) hr2)))).mono (by simp; omega)
  · intro s hs
    rw [hc2] at hs
    rw [hord2]
    rcases Nat.lt_or_ge s t with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hord s h
    · have hst : s = t := by omega
      subst hst
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
      exact ⟨hbl, hwb⟩

theorem collect_run {B : ℕ} {ws : List (List ℕ)} (hb : WordsBound B ws) {σ : Env}
    (hw : WordsAt ws σ) (hm : σ.vars "m" = ws.length) (hol : ws.length ≤ (σ.arrs "ord").length) :
    ∃ σ', Run B collect σ σ' ((Ks ws + 15) * (ws.length + 1) + 4) ∧
      σ'.vars "cnt" = (sortedDistinct ws).length ∧ WordsAt ws σ' ∧
      ws.length ≤ (σ'.arrs "ord").length ∧
      (∀ s < (sortedDistinct ws).length, (σ'.arrs "ord").getD s 0 < ws.length ∧
        wd ws ((σ'.arrs "ord").getD s 0) = (sortedDistinct ws).getD s []) := by
  have hlen := hb.len
  have h3 := hb.three
  have hLle := length_sortedDistinct_le ws
  set σ1 : Env := (σ.setVar "hp" 0).setVar "cnt" 0 with hσ1
  have hR0 : RoundParams ws 0 0 (σ.vars "prev") := ⟨by omega, by simp, fun h => absurd h (lt_irrefl 0)⟩
  obtain ⟨σ2, hr2, hsel, hs2⟩ := select_run (σ := σ1) (hp := 0) (p := σ.vars "prev") hb
    (by omega) (fun h => absurd h (by omega))
    (hw.of_arrs (by simp [hσ1]) (by simp [hσ1]) (by simp [hσ1])) (by simp [hσ1, hm])
    (by simp [hσ1]) (by simp [hσ1])
  obtain ⟨hf2, hfi2, hfb2⟩ := sel_result hR0 hsel hs2
  have hfr : ∀ y, y ∉ select.wvars → σ2.vars y = σ1.vars y := fun y hy => hr2.frame_var y hy
  have hfa : ∀ b, b ∉ select.warrs → σ2.arrs b = σ1.arrs b := fun b hb => hr2.frame_arr b hb
  have hc2 : σ2.vars "cnt" = 0 := by rw [hfr "cnt" (by decide)]; simp [hσ1]
  have hI2 : CollectInv ws σ2 := by
    refine ⟨?_, by rw [hfr "m" (by decide)]; simp [hσ1, hm], hsel.2.2.2.2.1,
      by rw [hfa "ord" (by decide)]; simpa [hσ1] using hol, by rw [hc2]; simp,
      hf2, by rw [hc2]; exact hfi2, by rw [hc2]; exact hfb2⟩
    rw [hc2, hfr "hp" (by decide), hfr "prev" (by decide)]
    simpa [hσ1] using hR0
  obtain ⟨σ', hloop, hI', hfalse⟩ :=
    Run.while_count (B := B) (b := .eq (.var "fnd") (.lit 1)) (c := collectBody)
      (CollectInv ws) (fun τ => (sortedDistinct ws).length - τ.vars "cnt") (Ks ws + 11)
      (fun τ hI => ⟨_, eq_true_iff' (by have := hI.2.2.2.2.2.1; omega) (by omega)⟩)
      (fun τ hI hc => collectBody_step hb hI hc) hI2
  obtain ⟨hR', -, hw', hol', hord', hf', hfi', -⟩ := hI'
  have hf0 : σ'.vars "fnd" ≠ 1 := by
    rw [eq_true_iff' (by omega) (by omega)] at hfalse; simpa using hfalse
  have hcnt : σ'.vars "cnt" = (sortedDistinct ws).length := by
    have := hR'.1; have := hfi'.not.mp hf0; omega
  refine ⟨σ', ?_, hcnt, hw', hol', fun s hs => hord' s (by omega)⟩
  unfold collect
  refine (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq (Run.assign (v := 0)
    (by simp; omega)) (Run.seq hr2 hloop))).mono ?_
  rw [hc2]
  simp only [size_condEq, Expr.size, Nat.sub_zero]
  have : (sortedDistinct ws).length ≤ ws.length := hLle
  nlinarith


end Lax185574Proofs.Words.Fast
