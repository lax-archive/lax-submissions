import Lax185574Proofs.Words.Emit
import Mathlib.Data.List.GetD
import Lax185574Proofs.Words.Computes
import Lax185574.CanonicalForm
import Lax185574Proofs.Interface.Poly

/-!
The canonical form of a list of words, computed on the word RAM.

The program `prog` is written in IMP+ and compiled by the compiler of
lax-808846. It reads a list of words into arrays, selects the distinct
words in increasing order by repeated scans, and writes their number and
their frames. Correctness and cost are proved in the bounded semantics of
IMP+, and `Lax185574Proofs.Words.computes_of_run` turns this into
`Computes`.

The selection works in rounds. Round `t` scans all words and keeps the
smallest candidate, where a candidate of round `0` is any word and a
candidate of round `t + 1` is a word above the word selected in round
`t`. The word selected in round `t` is entry `t` of the sorted list of
distinct words (`Lax185574Proofs.Words.eq_getElem_of_min_cand`), and
round `t` finds no candidate exactly when `t` is the number of distinct
words.
-/

namespace Lax185574Proofs.CanonicalForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding

/-- Word `i` of `ws`, or the empty word. -/
def wd (ws : List (List ℕ)) (i : ℕ) : List ℕ := ws.getD i []

theorem wd_eq {ws : List (List ℕ)} {i : ℕ} (h : i < ws.length) : wd ws i = ws[i] := by
  simp [wd, h]

theorem length_wd_le (ws : List (List ℕ)) (i : ℕ) : (wd ws i).length ≤ total ws := by
  rcases lt_or_ge i ws.length with h | h
  · rw [wd_eq h]; have := off_add_le h; omega
  · simp [wd, h]

/-- The cost bound of one comparison. -/
def Kc (ws : List (List ℕ)) : ℕ := 36 * total ws + 56

theorem cmpWords_run' {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) {i j : ℕ} (hi : σ.vars "ci" = i) (hj : σ.vars "cj" = j)
    (hil : i < ws.length) (hjl : j < ws.length) :
    ∃ σ', Run B cmpWords σ σ' (Kc ws) ∧ σ'.vars "c" = cmpCode (wd ws i) (wd ws j) := by
  obtain ⟨σ', hr, hc⟩ := cmpWords_run hw hb hi hj hil hjl
  refine ⟨σ', hr.mono ?_, by rw [hc, wd_eq hil, wd_eq hjl]⟩
  have := length_wd_le ws i
  rw [wd_eq hil] at this
  simp only [Kc]; omega

/-- Whether word `i` is a candidate: there is no previous selection
(`hp = 0`), or it is above the previous selection `p`. -/
def Cand (ws : List (List ℕ)) (hp p i : ℕ) : Prop := hp = 0 ∨ wd ws p < wd ws i

instance (ws : List (List ℕ)) (hp p i : ℕ) : Decidable (Cand ws hp p i) := by
  unfold Cand; infer_instance

/-- Test whether word `s` is a candidate, leaving `1` or `0` in `ok`. -/
def candTest : Com :=
  .seq (.assign "ok" (.lit 1))
    (.ite (.eq (.var "hp") (.lit 1))
      (.seq (.assign "ci" (.var "s")) (.seq (.assign "cj" (.var "prev")) (.seq cmpWords
        (.ite (.eq (.var "c") (.lit 2)) .skip (.assign "ok" (.lit 0))))))
      .skip)

theorem eq_true_iff' {B : ℕ} {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x < B) (hn : n < B) :
    (Cond.eq (.var x) (.lit n)).evalB B σ = some (decide (σ.vars x = n)) := by
  rw [evalB_condEq (evalB_var hx) (evalB_lit hn)]
  by_cases h : σ.vars x = n <;> simp [h]

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

/-- If word `s` is a candidate, make it the selection when there is none
yet or when it is below the selection `best`. -/
def candTake : Com :=
  .ite (.eq (.var "ok") (.lit 1))
    (.ite (.eq (.var "fnd") (.lit 0))
      (.seq (.assign "fnd" (.lit 1)) (.assign "best" (.var "s")))
      (.seq (.assign "ci" (.var "s")) (.seq (.assign "cj" (.var "best")) (.seq cmpWords
        (.ite (.eq (.var "c") (.lit 0)) (.assign "best" (.var "s")) .skip)))))
    .skip

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

/-- One round of the selection scan. -/
def selBody : Com := .seq candTest (.seq candTake (.assign "s" (.add (.var "s") (.lit 1))))

/-- Select the smallest candidate: `fnd` becomes `1` if there is one,
and `best` its index. -/
def select : Com :=
  .seq (.assign "fnd" (.lit 0)) (.seq (.assign "s" (.lit 0))
    (.while (.lt (.var "s") (.var "m")) selBody))

/-- The result of the selection after scanning the words below `s`. -/
def SelInv (ws : List (List ℕ)) (hp p : ℕ) (τ : Env) : Prop :=
  τ.vars "s" ≤ ws.length ∧ τ.vars "m" = ws.length ∧ τ.vars "hp" = hp ∧ τ.vars "prev" = p ∧
    WordsAt ws τ ∧ τ.vars "fnd" ≤ 1 ∧
    (τ.vars "fnd" = 0 → ∀ i < τ.vars "s", ¬ Cand ws hp p i) ∧
    (τ.vars "fnd" = 1 → τ.vars "best" < τ.vars "s" ∧ Cand ws hp p (τ.vars "best") ∧
      ∀ i < τ.vars "s", Cand ws hp p i → wd ws (τ.vars "best") ≤ wd ws i)

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

theorem wd_mem {ws : List (List ℕ)} {i : ℕ} (h : i < ws.length) : wd ws i ∈ ws := by
  rw [wd_eq h]; exact List.getElem_mem h

theorem exists_wd_of_mem {ws : List (List ℕ)} {u : List ℕ} (h : u ∈ ws) :
    ∃ i < ws.length, wd ws i = u := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, wd_eq hi⟩

/-- The selection parameters of round `t`. -/
def RoundParams (ws : List (List ℕ)) (t hp p : ℕ) : Prop :=
  t ≤ (sortedDistinct ws).length ∧ hp = (if t = 0 then 0 else 1) ∧
    (0 < t → p < ws.length ∧ wd ws p = (sortedDistinct ws).getD (t - 1) [])

theorem cand_iff {ws : List (List ℕ)} {t hp p i : ℕ} (hR : RoundParams ws t hp p)
    (hi : i < ws.length) : Cand ws hp p i ↔ IsCand ws t (wd ws i) := by
  obtain ⟨ht, hhp, hp⟩ := hR
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · simp only [if_true] at hhp
    simp only [Cand, hhp, true_or, true_iff]
    exact ⟨wd_mem hi, fun h => absurd h (lt_irrefl 0)⟩
  · have hne : t ≠ 0 := by omega
    simp only [hne, if_false] at hhp
    obtain ⟨_, hwp⟩ := hp h0
    have hL : t - 1 < (sortedDistinct ws).length := by omega
    rw [List.getD_eq_getElem _ _ hL] at hwp
    simp only [Cand, hhp, one_ne_zero, false_or, IsCand, hwp]
    exact ⟨fun h => ⟨wd_mem hi, fun _ _ => h⟩, fun h => h.2 h0 hL⟩

/-- What the selection of round `t` finds. -/
theorem sel_result {ws : List (List ℕ)} {t hp p : ℕ} (hR : RoundParams ws t hp p)
    {τ : Env} (hI : SelInv ws hp p τ) (hs : τ.vars "s" = ws.length) :
    τ.vars "fnd" ≤ 1 ∧ (τ.vars "fnd" = 1 ↔ t < (sortedDistinct ws).length) ∧
      (τ.vars "fnd" = 1 → τ.vars "best" < ws.length ∧
        wd ws (τ.vars "best") = (sortedDistinct ws).getD t []) := by
  obtain ⟨-, -, -, -, -, hfnd, h0, h1⟩ := hI
  rw [hs] at h0 h1
  have ht := hR.1
  refine ⟨hfnd, ⟨fun hf => ?_, fun hlt => ?_⟩, fun hf => ?_⟩
  · obtain ⟨hbl, hcb, -⟩ := h1 hf
    exact (cand_exists_iff ht).mp ⟨_, (cand_iff hR hbl).mp hcb⟩
  · by_contra hf
    obtain ⟨u, hu⟩ := (cand_exists_iff ht).mpr hlt
    obtain ⟨i, hi, rfl⟩ := exists_wd_of_mem hu.1
    exact h0 (by omega) i hi ((cand_iff hR hi).mpr hu)
  · obtain ⟨hbl, hcb, hmin⟩ := h1 hf
    have hlt : t < (sortedDistinct ws).length := (cand_exists_iff ht).mp ⟨_, (cand_iff hR hbl).mp hcb⟩
    refine ⟨hbl, ?_⟩
    rw [List.getD_eq_getElem _ _ hlt]
    refine eq_getElem_of_min_cand hlt ((cand_iff hR hbl).mp hcb) fun v hv => ?_
    obtain ⟨i, hi, rfl⟩ := exists_wd_of_mem hv.1
    exact hmin i hi ((cand_iff hR hi).mpr hv)

/-- Record the selection as the next word of the output, and select
again above it. -/
def collectBody : Com :=
  .seq (.store "ord" (.var "cnt") (.var "best")) (.seq (.assign "cnt" (.add (.var "cnt") (.lit 1)))
    (.seq (.assign "prev" (.var "best")) (.seq (.assign "hp" (.lit 1)) select)))

/-- Select the distinct words in increasing order, recording their
indices in `ord` and their number in `cnt`. -/
def collect : Com :=
  .seq (.assign "hp" (.lit 0)) (.seq (.assign "cnt" (.lit 0)) (.seq select
    (.while (.eq (.var "fnd") (.lit 1)) collectBody)))

/-- The invariant of `collect`: `cnt` words have been recorded, and the
selection of the next round has been made. -/
def CollectInv (ws : List (List ℕ)) (τ : Env) : Prop :=
  RoundParams ws (τ.vars "cnt") (τ.vars "hp") (τ.vars "prev") ∧ τ.vars "m" = ws.length ∧
    WordsAt ws τ ∧ (τ.arrs "ord").length = ws.length ∧
    (∀ s < τ.vars "cnt", (τ.arrs "ord").getD s 0 < ws.length ∧
      wd ws ((τ.arrs "ord").getD s 0) = (sortedDistinct ws).getD s []) ∧
    τ.vars "fnd" ≤ 1 ∧ (τ.vars "fnd" = 1 ↔ τ.vars "cnt" < (sortedDistinct ws).length) ∧
    (τ.vars "fnd" = 1 → τ.vars "best" < ws.length ∧
      wd ws (τ.vars "best") = (sortedDistinct ws).getD (τ.vars "cnt") [])

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
    (hw : WordsAt ws σ) (hm : σ.vars "m" = ws.length) (hol : (σ.arrs "ord").length = ws.length) :
    ∃ σ', Run B collect σ σ' ((Ks ws + 15) * (ws.length + 1) + 4) ∧
      σ'.vars "cnt" = (sortedDistinct ws).length ∧ WordsAt ws σ' ∧
      (σ'.arrs "ord").length = ws.length ∧
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

/-- Write the next recorded word. -/
def emitBody : Com :=
  .seq (.assign "ow" (.get "ord" (.var "t")))
    (.seq writeWord (.assign "t" (.add (.var "t") (.lit 1))))

/-- Write the number of recorded words, then the words. -/
def emitAll : Com :=
  .seq (.write (.var "cnt")) (.seq (.assign "t" (.lit 0))
    (.while (.lt (.var "t") (.var "cnt")) emitBody))

theorem frames_take_succ {L : List (List ℕ)} {t : ℕ} (h : t < L.length) :
    frames (L.take (t + 1)) = frames (L.take t) ++ (L[t].length :: L[t]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [frames, List.map_append, List.flatten_append, Option.toList_some, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem emitAll_run {B : ℕ} {ws : List (List ℕ)} (hb : WordsBound B ws) {σ : Env}
    (hw : WordsAt ws σ) (hcnt : σ.vars "cnt" = (sortedDistinct ws).length)
    (hol : (σ.arrs "ord").length = ws.length)
    (hord : ∀ s < (sortedDistinct ws).length, (σ.arrs "ord").getD s 0 < ws.length ∧
        wd ws ((σ.arrs "ord").getD s 0) = (sortedDistinct ws).getD s []) :
    ∃ σ', Run B emitAll σ σ' ((13 * total ws + 25) * ws.length + 8) ∧
      σ'.out = σ.out ++ toWord (sortedDistinct ws) := by
  have hlen := hb.len
  have hLle := length_sortedDistinct_le ws
  set L := sortedDistinct ws with hL
  let I : Env → Prop := fun τ => τ.vars "cnt" = L.length ∧ τ.vars "t" ≤ L.length ∧
    WordsAt ws τ ∧ τ.arrs "ord" = σ.arrs "ord" ∧
    τ.out = σ.out ++ (L.length :: frames (L.take (τ.vars "t")))
  set σ0 : Env := { σ with out := σ.out ++ [L.length] }.setVar "t" 0 with hσ0
  obtain ⟨σ', hloop, ⟨hc', ht', -, -, hout'⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "t") (.var "cnt")) (c := emitBody) I
      (fun τ => L.length - τ.vars "t") (13 * total ws + 21)
      (fun τ hI => evalB_condLt_vars (by have := hI.2.1; omega) (by rw [hI.1]; omega))
      (by
        rintro τ ⟨hc, ht, hwτ, hoτ, hout⟩ hcond
        have htl : τ.vars "t" < L.length := by
          have := lt_of_condLt_true hcond; rwa [hc] at this
        obtain ⟨hol', hwo⟩ := hord _ htl
        set o := (σ.arrs "ord").getD (τ.vars "t") 0 with ho
        have hget : (τ.arrs "ord")[τ.vars "t"]? = some o := by
          rw [hoτ, ho, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
        set τ1 := τ.setVar "ow" o with hτ1
        obtain ⟨τ2, hr2, hout2⟩ := writeWord_run (σ := τ1) (i := o)
          (hwτ.of_arrs (by simp [hτ1]) (by simp [hτ1]) (by simp [hτ1])) hb (by simp [hτ1]) hol'
        have hfr : ∀ y, y ∉ writeWord.wvars → τ2.vars y = τ1.vars y := fun y hy => hr2.frame_var y hy
        have hfa : ∀ b, b ∉ writeWord.warrs → τ2.arrs b = τ1.arrs b := fun b hb => hr2.frame_arr b hb
        have ht2 : τ2.vars "t" = τ.vars "t" := by rw [hfr "t" (by decide)]; simp [hτ1]
        have hlo := length_wd_le ws o
        rw [wd_eq hol'] at hlo hwo
        rw [List.getD_eq_getElem _ _ htl] at hwo
        have hc2 : τ2.vars "cnt" = L.length := by rw [hfr "cnt" (by decide)]; simp [hτ1, hc]
        refine ⟨τ2.setVar "t" (τ.vars "t" + 1), ?_, ⟨by simp [hc2], by simp; omega,
          hwτ.of_arrs (by simp [hfa "a" (by decide), hτ1]) (by simp [hfa "st" (by decide), hτ1])
            (by simp [hfa "ln" (by decide), hτ1]), by simp [hfa "ord" (by decide), hτ1, hoτ], ?_⟩,
          by simp; omega⟩
        · unfold emitBody
          refine (Run.seq (Run.assign (v := o) ?_) (Run.seq hr2 (Run.assign (by simp [ht2]; omega)))).mono
            (by simp; omega)
          simp only [evalB_get_iff, evalB_var_iff]
          exact ⟨τ.vars "t", ⟨rfl, by omega⟩, hget, by omega⟩
        · simp only [out_setVar, hout2, hτ1, out_setVar, hout, hwo]
          simp only [vars_setVar, if_true, frames_take_succ htl]
          simp)
      (show I σ0 by
        refine ⟨by simp [hσ0, hcnt], by simp [hσ0], hw.of_arrs (by simp [hσ0]) (by simp [hσ0])
          (by simp [hσ0]), by simp [hσ0], by simp [hσ0, frames]⟩)
  have htL : σ'.vars "t" = L.length := by
    have := le_of_condLt_false hfalse; rw [hc'] at this; omega
  refine ⟨σ', ?_, ?_⟩
  · unfold emitAll
    refine (Run.seq (Run.write (v := L.length) (by simp [hcnt]; omega))
      (Run.seq (Run.assign (v := 0) (by simp; omega)) hloop)).mono ?_
    have : σ0.vars "t" = 0 := by simp [hσ0]
    rw [this]
    simp only [size_condLt, Expr.size, Nat.sub_zero]
    nlinarith
  · rw [hout', htL, List.take_length, toWord_words]

/-- The whole program: read the words, collect the distinct ones in
increasing order, write them. -/
def prog : Com := .seq readWords (.seq collect emitAll)

/-- The scalars and arrays of `prog`. -/
def layout : Lax808846Proofs.Compile.Layout :=
  ⟨["m", "i", "p", "n", "j", "v", "ci", "cj", "pa", "pb", "la", "lb", "k", "c", "fnd", "s", "ok",
    "best", "hp", "prev", "cnt", "t", "ow"], ["a", "st", "ln", "ord"], 4⟩

theorem prog_ok : Lax808846Proofs.Compile.Com.Ok layout prog := by
  simp [prog, readWords, readWord, readEntries, readEntry, collect, collectBody, select, selBody,
    candTest, candTake, cmpWords, cmpStep, entA, entB, emitAll, emitBody, writeWord, writeEntry,
    layout, Lax808846Proofs.Compile.Com.Ok, Lax808846Proofs.Compile.Cond.Ok,
    Lax808846Proofs.Compile.condExpr, Lax808846Proofs.Compile.Expr.Ok]

/-- The array lengths `prog` needs. -/
def extOf (ws : List (List ℕ)) : String → ℕ := fun a =>
  if a = "a" then total ws else if a = "st" ∨ a = "ln" ∨ a = "ord" then ws.length else 0

theorem prog_run (ws : List (List ℕ)) :
    ∃ σ', Run (valBound 4 1 (toWord ws)) prog (initEnv (extOf ws) (toWord ws)) σ'
      (400 * ((toWord ws).length + 1) ^ 3) ∧ σ'.out = toWord (sortedDistinct ws) := by
  set x := toWord ws with hx
  set B := valBound 4 1 x with hB
  have hN := length_toWord_words ws
  rw [← hx] at hN
  have hxne : x ≠ [] := by rw [hx, toWord_words]; simp
  have hM : ∀ v ∈ x, v ≤ maxEntry x := fun v hv => le_maxEntry hv
  have hBdef : B = 4 * (x.length + maxEntry x + 1) := by simp [hB, valBound]
  have hb : WordsBound B ws := ⟨by omega, fun u hu v hv => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      have := hM v (by rw [hx]; exact (mem_toWord_words hi).2 v hv)
      omega, by omega⟩
  obtain ⟨σ1, hr1, hm1, -, hw1⟩ := readWords_wordsAt (B := B) (ws := ws) (rest := [])
    (σ := initEnv (extOf ws) x) (by simp [initEnv, hx]) (by simp [initEnv, extOf])
    (by simp [initEnv, extOf]) (by simp [initEnv, extOf]) (by rw [← hx]; omega)
    (fun v hv => by rw [← hx] at hv; have := hM v hv; omega)
  have hol1 : (σ1.arrs "ord").length = ws.length := by
    rw [hr1.frame_arr "ord" (by decide)]; simp [initEnv, extOf]
  obtain ⟨σ2, hr2, hc2, hw2, hol2, hord2⟩ := collect_run hb hw1 hm1 hol1
  obtain ⟨σ3, hr3, hout3⟩ := emitAll_run hb hw2 hc2 hol2 hord2
  have hout2 : σ2.out = [] := by
    rw [hr2.out_eq (by decide), hr1.out_eq (by decide)]; rfl
  refine ⟨σ3, (Run.seq hr1 (Run.seq hr2 hr3)).mono ?_, by rw [hout3, hout2]; rfl⟩
  have hm : ws.length ≤ x.length := by omega
  have ht : total ws ≤ x.length := by omega
  have hL := length_sortedDistinct_le ws
  simp only [Ks, Kc]
  generalize x.length = N at hm ht hN ⊢
  generalize ws.length = m at hm hL ⊢
  generalize total ws = T at ht ⊢
  nlinarith [Nat.mul_le_mul hm ht, Nat.mul_le_mul hm hm]

/-- The word of the finite set of the entries of `l` is the word of the
sorted distinct words of the entries. -/
theorem toWord_finsetOf {α : Type} [WordEncoding α] (l : List α) :
    toWord (finsetOf {x | x ∈ l}) = toWord (sortedDistinct (l.map toWord)) := by
  have hfin : {x | x ∈ l}.Finite := List.finite_toSet l
  have himg : (finsetOf {x | x ∈ l}).image toWord = (l.map toWord).toFinset := by
    ext u
    simp only [finsetOf, dif_pos hfin, Finset.mem_image, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, List.mem_toFinset, List.mem_map]
  change toWord (Finset.words (finsetOf {x | x ∈ l})) = _
  rw [Finset.words, himg]
  rfl

/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_canonical_old :
    ∃ (p : Lax808846.Ram.Program) (e c a : ℕ),
      ∀ (α : Type) [WordEncoding α] (l : List α),
        Lax185574.Computing.Computes p e c (l.map toWord) (finsetOf {x | x ∈ l})
          (fun m => c * (m + 1) ^ a) := by
  refine ⟨Lax808846Proofs.Compile.compileProgram layout prog, 1, bridgeConst layout 4 400, 3,
    fun α _ l => ?_⟩
  refine computes_of_run prog_ok (by norm_num) le_rfl ?_ ?_
  · rw [toWord_words]; simp
  · obtain ⟨σ', hr, hout⟩ := prog_run (l.map toWord)
    exact ⟨extOf (l.map toWord), σ', hr, by rw [hout, toWord_finsetOf]⟩

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.CanonicalForm.exists_program_canonical
---
The program reads the list of words into arrays, the entries one after
the other with the start and the length of every word. It then selects
the distinct words in increasing order: in round `t` it scans all words
and keeps the smallest one above the word selected in round `t - 1`,
comparing words lexicographically entry by entry. The indices of the
selected words are recorded, and finally their number and their frames
are written. With `m` words of total length `N`, this takes
`O(m² · N)` steps, so cubic time in the length of the input. Every value
the program produces is at most the length of the input plus its
largest entry, so word-length exponent `1` suffices.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_canonical :
    ∃ (A : Algorithm) (c a : ℕ), ∀ (α : Type) [Encode α] [DecidableEq α] (l : List α),
      A.Computes c (l.map encode) l.toFinset (((encode (l.map encode)).length + 1) ^ a) := by
  obtain ⟨p, e, c, a, h⟩ := exists_program_canonical_old
  refine ⟨⟨p, e⟩, c, a, fun α _ _ l => ?_⟩
  rw [← finsetOf_list]
  exact computes_of_poly rfl (h α l)

end Lax185574Proofs.CanonicalForm
