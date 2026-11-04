import Lax185574Proofs.Words.Select
import Lax185574Proofs.Words.TreeWord

/-!
Appending the canonical form of a list of words to a buffer.

After `collect` (`Lax185574Proofs.Words.Select`), the command `bufAll`
appends the number of distinct words and their frames, in increasing
order, to the array `b` at the pointer `bp`. It is `emitAll` of
`Lax185574Proofs.CanonicalForm` with the output tape replaced by the
buffer, so that the result can be read again.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding

/-- The buffer `b` holds `L` followed by the rest of its original
contents `O`, and `bp` points after `L`. -/
def BufAt (O L : List ℕ) (τ : Env) : Prop :=
  τ.vars "bp" = L.length ∧ τ.arrs "b" = L ++ O.drop L.length

/-- Append one entry of word `ow` to the buffer. -/
def bufEntry : Com :=
  .seq (.store "b" (.var "bp") (.get "a" (.add (.var "pa") (.var "k"))))
    (.seq (.assign "bp" (.add (.var "bp") (.lit 1))) (.assign "k" (.add (.var "k") (.lit 1))))

/-- Append the frame of word `ow` to the buffer. -/
def bufWord : Com :=
  .seq (.assign "pa" (.get "st" (.var "ow"))) (.seq (.assign "la" (.get "ln" (.var "ow")))
    (.seq (.store "b" (.var "bp") (.var "la")) (.seq (.assign "bp" (.add (.var "bp") (.lit 1)))
      (.seq (.assign "k" (.lit 0)) (.while (.lt (.var "k") (.var "la")) bufEntry)))))

theorem bufWord_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) {i : ℕ} (hi : σ.vars "ow" = i) (hil : i < ws.length)
    {O L : List ℕ} (hbuf : BufAt O L σ) (hfit : L.length + 1 + ws[i].length ≤ O.length)
    (hB : L.length + 1 + ws[i].length < B) :
    ∃ σ', Run B bufWord σ σ' (18 * total ws + 20) ∧
      BufAt O (L ++ (ws[i].length :: ws[i])) σ' ∧ σ'.arrs "a" = σ.arrs "a" ∧
      σ'.arrs "st" = σ.arrs "st" ∧ σ'.arrs "ln" = σ.arrs "ln" := by
  have hoi := off_add_le hil
  have hlen := hb.len
  generalize hu : ws[i] = u at hoi hfit hB
  have hea : ∀ k (h : k < u.length), (σ.arrs "a")[off ws i + k]? = some u[k] := by
    subst hu; exact hw.a i hil
  have hent : ∀ x ∈ u, x < B := by subst hu; exact hb.ent _ (List.getElem_mem hil)
  have hln : (σ.arrs "ln")[i]? = some u.length := by subst hu; exact hw.ln i hil
  obtain ⟨hbp, hba⟩ := hbuf
  have hbl : (σ.arrs "b").length = O.length := by rw [hba]; simp; omega
  set σ0 : Env := ((((σ.setVar "pa" (off ws i)).setVar "la" u.length).setArr "b" L.length
    u.length).setVar "bp" (L.length + 1)).setVar "k" 0 with hσ0
  let I : Env → Prop := fun τ => τ.vars "pa" = off ws i ∧ τ.vars "la" = u.length ∧
    τ.vars "k" ≤ u.length ∧ τ.arrs "a" = σ.arrs "a" ∧ τ.arrs "st" = σ.arrs "st" ∧
    τ.arrs "ln" = σ.arrs "ln" ∧ BufAt O (L ++ (u.length :: u.take (τ.vars "k"))) τ
  obtain ⟨σ', hloop, ⟨hpa, hla, hkle, ha, hst, hln', hbuf'⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "k") (.var "la")) (c := bufEntry) I
      (fun τ => u.length - τ.vars "k") 14
      (fun τ ⟨_, hla, hkle, _⟩ => evalB_condLt_vars (by omega) (by rw [hla]; omega))
      (by
        rintro τ ⟨hpa, hla, hkle, ha, hst, hln, hbp, hba⟩ hc
        have hk : τ.vars "k" < u.length := by
          have := lt_of_condLt_true hc; rwa [hla] at this
        have hget : (τ.arrs "a")[off ws i + τ.vars "k"]? = some u[τ.vars "k"] := by
          rw [ha]; exact hea _ hk
        have hlk : (L ++ (u.length :: u.take (τ.vars "k"))).length = L.length + 1 + τ.vars "k" := by
          simp; omega
        set τ' := ((τ.setArr "b" (L.length + 1 + τ.vars "k") u[τ.vars "k"]).setVar "bp"
          (L.length + 1 + τ.vars "k" + 1)).setVar "k" (τ.vars "k" + 1) with hτ'
        have hr : Run B bufEntry τ τ' 14 := by
          unfold bufEntry
          refine (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.assign ?_) (Run.assign ?_))).mono
            (by simp)
          · simp [hbp, hlk]; omega
          · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, hpa]
            exact ⟨_, ⟨_, _, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by simp only [Bop.apply_add]; omega⟩,
              hget, hent _ (List.getElem_mem hk)⟩
          · rw [hba]; simp; omega
          · simp [hbp, hlk]; omega
          · simp; omega
        refine ⟨τ', hr, ⟨by simp [hτ', hpa], by simp [hτ', hla], by simp [hτ']; omega,
          by simp [hτ', ha], by simp [hτ', hst], by simp [hτ', hln], ?_, ?_⟩, by simp [hτ']; omega⟩
        · simp only [hτ', vars_setVar, if_true, show ("bp" : String) = "k" ↔ False by decide,
            if_false, List.length_append, List.length_cons, List.length_take]
          omega
        · simp only [hτ', vars_setVar, if_true, arrs_setVar, arrs_setArr]
          rw [hba, ← hlk, set_prefix (by simp; omega), List.take_add_one, List.getElem?_eq_getElem hk]
          simp; omega)
      (show I σ0 by
        refine ⟨by simp [hσ0], by simp [hσ0], by simp [hσ0], by simp [hσ0], by simp [hσ0],
          by simp [hσ0], by simp [hσ0], ?_⟩
        simp only [hσ0, arrs_setVar, arrs_setArr, if_true, vars_setVar, List.take_zero]
        rw [hba, set_prefix (by omega)]
        simp)
  have hku : σ'.vars "k" = u.length := by
    have := le_of_condLt_false hfalse; rw [hla] at this; omega
  refine ⟨σ', ?_, by rw [hku, List.take_length] at hbuf'; exact hbuf', ha, hst, hln'⟩
  unfold bufWord
  refine (Run.seq (Run.assign (v := off ws i) ?_) (Run.seq (Run.assign (v := u.length) ?_)
    (Run.seq (Run.store (idx := L.length) (v := u.length) ?_ ?_ ?_)
      (Run.seq (Run.assign (v := L.length + 1) ?_) (Run.seq (Run.assign (v := 0) ?_) hloop))))).mono ?_
  · simp only [evalB_get_iff, evalB_var_iff, hi]
    exact ⟨i, ⟨rfl, by omega⟩, hw.st i hil, by omega⟩
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    exact ⟨i, ⟨by simp [hi], by simp [hi]; omega⟩, hln, by omega⟩
  · simp [hbp]; omega
  · simp; omega
  · simp [hbl]; omega
  · simp [hbp]; omega
  · simp; omega
  · simp; omega

/-- Append the next recorded word. -/
def bufBody : Com :=
  .seq (.assign "ow" (.get "ord" (.var "t")))
    (.seq bufWord (.assign "t" (.add (.var "t") (.lit 1))))

/-- Append the number of recorded words, then the words. -/
def bufAll : Com :=
  .seq (.store "b" (.var "bp") (.var "cnt")) (.seq (.assign "bp" (.add (.var "bp") (.lit 1)))
    (.seq (.assign "t" (.lit 0)) (.while (.lt (.var "t") (.var "cnt")) bufBody)))

theorem frames_take_succ'' {L : List (List ℕ)} {t : ℕ} (h : t < L.length) :
    frames (L.take (t + 1)) = frames (L.take t) ++ (L[t].length :: L[t]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [frames, List.map_append, List.flatten_append, Option.toList_some, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- **Appending the canonical form.** After `collect`, `bufAll` appends
the word of the sorted distinct words to the buffer. -/
theorem bufAll_run {B : ℕ} {ws : List (List ℕ)} (hb : WordsBound B ws) {σ : Env}
    (hw : WordsAt ws σ) (hcnt : σ.vars "cnt" = (sortedDistinct ws).length)
    (hol : ws.length ≤ (σ.arrs "ord").length)
    (hord : ∀ s < (sortedDistinct ws).length, (σ.arrs "ord").getD s 0 < ws.length ∧
        wd ws ((σ.arrs "ord").getD s 0) = (sortedDistinct ws).getD s [])
    {O L : List ℕ} (hbuf : BufAt O L σ) (hfit : L.length + (toWord ws).length ≤ O.length)
    (hB : L.length + (toWord ws).length < B) :
    ∃ σ', Run B bufAll σ σ' ((18 * total ws + 34) * ws.length + 16) ∧
      BufAt O (L ++ toWord (sortedDistinct ws)) σ' ∧ WordsAt ws σ' := by
  have hlen := hb.len
  have hLle := length_sortedDistinct_le ws
  have htle := total_sortedDistinct_le ws
  have hlw := length_toWord_words ws
  have hlw' := length_toWord_words (sortedDistinct ws)
  set S := sortedDistinct ws with hS
  obtain ⟨hbp, hba⟩ := hbuf
  have hbl : (σ.arrs "b").length = O.length := by rw [hba]; simp; omega
  let I : Env → Prop := fun τ => τ.vars "cnt" = S.length ∧ τ.vars "t" ≤ S.length ∧
    WordsAt ws τ ∧ τ.arrs "ord" = σ.arrs "ord" ∧
    BufAt O (L ++ (S.length :: frames (S.take (τ.vars "t")))) τ
  have hfr_le : ∀ t, (frames (S.take t)).length ≤ S.length + total S := by
    intro t
    rw [← length_frames]
    exact (List.IsPrefix.length_le (by
      conv_rhs => rw [← List.take_append_drop t S, frames_append]
      exact List.prefix_append _ _))
  set σ0 : Env := ((σ.setArr "b" L.length S.length).setVar "bp" (L.length + 1)).setVar "t" 0 with hσ0
  obtain ⟨σ', hloop, ⟨hc', ht', hw', -, hbuf'⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "t") (.var "cnt")) (c := bufBody) I
      (fun τ => S.length - τ.vars "t") (18 * total ws + 27)
      (fun τ hI => evalB_condLt_vars (by have := hI.2.1; omega) (by rw [hI.1]; omega))
      (by
        rintro τ ⟨hc, ht, hwτ, hoτ, hbτ⟩ hcond
        have htl : τ.vars "t" < S.length := by
          have := lt_of_condLt_true hcond; rwa [hc] at this
        obtain ⟨hol', hwo⟩ := hord _ htl
        set o := (σ.arrs "ord").getD (τ.vars "t") 0 with ho
        have hget : (τ.arrs "ord")[τ.vars "t"]? = some o := by
          rw [hoτ, ho, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
        set τ1 := τ.setVar "ow" o with hτ1
        have hlo := length_wd_le ws o
        rw [wd_eq hol'] at hlo hwo
        rw [List.getD_eq_getElem _ _ htl] at hwo
        have hft := frames_take_succ'' htl
        have hfl1 := hfr_le (τ.vars "t" + 1)
        rw [hft] at hfl1
        simp only [List.length_append, List.length_cons] at hfl1
        obtain ⟨τ2, hr2, hbuf2, ha2, hst2, hln2⟩ := bufWord_run (σ := τ1) (i := o)
          (hwτ.of_arrs (by simp [hτ1]) (by simp [hτ1]) (by simp [hτ1])) hb (by simp [hτ1]) hol'
          (O := O) (L := L ++ (S.length :: frames (S.take (τ.vars "t"))))
          (by obtain ⟨h1, h2⟩ := hbτ; exact ⟨by simp [hτ1, h1], by simp [hτ1, h2]⟩)
          (by rw [hwo]; simp; omega) (by rw [hwo]; simp; omega)
        have hfr : ∀ y, y ∉ bufWord.wvars → τ2.vars y = τ1.vars y := fun y hy => hr2.frame_var y hy
        have hfa : ∀ b, b ∉ bufWord.warrs → τ2.arrs b = τ1.arrs b := fun b hb => hr2.frame_arr b hb
        have ht2 : τ2.vars "t" = τ.vars "t" := by rw [hfr "t" (by decide)]; simp [hτ1]
        have hc2 : τ2.vars "cnt" = S.length := by rw [hfr "cnt" (by decide)]; simp [hτ1, hc]
        refine ⟨τ2.setVar "t" (τ.vars "t" + 1), ?_, ⟨by simp [hc2], by simp; omega,
          hwτ.of_arrs (by simp [ha2, hτ1]) (by simp [hst2, hτ1]) (by simp [hln2, hτ1]),
          by simp [hfa "ord" (by decide), hτ1, hoτ], ?_⟩, by simp; omega⟩
        · unfold bufBody
          refine (Run.seq (Run.assign (v := o) ?_) (Run.seq hr2 (Run.assign (by simp [ht2]; omega)))).mono
            (by simp; omega)
          simp only [evalB_get_iff, evalB_var_iff]
          exact ⟨τ.vars "t", ⟨rfl, by omega⟩, hget, by omega⟩
        · obtain ⟨h1, h2⟩ := hbuf2
          rw [hwo] at h1 h2
          refine ⟨by simp [h1, hft], ?_⟩
          simp only [arrs_setVar, h2, vars_setVar, if_true, hft]
          simp)
      (show I σ0 by
        refine ⟨by simp [hσ0, hcnt], by simp [hσ0], hw.of_arrs (by simp [hσ0]) (by simp [hσ0])
          (by simp [hσ0]), by simp [hσ0], by simp [hσ0, frames], ?_⟩
        simp only [hσ0, arrs_setVar, arrs_setArr, if_true, vars_setVar, List.take_zero]
        rw [hba, set_prefix (by omega)]
        simp [frames])
  have htL : σ'.vars "t" = S.length := by
    have := le_of_condLt_false hfalse; rw [hc'] at this; omega
  refine ⟨σ', ?_, ?_, hw'⟩
  · unfold bufAll
    refine (Run.seq (Run.store (idx := L.length) (v := S.length) (by simp [hbp]; omega)
      (by simp [hcnt]; omega) (by omega)) (Run.seq (Run.assign (v := L.length + 1)
        (by simp [hbp]; omega)) (Run.seq (Run.assign (v := 0) (by simp; omega)) hloop))).mono ?_
    have : σ0.vars "t" = 0 := by simp [hσ0]
    rw [this]
    simp only [size_condLt, Expr.size, Nat.sub_zero]
    have := Nat.mul_le_mul (show 18 * total ws + 31 ≤ 18 * total ws + 34 by omega) hLle
    have h2 : 1 + 3 + (18 * total ws + 27) = 18 * total ws + 31 := by ring
    rw [h2]; omega
  · rw [htL, List.take_length] at hbuf'
    rw [toWord_words]; exact hbuf'

end Lax185574Proofs.Words
