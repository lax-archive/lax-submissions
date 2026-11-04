import Lax185574Proofs.Words.Emit
import Lax185574Proofs.Words.Computes
import Lax185574Proofs.Compose.GraphLength

/-!
Reversing a list of vertex sets.

The word of a list of sets of vertices is its length followed by one
block per set, where the block of a set with `d` elements is `d`
followed by `2d` numbers (`Compose.toWord_finset_fin`). The command
`revBlocks` reads the blocks into the arrays of
`Lax185574Proofs.Words.Read`, in the same layout as `readWords`, and
then writes them in the opposite order. Adapted from `readWords` and
`writeWord` of the word library.
-/

namespace Lax185574Proofs.Compose

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574.WordEncoding Lax185574Proofs.Words

/-! ### Reading the blocks -/

/-- Read one block: half its length into `d`, its length into `n`, its
start and length into `st` and `ln` at `i`, its entries into `a`. -/
def readBlock : Com :=
  .seq (.read "d") (.seq (.assign "n" (.add (.var "d") (.var "d")))
    (.seq (.store "st" (.var "i") (.var "p"))
      (.seq (.store "ln" (.var "i") (.var "n"))
        (.seq (.assign "j" (.lit 0)) (.seq readEntries (.assign "i" (.add (.var "i") (.lit 1))))))))

/-- Read the number of blocks into `m`, then the blocks. -/
def readBlocks : Com :=
  .seq (.read "m") (.seq (.assign "i" (.lit 0)) (.seq (.assign "p" (.lit 0))
    (.while (.lt (.var "i") (.var "m")) readBlock)))

/-- The invariant of the loop of `readBlocks`: `i` blocks have been
read. -/
def BlockInv (ws : List (List ℕ)) (oa ost oln rest : List ℕ) (τ : Env) : Prop :=
  ∃ i ≤ ws.length, τ.vars "i" = i ∧ τ.vars "m" = ws.length ∧ τ.vars "p" = off ws i ∧
    τ.inp = blocksWord (ws.drop i) ++ rest ∧
    τ.arrs "a" = (ws.take i).flatten ++ oa.drop (off ws i) ∧
    τ.arrs "st" = (List.range i).map (off ws) ++ ost.drop i ∧
    τ.arrs "ln" = (ws.take i).map List.length ++ oln.drop i

theorem total_le_blocksWord (ws : List (List ℕ)) :
    ws.length + total ws ≤ (blocksWord ws).length := by
  induction ws with
  | nil => simp [total, blocksWord]
  | cons u ws ih =>
      rw [blocksWord_cons, List.length_append]
      simp only [total, List.flatten_cons, List.length_append, List.length_cons, blk] at ih ⊢
      omega

theorem readBlock_step {B : ℕ} {ws : List (List ℕ)} {oa ost oln rest : List ℕ}
    (hev : EvenBlocks ws)
    (hoa : total ws ≤ oa.length) (host : ws.length ≤ ost.length) (holn : ws.length ≤ oln.length)
    (hB : (blocksWord ws).length < B) (hv : ∀ u ∈ ws, ∀ v ∈ u, v < B)
    {τ : Env} (hI : BlockInv ws oa ost oln rest τ)
    (hc : (Cond.lt (.var "i") (.var "m")).evalB B τ = some true) :
    ∃ τ' K, Run B readBlock τ τ' K ∧ BlockInv ws oa ost oln rest τ' ∧
      1 + (Cond.lt (.var "i") (.var "m")).size + K +
        (25 * (ws.length - τ'.vars "i") + 16 * (total ws - τ'.vars "p")) ≤
        25 * (ws.length - τ.vars "i") + 16 * (total ws - τ.vars "p") := by
  obtain ⟨i, hile, hi, hm, hp, hinp, ha, hst, hln⟩ := hI
  have hilt : i < ws.length := by
    have := lt_of_condLt_true hc; rw [hi, hm] at this; exact this
  have hlenB := total_le_blocksWord ws
  have hofu := off_add_le hilt
  have hoff : off ws i = ((ws.take i).flatten).length := rfl
  have hdrop := blocksWord_drop hilt
  have hev' : ws[i].length % 2 = 0 := hev _ (List.getElem_mem _)
  have hu' : ∀ v ∈ ws[i], v < B := hv _ (List.getElem_mem _)
  have hts := take_succ_flatten hilt
  have hos := off_succ hilt
  have htl : (ws.take (i + 1)).map List.length = (ws.take i).map List.length ++ [ws[i].length] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hilt, List.map_append]; rfl
  generalize hu : ws[i] = u at *
  have hinp' : τ.inp = u.length / 2 :: (u ++ (blocksWord (ws.drop (i + 1)) ++ rest)) := by
    rw [hinp, hdrop]; simp [blk]
  have hlst : ((List.range i).map (off ws)).length = i := by simp
  have hlln : ((ws.take i).map List.length).length = i := by simp; omega
  have hdd : u.length / 2 + u.length / 2 = u.length := by omega
  set τ4 : Env := ((({ τ.setVar "d" (u.length / 2) with
      inp := u ++ (blocksWord (ws.drop (i + 1)) ++ rest) }.setVar "n" u.length).setArr
      "st" i (off ws i)).setArr "ln" i u.length).setVar "j" 0 with hτ4
  have hE : EntriesInv (ws.take i).flatten oa u (blocksWord (ws.drop (i + 1)) ++ rest) τ4 := by
    refine ⟨0, by omega, by simp [hτ4], by simp [hτ4], ?_, by simp [hτ4], ?_⟩
    · simp [hτ4, hp, off]
    · simp [hτ4, ha, off]
  obtain ⟨τ5, hr5, hp5, hj5, hinp5, ha5⟩ := readEntries_run (B := B)
    (by rw [← hoff]; omega) (by rw [← hoff]; omega) hu' hE (by simp [hτ4])
  have hr : Run B readBlock τ (τ5.setVar "i" (i + 1)) (21 + 16 * u.length) := by
    unfold readBlock
    refine (Run.seq (Run.read hinp') (Run.seq (Run.assign ?_) (Run.seq (Run.store ?_ ?_ ?_)
      (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.assign ?_) (Run.seq hr5 (Run.assign ?_))))))).mono
      (by simp; omega)
    · simp; omega
    · simp [hi]; omega
    · simp [hp]; omega
    · simp [hst]; omega
    · simp [hi]; omega
    · simp; omega
    · simp [hln]; omega
    · simp; omega
    · have hi5 : τ5.vars "i" = i := by
        rw [hr5.frame_var "i" (by decide)]; simp [hτ4, hi]
      simp [hi5]; omega
  have hfr : ∀ y, y ∉ readEntries.wvars → τ5.vars y = τ4.vars y := fun y hy => hr5.frame_var y hy
  have hfa : ∀ b, b ∉ readEntries.warrs → τ5.arrs b = τ4.arrs b := fun b hb => hr5.frame_arr b hb
  refine ⟨_, _, hr, ⟨i + 1, by omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hfr "m" (by decide), hτ4, hm]
  · simp [hp5, hos, hoff]
  · simp [hinp5]
  · simp only [arrs_setVar, ha5, hts, hos, hoff, List.append_assoc]
  · simp only [arrs_setVar, hfa "st" (by decide), hτ4, arrs_setArr, if_true]
    simp only [show ("st" : String) = "ln" ↔ False by decide, if_false, hst]
    rw [set_prefix' hlst (by omega), List.range_succ, List.map_append]
    simp
  · simp only [arrs_setVar, hfa "ln" (by decide), hτ4, arrs_setArr, if_true]
    simp only [show ("ln" : String) = "st" ↔ False by decide, if_false, hln]
    rw [set_prefix' hlln (by omega), htl]
  · simp only [vars_setVar, if_true, hp5]
    simp only [show ("p" : String) = "i" ↔ False by decide, if_false]
    rw [hi, hp, ← hoff]
    simp
    omega

theorem readBlocks_run {B : ℕ} {ws : List (List ℕ)} {rest : List ℕ} {σ : Env}
    (hev : EvenBlocks ws)
    (hinp : σ.inp = ws.length :: (blocksWord ws ++ rest))
    (hoa : total ws ≤ (σ.arrs "a").length) (host : ws.length ≤ (σ.arrs "st").length)
    (holn : ws.length ≤ (σ.arrs "ln").length)
    (hB : (blocksWord ws).length + 1 < B) (hv : ∀ u ∈ ws, ∀ v ∈ u, v < B) :
    ∃ σ', Run B readBlocks σ σ' (25 * (blocksWord ws).length + 9) ∧
      σ'.vars "m" = ws.length ∧ σ'.inp = rest ∧ σ'.out = σ.out ∧ WordsAt ws σ' := by
  have hlenB := total_le_blocksWord ws
  set σ0 : Env := ({ σ.setVar "m" ws.length with inp := blocksWord ws ++ rest }.setVar "i" 0).setVar
    "p" 0 with hσ0
  have hI0 : BlockInv ws (σ.arrs "a") (σ.arrs "st") (σ.arrs "ln") rest σ0 := by
    refine ⟨0, by omega, by simp [hσ0], by simp [hσ0], by simp [hσ0, off], by simp [hσ0], ?_, ?_, ?_⟩
    · simp [hσ0, off]
    · simp [hσ0]
    · simp [hσ0]
  obtain ⟨σ', K, hrun, ⟨i, hile, hi, hm, hp, hinp2, ha, hst, hln⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "i") (.var "m")) (c := readBlock)
      (BlockInv ws (σ.arrs "a") (σ.arrs "st") (σ.arrs "ln") rest)
      (fun τ => 25 * (ws.length - τ.vars "i") + 16 * (total ws - τ.vars "p"))
      (fun τ ⟨i, hile, hi, hm, _⟩ => evalB_condLt_vars (by rw [hi]; omega) (by rw [hm]; omega))
      (fun τ hI hc => readBlock_step hev hoa host holn (by omega) hv hI hc) hI0
  have hiw : i = ws.length := by
    have := le_of_condLt_false hfalse; rw [hi, hm] at this; omega
  subst hiw
  have hr : Run B readBlocks σ σ' (25 * (blocksWord ws).length + 9) := by
    refine (Run.seq (Run.read hinp) (Run.seq (Run.assign (v := 0) (by simp; omega))
      (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun))).mono ?_
    have : σ0.vars "i" = 0 := by simp [hσ0]
    have : σ0.vars "p" = 0 := by simp [hσ0]
    simp only [Cond.size, Expr.size] at hK
    simp only [Expr.size]
    omega
  refine ⟨σ', hr, hm, by simpa [blocksWord] using hinp2, ?_, ?_⟩
  · have := hr.out_eq (by decide)
    exact this
  · refine wordsAt_of_arrs (oa := (σ.arrs "a").drop (total ws))
      (oln := (σ.arrs "ln").drop ws.length) ?_ hst ?_
    · rw [ha, List.take_length, off_length]; rfl
    · rw [hln, List.take_length]

/-! ### Writing a block -/

/-- Write block `ow`: half its length, then its entries. -/
def writeBlock : Com :=
  .seq (.assign "pa" (.get "st" (.var "ow"))) (.seq (.assign "la" (.get "ln" (.var "ow")))
    (.seq (.write (.div (.var "la") (.lit 2))) (.seq (.assign "k" (.lit 0))
      (.while (.lt (.var "k") (.var "la")) writeEntry))))

theorem writeBlock_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) {i : ℕ} (hi : σ.vars "ow" = i) (hil : i < ws.length) :
    ∃ σ', Run B writeBlock σ σ' (13 * ws[i].length + 16) ∧
      σ'.out = σ.out ++ blk ws[i] ∧ ∀ y, y ∉ writeBlock.wvars → σ'.vars y = σ.vars y := by
  have hoi := off_add_le hil
  have hlen := hb.len
  have h3 := hb.three
  generalize hu : ws[i] = u at hoi
  have hea : ∀ k (h : k < u.length), (σ.arrs "a")[off ws i + k]? = some u[k] := by
    subst hu; exact hw.a i hil
  have hent : ∀ x ∈ u, x < B := by subst hu; exact hb.ent _ (List.getElem_mem hil)
  have hln : (σ.arrs "ln")[i]? = some u.length := by subst hu; exact hw.ln i hil
  set σ0 : Env := { ((σ.setVar "pa" (off ws i)).setVar "la" u.length) with
    out := σ.out ++ [u.length / 2] } with hσ0
  let I : Env → Prop := fun τ => τ.vars "pa" = off ws i ∧ τ.vars "la" = u.length ∧
    τ.vars "k" ≤ u.length ∧ τ.arrs "a" = σ.arrs "a" ∧
    τ.out = σ.out ++ (u.length / 2 :: u.take (τ.vars "k"))
  obtain ⟨σ', hloop, ⟨hpa, hla, hkle, ha, hout⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "k") (.var "la")) (c := writeEntry) I
      (fun τ => u.length - τ.vars "k") 9
      (fun τ ⟨_, hla, hkle, _⟩ => evalB_condLt_vars (by omega) (by rw [hla]; omega))
      (by
        rintro τ ⟨hpa, hla, hkle, ha, hout⟩ hc
        have hk : τ.vars "k" < u.length := by
          have := lt_of_condLt_true hc; rwa [hla] at this
        have hget : (τ.arrs "a")[off ws i + τ.vars "k"]? = some u[τ.vars "k"] := by
          rw [ha]; exact hea _ hk
        refine ⟨_, Run.seq (Run.write (v := u[τ.vars "k"]) ?_) (Run.assign (v := τ.vars "k" + 1) ?_),
          ⟨by simp [hpa], by simp [hla], by simp; omega, by simp [ha], ?_⟩, by simp; omega⟩
        · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, hpa]
          exact ⟨_, ⟨_, _, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by simp only [Bop.apply_add]; omega⟩,
            hget,
            hent _ (List.getElem_mem hk)⟩
        · simp; omega
        · simp only [vars_setVar, if_true]
          rw [hout, List.take_add_one, List.getElem?_eq_getElem hk]
          simp)
      (show I (σ0.setVar "k" 0) by
        refine ⟨by simp [hσ0], by simp [hσ0], by simp, by simp [hσ0], by simp [hσ0]⟩)
  have hku : σ'.vars "k" = u.length := by
    have := le_of_condLt_false hfalse; rw [hla] at this; omega
  have hr : Run B writeBlock σ σ' (13 * u.length + 16) := by
    unfold writeBlock
    refine (Run.seq (Run.assign (v := off ws i) ?_) (Run.seq (Run.assign (v := u.length) ?_)
      (Run.seq (Run.write (v := u.length / 2) ?_) (Run.seq (Run.assign (v := 0) ?_) hloop)))).mono ?_
    · simp only [evalB_get_iff, evalB_var_iff, hi]
      exact ⟨i, ⟨rfl, by omega⟩, hw.st i hil, by omega⟩
    · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
      exact ⟨i, ⟨by simp [hi], by simp [hi]; omega⟩, hln, by omega⟩
    · simp; omega
    · simp; omega
    · simp; omega
  refine ⟨σ', hr, by rw [hout, hku, List.take_length]; rfl, fun y hy => hr.frame_var y hy⟩

/-! ### The program -/

/-- Write the blocks in reverse order, counting with `r`. -/
def writeRev : Com :=
  .seq (.write (.var "m")) (.seq (.assign "r" (.lit 0))
    (.while (.lt (.var "r") (.var "m"))
      (.seq (.assign "ow" (.sub (.sub (.var "m") (.lit 1)) (.var "r")))
        (.seq writeBlock (.assign "r" (.add (.var "r") (.lit 1)))))))

def revBlocks : Com := .seq readBlocks writeRev

def revLayout : Layout where
  scalars := ["m", "i", "p", "d", "n", "j", "v", "pa", "la", "k", "r", "ow"]
  arrays := ["a", "st", "ln"]
  temps := 4

theorem revBlocks_ok : Com.Ok revLayout revBlocks := by
  simp [revBlocks, readBlocks, readBlock, readEntries, readEntry, writeRev, writeBlock, writeEntry,
    revLayout, Com.Ok, Cond.Ok, Expr.Ok, condExpr]

theorem blocksWord_reverse_take_succ {ws : List (List ℕ)} {r : ℕ} (hr : r < ws.length) :
    blocksWord (ws.reverse.take (r + 1)) =
      blocksWord (ws.reverse.take r) ++ blk ws[ws.length - 1 - r] := by
  have hr' : r < ws.reverse.length := by simpa using hr
  rw [List.take_add_one, List.getElem?_eq_getElem hr', Option.toList_some, blocksWord_append,
    List.getElem_reverse]
  simp [blocksWord]

theorem writeRev_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) (hm : σ.vars "m" = ws.length) :
    ∃ σ', Run B writeRev σ σ' (17 * (total ws) + 40 * ws.length + 10) ∧
      σ'.out = σ.out ++ ws.length :: blocksWord ws.reverse := by
  have hlen := hb.len
  set M := ws.length
  let I : Env → Prop := fun τ => τ.vars "m" = M ∧ τ.vars "r" ≤ M ∧ WordsAt ws τ ∧
    τ.out = σ.out ++ M :: blocksWord (ws.reverse.take (τ.vars "r"))
  have htd : ∀ r (hr : r < M), total (ws.reverse.drop r) =
      ws[M - 1 - r].length + total (ws.reverse.drop (r + 1)) := by
    intro r hr
    have hr' : r < ws.reverse.length := by simpa using hr
    rw [List.drop_eq_getElem_cons hr', List.getElem_reverse]
    simp [total, M]
  obtain ⟨σ', K, hloop, ⟨hm', hrM, hw', hout⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "r") (.var "m"))
      (c := .seq (.assign "ow" (.sub (.sub (.var "m") (.lit 1)) (.var "r")))
        (.seq writeBlock (.assign "r" (.add (.var "r") (.lit 1)))))
      I (fun τ => 17 * total (ws.reverse.drop (τ.vars "r")) + 40 * (M - τ.vars "r"))
      (fun τ ⟨hm, hr, _⟩ => evalB_condLt_vars (by omega) (by omega))
      (by
        rintro τ ⟨hm, hr, hwτ, hout⟩ hc
        have hlt : τ.vars "r" < M := by have := lt_of_condLt_true hc; rwa [hm] at this
        set r := τ.vars "r"
        have hil : M - 1 - r < M := by omega
        set τ1 := τ.setVar "ow" (M - 1 - r)
        have r1 : Run B (.assign "ow" (.sub (.sub (.var "m") (.lit 1)) (.var "r"))) τ τ1 6 := by
          refine (Run.assign ?_).mono (by simp)
          simp [hm]; omega
        obtain ⟨τ2, r2, hout2, hfr2⟩ := writeBlock_run (σ := τ1) (hwτ.of_arrs rfl rfl rfl) hb
          (i := M - 1 - r) (by simp [τ1]) hil
        have hr2 : τ2.vars "r" = r := by rw [hfr2 "r" (by decide)]; simp [τ1, r]
        have hm2 : τ2.vars "m" = M := by rw [hfr2 "m" (by decide)]; simp [τ1, hm]
        have r3 : Run B (.assign "r" (.add (.var "r") (.lit 1))) τ2 (τ2.setVar "r" (r + 1)) 4 := by
          refine (Run.assign ?_).mono (by simp)
          simp [hr2]; omega
        have hwa : WordsAt ws τ2 := by
          have h2 := r2.frame_arr
          exact hwτ.of_arrs (by rw [h2 "a" (by decide)]; rfl) (by rw [h2 "st" (by decide)]; rfl)
            (by rw [h2 "ln" (by decide)]; rfl)
        refine ⟨_, _, r1.seq (r2.seq r3), ⟨by simp [hm2], by simp; omega, hwa.of_arrs rfl rfl rfl, ?_⟩, ?_⟩
        · simp only [vars_setVar, if_true, out_setVar]
          rw [hout2, blocksWord_reverse_take_succ hlt]
          simp [τ1, hout, M]
        · simp only [vars_setVar, if_true, Cond.size, Expr.size]
          have := htd r hlt
          omega)
      (show I (({ σ with out := σ.out ++ [M] }).setVar "r" 0) by
        refine ⟨by simp [hm], by simp, hw.of_arrs rfl rfl rfl, by simp [blocksWord]⟩)
  have hrM' : σ'.vars "r" = M := by have := le_of_condLt_false hfalse; rw [hm'] at this; omega
  refine ⟨σ', ?_, by rw [hout, hrM', List.take_of_length_le (by simp [M])]⟩
  unfold writeRev
  refine (Run.seq (Run.write (v := M) ?_) (Run.seq (Run.assign (v := 0) ?_) hloop)).mono ?_
  · simp [hm]; omega
  · simp; omega
  · simp only [vars_setVar, if_true, Cond.size, Expr.size, List.drop_zero] at hK
    have : total ws.reverse = total ws := by simp [total]
    simp only [Expr.size]
    omega

/-- **Reversal.** The command `revBlocks` turns the blocks
`m, blk u₀, …, blk u_{m-1}` into `m, blk u_{m-1}, …, blk u₀`. -/
theorem revBlocks_run (ws : List (List ℕ)) (hev : EvenBlocks ws) (B : ℕ)
    (hB : (blocksWord ws).length + 3 < B) (hv : ∀ u ∈ ws, ∀ v ∈ u, v < B) :
    ∃ σ', Run B revBlocks
        (initEnv (fun a => if a = "a" then total ws else ws.length)
          (ws.length :: blocksWord ws)) σ'
        (65 * (blocksWord ws).length + 19) ∧
      σ'.out = ws.length :: blocksWord ws.reverse := by
  have hlenB := total_le_blocksWord ws
  obtain ⟨σ₁, r₁, hm₁, -, hout₁, hw₁⟩ := readBlocks_run (rest := [])
    (σ := initEnv (fun a => if a = "a" then total ws else ws.length) (ws.length :: blocksWord ws))
    hev (by simp [initEnv])
    (by simp [initEnv]) (by simp [initEnv]) (by simp [initEnv]) (by omega) hv
  obtain ⟨σ₂, r₂, hout₂⟩ := writeRev_run hw₁ ⟨by omega, hv, by omega⟩ hm₁
  refine ⟨σ₂, (r₁.seq r₂).mono (by omega), ?_⟩
  rw [hout₂, hout₁]; simp [initEnv]

theorem toWord_setList {n : ℕ} (l : List (Finset (Fin n))) :
    toWord l = l.length :: blocksWord (l.map setBlock) := by
  change l.length :: (l.map toWord).flatten = _
  simp only [blocksWord, List.map_map]
  congr 2
  exact List.map_congr_left fun S _ => toWord_finset_fin S

theorem evenBlocks_setList {n : ℕ} (l : List (Finset (Fin n))) : EvenBlocks (l.map setBlock) := by
  intro u hu
  simp only [List.mem_map] at hu
  obtain ⟨S, -, rfl⟩ := hu
  rw [setBlock_length]; omega

/-- **Reversing a list of vertex sets** on the word RAM, in linear
time. -/
theorem exists_program_reverse :
    ∃ (p : Lax808846.Ram.Program) (e c : ℕ), ∀ (n : ℕ) (l : List (Finset (Fin n))),
      Lax185574.Computing.Computes p e c l l.reverse (fun m => c * (m + 1)) := by
  refine ⟨compileProgram revLayout revBlocks, 1, bridgeConst revLayout 4 65, fun n l => ?_⟩
  have h := computes_of_run (a := l) (b := l.reverse) (A := 4) (e := 1) (K := 65) (d := 1)
    revBlocks_ok (by norm_num) le_rfl (by rw [toWord_setList]; simp) ?_
  · simpa using h
  set ws := l.map setBlock
  have hx : toWord l = ws.length :: blocksWord ws := by rw [toWord_setList]; simp [ws]
  have hy : toWord l.reverse = ws.length :: blocksWord ws.reverse := by
    rw [toWord_setList]; simp [ws, List.map_reverse]
  set B := valBound 4 1 (toWord l)
  have hBl : 4 * ((toWord l).length + maxEntry (toWord l) + 1) ≤ B := by
    simp only [B, valBound, pow_one]; omega
  have hlen : (toWord l).length = 1 + (blocksWord ws).length := by rw [hx]; simp; omega
  obtain ⟨σ', hr, hout⟩ := revBlocks_run ws (evenBlocks_setList l) B (by omega) (by
    intro u hu v hv
    have : v ∈ toWord l := by
      rw [hx]
      refine List.mem_cons_of_mem _ ?_
      simp only [blocksWord, List.mem_flatten, List.mem_map]
      exact ⟨blk u, ⟨u, hu, rfl⟩, List.mem_cons_of_mem _ hv⟩
    have := le_maxEntry this
    omega)
  refine ⟨fun a => if a = "a" then total ws else ws.length, σ', ?_, by rw [hout, hy]⟩
  rw [hx]
  refine hr.mono ?_
  simp only [List.length_cons, pow_one]
  omega

end Lax185574Proofs.Compose
