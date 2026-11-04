import Lax185574Proofs.ResolveRam.Glue.ClauseJ
import Lax185574Proofs.ResolveRam.Glue.CaseKit
import Lax185574Proofs.ResolveRam.Glue.PH3

/-!
Copying steps of the last round of the glue program of lem:resolve-lift.

The last round writes words of the library and a segment of the answer
of the switch to the buffer `OB` without their lengths.

* `feOU`: the last `ii` words of the library (`feOU_run`).
* `feHd`: the entries `2, 3, 4` of the library word with index
  `4 + nSG + nFA + nCO + ii` (`feHd_run`).
* `feAT`: the library word with index `2` (`feAT_run`).
* `feY pl dl`: the segment of the answer from `pl` without its last `dl`
  entries (`feY_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue

/-- The entries of the library from the start of word `lo` to the end. -/
theorem fe_seg_drop {ws : List (List ℕ)} {τ : Env} (h : WordsAt ws τ) (lo : ℕ) :
    seg (τ.arrs "a") (off ws lo) (total ws - off ws lo) = (ws.drop lo).flatten := by
  have h0 := seg_lib h
  simp only [seg, List.drop_zero] at h0
  simp only [seg]
  rw [← List.drop_take, h0,
    show ws.flatten = (ws.take lo).flatten ++ (ws.drop lo).flatten by
      rw [← List.flatten_append, List.take_append_drop],
    show off ws lo = (ws.take lo).flatten.length from rfl, List.drop_left]

/-- Entries `d, …, d + N - 1` of a library word. -/
theorem fe_seg_word {ws : List (List ℕ)} {τ : Env} (h : WordsAt ws τ) {i : ℕ} (hi : i < ws.length)
    (d N : ℕ) (hdN : d + N ≤ ws[i].length) :
    seg (τ.arrs "a") (off ws i + d) N = (ws[i].drop d).take N := by
  apply List.ext_getElem?
  intro j
  simp only [seg, List.getElem?_take, List.getElem?_drop]
  split_ifs with hj
  · rw [show off ws i + d + j = off ws i + (d + j) by omega, h.a i hi (d + j) (by omega),
      List.getElem?_eq_getElem (by omega)]
  · rfl

/-! ### The last words of the library -/

/-- Append the last `ii` words of the library, without their lengths. -/
def feOU : Com :=
  .ite (.eq (.var "ii") (.lit 0)) .skip
    (.seq (.assign "wa" (.get "st" (.sub (.var "m") (.var "ii"))))
      (.seq (.assign "wl" (.sub (.var "lt") (.var "wa"))) (cpSeg "a" "wa" "wl")))

theorem feOU_run {W i : ℕ} {ws : List (List ℕ)} {τ : Env} {pre : List ℕ} (hL : Lib ws τ)
    (hi : τ.vars "ii" = i) (hil : i ≤ ws.length) (hF : Filled "OB" "po" pre τ)
    (hlt : EnvLt (W + 1) τ) (harr : ArrW W τ) (hB : pre.length + total ws + ws.length + 1 ≤ W) :
    ∃ τ', Run (W + 1) feOU τ τ' (20 * total ws + 40) ∧
      Filled "OB" "po" (pre ++ (ws.drop (ws.length - i)).flatten) τ' ∧
      OFr τ τ' ["wa", "wl", "ci", "po"] := by
  have hw := hL.at_
  by_cases h0 : i = 0
  · subst h0
    have hc : (Cond.eq (.var "ii") (.lit 0)).evalB (W + 1) τ = some true := by
      rw [evalB_condEq (ev_var hi (by omega)) (evalB_lit (by omega))]; rfl
    refine ⟨τ, (Run.ite_true hc Run.skip).mono ?_, by simpa using hF, (OFr.refl τ).mono (by simp)⟩
    simp [Cond.size, Expr.size]
  have hc : (Cond.eq (.var "ii") (.lit 0)).evalB (W + 1) τ = some false := by
    rw [evalB_condEq (ev_var hi (by omega)) (evalB_lit (by omega))]
    simp [h0]
  set lo := ws.length - i
  have hlo : lo < ws.length := by omega
  have hoff : off ws lo + ws[lo].length ≤ total ws := off_add_le hlo
  have hst := hw.st lo hlo
  obtain ⟨τ1, r1, o1⟩ := asg_run (x := "wa") (B := W + 1) (σ := τ)
    (evalB_get (ev_sub (ev_var hL.m (by omega)) (ev_var hi (by omega)) (by omega)) hst (by omega))
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "wl") (B := W + 1) (σ := τ1)
    (ev_sub (ev_var (by rw [o1.vars "lt" (by decide), hL.lt]) (by omega)) (ev_var o1.self (by omega))
      (by omega))
  have hF2 : Filled "OB" "po" pre τ2 :=
    hF.congr (by rw [o2.vars "po" (by decide), o1.vars "po" (by decide)]) (by rw [o2.arrs, o1.arrs])
  have ha2 : τ2.arrs "a" = τ.arrs "a" := by rw [o2.arrs, o1.arrs]
  have hseg : seg (τ2.arrs "a") (off ws lo) (total ws - off ws lo) = (ws.drop lo).flatten := by
    rw [ha2]; exact fe_seg_drop hw lo
  have hval := lib_lt hw hlt
  obtain ⟨τ3, r3, F3, O3⟩ := cpSeg_ofr (W := W) (src := "a") (s := "wa") (l := "wl") (σ := τ2)
    (a := off ws lo) (N := total ws - off ws lo) (by decide)
    (by rw [o2.vars "wa" (by decide), o1.self]) o2.self (by decide) (by decide) (by decide) (by decide) hF2
    (by rw [ha2, harr "a"]; omega) (by rw [o2.arrs, o1.arrs, harr "OB"]; omega) (by omega) (by omega)
    (by
      rw [hseg]; intro v hv
      obtain ⟨w, hw', hv'⟩ := List.mem_flatten.1 hv
      exact hval w (List.mem_of_mem_drop hw') v hv')
  rw [hseg] at F3
  refine ⟨τ3, ?_, F3, ?_⟩
  · refine (Run.ite_false hc (Run.seq r1 (Run.seq r2 r3))).mono ?_
    simp only [Cond.size, Expr.size]; omega
  · refine ⟨fun y hy => ?_, fun b hb => ?_, ?_, ?_, ?_⟩
    · rw [O3.vars y (fun h => hy (by simp at h ⊢; tauto)), o2.vars y (fun h => hy (by simp [h])),
        o1.vars y (fun h => hy (by simp [h]))]
    · rw [O3.arrs b hb, o2.arrs, o1.arrs]
    · rw [O3.len, o2.arrs, o1.arrs]
    · rw [O3.out, o2.out, o1.out]
    · rw [O3.inp, o2.inp, o1.inp]

/-! ### The head of the tree of an item -/

/-- The index `4 + nSG + nFA + nCO + ii`. -/
def feIw : Expr := .add (.add (.add (.add (.lit 4) (.var "nSG")) (.var "nFA")) (.var "nCO")) (.var "ii")

/-- Append the entries `2, 3, 4` of the library word with index `feIw`. -/
def feHd : Com :=
  .seq (.assign "ow" feIw) (.seq (.assign "wa" (.add (.get "st" (.var "ow")) (.lit 2)))
    (.seq (.assign "wl" (.lit 3)) (cpSeg "a" "wa" "wl")))

theorem feHd_run {W a1 a2 a3 i iw : ℕ} {ws : List (List ℕ)} {τ : Env} {pre : List ℕ} (hL : Lib ws τ)
    (h1 : τ.vars "nSG" = a1) (h2 : τ.vars "nFA" = a2) (h3 : τ.vars "nCO" = a3) (hi : τ.vars "ii" = i)
    (hiw : 4 + a1 + a2 + a3 + i = iw) (hil : iw < ws.length) (h5 : 5 ≤ (ws.getD iw []).length)
    (hF : Filled "OB" "po" pre τ)
    (hlt : EnvLt (W + 1) τ) (harr : ArrW W τ) (hB : pre.length + total ws + ws.length + 4 ≤ W) :
    ∃ τ', Run (W + 1) feHd τ τ' 120 ∧
      Filled "OB" "po" (pre ++ ((ws.getD iw []).drop 2).take 3) τ' ∧
      OFr τ τ' ["ow", "wa", "wl", "ci", "po"] := by
  have hw := hL.at_
  have hg : ws.getD iw [] = ws[iw] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
  rw [hg] at h5 ⊢
  have hoff : off ws iw + ws[iw].length ≤ total ws := off_add_le hil
  have hst := hw.st iw hil
  have hev : feIw.evalB (W + 1) τ = some iw := by
    rw [← hiw]
    exact ev_add (ev_add (ev_add (ev_add (evalB_lit (by omega)) (ev_var h1 (by omega)) (by omega))
      (ev_var h2 (by omega)) (by omega)) (ev_var h3 (by omega)) (by omega)) (ev_var hi (by omega)) (by omega)
  obtain ⟨τ0, r0, o0⟩ := asg_run (x := "ow") (B := W + 1) (σ := τ) hev
  obtain ⟨τ1, r1, o1⟩ := asg_run (x := "wa") (B := W + 1) (σ := τ0)
    (ev_add (evalB_get (ev_var o0.self (by omega)) (by rw [o0.arrs]; exact hst) (by omega))
      (evalB_lit (n := 2) (by omega)) (by omega))
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "wl") (B := W + 1) (σ := τ1) (evalB_lit (n := 3) (by omega))
  have hF2 : Filled "OB" "po" pre τ2 :=
    hF.congr (by rw [o2.vars "po" (by decide), o1.vars "po" (by decide), o0.vars "po" (by decide)])
      (by rw [o2.arrs, o1.arrs, o0.arrs])
  have ha2 : τ2.arrs "a" = τ.arrs "a" := by rw [o2.arrs, o1.arrs, o0.arrs]
  have hseg : seg (τ2.arrs "a") (off ws iw + 2) 3 = (ws[iw].drop 2).take 3 := by
    rw [ha2]; exact fe_seg_word hw hil 2 3 (by omega)
  have hval := lib_lt hw hlt
  obtain ⟨τ3, r3, F3, O3⟩ := cpSeg_ofr (W := W) (src := "a") (s := "wa") (l := "wl") (σ := τ2)
    (a := off ws iw + 2) (N := 3) (by decide)
    (by rw [o2.vars "wa" (by decide), o1.self]) o2.self (by decide) (by decide) (by decide) (by decide) hF2
    (by rw [ha2, harr "a"]; omega) (by rw [o2.arrs, o1.arrs, o0.arrs, harr "OB"]; omega) (by omega)
    (by omega)
    (by
      rw [hseg]; intro v hv
      exact hval _ (List.getElem_mem hil) v (List.mem_of_mem_drop (List.mem_of_mem_take hv)))
  rw [hseg] at F3
  refine ⟨τ3, ?_, F3, ?_⟩
  · refine (Run.seq r0 (Run.seq r1 (Run.seq r2 r3))).mono ?_
    simp only [feIw, Expr.size]; omega
  · refine ⟨fun y hy => ?_, fun b hb => ?_, ?_, ?_, ?_⟩
    · rw [O3.vars y (fun h => hy (by simp at h ⊢; tauto)), o2.vars y (fun h => hy (by simp [h])),
        o1.vars y (fun h => hy (by simp [h])), o0.vars y (fun h => hy (by simp [h]))]
    · rw [O3.arrs b hb, o2.arrs, o1.arrs, o0.arrs]
    · rw [O3.len, o2.arrs, o1.arrs, o0.arrs]
    · rw [O3.out, o2.out, o1.out, o0.out]
    · rw [O3.inp, o2.inp, o1.inp, o0.inp]

/-! ### The answer on the atom words -/

/-- Append the library word with index `2`. -/
def feAT : Com := .seq (.assign "ow" (.lit 2)) (cpPart "ow" 0)

theorem feAT_run {W : ℕ} {ws : List (List ℕ)} {τ : Env} {pre : List ℕ} (hL : Lib ws τ)
    (h3 : 3 ≤ ws.length) (hF : Filled "OB" "po" pre τ)
    (hlt : EnvLt (W + 1) τ) (harr : ArrW W τ) (hB : pre.length + total ws + ws.length + 1 ≤ W) :
    ∃ τ', Run (W + 1) feAT τ τ' (20 * total ws + 30) ∧
      Filled "OB" "po" (pre ++ ws.getD 2 []) τ' ∧ OFr τ τ' ["ow", "wa", "wl", "ci", "po"] := by
  have hw := hL.at_
  have hg : ws.getD 2 [] = ws[2] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 2 < ws.length by omega)]
  rw [hg]
  have hle : ws[2].length ≤ total ws := len_le_total (by omega)
  obtain ⟨τ0, r0, o0⟩ := asg_run (x := "ow") (B := W + 1) (σ := τ) (evalB_lit (n := 2) (by omega))
  have hval := lib_lt hw hlt
  obtain ⟨τ1, r1, F1, O1⟩ := cpPart_run (W := W) (ix := "ow") (d := 0) (ws := ws) (i := 2) (σ := τ0)
    (hw.of_arrs (by rw [o0.arrs]) (by rw [o0.arrs]) (by rw [o0.arrs])) o0.self (by omega) (by decide)
    (by omega) (hF.congr (o0.vars "po" (by decide)) (by rw [o0.arrs])) (by rw [o0.arrs, harr "OB"])
    (by omega) (by omega) (hval _ (List.getElem_mem _)) (by rw [o0.arrs, harr "a"]; omega)
  simp only [List.drop_zero] at F1
  refine ⟨τ1, (Run.seq r0 r1).mono ?_, F1, ?_⟩
  · simp only [Expr.size]; omega
  · refine ⟨fun y hy => ?_, fun b hb => ?_, ?_, ?_, ?_⟩
    · rw [O1.vars y (fun h => hy (by simp at h ⊢; tauto)), o0.vars y (fun h => hy (by simp [h]))]
    · rw [O1.arrs b hb, o0.arrs]
    · rw [O1.len, o0.arrs]
    · rw [O1.out, o0.out]
    · rw [O1.inp, o0.inp]

/-! ### A segment of the answer -/

/-- Append the segment of the answer from `pl`, without its last `dl` entries. -/
def feY (pl dl : ℕ) : Com :=
  .seq (.assign "wa" (.lit pl)) (.seq (.assign "wl" (.sub (.var "bl") (.lit dl))) (cpSeg "y" "wa" "wl"))

theorem feY_run {W pl dl : ℕ} {b : List ℕ} {τ : Env} {pre : List ℕ}
    (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ) (hpd : pl ≤ dl) (hdl : dl ≤ b.length)
    (hF : Filled "OB" "po" pre τ) (hlt : EnvLt (W + 1) τ) (harr : ArrW W τ)
    (hB : pre.length + b.length + dl + 1 ≤ W) :
    ∃ τ', Run (W + 1) (feY pl dl) τ τ' (20 * b.length + 20) ∧
      Filled "OB" "po" (pre ++ (b.drop pl).take (b.length - dl)) τ' ∧
      OFr τ τ' ["wa", "wl", "ci", "po"] := by
  obtain ⟨τ1, r1, o1⟩ := asg_run (x := "wa") (B := W + 1) (σ := τ) (evalB_lit (n := pl) (by omega))
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "wl") (B := W + 1) (σ := τ1)
    (ev_sub (ev_var (by rw [o1.vars "bl" (by decide), hbl]) (by omega)) (evalB_lit (n := dl) (by omega))
      (by omega))
  have hF2 : Filled "OB" "po" pre τ2 :=
    hF.congr (by rw [o2.vars "po" (by decide), o1.vars "po" (by decide)]) (by rw [o2.arrs, o1.arrs])
  have ha2 : τ2.arrs "y" = τ.arrs "y" := by rw [o2.arrs, o1.arrs]
  have hseg : seg (τ2.arrs "y") pl (b.length - dl) = (b.drop pl).take (b.length - dl) := by
    rw [ha2]
    apply List.ext_getElem?
    intro j
    simp only [seg, List.getElem?_take, List.getElem?_drop]
    split_ifs with hj
    · have := hy (pl + j) (by omega)
      rw [Nat.zero_add] at this
      rw [this, List.getElem?_eq_getElem (by omega)]
    · rfl
  have hlen : pl + (b.length - dl) ≤ (τ.arrs "y").length := by rw [harr "y"]; omega
  obtain ⟨τ3, r3, F3, O3⟩ := cpSeg_ofr (W := W) (src := "y") (s := "wa") (l := "wl") (σ := τ2)
    (a := pl) (N := b.length - dl) (by decide)
    (by rw [o2.vars "wa" (by decide), o1.self]) o2.self (by decide) (by decide) (by decide) (by decide) hF2
    (by rw [ha2]; exact hlen) (by rw [o2.arrs, o1.arrs, harr "OB"]; omega) (by omega) (by omega)
    (by
      rw [hseg]; intro v hv
      have hv' : v ∈ seg (τ.arrs "y") pl (b.length - dl) := by rw [← ha2, hseg]; exact hv
      have := hlt.arrs "y" v (List.mem_of_mem_drop (List.mem_of_mem_take hv'))
      omega)
  rw [hseg] at F3
  refine ⟨τ3, ?_, F3, ?_⟩
  · refine (Run.seq r1 (Run.seq r2 r3)).mono ?_
    simp only [Expr.size]; omega
  · refine ⟨fun y hy => ?_, fun b hb => ?_, ?_, ?_, ?_⟩
    · rw [O3.vars y (fun h => hy (by simp at h ⊢; tauto)), o2.vars y (fun h => hy (by simp [h])),
        o1.vars y (fun h => hy (by simp [h]))]
    · rw [O3.arrs b hb, o2.arrs, o1.arrs]
    · rw [O3.len, o2.arrs, o1.arrs]
    · rw [O3.out, o2.out, o1.out]
    · rw [O3.inp, o2.inp, o1.inp]

end Lax185574Proofs.ResolveRam.Glue
