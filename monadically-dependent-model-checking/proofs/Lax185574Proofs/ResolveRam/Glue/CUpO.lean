import Lax185574Proofs.ResolveRam.Glue.CFinLL
import Lax185574Proofs.ResolveRam.Glue.CaseLib

/-!
The output word of an item on the way up, as a new word of the library:
the entries `2, 3, 4` of the item word, the word `2` of the library (the
atom words) and the real answer (`ouC_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- The scalars of the copies. -/
def ouA (pl dl : ℕ) : List (String × Expr) :=
  [("po", .lit 0), ("tsa", .add (.get "st" (.var "ow")) (.lit 2)), ("tsl", .lit 3), ("tsb", .get "st" (.lit 2)),
    ("tsm", .get "ln" (.lit 2)), ("tys", .lit pl), ("tyl", .sub (.var "bl") (.lit dl))]

/-- Build the output word in the buffer and append it to the library. -/
def ouC (pl dl : ℕ) : Com :=
  .seq (asgs (ouA pl dl)) (.seq (cpSeg "a" "tsa" "tsl") (.seq (cpSeg "a" "tsb" "tsm") (.seq (cpSeg "y" "tys" "tyl")
    (.seq (asgs [("ls", .lit 0), ("lL", .var "po")]) (lbApp "OB")))))

/-- The scalars that `ouC` may write. -/
def ouV : List String := ["po", "tsa", "tsl", "tsb", "tsm", "tys", "tyl", "ci", "ls", "lL", "lt", "m"]

/-- The output word. -/
def ouW (L : List (List ℕ)) (iw : ℕ) (b : List ℕ) (pl dl : ℕ) : List ℕ :=
  ((L.getD iw []).drop 2).take 3 ++ L.getD 2 [] ++ (b.drop pl).take (b.length - dl)

theorem seg_word' {L : List (List ℕ)} {τ : Env} (hw : WordsAt L τ) {i : ℕ} (hi : i < L.length) {j N : ℕ}
    (hN : j + N ≤ L[i].length) : seg (τ.arrs "a") (off L i + j) N = (L[i].drop j).take N := by
  apply List.ext_getElem?
  intro k
  simp only [seg, List.getElem?_take, List.getElem?_drop]
  split_ifs with h
  · rw [show off L i + j + k = off L i + (j + k) by omega]
    exact (hw.a i hi (j + k) (by omega)).trans (List.getElem?_eq_getElem (by omega)).symm
  · rfl

theorem seg_segAt {τ : Env} {src : String} {b : List ℕ} (h : SegAt src 0 b τ) {a N : ℕ} (hN : a + N ≤ b.length) :
    seg (τ.arrs src) a N = (b.drop a).take N := by
  apply List.ext_getElem?
  intro k
  simp only [seg, List.getElem?_take, List.getElem?_drop]
  split_ifs with hk
  · have := h (a + k) (by omega)
    rw [Nat.zero_add] at this
    rw [this, List.getElem?_eq_getElem (by omega)]
  · rfl

theorem ouA_rd (pl dl : ℕ) : ∀ p ∈ ouA pl dl, ∀ q ∈ ouA pl dl, q.1 ∉ exRv p.2 := by
  intro p hp q hq
  simp only [ouA, List.mem_cons, List.mem_nil_iff, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [exRv]

set_option maxHeartbeats 1600000 in
/-- **The output word.** -/
theorem ouC_run {W pl dl iw : ℕ} {L : List (List ℕ)} {b : List ℕ} {τ : Env}
    (har : ArrW W τ) (hlt : EnvLt (W + 1) τ) (hL : Lib L τ) (h3 : 3 < L.length) (hiw : iw < L.length)
    (h5 : 5 ≤ L[iw].length) (how : τ.vars "ow" = iw) (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ)
    (hdl : dl ≤ b.length) (hpd : pl ≤ dl) (hroom : 2 * total L + 2 * L.length + 2 * b.length + 16 ≤ W)
    (hbv : ∀ v ∈ b, v ≤ W) :
    ∃ τ', Run (W + 1) (ouC pl dl) τ τ' (40 * (L[2].length + b.length) + 500) ∧
      Lib (L ++ [ouW L iw b pl dl]) τ' ∧
      (∀ y, y ∉ ouV → τ'.vars y = τ.vars y) ∧ (∀ c, c ∉ ["a", "st", "ln", "OB"] → τ'.arrs c = τ.arrs c) ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hLv := lib_lt hL.at_ hlt
  have hsw := hL.at_.st iw hiw
  have hoffW : off L iw < W + 1 := hlt.arrs "st" _ (List.mem_of_getElem? hsw)
  have hoffi := off_add_le hiw
  have h2 : 2 < L.length := by omega
  have hs2 := hL.at_.st 2 h2
  have hl2 := hL.at_.ln 2 h2
  have hoff2 := off_add_le h2
  have hoff2W : off L 2 < W + 1 := hlt.arrs "st" _ (List.mem_of_getElem? hs2)
  have hln2W : L[2].length < W + 1 := hlt.arrs "ln" _ (List.mem_of_getElem? hl2)
  have hwW : total L ≤ W := by omega
  -- step 1
  let f1 : String → ℕ := fun y => if y = "tsa" then off L iw + 2 else if y = "tsl" then 3
    else if y = "tsb" then off L 2 else if y = "tsm" then L[2].length else if y = "tys" then pl
    else if y = "tyl" then b.length - dl else 0
  obtain ⟨τ1, r1, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ) (l := ouA pl dl) (f := f1)
    (by
      intro p hp
      simp only [ouA, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact evalB_lit (by omega)
      · exact ev_add (evalB_get (ev_var how (by omega)) hsw hoffW) (evalB_lit (by omega)) (by omega)
      · exact evalB_lit (by omega)
      · exact evalB_get (evalB_lit (by omega)) hs2 hoff2W
      · exact evalB_get (evalB_lit (by omega)) hl2 hln2W
      · exact evalB_lit (by omega)
      · exact ev_sub (ev_var hbl (by omega)) (evalB_lit (by omega)) (by omega))
    (ouA_rd pl dl)
  have F1 : Filled "OB" "po" [] τ1 := ⟨by rw [s1 "po" (by simp [ouA])]; simp [f1], fun i h => absurd h (by simp)⟩
  have hOB : (τ1.arrs "OB").length = W + 1 := by rw [a1]; exact har "OB"
  have hw1 : WordsAt L τ1 := hL.at_.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1])
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  -- step 2: the header of the tree
  have hseg2 := seg_word' (τ := τ1) hw1 hiw (j := 2) (N := 3) (by omega)
  obtain ⟨τ2, r2, F2, O2⟩ := cpSeg_ofr (W := W) (src := "a") (s := "tsa") (l := "tsl") (σ := τ1) (pre := [])
    (a := off L iw + 2) (N := 3) (by decide) (s1 "tsa" (by simp [ouA])) (s1 "tsl" (by simp [ouA])) (by decide)
    (by decide) (by decide) (by decide) F1 (by rw [a1, har "a"]; omega) (by rw [hOB]; simp; omega) (by omega)
    (by simp; omega)
    (by
      intro v hv
      rw [hseg2] at hv
      exact hLv _ (List.getElem_mem hiw) v (List.mem_of_mem_drop (List.mem_of_mem_take hv)))
  rw [hseg2, List.nil_append] at F2
  -- step 3: the atom words
  have hw2 : WordsAt L τ2 := hw1.of_arrs (O2.arrs "a" (by decide)) (O2.arrs "st" (by decide))
    (O2.arrs "ln" (by decide))
  have hseg3 := seg_take (τ := τ2) hw2 h2 (N := L[2].length) le_rfl
  rw [List.take_length] at hseg3
  have hOB2 : (τ2.arrs "OB").length = W + 1 := by rw [O2.len, hOB]
  obtain ⟨τ3, r3, F3, O3⟩ := cpSeg_ofr (W := W) (src := "a") (s := "tsb") (l := "tsm") (σ := τ2)
    (pre := (L[iw].drop 2).take 3) (a := off L 2) (N := L[2].length) (by decide)
    (by rw [O2.vars "tsb" (by decide), s1 "tsb" (by simp [ouA])]; simp [f1])
    (by rw [O2.vars "tsm" (by decide), s1 "tsm" (by simp [ouA])]; simp [f1]) (by decide)
    (by decide) (by decide) (by decide) F2 (by rw [O2.arrs "a" (by decide), a1, har "a"]; omega)
    (by rw [hOB2]; simp; omega) (by omega) (by simp; omega)
    (by
      intro v hv
      rw [hseg3] at hv
      exact hLv _ (List.getElem_mem h2) v hv)
  rw [hseg3] at F3
  -- step 4: the answer
  have hy3 : SegAt "y" 0 b τ3 := fun j hj => by
    rw [O3.arrs "y" (by decide), O2.arrs "y" (by decide), a1]; exact hy j hj
  have hseg4 := seg_segAt hy3 (a := pl) (N := b.length - dl) (by omega)
  have hOB3 : (τ3.arrs "OB").length = W + 1 := by rw [O3.len, hOB2]
  obtain ⟨τ4, r4, F4, O4⟩ := cpSeg_ofr (W := W) (src := "y") (s := "tys") (l := "tyl") (σ := τ3)
    (pre := (L[iw].drop 2).take 3 ++ L[2]) (a := pl) (N := b.length - dl) (by decide)
    (by rw [O3.vars "tys" (by decide), O2.vars "tys" (by decide), s1 "tys" (by simp [ouA])]; simp [f1])
    (by rw [O3.vars "tyl" (by decide), O2.vars "tyl" (by decide), s1 "tyl" (by simp [ouA])]; simp [f1]) (by decide)
    (by decide) (by decide) (by decide) F3
    (by rw [O3.arrs "y" (by decide), O2.arrs "y" (by decide), a1, har "y"]; omega)
    (by rw [hOB3]; simp; omega) (by omega) (by simp; omega)
    (by
      intro v hv
      rw [hseg4] at hv
      exact hbv v (List.mem_of_mem_drop (List.mem_of_mem_take hv)))
  rw [hseg4] at F4
  set O := (L[iw].drop 2).take 3 ++ L[2] ++ (b.drop pl).take (b.length - dl) with hO
  have hOe : O = ouW L iw b pl dl := by
    simp only [O, ouW, List.getD_eq_getElem _ _ hiw, List.getD_eq_getElem _ _ h2]
  have hOl : O.length ≤ 3 + L[2].length + b.length := by simp [O]; omega
  -- step 5: the copy
  have O4' := (O2.trans O3).trans O4
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))) hlt
  obtain ⟨τ5, r5, s5, g5, a5, o5, i5⟩ := asgs_run (B := W + 1) (τ := τ4)
    (l := [("ls", .lit 0), ("lL", .var "po")]) (f := fun y => if y = "ls" then 0 else O.length)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · simp
      · simp only [show ("lL" : String) ≠ "ls" by decide, if_false]; exact ev_var F4.pos (by omega))
    (by decide)
  have L5 : Lib L τ5 := by
    refine hL.of ?_ ?_ ?_ ?_ ?_
    · rw [g5 "m" (by decide), O4'.vars "m" (by decide), g1 "m" (by simp [ouA])]
    · rw [g5 "lt" (by decide), O4'.vars "lt" (by decide), g1 "lt" (by simp [ouA])]
    · rw [a5, O4'.arrs "a" (by decide), a1]
    · rw [a5, O4'.arrs "st" (by decide), a1]
    · rw [a5, O4'.arrs "ln" (by decide), a1]
  have hseg : SegAt "OB" 0 O τ5 := fun j hj => by rw [a5, Nat.zero_add]; exact F4.get j hj
  have hAr : ∀ c, (τ5.arrs c).length = W + 1 := fun c => by
    rw [a5]
    by_cases hc : c = "OB"
    · subst hc; rw [O4'.len, hOB]
    · rw [O4'.arrs c hc, a1]; exact har c
  have hOv : ∀ v ∈ O, v ≤ W := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := hl4.arrs "OB" _ (List.mem_of_getElem? (F4.get j hj))
    omega
  obtain ⟨τ6, r6, L6, f6, a6, l6, o6, i6⟩ := lbApp_run (W := W) (src := "OB") (s := 0) L5
    (by rw [s5 "ls" (by simp)]; simp) (by rw [s5 "lL" (by simp)]; simp) hseg (by decide) (by simp)
    (by rw [hAr]; omega) (by rw [hAr]; omega) (by rw [hAr]; omega) (by omega) (by omega) hOv
  rw [hOe] at L6
  have hrun := Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))
  refine ⟨τ6, hrun.mono ?_, L6, fun y hy => ?_, fun c hc => ?_, fun c => by rw [l6]; exact hAr c,
    Run.envLt hrun hlt, by rw [o6, o5, O4'.out, o1], by rw [i6, i5, O4'.inp, i1]⟩
  · have hA : asgK (ouA pl dl) ≤ 60 := by simp [asgK, ouA, Expr.size]
    have hO' : (ouW L iw b pl dl).length ≤ 3 + L[2].length + b.length := by rw [← hOe]; exact hOl
    have hB : asgK [("ls", Expr.lit 0), ("lL", Expr.var "po")] = 5 := rfl
    rw [hB]
    rw [← hOe] at hO'
    have : O.length * 18 ≤ 18 * (3 + L[2].length + b.length) := by omega
    have : (b.length - dl) * 20 ≤ 20 * b.length := by omega
    omega
  · have h1 : y ∉ ["ci", "lt", "m"] := fun h => hy (by simp [ouV] at h ⊢; tauto)
    have h2 : y ∉ ["ls", "lL"] := fun h => hy (by simp [ouV] at h ⊢; tauto)
    have h3 : y ∉ ["ci", "po"] ++ ["ci", "po"] ++ ["ci", "po"] := fun h => hy (by simp [ouV] at h ⊢; tauto)
    have h4 : y ∉ (ouA pl dl).map Prod.fst := fun h => hy (by simp [ouV, ouA] at h ⊢; tauto)
    rw [f6 y h1, g5 y h2, O4'.vars y h3, g1 y h4]
  · have h1 : c ∉ ["a", "st", "ln"] := fun h => hc (by simp at h ⊢; tauto)
    rw [a6 c h1, a5, O4'.arrs c (fun h => hc (by simp [h])), a1]

end Lax185574Proofs.ResolveRam.Glue
