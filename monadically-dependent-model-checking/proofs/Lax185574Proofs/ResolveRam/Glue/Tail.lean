import Lax185574Proofs.ResolveRam.Glue.Plan

/-!
Writing the head and the new state in a later round of the glue program
of lem:resolve-lift.

`wrHS` writes the tag `Nt`, the length of the state, the length `Nw`
of the window, the seventeen scalars of the new state (the first nine
unchanged, then `Nph Nd Ni Nm NSG NFA NCO NLV`) and the word of the
list of library words given by the ranges in `PR` (`wrHS_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- Replace one entry of a filled buffer. -/
theorem _root_.Lax185574Proofs.MC.Filled.patch {a pv : String} {pre F : List ℕ} {x v : ℕ} {τ : Env}
    (h : Filled a pv (pre ++ x :: F) τ) (hl : pre.length < (τ.arrs a).length) :
    Filled a pv (pre ++ v :: F) (τ.setArr a pre.length v) := by
  refine ⟨by simp [h.pos], fun i hi => ?_⟩
  rw [← List.getElem?_eq_getElem hi]
  simp only [arrs_setArr, ↓reduceIte, List.getElem?_set]
  by_cases hip : pre.length = i
  · subst hip; rw [if_pos rfl, if_pos hl]; simp
  · rw [if_neg hip, getElem?_mid pre _ _ x i (Ne.symm hip)]
    have hi' : i < (pre ++ x :: F).length := by simp at hi ⊢; omega
    rw [h.get i hi', ← List.getElem?_eq_getElem hi']

/-- The scalars of the new state. -/
def hsV : List String :=
  ["z0", "gX", "nx", "gn", "gP", "gQ", "gS", "gK", "gq", "Nph", "Nd", "Ni", "Nm", "NSG", "NFA", "NCO", "NLV"]

/-- Write the head and the new state. -/
def wrHS : Com :=
  .seq (.assign "po" (.lit 0)) (.seq (pushL "OB" "po" [.var "Nt", .lit 0, .var "Nw"])
    (.seq (pushL "OB" "po" (hsV.map Expr.var)) (.seq wrPlan
      (.store "OB" (.lit 1) (.sub (.var "po") (.lit 3))))))

/-- The scalars that `wrHS` writes. -/
def hsW : List String := ["po"] ++ wpV

/-- **Writing the head and the new state.** -/
theorem wrHS_run {W : ℕ} {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {τ : Env}
    (hw : WordsAt L τ) (hPR : PreAt "PR" (prW ps) τ) (hnp : τ.vars "np" = ps.length)
    (hps : ∀ p ∈ ps, p.1 + p.2 ≤ L.length) (hcap : (τ.arrs "OB").length = W + 1)
    (hB : 30 + (ps.length + 1) * (total L + L.length + 1) ≤ W) (hPW2 : 2 * ps.length + 2 ≤ W)
    (hv : ∀ w ∈ L, ∀ v ∈ w, v ≤ W) (ha : total L ≤ (τ.arrs "a").length)
    (hs : ∀ y ∈ "Nt" :: "Nw" :: hsV, τ.vars y ≤ W) :
    ∃ τ', Run (W + 1) wrHS τ τ'
        (40 * (total (planW L ps) + (planW L ps).length) + 100 * ps.length + 250) ∧
      Filled "OB" "po" (τ.vars "Nt" :: (17 + (toWord (planW L ps)).length) :: τ.vars "Nw" ::
        (hsV.map τ.vars ++ toWord (planW L ps))) τ' ∧
      OFr τ τ' hsW := by
  have hW1 : W < W + 1 := by omega
  have r1 : Run (W + 1) (.assign "po" (.lit 0)) τ (τ.setVar "po" 0) 2 := Run.assign (evalB_lit (by omega))
  have F1 := Filled.empty "OB" "po" τ
  have o1 := OFr.setVar τ "po" 0
  have hNt := hs "Nt" (by simp)
  have hNw := hs "Nw" (by simp)
  obtain ⟨τ2, r2, F2, v2, a2, l2, u2, i2⟩ := pushL_run (B := W + 1) (es := [.var "Nt", .lit 0, .var "Nw"])
    (vs := [τ.vars "Nt", 0, τ.vars "Nw"]) F1
    (fun τ' hv' ha' => by
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true]
      refine ⟨ev_var (by rw [hv' _ (by decide)]; simp) (by omega), evalB_lit (by omega),
        ev_var (by rw [hv' _ (by decide)]; simp) (by omega)⟩)
    (by simp; omega) (by simp; omega)
  have o2 : OFr (τ.setVar "po" 0) τ2 ["po"] := ⟨fun y hy => v2 y (by simpa using hy), a2, l2, u2, i2⟩
  simp only [List.nil_append] at F2
  have hv2 : ∀ y, y ≠ "po" → τ2.vars y = τ.vars y := fun y hy => by rw [v2 y hy]; simp [hy]
  obtain ⟨τ3, r3, F3, o3⟩ := pushVars_run (W := W) (xs := hsV) (pre := [τ.vars "Nt", 0, τ.vars "Nw"])
    (by decide) F2 (fun x hx => by rw [hv2 x (by intro h; subst h; revert hx; decide)]; exact hs x (by simp [hx]))
    (by rw [l2]; simp [hcap, hsV]; omega) (by simp [hsV]; omega)
  have hmap : hsV.map τ2.vars = hsV.map τ.vars :=
    List.map_congr_left fun x hx => hv2 x (by intro h; subst h; revert hx; decide)
  rw [hmap] at F3
  have o13 := (o1.trans o2).trans o3
  have hw3 : WordsAt L τ3 := hw.of_arrs (by rw [o13.arrs _ (by decide)]) (by rw [o13.arrs _ (by decide)])
    (by rw [o13.arrs _ (by decide)])
  have hpre : ([τ.vars "Nt", 0, τ.vars "Nw"] ++ hsV.map τ.vars).length = 20 := by simp [hsV]
  obtain ⟨τ4, r4, F4, o4⟩ := wrPlan_run (W := W) (L := L) (ps := ps) hw3
    (fun i hi => by rw [o13.arrs _ (by decide)]; exact hPR i hi)
    (by rw [o13.vars _ (by decide), hnp]) hps F3 (by rw [o13.len, hcap]) (by rw [hpre]; omega) hPW2 hv
    (by rw [o13.arrs _ (by decide)]; exact ha)
  have hlen4 : (([τ.vars "Nt", 0, τ.vars "Nw"] ++ hsV.map τ.vars) ++ toWord (planW L ps)).length =
      20 + (toWord (planW L ps)).length := by rw [List.length_append, hpre]
  have hpo4 : τ4.vars "po" = 20 + (toWord (planW L ps)).length := by rw [F4.pos, hlen4]
  have hsz := planW_sub_size L ps
  have hlw := length_toWord_words (planW L ps)
  have hfr := length_frames (planW L ps)
  have hcp : 20 + (toWord (planW L ps)).length ≤ W := by
    have : ps.length * (total L + L.length) ≤ (ps.length + 1) * (total L + L.length + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [hlw]; omega
  have hF4 : Filled "OB" "po" ([τ.vars "Nt"] ++ 0 :: (τ.vars "Nw" :: (hsV.map τ.vars ++ toWord (planW L ps)))) τ4 := by
    simpa using F4
  have r5 : Run (W + 1) (.store "OB" (.lit 1) (.sub (.var "po") (.lit 3))) τ4
      (τ4.setArr "OB" 1 (17 + (toWord (planW L ps)).length)) 5 := by
    have := Run.store (B := W + 1) (σ := τ4) (a := "OB") (i := .lit 1) (e := .sub (.var "po") (.lit 3))
      (idx := 1) (v := 17 + (toWord (planW L ps)).length) (evalB_lit (by omega))
      (by rw [show 17 + (toWord (planW L ps)).length = 20 + (toWord (planW L ps)).length - 3 by omega]
          exact ev_sub (ev_var hpo4 (by omega)) (evalB_lit (by omega)) (by omega))
      (by rw [o4.len, o13.len, hcap]; omega)
    exact this.mono (by simp [Expr.size])
  have F5 := hF4.patch (v := 17 + (toWord (planW L ps)).length) (by rw [o4.len, o13.len, hcap]; simp; omega)
  refine ⟨_, ?_, by simpa using F5, ?_⟩
  · unfold wrHS
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    simp [Expr.size, sum_size_vars, hsV]
    omega
  · have := o13.trans o4 |>.trans (xs := ["po"] ++ ["po"] ++ ["po"] ++ wpV) (ys := [])
      (τ'' := τ4.setArr "OB" 1 (17 + (toWord (planW L ps)).length))
      ⟨fun _ _ => by simp, fun b hb => by simp [hb], by simp, by simp, by simp⟩
    exact this.mono (by intro y hy; simp [hsW, wpV] at hy ⊢; tauto)

end Lax185574Proofs.ResolveRam.Glue
