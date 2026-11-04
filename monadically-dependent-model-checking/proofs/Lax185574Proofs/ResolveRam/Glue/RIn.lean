import Lax185574Proofs.ResolveRam.Glue.Lib

/-!
Reading the input of a later round of the glue program of
lem:resolve-lift.

After the tag `tg`, the input of a later round is the length `sl` of the
state, the window (`tg - 1` entries), the state (the seventeen scalars
and the word of the list of words) and the answer of the switch with its
length. `rdIn` reads the window into `x` (its maximum into `mw`), the
scalars into `scR`, the words into the library, the answer into `y`, and
sets the total length `lt` of the library (`rdIn_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- Read the input of a later round, after the tag. -/
def rdIn : Com :=
  .seq (.read "sl") (.seq (.assign "nx" (.sub (.var "tg") (.lit 1))) (.seq rdX
    (.seq (.assign "mw" (.var "mx")) (.seq rdState (.seq rdAns
      (.assign "lt" (.add (.get "st" (.sub (.var "m") (.lit 1)))
        (.get "ln" (.sub (.var "m") (.lit 1))))))))))

theorem total_eq_last {ws : List (List ℕ)} (h : 0 < ws.length) :
    total ws = off ws (ws.length - 1) + ws[ws.length - 1].length := by
  rw [← off_succ (by omega), Nat.sub_add_cancel h, off_length]; rfl

/-- **Reading the input of a later round.** -/
theorem rdIn_run {W t : ℕ} {wx sc b : List ℕ} {ws : List (List ℕ)} {τ : Env}
    (htg : τ.vars "tg" = t) (hwx : wx.length = t - 1) (hsc : sc.length = 17) (hws : 1 ≤ ws.length)
    (hinp : τ.inp = (sc ++ toWord ws).length :: wx ++ (sc ++ toWord ws) ++ (b.length :: b))
    (harr : ArrW W τ) (hW64 : 64 ≤ W + 1)
    (hu : ∀ e ∈ [t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++ (b.length :: b),
      64 * e < W + 1) :
    ∃ τ', Run (W + 1) rdIn τ τ' (30 * (wx.length + (sc ++ toWord ws).length + b.length) + 100) ∧
      τ'.vars "sl" = (sc ++ toWord ws).length ∧ τ'.vars "tg" = t ∧ τ'.vars "mw" = maxEntry wx ∧
      (∀ i (h : i < 17), τ'.vars (scR[i]'(by simp [scR]; omega)) = sc.getD i 0) ∧
      Lib ws τ' ∧ τ'.vars "bl" = b.length ∧ SegAt "y" 0 b τ' ∧ PreAt "x" wx τ' ∧ ArrW W τ' ∧
      τ'.inp = [] ∧ τ'.out = τ.out ∧ (∀ y, y ∉ rdIn.wvars → τ'.vars y = τ.vars y) := by
  have hl : 64 * (sc ++ toWord ws).length < W + 1 := hu _ (by simp)
  have hbl : 64 * b.length < W + 1 := hu _ (by simp)
  have hwxl : 64 * wx.length < W + 1 := by
    have ht := hu t (by simp); rw [hwx]; omega
  have hwv : ∀ v ∈ wx, v < W + 1 := fun v hv => by have := hu v (by simp [hv]); omega
  have hsv : ∀ v ∈ toWord ws, v < W + 1 := fun v hv => by have := hu v (by simp [hv]); omega
  have hbv : ∀ v ∈ b, v < W + 1 := fun v hv => by have := hu v (by simp [hv]); omega
  have hlw : (toWord ws).length ≤ (sc ++ toWord ws).length := by simp
  have htw := length_toWord_words ws
  -- read sl
  set τ1 : Env := { τ.setVar "sl" (sc ++ toWord ws).length with inp := wx ++ ((sc ++ toWord ws) ++ (b.length :: b)) }
  have r1 : Run (W + 1) (.read "sl") τ τ1 1 := Run.read (by rw [hinp]; simp)
  -- nx := tg - 1
  set τ2 := τ1.setVar "nx" (t - 1)
  have r2 : Run (W + 1) (.assign "nx" (.sub (.var "tg") (.lit 1))) τ1 τ2 4 :=
    (Run.assign (ev_sub (ev_var (by simp [τ1, htg]) (by have := hu t (by simp); omega)) (evalB_lit (by omega))
      (by have := hu t (by simp); omega))).mono (by simp [Expr.size])
  obtain ⟨τ3, r3, i3, m3, x3, l3, o3, v3, a3⟩ := rdX_run (B := W + 1) (x := wx) (σ := τ2)
    (rest := (sc ++ toWord ws) ++ (b.length :: b)) (by simp [τ2, τ1]) (by simp [τ2, hwx])
    (by simp [τ2, τ1, harr "x"]; omega) (by omega) hwv
  set τ4 := τ3.setVar "mw" (maxEntry wx)
  have r4 : Run (W + 1) (.assign "mw" (.var "mx")) τ3 τ4 2 :=
    Run.assign (ev_var m3 (by
      have := maxEntry_le (b := W) (x := wx) (fun v hv => by have := hwv v hv; omega); omega))
  have ha4 : ∀ a, a ≠ "x" → τ4.arrs a = τ.arrs a := fun a ha => by simp [τ4, a3 a ha, τ2, τ1]
  obtain ⟨τ5, r5, i5, s5, m5, w5, o5, f5, aa5⟩ := rdState_run (B := W + 1) (sc := sc) (ws := ws)
    (rest := b.length :: b) (σ := τ4) hsc (by simp [τ4, i3, List.append_assoc])
    (by rw [ha4 _ (by decide), harr "a"]; have : total ws ≤ (toWord ws).length := by omega
        omega)
    (by rw [ha4 _ (by decide), harr "st"]; omega) (by rw [ha4 _ (by decide), harr "ln"]; omega)
    (by omega) hsv
  obtain ⟨τ6, r6, b6, y6, i6, o6, f6, a6⟩ := rdAns_run (B := W + 1) (b := b) (σ := τ5) i5
    (by rw [aa5 _ (by decide), ha4 _ (by decide), harr "y"]; omega) (by omega) hbv
  -- lt
  have hm6 : τ6.vars "m" = ws.length := by rw [f6 _ (by decide), m5]
  have hst6 : τ6.arrs "st" = τ5.arrs "st" := a6 _ (by decide)
  have hln6 : τ6.arrs "ln" = τ5.arrs "ln" := a6 _ (by decide)
  have hlast : ws.length - 1 < ws.length := by omega
  have hT := total_eq_last (ws := ws) (by omega)
  have hTle : total ws ≤ (toWord ws).length := by omega
  set τ7 := τ6.setVar "lt" (total ws)
  have r7 : Run (W + 1) (.assign "lt" (.add (.get "st" (.sub (.var "m") (.lit 1)))
      (.get "ln" (.sub (.var "m") (.lit 1))))) τ6 τ7 10 := by
    have e1 : (Expr.sub (.var "m") (.lit 1)).evalB (W + 1) τ6 = some (ws.length - 1) :=
      ev_sub (ev_var hm6 (by omega)) (evalB_lit (by omega)) (by omega)
    have hoff := off_le_total ws (ws.length - 1)
    refine (Run.assign (ev_add (evalB_get e1 (by rw [hst6]; exact w5.st _ hlast) (by omega))
      (evalB_get e1 (by rw [hln6]; exact w5.ln _ hlast) (by omega)) (by omega))).congr ?_ |>.mono
      (by simp [Expr.size])
    rw [← hT]
  have hrun : Run (W + 1) rdIn τ τ7 (30 * (wx.length + (sc ++ toWord ws).length + b.length) + 100) := by
    unfold rdIn
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono ?_
    simp only [List.length_append] at *
    omega
  have hfr : ∀ y, y ∉ rdIn.wvars → τ7.vars y = τ.vars y := fun y hy => hrun.frame_var y hy
  refine ⟨τ7, hrun, ?_, ?_, ?_, fun i h => ?_, ⟨?_, ?_, by simp [τ7]⟩, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩
  · simp only [τ7, vars_setVar]; simp
    rw [f6 _ (by decide), f5 _ (by decide) (by decide)]; simp [τ4, v3 "sl" (by decide), τ2, τ1]
  · simp only [τ7, vars_setVar]; simp
    rw [f6 _ (by decide), f5 _ (by decide) (by decide)]; simp [τ4, v3 "tg" (by decide), τ2, τ1, htg]
  · simp only [τ7, vars_setVar]; simp
    rw [f6 _ (by decide), f5 _ (by decide) (by decide)]; simp [τ4]
  · have hmem : scR[i]'(by simp [scR]; omega) ∈ scR := List.getElem_mem _
    have hne : scR[i]'(by simp [scR]; omega) ≠ "lt" := by
      intro h; rw [h] at hmem; exact absurd hmem (by decide)
    simp only [τ7, vars_setVar, if_neg hne]
    rw [f6 _ (by
      intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> rw [h] at hmem <;> exact absurd hmem (by decide)), s5 i h]
  · exact w5.of_arrs (by simp [τ7, a6 "a" (by decide)]) (by simp [τ7, hst6]) (by simp [τ7, hln6])
  · simp [τ7, hm6]
  · simp only [τ7, vars_setVar]; simp; exact b6
  · intro j hj; simp only [τ7, arrs_setVar, Nat.zero_add]; exact y6 j hj
  · intro j hj
    simp only [τ7, arrs_setVar]
    rw [a6 _ (by decide), aa5 _ (by decide), show τ4.arrs "x" = τ3.arrs "x" by simp [τ4]]
    exact x3 j hj
  · intro b'
    rw [Run.length_arrs hrun b', harr b']
  · simp [τ7, i6]
  · rw [hrun.out_eq (by decide)]

end Lax185574Proofs.ResolveRam.Glue
