import Lax185574Proofs.ResolveRam.Glue.Slots
import Lax185574Proofs.ResolveRam.Glue.Wrap

/-!
The end of a later round of the glue program of lem:resolve-lift.

The buffer holds the output `pre ++ q ++ post`, with the real query `q`
at `qa` of length `ql`, followed by at least one entry. `finCallM e d`
puts the size `X` of the input of the composite (in `gX`) right behind
`q`, checks the guard on `q ++ [X]`, puts the entry back, checks the
entries and writes the output (`finCallM_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue

/-- The end of a later round with a call. -/
def finCallM (e d : ℕ) : Com :=
  .seq (.assign "sv" (.get "OB" (.add (.var "qa") (.var "ql"))))
  (.seq (.store "OB" (.add (.var "qa") (.var "ql")) (.var "gX"))
  (.seq (.assign "ql" (.add (.var "ql") (.lit 1)))
  (.seq (guardChk e d)
  (.seq (.assign "ql" (.sub (.var "ql") (.lit 1)))
  (.seq (.store "OB" (.add (.var "qa") (.var "ql")) (.var "sv"))
  (.seq entChk wrAll))))))

set_option maxHeartbeats 400000 in
/-- **The end of a later round with a call.** -/
theorem finCallM_run {W e d X : ℕ} {σ : Env} {pre q post : List ℕ} (hW : σ.vars "W" = W) (hW32 : 32 ≤ W)
    (hF : Filled "OB" "po" (pre ++ q ++ post) σ) (hpost : post ≠ []) (hqa : σ.vars "qa" = pre.length)
    (hql : σ.vars "ql" = q.length) (hgX : σ.vars "gX" = X) (hcap : (σ.arrs "OB").length = W + 1)
    (hlen : (pre ++ q ++ post).length + 1 ≤ W) (hv : ∀ v ∈ pre ++ q ++ post, v ≤ W) (hX : X ≤ W)
    (hovf : σ.vars "ovf" = 0) :
    ∃ σ', Run (W + 1) (finCallM e d) σ σ'
        ((pre ++ q ++ post).length * 72 + 60 * (e + 1) + 30 * 2 ^ d + 400) ∧
      σ'.out = σ.out ++ (pre ++ q ++ post) ∧
      σ'.vars "ovf" = (if guardOK W e d X q ∧ maxEntry (pre ++ q ++ post) < W / 32 / 32 then 0 else 1) := by
  set o := pre ++ q ++ post
  obtain ⟨x, post', rfl⟩ : ∃ x post', post = x :: post' := List.exists_cons_of_ne_nil hpost
  have hol : o.length = pre.length + q.length + 1 + post'.length := by simp [o]; omega
  set p := pre.length + q.length
  have hop : o[p]? = some x := by simp [o, p]
  have hxW : x ≤ W := hv x (by simp [o])
  have hidx : (Expr.add (.var "qa") (.var "ql")).evalB (W + 1) σ = some p :=
    ev_add (ev_var hqa (by omega)) (ev_var hql (by omega)) (by omega)
  obtain ⟨σ1, r1, o1⟩ := asg_run (x := "sv") (B := W + 1) (σ := σ) (v := x)
    (evalB_get hidx (by rw [hF.get p (by omega), ← List.getElem?_eq_getElem]; exact hop) (by omega))
  have hidx1 : (Expr.add (.var "qa") (.var "ql")).evalB (W + 1) σ1 = some p :=
    ev_add (ev_var (by rw [o1.vars "qa" (by decide), hqa]) (by omega))
      (ev_var (by rw [o1.vars "ql" (by decide), hql]) (by omega)) (by omega)
  have r2 : Run (W + 1) (.store "OB" (.add (.var "qa") (.var "ql")) (.var "gX")) σ1 (σ1.setArr "OB" p X) 5 :=
    (Run.store hidx1 (ev_var (by rw [o1.vars "gX" (by decide), hgX]) (by omega))
      (by rw [o1.arrs, hcap]; omega)).mono (by simp [Expr.size])
  set σ2 := σ1.setArr "OB" p X
  have F2 : Filled "OB" "po" (pre ++ q ++ X :: post') σ2 := by
    have := (show Filled "OB" "po" ((pre ++ q) ++ x :: post') σ1 from
      hF.congr (by rw [o1.vars "po" (by decide)]) (by rw [o1.arrs])).patch (v := X)
      (by rw [o1.arrs, hcap]; simp; omega)
    simpa [p] using this
  obtain ⟨σ3, r3, o3⟩ := asg_run (x := "ql") (B := W + 1) (σ := σ2)
    (ev_add (ev_var (by simp [σ2]; rw [o1.vars "ql" (by decide), hql]) (by omega)) (evalB_lit (n := 1) (by omega))
      (by omega))
  have hseg : seg (σ3.arrs "OB") pre.length (q.length + 1) = q ++ [X] := by
    have F3 : Filled "OB" "po" (pre ++ (q ++ [X]) ++ post') σ3 :=
      (F2.congr (by rw [o3.vars "po" (by decide)]) (by rw [o3.arrs])).congr rfl rfl |> fun h => by
        simpa using h
    have := seg_of_filled (A := pre) (M := q ++ [X]) (C := post') F3
    simpa using this
  have hW3 : σ3.vars "W" = W := by rw [o3.vars "W" (by decide)]; simp [σ2]; rw [o1.vars "W" (by decide), hW]
  obtain ⟨σ4, r4, h4, f4, a4, u4, i4⟩ := guardChk_run (W := W) (e := e) (d := d) (a := pre.length)
    (N := q.length + 1) (σ := σ3) hW3 (by omega)
    (by rw [o3.vars "qa" (by decide)]; simp [σ2]; rw [o1.vars "qa" (by decide), hqa]) o3.self
    (by rw [o3.arrs]; simp [σ2, o1.arrs, hcap]; omega) (by omega)
    (by rw [hseg]; intro v hv'; simp at hv'; rcases hv' with h | h
        · exact hv v (by simp [o, h])
        · omega)
  rw [hseg, maxEntry_append_X] at h4
  have e4 : ∀ y, y ∉ gVars → y ≠ "ql" → y ≠ "sv" → σ4.vars y = σ.vars y := fun y hy h1 h2 => by
    rw [f4 y hy]
    rw [o3.vars y h1]; simp only [σ2, vars_setArr]; rw [o1.vars y h2]
  obtain ⟨σ5, r5, o5⟩ := asg_run (x := "ql") (B := W + 1) (σ := σ4) (v := q.length)
    (ev_sub (ev_var (x := "ql") (v := q.length + 1) (by rw [f4 "ql" (by decide), o3.self]) (by omega))
      (evalB_lit (n := 1) (by omega)) (by omega))
  have hidx5 : (Expr.add (.var "qa") (.var "ql")).evalB (W + 1) σ5 = some p :=
    ev_add (ev_var (by rw [o5.vars "qa" (by decide), e4 "qa" (by decide) (by decide) (by decide), hqa]) (by omega))
      (ev_var o5.self (by omega)) (by omega)
  have hsv5 : σ5.vars "sv" = x := by
    rw [o5.vars "sv" (by decide), f4 "sv" (by decide), o3.vars "sv" (by decide)]; simp [σ2, o1.self]
  have hOB5 : σ5.arrs "OB" = σ2.arrs "OB" := by rw [o5.arrs, a4, o3.arrs]
  have r6 : Run (W + 1) (.store "OB" (.add (.var "qa") (.var "ql")) (.var "sv")) σ5 (σ5.setArr "OB" p x) 5 :=
    (Run.store hidx5 (ev_var hsv5 (by omega)) (by rw [hOB5]; simp [σ2, o1.arrs, hcap]; omega)).mono
      (by simp [Expr.size])
  set σ6 := σ5.setArr "OB" p x
  have F6 : Filled "OB" "po" o σ6 := by
    have h := (show Filled "OB" "po" ((pre ++ q) ++ X :: post') σ5 from
      F2.congr (by rw [o5.vars "po" (by decide), f4 "po" (by decide), o3.vars "po" (by decide)])
        (by rw [hOB5])).patch (v := x) (by rw [hOB5]; simp [σ2, o1.arrs, hcap]; omega)
    simpa [o, p] using h
  have hW6 : σ6.vars "W" = W := by simp [σ6]; rw [o5.vars "W" (by decide), e4 "W" (by decide) (by decide) (by decide), hW]
  obtain ⟨σ7, r7, h7, f7, a7, u7, i7⟩ := entChk_run (o := o) hW6 hW32 F6 (by omega) hv
  have hF7 : Filled "OB" "po" o σ7 := F6.congr (f7 _ (by decide)) (by rw [a7])
  obtain ⟨σ8, r8, ho8⟩ := wrAll_run (B := W + 1) hF7 (by omega) (fun v hv' => by have := hv v hv'; omega)
  have hov8 : σ8.vars "ovf" = σ7.vars "ovf" := r8.frame_var _ (by simp [wrAll, forUp, Com.wvars])
  refine ⟨σ8, ?_, ?_, ?_⟩
  · unfold finCallM
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono ?_
    simp only [Expr.size]; omega
  · rw [ho8, u7]; simp only [σ6, out_setArr]; rw [o5.out, u4, o3.out]; simp [σ2, o1.out]
  · rw [hov8, h7]
    simp only [σ6, vars_setArr]
    rw [o5.vars "ovf" (by decide), h4]
    have h0 : σ3.vars "ovf" = 0 := by rw [o3.vars "ovf" (by decide)]; simp [σ2]; rw [o1.vars "ovf" (by decide), hovf]
    rw [h0]
    unfold guardOK
    by_cases hg : min ((q.length + 1 + max (maxEntry q) X + 1) ^ (e + 1)) W ≤ W / min (2 ^ d) W <;>
      by_cases he : maxEntry o < W / 32 / 32 <;> simp [hg, he]

end Lax185574Proofs.ResolveRam.Glue
