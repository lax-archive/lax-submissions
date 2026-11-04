import Lax185574Proofs.ResolveRam.Glue.PLv0

/-!
The item words of level `0` of lem:resolve-lift (`LV0Spec`).

The input is the word of `G`, then `P`, `Q`, the sign, and the family:
`n` followed by the words of the `n` trees, without frames. `lv0Cmd`
skips the colors and the two graphs of `G`, then the three scalars and
`n`, and runs `lvTree` once per tree. That appends the frame of the item
word `0 :: 0 :: w` of the tree word `w` (`lv0Cmd_spec`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TreeAlgo

/-- Append the frame of the item word of level `0` of the tree at `tu`. -/
def lvTree : Com :=
  .seq (.assign "ts" (.var "tu")) (.seq (.assign "tq" (.get "x" (.add (.var "tu") (.lit 1))))
    (.seq (.assign "tf" (.add (.var "tu") (.lit 3))) (.seq (skL "x")
      (.seq (.ite (.lt (.lit 0) (.var "tq")) (skL "x") .skip)
        (.seq (.assign "tl" (.sub (.var "tf") (.var "ts")))
          (.seq (push1 "OB" "po" (.add (.var "tl") (.lit 2))) (.seq (push1 "OB" "po" (.lit 0))
            (.seq (push1 "OB" "po" (.lit 0)) (.seq (cpSeg "x" "ts" "tl") (.assign "tu" (.var "tf")))))))))))

/-- The scalars that `lvTree` writes. -/
def lvV0 : List String := ["ts", "tq", "tf", "tn", "tz", "tl", "po", "ci", "tu"]

/-- **One tree.** -/
theorem lvTree_run {W : ℕ} {X : List ℕ} {u : ℕ} {σ : TypeTree} {r pre : List ℕ} {τ : Env}
    (ha : τ.arrs "x" = X) (hd : X.drop u = toWord σ ++ r) (hu : τ.vars "tu" = u)
    (hF : Filled "OB" "po" pre τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : u + (toWord σ).length + 2 < W + 1) (hB' : pre.length + (toWord σ).length + 3 ≤ W)
    (hv : ∀ v ∈ toWord σ, v < W + 1) :
    ∃ τ', Run (W + 1) lvTree τ τ' (60 * (toWord σ).length + 200) ∧
      Filled "OB" "po" (pre ++ frames [0 :: 0 :: toWord σ]) τ' ∧
      τ'.vars "tu" = u + (toWord σ).length ∧ OFr τ τ' lvV0 := by
  obtain ⟨k, q, ℓ, t⟩ := σ
  have hw : toWord (⟨k, q, ℓ, t⟩ : TypeTree) = k :: q :: ℓ :: toWord t := rfl
  rw [hw] at hd hB hB' hv ⊢
  simp only [List.length_cons] at hB hB'
  obtain ⟨A, E', hs, hE'⟩ : ∃ (A : List (List ℕ)) (E' : List ℕ), toWord t = toWord A ++ E' ∧
      ((q = 0 ∧ E' = []) ∨ (0 < q ∧ ∃ E : List (List ℕ), E' = toWord E)) := by
    cases q with
    | zero => exact ⟨(Node.atoms t).words, [], by rw [List.append_nil]; exact toWord_node_zero t,
      Or.inl ⟨rfl, rfl⟩⟩
    | succ h => exact ⟨_, _, toWord_node_succ t, Or.inr ⟨by omega, _, rfl⟩⟩
  have hlen : (toWord t).length = (toWord A).length + E'.length := by rw [hs, List.length_append]
  have hXl : u + (toWord t).length + 3 ≤ X.length := by
    have := congrArg List.length hd; simp at this; omega
  have hX1 : X[u + 1]? = some q := by
    have := getElem?_of_drop hd (i := 1) (by simp); simpa using this
  have hd3 : X.drop (u + 3) = toWord A ++ (E' ++ r) := by
    rw [← List.drop_drop, hd]; simp [hs]
  have hqv : q < W + 1 := hv q (by simp)
  set τ1 := τ.setVar "ts" u
  have r1 : Run (W + 1) (.assign "ts" (.var "tu")) τ τ1 2 := Run.assign (ev_var hu (by omega))
  set τ2 := τ1.setVar "tq" q
  have r2 : Run (W + 1) (.assign "tq" (.get "x" (.add (.var "tu") (.lit 1)))) τ1 τ2 5 :=
    (Run.assign (evalB_get (ev_add (ev_var (v := u) (by simp [τ1, hu]) (by omega)) (evalB_lit (by omega))
      (by omega)) (by simp [τ1, ha]; exact hX1) hqv)).mono (by simp [Expr.size])
  set τ3 := τ2.setVar "tf" (u + 3)
  have r3 : Run (W + 1) (.assign "tf" (.add (.var "tu") (.lit 3))) τ2 τ3 4 :=
    (Run.assign (ev_add (ev_var (v := u) (by simp [τ2, τ1, hu]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  obtain ⟨τ4, r4, f4, a4, o4⟩ := skL_run (W := W) (A := "x") (τ := τ3) (by simp [τ3, τ2, τ1, ha]) hd3
    (by simp [τ3]) (by omega) (fun v hv' => hv v (by simp [hs, hv']))
  have h5 : ∃ τ5, Run (W + 1) (.ite (.lt (.lit 0) (.var "tq")) (skL "x") .skip) τ4 τ5
      (20 * E'.length + 25) ∧ τ5.vars "tf" = u + 3 + (toWord A).length + E'.length ∧
      τ5.arrs = τ4.arrs ∧ OFr τ4 τ5 ["tn", "tf", "tz"] := by
    have hq4 : τ4.vars "tq" = q := by rw [o4.vars "tq" (by decide)]; simp [τ3, τ2]
    have hc := evalB_condLt (B := W + 1) (σ := τ4) (evalB_lit (n := 0) (by omega)) (ev_var hq4 hqv)
    rcases hE' with ⟨rfl, rfl⟩ | ⟨hq, E, rfl⟩
    · refine ⟨τ4, (Run.ite_false (by simpa using hc) Run.skip).mono (by simp [Cond.size, Expr.size]),
        by simp [f4], rfl, (OFr.refl _).mono (by simp)⟩
    · have hd5 : X.drop (u + 3 + (toWord A).length) = toWord E ++ r := by
        rw [← List.drop_drop, hd3, List.drop_left]
      obtain ⟨τ5, r5, f5, a5, o5⟩ := skL_run (W := W) (A := "x") (τ := τ4) (by rw [a4]; simp [τ3, τ2, τ1, ha])
        hd5 f4 (by omega) (fun v hv' => hv v (by simp [hs, hv']))
      exact ⟨τ5, (Run.ite_true (by rw [hc]; simp [hq]) r5).mono (by simp [Cond.size, Expr.size]; omega),
        f5, a5, o5⟩
  obtain ⟨τ5, r5, f5, a5, o5⟩ := h5
  set L := 3 + (toWord A).length + E'.length
  have hL : (k :: q :: ℓ :: toWord t).length = L := by simp [hlen, L]; omega
  have hts5 : τ5.vars "ts" = u := by
    rw [o5.vars "ts" (by decide), o4.vars "ts" (by decide)]; simp [τ3, τ2, τ1]
  set τ6 := τ5.setVar "tl" L
  have r6 : Run (W + 1) (.assign "tl" (.sub (.var "tf") (.var "ts"))) τ5 τ6 4 :=
    ((Run.assign (ev_sub (ev_var f5 (by omega)) (ev_var hts5 (by omega)) (by omega))).mono
      (by simp [Expr.size])).congr (by simp only [τ6]; congr 1; omega)
  have hpo5 : τ5.vars "po" = τ.vars "po" := by
    rw [o5.vars "po" (by decide), o4.vars "po" (by decide)]; simp [τ3, τ2, τ1]
  have hA5 : τ5.arrs = τ.arrs := by rw [a5, a4]; simp [τ3, τ2, τ1]
  have F6 : Filled "OB" "po" pre τ6 := hF.congr (by simp [τ6, hpo5]) (by simp [τ6, hA5])
  have hOB6 : (τ6.arrs "OB").length = W + 1 := by simp [τ6, hA5, hOB]
  obtain ⟨τ7, r7, F7, o7⟩ := push1_ofr (W := W) (e := .add (.var "tl") (.lit 2)) (v := L + 2) F6
    (ev_add (ev_var (by simp [τ6]) (by omega)) (evalB_lit (by omega)) (by omega)) (by rw [hOB6]; omega)
    (by omega)
  obtain ⟨τ8, r8, F8, o8⟩ := push1_ofr (W := W) (e := .lit 0) (v := 0) F7 (evalB_lit (by omega))
    (by rw [o7.len, hOB6]; simp; omega) (by simp; omega)
  obtain ⟨τ9, r9, F9, o9⟩ := push1_ofr (W := W) (e := .lit 0) (v := 0) F8 (evalB_lit (by omega))
    (by rw [o8.len, o7.len, hOB6]; simp; omega) (by simp; omega)
  have hts9 : τ9.vars "ts" = u := by
    rw [o9.vars "ts" (by decide), o8.vars "ts" (by decide), o7.vars "ts" (by decide)]; simp [τ6, hts5]
  have htl9 : τ9.vars "tl" = L := by
    rw [o9.vars "tl" (by decide), o8.vars "tl" (by decide), o7.vars "tl" (by decide)]; simp [τ6]
  have hx9 : τ9.arrs "x" = X := by
    rw [o9.arrs "x" (by decide), o8.arrs "x" (by decide), o7.arrs "x" (by decide)]; simp [τ6, hA5, ha]
  have hseg : seg (τ9.arrs "x") u L = k :: q :: ℓ :: toWord t := by
    rw [hx9, seg, hd, ← hL, List.take_left]
  obtain ⟨τ10, r10, F10, o10⟩ := cpSeg_ofr (W := W) (src := "x") (s := "ts") (l := "tl") (a := u)
    (N := L) (σ := τ9) (by decide) hts9 htl9 (by decide) (by decide) (by decide) (by decide) F9
    (by rw [hx9]; omega) (by rw [o9.len, o8.len, o7.len, hOB6]; simp; omega) (by omega)
    (by simp; omega) (by rw [hseg]; intro v hv'; have := hv v hv'; omega)
  rw [hseg] at F10
  have hf10 : τ10.vars "tf" = u + L := by
    rw [o10.vars "tf" (by decide), o9.vars "tf" (by decide), o8.vars "tf" (by decide), o7.vars "tf" (by decide)]
    simp [τ6, f5, L]; omega
  set τ11 := τ10.setVar "tu" (u + L)
  have r11 : Run (W + 1) (.assign "tu" (.var "tf")) τ10 τ11 2 := Run.assign (ev_var hf10 (by omega))
  refine ⟨τ11, ?_, ?_, by simp [τ11, hL], ?_⟩
  · unfold lvTree
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
      (Run.seq r8 (Run.seq r9 (Run.seq r10 r11)))))))))).mono ?_
    rw [hL]
    simp only [Expr.size, L]; omega
  · have e : frames [0 :: 0 :: k :: q :: ℓ :: toWord t] = [L + 2, 0, 0] ++ k :: q :: ℓ :: toWord t := by
      rw [frames_single]; simp only [List.length_cons] at hL ⊢; simp; omega
    rw [e]
    simpa [List.append_assoc] using F10.setVar (y := "tu") (by decide) (u + L)
  · exact (((((((((((OFr.setVar τ "ts" u).trans (OFr.setVar τ1 "tq" q)).trans (OFr.setVar τ2 "tf" _)).trans
      o4).trans o5).trans (OFr.setVar τ5 "tl" L)).trans o7).trans o8).trans o9).trans o10).trans
      (OFr.setVar τ10 "tu" _)).mono (by decide)

end Lax185574Proofs.ResolveRam.Glue
