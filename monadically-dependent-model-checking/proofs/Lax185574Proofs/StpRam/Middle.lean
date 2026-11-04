import Lax185574Proofs.StpRam.Round0

/-!
The middle rounds of the glue program of lem:compute-stp.

A middle round gets the state after `j` calls and the answer `b` of the
last call. It copies the state into the buffer with `j + 1` in place of
`j` and `b` appended to the list of answers. If `j + 1 < q · n` it asks
for the shift of entry `j + 1` of the list `F ++ A`, with tag `1` and no
window. Otherwise all answers are in the state, and it asks for the shift
of the first family tree again, with tag `2` and the window of length
`gl`, so that the next round is the final round.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574Proofs.Words

theorem XAt.read {O pre : List ℕ} {τ : Env} (h : XAt O pre τ) {x : String} (hx : x ≠ "xp") (v : ℕ)
    (l : List ℕ) : XAt O pre { τ.setVar x v with inp := l } :=
  ⟨by simp only [vars_setVar, if_neg (Ne.symm hx)]; exact h.1, by simpa using h.2⟩

theorem drop_mid (a b c : List ℕ) (i : ℕ) (h : i = a.length + b.length + 1) :
    (a ++ b ++ c).drop i = c.drop 1 := by
  subst h
  rw [List.append_assoc, show a.length + b.length + 1 = a.length + (b.length + 1) by omega,
    ← List.drop_drop, List.drop_left, ← List.drop_drop, List.drop_left]

/-- Read the header of the state and copy it, with `j + 1`. -/
def midHead : Com :=
  .seq (.assign "xp" (.lit 0)) (.seq (.read "h0") (.seq (push (.lit 0)) (.seq (.read "hn")
  (.seq (push (.var "hn")) (.seq (.read "hk2") (.seq (push (.var "hk2")) (.seq (.read "hq2")
  (.seq (push (.var "hq2")) (.seq (.read "hj") (.seq (push (.add (.var "hj") (.lit 1)))
  (.seq (.read "hg") (push (.var "hg")))))))))))))

/-- Choose the tag, the window and the query. -/
def midSel : Com :=
  .seq (.assign "jn" (.add (.var "hj") (.lit 1)))
   (.ite (.lt (.var "jn") (.mul (.var "hq2") (.var "hn")))
     (.seq (.assign "otg" (.lit 1)) (.seq (.assign "owin" (.lit 0))
       (.ite (.lt (.var "jn") (.var "hn")) (.seq (.assign "ws0" (.lit 7)) (.assign "wc" (.var "jn")))
         (.seq (.assign "ws0" (.add (.var "pa") (.lit 1))) (.assign "wc" (.sub (.var "jn") (.var "hn")))))))
     (.seq (.assign "otg" (.lit 2)) (.seq (.assign "owin" (.var "hg"))
       (.seq (.assign "ws0" (.lit 7)) (.assign "wc" (.lit 0))))))

/-- A middle round after the tag and the length of the state. -/
def mid : Com := .seq midHead (.seq cpMid (.seq midSel tail))

set_option maxHeartbeats 1000000 in
theorem midHead_run {B n k q j gl : ℕ} {rest : List ℕ} {τ : Env}
    (hinp : τ.inp = [0, n, k, q, j, gl] ++ rest) (hxl : 6 ≤ (τ.arrs "x").length)
    (hB : n < B ∧ k < B ∧ q < B ∧ j + 1 < B ∧ gl < B ∧ 7 < B) :
    ∃ τ', Run B midHead τ τ' 120 ∧ XAt (τ.arrs "x") [0, n, k, q, j + 1, gl] τ' ∧ τ'.inp = rest ∧
      τ'.out = τ.out ∧ τ'.vars "hn" = n ∧ τ'.vars "hq2" = q ∧ τ'.vars "hj" = j ∧
      τ'.vars "hg" = gl := by
  obtain ⟨hn, hk, hq, hj, hg, h7⟩ := hB
  set O := τ.arrs "x" with hO
  set τ0 := τ.setVar "xp" 0 with hτ0
  have r0 : Run B (.assign "xp" (.lit 0)) τ τ0 2 := (Run.assign (by simp; omega)).mono (by simp [Expr.size])
  have hx0 : XAt O [] τ0 := ⟨by simp [hτ0], by simp [hτ0, hO]⟩
  set τ1 : Env := { τ0.setVar "h0" 0 with inp := n :: k :: q :: j :: gl :: rest } with hτ1
  have r1 : Run B (.read "h0") τ0 τ1 1 := Run.read (by simp [hτ0, hinp])
  obtain ⟨τ2, r2, hx2, hi2, ho2⟩ := push_run (B := B) (O := O) (pre := []) (e := .lit 0) (v := 0)
    (XAt.read hx0 (x := "h0") (by decide) 0 (n :: k :: q :: j :: gl :: rest)) (by simp; omega) (by simp; omega) (by simp; omega)
  set τ3 : Env := { τ2.setVar "hn" n with inp := k :: q :: j :: gl :: rest } with hτ3
  have r3 : Run B (.read "hn") τ2 τ3 1 := Run.read (by simp [hi2, hτ1])
  obtain ⟨τ4, r4, hx4, hi4, ho4⟩ := push_run (B := B) (O := O) (pre := [0]) (e := .var "hn") (v := n)
    (XAt.read hx2 (x := "hn") (by decide) n (k :: q :: j :: gl :: rest)) (by simp; omega) (by simp; omega) (by simp [hτ3]; omega)
  set τ5 : Env := { τ4.setVar "hk2" k with inp := q :: j :: gl :: rest } with hτ5
  have r5 : Run B (.read "hk2") τ4 τ5 1 := Run.read (by simp [hi4, hτ3])
  obtain ⟨τ6, r6, hx6, hi6, ho6⟩ := push_run (B := B) (O := O) (pre := [0] ++ [n]) (e := .var "hk2")
    (v := k) (XAt.read hx4 (x := "hk2") (by decide) k (q :: j :: gl :: rest)) (by simp; omega) (by simp; omega)
    (by simp [hτ5]; omega)
  set τ7 : Env := { τ6.setVar "hq2" q with inp := j :: gl :: rest } with hτ7
  have r7 : Run B (.read "hq2") τ6 τ7 1 := Run.read (by simp [hi6, hτ5])
  obtain ⟨τ8, r8, hx8, hi8, ho8⟩ := push_run (B := B) (O := O) (pre := [0] ++ [n] ++ [k]) (e := .var "hq2")
    (v := q) (XAt.read hx6 (x := "hq2") (by decide) q (j :: gl :: rest)) (by simp; omega) (by simp; omega)
    (by simp [hτ7]; omega)
  set τ9 : Env := { τ8.setVar "hj" j with inp := gl :: rest } with hτ9
  have r9 : Run B (.read "hj") τ8 τ9 1 := Run.read (by simp [hi8, hτ7])
  obtain ⟨τ10, r10, hx10, hi10, ho10⟩ := push_run (B := B) (O := O) (pre := [0] ++ [n] ++ [k] ++ [q])
    (e := .add (.var "hj") (.lit 1)) (v := j + 1) (XAt.read hx8 (x := "hj") (by decide) j (gl :: rest))
    (by simp; omega) (by simp; omega) (by simp [hτ9]; omega)
  set τ11 : Env := { τ10.setVar "hg" gl with inp := rest } with hτ11
  have r11 : Run B (.read "hg") τ10 τ11 1 := Run.read (by simp [hi10, hτ9])
  obtain ⟨τ12, r12, hx12, hi12, ho12⟩ := push_run (B := B) (O := O)
    (pre := [0] ++ [n] ++ [k] ++ [q] ++ [j + 1]) (e := .var "hg") (v := gl)
    (XAt.read hx10 (x := "hg") (by decide) gl (rest)) (by simp; omega) (by simp; omega) (by simp [hτ11]; omega)
  have hrun : Run B midHead τ τ12 120 := by
    unfold midHead
    exact (Run.seq r0 (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6
      (Run.seq r7 (Run.seq r8 (Run.seq r9 (Run.seq r10 (Run.seq r11 r12)))))))))))).mono
      (by simp [Expr.size])
  refine ⟨τ12, hrun, by simpa using hx12, by simp [hi12, hτ11], by
      simp [ho12, hτ11, ho10, hτ9, ho8, hτ7, ho6, hτ5, ho4, hτ3, ho2, hτ1, hτ0], ?_, ?_, ?_, ?_⟩
  · rw [r12.frame_var "hn" (by decide)]
    simp [hτ11, r10.frame_var "hn" (by decide), hτ9, r8.frame_var "hn" (by decide), hτ7,
      r6.frame_var "hn" (by decide), hτ5, r4.frame_var "hn" (by decide), hτ3]
  · rw [r12.frame_var "hq2" (by decide)]
    simp [hτ11, r10.frame_var "hq2" (by decide), hτ9, r8.frame_var "hq2" (by decide), hτ7]
  · rw [r12.frame_var "hj" (by decide)]
    simp [hτ11, r10.frame_var "hj" (by decide), hτ9]
  · rw [r12.frame_var "hg" (by decide)]
    simp [hτ11]

/-- The tag of the output of the round after `j` calls. -/
def midTag (n q j : ℕ) : ℕ := if j + 1 < q * n then 1 else 2

/-- The length of the window of the output of the round after `j`
calls. -/
def midWin (n q j gl : ℕ) : ℕ := if j + 1 < q * n then 0 else gl

/-- The index of the query of the round after `j` calls. -/
def midIdx (n q j : ℕ) : ℕ := if j + 1 < q * n then j + 1 else 0

set_option maxHeartbeats 1000000 in
theorem midSel_run {B n q j gl P : ℕ} {τ : Env} (hn : τ.vars "hn" = n) (hq : τ.vars "hq2" = q)
    (hj : τ.vars "hj" = j) (hg : τ.vars "hg" = gl) (hp : τ.vars "pa" = P)
    (hB : q * n < B ∧ j + 2 < B ∧ gl < B ∧ P + 1 < B ∧ n < B ∧ 7 < B ∧ q < B) :
    ∃ τ', Run B midSel τ τ' 40 ∧ τ'.vars "otg" = midTag n q j ∧ τ'.vars "owin" = midWin n q j gl ∧
      τ'.vars "ws0" = (if j + 1 < q * n ∧ n ≤ j + 1 then P + 1 else 7) ∧
      τ'.vars "wc" = (if j + 1 < q * n then (if j + 1 < n then j + 1 else j + 1 - n) else 0) ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp ∧ τ'.vars "xp" = τ.vars "xp" := by
  obtain ⟨hqn, hjB, hgB, hPB, hnB, h7, hqB⟩ := hB
  set τ1 := τ.setVar "jn" (j + 1) with hτ1
  have r1 : Run B (.assign "jn" (.add (.var "hj") (.lit 1))) τ τ1 4 :=
    (Run.assign (by simp [hj]; omega)).mono (by simp [Expr.size])
  have hc1 : (Cond.lt (.var "jn") (.mul (.var "hq2") (.var "hn"))).evalB B τ1 =
      some (decide (j + 1 < q * n)) := by
    simp only [evalB_condLt_iff, evalB_bin_iff, evalB_var_iff]
    exact ⟨j + 1, q * n, ⟨by simp [hτ1], by simp [hτ1]; omega⟩,
      ⟨q, n, ⟨by simp [hτ1, hq], by simp [hτ1, hq]; omega⟩, ⟨by simp [hτ1, hn], by simp [hτ1, hn]; omega⟩,
        rfl, hqn⟩, rfl⟩
  have hc2 : ∀ ρ : Env, ρ.vars "jn" = j + 1 → ρ.vars "hn" = n →
      (Cond.lt (.var "jn") (.var "hn")).evalB B ρ = some (decide (j + 1 < n)) := by
    intro ρ h1 h2
    simp only [evalB_condLt_iff, evalB_var_iff]
    exact ⟨j + 1, n, ⟨h1.symm, by omega⟩, ⟨h2.symm, by omega⟩, rfl⟩
  have hjn : ∀ ρ : Env, ρ.vars "jn" = j + 1 → (Expr.var "jn").evalB B ρ = some (j + 1) := by
    intro ρ h; simp [h]; omega
  by_cases hlt : j + 1 < q * n
  · have ra : Run B (.assign "otg" (.lit 1)) τ1 (τ1.setVar "otg" 1) 2 :=
      (Run.assign (by simp; omega)).mono (by simp [Expr.size])
    have rb : Run B (.assign "owin" (.lit 0)) (τ1.setVar "otg" 1) ((τ1.setVar "otg" 1).setVar "owin" 0) 2 :=
      (Run.assign (by simp; omega)).mono (by simp [Expr.size])
    set τ2 := (τ1.setVar "otg" 1).setVar "owin" 0 with hτ2
    have hn2 : τ2.vars "hn" = n := by simp [hτ2, hτ1, hn]
    have hjn2 : τ2.vars "jn" = j + 1 := by simp [hτ2, hτ1]
    by_cases hl2 : j + 1 < n
    · have rc : Run B (.assign "ws0" (.lit 7)) τ2 (τ2.setVar "ws0" 7) 2 :=
        (Run.assign (by simp; omega)).mono (by simp [Expr.size])
      have rd : Run B (.assign "wc" (.var "jn")) (τ2.setVar "ws0" 7) ((τ2.setVar "ws0" 7).setVar "wc" (j + 1)) 2 :=
        (Run.assign (hjn _ (by simp [hjn2]))).mono (by simp [Expr.size])
      have hrun : Run B midSel τ ((τ2.setVar "ws0" 7).setVar "wc" (j + 1)) 40 := by
        unfold midSel
        refine (Run.seq r1 (Run.ite_true (by rw [hc1]; simp [hlt]) (Run.seq ra (Run.seq rb
          (Run.ite_true (by rw [hc2 τ2 hjn2 hn2]; simp [hl2]) (Run.seq rc rd)))))).mono ?_
        simp [Expr.size, Cond.size]
      refine ⟨_, hrun, by simp [hτ2, midTag, hlt], by simp [hτ2, midWin, hlt], by simp [hlt]; omega,
        by simp [hlt, hl2], by simp [hτ2, hτ1], by simp [hτ2, hτ1], by simp [hτ2, hτ1], by simp [hτ2, hτ1]⟩
    · have rc : Run B (.assign "ws0" (.add (.var "pa") (.lit 1))) τ2 (τ2.setVar "ws0" (P + 1)) 4 :=
        (Run.assign (by simp [hτ2, hτ1, hp]; omega)).mono (by simp [Expr.size])
      have rd : Run B (.assign "wc" (.sub (.var "jn") (.var "hn"))) (τ2.setVar "ws0" (P + 1))
          ((τ2.setVar "ws0" (P + 1)).setVar "wc" (j + 1 - n)) 4 := by
        refine (Run.assign ?_).mono (by simp [Expr.size])
        simp only [evalB_bin_iff, evalB_var_iff]
        exact ⟨j + 1, n, ⟨by simp [hjn2], by simp [hjn2]; omega⟩, ⟨by simp [hn2], by simp [hn2]; omega⟩,
          rfl, by show _ - _ < B; omega⟩
      have hrun : Run B midSel τ ((τ2.setVar "ws0" (P + 1)).setVar "wc" (j + 1 - n)) 40 := by
        unfold midSel
        refine (Run.seq r1 (Run.ite_true (by rw [hc1]; simp [hlt]) (Run.seq ra (Run.seq rb
          (Run.ite_false (by rw [hc2 τ2 hjn2 hn2]; simp [hl2]) (Run.seq rc rd)))))).mono ?_
        simp [Expr.size, Cond.size]
      refine ⟨_, hrun, by simp [hτ2, midTag, hlt], by simp [hτ2, midWin, hlt], by simp [hlt]; omega,
        by simp [hlt, hl2], by simp [hτ2, hτ1], by simp [hτ2, hτ1], by simp [hτ2, hτ1], by simp [hτ2, hτ1]⟩
  · have ra : Run B (.assign "otg" (.lit 2)) τ1 (τ1.setVar "otg" 2) 2 :=
      (Run.assign (by simp; omega)).mono (by simp [Expr.size])
    have rb : Run B (.assign "owin" (.var "hg")) (τ1.setVar "otg" 2) ((τ1.setVar "otg" 2).setVar "owin" gl) 2 :=
      (Run.assign (by simp [hτ1, hg]; omega)).mono (by simp [Expr.size])
    set τ2 := (τ1.setVar "otg" 2).setVar "owin" gl with hτ2
    have rc : Run B (.assign "ws0" (.lit 7)) τ2 (τ2.setVar "ws0" 7) 2 :=
      (Run.assign (by simp; omega)).mono (by simp [Expr.size])
    have rd : Run B (.assign "wc" (.lit 0)) (τ2.setVar "ws0" 7) ((τ2.setVar "ws0" 7).setVar "wc" 0) 2 :=
      (Run.assign (by simp; omega)).mono (by simp [Expr.size])
    have hrun : Run B midSel τ ((τ2.setVar "ws0" 7).setVar "wc" 0) 40 := by
      unfold midSel
      refine (Run.seq r1 (Run.ite_false (by rw [hc1]; simp [hlt]) (Run.seq ra (Run.seq rb
        (Run.seq rc rd))))).mono ?_
      simp [Expr.size, Cond.size]
    refine ⟨_, hrun, by simp [hτ2, midTag, hlt], by simp [hτ2, midWin, hlt], by simp [hlt],
      by simp [hlt], by simp [hτ2, hτ1], by simp [hτ2, hτ1], by simp [hτ2, hτ1], by simp [hτ2, hτ1]⟩

set_option maxHeartbeats 4000000 in
/-- **A middle round.** -/
theorem mid_run {B n k q j gl : ℕ} {F A : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hF : F.length = n) (hA : A.length = j) (hn : 1 ≤ n) (hj : j < q * n)
    (hinp : τ.inp = stState n k q j gl F A ++ (b.length :: b))
    (hxl : (stState n k q (j + 1) gl F (A ++ [b])).length ≤ (τ.arrs "x").length)
    (hB : (stState n k q (j + 1) gl F (A ++ [b])).length + q * n + gl + 10 < B)
    (hv : ∀ v ∈ stState n k q j gl F A ++ (b.length :: b), v < B) :
    ∃ τ', Run B mid τ τ' (100 * (stState n k q (j + 1) gl F (A ++ [b])).length + 400) ∧
      τ'.out = τ.out ++ [midTag n q j, (stState n k q (j + 1) gl F (A ++ [b])).length,
        midWin n q j gl] ++ stState n k q (j + 1) gl F (A ++ [b]) ++
        (F ++ (A ++ [b])).getD (midIdx n q j) [] := by
  have hSl := length_stState n k q (j + 1) gl F (A ++ [b])
  generalize hS : stState n k q (j + 1) gl F (A ++ [b]) = S at hxl hB hSl ⊢
  have hAl : (toWord (A ++ [b])).length = (toWord A).length + 1 + b.length := by
    rw [toWord_snoc, toWord_words]; simp; omega
  have hqB : q < B := hv q (by simp [stState])
  have hkB : k < B := hv k (by simp [stState])
  have hnB : n < B := hv n (by simp [stState])
  have hgB : gl < B := hv gl (by simp [stState])
  set O := τ.arrs "x" with hO
  obtain ⟨τ1, r1, hx1, hi1, ho1, hn1, hq1, hj1, hg1⟩ := midHead_run (B := B) (n := n) (k := k) (q := q)
    (j := j) (gl := gl) (rest := toWord F ++ toWord A ++ (b.length :: b)) (τ := τ)
    (by rw [hinp]; simp [stState]) (by rw [← hO]; omega) ⟨hnB, hkB, hqB, by omega, hgB, by omega⟩
  obtain ⟨τ2, r2, hx2, hp2, hi2, ho2⟩ := cpMid_run (B := B) (O := O) (pre := [0, n, k, q, j + 1, gl])
    (rest := []) F A b hx1 (by rw [hi1]; simp) (by simp; omega) (by simp; omega)
    (fun v h => hv v (by simp only [stState, List.mem_append] at h ⊢; tauto))
  have hfr2 : ∀ x ∈ ["hn", "hq2", "hj", "hg"], τ2.vars x = τ1.vars x := by
    intro x hx
    exact r2.frame_var x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [cpMid, cpList, cpFrame, cpEntries, cpEntry, Com.wvars])
  obtain ⟨τ3, r3, ht3, hw3, hs3, hc3, ha3, ho3, -, hxp3⟩ := midSel_run (B := B) (n := n) (q := q) (j := j)
    (gl := gl) (P := 6 + (toWord F).length) (τ := τ2)
    (by rw [hfr2 _ (by simp), hn1]) (by rw [hfr2 _ (by simp), hq1]) (by rw [hfr2 _ (by simp), hj1])
    (by rw [hfr2 _ (by simp), hg1]) (by rw [hp2]; simp)
    ⟨by omega, by omega, hgB, by omega, hnB, by omega, hqB⟩
  have hpre : [0, n, k, q, j + 1, gl] ++ toWord F ++ toWord (A ++ [b]) = S := by rw [← hS, stState]
  rw [hpre] at hx2
  have hX3 : τ3.arrs "x" = S ++ O.drop S.length := by rw [ha3, hx2.2]
  have hxp3' : τ3.vars "xp" = S.length := by rw [hxp3, hx2.1]
  have hFw : toWord F = n :: frames F := by rw [toWord_words, hF]
  -- the query
  obtain ⟨ws, p, jj, r, hjj, hq, hd, hp, hjv⟩ : ∃ (ws : List (List ℕ)) (p jj : ℕ) (r : List ℕ),
      ∃ h : jj < ws.length, ws[jj] = (F ++ (A ++ [b])).getD (midIdx n q j) [] ∧
        S.drop p = frames ws ++ r ∧ τ3.vars "ws0" = p ∧ τ3.vars "wc" = jj := by
    have hd7 : S.drop 7 = frames F ++ toWord (A ++ [b]) := by
      rw [← hS]; simp [stState, hFw]
    by_cases hlt : j + 1 < q * n
    · by_cases hl2 : j + 1 < n
      · refine ⟨F, 7, j + 1, toWord (A ++ [b]), by omega, ?_, hd7, by rw [hs3]; simp [hlt, hl2],
          by rw [hc3]; simp [hlt, hl2]⟩
        simp only [midIdx, if_pos hlt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          List.getElem?_eq_getElem (by omega)]; rfl
      · refine ⟨A ++ [b], 7 + (toWord F).length, j + 1 - n, [], by simp; omega, ?_, ?_,
          by rw [hs3, if_pos ⟨hlt, by omega⟩]; omega, by rw [hc3]; simp [hlt, hl2]⟩
        · simp only [midIdx, if_pos hlt]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hF,
            List.getElem?_eq_getElem (by simp; omega)]; rfl
        · rw [← hS, stState, drop_mid _ _ _ _ (by simp; omega), toWord_words]
          simp
    · refine ⟨F, 7, 0, toWord (A ++ [b]), by omega, ?_, hd7, by rw [hs3]; simp [hlt],
        by rw [hc3]; simp [hlt]⟩
      simp only [midIdx, if_neg hlt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega)]; rfl
  have hSv : ∀ v ∈ S, v < B := by
    intro v hv'
    rw [← hS, stState] at hv'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with ((h | h | h | h | h | h) | h) | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact hv v (by simp [stState, h])
    · rw [toWord_snoc] at h
      rcases List.mem_cons.mp h with h | h
      · have := length_toWord_words A; omega
      · rcases List.mem_append.mp h with h | h
        · exact hv v (by rw [stState, toWord_words A]; simp [h])
        · exact hv v (by simp [h])
  obtain ⟨τ4, r4, ho4⟩ := tail_run (B := B) (S := S) (D := O.drop S.length) (p := p) (j := jj)
    (tg := midTag n q j) (win := midWin n q j gl) (ws := ws) (r := r) (τ := τ3) hX3 hxp3' ht3 hw3 hp hjv
    hjj hd (by omega) hSv (by unfold midTag; split_ifs <;> omega) (by unfold midWin; split_ifs <;> omega)
  have hrun : Run B mid τ τ4 (100 * S.length + 400) := by
    unfold mid
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono ?_
    omega
  refine ⟨τ4, hrun, ?_⟩
  rw [ho4, ← hq, ho3, ho2, ho1]

end Lax185574Proofs.StpRam
