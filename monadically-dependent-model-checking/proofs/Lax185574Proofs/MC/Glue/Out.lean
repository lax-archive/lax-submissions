import Lax185574Proofs.MC.Glue.Walk

/-!
The writer of the glue program of thm:mc.

A round with a call writes its output into the buffer `OB` (filled up to
`po`) and then onto the output tape. The output is the head `hdW` (tag,
state length, window length, state) and the query `qW` to the callee:
`swIn` of the three callee queries, where the callee that does the work
gets the query `realQ` and the other two the fixed queries. The state
`stW` is the eleven scalars `scN`, the lengths of the words of the
partial graph (`GW`), of the family of trees (`FW`) and of the
localized sentence (`lo`), and then these words. The kind `ck` of the
call is `0` for a merge (on the tree of `FW` at `ta` of length `tl`),
`1` for a resolve, `2` for the evaluation and `3` for the fixed merge
query.

Before writing, `outCmd` checks that the words are small
(`sizeChk`), and after filling the buffer that every entry is below
`W / 32 / 32` (`entChk`) and that the query of the working callee
passes the guard `(|u| + max u + 1) ^ (e + 1) ≤ W / 2 ^ d` (`guardChk`),
otherwise it sets `ovf`. Constants that may exceed the word size, the
exponent `e + 1` and the factor `2 ^ d`, are built from the literals `0`
and `1` by saturating arithmetic (`satLit`), so that the command runs at
every word length. `outCmd_run` gives the output when `ovf` stays `0`
and the conditions under which it does.
-/

namespace Lax185574Proofs.MC.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.Simulate

/-! ### Copying a segment onto the output buffer -/

/-- Append the `l` cells of `src` from position `s` to the buffer `OB`. -/
def cpSeg (src s l : String) : Com :=
  forUp "ci" (.var l) (push1 "OB" "po" (.get src (.add (.var s) (.var "ci"))))

/-- The segment of `A` of length `N` from position `a`. -/
def seg (A : List ℕ) (a N : ℕ) : List ℕ := (A.drop a).take N

theorem flatMap_getD_eq_seg (A : List ℕ) (a N : ℕ) (h : a + N ≤ A.length) :
    ((List.range N).flatMap fun k => [A.getD (a + k) 0]) = seg A a N := by
  have hm : ∀ l : List ℕ, (l.flatMap fun k => [A.getD (a + k) 0]) = l.map fun k => A.getD (a + k) 0 := by
    intro l; induction l <;> simp_all
  rw [hm]
  apply List.ext_getElem
  · simp [seg]; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [seg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show a + i < A.length by omega)]

theorem length_seg {A : List ℕ} {a N : ℕ} (h : a + N ≤ A.length) : (seg A a N).length = N := by
  simp [seg]; omega

theorem cpSeg_run {B : ℕ} {src s l : String} {σ : Env} {pre : List ℕ} {a N : ℕ}
    (hsrc : src ≠ "OB") (hs : σ.vars s = a) (hl : σ.vars l = N)
    (hs1 : s ≠ "po") (hs2 : s ≠ "ci") (hl1 : l ≠ "po") (hl2 : l ≠ "ci")
    (hF : Filled "OB" "po" pre σ) (hA : a + N ≤ (σ.arrs src).length)
    (hcap : pre.length + N ≤ (σ.arrs "OB").length) (hB : a + N < B) (hB' : pre.length + N < B)
    (hv : ∀ v ∈ seg (σ.arrs src) a N, v < B) :
    ∃ σ', Run B (cpSeg src s l) σ σ' (N * 20 + 6) ∧
      Filled "OB" "po" (pre ++ seg (σ.arrs src) a N) σ' := by
  set A := σ.arrs src with hAdef
  let P : Env → Prop := fun τ => τ.vars s = a ∧ τ.vars l = N ∧ τ.arrs src = A ∧
    (τ.arrs "OB").length = (σ.arrs "OB").length
  obtain ⟨σ', r, -, -, F⟩ := forUp_push1 (B := B) (N := N) (cap := (σ.arrs "OB").length)
    (i := "ci") (a := "OB") (pv := "po") (e := .get src (.add (.var s) (.var "ci")))
    (bnd := .var l) (by decide) (fun k => A.getD (a + k) 0) P
    (fun τ v hP => ⟨by simp [hs2, hP.1], by simp [hl2, hP.2.1], by simp [hP.2.2.1],
      by simp [hP.2.2.2]⟩)
    (fun τ τ' hP hv' ha hlen => ⟨by rw [hv' s hs1, hP.1], by rw [hv' l hl1, hP.2.1],
      by rw [ha src hsrc, hP.2.2.1], by rw [hlen, hP.2.2.2]⟩)
    (fun τ hP => hP.2.2.2) (by omega) ⟨hs, hl, rfl, rfl⟩ hF
    (fun τ hP => ev_var hP.2.1 (by omega))
    (fun k hk τ hP hik => by
      have hk' : a + k < A.length := by omega
      have hmem : A.getD (a + k) 0 ∈ seg A a N := by
        rw [← flatMap_getD_eq_seg A a N hA]
        exact List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by simp⟩
      exact evalB_get (ev_add (ev_var hP.1 (by omega)) (ev_var hik (by omega)) (by omega))
        (by rw [hP.2.2.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; simp)
        (hv _ hmem))
    hcap hB'
  refine ⟨σ', r.mono (by simp [Expr.size]; omega), ?_⟩
  rwa [flatMap_getD_eq_seg A a N hA] at F


/-! ### The largest entry of a segment -/

theorem maxEntry_append_single (l : List ℕ) (v : ℕ) : maxEntry (l ++ [v]) = max (maxEntry l) v := by
  induction l with
  | nil => simp [maxEntry]
  | cons a l ih => simp only [maxEntry, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih]; omega

theorem maxEntry_le {x : List ℕ} {b : ℕ} (h : ∀ v ∈ x, v ≤ b) : maxEntry x ≤ b := by
  induction x with
  | nil => simp [maxEntry]
  | cons a l ih =>
    simp only [maxEntry, List.foldr_cons] at ih ⊢
    exact max_le (h a (by simp)) (ih fun v hv => h v (by simp [hv]))

theorem seg_succ {A : List ℕ} {a k : ℕ} (h : a + k < A.length) :
    seg A a (k + 1) = seg A a k ++ [A.getD (a + k) 0] := by
  simp only [seg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h]; rfl

theorem seg_zero (A : List ℕ) (a : ℕ) : seg A a 0 = [] := by simp [seg]

/-- One round of the scan for the largest entry. -/
def mxBody (ar s : String) : Com :=
  .ite (.lt (.var "mx") (.get ar (.add (.var s) (.var "ci"))))
    (.assign "mx" (.get ar (.add (.var s) (.var "ci")))) .skip

/-- `mx` is the largest of the `l` cells of `ar` from position `s`. -/
def mxSeg (ar s l : String) : Com := .seq (.assign "mx" (.lit 0)) (forUp "ci" (.var l) (mxBody ar s))

theorem mxSeg_run {B : ℕ} {ar s l : String} {σ : Env} {a N : ℕ}
    (hs : σ.vars s = a) (hl : σ.vars l = N)
    (hs1 : s ≠ "mx") (hs2 : s ≠ "ci") (hl1 : l ≠ "mx") (hl2 : l ≠ "ci")
    (hA : a + N ≤ (σ.arrs ar).length) (hB : a + N < B)
    (hv : ∀ v ∈ seg (σ.arrs ar) a N, v < B) :
    ∃ σ', Run B (mxSeg ar s l) σ σ' (N * 30 + 10) ∧
      σ'.vars "mx" = maxEntry (seg (σ.arrs ar) a N) := by
  set A := σ.arrs ar with hAdef
  have hv' : ∀ k < N, A.getD (a + k) 0 < B := fun k hk => hv _ (by
    rw [← flatMap_getD_eq_seg A a N hA]
    exact List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by simp⟩)
  have hmB : ∀ k ≤ N, maxEntry (seg A a k) < B := by
    intro k hk
    induction k with
    | zero => simp [seg_zero, maxEntry]; omega
    | succ k ih => rw [seg_succ (by omega), maxEntry_append_single]; have := hv' k (by omega)
                   have := ih (by omega); omega
  obtain ⟨σ', r, ⟨hm, -⟩, -⟩ := forUp_run (B := B) (σ := σ.setVar "mx" 0) (i := "ci") (e := .var l)
    (body := mxBody ar s) (N := N) (K := 20)
    (fun k τ => τ.vars "mx" = maxEntry (seg A a k) ∧ τ.vars s = a ∧ τ.vars l = N ∧ τ.arrs ar = A)
    (by omega) (fun k _ τ hI _ => ev_var hI.2.2.1 (by omega))
    ⟨by simp [seg_zero, maxEntry], by simp [hs2, hs1, hs], by simp [hl2, hl1, hl], by simp [hAdef]⟩
    (by
      rintro k hk τ ⟨hm, hsτ, hlτ, hAτ⟩ hik
      have hk' : a + k < A.length := by omega
      have hget : (Expr.get ar (.add (.var s) (.var "ci"))).evalB B τ = some (A.getD (a + k) 0) :=
        evalB_get (ev_add (ev_var hsτ (by omega)) (ev_var hik (by omega)) (by omega))
          (by rw [hAτ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; simp) (hv' k hk)
      have hc := evalB_condLt (ev_var hm (hmB k (by omega))) hget
      have hsucc : maxEntry (seg A a (k + 1)) = max (maxEntry (seg A a k)) (A.getD (a + k) 0) := by
        rw [seg_succ hk', maxEntry_append_single]
      by_cases hlt : maxEntry (seg A a k) < A.getD (a + k) 0
      · refine ⟨τ.setVar "mx" (A.getD (a + k) 0), (Run.ite_true (by rw [hc, decide_eq_true hlt])
          (Run.assign hget)).mono (by simp [Expr.size, Cond.size]), by simp [hik], ?_⟩
        refine ⟨by rw [hsucc, max_eq_right hlt.le]; simp, by simp [hs1, hs2, hsτ], by simp [hl1, hl2, hlτ], by simp [hAτ]⟩
      · refine ⟨τ, (Run.ite_false (by rw [hc, decide_eq_false hlt]) Run.skip).mono
          (by simp [Expr.size, Cond.size]), hik, ?_⟩
        refine ⟨by rw [hsucc, max_eq_left (not_lt.1 hlt)]; simp [hm], by simp [hs2, hsτ], by simp [hl2, hlτ], by simp [hAτ]⟩)
  refine ⟨σ', (Run.seq (Run.assign (evalB_lit (by omega))) r).mono (by simp [Expr.size]; omega),
    hm⟩

/-! ### Writing the buffer -/

/-- Write the first `po` cells of `OB`. -/
def wrAll : Com := forUp "ci" (.var "po") (.write (.get "OB" (.var "ci")))

theorem wrAll_run {B : ℕ} {σ : Env} {o : List ℕ} (hF : Filled "OB" "po" o σ) (hB : o.length < B)
    (hv : ∀ v ∈ o, v < B) :
    ∃ σ', Run B wrAll σ σ' (o.length * 12 + 6) ∧ σ'.out = σ.out ++ o := by
  have hA : 0 + o.length ≤ (σ.arrs "OB").length := by have := hF.length_le; omega
  have hseg : ∀ k ≤ o.length, seg (σ.arrs "OB") 0 k = o.take k := by
    intro k hk
    apply List.ext_getElem
    · simp [seg]; omega
    · intro i h1 h2
      simp only [seg, List.drop_zero, List.getElem_take]
      have := hF.get i (by simp at h2; omega)
      rw [List.getElem?_eq_getElem (by simp [seg] at h1; omega)] at this
      exact Option.some.inj this
  obtain ⟨σ', r, ⟨ho, -⟩, -⟩ := forUp_run (B := B) (σ := σ) (i := "ci") (e := .var "po")
    (body := .write (.get "OB" (.var "ci"))) (N := o.length) (K := 4)
    (fun k τ => τ.out = σ.out ++ o.take k ∧ τ.vars "po" = o.length ∧ τ.arrs "OB" = σ.arrs "OB")
    hB (fun k _ τ hI _ => ev_var hI.2.1 hB) ⟨by simp, by simp [hF.pos], by simp⟩
    (by
      rintro k hk τ ⟨ho, hp, ha⟩ hik
      have hget : (Expr.get "OB" (.var "ci")).evalB B τ = some o[k] :=
        evalB_get (ev_var hik (by omega)) (by rw [ha]; exact hF.get k hk)
          (hv _ (List.getElem_mem hk))
      refine ⟨_, (Run.write hget).mono (by simp [Expr.size]), by simp [hik], ?_⟩
      refine ⟨?_, by simp [hp], by simp [ha]⟩
      show τ.out ++ [o[k]] = σ.out ++ o.take (k + 1)
      rw [ho, List.take_add_one, List.getElem?_eq_getElem hk]; simp)
  exact ⟨σ', r.mono (by simp only [Expr.size]; omega), by rw [ho, List.take_length]⟩


/-! ### Large constants from small literals -/

/-- `z := min (z + 1) W`. -/
def satInc (z : String) : Com :=
  .ite (.lt (.var z) (.var "W")) (.assign z (.add (.var z) (.lit 1))) .skip

/-- `z := min N W`, by binary digits, with the literals `0` and `1` only. -/
def satLit (z : String) (N : ℕ) : Com :=
  if N < 2 then .assign z (.lit N)
  else .seq (satLit z (N / 2)) (.seq (satAdd z z z) (if N % 2 = 1 then satInc z else .skip))
termination_by N
decreasing_by omega

theorem setVar_vars_self (σ : Env) (z : String) : σ.setVar z (σ.vars z) = σ := by
  cases σ with
  | mk vars arrs inp out =>
    simp only [Env.setVar, Env.mk.injEq, and_true]
    funext y; split <;> simp_all

theorem satInc_run {B W : ℕ} {z : String} {σ : Env} (hW : σ.vars "W" = W) (hWB : W < B)
    (hz : σ.vars z ≤ W) :
    Run B (satInc z) σ (σ.setVar z (min (σ.vars z + 1) W)) 8 := by
  unfold satInc
  have hc := evalB_condLt (B := B) (σ := σ) (e := .var z) (f := .var "W") (ev_var rfl (by omega))
    (ev_var hW hWB)
  by_cases h : σ.vars z < W
  · rw [show min (σ.vars z + 1) W = σ.vars z + 1 by omega]
    exact (Run.ite_true (by rw [hc, decide_eq_true h]) (Run.assign (ev_add (ev_var rfl (by omega))
      (evalB_lit (by omega)) (by omega)))).mono (by simp [Expr.size, Cond.size])
  · have he : σ.setVar z (min (σ.vars z + 1) W) = σ := by
      rw [show min (σ.vars z + 1) W = σ.vars z by omega]; exact setVar_vars_self σ z
    rw [he]
    exact (Run.ite_false (by rw [hc, decide_eq_false h]) Run.skip).mono
      (by simp [Expr.size, Cond.size])

theorem satLit_run {B W : ℕ} {z : String} (hz : z ≠ "W") (hWB : W < B) (hW1 : 1 ≤ W) :
    ∀ (N : ℕ) (σ : Env), σ.vars "W" = W →
      ∃ σ', Run B (satLit z N) σ σ' (30 * N + 30) ∧ σ'.vars z = min N W ∧
        (∀ y, y ≠ z → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro σ hW
    by_cases hN : N < 2
    · rw [satLit, if_pos hN]
      exact ⟨_, (Run.assign (evalB_lit (by omega))).mono (by simp only [Expr.size]; omega),
        by simp; omega, fun y hy => by simp [hy], rfl, rfl, rfl⟩
    · rw [satLit, if_neg hN]
      obtain ⟨σ₁, r₁, h₁, f₁, a₁, o₁, i₁⟩ := ih (N / 2) (by omega) σ hW
      have hW₁ : σ₁.vars "W" = W := by rw [f₁ _ (Ne.symm hz), hW]
      have r₂ := satAdd_run (B := B) (x := z) (y := z) (z := z) hW₁ hWB (by omega) (by omega)
      set σ₂ := σ₁.setVar z (min (σ₁.vars z + σ₁.vars z) W) with hσ₂
      have h₂ : σ₂.vars z = min (2 * (N / 2)) W := by simp [hσ₂, h₁]; omega
      have hW₂ : σ₂.vars "W" = W := by simp [hσ₂, Ne.symm hz, hW₁]
      by_cases hb : N % 2 = 1
      · rw [if_pos hb]
        have r₃ := satInc_run (z := z) hW₂ hWB (by omega)
        refine ⟨_, (Run.seq r₁ (Run.seq r₂ r₃)).mono (by omega), by simp [h₂]; omega,
          fun y hy => by simp [hσ₂, hy, f₁ y hy], by simp [hσ₂, a₁], by simp [hσ₂, o₁],
          by simp [hσ₂, i₁]⟩
      · rw [if_neg hb]
        refine ⟨_, (Run.seq r₁ (Run.seq r₂ Run.skip)).mono (by omega), by rw [h₂]; omega,
          fun y hy => by simp [hσ₂, hy, f₁ y hy], by simp [hσ₂, a₁], by simp [hσ₂, o₁],
          by simp [hσ₂, i₁]⟩


/-! ### The arithmetic of the guard -/

theorem pow_min_sat (s E W : ℕ) (hW : 1 ≤ W) : min (s ^ min E W) W = min (s ^ E) W := by
  by_cases hE : E ≤ W
  · rw [min_eq_left hE]
  rw [show min E W = W by omega]
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s
    · rw [zero_pow (by omega), zero_pow (by omega)]
    · simp
  · have h1 : W < s ^ W := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hs W)
    have h2 : s ^ W ≤ s ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- A passed guard bounds the power. -/
theorem guard_sound_arith {s E W v r sQ : ℕ} (hW1 : W + 1 = 2 ^ (v - r)) (hrs : r < sQ)
    (hW : 2 ≤ W) (h : min (s ^ E) W ≤ W / min (2 ^ (sQ - r)) W) : s ^ E ≤ 2 ^ (v - sQ) := by
  have hc2 : 2 ≤ min (2 ^ (sQ - r)) W := by
    have : 2 ≤ 2 ^ (sQ - r) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (sQ - r) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdiv : W / min (2 ^ (sQ - r)) W < W := Nat.div_lt_self (by omega) (by omega)
  have hsE : s ^ E ≤ W / min (2 ^ (sQ - r)) W := by
    rcases le_or_gt (s ^ E) W with h' | h'
    · rwa [min_eq_left h'] at h
    · rw [min_eq_right h'.le] at h; omega
  by_cases hc : 2 ^ (sQ - r) ≤ W
  · rw [min_eq_left hc] at hsE
    have hlt : sQ - r < v - r := by
      by_contra hh
      have : 2 ^ (v - r) ≤ 2 ^ (sQ - r) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hsplit : 2 ^ (v - r) = 2 ^ (sQ - r) * 2 ^ (v - sQ) := by
      rw [← pow_add]; congr 1; omega
    calc s ^ E ≤ W / 2 ^ (sQ - r) := hsE
      _ ≤ (W + 1) / 2 ^ (sQ - r) := Nat.div_le_div_right (by omega)
      _ = 2 ^ (v - sQ) := by
        rw [hW1, hsplit, Nat.mul_div_cancel_left _ (by positivity)]
  · rw [min_eq_right (by omega), Nat.div_self (by omega)] at hsE
    exact hsE.trans Nat.one_le_two_pow

/-- A small power passes the guard. -/
theorem guard_compl_arith {s E W v r sQ : ℕ} (hW1 : W + 1 = 2 ^ (v - r)) (hrs : r < sQ)
    (hs : 1 ≤ s) (h : 2 * s ^ E ≤ 2 ^ (v - sQ)) : min (s ^ E) W ≤ W / min (2 ^ (sQ - r)) W := by
  have hsE1 : 1 ≤ s ^ E := Nat.one_le_pow _ _ (by omega)
  have hv : sQ < v := by
    by_contra hh
    rw [show v - sQ = 0 by omega] at h; simp at h; omega
  have hsplit : W + 1 = 2 ^ (sQ - r) * 2 ^ (v - sQ) := by
    rw [hW1, ← pow_add]; congr 1; omega
  have hc1 : 1 ≤ 2 ^ (sQ - r) := Nat.one_le_two_pow
  have hc : 2 ^ (sQ - r) ≤ W := by
    have : 2 ≤ 2 ^ (v - sQ) := by omega
    nlinarith
  rw [min_eq_left hc]
  refine le_trans (min_le_left _ _) ((Nat.le_div_iff_mul_le (by omega)).2 ?_)
  have : s ^ E + 1 ≤ 2 ^ (v - sQ) := by omega
  nlinarith


/-! ### The guard -/

/-- The scalars written by the guard. -/
def gVars : List String := ["mx", "ci", "ob", "o1", "oe", "oc", "oa", "oi", "ovf"]

/-- The guard on the `ql` cells of `OB` from position `qa`, with exponent
`e + 1` and the factor `2 ^ d`: `ovf := 1` unless
`min ((ql + max + 1) ^ (e + 1)) W ≤ W / min (2 ^ d) W`. -/
def guardChk (e d : ℕ) : Com :=
  .seq (mxSeg "OB" "qa" "ql") (.seq (satAdd "ql" "mx" "ob") (.seq (.assign "o1" (.lit 1))
  (.seq (satAdd "ob" "o1" "ob") (.seq (satLit "oe" (e + 1)) (.seq (satLit "oc" (2 ^ d))
  (.seq (.assign "oa" (.lit 1)) (.seq (satPow "oa" "ob" "oi" "oe")
  (.ite (.lt (.div (.var "W") (.var "oc")) (.var "oa")) (.assign "ovf" (.lit 1)) .skip))))))))

theorem mxSeg_wvars (ar s l : String) : (mxSeg ar s l).wvars ⊆ ["mx", "ci"] := by
  intro y hy; simp [mxSeg, forUp, mxBody, Com.wvars] at hy ⊢; tauto

theorem mxSeg_warrs (ar s l : String) : (mxSeg ar s l).warrs = [] := by
  simp [mxSeg, forUp, mxBody, Com.warrs]

theorem guardChk_run {W e d a N : ℕ} {σ : Env} (hW : σ.vars "W" = W) (hW2 : 2 ≤ W)
    (ha : σ.vars "qa" = a) (hl : σ.vars "ql" = N) (hA : a + N ≤ (σ.arrs "OB").length)
    (hB : a + N ≤ W) (hv : ∀ v ∈ seg (σ.arrs "OB") a N, v ≤ W) :
    ∃ σ', Run (W + 1) (guardChk e d) σ σ' (N * 30 + 60 * (e + 1) + 30 * 2 ^ d + 200) ∧
      σ'.vars "ovf" = (if min ((N + maxEntry (seg (σ.arrs "OB") a N) + 1) ^ (e + 1)) W ≤
        W / min (2 ^ d) W then σ.vars "ovf" else 1) ∧
      (∀ y, y ∉ gVars → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.inp = σ.inp := by
  set M := maxEntry (seg (σ.arrs "OB") a N) with hM
  have hMW : M ≤ W := maxEntry_le (fun v hv' => hv v hv')
  obtain ⟨σ₁, r₁, h₁⟩ := mxSeg_run (B := W + 1) (ar := "OB") (s := "qa") (l := "ql") ha hl
    (by decide) (by decide) (by decide) (by decide) hA (by omega) (fun v hv' => by
      have := hv v hv'; omega)
  have f₁ : ∀ y, y ∉ ["mx", "ci"] → σ₁.vars y = σ.vars y :=
    fun y hy => r₁.frame_var_sub y (mxSeg_wvars _ _ _) hy
  have a₁ : σ₁.arrs = σ.arrs := r₁.frame_arrs_eqOn (mxSeg_warrs _ _ _)
  have o₁ : σ₁.out = σ.out := r₁.out_eq (by decide)
  have i₁ : σ₁.inp = σ.inp := r₁.frame_inp (by decide)
  have hW₁ : σ₁.vars "W" = W := by rw [f₁ _ (by decide), hW]
  have hl₁ : σ₁.vars "ql" = N := by rw [f₁ _ (by decide), hl]
  have r₂ := satAdd_run (B := W + 1) (x := "ql") (y := "mx") (z := "ob") hW₁ (by omega)
    (by omega) (by omega)
  set σ₂ := σ₁.setVar "ob" (min (σ₁.vars "ql" + σ₁.vars "mx") W) with hσ₂
  set σ₃ := σ₂.setVar "o1" 1 with hσ₃
  have r₃ : Run (W + 1) (.assign "o1" (.lit 1)) σ₂ σ₃ 2 := Run.assign (evalB_lit (by omega))
  have hW₃ : σ₃.vars "W" = W := by simp [hσ₃, hσ₂, hW₁]
  have r₄ := satAdd_run (B := W + 1) (x := "ob") (y := "o1") (z := "ob") hW₃ (by omega)
    (by simp [hσ₃, hσ₂]) (by simp [hσ₃]; omega)
  set σ₄ := σ₃.setVar "ob" (min (σ₃.vars "ob" + σ₃.vars "o1") W) with hσ₄
  have hob₄ : σ₄.vars "ob" = min (N + M + 1) W := by
    simp [hσ₄, hσ₃, hσ₂, hl₁, h₁]; omega
  have hW₄ : σ₄.vars "W" = W := by simp [hσ₄, hW₃]
  obtain ⟨σ₅, r₅, h₅, f₅, a₅, o₅, i₅⟩ := satLit_run (B := W + 1) (z := "oe") (by decide) (by omega)
    (by omega) (e + 1) σ₄ hW₄
  have hW₅ : σ₅.vars "W" = W := by rw [f₅ _ (by decide), hW₄]
  obtain ⟨σ₆, r₆, h₆, f₆, a₆, o₆, i₆⟩ := satLit_run (B := W + 1) (z := "oc") (by decide) (by omega)
    (by omega) (2 ^ d) σ₅ hW₅
  have hW₆ : σ₆.vars "W" = W := by rw [f₆ _ (by decide), hW₅]
  set σ₇ := σ₆.setVar "oa" 1 with hσ₇
  have r₇ : Run (W + 1) (.assign "oa" (.lit 1)) σ₆ σ₇ 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨σ₈, r₈, h₈, f₈, a₈⟩ := satPow_run (B := W + 1) (W := W) (a0 := 1) (b := N + M + 1)
    (N := min (e + 1) W) (acc := "oa") (base := "ob") (i := "oi") (n := "oe") (σ := σ₇)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hσ₇, hW₆]) (by omega) (by simp [hσ₇]; omega)
    (by simp only [hσ₇, vars_setVar]; simp; rw [f₆ _ (by decide), f₅ _ (by decide)]; exact hob₄)
    (by simp only [hσ₇, vars_setVar]; simp; rw [f₆ _ (by decide), h₅]) (by omega)
  rw [one_mul, pow_min_sat _ _ _ (by omega)] at h₈
  have hW₈ : σ₈.vars "W" = W := by rw [f₈ _ (by decide) (by decide)]; simp [hσ₇, hW₆]
  have hoc₈ : σ₈.vars "oc" = min (2 ^ d) W := by
    rw [f₈ _ (by decide) (by decide)]; simp [hσ₇, h₆]
  have hc : (Cond.lt (.div (.var "W") (.var "oc")) (.var "oa")).evalB (W + 1) σ₈ =
      some (decide (W / min (2 ^ d) W < min ((N + M + 1) ^ (e + 1)) W)) :=
    evalB_condLt (evalB_bin (ev_var hW₈ (by omega)) (ev_var hoc₈ (by omega))
      (by simp only [Bop.apply]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)))
      (ev_var h₈ (by omega))
  -- frames of the phases from σ to σ₈
  have fr : ∀ y, y ∉ ["mx", "ci", "ob", "o1", "oe", "oc", "oa", "oi"] → σ₈.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f₈ y (by tauto) (by tauto)]
    simp only [hσ₇, vars_setVar, if_neg hy.2.2.2.2.2.2.1]
    rw [f₆ y hy.2.2.2.2.2.1, f₅ y hy.2.2.2.2.1]
    simp only [hσ₄, hσ₃, hσ₂, vars_setVar, if_neg hy.2.2.1, if_neg hy.2.2.2.1]
    exact f₁ y (by simp; tauto)
  have fr' : ∀ y, y ∉ gVars → σ₈.vars y = σ.vars y := fun y hy => fr y (fun h => hy (by
    simp only [gVars, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto))
  have ar8 : σ₈.arrs = σ.arrs := by rw [a₈]; simp [hσ₇, a₆, a₅, hσ₄, hσ₃, hσ₂, a₁]
  have hcost : N * 30 + 10 + 10 + 2 + 10 + (30 * (e + 1) + 30) + (30 * 2 ^ d + 30) + 2 +
      (min (e + 1) W * 23 + 6) + 8 ≤ N * 30 + 60 * (e + 1) + 30 * 2 ^ d + 200 := by
    have : min (e + 1) W ≤ e + 1 := min_le_left _ _
    omega
  have o8 : σ₈.out = σ.out := by
    rw [r₈.out_eq (by decide)]; simp [hσ₇, o₆, o₅, hσ₄, hσ₃, hσ₂, o₁]
  have i8 : σ₈.inp = σ.inp := by
    rw [r₈.frame_inp (by decide)]; simp [hσ₇, i₆, i₅, hσ₄, hσ₃, hσ₂, i₁]
  by_cases hg : min ((N + M + 1) ^ (e + 1)) W ≤ W / min (2 ^ d) W
  · refine ⟨σ₈, ?_, by rw [if_pos hg]; exact fr "ovf" (by decide), fr', ar8, o8, i8⟩
    unfold guardChk
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq r₆
      (Run.seq r₇ (Run.seq r₈ (Run.ite_false (by rw [hc, decide_eq_false (not_lt.2 hg)])
      Run.skip))))))))).mono ?_
    simp only [Cond.size, Expr.size]; omega
  · refine ⟨σ₈.setVar "ovf" 1, ?_, by rw [if_neg hg]; simp,
      fun y hy => by
        have : y ≠ "ovf" := fun h => hy (by simp [gVars, h])
        simp [this, fr' y hy], by simp [ar8], by simp [o8], by simp [i8]⟩
    unfold guardChk
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq r₆
      (Run.seq r₇ (Run.seq r₈ (Run.ite_true (by rw [hc, decide_eq_true (not_le.1 hg)])
      (Run.assign (evalB_lit (by omega)))))))))))).mono ?_
    simp only [Cond.size, Expr.size]; omega

/-! ### The bound on the output entries -/

/-- `ovf := 1` unless every entry of the buffer is below `W / 32 / 32`. -/
def entChk : Com :=
  .seq (.assign "qz" (.lit 0)) (.seq (mxSeg "OB" "qz" "po")
    (.ite (.lt (.var "mx") (.div (.div (.var "W") (.lit 32)) (.lit 32))) .skip
      (.assign "ovf" (.lit 1))))

theorem entChk_run {W : ℕ} {σ : Env} {o : List ℕ} (hW : σ.vars "W" = W) (hW2 : 32 ≤ W)
    (hF : Filled "OB" "po" o σ) (hB : o.length ≤ W) (hv : ∀ v ∈ o, v ≤ W) :
    ∃ σ', Run (W + 1) entChk σ σ' (o.length * 30 + 30) ∧
      σ'.vars "ovf" = (if maxEntry o < W / 32 / 32 then σ.vars "ovf" else 1) ∧
      (∀ y, y ∉ ["qz", "mx", "ci", "ovf"] → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hA : 0 + o.length ≤ (σ.arrs "OB").length := by have := hF.length_le; omega
  have hseg : seg (σ.arrs "OB") 0 o.length = o := by
    apply List.ext_getElem
    · simp [seg]; omega
    · intro i h1 h2
      have := hF.get i h2
      simp only [seg, List.drop_zero, List.getElem_take]
      rw [List.getElem?_eq_getElem (by simp [seg] at h1; omega)] at this
      exact Option.some.inj this
  set σ₀ := σ.setVar "qz" 0 with hσ₀
  obtain ⟨σ₁, r₁, h₁⟩ := mxSeg_run (B := W + 1) (σ := σ₀) (ar := "OB") (s := "qz") (l := "po")
    (a := 0) (N := o.length) (by simp [hσ₀]) (by simp [hσ₀, hF.pos]) (by decide) (by decide)
    (by decide) (by decide) (by simpa [hσ₀] using hA) (by omega)
    (by simp only [hσ₀, arrs_setVar]; rw [hseg]; intro v hv'; have := hv v hv'; omega)
  simp only [hσ₀, arrs_setVar] at h₁; rw [hseg] at h₁
  have f₁ : ∀ y, y ∉ ["mx", "ci"] → σ₁.vars y = σ₀.vars y :=
    fun y hy => r₁.frame_var_sub y (mxSeg_wvars _ _ _) hy
  have a₁ : σ₁.arrs = σ.arrs := by rw [r₁.frame_arrs_eqOn (mxSeg_warrs _ _ _)]; simp [hσ₀]
  have o₁ : σ₁.out = σ.out := by rw [r₁.out_eq (by decide)]; simp [hσ₀]
  have i₁ : σ₁.inp = σ.inp := by rw [r₁.frame_inp (by decide)]; simp [hσ₀]
  have hW₁ : σ₁.vars "W" = W := by rw [f₁ _ (by decide)]; simp [hσ₀, hW]
  have hMW : maxEntry o ≤ W := maxEntry_le hv
  have hc : (Cond.lt (.var "mx") (.div (.div (.var "W") (.lit 32)) (.lit 32))).evalB (W + 1) σ₁ =
      some (decide (maxEntry o < W / 32 / 32)) :=
    evalB_condLt (ev_var h₁ (by omega)) (evalB_bin (evalB_bin (ev_var hW₁ (by omega))
      (evalB_lit (by omega)) (by simp only [Bop.apply]; omega)) (evalB_lit (by omega))
      (by simp only [Bop.apply]; omega))
  have fr : ∀ y, y ∉ ["qz", "mx", "ci", "ovf"] → σ₁.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f₁ y (by simp; tauto)]; simp [hσ₀, hy.1]
  by_cases hg : maxEntry o < W / 32 / 32
  · have hov : σ₁.vars "ovf" = σ.vars "ovf" := by rw [f₁ _ (by decide)]; simp [hσ₀]
    refine ⟨σ₁, ?_, by rw [if_pos hg, hov], fr, a₁, o₁, i₁⟩
    unfold entChk
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₁ (Run.ite_true
      (by rw [hc, decide_eq_true hg]) Run.skip))).mono ?_
    simp only [Cond.size, Expr.size]; omega
  · refine ⟨σ₁.setVar "ovf" 1, ?_, by rw [if_neg hg]; simp,
      fun y hy => by
        have : y ≠ "ovf" := fun h => hy (by simp [h])
        simp [this, fr y hy], by simp [a₁], by simp [o₁], by simp [i₁]⟩
    unfold entChk
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₁ (Run.ite_false
      (by rw [hc, decide_eq_false hg]) (Run.assign (evalB_lit (by omega)))))).mono ?_
    simp only [Cond.size, Expr.size]; omega

/-- A passed entry check bounds every entry of the output. -/
theorem ent_sound_arith {W v r e : ℕ} (hW1 : W + 1 = 2 ^ (v - r)) (h : e < W / 32 / 32) :
    e < 2 ^ (v - r - 10) := by
  rw [Nat.div_div_eq_div_mul] at h
  have hv : 10 ≤ v - r := by
    by_contra hh
    have : 2 ^ (v - r) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : W / (32 * 32) = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hsplit : 2 ^ (v - r) = 2 ^ (v - r - 10) * 1024 := by
    rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, ← pow_add]; congr 1; omega
  have : W / (32 * 32) < 2 ^ (v - r - 10) := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
  omega

/-! ### Pushing scalars and literals -/

theorem evalsTo_vars {B : ℕ} {τ : Env} : ∀ (xs : List String), "po" ∉ xs →
    (∀ x ∈ xs, τ.vars x < B) → EvalsTo B "OB" "po" τ (xs.map Expr.var) (xs.map τ.vars)
  | [], _, _ => fun _ _ _ => by simp
  | x :: xs, hx, hB => fun τ' hv ha => by
      simp only [List.map_cons, List.forall₂_cons]
      have hx' : x ≠ "po" := fun h => hx (by simp [h])
      refine ⟨ev_var (hv x hx') (hB x (by simp)), ?_⟩
      exact evalsTo_vars xs (fun h => hx (by simp [h])) (fun y hy => hB y (by simp [hy])) τ' hv ha

theorem evalsTo_lits {B : ℕ} {τ : Env} : ∀ (l : List ℕ), (∀ v ∈ l, v < B) →
    EvalsTo B "OB" "po" τ (l.map Expr.lit) l
  | [], _ => fun _ _ _ => by simp
  | v :: l, hB => fun τ' hv ha => by
      simp only [List.map_cons, List.forall₂_cons]
      exact ⟨evalB_lit (hB v (by simp)), evalsTo_lits l (fun y hy => hB y (by simp [hy])) τ' hv ha⟩

/-! ### The head -/

/-- The scalars of the state, before the lengths of the three words. -/
def scN : List String := ["s0", "gn", "sm", "off", "rk", "ck", "ct", "cv", "cP", "cQ", "cs"]

/-- The scalars of the state, with the lengths of the three words. -/
def scA : List String := scN ++ ["pg", "pf", "lp"]

/-- The state: the scalars, the lengths, then the words `gw`, `fw`, `lw`. -/
def stW (sc : List ℕ) (gw fw lw : List ℕ) : List ℕ :=
  sc ++ [gw.length, fw.length, lw.length] ++ gw ++ fw ++ lw

/-- The head: tag, state length, window length, state. -/
def hdW (tag k : ℕ) (st : List ℕ) : List ℕ := tag :: st.length :: k :: st

/-- Write the head into `OB`. -/
def wrHd : Com :=
  .seq (push1 "OB" "po" (.var "otg")) (.seq (push1 "OB" "po"
    (.add (.lit 14) (.add (.var "pg") (.add (.var "pf") (.var "lp")))))
  (.seq (push1 "OB" "po" (.var "okk")) (.seq (pushL "OB" "po" (scA.map Expr.var))
  (.seq (.assign "qz" (.lit 0)) (.seq (cpSeg "GW" "qz" "pg") (.seq (cpSeg "FW" "qz" "pf")
    (cpSeg "lo" "qz" "lp")))))))

theorem length_stW (sc gw fw lw : List ℕ) :
    (stW sc gw fw lw).length = sc.length + 3 + gw.length + fw.length + lw.length := by
  simp [stW]; omega

theorem cpSeg_wvars (src s l : String) : (cpSeg src s l).wvars ⊆ ["ci", "po"] := by
  intro y hy; simp [cpSeg, forUp, push1, Com.wvars] at hy ⊢; tauto

theorem cpSeg_warrs (src s l : String) : (cpSeg src s l).warrs ⊆ ["OB"] := by
  intro y hy; simp [cpSeg, forUp, push1, Com.warrs] at hy ⊢; tauto

theorem seg_filled {a pv : String} {l : List ℕ} {τ : Env} (h : Filled a pv l τ) :
    seg (τ.arrs a) 0 l.length = l := by
  apply List.ext_getElem
  · have := h.length_le; simp [seg]; omega
  · intro i h1 h2
    have := h.get i h2
    simp only [seg, List.drop_zero, List.getElem_take]
    rw [List.getElem?_eq_getElem (by simp [seg] at h1; omega)] at this
    exact Option.some.inj this

/-- One copy of a filled word onto the buffer, with the frames. -/
theorem cpSeg_filled {W : ℕ} {src pv : String} {σ : Env} {pre l : List ℕ}
    (hsrc : src ≠ "OB") (hpv : pv ≠ "po") (hpv' : pv ≠ "ci") (hz : σ.vars "qz" = 0)
    (hF : Filled "OB" "po" pre σ) (hl : Filled src pv l σ)
    (hcap : pre.length + l.length ≤ (σ.arrs "OB").length) (hB : pre.length + l.length ≤ W)
    (hv : ∀ v ∈ l, v ≤ W) :
    ∃ σ', Run (W + 1) (cpSeg src "qz" pv) σ σ' (l.length * 20 + 6) ∧
      Filled "OB" "po" (pre ++ l) σ' ∧ (∀ y, y ≠ "ci" → y ≠ "po" → σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ "OB" → σ'.arrs b = σ.arrs b) ∧ (σ'.arrs "OB").length = (σ.arrs "OB").length ∧
      σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hA : 0 + l.length ≤ (σ.arrs src).length := by have := hl.length_le; omega
  obtain ⟨σ', r, F⟩ := cpSeg_run (B := W + 1) (src := src) (s := "qz") (l := pv) (pre := pre)
    (a := 0) (N := l.length) hsrc hz hl.pos (by decide) (by decide) hpv hpv' hF hA hcap (by omega)
    (by omega) (by rw [seg_filled hl]; intro v hv'; have := hv v hv'; omega)
  rw [seg_filled hl] at F
  refine ⟨σ', r, F, fun y h1 h2 => r.frame_var_sub y (cpSeg_wvars _ _ _) (by simp; tauto),
    fun b hb => r.frame_arr b (fun h => hb (by simpa using cpSeg_warrs _ _ _ h)),
    run_length_arrs r "OB", r.out_eq (by simp [cpSeg, forUp, push1, Com.NoWrite]),
    r.frame_inp (by simp [cpSeg, forUp, push1, Com.reads])⟩

theorem scA_map {σ : Env} {gw fw lw : List ℕ} (hg : σ.vars "pg" = gw.length)
    (hf : σ.vars "pf" = fw.length) (hl : σ.vars "lp" = lw.length) :
    scA.map σ.vars = scN.map σ.vars ++ [gw.length, fw.length, lw.length] := by
  simp [scA, hg, hf, hl]

theorem wrHd_run {W tag k : ℕ} {σ : Env} {gw fw lw : List ℕ}
    (hF : Filled "OB" "po" [] σ) (hGW : Filled "GW" "pg" gw σ) (hFW : Filled "FW" "pf" fw σ)
    (hlo : Filled "lo" "lp" lw σ) (htg : σ.vars "otg" = tag) (hk : σ.vars "okk" = k)
    (hsc : ∀ x ∈ scN, σ.vars x ≤ W) (htk : tag ≤ W) (hkW : k ≤ W)
    (hcap : W + 1 ≤ (σ.arrs "OB").length)
    (hB : 20 + gw.length + fw.length + lw.length ≤ W) (hv : ∀ v ∈ gw ++ fw ++ lw, v ≤ W) :
    ∃ σ', Run (W + 1) wrHd σ σ' (20 * (gw.length + fw.length + lw.length) + 200) ∧
      Filled "OB" "po" (hdW tag k (stW (scN.map σ.vars) gw fw lw)) σ' ∧
      (∀ y, y ≠ "ci" → y ≠ "po" → y ≠ "qz" → σ'.vars y = σ.vars y) ∧ σ'.vars "qz" = 0 ∧
      (∀ b, b ≠ "OB" → σ'.arrs b = σ.arrs b) ∧ (σ'.arrs "OB").length = (σ.arrs "OB").length ∧
      σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hgl := hGW.pos
  have hfl := hFW.pos
  have hll := hlo.pos
  -- the three single pushes
  obtain ⟨τ₁, r₁, F₁, v₁, a₁, l₁, o₁, i₁⟩ := push1_run (B := W + 1) (e := .var "otg") hF
    (ev_var htg (by omega)) (by simp; omega) (by simp; omega)
  have hℓ : (Expr.add (.lit 14) (.add (.var "pg") (.add (.var "pf") (.var "lp")))).evalB (W + 1) τ₁ =
      some (14 + (gw.length + (fw.length + lw.length))) :=
    ev_add (evalB_lit (by omega)) (ev_add (ev_var (by rw [v₁ _ (by decide), hgl]) (by omega))
      (ev_add (ev_var (by rw [v₁ _ (by decide), hfl]) (by omega))
        (ev_var (by rw [v₁ _ (by decide), hll]) (by omega)) (by omega)) (by omega)) (by omega)
  obtain ⟨τ₂, r₂, F₂, v₂, a₂, l₂, o₂, i₂⟩ := push1_run F₁ hℓ (by simp [l₁]; omega) (by simp; omega)
  obtain ⟨τ₃, r₃, F₃, v₃, a₃, l₃, o₃, i₃⟩ := push1_run (B := W + 1) (e := .var "okk") F₂
    (ev_var (by rw [v₂ _ (by decide), v₁ _ (by decide), hk]) (by omega)) (by simp [l₁, l₂]; omega)
    (by simp; omega)
  have v₁₃ : ∀ y, y ≠ "po" → τ₃.vars y = σ.vars y := fun y hy => by
    rw [v₃ y hy, v₂ y hy, v₁ y hy]
  have a₁₃ : ∀ b, b ≠ "OB" → τ₃.arrs b = σ.arrs b := fun b hb => by
    rw [a₃ b hb, a₂ b hb, a₁ b hb]
  have hl₁₃ : (τ₃.arrs "OB").length = (σ.arrs "OB").length := by rw [l₃, l₂, l₁]
  -- the scalars of the state
  have hev : EvalsTo (W + 1) "OB" "po" τ₃ (scA.map Expr.var) (scA.map τ₃.vars) :=
    evalsTo_vars scA (by decide) (fun x hx => by
      rw [v₁₃ x (by intro h; subst h; revert hx; decide)]
      simp only [scA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | rfl | rfl
      · have := hsc x hx; omega
      all_goals omega)
  have hscA : scA.map τ₃.vars = scN.map σ.vars ++ [gw.length, fw.length, lw.length] := by
    rw [scA_map (by rw [v₁₃ _ (by decide), hgl]) (by rw [v₁₃ _ (by decide), hfl])
      (by rw [v₁₃ _ (by decide), hll])]
    congr 1
    exact List.map_congr_left fun x hx => v₁₃ x (by intro h; subst h; revert hx; decide)
  have hlenN : (scN.map σ.vars).length = 11 := by simp [scN]
  obtain ⟨τ₄, r₄, F₄, v₄, a₄, l₄, o₄, i₄⟩ := pushL_run F₃ hev (by simp [hl₁₃, scA, scN]; omega)
    (by simp [scA, scN]; omega)
  rw [hscA] at F₄
  set τ₅ := τ₄.setVar "qz" 0 with hτ₅
  have r₅ : Run (W + 1) (.assign "qz" (.lit 0)) τ₄ τ₅ 2 := Run.assign (evalB_lit (by omega))
  have F₅ : Filled "OB" "po" ([] ++ [tag] ++ [14 + (gw.length + (fw.length + lw.length))] ++ [k] ++
      (scN.map σ.vars ++ [gw.length, fw.length, lw.length])) τ₅ := F₄.setVar (by decide) 0
  have v₁₅ : ∀ y, y ≠ "po" → y ≠ "qz" → τ₅.vars y = σ.vars y := fun y hy hz => by
    simp only [hτ₅, vars_setVar, if_neg hz]; rw [v₄ y hy, v₁₃ y hy]
  have a₁₅ : ∀ b, b ≠ "OB" → τ₅.arrs b = σ.arrs b := fun b hb => by
    simp only [hτ₅, arrs_setVar]; rw [a₄ b hb, a₁₃ b hb]
  have hl₁₅ : (τ₅.arrs "OB").length = (σ.arrs "OB").length := by simp [hτ₅, l₄, hl₁₃]
  set pre₅ := [] ++ [tag] ++ [14 + (gw.length + (fw.length + lw.length))] ++ [k] ++
      (scN.map σ.vars ++ [gw.length, fw.length, lw.length]) with hpre₅
  have hpl : pre₅.length = 17 := by simp [hpre₅, hlenN]
  obtain ⟨τ₆, r₆, F₆, v₆, a₆, l₆, o₆, i₆⟩ := cpSeg_filled (W := W) (src := "GW") (pv := "pg")
    (by decide) (by decide) (by decide) (by simp [hτ₅]) F₅
    (hGW.congr (by rw [v₁₅ _ (by decide) (by decide)]) (by rw [a₁₅ _ (by decide)]))
    (by rw [hl₁₅, hpl]; omega) (by rw [hpl]; omega) (fun v hv' => hv v (by simp [hv']))
  obtain ⟨τ₇, r₇, F₇, v₇, a₇, l₇, o₇, i₇⟩ := cpSeg_filled (W := W) (src := "FW") (pv := "pf")
    (by decide) (by decide) (by decide) (by rw [v₆ _ (by decide) (by decide)]; simp [hτ₅]) F₆
    (hFW.congr (by rw [v₆ _ (by decide) (by decide), v₁₅ _ (by decide) (by decide)])
      (by rw [a₆ _ (by decide), a₁₅ _ (by decide)]))
    (by rw [l₆, hl₁₅]; simp [hpl]; omega) (by simp [hpl]; omega)
    (fun v hv' => hv v (by simp [hv']))
  obtain ⟨τ₈, r₈, F₈, v₈, a₈, l₈, o₈, i₈⟩ := cpSeg_filled (W := W) (src := "lo") (pv := "lp")
    (by decide) (by decide) (by decide)
    (by rw [v₇ _ (by decide) (by decide), v₆ _ (by decide) (by decide)]; simp [hτ₅]) F₇
    (hlo.congr (by rw [v₇ _ (by decide) (by decide), v₆ _ (by decide) (by decide),
        v₁₅ _ (by decide) (by decide)])
      (by rw [a₇ _ (by decide), a₆ _ (by decide), a₁₅ _ (by decide)]))
    (by rw [l₇, l₆, hl₁₅]; simp [hpl]; omega) (by simp [hpl]; omega)
    (fun v hv' => hv v (by simp [hv']))
  refine ⟨τ₈, ?_, ?_, fun y h1 h2 h3 => ?_, ?_, fun b hb => ?_, by rw [l₈, l₇, l₆, hl₁₅], ?_, ?_⟩
  · unfold wrHd
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq r₆
      (Run.seq r₇ r₈))))))).mono ?_
    simp [Expr.size, scA, scN]; omega
  · convert F₈ using 1
    simp [hdW, stW, hpre₅, length_stW, hlenN]; omega
  · rw [v₈ y h1 h2, v₇ y h1 h2, v₆ y h1 h2, v₁₅ y h2 h3]
  · rw [v₈ _ (by decide) (by decide), v₇ _ (by decide) (by decide), v₆ _ (by decide) (by decide)]
    simp [hτ₅]
  · rw [a₈ b hb, a₇ b hb, a₆ b hb, a₁₅ b hb]
  · rw [o₈, o₇, o₆]; simp [hτ₅, o₄, o₃, o₂, o₁]
  · rw [i₈, i₇, i₆]; simp [hτ₅, i₄, i₃, i₂, i₁]

/-! ### Frames of the buffer phases -/

/-- `τ'` agrees with `τ` outside the scalars `xs` and the buffer `OB`,
the buffer keeps its length, and the tapes are unchanged. -/
structure OFr (τ τ' : Env) (xs : List String) : Prop where
  vars : ∀ y, y ∉ xs → τ'.vars y = τ.vars y
  arrs : ∀ b, b ≠ "OB" → τ'.arrs b = τ.arrs b
  len : (τ'.arrs "OB").length = (τ.arrs "OB").length
  out : τ'.out = τ.out
  inp : τ'.inp = τ.inp

theorem OFr.trans {τ τ' τ'' : Env} {xs ys : List String} (h : OFr τ τ' xs) (h' : OFr τ' τ'' ys) :
    OFr τ τ'' (xs ++ ys) :=
  ⟨fun y hy => by rw [h'.vars y (fun hh => hy (by simp [hh])), h.vars y (fun hh => hy (by simp [hh]))],
    fun b hb => by rw [h'.arrs b hb, h.arrs b hb], by rw [h'.len, h.len], by rw [h'.out, h.out],
    by rw [h'.inp, h.inp]⟩

theorem OFr.mono {τ τ' : Env} {xs ys : List String} (h : OFr τ τ' xs) (hs : xs ⊆ ys) :
    OFr τ τ' ys := ⟨fun y hy => h.vars y (fun hh => hy (hs hh)), h.arrs, h.len, h.out, h.inp⟩

theorem OFr.setVar (τ : Env) (x : String) (v : ℕ) : OFr τ (τ.setVar x v) [x] :=
  ⟨fun y hy => by simp at hy; simp [hy], fun _ _ => rfl, rfl, rfl, rfl⟩

theorem OFr.refl (τ : Env) : OFr τ τ [] := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Append one value. -/
theorem push1_ofr {W : ℕ} {e : Expr} {l : List ℕ} {τ : Env} {v : ℕ}
    (h : Filled "OB" "po" l τ) (he : e.evalB (W + 1) τ = some v)
    (hcap : l.length + 1 ≤ (τ.arrs "OB").length) (hB : l.length + 1 ≤ W) :
    ∃ τ', Run (W + 1) (push1 "OB" "po" e) τ τ' (6 + e.size) ∧ Filled "OB" "po" (l ++ [v]) τ' ∧
      OFr τ τ' ["po"] := by
  obtain ⟨τ', r, F, fv, fa, fl, fo, fi⟩ := push1_run h he (by omega) (by omega)
  exact ⟨τ', r, F, ⟨fun y hy => fv y (by simpa using hy), fa, fl, fo, fi⟩⟩

theorem sum_size_lits (l : List ℕ) : (List.map Expr.size (List.map Expr.lit l)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Expr.size, List.length_cons]; omega

theorem sum_size_vars (l : List String) :
    (List.map Expr.size (List.map Expr.var l)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Expr.size, List.length_cons]; omega

/-- Append literals. -/
def pushLits (l : List ℕ) : Com := pushL "OB" "po" (l.map Expr.lit)

theorem pushLits_run {W : ℕ} {l pre : List ℕ} {τ : Env} (h : Filled "OB" "po" pre τ)
    (hl : ∀ v ∈ l, v ≤ W) (hcap : pre.length + l.length ≤ (τ.arrs "OB").length)
    (hB : pre.length + l.length ≤ W) :
    ∃ τ', Run (W + 1) (pushLits l) τ τ' (1 + 8 * l.length) ∧ Filled "OB" "po" (pre ++ l) τ' ∧
      OFr τ τ' ["po"] := by
  obtain ⟨τ', r, F, fv, fa, fl, fo, fi⟩ := pushL_run h
    (evalsTo_lits (B := W + 1) l (fun v hv => by have := hl v hv; omega)) (by simpa using hcap)
    (by simp; omega)
  refine ⟨τ', r.mono ?_, F, ⟨fun y hy => fv y (by simpa using hy), fa, fl, fo, fi⟩⟩
  rw [sum_size_lits l]; simp only [List.length_map]; omega

/-- Append the values of scalars. -/
theorem pushVars_run {W : ℕ} {xs : List String} {pre : List ℕ} {τ : Env} (hpo : "po" ∉ xs)
    (h : Filled "OB" "po" pre τ) (hx : ∀ x ∈ xs, τ.vars x ≤ W)
    (hcap : pre.length + xs.length ≤ (τ.arrs "OB").length) (hB : pre.length + xs.length ≤ W) :
    ∃ τ', Run (W + 1) (pushL "OB" "po" (xs.map Expr.var)) τ τ' (1 + 8 * xs.length) ∧
      Filled "OB" "po" (pre ++ xs.map τ.vars) τ' ∧ OFr τ τ' ["po"] := by
  obtain ⟨τ', r, F, fv, fa, fl, fo, fi⟩ := pushL_run h
    (evalsTo_vars (B := W + 1) xs hpo (fun x hx' => by have := hx x hx'; omega))
    (by simpa using hcap) (by simp; omega)
  refine ⟨τ', r.mono ?_, F, ⟨fun y hy => fv y (by simpa using hy), fa, fl, fo, fi⟩⟩
  rw [sum_size_vars xs]; simp only [List.length_map]; omega

/-- Copy a segment, with the frames. -/
theorem cpSeg_ofr {W : ℕ} {src s l : String} {σ : Env} {pre : List ℕ} {a N : ℕ}
    (hsrc : src ≠ "OB") (hs : σ.vars s = a) (hl : σ.vars l = N)
    (hs1 : s ≠ "po") (hs2 : s ≠ "ci") (hl1 : l ≠ "po") (hl2 : l ≠ "ci")
    (hF : Filled "OB" "po" pre σ) (hA : a + N ≤ (σ.arrs src).length)
    (hcap : pre.length + N ≤ (σ.arrs "OB").length) (hB : a + N ≤ W) (hB' : pre.length + N ≤ W)
    (hv : ∀ v ∈ seg (σ.arrs src) a N, v ≤ W) :
    ∃ σ', Run (W + 1) (cpSeg src s l) σ σ' (N * 20 + 6) ∧
      Filled "OB" "po" (pre ++ seg (σ.arrs src) a N) σ' ∧ OFr σ σ' ["ci", "po"] := by
  obtain ⟨σ', r, F⟩ := cpSeg_run (B := W + 1) hsrc hs hl hs1 hs2 hl1 hl2 hF hA hcap (by omega)
    (by omega) (fun v hv' => by have := hv v hv'; omega)
  exact ⟨σ', r, F, ⟨fun y hy => r.frame_var_sub y (cpSeg_wvars _ _ _) hy,
    fun b hb => r.frame_arr b (fun h => hb (by simpa using cpSeg_warrs _ _ _ h)),
    run_length_arrs r "OB", r.out_eq (by simp [cpSeg, forUp, push1, Com.NoWrite]),
    r.frame_inp (by simp [cpSeg, forUp, push1, Com.reads])⟩⟩

theorem seg_of_filled {a pv : String} {A M C : List ℕ} {τ : Env} (h : Filled a pv (A ++ M ++ C) τ) :
    seg (τ.arrs a) A.length M.length = M := by
  have hl := h.length_le
  simp only [List.length_append] at hl
  apply List.ext_getElem
  · simp [seg]; omega
  · intro i h1 h2
    have := h.get (A.length + i) (by simp; omega)
    simp only [seg, List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega)] at this
    rw [Option.some.inj this]
    simp [List.getElem_append, h2]

/-! ### The query -/

/-- A bound on the lengths and entries of the fixed queries and answers. -/
noncomputable def dK : ℕ :=
  qM0.length + qR0.length + qE0.length + yM0.length + zR0.length + uE0.length +
    maxEntry (qM0 ++ qR0 ++ qE0 ++ yM0 ++ zR0 ++ uE0) + 10

theorem le_dK_of_mem {v : ℕ} (h : v ∈ qM0 ∨ v ∈ qR0 ∨ v ∈ qE0) : v ≤ dK := by
  have : v ≤ maxEntry (qM0 ++ qR0 ++ qE0 ++ yM0 ++ zR0 ++ uE0) :=
    le_maxEntry (by simp only [List.mem_append]; tauto)
  unfold dK; omega

theorem lens_le_dK : qM0.length + qR0.length + qE0.length + 10 ≤ dK := by unfold dK; omega

attribute [irreducible] dK

/-- The query to the callee that does the work, by the kind `ck` of the call:
`0` merge (the jobs `tr`), `1` resolve, `2` evaluation (on the tree `tr`),
otherwise the fixed merge query. -/
noncomputable def realQ (ck P Q sg : ℕ) (gw fw tr lw : List ℕ) : List ℕ :=
  if ck = 0 then tr else if ck = 1 then gw ++ [P, Q, sg] ++ fw
  else if ck = 2 then tr ++ lw else qM0

/-- The query to the callee. -/
noncomputable def qW (ck P Q sg : ℕ) (gw fw tr lw : List ℕ) : List ℕ :=
  if ck = 0 then swIn (realQ ck P Q sg gw fw tr lw) qR0 qE0
  else if ck = 1 then swIn qM0 (realQ ck P Q sg gw fw tr lw) qE0
  else if ck = 2 then swIn qM0 qR0 (realQ ck P Q sg gw fw tr lw) else swIn qM0 qR0 qE0

theorem seg_filled_sub {a pv : String} {l : List ℕ} {τ : Env} (h : Filled a pv l τ) {s N : ℕ}
    (hs : s + N ≤ l.length) : seg (τ.arrs a) s N = seg l s N := by
  have hl := h.length_le
  apply List.ext_getElem
  · simp [seg]; omega
  · intro i h1 h2
    have h2' := h2
    simp only [seg, List.length_take, List.length_drop] at h2'
    have := h.get (s + i) (by omega)
    simp only [seg, List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this

theorem mem_seg {l : List ℕ} {s N v : ℕ} (h : v ∈ seg l s N) : v ∈ l :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-! ### The jobs of a merge step -/

open Lax185574.WordEncoding Lax185574.TypeTrees in
/-- The frames of the jobs of a merge step on the trees `ts` with the
colors `P, Q`: the length of a job, then the tree and the two colors. -/
noncomputable def jbF (ts : List TypeTree) (P Q : ℕ) : List (List ℕ) :=
  ts.map fun t => ((toWord t).length + 2) :: (toWord t ++ [P, Q])

open Lax185574.WordEncoding Lax185574.TypeTrees in
/-- The word of the jobs of a merge step on the trees `ts`. -/
noncomputable def jbW (ts : List TypeTree) (P Q : ℕ) : List ℕ := ts.length :: (jbF ts P Q).flatten

open Lax185574.WordEncoding Lax185574.TypeTrees in
theorem length_jbF (ts : List TypeTree) (P Q : ℕ) :
    (jbF ts P Q).flatten.length = (ts.map toWord).flatten.length + 3 * ts.length := by
  induction ts with
  | nil => simp [jbF]
  | cons t ts ih =>
    simp only [jbF, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih]; simp; ring

open Lax185574.WordEncoding Lax185574.TypeTrees in
theorem length_le_flatten_trees (ts : List TypeTree) : 3 * ts.length ≤ (ts.map toWord).flatten.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have : 3 ≤ (toWord t).length := by rw [toWord_typeTree_split]; simp
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]; omega

open Lax185574.WordEncoding Lax185574.TypeTrees in
theorem length_jbW {ts : List TypeTree} {fw : List ℕ} (P Q : ℕ)
    (hfw : fw = ts.length :: (ts.map toWord).flatten) :
    (jbW ts P Q).length = fw.length + 3 * ts.length ∧ 3 * ts.length + 1 ≤ fw.length := by
  have := length_le_flatten_trees ts
  subst hfw; simp only [jbW, List.length_cons, length_jbF]; omega

open Lax185574.WordEncoding Lax185574.TypeTrees in
theorem mem_jbW {ts : List TypeTree} {fw : List ℕ} {P Q W : ℕ}
    (hfw : fw = ts.length :: (ts.map toWord).flatten) (hv : ∀ v ∈ fw, v ≤ W) (hPW : P ≤ W)
    (hQW : Q ≤ W) (hl : fw.length + 2 ≤ W) : ∀ v ∈ jbW ts P Q, v ≤ W := by
  have hfl : (ts.map toWord).flatten.length + 1 = fw.length := by rw [hfw]; simp
  intro v hv'
  simp only [jbW, List.mem_cons, jbF, List.mem_flatten, List.mem_map] at hv'
  rcases hv' with rfl | ⟨_, ⟨t, ht, rfl⟩, hm⟩
  · have := length_le_flatten_trees ts; omega
  · have htw : (toWord t).length ≤ (ts.map toWord).flatten.length :=
      (List.sublist_flatten_of_mem (List.mem_map_of_mem ht)).length_le
    have hmf : ∀ u ∈ toWord t, u ∈ fw := fun u hu => by
      rw [hfw]; exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_map_of_mem ht, hu⟩)
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | hm | rfl | rfl
    · omega
    · exact hv v (hmf v hm)
    · exact hPW
    · exact hQW

theorem skipT_ofr {B : ℕ} {ar : String} {τ τ' : Env} {K : ℕ} (r : Run B (skipT ar) τ τ' K) :
    OFr τ τ' ["e3", "y", "e1", "e2"] :=
  ⟨fun y hy => r.frame_var_sub y (by intro z hz; simp [skipT, skipL, Com.wvars] at hz ⊢; tauto) hy,
    fun b _ => r.frame_arr b (by simp [skipT, skipL, Com.warrs]), run_length_arrs r "OB",
    r.out_eq (by simp [skipT, skipL, Com.NoWrite]), r.frame_inp (by simp [skipT, skipL, Com.reads])⟩

/-- One job: the length of the tree at `y` in `FW` plus two, the tree,
and the two colors. -/
def jbOne : Com :=
  .seq (.assign "tS" (.var "y")) (.seq (skipT "FW") (.seq (.assign "tE" (.sub (.var "y") (.var "tS")))
  (.seq (push1 "OB" "po" (.add (.var "tE") (.lit 2))) (.seq (cpSeg "FW" "tS" "tE")
  (pushL "OB" "po" [.var "cP", .var "cQ"])))))

/-- The merge query: the jobs of the trees of `FW`. -/
noncomputable def wq0 : Com :=
  .seq (push1 "OB" "po" (.add (.var "pf") (.mul (.lit 3) (.var "gn"))))
  (.seq (pushLits [qR0.length, qE0.length])
  (.seq (.assign "qa" (.var "po")) (.seq (.assign "ql" (.add (.var "pf") (.mul (.lit 3) (.var "gn"))))
  (.seq (push1 "OB" "po" (.var "gn")) (.seq (.assign "y" (.lit 1))
  (.seq (forUp "e4" (.var "gn") jbOne) (.seq (pushLits qR0) (pushLits qE0))))))))

open Lax185574.WordEncoding Lax185574.TypeTrees in
set_option maxHeartbeats 1000000 in
theorem jbOne_run {W P Q k : ℕ} {ts : List TypeTree} {X R pre : List ℕ} {τ : Env}
    (hk : k < ts.length) (hX : τ.arrs "FW" = X) (hXd : X.drop 1 = (ts.map toWord).flatten ++ R)
    (hy : τ.vars "y" = 1 + ((ts.map toWord).take k).flatten.length)
    (hF : Filled "OB" "po" (pre ++ ((jbF ts P Q).take k).flatten) τ)
    (hP : τ.vars "cP" = P) (hQ : τ.vars "cQ" = Q) (hcap : W + 1 ≤ (τ.arrs "OB").length)
    (hB : pre.length + 4 * (ts.map toWord).flatten.length + 10 ≤ W)
    (hv : ∀ v ∈ (ts.map toWord).flatten, v ≤ W) (hPW : P ≤ W) (hQW : Q ≤ W) :
    ∃ τ', Run (W + 1) jbOne τ τ' (100 * (toWord ts[k]).length + 100) ∧
      τ'.vars "y" = 1 + ((ts.map toWord).take (k + 1)).flatten.length ∧
      Filled "OB" "po" (pre ++ ((jbF ts P Q).take (k + 1)).flatten) τ' ∧
      OFr τ τ' ["tS", "e3", "y", "e1", "e2", "tE", "po", "ci"] := by
  have hkl : k < (ts.map toWord).length := by simp; omega
  have hkj : k < (jbF ts P Q).length := by simp [jbF]; omega
  have hg : (ts.map toWord).getD k [] = toWord ts[k] := by
    rw [List.getD_eq_getElem _ _ hkl]; simp
  have hjg : (jbF ts P Q).getD k [] = ((toWord ts[k]).length + 2) :: (toWord ts[k] ++ [P, Q]) := by
    rw [List.getD_eq_getElem _ _ hkj]; simp [jbF]
  have hd := drop_flatten_take (p := 1) hXd hkl
  rw [hg] at hd
  have hle := flatten_take_add_le (ts.map toWord) hkl
  rw [hg] at hle
  have hjle := flatten_take_add_le (jbF ts P Q) hkj
  rw [hjg] at hjle
  simp only [List.length_cons, List.length_append, List.length_nil] at hjle
  have hjF := length_jbF ts P Q
  have h3 := length_le_flatten_trees ts
  have hFl := hF.length_le
  have htk1 := flatten_take_succ (ts.map toWord) hkl
  have hjk1 := flatten_take_succ (jbF ts P Q) hkj
  rw [hg] at htk1
  rw [hjg] at hjk1
  obtain ⟨p, hp⟩ : ∃ p, p = 1 + ((ts.map toWord).take k).flatten.length := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = (toWord ts[k]).length := ⟨_, rfl⟩
  rw [← hp] at hd hy
  -- tS
  have r₁ : Run (W + 1) (.assign "tS" (.var "y")) τ (τ.setVar "tS" p) 2 :=
    Run.assign (ev_var hy (by omega))
  have f₁ := OFr.setVar τ "tS" p
  -- skip the tree
  have hwv : ∀ v ∈ toWord ts[k], v < W + 1 := fun v h => by
    have := hv v (List.mem_flatten.2 ⟨toWord ts[k], List.mem_map_of_mem (List.getElem_mem hk), h⟩)
    omega
  obtain ⟨τ₂, r₂, hy₂⟩ := skipT_run' (B := W + 1) (ar := "FW") (X := X) (p := p) (t := ts[k])
    (r := ((ts.map toWord).drop (k + 1)).flatten ++ R) (τ := τ.setVar "tS" p) (by simp [hX])
    (by simp [hy]) hd (by omega) hwv
  rw [← hL] at hy₂ r₂
  have f₂ := skipT_ofr r₂
  have f₁₂ := f₁.trans f₂
  have hOB₂ : τ₂.arrs "OB" = τ.arrs "OB" := by
    rw [r₂.frame_arr "OB" (by simp [skipT, skipL, Com.warrs])]; simp
  have htS₂ : τ₂.vars "tS" = p := by rw [f₂.vars "tS" (by decide)]; simp
  -- tE
  have r₃ : Run (W + 1) (.assign "tE" (.sub (.var "y") (.var "tS"))) τ₂ (τ₂.setVar "tE" (p + L - p)) 4 :=
    (Run.assign (ev_sub (ev_var hy₂ (by omega)) (ev_var htS₂ (by omega)) (by omega))).mono
      (by simp [Expr.size])
  rw [show p + L - p = L by omega] at r₃
  set τ₃ := τ₂.setVar "tE" L with hτ₃
  have f₁₃ := f₁₂.trans (OFr.setVar τ₂ "tE" L)
  have hlj : ((jbF ts P Q).take k).flatten.length + L + 3 ≤ (jbF ts P Q).flatten.length := by
    rw [hL]; omega
  -- push the length
  have F₃ : Filled "OB" "po" (pre ++ ((jbF ts P Q).take k).flatten) τ₃ :=
    hF.congr (f₁₃.vars _ (by decide)) (by simp [hτ₃, hOB₂])
  obtain ⟨τ₄, r₄, F₄, f₄⟩ := push1_ofr (W := W) (e := .add (.var "tE") (.lit 2)) (v := L + 2) F₃
    (ev_add (ev_var (v := L) (by simp [hτ₃]) (by omega)) (evalB_lit (by omega)) (by omega))
    (by rw [f₁₃.len, List.length_append]; omega) (by rw [List.length_append]; omega)
  -- copy the tree
  have hX₄ : τ₄.arrs "FW" = X := by rw [f₄.arrs _ (by decide), f₁₃.arrs _ (by decide), hX]
  have hseg : seg (τ₄.arrs "FW") p L = toWord ts[k] := by
    rw [hX₄, seg, hd, hL, List.take_left' rfl]
  have hL3 : 3 ≤ L := by rw [hL, toWord_typeTree_split]; simp
  have hXl : p + L ≤ X.length := by
    have := congrArg List.length hd; simp only [List.length_drop, List.length_append] at this; omega
  obtain ⟨τ₅, r₅, F₅, f₅⟩ := cpSeg_ofr (W := W) (src := "FW") (s := "tS") (l := "tE") (a := p) (N := L)
    (by decide) (by rw [f₄.vars _ (by decide)]; simp [hτ₃, htS₂])
    (by rw [f₄.vars _ (by decide)]; simp [hτ₃]) (by decide) (by decide) (by decide) (by decide) F₄
    (by rw [hX₄]; omega)
    (by rw [f₄.len, f₁₃.len]; simp only [List.length_append, List.length_singleton]; omega) (by omega)
    (by simp only [List.length_append, List.length_singleton]; omega)
    (by rw [hseg]; exact fun v h => by have := hwv v h; omega)
  rw [hseg] at F₅
  -- the colors
  have f₁₅ := (f₁₃.trans f₄).trans f₅
  obtain ⟨τ₆, r₆, F₆, f₆⟩ := pushVars_run (W := W) (xs := ["cP", "cQ"]) (by decide) F₅
    (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [f₁₅.vars _ (by decide), hP]; exact hPW
      · rw [f₁₅.vars _ (by decide), hQ]; exact hQW)
    (by rw [f₁₅.len]; simp only [List.length_append, List.length_singleton, List.length_cons,
      List.length_nil]; omega)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega)
  have hPQ : ["cP", "cQ"].map τ₅.vars = [P, Q] := by
    simp [f₁₅.vars "cP" (by decide), f₁₅.vars "cQ" (by decide), hP, hQ]
  rw [hPQ] at F₆
  refine ⟨τ₆, ?_, ?_, ?_, (f₁₅.trans f₆).mono (by intro z hz; simp at hz ⊢; tauto)⟩
  · unfold jbOne
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ r₆))))).mono ?_
    simp only [Expr.size, List.length_cons, List.length_nil]; omega
  · rw [f₆.vars _ (by decide), f₅.vars _ (by decide), f₄.vars _ (by decide)]
    simp only [hτ₃, vars_setVar, if_neg (show ("y" : String) ≠ "tE" by decide)]
    rw [hy₂, htk1, List.length_append]; omega
  · convert F₆ using 1
    rw [hjk1, hL]; simp

open Lax185574.WordEncoding Lax185574.TypeTrees in
set_option maxHeartbeats 1000000 in
theorem wq0_run {W P Q : ℕ} {σ : Env} {pre fw : List ℕ} {ts : List TypeTree}
    (hF : Filled "OB" "po" pre σ) (hFW : Filled "FW" "pf" fw σ)
    (hfw : fw = ts.length :: (ts.map toWord).flatten) (hgn : σ.vars "gn" = ts.length)
    (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hcap : W + 1 ≤ (σ.arrs "OB").length)
    (hB : pre.length + 4 * fw.length + 2 * dK + 10 ≤ W) (hv : ∀ v ∈ fw, v ≤ W) (hPW : P ≤ W)
    (hQW : Q ≤ W) :
    ∃ σ', Run (W + 1) wq0 σ σ' (250 * fw.length + 10 * dK + 100) ∧
      Filled "OB" "po" (pre ++ swIn (jbW ts P Q) qR0 qE0) σ' ∧
      σ'.vars "qa" = pre.length + 3 ∧ σ'.vars "ql" = (jbW ts P Q).length ∧
      OFr σ σ' ["po", "qa", "ql", "ci", "y", "e4", "tS", "tE", "e1", "e2", "e3"] := by
  have hK := lens_le_dK
  obtain ⟨hjl, h3n⟩ := length_jbW P Q hfw
  have hfl : fw.length = 1 + (ts.map toWord).flatten.length := by rw [hfw]; simp; omega
  have hpf := hFW.pos
  have hXd : (σ.arrs "FW").drop 1 = (ts.map toWord).flatten ++ (σ.arrs "FW").drop fw.length := by
    have := hFW.length_le
    have e : σ.arrs "FW" = fw ++ (σ.arrs "FW").drop fw.length := by
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        by_cases hi : i < fw.length
        · rw [List.getElem_append_left hi]
          have := hFW.get i hi
          rw [List.getElem?_eq_getElem h1] at this; exact Option.some.inj this
        · rw [List.getElem_append_right (by omega)]; simp; congr 1; omega
    conv_lhs => rw [e]
    rw [hfw]; simp
  -- the lengths
  obtain ⟨τ₁, r₁, F₁, f₁⟩ := push1_ofr (W := W) (e := .add (.var "pf") (.mul (.lit 3) (.var "gn"))) hF
    (v := fw.length + 3 * ts.length)
    (ev_add (ev_var hpf (by omega)) (evalB_bin (evalB_lit (by omega)) (ev_var hgn (by omega))
      (by show 3 * ts.length < W + 1; omega)) (by show fw.length + 3 * ts.length < W + 1; omega)) (by omega) (by omega)
  obtain ⟨τ₂, r₂, F₂, f₂⟩ := pushLits_run (W := W) (l := [qR0.length, qE0.length]) F₁
    (by simp; omega) (by simp [f₁.len]; omega) (by simp; omega)
  set τ₃ := τ₂.setVar "qa" (pre.length + 3) with hτ₃
  have r₃ : Run (W + 1) (.assign "qa" (.var "po")) τ₂ τ₃ 2 :=
    Run.assign (ev_var (by rw [F₂.pos]; simp) (by omega))
  have f₁₂ := (f₁.trans f₂).trans (OFr.setVar τ₂ "qa" (pre.length + 3))
  set τ₄ := τ₃.setVar "ql" (fw.length + 3 * ts.length) with hτ₄
  have r₄ : Run (W + 1) (.assign "ql" (.add (.var "pf") (.mul (.lit 3) (.var "gn")))) τ₃ τ₄ 6 :=
    (Run.assign (ev_add (ev_var (by rw [f₁₂.vars _ (by decide), hpf]) (by omega))
      (evalB_bin (evalB_lit (by omega)) (ev_var (by rw [f₁₂.vars _ (by decide), hgn]) (by omega))
        (by show 3 * ts.length < W + 1; omega)) (by show fw.length + 3 * ts.length < W + 1; omega))).mono
      (by simp [Expr.size])
  have f₄ := f₁₂.trans (OFr.setVar τ₃ "ql" (fw.length + 3 * ts.length))
  have F₄ : Filled "OB" "po" (pre ++ [fw.length + 3 * ts.length] ++ [qR0.length, qE0.length]) τ₄ :=
    (F₂.setVar (by decide) _).setVar (by decide) _
  -- the count
  obtain ⟨τ₅, r₅, F₅, f₅⟩ := push1_ofr (W := W) (e := .var "gn") F₄
    (ev_var (by rw [f₄.vars _ (by decide), hgn]) (by omega)) (by rw [f₄.len]; simp; omega)
    (by simp; omega)
  have f₁₅ := f₄.trans f₅
  set pre' := pre ++ [fw.length + 3 * ts.length] ++ [qR0.length, qE0.length] ++ [ts.length] with hpre'
  have hpre'l : pre'.length = pre.length + 4 := by simp [hpre']
  set τ₆ := τ₅.setVar "y" 1 with hτ₆
  have f₁₆ := f₁₅.trans (OFr.setVar τ₅ "y" 1)
  -- the jobs
  have hXd' : (τ₆.arrs "FW").drop 1 = (ts.map toWord).flatten ++ (σ.arrs "FW").drop fw.length := by
    rw [f₁₆.arrs _ (by decide)]; exact hXd
  have hvu : ∀ v ∈ (ts.map toWord).flatten, v ≤ W := fun v h => hv v (by rw [hfw]; exact List.mem_cons_of_mem _ h)
  obtain ⟨τ₇, r₇, ⟨hy₇, F₇, f₇⟩, -⟩ := forUp_pot (B := W + 1) (i := "e4") (e := .var "gn")
    (body := jbOne) (N := ts.length) (c := 100) (σ := τ₆) (fun k => ((ts.map toWord).getD k []).length)
    (fun k ρ => ρ.vars "y" = 1 + ((ts.map toWord).take k).flatten.length ∧
      Filled "OB" "po" (pre' ++ ((jbF ts P Q).take k).flatten) ρ ∧
      OFr τ₆ ρ ["e4", "tS", "e3", "y", "e1", "e2", "tE", "po", "ci"]) (by omega)
    (fun k _ ρ hI _ => ev_var (by rw [hI.2.2.vars _ (by decide), f₁₆.vars _ (by decide), hgn])
      (by omega))
    ⟨by simp [hτ₆], by simpa using (F₅.setVar (y := "y") (by decide) 1).setVar (y := "e4") (by decide) 0, (OFr.setVar τ₆ "e4" 0).mono (by simp)⟩
    (by
      intro k hk ρ ⟨hyρ, Fρ, fρ⟩ hik
      have hρ : ∀ y ∈ ["cP", "cQ"], ρ.vars y = σ.vars y := fun y hy => by
        rw [fρ.vars y (by simp at hy ⊢; rcases hy with rfl | rfl <;> decide),
          f₁₆.vars y (by simp at hy ⊢; rcases hy with rfl | rfl <;> decide)]
      obtain ⟨ρ', r', hy', F', f'⟩ := jbOne_run (W := W) (P := P) (Q := Q) (k := k) (ts := ts)
        (X := τ₆.arrs "FW") (R := (σ.arrs "FW").drop fw.length) (pre := pre') (τ := ρ) (by omega)
        (by rw [fρ.arrs _ (by decide)]) hXd' hyρ Fρ (by rw [hρ _ (by simp), hP])
        (by rw [hρ _ (by simp), hQ]) (by rw [fρ.len, f₁₆.len]; omega) (by omega) hvu hPW hQW
      have hg : ((ts.map toWord).getD k []).length = (toWord ts[k]).length := by
        rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
      refine ⟨ρ', r'.mono (by rw [hg]), by rw [f'.vars _ (by decide), hik], by simpa using hy',
        F'.setVar (by decide) _, ((fρ.trans f').trans (OFr.setVar ρ' "e4" (k + 1))).mono
          (by intro z hz; simp at hz ⊢; tauto)⟩)
  have hsum : ∑ k ∈ Finset.range ts.length, ((ts.map toWord).getD k []).length = (ts.map toWord).flatten.length := by
    have : ∀ m ≤ (ts.map toWord).length, ∑ k ∈ Finset.range m, ((ts.map toWord).getD k []).length = ((ts.map toWord).take m).flatten.length := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih (by omega), flatten_take_succ (ts.map toWord) (by omega)]; simp
    rw [this ts.length (by simp), List.take_of_length_le (by simp)]
  rw [hsum] at r₇
  rw [List.take_of_length_le (by simp [jbF])] at F₇
  have f₁₇ := f₁₆.trans f₇
  obtain ⟨τ₈, r₈, F₈, f₈⟩ := pushLits_run (W := W) (l := qR0) F₇
    (fun v hv' => by have := le_dK_of_mem (Or.inr (Or.inl hv')); omega)
    (by rw [f₁₇.len]; simp only [List.length_append, hpre'l, length_jbF]; omega)
    (by simp only [List.length_append, hpre'l, length_jbF]; omega)
  obtain ⟨τ₉, r₉, F₉, f₉⟩ := pushLits_run (W := W) (l := qE0) F₈
    (fun v hv' => by have := le_dK_of_mem (Or.inr (Or.inr hv')); omega)
    (by rw [f₈.len, f₁₇.len]; simp only [List.length_append, hpre'l, length_jbF]; omega)
    (by simp only [List.length_append, hpre'l, length_jbF]; omega)
  refine ⟨τ₉, ?_, ?_, ?_, ?_, ((f₁₇.trans f₈).trans f₉).mono (by intro z hz; simp at hz ⊢; tauto)⟩
  · unfold wq0
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq
      (Run.assign (evalB_lit (by omega))) (Run.seq r₇ (Run.seq r₈ r₉)))))))).mono ?_
    simp only [Expr.size, List.length_cons, List.length_nil]
    omega
  · convert F₉ using 1
    have e : swIn (jbW ts P Q) qR0 qE0 = [fw.length + 3 * ts.length, qR0.length, qE0.length] ++
        (ts.length :: (jbF ts P Q).flatten) ++ qR0 ++ qE0 := by rw [swIn, hjl]; rfl
    rw [e, hpre']; simp only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append]
  · rw [f₉.vars _ (by decide), f₈.vars _ (by decide), f₇.vars _ (by decide)]
    simp only [hτ₆, vars_setVar, if_neg (show ("qa" : String) ≠ "y" by decide)]
    rw [f₅.vars _ (by decide)]; simp [hτ₄, hτ₃]
  · rw [f₉.vars _ (by decide), f₈.vars _ (by decide), f₇.vars _ (by decide)]
    simp only [hτ₆, vars_setVar, if_neg (show ("ql" : String) ≠ "y" by decide)]
    rw [f₅.vars _ (by decide)]; simp [hτ₄, hjl]

/-- Copy a whole filled word, with the frames. -/
theorem cpAll_ofr {W : ℕ} {src pv : String} {σ : Env} {pre l : List ℕ}
    (hsrc : src ≠ "OB") (hpv : pv ≠ "po") (hpv' : pv ≠ "ci") (hz : σ.vars "qz" = 0)
    (hF : Filled "OB" "po" pre σ) (hl : Filled src pv l σ)
    (hcap : pre.length + l.length ≤ (σ.arrs "OB").length) (hB : pre.length + l.length ≤ W)
    (hv : ∀ v ∈ l, v ≤ W) :
    ∃ σ', Run (W + 1) (cpSeg src "qz" pv) σ σ' (l.length * 20 + 6) ∧
      Filled "OB" "po" (pre ++ l) σ' ∧ OFr σ σ' ["ci", "po"] := by
  have hA : 0 + l.length ≤ (σ.arrs src).length := by have := hl.length_le; omega
  obtain ⟨σ', r, F, f⟩ := cpSeg_ofr (W := W) (src := src) (s := "qz") (l := pv) (pre := pre)
    (a := 0) (N := l.length) hsrc hz hl.pos (by decide) (by decide) hpv hpv' hF hA hcap (by omega)
    hB (by rw [seg_filled hl]; exact hv)
  rw [seg_filled hl] at F
  exact ⟨σ', r, F, f⟩

/-- The resolve query. -/
noncomputable def wq1 : Com :=
  .seq (pushLits [qM0.length]) (.seq (push1 "OB" "po" (.add (.var "pg") (.add (.lit 3) (.var "pf"))))
  (.seq (pushLits [qE0.length]) (.seq (pushLits qM0) (.seq (.assign "qa" (.var "po"))
  (.seq (.assign "ql" (.add (.var "pg") (.add (.lit 3) (.var "pf"))))
  (.seq (cpSeg "GW" "qz" "pg") (.seq (pushL "OB" "po" [.var "cP", .var "cQ", .var "cs"])
  (.seq (cpSeg "FW" "qz" "pf") (pushLits qE0)))))))))

theorem wq1_run {W P Q sg : ℕ} {σ : Env} {pre gw fw : List ℕ}
    (hF : Filled "OB" "po" pre σ) (hGW : Filled "GW" "pg" gw σ) (hFW : Filled "FW" "pf" fw σ)
    (hz : σ.vars "qz" = 0) (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hs : σ.vars "cs" = sg)
    (hcap : W + 1 ≤ (σ.arrs "OB").length)
    (hB : pre.length + gw.length + fw.length + 2 * dK + 10 ≤ W) (hv : ∀ v ∈ gw ++ fw, v ≤ W)
    (hPW : P ≤ W) (hQW : Q ≤ W) (hsW : sg ≤ W) :
    ∃ σ', Run (W + 1) wq1 σ σ' (20 * (gw.length + fw.length) + 10 * dK + 100) ∧
      Filled "OB" "po" (pre ++ swIn qM0 (gw ++ [P, Q, sg] ++ fw) qE0) σ' ∧
      σ'.vars "qa" = pre.length + 3 + qM0.length ∧ σ'.vars "ql" = gw.length + 3 + fw.length ∧
      OFr σ σ' ["po", "qa", "ql", "ci"] := by
  have hK := lens_le_dK
  have hgl := hGW.pos
  have hfl := hFW.pos
  obtain ⟨τ₁, r₁, F₁, f₁⟩ := pushLits_run (W := W) (l := [qM0.length]) hF
    (by simp; omega) (by simp; omega) (by simp; omega)
  obtain ⟨τ₂, r₂, F₂, f₂⟩ := push1_ofr (W := W) (e := .add (.var "pg") (.add (.lit 3) (.var "pf"))) F₁
    (ev_add (ev_var (by rw [f₁.vars _ (by decide), hgl]) (by omega))
      (ev_add (evalB_lit (by omega)) (ev_var (by rw [f₁.vars _ (by decide), hfl]) (by omega))
        (by omega)) (by omega)) (by rw [f₁.len]; simp; omega) (by simp; omega)
  obtain ⟨τ₃, r₃, F₃, f₃⟩ := pushLits_run (W := W) (l := [qE0.length]) F₂
    (by simp; omega) (by rw [f₂.len, f₁.len]; simp; omega) (by simp; omega)
  obtain ⟨τ₄, r₄, F₄, f₄⟩ := pushLits_run (W := W) (l := qM0) F₃
    (fun v hv' => by have := le_dK_of_mem (Or.inl hv'); omega)
    (by rw [f₃.len, f₂.len, f₁.len]; simp; omega) (by simp; omega)
  have f₁₄ := ((f₁.trans f₂).trans f₃).trans f₄
  set qa := pre.length + 3 + qM0.length with hqa
  set τ₅ := τ₄.setVar "qa" qa with hτ₅
  have r₅ : Run (W + 1) (.assign "qa" (.var "po")) τ₄ τ₅ 2 :=
    Run.assign (ev_var (by rw [F₄.pos]; simp [hqa]; omega) (by omega))
  set τ₆ := τ₅.setVar "ql" (gw.length + (3 + fw.length)) with hτ₆
  have f₁₆ := (f₁₄.trans (OFr.setVar τ₄ "qa" qa)).trans (OFr.setVar τ₅ "ql" (gw.length + (3 + fw.length)))
  have r₆ : Run (W + 1) (.assign "ql" (.add (.var "pg") (.add (.lit 3) (.var "pf")))) τ₅ τ₆ 6 :=
    Run.assign (ev_add (ev_var (by rw [(f₁₄.trans (OFr.setVar τ₄ "qa" qa)).vars _ (by decide), hgl])
      (by omega)) (ev_add (evalB_lit (by omega))
        (ev_var (by rw [(f₁₄.trans (OFr.setVar τ₄ "qa" qa)).vars _ (by decide), hfl]) (by omega))
        (by omega)) (by omega))
  have F₆ : Filled "OB" "po" (pre ++ [qM0.length] ++ [gw.length + (3 + fw.length)] ++
      [qE0.length] ++ qM0) τ₆ := (F₄.setVar (by decide) _).setVar (by decide) _
  obtain ⟨τ₇, r₇, F₇, f₇⟩ := cpAll_ofr (W := W) (src := "GW") (pv := "pg") (by decide) (by decide)
    (by decide) (by rw [f₁₆.vars _ (by decide), hz]) F₆
    (hGW.congr (f₁₆.vars _ (by decide)) (f₁₆.arrs _ (by decide)))
    (by rw [f₁₆.len]; simp; omega) (by simp; omega) (fun v hv' => hv v (by simp [hv']))
  obtain ⟨τ₈, r₈, F₈, f₈⟩ := pushVars_run (W := W) (xs := ["cP", "cQ", "cs"]) (by decide) F₇
    (by
      intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl
      · rw [f₇.vars _ (by decide), f₁₆.vars _ (by decide), hP]; exact hPW
      · rw [f₇.vars _ (by decide), f₁₆.vars _ (by decide), hQ]; exact hQW
      · rw [f₇.vars _ (by decide), f₁₆.vars _ (by decide), hs]; exact hsW)
    (by rw [f₇.len, f₁₆.len]; simp; omega) (by simp; omega)
  have f₁₈ := (f₁₆.trans f₇).trans f₈
  obtain ⟨τ₉, r₉, F₉, f₉⟩ := cpAll_ofr (W := W) (src := "FW") (pv := "pf") (by decide) (by decide)
    (by decide) (by rw [f₁₈.vars _ (by decide), hz]) F₈
    (hFW.congr (f₁₈.vars _ (by decide)) (f₁₈.arrs _ (by decide)))
    (by rw [f₁₈.len]; simp; omega) (by simp; omega) (fun v hv' => hv v (by simp [hv']))
  obtain ⟨τ₁₀, r₁₀, F₁₀, f₁₀⟩ := pushLits_run (W := W) (l := qE0) F₉
    (fun v hv' => by have := le_dK_of_mem (Or.inr (Or.inr hv')); omega)
    (by rw [f₉.len, f₁₈.len]; simp; omega) (by simp; omega)
  have hτ₇ : τ₇.vars "cP" = P ∧ τ₇.vars "cQ" = Q ∧ τ₇.vars "cs" = sg := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [f₇.vars _ (by decide), f₁₆.vars _ (by decide)] <;> assumption
  refine ⟨τ₁₀, ?_, ?_, ?_, ?_, ?_⟩
  · unfold wq1
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq r₆
      (Run.seq r₇ (Run.seq r₈ (Run.seq r₉ r₁₀))))))))).mono ?_
    simp only [Expr.size, List.length_cons, List.length_nil]
    omega
  · convert F₁₀ using 1
    simp [swIn, hτ₇]; omega
  · rw [f₁₀.vars _ (by decide), f₉.vars _ (by decide), f₈.vars _ (by decide),
      f₇.vars _ (by decide)]; simp [hτ₆, hτ₅]
  · rw [f₁₀.vars _ (by decide), f₉.vars _ (by decide), f₈.vars _ (by decide),
      f₇.vars _ (by decide)]; simp [hτ₆]; omega
  · exact ((f₁₈.trans f₉).trans f₁₀).mono (by intro y hy; simp at hy ⊢; tauto)

/-- The evaluation query. -/
noncomputable def wq2 : Com :=
  .seq (pushLits [qM0.length, qR0.length]) (.seq (push1 "OB" "po" (.add (.var "tl") (.var "lp")))
  (.seq (pushLits qM0) (.seq (pushLits qR0) (.seq (.assign "qa" (.var "po"))
  (.seq (.assign "ql" (.add (.var "tl") (.var "lp")))
  (.seq (cpSeg "FW" "ta" "tl") (cpSeg "lo" "qz" "lp")))))))

theorem wq2_run {W a N : ℕ} {σ : Env} {pre fw lw : List ℕ}
    (hF : Filled "OB" "po" pre σ) (hFW : Filled "FW" "pf" fw σ) (hlo : Filled "lo" "lp" lw σ)
    (hz : σ.vars "qz" = 0) (hta : σ.vars "ta" = a) (htl : σ.vars "tl" = N)
    (haN : a + N ≤ fw.length) (hcap : W + 1 ≤ (σ.arrs "OB").length)
    (hB : pre.length + fw.length + lw.length + 2 * dK + 10 ≤ W) (hv : ∀ v ∈ fw ++ lw, v ≤ W) :
    ∃ σ', Run (W + 1) wq2 σ σ' (20 * (fw.length + lw.length) + 10 * dK + 100) ∧
      Filled "OB" "po" (pre ++ swIn qM0 qR0 (seg fw a N ++ lw)) σ' ∧
      σ'.vars "qa" = pre.length + 3 + qM0.length + qR0.length ∧ σ'.vars "ql" = N + lw.length ∧
      OFr σ σ' ["po", "qa", "ql", "ci"] := by
  have hK := lens_le_dK
  have hll := hlo.pos
  obtain ⟨τ₁, r₁, F₁, f₁⟩ := pushLits_run (W := W) (l := [qM0.length, qR0.length]) hF
    (by simp; omega) (by simp; omega) (by simp; omega)
  obtain ⟨τ₂, r₂, F₂, f₂⟩ := push1_ofr (W := W) (e := .add (.var "tl") (.var "lp")) F₁
    (ev_add (ev_var (by rw [f₁.vars _ (by decide), htl]) (by omega))
      (ev_var (by rw [f₁.vars _ (by decide), hll]) (by omega)) (by omega))
    (by rw [f₁.len]; simp; omega) (by simp; omega)
  obtain ⟨τ₃, r₃, F₃, f₃⟩ := pushLits_run (W := W) (l := qM0) F₂
    (fun v hv' => by have := le_dK_of_mem (Or.inl hv'); omega)
    (by rw [f₂.len, f₁.len]; simp; omega) (by simp; omega)
  obtain ⟨τ₄, r₄, F₄, f₄⟩ := pushLits_run (W := W) (l := qR0) F₃
    (fun v hv' => by have := le_dK_of_mem (Or.inr (Or.inl hv')); omega)
    (by rw [f₃.len, f₂.len, f₁.len]; simp; omega) (by simp; omega)
  have f₁₄ := ((f₁.trans f₂).trans f₃).trans f₄
  set qa := pre.length + 3 + qM0.length + qR0.length with hqa
  set τ₅ := τ₄.setVar "qa" qa with hτ₅
  have r₅ : Run (W + 1) (.assign "qa" (.var "po")) τ₄ τ₅ 2 :=
    Run.assign (ev_var (by rw [F₄.pos]; simp [hqa]; omega) (by omega))
  have f₁₅ := f₁₄.trans (OFr.setVar τ₄ "qa" qa)
  set τ₆ := τ₅.setVar "ql" (N + lw.length) with hτ₆
  have r₆ : Run (W + 1) (.assign "ql" (.add (.var "tl") (.var "lp"))) τ₅ τ₆ 4 :=
    Run.assign (ev_add (ev_var (by rw [f₁₅.vars _ (by decide), htl]) (by omega))
      (ev_var (by rw [f₁₅.vars _ (by decide), hll]) (by omega)) (by omega))
  have f₁₆ := f₁₅.trans (OFr.setVar τ₅ "ql" (N + lw.length))
  have F₆ : Filled "OB" "po" (pre ++ [qM0.length, qR0.length] ++ [N + lw.length] ++ qM0 ++ qR0) τ₆ :=
    (F₄.setVar (by decide) _).setVar (by decide) _
  have hFW₆ : Filled "FW" "pf" fw τ₆ := hFW.congr (f₁₆.vars _ (by decide)) (f₁₆.arrs _ (by decide))
  obtain ⟨τ₇, r₇, F₇, f₇⟩ := cpSeg_ofr (W := W) (src := "FW") (s := "ta") (l := "tl") (a := a)
    (N := N) (by decide) (by rw [f₁₆.vars _ (by decide), hta]) (by rw [f₁₆.vars _ (by decide), htl])
    (by decide) (by decide) (by decide) (by decide) F₆
    (by have := hFW₆.length_le; omega) (by rw [f₁₆.len]; simp; omega) (by omega) (by simp; omega)
    (by rw [seg_filled_sub hFW₆ haN]; exact fun v hv' => hv v (by simp [mem_seg hv']))
  rw [seg_filled_sub hFW₆ haN] at F₇
  have hsl : (seg fw a N).length = N := length_seg haN
  have f₁₇ := f₁₆.trans f₇
  obtain ⟨τ₈, r₈, F₈, f₈⟩ := cpAll_ofr (W := W) (src := "lo") (pv := "lp") (by decide) (by decide)
    (by decide) (by rw [f₁₇.vars _ (by decide), hz]) F₇
    (hlo.congr (f₁₇.vars _ (by decide)) (f₁₇.arrs _ (by decide)))
    (by rw [f₁₇.len]; simp [hsl]; omega) (by simp [hsl]; omega) (fun v hv' => hv v (by simp [hv']))
  refine ⟨τ₈, ?_, ?_, ?_, ?_, ?_⟩
  · unfold wq2
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq r₆
      (Run.seq r₇ r₈))))))).mono ?_
    simp only [Expr.size, List.length_cons, List.length_nil]
    omega
  · convert F₈ using 1
    simp [swIn, hsl]
  · rw [f₈.vars _ (by decide), f₇.vars _ (by decide)]; simp [hτ₆, hτ₅]
  · rw [f₈.vars _ (by decide), f₇.vars _ (by decide)]; simp [hτ₆]
  · exact (f₁₇.trans f₈).mono (by intro y hy; simp at hy ⊢; tauto)

/-- The fixed query. -/
noncomputable def wq3 : Com :=
  .seq (pushLits [qM0.length, qR0.length, qE0.length]) (.seq (.assign "qa" (.var "po"))
  (.seq (.assign "ql" (.lit qM0.length)) (.seq (pushLits qM0) (.seq (pushLits qR0) (pushLits qE0)))))

theorem wq3_run {W : ℕ} {σ : Env} {pre : List ℕ}
    (hF : Filled "OB" "po" pre σ) (hcap : W + 1 ≤ (σ.arrs "OB").length)
    (hB : pre.length + 2 * dK + 10 ≤ W) :
    ∃ σ', Run (W + 1) wq3 σ σ' (10 * dK + 100) ∧
      Filled "OB" "po" (pre ++ swIn qM0 qR0 qE0) σ' ∧
      σ'.vars "qa" = pre.length + 3 ∧ σ'.vars "ql" = qM0.length ∧
      OFr σ σ' ["po", "qa", "ql", "ci"] := by
  have hK := lens_le_dK
  obtain ⟨τ₁, r₁, F₁, f₁⟩ := pushLits_run (W := W) (l := [qM0.length, qR0.length, qE0.length]) hF
    (by simp; omega) (by simp; omega) (by simp; omega)
  set τ₂ := τ₁.setVar "qa" (pre.length + 3) with hτ₂
  have r₂ : Run (W + 1) (.assign "qa" (.var "po")) τ₁ τ₂ 2 :=
    Run.assign (ev_var (by rw [F₁.pos]; simp) (by simp; omega))
  set τ₃ := τ₂.setVar "ql" qM0.length with hτ₃
  have r₃ : Run (W + 1) (.assign "ql" (.lit qM0.length)) τ₂ τ₃ 2 := Run.assign (evalB_lit (by omega))
  have f₁₃ := (f₁.trans (OFr.setVar τ₁ "qa" _)).trans (OFr.setVar τ₂ "ql" qM0.length)
  have F₃ : Filled "OB" "po" (pre ++ [qM0.length, qR0.length, qE0.length]) τ₃ :=
    (F₁.setVar (by decide) _).setVar (by decide) _
  obtain ⟨τ₄, r₄, F₄, f₄⟩ := pushLits_run (W := W) (l := qM0) F₃
    (fun v hv' => by have := le_dK_of_mem (Or.inl hv'); omega)
    (by rw [f₁₃.len]; simp; omega) (by simp; omega)
  obtain ⟨τ₅, r₅, F₅, f₅⟩ := pushLits_run (W := W) (l := qR0) F₄
    (fun v hv' => by have := le_dK_of_mem (Or.inr (Or.inl hv')); omega)
    (by rw [f₄.len, f₁₃.len]; simp; omega) (by simp; omega)
  obtain ⟨τ₆, r₆, F₆, f₆⟩ := pushLits_run (W := W) (l := qE0) F₅
    (fun v hv' => by have := le_dK_of_mem (Or.inr (Or.inr hv')); omega)
    (by rw [f₅.len, f₄.len, f₁₃.len]; simp; omega) (by simp; omega)
  refine ⟨τ₆, ?_, ?_, ?_, ?_, ?_⟩
  · unfold wq3
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ r₆))))).mono ?_
    simp only [Expr.size, List.length_cons, List.length_nil]
    omega
  · convert F₆ using 1
    simp [swIn]
  · rw [f₆.vars _ (by decide), f₅.vars _ (by decide), f₄.vars _ (by decide)]; simp [hτ₃, hτ₂]
  · rw [f₆.vars _ (by decide), f₅.vars _ (by decide), f₄.vars _ (by decide)]; simp [hτ₃]
  · exact (((f₁₃.trans f₄).trans f₅).trans f₆).mono (by intro y hy; simp at hy ⊢; tauto)

open Lax185574.WordEncoding Lax185574.TypeTrees in
/-- The word `tr` that the query of kind `c` uses: the jobs of the trees
of `fw` for a merge, the tree of `fw` at `a` of length `N` for the
evaluation. -/
def TrOK (c P Q a N : ℕ) (fw tr : List ℕ) : Prop :=
  (c = 0 → ∃ ts : List TypeTree, fw = ts.length :: (ts.map toWord).flatten ∧ tr = jbW ts P Q) ∧
  (c = 2 → a + N ≤ fw.length ∧ tr = seg fw a N)

/-! ### The query by kind -/

/-- The query by the kind `ck`. -/
noncomputable def wrQ : Com :=
  .ite (.eq (.var "ck") (.lit 0)) wq0 (.ite (.eq (.var "ck") (.lit 1)) wq1
    (.ite (.eq (.var "ck") (.lit 2)) wq2 wq3))

theorem length_realQ_le (c P Q sg : ℕ) (gw fw tr lw : List ℕ) (htr : tr.length ≤ 4 * fw.length) :
    (realQ c P Q sg gw fw tr lw).length ≤ gw.length + 4 * fw.length + lw.length + dK := by
  have hK := lens_le_dK
  unfold realQ
  split_ifs <;> simp <;> omega

theorem length_qW_le (c P Q sg : ℕ) (gw fw tr lw : List ℕ) (htr : tr.length ≤ 4 * fw.length) :
    (qW c P Q sg gw fw tr lw).length ≤ gw.length + 4 * fw.length + lw.length + dK + 6 := by
  have hK := lens_le_dK
  unfold qW realQ
  split_ifs <;> simp [swIn] <;> omega

/-- The scalars that writing the query changes. -/
def wqVars : List String := ["po", "qa", "ql", "ci", "y", "e4", "tS", "tE", "e1", "e2", "e3"]

open Lax185574.WordEncoding Lax185574.TypeTrees in
theorem wrQ_run {W c P Q sg a N : ℕ} {σ : Env} {pre gw fw lw tr : List ℕ}
    (hF : Filled "OB" "po" pre σ) (hGW : Filled "GW" "pg" gw σ) (hFW : Filled "FW" "pf" fw σ)
    (hlo : Filled "lo" "lp" lw σ) (hz : σ.vars "qz" = 0) (hc : σ.vars "ck" = c)
    (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hs : σ.vars "cs" = sg)
    (hta : σ.vars "ta" = a) (htl : σ.vars "tl" = N) (htr : TrOK c P Q a N fw tr)
    (hgn : ∀ ts : List TypeTree, c = 0 → fw = ts.length :: (ts.map toWord).flatten →
      σ.vars "gn" = ts.length)
    (hcap : W + 1 ≤ (σ.arrs "OB").length)
    (hB : pre.length + gw.length + 4 * fw.length + lw.length + 2 * dK + 10 ≤ W)
    (hv : ∀ v ∈ gw ++ fw ++ lw, v ≤ W) (hPW : P ≤ W) (hQW : Q ≤ W) (hsW : sg ≤ W)
    (hcW : c ≤ W) :
    ∃ σ', Run (W + 1) wrQ σ σ' (250 * (gw.length + fw.length + lw.length) + 10 * dK + 120) ∧
      Filled "OB" "po" (pre ++ qW c P Q sg gw fw tr lw) σ' ∧
      seg (σ'.arrs "OB") (σ'.vars "qa") (σ'.vars "ql") = realQ c P Q sg gw fw tr lw ∧
      σ'.vars "ql" = (realQ c P Q sg gw fw tr lw).length ∧
      σ'.vars "qa" + σ'.vars "ql" ≤ (pre ++ qW c P Q sg gw fw tr lw).length ∧
      OFr σ σ' wqVars := by
  have hcond : ∀ d : ℕ, d < 3 → (Cond.eq (.var "ck") (.lit d)).evalB (W + 1) σ = some (decide (c = d)) :=
    fun d hd => condEq_lit hc (by omega) (by omega)
  unfold wrQ
  by_cases h0 : c = 0
  · subst h0
    obtain ⟨ts, hfw, rfl⟩ := htr.1 rfl
    obtain ⟨σ', r, F, hqa, hql, f⟩ := wq0_run (W := W) hF hFW hfw (hgn ts rfl hfw) hP hQ hcap
      (by omega) (fun v hv' => hv v (by simp [hv'])) hPW hQW
    have hr : realQ 0 P Q sg gw fw (jbW ts P Q) lw = jbW ts P Q := by simp [realQ]
    have hq : qW 0 P Q sg gw fw (jbW ts P Q) lw = swIn (jbW ts P Q) qR0 qE0 := by
      rw [qW, if_pos rfl, hr]
    have hF' : Filled "OB" "po" ((pre ++ [(jbW ts P Q).length, qR0.length, qE0.length]) ++
        jbW ts P Q ++ (qR0 ++ qE0)) σ' := by convert F using 1; simp [swIn]
    refine ⟨σ', (Run.ite_true (by rw [hcond 0 (by omega)]; simp) r).mono (by simp [Cond.size, Expr.size]; omega),
      by rw [hq]; exact F, ?_, ?_, ?_, f.mono (by simp [wqVars])⟩
    · rw [hqa, hql, hr]; have := seg_of_filled hF'
      rw [show (pre ++ [(jbW ts P Q).length, qR0.length, qE0.length]).length = pre.length + 3 by simp]
        at this
      exact this
    · simp [hql, hr]
    · rw [hq]; simp [hqa, hql, swIn]; omega
  by_cases h1 : c = 1
  · subst h1
    have hr : realQ 1 P Q sg gw fw tr lw = gw ++ [P, Q, sg] ++ fw := by simp [realQ]
    have hq : qW 1 P Q sg gw fw tr lw = swIn qM0 (gw ++ [P, Q, sg] ++ fw) qE0 := by
      rw [qW, if_neg (by decide), if_pos rfl, hr]
    obtain ⟨σ', r, F, hqa, hql, f⟩ := wq1_run (W := W) hF hGW hFW hz hP hQ hs hcap (by omega)
      (fun v hv' => hv v (by simp at hv' ⊢; tauto)) hPW hQW hsW
    have hF' : Filled "OB" "po" ((pre ++ [qM0.length, gw.length + 3 + fw.length, qE0.length] ++ qM0) ++
        (gw ++ [P, Q, sg] ++ fw) ++ qE0) σ' := by convert F using 1; simp [swIn]; omega
    refine ⟨σ', (Run.ite_false (by rw [hcond 0 (by omega)]; simp) (Run.ite_true
      (by rw [hcond 1 (by omega)]; simp) r)).mono (by simp [Cond.size, Expr.size]; omega),
      by rw [hq]; exact F, ?_, ?_, ?_, f.mono (by simp [wqVars])⟩
    · rw [hqa, hql, hr]; have := seg_of_filled hF'
      rw [show (pre ++ [qM0.length, gw.length + 3 + fw.length, qE0.length] ++ qM0).length =
          pre.length + 3 + qM0.length by simp; omega,
        show (gw ++ [P, Q, sg] ++ fw).length = gw.length + 3 + fw.length by simp; omega] at this
      exact this
    · rw [hql, hr]; simp; omega
    · rw [hq]; simp [hqa, hql, swIn]; omega
  by_cases h2 : c = 2
  · subst h2
    obtain ⟨haN, rfl⟩ := htr.2 rfl
    obtain ⟨σ', r, F, hqa, hql, f⟩ := wq2_run (W := W) hF hFW hlo hz hta htl haN hcap
      (by omega) (fun v hv' => hv v (by simp at hv' ⊢; tauto))
    have hsl : (seg fw a N).length = N := length_seg haN
    have hr : realQ 2 P Q sg gw fw (seg fw a N) lw = seg fw a N ++ lw := by simp [realQ]
    have hq : qW 2 P Q sg gw fw (seg fw a N) lw = swIn qM0 qR0 (seg fw a N ++ lw) := by
      rw [qW, if_neg (by decide), if_neg (by decide), if_pos rfl, hr]
    have hF' : Filled "OB" "po" ((pre ++ [qM0.length, qR0.length, N + lw.length] ++ qM0 ++ qR0) ++
        (seg fw a N ++ lw) ++ []) σ' := by convert F using 1; simp [swIn, hsl]
    refine ⟨σ', (Run.ite_false (by rw [hcond 0 (by omega)]; simp) (Run.ite_false
      (by rw [hcond 1 (by omega)]; simp) (Run.ite_true (by rw [hcond 2 (by omega)]; simp) r))).mono
      (by simp [Cond.size, Expr.size]; omega), by rw [hq]; exact F, ?_, ?_, ?_,
      f.mono (by intro z hz; simp at hz; simp [wqVars]; tauto)⟩
    · rw [hqa, hql, hr]; have := seg_of_filled hF'
      rw [show (pre ++ [qM0.length, qR0.length, N + lw.length] ++ qM0 ++ qR0).length =
          pre.length + 3 + qM0.length + qR0.length by simp; omega,
        show (seg fw a N ++ lw).length = N + lw.length by simp [hsl]] at this
      exact this
    · rw [hql, hr]; simp [hsl]
    · rw [hq]; simp [hqa, hql, swIn, hsl]; omega
  · have hr : realQ c P Q sg gw fw tr lw = qM0 := by
      rw [realQ, if_neg h0, if_neg h1, if_neg h2]
    have hq : qW c P Q sg gw fw tr lw = swIn qM0 qR0 qE0 := by
      rw [qW, if_neg h0, if_neg h1, if_neg h2]
    obtain ⟨σ', r, F, hqa, hql, f⟩ := wq3_run (W := W) hF hcap (by omega)
    have hF' : Filled "OB" "po" ((pre ++ [qM0.length, qR0.length, qE0.length]) ++ qM0 ++
        (qR0 ++ qE0)) σ' := by convert F using 1; simp [swIn]
    refine ⟨σ', (Run.ite_false (by rw [hcond 0 (by omega), decide_eq_false h0]) (Run.ite_false
      (by rw [hcond 1 (by omega), decide_eq_false h1]) (Run.ite_false
        (by rw [hcond 2 (by omega), decide_eq_false h2])
      r))).mono (by simp only [Cond.size, Expr.size]; generalize dK = D; omega), by rw [hq]; exact F, ?_, ?_, ?_,
      f.mono (by intro z hz; simp at hz; simp [wqVars]; tauto)⟩
    · rw [hqa, hql, hr]; have := seg_of_filled hF'
      rw [show (pre ++ [qM0.length, qR0.length, qE0.length]).length = pre.length + 3 by simp] at this
      exact this
    · rw [hql, hr]
    · rw [hq]; simp [hqa, hql, swIn]; omega

/-! ### The size check and the guard by kind -/

/-- `ovf := 1` unless `dK + |gw| + |fw| + |lw| < W / 8`. -/
noncomputable def sizeChk : Com :=
  .seq (satLit "oz" dK) (.seq (satAdd "oz" "pg" "oz") (.seq (satAdd "oz" "pf" "oz")
  (.seq (satAdd "oz" "lp" "oz")
    (.ite (.lt (.var "oz") (.div (.var "W") (.lit 8))) .skip (.assign "ovf" (.lit 1))))))

theorem sizeChk_run {W A F L : ℕ} {σ : Env} (hW : σ.vars "W" = W) (hW8 : 8 ≤ W)
    (hA : σ.vars "pg" = A) (hF : σ.vars "pf" = F) (hL : σ.vars "lp" = L) (hAW : A ≤ W)
    (hFW : F ≤ W) (hLW : L ≤ W) :
    ∃ σ', Run (W + 1) sizeChk σ σ' (30 * dK + 100) ∧
      σ'.vars "ovf" = (if dK + A + F + L < W / 8 then σ.vars "ovf" else 1) ∧
      OFr σ σ' ["oz", "ovf"] := by
  obtain ⟨σ₁, r₁, h₁, f₁, a₁, o₁, i₁⟩ := satLit_run (B := W + 1) (z := "oz") (by decide) (by omega)
    (by omega) dK σ hW
  have hW₁ : σ₁.vars "W" = W := by rw [f₁ _ (by decide), hW]
  have r₂ := satAdd_run (B := W + 1) (x := "oz") (y := "pg") (z := "oz") hW₁ (by omega)
    (by omega) (by rw [f₁ _ (by decide)]; omega)
  set σ₂ := σ₁.setVar "oz" (min (σ₁.vars "oz" + σ₁.vars "pg") W) with hσ₂
  have r₃ := satAdd_run (B := W + 1) (W := W) (x := "oz") (y := "pf") (z := "oz") (σ := σ₂)
    (by simp [hσ₂, hW₁]) (by omega) (by simp [hσ₂]) (by simp [hσ₂, f₁ _ (by decide : "pf" ≠ "oz"), hF, hFW])
  set σ₃ := σ₂.setVar "oz" (min (σ₂.vars "oz" + σ₂.vars "pf") W) with hσ₃
  have r₄ := satAdd_run (B := W + 1) (W := W) (x := "oz") (y := "lp") (z := "oz") (σ := σ₃)
    (by simp [hσ₃, hσ₂, hW₁]) (by omega) (by simp [hσ₃])
    (by simp [hσ₃, hσ₂, f₁ _ (by decide : "lp" ≠ "oz"), hL, hLW])
  set σ₄ := σ₃.setVar "oz" (min (σ₃.vars "oz" + σ₃.vars "lp") W) with hσ₄
  have hoz : σ₄.vars "oz" = min (dK + A + F + L) W := by
    simp [hσ₄, hσ₃, hσ₂, h₁, f₁ _ (by decide : "pg" ≠ "oz"), f₁ _ (by decide : "pf" ≠ "oz"),
      f₁ _ (by decide : "lp" ≠ "oz"), hA, hF, hL]
    omega
  have hW₄ : σ₄.vars "W" = W := by simp [hσ₄, hσ₃, hσ₂, hW₁]
  have hc : (Cond.lt (.var "oz") (.div (.var "W") (.lit 8))).evalB (W + 1) σ₄ =
      some (decide (min (dK + A + F + L) W < W / 8)) :=
    condLt_div hoz hW₄ (by omega) (by omega) (by omega)
  have hiff : min (dK + A + F + L) W < W / 8 ↔ dK + A + F + L < W / 8 := by omega
  have f₄ : OFr σ σ₄ ["oz"] := ⟨fun y hy => by
      have : y ≠ "oz" := by simpa using hy
      simp [hσ₄, hσ₃, hσ₂, this, f₁ y this], fun b _ => by simp [hσ₄, hσ₃, hσ₂, a₁],
    by simp [hσ₄, hσ₃, hσ₂, a₁], by simp [hσ₄, hσ₃, hσ₂, o₁], by simp [hσ₄, hσ₃, hσ₂, i₁]⟩
  by_cases hg : dK + A + F + L < W / 8
  · refine ⟨σ₄, ?_, by rw [if_pos hg]; exact f₄.vars _ (by decide), f₄.mono (by simp)⟩
    unfold sizeChk
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.ite_true
      (by rw [hc, decide_eq_true (hiff.2 hg)]) Run.skip))))).mono ?_
    simp only [Cond.size, Expr.size]; omega
  · refine ⟨σ₄.setVar "ovf" 1, ?_, by rw [if_neg hg]; simp,
      (f₄.trans (OFr.setVar _ "ovf" 1)).mono (by simp)⟩
    unfold sizeChk
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.seq r₄ (Run.ite_false
      (by rw [hc, decide_eq_false (fun h => hg (hiff.1 h))])
      (Run.assign (evalB_lit (by omega)))))))).mono ?_
    simp only [Cond.size, Expr.size]; omega

/-- The exponent of the guard of a call of kind `ck`. -/
def expOf (eM eR eE ck : ℕ) : ℕ := if ck = 1 then eR else if ck = 2 then eE else eM

/-- The guard of the callee that does the work. -/
def guardSel (eM eR eE d : ℕ) : Com :=
  .ite (.eq (.var "ck") (.lit 1)) (guardChk eR d)
    (.ite (.eq (.var "ck") (.lit 2)) (guardChk eE d) (guardChk eM d))

theorem guardSel_run {W eM eR eE d c a N : ℕ} {σ : Env} (hW : σ.vars "W" = W) (hW2 : 2 ≤ W)
    (hc : σ.vars "ck" = c) (hcW : c ≤ W)
    (ha : σ.vars "qa" = a) (hl : σ.vars "ql" = N) (hA : a + N ≤ (σ.arrs "OB").length)
    (hB : a + N ≤ W) (hv : ∀ v ∈ seg (σ.arrs "OB") a N, v ≤ W) :
    ∃ σ', Run (W + 1) (guardSel eM eR eE d) σ σ'
        (N * 30 + 60 * (eM + eR + eE + 1) + 30 * 2 ^ d + 220) ∧
      σ'.vars "ovf" = (if min ((N + maxEntry (seg (σ.arrs "OB") a N) + 1) ^ (expOf eM eR eE c + 1)) W ≤
        W / min (2 ^ d) W then σ.vars "ovf" else 1) ∧
      (∀ y, y ∉ gVars → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.inp = σ.inp := by
  have hcond : ∀ k : ℕ, k < 3 → (Cond.eq (.var "ck") (.lit k)).evalB (W + 1) σ = some (decide (c = k)) :=
    fun k hk => condEq_lit hc (by omega) (by omega)
  unfold guardSel
  by_cases h1 : c = 1
  · obtain ⟨σ', r, h, f⟩ := guardChk_run (e := eR) (d := d) hW hW2 ha hl hA hB hv
    refine ⟨σ', (Run.ite_true (by rw [hcond 1 (by omega), decide_eq_true h1]) r).mono ?_,
      by rw [h, expOf, if_pos h1], f⟩
    simp only [Cond.size, Expr.size]; nlinarith
  by_cases h2 : c = 2
  · obtain ⟨σ', r, h, f⟩ := guardChk_run (e := eE) (d := d) hW hW2 ha hl hA hB hv
    refine ⟨σ', (Run.ite_false (by rw [hcond 1 (by omega), decide_eq_false h1]) (Run.ite_true
      (by rw [hcond 2 (by omega), decide_eq_true h2]) r)).mono ?_,
      by rw [h, expOf, if_neg h1, if_pos h2], f⟩
    simp only [Cond.size, Expr.size]; nlinarith
  · obtain ⟨σ', r, h, f⟩ := guardChk_run (e := eM) (d := d) hW hW2 ha hl hA hB hv
    refine ⟨σ', (Run.ite_false (by rw [hcond 1 (by omega), decide_eq_false h1]) (Run.ite_false
      (by rw [hcond 2 (by omega), decide_eq_false h2]) r)).mono ?_,
      by rw [h, expOf, if_neg h1, if_neg h2], f⟩
    simp only [Cond.size, Expr.size]; nlinarith


/-- The output: the head, then the query. -/
noncomputable def oW (tag k : ℕ) (sc gw fw lw : List ℕ) (c P Q sg : ℕ) (tr : List ℕ) : List ℕ :=
  hdW tag k (stW sc gw fw lw) ++ qW c P Q sg gw fw tr lw

theorem dummies_le {W v : ℕ} (hK : dK ≤ W) (h : v ∈ qM0 ∨ v ∈ qR0 ∨ v ∈ qE0) : v ≤ W :=
  (le_dK_of_mem h).trans hK

theorem realQ_le {W c P Q sg : ℕ} {gw fw tr lw : List ℕ} (hK : dK ≤ W)
    (hv : ∀ v ∈ gw ++ fw ++ lw, v ≤ W) (htr : ∀ v ∈ tr, v ≤ W) (hP : P ≤ W) (hQ : Q ≤ W)
    (hs : sg ≤ W) : ∀ v ∈ realQ c P Q sg gw fw tr lw, v ≤ W := by
  intro v hv'
  unfold realQ at hv'
  split_ifs at hv' with h0 h1 h2
  · exact htr v hv'
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with (h | rfl | rfl | rfl) | h
    · exact hv v (by simp [h])
    · exact hP
    · exact hQ
    · exact hs
    · exact hv v (by simp [h])
  · simp only [List.mem_append] at hv'
    rcases hv' with h | h
    · exact htr v h
    · exact hv v (by simp [h])
  · exact dummies_le hK (Or.inl hv')

theorem oW_le {W tag k c P Q sg : ℕ} {sc gw fw tr lw : List ℕ} (htg : tag ≤ W) (hk : k ≤ W)
    (hsc : ∀ x ∈ sc, x ≤ W)
    (hL : sc.length + 5 * (gw.length + fw.length + lw.length) + dK + 20 ≤ W)
    (hv : ∀ v ∈ gw ++ fw ++ lw, v ≤ W) (htr : ∀ v ∈ tr, v ≤ W) (hP : P ≤ W) (hQ : Q ≤ W)
    (hs : sg ≤ W) (htrl : tr.length ≤ 4 * fw.length) :
    ∀ v ∈ oW tag k sc gw fw lw c P Q sg tr, v ≤ W := by
  have hK := lens_le_dK
  have hr := realQ_le (c := c) (by omega) hv htr hP hQ hs
  have hrl := length_realQ_le c P Q sg gw fw tr lw htrl
  have hd : ∀ v : ℕ, (v ∈ qM0 ∨ v ∈ qR0 ∨ v ∈ qE0) → v ≤ W := fun v h => dummies_le (by omega) h
  intro v hv'
  simp only [oW, List.mem_append] at hv'
  rcases hv' with h | h
  · simp only [hdW, List.mem_cons] at h
    rcases h with h | h | h | h
    · rw [h]; exact htg
    · rw [h, length_stW]; omega
    · rw [h]; exact hk
    · simp only [stW, List.mem_append] at h
      rcases h with (((h | h) | h) | h) | h
      · exact hsc v h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h <;> rw [h] <;> omega
      · exact hv v (by simp [h])
      · exact hv v (by simp [h])
      · exact hv v (by simp [h])
  · unfold qW at h
    split_ifs at h
    all_goals
      simp only [swIn, List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h <;> rw [h] <;> omega
      all_goals first | exact hr v h | exact hd v (by tauto)

/-! ### The output of a round with a call -/


/-- The writer of a round with a call: the size check, the head and the
query into `OB`, the entry check, the guard, and the output. -/
noncomputable def outCmd (eM eR eE d : ℕ) : Com :=
  .seq sizeChk (.ite (.eq (.var "ovf") (.lit 0))
    (.seq (.assign "po" (.lit 0)) (.seq wrHd (.seq wrQ (.seq entChk
      (.seq (guardSel eM eR eE d) wrAll))))) .skip)

theorem length_oW_le (tag k : ℕ) (sc gw fw lw : List ℕ) (c P Q sg : ℕ) (tr : List ℕ)
    (hsc : sc.length = 11) (htr : tr.length ≤ 4 * fw.length) :
    (oW tag k sc gw fw lw c P Q sg tr).length ≤
      5 * (gw.length + fw.length + lw.length) + dK + 23 := by
  have := length_qW_le c P Q sg gw fw tr lw htr
  simp only [oW, hdW, List.length_append, List.length_cons, length_stW, hsc]
  omega

open Lax185574.WordEncoding Lax185574.TypeTrees in
theorem outCmd_run {W eM eR eE d tag k c P Q sg a N : ℕ} {σ : Env} {gw fw lw tr : List ℕ}
    (hW : σ.vars "W" = W) (hW64 : 64 ≤ W) (hovf : σ.vars "ovf" = 0)
    (hGW : Filled "GW" "pg" gw σ) (hFW : Filled "FW" "pf" fw σ) (hlo : Filled "lo" "lp" lw σ)
    (htg : σ.vars "otg" = tag) (hk : σ.vars "okk" = k) (hc : σ.vars "ck" = c)
    (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hs : σ.vars "cs" = sg)
    (hta : σ.vars "ta" = a) (htl : σ.vars "tl" = N) (htr : TrOK c P Q a N fw tr)
    (hgn : ∀ ts : List TypeTree, c = 0 → fw = ts.length :: (ts.map toWord).flatten →
      σ.vars "gn" = ts.length)
    (htrl : tr.length ≤ 4 * fw.length) (htrv : ∀ v ∈ tr, v ≤ W)
    (hsc : ∀ x ∈ scN, σ.vars x ≤ W) (htk : tag ≤ W) (hkW : k ≤ W)
    (hcap : (σ.arrs "OB").length = W + 1)
    (hlg : gw.length ≤ W) (hlf : fw.length ≤ W) (hll : lw.length ≤ W)
    (hv : ∀ v ∈ gw ++ fw ++ lw, v ≤ W) :
    ∃ σ', Run (W + 1) (outCmd eM eR eE d) σ σ'
        (700 * (gw.length + fw.length + lw.length + dK) + 60 * (eM + eR + eE + 1) +
          30 * 2 ^ d + 3000) ∧
      (σ'.vars "ovf" = 0 →
        σ'.out = σ.out ++ oW tag k (scN.map σ.vars) gw fw lw c P Q sg tr ∧
        maxEntry (oW tag k (scN.map σ.vars) gw fw lw c P Q sg tr) < W / 32 / 32 ∧
        min (((realQ c P Q sg gw fw tr lw).length +
          maxEntry (realQ c P Q sg gw fw tr lw) + 1) ^ (expOf eM eR eE c + 1)) W ≤
          W / min (2 ^ d) W) ∧
      (dK + gw.length + fw.length + lw.length < W / 8 →
        maxEntry (oW tag k (scN.map σ.vars) gw fw lw c P Q sg tr) < W / 32 / 32 →
        min (((realQ c P Q sg gw fw tr lw).length +
          maxEntry (realQ c P Q sg gw fw tr lw) + 1) ^ (expOf eM eR eE c + 1)) W ≤
          W / min (2 ^ d) W → σ'.vars "ovf" = 0) := by
  have hK := lens_le_dK
  have hPW : P ≤ W := hP ▸ hsc "cP" (by decide)
  have hQW : Q ≤ W := hQ ▸ hsc "cQ" (by decide)
  have hsW : sg ≤ W := hs ▸ hsc "cs" (by decide)
  have hcW : c ≤ W := hc ▸ hsc "ck" (by decide)
  obtain ⟨σ₁, r₁, h₁, f₁⟩ := sizeChk_run (A := gw.length) (F := fw.length) (L := lw.length) hW
    (by omega) hGW.pos hFW.pos hlo.pos hlg hlf hll
  have hc₁ : (Cond.eq (.var "ovf") (.lit 0)).evalB (W + 1) σ₁ =
      some (decide (σ₁.vars "ovf" = 0)) := condEq_lit rfl (by rw [h₁]; split_ifs <;> omega) (by omega)
  by_cases hS : dK + gw.length + fw.length + lw.length < W / 8
  swap
  · rw [if_neg hS] at h₁
    refine ⟨σ₁, (Run.seq r₁ (Run.ite_false (by rw [hc₁, h₁]; rfl) Run.skip)).mono ?_,
      fun h => absurd (h₁.symm.trans h) (by omega), fun h => absurd h hS⟩
    simp only [Cond.size, Expr.size]; omega
  rw [if_pos hS, hovf] at h₁
  -- the buffer
  set σ₂ := σ₁.setVar "po" 0 with hσ₂
  have f₂ := f₁.trans (OFr.setVar σ₁ "po" 0)
  have F₂ : Filled "OB" "po" [] σ₂ := Filled.empty "OB" "po" σ₁
  have v₂ : ∀ y, y ∉ ["oz", "ovf", "po"] → σ₂.vars y = σ.vars y := fun y hy => f₂.vars y (by simpa using hy)
  obtain ⟨σ₃, r₃, F₃, fv₃, hz₃, fa₃, fl₃, fo₃, fi₃⟩ := wrHd_run (W := W) (tag := tag) (k := k) F₂
    (hGW.congr (v₂ _ (by decide)) (f₂.arrs _ (by decide)))
    (hFW.congr (v₂ _ (by decide)) (f₂.arrs _ (by decide)))
    (hlo.congr (v₂ _ (by decide)) (f₂.arrs _ (by decide)))
    (by rw [v₂ _ (by decide), htg]) (by rw [v₂ _ (by decide), hk])
    (fun x hx => by
      rw [v₂ x (by intro h; revert hx; simp at h; rcases h with rfl | rfl | rfl <;> decide)]
      exact hsc x hx)
    htk hkW (by rw [f₂.len, hcap]) (by omega) hv
  have hscN : scN.map σ₂.vars = scN.map σ.vars :=
    List.map_congr_left fun x hx => v₂ x (by intro h; revert hx; simp at h; rcases h with rfl | rfl | rfl <;> decide)
  rw [hscN] at F₃
  set hd := hdW tag k (stW (scN.map σ.vars) gw fw lw) with hhd
  have hlhd : hd.length = 17 + gw.length + fw.length + lw.length := by
    simp [hhd, hdW, length_stW, scN]; omega
  have v₃ : ∀ y, y ∉ ["oz", "ovf", "po", "ci", "qz"] → σ₃.vars y = σ.vars y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [fv₃ y hy.2.2.2.1 hy.2.2.1 hy.2.2.2.2, v₂ y (by simp; tauto)]
  have a₃ : ∀ b, b ≠ "OB" → σ₃.arrs b = σ.arrs b := fun b hb => by rw [fa₃ b hb, f₂.arrs b hb]
  obtain ⟨σ₄, r₄, F₄, hseg₄, hql₄, hqa₄, f₄⟩ := wrQ_run (W := W) (c := c) (P := P) (Q := Q) (sg := sg)
    (a := a) (N := N) F₃ (hGW.congr (v₃ _ (by decide)) (a₃ _ (by decide)))
    (hFW.congr (v₃ _ (by decide)) (a₃ _ (by decide)))
    (hlo.congr (v₃ _ (by decide)) (a₃ _ (by decide)))
    hz₃
    (by rw [v₃ _ (by decide), hc]) (by rw [v₃ _ (by decide), hP]) (by rw [v₃ _ (by decide), hQ])
    (by rw [v₃ _ (by decide), hs]) (by rw [v₃ _ (by decide), hta]) (by rw [v₃ _ (by decide), htl])
    htr (fun ts h0 hfw => by rw [v₃ _ (by decide)]; exact hgn ts h0 hfw)
    (by rw [fl₃, f₂.len, hcap]) (by rw [hlhd]; omega) hv hPW hQW hsW hcW
  set o := oW tag k (scN.map σ.vars) gw fw lw c P Q sg tr with ho
  have hoeq : hd ++ qW c P Q sg gw fw tr lw = o := rfl
  rw [hoeq] at F₄ hqa₄
  have hlo' : o.length ≤ 5 * (gw.length + fw.length + lw.length) + dK + 23 :=
    length_oW_le _ _ _ _ _ _ _ _ _ _ _ (by simp [scN]) htrl
  have hoW : ∀ v ∈ o, v ≤ W := oW_le htk hkW (fun x hx => by
      simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact hsc y hy)
    (by simp only [List.length_map, scN, List.length_cons, List.length_nil]; omega) hv htrv hPW hQW hsW
    htrl
  have v₄ : ∀ y, y ∉ ["oz", "ovf", "po", "ci", "qz"] ++ wqVars → σ₄.vars y = σ.vars y :=
    fun y hy => by
      rw [f₄.vars y (fun h => hy (List.mem_append_right _ h)),
        v₃ y (fun h => hy (List.mem_append_left _ h))]
  have hW₄ : σ₄.vars "W" = W := by rw [v₄ _ (by decide), hW]
  have hov₄ : σ₄.vars "ovf" = 0 := by
    rw [f₄.vars _ (by decide), fv₃ _ (by decide) (by decide) (by decide)]
    simp [hσ₂, h₁]
  obtain ⟨σ₅, r₅, h₅, fv₅, fa₅, fo₅, fi₅⟩ := entChk_run hW₄ (by omega) F₄
    (by omega) hoW
  have hW₅ : σ₅.vars "W" = W := by rw [fv₅ _ (by decide), hW₄]
  set u := realQ c P Q sg gw fw tr lw with hu
  have hql₅ : σ₅.vars "ql" = u.length := by rw [fv₅ _ (by decide), hql₄]
  have hqa₅ : σ₅.vars "qa" = σ₄.vars "qa" := fv₅ _ (by decide)
  have hseg₅ : seg (σ₅.arrs "OB") (σ₄.vars "qa") u.length = u := by rw [fa₅, ← hql₄]; exact hseg₄
  have hlenOB : (σ₅.arrs "OB").length = W + 1 := by rw [fa₅, f₄.len, fl₃, f₂.len, hcap]
  have hlu : u.length ≤ gw.length + 4 * fw.length + lw.length + dK := length_realQ_le _ _ _ _ _ _ _ _ htrl
  obtain ⟨σ₆, r₆, h₆, fv₆, fa₆, fo₆, fi₆⟩ := guardSel_run (eM := eM) (eR := eR) (eE := eE) (d := d)
    (c := c) hW₅ (by omega) (by rw [fv₅ _ (by decide), v₄ _ (by decide), hc]) hcW hqa₅ hql₅
    (by rw [hlenOB]; omega) (by omega)
    (by rw [hseg₅]; exact realQ_le (by omega) hv htrv hPW hQW hsW)
  rw [hseg₅] at h₆
  have hF₆ : Filled "OB" "po" o σ₆ :=
    F₄.congr (by rw [fv₆ _ (by decide), fv₅ _ (by decide)]) (by rw [fa₆, fa₅])
  obtain ⟨σ₇, r₇, ho₇⟩ := wrAll_run (B := W + 1) hF₆ (by omega) (fun v hv' => by
    have := hoW v hv'; omega)
  have hov₇ : σ₇.vars "ovf" = σ₆.vars "ovf" := r₇.frame_var _ (by decide)
  have hout : σ₇.out = σ.out ++ o := by
    rw [ho₇, fo₆, fo₅, f₄.out, fo₃, f₂.out]
  have hc₁' : (Cond.eq (.var "ovf") (.lit 0)).evalB (W + 1) σ₁ = some true := by
    rw [hc₁, h₁]; rfl
  refine ⟨σ₇, ?_, fun h => ?_, fun _ hE hG => ?_⟩
  · refine (Run.seq r₁ (Run.ite_true hc₁' (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq r₃ (Run.seq r₄ (Run.seq r₅ (Run.seq r₆ r₇))))))).mono ?_
    simp only [Cond.size, Expr.size]
    have h1 := hlo'
    have h2 := hlu
    generalize 2 ^ d = T
    generalize o.length = lo at h1 ⊢
    generalize u.length = lu at h2 ⊢
    generalize dK = D at h1 h2 ⊢
    omega
  · rw [hov₇, h₆] at h
    split_ifs at h with hG
    rw [h₅, hov₄] at h
    split_ifs at h with hE
    exact ⟨hout, hE, hG⟩
  · rw [hov₇, h₆, if_pos hG, h₅, if_pos hE, hov₄]

/-! ### The output of the last round -/

/-- The writer of the last round: `0, 1` and the bit in `fb`. -/
def outEnd : Com :=
  .seq (.assign "po" (.lit 0)) (.seq (pushL "OB" "po" [.lit 0, .lit 1, .var "fb"])
    (.seq entChk wrAll))

theorem outEnd_run {W bit : ℕ} {σ : Env} (hW : σ.vars "W" = W) (hW64 : 64 ≤ W)
    (hb : σ.vars "fb" = bit) (hbit : bit ≤ 1) (hcap : (σ.arrs "OB").length = W + 1) :
    ∃ σ', Run (W + 1) outEnd σ σ' 300 ∧
      σ'.vars "ovf" = (if maxEntry [0, 1, bit] < W / 32 / 32 then σ.vars "ovf" else 1) ∧
      σ'.out = σ.out ++ [0, 1, bit] := by
  set σ₁ := σ.setVar "po" 0 with hσ₁
  have F₁ : Filled "OB" "po" [] σ₁ := Filled.empty "OB" "po" σ
  obtain ⟨σ₂, r₂, F₂, fv₂, fa₂, fl₂, fo₂, fi₂⟩ := pushL_run (B := W + 1) (es := [.lit 0, .lit 1, .var "fb"])
    (vs := [0, 1, bit]) F₁ (fun τ' hv _ => by
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true]
      exact ⟨evalB_lit (by omega), evalB_lit (by omega),
        ev_var (by rw [hv _ (by decide)]; simp [hσ₁, hb]) (by omega)⟩)
    (by simp [hσ₁, hcap]; omega) (by simp; omega)
  have hW₂ : σ₂.vars "W" = W := by rw [fv₂ _ (by decide)]; simp [hσ₁, hW]
  obtain ⟨σ₃, r₃, h₃, fv₃, fa₃, fo₃, fi₃⟩ := entChk_run (o := [0, 1, bit]) hW₂ (by omega)
    (by simpa using F₂) (by simp; omega) (by intro v hv; simp at hv; omega)
  have F₃ : Filled "OB" "po" [0, 1, bit] σ₃ :=
    (by simpa using F₂ : Filled "OB" "po" [0, 1, bit] σ₂).congr (fv₃ _ (by decide)) (by rw [fa₃])
  obtain ⟨σ₄, r₄, ho₄⟩ := wrAll_run (B := W + 1) F₃ (by simp; omega)
    (by intro v hv; simp at hv; omega)
  refine ⟨σ₄, ?_, ?_, ?_⟩
  · unfold outEnd
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₂ (Run.seq r₃ r₄))).mono ?_
    simp [Expr.size]
  · rw [r₄.frame_var _ (by decide), h₃, fv₂ _ (by decide)]; simp [hσ₁]
  · rw [ho₄, fo₃, fo₂]; simp [hσ₁]

end Lax185574Proofs.MC.Glue
