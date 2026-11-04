import Lax185574Proofs.MC.Glue.NextW

/-!
Issuing a call, at the end of a round of the glue program of thm:mc
after the first.

Once the fields of the call are set and the words of its state are in
`GW`, `FW` and `lo`, `issue` finds the tree of the evaluation (`tLoc`), sets
the tag (`tagSet`) and writes the head and the query (`outCmd`).
`issue_run`: if `ovf` stays `0` the output is `hdOf c ++ callQ c`, and
`ovf` stays `0` under the size bound, the entry bound and the guard on
the query `workQ` of the working callee.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees

variable {n : ℕ}

/-- Find the tree, set the tag, write. -/
noncomputable def issue (eM eR eE d : ℕ) : Com := .seq tLoc (.seq tagSet (outCmd eM eR eE d))

theorem ckOf_le (c : PCall n) : ckOf c ≤ 3 := by
  cases c <;> simp [ckOf] <;> split_ifs <;> omega

theorem ctOf_le (σ : Script n) {c : PCall n} (hc : Valid σ.steps c) :
    ctOf σ.steps.length c ≤ σ.steps.length := by
  cases c with
  | merge t P Q => exact (step_lt (show σ.steps[t]? = some (.merge P Q) from hc)).le
  | resolve t sg P Q => exact (step_lt hc).le
  | eval a => simp [ctOf]

/-- The cost of `issue`. -/
noncomputable def issueC (eM eR eE d L : ℕ) : ℕ :=
  900 * L + 900 * dK + 60 * (eM + eR + eE + 1) + 30 * 2 ^ d + 4000

set_option maxHeartbeats 1000000 in
theorem issue_run {W eM eR eE d : ℕ} (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n)
    (c : PCall n) (hval : Valid σ.steps c) {τ : Env} (hrk : τ.vars "rk" = Lax3.FirstOrder.rank φ)
    (hf : HasFields σ.steps.length c τ) (hgn : τ.vars "gn" = n) (hsm : τ.vars "sm" = σ.steps.length)
    (hoff : τ.vars "off" = n + 3) (hW : τ.vars "W" = W) (hW64 : 64 ≤ W) (hovf : τ.vars "ovf" = 0)
    (hGW : Filled "GW" "pg" (gwOf σ.run σ.steps.length c) τ)
    (hFW : Filled "FW" "pf" (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c) τ)
    (hlo : Filled "lo" "lp" (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) τ)
    (hOB : (τ.arrs "OB").length = W + 1) (hvals : ValsLt (W + 1) τ)
    (hb : n + 3 + 3 * (σ.steps.length + 1) ≤ W)
    (hfl : 2 * (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length + n < W) :
    let q := Lax3.FirstOrder.rank φ
    let lw := Lax185574.DistanceLogic.DistFO.code (loc q φ)
    let gw := gwOf σ.run σ.steps.length c
    let fw := fwOf σ.run q σ.steps.length c
    let o := hdOf σ.run q (n + 3) σ.steps.length lw c ++ callQ σ.run q φ c
    let u := workQ σ.run q φ c
    ∃ τ', Run (W + 1) (issue eM eR eE d) τ τ' (issueC eM eR eE d (gw.length + fw.length + lw.length + n)) ∧
      (τ'.vars "ovf" = 0 → τ'.out = τ.out ++ o ∧ maxEntry o < W / 32 / 32 ∧
        min ((u.length + maxEntry u + 1) ^ (expOf eM eR eE (ckOf c) + 1)) W ≤ W / min (2 ^ d) W) ∧
      (dK + gw.length + fw.length + lw.length < W / 8 → maxEntry o < W / 32 / 32 →
        min ((u.length + maxEntry u + 1) ^ (expOf eM eR eE (ckOf c) + 1)) W ≤ W / min (2 ^ d) W →
        τ'.vars "ovf" = 0) := by
  intro q lw gw fw o u
  obtain ⟨hck, hct, hcv, hcP, hcQ, hcs⟩ := hf
  have hts := fwOf_tsOf σ.run q σ.steps.length c
  have hlt := length_tsOf σ.run q σ.steps.length c
  have hcvn : cvOf c < n := by simp only [cvOf]; exact hn
  have hFW' : Filled "FW" "pf" ((tsOf σ.run q σ.steps.length c).length ::
      ((tsOf σ.run q σ.steps.length c).map toWord).flatten) τ := by rw [hlt, ← hts]; exact hFW
  have hflt : fw.length = 1 + ((tsOf σ.run q σ.steps.length c).map toWord).flatten.length := by
    simp only [fw, hts, List.length_cons]; omega
  obtain ⟨τ₁, r₁, hT₁, fv₁, fa₁, fi₁, fo₁'⟩ := tLoc_run (W := W) (v := cvOf c) (k := ckOf c)
    (ts := tsOf σ.run q σ.steps.length c) hck (ckOf_le c) hcv (by rw [hlt]; exact hcvn) hFW'
    (by have hfl' : 2 * fw.length + n < W := hfl; rw [hlt]; omega) (hvals.2.1 "FW")
  have hv₁ := Run.vals_lt r₁ hvals
  have e₁ : ∀ y ∈ ["ck", "cv", "ct", "cP", "cQ", "cs", "gn", "sm", "off", "rk", "W", "ovf", "pg",
      "pf", "lp"], τ₁.vars y = τ.vars y := fun y hy => fv₁ y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    rcases hy with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)
  have hctm := ctOf_le σ hval
  obtain ⟨τ₂, r₂, htg₂, hk₂, hs0₂, f₂⟩ := tagSet_run (W := W) (m := σ.steps.length) (o := n + 3)
    (τ := τ₁) c (by rw [e₁ "ck" (by simp), hck])
    (by rw [e₁ "ct" (by simp), hct])
    (by rw [e₁ "sm" (by simp), hsm]) (by rw [e₁ "off" (by simp), hoff]) (by omega)
    (by have := ckOf_le c; omega) (by omega) (by omega)
  have hv₂ := Run.vals_lt r₂ hv₁
  have e₂ : ∀ y ∈ ["ck", "cv", "ct", "cP", "cQ", "cs", "gn", "sm", "off", "rk", "W", "ovf", "pg",
      "pf", "lp"] ++ ["ta", "tl"], τ₂.vars y = τ₁.vars y := fun y hy => f₂.vars y (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    rcases hy with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      decide)
  have ee : ∀ y ∈ ["ck", "cv", "ct", "cP", "cQ", "cs", "gn", "sm", "off", "rk", "W", "ovf", "pg",
      "pf", "lp"], τ₂.vars y = τ.vars y := fun y hy => by
    rw [e₂ y (List.mem_append_left _ hy), e₁ y hy]
  have ha₂ : ∀ b, τ₂.arrs b = τ.arrs b := fun b => by
    by_cases hb : b = "OB"
    · subst hb; rw [r₂.frame_arr "OB" (by simp [tagSet, lastChk, setIf, tag1, tag2, Com.warrs]), fa₁]
    · rw [f₂.arrs b hb, fa₁]
  have hGW₂ := hGW.congr (ee "pg" (by simp)) (ha₂ "GW")
  have hFW₂ : Filled "FW" "pf" fw τ₂ := hFW.congr (ee "pf" (by simp)) (ha₂ "FW")
  have hlo₂ := hlo.congr (ee "lp" (by simp)) (ha₂ "lo")
  have hlW : ∀ {a pv : String} {l : List ℕ}, Filled a pv l τ₂ → l.length ≤ W := fun {a pv l} h => by
    have := hv₂.1 pv; rw [h.pos] at this; omega
  have hEW : ∀ v ∈ gw ++ fw ++ lw, v ≤ W := fun v h => by
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · have := Filled.lt_of_vals hGW₂ hv₂ v h; omega
    · have := Filled.lt_of_vals hFW₂ hv₂ v h; omega
    · have := Filled.lt_of_vals hlo₂ hv₂ v h; omega
  have htag : tagOf σ.steps.length c ≤ 2 := by unfold tagOf; split_ifs <;> omega
  have hkk : kOf σ.steps.length c ≤ 3 := by unfold kOf; split_ifs <;> omega
  -- the segment is the tree of the evaluation
  have hev : ckOf c = 2 → τ₁.vars "ta" + τ₁.vars "tl" ≤ fw.length ∧
      trOf σ.run q c = seg fw (τ₁.vars "ta") (τ₁.vars "tl") := by
    intro h2
    obtain ⟨a, rfl⟩ : ∃ a, c = .eval a := by
      cases c with
      | merge t P Q => simp only [ckOf] at h2; split_ifs at h2 <;> omega
      | resolve => simp [ckOf] at h2
      | eval a => exact ⟨a, rfl⟩
    have h := hT₁ (Or.inr h2)
    refine ⟨by rw [hflt]; exact h.1, ?_⟩
    have hfw' : fw = (tsOf σ.run q σ.steps.length (.eval a)).length ::
        ((tsOf σ.run q σ.steps.length (.eval a)).map toWord).flatten := by rw [hlt]; exact hts
    have ha0 : a.val = 0 := hval
    rw [hfw', h.2]
    have := tsOf_eval σ q a
    simp only [trOf]
    convert (congrArg toWord this).symm using 3
    simp [cvOf, ha0]
  have hPW : cPOf c ≤ W := by rw [← hcP]; have := hv₂.1 "cP"; rw [ee "cP" (by simp)] at this; omega
  have hQW : cQOf c ≤ W := by rw [← hcQ]; have := hv₂.1 "cQ"; rw [ee "cQ" (by simp)] at this; omega
  obtain ⟨htrl, htrv⟩ := trOf_bounds σ.run q σ.steps.length c hev
    (fun v h => hEW v (List.mem_append_left _ (List.mem_append_right _ h))) hPW hQW (by
      have h1 : (fwOf σ.run q σ.steps.length c).length =
        (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length := rfl
      omega)
  obtain ⟨τ₃, r₃, hS, hC⟩ := outCmd_run (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d)
    (tag := tagOf σ.steps.length c) (k := kOf σ.steps.length c) (c := ckOf c) (P := cPOf c)
    (Q := cQOf c) (sg := csOf c) (a := τ₁.vars "ta") (N := τ₁.vars "tl") (σ := τ₂) (gw := gw)
    (fw := fw) (lw := lw) (tr := trOf σ.run q c) (by rw [ee "W" (by simp), hW]) hW64
    (by rw [ee "ovf" (by simp), hovf])
    hGW₂ hFW₂ hlo₂ htg₂ hk₂ (by rw [ee "ck" (by simp), hck]) (by rw [ee "cP" (by simp), hcP])
    (by rw [ee "cQ" (by simp), hcQ]) (by rw [ee "cs" (by simp), hcs]) (e₂ "ta" (List.mem_append_right _ (by simp)))
    (e₂ "tl" (List.mem_append_right _ (by simp))) (trOK_of σ.run q σ.steps.length c _ _ hev)
    (fun ts _ hfw => by rw [ee "gn" (by simp), hgn]; exact (gn_of_fwOf hfw).symm) htrl htrv
    (fun y _ => by have := hv₂.1 y; omega) (by omega) (by omega)
    (by rw [ha₂, hOB]) (hlW hGW₂) (hlW hFW₂) (hlW hlo₂) hEW
  have hsc : scN.map τ₂.vars = scOf (n + 3) σ.steps.length q c := by
    simp only [scN, scOf, List.map_cons, List.map_nil]
    rw [hs0₂, ee "gn" (by simp), ee "sm" (by simp), ee "off" (by simp), ee "rk" (by simp),
      ee "ck" (by simp), ee "ct" (by simp), ee "cv" (by simp), ee "cP" (by simp), ee "cQ" (by simp),
      ee "cs" (by simp), hgn, hsm, hoff, hrk, hck, hct, hcv, hcP, hcQ, hcs]
  have hoeq : oW (tagOf σ.steps.length c) (kOf σ.steps.length c) (scN.map τ₂.vars) gw fw lw (ckOf c)
      (cPOf c) (cQOf c) (csOf c) (trOf σ.run q c) = o := by
    rw [oW, hsc, qW_trOf σ.run q σ.steps.length φ c]; rfl
  have hueq : realQ (ckOf c) (cPOf c) (cQOf c) (csOf c) gw fw (trOf σ.run q c)
      lw = u := realQ_call σ.run q σ.steps.length φ c
  rw [hoeq, hueq] at hS hC
  refine ⟨τ₃, ?_, fun h => ?_, hC⟩
  · refine (Run.seq r₁ (Run.seq r₂ r₃)).mono ?_
    rw [hlt]
    unfold issueC
    have h1 : ((tsOf σ.run q σ.steps.length c).map toWord).flatten.length ≤ fw.length := by omega
    clear * - h1
    generalize dK = D
    generalize 2 ^ d = T
    omega
  · obtain ⟨ho, hE, hG⟩ := hS h
    exact ⟨by rw [ho, r₂.out_eq (by simp [tagSet, lastChk, setIf, tag1, tag2, Com.NoWrite]), fo₁'], hE, hG⟩

end Lax185574Proofs.MC.Glue
