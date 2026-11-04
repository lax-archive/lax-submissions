import Lax185574Proofs.ResolveRam.Glue.Lib

/-!
Writing a list of words of the library that is given by ranges.

The array `PR` holds pairs `lo, N` (`np` of them). `wrPlan` writes the
word of the list of the library words of all these ranges, one range
after the other (`wrPlan_run`). A later round of the glue program writes
the words of its new state in this way.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- The words of the ranges `ps` of `L`. -/
def planW (L : List (List ℕ)) (ps : List (ℕ × ℕ)) : List (List ℕ) := ps.flatMap fun p => rng L p.1 p.2

/-- The entries of the array `PR` for the ranges `ps`. -/
def prW (ps : List (ℕ × ℕ)) : List ℕ := ps.flatMap fun p => [p.1, p.2]

theorem prW_get {ps : List (ℕ × ℕ)} {k : ℕ} (hk : k < ps.length) :
    (prW ps)[k + k]? = some ps[k].1 ∧ (prW ps)[k + k + 1]? = some ps[k].2 := by
  induction ps generalizing k with
  | nil => simp at hk
  | cons p ps ih =>
    cases k with
    | zero => simp [prW]
    | succ k =>
      have := ih (k := k) (by simpa using hk)
      have e : prW (p :: ps) = [p.1, p.2] ++ prW ps := by simp [prW]
      rw [e, show k + 1 + (k + 1) = 2 + (k + k) by omega, show 2 + (k + k) + 1 = 2 + (k + k + 1) by omega,
        List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
      simpa using this

theorem planW_succ {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {k : ℕ} (hk : k < ps.length) :
    planW L (ps.take (k + 1)) = planW L (ps.take k) ++ rng L ps[k].1 ps[k].2 := by
  simp only [planW, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp

/-- The body of `wrPlan`. -/
def wrPlanBody : Com :=
  .seq (.assign "lo" (.get "PR" (.add (.var "pk") (.var "pk"))))
    (.seq (.assign "lN" (.get "PR" (.add (.add (.var "pk") (.var "pk")) (.lit 1))))
      (.seq emRng (.assign "pq" (.add (.var "pq") (.var "lN")))))

/-- Write the word of the list of the words of the ranges in `PR`. -/
def wrPlan : Com :=
  .seq (.assign "pz" (.var "po")) (.seq (push1 "OB" "po" (.lit 0)) (.seq (.assign "pq" (.lit 0))
    (.seq (forUp "pk" (.var "np") wrPlanBody) (.store "OB" (.var "pz") (.var "pq")))))

theorem length_planW {L : List (List ℕ)} {ps : List (ℕ × ℕ)} (h : ∀ p ∈ ps, p.1 + p.2 ≤ L.length) :
    (planW L ps).length = (ps.map Prod.snd).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [planW, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih (fun q hq => h q (by simp [hq])), length_rng (h p (by simp))]

theorem planW_sub_size (L : List (List ℕ)) (ps : List (ℕ × ℕ)) :
    total (planW L ps) + (planW L ps).length ≤ ps.length * (total L + L.length) := by
  induction ps with
  | nil => simp [planW, total]
  | cons p ps ih =>
    simp only [planW, List.flatMap_cons, List.length_append, total_append, List.length_cons] at ih ⊢
    have := size_sub (rng_sub L p.1 p.2)
    nlinarith

theorem length_prW (ps : List (ℕ × ℕ)) : (prW ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [prW] at ih ⊢; omega

/-- The cost of the range `k` of a plan. -/
def planK (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  20 * total (rng L (ps.getD k (0, 0)).1 (ps.getD k (0, 0)).2) + 40 * (ps.getD k (0, 0)).2 + 60

theorem sum_planK (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (h : ∀ p ∈ ps, p.1 + p.2 ≤ L.length) :
    ∀ N, N ≤ ps.length → ∑ k ∈ Finset.range N, planK L ps k =
      20 * total (planW L (ps.take N)) + 40 * (planW L (ps.take N)).length + 60 * N := by
  intro N
  induction N with
  | zero => intro _; simp [planW, total]
  | succ N ih =>
    intro hN
    have hk : N < ps.length := by omega
    have hp := h _ (List.getElem_mem hk)
    rw [Finset.sum_range_succ, ih (by omega), planW_succ hk, total_append, List.length_append,
      length_rng hp]
    simp only [planK, List.getD_eq_getElem _ _ hk]
    ring

/-- The scalars that `wrPlan` writes. -/
def wpV : List String := ["pz", "pq", "pk", "lo", "lN", "fk", "ow", "wa", "wl", "po", "ci"]

/-- **Writing the words of the ranges.** -/
theorem wrPlan_run {W : ℕ} {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {τ : Env} {pre : List ℕ}
    (hw : WordsAt L τ) (hPR : PreAt "PR" (prW ps) τ) (hnp : τ.vars "np" = ps.length)
    (hps : ∀ p ∈ ps, p.1 + p.2 ≤ L.length) (hF : Filled "OB" "po" pre τ)
    (hcap : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 2 + (ps.length + 1) * (total L + L.length + 1) ≤ W)
    (hPW2 : 2 * ps.length + 2 ≤ W)
    (hv : ∀ w ∈ L, ∀ v ∈ w, v ≤ W) (ha : total L ≤ (τ.arrs "a").length) :
    ∃ τ', Run (W + 1) wrPlan τ τ'
        (40 * (total (planW L ps) + (planW L ps).length) + 100 * ps.length + 40) ∧
      Filled "OB" "po" (pre ++ toWord (planW L ps)) τ' ∧
      OFr τ τ' wpV := by
  have hPA : ps.length * (total L + L.length + 1) + (total L + L.length + 1) ≤ W := by
    have : (ps.length + 1) * (total L + L.length + 1) = ps.length * (total L + L.length + 1) + (total L + L.length + 1) := by ring
    omega
  have hAW : (total L + L.length + 1) ≤ W := by omega
  have hP1 : ps.length ≤ ps.length * (total L + L.length + 1) := Nat.le_mul_of_pos_right ps.length (by omega)
  have hPW : ps.length ≤ W := by omega
  have hml := maxLen_le_total L
  have hPRv : ∀ k (hk : k < ps.length), ps[k].1 ≤ W ∧ ps[k].2 ≤ W := fun k hk => by
    have := hps _ (List.getElem_mem hk); omega
  obtain ⟨τ1, r1, o1⟩ := asg_run (x := "pz") (B := W + 1) (σ := τ) (ev_var hF.pos (by omega))
  have F1 : Filled "OB" "po" pre τ1 := hF.congr (by rw [o1.vars "po" (by decide)]) (by rw [o1.arrs])
  obtain ⟨τ2, r2, F2, O2⟩ := push1_ofr (W := W) (e := .lit 0) (v := 0) F1 (evalB_lit (by omega))
    (by rw [o1.arrs]; omega) (by omega)
  obtain ⟨τ3, r3, o3⟩ := asg_run (x := "pq") (B := W + 1) (σ := τ2) (evalB_lit (n := 0) (by omega))
  have F3 : Filled "OB" "po" (pre ++ [0]) τ3 := F2.congr (by rw [o3.vars "po" (by decide)]) (by rw [o3.arrs])
  have O13 : OFr τ τ3 wpV := by
    refine ⟨fun y hy => ?_, fun b hb => ?_, ?_, ?_, ?_⟩
    · have h1 : y ≠ "pq" := fun h => hy (by simp [wpV, h])
      have h2 : y ∉ ["po"] := fun h => hy (by simp [wpV] at h ⊢; tauto)
      have h3 : y ≠ "pz" := fun h => hy (by simp [wpV, h])
      rw [o3.vars y h1, O2.vars y h2, o1.vars y h3]
    · rw [o3.arrs, O2.arrs b hb, o1.arrs]
    · rw [o3.arrs, O2.len, o1.arrs]
    · rw [o3.out, O2.out, o1.out]
    · rw [o3.inp, O2.inp, o1.inp]
  have hpz : τ3.vars "pz" = pre.length := by
    rw [o3.vars "pz" (by decide), O2.vars "pz" (by decide), o1.self]
  let I : ℕ → Env → Prop := fun k ρ =>
    Filled "OB" "po" (pre ++ [0] ++ frames (planW L (ps.take k))) ρ ∧
    ρ.vars "pq" = (planW L (ps.take k)).length ∧ ρ.vars "pz" = pre.length ∧ OFr τ ρ wpV
  have hI0 : I 0 (τ3.setVar "pk" 0) := by
    refine ⟨?_, by simp [planW, o3.self], by simp [hpz],
      (O13.trans (OFr.setVar τ3 "pk" 0)).mono (by intro y hy; revert y hy; decide)⟩
    have : frames (planW L (ps.take 0)) = [] := by simp [planW, frames]
    rw [this, List.append_nil]; exact F3.setVar (by decide) 0
  obtain ⟨τ4, r4, ⟨F4, q4, z4, O4⟩, -⟩ := FarRam.forUp_run_sum (B := W + 1) (i := "pk") (e := .var "np")
    (body := wrPlanBody) (N := ps.length) (planK L ps) I (σ := τ3) (by omega)
    (fun k _ ρ hI _ => ev_var (by rw [hI.2.2.2.vars "np" (by decide), hnp]) (by omega)) hI0
    (by
      rintro k hk ρ ⟨Fρ, qρ, zρ, Oρ⟩ hpk
      obtain ⟨hlo, hN⟩ := prW_get hk
      have hPRρ : ρ.arrs "PR" = τ.arrs "PR" := Oρ.arrs _ (by decide)
      have hpk2 : k + k + 1 < (prW ps).length := by rw [length_prW]; omega
      have hp1 : ps[k].1 + ps[k].2 ≤ L.length := hps _ (List.getElem_mem hk)
      have hsz := planW_sub_size L (ps.take (k + 1))
      have htk : (ps.take (k + 1)).length = k + 1 := by simp; omega
      rw [htk] at hsz
      have hkA : (k + 1) * (total L + L.length) ≤ ps.length * (total L + L.length + 1) := by
        have h1 : k + 1 ≤ ps.length := by omega
        have h2 : total L + L.length ≤ (total L + L.length + 1) := by omega
        exact Nat.mul_le_mul h1 h2
      have hpre1 : planW L (ps.take (k + 1)) = planW L (ps.take k) ++ rng L ps[k].1 ps[k].2 := planW_succ hk
      have hfr : (frames (planW L (ps.take k))).length ≤ ps.length * (total L + L.length + 1) := by
        rw [length_frames]
        have h0 := planW_sub_size L (ps.take k)
        have h1 : (ps.take k).length ≤ ps.length := by simp
        have h2 : (ps.take k).length * (total L + L.length) ≤ ps.length * (total L + L.length + 1) :=
          Nat.mul_le_mul h1 (by omega)
        omega
      have hfl0 := length_frames (planW L (ps.take k))
      have hfl1 := length_frames (planW L (ps.take (k + 1)))
      have hsz0 : total (planW L (ps.take k)) + (planW L (ps.take k)).length ≤ ps.length * (total L + L.length + 1) := by
        rw [hpre1, total_append, List.length_append] at hsz; omega
      obtain ⟨ρ1, s1, p1⟩ := asg_run (x := "lo") (B := W + 1) (σ := ρ) (v := ps[k].1)
        (evalB_get (ev_add (ev_var hpk (by omega)) (ev_var hpk (by omega)) (by omega))
          (by rw [hPRρ, hPR (k + k) (by omega)]; rw [List.getElem?_eq_getElem (by omega)] at hlo; exact hlo)
          (by have := (hPRv k hk).1; omega))
      obtain ⟨ρ2, s2, p2⟩ := asg_run (x := "lN") (B := W + 1) (σ := ρ1) (v := ps[k].2)
        (evalB_get (ev_add (ev_add (ev_var (x := "pk") (v := k) (by rw [p1.vars "pk" (by decide), hpk]) (by omega))
          (ev_var (x := "pk") (v := k) (by rw [p1.vars "pk" (by decide), hpk]) (by omega)) (by omega))
          (evalB_lit (n := 1) (by omega)) (by omega))
          (by rw [p1.arrs, hPRρ, hPR (k + k + 1) hpk2]; rw [List.getElem?_eq_getElem hpk2] at hN; exact hN)
          (by have := (hPRv k hk).2; omega))
      have ea : ∀ b, b ≠ "OB" → ρ2.arrs b = τ.arrs b := fun b hb => by rw [p2.arrs, p1.arrs, Oρ.arrs b hb]
      have hw2 : WordsAt L ρ2 := hw.of_arrs (ea "a" (by decide)) (ea "st" (by decide)) (ea "ln" (by decide))
      obtain ⟨ρ3, s3, F3', O3'⟩ := emRng_run (W := W) (ws := L) (lo := ps[k].1) (N := ps[k].2)
        (pre := pre ++ [0] ++ frames (planW L (ps.take k))) hw2
        (by rw [p2.vars "lo" (by decide), p1.self]) p2.self hp1
        (Fρ.congr (by rw [p2.vars "po" (by decide), p1.vars "po" (by decide)]) (by rw [p2.arrs, p1.arrs]))
        (by rw [p2.arrs, p1.arrs, Oρ.len, hcap]; simp only [List.length_append, List.length_singleton]
            have h1 := hfr; have h2 := hPA; have h3 := hB; linarith)
        (by simp only [List.length_append, List.length_singleton]; have h1 := hfr; have h2 := hPA; linarith) hv
        (by rw [ea "a" (by decide)]; exact ha)
      have hq3 : ρ3.vars "pq" = (planW L (ps.take k)).length := by
        rw [O3'.vars "pq" (by decide), p2.vars "pq" (by decide), p1.vars "pq" (by decide), qρ]
      have hl3 : ρ3.vars "lN" = ps[k].2 := by rw [O3'.vars "lN" (by decide), p2.self]
      have hlen1 : (planW L (ps.take (k + 1))).length = (planW L (ps.take k)).length + ps[k].2 := by
        rw [hpre1, List.length_append, length_rng hp1]
      obtain ⟨ρ4, s4, p4⟩ := asg_run (x := "pq") (B := W + 1) (σ := ρ3)
        (ev_add (ev_var hq3 (by omega)) (ev_var hl3 (by omega)) (by omega))
      have hrun : Run (W + 1) wrPlanBody ρ ρ4 (planK L ps k) := by
        unfold wrPlanBody
        refine (Run.seq s1 (Run.seq s2 (Run.seq s3 s4))).mono ?_
        simp only [planK, List.getD_eq_getElem _ _ hk, Expr.size]
        omega
      refine ⟨ρ4, hrun, by rw [p4.vars "pk" (by decide), O3'.vars "pk" (by decide), p2.vars "pk" (by decide),
        p1.vars "pk" (by decide), hpk], ?_, ?_, ?_, ?_⟩
      · rw [hpre1, frames_append, ← List.append_assoc]
        exact (F3'.congr (by rw [p4.vars "po" (by decide)]) (by rw [p4.arrs])).setVar (by decide) _
      · simp only [vars_setVar, if_neg (show ("pq" : String) ≠ "pk" by decide)]; rw [p4.self, hlen1]
      · simp only [vars_setVar, if_neg (show ("pz" : String) ≠ "pk" by decide)]
        rw [p4.vars "pz" (by decide), O3'.vars "pz" (by decide), p2.vars "pz" (by decide),
          p1.vars "pz" (by decide), zρ]
      · have e1 : OFr ρ ρ2 ["lo", "lN"] := ⟨fun y hy => by
            simp at hy; rw [p2.vars y hy.2, p1.vars y hy.1], fun b _ => by rw [p2.arrs, p1.arrs],
            by rw [p2.arrs, p1.arrs], by rw [p2.out, p1.out], by rw [p2.inp, p1.inp]⟩
        have e4 : OFr ρ3 ρ4 ["pq"] := ⟨fun y hy => p4.vars y (by simpa using hy), fun b _ => by rw [p4.arrs],
          by rw [p4.arrs], p4.out, p4.inp⟩
        exact ((((Oρ.trans e1).trans O3').trans e4).trans (OFr.setVar ρ4 "pk" (k + 1))).mono
          (by intro y hy; revert y hy; decide))
  -- the count
  have hall : ps.take ps.length = ps := List.take_length
  rw [hall] at F4 q4
  have hsz := planW_sub_size L ps
  have hPA' : ps.length * (total L + L.length) ≤ ps.length * (total L + L.length + 1) := Nat.mul_le_mul_left _ (by omega)
  have hfl := length_frames (planW L ps)
  have r5 : Run (W + 1) (.store "OB" (.var "pz") (.var "pq")) τ4
      (τ4.setArr "OB" pre.length (planW L ps).length) 3 :=
    (Run.store (ev_var z4 (by omega)) (ev_var q4 (by omega)) (by rw [O4.len, hcap]; omega)).mono
      (by simp [Expr.size])
  refine ⟨τ4.setArr "OB" pre.length (planW L ps).length, ?_, ?_, ?_⟩
  · unfold wrPlan
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    have e1 : ∑ k ∈ Finset.range ps.length, (planK L ps k + (Expr.var "np").size + 7) =
        ∑ k ∈ Finset.range ps.length, planK L ps k + ps.length * 8 := by
      simp only [Expr.size, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      ring
    rw [e1, sum_planK L ps hps _ le_rfl, List.take_length]
    simp only [Expr.size]
    omega
  · rw [toWord_words]
    refine ⟨by simp [F4.pos], fun i hi => ?_⟩
    rw [← List.getElem?_eq_getElem hi]
    simp only [arrs_setArr, ↓reduceIte, List.getElem?_set]
    by_cases hip : pre.length = i
    · subst hip
      rw [if_pos rfl, if_pos (by rw [O4.len, hcap]; omega)]
      simp
    · rw [if_neg hip, getElem?_mid pre _ _ 0 i (Ne.symm hip)]
      have hi' : i < (pre ++ [0] ++ frames (planW L ps)).length := by simp at hi ⊢; omega
      rw [F4.get i hi', ← List.getElem?_eq_getElem hi']
      simp
  · have := O4.trans (xs := wpV) (ys := []) (τ'' := τ4.setArr "OB" pre.length (planW L ps).length)
      ⟨fun _ _ => by simp, fun b hb => by simp [hb], by simp, by simp, by simp⟩
    rwa [List.append_nil] at this

end Lax185574Proofs.ResolveRam.Glue
