import Lax185574Proofs.MC.Glue.Issue

/-!
Applying the answer of any call but the evaluation, in a round of the
glue program of thm:mc after the first: `apAll` runs `apJ`, `apR` or
`apS` by the kind of the call, and `apAll_run` gives the words of the
partial graph and of the family of the next call in `GW` and `FW`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix

variable {n : ℕ}

/-- Apply the answer by the kind of the call. -/
noncomputable def apAll : Com :=
  .ite (.eq (.var "ck") (.lit 0)) apJ (.ite (.eq (.var "ck") (.lit 1)) apR apS)

/-- The scalars written by `apAll`. -/
def apVars : List String :=
  ["y", "tS", "tE", "rc", "pg", "cA", "pf", "ca", "cl", "ci", "e1", "e2", "e3", "e4", "gS", "gE", "e5"]

theorem apS_sub : ["rc", "pg", "cA", "ci", "ca", "cl", "pf"] ⊆ apVars := by simp [apVars]
theorem apJ_sub : ["rc", "pg", "cA", "ci", "ca", "cl", "pf", "y", "e1", "e4"] ⊆
    apVars := by simp [apVars]
theorem apR_sub : ["gS", "y", "gE", "pg", "pf", "ca", "cl", "ci", "e1", "e2", "e5"] ⊆ apVars := by
  simp [apVars]

set_option maxHeartbeats 1000000 in
theorem apAll_run {W : ℕ} (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n) (c : PCall n)
    (hval : Valid σ.steps c) (hne : ∀ a, c ≠ .eval a) {τ : Env} {X R : List ℕ}
    (hX : τ.arrs "x" = X) (hf : HasFields σ.steps.length c τ) (hgn : τ.vars "gn" = n)
    (hgA : τ.vars "gA" = 14)
    (hfA : τ.vars "fA" = 14 + (gwOf σ.run σ.steps.length c).length)
    (hgl : τ.vars "gl" = (gwOf σ.run σ.steps.length c).length)
    (hfl : τ.vars "fl" = (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length)
    (hbA : τ.vars "bA" = 14 + (gwOf σ.run σ.steps.length c).length +
      (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length +
      (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length)
    (hbl : τ.vars "bl" = (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length)
    (hXd : X.drop 14 = gwOf σ.run σ.steps.length c ++
      fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c ++
      Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ) ++
      callY σ.run (Lax3.FirstOrder.rank φ) φ c ++ R)
    (hB : 14 + 2 * ((gwOf σ.run σ.steps.length c).length +
      (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length +
      (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)).length +
      (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length) + n < W)
    (hXl : W ≤ X.length) (hGW : W ≤ (τ.arrs "GW").length) (hFW : W ≤ (τ.arrs "FW").length)
    (hv : ∀ v ∈ X, v ≤ W) (hvP : cPOf c ≤ W ∧ cQOf c ≤ W) :
    ∃ τ', Run (W + 1) apAll τ τ' (300 * ((gwOf σ.run σ.steps.length c).length +
        (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c).length +
        (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length) + 400) ∧
      (∀ c', nextCall hn σ.steps c = some c' →
        Filled "GW" "pg" (gwOf σ.run σ.steps.length c') τ' ∧
        Filled "FW" "pf" (fwOf σ.run (Lax3.FirstOrder.rank φ) σ.steps.length c') τ') ∧
      τ'.arrs "x" = X ∧
      (∀ y, y ∉ apVars → τ'.vars y = τ.vars y) ∧
      (∀ b, b ≠ "GW" → b ≠ "FW" → τ'.arrs b = τ.arrs b) ∧
      (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  obtain ⟨hck, hct, hcv, hcP, hcQ, hcs⟩ := hf
  set q := Lax3.FirstOrder.rank φ with hq
  generalize hgw0 : gwOf σ.run σ.steps.length c = gw at hfA hgl hbA hXd hB ⊢
  generalize hfw0 : fwOf σ.run q σ.steps.length c = fw at hfl hbA hXd hB ⊢
  generalize hbw0 : callY σ.run q φ c = b at hbl hXd hB ⊢
  generalize hlw0 : Lax185574.DistanceLogic.DistFO.code (loc q φ) = lw at hbA hXd hB
  have hXl' : 14 + (gw ++ fw ++ lw ++ b).length ≤ X.length := by simp; omega
  have hd1 : X.drop 14 = gw ++ (fw ++ lw ++ b ++ R) := by rw [hXd]; simp
  have hd2 : X.drop (14 + gw.length) = fw ++ (lw ++ b ++ R) := by
    have := drop_add_of_drop hd1; rw [this]; simp only [List.append_assoc]
  have hd3 : X.drop (14 + gw.length + fw.length + lw.length) = b ++ R := by
    have h := drop_add_of_drop hd2
    have h' := drop_add_of_drop (u := lw) (r := b ++ R) (by rw [h]; simp)
    rw [← h']
  have hc0 := condEq_lit (B := W + 1) (d := 0) hck (by have := ckOf_le c; omega) (by omega)
  have hc1 := condEq_lit (B := W + 1) (d := 1) hck (by have := ckOf_le c; omega) (by omega)
  cases c with
  | merge t P Q =>
    have hst : σ.steps[t]? = some (.merge P Q) := hval
    have hgw : gw = toWord (sAt σ.run t) ++ toWord (distMatrix (sAt σ.run t)) := hgw0.symm
    subst hgw
    have hd1' : X.drop 14 = toWord (sAt σ.run t) ++ toWord (distMatrix (sAt σ.run t)) ++
        (fw ++ lw ++ b ++ R) := by rw [hd1, List.append_assoc]
    have hgl' : τ.vars "gl" = (toWord (sAt σ.run t)).length +
        (toWord (distMatrix (sAt σ.run t))).length := by rw [hgl, List.length_append]
    simp only [List.length_append] at hfA hbA hB hXl' hd2 hd3
    by_cases hPQ : P = Q
    · -- merge_{P,P}
      subst hPQ
      have hk : ckOf (PCall.merge t P P : PCall n) = 3 := by simp [ckOf]
      obtain ⟨τ', r, F1, F2, hx, fv, fa, fl, fi, fo⟩ := apS_run (W := W) (P := P) (Q := P)
        (G := sAt σ.run t) (E := toWord (distMatrix (sAt σ.run t))) (fw := fw) (a := 14)
        (f := 14 + ((toWord (sAt σ.run t)).length + (toWord (distMatrix (sAt σ.run t))).length))
        (X := X) (σ := τ) hX hgA hd1' hgl' hgn (by rw [hcP]; rfl) (by rw [hcQ]; rfl) hvP.1 hvP.2
        (by rw [hfA]) hfl hd2 (by omega) (by omega) (by omega) (by omega) (by omega) hv
      refine ⟨τ', (Run.ite_false (by rw [hc0, hk]; rfl) (Run.ite_false (by rw [hc1, hk]; rfl)
        r)).mono ?_, fun c' hc' => ?_, hx, fun y hy => fv y (fun h => hy (apS_sub h)), fa, fl, fi, fo⟩
      · simp only [Cond.size, Expr.size]; omega
      · obtain ⟨h1, h2⟩ := self_next σ q hn hst hc'
        exact ⟨by rw [h1, hgw0]; exact F1, by rw [h2, hfw0]; exact F2⟩
    · have hk : ckOf (PCall.merge t P Q : PCall n) = 0 := by simp [ckOf, hPQ]
      obtain ⟨us, hus⟩ : ∃ us, us = mans (sAt σ.run t) q P Q := ⟨_, rfl⟩
      have husl : us.length = n := by rw [hus]; simp [mans]
      have hb : b = (us.length :: frames us) ++ (zR0 ++ uE0) := by
        rw [← hbw0, ← toWord_words]; simp [callY, callYM, callYR, callYE, hPQ, hus]
      have hbl' : b.length = 1 + (frames us).length + dR := by
        rw [hb]; simp [dR]; omega
      have hfr := length_frames_flatten us
      obtain ⟨τ', r, F1, F2, hx, fv, fa, fl, fi, fo⟩ := apJ_run (W := W) (P := P) (Q := Q)
        (G := sAt σ.run t) (E := toWord (distMatrix (sAt σ.run t))) (us := us) (a := 14)
        (b0 := 14 + ((toWord (sAt σ.run t)).length + (toWord (distMatrix (sAt σ.run t))).length) +
          fw.length + lw.length)
        (X := X) (σ := τ) hX hgA hd1' hgl' hgn (by rw [hcP]; rfl) (by rw [hcQ]; rfl) hvP.1 hvP.2
        husl (by rw [hbA]) (by rw [hd3, hb, List.append_assoc])
        (by omega) (by omega) (by omega) (by rw [hbl'] at hB; omega) hv
      refine ⟨τ', (Run.ite_true (by rw [hc0, hk]; rfl) r).mono ?_, fun c' hc' => ?_, hx,
        fun y hy => fv y (fun h => hy (apJ_sub h)), fa, fl, fi, fo⟩
      · simp only [Cond.size, Expr.size]; rw [hbl']; generalize dR = D at *; omega
      · obtain ⟨h1, h2⟩ := merge_next σ q hn hst hc'
        exact ⟨by rw [h1]; exact F1, by rw [h2, ← hus]; exact F2⟩
  | resolve t sg P Q =>
    have hk : ckOf (PCall.resolve t sg P Q : PCall n) = 1 := rfl
    set G' := resolveBy (sAt σ.run t) sg P Q with hG'
    have hb : b = yM0 ++ (toWord G' ++ toWord (distMatrix G') ++ toWord (family G' 1 q)) ++ uE0 := by
      have e3 : ∀ {α β γ : Type} [WordEncoding α] [WordEncoding β] [WordEncoding γ] (x : α) (y : β)
          (z : γ), toWord (x, y, z) = toWord x ++ (toWord y ++ toWord z) := fun _ _ _ => rfl
      rw [← hbw0]; simp only [callY, callYM, callYR, callYE, e3, List.append_assoc]; rfl
    have hE := length_toWord_distMatrix G'
    have hbl' : b.length = yM0.length + (toWord G').length + (toWord (distMatrix G')).length +
        (toWord (family G' 1 q)).length + uE0.length := by rw [hb]; simp; omega
    obtain ⟨τ', r, F1, F2, hx, fv, fa, fl, fi, fo⟩ := apR_run (W := W) (G := G')
      (E := toWord (distMatrix G')) (F := toWord (family G' 1 q))
      (a := 14 + gw.length + fw.length + lw.length) (X := X) (σ := τ)
      (R := R) hX (by rw [hbA]) hgn (by rw [hd3, hb]) hE (by rw [hbl, hbl'])
      (by simp at hXl'; rw [hbl'] at hXl'; omega) (by rw [hbl'] at hB; omega)
      (by rw [hbl'] at hB; omega) (by rw [hbl'] at hB; omega) hv
    refine ⟨τ', (Run.ite_false (by rw [hc0, hk]; rfl) (Run.ite_true (by rw [hc1, hk]; rfl)
      r)).mono ?_, fun c' hc' => ?_, hx, fun y hy => fv y (fun h => hy (apR_sub h)), fa, fl, fi, fo⟩
    · simp only [Cond.size, Expr.size]; rw [hbl']; omega
    · obtain ⟨h1, h2⟩ := resolve_next σ q hn hval hc'
      exact ⟨by rw [h1]; exact F1, by rw [h2]; exact F2⟩
  | eval a => exact absurd rfl (hne a)

end Lax185574Proofs.MC.Glue
