import Lax185574Proofs.MC.Glue.Glue0

/-!
Runs of the glue command of thm:mc on the input of a round after the
first: the tag of the head of the previous call `c`, then the input of
`roundJ_run`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees

variable {n : ℕ}

/-- The input of the round after call `c`. -/
noncomputable def inJ (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) : List ℕ :=
  tagOf σ.steps.length c :: ((stOf σ φ c).length :: winOf σ φ c ++ stOf σ φ c ++
    (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length :: callY σ.run (Lax3.FirstOrder.rank φ) φ c)

theorem n_mem_stOf (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) :
    n ∈ stOf σ φ c ∧ σ.steps.length ∈ stOf σ φ c := by
  simp [stOf, stW, scOf]

set_option maxHeartbeats 1000000 in
theorem glueJ_run {W eM eR eE d : ℕ} (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (hn : 0 < n)
    (c : PCall n) (hval : Valid σ.steps c)
    (hval' : ∀ c', nextCall hn σ.steps c = some c' → Valid σ.steps c') (hW63 : 63 ≤ W)
    (hent : ∀ e ∈ inJ σ φ c, 64 * (e + 1) ≤ W + 1) :
    let q := Lax3.FirstOrder.rank φ
    let lw := Lax185574.DistanceLogic.DistFO.code (loc q φ)
    ∃ σ' k, Run (W + 1) (glueCmd eM eR eE d) ((initEnv (fun _ => W + 1) (inJ σ φ c)).setVar "W" W) σ' k ∧
      k ≤ 30 * dK + 50 + roundJC eM eR eE d ((stOf σ φ c).length + (callY σ.run q φ c).length + n) ∧
      (∀ c', nextCall hn σ.steps c = some c' →
        (σ'.vars "ovf" = 0 → σ'.out = hdOf σ.run q (n + 3) σ.steps.length lw c' ++ callQ σ.run q φ c' ∧
          maxEntry (hdOf σ.run q (n + 3) σ.steps.length lw c' ++ callQ σ.run q φ c') < W / 32 / 32 ∧
          min (((workQ σ.run q φ c').length + maxEntry (workQ σ.run q φ c') + 1) ^
              (expOf eM eR eE (ckOf c') + 1)) W ≤ W / min (2 ^ d) W) ∧
        (dK < W / 8 → dK + (gwOf σ.run σ.steps.length c').length +
            (fwOf σ.run q σ.steps.length c').length + lw.length < W / 8 →
          maxEntry (hdOf σ.run q (n + 3) σ.steps.length lw c' ++ callQ σ.run q φ c') < W / 32 / 32 →
          min (((workQ σ.run q φ c').length + maxEntry (workQ σ.run q φ c') + 1) ^
              (expOf eM eR eE (ckOf c') + 1)) W ≤ W / min (2 ^ d) W → σ'.vars "ovf" = 0)) ∧
      (nextCall hn σ.steps c = none →
        (σ'.vars "ovf" = 0 → σ'.out = 0 :: finAns σ.run q φ ∧
          maxEntry (0 :: finAns σ.run q φ) < W / 32 / 32) ∧
        (dK < W / 8 → maxEntry (0 :: finAns σ.run q φ) < W / 32 / 32 → σ'.vars "ovf" = 0)) := by
  intro q lw
  have eqb : (callY σ.run q φ c).length = (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length := rfl
  have eqC : roundJC eM eR eE d ((stOf σ φ c).length + (callY σ.run q φ c).length + n) =
    roundJC eM eR eE d ((stOf σ φ c).length + (callY σ.run (Lax3.FirstOrder.rank φ) φ c).length + n) :=
    rfl
  set ρ := (initEnv (fun _ => W + 1) (inJ σ φ c)).setVar "W" W with hρ
  have hvρ : ValsLt (W + 1) ρ := valsLt_init _ _ (by omega) (fun v h => by have := hent v h; omega)
  obtain ⟨τ₁, r₁, htg₁, hzk₁, fv₁, fa₁, fo₁, fi₁⟩ := glue_top (W := W) (t := tagOf σ.steps.length c)
    (σ := ρ) (rest := (stOf σ φ c).length :: winOf σ φ c ++ stOf σ φ c ++
      (callY σ.run q φ c).length :: callY σ.run q φ c) (by simp only [hρ, inp_setVar]; rfl) (by simp [hρ])
    (by omega)
  have hv₁ := Run.vals_lt r₁ hvρ
  have hW₁ : τ₁.vars "W" = W := by rw [fv₁ _ (by decide) (by decide)]; simp [hρ]
  have hovf₁ : τ₁.vars "ovf" = 0 := by rw [fv₁ _ (by decide) (by decide)]; simp [hρ, initEnv]
  have hc := condLt_div (B := W + 1) (x := "zk") (d := 8) hzk₁ hW₁ (by omega) (by omega) (by omega)
  have hdK := lens_le_dK
  by_cases hz : min dK W < W / 8
  · have hdW : dK < W / 8 := by
      by_contra h; have : min dK W = W ∨ min dK W = dK := by omega
      rcases this with h' | h' <;> omega
    have htag : tagOf σ.steps.length c ≠ 0 := tagOf_pos _ _
    have hc0 := condEq_lit (B := W + 1) (d := 0) htg₁ (by have := tagOf_le2 σ.steps.length c; omega)
      (by omega)
    have hent' : ∀ e ∈ (stOf σ φ c).length :: winOf σ φ c ++ stOf σ φ c ++
        (callY σ.run q φ c).length :: callY σ.run q φ c, 64 * (e + 1) ≤ W + 1 :=
      fun e h => hent e (List.mem_cons_of_mem _ h)
    have h1 := hent' _ List.mem_cons_self
    have h2 := hent' (callY σ.run q φ c).length (by simp)
    obtain ⟨hn1, hm1⟩ := n_mem_stOf σ φ c
    have h3 := hent' n (by simp [hn1])
    have h4 := hent' σ.steps.length (by simp [hm1])
    obtain ⟨τ₂, r₂, hS, hE⟩ := roundJ_run (W := W) (eM := eM) (eR := eR) (eE := eE) (d := d) σ φ hn c
      hval hval' (τ := τ₁) (rest := []) hW₁ (by omega) hovf₁ htg₁ (by rw [fi₁]; simp only [List.append_nil]; rfl)
      (fun a _ => by rw [fa₁]; simp [hρ, initEnv]) hv₁ hent' (by omega)
    have ho₁ : τ₁.out = [] := by rw [fo₁]; simp [hρ, initEnv]
    refine ⟨τ₂, _, Run.seq r₁ (Run.ite_true (by rw [hc, decide_eq_true hz]) (Run.ite_false
      (by rw [hc0, decide_eq_false htag]) r₂)), ?_, fun c' hc' => ?_, fun hnone => ?_⟩
    · simp only [Cond.size, Expr.size]; omega
    · obtain ⟨hS1, hS2⟩ := hS c' hc'
      exact ⟨fun h => by obtain ⟨a1, a2, a3⟩ := hS1 h; exact ⟨by rw [a1, ho₁]; rfl, a2, a3⟩,
        fun _ => hS2⟩
    · obtain ⟨hE1, hE2⟩ := hE hnone
      refine ⟨fun h0 => ⟨by rw [hE1, ho₁]; rfl, ?_⟩, fun _ h => by rw [hE2, if_pos h]⟩
      rw [hE2] at h0
      split_ifs at h0 with h'
      · exact h'
  · refine ⟨τ₁.setVar "ovf" 1, _, Run.seq r₁ (Run.ite_false (by rw [hc, decide_eq_false hz])
      (Run.assign (evalB_lit (by omega)))), ?_, fun c' _ => ⟨fun h => by simp at h,
        fun h => absurd (lt_of_le_of_lt (min_le_left _ _) h) hz⟩,
      fun _ => ⟨fun h => by simp at h, fun h => absurd (lt_of_le_of_lt (min_le_left _ _) h) hz⟩⟩
    simp only [Cond.size, Expr.size]; unfold roundJC; omega

end Lax185574Proofs.MC.Glue
