import Lax185574Proofs.MC.Glue.GlueJ
import Lax185574Proofs.MC.Bounds.WordSizes

/-!
Bounds on the heads of the glue program of thm:mc.

The words of the partial graph with its matrix of distances and of the
family of trees of a call are small (`gw_small`, `fw_small`), with
`T = treeMax` and `M` the largest entry of the word of the script. So
the head of a call has length at most
`17 + 6 (n + 1) ^ 2 + 1 + n (T + treeCst q) + |lw|`, and its entries
are bounded by that plus `|x|`, `M` and constants of the sentence
(`hd_bounds`).
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees

variable {n : ℕ}

open Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix in
theorem gw_small (σ : Script n) {c : PCall n} (hval : Valid σ.steps c) :
    Small (gwOf σ.run σ.steps.length c) (6 * (n + 1) ^ 2) (maxEntry (toWord σ)) := by
  have h := ctOf_le σ hval
  obtain ⟨h1, h2⟩ := small_pgraph (sAt σ.run (ctOf σ.steps.length c))
    (fun v => color_le_script σ (by rw [length_run]; omega) v)
  have hD := length_toWord_distMatrix (sAt σ.run (ctOf σ.steps.length c))
  have hDe := toWord_distMatrix_le (sAt σ.run (ctOf σ.steps.length c))
  have hsq : 1 + n * (n + 1) ≤ (n + 1) ^ 2 := by nlinarith
  refine ⟨?_, fun e he => ?_⟩
  · simp only [gwOf, List.length_append]; omega
  · simp only [gwOf, List.mem_append] at he
    rcases he with he | he
    · have := h2 e he; omega
    · have := hDe e he; nlinarith

theorem fw_small (σ : Script n) (q : ℕ) {c : PCall n} (hval : Valid σ.steps c) :
    Small (fwOf σ.run q σ.steps.length c) (1 + n * (treeMax σ.run q + treeCst q))
      (maxEntry (toWord σ)) := by
  have hl := length_run σ
  cases c with
  | merge t P Q =>
    have ht := step_lt (show σ.steps[t]? = some (.merge P Q) from hval)
    exact small_family _ q (fun a => tree_le_treeMax σ.run q (by show t < σ.run.length; omega) a)
      (fun u => color_le_script σ (by show t < σ.run.length; omega) u)
  | resolve t sg P Q =>
    have ht := step_lt hval
    exact small_family _ q (fun a => tree_le_treeMax σ.run q (by show t < σ.run.length; omega) a)
      (fun u => color_le_script σ (by show t < σ.run.length; omega) u)
  | eval a =>
    exact small_family _ q (fun b => tree_le_treeMax σ.run q (by show σ.steps.length < σ.run.length; omega) b)
      (fun u => color_le_script σ (by show σ.steps.length < σ.run.length; omega) u)

theorem length_x (σ : Script n) (φ : Lax3.FirstOrder.FO 0) :
    ([n] ++ toWord σ ++ toWord φ).length = n + 3 + 3 * σ.steps.length + (toWord φ).length := by
  simp only [List.length_append, toWord_script, List.length_cons, List.length_ofFn,
    length_flatten_stepCode, List.length_nil, List.length_singleton]; omega

theorem toWord_le_x (σ : Script n) (φ : Lax3.FirstOrder.FO 0) :
    maxEntry (toWord σ) ≤ maxEntry ([n] ++ toWord σ ++ toWord φ) := by
  apply maxEntry_le
  intro v hv; exact le_maxEntry (by simp [hv])

theorem fields_le (σ : Script n) {c : PCall n} (hval : Valid σ.steps c) :
    cPOf c ≤ maxEntry (toWord σ) ∧ cQOf c ≤ maxEntry (toWord σ) := by
  cases c with
  | merge t P Q =>
    have := step_le_script σ (show σ.steps[t]? = some (.merge P Q) from hval)
    exact ⟨this P (by simp [stepCode]), this Q (by simp [stepCode])⟩
  | resolve t sg P Q =>
    have := step_le_script σ hval
    cases sg <;> exact ⟨this P (by simp [stepCode]), this Q (by simp [stepCode])⟩
  | eval a => simp [cPOf, cQOf]

/-- The constant of the heads. -/
noncomputable def hdL (n T q : ℕ) : ℕ := 6 * (n + 1) ^ 2 + (1 + n * (T + treeCst q))

theorem hd_bounds (σ : Script n) (φ : Lax3.FirstOrder.FO 0) {c : PCall n} (hval : Valid σ.steps c) :
    let q := Lax3.FirstOrder.rank φ
    let lw := Lax185574.DistanceLogic.DistFO.code (loc q φ)
    let hd := hdOf σ.run q (n + 3) σ.steps.length lw c
    hd.length ≤ 17 + hdL n (treeMax σ.run q) q + lw.length ∧
    ∀ e ∈ hd, e ≤ ([n] ++ toWord σ ++ toWord φ).length + maxEntry (toWord σ) +
      2 * hdL n (treeMax σ.run q) q + 2 * lw.length + maxEntry lw + q + 40 := by
  intro q lw hd
  obtain ⟨hg1, hg2⟩ := gw_small σ hval
  obtain ⟨hf1, hf2⟩ := fw_small σ q hval
  have hx := length_x σ φ
  have hct := ctOf_le σ hval
  obtain ⟨hP, hQ⟩ := fields_le σ hval
  have hL : hd.length = 17 + (gwOf σ.run σ.steps.length c).length +
      (fwOf σ.run q σ.steps.length c).length + lw.length := by
    simp [hd, hdOf, hdW, stW, scOf]; omega
  refine ⟨by rw [hL]; unfold hdL; omega, fun e he => ?_⟩
  have hs0 : s0Of (n + 3) σ.steps.length c ≤ n + 3 + 3 * σ.steps.length := by
    unfold s0Of; split_ifs with h
    · have : ctOf σ.steps.length c + 1 < σ.steps.length := by
        unfold tagOf at h; split_ifs at h with h' <;> omega
      omega
    · omega
  have hlw : ∀ v ∈ lw, v ≤ maxEntry lw := fun v h => le_maxEntry h
  have htag := tagOf_le2 σ.steps.length c
  have hk : kOf σ.steps.length c ≤ 3 := by unfold kOf; split_ifs <;> omega
  have hck := ckOf_le c
  have hcv : cvOf c ≤ n := by simp [cvOf]
  have hcs : csOf c ≤ 1 := by
    cases c with
    | resolve t sg P Q => simp only [csOf]; split_ifs <;> omega
    | _ => simp [csOf]
  unfold hdL
  simp only [hd, hdOf, hdW, stW, scOf, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    at he
  rcases he with h | h | h | ((((h | h | h | h | h | h | h | h | h | h | h) | (h | h | h)) | h) | h) | h
  all_goals first
    | (subst h; simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
    | (have := hg2 e h; omega)
    | (have := hf2 e h; omega)
    | (have := hlw e h; omega)

end Lax185574Proofs.MC.Glue
