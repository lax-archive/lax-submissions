import Lax185574Proofs.MC.Glue.Heads
import Lax185574Proofs.Words.GuardedSound

/-!
From a run of the glue command to the clauses of `GlueAt`.

`step_clause`: if the command has a run on an input whose entries are
below `2 ^ (v - sI)`, with output `o` when `ovf` stays `0`, then every
halting run of the guarded program outputs `o`, and the guarded program
halts within `10 k + 5` steps when `ovf` stays `0`. `guardOK_workQ`:
the guard on `workQ` is `GuardOK`. `pU_zero`, `pU_succ`: the inputs of
the rounds.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile Lax808846.Ram
open Lax808846.RamComputes Lax185574Proofs.RamSim
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees

variable {n : ℕ}

theorem step_clause {cmd : Com} (hok : Com.Ok gLayout cmd) {u o : List ℕ} {v W K : ℕ} {P C : Prop}
    (hWd : W = guardW gLayout v) (hv : guardBits gLayout + 6 ≤ v)
    (hu : ∀ e ∈ u, 64 * (e + 1) ≤ W + 1)
    (hrun : ∃ σ' k, Run (W + 1) cmd ((initEnv (fun _ => W + 1) u).setVar "W" W) σ' k ∧ k ≤ K ∧
      (σ'.vars "ovf" = 0 → σ'.out = o ∧ maxEntry o < W / 32 / 32 ∧ P) ∧ (C → σ'.vars "ovf" = 0)) :
    (∀ o' t, RunsTo v (guardedProgram gLayout cmd) u o' t →
      o' = o ∧ (∀ e ∈ o, e < 2 ^ (v - (guardBits gLayout + 6) - 4)) ∧ P) ∧
    (C → ∃ t ≤ 10 * K + 5, RunsTo v (guardedProgram gLayout cmd) u o t) := by
  obtain ⟨σ', k, hr, hk, hS, hC⟩ := hrun
  have hW1 : W + 1 = 2 ^ (v - guardBits gLayout) := hWd ▸ guardW_succ gLayout v
  rw [hWd] at hr
  obtain ⟨hsound, hfwd⟩ := guarded_sound hok (by simp [gLayout]) (by simp [gLayout])
    (w := v) (by omega) (x := u) (fun e h => by have := hu e h; rw [← hWd]; omega) hr
  refine ⟨fun o' t h => ?_, fun hc => ?_⟩
  · obtain ⟨hov, ho'⟩ := hsound o' t h
    obtain ⟨ho, hE, hP⟩ := hS hov
    refine ⟨ho' ▸ ho, fun e he => ?_, hP⟩
    have h1 := ent_sound_arith hW1 (lt_of_le_of_lt (le_maxEntry he) hE)
    rw [show v - (guardBits gLayout + 6) - 4 = v - guardBits gLayout - 10 by omega]
    exact h1
  · obtain ⟨t, ht, hR⟩ := hfwd (hC hc)
    obtain ⟨ho, -, -⟩ := hS (hC hc)
    refine ⟨t, le_trans ht ?_, ho ▸ hR⟩
    show gLayout.const * k + 5 ≤ 10 * K + 5
    simp only [Layout.const]; omega

/-! ### The guard -/

theorem workQ_sub (s : List (PartialGraph (Fin n))) (q : ℕ) (φ : Lax3.FirstOrder.FO 0) (c : PCall n) :
    (workQ s q φ c).length ≤ (callQ s q φ c).length ∧
      ∀ e ∈ workQ s q φ c, e ∈ callQ s q φ c := by
  cases c <;> simp only [workQ, callQ, swIn, List.length_append, List.mem_append] <;>
    refine ⟨by omega, fun e h => by tauto⟩

theorem guardOK_workQ {s : List (PartialGraph (Fin n))} {q : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {eM eR eE v sQ : ℕ} (c : PCall n)
    (h : ((workQ s q φ c).length + maxEntry (workQ s q φ c) + 1) ^ (expOf eM eR eE (ckOf c) + 1) ≤
      2 ^ (v - sQ)) : GuardOK s q φ eM eR eE v sQ c := by
  cases c with
  | merge t P Q =>
    have he : expOf eM eR eE (ckOf (PCall.merge (n := n) t P Q)) = eM := by
      simp only [expOf, ckOf]; split_ifs <;> simp_all
    rw [he] at h; exact h
  | resolve t sg P Q => simp only [GuardOK]; simpa [expOf, ckOf, workQ] using h
  | eval a => simp only [GuardOK]; simpa [expOf, ckOf, workQ] using h

/-! ### The inputs of the rounds -/

theorem pU_zero (x : List ℕ) (s : List (PartialGraph (Fin n))) (q : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (cs : List (PCall n)) (hd : ℕ → List ℕ) (ans : List ℕ) :
    pU x s q φ cs hd ans 0 = 0 :: x.length :: (x ++ [0]) := by
  simp [pU, pA, pB, lpU, lpA0]

theorem take3 (A B C D : List ℕ) :
    (A ++ (B ++ (C ++ D))).take (A.length + (B.length + C.length)) = A ++ (B ++ C) := by
  rw [show A ++ (B ++ (C ++ D)) = (A ++ B ++ C) ++ D by simp, List.take_left' (by simp)]
  simp

theorem pU_succ (σ : Script n) (φ : Lax3.FirstOrder.FO 0) (ans : List ℕ) {j : ℕ} {c : PCall n}
    (hc : (pcalls n σ.steps)[j]? = some c) :
    pU ([n] ++ toWord σ ++ toWord φ) σ.run (Lax3.FirstOrder.rank φ) φ (pcalls n σ.steps)
      (hdSeq σ.run (Lax3.FirstOrder.rank φ) (n + 3) σ.steps.length
        (Lax185574.DistanceLogic.DistFO.code (loc (Lax3.FirstOrder.rank φ) φ)) (pcalls n σ.steps))
      ans (j + 1) = inJ σ φ c := by
  simp only [pU, pA, pB, glueOut, hc, hdSeq, lpU, inJ, hdOf, hdW, winOf, stOf]
  simp [stW, scOf, take3]

end Lax185574Proofs.MC.Glue
