import Lax185574Proofs.MC.Asm.Defs

/-!
Facts about the calls of the pipeline: their number, and the answer of
the last call, which is the answer of thm:mc by the localization.
-/

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences

theorem length_stepCalls (n t : ℕ) (st : Step) : (stepCalls n t st).length = 1 := by
  cases st <;> simp [stepCalls]

theorem length_stepCalls_le (n t : ℕ) (st : Step) : (stepCalls n t st).length ≤ n + 1 := by
  rw [length_stepCalls]; omega

theorem length_callsFrom (n : ℕ) : ∀ (t : ℕ) (steps : List Step),
    (callsFrom n t steps).length = steps.length
  | _, [] => by simp [callsFrom]
  | t, st :: r => by
      simp only [callsFrom, List.length_append, length_stepCalls, length_callsFrom n (t + 1) r,
        List.length_cons]
      omega

theorem length_callsFrom_le (n : ℕ) : ∀ (t : ℕ) (steps : List Step),
    (callsFrom n t steps).length ≤ (n + 1) * steps.length
  | _, [] => by simp [callsFrom]
  | t, st :: r => by
      have h1 := length_stepCalls_le n t st
      have h2 := length_callsFrom_le n (t + 1) r
      simp only [callsFrom, List.length_append, List.length_cons]
      nlinarith

/-- The number of calls. -/
theorem length_pcalls_le (n : ℕ) (steps : List Step) :
    (pcalls n steps).length ≤ (n + 1) * steps.length + 1 := by
  have := length_callsFrom_le n 0 steps
  unfold pcalls; split_ifs <;> simp <;> omega

theorem sAt_last {n : ℕ} {s : List (PartialGraph (Fin n))} (h : s ≠ []) :
    sAt s (s.length - 1) = s.getLast h := by
  simp only [sAt, List.getD_eq_getElem?_getD, List.getLast_eq_getElem]
  rw [List.getElem?_eq_getElem (by have := List.length_pos_of_ne_nil h; omega)]
  rfl

open Classical in
/-- **The answer of the last call.** -/
theorem finAns_eq {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin n)}
    {s : List (PartialGraph (Fin n))} (hcs : IsConstructionSequence G s)
    (φ : Lax3.FirstOrder.FO 0) : finAns s (Lax3.FirstOrder.rank φ) φ = 1 :: mcAns G φ := by
  obtain ⟨hs, -, -, -, hE, hN⟩ := hcs
  have key := (sat_loc_sentence G (s.getLast hs) hE hN (Lax3.FirstOrder.rank φ) φ le_rfl
    ⟨0, hn⟩).2
  simp only [finAns, hn, dite_true, callYE, sAt_last hs, mcAns]
  congr 1
  by_cases h : Lax3.FirstOrder.Sat G Fin.elim0 φ
  · have h' := key.2 h
    simp [word_simps, h, h']
  · have h' : ¬ Lax185574.DistanceLogic.DistFO.Sat (s.getLast hs) ![⟨0, hn⟩]
        (loc (Lax3.FirstOrder.rank φ) φ) := fun hh => h (key.1 hh)
    simp [word_simps, h, h']

end Lax185574Proofs.MC
