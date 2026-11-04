import Lax185574Proofs.MC.Asm.Calls

/-!
The calls of the pipeline and the steps of the script.

`sAt_run_succ`: the partial graph after step `t` is the step applied to
the partial graph before. `pcalls_step`: a merge call or a resolve call
of step `t` comes from the step `t` of the script. `sum_cost_pcalls`: if a
merge call and the evaluation cost at most `A` and a resolve call at most
`B`, with `A ≤ B`, then all calls cost at most `(m + 1) B` for `m`
steps, since every step has exactly one call. This is how the time of
thm:mc stays linear in the number of steps.
-/

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences

theorem scanl_get_succ {α β : Type*} (f : β → α → β) :
    ∀ (b : β) (l : List α) (t : ℕ) (ht : t < l.length),
      (l.scanl f b)[t + 1]? = ((l.scanl f b)[t]?).map (fun g => f g l[t])
  | b, a :: l, 0, _ => by simp
  | b, a :: l, t + 1, ht => by
      simp only [List.scanl_cons, List.getElem?_cons_succ, List.getElem_cons_succ]
      exact scanl_get_succ f (f b a) l t (by simp at ht; omega)

theorem sAt_run_succ {n : ℕ} (σ : Script n) {t : ℕ} (ht : t < σ.steps.length) :
    sAt σ.run (t + 1) = apply (sAt σ.run t) σ.steps[t] := by
  have hl : σ.run.length = σ.steps.length + 1 := by simp [Script.run]
  simp only [sAt, List.getD_eq_getElem?_getD]
  have h := scanl_get_succ apply (unresolved σ.colors) σ.steps t ht
  simp only [Script.run] at hl ⊢
  rw [h, List.getElem?_eq_getElem (by omega)]
  simp

/-- Where a call of step `t` comes from. -/
def FromStep {n : ℕ} (steps : List Step) : PCall n → Prop
  | .merge t P Q => steps[t]? = some (.merge P Q)
  | .resolve t sg P Q => steps[t]? = some (if sg then .resolvePos P Q else .resolveNeg P Q)
  | .eval _ => True

theorem fromStep_callsFrom {n : ℕ} (all : List Step) :
    ∀ (t₀ : ℕ) (r : List Step), (∀ i (h : i < r.length), all[t₀ + i]? = some r[i]) →
      ∀ c ∈ callsFrom n t₀ r, FromStep all c := by
  intro t₀ r
  induction r generalizing t₀ with
  | nil => simp [callsFrom]
  | cons a r ih =>
    intro hr c hc
    simp only [callsFrom, List.mem_append] at hc
    rcases hc with hc | hc
    · have h0 := hr 0 (by simp)
      simp only [add_zero, List.getElem_cons_zero] at h0
      cases a with
      | merge P Q =>
        simp only [stepCalls, List.mem_singleton] at hc; subst hc; exact h0
      | resolvePos P Q =>
        simp only [stepCalls, List.mem_singleton] at hc; subst hc; simpa [FromStep] using h0
      | resolveNeg P Q =>
        simp only [stepCalls, List.mem_singleton] at hc; subst hc; simpa [FromStep] using h0
    · refine ih (t₀ + 1) (fun i h => ?_) c hc
      have := hr (i + 1) (by simp; omega)
      simpa [show t₀ + (i + 1) = t₀ + 1 + i by omega] using this

theorem fromStep_pcalls {n : ℕ} {steps : List Step} {c : PCall n} (hc : c ∈ pcalls n steps) :
    FromStep steps c := by
  unfold pcalls at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · exact fromStep_callsFrom steps 0 steps (fun i h => by simp [h]) c hc
  · split_ifs at hc
    · simp only [List.mem_singleton] at hc; subst hc; trivial
    · simp at hc

/-- The cost of a call: `A` for a merge and the evaluation, `B` for a
resolve. -/
def callCost {n : ℕ} (A B : ℕ) : PCall n → ℕ
  | .resolve .. => B
  | _ => A

theorem sum_cost_callsFrom {n A B : ℕ} (hA : A ≤ B) :
    ∀ (t : ℕ) (r : List Step), ((callsFrom n t r).map (callCost A B)).sum ≤ r.length * B := by
  intro t r
  induction r generalizing t with
  | nil => simp [callsFrom]
  | cons a r ih =>
    simp only [callsFrom, List.map_append, List.sum_append, List.length_cons]
    have h1 : ((stepCalls n t a).map (callCost A B)).sum ≤ B := by
      cases a with
      | merge P Q => simp [stepCalls, callCost]; exact hA
      | resolvePos => simp [stepCalls, callCost]
      | resolveNeg => simp [stepCalls, callCost]
    have := ih (t + 1)
    nlinarith

/-- **Cost of all calls.** -/
theorem sum_cost_pcalls {n A B : ℕ} (hA : A ≤ B) (steps : List Step) :
    ((pcalls n steps).map (callCost A B)).sum ≤ (steps.length + 1) * B := by
  have := sum_cost_callsFrom (n := n) hA 0 steps
  unfold pcalls
  split_ifs <;> simp [callCost] <;> nlinarith

end Lax185574Proofs.MC
