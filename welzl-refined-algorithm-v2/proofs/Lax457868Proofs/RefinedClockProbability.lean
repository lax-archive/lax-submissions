import Lax457868Proofs.ClockedSource
import Mathlib.Tactic

/-! The final bounded-time conversion. Reserve one sixth of the tape space
for capped-sampling failures and one sixth for exceeding six times the mean
source cost. The checked source clock then preserves correct outputs on at
least two thirds of tapes. -/
namespace Lax457868Proofs.RefinedClockProbability

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ClockedSource
open scoped BigOperators

/-- The integer form of the final Markov and union bounds. -/
lemma clock_good_count {Ω : Type*} [Fintype Ω]
    (cost : Ω → ℕ) (bad : Finset Ω) (cap : ℕ) (hcap : 0 < cap)
    (hmean : 6 * (∑ ρ, cost ρ) ≤ cap * Fintype.card Ω)
    (hbad : 6 * bad.card ≤ Fintype.card Ω) :
    ∃ good : Finset Ω, 2 * Fintype.card Ω ≤ 3 * good.card ∧
      ∀ ρ ∈ good, ρ ∉ bad ∧ cost ρ ≤ cap := by
  classical
  let slow := Finset.univ.filter fun ρ => cap < cost ρ
  have hw : slow.card * cap ≤ ∑ ρ, cost ρ := by
    calc
      _ = ∑ _ρ ∈ slow, cap := by simp
      _ ≤ ∑ ρ ∈ slow, cost ρ := Finset.sum_le_sum fun ρ hρ =>
        (Finset.mem_filter.mp hρ).2.le
      _ ≤ ∑ ρ, cost ρ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hs : 6 * slow.card ≤ Fintype.card Ω := by
    have hh : cap * (6 * slow.card) ≤ cap * Fintype.card Ω := by nlinarith
    exact Nat.le_of_mul_le_mul_left hh hcap
  let good := Finset.univ \ (bad ∪ slow)
  have hcover : Fintype.card Ω ≤ good.card + bad.card + slow.card := by
    have hc : (Finset.univ : Finset Ω) = good ∪ (bad ∪ slow) := by
      ext ρ
      simp only [good, Finset.mem_univ, Finset.mem_union, Finset.mem_sdiff,
        true_and]
      tauto
    have hc' := Finset.card_union_le good (bad ∪ slow)
    rw [← hc, Finset.card_univ] at hc'
    have hu := Finset.card_union_le bad slow
    omega
  refine ⟨good, by omega, ?_⟩
  intro ρ hρ
  have hm := (Finset.mem_sdiff.mp hρ).2
  have hb : ρ ∉ bad := fun h => hm (Finset.mem_union_left _ h)
  refine ⟨hb, ?_⟩
  by_contra hn
  apply hm
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by omega⟩)

/-- Apply the clock to actual source runs, with no claim that the mean or
failure estimate follows merely from a successful mathematical sample. -/
lemma clocked_runs_of_mean {Ω : Type*} [Fintype Ω]
    {B S cap : ℕ} {c : Com} (hf : Fresh c)
    (initial clockInitial final : Ω → Env) (cost : Ω → ℕ)
    (bad : Finset Ω) (Accept : List ℕ → Prop)
    (hrun : ∀ ρ, Run B c (initial ρ) (final ρ) (cost ρ))
    (hready : ∀ ρ, Ready B S (clockInitial ρ))
    (hsame : ∀ ρ, SameSource (initial ρ) (clockInitial ρ))
    (hcapacity : ∀ ρ, capacity S (clockInitial ρ) = cap)
    (hcorrect : ∀ ρ, ρ ∉ bad → Accept (final ρ).out)
    (hcap : 0 < cap)
    (hmean : 6 * (∑ ρ, cost ρ) ≤ cap * Fintype.card Ω)
    (hbad : 6 * bad.card ≤ Fintype.card Ω) :
    ∃ good : Finset Ω, 2 * Fintype.card Ω ≤ 3 * good.card ∧
      (∀ ρ, ∃ τ, Run B (clocked c) (clockInitial ρ) τ
        (clockFactor c * (cap + 1))) ∧
      ∀ ρ ∈ good, ∃ τ, Run B (clocked c) (clockInitial ρ) τ
        (clockFactor c * (cap + 1)) ∧ Accept τ.out := by
  obtain ⟨good, hcard, hgood⟩ := clock_good_count cost bad cap hcap hmean hbad
  have hc (ρ : Ω) :
      ∃ τ, Run B (clocked c) (clockInitial ρ) τ
        (clockFactor c * (cap + 1)) ∧
        (cost ρ ≤ cap → SameSource (final ρ) τ) := by
    obtain ⟨k, hk, hr⟩ := hrun ρ
    obtain ⟨τ, K, ht, hb, _, _, hg⟩ :=
      clocked_run hr hf (hready ρ) (hsame ρ)
    rw [hcapacity ρ] at hb hg
    exact ⟨τ, ht.mono hb, fun hh => (hg (hk.trans hh)).2.1⟩
  refine ⟨good, hcard, ?_, ?_⟩
  · intro ρ
    obtain ⟨τ, ht, _⟩ := hc ρ
    exact ⟨τ, ht⟩
  · intro ρ hρ
    obtain ⟨hb, hcost⟩ := hgood ρ hρ
    obtain ⟨τ, ht, hs⟩ := hc ρ
    exact ⟨τ, ht, (hs hcost).2.2.2 ▸ hcorrect ρ hb⟩

end Lax457868Proofs.RefinedClockProbability
