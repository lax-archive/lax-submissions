import Lax457868Proofs.SamplerInitialRetries

/-! Uniform representative choices preserve total expected vertex weight.
This charges repeated CSR scans of a shared representative. -/
namespace Lax457868Proofs.SamplerRepresentativeCharge
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerInitialExpectation
open Lax457868Proofs.SamplerInitialProbability
open Lax457868Proofs.SamplerInitialRetries
open Lax457868Proofs.SamplerFiniteMean
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma representative_charge_eq_classsum
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) (reps : RepChoices A B N draw)
    (weight : β → ℚ) :
    (∑ b ∈ B, weight ((decodeChoice A B N draw reps).representative b)) =
      ∑ T : ClassIndex A B N draw,
        ((traceFiber A B N draw T.1).card : ℚ) * weight (reps T).1 := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := traceClasses N (drawSet A draw) B)
    (g := trace N (drawSet A draw))
    (fun b hb => Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    (fun b => weight ((decodeChoice A B N draw reps).representative b))
  rw [← hfiber]
  apply Finset.sum_bij (fun T hT => (⟨T, hT⟩ : ClassIndex A B N draw))
  · intro T hT; exact Finset.mem_univ _
  · intro T hT U hU heq; exact congrArg Subtype.val heq
  · intro T hT; exact ⟨T.1, T.2, Subtype.ext rfl⟩
  · intro T hT
    have heq (b : β) (hb : b ∈ B.filter (fun b => trace N (drawSet A draw) b = T)) :
        (decodeChoice A B N draw reps).representative b =
          (reps ⟨T, hT⟩).1 := by
      have hbB := (Finset.mem_filter.mp hb).1
      simp only [decodeChoice, dif_pos hbB]
      have hi : (⟨trace N (drawSet A draw) b,
          Finset.mem_image.mpr ⟨b, hbB, rfl⟩⟩ : ClassIndex A B N draw) =
          ⟨T, hT⟩ := Subtype.ext (Finset.mem_filter.mp hb).2
      exact congrArg (fun T : ClassIndex A B N draw => (reps T).1) hi
    calc
      _ = ∑ _b ∈ B.filter (fun b => trace N (drawSet A draw) b = T),
          weight (reps ⟨T, hT⟩).1 := Finset.sum_congr rfl (fun b hb => congrArg weight (heq b hb))
      _ = _ := by simp [traceFiber]

/-- Each class pays its size times a uniformly selected vertex weight;
its expectation is exactly the sum of weights within that class. -/
lemma conditional_representative_charge
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) (weight : β → ℚ) :
    finiteMean (fun reps : RepChoices A B N draw =>
      ∑ b ∈ B, weight ((decodeChoice A B N draw reps).representative b)) =
      ∑ b ∈ B, weight b := by
  classical
  simp_rw [representative_charge_eq_classsum]
  rw [finiteMean_sum_pi (RepFiber A B N draw)
    (fun T rep => ((traceFiber A B N draw T.1).card : ℚ) * weight rep.1)]
  have hclass (T : ClassIndex A B N draw) :
      finiteMean (fun rep : RepFiber A B N draw T =>
        ((traceFiber A B N draw T.1).card : ℚ) * weight rep.1) =
          ∑ b ∈ traceFiber A B N draw T.1, weight b := by
    have hpos : (traceFiber A B N draw T.1).Nonempty :=
      traceFiber_nonempty_of_mem_traceClasses A B N draw T.2
    have hne : ((traceFiber A B N draw T.1).card : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hpos)
    unfold finiteMean
    rw [← Finset.mul_sum]
    simp only [Fintype.card_coe]
    rw [Finset.sum_coe_sort]
    field_simp
  simp_rw [hclass]
  rw [Finset.sum_coe_sort (traceClasses N (drawSet A draw) B)
    (fun T => ∑ b ∈ traceFiber A B N draw T, weight b)]
  exact Finset.sum_fiberwise_of_maps_to
    (s := B) (t := traceClasses N (drawSet A draw) B)
    (g := trace N (drawSet A draw))
    (fun b hb => Finset.mem_image.mpr ⟨b, hb, rfl⟩) weight

/-- The complete hierarchical initial law has the same expected replicated
representative weight as one scan of the active vertex set. -/
lemma outcome_representative_charge
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (r : ℕ) (hA : A.Nonempty) (weight : β → ℚ) :
    (∑ ω : InitialOutcome A B N r, outcomeWeight A B N r ω *
      (∑ b ∈ B, weight ((outcomeChoice A B N r ω).representative b))) =
      ∑ b ∈ B, weight b := by
  rw [outcomeWeight_sum_eq_hierarchical]
  simp only [outcomeChoice, conditional_representative_charge]
  have hnonempty : Nonempty (Fin r → A) :=
    ⟨fun _ => ⟨Classical.choose hA, Classical.choose_spec hA⟩⟩
  have hne : (Fintype.card (Fin r → A) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (@Fintype.card_pos (Fin r → A) _ hnonempty)
  simp only [finiteMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hne

end Lax457868Proofs.SamplerRepresentativeCharge
