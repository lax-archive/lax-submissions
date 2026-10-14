import Lax457868Proofs.SamplerInitialExpectation
import Lax457868Proofs.SamplerFiniteMean
import Lax457868Proofs.SamplerRetries
import Lax457868Proofs.SamplerTwinSuppression
import Mathlib.Tactic

/-!
The actual finite probability law for one initial attempt.  An ordered draw is
uniform in `A^r`; conditional on that draw, one representative is chosen
uniformly and independently from each nonempty trace fibre.  Thus the joint
law is a hierarchical mean, because the number of representative choices
depends on the draw.
-/

namespace Lax457868Proofs.SamplerInitialProbability

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerInitialExpectation
open Lax457868Proofs.SamplerFiniteMean
open Lax457868Proofs.SamplerRetries
open Lax457868Proofs.SamplerRepresentative
open Lax457868Proofs.SamplerVCDimension
open Lax457868Proofs.SamplerTwinSuppression

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A trace class is an index for one independent representative choice. -/
abbrev ClassIndex (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) :=
  {T : Finset α // T ∈ traceClasses N (drawSet A draw) B}

/-- The possible representatives of one class, as a finite nonempty type. -/
abbrev RepFiber (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) (T : ClassIndex A B N draw) :=
  {b : β // b ∈ traceFiber A B N draw T.1}

/-- Independent representative choices across all trace classes. -/
abbrev RepChoices (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) :=
  ∀ T : ClassIndex A B N draw, RepFiber A B N draw T

instance repFiberNonempty (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) (T : ClassIndex A B N draw) :
    Nonempty (RepFiber A B N draw T) := by
  obtain ⟨b, hb⟩ := traceFiber_nonempty_of_mem_traceClasses A B N draw T.2
  exact ⟨⟨b, hb⟩⟩

private lemma draws_toFinset (A : Finset α) {r : ℕ} (draw : Fin r → A) :
    (List.ofFn fun i : Fin r => (draw i : α)).toFinset = drawSet A draw := by
  ext x
  simp [drawSet, List.mem_toFinset, List.mem_ofFn]

/-- Decode the finite random choices into an actual legal initial choice.
Outside `B`, the representative map is the identity. -/
noncomputable def decodeChoice (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A)
    (reps : RepChoices A B N draw) : InitialChoice A B N r := by
  classical
  let chosen : β → β := fun b =>
    if hb : b ∈ B then
      (reps ⟨trace N (drawSet A draw) b,
        Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩).1
    else b
  refine {
    draws := List.ofFn fun i : Fin r => (draw i : α)
    draws_length := by simp
    draws_mem := ?_
    representative := chosen
    representative_mem := ?_
    representative_trace := ?_
    representative_constant := ?_
  }
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (draw i).2
  · intro b hb
    simp only [chosen, dif_pos hb]
    exact (Finset.mem_filter.mp (reps ⟨trace N (drawSet A draw) b,
      Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩).2).1
  · intro b hb
    have hrep := (Finset.mem_filter.mp (reps ⟨trace N (drawSet A draw) b,
      Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩).2).2
    simpa only [InitialChoice.sample, draws_toFinset, chosen, dif_pos hb] using hrep
  · intro b hb b' hb' heq
    dsimp [chosen]
    rw [dif_pos hb, dif_pos hb']
    have hindex :
        (⟨trace N (drawSet A draw) b,
          Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩ : ClassIndex A B N draw) =
        ⟨trace N (drawSet A draw) b',
          Finset.mem_image.mpr ⟨b', hb', rfl⟩⟩ := by
      apply Subtype.ext
      simpa only [InitialChoice.sample, draws_toFinset] using heq
    exact congrArg (fun T : ClassIndex A B N draw => (reps T).1) hindex

/-- Total disagreement realized by one legal decoded attempt. -/
noncomputable def totalDistance (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) (reps : RepChoices A B N draw) : ℕ :=
  ∑ b ∈ B, SamplerDistance.disagreement (N b)
    (N ((decodeChoice A B N draw reps).representative b))

lemma totalDistance_eq_classsum (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A)
    (reps : RepChoices A B N draw) :
    (totalDistance A B N draw reps : ℚ) =
      ∑ T : ClassIndex A B N draw,
        ∑ b ∈ traceFiber A B N draw T.1,
          (SamplerDistance.disagreement (N b) (N (reps T).1) : ℚ) := by
  classical
  have hrep (b : β) (hb : b ∈ B) :
      (decodeChoice A B N draw reps).representative b =
        (reps ⟨trace N (drawSet A draw) b,
          Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩).1 := by
    simp [decodeChoice, hb]
  have hfiber :
      (∑ T ∈ traceClasses N (drawSet A draw) B,
        ∑ b ∈ traceFiber A B N draw T,
          (SamplerDistance.disagreement (N b)
            (N ((decodeChoice A B N draw reps).representative b)) : ℚ)) =
      (∑ b ∈ B,
          (SamplerDistance.disagreement (N b)
            (N ((decodeChoice A B N draw reps).representative b)) : ℚ)) := by
    simpa only [traceFiber] using
      (Finset.sum_fiberwise_of_maps_to
        (s := B) (t := traceClasses N (drawSet A draw) B)
        (g := trace N (drawSet A draw))
        (fun b hb => Finset.mem_image.mpr ⟨b, hb, rfl⟩)
        (fun b => (SamplerDistance.disagreement (N b)
          (N ((decodeChoice A B N draw reps).representative b)) : ℚ)))
  rw [show (totalDistance A B N draw reps : ℚ) =
      ∑ b ∈ B, (SamplerDistance.disagreement (N b)
        (N ((decodeChoice A B N draw reps).representative b)) : ℚ) by
      simp [totalDistance]]
  rw [← hfiber]
  apply Finset.sum_bij (fun T hT => (⟨T, hT⟩ : ClassIndex A B N draw))
  · intro T hT
    exact Finset.mem_univ _
  · intro T hT U hU hEq
    exact congrArg Subtype.val hEq
  · intro U hU
    exact ⟨U.1, U.2, Subtype.ext rfl⟩
  · intro T hT
    apply Finset.sum_congr rfl
    intro b hb
    rw [hrep b (Finset.mem_filter.mp hb).1]
    have hindex :
        (⟨trace N (drawSet A draw) b,
          Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1, rfl⟩⟩ :
          ClassIndex A B N draw) = ⟨T, hT⟩ := by
      apply Subtype.ext
      exact (Finset.mem_filter.mp hb).2
    exact congrArg (fun U : ClassIndex A B N draw =>
      (SamplerDistance.disagreement (N b) (N (reps U).1) : ℚ)) hindex

/-- The uniform product law for the independent class representatives has
exactly the conditional first moment used in the expectation theorem. -/
lemma conditionalMeanZ_eq_repMean (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) :
    finiteMean (fun reps : RepChoices A B N draw =>
      (totalDistance A B N draw reps : ℚ)) =
      conditionalMeanZ A B N draw := by
  classical
  have hfun :
      (fun reps : RepChoices A B N draw =>
        (totalDistance A B N draw reps : ℚ)) =
      (fun reps : RepChoices A B N draw =>
        ∑ T : ClassIndex A B N draw,
          ∑ b ∈ traceFiber A B N draw T.1,
            (SamplerDistance.disagreement (N b) (N (reps T).1) : ℚ)) := by
    funext reps
    exact totalDistance_eq_classsum A B N draw reps
  rw [hfun, finiteMean_sum_pi (RepFiber A B N draw)
    (fun T rep => ∑ b ∈ traceFiber A B N draw T.1,
      (SamplerDistance.disagreement (N b) (N rep.1) : ℚ))]
  unfold conditionalMeanZ
  symm
  apply Finset.sum_bij (fun T hT => (⟨T, hT⟩ : ClassIndex A B N draw))
  · intro T hT
    exact Finset.mem_univ _
  · intro T hT U hU hEq
    exact congrArg Subtype.val hEq
  · intro U hU
    exact ⟨U.1, U.2, Subtype.ext rfl⟩
  · intro T hT
    unfold finiteMean
    simp only [Fintype.card_coe]
    rw [Finset.sum_coe_sort (traceFiber A B N draw T)
      (fun rep : β => ∑ b ∈ traceFiber A B N draw T,
        (SamplerDistance.disagreement (N b) (N rep) : ℚ))]

/-- The conditional probability that the concrete initial selector rejects an
attempt, uniformly averaging all class representative choices. -/
noncomputable def conditionalRejectProbability (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A)
    (threshold cap : ℕ) : ℚ :=
  finiteMean fun reps : RepChoices A B N draw =>
    if cap < ((decodeChoice A B N draw reps).exceptions threshold).card
    then 1 else 0

/-- The hierarchical rejection probability: first draw uniformly from
`A^r`, then choose representatives uniformly inside each trace class. -/
noncomputable def initialRejectProbability (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r threshold cap : ℕ) : ℚ :=
  finiteMean fun draw : Fin r → A =>
    conditionalRejectProbability A B N draw threshold cap

lemma finiteMean_const_mul {Ω : Type*} [Fintype Ω] (a : ℚ)
    (f : Ω → ℚ) :
    finiteMean (fun ω => a * f ω) = a * finiteMean f := by
  unfold finiteMean
  rw [← Finset.mul_sum]
  ring

lemma initialMeanZ_eq_hierarchical_mean (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ) :
    finiteMean (fun draw : Fin r → A =>
      finiteMean (fun reps : RepChoices A B N draw =>
        (totalDistance A B N draw reps : ℚ))) =
      initialMeanZ A B N r := by
  unfold finiteMean initialMeanZ
  rw [card_draws]
  norm_cast
  congr 1
  apply Finset.sum_congr rfl
  intro draw hdraw
  exact conditionalMeanZ_eq_repMean A B N draw

/-- The exception-cap test is controlled pointwise by the realized total
distance.  This is the finite Markov inequality before averaging. -/
lemma rejection_pointwise_charge (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A)
    (reps : RepChoices A B N draw) (D k : ℕ) (hD : 0 < D) :
    (2 * A.card * k : ℚ) *
        (if A.card / D <
            ((decodeChoice A B N draw reps).exceptions k).card
         then 1 else 0) ≤
      (6 * D : ℚ) * (totalDistance A B N draw reps : ℚ) := by
  let q := ((decodeChoice A B N draw reps).exceptions k).card
  have hcharge := initialExceptions_distance_bound
    (choice := decodeChoice A B N draw reps) (k := k)
  change k * q ≤ 3 * totalDistance A B N draw reps at hcharge
  by_cases hreject : A.card / D < q
  · have hcap : A.card < q * D := (Nat.div_lt_iff_lt_mul hD).mp hreject
    have hmul1 : 2 * A.card * k ≤ 2 * (q * D) * k :=
      Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 hcap.le)
    have hmul2 : 2 * D * (k * q) ≤ 2 * D *
        (3 * totalDistance A B N draw reps) :=
      Nat.mul_le_mul_left (2 * D) hcharge
    have hnat : 2 * A.card * k ≤
        6 * D * totalDistance A B N draw reps := by
      calc
        2 * A.card * k ≤ 2 * (q * D) * k := hmul1
        _ = 2 * D * (k * q) := by ring
        _ ≤ 2 * D * (3 * totalDistance A B N draw reps) := hmul2
        _ = 6 * D * totalDistance A B N draw reps := by ring
    dsimp [q] at hreject
    simp only [if_pos hreject, mul_one]
    exact_mod_cast hnat
  · dsimp [q] at hreject
    simp only [if_neg hreject, mul_zero]
    positivity

/-- Averaging the pointwise charge retains the correct hierarchical law:
uniform draws first, then conditional uniform class representatives. -/
lemma rejection_probability_charge (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r D k : ℕ) (hD : 0 < D) :
    (2 * A.card * k : ℚ) *
        initialRejectProbability A B N r k (A.card / D) ≤
      (6 * D : ℚ) * initialMeanZ A B N r := by
  have hpoint (draw : Fin r → A) :
      (2 * A.card * k : ℚ) *
          conditionalRejectProbability A B N draw k (A.card / D) ≤
        (6 * D : ℚ) *
          finiteMean (fun reps : RepChoices A B N draw =>
            (totalDistance A B N draw reps : ℚ)) := by
    unfold conditionalRejectProbability
    rw [← finiteMean_const_mul, ← finiteMean_const_mul]
    apply finiteMean_mono
    intro reps
    exact rejection_pointwise_charge A B N draw reps D k hD
  unfold initialRejectProbability
  rw [← initialMeanZ_eq_hierarchical_mean A B N r]
  rw [← finiteMean_const_mul, ← finiteMean_const_mul]
  exact finiteMean_mono _ _ hpoint

/-- A single initial attempt rejects with probability at most one half under
the actual hierarchical finite law and the original linear shatter bound. -/
lemma initialRejectProbability_le_half (A : Finset α) (B : Finset β)
    (N : β → Finset α) (c : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c) (hB : B.card ≤ c * A.card)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (traceFamily (B.image N) S).card ≤ c * S.card) :
    initialRejectProbability A B N
      (A.card / (4 * c ^ 2))
      (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
      (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) ≤
      (1 / 2 : ℚ) := by
  let n := A.card
  let l := Nat.clog 2 c
  let s := 64 * l
  let D := 4 * c ^ 2 * (s + 1)
  let k := 768 * c ^ 5 * (s + 1) * l + 1
  let r := n / (4 * c ^ 2)
  have hn : 0 < n := Finset.card_pos.mpr hA
  have hD : 0 < D := by dsimp [D]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hE := initialMeanZ_explicit_bound A B N c hA hN hc hB hlinear
  have hcharge := rejection_probability_charge A B N r D k hD
  have hmult : (6 * D : ℚ) * initialMeanZ A B N r ≤
      (6 * D : ℚ) * (32 * c ^ 3 * n * l : ℚ) := by
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hconst : 6 * D * (32 * c ^ 3 * n * l) ≤ n * k := by
    calc
      6 * D * (32 * c ^ 3 * n * l) =
          n * (768 * c ^ 5 * (s + 1) * l) := by dsimp [D]; ring
      _ ≤ n * k := by
        dsimp [k]
        exact Nat.mul_le_mul_left n (Nat.le_succ _)
  have hconstQ : (6 * D : ℚ) * (32 * c ^ 3 * n * l : ℚ) ≤
      (n * k : ℚ) := by exact_mod_cast hconst
  have hbound : (2 * n * k : ℚ) *
      initialRejectProbability A B N r k (n / D) ≤ (n * k : ℚ) :=
    hcharge.trans (hmult.trans hconstQ)
  have hnk : (0 : ℚ) < (n * k : ℚ) := by exact_mod_cast Nat.mul_pos hn hk
  have hdiv : (n * k : ℚ) *
      (2 * initialRejectProbability A B N r k (n / D)) ≤
      (n * k : ℚ) * 1 := by nlinarith [hbound]
  have htwo := le_of_mul_le_mul_left hdiv hnk
  dsimp [r, D, k, s, l, n] at htwo ⊢
  linarith

omit [DecidableEq β] in
lemma traceFamily_eq_traceClasses_id (H : Finset (Finset α))
    (S : Finset α) :
    traceFamily H S = traceClasses id S H := by
  ext T
  simp only [traceFamily, traceClasses, Finset.mem_image]
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U, hU, by ext x; simp [trace, and_comm]⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U, hU, by ext x; simp [trace, and_comm]⟩

omit [DecidableEq β] in
/-- For neighborhoods contained in `A`, tracing on any ground set only uses
its intersection with `A`. -/
lemma traceClasses_eq_inter_ground (A : Finset α) (B : Finset β)
    (N : β → Finset α) (S : Finset α)
    (hN : ∀ b ∈ B, N b ⊆ A) :
    traceClasses N S B = traceClasses N (S ∩ A) B := by
  unfold traceClasses
  apply Finset.image_congr
  intro b hb
  ext x
  simp only [trace, Finset.mem_inter]
  constructor
  · rintro ⟨hxb, hxS⟩
    exact ⟨hxb, hxS, hN b hb hxb⟩
  · rintro ⟨hxb, hxS, -⟩
    exact ⟨hxb, hxS⟩

omit [DecidableEq β] in
/-- The original trace hypothesis on nonempty subsets of `A` extends to
all nonempty ground sets after twin suppression. -/
lemma deduplicated_linear_trace_bound (A : Finset α) (B : Finset β)
    (N : β → Finset α) (c : ℕ)
    (hN : ∀ b ∈ B, N b ⊆ A) (hc : 2 ≤ c)
    (htrace : ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses N Y B).card ≤ c * Y.card) :
    ∀ S : Finset α, S.Nonempty →
      (traceFamily (B.image N) S).card ≤ c * S.card := by
  intro S hS
  have hEq : traceFamily (B.image N) S =
      traceClasses N (S ∩ A) B := by
    rw [traceFamily_eq_traceClasses_id,
      traceClasses_eq_deduplicated B N S,
      traceClasses_eq_inter_ground A B N S hN]
  rw [hEq]
  by_cases hY : (S ∩ A).Nonempty
  · exact (htrace (S ∩ A) Finset.inter_subset_right hY).trans
      (Nat.mul_le_mul_left c (Finset.card_le_card Finset.inter_subset_left))
  · have hEmpty : S ∩ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hY
    rw [hEmpty]
    have hsubset : traceClasses N ∅ B ⊆ ({∅} : Finset (Finset α)) := by
      intro T hT
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hT
      simp [trace]
    have hcard : (traceClasses N ∅ B).card ≤ 1 := by
      simpa using Finset.card_le_card hsubset
    have hpos : 0 < c * S.card :=
      Nat.mul_pos (by omega) (Finset.card_pos.mpr hS)
    omega

omit [DecidableEq β] in
/-- The half-rejection theorem with only the original nonempty-subset trace
bound, applied to the distinct neighborhood labels. -/
lemma deduplicated_initialRejectProbability_le_half
    (A : Finset α) (B : Finset β) (N : β → Finset α) (c : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c)
    (htrace : ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses N Y B).card ≤ c * Y.card) :
    initialRejectProbability A (B.image N) id
      (A.card / (4 * c ^ 2))
      (768 * c ^ 5 * (64 * Nat.clog 2 c + 1) * Nat.clog 2 c + 1)
      (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) ≤
      (1 / 2 : ℚ) := by
  have hN' := image_neighborhoods_subset_of A B N hN
  have hB' : (B.image N).card ≤ c * A.card :=
    deduplicated_neighborhoods_card_le A B N c hN
      (htrace A (Finset.Subset.rfl) hA)
  have hlinear := deduplicated_linear_trace_bound A B N c hN hc htrace
  have h := initialRejectProbability_le_half A (B.image N) id c
    hA hN' hc hB' (by simpa using hlinear)
  exact h

end Lax457868Proofs.SamplerInitialProbability
