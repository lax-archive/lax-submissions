import Lax457868Proofs.SamplerOneInclusion
import Lax457868Proofs.SamplerVCDimension
import Lax457868Proofs.SamplerDistance
import Lax457868Proofs.SamplerPhases
import Lax457868Proofs.SamplerRepresentative
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
Finite uniform means for the initial sampler.  A draw is an ordered tuple of
elements of `A`, so repeated draws remain distinct positions.  The rational
means below are explicit averages over these tuples and over each nonempty
trace class's representative choices.
-/

namespace Lax457868Proofs.SamplerInitialExpectation

open Lax457868Proofs.SamplerDistance
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerRepresentative
open Lax457868Proofs.SamplerVCDimension
open Lax457868Proofs.SamplerOneInclusion

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The set of points seen in an ordered sample. -/
def drawSet (A : Finset α) {r : ℕ} (draw : Fin r → A) : Finset α :=
  Finset.univ.image fun i => (draw i : α)

/-- One class of neighborhood vertices with a given trace on a sample. -/
def traceFiber (A : Finset α) (B : Finset β) (N : β → Finset α)
    {r : ℕ} (draw : Fin r → A) (T : Finset α) : Finset β :=
  B.filter fun b => trace N (drawSet A draw) b = T

/-- A trace class on an arbitrary finite ground set. -/
def fiberOn (B : Finset β) (N : β → Finset α)
    (W T : Finset α) : Finset β :=
  B.filter fun b => trace N W b = T

omit [DecidableEq β] in
lemma traceFiber_eq_fiberOn (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) (T : Finset α) :
    traceFiber A B N draw T = fiberOn B N (drawSet A draw) T := rfl

/-- Mean total disagreement from uniformly choosing one representative in
each nonempty trace class, conditional on a fixed ordered sample. -/
noncomputable def conditionalMeanZ (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) : ℚ :=
  ∑ T ∈ traceClasses N (drawSet A draw) B,
    (∑ rep ∈ traceFiber A B N draw T,
      ∑ b ∈ traceFiber A B N draw T,
        (disagreement (N b) (N rep) : ℚ)) /
      ((traceFiber A B N draw T).card : ℚ)

/-- First moment of the initial distance, with ordered draws uniform in
`A^r` and independent uniform representatives inside each trace class. -/
noncomputable def initialMeanZ (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ) : ℚ :=
  (∑ draw : Fin r → A, conditionalMeanZ A B N draw) / (A.card ^ r : ℚ)

omit [DecidableEq α] in
/-- Deleting a fixed position from a full ordered tuple is exactly the
product bijection between a fresh draw and the remaining tuple. -/
lemma sum_full_delete (A : Finset α) (r : ℕ) (i : Fin (r + 1))
    (F : A → (Fin r → A) → ℚ) :
    (∑ full : Fin (r + 1) → A, F (full i) (i.removeNth full)) =
      ∑ x : A, ∑ draw : Fin r → A, F x draw := by
  have h := (Equiv.sum_comp (Fin.insertNthEquiv (fun _ => A) i)
    (fun full : Fin (r + 1) → A => F (full i) (i.removeNth full))).symm
  simpa [Fin.insertNthEquiv, Fin.removeNth_insertNth,
    Fintype.sum_prod_type] using h

lemma drawSet_full_eq_insert (A : Finset α) {r : ℕ}
    (full : Fin (r + 1) → A) (i : Fin (r + 1)) :
    drawSet A full = insert (full i).1 (drawSet A (i.removeNth full)) := by
  ext x
  simp only [drawSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [Fin.exists_iff_succAbove i]
  simp [Fin.removeNth, eq_comm]

omit [DecidableEq α] in
lemma card_draws (A : Finset α) (r : ℕ) :
    Fintype.card (Fin r → A) = A.card ^ r := by
  simp

/-- The expected disagreements at one point of the ground set, conditional
on the ordered initial sample. -/
noncomputable def conditionalPositionMean (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) (x : A) : ℚ :=
  ∑ T ∈ traceClasses N (drawSet A draw) B,
    (∑ rep ∈ traceFiber A B N draw T,
      ∑ b ∈ traceFiber A B N draw T,
        if (x.1 ∈ N b) ≠ (x.1 ∈ N rep) then (1 : ℚ) else 0) /
      ((traceFiber A B N draw T).card : ℚ)

private lemma disagreement_eq_sum_indicator (A X Y : Finset α)
    (hX : X ⊆ A) (hY : Y ⊆ A) :
    (disagreement X Y : ℚ) =
      ∑ x ∈ A, if (x ∈ X) ≠ (x ∈ Y) then (1 : ℚ) else 0 := by
  have hset : A.filter (fun x => (x ∈ X) ≠ (x ∈ Y)) =
      (X \ Y) ∪ (Y \ X) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨-, hne⟩
      by_cases hxX : x ∈ X <;> by_cases hxY : x ∈ Y <;> simp_all
    · intro hxy
      refine ⟨?_, ?_⟩
      · rcases hxy with ⟨hxX, -⟩ | ⟨hxY, -⟩
        · exact hX hxX
        · exact hY hxY
      · tauto
  rw [← Finset.sum_filter, hset]
  simp [SamplerDistance.disagreement]

omit [DecidableEq β] in
/-- The full disagreement mean is the sum of the means at each ground point. -/
lemma conditionalMeanZ_eq_sum_positionMean (A : Finset α) (B : Finset β)
    (N : β → Finset α) (hN : ∀ b ∈ B, N b ⊆ A)
    {r : ℕ} (draw : Fin r → A) :
    conditionalMeanZ A B N draw =
      ∑ x : A, conditionalPositionMean A B N draw x := by
  unfold conditionalMeanZ conditionalPositionMean
  let C := fun T : Finset α => traceFiber A B N draw T
  have hnum (T : Finset α) :
      (∑ rep ∈ C T, ∑ b ∈ C T,
        (SamplerDistance.disagreement (N b) (N rep) : ℚ)) =
      ∑ x : A, ∑ rep ∈ C T, ∑ b ∈ C T,
        if (x.1 ∈ N b) ≠ (x.1 ∈ N rep) then (1 : ℚ) else 0 := by
    calc
      (∑ rep ∈ C T, ∑ b ∈ C T,
          (SamplerDistance.disagreement (N b) (N rep) : ℚ)) =
          ∑ rep ∈ C T, ∑ b ∈ C T, ∑ x : A,
            if (x.1 ∈ N b) ≠ (x.1 ∈ N rep) then (1 : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro rep hrep
        apply Finset.sum_congr rfl
        intro b hb
        have hrepB : rep ∈ B := (Finset.mem_filter.mp hrep).1
        have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
        have hd := disagreement_eq_sum_indicator A (N b) (N rep)
          (hN b hbB) (hN rep hrepB)
        rw [← Finset.sum_coe_sort] at hd
        exact hd
      _ = ∑ rep ∈ C T, ∑ x : A, ∑ b ∈ C T,
          if (x.1 ∈ N b) ≠ (x.1 ∈ N rep) then (1 : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro rep hrep
        rw [Finset.sum_comm]
      _ = ∑ x : A, ∑ rep ∈ C T, ∑ b ∈ C T,
          if (x.1 ∈ N b) ≠ (x.1 ∈ N rep) then (1 : ℚ) else 0 := by
        rw [Finset.sum_comm]
  calc
    (∑ T ∈ traceClasses N (drawSet A draw) B,
      (∑ rep ∈ C T, ∑ b ∈ C T,
        (SamplerDistance.disagreement (N b) (N rep) : ℚ)) / (C T).card) =
      ∑ T ∈ traceClasses N (drawSet A draw) B,
        ∑ x : A, (∑ rep ∈ C T, ∑ b ∈ C T,
          if (x.1 ∈ N b) ≠ (x.1 ∈ N rep) then (1 : ℚ) else 0) / (C T).card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [hnum T, Finset.sum_div]
    _ = ∑ x : A, ∑ T ∈ traceClasses N (drawSet A draw) B,
        (∑ rep ∈ C T, ∑ b ∈ C T,
          if (x.1 ∈ N b) ≠ (x.1 ∈ N rep) then (1 : ℚ) else 0) / (C T).card := by
      rw [Finset.sum_comm]

private lemma sum_coordinate_indicator_eq_disagreementToRepresentative
    (C : Finset β) (N : β → Finset α) (x : α) (rep : β) :
    (∑ b ∈ C, if (x ∈ N b) ≠ (x ∈ N rep) then (1 : ℚ) else 0) =
      (disagreementToRepresentative C (coordinateLabel N x) rep : ℚ) := by
  have hfilter : C.filter (fun b => (x ∈ N b) ≠ (x ∈ N rep)) =
      C.filter (fun b => coordinateLabel N x b != coordinateLabel N x rep) := by
    ext b
    simp [coordinateLabel]
  calc
    (∑ b ∈ C, if (x ∈ N b) ≠ (x ∈ N rep) then (1 : ℚ) else 0) =
        ((C.filter fun b => (x ∈ N b) ≠ (x ∈ N rep)).card : ℚ) := by
      rw [← Finset.sum_filter]
      simp
    _ = (disagreementToRepresentative C (coordinateLabel N x) rep : ℚ) := by
      rw [hfilter]
      rfl

lemma conditionalPositionMean_eq_uniform (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) (x : A) :
    conditionalPositionMean A B N draw x =
      ∑ T ∈ traceClasses N (drawSet A draw) B,
        uniformRepresentativeMean (traceFiber A B N draw T)
          (coordinateLabel N x.1) := by
  unfold conditionalPositionMean uniformRepresentativeMean
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  apply Finset.sum_congr rfl
  intro rep hrep
  exact sum_coordinate_indicator_eq_disagreementToRepresentative
    (traceFiber A B N draw T) N x rep

omit [DecidableEq β] in
lemma traceFiber_nonempty_of_mem_traceClasses (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) {T : Finset α}
    (hT : T ∈ traceClasses N (drawSet A draw) B) :
    (traceFiber A B N draw T).Nonempty := by
  obtain ⟨b, hb, htrace⟩ := Finset.mem_image.mp hT
  refine ⟨b, Finset.mem_filter.mpr ⟨hb, ?_⟩⟩
  exact htrace

omit [DecidableEq β] in
lemma sum_traceFiber_card (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) :
    (∑ T ∈ traceClasses N (drawSet A draw) B,
      (traceFiber A B N draw T).card) = B.card := by
  simpa [traceFiber, traceClasses] using
    (Finset.card_eq_sum_card_image (trace N (drawSet A draw)) B).symm

omit [DecidableEq β] in
lemma sum_fiberOn_card (B : Finset β) (N : β → Finset α)
    (W : Finset α) :
    (∑ T ∈ traceClasses N W B, (fiberOn B N W T).card) = B.card := by
  simpa [fiberOn, traceClasses] using
    (Finset.card_eq_sum_card_image (trace N W) B).symm

omit [DecidableEq β] in
/-- Restricting neighborhood traces to a finite sample does not increase VC
dimension. -/
lemma vcDim_traceClasses_le (B : Finset β) (N : β → Finset α)
    (W : Finset α) :
    (traceClasses N W B).vcDim ≤ (B.image N).vcDim := by
  have heq : traceClasses N W B = positionFamily (B.image N) W id := by
    ext T
    simp only [traceClasses, positionFamily, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨N b, ⟨b, hb, rfl⟩, ?_⟩
      ext x
      simp [trace, Finset.mem_inter, and_comm]
    · rintro ⟨h, ⟨b, hb, rfl⟩, heq'⟩
      refine ⟨b, hb, ?_⟩
      rw [← heq']
      ext x
      simp [trace, Finset.mem_inter, and_comm]
  rw [heq]
  exact positionFamily_vcDim_le (B.image N) W id

omit [DecidableEq β] in
lemma trace_insert_of_mem (N : β → Finset α) (W : Finset α)
    (b : β) (x : α) (hx : x ∈ N b) :
    trace N (insert x W) b = insert x (trace N W b) := by
  ext y
  simp only [trace, Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨hy, hxy | hyW⟩
    · exact Or.inl hxy
    · exact Or.inr ⟨hy, hyW⟩
  · rintro (hxy | ⟨hy, hyW⟩)
    · subst y
      exact ⟨hx, Or.inl rfl⟩
    · exact ⟨hy, Or.inr hyW⟩

omit [DecidableEq β] in
lemma trace_insert_of_not_mem (N : β → Finset α) (W : Finset α)
    (b : β) (x : α) (hx : x ∉ N b) :
    trace N (insert x W) b = trace N W b := by
  ext y
  simp only [trace, Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨hy, hxy | hyW⟩
    · subst y
      exact False.elim (hx hy)
    · exact ⟨hy, hyW⟩
  · rintro ⟨hy, hyW⟩
    exact ⟨hy, Or.inr hyW⟩

omit [DecidableEq β] in
lemma traceClass_subset_ground (B : Finset β) (N : β → Finset α)
    (W : Finset α) {T : Finset α} (hT : T ∈ traceClasses N W B) :
    T ⊆ W := by
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hT
  exact Finset.inter_subset_right

omit [DecidableEq β] in
lemma falseFiber_eq_fullFiber (B : Finset β) (N : β → Finset α)
    (W T : Finset α) (x : α) (hxW : x ∉ W) (hTW : T ⊆ W) :
    (fiberOn B N W T).filter (fun b => coordinateLabel N x b = false) =
      fiberOn B N (insert x W) T := by
  have hxT : x ∉ T := fun hx => hxW (hTW hx)
  ext b
  simp only [fiberOn, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hb, htr⟩, hfalse⟩
    have hxnot : x ∉ N b := by simpa [coordinateLabel] using hfalse
    exact ⟨hb, by rw [trace_insert_of_not_mem N W b x hxnot]; exact htr⟩
  · rintro ⟨hb, htr⟩
    have hxnot : x ∉ N b := by
      intro hx
      have hxtr : x ∈ trace N (insert x W) b := by
        simp [trace, hx]
      rw [htr] at hxtr
      exact hxT hxtr
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · rwa [trace_insert_of_not_mem N W b x hxnot] at htr
    · simp [coordinateLabel, hxnot]

omit [DecidableEq β] in
lemma trueFiber_eq_fullFiber (B : Finset β) (N : β → Finset α)
    (W T : Finset α) (x : α) (hxW : x ∉ W) (hTW : T ⊆ W) :
    (fiberOn B N W T).filter (fun b => coordinateLabel N x b = true) =
      fiberOn B N (insert x W) (insert x T) := by
  have hxT : x ∉ T := fun hx => hxW (hTW hx)
  ext b
  simp only [fiberOn, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hb, htr⟩, htrue⟩
    have hx : x ∈ N b := by simpa [coordinateLabel] using htrue
    exact ⟨hb, by rw [trace_insert_of_mem N W b x hx, htr]⟩
  · rintro ⟨hb, htr⟩
    have hx : x ∈ N b := by
      have hxtr : x ∈ trace N (insert x W) b := by
        rw [htr]
        exact Finset.mem_insert_self _ _
      exact (Finset.mem_inter.mp hxtr).1
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · rw [trace_insert_of_mem N W b x hx] at htr
      have hxshort : x ∉ trace N W b := by
        intro hxtr
        exact hxW (Finset.mem_inter.mp hxtr).2
      have := congrArg (fun U : Finset α => U.erase x) htr
      simpa [Finset.erase_insert hxshort, Finset.erase_insert hxT] using this
    · simp [coordinateLabel, hx]

omit [DecidableEq β] in
/-- Double counting the deleted position of a full IID draw converts the
sum of conditional coordinate means into the original distance mean. -/
lemma sum_full_positionMean_eq (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r : ℕ) (hN : ∀ b ∈ B, N b ⊆ A) :
    (∑ full : Fin (r + 1) → A,
      ∑ i : Fin (r + 1),
        conditionalPositionMean A B N (i.removeNth full) (full i)) =
      (r + 1 : ℚ) * ∑ draw : Fin r → A, conditionalMeanZ A B N draw := by
  calc
    (∑ full : Fin (r + 1) → A,
        ∑ i : Fin (r + 1),
          conditionalPositionMean A B N (i.removeNth full) (full i)) =
        ∑ i : Fin (r + 1), ∑ full : Fin (r + 1) → A,
          conditionalPositionMean A B N (i.removeNth full) (full i) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ x : A, ∑ draw : Fin r → A,
          conditionalPositionMean A B N draw x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_full_delete A r i
        (fun x draw => conditionalPositionMean A B N draw x)
    _ = ∑ i : Fin (r + 1), ∑ draw : Fin r → A, ∑ x : A,
          conditionalPositionMean A B N draw x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (r + 1), ∑ draw : Fin r → A,
          conditionalMeanZ A B N draw := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro draw hdraw
      exact (conditionalMeanZ_eq_sum_positionMean A B N hN draw).symm
    _ = (r + 1 : ℚ) * ∑ draw : Fin r → A,
          conditionalMeanZ A B N draw := by simp

/-- Applying the exact uniform-representative calculation to every trace
class gives the per-coordinate two-fiber upper bound. -/
lemma conditionalPositionMean_le_two_min (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) (x : A) :
    conditionalPositionMean A B N draw x ≤
      ∑ T ∈ traceClasses N (drawSet A draw) B,
        (2 * min
          (falseLabelCount (traceFiber A B N draw T) (coordinateLabel N x.1))
          (trueLabelCount (traceFiber A B N draw T) (coordinateLabel N x.1)) : ℚ) := by
  rw [conditionalPositionMean_eq_uniform]
  apply Finset.sum_le_sum
  intro T hT
  exact uniform_coordinateDisagreement_le_two_min
    (traceFiber A B N draw T) N x.1
    (traceFiber_nonempty_of_mem_traceClasses A B N draw hT)

lemma conditionalPositionMean_zero_of_mem_drawSet (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r : ℕ} (draw : Fin r → A) (x : A)
    (hx : x.1 ∈ drawSet A draw) :
    conditionalPositionMean A B N draw x = 0 := by
  rw [conditionalPositionMean_eq_uniform]
  apply Finset.sum_eq_zero
  intro T hT
  let C := traceFiber A B N draw T
  have hconstant (b rep : β) (hb : b ∈ C) (hrep : rep ∈ C) :
      coordinateLabel N x.1 b = coordinateLabel N x.1 rep := by
    have hbt : trace N (drawSet A draw) b = T := (Finset.mem_filter.mp hb).2
    have hrt : trace N (drawSet A draw) rep = T := (Finset.mem_filter.mp hrep).2
    have heq : x.1 ∈ N b ↔ x.1 ∈ N rep := by
      have hxb : x.1 ∈ N b ↔ x.1 ∈ T := by
        rw [← hbt]
        simp [trace, hx]
      have hxr : x.1 ∈ N rep ↔ x.1 ∈ T := by
        rw [← hrt]
        simp [trace, hx]
      exact hxb.trans hxr.symm
    simp only [coordinateLabel]
    by_cases hb' : x.1 ∈ N b <;> by_cases hr' : x.1 ∈ N rep <;>
      simp_all
  unfold uniformRepresentativeMean
  have hzero (rep : β) (hrep : rep ∈ C) :
      disagreementToRepresentative C (coordinateLabel N x.1) rep = 0 := by
    unfold disagreementToRepresentative
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b hb
    simp [hconstant b rep hb hrep]
  have hsum : (∑ rep ∈ C,
      (disagreementToRepresentative C (coordinateLabel N x.1) rep : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro rep hrep
    exact_mod_cast hzero rep hrep
  rw [hsum]
  simp

/-- At a fresh coordinate, every positive two-fiber contribution is charged
to its unique one-inclusion edge in the full trace family. -/
lemma sum_two_min_le_edges_at_coordinate (B : Finset β) (N : β → Finset α)
    (W : Finset α) (x : α) (hxW : x ∉ W) :
    (∑ T ∈ traceClasses N W B,
      (2 * min
        (falseLabelCount (fiberOn B N W T) (coordinateLabel N x))
        (trueLabelCount (fiberOn B N W T) (coordinateLabel N x)) : ℚ)) ≤
      ∑ e ∈ (edges (traceClasses N (insert x W) B)).filter (fun e => e.2 = x),
        (2 * min
          (fiberOn B N (insert x W) e.1).card
          (fiberOn B N (insert x W) (e.1.erase e.2)).card : ℚ) := by
  let H := traceClasses N (insert x W) B
  let w := fun T : Finset α => (fiberOn B N (insert x W) T).card
  let f := fun T : Finset α => (2 * min
    (falseLabelCount (fiberOn B N W T) (coordinateLabel N x))
    (trueLabelCount (fiberOn B N W T) (coordinateLabel N x)) : ℚ)
  let g := fun e : Finset α × α => (2 * min (w e.1) (w (e.1.erase e.2)) : ℚ)
  let S := (traceClasses N W B).filter (fun T =>
    0 < falseLabelCount (fiberOn B N W T) (coordinateLabel N x) ∧
    0 < trueLabelCount (fiberOn B N W T) (coordinateLabel N x))
  let E := (edges H).filter (fun e => e.2 = x)
  have hsumS : (∑ T ∈ traceClasses N W B, f T) = ∑ T ∈ S, f T := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro T hT hTS
    have hnot : ¬ (0 < falseLabelCount (fiberOn B N W T) (coordinateLabel N x) ∧
        0 < trueLabelCount (fiberOn B N W T) (coordinateLabel N x)) := by
      simpa [S, hT] using hTS
    by_cases hf : 0 < falseLabelCount (fiberOn B N W T) (coordinateLabel N x)
    · have ht : trueLabelCount (fiberOn B N W T) (coordinateLabel N x) = 0 := by
        omega
      simp [f, ht]
    · have hf0 : falseLabelCount (fiberOn B N W T) (coordinateLabel N x) = 0 := by
        omega
      simp [f, hf0]
  have hmap (T : Finset α) (hT : T ∈ S) : (insert x T, x) ∈ E := by
    have hbase : T ∈ traceClasses N W B := (Finset.mem_filter.mp hT).1
    have hground : T ⊆ W := traceClass_subset_ground B N W hbase
    have hxT : x ∉ T := fun hx => hxW (hground hx)
    have hfalse : 0 < falseLabelCount (fiberOn B N W T) (coordinateLabel N x) :=
      (Finset.mem_filter.mp hT).2.1
    have htrue : 0 < trueLabelCount (fiberOn B N W T) (coordinateLabel N x) :=
      (Finset.mem_filter.mp hT).2.2
    have hlower : T ∈ H := by
      have hne : (fiberOn B N (insert x W) T).Nonempty := by
        rw [← falseFiber_eq_fullFiber B N W T x hxW hground]
        exact Finset.card_pos.mp hfalse
      obtain ⟨b, hb⟩ := hne
      exact Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1,
        (Finset.mem_filter.mp hb).2⟩
    have hupper : insert x T ∈ H := by
      have hne : (fiberOn B N (insert x W) (insert x T)).Nonempty := by
        rw [← trueFiber_eq_fullFiber B N W T x hxW hground]
        exact Finset.card_pos.mp htrue
      obtain ⟨b, hb⟩ := hne
      exact Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1,
        (Finset.mem_filter.mp hb).2⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_edges.mpr
      refine ⟨hupper, Finset.mem_insert_self _ _, ?_⟩
      simpa [Finset.erase_insert hxT] using hlower
    · rfl
  have hinj : Set.InjOn (fun T : Finset α => (insert x T, x)) (S : Set (Finset α)) := by
    intro T hT U hU heq
    have hgroundT : T ⊆ W := traceClass_subset_ground B N W (Finset.mem_filter.mp hT).1
    have hgroundU : U ⊆ W := traceClass_subset_ground B N W (Finset.mem_filter.mp hU).1
    have hxT : x ∉ T := fun hx => hxW (hgroundT hx)
    have hxU : x ∉ U := fun hx => hxW (hgroundU hx)
    have heq' : insert x T = insert x U := congrArg Prod.fst heq
    have := congrArg (fun V : Finset α => V.erase x) heq'
    simpa [Finset.erase_insert hxT, Finset.erase_insert hxU] using this
  have hvalue (T : Finset α) (hT : T ∈ S) : f T = g (insert x T, x) := by
    have hground : T ⊆ W := traceClass_subset_ground B N W (Finset.mem_filter.mp hT).1
    have hxT : x ∉ T := fun hx => hxW (hground hx)
    have hfalse := falseFiber_eq_fullFiber B N W T x hxW hground
    have htrue := trueFiber_eq_fullFiber B N W T x hxW hground
    simp only [f, g, w, falseLabelCount, trueLabelCount]
    rw [hfalse, htrue]
    simp [Finset.erase_insert hxT, min_comm]
  calc
    (∑ T ∈ traceClasses N W B, f T) = ∑ T ∈ S, f T := hsumS
    _ = ∑ e ∈ S.image (fun T => (insert x T, x)), g e := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl hvalue
    _ ≤ ∑ e ∈ E, g e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp he
        exact hmap T hT
      · intro e he hnot
        simp [g]

lemma conditionalPositionMean_le_edges_at_coordinate (A : Finset α)
    (B : Finset β) (N : β → Finset α) {r : ℕ}
    (full : Fin (r + 1) → A) (i : Fin (r + 1)) :
    conditionalPositionMean A B N (i.removeNth full) (full i) ≤
      if (full i).1 ∉ drawSet A (i.removeNth full) then
        ∑ e ∈ (edges (traceClasses N (drawSet A full) B)).filter
            (fun e => e.2 = (full i).1),
          (2 * min
            (fiberOn B N (drawSet A full) e.1).card
            (fiberOn B N (drawSet A full) (e.1.erase e.2)).card : ℚ)
      else 0 := by
  let W := drawSet A (i.removeNth full)
  let x := (full i).1
  by_cases hx : x ∈ W
  · simp only [show ¬ ((full i).1 ∉ drawSet A (i.removeNth full)) from
        not_not.mpr hx, ↓reduceIte]
    exact le_of_eq (conditionalPositionMean_zero_of_mem_drawSet A B N
      (i.removeNth full) (full i) hx)
  · simp only [show (full i).1 ∉ drawSet A (i.removeNth full) from hx]
    have hle := conditionalPositionMean_le_two_min A B N
      (i.removeNth full) (full i)
    have hbound := sum_two_min_le_edges_at_coordinate B N W x hx
    simp only [traceFiber_eq_fiberOn] at hle
    rw [drawSet_full_eq_insert A full i]
    exact hle.trans hbound

lemma fresh_position_unique (A : Finset α) {r : ℕ}
    (full : Fin (r + 1) → A) (i : Fin (r + 1))
    (hi : (full i).1 ∉ drawSet A (i.removeNth full))
    (j : Fin (r + 1)) (hij : (full j).1 = (full i).1) : j = i := by
  rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨k, hji⟩
  · exact hji
  · exfalso
    apply hi
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    simpa [drawSet, Fin.removeNth, hji] using hij

/-- On one full ordered tape, fresh-position charges use distinct edge
coordinates, so the weighted VC bound controls their total. -/
lemma sum_full_positionMean_le (A : Finset α) (B : Finset β)
    (N : β → Finset α) {r d : ℕ} (full : Fin (r + 1) → A)
    (hvc : (B.image N).vcDim ≤ d) :
    (∑ i : Fin (r + 1),
      conditionalPositionMean A B N (i.removeNth full) (full i)) ≤
      (2 * d * B.card : ℚ) := by
  let H := traceClasses N (drawSet A full) B
  let w := fun T : Finset α => (fiberOn B N (drawSet A full) T).card
  let g := fun e : Finset α × α => (2 * min (w e.1) (w (e.1.erase e.2)) : ℚ)
  let fresh := fun i : Fin (r + 1) => (full i).1 ∉ drawSet A (i.removeNth full)
  have hpoint (i : Fin (r + 1)) :
      conditionalPositionMean A B N (i.removeNth full) (full i) ≤
        if fresh i then ∑ e ∈ (edges H).filter (fun e => e.2 = (full i).1), g e
        else 0 := conditionalPositionMean_le_edges_at_coordinate A B N full i
  have hcharge :
      (∑ i : Fin (r + 1),
        if fresh i then ∑ e ∈ (edges H).filter (fun e => e.2 = (full i).1), g e
        else 0) ≤ ∑ e ∈ edges H, g e := by
    have hreorder :
        (∑ i : Fin (r + 1),
          if fresh i then ∑ e ∈ (edges H).filter (fun e => e.2 = (full i).1), g e
          else 0) =
          ∑ e ∈ edges H, ∑ i : Fin (r + 1),
            if fresh i ∧ e.2 = (full i).1 then g e else 0 := by
      calc
        _ = ∑ i : Fin (r + 1), ∑ e ∈ edges H,
              if fresh i ∧ e.2 = (full i).1 then g e else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hfi : fresh i
          · simp [hfi, Finset.sum_filter]
          · simp [hfi]
        _ = _ := Finset.sum_comm
    rw [hreorder]
    apply Finset.sum_le_sum
    intro e he
    let I := (Finset.univ : Finset (Fin (r + 1))).filter
      (fun i => fresh i ∧ e.2 = (full i).1)
    have hcard : I.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      have hii := (Finset.mem_filter.mp hi).2
      have hjj := (Finset.mem_filter.mp hj).2
      have hval : (full j).1 = (full i).1 := hjj.2.symm.trans hii.2
      exact (fresh_position_unique A full i hii.1 j hval).symm
    have heq : (∑ i : Fin (r + 1),
        if fresh i ∧ e.2 = (full i).1 then g e else 0) = (I.card : ℚ) * g e := by
      rw [← Finset.sum_filter]
      simp [I, Finset.sum_const, nsmul_eq_mul]
    rw [heq]
    have hgnonneg : 0 ≤ g e := by simp [g]
    exact mul_le_of_le_one_left hgnonneg (by exact_mod_cast hcard)
  have hedge : (∑ e ∈ edges H, g e) ≤ (2 * d * B.card : ℚ) := by
    have hHvc : H.vcDim ≤ d :=
      (vcDim_traceClasses_le B N (drawSet A full)).trans hvc
    have hnat := twice_weighted_oneInclusion_bound H w d hHvc
    have hnatQ :
        (∑ e ∈ edges H, g e) ≤
          (2 * d * ∑ T ∈ H, w T : ℚ) := by
      dsimp [g]
      exact_mod_cast hnat
    rw [show (∑ T ∈ H, w T) = B.card from
      sum_fiberOn_card B N (drawSet A full)] at hnatQ
    exact hnatQ
  exact (Finset.sum_le_sum (fun i hi => hpoint i)).trans (hcharge.trans hedge)

/-- The actual first moment of independent uniform draws and independent
uniform representatives satisfies the initial one-inclusion estimate. -/
lemma initialMeanZ_bound (A : Finset α) (B : Finset β)
    (N : β → Finset α) (r d : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hvc : (B.image N).vcDim ≤ d) :
    (r + 1 : ℚ) * initialMeanZ A B N r ≤
      (2 * d * A.card * B.card : ℚ) := by
  have hsum :
      (r + 1 : ℚ) * ∑ draw : Fin r → A, conditionalMeanZ A B N draw ≤
        (A.card ^ (r + 1) : ℚ) * (2 * d * B.card : ℚ) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (r + 1) → A)))
      (fun full _ => sum_full_positionMean_le A B N full hvc)
    rw [sum_full_positionMean_eq A B N r hN] at h
    simpa [card_draws, mul_comm] using h
  have hden : 0 < (A.card ^ r : ℚ) := by
    have hc : 0 < A.card := Finset.card_pos.mpr hA
    positivity
  have hpow : (A.card ^ (r + 1) : ℚ) = (A.card : ℚ) * (A.card ^ r : ℚ) := by
    ring
  unfold initialMeanZ
  rw [mul_div_assoc', div_le_iff₀ hden]
  rw [hpow] at hsum
  nlinarith

/-- The paper's explicit initial-distance constant follows from a linear
trace bound and the floor-sized sample. -/
lemma initialMeanZ_explicit_bound (A : Finset α) (B : Finset β)
    (N : β → Finset α) (c : ℕ)
    (hA : A.Nonempty) (hN : ∀ b ∈ B, N b ⊆ A)
    (hc : 2 ≤ c) (hB : B.card ≤ c * A.card)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (traceFamily (B.image N) S).card ≤ c * S.card) :
    initialMeanZ A B N (A.card / (4 * c ^ 2)) ≤
      (32 * c ^ 3 * A.card * Nat.clog 2 c : ℚ) := by
  let n := A.card
  let l := Nat.clog 2 c
  let k := 4 * c ^ 2
  let r := n / k
  have hk : 0 < k := by dsimp [k]; positivity
  have hn : 0 < n := Finset.card_pos.mpr hA
  have hvc : (B.image N).vcDim ≤ 4 * l :=
    vcDim_le_four_clog (B.image N) c hc hlinear
  have hmean := initialMeanZ_bound A B N r (4 * l) hA hN hvc
  simp only [Nat.cast_mul] at hmean
  have hnum : 2 * (4 * l) * n * B.card ≤
      8 * c * l * n * n := by
    calc
      2 * (4 * l) * n * B.card ≤ 2 * (4 * l) * n * (c * n) := by
        gcongr
      _ = 8 * c * l * n * n := by ring
  have hnumQ : (2 * (4 * l) * n * B.card : ℚ) ≤
      (8 * c * l * n * n : ℚ) := by exact_mod_cast hnum
  have hfloor : n ≤ k * (r + 1) :=
    (Nat.lt_mul_div_succ n hk).le
  have hfloorQ : (n : ℚ) ≤ (k : ℚ) * (r + 1 : ℚ) := by
    exact_mod_cast hfloor
  have htarget : (8 * c * l * n * n : ℚ) ≤
      (r + 1 : ℚ) * (32 * c ^ 3 * n * l : ℚ) := by
    have hmul : (8 * c * l * n : ℚ) * n ≤
        (8 * c * l * n : ℚ) * ((k : ℚ) * (r + 1 : ℚ)) := by
      exact mul_le_mul_of_nonneg_left hfloorQ (by positivity)
    dsimp [k] at hmul
    push_cast at hmul
    nlinarith [hmul]
  have hbound : (r + 1 : ℚ) * initialMeanZ A B N r ≤
      (r + 1 : ℚ) * (32 * c ^ 3 * n * l : ℚ) :=
    hmean.trans (hnumQ.trans htarget)
  have hrpos : (0 : ℚ) < r + 1 := by positivity
  have := le_of_mul_le_mul_left hbound hrpos
  simpa [r, n, l, k] using this

end Lax457868Proofs.SamplerInitialExpectation
