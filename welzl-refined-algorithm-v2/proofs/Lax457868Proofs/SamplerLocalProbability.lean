import Mathlib.Tactic
import Lax457868Proofs.SamplerUniformDraws

/-!
The local repair check is exactly a range-hitting event in the finite uniform
draw experiment.  Counts are kept as finite cardinalities, so no probability
axioms or assumed outcome probabilities enter the statements.
-/

namespace Lax457868Proofs.SamplerLocalProbability

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerUniformDraws

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The ground vertices that distinguish the neighborhoods at `b` and `v`. -/
def distinguishingRange (N : β → Finset α) (b v : β) : Finset α :=
  (N b \ N v) ∪ (N v \ N b)

/-- Once `b` and `v` agree on `W`, a local trial separates them exactly when
at least one draw lies in their distinguishing range. -/
lemma trace_ne_iff_draw_hits (N : β → Finset α) (W : Finset α)
    (b v : β) (draws : List α)
    (hbase : trace N W b = trace N W v) :
    trace N (W ∪ draws.toFinset) b ≠ trace N (W ∪ draws.toFinset) v ↔
      ∃ a ∈ draws, a ∈ distinguishingRange N b v := by
  constructor
  · intro hne
    have hex : ∃ a, (a ∈ trace N (W ∪ draws.toFinset) b ∧
        a ∉ trace N (W ∪ draws.toFinset) v) ∨
        (a ∈ trace N (W ∪ draws.toFinset) v ∧
          a ∉ trace N (W ∪ draws.toFinset) b) := by
      by_contra hn
      apply hne
      ext a
      by_cases hab : a ∈ trace N (W ∪ draws.toFinset) b
      · have hav : a ∈ trace N (W ∪ draws.toFinset) v := by
          by_contra hnot
          exact hn ⟨a, Or.inl ⟨hab, hnot⟩⟩
        simp [hab, hav]
      · have hav : a ∉ trace N (W ∪ draws.toFinset) v := by
          by_contra hmem
          exact hn ⟨a, Or.inr ⟨hmem, hab⟩⟩
        simp [hab, hav]
    rcases hex with ⟨a, hdiff | hdiff⟩
    · have hleft : a ∈ N b ∧ a ∈ W ∪ draws.toFinset := by
        simpa [trace] using hdiff.1
      have hright : ¬ (a ∈ N v ∧ a ∈ W ∪ draws.toFinset) := by
        simpa [trace] using hdiff.2
      have hnotW : a ∉ W := by
        intro haW
        have htraceB : a ∈ trace N W b := by
          simpa [trace] using ⟨hleft.1, haW⟩
        have htraceV : a ∈ trace N W v := hbase ▸ htraceB
        have hNv : a ∈ N v := (Finset.mem_inter.mp (by simpa [trace] using htraceV)).1
        exact hright ⟨hNv, Finset.mem_union.mpr (Or.inl haW)⟩
      have haDraw : a ∈ draws := by
        have haSample := Finset.mem_union.mp hleft.2
        rcases haSample with haW | haD
        · exact (hnotW haW).elim
        · simpa using haD
      have hnotNv : a ∉ N v := by
        intro haNv
        exact hright ⟨haNv, Finset.mem_union.mpr (Or.inr (by simpa using haDraw))⟩
      exact ⟨a, haDraw, by
        simp only [distinguishingRange, Finset.mem_union, Finset.mem_sdiff]
        exact Or.inl ⟨hleft.1, hnotNv⟩⟩
    · have hleft : a ∈ N v ∧ a ∈ W ∪ draws.toFinset := by
        simpa [trace] using hdiff.1
      have hright : ¬ (a ∈ N b ∧ a ∈ W ∪ draws.toFinset) := by
        simpa [trace] using hdiff.2
      have hnotW : a ∉ W := by
        intro haW
        have htraceV : a ∈ trace N W v := by
          simpa [trace] using ⟨hleft.1, haW⟩
        have htraceB : a ∈ trace N W b := hbase.symm ▸ htraceV
        have hNb : a ∈ N b := (Finset.mem_inter.mp (by simpa [trace] using htraceB)).1
        exact hright ⟨hNb, Finset.mem_union.mpr (Or.inl haW)⟩
      have haDraw : a ∈ draws := by
        have haSample := Finset.mem_union.mp hleft.2
        rcases haSample with haW | haD
        · exact (hnotW haW).elim
        · simpa using haD
      have hnotNb : a ∉ N b := by
        intro haNb
        exact hright ⟨haNb, Finset.mem_union.mpr (Or.inr (by simpa using haDraw))⟩
      exact ⟨a, haDraw, by
        simp only [distinguishingRange, Finset.mem_union, Finset.mem_sdiff]
        exact Or.inr ⟨hleft.1, hnotNb⟩⟩
  · rintro ⟨a, haDraw, haRange⟩
    have haSample : a ∈ W ∪ draws.toFinset :=
      Finset.mem_union.mpr (Or.inr (by simpa using haDraw))
    have hmemDiff := by
      simpa only [distinguishingRange, Finset.mem_union, Finset.mem_sdiff] using haRange
    intro heq
    have hmem := congrArg (fun T : Finset α => a ∈ T) heq
    simp only [trace, Finset.mem_inter] at hmem
    rcases hmemDiff with h | h
    · exact h.2 ((hmem.mp ⟨h.1, haSample⟩).1)
    · exact h.2 ((hmem.mpr ⟨h.1, haSample⟩).1)

/-- A tape intersects a range precisely when its associated draw list does. -/
lemma tape_hits_iff (X D : Finset α) (s : ℕ) (tape : Tape X s) :
    (∃ a ∈ tape.toList, a ∈ D) ↔ ∃ i, (tape i).val ∈ D := by
  simp [Tape.toList, List.mem_ofFn]

/-- Restricting a distinguishing range to `Y ⊆ X` is the symmetric difference
of the two neighborhood traces on `Y`. -/
lemma distinguishingRange_inter_eq_traceDiff
    (N : β → Finset α) (X Y : Finset α) (b v : β)
    (hYX : Y ⊆ X) :
    (X ∩ distinguishingRange N b v) ∩ Y =
      (trace N Y b \ trace N Y v) ∪ (trace N Y v \ trace N Y b) := by
  ext a
  by_cases hy : a ∈ Y
  · have hx : a ∈ X := hYX hy
    simp [trace, distinguishingRange, hy, hx, Finset.mem_inter, Finset.mem_sdiff]
  · simp [trace, distinguishingRange, hy, Finset.mem_inter, Finset.mem_sdiff]

/-- The distinguishing-range family inherits the same trace bound as the
original neighborhood family: fixing `b` and taking symmetric difference
cannot create more traces. -/
lemma distinguishingFamily_trace_card_le
    (N : β → Finset α) (X Y : Finset α) (B : Finset β) (b : β)
    (hYX : Y ⊆ X) :
    (B.image fun v => (X ∩ distinguishingRange N b v) ∩ Y).card ≤
      (traceClasses N Y B).card := by
  let fixed := trace N Y b
  let xorFixed := fun T : Finset α => (fixed \ T) ∪ (T \ fixed)
  have himage : B.image (fun v => (X ∩ distinguishingRange N b v) ∩ Y) =
      (traceClasses N Y B).image xorFixed := by
    rw [traceClasses, Finset.image_image]
    apply Finset.image_congr
    intro v hv
    exact distinguishingRange_inter_eq_traceDiff N X Y b v hYX
  rw [himage]
  exact Finset.card_image_le

/-- If neighborhood traces satisfy the linear shatter bound `c·|Y|`, the
induced distinguishing ranges satisfy that same bound on every `Y ⊆ X`. -/
lemma distinguishingFamily_card_le_of_trace_bound
    (N : β → Finset α) (X Y : Finset α) (B : Finset β) (b : β)
    (c : ℕ) (hYX : Y ⊆ X)
    (htrace : (traceClasses N Y B).card ≤ c * Y.card) :
    (B.image fun v => (X ∩ distinguishingRange N b v) ∩ Y).card ≤ c * Y.card :=
  (distinguishingFamily_trace_card_le N X Y B b hYX).trans htrace

/-- A range meeting more than half of `X` is missed by at most a `2^-s`
fraction of the uniform ordered tapes.  The probability inequality is stated
as a cross-multiplied count inequality to avoid division-by-zero conventions. -/
lemma majority_range_miss_count
    (X D : Finset α) (s : ℕ)
    (hmajority : 2 * (X ∩ D).card > X.card) :
    missSpace X D s * 2 ^ s ≤ (sampleSpace X s).card := by
  have hfilter : (X.filter (fun a => a ∉ D)).card = X.card - (X ∩ D).card := by
    rw [show X.filter (fun a => a ∉ D) = X \ D by
      ext a
      simp [Finset.mem_sdiff]]
    rw [Finset.card_sdiff]
    simp only [Finset.inter_comm]
  have hhalf : 2 * (X.card - (X ∩ D).card) ≤ X.card := by omega
  have hpow : (X.card - (X ∩ D).card) ^ s * 2 ^ s ≤ X.card ^ s := by
    calc
      (X.card - (X ∩ D).card) ^ s * 2 ^ s =
          ((X.card - (X ∩ D).card) * 2) ^ s := by rw [Nat.mul_pow]
      _ ≤ X.card ^ s := Nat.pow_le_pow_left (by omega) s
  rw [card_missSpace, hfilter, card_sampleSpace]
  exact hpow

/-- For a legal tape, failure of the phase-three local isolation predicate is
equivalent to the tape missing one distinguishing range from the fixed
phase-two trace class. -/
lemma not_localTrialIsolates_iff_tape_misses_range
    (N : β → Finset α) (B : Finset β) (W : Finset α) (b : β)
    (X : Finset α) (s : ℕ) (tape : Tape X s) :
    ¬ localTrialIsolates N B W b tape.toList ↔
      ∃ v ∈ B, trace N W b = trace N W v ∧ v ≠ b ∧
        Misses (distinguishingRange N b v) tape := by
  classical
  simp only [localTrialIsolates, not_forall, _root_.not_imp]
  constructor
  · rintro ⟨v, hv, htrace, hvb, hfail⟩
    refine ⟨v, hv, htrace, hvb, ?_⟩
    intro i
    have hnotHit : ¬ ∃ a ∈ tape.toList,
        a ∈ distinguishingRange N b v := by
      intro hhit
      exact hfail ((trace_ne_iff_draw_hits N W b v tape.toList htrace).2 hhit)
    exact fun ha => hnotHit ⟨(tape i).val, by simp [Tape.toList], ha⟩
  · rintro ⟨v, hv, htrace, hvb, hmiss⟩
    refine ⟨v, hv, htrace, hvb, ?_⟩
    intro hsep
    have hhit := (trace_ne_iff_draw_hits N W b v tape.toList htrace).1 hsep
    rcases (tape_hits_iff X _ s tape).1 hhit with ⟨i, hi⟩
    exact hmiss i hi

end Lax457868Proofs.SamplerLocalProbability
