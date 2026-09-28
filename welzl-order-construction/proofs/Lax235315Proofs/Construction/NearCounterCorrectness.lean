import Lax235315Proofs.Construction.NearCheckSource
import Lax235315Proofs.Construction.NearVerification
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-! Identification of the numeric sweep counters with graph traces. -/

namespace Lax235315Proofs.Construction.NearCounterCorrectness

open scoped symmDiff
open Lax11.GraphEncoding Lax11Proofs.CC
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NeighborhoodComplexity
open Lax235315Proofs.Construction.NearCheckSource
open Lax235315Proofs.Construction.NearSweepMath
open Lax235315Proofs.Construction.NeighborScan
open Lax235315Proofs.Construction.NearVerification

noncomputable section

/-- A generic array view of one completed CSR block has exactly the active
graph neighbors of its source. -/
lemma mem_neighborBlock_iff
    {n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off active : ℕ → ℕ}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    {a v : ℕ} (ha : a < n) :
    v ∈ neighborBlock target off active a ↔ active v = 1 ∧ Adjn G a v := by
  rw [neighborBlock, mem_activeTargets]
  constructor
  · rintro ⟨hv, j, hlo, hhi, hjv⟩
    have hhi' : j < offset x (a + 1) := by
      rwa [hoffEq (a + 1) (by omega)] at hhi
    have hlo' : offset x a ≤ j := by rwa [hoffEq a (by omega)] at hlo
    have hjCap : j < targetCap := by
      calc
        j < offset x (a + 1) := hhi'
        _ ≤ 2 * edgeCount x := offset_le hx (by omega)
        _ = targetCap := htargetCap.symm
    have hjv' : Lax11.GraphEncoding.target x j = v := by
      rw [← htargetEq j hjCap]
      exact hjv
    exact ⟨hv, hjv' ▸ adjn_of_slot hx ha hlo' hhi'⟩
  · rintro ⟨hv, hadj⟩
    obtain ⟨j, hlo, hhi, hjv⟩ := slot_of_adjn hx hadj
    have hjCap : j < targetCap := by
      calc
        j < offset x (a + 1) := hhi
        _ ≤ 2 * edgeCount x := offset_le hx (by omega)
        _ = targetCap := htargetCap.symm
    refine ⟨hv, j, ?_, ?_, ?_⟩
    · rwa [hoffEq a (by omega)]
    · rwa [hoffEq (a + 1) (by omega)]
    · rw [htargetEq j hjCap]
      exact hjv

/-- Numeric active neighbors of the vertex numbered `b`. -/
def activeNeighborNumbers {n : ℕ} (G : SimpleGraph (Fin n))
    (active : ℕ → ℕ) (b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun a => active a = 1 ∧ Adjn G a b

/-- Numeric active common neighbors of `b` and `r`. -/
def activeCommonNeighborNumbers {n : ℕ} (G : SimpleGraph (Fin n))
    (active : ℕ → ℕ) (b r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun a =>
    active a = 1 ∧ Adjn G a b ∧ Adjn G a r

lemma degreePrefix_full_eq_card
    {n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB : ℕ → ℕ}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    {b : ℕ} (hb : activeB b = 1) :
    degreePrefix target off activeA activeB n b =
      (activeNeighborNumbers G activeA b).card := by
  unfold degreePrefix activeNeighborNumbers
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨haN, haa, hab⟩
    exact ⟨haN, haa, (mem_neighborBlock_iff hx htargetCap hoffEq htargetEq haN).mp hab |>.2⟩
  · rintro ⟨haN, haa, hab⟩
    exact ⟨haN, haa, (mem_neighborBlock_iff hx htargetCap hoffEq htargetEq haN).mpr
      ⟨hb, hab⟩⟩

lemma commonPrefix_full_eq_card
    {n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB rep : ℕ → ℕ}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    {b : ℕ} (hb : activeB b = 1) (hr : activeB (rep b) = 1) :
    commonPrefix target off activeA activeB rep n b =
      (activeCommonNeighborNumbers G activeA b (rep b)).card := by
  unfold commonPrefix activeCommonNeighborNumbers
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨haN, haa, hab, har⟩
    exact ⟨haN, haa,
      (mem_neighborBlock_iff hx htargetCap hoffEq htargetEq haN).mp hab |>.2,
      (mem_neighborBlock_iff hx htargetCap hoffEq htargetEq haN).mp har |>.2⟩
  · rintro ⟨haN, haa, hab, har⟩
    exact ⟨haN, haa,
      (mem_neighborBlock_iff hx htargetCap hoffEq htargetEq haN).mpr ⟨hb, hab⟩,
      (mem_neighborBlock_iff hx htargetCap hoffEq htargetEq haN).mpr ⟨hr, har⟩⟩

/-- The active ground set represented by a zero-one array. -/
def activeFinset {n : ℕ} (active : ℕ → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => active v.val = 1

@[simp] lemma mem_activeFinset {n : ℕ} {active : ℕ → ℕ}
    {v : Fin n} : v ∈ activeFinset active ↔ active v.val = 1 := by
  simp [activeFinset]

lemma activeNeighborNumbers_card_eq_traceFinset
    {n : ℕ} (G : SimpleGraph (Fin n)) (active : ℕ → ℕ)
    (b : Fin n) :
    (activeNeighborNumbers G active b.val).card =
      (traceFinset G (activeFinset active) b).card := by
  classical
  apply Finset.card_bij
      (fun a ha => ⟨a, by
        change a ∈ (Finset.range n).filter
          (fun q => active q = 1 ∧ Adjn G q b.val) at ha
        exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1⟩)
  · intro a ha
    change a ∈ (Finset.range n).filter
      (fun q => active q = 1 ∧ Adjn G q b.val) at ha
    rcases Finset.mem_filter.mp ha with ⟨haN, haa, hadj⟩
    rcases hadj with ⟨haN', hbN, hadj⟩
    simp [traceFinset, neighborhoodTrace, activeFinset]
    exact ⟨by simpa using hadj.symm, haa⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    exact Fin.ext_iff.mp heq
  · intro v hv
    simp [traceFinset, neighborhoodTrace, activeFinset] at hv
    refine ⟨v.val, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr v.isLt, hv.2, ?_⟩, ?_⟩
    · exact ⟨v.isLt, b.isLt, by simpa using hv.1.symm⟩
    · exact Fin.ext rfl

lemma activeCommonNeighborNumbers_card_eq_inter
    {n : ℕ} (G : SimpleGraph (Fin n)) (active : ℕ → ℕ)
    (b r : Fin n) :
    (activeCommonNeighborNumbers G active b.val r.val).card =
      (traceFinset G (activeFinset active) b ∩
        traceFinset G (activeFinset active) r).card := by
  classical
  apply Finset.card_bij
      (fun a ha => ⟨a, by
        change a ∈ (Finset.range n).filter
          (fun q => active q = 1 ∧ Adjn G q b.val ∧ Adjn G q r.val) at ha
        exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1⟩)
  · intro a ha
    change a ∈ (Finset.range n).filter
      (fun q => active q = 1 ∧ Adjn G q b.val ∧ Adjn G q r.val) at ha
    rcases Finset.mem_filter.mp ha with ⟨haN, haa, hab, har⟩
    rcases hab with ⟨haN', hbN, hab⟩
    rcases har with ⟨haN'', hrN, har⟩
    simp [traceFinset, neighborhoodTrace, activeFinset]
    exact ⟨by simpa using hab.symm, haa, by simpa using har.symm, haa⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    exact Fin.ext_iff.mp heq
  · intro v hv
    simp [traceFinset, neighborhoodTrace, activeFinset] at hv
    refine ⟨v.val, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr v.isLt, hv.2.1, ?_, ?_⟩, ?_⟩
    · exact ⟨v.isLt, b.isLt, by simpa using hv.1.symm⟩
    · exact ⟨v.isLt, r.isLt, by simpa using hv.2.2.1.symm⟩
    · exact Fin.ext rfl

/-- The verifier's final arithmetic distance is exactly the restricted
open-neighborhood symmetric difference used in the paper. -/
lemma nearDistance_eq_neighborhood_symmDiff
    {n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {target off activeA activeB rep : ℕ → ℕ}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hoffEq : ∀ i ≤ n, off i = offset x i)
    (htargetEq : ∀ j < targetCap, target j = Lax11.GraphEncoding.target x j)
    {b : ℕ} (hbN : b < n) (hrN : rep b < n)
    (hb : activeB b = 1) (hr : activeB (rep b) = 1) :
    nearDistance
        (degreePrefix target off activeA activeB n)
        (commonPrefix target off activeA activeB rep n) rep b =
      ((G.neighborSet ⟨b, hbN⟩ ∩
          (activeFinset (n := n) activeA : Set (Fin n))) ∆
        (G.neighborSet ⟨rep b, hrN⟩ ∩
          (activeFinset (n := n) activeA : Set (Fin n)))).ncard := by
  rw [nearDistance, degreePrefix_full_eq_card hx htargetCap hoffEq htargetEq hb,
    degreePrefix_full_eq_card hx htargetCap hoffEq htargetEq hr,
    commonPrefix_full_eq_card hx htargetCap hoffEq htargetEq hb hr,
    activeNeighborNumbers_card_eq_traceFinset G activeA ⟨b, hbN⟩,
    activeNeighborNumbers_card_eq_traceFinset G activeA ⟨rep b, hrN⟩,
    activeCommonNeighborNumbers_card_eq_inter G activeA ⟨b, hbN⟩
      ⟨rep b, hrN⟩]
  exact (neighborhood_symmDiff_ncard_eq G (activeFinset (n := n) activeA)
    ⟨b, hbN⟩ ⟨rep b, hrN⟩).symm

end

end Lax235315Proofs.Construction.NearCounterCorrectness
