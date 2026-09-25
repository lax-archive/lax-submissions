import Lax235315Proofs.Construction.RepresentativeSource
import Lax235315Proofs.Construction.PartitionRefinement
import Mathlib.Tactic

/-! Conversion of concrete representative arrays into a trace partition. -/

namespace Lax235315Proofs.Construction.PartitionResult

open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PartitionRefinement
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

/-- A finite set of numeric vertices, viewed in `Fin n`. -/
def finSetAsSet {n : ℕ} (R : Finset ℕ) : Set (Fin n) :=
  {v | v.val ∈ R}

/-- A trace partition whose representative function is realized by the
concrete numeric `repOf` array on every active vertex. -/
structure ConcreteTracePartition {n : ℕ} (G : SimpleGraph (Fin n))
    (active : ℕ → ℕ) (S : Set (Fin n)) (R : Finset ℕ)
    (repOf : ℕ → ℕ) where
  partition : TracePartition G {v : Fin n | active v.val = 1} S (finSetAsSet R)
  representative_val : ∀ (v : Fin n), active v.val = 1 →
    (partition.representative v).val = repOf v.val

theorem ConcreteTracePartition.rep_lt
    {n : ℕ} {G : SimpleGraph (Fin n)} {active repOf : ℕ → ℕ}
    {S : Set (Fin n)} {R : Finset ℕ}
    (h : ConcreteTracePartition G active S R repOf)
    {v : ℕ} (hvn : v < n) (hv : active v = 1) : repOf v < n := by
  let vf : Fin n := ⟨v, hvn⟩
  rw [← h.representative_val vf hv]
  exact (h.partition.representative vf).isLt

theorem ConcreteTracePartition.rep_active
    {n : ℕ} {G : SimpleGraph (Fin n)} {active repOf : ℕ → ℕ}
    {S : Set (Fin n)} {R : Finset ℕ}
    (h : ConcreteTracePartition G active S R repOf)
    {v : ℕ} (hvn : v < n) (hv : active v = 1) : active (repOf v) = 1 := by
  let vf : Fin n := ⟨v, hvn⟩
  have hr := h.partition.reps_mem
    (h.partition.representative_mem vf hv)
  change active (h.partition.representative vf).val = 1 at hr
  rwa [h.representative_val vf hv] at hr

theorem repClass_lt_of_active
    {n current : ℕ} {active label repClass reps outActive : ℕ → ℕ}
    {R : Finset ℕ}
    (h : RepData n current n active label repClass reps outActive R)
    {v : ℕ} (hvn : v < n) (hav : active v = 1)
    (hlabel : label v < current) :
    repClass (label v) < n := by
  have hle := h.table_le (label v) hlabel
  have hne : repClass (label v) ≠ n := by
    intro heq
    obtain ⟨r, hr, hl⟩ := h.covers v
      (mem_activeVertices.mpr ⟨hvn, hav⟩)
    exact (h.table_empty (label v) hlabel).mp heq r hr hl
  omega

/-- The total `Fin n` representative function encoded by `repOf`; inactive
vertices use themselves in the irrelevant branch. -/
def representativeFin {n current : ℕ}
    (active label repClass repOf reps outActive : ℕ → ℕ)
    (R : Finset ℕ)
    (hdata : RepData n current n active label repClass reps outActive R)
    (hlabels : ∀ v < n, active v = 1 → label v < current)
    (hmap : ∀ v < n, active v = 1 → repOf v = repClass (label v))
    (v : Fin n) : Fin n := by
  by_cases hav : active v.val = 1
  · exact ⟨repOf v.val, by
      rw [hmap v.val v.isLt hav]
      exact repClass_lt_of_active hdata v.isLt hav (hlabels _ v.isLt hav)⟩
  · exact v

@[simp] theorem representativeFin_val_of_active
    {n current : ℕ}
    {active label repClass repOf reps outActive : ℕ → ℕ}
    {R : Finset ℕ}
    (hdata : RepData n current n active label repClass reps outActive R)
    (hlabels : ∀ v < n, active v = 1 → label v < current)
    (hmap : ∀ v < n, active v = 1 → repOf v = repClass (label v))
    (v : Fin n) (hav : active v.val = 1) :
    (representativeFin active label repClass repOf reps outActive R
      hdata hlabels hmap v).val = repOf v.val := by
  simp [representativeFin, hav]

/-- Completed source arrays realize exactly the abstract trace partition used
by the paper proof. -/
noncomputable def tracePartition_of_repData
    {n current : ℕ} (G : SimpleGraph (Fin n))
    {S : Set (Fin n)}
    {active label repClass repOf reps outActive : ℕ → ℕ}
    {R : Finset ℕ}
    (hclass : Classifies G {v : Fin n | active v.val = 1} S
      (fun v => label v.val))
    (hlabels : ∀ v < n, active v = 1 → label v < current)
    (hdata : RepData n current n active label repClass reps outActive R)
    (hmap : ∀ v < n, active v = 1 → repOf v = repClass (label v)) :
    TracePartition G {v : Fin n | active v.val = 1} S (finSetAsSet R) := by
  let representative := representativeFin active label repClass repOf reps
    outActive R hdata hlabels hmap
  apply tracePartitionOfLabels G hclass representative
  · intro v hv
    have hlabelv := hlabels v.val v.isLt hv
    have hrepLt := repClass_lt_of_active hdata v.isLt hv hlabelv
    have hrepMem := (hdata.table_mem (label v.val) hlabelv hrepLt).1
    change (representative v).val ∈ R
    rw [show (representative v).val = repOf v.val by
      exact representativeFin_val_of_active hdata hlabels hmap v hv,
      hmap v.val v.isLt hv]
    exact hrepMem
  · intro v hv
    have hlabelv := hlabels v.val v.isLt hv
    have hrepLt := repClass_lt_of_active hdata v.isLt hv hlabelv
    have hrepLabel := (hdata.table_mem (label v.val) hlabelv hrepLt).2
    change label (representative v).val = label v.val
    rw [show (representative v).val = repOf v.val by
      exact representativeFin_val_of_active hdata hlabels hmap v hv,
      hmap v.val v.isLt hv]
    exact hrepLabel
  · intro r hr
    change active r.val = 1
    have hrProcessed := hdata.reps_processed hr
    exact (mem_activeVertices.mp hrProcessed).2
  · intro r hr s hs hrs
    apply Fin.ext
    exact hdata.labels_injective hr hs hrs

end

/-- Package the abstract trace partition together with the exact concrete
representative-array interpretation used by the source verifier. -/
noncomputable def concreteTracePartition_of_repData
    {n current : ℕ} (G : SimpleGraph (Fin n))
    {S : Set (Fin n)}
    {active label repClass repOf reps outActive : ℕ → ℕ}
    {R : Finset ℕ}
    (hclass : Classifies G {v : Fin n | active v.val = 1} S
      (fun v => label v.val))
    (hlabels : ∀ v < n, active v = 1 → label v < current)
    (hdata : RepData n current n active label repClass reps outActive R)
    (hmap : ∀ v < n, active v = 1 → repOf v = repClass (label v)) :
    ConcreteTracePartition G active S R repOf where
  partition := tracePartition_of_repData G hclass hlabels hdata hmap
  representative_val := by
    intro v hv
    exact representativeFin_val_of_active hdata hlabels hmap v hv

end Lax235315Proofs.Construction.PartitionResult
