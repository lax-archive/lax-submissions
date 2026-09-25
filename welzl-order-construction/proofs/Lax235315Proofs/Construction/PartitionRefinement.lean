import Lax235315Proofs.Construction.TracePartitions
import Mathlib.Tactic

/-!
Semantic invariant of the partition-refinement loops used by the RAM program.
-/

namespace Lax235315Proofs.Construction.PartitionRefinement

open Lax235315Proofs.Construction.NeighborhoodComplexity
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- A numeric labelling represents exactly equality of neighborhood traces on
the already processed test vertices. -/
def Classifies (V S : Set (Fin n)) (label : Fin n → ℕ) : Prop :=
  ∀ ⦃u⦄, u ∈ V → ∀ ⦃v⦄, v ∈ V →
    (label u = label v ↔ neighborhoodTrace G S u = neighborhoodTrace G S v)

theorem classifies_empty (V : Set (Fin n)) :
    Classifies G V ∅ (fun _ => 0) := by
  intro u hu v hv
  simp [neighborhoodTrace]

/-- The abstract effect of splitting every old class according to adjacency
to one new test vertex. -/
def refineLabel (label : Fin n → ℕ) (t : Fin n) (v : Fin n) : ℕ := by
  classical
  exact if G.Adj t v then 2 * label v + 1 else 2 * label v

theorem refineLabel_eq_iff {label : Fin n → ℕ} {t u v : Fin n} :
    refineLabel G label t u = refineLabel G label t v ↔
      label u = label v ∧ (G.Adj t u ↔ G.Adj t v) := by
  classical
  unfold refineLabel
  by_cases hu : G.Adj t u <;> by_cases hv : G.Adj t v <;>
    simp [hu, hv] <;> omega

theorem neighborhoodTrace_insert_eq_iff {S : Set (Fin n)} {t u v : Fin n} :
    neighborhoodTrace G (insert t S) u = neighborhoodTrace G (insert t S) v ↔
      neighborhoodTrace G S u = neighborhoodTrace G S v ∧
        (G.Adj t u ↔ G.Adj t v) := by
  constructor
  · intro h
    have hall := Set.ext_iff.mp h
    have ht' := hall t
    have ht : G.Adj t u ↔ G.Adj t v := by
      simpa [neighborhoodTrace, G.adj_comm] using ht'
    constructor
    · ext x
      have hx := hall x
      by_cases hxt : x = t
      · subst x
        simp [neighborhoodTrace, G.adj_comm, ht]
      · simpa [neighborhoodTrace, hxt] using hx
    · exact ht
  · rintro ⟨hS, ht⟩
    ext x
    have hx := Set.ext_iff.mp hS x
    by_cases hxt : x = t
    · subst x
      simp [neighborhoodTrace, G.adj_comm, ht]
    · simpa [neighborhoodTrace, hxt] using hx

theorem Classifies.refine {V S : Set (Fin n)} {label : Fin n → ℕ}
    (h : Classifies G V S label) (t : Fin n) :
    Classifies G V (insert t S) (refineLabel G label t) := by
  intro u hu v hv
  rw [refineLabel_eq_iff,
    neighborhoodTrace_insert_eq_iff]
  exact and_congr (h hu hv) Iff.rfl

/-- An implementation may allocate compact class numbers rather than the
literal numbers produced by `refineLabel`.  This relation records exactly
the equivalence relation that a correct compact refinement must realize. -/
def RefinesBy (V : Set (Fin n)) (label label' : Fin n → ℕ)
    (t : Fin n) : Prop :=
  ∀ ⦃u⦄, u ∈ V → ∀ ⦃v⦄, v ∈ V →
    (label' u = label' v ↔
      label u = label v ∧ (G.Adj t u ↔ G.Adj t v))

/-- Compact numeric refinement preserves the semantic trace invariant. -/
theorem Classifies.of_refinesBy {V S : Set (Fin n)}
    {label label' : Fin n → ℕ} {t : Fin n}
    (h : Classifies G V S label)
    (hrefine : RefinesBy G V label label' t) :
    Classifies G V (insert t S) label' := by
  intro u hu v hv
  rw [hrefine hu hv, neighborhoodTrace_insert_eq_iff]
  exact and_congr (h hu hv) Iff.rfl

/-- Any representative selected once per final numeric class yields the trace
partition required by the paper. -/
def tracePartitionOfLabels {V S R : Set (Fin n)} {label : Fin n → ℕ}
    (hclass : Classifies G V S label)
    (representative : Fin n → Fin n)
    (hrep : ∀ v ∈ V, representative v ∈ R)
    (hreplabel : ∀ v ∈ V, label (representative v) = label v)
    (hR : R ⊆ V)
    (hRunique : Set.InjOn label R) :
    TracePartition G V S R where
  representative := representative
  representative_mem := hrep
  same_trace := fun v hv => (hclass (hR (hrep v hv)) hv).mp (hreplabel v hv)
  reps_mem := hR
  reps_separated := by
    intro u hu v hv htrace
    apply hRunique hu hv
    exact (hclass (hR hu) (hR hv)).mpr htrace

end

end Lax235315Proofs.Construction.PartitionRefinement
