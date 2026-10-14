import Lax457868Proofs.ContractionRounds
import Lax457868Proofs.GraphTraceBounds
import Lax457868Proofs.SamplerContract

set_option autoImplicit false

/-!
The finite trace contraction preserves the refined sample's near-twin
guarantee and the dual incidence labels. The size bound is then obtained
from graph neighborhood complexity, including the empty-trace cases.
-/

namespace Lax457868Proofs.RefinedContraction

open Lax457868Proofs.ContractionRounds
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.GraphTraceBounds
open Lax457868Proofs.SamplerContract
open Lax457868Proofs.RefinedSampleSpec
open Lax195003.WelzlOrdersNeighborhoodComplexity

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A representative has the same sample trace, hence the refined-sample
contract bounds its full neighborhood disagreement. -/
lemma representative_near_twin
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (W : Finset α) (m k : ℕ)
    (hsample : IsRefinedSample (neighborhoodFamily B N)
      (A : Set α) (W : Set α) m k)
    (contraction : TraceContraction A B N W)
    (b : β) (hb : b ∈ B) :
    contraction.bChoice.representative b ∈ contraction.retainedB ∧
      ((N b \ N (contraction.bChoice.representative b)) ∪
        (N (contraction.bChoice.representative b) \ N b)).card ≤ k := by
  classical
  let rb := contraction.bChoice.representative b
  have hrbB : rb ∈ B := contraction.bChoice.representative_mem b hb
  have hrbR : rb ∈ contraction.retainedB :=
    Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hbF : (N b : Set α) ∈ neighborhoodFamily B N := ⟨b, hb, rfl⟩
  have hrbF : (N rb : Set α) ∈ neighborhoodFamily B N :=
    ⟨rb, hrbB, rfl⟩
  have htrace : (N b : Set α) ∩ (W : Set α) =
      (N rb : Set α) ∩ (W : Set α) := by
    exact_mod_cast (contraction.bChoice.representative_label b hb).symm
  rcases hsample with ⟨_, _, _, _, hnear⟩
  have hset :
      (((N b : Set α) \ (N rb : Set α)) ∪
        ((N rb : Set α) \ (N b : Set α))) =
      (↑((N b \ N rb) ∪ (N rb \ N b)) : Set α) := by
    ext a
    simp
  have hbound := hnear (N b : Set α) hbF (N rb : Set α) hrbF htrace
  rw [hset, Set.ncard_coe_finset] at hbound
  exact ⟨hrbR, hbound⟩

/-- The retained ground representative has exactly the same incidences
against all retained neighborhood representatives. -/
lemma representative_incidence
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (W : Finset α) (contraction : TraceContraction A B N W)
    (a : α) (ha : a ∈ A) (b : β) (hb : b ∈ contraction.retainedB) :
    contraction.aChoice.representative a ∈ contraction.retainedA ∧
      (a ∈ N b ↔ contraction.aChoice.representative a ∈ N b) := by
  classical
  have hra : contraction.aChoice.representative a ∈ contraction.retainedA :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hlabel := contraction.aChoice.representative_label a ha
  have hbmem := congrArg (fun S : Finset β => b ∈ S) hlabel
  change (b ∈ contraction.retainedB.filter
    (fun b => contraction.aChoice.representative a ∈ N b)) =
    (b ∈ contraction.retainedB.filter (fun b => a ∈ N b)) at hbmem
  simp only [Finset.mem_filter, hb, true_and] at hbmem
  exact ⟨hra, Iff.of_eq hbmem.symm⟩

/-- In a graph instance the sampler's public contract gives every retained
neighborhood representative a k-close original neighborhood. -/
lemma graph_representative_near_twin {n c k : ℕ}
    (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (hsample : IsRefinedSample
      (neighborhoodFamily B (finiteNeighborhood G A))
      (A : Set (Fin n)) (W : Set (Fin n))
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (b : Fin n) (hb : b ∈ B) :
    contraction.bChoice.representative b ∈ contraction.retainedB ∧
      ((finiteNeighborhood G A b \
          finiteNeighborhood G A (contraction.bChoice.representative b)) ∪
        (finiteNeighborhood G A (contraction.bChoice.representative b) \
          finiteNeighborhood G A b)).card ≤ k :=
  representative_near_twin A B (finiteNeighborhood G A) W _ k
    hsample contraction b hb

/-- The graph contraction's ground representatives preserve incidence with
each retained neighborhood vertex. -/
lemma graph_representative_incidence {n : ℕ}
    (G : SimpleGraph (Fin n)) (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (a : Fin n) (ha : a ∈ A)
    (b : Fin n) (hb : b ∈ contraction.retainedB) :
    contraction.aChoice.representative a ∈ contraction.retainedA ∧
      (a ∈ finiteNeighborhood G A b ↔
        contraction.aChoice.representative a ∈ finiteNeighborhood G A b) :=
  representative_incidence A B (finiteNeighborhood G A) W
    contraction a ha b hb

/-- Graph linearity supplies both trace estimates required by the actual
finite contraction, while the sampler contract supplies its size budget. -/
lemma graph_traceContraction_size_bound {n c k : ℕ}
    {G : SimpleGraph (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    (A B W : Finset (Fin n))
    (hsample : IsRefinedSample
      (neighborhoodFamily B (finiteNeighborhood G A))
      (A : Set (Fin n)) (W : Set (Fin n))
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (contraction : TraceContraction A B (finiteNeighborhood G A) W) :
    2 * contraction.retainedA.card ≤ A.card + 2 * c ^ 2 := by
  classical
  rcases hsample with ⟨_, _, hWA, hWsize, _⟩
  have hWsubset : W ⊆ A := by
    intro a ha
    exact hWA ha
  have hWcard : W.card ≤ (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2) := by
    simpa only [Set.ncard_coe_finset] using hWsize
  apply traceContraction_size_bound A B (finiteNeighborhood G A) W c
    (by omega) hWsubset hWcard
  · intro X hXA hX
    change (traceClasses (finiteNeighborhood G A) X B).card ≤ c * X.card
    exact traceClasses_finiteNeighborhood_bound hG A B X hXA hX
  · intro Y _ hY
    change
      (A.image (fun a => Y.filter
        (fun b => a ∈ finiteNeighborhood G A b))).card ≤ c * Y.card
    exact finiteNeighborhood_dual_trace_bound hG A Y hY

end Lax457868Proofs.RefinedContraction
