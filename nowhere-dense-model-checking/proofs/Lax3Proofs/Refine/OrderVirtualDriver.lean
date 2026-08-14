import Lax3Proofs.Refine.OrderVirtualBaseProvider

/-!
# End-to-end virtual elimination

This file composes regenerated degree initialization, the first compact
bucket rebuild, and the complete amortised elimination loop.  It is the
single entry point used for the input graph and for every later implicit
graph provider.
-/

namespace Lax3Proofs.Refine.OrderVirtualDriver

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualInit
open Lax3Proofs.Refine.OrderVirtualBucket
open Lax3Proofs.Refine.OrderVirtualReady
open Lax3Proofs.Refine.OrderVirtualLoop
open Lax3Proofs.Refine.OrderVirtualPotential
open Lax3Proofs.Refine.OrderVirtualBaseProvider

/-- Degree initialization, compact bucket construction, and greedy
elimination, with no materialized edge set between the three stages. -/
def virtualElim (provide : Com) : Com :=
  .seq (virtualInitDeg provide)
    (.seq rebuildBuckets (virtualElimLoop provide))

/-- Exact compositional charge of `virtualElim`. -/
noncomputable def virtualElimCost {n : ℕ} (G : SimpleGraph (Fin n))
    (kappa : ℕ → ℕ) : ℕ :=
  ((∑ k ∈ Finset.range n, (kappa k + 13)) + 6) +
    (rebuildBucketsCost n + (virtualPotCap G kappa + 10))

/-- A verified row provider yields a complete greedy ordering using only the
fixed carrier-linear engine arrays. -/
theorem virtualElim_spec {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {kappa : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide kappa)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B) :
    Spec B
      (fun sigma => P sigma ∧
        ∃ E D R ID BH BV BN,
          EngineArrays n (bucketExtra n) E D R ID BH BV BN sigma ∧
          ∀ u < n, E u = 0)
      (virtualElim provide)
      (fun _ sigma' => VirtualElimResult G sigma')
      (virtualElimCost G kappa) := by
  have hBW : n + bucketExtra n + 1 < B := by
    simpa only [bucket_arena_length] using hB
  intro sigma hpre
  obtain ⟨sigma1, r1, hdeg, hi⟩ :=
    (virtualInitDeg_spec hp hclosed hBW).run hpre
  obtain ⟨sigma2, r2, hready⟩ :=
    (rebuild_after_virtual_deg hrunClosed hB).run ⟨hdeg, hi⟩
  obtain ⟨sigma3, r3, hresult⟩ :=
    (virtualElimLoop_spec hp hclosed hrunClosed hB).run hready
  refine ⟨sigma3, ?_, hresult⟩
  simpa only [virtualElim, virtualElimCost] using r1.seq (r2.seq r3)

/-- The input CSR is the executable base case of the virtual campaign. -/
theorem baseVirtualElim_spec {B n ns nt : ℕ} {G : SimpleGraph (Fin n)}
    {o t : String} {O T : ℕ → ℕ}
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T) (hnsnt : ns ≤ nt)
    (hB : 3 * n + 3 < B) (hnsB : ns < B)
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames) :
    Spec B
      (fun sigma => BaseCsrMem n nt o t O T sigma ∧
        ∃ E D R ID BH BV BN,
          EngineArrays n (bucketExtra n) E D R ID BH BV BN sigma ∧
          ∀ u < n, E u = 0)
      (virtualElim (baseProvide o t))
      (fun _ sigma' => VirtualElimResult G sigma')
      (virtualElimCost G (baseProvideCost O)) := by
  have hBW : n + bucketExtra n + 1 < B := by
    simpa only [bucket_arena_length] using hB
  apply virtualElim_spec
  · exact baseProvidesRows hcsr hnsnt hBW hnsB ho ht
  · exact baseCsrMem_engineClosed ho ht
  · exact baseCsrMem_engineRunClosed ho ht
  · exact hB

/-! ## Axiom audit -/

#print axioms virtualElim_spec
#print axioms baseVirtualElim_spec

end Lax3Proofs.Refine.OrderVirtualDriver
