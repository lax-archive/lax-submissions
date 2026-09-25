import Lax235315.NearTwinReplacement
import Lax235315.UniformSampleAvoidance
import Lax235315.RandomKeyCollisions
import Lax235315Proofs.Construction.Crossing
import Lax235315Proofs.Construction.Sampling
import Lax235315Proofs.Construction.FiniteRandomKeys

namespace Lax235315Proofs.ComponentProofs
open scoped symmDiff
open Lax195003.WelzlOrders

/--
---
conclusion: Lax235315.NearTwinReplacement.crossingNumber_le_add_two_mul
---
Near-twin replacement satisfies the exact registered crossing-number definition.

# Proof strategy

For each set, new crossings must have an endpoint in the symmetric difference.
The successor map bounds the number charged to second endpoints. Apply the
result to a representative of each set and take the finite supremum.

# Attribution

Lemma 2.2 of Dreier--Kuske, arXiv:2602.14625v1. The component proof is ported
from the existing local Welzl development at commit 44a44623.
-/
theorem nearTwinReplacement {n k m : ℕ}
    {F R : SetSystem (Fin n)} {π : Equiv.Perm (Fin n)}
    (hrep : ∀ X ∈ F, ∃ Y ∈ R, (X ∆ Y).ncard ≤ k)
    (hπ : crossingNumber R π ≤ m) :
    crossingNumber F π ≤ m + 2 * k :=
  Construction.Crossing.crossingNumber_le_add_two_mul hrep hπ

/--
---
conclusion: Lax235315.UniformSampleAvoidance.miss_fraction_le
---
The fixed-size sample avoidance estimate holds as a finite counting inequality.

# Proof strategy

Count avoiding samples by a binomial coefficient, bound its ratio to all
samples by an exponential, and use the ceiling sampling rate and N≤2^L.

# Attribution

Lemma 3.7 of Dreier--Kuske, arXiv:2602.14625v1, through the component proof
ported from the existing local development at commit 44a44623.
-/
theorem uniformSampleAvoidance {n : ℕ} {A X : Finset (Fin n)} {c N L : ℕ}
    (hc : 1 ≤ c) (hA : A.Nonempty) (hX : X ⊆ A)
    (hXcard : 6 * c ^ 2 * L ≤ X.card)
    (hAN : A.card ≤ N) (hNpow : N ≤ 2 ^ L) :
    let s := (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)
    (((A.powersetCard s).filter (fun W => Disjoint W X)).card : ℝ) /
      (A.powersetCard s).card ≤ 1 / (N : ℝ) ^ 3 := by
  simpa only [Construction.Sampling.misses, Construction.Sampling.samples,
    Construction.TracePartitions.sampleSize] using
      Construction.Sampling.uniform_sample_miss_fraction_le hc hA hX hXcard hAN hNpow

/--
---
conclusion: Lax235315.RandomKeyCollisions.count_noninjective_le
---
The noninjective key assignments satisfy the stated finite collision bound.

# Proof strategy

Identify noninjectivity with the union of equality events over distinct
coordinate pairs. Fixing equality removes one independent key choice; the
finite union bound then gives the result.

# Attribution

The elementary collision estimate is used to implement the paper's ideal
sampler with finite random keys. The component proof is ported from the local
Welzl development at commit 44a44623.
-/
theorem randomKeyCollisions (a M : ℕ) :
    {f : Fin a → Fin M | ¬ Function.Injective f}.ncard ≤
      a ^ 2 * M ^ (a - 1) := by
  classical
  have heq : {f : Fin a → Fin M | ¬ Function.Injective f} =
      (Construction.FiniteRandomKeys.collisions (Fin a) M : Set (Fin a → Fin M)) := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.mem_coe,
      Construction.FiniteRandomKeys.collisions, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      Construction.FiniteRandomKeys.pairCollisions,
      Construction.FiniteRandomKeys.allAssignments]
    simp only [Function.Injective]
    aesop
  rw [heq, Set.ncard_coe_finset]
  simpa using Construction.FiniteRandomKeys.card_collisions_le (Fin a) M

end Lax235315Proofs.ComponentProofs
