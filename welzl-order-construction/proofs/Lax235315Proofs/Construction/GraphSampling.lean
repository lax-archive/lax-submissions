import Lax235315Proofs.Construction.Sampling

/-!
The graph-specialized form of the sampling argument in Lemmas 3.7 and 3.8.
-/

namespace Lax235315Proofs.Construction.GraphSampling

open scoped symmDiff
open Finset
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax235315Proofs.Construction.NeighborhoodComplexity
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- The trace of one open neighborhood on a finite test set. -/
def traceFinset {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (Set.toFinite (neighborhoodTrace G (A : Set (Fin n)) v)).toFinset

@[simp] lemma coe_traceFinset (A : Finset (Fin n)) (v : Fin n) :
    (traceFinset G A v : Set (Fin n)) =
      neighborhoodTrace G (A : Set (Fin n)) v := by
  simp [traceFinset]

lemma traceFinset_subset (A : Finset (Fin n)) (v : Fin n) :
    traceFinset G A v ⊆ A := by
  intro u hu
  have hu' : u ∈ neighborhoodTrace G (A : Set (Fin n)) v := by
    simpa [traceFinset] using hu
  exact hu'.2

/-- The distinct traces made by vertices in `B` on `A`. -/
def traceFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  B.image (traceFinset G A)

lemma coe_traceFamily (A B : Finset (Fin n)) :
    (traceFamily G A B : Set (Finset (Fin n))) =
      traceFinset G A '' (B : Set (Fin n)) := by
  ext X
  simp [traceFamily]

/-- Linear neighborhood complexity bounds the number of distinct finite
traces made by any selected family of vertices. -/
lemma traceFamily_card_le_mul {c : ℕ} {A B : Finset (Fin n)}
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (hA : A.Nonempty) :
    (traceFamily G A B).card ≤ c * A.card := by
  have hinj : Set.InjOn
      (fun X : Finset (Fin n) => (X : Set (Fin n)))
      (traceFinset G A '' (B : Set (Fin n))) := by
    intro X hX Y hY hXY
    exact Finset.coe_injective hXY
  have himage :
      (fun X : Finset (Fin n) => (X : Set (Fin n))) ''
          (traceFinset G A '' (B : Set (Fin n))) =
        neighborhoodTrace G (A : Set (Fin n)) '' (B : Set (Fin n)) := by
    ext X
    constructor
    · rintro ⟨T, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, (coe_traceFinset G A v).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨traceFinset G A v, ⟨v, hv, rfl⟩,
        coe_traceFinset G A v⟩
  calc
    (traceFamily G A B).card =
        (traceFinset G A '' (B : Set (Fin n))).ncard := by
      rw [← coe_traceFamily G A B]
      simp
    _ = (neighborhoodTrace G (A : Set (Fin n)) ''
          (B : Set (Fin n))).ncard := by
      rw [← himage, hinj.ncard_image]
    _ ≤ traceCount G (A : Set (Fin n)) :=
      ncard_image_neighborhoodTrace_le_traceCount G _ _
    _ ≤ c * (A : Set (Fin n)).ncard :=
      traceCount_le_mul_ncard hG (by simpa using hA)
    _ = c * A.card := by simp

/-- The set symmetric difference used by the paper agrees with the explicit
finite symmetric difference used in the counting proof. -/
lemma card_finSymmDiff_trace (A : Finset (Fin n)) (u v : Fin n) :
    (finSymmDiff (traceFinset G A u) (traceFinset G A v)).card =
      ((G.neighborSet u ∩ (A : Set (Fin n))) ∆
        (G.neighborSet v ∩ (A : Set (Fin n)))).ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [finSymmDiff, traceFinset, neighborhoodTrace, Set.mem_symmDiff]

/-- A trace partition on `W` cannot distinguish its vertex from its
representative on `W`; hence the sample misses their full traces' symmetric
difference on `A`. -/
lemma sample_disjoint_trace_symmDiff {A B W B' : Finset (Fin n)}
    (hWsub : W ⊆ A)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    {b : Fin n} (hb : b ∈ B) :
    Disjoint W
      (finSymmDiff (traceFinset G A b)
        (traceFinset G A (hB.representative b))) := by
  rw [Finset.disjoint_left]
  intro w hw hwdiff
  have hsame := Set.ext_iff.mp (hB.same_trace b (by simpa using hb)) w
  have hwA : w ∈ A := hWsub hw
  have hwW : w ∈ (W : Set (Fin n)) := by simpa using hw
  simp only [neighborhoodTrace, Set.mem_inter_iff, SimpleGraph.mem_neighborSet,
    hwW, and_true] at hsame
  have hdiffset : w ∈
      ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
        (G.neighborSet (hB.representative b) ∩
          (A : Set (Fin n)))) := by
    simpa [finSymmDiff, traceFinset, neighborhoodTrace,
      Set.mem_symmDiff] using hwdiff
  rcases hdiffset with h | h
  · exact h.2 ⟨hsame.mpr h.1.1, by simpa using hwA⟩
  · exact h.2 ⟨hsame.mp h.1.1, by simpa using hwA⟩

/-- If the near-partition verification in Figure 1 fails, its sample lies in
the finite bad-sample family from Lemma 3.8. -/
lemma failed_near_check_mem_familyBadSamples
    {A B W B' : Finset (Fin n)} {c L : ℕ}
    (hWsub : W ⊆ A)
    (hWcard : W.card = sampleSize A.card c)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    {b : Fin n} (hb : b ∈ B)
    (hfar : 6 * c ^ 2 * L <
      ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
        (G.neighborSet (hB.representative b) ∩
          (A : Set (Fin n)))).ncard) :
    W ∈ familyBadSamples (traceFamily G A B) id A c L := by
  let X := traceFinset G A b
  let Y := traceFinset G A (hB.representative b)
  have hX : X ∈ traceFamily G A B := by
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hrepB : hB.representative b ∈ B := by
    apply hB.reps_mem
    exact hB.representative_mem b (by simpa using hb)
  have hY : Y ∈ traceFamily G A B := by
    exact Finset.mem_image.mpr ⟨hB.representative b, hrepB, rfl⟩
  have hlarge : 6 * c ^ 2 * L ≤ (finSymmDiff X Y).card := by
    rw [card_finSymmDiff_trace G A b (hB.representative b)]
    omega
  have hsample : W ∈ samples A (sampleSize A.card c) := by
    simp [samples, hWsub, hWcard]
  have hmiss : W ∈ misses A (finSymmDiff X Y)
      (sampleSize A.card c) := by
    simp only [misses, Finset.mem_filter]
    exact ⟨hsample, sample_disjoint_trace_symmDiff G hWsub hB hb⟩
  unfold familyBadSamples
  apply Finset.mem_biUnion.mpr
  refine ⟨(X, Y), Finset.mem_product.mpr ⟨hX, hY⟩, ?_⟩
  change W ∈ pairBadSamples A X Y c L
  rw [pairBadSamples, if_pos hlarge]
  exact hmiss

/-- **Lemma 3.8 (graph form).** Under linear neighborhood complexity, the
fraction of samples which can make the near-partition check fail is at most
`c²/N`. -/
lemma graph_bad_fraction_le {c N L : ℕ} {A B : Finset (Fin n)}
    (hc : 1 ≤ c) (hA : A.Nonempty)
    (hG : HasLinearNeighborhoodComplexityWithConstant G c)
    (hAN : A.card ≤ N) (hNpow : N ≤ 2 ^ L) :
    ((familyBadSamples (traceFamily G A B) id A c L).card : ℝ) /
        (samples A (sampleSize A.card c)).card ≤
      (c : ℝ) ^ 2 / N := by
  apply family_bad_fraction_le_csq_div hc hA
  · intro X hX
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hX
    exact traceFinset_subset G A v
  · exact traceFamily_card_le_mul G hG hA
  · exact hAN
  · exact hNpow

end

end Lax235315Proofs.Construction.GraphSampling
