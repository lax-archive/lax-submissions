import Lax235315Proofs.Construction.NeighborhoodComplexity
import Lax235315Proofs.Construction.Reconstruction
import Mathlib.Tactic.Ring

/-!
The two trace partitions formed in every reduction round of the paper.
-/

namespace Lax235315Proofs.Construction.TracePartitions

open scoped symmDiff
open Lax235315Proofs.Construction.NeighborhoodComplexity
open Lax235315Proofs.Construction.ListCrossing
open Lax235315Proofs.Construction.Reconstruction

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- The vertices of `V` having the same trace on `S` as `v`. -/
def traceClass (V S : Set (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun u =>
    u ∈ V ∧ neighborhoodTrace G S u = neighborhoodTrace G S v

lemma traceClass_nonempty {V S : Set (Fin n)} {v : Fin n} (hv : v ∈ V) :
    (traceClass G V S v).Nonempty := by
  exact ⟨v, by simp [traceClass, hv]⟩

/-- The least vertex in `v`'s trace class, with the irrelevant value `v`
outside `V`. This is also a directly implementable tie-breaking rule. -/
def canonicalRepresentative (V S : Set (Fin n)) (v : Fin n) : Fin n := by
  classical
  exact if h : v ∈ V then
      (traceClass G V S v).min' (traceClass_nonempty G h)
    else v

lemma canonicalRepresentative_mem {V S : Set (Fin n)} {v : Fin n}
    (hv : v ∈ V) : canonicalRepresentative G V S v ∈ V := by
  classical
  rw [canonicalRepresentative, dif_pos hv]
  have := Finset.min'_mem (traceClass G V S v) (traceClass_nonempty G hv)
  exact (Finset.mem_filter.mp this).2.1

lemma canonicalRepresentative_same_trace {V S : Set (Fin n)} {v : Fin n}
    (hv : v ∈ V) :
    neighborhoodTrace G S (canonicalRepresentative G V S v) =
      neighborhoodTrace G S v := by
  classical
  rw [canonicalRepresentative, dif_pos hv]
  have := Finset.min'_mem (traceClass G V S v) (traceClass_nonempty G hv)
  exact (Finset.mem_filter.mp this).2.2

/-- The set of canonical representatives of traces made by `V` on `S`. -/
def canonicalRepresentatives (V S : Set (Fin n)) : Set (Fin n) :=
  canonicalRepresentative G V S '' V

/-- `R` contains one representative of every trace induced by vertices in
`V` on the test set `S`. -/
structure TracePartition (V S R : Set (Fin n)) where
  representative : Fin n → Fin n
  representative_mem : ∀ v ∈ V, representative v ∈ R
  same_trace : ∀ v ∈ V,
    neighborhoodTrace G S (representative v) = neighborhoodTrace G S v
  reps_mem : R ⊆ V
  reps_separated : Set.InjOn (neighborhoodTrace G S) R

/-- Every finite trace quotient has a canonical trace partition. -/
def canonicalTracePartition (V S : Set (Fin n)) :
    TracePartition G V S (canonicalRepresentatives G V S) where
  representative := canonicalRepresentative G V S
  representative_mem := fun v hv => ⟨v, hv, rfl⟩
  same_trace := fun v hv => canonicalRepresentative_same_trace G hv
  reps_mem := by
    rintro r ⟨v, hv, rfl⟩
    exact canonicalRepresentative_mem G hv
  reps_separated := by
    classical
    intro u hu v hv heq
    obtain ⟨u', hu'V, rfl⟩ := hu
    obtain ⟨v', hv'V, rfl⟩ := hv
    have huv : neighborhoodTrace G S u' = neighborhoodTrace G S v' := by
      rw [← canonicalRepresentative_same_trace G hu'V,
        ← canonicalRepresentative_same_trace G hv'V]
      exact heq
    simp only [canonicalRepresentative, dif_pos hu'V, dif_pos hv'V]
    have hvmin_mem_u :
        (traceClass G V S v').min' (traceClass_nonempty G hv'V) ∈
          traceClass G V S u' := by
      have hm := Finset.min'_mem (traceClass G V S v')
        (traceClass_nonempty G hv'V)
      simp only [traceClass, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      exact ⟨hm.1, hm.2.trans huv.symm⟩
    have humin_mem_v :
        (traceClass G V S u').min' (traceClass_nonempty G hu'V) ∈
          traceClass G V S v' := by
      have hm := Finset.min'_mem (traceClass G V S u')
        (traceClass_nonempty G hu'V)
      simp only [traceClass, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      exact ⟨hm.1, hm.2.trans huv⟩
    apply le_antisymm
    · apply Finset.min'_le
      exact hvmin_mem_u
    · apply Finset.min'_le
      exact humin_mem_v

/-- A representative set has at most as many elements as there are
neighborhood traces on its test set. -/
lemma TracePartition.ncard_le_traceCount {V S R : Set (Fin n)}
    (h : TracePartition G V S R) :
    R.ncard ≤ Lax195003.WelzlOrdersNeighborhoodComplexity.traceCount G S :=
  ncard_le_traceCount_of_injOn G S R h.reps_separated

/-- Under linear neighborhood complexity, a trace partition on a nonempty
test set has at most `c |S|` representatives. -/
lemma TracePartition.ncard_le_mul {c : ℕ} {V S R : Set (Fin n)}
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant
      G c)
    (h : TracePartition G V S R) (hS : S.Nonempty) :
    R.ncard ≤ c * S.ncard :=
  ncard_le_mul_of_injOn hG hS h.reps_separated

lemma TracePartition.reps_nonempty {V S R : Set (Fin n)}
    (h : TracePartition G V S R) (hV : V.Nonempty) : R.Nonempty := by
  obtain ⟨v, hv⟩ := hV
  exact ⟨h.representative v, h.representative_mem v hv⟩

/-- The sample size used in Figure 1, written with natural-number ceiling
division. -/
def sampleSize (a c : ℕ) : ℕ :=
  (a + 2 * c ^ 2 - 1) / (2 * c ^ 2)

lemma sampleSize_le_div_add_one {a c : ℕ} (hc : 1 ≤ c) :
    sampleSize a c ≤ a / (2 * c ^ 2) + 1 := by
  unfold sampleSize
  have hd : 0 < 2 * c ^ 2 :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  calc
    (a + 2 * c ^ 2 - 1) / (2 * c ^ 2) ≤
        (a + 2 * c ^ 2) / (2 * c ^ 2) :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    _ = a / (2 * c ^ 2) + 1 := Nat.add_div_right a hd

lemma sq_mul_sampleSize_le {a c : ℕ} (hc : 1 ≤ c) :
    c ^ 2 * sampleSize a c ≤ a / 2 + c ^ 2 := by
  have hd : 0 < 2 * c ^ 2 :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hdiv : c ^ 2 * (a / (2 * c ^ 2)) ≤ a / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    calc
      (c ^ 2 * (a / (2 * c ^ 2))) * 2 =
          a / (2 * c ^ 2) * (2 * c ^ 2) := by ring
      _ ≤ a := Nat.div_mul_le_self _ _
  calc
    c ^ 2 * sampleSize a c ≤
        c ^ 2 * (a / (2 * c ^ 2) + 1) :=
      Nat.mul_le_mul_left _ (sampleSize_le_div_add_one hc)
    _ = c ^ 2 * (a / (2 * c ^ 2)) + c ^ 2 := by ring
    _ ≤ a / 2 + c ^ 2 := Nat.add_le_add_right hdiv _

/-- The two quotient steps shrink the active ground side to at most
`c² |W|`. -/
lemma partitions_ground_ncard_le {c : ℕ} {A B W A' B' : Set (Fin n)}
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant
      G c)
    (hB : TracePartition G B W B')
    (hA : TracePartition G A B' A')
    (hW : W.Nonempty) (hBne : B.Nonempty) :
    A'.ncard ≤ c ^ 2 * W.ncard := by
  have hB'ne := hB.reps_nonempty G hBne
  have hBc : B'.ncard ≤ c * W.ncard := hB.ncard_le_mul G hG hW
  have hAc : A'.ncard ≤ c * B'.ncard := hA.ncard_le_mul G hG hB'ne
  calc
    A'.ncard ≤ c * B'.ncard := hAc
    _ ≤ c * (c * W.ncard) := Nat.mul_le_mul_left c hBc
    _ = c ^ 2 * W.ncard := by ring

/-- With the prescribed sample cardinality, the paper's one-step recurrence
is `|A'| ≤ |A|/2 + c²`. -/
lemma partitions_ground_ncard_le_half_add {c : ℕ}
    {A B W A' B' : Set (Fin n)}
    (hc : 1 ≤ c)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant
      G c)
    (hB : TracePartition G B W B')
    (hA : TracePartition G A B' A')
    (hW : W.Nonempty) (hBne : B.Nonempty)
    (hWcard : W.ncard = sampleSize A.ncard c) :
    A'.ncard ≤ A.ncard / 2 + c ^ 2 := by
  calc
    A'.ncard ≤ c ^ 2 * W.ncard :=
      partitions_ground_ncard_le G hG hB hA hW hBne
    _ = c ^ 2 * sampleSize A.ncard c := by rw [hWcard]
    _ ≤ A.ncard / 2 + c ^ 2 := sq_mul_sampleSize_le hc

private lemma same_trace_adj {V S R : Set (Fin n)}
    (h : TracePartition G V S R) {v : Fin n} (hv : v ∈ V)
    {s : Fin n} (hs : s ∈ S) :
    G.Adj s (h.representative v) ↔ G.Adj s v := by
  have heq := Set.ext_iff.mp (h.same_trace v hv) s
  simpa [neighborhoodTrace, hs, G.adj_comm] using heq

/-- Restoring every nonrepresentative immediately after its representative
produces an enumeration of `V` by genuine twin insertions over `S`. -/
lemma TracePartition.exists_twinExpansion {V S R : Set (Fin n)}
    (h : TracePartition G V S R) {small : List (Fin n)}
    (hsmall : Enumerates R small) :
    ∃ big, Enumerates V big ∧ TwinExpansion G S small big := by
  classical
  let D : Finset (Fin n) := (V \ R).toFinset
  have hbuild : ∀ E : Finset (Fin n), E ⊆ D →
      ∃ current,
        Enumerates (R ∪ (E : Set (Fin n))) current ∧
          TwinExpansion G S small current := by
    intro E hED
    induction E using Finset.induction_on with
    | empty =>
        refine ⟨small, ?_, TwinExpansion.refl small⟩
        simpa using hsmall
    | @insert x E hxE ih =>
        have hED' : E ⊆ D := fun z hz => hED (Finset.mem_insert_of_mem hz)
        obtain ⟨current, hcurrent, hexpand⟩ := ih hED'
        have hxD : x ∈ D := hED (Finset.mem_insert_self x E)
        have hxVR : x ∈ V \ R := by simpa [D] using hxD
        have hrepR : h.representative x ∈ R := h.representative_mem x hxVR.1
        have hrepCurrent : h.representative x ∈ current :=
          (hcurrent.2 _).mpr (Set.mem_union_left _ hrepR)
        have hxCurrent : x ∉ current := by
          intro hxc
          have hxUnion := (hcurrent.2 x).mp hxc
          rcases hxUnion with hxR | hxEset
          · exact hxVR.2 hxR
          · exact hxE (by simpa using hxEset)
        let next := insertAfter (h.representative x) x current
        have hnextEnum :
            Enumerates (R ∪ ((insert x E : Finset (Fin n)) : Set (Fin n))) next := by
          constructor
          · exact nodup_insertAfter hcurrent.1 hrepCurrent hxCurrent
          · intro z
            rw [mem_insertAfter_iff hrepCurrent]
            simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
              Finset.mem_coe]
            rw [hcurrent.2]
            aesop
        refine ⟨next, hnextEnum, ?_⟩
        exact TwinExpansion.insert hexpand hrepCurrent hxCurrent
          (fun s hs => same_trace_adj G h hxVR.1 hs)
  obtain ⟨big, hbig, hexpand⟩ := hbuild D (Finset.Subset.refl D)
  refine ⟨big, ?_, hexpand⟩
  have hset : R ∪ ((D : Finset (Fin n)) : Set (Fin n)) = V := by
    ext v
    simp only [D, Set.mem_union, Finset.mem_coe, Set.mem_toFinset,
      Set.mem_diff]
    constructor
    · rintro (hvR | ⟨hvV, -⟩)
      · exact h.reps_mem hvR
      · exact hvV
    · intro hvV
      by_cases hvR : v ∈ R
      · exact Or.inl hvR
      · exact Or.inr ⟨hvV, hvR⟩
  rwa [hset] at hbig

/-- The two trace partitions and the checked near-twin condition constitute
one reconstruction reduction. -/
lemma exists_reduction_of_partitions {k : ℕ}
    {A B W A' B' : Set (Fin n)} {small : List (Fin n)}
    (hB : TracePartition G B W B')
    (hA : TracePartition G A B' A')
    (hnear : ∀ b ∈ B,
      ((G.neighborSet b ∩ A) ∆
        (G.neighborSet (hB.representative b) ∩ A)).ncard ≤ k)
    (hsmall : Enumerates A' small) :
    ∃ big, Nonempty (Reduction G k A B A' B' small big) := by
  obtain ⟨big, hbig, hexpand⟩ := hA.exists_twinExpansion G hsmall
  exact ⟨big, ⟨{
    small_enumerates := hsmall
    big_enumerates := hbig
    expands := hexpand
    representative := hB.representative
    representative_mem := hB.representative_mem
    near := hnear
  }⟩⟩

end

end Lax235315Proofs.Construction.TracePartitions
