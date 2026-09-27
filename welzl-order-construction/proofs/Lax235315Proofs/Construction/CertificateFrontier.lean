import Lax235315Proofs.Construction.AcceptedCommit
import Lax235315Proofs.Construction.RoundSamplePartitionSource

/-! Bridge from the literal two-partition certificate builder to the
shrinking frontier needed by the accepted-round commit. -/

namespace Lax235315Proofs.Construction.CertificateFrontier
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.BitArrays
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.AcceptedCommit
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.PartitionCompleteSource
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.RoundPartitionSource
open Lax235315Proofs.Construction.RoundSamplePartitionSource
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.Reconstruction
open scoped symmDiff

lemma prefix_card {k : ℕ} {f : ℕ → ℕ} {S : Finset ℕ}
    (h : PrefixEnumerates k f S) : S.card = k := by
  have he : (Stack.toList k f).toFinset = S := by
    ext v; simpa using h.2 v
  rw [← he, List.toFinset_card_of_nodup h.1]
  simp

/-- All mathematical and storage conditions needed by the actual commit. -/
structure Candidate (B c n : ℕ) (x : List ℕ) (σ : Env) : Prop where
  frontier : Frontier B c n x σ
  nextCount : σ.vars "nextACount" = (activeVertices n (view σ "nextA")).card
  subset : activeVertices n (view σ "nextA") ⊆ activeVertices n (view σ "activeA")
  nonemptyA : (activeVertices n (view σ "nextA")).Nonempty
  nonemptyB : (activeVertices n (view σ "nextB")).Nonempty
  shrinks : (activeVertices n (view σ "nextA")).card ≤ σ.vars "acount" / 2 + c ^ 2

lemma Candidate.commit {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Candidate B c n x σ) (hc : 1 ≤ c) (hn : 1 < n) (hnB : n < B)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount") :
    ∃ σ', Run B commitReduction σ σ' (80 * (n + 1)) ∧
      Frontier B c n x σ' ∧ σ'.vars "round" = σ.vars "round" + 1 ∧
      σ'.vars "acount" = σ.vars "nextACount" :=
  frontier_commit_run h.frontier hc hn hnB hlarge h.nextCount h.subset
    h.nonemptyA h.nonemptyB h.shrinks

/-- The accepted certificate data produced by the literal builder, alongside
the shrinking frontier used by the commit.  The arrays are exposed as exact
`arrOf` equalities so a later loop invariant can append the same stored order
and representatives that the source program computed. -/
structure CertificateSnapshot {B c n : ℕ} {x : List ℕ} {σ : Env}
    (bound : ℕ) (G : SimpleGraph (Fin n)) (W : Finset ℕ) (σ' : Env)
    (h : Frontier B c n x σ) : Prop where
  candidate : Candidate B c n x σ'
  arrays : ∃ nextA nextB repA repB : ℕ → ℕ,
    σ'.arrs "activeA" = arrOf n (view σ "activeA") ∧
    σ'.arrs "activeB" = arrOf n (view σ "activeB") ∧
    σ'.arrs "nextA" = arrOf n nextA ∧
    σ'.arrs "nextB" = arrOf n nextB ∧
    σ'.arrs "repA" = arrOf n repA ∧
    σ'.arrs "repB" = arrOf n repB
  certificate : ∃ (currentB : ℕ) (labelB tableB repsB nextB repB : ℕ → ℕ)
      (R : Finset ℕ) (currentA : ℕ)
      (labelA tableA repsA nextA repA : ℕ → ℕ) (S : Finset ℕ),
    ∃ hB : ConcreteTracePartition G (view σ "activeB") (finSetAsSet W) R repB,
      RepData n currentB n (view σ "activeB") labelB tableB repsB nextB R ∧
      Nonempty (ConcreteTracePartition G (view σ "activeA") (finSetAsSet R) S repA) ∧
      RepData n currentA n (view σ "activeA") labelA tableA repsA nextA S ∧
      (∀ (v : Fin n), view σ "activeB" v.val = 1 →
      ((G.neighborSet v ∩
          (activeFinset (n := n) (view σ "activeA") : Set (Fin n))) ∆
        (G.neighborSet (hB.partition.representative v) ∩
          (activeFinset (n := n) (view σ "activeA") : Set (Fin n)))).ncard ≤ bound) ∧
      (∃ small big : List (Fin n),
        Enumerates (finSetAsSet S) small ∧
        Nonempty (Reduction G bound
          {v : Fin n | view σ "activeA" v.val = 1}
          {v : Fin n | view σ "activeB" v.val = 1}
          (finSetAsSet S) (finSetAsSet R) small big))

lemma workspace_certificate {B C c n : ℕ} {x : List ℕ} {σ σ' : Env}
    (h : Workspace B c n x σ) (hr : Run B buildReductionCertificate σ σ' C) :
    Workspace B c n x σ' := by
  refine ⟨SourceBounds.run_preserves hr h.bounded,
    (hr.frame_var "c" (by decide)).trans h.parameter,
    (hr.frame_var "n" (by decide)).trans h.vertices,
    (hr.frame_var "m" (by decide)).trans h.edges,
    (hr.frame_var "L" (by decide)).trans h.logarithm,
    (hr.frame_var "qpow" (by decide)).trans h.radixSize,
    (hr.frame_arr "off" (by decide)).trans h.offsets,
    (hr.frame_arr "tgt" (by decide)).trans h.targets,
    fun a => (run_array_length_eq hr a).trans (h.lengths a),
    inputBits_run hr h.randomInput, ?_⟩
  exact (hr.out_eq (by decide)).trans h.output

lemma frontier_certificate {B C c n : ℕ} {x : List ℕ} {σ σ' : Env}
    (h : Frontier B c n x σ) (hr : Run B buildReductionCertificate σ σ' C)
    (hgood : σ'.vars "good" = 1) : Frontier B c n x σ' := by
  have hA := hr.frame_arr "activeA" (by decide)
  have hB := hr.frame_arr "activeB" (by decide)
  have hvA : view σ' "activeA" = view σ "activeA" := by funext i; simp [view, hA]
  have hvB : view σ' "activeB" = view σ "activeB" := by funext i; simp [view, hB]
  have hac := hr.frame_var "acount" (by decide)
  have hround := hr.frame_var "round" (by decide)
  have hrem := hr.frame_var "removedCount" (by decide)
  refine ⟨workspace_certificate h.workspace hr, hgood, ?_, ?_, ?_, ?_, ?_,
    BitArrays.run_preserves hr (by decide) h.nextABits,
    BitArrays.run_preserves hr (by decide) h.nextBBits, ?_, ?_⟩
  · simpa only [hac, hvA] using h.activeCount
  · simpa only [hvA] using h.nonemptyA
  · simpa only [hvB] using h.nonemptyB
  · simpa only [ArrayBits, hA] using h.activeABits
  · simpa only [ArrayBits, hB] using h.activeBBits
  · simpa only [hac, hrem] using h.conservation
  · simpa only [hac, hround] using h.shrinking

/-- Running both trace partitions and the near verifier constructs a commit
candidate whenever it accepts. The source charge is linear in the CSR input;
shrinkage and log capacity are consequences, not additional run assumptions. -/
lemma certificate_candidate_run_full {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env} {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hc : 1 ≤ c) (hn : 0 < n)
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W)
    (hWr : ∀ v ∈ W, v < n)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B buildReductionCertificate σ σ' (2200 * (x.length + 1)) ∧
      (σ'.vars "good" = 1 → CertificateSnapshot bound G W σ' h) := by
  have arr (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt") (h₃ : a ≠ "count") :=
    h.workspace.vertex_array h₁ h₂ h₃
  have habound : ∀ v < n, view σ "activeA" v < B := by
    intro v hv
    exact h.workspace.value_bound (by rw [h.workspace.lengths]; exact hv)
  have hbbound : ∀ v < n, view σ "activeB" v < B := by
    intro v hv
    exact h.workspace.value_bound (by rw [h.workspace.lengths]; exact hv)
  have ha : 0 < σ.vars "acount" := by
    rw [h.activeCount]; exact Finset.card_pos.mpr (h.nonemptyA hn)
  have haN : σ.vars "acount" ≤ n := by
    rw [h.activeCount]; exact activeVertices_card_le _ _
  obtain ⟨τ, curB, labelB, tableB, repsB, nextB, repB, R, partB,
      curA, labelA, tableA, repsA, nextA, repA, S, hr, dataB, dataA,
      ⟨partA⟩, hnear, hred, hcountB, hcountA, hactiveA, hactiveB,
      hrepsA, hrepsB, hnextA, hnextB, hrepA, hrepB⟩ :=
    preparePartitionsAndVerify_run hx rfl h.workspace.vertices rfl hcsq hbound
      (h.workspace.bounded.vars "good") h.workspace.offsets h.workspace.targets
      (arr "activeA" (by decide) (by decide) (by decide))
      (arr "activeB" (by decide) (by decide) (by decide))
      (arr "ord" (by decide) (by decide) (by decide))
      (arr "classB" (by decide) (by decide) (by decide))
      (arr "classA" (by decide) (by decide) (by decide))
      (arr "classSize" (by decide) (by decide) (by decide))
      (arr "markedCount" (by decide) (by decide) (by decide))
      (arr "stamp" (by decide) (by decide) (by decide))
      (arr "marked" (by decide) (by decide) (by decide))
      (arr "touched" (by decide) (by decide) (by decide))
      (arr "split" (by decide) (by decide) (by decide))
      (arr "repClass" (by decide) (by decide) (by decide))
      (arr "repsB" (by decide) (by decide) (by decide))
      (arr "nextB" (by decide) (by decide) (by decide))
      (arr "repB" (by decide) (by decide) (by decide))
      (arr "repsA" (by decide) (by decide) (by decide))
      (arr "nextA" (by decide) (by decide) (by decide))
      (arr "repA" (by decide) (by decide) (by decide))
      (arr "degree" (by decide) (by decide) (by decide))
      (arr "inter" (by decide) (by decide) (by decide))
      (arr "neighbors" (by decide) (by decide) (by decide))
      henum hWr (h.nonemptyA hn) (h.nonemptyB hn) hc ha haN habound hbbound
      hnB htargetB hdenomB hboundB
  have hRr : ∀ v ∈ R, v < n := fun v hv =>
    (mem_activeVertices.mp (dataB.reps_processed hv)).1
  have hSr : ∀ v ∈ S, v < n := fun v hv =>
    (mem_activeVertices.mp (dataA.reps_processed hv)).1
  have hRcard : R.card ≤ n :=
    (Finset.card_le_card dataB.reps_processed).trans (activeVertices_card_le _ _)
  have hcostA := partitionCost_le_input hx ((sampleSize_le_self hc ha).trans haN)
    (PrefixEnumerates.entry_lt henum hWr) henum.injective_on_prefix
  have hcostB := partitionCost_le_input hx hRcard
    (PrefixEnumerates.entry_lt dataB.enum hRr) dataB.enum.injective_on_prefix
  have hcost : Run B buildReductionCertificate σ τ (2200 * (x.length + 1)) := by
    apply hr.mono
    have hxlen := hx.length_eq
    omega
  refine ⟨τ, hcost, ?_⟩
  intro hgood
  have hWcard : W.card = sampleSize (activeVertices n (view σ "activeA")).card c := by
    rw [prefix_card henum, ← h.activeCount]
  have hW : W.Nonempty := by
    apply Finset.card_pos.mp
    have hs := le_mul_sampleSize (a := σ.vars "acount") hc
    rw [prefix_card henum]
    by_contra hz
    have he : sampleSize (σ.vars "acount") c = 0 := by omega
    rw [he] at hs
    omega
  have hnextASet : activeVertices n (view τ "nextA") = S :=
    (active_of_array hnextA).trans (ActiveBookkeeping.RepData.active_eq dataA)
  have hnextBSet : activeVertices n (view τ "nextB") = R :=
    (active_of_array hnextB).trans (ActiveBookkeeping.RepData.active_eq dataB)
  have hcand : Candidate B c n x τ := by
    refine ⟨frontier_certificate h hcost hgood, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnextASet]; exact hcountA
    · rw [hnextASet, active_of_array hactiveA]
      exact dataA.reps_processed
    · rw [hnextASet]
      exact ActiveBookkeeping.ConcreteTracePartition.next_nonempty partA (h.nonemptyA hn)
    · rw [hnextBSet]
      exact ActiveBookkeeping.ConcreteTracePartition.next_nonempty partB (h.nonemptyB hn)
    · rw [hnextASet, hcost.frame_var "acount" (by decide), h.activeCount]
      exact concrete_partitions_shrink hc hG partB partA hWr hSr hW
        (h.nonemptyB hn) hWcard
  refine ⟨hcand, ?_, ?_⟩
  · exact ⟨nextA, nextB, repA, repB,
      hactiveA, hactiveB, hnextA, hnextB, hrepA, hrepB⟩
  · refine ⟨curB, labelB, tableB, repsB, nextB, repB, R,
      curA, labelA, tableA, repsA, nextA, repA, S, ?_⟩
    refine ⟨partB, dataB, ⟨partA⟩, dataA, ?_, ?_⟩
    · intro v hv
      exact hnear hgood v hv
    · simpa only [activeFinset] using hred hgood

/-- Backwards-compatible projection retaining the original candidate API. -/
lemma certificate_candidate_run {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env} {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hc : 1 ≤ c) (hn : 0 < n)
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W)
    (hWr : ∀ v ∈ W, v < n)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B buildReductionCertificate σ σ' (2200 * (x.length + 1)) ∧
      (σ'.vars "good" = 1 → Candidate B c n x σ') := by
  obtain ⟨σ', hr, hcert⟩ := certificate_candidate_run_full hx hG h hc hn hcsq
    hbound henum hWr hnB htargetB hdenomB hboundB
  exact ⟨σ', hr, fun hgood => (hcert hgood).candidate⟩

end Lax235315Proofs.Construction.CertificateFrontier
