import Lax457868Proofs.RefinedSetup
import Lax457868Proofs.PackedActiveSource
import Lax457868Proofs.DistinctNeighborhoodDomain
import Lax457868Proofs.RefinedTwinDomain
import Lax457868Proofs.RefinedRecordedCommit
import Lax457868Proofs.RefinedRoundSource
import Lax457868Proofs.RefinedRoundInput

/-! Execute the existing full-neighborhood partition before the first refined
sampler. Initially both sides are the entire vertex set, so the existing
active-side packer supplies the full ground set of tests. -/
namespace Lax457868Proofs.InitialNeighborhoodQuotient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.PackedActiveSource
open Lax457868Proofs.DistinctNeighborhoodDomain
open Lax457868Proofs.VerifiedPartitionBridge
open Lax457868Proofs.GraphTraceBounds
open Lax457868Proofs.SamplePacking

/-- The original full-vertex scan supplies the tests for deduplication. -/
def prepareQuotient : Com := packActiveBSource.seq
  (.assign "sampleCount" (.var "alen"))

/-- Populate the existing full-neighborhood partition input from actual setup
and packing runs. No representative set is provided as an assumption. -/
lemma prepareQuotient_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x bits : List ℕ} {σ : Env} (R : RefinedSetup.Ready c n x bits σ)
    (hx : EncodesGraph x n G) (hn2 : 2 ≤ n)
    (hB : 4 * (x.length + 1) ≤ B) :
    ∃ I : DistinctNeighborhoodInput B n (2 * edgeCount x) n G x
        Finset.univ Finset.univ (Finset.range n),
      Run B prepareQuotient σ I.σ (20 * n + 11) ∧
      (∀ a, a ≠ "ord" → I.σ.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "sampleCount" → v ≠ "alen" → v ≠ "activePackCursor" →
        I.σ.vars v = σ.vars v) := by
  classical
  have hlen := hx.length_eq
  have hnB : n < B := by omega
  have h1B : 1 < B := by omega
  have htargetB : 2 * edgeCount x < B := by omega
  have hord : σ.arrs "ord" = arrOf n (fun _ => 0) := by
    rw [R.scratch _ (by decide) (by decide) (by decide) (by decide)]
    simp [welzlExt, arrOf]
  obtain ⟨σ₁, packed, hpack, hactive, hord₁, hprefix, halen, _, hfa, hfv, hi, ho, _⟩ :=
    packActiveB_run R.vertices R.activeB hord (by intros; omega) hnB h1B
  have hflags : flaggedVertices n (fun _ => 1) = Finset.range n := by
    ext v; simp [flaggedVertices, activeVertices]
  rw [hflags, Finset.card_range] at halen
  rw [hflags, halen] at hprefix
  let τ := σ₁.setVar "sampleCount" n
  have rcount : Run B (.assign "sampleCount" (.var "alen")) σ₁ τ 2 := by
    apply Run.assign
    rw [evalB_var (by rw [halen]; exact hnB), halen]
  have hr : Run B prepareQuotient σ τ (20 * n + 11) := by
    simpa [prepareQuotient, Nat.add_assoc] using hpack.seq rcount
  have harr (a : String) (ha : a ≠ "ord") : τ.arrs a = σ.arrs a := hfa a ha
  have hvars (v : String) (hv : v ≠ "sampleCount") (hv₁ : v ≠ "alen")
      (hv₂ : v ≠ "activePackCursor") : τ.vars v = σ.vars v := by
    simp only [τ, Env.setVar, hv, ↓reduceIte]
    exact hfv v hv₁ hv₂
  have hnτ : τ.vars "n" = n := (hvars _ (by decide) (by decide) (by decide)).trans R.vertices
  have hrepr : ∀ a, ∃ f : ℕ → ℕ,
      τ.arrs a = arrOf (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a) f := by
    intro a
    apply exists_arrOf_of_length
    rw [run_array_length_eq hr a]
    exact R.lengths a
  choose f hf using hrepr
  have hreprN (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt")
      (h₃ : a ≠ "count") : τ.arrs a = arrOf n (f a) := by
    simpa [welzlExt, h₁, h₂, h₃] using hf a
  let I : DistinctNeighborhoodInput B n (2 * edgeCount x) n G x
      Finset.univ Finset.univ (Finset.range n) := {
    σ := τ, activeB := fun _ => 1, ord := packed
    classB := f "classB", classSize := f "classSize", markedCount := f "markedCount"
    stamp := f "stamp", marked := f "marked", touched := f "touched", split := f "split"
    repClass := f "repClass", repsB := f "repsB", nextB := f "nextB", repB := f "repB"
    hx := hx, htargetCap := rfl, hn := hnτ, hsampleCount := by simp [τ]
    hoff := (harr _ (by decide)).trans R.offsets
    htarget := (harr _ (by decide)).trans R.targets
    hactiveBArray := hactive, hord := hord₁
    hclassB := hreprN _ (by decide) (by decide) (by decide)
    hclassSize := hreprN _ (by decide) (by decide) (by decide)
    hmarkedCount := hreprN _ (by decide) (by decide) (by decide)
    hstamp := hreprN _ (by decide) (by decide) (by decide)
    hmarked := hreprN _ (by decide) (by decide) (by decide)
    htouched := hreprN _ (by decide) (by decide) (by decide)
    hsplit := hreprN _ (by decide) (by decide) (by decide)
    hrepClass := hreprN _ (by decide) (by decide) (by decide)
    hrepsB := hreprN _ (by decide) (by decide) (by decide)
    hnextB := hreprN _ (by decide) (by decide) (by decide)
    hrepB := hreprN _ (by decide) (by decide) (by decide)
    henum := hprefix
    hWrange := by intro v hv; exact Finset.mem_range.mp hv
    hWfull := by ext v; simp [finsetOfNumeric, v.isLt]
    hCactive := by simp
    hCnonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    hsampleCountN := le_rfl, hnB := hnB, htargetCapB := htargetB
    honeB := h1B, hactiveBBound := by intros; exact h1B }
  exact ⟨I, hr, harr, hvars⟩

/-- Initialize the ground-side copy to retain every original vertex when the
neighborhood-side quotient is adopted. -/
def fillNextA : Com := (Com.assign "i" (.lit 0)).seq
  (.while (.lt (.var "i") (.var "n")) (Fill.put "nextA" "i" (.lit 1)))

lemma fillNextA_run {B n : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hlen : (σ.arrs "nextA").length = n)
    (hnB : n < B) (h1B : 1 < B) :
    ∃ τ, Run B fillNextA σ τ (11 * n + 6) ∧
      τ.arrs "nextA" = arrOf n (fun _ => 1) := by
  obtain ⟨f, hf⟩ := exists_arrOf_of_length hlen
  obtain ⟨τ, hr, ⟨g, hg, hcell⟩, _⟩ :=
    (Fill.loop_spec B n "nextA" "i" "n" (.lit 1) (fun _ => 1)
      (by decide) hnB (fun _ _ _ _ => evalB_lit h1B)).run
      (σ := σ) ⟨⟨f, hf⟩, hn⟩
  exact ⟨τ, hr, hg.trans (arrOf_congr hcell)⟩

/-- The once-only preprocessing uses the original partition and copy passes. -/
def initialQuotientSource : Com := seqs [prepareQuotient,
  partition "activeB" "ord" "sampleCount" "classB" "repsB" "nextB" "repB" "nextBCount",
  fillNextA, adoptNext]

open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.ReusedOriginal.Construction.TracePartitions

/-- The full-neighborhood quotient is actually installed as the sampler's
active neighborhood side. The ground side and reconstruction history remain
at their initial values. -/
lemma initialQuotientSource_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x bits : List ℕ} {σ : Env} (R : RefinedSetup.Ready c n x bits σ)
    (hx : EncodesGraph x n G) (hn2 : 2 ≤ n)
    (hlarge : 2 * refinedCutoffK c < n)
    (hB : 4 * (x.length + 1) ≤ B) :
    ∃ τ, ∃ C : Finset ℕ,
      Run B initialQuotientSource σ τ (951 * (x.length + 1)) ∧
      RoundData c n x (Finset.range n) C τ ∧
      C ⊆ Finset.range n ∧ C.Nonempty ∧
      Nonempty (TracePartition G Set.univ Set.univ (finSetAsSet C)) ∧
      (∀ v, v ∉ initialQuotientSource.wvars → τ.vars v = σ.vars v) ∧
      (∀ a, a ∉ initialQuotientSource.warrs → τ.arrs a = σ.arrs a) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  classical
  have hlen := hx.length_eq
  have hnB : n < B := by omega
  have h1B : 1 < B := by omega
  obtain ⟨I, rprep, hfa, hfv⟩ := prepareQuotient_run R hx hn2 hB
  obtain ⟨σ₁, current, label, repClass, reps, nextB, repB, C,
      rpart, hcount, hactive, hclass, hrc, hreps, hnext, hrep, hdata,
      hmap, ⟨htrace⟩, hsub, hinj, himage, hcard, hcost⟩ :=
    runDistinctNeighborhoodSource I
  have rbefore : Run B (prepareQuotient.seq
      (partition "activeB" "ord" "sampleCount" "classB" "repsB" "nextB" "repB" "nextBCount"))
      σ σ₁ (20 * n + 11 + partitionCost x I.ord n n) := rprep.seq rpart
  have hn₁ : σ₁.vars "n" = n := (rbefore.frame_var _ (by decide)).trans R.vertices
  have hlenA : (σ₁.arrs "nextA").length = n := by
    rw [run_array_length_eq rbefore]
    simpa [welzlExt] using R.lengths "nextA"
  obtain ⟨σ₂, rfill, hnextA⟩ := fillNextA_run hn₁ hlenA hnB h1B
  have hn₂ : σ₂.vars "n" = n := (rfill.frame_var _ (by decide)).trans hn₁
  have hactiveA₂ : σ₂.arrs "activeA" = arrOf n (fun _ => 1) := by
    rw [rfill.frame_arr _ (by decide), rbefore.frame_arr _ (by decide)]
    exact R.activeA
  have hactiveB₂ : σ₂.arrs "activeB" = arrOf n (fun _ => 1) := by
    rw [rfill.frame_arr _ (by decide), rbefore.frame_arr _ (by decide)]
    exact R.activeB
  have hnextB₂ : σ₂.arrs "nextB" = arrOf n nextB := by
    rw [rfill.frame_arr _ (by decide)]; exact hnext
  have hzero : arrayBits I.σ "nextB" := by
    intro v hv
    rw [hfa _ (by decide), R.scratch _ (by decide) (by decide) (by decide) (by decide)] at hv
    have hz := (List.mem_replicate.mp hv).2
    omega
  have hbits₁ := onlyBitStores_preserves rpart partitionB_onlyBitStores hzero
  have hbits : ∀ i < n, nextB i ≤ 1 := by
    intro i hi
    apply hbits₁
    rw [hnext]
    exact List.mem_of_getElem? (getElem?_arrOf nextB hi)
  have hCrange : C ⊆ Finset.range n := by
    intro v hv
    exact Finset.mem_range.mpr (mem_activeVertices.mp (hdata.reps_processed hv)).1
  have hnextFlag : arrOf n nextB = arrOf n (setFlag C) := by
    apply arrOf_congr
    intro i hi
    have hb := hbits i hi
    have hm := hdata.out_mem i hi
    by_cases hmem : i ∈ C
    · simp [setFlag, hmem, hm.mpr hmem]
    · have hne : nextB i ≠ 1 := by simpa [hmem] using hm
      simp [setFlag, hmem, show nextB i = 0 by omega]
  obtain ⟨τ, a, b, radopt, ha, hb, hva, hvb, _⟩ :=
    RefinedRecordedCommit.adoptNext_run hn₂ hactiveA₂ hactiveB₂ hnextA hnextB₂
      (by intros; exact h1B) (by intro i hi; exact (hbits i hi).trans_lt h1B) hnB
  have hrun : Run B initialQuotientSource σ τ (951 * (x.length + 1)) := by
    have hh := rprep.seq (rpart.seq (rfill.seq radopt))
    apply hh.mono
    dsimp [initialQuotientSource, seqs] at *
    omega
  have hactiveAτ : τ.arrs "activeA" = arrOf n (setFlag (Finset.range n)) := by
    rw [ha]
    apply arrOf_congr
    intro i hi
    simpa [setFlag, Finset.mem_range.mpr hi] using hva i hi
  have hactiveBτ : τ.arrs "activeB" = arrOf n (setFlag C) :=
    hb.trans ((arrOf_congr hvb).trans hnextFlag)
  have hnonempty : C.Nonempty := by
    have h0 : 0 ∈ activeVertices n I.activeB := by
      apply mem_activeVertices.mpr
      refine ⟨by omega, ?_⟩
      exact (I.hCactive ⟨0, by omega⟩).mp (Finset.mem_univ _)
    obtain ⟨v, hv, _⟩ := hdata.covers 0 h0
    exact ⟨v, hv⟩
  have hfullTrace : TracePartition G Set.univ Set.univ (finSetAsSet C) := by
    have hset : {v : Fin n | I.activeB v.val = 1} = Set.univ := by
      ext v; simp [← I.hCactive v]
    simpa only [hset, Finset.coe_univ] using htrace.partition
  refine ⟨τ, C, hrun, ?_, hCrange, hnonempty, ⟨hfullTrace⟩,
    hrun.frame_var, hrun.frame_arr, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hactiveAτ, hactiveBτ, ?_, ?_, ?_, ?_⟩
    · exact (hrun.frame_var _ (by decide)).trans R.parameter
    · exact (hrun.frame_var _ (by decide)).trans R.vertices
    · exact (hrun.frame_var _ (by decide)).trans R.radixSize
    · rw [hrun.frame_var _ (by decide), R.cutoff, Nat.min_eq_right hlarge.le]
    · exact (hrun.frame_var _ (by decide)).trans (R.logParameter hlarge)
    · exact (hrun.frame_arr _ (by decide)).trans R.offsets
    · exact (hrun.frame_arr _ (by decide)).trans R.targets
    · intro a; rw [run_array_length_eq hrun]; exact R.lengths a
    · intro a ha
      have hz := (initial_roundData R hlarge).cleared a ha
      rw [hrun.frame_arr a (by
        simp only [repairMarks, List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide)]
      exact hz
    · intro v hv
      rw [radopt.frame_arr _ (by decide), hnextA] at hv
      have hmem : v = 1 := (List.mem_replicate.mp (by simpa [arrOf] using hv)).2
      omega
    · intro v hv
      rw [radopt.frame_arr _ (by decide), rfill.frame_arr _ (by decide)] at hv
      exact hbits₁ v hv
  · exact hrun.frame_inp (by decide)
  · exact hrun.out_eq (by decide)

end Lax457868Proofs.InitialNeighborhoodQuotient
