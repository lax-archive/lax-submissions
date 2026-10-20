import Lax457868Proofs.CompleteSamplerSource
import Lax457868Proofs.VerifiedRoundPartitions
import Lax457868Proofs.VerifiedReconstructionBridge
import Lax457868Proofs.RefinedContraction
import Lax457868Proofs.RefinedRecordedCommit
import Lax457868Proofs.ReusedOriginal.Construction.RecordedHistory
import Lax457868Proofs.ReusedOriginal.Construction.RemovedRestoreBridge
import Mathlib.Tactic

set_option autoImplicit false

/-! One literal refined reduction round and its chronological source log.
The generic stored-history invariant below is ported from
`Lax235315Proofs.Construction.StoredHistory` (Apache-2.0). -/

namespace Lax457868Proofs.RefinedRoundSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.RecordedHistory
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys

/-- The source array read with its default value, transported from the
original round invariant. -/
def view (σ : Env) (a : String) (i : ℕ) : ℕ := (σ.arrs a).getD i 0

lemma view_of_array {σ : Env} {a : String} {n : ℕ} {f : ℕ → ℕ}
    (h : σ.arrs a = arrOf n f) {i : ℕ} (hi : i < n) : view σ a i = f i := by
  simp [view, h, List.getD_eq_getElem?_getD, getElem?_arrOf f hi]

/-- Every accepted reduction is connected to the actual deletion log and
round-boundary arrays. Unused log entries retain valid vertex indices too. -/
structure Stored {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Env) where
  A : ℕ → Set (Fin n)
  C : ℕ → Set (Fin n)
  boundary : ℕ → ℕ
  history : History G k (σ.vars "round") A C boundary
    (view σ "removed") (view σ "removedRep")
  initialA : A 0 = Set.univ
  initialC : C 0 = Set.univ
  currentA : A (σ.vars "round") = {v : Fin n | view σ "activeA" v.val = 1}
  currentC : C (σ.vars "round") = {v : Fin n | view σ "activeB" v.val = 1}
  starts : ∀ r < σ.vars "round", view σ "roundStart" r = boundary r
  ends : ∀ r < σ.vars "round", view σ "roundEnd" r = boundary (r + 1)
  monotone : ∀ r s, r ≤ s → s ≤ σ.vars "round" → boundary r ≤ boundary s
  capacity : ∀ r ≤ σ.vars "round", boundary r ≤ n
  used : boundary (σ.vars "round") = σ.vars "removedCount"
  removedBound : ∀ i < n, view σ "removed" i < n
  representativeBound : ∀ i < n, view σ "removedRep" i < n

/-- Scratch computations leave the stored graph history unchanged. -/
def Stored.frame {n k : ℕ} {G : SimpleGraph (Fin n)} {σ τ : Env}
    (h : Stored G k σ)
    (hround : τ.vars "round" = σ.vars "round")
    (hused : τ.vars "removedCount" = σ.vars "removedCount")
    (ha : τ.arrs "activeA" = σ.arrs "activeA")
    (hb : τ.arrs "activeB" = σ.arrs "activeB")
    (hs : τ.arrs "roundStart" = σ.arrs "roundStart")
    (he : τ.arrs "roundEnd" = σ.arrs "roundEnd")
    (hr : τ.arrs "removed" = σ.arrs "removed")
    (hp : τ.arrs "removedRep" = σ.arrs "removedRep") : Stored G k τ where
  A := h.A
  C := h.C
  boundary := h.boundary
  history := by
    have vr : view τ "removed" = view σ "removed" := by funext i; simp [view, hr]
    have vp : view τ "removedRep" = view σ "removedRep" := by funext i; simp [view, hp]
    simpa only [hround, vr, vp] using h.history
  initialA := h.initialA
  initialC := h.initialC
  currentA := by simpa only [hround, view, ha] using h.currentA
  currentC := by simpa only [hround, view, hb] using h.currentC
  starts := by simpa only [hround, view, hs] using h.starts
  ends := by simpa only [hround, view, he] using h.ends
  monotone := by simpa only [hround] using h.monotone
  capacity := by simpa only [hround] using h.capacity
  used := by simpa only [hround, hused] using h.used
  removedBound := by simpa only [view, hr] using h.removedBound
  representativeBound := by simpa only [view, hp] using h.representativeBound

/-- At zero rounds, all vertices are active and both logs contain zero. -/
def initial {n k : ℕ} (G : SimpleGraph (Fin n)) {σ : Env}
    (hround : σ.vars "round" = 0) (hused : σ.vars "removedCount" = 0)
    (ha : ∀ i < n, view σ "activeA" i = 1)
    (hb : ∀ i < n, view σ "activeB" i = 1)
    (hr : ∀ i < n, view σ "removed" i = 0)
    (hp : ∀ i < n, view σ "removedRep" i = 0) : Stored G k σ where
  A := fun _ => Set.univ
  C := fun _ => Set.univ
  boundary := fun _ => 0
  history := ⟨by intro r hr; omega⟩
  initialA := rfl
  initialC := rfl
  currentA := by ext v; simp [ha v.val v.isLt]
  currentC := by ext v; simp [hb v.val v.isLt]
  starts := by intro r hr; omega
  ends := by intro r hr; omega
  monotone := by intros; omega
  capacity := by intros; omega
  used := hused.symm
  removedBound := by intro i hi; rw [hr i hi]; omega
  representativeBound := by intro i hi; rw [hp i hi]; omega


/-- Append an accepted step to the concrete history. The premises are the
actual commit's counter, boundary-array, prefix and value postconditions. -/
def Stored.append {n k : ℕ} {G : SimpleGraph (Fin n)} {σ τ : Env}
    (h : Stored G k σ) {boundary' : ℕ → ℕ}
    (hround : τ.vars "round" = σ.vars "round" + 1)
    (hboundary : ∀ r ≤ σ.vars "round", boundary' r = h.boundary r)
    (hnew : boundary' (σ.vars "round" + 1) = τ.vars "removedCount")
    (hinc : σ.vars "removedCount" ≤ τ.vars "removedCount")
    (hcap : τ.vars "removedCount" ≤ n)
    (hstarts : ∀ r < τ.vars "round", view τ "roundStart" r = boundary' r)
    (hends : ∀ r < τ.vars "round", view τ "roundEnd" r = boundary' (r + 1))
    (hremoved : ∀ i < σ.vars "removedCount", view τ "removed" i = view σ "removed" i)
    (hreps : ∀ i < σ.vars "removedCount", view τ "removedRep" i = view σ "removedRep" i)
    (hremBound : ∀ i < n, view τ "removed" i < n)
    (hrepBound : ∀ i < n, view τ "removedRep" i < n)
    (s : RecordedStep G k (σ.vars "round") (h.A (σ.vars "round"))
      (h.C (σ.vars "round")) {v : Fin n | view τ "activeA" v.val = 1}
      {v : Fin n | view τ "activeB" v.val = 1} boundary'
      (view τ "removed") (view τ "removedRep")) : Stored G k τ where
  A := Function.update h.A (σ.vars "round" + 1) {v : Fin n | view τ "activeA" v.val = 1}
  C := Function.update h.C (σ.vars "round" + 1) {v : Fin n | view τ "activeB" v.val = 1}
  boundary := boundary'
  history := by
    rw [hround]
    exact h.history.append hboundary
      (fun r hr => h.monotone r (r + 1) (by omega) (by omega))
      (fun r hr => h.monotone (r + 1) (σ.vars "round") (by omega) le_rfl)
      (by simpa only [h.used] using hremoved)
      (by simpa only [h.used] using hreps) s
  initialA := by simpa using h.initialA
  initialC := by simpa using h.initialC
  currentA := by simp [hround]
  currentC := by simp [hround]
  starts := hstarts
  ends := hends
  monotone := by
    intro r t hrt ht
    by_cases he : t = σ.vars "round" + 1
    · subst t
      rw [hnew]
      by_cases hr : r = σ.vars "round" + 1
      · rw [hr, hnew]
      · have hrle : r ≤ σ.vars "round" := by omega
        rw [hboundary r hrle]
        exact (h.monotone r (σ.vars "round") hrle le_rfl).trans (h.used.symm ▸ hinc)
    · have htle : t ≤ σ.vars "round" := by omega
      rw [hboundary t htle, hboundary r (by omega)]
      exact h.monotone r t hrt htle
  capacity := by
    intro r hr
    by_cases he : r = σ.vars "round" + 1
    · rw [he, hnew]; exact hcap
    · have hrle : r ≤ σ.vars "round" := by omega
      rw [hboundary r hrle]; exact h.capacity r hrle
  used := by simpa only [hround] using hnew
  removedBound := hremBound
  representativeBound := hrepBound


open Lax457868Proofs.CompleteSamplerSource
open Lax457868Proofs.VerifiedRoundPartitions
open Lax457868Proofs.VerifiedPartitionBridge
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource
open Lax457868Proofs.ReusedOriginal.Construction.RemovedRestoreBridge
open Lax457868Proofs.ReusedOriginal.Construction.Reconstruction
open Lax457868Proofs.ReusedOriginal.Construction.ConcreteReconstruction
open Lax457868Proofs.ReusedOriginal.Construction.TracePartitions
open Lax457868Proofs.ReusedOriginal.Construction.LinkedSource
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.RefinedSampleSpec
open Lax11.GraphEncoding

noncomputable section

private lemma array_shape {σ : Env} {a : String} {n : ℕ}
    (h : (σ.arrs a).length = n) : σ.arrs a = arrOf n (view σ a) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [getElem?_arrOf _ hi]
    have hi' : i < (σ.arrs a).length := by omega
    simp [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- Array capacities supplied at the start of a round. The sampler and the
partition passes preserve lengths, so their old contents may be arbitrary. -/
structure RoundScratch (n : ℕ) (σ : Env) : Prop where
  classA : (σ.arrs "classA").length = n
  repsA : (σ.arrs "repsA").length = n
  repsB : (σ.arrs "repsB").length = n
  nextA : (σ.arrs "nextA").length = n
  nextB : (σ.arrs "nextB").length = n
  repA : (σ.arrs "repA").length = n
  roundStart : (σ.arrs "roundStart").length = n
  roundEnd : (σ.arrs "roundEnd").length = n
  removed : (σ.arrs "removed").length = n
  removedRep : (σ.arrs "removedRep").length = n

lemma RoundScratch.frame {B n K : ℕ} {c : Com} {σ τ : Env}
    (h : RoundScratch n σ) (hrun : Run B c σ τ K) : RoundScratch n τ where
  classA := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.classA
  repsA := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.repsA
  repsB := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.repsB
  nextA := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.nextA
  nextB := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.nextB
  repA := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.repA
  roundStart := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.roundStart
  roundEnd := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.roundEnd
  removed := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.removed
  removedRep := by rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]; exact h.removedRep

/-- Reconstruct the actual partition input from a successful sampler exit.
Only the scratch lengths are extra input; every witness function reads an
existing physical array. -/
lemma partition_input_of_sampler
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      cost c : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A W : Finset ℕ}
    (R : Lax457868Proofs.InitialSamplerRetriesSource.ReadyInput
      B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    (hscratch : RoundScratch n R.I.σ)
    {σ : Env} (hrun : Run B completeSamplerSource R.I.σ σ cost)
    (hframe : FinalFrame R S σ)
    (hord : ∃ packed : ℕ → ℕ,
      σ.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ.vars "sampleCount") packed W)
    (hcount : σ.vars "sampleCount" = W.card)
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily
        (activeVertices n R.I.activeB)
        (fun b => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G b ∩ A))
      (A : Set ℕ) (W : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (hC : (activeVertices n R.I.activeB).Nonempty) :
    ∃ I : RoundPartitionInput B n targetCap W.card G x
        (finsetOfNumeric A)
        (finsetOfNumeric (activeVertices n R.I.activeB)) W,
      I.σ = σ ∧ I.activeA = setFlag A ∧ I.activeB = R.I.activeB := by
  classical
  obtain ⟨packed, hordArray, hprefix⟩ := hord
  have hscratchOut := hscratch.frame hrun
  have hlen (a : String) (h : (R.I.σ.arrs a).length = n) :
      (σ.arrs a).length = n := by
    rw [Lax457868Proofs.ReusedOriginal.Construction.RadixEight.run_array_length_eq hrun]
    exact h
  have hWsubset : W ⊆ A := by
    intro v hv
    exact hsample.2.2.1 hv
  have hWrange : ∀ v ∈ W, v < n := by
    intro v hv
    exact Finset.mem_range.mp (R.I.hA (hWsubset hv))
  let I : RoundPartitionInput B n targetCap W.card G x
      (finsetOfNumeric A)
      (finsetOfNumeric (activeVertices n R.I.activeB)) W := {
    σ := σ
    activeA := setFlag A
    activeB := R.I.activeB
    ord := packed
    classA := view σ "classA"
    classB := view σ "classB"
    classSize := view σ "classSize"
    markedCount := view σ "markedCount"
    stamp := view σ "stamp"
    marked := view σ "marked"
    touched := view σ "touched"
    split := view σ "split"
    repClass := view σ "repClass"
    repsA := view σ "repsA"
    repsB := view σ "repsB"
    nextA := view σ "nextA"
    nextB := view σ "nextB"
    repA := view σ "repA"
    repB := view σ "repB"
    hx := R.I.hx
    htargetCap := R.I.htargetCapEq
    hn := hframe.1
    hsampleCount := hcount
    hoff := hframe.2.2.2.2.1
    htarget := hframe.2.2.2.2.2.1
    hactiveAArray := hframe.2.2.1
    hactiveBArray := hframe.2.2.2.1
    hord := hordArray
    hclassA := array_shape hscratchOut.classA
    hclassB := array_shape (hlen "classB" (by rw [R.I.hclassB]; simp [arrOf]))
    hclassSize := array_shape (hlen "classSize" (by rw [R.I.hclassSize]; simp [arrOf]))
    hmarkedCount := array_shape (hlen "markedCount" (by rw [R.I.hmarkedCount]; simp [arrOf]))
    hstamp := array_shape (hlen "stamp" (by rw [R.I.hstamp]; simp [arrOf]))
    hmarked := array_shape (hlen "marked" (by rw [R.I.hmarked]; simp [arrOf]))
    htouched := array_shape (hlen "touched" (by rw [R.I.htouched]; simp [arrOf]))
    hsplit := array_shape (hlen "split" (by rw [R.I.hsplit]; simp [arrOf]))
    hrepClass := array_shape (hlen "repClass" (by rw [R.I.hrepClass]; simp [arrOf]))
    hrepsA := array_shape hscratchOut.repsA
    hrepsB := array_shape hscratchOut.repsB
    hnextA := array_shape hscratchOut.nextA
    hnextB := array_shape hscratchOut.nextB
    hrepA := array_shape hscratchOut.repA
    hrepB := array_shape (hlen "repB" (by rw [R.I.hrepB]; simp [arrOf]))
    henum := by simpa [hcount] using hprefix
    hWrange := hWrange
    hactiveANonempty := by
      obtain ⟨v, hv⟩ := R.I.hAnonempty
      exact ⟨v, by simp [activeVertices, mem_activeVertices, setFlag,
        Finset.mem_range.mp (R.I.hA hv), hv]⟩
    hactiveBNonempty := by
      exact hC
    hsampleCountN := by
      have hle := Finset.card_le_card (show W ⊆ Finset.range n by
        intro v hv; exact Finset.mem_range.mpr (hWrange v hv))
      simpa using hle
    hnB := by have := R.hnB; omega
    htargetCapB := R.I.htargetCapB
    honeB := R.I.honeB
    hactiveABound := by
      intro v hv
      have hB := R.I.honeB
      by_cases h : v ∈ A <;> simp [setFlag, h] <;> omega
    hactiveBBound := by
      intro v hv
      have h := R.I.hactive01 v hv
      have hB := R.I.honeB
      omega
    hAactive := by
      intro v
      simp [finsetOfNumeric, setFlag]
    hBactive := by
      intro v
      simp [finsetOfNumeric, activeVertices, mem_activeVertices]
    hWsubsetA := by
      intro v hv
      have hvW : v.val ∈ W := by simpa [finsetOfNumeric] using hv
      simpa [finsetOfNumeric] using hWsubset hvW
  }
  exact ⟨I, rfl, rfl, rfl⟩


private lemma numeric_image_finset {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) :
    Fin.val '' ((finsetOfNumeric S : Finset (Fin n)) : Set (Fin n)) =
      (S : Set ℕ) := by
  ext i
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [finsetOfNumeric] using hv
  · intro hi
    refine ⟨⟨i, Finset.mem_range.mp (hS hi)⟩, ?_, rfl⟩
    simpa [finsetOfNumeric] using hi

private lemma numeric_card_eq {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) :
    (finsetOfNumeric (n := n) S).card = S.card := by
  have himage := numeric_image_finset hS
  have h := Set.ncard_image_of_injective
    ((finsetOfNumeric (n := n) S : Finset (Fin n)) : Set (Fin n))
    Fin.val_injective
  rw [himage, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
  exact h.symm

private lemma finite_neighborhood_image {n : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset ℕ} (b : Fin n) :
    Fin.val '' ((Lax457868Proofs.GraphTraceBounds.finiteNeighborhood
      G (finsetOfNumeric A) b : Finset (Fin n)) : Set (Fin n)) =
      (Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G b.val ∩ A :
        Finset ℕ) := by
  classical
  ext i
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [Lax457868Proofs.GraphTraceBounds.finiteNeighborhood,
      Finset.mem_coe, Finset.mem_filter] at hv
    rcases hv with ⟨hA, hadj⟩
    have hA' : v.val ∈ A := by simpa [finsetOfNumeric] using hA
    simp [Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood,
      Lax11Proofs.CC.Adjn, v.isLt, hA', hadj.symm]
  · intro hi
    have hiA : i ∈ A := (Finset.mem_inter.mp hi).2
    have hin : i < n := Finset.mem_range.mp
      (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).1
    let v : Fin n := ⟨i, hin⟩
    refine ⟨v, ?_, rfl⟩
    have hadj : G.Adj b v := by
      have hnum := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
      rcases hnum with ⟨_, _, hnum⟩
      simpa [v, G.adj_comm] using hnum
    change v ∈ Lax457868Proofs.GraphTraceBounds.finiteNeighborhood
      G (finsetOfNumeric A) b
    simp [Lax457868Proofs.GraphTraceBounds.finiteNeighborhood,
      finsetOfNumeric, v, hiA, hadj]

/-- The numeric sampler certificate is the graph certificate on the same
physical vertices. `Fin.val` is injective and preserves every trace and
disagreement cardinality. -/
private lemma sample_fin_of_numeric {n c k : ℕ} {G : SimpleGraph (Fin n)}
    {A W C : Finset ℕ}
    (hA : A ⊆ Finset.range n) (hW : W ⊆ A)
    (hC : C ⊆ Finset.range n)
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily C
        (fun b => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G b ∩ A))
      (A : Set ℕ) (W : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k) :
    IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily
        (finsetOfNumeric C)
        (Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G (finsetOfNumeric A)))
      ((finsetOfNumeric A : Finset (Fin n)) : Set (Fin n))
      ((finsetOfNumeric W : Finset (Fin n)) : Set (Fin n))
      (((finsetOfNumeric (n := n) A).card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k := by
  classical
  have hWrange : W ⊆ Finset.range n := hW.trans hA
  have hAimg := numeric_image_finset hA
  have hWimg := numeric_image_finset hWrange
  have hAcard := numeric_card_eq hA
  rcases hsample with ⟨_, hwithin, hWA, hsize, hnear⟩
  refine ⟨Set.toFinite _, ?_, ?_, ?_, ?_⟩
  · rintro X ⟨b, hb, rfl⟩
    intro v hv
    simp only [Lax457868Proofs.GraphTraceBounds.finiteNeighborhood,
      Finset.mem_coe, Finset.mem_filter] at hv
    exact hv.1
  · intro v hv
    simp only [Finset.mem_coe] at hv ⊢
    have hvW : v.val ∈ W := by simpa [finsetOfNumeric] using hv
    have hvA := hW hvW
    simpa [finsetOfNumeric] using hvA
  · rw [hAcard]
    have hsize' := hsize
    rw [← hWimg, Set.ncard_image_of_injective _ Fin.val_injective,
      Set.ncard_coe_finset] at hsize'
    simpa only [Set.ncard_coe_finset] using hsize'
  · intro X hX Y hY htrace
    rcases hX with ⟨b, hb, rfl⟩
    rcases hY with ⟨d, hd, rfl⟩
    have hbc : b.val ∈ C := by simpa [finsetOfNumeric] using hb
    have hdc : d.val ∈ C := by simpa [finsetOfNumeric] using hd
    have hXnum : Fin.val ''
        ((Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G
          (finsetOfNumeric A) b : Finset (Fin n)) : Set (Fin n)) ∈
        Lax457868Proofs.SamplerContract.neighborhoodFamily C
          (fun z => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G z ∩ A) := by
      exact ⟨b.val, hbc, (finite_neighborhood_image b).symm⟩
    have hYnum : Fin.val ''
        ((Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G
          (finsetOfNumeric A) d : Finset (Fin n)) : Set (Fin n)) ∈
        Lax457868Proofs.SamplerContract.neighborhoodFamily C
          (fun z => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G z ∩ A) := by
      exact ⟨d.val, hdc, (finite_neighborhood_image d).symm⟩
    have htraceNum : Fin.val ''
        (((Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G
          (finsetOfNumeric A) b : Finset (Fin n)) : Set (Fin n)) ∩
          ((finsetOfNumeric W : Finset (Fin n)) : Set (Fin n))) =
        Fin.val ''
        (((Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G
          (finsetOfNumeric A) d : Finset (Fin n)) : Set (Fin n)) ∩
          ((finsetOfNumeric W : Finset (Fin n)) : Set (Fin n))) :=
      congrArg (Set.image Fin.val) htrace
    rw [Set.image_inter Fin.val_injective, Set.image_inter Fin.val_injective,
      hWimg] at htraceNum
    have hk := hnear _ hXnum _ hYnum htraceNum
    rw [← Set.image_sdiff Fin.val_injective,
      ← Set.image_sdiff Fin.val_injective,
      ← Set.image_union, Set.ncard_image_of_injective _ Fin.val_injective] at hk
    exact hk

/-- The fixed outer command commits only after both source retry loops have
reported acceptance. Each failure explicitly stops the outer iteration. -/
def refinedRoundSource : Com :=
  completeSamplerSource.seq
    (.ite (.eq (.var "initialRetryStatus") (.lit 1))
      (.ite (.eq (.var "repairRetryStatus") (.lit 1))
        ((partition "activeB" "ord" "sampleCount" "classB"
          "repsB" "nextB" "repB" "nextBCount").seq
          ((partition "activeA" "repsB" "nextBCount" "classA"
            "repsA" "nextA" "repA" "nextACount").seq commitReduction))
        (.assign "acount" (.lit 0)))
      (.assign "acount" (.lit 0)))

/-- The accepted sampler output drives the two literal partition passes.
The recurrence is about their actual representative array, not a separately
selected abstract contraction. -/
lemma accepted_partitions_run
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      cost c : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A W : Finset ℕ}
    (R : Lax457868Proofs.InitialSamplerRetriesSource.ReadyInput
      B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    (hscratch : RoundScratch n R.I.σ)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    {σ : Env} (hrun : Run B completeSamplerSource R.I.σ σ cost)
    (hframe : FinalFrame R S σ)
    (hord : ∃ packed : ℕ → ℕ,
      σ.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ.vars "sampleCount") packed W)
    (hcount : σ.vars "sampleCount" = W.card)
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily
        (activeVertices n R.I.activeB)
        (fun b => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G b ∩ A))
      (A : Set ℕ) (W : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (hC : (activeVertices n R.I.activeB).Nonempty) :
    ∃ σ₂ : Env, ∃ Rnum Snum : Finset ℕ,
      ∃ partCostB partCostA : ℕ,
      Run B ((partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount").seq
        (partition "activeA" "repsB" "nextBCount" "classA"
          "repsA" "nextA" "repA" "nextACount")) σ σ₂
        (partCostB + partCostA) ∧
      σ₂.vars "nextACount" = Snum.card ∧
      σ₂.vars "nextBCount" = Rnum.card ∧
      σ₂.arrs "activeA" = arrOf n (setFlag A) ∧
      σ₂.arrs "activeB" = arrOf n R.I.activeB ∧
      2 * Snum.card ≤ A.card + 2 * c ^ 2 ∧
      partCostB + partCostA ≤ 1800 * (x.length + 1) := by
  classical
  obtain ⟨I, hIσ, hIA, hIB⟩ :=
    partition_input_of_sampler R S hscratch hrun hframe hord hcount hsample hC
  obtain ⟨σ₁, σ₂, currentB, currentA, Rnum, Snum,
    labelB, repClassB, repsB', nextB', repB', labelA, repClassA,
    repsA', nextA', repA', hB, hA, runB, runA, runPart,
    dataB, dataA, hcountB₁, hcountA₂, hcountB₂,
    hactiveB₂, hrepsB₂, hrepB₂, hnextB₂,
    hactiveA₂, hrepsA₂, hrepA₂, hnextA₂,
    contraction, hmapB, hmapA, hretB, hretA, hcost⟩ :=
      runVerifiedRoundPartitions I
  have hWsub : W ⊆ A := by
    intro v hv
    exact hsample.2.2.1 hv
  have hCsub : activeVertices n R.I.activeB ⊆ Finset.range n := by
    intro v hv
    exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
  have hsampleFin := sample_fin_of_numeric R.I.hA hWsub hCsub hsample
  have hshrink :=
    Lax457868Proofs.RefinedContraction.graph_traceContraction_size_bound
      hG hc (finsetOfNumeric A)
      (finsetOfNumeric (activeVertices n R.I.activeB))
      (finsetOfNumeric W) hsampleFin contraction
  have hSrange : Snum ⊆ Finset.range n := by
    intro v hv
    exact Finset.mem_range.mpr
      (mem_activeVertices.mp (dataA.reps_processed hv)).1
  rw [hretA, numeric_card_eq hSrange, numeric_card_eq R.I.hA] at hshrink
  exact ⟨σ₂, Rnum, Snum,
    Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource.partitionCost
      x I.ord n W.card,
    Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource.partitionCost
      x repsB' n Rnum.card,
    by simpa only [hIσ] using runPart,
    hcountA₂, hcountB₂,
    by simpa only [hIA] using hactiveA₂,
    by simpa only [hIB] using hactiveB₂,
    hshrink, hcost⟩

/-- Either retry failure stops the fixed source round by zeroing `acount`.
The corresponding guard costs are included in the actual `Run`. -/
lemma failed_initial_round_run {B K : ℕ} {σ τ : Env}
    (hrun : Run B completeSamplerSource σ τ K)
    (hstatus : τ.vars "initialRetryStatus" = 2 ∨
      τ.vars "initialRetryStatus" = 3)
    (hB : 3 < B) :
    Run B refinedRoundSource σ (τ.setVar "acount" 0)
      (K + (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size + 2)) := by
  have hstatusB : τ.vars "initialRetryStatus" < B := by rcases hstatus with h|h <;> omega
  have hneq : τ.vars "initialRetryStatus" ≠ 1 := by rcases hstatus with h|h <;> omega
  have hguard : (Cond.eq (.var "initialRetryStatus") (.lit 1)).evalB B τ =
      some false := by
    rw [evalB_condEq (evalB_var hstatusB) (evalB_lit (by omega : 1 < B))]
    simp [hneq]
  have hstop : Run B (.assign "acount" (.lit 0)) τ (τ.setVar "acount" 0) 2 :=
    Run.assign (evalB_lit (by omega : 0 < B))
  simpa only [refinedRoundSource, Nat.add_assoc] using
    hrun.seq (Run.ite_false hguard hstop)

lemma failed_repair_round_run {B K : ℕ} {σ τ : Env}
    (hrun : Run B completeSamplerSource σ τ K)
    (hinitial : τ.vars "initialRetryStatus" = 1)
    (hstatus : τ.vars "repairRetryStatus" = 2 ∨
      τ.vars "repairRetryStatus" = 3)
    (hB : 3 < B) :
    Run B refinedRoundSource σ (τ.setVar "acount" 0)
      (K + (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size +
        (1 + (Cond.eq (.var "repairRetryStatus") (.lit 1)).size + 2))) := by
  have hstatusB : τ.vars "repairRetryStatus" < B := by rcases hstatus with h|h <;> omega
  have hneq : τ.vars "repairRetryStatus" ≠ 1 := by rcases hstatus with h|h <;> omega
  have hguard₁ : (Cond.eq (.var "initialRetryStatus") (.lit 1)).evalB B τ =
      some true := by
    rw [evalB_condEq (evalB_var (by rw [hinitial]; omega :
      τ.vars "initialRetryStatus" < B)) (evalB_lit (by omega : 1 < B))]
    simp [hinitial]
  have hguard₂ : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB B τ =
      some false := by
    rw [evalB_condEq (evalB_var hstatusB) (evalB_lit (by omega : 1 < B))]
    simp [hneq]
  have hstop : Run B (.assign "acount" (.lit 0)) τ (τ.setVar "acount" 0) 2 :=
    Run.assign (evalB_lit (by omega : 0 < B))
  simpa only [refinedRoundSource, Nat.add_assoc] using
    hrun.seq (Run.ite_true hguard₁ (Run.ite_false hguard₂ hstop))

private lemma scan_setFlag_length {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range n) :
    (scanList (setFlag A) 0 n).length = A.card := by
  have hset : (scanList (setFlag A) 0 n).toFinset = A := by
    ext i
    constructor
    · intro hi
      have hm := mem_scanList.mp (List.mem_toFinset.mp hi)
      simpa [setFlag] using hm.2.2
    · intro hi
      apply List.mem_toFinset.mpr
      exact mem_scanList.mpr ⟨by omega,
        by simpa using Finset.mem_range.mp (hA hi), by simp [setFlag, hi]⟩
  have hn := scanList_nodup (setFlag A) 0 n
  calc
    _ = (scanList (setFlag A) 0 n).toFinset.card :=
      (List.toFinset_card_of_nodup hn).symm
    _ = A.card := by rw [hset]

/-- Syntax check for a scratch array written only with Boolean literals. -/
def onlyBitStores (name : String) : Com → Prop
  | .skip => True
  | .assign _ _ => True
  | .store a _ e => a ≠ name ∨ e = .lit 0 ∨ e = .lit 1
  | .seq c d => onlyBitStores name c ∧ onlyBitStores name d
  | .ite _ c d => onlyBitStores name c ∧ onlyBitStores name d
  | .while _ c => onlyBitStores name c
  | .read _ => True
  | .write _ => True

def arrayBits (σ : Env) (name : String) : Prop :=
  ∀ v ∈ σ.arrs name, v ≤ 1

private lemma onlyBitStores_preserves_step {B K : ℕ} {c : Com} {σ τ : Env}
    (h : BigStepB B c σ τ K) {name : String}
    (hsafe : onlyBitStores name c) (hbits : arrayBits σ name) :
    arrayBits τ name := by
  induction h with
  | skip => exact hbits
  | assign _ => exact hbits
  | @store σ a i e k v hi he hk =>
      by_cases ha : a = name
      · subst a
        have hv : v ≤ 1 := by
          rcases hsafe with hne | hzero | hone
          · exact False.elim (hne rfl)
          · subst e; have := (evalB_lit_iff.mp he).1; omega
          · subst e; have := (evalB_lit_iff.mp he).1; omega
        intro x hx
        simp only [Env.setArr] at hx
        simp only [↓reduceIte] at hx
        rcases List.mem_or_eq_of_mem_set hx with hold | rfl
        · exact hbits x hold
        · exact hv
      · simpa [arrayBits, Env.setArr, show name ≠ a from Ne.symm ha] using hbits
  | seq _ _ ih₁ ih₂ => exact ih₂ hsafe.2 (ih₁ hsafe.1 hbits)
  | ite_true _ _ ih => exact ih hsafe.1 hbits
  | ite_false _ _ ih => exact ih hsafe.2 hbits
  | while_true _ _ _ ihbody ihloop =>
      exact ihloop hsafe (ihbody hsafe hbits)
  | while_false _ => exact hbits
  | read _ => exact hbits
  | write _ => exact hbits

lemma onlyBitStores_preserves {B K : ℕ} {c : Com} {σ τ : Env}
    (h : Run B c σ τ K) {name : String}
    (hsafe : onlyBitStores name c) (hbits : arrayBits σ name) :
    arrayBits τ name := by
  obtain ⟨_, _, hstep⟩ := h
  exact onlyBitStores_preserves_step hstep hsafe hbits

private lemma partitionA_onlyBitStores :
    onlyBitStores "nextA"
      (partition "activeA" "repsB" "nextBCount" "classA"
        "repsA" "nextA" "repA" "nextACount") := by
  simp [onlyBitStores, partition, seqs, clearArray, initPartition,
    refineOne, refineMarkBody, inc]

lemma partitionB_onlyBitStores :
    onlyBitStores "nextB"
      (partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount") := by
  simp [onlyBitStores, partition, seqs, clearArray, initPartition,
    refineOne, refineMarkBody, inc]

/-- All sampler workspace needed by the next round survives the two partition
passes and the chronological commit; only the active arrays change. -/
structure NextFrame (n Q bufferCap targetCap : ℕ) (x : List ℕ)
    (σ : Env) (nextA nextB : ℕ → ℕ) : Prop where
  hn : σ.vars "n" = n
  hqpow : σ.vars "qpow" = Q
  hactiveA : σ.arrs "activeA" = arrOf n nextA
  hactiveB : σ.arrs "activeB" = arrOf n nextB
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htgt : σ.arrs "tgt" = arrOf targetCap (target x)
  hdrawDomain : (σ.arrs "drawDomain").length = n
  hkey0 : (σ.arrs "key0").length = n
  hsampleDraws : (σ.arrs "sampleDraws").length = bufferCap
  htrialActive : σ.arrs "trialActive" = arrOf n (fun _ => 0)
  htrialRowMarks : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0)
  htrialDesiredMarks : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0)
  hrepairBMarks : σ.arrs "repairBMarks" = arrOf n (fun _ => 0)
  hrepairRMarks : σ.arrs "repairRMarks" = arrOf n (fun _ => 0)
  htrialRowList : (σ.arrs "trialRowList").length = n
  htrialDesiredList : (σ.arrs "trialDesiredList").length = n
  htrialDiffList : (σ.arrs "trialDiffList").length = n
  hrepairBList : (σ.arrs "repairBList").length = n
  hrepairRList : (σ.arrs "repairRList").length = n

private lemma nextFrame_of_suffix
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      cost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : Lax457868Proofs.InitialSamplerRetriesSource.ReadyInput
      B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    {σ τ : Env}
    (hframe : FinalFrame R S σ)
    (hrun : Run B ((partition "activeB" "ord" "sampleCount" "classB"
      "repsB" "nextB" "repB" "nextBCount").seq
      ((partition "activeA" "repsB" "nextBCount" "classA"
        "repsA" "nextA" "repA" "nextACount").seq commitReduction)) σ τ cost)
    {nextA nextB : ℕ → ℕ}
    (ha : τ.arrs "activeA" = arrOf n nextA)
    (hb : τ.arrs "activeB" = arrOf n nextB) :
    NextFrame n Q bufferCap targetCap x τ nextA nextB := by
  rcases hframe with ⟨hn,hq,_,_,hoff,htgt,hdraw,hkey,hsample,
    htrial,hrow,hdesired,hB,hR,hrowList,hdesiredList,hdiffList,hBList,hRList⟩
  refine ⟨?_, ?_, ha, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun.frame_var "n" (by decide)]; exact hn
  · rw [hrun.frame_var "qpow" (by decide)]; exact hq
  · rw [hrun.frame_arr "off" (by decide)]; exact hoff
  · rw [hrun.frame_arr "tgt" (by decide)]; exact htgt
  · rw [hrun.frame_arr "drawDomain" (by decide)]; exact hdraw
  · rw [hrun.frame_arr "key0" (by decide)]; exact hkey
  · rw [hrun.frame_arr "sampleDraws" (by decide)]; exact hsample
  · rw [hrun.frame_arr "trialActive" (by decide)]; exact htrial
  · rw [hrun.frame_arr "trialRowMarks" (by decide)]; exact hrow
  · rw [hrun.frame_arr "trialDesiredMarks" (by decide)]; exact hdesired
  · rw [hrun.frame_arr "repairBMarks" (by decide)]; exact hB
  · rw [hrun.frame_arr "repairRMarks" (by decide)]; exact hR
  · rw [hrun.frame_arr "trialRowList" (by decide)]; exact hrowList
  · rw [hrun.frame_arr "trialDesiredList" (by decide)]; exact hdesiredList
  · rw [hrun.frame_arr "trialDiffList" (by decide)]; exact hdiffList
  · rw [hrun.frame_arr "repairBList" (by decide)]; exact hBList
  · rw [hrun.frame_arr "repairRList" (by decide)]; exact hRList


/-- The accepted partitions feed the unchanged chronological commit. The
output records the actual deletion interval and parallel representative log. -/
lemma accepted_commit_run
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      samplerCost c : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A W : Finset ℕ}
    (R : Lax457868Proofs.InitialSamplerRetriesSource.ReadyInput
      B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    (hscratch : RoundScratch n R.I.σ)
    (hnextABits : arrayBits R.I.σ "nextA")
    (hnextBBits : arrayBits R.I.σ "nextB")
    (hbounded : Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B R.I.σ)
    (hcapacity : R.I.σ.vars "removedCount" + A.card ≤ n)
    (hround : R.I.σ.vars "round" < n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    {σ : Env} (hrun : Run B completeSamplerSource R.I.σ σ samplerCost)
    (hframe : FinalFrame R S σ)
    (hord : ∃ packed : ℕ → ℕ,
      σ.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ.vars "sampleCount") packed W)
    (hcount : σ.vars "sampleCount" = W.card)
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily
        (activeVertices n R.I.activeB)
        (fun b => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G b ∩ A))
      (A : Set ℕ) (W : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (hC : (activeVertices n R.I.activeB).Nonempty) :
    ∃ σ₂ σ₃ : Env, ∃ Rnum Snum : Finset ℕ,
      ∃ nextA nextB repA rem remRep : ℕ → ℕ,
      ∃ partCostB partCostA : ℕ,
      ∃ currentA : ℕ, ∃ labelA repClassA repsA repB : ℕ → ℕ,
      Run B ((partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount").seq
        ((partition "activeA" "repsB" "nextBCount" "classA"
          "repsA" "nextA" "repA" "nextACount").seq commitReduction))
        σ σ₃ (partCostB + (partCostA + 80 * (n + 1))) ∧
      Run B ((partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount").seq
        (partition "activeA" "repsB" "nextBCount" "classA"
          "repsA" "nextA" "repA" "nextACount"))
        σ σ₂ (partCostB + partCostA) ∧
      Run B commitReduction σ₂ σ₃ (80 * (n + 1)) ∧
      σ₃.vars "round" = R.I.σ.vars "round" + 1 ∧
      σ₃.vars "acount" = Snum.card ∧
      σ₃.arrs "activeA" = arrOf n nextA ∧
      σ₃.arrs "activeB" = arrOf n nextB ∧
      NextFrame n Q bufferCap targetCap x σ₃ nextA nextB ∧
      σ₂.arrs "nextA" = arrOf n nextA ∧
      σ₂.arrs "nextB" = arrOf n nextB ∧
      σ₂.arrs "repA" = arrOf n repA ∧
      (∀ i < n, nextA i ≤ 1) ∧
      (∀ i < n, nextB i ≤ 1) ∧
      σ₃.arrs "activeA" = arrOf n (setFlag Snum) ∧
      σ₃.arrs "activeB" = arrOf n (setFlag Rnum) ∧
      σ₃.vars "removedCount" = R.I.σ.vars "removedCount" +
        (Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedList
          (setFlag A) nextA 0 n).length ∧
      σ₃.arrs "roundStart" = (σ₂.arrs "roundStart").set
        (R.I.σ.vars "round") (R.I.σ.vars "removedCount") ∧
      σ₃.arrs "roundEnd" = (σ₂.arrs "roundEnd").set
        (R.I.σ.vars "round")
        (R.I.σ.vars "removedCount" +
          (Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedList
            (setFlag A) nextA 0 n).length) ∧
      σ₃.arrs "removed" = arrOf n rem ∧
      σ₃.arrs "removedRep" = arrOf n remRep ∧
      (∀ j < R.I.σ.vars "removedCount", rem j = view σ₂ "removed" j) ∧
      (∀ j < (Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedList
          (setFlag A) nextA 0 n).length,
        rem (R.I.σ.vars "removedCount" + j) =
          (Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedList
            (setFlag A) nextA 0 n).getD j 0) ∧
      (∀ j < R.I.σ.vars "removedCount", remRep j = view σ₂ "removedRep" j) ∧
      (∀ j < (Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedList
          (setFlag A) nextA 0 n).length,
        remRep (R.I.σ.vars "removedCount" + j) =
          (Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedRepList
            (setFlag A) nextA repA 0 n).getD j 0) ∧
      2 * Snum.card ≤ A.card + 2 * c ^ 2 ∧
      partCostB + partCostA ≤ 1800 * (x.length + 1) ∧
      Lax457868Proofs.ReusedOriginal.Construction.RepresentativeMath.RepData
        n currentA n (setFlag A) labelA repClassA repsA nextA Snum ∧
      Nonempty (Lax457868Proofs.ReusedOriginal.Construction.PartitionResult.ConcreteTracePartition
        G (setFlag A) (finSetAsSet Rnum) Snum repA) ∧
      Nonempty (Lax457868Proofs.ReusedOriginal.Construction.PartitionResult.ConcreteTracePartition
        G R.I.activeB (finSetAsSet W) Rnum repB) := by
  classical
  obtain ⟨I, hIσ, hIA, hIB⟩ :=
    partition_input_of_sampler R S hscratch hrun hframe hord hcount hsample hC
  obtain ⟨σ₁, σ₂, currentB, currentA, Rnum, Snum,
    labelB, repClassB, repsB', nextB', repB', labelA, repClassA,
    repsA', nextA', repA', hB, hA, runB, runA, runPart,
    dataB, dataA, hcountB₁, hcountA₂, hcountB₂,
    hactiveB₂, hrepsB₂, hrepB₂, hnextB₂,
    hactiveA₂, hrepsA₂, hrepA₂, hnextA₂,
    contraction, hmapB, hmapA, hretB, hretA, hcost⟩ :=
      runVerifiedRoundPartitions I
  have hWsub : W ⊆ A := by
    intro v hv; exact hsample.2.2.1 hv
  have hCsub : activeVertices n R.I.activeB ⊆ Finset.range n := by
    intro v hv; exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
  have hsampleFin := sample_fin_of_numeric R.I.hA hWsub hCsub hsample
  have hshrink :=
    Lax457868Proofs.RefinedContraction.graph_traceContraction_size_bound
      hG hc (finsetOfNumeric A)
      (finsetOfNumeric (activeVertices n R.I.activeB))
      (finsetOfNumeric W) hsampleFin contraction
  have hSrange : Snum ⊆ Finset.range n := by
    intro v hv
    exact Finset.mem_range.mpr
      (mem_activeVertices.mp (dataA.reps_processed hv)).1
  rw [hretA, numeric_card_eq hSrange, numeric_card_eq R.I.hA] at hshrink
  have hnextABitsσ : arrayBits σ "nextA" := by
    unfold arrayBits
    rw [hrun.frame_arr "nextA" (by decide)]
    exact hnextABits
  have hnextABits₁ : arrayBits σ₁ "nextA" := by
    unfold arrayBits
    rw [runB.frame_arr "nextA" (by decide)]
    rw [hIσ]
    exact hnextABitsσ
  have hnextABits₂ := onlyBitStores_preserves runA
    partitionA_onlyBitStores hnextABits₁
  have hnextAValues : ∀ i < n, nextA' i ≤ 1 := by
    intro i hi
    apply hnextABits₂
    rw [hnextA₂]
    exact List.mem_of_getElem? (getElem?_arrOf nextA' hi)
  have hnextBBitsσ : arrayBits σ "nextB" := by
    unfold arrayBits
    rw [hrun.frame_arr "nextB" (by decide)]
    exact hnextBBits
  have hnextBBits₁ := onlyBitStores_preserves runB
    partitionB_onlyBitStores (by rw [hIσ]; exact hnextBBitsσ)
  have hnextBBits₂ : arrayBits σ₂ "nextB" := by
    unfold arrayBits
    rw [runA.frame_arr "nextB" (by decide)]
    exact hnextBBits₁
  have hnextBValues : ∀ i < n, nextB' i ≤ 1 := by
    intro i hi
    apply hnextBBits₂
    rw [hnextB₂]
    exact List.mem_of_getElem? (getElem?_arrOf nextB' hi)
  have hnextAFlag : ∀ i < n, nextA' i = setFlag Snum i := by
    intro i hi
    by_cases h : i ∈ Snum
    · have hone := (dataA.out_mem i hi).2 h
      simp [setFlag, h, hone]
    · have hne : nextA' i ≠ 1 := fun he => h ((dataA.out_mem i hi).1 he)
      have hzero : nextA' i = 0 := by have := hnextAValues i hi; omega
      simp [setFlag, h, hzero]
  have hnextBFlag : ∀ i < n, nextB' i = setFlag Rnum i := by
    intro i hi
    by_cases h : i ∈ Rnum
    · have hone := (dataB.out_mem i hi).2 h
      simp [setFlag, h, hone]
    · have hne : nextB' i ≠ 1 := fun he => h ((dataB.out_mem i hi).1 he)
      have hzero : nextB' i = 0 := by have := hnextBValues i hi; omega
      simp [setFlag, h, hzero]
  let scratch₂ := (hscratch.frame hrun).frame (by simpa only [hIσ] using runPart)
  have hn₂ : σ₂.vars "n" = n := by
    rw [runPart.frame_var "n" (by decide), hIσ]
    exact hframe.1
  have hbase₂ : σ₂.vars "removedCount" = R.I.σ.vars "removedCount" := by
    rw [runPart.frame_var "removedCount" (by decide), hIσ,
      hrun.frame_var "removedCount" (by decide)]
  have hround₂ : σ₂.vars "round" = R.I.σ.vars "round" := by
    rw [runPart.frame_var "round" (by decide), hIσ,
      hrun.frame_var "round" (by decide)]
  have hcapacity₂ : R.I.σ.vars "removedCount" +
      (Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedList
        (setFlag A) nextA' 0 n).length ≤ n := by
    have hscan := scan_setFlag_length R.I.hA
    have hle :=
      Lax457868Proofs.ReusedOriginal.Construction.RecordRemovedSource.removedList_length_le_scanList
        (setFlag A) nextA' 0 n
    omega
  have hbound₂ : Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B σ₂ :=
    Lax457868Proofs.RefinedRecordedCommit.run_preserves runPart
      (by rw [hIσ]; exact
        Lax457868Proofs.RefinedRecordedCommit.run_preserves hrun hbounded)
  have hroundB : R.I.σ.vars "round" + 1 < B := by have := R.hnB; omega
  obtain ⟨σ₃, rem, remRep, hcommit, hactA₃, hactB₃,
    hround₃, hacount₃, hremovedCount₃, hstart₃, hend₃,
    hrem₃, hrep₃, hprefix, hsuffix, hprefixRep, hsuffixRep,
    _, _⟩ :=
      Lax457868Proofs.RefinedRecordedCommit.commitReduction_run
        hn₂ hbase₂ hround₂
        hactiveA₂ hactiveB₂ hnextA₂ hnextB₂ hrepA₂
        (array_shape scratch₂.removed) (array_shape scratch₂.removedRep)
        (by rw [scratch₂.roundStart]; exact hround)
        (by rw [scratch₂.roundEnd]; exact hround)
        (by have := R.hnB; omega) hroundB hbound₂
        (by simpa only [hIA] using hcapacity₂)
  have hactiveAFlag : σ₃.arrs "activeA" = arrOf n (setFlag Snum) :=
    hactA₃.trans (arrOf_congr hnextAFlag)
  have hactiveBFlag : σ₃.arrs "activeB" = arrOf n (setFlag Rnum) :=
    hactB₃.trans (arrOf_congr hnextBFlag)
  have hsource : Run B ((partition "activeB" "ord" "sampleCount" "classB"
      "repsB" "nextB" "repB" "nextBCount").seq
      ((partition "activeA" "repsB" "nextBCount" "classA"
        "repsA" "nextA" "repA" "nextACount").seq commitReduction))
      σ σ₃ (Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource.partitionCost
        x I.ord n W.card +
        (Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource.partitionCost
          x repsB' n Rnum.card + 80 * (n + 1))) := by
    rw [← hIσ]
    exact runB.seq (runA.seq hcommit)
  refine ⟨σ₂, σ₃, Rnum, Snum, nextA', nextB', repA', rem, remRep,
    _, _, currentA, labelA, repClassA, repsA', repB',
    hsource, by simpa only [hIσ] using runPart,
    hcommit, by simpa only [hround₂] using hround₃,
    hacount₃.trans hcountA₂, hactA₃, hactB₃,
    nextFrame_of_suffix R S hframe hsource hactA₃ hactB₃,
    hnextA₂, hnextB₂, hrepA₂, hnextAValues, hnextBValues,
    hactiveAFlag, hactiveBFlag,
    ?_, ?_, ?_, hrem₃, hrep₃, ?_, ?_, ?_, ?_, hshrink, hcost,
    ?_, ?_, ?_⟩
  · simpa only [hIA] using hremovedCount₃
  · simpa only [hIA] using hstart₃
  · simpa only [hIA] using hend₃
  · exact hprefix
  · simpa only [hIA] using hsuffix
  · exact hprefixRep
  · simpa only [hIA] using hsuffixRep
  · simpa only [hIA] using dataA
  · exact ⟨by simpa only [hIA] using hA⟩
  · exact ⟨by simpa only [hIB] using hB⟩

/-- The two acceptance guards execute the exact partition/commit suffix after
the concrete sampler. All three charges are added in source order. -/
lemma accepted_round_run
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      samplerCost c : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A W : Finset ℕ}
    (R : Lax457868Proofs.InitialSamplerRetriesSource.ReadyInput
      B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    (hscratch : RoundScratch n R.I.σ)
    (hnextABits : arrayBits R.I.σ "nextA")
    (hnextBBits : arrayBits R.I.σ "nextB")
    (hbounded : Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B R.I.σ)
    (hcapacity : R.I.σ.vars "removedCount" + A.card ≤ n)
    (hround : R.I.σ.vars "round" < n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    {σ : Env} (hrun : Run B completeSamplerSource R.I.σ σ samplerCost)
    (hframe : FinalFrame R S σ)
    (hstatus₁ : σ.vars "initialRetryStatus" = 1)
    (hstatus₂ : σ.vars "repairRetryStatus" = 1)
    (hord : ∃ packed : ℕ → ℕ,
      σ.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ.vars "sampleCount") packed W)
    (hcount : σ.vars "sampleCount" = W.card)
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily
        (activeVertices n R.I.activeB)
        (fun b => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G b ∩ A))
      (A : Set ℕ) (W : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (hC : (activeVertices n R.I.activeB).Nonempty) :
    ∃ σout : Env, ∃ Snum : Finset ℕ,
      ∃ partCostB partCostA : ℕ,
      Run B refinedRoundSource R.I.σ σout
        (samplerCost +
          (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size +
            (1 + (Cond.eq (.var "repairRetryStatus") (.lit 1)).size +
              (partCostB + (partCostA + 80 * (n + 1)))))) ∧
      σout.vars "round" = R.I.σ.vars "round" + 1 ∧
      σout.vars "acount" = Snum.card ∧
      2 * Snum.card ≤ A.card + 2 * c ^ 2 ∧
      partCostB + partCostA ≤ 1800 * (x.length + 1) := by
  obtain ⟨σ₂, σ₃, Rnum, Snum, nextA, nextB, repA, rem, remRep,
    partCostB, partCostA, currentA, labelA, repClassA, repsA, repB,
    hsuffix, _, _, hround₃, hacount₃,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hshrink, hcost, _, _, _⟩ :=
    accepted_commit_run R S hscratch hnextABits hnextBBits hbounded hcapacity hround hG hc
      hrun hframe hord hcount hsample hC
  have hB : 1 < B := R.I.honeB
  have hguard₁ : (Cond.eq (.var "initialRetryStatus") (.lit 1)).evalB B σ =
      some true := by
    rw [evalB_condEq (evalB_var (by rw [hstatus₁]; omega :
      σ.vars "initialRetryStatus" < B)) (evalB_lit (by omega : 1 < B))]
    simp [hstatus₁]
  have hguard₂ : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB B σ =
      some true := by
    rw [evalB_condEq (evalB_var (by rw [hstatus₂]; omega :
      σ.vars "repairRetryStatus" < B)) (evalB_lit (by omega : 1 < B))]
    simp [hstatus₂]
  have hinner := Run.ite_true (d := .assign "acount" (.lit 0)) hguard₂ hsuffix
  have hfull := hrun.seq
    (Run.ite_true (d := .assign "acount" (.lit 0)) hguard₁ hinner)
  exact ⟨σ₃, Snum, partCostB, partCostA,
    by simpa only [refinedRoundSource] using hfull,
    hround₃, hacount₃, hshrink, hcost⟩

private lemma getD_map_of_lt {α β : Type*} (f : α → β) (xs : List α)
    (i : ℕ) (d : α) (e : β) (hi : i < xs.length) :
    (xs.map f).getD i e = f (xs.getD i d) := by
  rw [List.getD_eq_getElem? xs d ⟨i, hi⟩]
  rw [List.getD_eq_getElem? (xs.map f) e ⟨i, by simpa using hi⟩]
  simp

/-- Append the accepted reduction to the genuine pre-round stored history,
using the exact interval and representative values written by the commit. -/
lemma accepted_commit_stored_run
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      samplerCost c : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A W : Finset ℕ}
    (R : Lax457868Proofs.InitialSamplerRetriesSource.ReadyInput
      B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    (hscratch : RoundScratch n R.I.σ)
    (hnextABits : arrayBits R.I.σ "nextA")
    (hnextBBits : arrayBits R.I.σ "nextB")
    (hbounded : Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B R.I.σ)
    (hstore : Stored G k R.I.σ)
    (hcapacity : R.I.σ.vars "removedCount" + A.card ≤ n)
    (hround : R.I.σ.vars "round" < n)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c)
    {σ : Env} (hrun : Run B completeSamplerSource R.I.σ σ samplerCost)
    (hframe : FinalFrame R S σ)
    (hord : ∃ packed : ℕ → ℕ,
      σ.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ.vars "sampleCount") packed W)
    (hcount : σ.vars "sampleCount" = W.card)
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily
        (activeVertices n R.I.activeB)
        (fun b => Lax457868Proofs.ExceptionPhaseSource.numericNeighborhood G b ∩ A))
      (A : Set ℕ) (W : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (hC : (activeVertices n R.I.activeB).Nonempty) :
    ∃ σ₂ σ₃ : Env, ∃ Rnum Snum : Finset ℕ,
      ∃ nextA nextB repA repB : ℕ → ℕ,
      ∃ partCostB partCostA : ℕ,
      Run B ((partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount").seq
        ((partition "activeA" "repsB" "nextBCount" "classA"
          "repsA" "nextA" "repA" "nextACount").seq commitReduction))
        σ σ₃ (partCostB + (partCostA + 80 * (n + 1))) ∧
      Nonempty (Stored G k σ₃) ∧
      σ₃.vars "round" = R.I.σ.vars "round" + 1 ∧
      σ₃.vars "acount" = Snum.card ∧
      2 * Snum.card ≤ A.card + 2 * c ^ 2 ∧
      partCostB + partCostA ≤ 1800 * (x.length + 1) ∧
      NextFrame n Q bufferCap targetCap x σ₃ nextA nextB ∧
      σ₃.arrs "activeA" = arrOf n (setFlag Snum) ∧
      σ₃.arrs "activeB" = arrOf n (setFlag Rnum) ∧
      (∀ v ∈ σ₃.arrs "nextA", v ≤ 1) ∧
      (∀ v ∈ σ₃.arrs "nextB", v ≤ 1) ∧
      Lax457868Proofs.RefinedRecordedCommit.ValuesBounded B σ₃ ∧
      σ₃.vars "removedCount" + Snum.card ≤ n ∧
      Nonempty (ConcreteTracePartition G (setFlag A) (finSetAsSet Rnum) Snum repA) ∧
      Nonempty (ConcreteTracePartition G R.I.activeB (finSetAsSet W) Rnum repB) := by
  classical
  obtain ⟨σ₂, σ₃, Rnum, Snum, nextA, nextB, repA, rem, remRep,
    partCostB, partCostA, currentA, labelA, repClassA, repsA, repB,
    hsuffix, hpart, hcommit, hround₃, hacount₃,
    hactiveA₃, hactiveB₃, hnextFrame, hnextA₂, hnextB₂,
    hrepA₂, hbitsA, hbitsB, hactiveAFlag, hactiveBFlag,
    hremovedCount₃, hstart₃, hend₃,
    hrem₃, hrep₃, hprefix, hsuffixRem, hprefixRep, hsuffixRep,
    hshrink, hcost, dataA, ⟨partA⟩, ⟨partB⟩⟩ :=
    accepted_commit_run R S hscratch hnextABits hnextBBits hbounded hcapacity hround
      hG hc hrun hframe hord hcount hsample hC
  let hstoreσ := hstore.frame
    (hrun.frame_var "round" (by decide))
    (hrun.frame_var "removedCount" (by decide))
    (hrun.frame_arr "activeA" (by decide))
    (hrun.frame_arr "activeB" (by decide))
    (hrun.frame_arr "roundStart" (by decide))
    (hrun.frame_arr "roundEnd" (by decide))
    (hrun.frame_arr "removed" (by decide))
    (hrun.frame_arr "removedRep" (by decide))
  let hstore₂ := hstoreσ.frame
    (hpart.frame_var "round" (by decide))
    (hpart.frame_var "removedCount" (by decide))
    (hpart.frame_arr "activeA" (by decide))
    (hpart.frame_arr "activeB" (by decide))
    (hpart.frame_arr "roundStart" (by decide))
    (hpart.frame_arr "roundEnd" (by decide))
    (hpart.frame_arr "removed" (by decide))
    (hpart.frame_arr "removedRep" (by decide))
  have hbase₂ : σ₂.vars "removedCount" = R.I.σ.vars "removedCount" := by
    rw [hpart.frame_var "removedCount" (by decide),
      hrun.frame_var "removedCount" (by decide)]
  have hround₂ : σ₂.vars "round" = R.I.σ.vars "round" := by
    rw [hpart.frame_var "round" (by decide),
      hrun.frame_var "round" (by decide)]
  have hn₂ : σ₂.vars "n" = n := by
    rw [hpart.frame_var "n" (by decide)]
    exact hframe.1
  have hactiveA₂ : σ₂.arrs "activeA" = arrOf n (setFlag A) := by
    rw [hpart.frame_arr "activeA" (by decide)]
    exact hframe.2.2.1
  have hactiveB₂ : σ₂.arrs "activeB" = arrOf n R.I.activeB := by
    rw [hpart.frame_arr "activeB" (by decide)]
    exact hframe.2.2.2.1
  have hscratch₂ := (hscratch.frame hrun).frame hpart
  have hbounded₂ := Lax457868Proofs.RefinedRecordedCommit.run_preserves hpart
    (Lax457868Proofs.RefinedRecordedCommit.run_preserves hrun hbounded)
  have hcap₂ : R.I.σ.vars "removedCount" +
      (removedList (setFlag A) nextA 0 n).length ≤ n := by
    have hlen := scan_setFlag_length R.I.hA
    have hle := removedList_length_le_scanList (setFlag A) nextA 0 n
    omega
  have hrepNew : ∀ i < n, (setFlag A) i = 1 → nextA i = 0 → repA i < n := by
    intro i hi hactive _
    exact partA.rep_lt hi hactive
  obtain ⟨σb, remb, repb, hcommitB, harrRemB, harrRepB, hlogB⟩ :=
    Lax457868Proofs.RefinedRecordedCommit.commitReduction_run_logValues_lt
      hn₂ hbase₂ hround₂ hactiveA₂ hactiveB₂ hnextA₂ hnextB₂ hrepA₂
      (array_shape hscratch₂.removed) (array_shape hscratch₂.removedRep)
      (by rw [hscratch₂.roundStart]; exact hround₂ ▸ hround)
      (by rw [hscratch₂.roundEnd]; exact hround₂ ▸ hround)
      (by have := R.hnB; omega)
      (by have := R.hnB; omega) hbounded₂ hcap₂
      hstore₂.removedBound hstore₂.representativeBound hrepNew
  have hσb : σb = σ₃ := by
    obtain ⟨_, _, hb⟩ := hcommitB
    obtain ⟨_, _, hc⟩ := hcommit
    exact (BigStep.unique hb.bigStep hc.bigStep).1
  subst σb
  have hlogBound : ∀ i < n,
      view σ₃ "removed" i < n ∧ view σ₃ "removedRep" i < n := by
    intro i hi
    have hh := hlogB i hi
    exact ⟨by simpa [view] using hh.1, by simpa [view] using hh.2⟩
  let round := R.I.σ.vars "round"
  let base := R.I.σ.vars "removedCount"
  let dlen := (removedList (setFlag A) nextA 0 n).length
  let boundary' := Function.update hstore₂.boundary (round + 1) (base + dlen)
  let deleted := removedFinList (n := n) (setFlag A) nextA
  let representative := partA.partition.representative
  have hdeletedLen : deleted.length = dlen := by
    dsimp [deleted, dlen]
    rw [← List.length_map Fin.val, removedFinList_map_val]
  have hbase : hstore₂.boundary round = base := by
    rw [show round = σ₂.vars "round" from hround₂.symm]
    rw [hstore₂.used, hbase₂]
  have hstart : boundary' round = base := by
    simpa [boundary', round, base,
      show round ≠ round + 1 by omega] using hbase
  have hend : boundary' (round + 1) = base + dlen := by
    simp [boundary', round, base]
  have hcount : boundary' (round + 1) - boundary' round = dlen := by
    rw [hend, hstart]
    simp [dlen]
  have hlogSlice :
      logSlice (view σ₃ "removed") base dlen = deleted.map Fin.val := by
    have hget : ∀ j < dlen,
        view σ₃ "removed" (base + j) =
          (removedList (setFlag A) nextA 0 n).getD j 0 := by
      intro j hj
      have hi : base + j < n := by omega
      rw [view_of_array hrem₃ hi]
      exact hsuffixRem j hj
    rw [logSlice_eq_of_stored_getD hget]
    exact (removedFinList_map_val (setFlag A) nextA).symm
  have hOldA : hstore₂.A round =
      ({v : Fin n | (setFlag A) v.val = 1} : Set (Fin n)) := by
    rw [show round = σ₂.vars "round" from hround₂.symm]
    rw [hstore₂.currentA]
    ext v
    change view σ₂ "activeA" v.val = 1 ↔ (setFlag A) v.val = 1
    rw [view_of_array hactiveA₂ v.isLt]
  have hOldB : hstore₂.C round =
      ({v : Fin n | R.I.activeB v.val = 1} : Set (Fin n)) := by
    rw [show round = σ₂.vars "round" from hround₂.symm]
    rw [hstore₂.currentC]
    ext v
    change view σ₂ "activeB" v.val = 1 ↔ R.I.activeB v.val = 1
    rw [view_of_array hactiveB₂ v.isLt]
  have hNewA : ({v : Fin n | view σ₃ "activeA" v.val = 1} : Set (Fin n)) =
      finSetAsSet Snum := by
    ext v
    change view σ₃ "activeA" v.val = 1 ↔ v.val ∈ Snum
    rw [view_of_array hactiveA₃ v.isLt]
    exact dataA.out_mem v.val v.isLt
  have hNewB : ({v : Fin n | view σ₃ "activeB" v.val = 1} : Set (Fin n)) =
      finSetAsSet Rnum := by
    ext v
    change view σ₃ "activeB" v.val = 1 ↔ v.val ∈ Rnum
    rw [view_of_array hactiveBFlag v.isLt]
    simp [setFlag]
  have hWA : W ⊆ A := by
    intro v hv; exact hsample.2.2.1 hv
  have hCsub : activeVertices n R.I.activeB ⊆ Finset.range n := by
    intro v hv; exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
  have hsampleFin := sample_fin_of_numeric R.I.hA hWA hCsub hsample
  have hAset : ({v : Fin n | (setFlag A) v.val = 1} : Set (Fin n)) =
      ((finsetOfNumeric A : Finset (Fin n)) : Set (Fin n)) := by
    ext v; simp [finsetOfNumeric, setFlag]
  have hBset : ({v : Fin n | R.I.activeB v.val = 1} : Set (Fin n)) =
      ((finsetOfNumeric (activeVertices n R.I.activeB) : Finset (Fin n)) : Set (Fin n)) := by
    ext v; simp [finsetOfNumeric, activeVertices, mem_activeVertices]
  have hWset : (finSetAsSet W : Set (Fin n)) =
      ((finsetOfNumeric W : Finset (Fin n)) : Set (Fin n)) := by
    ext v; simp [finSetAsSet, finsetOfNumeric]
  have hRset : (finSetAsSet Rnum : Set (Fin n)) =
      ((finsetOfNumeric Rnum : Finset (Fin n)) : Set (Fin n)) := by
    ext v; simp [finSetAsSet, finsetOfNumeric]
  have hSset : (finSetAsSet Snum : Set (Fin n)) =
      ((finsetOfNumeric Snum : Finset (Fin n)) : Set (Fin n)) := by
    ext v; simp [finSetAsSet, finsetOfNumeric]
  have hsourceB : TracePartition G
      ((finsetOfNumeric (activeVertices n R.I.activeB) : Finset (Fin n)) : Set (Fin n))
      ((finsetOfNumeric W : Finset (Fin n)) : Set (Fin n))
      ((finsetOfNumeric Rnum : Finset (Fin n)) : Set (Fin n)) := by
    simpa only [← hBset, ← hWset, ← hRset] using partB.partition
  let hsourceA : TracePartition G
      ((finsetOfNumeric A : Finset (Fin n)) : Set (Fin n))
      ((finsetOfNumeric Rnum : Finset (Fin n)) : Set (Fin n))
      ((finsetOfNumeric Snum : Finset (Fin n)) : Set (Fin n)) := by
    exact {
      representative := partA.partition.representative
      representative_mem := by simpa only [← hAset, ← hSset] using partA.partition.representative_mem
      same_trace := by simpa only [← hAset, ← hRset] using partA.partition.same_trace
      reps_mem := by simpa only [← hAset, ← hSset] using partA.partition.reps_mem
      reps_separated := by simpa only [← hRset, ← hSset] using partA.partition.reps_separated
    }
  have hrepEq : hsourceA.representative = partA.partition.representative := rfl
  have hremovedEnum : Enumerates
      (hstore₂.A round \ ({v : Fin n | view σ₃ "activeA" v.val = 1} : Set (Fin n)))
      deleted := by
    rw [hOldA, hNewA]
    exact removedFinList_enumerates hbitsA dataA
  have hReduction {small : List (Fin n)}
      (hsmall : Enumerates
        ({v : Fin n | view σ₃ "activeA" v.val = 1} : Set (Fin n)) small) :
      Nonempty (Reduction G k (hstore₂.A round) (hstore₂.C round)
        ({v : Fin n | view σ₃ "activeA" v.val = 1} : Set (Fin n))
        ({v : Fin n | view σ₃ "activeB" v.val = 1} : Set (Fin n))
        small (restoreAfter representative small deleted)) := by
    have hsmall' : Enumerates
        ((finsetOfNumeric Snum : Finset (Fin n)) : Set (Fin n)) small := by
      simpa only [hNewA, hSset] using hsmall
    have hremoved' : Enumerates
        (((finsetOfNumeric A : Finset (Fin n)) : Set (Fin n)) \
          ((finsetOfNumeric Snum : Finset (Fin n)) : Set (Fin n))) deleted := by
      simpa only [hOldA, hAset, hNewA, hSset] using hremovedEnum
    have hred :=
      Lax457868Proofs.VerifiedReconstructionBridge.restoreAfter_reduction
        (finsetOfNumeric A)
        (finsetOfNumeric (activeVertices n R.I.activeB))
        (finsetOfNumeric W) (finsetOfNumeric Snum) (finsetOfNumeric Rnum)
        hsampleFin (by
          intro v hv
          have hw : v.val ∈ W := by simpa [finsetOfNumeric] using hv
          simpa [finsetOfNumeric] using hWA hw)
        hsourceB hsourceA small deleted hsmall' hremoved'
    simpa only [hOldA, hAset, hOldB, hBset, hNewA, hSset,
      hNewB, hRset, representative, hrepEq] using hred
  have hstep : RecordedStep G k round (hstore₂.A round) (hstore₂.C round)
      {v : Fin n | view σ₃ "activeA" v.val = 1}
      {v : Fin n | view σ₃ "activeB" v.val = 1}
      boundary' (view σ₃ "removed") (view σ₃ "removedRep") := by
    refine ⟨deleted, representative, ?_, ?_, ?_, ?_, ?_⟩
    · have hlen : boundary' (round + 1) - base = dlen := by
        rw [← hstart, hcount]
      rw [hstart, hlen]
      simpa [deleted, dlen] using hlogSlice.symm
    · intro i hi
      have hi' : i < dlen := by simpa [hcount] using hi
      let zeroFin : Fin n := ⟨0, by omega⟩
      have hgetNum : (deleted.getD i zeroFin).val =
          (removedList (setFlag A) nextA 0 n).getD i 0 := by
        calc
          (deleted.getD i zeroFin).val =
              (deleted.map Fin.val).getD i 0 := by
            symm
            exact getD_map_of_lt Fin.val deleted i zeroFin 0 (by
              simpa [hdeletedLen] using hi')
          _ = (removedList (setFlag A) nextA 0 n).getD i 0 := by
            simpa [deleted] using congrArg (fun l : List ℕ => l.getD i 0)
              (removedFinList_map_val (n := n) (setFlag A) nextA)
      have hgetRemoved : view σ₃ "removed" (base + i) = (deleted.getD i zeroFin).val := by
        have hidx : base + i < n := by omega
        rw [view_of_array hrem₃ hidx, hsuffixRem i hi', hgetNum]
      have hgetRep : view σ₃ "removedRep" (base + i) =
          (removedRepList (setFlag A) nextA repA 0 n).getD i 0 := by
        have hidx : base + i < n := by omega
        rw [view_of_array hrep₃ hidx, hsuffixRep i hi']
      rw [hstart, hgetRemoved, numericRepresentative_val, hgetRep]
      have hmap := removedFinList_concrete_representative_map (n := n)
        (active := setFlag A) (next := nextA) (repOf := repA) partA
      have hpoint : (representative (deleted.getD i zeroFin)).val =
          (removedRepList (setFlag A) nextA repA 0 n).getD i 0 := by
        calc
          (representative (deleted.getD i zeroFin)).val =
              (deleted.map (fun v => (representative v).val)).getD i 0 := by
            symm
            exact getD_map_of_lt (fun v => (representative v).val) deleted i zeroFin 0
              (by simpa [hdeletedLen] using hi')
          _ = (removedRepList (setFlag A) nextA repA 0 n).getD i 0 := by
            simpa [deleted] using congrArg (fun l : List ℕ => l.getD i 0) hmap
      exact hpoint
    · exact hremovedEnum
    · intro v hv
      have hmem := mem_removedFinList.mp hv
      have hactive : (setFlag A) v.val = 1 :=
        (Lax457868Proofs.ReusedOriginal.Construction.ActiveBookkeeping.mem_removedList.mp hmem).2.2.1
      have hrepmem := partA.partition.representative_mem v hactive
      have hS : (representative v).val ∈ Snum := by
        simpa [representative, finSetAsSet] using hrepmem
      change view σ₃ "activeA" (representative v).val = 1
      rw [view_of_array hactiveA₃ (representative v).isLt]
      exact (dataA.out_mem (representative v).val (representative v).isLt).2 hS
    · intro small hsmall
      exact hReduction hsmall
  have hremovedPrefix : ∀ i < σ₂.vars "removedCount",
      view σ₃ "removed" i = view σ₂ "removed" i := by
    intro i hi
    have hi' : i < base := by simpa [base, ← hbase₂] using hi
    have hiN : i < n := by
      have hcap := hstore₂.capacity (σ₂.vars "round") le_rfl
      rw [hstore₂.used] at hcap
      omega
    rw [view_of_array hrem₃ hiN, view_of_array (array_shape hscratch₂.removed) hiN,
      hprefix i hi']
  have hrepPrefix : ∀ i < σ₂.vars "removedCount",
      view σ₃ "removedRep" i = view σ₂ "removedRep" i := by
    intro i hi
    have hi' : i < base := by simpa [base, ← hbase₂] using hi
    have hiN : i < n := by
      have hcap := hstore₂.capacity (σ₂.vars "round") le_rfl
      rw [hstore₂.used] at hcap
      omega
    rw [view_of_array hrep₃ hiN, view_of_array (array_shape hscratch₂.removedRep) hiN,
      hprefixRep i hi']
  have hboundary : ∀ r' ≤ round, boundary' r' = hstore₂.boundary r' := by
    intro r' hr'
    simp [boundary', show r' ≠ round + 1 by omega]
  have hnewBoundary : boundary' (round + 1) = σ₃.vars "removedCount" := by
    simp [boundary', base, dlen, round, hremovedCount₃]
  have hstarts : ∀ r' < σ₃.vars "round", view σ₃ "roundStart" r' = boundary' r' := by
    intro r' hr'
    rw [hround₃] at hr'
    by_cases heq : r' = round
    · subst r'
      change ((σ₃.arrs "roundStart").getD (R.I.σ.vars "round") 0) =
        boundary' (R.I.σ.vars "round")
      rw [hstart₃]
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_set] using
        (by rw [hscratch₂.roundStart]; exact hround))]
      rw [List.getElem_set_self (by simpa [List.length_set] using
        (by rw [hscratch₂.roundStart]; exact hround))]
      exact hstart.symm
    · have hrOld : r' < round := by omega
      have hold := hstore₂.starts r' (by simpa [round, hround₂] using hrOld)
      have hstartView : view σ₃ "roundStart" r' = view σ₂ "roundStart" r' := by
        change (σ₃.arrs "roundStart").getD r' 0 = (σ₂.arrs "roundStart").getD r' 0
        rw [hstart₃]
        simp [List.getElem?_set, show R.I.σ.vars "round" ≠ r' by
          simpa [round] using Ne.symm heq]
      rw [hstartView, hold, hboundary r' (by omega)]
  have hends : ∀ r' < σ₃.vars "round", view σ₃ "roundEnd" r' = boundary' (r' + 1) := by
    intro r' hr'
    rw [hround₃] at hr'
    by_cases heq : r' = round
    · subst r'
      change ((σ₃.arrs "roundEnd").getD (R.I.σ.vars "round") 0) =
        boundary' (R.I.σ.vars "round" + 1)
      rw [hend₃]
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_set] using
        (by rw [hscratch₂.roundEnd]; exact hround))]
      rw [List.getElem_set_self (by simpa [List.length_set] using
        (by rw [hscratch₂.roundEnd]; exact hround))]
      exact hend.symm
    · have hrOld : r' < round := by omega
      have hold := hstore₂.ends r' (by simpa [round, hround₂] using hrOld)
      have hendView : view σ₃ "roundEnd" r' = view σ₂ "roundEnd" r' := by
        change (σ₃.arrs "roundEnd").getD r' 0 = (σ₂.arrs "roundEnd").getD r' 0
        rw [hend₃]
        simp [List.getElem?_set, show R.I.σ.vars "round" ≠ r' by
          simpa [round] using Ne.symm heq]
      rw [hendView, hold, hboundary (r' + 1) (by omega)]
  have hround₂₃ : σ₃.vars "round" = σ₂.vars "round" + 1 := by
    rw [hround₃, hround₂]
  have hboundary₂ : ∀ r' ≤ σ₂.vars "round", boundary' r' = hstore₂.boundary r' := by
    simpa [round, hround₂] using hboundary
  have hnewBoundary₂ : boundary' (σ₂.vars "round" + 1) = σ₃.vars "removedCount" := by
    simpa [round, hround₂] using hnewBoundary
  have hinc : σ₂.vars "removedCount" ≤ σ₃.vars "removedCount" := by
    rw [hremovedCount₃, hbase₂]
    omega
  have hcap : σ₃.vars "removedCount" ≤ n := by
    rw [hremovedCount₃]
    exact hcap₂
  let hstored := hstore₂.append hround₂₃ hboundary₂ hnewBoundary₂ hinc hcap
    hstarts hends hremovedPrefix hrepPrefix
    (fun i hi => (hlogBound i hi).1) (fun i hi => (hlogBound i hi).2)
    (by simpa [round, hround₂] using hstep)
  have hbits₂A : arrayBits σ₂ "nextA" := by
    have hsigma : arrayBits σ "nextA" := by
      unfold arrayBits
      rw [hrun.frame_arr "nextA" (by decide)]
      exact hnextABits
    exact onlyBitStores_preserves hpart (by
      simp [onlyBitStores, partition, seqs, clearArray, initPartition,
        refineOne, refineMarkBody, inc]) hsigma
  have hbits₂B : arrayBits σ₂ "nextB" := by
    have hsigma : arrayBits σ "nextB" := by
      unfold arrayBits
      rw [hrun.frame_arr "nextB" (by decide)]
      exact hnextBBits
    exact onlyBitStores_preserves hpart (by
      simp [onlyBitStores, partition, seqs, clearArray, initPartition,
        refineOne, refineMarkBody, inc]) hsigma
  have hbits₃A : arrayBits σ₃ "nextA" := by
    unfold arrayBits
    rw [hcommit.frame_arr "nextA" (by decide)]
    exact hbits₂A
  have hbits₃B : arrayBits σ₃ "nextB" := by
    unfold arrayBits
    rw [hcommit.frame_arr "nextB" (by decide)]
    exact hbits₂B
  have hsub : activeVertices n nextA ⊆ activeVertices n (setFlag A) := by
    intro v hv
    have hvn := (mem_activeVertices.mp hv).1
    have hvS : v ∈ Snum := (dataA.out_mem v hvn).1
      (mem_activeVertices.mp hv).2
    exact dataA.reps_processed hvS
  have hconserve :=
    Lax457868Proofs.ReusedOriginal.Construction.ActiveBookkeeping.removed_length_add_next
      hbitsA hsub
  have hnextSet : activeVertices n nextA = Snum := by
    ext v
    simp only [mem_activeVertices]
    constructor
    · rintro ⟨hv, hflag⟩
      exact (dataA.out_mem v hv).1 hflag
    · intro hv
      have hvn := (mem_activeVertices.mp (dataA.reps_processed hv)).1
      exact ⟨hvn, (dataA.out_mem v hvn).2 hv⟩
  have holdSet : activeVertices n (setFlag A) = A := by
    ext v
    simp only [mem_activeVertices, setFlag, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact (by simpa using h.2)
    · intro hv; exact ⟨Finset.mem_range.mp (R.I.hA hv), by simp [hv]⟩
  have hcapNext : σ₃.vars "removedCount" + Snum.card ≤ n := by
    rw [hremovedCount₃]
    rw [hnextSet, holdSet] at hconserve
    omega
  exact ⟨σ₂, σ₃, Rnum, Snum, nextA, nextB, repA, repB, partCostB, partCostA,
    hsuffix, ⟨hstored⟩, hround₃, hacount₃, hshrink, hcost,
    hnextFrame, hactiveAFlag, hactiveBFlag, hbits₃A, hbits₃B,
    Lax457868Proofs.RefinedRecordedCommit.run_preserves hcommit hbounded₂,
    hcapNext, ⟨partA⟩, ⟨partB⟩⟩


end

end Lax457868Proofs.RefinedRoundSource
