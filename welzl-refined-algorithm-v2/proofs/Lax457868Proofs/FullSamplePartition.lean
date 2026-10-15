import Lax457868Proofs.ExceptionPhaseSource
import Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource
import Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
import Lax457868Proofs.ReusedOriginal.Construction.RadixMath
import Lax457868Proofs.PackedActiveSource
import Lax457868Proofs.GroupedClassRepresentatives

/-! One reusable full active-B partition on a packed sample.  The same source
boundary applies before the initial representative draw and after phase two. -/

namespace Lax457868Proofs.FullSamplePartition

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionLoopSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionRefinement
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.PackedActiveSource
open Lax457868Proofs.ReusedOriginal.Construction.RadixPass
open Lax457868Proofs.GroupedClassRepresentatives
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.SamplePacking

noncomputable section

/-- The empty active side has an explicit source return path. -/
def fullSamplePartition : Com :=
  .ite (.eq (.var "activeBCount") (.lit 0))
    (.assign "classCount" (.lit 0))
    (partitionRefinePrefix "activeB" "ord" "sampleCount" "classB")

def fullSamplePartitionCost (x : List ℕ) (ord : ℕ → ℕ)
    (n sampleCount : ℕ) : ℕ :=
  1 + (Cond.eq (.var "activeBCount") (.lit 0)).size +
    (60 * (n + 1) + 2 +
      (324 * refinementWork x ord 0 sampleCount + 4))

/-- Exact class multiplicities become the list counts read by radix grouping.
The list is only required to be a duplicate-free enumeration of the active
vertices. -/
lemma classMultiplicity_eq_countDigit (n : ℕ) (active label : ℕ → ℕ)
    (xs : List ℕ) (hxs : xs.Nodup)
    (hxsSet : xs.toFinset = activeVertices n active) (d : ℕ) :
    classMultiplicity label (activeVertices n active) d =
      countDigit label xs d := by
  have hfilter : (xs.filter fun v => label v = d).toFinset =
      (activeVertices n active).filter fun v => label v = d := by
    rw [List.toFinset_filter]
    simp only [hxsSet, decide_eq_true_eq]
  calc
    classMultiplicity label (activeVertices n active) d =
        (xs.filter fun v => label v = d).toFinset.card := by
          simp only [classMultiplicity, hfilter]
    _ = (xs.filter fun v => label v = d).length :=
      List.toFinset_card_of_nodup (hxs.filter _)
    _ = countDigit label xs d := rfl

/-- The compact class-size array has exactly the counts expected by radix
grouping on any duplicate-free active-B enumeration. -/
lemma ClassSizes.countDigit {n q : ℕ} {active label size : ℕ → ℕ}
    (hsizes : ClassSizes n q active label size)
    (xs : List ℕ) (hxs : xs.Nodup)
    (hxsSet : xs.toFinset = activeVertices n active) :
    ∀ d < q, size d = countDigit label xs d := by
  intro d hd
  rw [hsizes.2 d hd, classMultiplicity_eq_countDigit n active label xs hxs hxsSet]

/-- Concrete input state: a packed sample, the graph CSR arrays, an active
side and scratch arrays. No trace classification is assumed. -/
structure Input (B n targetCap sampleCount : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ) (W : Finset ℕ) where
  σ : Env
  activeB : ℕ → ℕ
  ord : ℕ → ℕ
  classB : ℕ → ℕ
  classSize : ℕ → ℕ
  markedCount : ℕ → ℕ
  stamp : ℕ → ℕ
  marked : ℕ → ℕ
  touched : ℕ → ℕ
  split : ℕ → ℕ
  repB : ℕ → ℕ
  sampleFlags : ℕ → ℕ
  hx : EncodesGraph x n G
  htargetCap : targetCap = 2 * edgeCount x
  hn : σ.vars "n" = n
  hsampleCount : σ.vars "sampleCount" = sampleCount
  hactiveBCount : σ.vars "activeBCount" = (activeVertices n activeB).card
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htarget : σ.arrs "tgt" = arrOf targetCap (target x)
  hactiveB : σ.arrs "activeB" = arrOf n activeB
  hord : σ.arrs "ord" = arrOf n ord
  hclassB : σ.arrs "classB" = arrOf n classB
  hclassSize : σ.arrs "classSize" = arrOf n classSize
  hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount
  hstamp : σ.arrs "stamp" = arrOf n stamp
  hmarked : σ.arrs "marked" = arrOf n marked
  htouched : σ.arrs "touched" = arrOf n touched
  hsplit : σ.arrs "split" = arrOf n split
  hrepB : σ.arrs "repB" = arrOf n repB
  hsampleFlags : σ.arrs "sampleFlags" = arrOf n sampleFlags
  henum : PrefixEnumerates sampleCount ord W
  hWrange : W ⊆ Finset.range n
  hsampleCountN : sampleCount ≤ n
  hnB : n < B
  htargetCapB : targetCap < B
  honeB : 1 < B
  hactiveBBound : ∀ v < n, activeB v < B

private lemma Input.refinePrefix_run {B n targetCap sampleCount : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {W : Finset ℕ}
    (I : Input B n targetCap sampleCount G x W)
    (hBne : (activeVertices n I.activeB).Nonempty) :
    ∃ σ₁, Run B (partitionRefinePrefix "activeB" "ord" "sampleCount" "classB")
        I.σ σ₁
        (60 * (n + 1) + 2 +
          (324 * refinementWork x I.ord 0 sampleCount + 4)) ∧
      RefineTestsInv G x targetCap sampleCount
        "activeB" "ord" "sampleCount" "classB"
        I.activeB I.ord σ₁ ∧
      σ₁.vars "ti" = sampleCount := by
  have hrange := PrefixEnumerates.entry_lt I.henum
    (fun v hv => Finset.mem_range.mp (I.hWrange hv))
  apply partitionRefinePrefix_run
    (activeName := "activeB") (testsName := "ord")
    (testCountName := "sampleCount") (clsName := "classB")
    I.hx I.htargetCap I.hn I.hsampleCount I.hoff I.htarget
    I.hactiveB I.hord I.hclassB I.hclassSize I.hmarkedCount
    I.hstamp I.hmarked I.htouched I.hsplit
    hBne I.hsampleCountN hrange I.hnB I.htargetCapB I.honeB I.hactiveBBound
  all_goals decide

/-- Partition all active B-vertices by their traces on the supplied packed
sample. Empty B sets the class count to zero in a concrete source branch.
The original representative map and sample flags are retained. -/
lemma fullSamplePartition_run {B n targetCap sampleCount : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {W : Finset ℕ}
    (I : Input B n targetCap sampleCount G x W) :
    ∃ σ' current label size,
      Run B fullSamplePartition I.σ σ'
        (fullSamplePartitionCost x I.ord n sampleCount) ∧
      σ'.vars "classCount" = current ∧ current ≤ n ∧
      σ'.arrs "classB" = arrOf n label ∧
      σ'.arrs "classSize" = arrOf n size ∧
      ClassSizes n current I.activeB label size ∧
      LabelsOccupyPrefix current label (activeVertices n I.activeB) ∧
      (∀ b ∈ activeVertices n I.activeB,
        ∀ b' ∈ activeVertices n I.activeB,
          (label b = label b' ↔
            trace (numericNeighborhood G) W b =
              trace (numericNeighborhood G) W b')) ∧
      σ'.arrs "activeB" = arrOf n I.activeB ∧
      σ'.arrs "sampleFlags" = arrOf n I.sampleFlags ∧
      σ'.arrs "ord" = arrOf n I.ord ∧
      σ'.arrs "repB" = arrOf n I.repB ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.vars "n" = n ∧
      σ'.vars "sampleCount" = sampleCount ∧
      σ'.vars "activeBCount" = (activeVertices n I.activeB).card ∧
      σ'.inp = I.σ.inp ∧ σ'.out = I.σ.out ∧
      (∀ a, a ∉ fullSamplePartition.warrs → σ'.arrs a = I.σ.arrs a) ∧
      (∀ v, v ∉ fullSamplePartition.wvars → σ'.vars v = I.σ.vars v) := by
  by_cases hBne : (activeVertices n I.activeB).Nonempty
  · obtain ⟨σ₁, rprefix, hInv, hti⟩ := I.refinePrefix_run hBne
    rcases hInv with ⟨current, label, size, stamp, counts,
      marked, touched, split, _htiLe, _hcountLe, _hsampleCount,
      hn₁, hcurrent₁, hcurrentLe, _hoff₁, _htarget₁,
      _hactive₁, _hord₁, hlabel₁, hsize₁, _hstamp₁,
      _hcounts₁, _hmarked₁, _htouched₁, _hsplit₁,
      _hstampLe, _hcountsZero, hsizes, hoccupied, hclassifies⟩
    have hclassify : ∀ b ∈ activeVertices n I.activeB,
        ∀ b' ∈ activeVertices n I.activeB,
          (label b = label b' ↔
            trace (numericNeighborhood G) W b =
              trace (numericNeighborhood G) W b') := by
      intro b hb b' hb'
      obtain ⟨hbN, hbActive⟩ := mem_activeVertices.mp hb
      obtain ⟨hb'N, hb'Active⟩ := mem_activeVertices.mp hb'
      have hclass := hclassifies
        (u := (⟨b, hbN⟩ : Fin n)) hbActive
        (v := (⟨b', hb'N⟩ : Fin n)) hb'Active
      rw [hti, testPrefix_eq_finSetAsSet_of_prefixEnumerates I.henum] at hclass
      exact hclass.trans (numeric_trace_iff G I.hWrange
        ⟨b, hbN⟩ ⟨b', hb'N⟩)
    have hcountB : (activeVertices n I.activeB).card < B := by
      have hsubset : activeVertices n I.activeB ⊆ Finset.range n := by
        intro b hb
        exact Finset.mem_range.mpr (mem_activeVertices.mp hb).1
      have hle := Finset.card_le_card hsubset
      simpa using lt_of_le_of_lt (by simpa using hle) I.hnB
    have hcond : (Cond.eq (.var "activeBCount") (.lit 0)).evalB B I.σ =
        some false := by
      have hvar : (Expr.var "activeBCount").evalB B I.σ =
          some (activeVertices n I.activeB).card := by
        rw [evalB_var_iff]
        exact ⟨I.hactiveBCount.symm,
          by rw [I.hactiveBCount]; exact hcountB⟩
      have hzero : (Expr.lit 0).evalB B I.σ = some 0 :=
        evalB_lit (by have := I.honeB; omega)
      have hpos : (activeVertices n I.activeB).card ≠ 0 :=
        Finset.card_ne_zero.mpr hBne
      simpa [hpos] using evalB_condEq hvar hzero
    have hrun : Run B fullSamplePartition I.σ σ₁
        (fullSamplePartitionCost x I.ord n sampleCount) := by
      simpa [fullSamplePartition, fullSamplePartitionCost] using
        (Run.ite_false (c := .assign "classCount" (.lit 0)) hcond rprefix)
    refine ⟨σ₁, current, label, size, hrun, hcurrent₁, hcurrentLe,
      hlabel₁, hsize₁, hsizes, hoccupied, hclassify, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hrun.frame_arr "activeB" (by decide)).trans I.hactiveB
    · exact (hrun.frame_arr "sampleFlags" (by decide)).trans I.hsampleFlags
    · exact (hrun.frame_arr "ord" (by decide)).trans I.hord
    · exact (hrun.frame_arr "repB" (by decide)).trans I.hrepB
    · exact (hrun.frame_arr "off" (by decide)).trans I.hoff
    · exact (hrun.frame_arr "tgt" (by decide)).trans I.htarget
    · exact (hrun.frame_var "n" (by decide)).trans I.hn
    · exact (hrun.frame_var "sampleCount" (by decide)).trans I.hsampleCount
    · exact (hrun.frame_var "activeBCount" (by decide)).trans I.hactiveBCount
    · exact hrun.frame_inp (by decide)
    · exact hrun.out_eq (by decide)
    · intro a ha; exact hrun.frame_arr a ha
    · intro v hv; exact hrun.frame_var v hv
  · have hBempty : activeVertices n I.activeB = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hBne
    let σ₁ := I.σ.setVar "classCount" 0
    have rassign : Run B (.assign "classCount" (.lit 0)) I.σ σ₁ 2 := by
      simpa [σ₁] using (Run.assign (evalB_lit (by have := I.honeB; omega)))
    have hcond : (Cond.eq (.var "activeBCount") (.lit 0)).evalB B I.σ =
        some true := by
      have hvar : (Expr.var "activeBCount").evalB B I.σ = some 0 := by
        rw [evalB_var_iff]
        exact ⟨by rw [I.hactiveBCount, hBempty]; simp,
          by rw [I.hactiveBCount, hBempty]; simp only [Finset.card_empty];
             have := I.honeB; omega⟩
      have hzero : (Expr.lit 0).evalB B I.σ = some 0 :=
        evalB_lit (by have := I.honeB; omega)
      simpa using evalB_condEq hvar hzero
    have hrun : Run B fullSamplePartition I.σ σ₁
        (fullSamplePartitionCost x I.ord n sampleCount) := by
      have hshort : Run B fullSamplePartition I.σ σ₁
          (1 + (Cond.eq (.var "activeBCount") (.lit 0)).size + 2) := by
        simpa [fullSamplePartition] using
          (Run.ite_true (d := partitionRefinePrefix "activeB" "ord"
            "sampleCount" "classB") hcond rassign)
      exact hshort.mono (by unfold fullSamplePartitionCost; omega)
    have hsizes : ClassSizes n 0 I.activeB I.classB I.classSize := by
      constructor
      · intro v hv hav
        have hmem : v ∈ activeVertices n I.activeB :=
          mem_activeVertices.mpr ⟨hv, hav⟩
        rw [hBempty] at hmem
        simp at hmem
      · intro d hd
        omega
    have hoccupied : LabelsOccupyPrefix 0 I.classB
        (activeVertices n I.activeB) := by
      intro d hd
      omega
    have hclassify : ∀ b ∈ activeVertices n I.activeB,
        ∀ b' ∈ activeVertices n I.activeB,
          (I.classB b = I.classB b' ↔
            trace (numericNeighborhood G) W b =
              trace (numericNeighborhood G) W b') := by
      intro b hb
      rw [hBempty] at hb
      simp at hb
    refine ⟨σ₁, 0, I.classB, I.classSize, hrun,
      by simp [σ₁], by omega, ?_, ?_, hsizes, hoccupied,
      hclassify, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (rassign.frame_arr "classB" (by decide)).trans I.hclassB
    · exact (rassign.frame_arr "classSize" (by decide)).trans I.hclassSize
    · exact (hrun.frame_arr "activeB" (by decide)).trans I.hactiveB
    · exact (hrun.frame_arr "sampleFlags" (by decide)).trans I.hsampleFlags
    · exact (hrun.frame_arr "ord" (by decide)).trans I.hord
    · exact (hrun.frame_arr "repB" (by decide)).trans I.hrepB
    · exact (hrun.frame_arr "off" (by decide)).trans I.hoff
    · exact (hrun.frame_arr "tgt" (by decide)).trans I.htarget
    · exact (hrun.frame_var "n" (by decide)).trans I.hn
    · exact (hrun.frame_var "sampleCount" (by decide)).trans I.hsampleCount
    · exact (hrun.frame_var "activeBCount" (by decide)).trans I.hactiveBCount
    · exact hrun.frame_inp (by decide)
    · exact hrun.out_eq (by decide)
    · intro a ha; exact hrun.frame_arr a ha
    · intro v hv; exact hrun.frame_var v hv

/-- The original duplicate-free test-prefix bound charges the full-B
partition to the graph CSR capacity and sample length. -/
lemma Input.fullSamplePartitionCost_le_linear {B n targetCap sampleCount : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {W : Finset ℕ}
    (I : Input B n targetCap sampleCount G x W) :
    fullSamplePartitionCost x I.ord n sampleCount ≤
      1 + (Cond.eq (.var "activeBCount") (.lit 0)).size +
        (60 * (n + 1) + 2 +
          (324 * (targetCap + sampleCount) + 4)) := by
  have hrange := PrefixEnumerates.entry_lt I.henum
    (fun v hv => Finset.mem_range.mp (I.hWrange hv))
  have hwork := refinementWork_le_edgeCount_add I.hx hrange
    I.henum.injective_on_prefix
  rw [← I.htargetCap] at hwork
  unfold fullSamplePartitionCost
  omega

/-! A separate grouping pass consumes either full-B partition result.  It
does not select representatives, so callers can choose whether the grouped
domain is needed and avoid a second radix pass. -/

def groupActiveB : Com := seqs [packActiveBSource, radixPass "classB"]

/-- State produced by the partition, with the scratch arrays required by a
single stable radix pass. -/
structure GroupInput (B n q Q : ℕ) where
  σ : Env
  active : ℕ → ℕ
  label : ℕ → ℕ
  size : ℕ → ℕ
  ord : ℕ → ℕ
  count : ℕ → ℕ
  scratch : ℕ → ℕ
  repB : ℕ → ℕ
  sampleFlags : ℕ → ℕ
  hn : σ.vars "n" = n
  hqpow : σ.vars "qpow" = Q
  hclassCount : σ.vars "classCount" = q
  hactive : σ.arrs "activeB" = arrOf n active
  hlabel : σ.arrs "classB" = arrOf n label
  hsize : σ.arrs "classSize" = arrOf n size
  hord : σ.arrs "ord" = arrOf n ord
  hcount : σ.arrs "count" = arrOf Q count
  hscratch : σ.arrs "scratchOrder" = arrOf n scratch
  hrepB : σ.arrs "repB" = arrOf n repB
  hsampleFlags : σ.arrs "sampleFlags" = arrOf n sampleFlags
  hsizes : ClassSizes n q active label size
  hflags01 : ∀ v < n, active v ≤ 1
  hqQ : q ≤ Q
  hQB : Q < B
  hnB : n < B
  honeB : 1 < B

/-- Pack the active vertices into `ord`, then group that one packed list by
the already computed class labels.  The output prefix is the actual sorted
array; `classStart` remains a mathematical address until a later source
prefix-sum pass materializes it. -/
lemma groupActiveB_run {B n q Q : ℕ} (I : GroupInput B n q Q) :
    ∃ (σ' : Env) (xs : List ℕ) (sorted : ℕ → ℕ),
      Run B groupActiveB I.σ σ'
        (20 * n + 9 + 64 * ((activeVertices n I.active).card + Q + 1)) ∧
      xs.Nodup ∧ xs.toFinset = activeVertices n I.active ∧
      xs.length = (activeVertices n I.active).card ∧
      σ'.vars "alen" = xs.length ∧
      σ'.vars "classCount" = q ∧
      σ'.vars "qpow" = Q ∧
      σ'.arrs "ord" = arrOf n sorted ∧
      (∀ i < xs.length,
        sorted i = (bucketSort Q I.label xs).getD i 0) ∧
      (∀ d < q, I.size d = countDigit I.label xs d) ∧
      (∀ d ≤ q, classStart I.size d = startDigit I.label xs d) ∧
      (∀ d < q, classStart I.size d + I.size d ≤ xs.length) ∧
      (∀ d < q, PrefixEnumerates (I.size d)
        (fun i => sorted (classStart I.size d + i))
        (labelClass xs I.label d)) ∧
      σ'.arrs "activeB" = arrOf n I.active ∧
      σ'.arrs "classB" = arrOf n I.label ∧
      σ'.arrs "classSize" = arrOf n I.size ∧
      σ'.arrs "repB" = arrOf n I.repB ∧
      σ'.arrs "sampleFlags" = arrOf n I.sampleFlags ∧
      σ'.vars "n" = n ∧
      σ'.vars "activePackCursor" = n ∧
      σ'.vars "sampleCount" = I.σ.vars "sampleCount" ∧
      σ'.inp = I.σ.inp ∧ σ'.out = I.σ.out ∧
      (∀ a, a ∉ groupActiveB.warrs → σ'.arrs a = I.σ.arrs a) ∧
      (∀ v, v ∉ groupActiveB.wvars → σ'.vars v = I.σ.vars v) := by
  obtain ⟨σ₁, packed, rpack, hactive₁, hord₁, henum, halen₁,
    _hcursor, hframeArr, hframeVar, _hinp, _hout⟩ :=
    packActiveB_run I.hn I.hactive I.hord I.hflags01 I.hnB I.honeB
  let xs := Stack.toList (σ₁.vars "alen") packed
  have hset : xs.toFinset = activeVertices n I.active := by
    ext v
    simpa [xs, flaggedVertices] using (henum.2 v)
  have hxs : xs.Nodup := henum.1
  have hlen : xs.length = (activeVertices n I.active).card := by
    simp [xs, halen₁, flaggedVertices]
  have hxn : xs.length ≤ n := by
    rw [hlen]
    have hsub : activeVertices n I.active ⊆ Finset.range n := by
      intro v hv
      exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
    simpa using Finset.card_le_card hsub
  have hval : ∀ i < xs.length, packed i = xs.getD i 0 := by
    intro i hi
    have hi' : i < σ₁.vars "alen" := by simpa [xs, Stack.toList] using hi
    change packed i = (arrOf (σ₁.vars "alen") packed).getD i 0
    exact (getD_arrOf packed hi').symm
  have hvertices : ∀ v ∈ xs, v < n := by
    intro v hv
    exact (mem_activeVertices.mp (hset ▸ List.mem_toFinset.mpr hv)).1
  have hsizeCount := ClassSizes.countDigit I.hsizes xs hxs hset
  have hkeys : ∀ v ∈ xs, I.label v < Q := by
    intro v hv
    have ha : v ∈ activeVertices n I.active := by
      rw [← hset]; exact List.mem_toFinset.mpr hv
    exact (I.hsizes.1 v (mem_activeVertices.mp ha).1
      (mem_activeVertices.mp ha).2).trans_le I.hqQ
  have hqpow₁ : σ₁.vars "qpow" = Q := by
    rw [hframeVar "qpow" (by decide) (by decide)]
    exact I.hqpow
  have hlabel₁ : σ₁.arrs "classB" = arrOf n I.label := by
    rw [hframeArr "classB" (by decide)]
    exact I.hlabel
  have hcount₁ : σ₁.arrs "count" = arrOf Q I.count := by
    rw [hframeArr "count" (by decide)]
    exact I.hcount
  have hscratch₁ : σ₁.arrs "scratchOrder" = arrOf n I.scratch := by
    rw [hframeArr "scratchOrder" (by decide)]
    exact I.hscratch
  obtain ⟨σ₂, sorted, rradix, halen₂, hqpow₂, hord₂, hsorted, hlabel₂⟩ :=
    radixPass_run (keyName := "classB")
      (xs := xs) (by simp [xs, Stack.toList])
      hqpow₁ hord₁ hval hlabel₁ hcount₁ hscratch₁
      (by decide) (by decide) (by decide)
      hxn I.hnB I.hQB hxs hvertices hkeys
  have hrun : Run B groupActiveB I.σ σ₂
      (20 * n + 9 + 64 * ((activeVertices n I.active).card + Q + 1)) := by
    simpa [groupActiveB, seqs, hlen] using rpack.seq rradix
  have hstart : ∀ d ≤ q, classStart I.size d = startDigit I.label xs d :=
    classStart_eq_startDigit hsizeCount
  have htotal : (bucketSort Q I.label xs).length = xs.length :=
    (bucketSort_perm hxs hkeys).length_eq
  have hintervals : ∀ d < q,
      classStart I.size d + I.size d ≤ xs.length := by
    intro d hd
    rw [hstart d (Nat.le_of_lt hd), hsizeCount d hd]
    have hinterval := digit_intervals_separated I.label xs
      (lt_of_lt_of_le hd I.hqQ)
    have hfinal : startDigit I.label xs Q = xs.length := by
      rw [← length_bucketSort_eq_startDigit]
      exact htotal
    omega
  have hslices : ∀ d < q, PrefixEnumerates (I.size d)
      (fun i => sorted (classStart I.size d + i))
      (labelClass xs I.label d) := by
    intro d hd
    have hbase := bucketSlice_prefixEnumerates xs I.label Q d
      (lt_of_lt_of_le hd I.hqQ) hxs
    have hbound : ∀ i < I.size d,
        classStart I.size d + i < xs.length := by
      intro i hi
      rw [hstart d (Nat.le_of_lt hd), hsizeCount d hd] at *
      have hinterval := digit_intervals_separated I.label xs
        (lt_of_lt_of_le hd I.hqQ)
      have hfinal : startDigit I.label xs Q = xs.length := by
        rw [← length_bucketSort_eq_startDigit]
        exact htotal
      omega
    have hlist : Stack.toList (I.size d)
        (fun i => sorted (classStart I.size d + i)) =
        Stack.toList (countDigit I.label xs d)
          (fun i => (bucketSort Q I.label xs).getD
            (startDigit I.label xs d + i) 0) := by
      rw [hsizeCount d hd]
      change arrOf (countDigit I.label xs d) _ = arrOf _ _
      apply arrOf_congr
      intro i hi
      rw [hstart d (Nat.le_of_lt hd)]
      have hb := hbound i (by rwa [hsizeCount d hd])
      rw [hstart d (Nat.le_of_lt hd)] at hb
      exact hsorted _ hb
    change (Stack.toList (I.size d)
      (fun i => sorted (classStart I.size d + i))).Nodup ∧
      ∀ v, v ∈ Stack.toList (I.size d)
        (fun i => sorted (classStart I.size d + i)) ↔
        v ∈ labelClass xs I.label d
    rw [hlist]
    exact hbase
  refine ⟨σ₂, xs, sorted, hrun, hxs, hset, hlen, halen₂, ?_, hqpow₂,
    hord₂, hsorted, hsizeCount, hstart, hintervals, hslices, ?_, hlabel₂,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rradix.frame_var "classCount" (by decide),
      hframeVar "classCount" (by decide) (by decide)]
    exact I.hclassCount
  · rw [rradix.frame_arr "activeB" (by decide)]
    exact hactive₁
  · rw [rradix.frame_arr "classSize" (by decide),
      hframeArr "classSize" (by decide)]
    exact I.hsize
  · rw [rradix.frame_arr "repB" (by decide),
      hframeArr "repB" (by decide)]
    exact I.hrepB
  · rw [rradix.frame_arr "sampleFlags" (by decide),
      hframeArr "sampleFlags" (by decide)]
    exact I.hsampleFlags
  · rw [rradix.frame_var "n" (by decide),
      hframeVar "n" (by decide) (by decide)]
    exact I.hn
  · rw [rradix.frame_var "activePackCursor" (by decide)]
    exact _hcursor
  · exact hrun.frame_var "sampleCount" (by decide)
  · exact hrun.frame_inp (by decide)
  · exact hrun.out_eq (by decide)
  · intro a ha; exact hrun.frame_arr a ha
  · intro v hv; exact hrun.frame_var v hv

/-- When the radix table capacity is at most twice the vertex capacity, the
separate pack-and-group source has a fixed linear budget. -/
lemma GroupInput.groupActiveBCost_le_linear {B n q Q : ℕ}
    (I : GroupInput B n q Q) (hQ : Q ≤ 2 * n) :
    20 * n + 9 + 64 * ((activeVertices n I.active).card + Q + 1) ≤
      212 * n + 73 := by
  have hsub : activeVertices n I.active ⊆ Finset.range n := by
    intro v hv
    exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
  have hcard : (activeVertices n I.active).card ≤ n := by
    simpa using Finset.card_le_card hsub
  omega

end

end Lax457868Proofs.FullSamplePartition
