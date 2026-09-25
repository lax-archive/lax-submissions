import Lax235315Proofs.Construction.PartitionResult
import Lax235315Proofs.Construction.PartitionSource
import Mathlib.Tactic

/-! Composition of the complete concrete `partition` routine. -/

namespace Lax235315Proofs.Construction.PartitionCompleteSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PartitionLoopSource
open Lax235315Proofs.Construction.PartitionRefinement
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.RepresentativeSource
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlStraight

noncomputable section

/-- Initialization followed by all test-refinement passes, exactly as they
occur at the front of `partition`. -/
def partitionRefinePrefix (activeName testsName testCountName clsName : String) : Com :=
  seqs [
    initPartition activeName clsName,
    .assign "ti" (.lit 0),
    .while (.lt (.var "ti") (.var testCountName))
      (partitionRefineBody activeName testsName clsName)]

/-- The sentinel-table initialization appearing between refinement and the
representative scans. -/
def fillRepClass : Com :=
  seqs [
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "n"))
      (seqs [
        .store "repClass" (.var "i") (.var "n"),
        inc "i"])]

lemma fillRepClass_run {B n : ℕ} {σ : Env} {old : ℕ → ℕ}
    (harr : σ.arrs "repClass" = arrOf n old) (hn : σ.vars "n" = n)
    (hnB : n < B) :
    ∃ σ' repClass,
      Run B fillRepClass σ σ' (11 * n + 6) ∧
      σ'.arrs "repClass" = arrOf n repClass ∧
      (∀ q < n, repClass q = n) ∧ σ'.vars "i" = n := by
  have hshape : fillRepClass =
      .seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var "n"))
          (Fill.put "repClass" "i" (.var "n"))) := by
    simp [fillRepClass, Fill.put, inc, seqs]
  rw [hshape]
  obtain ⟨σ', hrun, ⟨repClass, harr', hfill⟩, hi⟩ :=
    (Fill.loop_spec B n "repClass" "i" "n" (.var "n")
      (fun _ => n) (by decide) hnB
      (fun τ _ hn' _ => by
        have hnB' : τ.vars "n" < B := by rw [hn']; exact hnB
        simpa [hn'] using (evalB_var hnB'))).run
      ⟨⟨old, harr⟩, hn⟩
  exact ⟨σ', repClass, hrun, harr', hfill, hi⟩

/-- The part of `partition` after all trace-refinement passes. -/
def partitionRepresentativeSuffix (activeName clsName repsName activeOutName
    repOfName outCountName : String) : Com :=
  seqs [
    clearArray activeOutName "n",
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "n"))
      (seqs [
        .store "repClass" (.var "i") (.var "n"),
        inc "i"]),
    .assign outCountName (.lit 0),
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n"))
      (representativeSelectBody activeName clsName repsName activeOutName
        outCountName),
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n"))
      (representativeMapBody activeName clsName repOfName)]

def partitionCost (x : List ℕ) (tests : ℕ → ℕ)
    (n testCount : ℕ) : ℕ :=
  (60 * (n + 1) + 2 +
    (324 * refinementWork x tests 0 testCount + 4)) +
  (430 * n + 26)

/-- On a duplicate-free test prefix, one complete partition call is linear
in the encoded CSR word. -/
lemma partitionCost_le_input
    {n testCount : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {tests : ℕ → ℕ}
    (hx : EncodesGraph x n G) (htestCountN : testCount ≤ n)
    (htestsRange : ∀ i < testCount, tests i < n)
    (htestsInj : ∀ i < testCount, ∀ j < testCount,
      tests i = tests j → i = j) :
    partitionCost x tests n testCount ≤ 900 * (x.length + 1) := by
  have hwork := refinementWork_le_edgeCount_add hx htestsRange htestsInj
  have hlen := hx.length_eq
  unfold partitionCost
  omega

private lemma Run.append_right2 {B K K' : ℕ} {a b c : Com}
    {σ σ' σ'' : Env}
    (h : Run B (.seq a b) σ σ' K)
    (h' : Run B c σ' σ'' K') :
    Run B (.seq a (.seq b c)) σ σ'' (K + K') := by
  rcases h with ⟨k, hk, hrun⟩
  rcases h' with ⟨k', hk', hrun'⟩
  cases hrun with
  | seq ha hb =>
    refine ⟨_, by omega, .seq ha (.seq hb hrun')⟩

private lemma Run.append_right3 {B K K' : ℕ} {a b c d : Com}
    {σ σ' σ'' : Env}
    (h : Run B (.seq a (.seq b c)) σ σ' K)
    (h' : Run B d σ' σ'' K') :
    Run B (.seq a (.seq b (.seq c d))) σ σ'' (K + K') := by
  rcases h with ⟨k, hk, hrun⟩
  rcases h' with ⟨k', hk', hrun'⟩
  cases hrun with
  | seq ha hbc =>
    cases hbc with
    | seq hb hc =>
      refine ⟨_, by omega, .seq ha (.seq hb (.seq hc hrun'))⟩

lemma partitionRefinePrefix_run
    {B n targetCap testCount : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {active tests cls size counts stamp marked touched split : ℕ → ℕ}
    {activeName testsName testCountName clsName : String} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n) (htestCount : σ.vars testCountName = testCount)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs activeName = arrOf n active)
    (htests : σ.arrs testsName = arrOf n tests)
    (hcls : σ.arrs clsName = arrOf n cls)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hcounts : σ.arrs "markedCount" = arrOf n counts)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hsplit : σ.arrs "split" = arrOf n split)
    (hactiveNonempty : (activeVertices n active).Nonempty)
    (htestCountN : testCount ≤ n)
    (htestsRange : ∀ i < testCount, tests i < n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hactiveCls : activeName ≠ clsName)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (haSplit : activeName ≠ "split")
    (haSize : activeName ≠ "classSize")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount")
    (hcSplit : clsName ≠ "split")
    (hcSize : clsName ≠ "classSize")
    (hcOff : clsName ≠ "off") (hcTgt : clsName ≠ "tgt")
    (htestsInit : testsName ∉ (initPartition activeName clsName).warrs)
    (hmarkedInit : "marked" ∉ (initPartition activeName clsName).warrs)
    (htouchedInit : "touched" ∉ (initPartition activeName clsName).warrs)
    (hsplitInit : "split" ∉ (initPartition activeName clsName).warrs)
    (hoffInit : "off" ∉ (initPartition activeName clsName).warrs)
    (htargetInit : "tgt" ∉ (initPartition activeName clsName).warrs)
    (hcountInit : testCountName ∉ (initPartition activeName clsName).wvars)
    (hcountTi : testCountName ≠ "ti")
    (htestsFrame : testsName ∉
      (partitionRefineBody activeName testsName clsName).warrs)
    (hcountFrame : testCountName ∉
      (partitionRefineBody activeName testsName clsName).wvars) :
    ∃ σ', Run B (partitionRefinePrefix activeName testsName testCountName clsName)
        σ σ' (60 * (n + 1) + 2 +
          (324 * refinementWork x tests 0 testCount + 4)) ∧
      RefineTestsInv G x targetCap testCount activeName testsName
        testCountName clsName active tests σ' ∧
      σ'.vars "ti" = testCount := by
  have hnpos : 0 < n := by
    obtain ⟨v, hv⟩ := hactiveNonempty
    exact (mem_activeVertices.mp hv).1 |> Nat.zero_lt_of_lt
  obtain ⟨σ₁, cls₁, size₁, counts₁, stamp₁, rinit, hn₁, hvcount₁,
      hclassCount₁, hactive₁, hcls₁, hsize₁, hcounts₁, hstamp₁,
      hfill₁, hsizeZero₁, hcountsZero₁, hstampZero₁⟩ :=
    initPartition_run hactive hcls ⟨size, hsize⟩ ⟨counts, hcounts⟩
      ⟨stamp, hstamp⟩ hn hnpos hnB honeB hactiveB hactiveCls haSize
      haCount haStamp hcSize hcCount hcStamp
  have hoff₁ : σ₁.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [rinit.frame_arr "off" hoffInit, hoff]
  have htarget₁ : σ₁.arrs "tgt" = arrOf targetCap (target x) := by
    rw [rinit.frame_arr "tgt" htargetInit, htarget]
  have htests₁ : σ₁.arrs testsName = arrOf n tests := by
    rw [rinit.frame_arr testsName htestsInit, htests]
  have hmarked₁ : σ₁.arrs "marked" = arrOf n marked := by
    rw [rinit.frame_arr "marked" hmarkedInit, hmarked]
  have htouched₁ : σ₁.arrs "touched" = arrOf n touched := by
    rw [rinit.frame_arr "touched" htouchedInit, htouched]
  have hsplit₁ : σ₁.arrs "split" = arrOf n split := by
    rw [rinit.frame_arr "split" hsplitInit, hsplit]
  have htestCount₁ : σ₁.vars testCountName = testCount := by
    rw [rinit.frame_var testCountName hcountInit, htestCount]
  let σ₂ := σ₁.setVar "ti" 0
  have rti : Run B (.assign "ti" (.lit 0)) σ₁ σ₂ 2 :=
    Run.assign (evalB_lit (by omega))
  have hsizes₁ := initPartition_classSizes_and_occupancy
    hfill₁ hsizeZero₁ hactiveNonempty
  have hI₂ : RefineTestsInv G x targetCap testCount activeName testsName
      testCountName clsName active tests σ₂ := by
    refine ⟨1, cls₁, size₁, stamp₁, counts₁, marked, touched, split,
      by simp [σ₂], htestCountN, ?_, by simp [σ₂, hn₁],
      by simp [σ₂, hclassCount₁], hnpos,
      by simp [σ₂, hoff₁], by simp [σ₂, htarget₁],
      by simp [σ₂, hactive₁], by simp [σ₂, htests₁],
      by simp [σ₂, hcls₁], by simp [σ₂, hsize₁],
      by simp [σ₂, hstamp₁], by simp [σ₂, hcounts₁],
      by simp [σ₂, hmarked₁], by simp [σ₂, htouched₁],
      by simp [σ₂, hsplit₁], ?_, hcountsZero₁, hsizes₁.1, hsizes₁.2, ?_⟩
    · simp [σ₂, htestCount₁, hcountTi]
    · intro v hv
      simp [σ₂, hstampZero₁ v hv]
    · rw [show σ₂.vars "ti" = 0 by simp [σ₂], testPrefix_zero]
      intro u hu v hv
      have hu0 : cls₁ u.val = 0 :=
        hfill₁ u.val u.isLt hu
      have hv0 : cls₁ v.val = 0 :=
        hfill₁ v.val v.isLt hv
      simp [hu0, hv0,
        Lax235315Proofs.Construction.NeighborhoodComplexity.neighborhoodTrace]
  obtain ⟨σ₃, rloop, hI₃, hti₃⟩ :=
    partitionRefineLoop_run hI₂ (by simp [σ₂]) hx htargetCap htestsRange
      hnB htargetCapB honeB hactiveB hactiveCls haStamp haMarked haTouched
      haCount haSplit haSize hcStamp hcMarked hcTouched hcCount hcSplit hcSize
      hcOff hcTgt htestsFrame hcountFrame
  refine ⟨σ₃, ?_, hI₃, hti₃⟩
  simpa [partitionRefinePrefix, seqs, Nat.add_assoc] using
    rinit.seq (rti.seq rloop)

lemma partitionRepresentativeSuffix_run
    {B n current : ℕ} {active label oldRepClass oldReps oldOut oldRepOf : ℕ → ℕ}
    {activeName clsName repsName activeOutName repOfName outCountName : String}
    {σ : Env}
    (hn : σ.vars "n" = n) (hcurrent : σ.vars "classCount" = current)
    (hcurrentN : current ≤ n)
    (hactive : σ.arrs activeName = arrOf n active)
    (hlabel : σ.arrs clsName = arrOf n label)
    (hrepClass : σ.arrs "repClass" = arrOf n oldRepClass)
    (hreps : σ.arrs repsName = arrOf n oldReps)
    (hout : σ.arrs activeOutName = arrOf n oldOut)
    (hrepOf : σ.arrs repOfName = arrOf n oldRepOf)
    (hlabels : ∀ v < n, active v = 1 → label v < current)
    (hnB : n < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hactiveCls : activeName ≠ clsName)
    (haRepClass : activeName ≠ "repClass")
    (haReps : activeName ≠ repsName) (haOut : activeName ≠ activeOutName)
    (haRepOf : activeName ≠ repOfName)
    (hcRepClass : clsName ≠ "repClass")
    (hcReps : clsName ≠ repsName) (hcOut : clsName ≠ activeOutName)
    (hcRepOf : clsName ≠ repOfName)
    (hrepClassReps : "repClass" ≠ repsName)
    (hrepClassOut : "repClass" ≠ activeOutName)
    (hrepClassRepOf : "repClass" ≠ repOfName)
    (hrepOut : repsName ≠ activeOutName)
    (hrepRepOf : repsName ≠ repOfName)
    (houtRepOf : activeOutName ≠ repOfName)
    (hcountV : outCountName ≠ "v") (hcountCl : outCountName ≠ "cl")
    (hcountN : outCountName ≠ "n")
    (hcountClass : outCountName ≠ "classCount") :
    ∃ σ' repClass reps outActive repOf R,
      Run B (partitionRepresentativeSuffix activeName clsName repsName
        activeOutName repOfName outCountName) σ σ' (430 * n + 26) ∧
      σ'.vars outCountName = R.card ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs clsName = arrOf n label ∧
      σ'.arrs "repClass" = arrOf n repClass ∧
      σ'.arrs repsName = arrOf n reps ∧
      σ'.arrs activeOutName = arrOf n outActive ∧
      σ'.arrs repOfName = arrOf n repOf ∧
      RepData n current n active label repClass reps outActive R ∧
      ∀ v < n, active v = 1 → repOf v = repClass (label v) := by
  obtain ⟨σ₁, out₁, rclear, hout₁, hzero₁⟩ :=
    clearArray_run hout hn (by decide) hnB
  have hn₁ : σ₁.vars "n" = n := by
    rw [rclear.frame_var "n" (by simp [clearArray, seqs, inc, Com.wvars]), hn]
  have hcurrent₁ : σ₁.vars "classCount" = current := by
    rw [rclear.frame_var "classCount"
      (by simp [clearArray, seqs, inc, Com.wvars]), hcurrent]
  have hactive₁ : σ₁.arrs activeName = arrOf n active := by
    rw [rclear.frame_arr activeName
      (by simp [clearArray, seqs, inc, Com.warrs, haOut]), hactive]
  have hlabel₁ : σ₁.arrs clsName = arrOf n label := by
    rw [rclear.frame_arr clsName
      (by simp [clearArray, seqs, inc, Com.warrs, hcOut]), hlabel]
  have hrepClass₁ : σ₁.arrs "repClass" = arrOf n oldRepClass := by
    rw [rclear.frame_arr "repClass"
      (by simp [clearArray, seqs, inc, Com.warrs, hrepClassOut]), hrepClass]
  have hreps₁ : σ₁.arrs repsName = arrOf n oldReps := by
    rw [rclear.frame_arr repsName
      (by simp [clearArray, seqs, inc, Com.warrs, hrepOut]), hreps]
  have hrepOf₁ : σ₁.arrs repOfName = arrOf n oldRepOf := by
    rw [rclear.frame_arr repOfName
      (by simp [clearArray, seqs, inc, Com.warrs, Ne.symm houtRepOf]), hrepOf]
  obtain ⟨σ₂, repClass₂, rfill, hrepClass₂, hsentinel₂, hi₂⟩ :=
    fillRepClass_run hrepClass₁ hn₁ hnB
  have hn₂ : σ₂.vars "n" = n := by
    rw [rfill.frame_var "n" (by simp [fillRepClass, Fill.put, seqs, inc,
      Com.wvars]), hn₁]
  have hcurrent₂ : σ₂.vars "classCount" = current := by
    rw [rfill.frame_var "classCount" (by simp [fillRepClass, Fill.put, seqs,
      inc, Com.wvars]), hcurrent₁]
  have hactive₂ : σ₂.arrs activeName = arrOf n active := by
    rw [rfill.frame_arr activeName (by simp [fillRepClass, Fill.put, seqs,
      inc, Com.warrs, haRepClass]), hactive₁]
  have hlabel₂ : σ₂.arrs clsName = arrOf n label := by
    rw [rfill.frame_arr clsName (by simp [fillRepClass, Fill.put, seqs,
      inc, Com.warrs, hcRepClass]), hlabel₁]
  have hreps₂ : σ₂.arrs repsName = arrOf n oldReps := by
    rw [rfill.frame_arr repsName (by simp [fillRepClass, Fill.put, seqs,
      inc, Com.warrs, Ne.symm hrepClassReps]), hreps₁]
  have hout₂ : σ₂.arrs activeOutName = arrOf n out₁ := by
    rw [rfill.frame_arr activeOutName (by simp [fillRepClass, Fill.put,
      seqs, inc, Com.warrs, Ne.symm hrepClassOut]), hout₁]
  have hrepOf₂ : σ₂.arrs repOfName = arrOf n oldRepOf := by
    rw [rfill.frame_arr repOfName (by simp [fillRepClass, Fill.put, seqs,
      inc, Com.warrs, Ne.symm hrepClassRepOf]), hrepOf₁]
  let σ₃ := σ₂.setVar outCountName 0
  have rout : Run B (.assign outCountName (.lit 0)) σ₂ σ₃ 2 :=
    Run.assign (evalB_lit (by omega))
  let σ₄ := σ₃.setVar "v" 0
  have rv₀ : Run B (.assign "v" (.lit 0)) σ₃ σ₄ 2 :=
    Run.assign (evalB_lit (by omega))
  have hdata₄ : RepData n current 0 active label repClass₂ oldReps out₁ ∅ := by
    constructor
    · exact prefixEnumerates_zero oldReps
    · simp [activeVertices]
    · simp [Set.InjOn]
    · simp [activeVertices]
    · intro q hq
      rw [hsentinel₂ q (hq.trans_le hcurrentN)]
    · intro q hq
      rw [hsentinel₂ q (hq.trans_le hcurrentN)]
      simp
    · intro q hq hlt
      rw [hsentinel₂ q (hq.trans_le hcurrentN)] at hlt
      omega
    · intro v hv
      rw [hzero₁ v hv]
      simp
  have hselect₄ : RepSelectInv n current activeName clsName repsName
      activeOutName outCountName active label σ₄ := by
    refine ⟨repClass₂, oldReps, out₁, ∅, by simp [σ₄], ?_, ?_,
      hcurrentN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₄, σ₃, hn₂, hcountV, Ne.symm hcountN]
    · simp [σ₄, σ₃, hcurrent₂, hcountV, Ne.symm hcountClass]
    · simp [σ₄, σ₃, hcountV]
    · simp [σ₄, σ₃, hactive₂]
    · simp [σ₄, σ₃, hlabel₂]
    · simp [σ₄, σ₃, hrepClass₂]
    · simp [σ₄, σ₃, hreps₂]
    · simp [σ₄, σ₃, hout₂]
    · simpa [σ₄] using hdata₄
  obtain ⟨σ₅, repClass₅, reps₅, out₅, R, rselect, hv₅, hcount₅,
      hrepClass₅, hreps₅, hout₅, hdata₅⟩ :=
    representativeSelectLoop_run hselect₄ hnB honeB hactiveB hlabels
      hactiveCls haRepClass haReps haOut hcRepClass hcReps hcOut
      hrepClassReps hrepClassOut hrepOut hcountV hcountCl hcountN hcountClass
  have hactive₅ : σ₅.arrs activeName = arrOf n active := by
    rw [rselect.frame_arr activeName (by simp [representativeSelectBody,
      seqs, inc, Com.warrs, haRepClass, haReps, haOut])]
    simpa [σ₄, σ₃] using hactive₂
  have hlabel₅ : σ₅.arrs clsName = arrOf n label := by
    rw [rselect.frame_arr clsName (by simp [representativeSelectBody,
      seqs, inc, Com.warrs, hcRepClass, hcReps, hcOut])]
    simpa [σ₄, σ₃] using hlabel₂
  have hrepOf₅ : σ₅.arrs repOfName = arrOf n oldRepOf := by
    rw [rselect.frame_arr repOfName (by simp [representativeSelectBody,
      seqs, inc, Com.warrs, Ne.symm hrepClassRepOf, Ne.symm hrepRepOf,
      Ne.symm houtRepOf])]
    simpa [σ₄, σ₃] using hrepOf₂
  have hn₅ : σ₅.vars "n" = n := by
    rw [rselect.frame_var "n" (by simp [representativeSelectBody, seqs, inc,
      Com.wvars, Ne.symm hcountN])]
    simpa [σ₄, σ₃, Ne.symm hcountN, hcountV] using hn₂
  let σ₆ := σ₅.setVar "v" 0
  have rv₁ : Run B (.assign "v" (.lit 0)) σ₅ σ₆ 2 :=
    Run.assign (evalB_lit (by omega))
  have hrepRange : ∀ v < n, active v = 1 → repClass₅ (label v) < n := by
    intro v hv hav
    exact repClass_lt_of_active hdata₅ hv hav (hlabels v hv hav)
  have hmap₆ : RepMapInv n current activeName clsName repOfName active label
      repClass₅ σ₆ := by
    refine ⟨oldRepOf, by simp [σ₆], by simp [σ₆, hn₅], hcurrentN,
      by simp [σ₆, hactive₅], by simp [σ₆, hlabel₅],
      by simp [σ₆, hrepClass₅], by simp [σ₆, hrepOf₅], hlabels, ?_⟩
    intro v hv
    simp [σ₆] at hv
  obtain ⟨σ₇, repOf₇, rmap, hv₇, hrepOf₇, hmap₇⟩ :=
    representativeMapLoop_run hmap₆ hnB honeB hactiveB hrepRange
      hactiveCls haRepClass haRepOf hcRepClass hcRepOf hrepClassRepOf
  have hactive₇ : σ₇.arrs activeName = arrOf n active := by
    rw [rmap.frame_arr activeName (by simp [representativeMapBody, seqs, inc,
      Com.warrs, haRepOf])]
    simpa [σ₆] using hactive₅
  have hlabel₇ : σ₇.arrs clsName = arrOf n label := by
    rw [rmap.frame_arr clsName (by simp [representativeMapBody, seqs, inc,
      Com.warrs, hcRepOf])]
    simpa [σ₆] using hlabel₅
  have hrepClass₇ : σ₇.arrs "repClass" = arrOf n repClass₅ := by
    rw [rmap.frame_arr "repClass" (by simp [representativeMapBody, seqs, inc,
      Com.warrs, hrepClassRepOf])]
    simpa [σ₆] using hrepClass₅
  have hreps₇ : σ₇.arrs repsName = arrOf n reps₅ := by
    rw [rmap.frame_arr repsName (by simp [representativeMapBody, seqs, inc,
      Com.warrs, hrepRepOf])]
    simpa [σ₆] using hreps₅
  have hout₇ : σ₇.arrs activeOutName = arrOf n out₅ := by
    rw [rmap.frame_arr activeOutName (by simp [representativeMapBody, seqs, inc,
      Com.warrs, houtRepOf])]
    simpa [σ₆] using hout₅
  have hcount₇ : σ₇.vars outCountName = R.card := by
    rw [rmap.frame_var outCountName (by simp [representativeMapBody, seqs, inc,
      Com.wvars, hcountV, hcountCl]), rv₁.frame_var outCountName
      (by simp only [Com.wvars, List.mem_singleton]; exact hcountV), hcount₅]
  refine ⟨σ₇, repClass₅, reps₅, out₅, repOf₇, R, ?_, hcount₇,
    hactive₇, hlabel₇, hrepClass₇, hreps₇, hout₇, hrepOf₇,
    hdata₅, hmap₇⟩
  have rfill' : Run B
      (.seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var "n"))
          (seqs [.store "repClass" (.var "i") (.var "n"), inc "i"])))
      σ₁ σ₂ (11 * n + 6) := by
    simpa [fillRepClass, seqs] using rfill
  have rrest := rout.seq (rv₀.seq (rselect.seq (rv₁.seq rmap)))
  have rafterFill := Run.append_right2 rfill' rrest
  simpa only [partitionRepresentativeSuffix, seqs] using
    (rclear.seq rafterFill).mono (by omega)

/-- Once the verified refinement prefix has finished, the literal remainder
of `partition` produces the concrete representative arrays and an abstract
trace partition for exactly the supplied tests. -/
lemma partition_run_of_refinePrefix
    {B n targetCap testCount : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {active tests : ℕ → ℕ}
    {activeName testsName testCountName clsName repsName activeOutName
      repOfName outCountName : String}
    {σ σmid : Env} {oldRepClass oldReps oldOut oldRepOf : ℕ → ℕ}
    (rprefix : Run B
      (partitionRefinePrefix activeName testsName testCountName clsName)
      σ σmid
      (60 * (n + 1) + 2 +
        (324 * refinementWork x tests 0 testCount + 4)))
    (hI : RefineTestsInv G x targetCap testCount activeName testsName
      testCountName clsName active tests σmid)
    (hti : σmid.vars "ti" = testCount)
    (hrepClass : σmid.arrs "repClass" = arrOf n oldRepClass)
    (hreps : σmid.arrs repsName = arrOf n oldReps)
    (hout : σmid.arrs activeOutName = arrOf n oldOut)
    (hrepOf : σmid.arrs repOfName = arrOf n oldRepOf)
    (hnB : n < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hactiveCls : activeName ≠ clsName)
    (haRepClass : activeName ≠ "repClass")
    (haReps : activeName ≠ repsName) (haOut : activeName ≠ activeOutName)
    (haRepOf : activeName ≠ repOfName)
    (hcRepClass : clsName ≠ "repClass")
    (hcReps : clsName ≠ repsName) (hcOut : clsName ≠ activeOutName)
    (hcRepOf : clsName ≠ repOfName)
    (hrepClassReps : "repClass" ≠ repsName)
    (hrepClassOut : "repClass" ≠ activeOutName)
    (hrepClassRepOf : "repClass" ≠ repOfName)
    (hrepOut : repsName ≠ activeOutName)
    (hrepRepOf : repsName ≠ repOfName)
    (houtRepOf : activeOutName ≠ repOfName)
    (hcountV : outCountName ≠ "v") (hcountCl : outCountName ≠ "cl")
    (hcountN : outCountName ≠ "n")
    (hcountClass : outCountName ≠ "classCount") :
    ∃ σ' current label repClass reps outActive repOf R,
      Run B (partition activeName testsName testCountName clsName repsName
        activeOutName repOfName outCountName) σ σ'
        (partitionCost x tests n testCount) ∧
      σ'.vars outCountName = R.card ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs clsName = arrOf n label ∧
      σ'.arrs "repClass" = arrOf n repClass ∧
      σ'.arrs repsName = arrOf n reps ∧
      σ'.arrs activeOutName = arrOf n outActive ∧
      σ'.arrs repOfName = arrOf n repOf ∧
      RepData n current n active label repClass reps outActive R ∧
      (∀ v < n, active v = 1 → repOf v = repClass (label v)) ∧
      Nonempty (ConcreteTracePartition G active
        (testPrefix tests testCount) R repOf) := by
  rcases hI with ⟨current, label, size, stamp, counts, marked, touched, split,
    htiLe, htestCountN, htestCount, hn, hcurrent, hcurrentN,
    hoff, htarget, hactive, htests, hlabel, hsize, hstamp, hcounts,
    hmarked, htouched, hsplit, hstampLe, hcountsZero, hsizes,
    hoccupied, hclassifies⟩
  have hlabels : ∀ v < n, active v = 1 → label v < current := hsizes.1
  have hclassifies' : Classifies G {v : Fin n | active v.val = 1}
      (testPrefix tests testCount) (fun v => label v.val) := by
    simpa [hti] using hclassifies
  obtain ⟨σ', repClass, reps, outActive, repOf, R, rsuffix, hcount,
      hactive', hlabel', hrepClass', hreps', hout', hrepOf', hdata, hmap⟩ :=
    partitionRepresentativeSuffix_run hn hcurrent hcurrentN hactive hlabel
      hrepClass hreps hout hrepOf hlabels hnB honeB hactiveB hactiveCls
      haRepClass haReps haOut haRepOf hcRepClass hcReps hcOut hcRepOf
      hrepClassReps hrepClassOut hrepClassRepOf hrepOut hrepRepOf houtRepOf
      hcountV hcountCl hcountN hcountClass
  have rpartition : Run B
      (partition activeName testsName testCountName clsName repsName
        activeOutName repOfName outCountName) σ σ'
      (partitionCost x tests n testCount) := by
    have rprefix' : Run B
        (.seq (initPartition activeName clsName)
          (.seq (.assign "ti" (.lit 0))
            (.while (.lt (.var "ti") (.var testCountName))
              (partitionRefineBody activeName testsName clsName))))
        σ σmid
        (60 * (n + 1) + 2 +
          (324 * refinementWork x tests 0 testCount + 4)) := by
      simpa [partitionRefinePrefix, seqs] using rprefix
    have rjoined := Run.append_right3 rprefix' rsuffix
    simpa [partition, partitionRepresentativeSuffix, partitionRefineBody,
      representativeSelectBody, representativeMapBody, fillRepClass, seqs,
      partitionCost] using rjoined
  refine ⟨σ', current, label, repClass, reps, outActive, repOf, R,
    rpartition, hcount, hactive', hlabel', hrepClass', hreps', hout', hrepOf',
    hdata, hmap, ?_⟩
  exact ⟨concreteTracePartition_of_repData G hclassifies' hlabels hdata hmap⟩

/-- The complete literal `partition` command, from its initial arrays through
the final representative map and abstract trace-partition certificate. -/
lemma partition_run
    {B n targetCap testCount : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {active tests cls size counts stamp marked touched split
      oldRepClass oldReps oldOut oldRepOf : ℕ → ℕ}
    {activeName testsName testCountName clsName repsName activeOutName
      repOfName outCountName : String} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n) (htestCount : σ.vars testCountName = testCount)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs activeName = arrOf n active)
    (htests : σ.arrs testsName = arrOf n tests)
    (hcls : σ.arrs clsName = arrOf n cls)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hcounts : σ.arrs "markedCount" = arrOf n counts)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hsplit : σ.arrs "split" = arrOf n split)
    (hrepClass : σ.arrs "repClass" = arrOf n oldRepClass)
    (hreps : σ.arrs repsName = arrOf n oldReps)
    (hout : σ.arrs activeOutName = arrOf n oldOut)
    (hrepOf : σ.arrs repOfName = arrOf n oldRepOf)
    (hactiveNonempty : (activeVertices n active).Nonempty)
    (htestCountN : testCount ≤ n)
    (htestsRange : ∀ i < testCount, tests i < n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hactiveCls : activeName ≠ clsName)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (haSplit : activeName ≠ "split")
    (haSize : activeName ≠ "classSize")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount")
    (hcSplit : clsName ≠ "split")
    (hcSize : clsName ≠ "classSize")
    (hcOff : clsName ≠ "off") (hcTgt : clsName ≠ "tgt")
    (htestsInit : testsName ∉ (initPartition activeName clsName).warrs)
    (hmarkedInit : "marked" ∉ (initPartition activeName clsName).warrs)
    (htouchedInit : "touched" ∉ (initPartition activeName clsName).warrs)
    (hsplitInit : "split" ∉ (initPartition activeName clsName).warrs)
    (hoffInit : "off" ∉ (initPartition activeName clsName).warrs)
    (htargetInit : "tgt" ∉ (initPartition activeName clsName).warrs)
    (hcountInit : testCountName ∉ (initPartition activeName clsName).wvars)
    (hcountTi : testCountName ≠ "ti")
    (htestsFrame : testsName ∉
      (partitionRefineBody activeName testsName clsName).warrs)
    (hcountFrame : testCountName ∉
      (partitionRefineBody activeName testsName clsName).wvars)
    (hrepClassPrefix : "repClass" ∉
      (partitionRefinePrefix activeName testsName testCountName clsName).warrs)
    (hrepsPrefix : repsName ∉
      (partitionRefinePrefix activeName testsName testCountName clsName).warrs)
    (houtPrefix : activeOutName ∉
      (partitionRefinePrefix activeName testsName testCountName clsName).warrs)
    (hrepOfPrefix : repOfName ∉
      (partitionRefinePrefix activeName testsName testCountName clsName).warrs)
    (haRepClass : activeName ≠ "repClass")
    (haReps : activeName ≠ repsName) (haOut : activeName ≠ activeOutName)
    (haRepOf : activeName ≠ repOfName)
    (hcRepClass : clsName ≠ "repClass")
    (hcReps : clsName ≠ repsName) (hcOut : clsName ≠ activeOutName)
    (hcRepOf : clsName ≠ repOfName)
    (hrepClassReps : "repClass" ≠ repsName)
    (hrepClassOut : "repClass" ≠ activeOutName)
    (hrepClassRepOf : "repClass" ≠ repOfName)
    (hrepOut : repsName ≠ activeOutName)
    (hrepRepOf : repsName ≠ repOfName)
    (houtRepOf : activeOutName ≠ repOfName)
    (hcountV : outCountName ≠ "v") (hcountCl : outCountName ≠ "cl")
    (hcountN : outCountName ≠ "n")
    (hcountClass : outCountName ≠ "classCount") :
    ∃ σ' current label repClass reps outActive repOf R,
      Run B (partition activeName testsName testCountName clsName repsName
        activeOutName repOfName outCountName) σ σ'
        (partitionCost x tests n testCount) ∧
      σ'.vars outCountName = R.card ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs clsName = arrOf n label ∧
      σ'.arrs "repClass" = arrOf n repClass ∧
      σ'.arrs repsName = arrOf n reps ∧
      σ'.arrs activeOutName = arrOf n outActive ∧
      σ'.arrs repOfName = arrOf n repOf ∧
      RepData n current n active label repClass reps outActive R ∧
      (∀ v < n, active v = 1 → repOf v = repClass (label v)) ∧
      Nonempty (ConcreteTracePartition G active
        (testPrefix tests testCount) R repOf) := by
  obtain ⟨σmid, rprefix, hI, hti⟩ :=
    partitionRefinePrefix_run hx htargetCap hn htestCount hoff htarget
      hactive htests hcls hsize hcounts hstamp hmarked htouched hsplit
      hactiveNonempty htestCountN htestsRange hnB htargetCapB honeB
      hactiveB hactiveCls haStamp haMarked haTouched haCount haSplit haSize
      hcStamp hcMarked hcTouched hcCount hcSplit hcSize hcOff hcTgt
      htestsInit hmarkedInit htouchedInit hsplitInit hoffInit htargetInit
      hcountInit hcountTi htestsFrame hcountFrame
  have hrepClassMid : σmid.arrs "repClass" = arrOf n oldRepClass := by
    rw [rprefix.frame_arr "repClass" hrepClassPrefix, hrepClass]
  have hrepsMid : σmid.arrs repsName = arrOf n oldReps := by
    rw [rprefix.frame_arr repsName hrepsPrefix, hreps]
  have houtMid : σmid.arrs activeOutName = arrOf n oldOut := by
    rw [rprefix.frame_arr activeOutName houtPrefix, hout]
  have hrepOfMid : σmid.arrs repOfName = arrOf n oldRepOf := by
    rw [rprefix.frame_arr repOfName hrepOfPrefix, hrepOf]
  exact partition_run_of_refinePrefix rprefix hI hti hrepClassMid hrepsMid
    houtMid hrepOfMid hnB honeB hactiveB hactiveCls haRepClass haReps haOut
    haRepOf hcRepClass hcReps hcOut hcRepOf hrepClassReps hrepClassOut
    hrepClassRepOf hrepOut hrepRepOf houtRepOf hcountV hcountCl hcountN
    hcountClass

end

end Lax235315Proofs.Construction.PartitionCompleteSource
