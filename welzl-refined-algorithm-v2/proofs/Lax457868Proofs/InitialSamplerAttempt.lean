import Lax457868Proofs.FullSamplePartition
import Lax457868Proofs.InitialDrawSampleSource
import Lax457868Proofs.ExceptionRefinementStep

/-! Checked source boundary for the initial representative-selection attempt.
The packed active list is extracted from the actual active-flag packer; the
representative trace then runs against the remaining flat bit tape. -/

namespace Lax457868Proofs.InitialSamplerAttempt

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax457868Proofs.InitialDrawSampleSource
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.SequentialDraws
open Lax457868Proofs.FullSamplePartition
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.GroupedClassRepresentatives
open Lax457868Proofs.PackedActiveSource
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ExceptionRefinementStep

/-- Pack the already classified active side, radix-group it once, and select
one representative per class from the remaining flat tape. -/
def initialRepresentativeSelection : Com :=
  packActiveBSource.seq groupedClassRepresentatives

/-- Initialize the attempt status, draw the initial packed sample, and only
then partition and select representatives when the draw batch succeeded. -/
def initialSamplerAttempt : Com :=
  (Com.assign "attemptAccepted" (.lit 0)).seq
    (initialDrawSampleSource.seq
      (.ite (.eq (.var "batchFailed") (.lit 0))
        (fullSamplePartition.seq initialRepresentativeSelection) .skip))

/-- Concrete state at the representative-selection boundary. The supplied
labels and class sizes are the result of the full-sample partition source;
all radix scratch and representative arrays remain arbitrary concrete input. -/
structure RepresentativeInput (B n q Q t : ℕ) where
  σ : Env
  active : ℕ → ℕ
  label : ℕ → ℕ
  size : ℕ → ℕ
  ord : ℕ → ℕ
  count : ℕ → ℕ
  scratch : ℕ → ℕ
  repB : ℕ → ℕ
  sampleFlags : ℕ → ℕ
  repClass : ℕ → ℕ
  key0 : ℕ → ℕ
  bits : List Bool
  rest : List ℕ
  hnpos : 0 < n
  hn : σ.vars "n" = n
  hQpow : σ.vars "qpow" = Q
  hclassCount : σ.vars "classCount" = q
  hcap : σ.vars "drawCap" = t
  hinput : σ.inp = bits.map Bool.toNat ++ rest
  hactive : σ.arrs "activeB" = arrOf n active
  hlabel : σ.arrs "classB" = arrOf n label
  hsize : σ.arrs "classSize" = arrOf n size
  hord : σ.arrs "ord" = arrOf n ord
  hcount : σ.arrs "count" = arrOf Q count
  hscratch : σ.arrs "scratchOrder" = arrOf n scratch
  hrepB : σ.arrs "repB" = arrOf n repB
  hsampleFlags : σ.arrs "sampleFlags" = arrOf n sampleFlags
  hrepClass : σ.arrs "repClass" = arrOf n repClass
  hkey0 : σ.arrs "key0" = arrOf n key0
  hsizes : ClassSizes n q active label size
  hoccupied : ∀ d < q, 0 < size d
  hflags01 : ∀ v < n, active v ≤ 1
  hqQ : q ≤ Q
  hQB : Q < B
  hnB : n < B
  htB : t < B
  htwoB : 2 < B
  honeB : 1 < B
  hbudget : bitBudget size t 0 q ≤ bits.length
  hpowB : ∀ d < q, 2 ^ Nat.clog 2 (size d) < B

/-- Raw input for an initial attempt. The only sample facts are the enumerated
ground set and arbitrary old flags; the sample and its partition are produced
by the composed source below. -/
structure Input (B n m domainCap r t bufferCap targetCap Q : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ) (A : Finset ℕ) where
  σ : Env
  key0 : ℕ → ℕ
  domain : ℕ → ℕ
  oldDraws : ℕ → ℕ
  oldFlags : ℕ → ℕ
  ord : ℕ → ℕ
  activeB : ℕ → ℕ
  classB : ℕ → ℕ
  classSize : ℕ → ℕ
  markedCount : ℕ → ℕ
  stamp : ℕ → ℕ
  marked : ℕ → ℕ
  touched : ℕ → ℕ
  split : ℕ → ℕ
  repB : ℕ → ℕ
  count : ℕ → ℕ
  scratchOrder : ℕ → ℕ
  repClass : ℕ → ℕ
  bits : List Bool
  rest : List ℕ
  hx : EncodesGraph x n G
  htargetCapEq : targetCap = 2 * edgeCount x
  henum : PrefixEnumerates m domain A
  hAnonempty : A.Nonempty
  hA : A ⊆ Finset.range n
  hn : σ.vars "n" = n
  hQpow : σ.vars "qpow" = Q
  hactiveBCount : σ.vars "activeBCount" = (activeVertices n activeB).card
  hdrawModulus : σ.vars "drawModulus" = m
  hbatchTarget : σ.vars "batchTarget" = r
  hdrawCap : σ.vars "drawCap" = t
  hinput : σ.inp = bits.map Bool.toNat ++ rest
  hkey0 : σ.arrs "key0" = arrOf n key0
  hdrawDomain : σ.arrs "drawDomain" = arrOf domainCap domain
  hsampleDraws : σ.arrs "sampleDraws" = arrOf bufferCap oldDraws
  hsampleFlags : σ.arrs "sampleFlags" = arrOf n oldFlags
  hord : σ.arrs "ord" = arrOf n ord
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htarget : σ.arrs "tgt" = arrOf targetCap (target x)
  hactiveB : σ.arrs "activeB" = arrOf n activeB
  hclassB : σ.arrs "classB" = arrOf n classB
  hclassSize : σ.arrs "classSize" = arrOf n classSize
  hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount
  hstamp : σ.arrs "stamp" = arrOf n stamp
  hmarked : σ.arrs "marked" = arrOf n marked
  htouched : σ.arrs "touched" = arrOf n touched
  hsplit : σ.arrs "split" = arrOf n split
  hrepB : σ.arrs "repB" = arrOf n repB
  hcount : σ.arrs "count" = arrOf Q count
  hscratch : σ.arrs "scratchOrder" = arrOf n scratchOrder
  hrepClass : σ.arrs "repClass" = arrOf n repClass
  hactive01 : ∀ v < n, activeB v ≤ 1
  hQle : n ≤ Q
  hQltB : Q < B
  hnPlusOneB : n + 1 < B
  htargetCapB : targetCap < B
  hrBuf : r ≤ bufferCap
  hrB : r < B
  htB : t < B
  hmPos : 0 < m
  hmCap : m ≤ domainCap
  hmB : m < B
  htwoB : 2 < B
  honeB : 1 < B
  hpowM : 2 ^ Nat.clog 2 m < B
  hpowN : 2 ^ Nat.clog 2 n < B
  hbudget : r * t * Nat.clog 2 m + n * t * Nat.clog 2 n ≤ bits.length

/-- A per-class fixed upper width bounds the remaining representative tape. -/
private lemma bitBudget_le_uniform {size : ℕ → ℕ} {t d q width : ℕ}
    (hwidth : ∀ j, d + j < d + q → Nat.clog 2 (size (d + j)) ≤ width) :
    bitBudget size t d q ≤ q * t * width := by
  induction q generalizing d with
  | zero => simp [bitBudget]
  | succ q ih =>
      simp only [bitBudget]
      have hhead := hwidth 0 (by omega)
      have hhead' : Nat.clog 2 (size d) ≤ width := by simpa using hhead
      have htail : ∀ j, (d + 1) + j < (d + 1) + q →
          Nat.clog 2 (size ((d + 1) + j)) ≤ width := by
        intro j hj
        have h := hwidth (j + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hrec := ih (d := d + 1) htail
      nlinarith [hhead', hrec]

/-- The fixed representative-selection suffix executes from a full-sample
partition state, retaining the actual capped representative trace, exact
unread tape, and the failed/successful representative-map branch. -/
lemma initialRepresentativeSelection_run_bits {B n q Q t : ℕ}
    (I : RepresentativeInput B n q Q t) :
    ∃ (σ' : Env) (xs : List ℕ) (sorted : ℕ → ℕ)
      (values : List ℕ) (used charge : ℕ) (failed : Bool),
      Run B initialRepresentativeSelection I.σ σ'
        (20 * n + 9 + charge + 64 * (xs.length + Q + 1) + 104 * n + 24) ∧
      xs.Nodup ∧ xs.toFinset = activeVertices n I.active ∧
      xs.length = (activeVertices n I.active).card ∧
      ClassTrace I.size t (classStart I.size) 0 q I.bits values used charge failed ∧
      σ'.arrs "classSize" = arrOf n I.size ∧
      σ'.arrs "ord" = arrOf n sorted ∧
      (∀ i < xs.length, sorted i = (bucketSort Q I.label xs).getD i 0) ∧
      σ'.arrs "classB" = arrOf n I.label ∧
      σ'.arrs "activeB" = arrOf n I.active ∧
      σ'.arrs "sampleFlags" = arrOf n I.sampleFlags ∧
      σ'.vars "repFailed" = (if failed then 1 else 0) ∧
      (failed = false ↔ σ'.vars "repIndex" = q) ∧
      values.length ≤ q ∧ used ≤ I.bits.length ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = Q ∧
      σ'.vars "classCount" = q ∧ σ'.vars "drawCap" = t ∧
      σ'.inp = (I.bits.drop used).map Bool.toNat ++ I.rest ∧
      σ'.out = I.σ.out ∧
      (failed = true → σ'.arrs "repB" = arrOf n I.repB ∧ σ'.vars "v" = 0) ∧
      (failed = false → ∃ mapped : ℕ → ℕ,
        σ'.arrs "repB" = arrOf n mapped ∧ σ'.vars "v" = n ∧
        (∀ w < n, I.active w = 1 →
          mapped w = writeClassReps sorted I.repClass 0 values (I.label w)) ∧
        (∀ w < n, I.active w = 1 →
          w ∈ xs ∧ mapped w ∈ xs ∧ I.label (mapped w) = I.label w)) := by
  obtain ⟨σ₁, packed, hpack, hactive₁, hord₁, hprefix₁, halen₁,
      _, hframeArr₁, hframeVar₁, hinput₁, hout₁⟩ :=
    packActiveB_run I.hn I.hactive I.hord I.hflags01 I.hnB I.honeB
  let xs := Stack.toList (σ₁.vars "alen") packed
  have hset : xs.toFinset = activeVertices n I.active := by
    ext v
    simpa [xs, flaggedVertices] using (hprefix₁.2 v)
  have hnodup : xs.Nodup := hprefix₁.1
  have hlen : xs.length = (activeVertices n I.active).card := by
    simp [xs, halen₁, flaggedVertices]
  have hxn : xs.length ≤ n := by
    rw [hlen]
    have hsub : activeVertices n I.active ⊆ Finset.range n := by
      intro v hv
      exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
    simpa using Finset.card_le_card hsub
  have hvertex : ∀ v ∈ xs, v < n := by
    intro v hv
    exact (mem_activeVertices.mp (hset ▸ List.mem_toFinset.mpr hv)).1
  have hlabels : ∀ v ∈ xs, I.label v < q := by
    intro v hv
    have hvActive : v ∈ activeVertices n I.active := by
      rw [← hset]
      exact List.mem_toFinset.mpr hv
    obtain ⟨hvN, hvFlag⟩ := mem_activeVertices.mp hvActive
    exact I.hsizes.1 v hvN hvFlag
  have hsizeCount := ClassSizes.countDigit I.hsizes xs hnodup hset
  have hordPrefix : ∀ i < xs.length, packed i = xs.getD i 0 := by
    intro i hi
    have hi' : i < σ₁.vars "alen" := by simpa [xs, Stack.toList] using hi
    change packed i = (arrOf (σ₁.vars "alen") packed).getD i 0
    exact (getD_arrOf packed hi').symm
  have hactiveBound : ∀ v < n, I.active v < B := by
    intro v hv
    have hflag := I.hflags01 v hv
    exact lt_of_le_of_lt hflag I.honeB
  have hinputPack : σ₁.inp = I.bits.map Bool.toNat ++ I.rest := by
    rw [hinput₁]
    exact I.hinput
  have hclassCount : σ₁.vars "classCount" = q := by
    rw [hframeVar₁ "classCount" (by decide) (by decide)]
    exact I.hclassCount
  have hn : σ₁.vars "n" = n := by
    rw [hframeVar₁ "n" (by decide) (by decide)]
    exact I.hn
  have hQpow : σ₁.vars "qpow" = Q := by
    rw [hframeVar₁ "qpow" (by decide) (by decide)]
    exact I.hQpow
  have hcap : σ₁.vars "drawCap" = t := by
    rw [hframeVar₁ "drawCap" (by decide) (by decide)]
    exact I.hcap
  have hrepClass : σ₁.arrs "repClass" = arrOf n I.repClass := by
    rw [hframeArr₁ "repClass" (by decide)]
    exact I.hrepClass
  have hkey0 : σ₁.arrs "key0" = arrOf n I.key0 := by
    rw [hframeArr₁ "key0" (by decide)]
    exact I.hkey0
  have hsize₁ : σ₁.arrs "classSize" = arrOf n I.size := by
    rw [hframeArr₁ "classSize" (by decide)]
    exact I.hsize
  have hcount₁ : σ₁.arrs "count" = arrOf Q I.count := by
    rw [hframeArr₁ "count" (by decide)]
    exact I.hcount
  have hscratch₁ : σ₁.arrs "scratchOrder" = arrOf n I.scratch := by
    rw [hframeArr₁ "scratchOrder" (by decide)]
    exact I.hscratch
  have hlabel₁ : σ₁.arrs "classB" = arrOf n I.label := by
    rw [hframeArr₁ "classB" (by decide)]
    exact I.hlabel
  have hrepB₁ : σ₁.arrs "repB" = arrOf n I.repB := by
    rw [hframeArr₁ "repB" (by decide)]
    exact I.hrepB
  obtain ⟨values, used, charge, failed, σ₂, sorted,
      htrace, hgroup, hsize', hord', hsorted, hlabel', hactive', hrepClass',
      hrepIndex, hrepFailed, hcomplete, hnum, hused, hn', hQpow',
      hclassCount', hcap', hinp', hout', hframe', hrepFailure, hrepSuccess⟩ :=
    groupedClassRepresentatives_run_bits (σ := σ₁) I.hnpos hxn hnodup hvertex hlabels
      hsizeCount I.hoccupied hsize₁ hord₁ hordPrefix hcount₁ hscratch₁
      hlabel₁ hactive₁ hrepClass hrepB₁ hkey0
      (by
        intro w hw hactive
        have hwmem : w ∈ activeVertices n I.active :=
          mem_activeVertices.mpr ⟨hw, hactive⟩
        have hmem : w ∈ xs.toFinset := by rw [hset]; exact hwmem
        exact List.mem_toFinset.mp hmem)
      hactiveBound hclassCount (by simpa [xs, Stack.toList, flaggedVertices] using halen₁)
      hn hQpow hcap hinputPack I.hqQ I.hQB I.hnB I.htB I.htwoB
      I.hbudget I.hpowB
  have hrun : Run B initialRepresentativeSelection I.σ σ₂
      (20 * n + 9 + charge + 64 * (xs.length + Q + 1) + 104 * n + 24) := by
    change Run B (packActiveBSource.seq groupedClassRepresentatives)
      I.σ σ₂ _
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpack.seq hgroup
  refine ⟨σ₂, xs, sorted, values, used, charge, failed, hrun, hnodup,
    hset, hlen, htrace, hsize', hord', hsorted, hlabel', hactive', ?_,
    hrepFailed, hcomplete, hnum, hused, hn', hQpow', hclassCount', hcap',
    hinp', hout'.trans hout₁, hrepFailure, hrepSuccess⟩
  exact (hframe' "sampleFlags" (by decide)).trans
    ((hpack.frame_arr "sampleFlags" (by decide)).trans I.hsampleFlags)

/-- The initial source draws an actual sample, then derives classes from that
sample and selects representatives. A failed capped draw stops before either
partitioning or representative selection. -/
lemma initialSamplerAttempt_run_bits
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Input B n m domainCap r t bufferCap targetCap Q G x A) :
    ∃ (σd σ' : Env) (tape : Fin (r * t) → Fin (Nat.clog 2 m) → Bool)
      (tail : List Bool) (values : List (Fin m)) (used : ℕ)
      (drawFailed : Bool) (stageCost : ℕ),
      I.bits = tapeBits tape ++ tail ∧
      DrawTrace m I.hmPos t r (List.ofFn tape) values used drawFailed ∧
      Run B initialSamplerAttempt I.σ σ'
        (2 + initialDrawSampleCost n m used
          (values.length + if drawFailed then 1 else 0) values.length drawFailed +
          (if drawFailed then 5 else 4 + stageCost)) ∧
      σ'.vars "attemptAccepted" = 0 ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = Q ∧
      (∀ a, a ∉ initialSamplerAttempt.warrs →
        σ'.arrs a = I.σ.arrs a) ∧
      (∀ v, v ∉ initialSamplerAttempt.wvars →
        σ'.vars v = I.σ.vars v) ∧
      (drawFailed = true →
        σ'.vars "batchFailed" = 1 ∧
        σ'.arrs "sampleFlags" = arrOf n (fun _ => 0) ∧
        σ'.vars "sampleCount" = 0) ∧
      (drawFailed = false →
        ∃ (W : Finset ℕ) (sampleOrd : ℕ → ℕ) (sampleCount : ℕ)
          (σp : Env) (q : ℕ) (label size : ℕ → ℕ)
          (xs : List ℕ) (sorted : ℕ → ℕ) (repValues : List ℕ)
          (repUsed repCharge : ℕ) (repFailed : Bool),
          W = (values.map (fun i => I.domain i.val)).toFinset ∧
          W ⊆ A ∧
          W.card ≤ r ∧
          values.length = r ∧
          PrefixEnumerates sampleCount sampleOrd W ∧
          Run B fullSamplePartition σd σp
            (fullSamplePartitionCost x sampleOrd n sampleCount) ∧
          ClassSizes n q I.activeB label size ∧
          LabelsOccupyPrefix q label (activeVertices n I.activeB) ∧
          (∀ b ∈ activeVertices n I.activeB, ∀ b' ∈ activeVertices n I.activeB,
            (label b = label b' ↔
              trace (numericNeighborhood G) W b =
                trace (numericNeighborhood G) W b')) ∧
          Run B initialRepresentativeSelection σp σ'
            (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24) ∧
          σ'.vars "n" = n ∧ σ'.vars "qpow" = Q ∧
          σ'.vars "sampleCount" = W.card ∧
          σ'.arrs "classB" = arrOf n label ∧
          σ'.arrs "classSize" = arrOf n size ∧
          σ'.arrs "ord" = arrOf n sorted ∧
          xs.Nodup ∧ xs.toFinset = activeVertices n I.activeB ∧
          ClassTrace size t (classStart size) 0 q
            (I.bits.drop (used * Nat.clog 2 m)) repValues repUsed repCharge repFailed ∧
          σ'.vars "repFailed" = (if repFailed then 1 else 0) ∧
          (repFailed = true → σ'.arrs "repB" = σp.arrs "repB") ∧
          σ'.arrs "sampleFlags" = arrOf n (fun v => if v ∈ W then 1 else 0) ∧
          σ'.inp = (I.bits.drop (used * Nat.clog 2 m + repUsed)).map Bool.toNat ++ I.rest ∧
          (repFailed = false → ∃ mapped,
            σ'.arrs "repB" = arrOf n mapped ∧ σ'.vars "v" = n ∧
            (∀ w < n, I.activeB w = 1 →
              mapped w = writeClassReps sorted I.repClass 0 repValues (label w)) ∧
            (∀ w < n, I.activeB w = 1 →
              w ∈ xs ∧ mapped w ∈ xs ∧ label (mapped w) = label w)) ∧
          stageCost = fullSamplePartitionCost x sampleOrd n sampleCount +
            (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24)) := by
  let σ₀ := I.σ.setVar "attemptAccepted" 0
  have hBpos : 0 < B := Nat.lt_trans (by decide) I.htwoB
  have hinit : Run B (.assign "attemptAccepted" (.lit 0)) I.σ σ₀ 2 := by
    simpa [σ₀] using (Run.assign (evalB_lit hBpos))
  have hn₀ : σ₀.vars "n" = n := by simp [σ₀, I.hn]
  have hqpow₀ : σ₀.vars "qpow" = Q := by simp [σ₀, I.hQpow]
  have hmod₀ : σ₀.vars "drawModulus" = m := by simp [σ₀, I.hdrawModulus]
  have htarget₀ : σ₀.vars "batchTarget" = r := by simp [σ₀, I.hbatchTarget]
  have hcap₀ : σ₀.vars "drawCap" = t := by simp [σ₀, I.hdrawCap]
  have hinp₀ : σ₀.inp = I.bits.map Bool.toNat ++ I.rest := by
    simpa [σ₀] using I.hinput
  have hkey₀ : σ₀.arrs "key0" = arrOf n I.key0 := by simp [σ₀, I.hkey0]
  have hdomain₀ : σ₀.arrs "drawDomain" = arrOf domainCap I.domain := by
    simp [σ₀, I.hdrawDomain]
  have hdraws₀ : σ₀.arrs "sampleDraws" = arrOf bufferCap I.oldDraws := by
    simp [σ₀, I.hsampleDraws]
  have hflags₀ : σ₀.arrs "sampleFlags" = arrOf n I.oldFlags := by
    simp [σ₀, I.hsampleFlags]
  have hord₀ : σ₀.arrs "ord" = arrOf n I.ord := by simp [σ₀, I.hord]
  have hdrawBudget : r * t * Nat.clog 2 m ≤ I.bits.length := by
    exact (Nat.le_add_right _ _).trans I.hbudget
  obtain ⟨tape, tail, hsplit, values, used, drawFailed, σd, key',
      htrace, hdraw, hbad, hdrawCount, hdrawNum, hdrawComplete, hdrawFailure,
      hdrawSuccess, hdrawInp, hdrawOut, hdrawArrayFrame, hdrawVarFrame,
      hkeyOutside, hkeyFinal, hdomainFinal, hnSource, hqSource⟩ :=
    initialDrawSampleSource_run_bits (B := B) (n := n) (m := m)
      (domainCap := domainCap) (r := r) (t := t) (bufferCap := bufferCap)
      (σ := σ₀) (key := I.key0) (domain := I.domain)
      (oldDraws := I.oldDraws) (oldFlags := I.oldFlags) (ord := I.ord)
      (A := A) (bits := I.bits) (rest := I.rest)
      (by simpa [σ₀] using I.hn)
      (Nat.lt_trans (Nat.lt_succ_self n) I.hnPlusOneB)
      (by simpa [σ₀, I.hQpow] using I.hQltB)
      hmod₀ I.hmPos I.hmCap I.henum I.hAnonempty I.hA hkey₀ hdomain₀ hdraws₀
      hflags₀ hord₀ htarget₀ hcap₀ I.hrBuf I.hrB I.htB I.hmB I.htwoB I.honeB
      hdrawBudget hinp₀ I.hpowM
  have hacceptedDraw : σd.vars "attemptAccepted" = 0 := by
    rw [hdrawVarFrame "attemptAccepted" (by decide)]
    simp [σ₀]
  have hcondition :
      (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σd = some (!drawFailed) := by
    have hbadVal : σd.vars "batchFailed" = if drawFailed then 1 else 0 := hbad
    have hzeroB : 0 < B := Nat.lt_trans (by decide) I.htwoB
    have honeB' : 1 < B := I.honeB
    have hvar : (Expr.var "batchFailed").evalB B σd =
        some (if drawFailed then 1 else 0) := by
      cases drawFailed with
      | false =>
          have hb : σd.vars "batchFailed" < B := by simpa [hbad] using hzeroB
          simpa [hbad] using (evalB_var (x := "batchFailed") hb)
      | true =>
          have hb : σd.vars "batchFailed" < B := by simpa [hbad] using honeB'
          simpa [hbad] using (evalB_var (x := "batchFailed") hb)
    have hlit : (Expr.lit 0).evalB B σd = some 0 := evalB_lit hzeroB
    rw [evalB_condEq hvar hlit]
    cases drawFailed <;> rfl
  cases drawFailed with
  | true =>
      have hbranch : Run B
          (.ite (.eq (.var "batchFailed") (.lit 0))
            (fullSamplePartition.seq initialRepresentativeSelection) .skip)
          σd σd 5 := by
        have hfalse : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σd = some false := by
          simpa using hcondition
        simpa [Cond.size, Expr.size] using
          (Run.ite_false hfalse (Run.skip : Run B .skip σd σd 1))
      have htail : Run B
          (initialDrawSampleSource.seq
            (.ite (.eq (.var "batchFailed") (.lit 0))
              (fullSamplePartition.seq initialRepresentativeSelection) .skip))
          σ₀ σd
          (initialDrawSampleCost n m used (values.length + 1) values.length true + 5) := by
        simpa [initialDrawSampleSource, Nat.add_assoc] using hdraw.seq hbranch
      have hwhole : Run B initialSamplerAttempt I.σ σd
          (2 + initialDrawSampleCost n m used (values.length + 1) values.length true + 5) := by
        change Run B ((Com.assign "attemptAccepted" (.lit 0)).seq
          (initialDrawSampleSource.seq
            (.ite (.eq (.var "batchFailed") (.lit 0))
              (fullSamplePartition.seq initialRepresentativeSelection) .skip)))
          I.σ σd _
        exact hinit.seq htail
      have haccepted : σd.vars "attemptAccepted" = 0 := hacceptedDraw
      refine ⟨σd, σd, tape, tail, values, used, true, 0,
        hsplit, htrace, ?_, haccepted, hnSource, hqSource.trans hqpow₀,
        ?_, ?_, ?_, ?_⟩
      · simpa [initialSamplerAttempt, initialDrawSampleCost, Nat.add_assoc] using hwhole
      · intro a ha
        exact hwhole.frame_arr a ha
      · intro v hv
        exact hwhole.frame_var v hv
      · intro _
        have hf := hdrawFailure rfl
        exact ⟨by simpa [hbad], hf.1, hf.2⟩
      · intro hsuccess
        cases hsuccess
  | false =>
      obtain ⟨hflagsDraw, sampleOrd, hordDraw, hprefixDraw, hcountDraw,
          hdrawDomain, hsampleBound⟩ := hdrawSuccess rfl
      let W : Finset ℕ :=
        (values.map (fun i => I.domain i.val)).toFinset
      have hWsubset : W ⊆ A := by
        intro v hv
        rcases List.mem_map.mp (List.mem_toFinset.mp hv) with ⟨a, ha, heq⟩
        subst v
        obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ha
        have := hdrawDomain i hi
        simpa [hget] using this
      have hWrange : W ⊆ Finset.range n := hWsubset.trans I.hA
      have hsampleCount : σd.vars "sampleCount" = W.card := by
        simpa [W] using hcountDraw
      have hsampleFlagsExact : σd.arrs "sampleFlags" =
          arrOf n (fun v => if v ∈ W then 1 else 0) := by
        simpa [W] using hflagsDraw
      have hsampleCountN : W.card ≤ n := by
        have hc := Finset.card_le_card hWrange
        simpa using hc
      have hactiveBCountDraw : σd.vars "activeBCount" =
          (activeVertices n I.activeB).card := by
        rw [hdrawVarFrame "activeBCount" (by decide)]
        exact I.hactiveBCount
      have hoffDraw : σd.arrs "off" = arrOf (n + 1) (offset x) := by
        rw [hdrawArrayFrame "off" (by decide)]
        exact I.hoff
      have htargetDraw : σd.arrs "tgt" = arrOf targetCap (target x) := by
        rw [hdrawArrayFrame "tgt" (by decide)]
        exact I.htarget
      have hactiveDraw : σd.arrs "activeB" = arrOf n I.activeB := by
        rw [hdrawArrayFrame "activeB" (by decide)]
        exact I.hactiveB
      have hclassBDraw : σd.arrs "classB" = arrOf n I.classB := by
        rw [hdrawArrayFrame "classB" (by decide)]
        exact I.hclassB
      have hclassSizeDraw : σd.arrs "classSize" = arrOf n I.classSize := by
        rw [hdrawArrayFrame "classSize" (by decide)]
        exact I.hclassSize
      have hmarkedCountDraw : σd.arrs "markedCount" = arrOf n I.markedCount := by
        rw [hdrawArrayFrame "markedCount" (by decide)]
        exact I.hmarkedCount
      have hstampDraw : σd.arrs "stamp" = arrOf n I.stamp := by
        rw [hdrawArrayFrame "stamp" (by decide)]
        exact I.hstamp
      have hmarkedDraw : σd.arrs "marked" = arrOf n I.marked := by
        rw [hdrawArrayFrame "marked" (by decide)]
        exact I.hmarked
      have htouchedDraw : σd.arrs "touched" = arrOf n I.touched := by
        rw [hdrawArrayFrame "touched" (by decide)]
        exact I.htouched
      have hsplitDraw : σd.arrs "split" = arrOf n I.split := by
        rw [hdrawArrayFrame "split" (by decide)]
        exact I.hsplit
      have hrepBDraw : σd.arrs "repB" = arrOf n I.repB := by
        rw [hdrawArrayFrame "repB" (by decide)]
        exact I.hrepB
      let P : FullSamplePartition.Input B n targetCap W.card G x W := {
        σ := σd
        activeB := I.activeB
        ord := sampleOrd
        classB := I.classB
        classSize := I.classSize
        markedCount := I.markedCount
        stamp := I.stamp
        marked := I.marked
        touched := I.touched
        split := I.split
        repB := I.repB
        sampleFlags := fun v => if v ∈ W then 1 else 0
        hx := I.hx
        htargetCap := I.htargetCapEq
        hn := hnSource
        hsampleCount := hsampleCount
        hactiveBCount := hactiveBCountDraw
        hoff := hoffDraw
        htarget := htargetDraw
        hactiveB := hactiveDraw
        hord := by simpa using hordDraw
        hclassB := hclassBDraw
        hclassSize := hclassSizeDraw
        hmarkedCount := hmarkedCountDraw
        hstamp := hstampDraw
        hmarked := hmarkedDraw
        htouched := htouchedDraw
        hsplit := hsplitDraw
        hrepB := hrepBDraw
        hsampleFlags := hsampleFlagsExact
        henum := by simpa [W, hsampleCount] using hprefixDraw
        hWrange := hWrange
        hsampleCountN := hsampleCountN
        hnB := Nat.lt_trans (Nat.lt_succ_self n) I.hnPlusOneB
        htargetCapB := I.htargetCapB
        honeB := I.honeB
        hactiveBBound := fun v hv => Nat.lt_of_le_of_lt (I.hactive01 v hv) I.honeB
      }
      obtain ⟨σp, q, label, size, hpartition, hq, hqle, hlabel,
          hsize, hsizes, hoccupied, hclassifies, hactiveP, hflagsP,
          hordP, hrepBP, hoffP, htargetP, hnP, hcountP, hactiveCountP,
          hinP, houtP, hframePartArr, hframePartVar⟩ :=
        fullSamplePartition_run P
      have hrepInputBits : σp.inp =
          (I.bits.drop (used * Nat.clog 2 m)).map Bool.toNat ++ I.rest := by
        calc
          σp.inp = P.σ.inp := hinP
          _ = σd.inp := rfl
          _ = (I.bits.drop (used * Nat.clog 2 m)).map Bool.toNat ++ I.rest := hdrawInp
      have hrepClassDraw : σd.arrs "repClass" = arrOf n I.repClass := by
        rw [hdrawArrayFrame "repClass" (by decide)]
        exact I.hrepClass
      have hkey0Part : σp.arrs "key0" = arrOf n key' := by
        rw [hframePartArr "key0" (by decide)]
        exact hkeyFinal
      have hsizeLe : ∀ d < q, size d ≤ n := by
        intro d hd
        rw [hsizes.2 d hd]
        exact (classMultiplicity_le_card _ _ _).trans (activeVertices_card_le n I.activeB)
      have hwidth : ∀ j, 0 + j < 0 + q →
          Nat.clog 2 (size (0 + j)) ≤ Nat.clog 2 n := by
        intro j hj
        apply Nat.clog_mono_right
        simpa using hsizeLe j (by simpa using hj)
      have hbudgetUniform : bitBudget size t 0 q ≤ q * t * Nat.clog 2 n :=
        bitBudget_le_uniform hwidth
      have hbudgetN : bitBudget size t 0 q ≤ n * t * Nat.clog 2 n := by
        exact hbudgetUniform.trans (Nat.mul_le_mul_right (Nat.clog 2 n)
          (Nat.mul_le_mul_right t hqle))
      have husedTrace := DrawTrace.used_and_calls m I.hmPos t htrace
      have husedLe : used ≤ r * t := by simpa using husedTrace.1
      have hconsumed : used * Nat.clog 2 m ≤ r * t * Nat.clog 2 m := by
        exact Nat.mul_le_mul_right _ husedLe
      have hbudgetResidual : bitBudget size t 0 q ≤
          (I.bits.drop (used * Nat.clog 2 m)).length := by
        simp only [List.length_drop]
        have hsum : used * Nat.clog 2 m + bitBudget size t 0 q ≤ I.bits.length := by
          calc
            used * Nat.clog 2 m + bitBudget size t 0 q ≤
                r * t * Nat.clog 2 m + n * t * Nat.clog 2 n :=
              Nat.add_le_add hconsumed hbudgetN
            _ ≤ I.bits.length := I.hbudget
        exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)
      have hpowEach : ∀ d < q, 2 ^ Nat.clog 2 (size d) < B := by
        intro d hd
        have hc := Nat.clog_mono_right 2 (hsizeLe d hd)
        have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hc
        exact lt_of_le_of_lt hp I.hpowN
      have hcountPart : σp.arrs "count" = arrOf Q I.count := by
        rw [hframePartArr "count" (by decide)]
        rw [hdrawArrayFrame "count" (by decide)]
        exact I.hcount
      have hscratchPart : σp.arrs "scratchOrder" = arrOf n I.scratchOrder := by
        rw [hframePartArr "scratchOrder" (by decide)]
        rw [hdrawArrayFrame "scratchOrder" (by decide)]
        exact I.hscratch
      have hrepClassPart : σp.arrs "repClass" = arrOf n I.repClass := by
        rw [hframePartArr "repClass" (by decide)]
        exact hrepClassDraw
      have hrepBPart : σp.arrs "repB" = arrOf n I.repB := hrepBP
      let RI : RepresentativeInput B n q Q t := {
        σ := σp
        active := I.activeB
        label := label
        size := size
        ord := sampleOrd
        count := I.count
        scratch := I.scratchOrder
        repB := I.repB
        sampleFlags := fun v => if v ∈ W then 1 else 0
        repClass := I.repClass
        key0 := key'
        bits := I.bits.drop (used * Nat.clog 2 m)
        rest := I.rest
        hnpos := by
          obtain ⟨v, hv⟩ := I.hAnonempty
          have := Finset.mem_range.mp (I.hA hv)
          omega
        hn := by rw [hframePartVar "n" (by decide)]; exact hnSource
        hQpow := by
          rw [hframePartVar "qpow" (by decide)]
          simpa [σ₀, I.hQpow] using hqSource
        hclassCount := hq
        hcap := by
          rw [hframePartVar "drawCap" (by decide)]
          rw [hdrawVarFrame "drawCap" (by decide)]
          exact I.hdrawCap
        hinput := hrepInputBits
        hactive := hactiveP
        hlabel := hlabel
        hsize := hsize
        hord := by simpa using hordP
        hcount := hcountPart
        hscratch := hscratchPart
        hrepB := hrepBPart
        hsampleFlags := hflagsP
        hrepClass := hrepClassPart
        hkey0 := hkey0Part
        hsizes := hsizes
        hoccupied := by
          intro d hd
          rw [hsizes.2 d hd]
          exact hoccupied d hd
        hflags01 := I.hactive01
        hqQ := hqle.trans I.hQle
        hQB := I.hQltB
        hnB := Nat.lt_trans (Nat.lt_succ_self n) I.hnPlusOneB
        htB := I.htB
        htwoB := I.htwoB
        honeB := I.honeB
        hbudget := hbudgetResidual
        hpowB := hpowEach
      }
      obtain ⟨σrep, xs, sorted, repValues, repUsed, repCharge, repFailed,
          hrepRun, hnodup, hset, hlen, hclassTrace, hsizeRep, hordRep,
          hsorted, hlabelRep, hactiveRep, hflagsRep, hrepFailedVal,
          hrepComplete, hrepNum, hrepUsedBound, hnRep, hqRep, hclassCountRep,
          hcapRep, hinpRep, houtRep, hrepFailure, hrepSuccess⟩ :=
        initialRepresentativeSelection_run_bits RI
      have hpartAndRep : Run B
          (fullSamplePartition.seq initialRepresentativeSelection)
          σd σrep
          (fullSamplePartitionCost x sampleOrd n W.card +
            (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24)) := by
        exact hpartition.seq hrepRun
      have htail : Run B
          (initialDrawSampleSource.seq
            (.ite (.eq (.var "batchFailed") (.lit 0))
              (fullSamplePartition.seq initialRepresentativeSelection) .skip))
          σ₀ σrep
          (initialDrawSampleCost n m used (values.length + 0) values.length false +
            4 + fullSamplePartitionCost x sampleOrd n W.card +
              (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24)) := by
        have htrue : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σd = some true := by
          simpa using hcondition
        have hite : Run B
            (.ite (.eq (.var "batchFailed") (.lit 0))
              (fullSamplePartition.seq initialRepresentativeSelection) .skip)
            σd σrep
            (4 + fullSamplePartitionCost x sampleOrd n W.card +
              (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24)) := by
          simpa [Cond.size, Expr.size, Nat.add_assoc] using
            (Run.ite_true (d := .skip) htrue hpartAndRep)
        simpa [Nat.add_assoc] using hdraw.seq hite
      have hwhole : Run B initialSamplerAttempt I.σ σrep
          (2 + initialDrawSampleCost n m used (values.length + 0) values.length false +
            4 + fullSamplePartitionCost x sampleOrd n W.card +
              (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24)) := by
        change Run B ((Com.assign "attemptAccepted" (.lit 0)).seq
          (initialDrawSampleSource.seq
            (.ite (.eq (.var "batchFailed") (.lit 0))
              (fullSamplePartition.seq initialRepresentativeSelection) .skip)))
          I.σ σrep
          (2 + initialDrawSampleCost n m used (values.length + 0) values.length false +
            4 + fullSamplePartitionCost x sampleOrd n W.card +
              (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24))
        simpa [Nat.add_assoc] using hinit.seq htail
      have haccepted : σrep.vars "attemptAccepted" = 0 := by
        calc
          σrep.vars "attemptAccepted" = σp.vars "attemptAccepted" :=
            hrepRun.frame_var "attemptAccepted" (by decide)
          _ = P.σ.vars "attemptAccepted" := hframePartVar "attemptAccepted" (by decide)
          _ = 0 := by simpa [P] using hacceptedDraw
      have htraceClass : ∀ b ∈ activeVertices n I.activeB,
          ∀ b' ∈ activeVertices n I.activeB,
            (label b = label b' ↔
              trace (numericNeighborhood G) W b =
                trace (numericNeighborhood G) W b') := hclassifies
      have hqpowFinal : σrep.vars "qpow" = Q := by
        exact hqRep
      have hwholeArrFrame : ∀ a, a ∉ initialSamplerAttempt.warrs →
          σrep.arrs a = I.σ.arrs a := by
        intro a ha
        exact hwhole.frame_arr a ha
      have hwholeVarFrame : ∀ v, v ∉ initialSamplerAttempt.wvars →
          σrep.vars v = I.σ.vars v := by
        intro v hv
        exact hwhole.frame_var v hv
      refine ⟨σd, σrep, tape, tail, values, used, false,
        fullSamplePartitionCost x sampleOrd n W.card +
          (20 * n + 9 + repCharge + 64 * (xs.length + Q + 1) + 104 * n + 24),
        hsplit, htrace, ?_, haccepted, hnRep, hqpowFinal,
        hwholeArrFrame, hwholeVarFrame, ?_, ?_⟩
      · simpa [initialSamplerAttempt, Nat.add_assoc,
          Cond.size, Expr.size] using hwhole
      · intro hbadCase
        cases hbadCase
      · intro _
        refine ⟨W, sampleOrd, W.card, σp, q, label, size, xs, sorted,
          repValues, repUsed, repCharge, repFailed, rfl, hWsubset,
          (by simpa [W] using hsampleBound),
          (by
            have hcountEq := hdrawCount
            have hcompleteEq := hdrawComplete.mp rfl
            omega),
          (by simpa [W, hsampleCount] using hprefixDraw), hpartition,
          hsizes, hoccupied, htraceClass,
          hrepRun, hnRep, hqpowFinal,
          (by
            calc
              σrep.vars "sampleCount" = σp.vars "sampleCount" :=
                hrepRun.frame_var "sampleCount" (by decide)
              _ = σd.vars "sampleCount" := hframePartVar "sampleCount" (by decide)
              _ = W.card := hsampleCount),
          hlabelRep, hsizeRep,
          hordRep,
          hnodup, hset, hclassTrace, hrepFailedVal, ?_, ?_, ?_, ?_⟩
        · intro hfailed
          exact (hrepFailure hfailed).1.trans hrepBP.symm
        · exact hflagsRep
        · simpa [RI, Nat.add_comm] using hinpRep
        · constructor
          · intro hsuccess
            obtain ⟨mapped, hmap, hv, hformula, hclass⟩ := hrepSuccess hsuccess
            refine ⟨mapped, hmap, hv, hformula, ?_⟩
            intro w hw hactive
            obtain ⟨hmem, hmapped, hsame⟩ := hclass w hw hactive
            exact ⟨hmem, hmapped, hsame⟩
          · rfl

end Lax457868Proofs.InitialSamplerAttempt
