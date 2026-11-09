import Lax457868Proofs.LocalRepairRetriesSource
import Lax457868Proofs.LocalRepairPhase3
import Lax457868Proofs.SamplerOutputSize
import Lax457868Proofs.SamplePacking
import Mathlib.Tactic

/-! A single source loop over the packed phase-three exception list. -/

namespace Lax457868Proofs.ExceptionRepairLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.LocalRepairRetriesSource
open Lax457868Proofs.LocalRepairSource
open Lax457868Proofs.RepairFilterSource
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.RepairClassScan
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplePacking
open Lax11.GraphEncoding
open scoped symmDiff

noncomputable section

set_option maxHeartbeats 2000000

/-- The loop reads the packed exception at the current index. On a completed
repair it advances; on a draw failure or exhaustion it freezes the stop index.
The original exception count and the packed list are never changed. -/
def exceptionRepairBody : Com :=
  (Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
    (localRepairOneExceptionSource.seq
      (.ite (.eq (.var "repairRetryStatus") (.lit 1))
        (.assign "exceptionIndex" (.add (.var "exceptionIndex") (.lit 1)))
        (.assign "exceptionStop" (.var "exceptionIndex"))))

/-- Initialize the control state while leaving the packed list and all sample
and class arrays untouched. -/
def exceptionRepairInit : Com :=
  (Com.assign "exceptionIndex" (.lit 0)).seq
    ((Com.assign "exceptionStop" (.var "exceptionCount")).seq
      (Com.assign "repairRetryStatus" (.lit 1)))

/-- One fixed machine program for the entire phase-three exception list. -/
def exceptionRepairLoopSource : Com :=
  exceptionRepairInit.seq
    (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
      exceptionRepairBody)

/-- Pack the accumulated sample once, after all exceptions have completed. -/
def exceptionRepairPackedSource : Com :=
  exceptionRepairLoopSource.seq
    (.ite (.eq (.var "repairRetryStatus") (.lit 1))
      packMarkedSamples .skip)

/-- Per-exception cost of the domain builder, including both adjacency scans. -/
def domainCharge {n : ℕ} (x : List ℕ) (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (rep : ℕ → ℕ) (b : ℕ) : ℕ :=
  54 * ((offset x (b + 1) - offset x b) +
    (offset x (rep b + 1) - offset x (rep b))) +
  36 * (((numericNeighborhood G b ∩ A).card) +
    ((numericNeighborhood G (rep b) ∩ A).card)) + 73

/-- The runtime bound reported by the checked one-exception theorem: the near
branch has no retry cost; a far branch records its actual attempts and draws. -/
def oneExceptionCharge {n : ℕ} (x : List ℕ) (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (rep : ℕ → ℕ) (s scan b k attempts used : ℕ) : ℕ :=
  domainCharge x G A rep b +
    (if (((numericNeighborhood G b ∩ A) ∆
        (numericNeighborhood G (rep b) ∩ A)).card ≤ (2 * k) / 3)
      then 6
      else 4 + (12 * Nat.clog 2
          (((numericNeighborhood G b ∩ A) ∆
            (numericNeighborhood G (rep b) ∩ A)).card) + 24 +
        ((15 * Nat.clog 2
          (((numericNeighborhood G b ∩ A) ∆
            (numericNeighborhood G (rep b) ∩ A)).card) + 30) * used +
          attempts * (79 * s + scan + 50) + 14)))

/-- The class scan component for a vertex uses the fixed phase-two tables. -/
def classScanCharge (x : List ℕ) (size label ord : ℕ → ℕ)
    (b : ℕ) : ℕ :=
  66 * (offset x (b + 1) - offset x b) +
    repairClassPotential
      (classStart size (label b) + size (label b))
      (classStart size (label b))
      (repairClassSlotWeight x ord) + 47

/-- Factual machine state after phases one and two, with all fixed class data
for the *whole* packed exception set. The repair vertex and the domain buffer
are deliberately absent: each loop iteration reads and constructs them. -/
structure LoopInput (B n s t bufferCap targetCap q cap k e : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ)
    (E groupedB Wbase A Wcurrent : Finset ℕ) where
  σ : Env
  bits : List Bool
  rest : List ℕ
  exceptionList : ℕ → ℕ
  rep : ℕ → ℕ
  size : ℕ → ℕ
  starts : ℕ → ℕ
  label : ℕ → ℕ
  ord : ℕ → ℕ
  groupActive : ℕ → ℕ
  xs : List ℕ
  hgraph : EncodesGraph x n G
  htargetCap : targetCap = 2 * edgeCount x
  hinput : σ.inp = bits.map Bool.toNat ++ rest
  hn : σ.vars "n" = n
  hqpow : σ.vars "qpow" < B
  htarget : σ.vars "batchTarget" = s
  hdrawCap : σ.vars "drawCap" = t
  hclassCount : σ.vars "classCount" = q
  hretryCap : σ.vars "repairRetryCap" = cap
  hfarBound : σ.vars "repairFarBound" = (2 * k) / 3
  hexceptionCount : σ.vars "exceptionCount" = e
  hexceptionList : σ.arrs "exceptionList" = arrOf n exceptionList
  hprefix : PrefixEnumerates e exceptionList E
  hrep : σ.arrs "repB" = arrOf n rep
  hactive : σ.arrs "activeA" = arrOf n (setFlag A)
  hdrawDomainLength : (σ.arrs "drawDomain").length = n
  hkeyLength : (σ.arrs "key0").length = n
  hdrawsLength : (σ.arrs "sampleDraws").length = bufferCap
  hsample : σ.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)
  htrialZero : σ.arrs "trialActive" = arrOf n (fun _ => 0)
  hrowZero : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0)
  hdesiredZero : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0)
  hrowLength : (σ.arrs "trialRowList").length = n
  hdesiredLength : (σ.arrs "trialDesiredList").length = n
  hdiffLength : (σ.arrs "trialDiffList").length = n
  hBListLength : (σ.arrs "repairBList").length = n
  hRListLength : (σ.arrs "repairRList").length = n
  hBMarksZero : σ.arrs "repairBMarks" = arrOf n (fun _ => 0)
  hRMarksZero : σ.arrs "repairRMarks" = arrOf n (fun _ => 0)
  hclassB : σ.arrs "classB" = arrOf n label
  hclassSize : σ.arrs "classSize" = arrOf n size
  hclassStart : σ.arrs "repairClassStart" = arrOf n starts
  hord : σ.arrs "ord" = arrOf n ord
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htgt : σ.arrs "tgt" = arrOf targetCap (target x)
  hgroupActive : σ.arrs "activeB" = arrOf n groupActive
  hxsCard : xs.length = (activeVertices n groupActive).card
  hxsRange : xs.toFinset ⊆ Finset.range n
  hactiveCard : (activeVertices n groupActive).card ≤ n
  hslice : ∀ d < q, PrefixEnumerates (size d)
    (fun i => ord (classStart size d + i)) (labelClass xs label d)
  hstartTable : ∀ d < q, starts d = classStart size d
  hclassEnd : ∀ d < q, classStart size d + size d ≤ xs.length
  hclassFibre : ∀ b ∈ E, labelClass xs label (label b) =
    groupedB.filter (fun v =>
      trace (numericNeighborhood G) Wbase b =
        trace (numericNeighborhood G) Wbase v)
  hlabel : ∀ b ∈ E, label b < q
  hrepRange : ∀ b ∈ E, rep b < n
  hErange : E ⊆ Finset.range n
  hEgroup : E ⊆ groupedB
  hA : A ⊆ Finset.range n
  hWbase : Wbase ⊆ Wcurrent
  hWcurrentA : Wcurrent ⊆ A
  heLe : e ≤ n
  hqLe : q ≤ n
  hn1B : n + 1 < B
  htargetCapB : targetCap < B
  hbuffer : s ≤ bufferCap
  hsB : s < B
  htB : t < B
  hcapB : cap < B
  hfarB : (2 * k) / 3 < B
  hpowB : 2 ^ Nat.clog 2 n < B
  hthreeB : 3 < B

/-- Refill exactly the unread Boolean tape, retaining all graph metadata and
all noninput source registers at an exception-loop stopping prefix. -/
def LoopInput.reinput
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent) (bits : List Bool) :
    LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent := by
  let σ' := {R.σ with inp := bits.map Bool.toNat ++ R.rest}
  exact {
    R with
    σ := σ'
    bits := bits
    hinput := rfl
    hn := by simpa [σ'] using R.hn
    hqpow := by simpa [σ'] using R.hqpow
    htarget := by simpa [σ'] using R.htarget
    hdrawCap := by simpa [σ'] using R.hdrawCap
    hclassCount := by simpa [σ'] using R.hclassCount
    hretryCap := by simpa [σ'] using R.hretryCap
    hfarBound := by simpa [σ'] using R.hfarBound
    hexceptionCount := by simpa [σ'] using R.hexceptionCount
    hexceptionList := by simpa [σ'] using R.hexceptionList
    hrep := by simpa [σ'] using R.hrep
    hactive := by simpa [σ'] using R.hactive
    hdrawDomainLength := by simpa [σ'] using R.hdrawDomainLength
    hkeyLength := by simpa [σ'] using R.hkeyLength
    hdrawsLength := by simpa [σ'] using R.hdrawsLength
    hsample := by simpa [σ'] using R.hsample
    htrialZero := by simpa [σ'] using R.htrialZero
    hrowZero := by simpa [σ'] using R.hrowZero
    hdesiredZero := by simpa [σ'] using R.hdesiredZero
    hrowLength := by simpa [σ'] using R.hrowLength
    hdesiredLength := by simpa [σ'] using R.hdesiredLength
    hdiffLength := by simpa [σ'] using R.hdiffLength
    hBListLength := by simpa [σ'] using R.hBListLength
    hRListLength := by simpa [σ'] using R.hRListLength
    hBMarksZero := by simpa [σ'] using R.hBMarksZero
    hRMarksZero := by simpa [σ'] using R.hRMarksZero
    hclassB := by simpa [σ'] using R.hclassB
    hclassSize := by simpa [σ'] using R.hclassSize
    hclassStart := by simpa [σ'] using R.hclassStart
    hord := by simpa [σ'] using R.hord
    hoff := by simpa [σ'] using R.hoff
    htgt := by simpa [σ'] using R.htgt
    hgroupActive := by simpa [σ'] using R.hgroupActive
  }

lemma LoopInput.reinput_state
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent) (bits : List Bool) :
    (R.reinput bits).σ =
      {R.σ with inp := bits.map Bool.toNat ++ R.rest} := rfl

/-- Once distinct exceptions have distinct phase-two traces, their packed
class labels are distinct. The fixed `ord` slices may therefore be charged
at most once during the repair loop. -/
lemma LoopInput.label_injective_on_exceptions
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (hseparate : ∀ u ∈ E, ∀ v ∈ E,
      trace (numericNeighborhood G) Wbase u =
        trace (numericNeighborhood G) Wbase v → u = v) :
    ∀ u ∈ E, ∀ v ∈ E, R.label u = R.label v → u = v := by
  intro u hu v hv hlabelEq
  have hvClass : v ∈ labelClass R.xs R.label (R.label v) := by
    rw [R.hclassFibre v hv]
    simp [R.hEgroup hv]
  rw [← hlabelEq, R.hclassFibre u hu] at hvClass
  have htrace := (Finset.mem_filter.mp hvClass).2
  exact hseparate u hu v hv htrace

/-- The full phase-two scan separates exceptions by their neighborhoods on
the active ground set, which is the exact invariant needed by the fixed
class-slice charge. -/
lemma LoopInput.separate_exceptions_of_phase2
    {B n s t bufferCap targetCap q cap k e r : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (choice : InitialChoice A groupedB
      (fun v => numericNeighborhood G v ∩ A) r)
    (as : List ℕ) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hE : E = choice.exceptions k)
    (hW : Wbase = phase2Scan
      (fun v => numericNeighborhood G v ∩ A) E as choice.sample)
    (hinj : ∀ u ∈ E, ∀ v ∈ E,
      numericNeighborhood G u ∩ A = numericNeighborhood G v ∩ A → u = v) :
    ∀ u ∈ E, ∀ v ∈ E,
      trace (numericNeighborhood G) Wbase u =
        trace (numericNeighborhood G) Wbase v → u = v := by
  intro u hu v hv htrace
  have hWA : Wbase ⊆ A := R.hWbase.trans R.hWcurrentA
  have hrestrict (w : ℕ) :
      trace (fun z => numericNeighborhood G z ∩ A) Wbase w =
        trace (numericNeighborhood G) Wbase w := by
    ext a
    simp only [trace, Finset.mem_inter]
    constructor
    · rintro ⟨⟨haN, _⟩, haW⟩
      exact ⟨haN, haW⟩
    · rintro ⟨haN, haW⟩
      exact ⟨⟨haN, hWA haW⟩, haW⟩
  have htrace' : trace (fun w => numericNeighborhood G w ∩ A) Wbase u =
      trace (fun w => numericNeighborhood G w ∩ A) Wbase v := by
    rw [hrestrict, hrestrict]
    exact htrace
  have hN : ∀ w ∈ groupedB,
      numericNeighborhood G w ∩ A ⊆ A := by
    intro w _
    exact Finset.inter_subset_right
  have hrestricted := phase2_separates_distinct_neighborhoods
    A groupedB (fun w => numericNeighborhood G w ∩ A)
    as has hasNodup E choice.sample hN R.hEgroup u v hu hv
    (by simpa [hW] using htrace')
  exact hinj u hu v hv hrestricted

/-- Selected contiguous class slices are disjoint, so their actual slot
charges sum to at most one pass over the complete order array. -/
lemma sum_class_potential_le_total
    (size label weight : ℕ → ℕ) (E : Finset ℕ)
    (q length : ℕ)
    (hlabel : ∀ b ∈ E, label b < q)
    (hclassEnd : ∀ d < q,
      classStart size d + size d ≤ length)
    (hinj : Set.InjOn label E) :
    (∑ b ∈ E, repairClassPotential
      (classStart size (label b) + size (label b))
      (classStart size (label b)) weight) ≤
      ∑ i ∈ Finset.Ico 0 length, weight i := by
  classical
  let D := E.image label
  let slice (d : ℕ) := Finset.Ico (classStart size d)
    (classStart size d + size d)
  have hpair : (D : Set ℕ).PairwiseDisjoint slice := by
    intro d hd d' hd' hne
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have hi₁ : classStart size d ≤ i ∧
        i < classStart size d + size d := Finset.mem_Ico.mp hi
    have hi₂ : classStart size d' ≤ i ∧
        i < classStart size d' + size d' := Finset.mem_Ico.mp hi'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsep : classStart size d + size d ≤
          classStart size d' := by
        calc
          _ = classStart size (d + 1) := by rfl
          _ ≤ classStart size d' :=
            classStart_mono size (by omega)
      omega
    · have hsep : classStart size d' + size d' ≤
          classStart size d := by
        calc
          _ = classStart size (d' + 1) := by rfl
          _ ≤ classStart size d :=
            classStart_mono size (by omega)
      omega
  have hsubset : D.biUnion slice ⊆ Finset.Ico 0 length := by
    intro i hi
    obtain ⟨d, hd, hid⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
    have hstop := hclassEnd (label b) (hlabel b hb)
    have hii := Finset.mem_Ico.mp hid
    exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩
  calc
    _ = ∑ d ∈ D, ∑ i ∈ slice d, weight i := by
      rw [Finset.sum_image hinj]
      simp [repairClassPotential_eq_sum_Ico, D, slice]
    _ = ∑ i ∈ D.biUnion slice, weight i :=
      (Finset.sum_biUnion hpair).symm
    _ ≤ ∑ i ∈ Finset.Ico 0 length, weight i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro i hi hnot; exact Nat.zero_le _)

/-- Any subset of the packed exceptions pays for each fixed class slice at
most once. This isolates the scan contribution for outer-loop averaging. -/
lemma LoopInput.sum_classScanCharge_le
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (S : Finset ℕ) (hSE : S ⊆ E)
    (hseparate : ∀ u ∈ E, ∀ v ∈ E,
      trace (numericNeighborhood G) Wbase u =
        trace (numericNeighborhood G) Wbase v → u = v) :
    (∑ b ∈ S, classScanCharge x R.size R.label R.ord b) ≤
      66 * (∑ b ∈ S, (offset x (b + 1) - offset x b)) +
        (∑ i ∈ Finset.Ico 0 R.xs.length,
          repairClassSlotWeight x R.ord i) + 47 * S.card := by
  classical
  have hinj : Set.InjOn R.label S := by
    intro u hu v hv heq
    exact R.label_injective_on_exceptions hseparate u (hSE hu)
      v (hSE hv) heq
  have hpot := sum_class_potential_le_total R.size R.label
    (repairClassSlotWeight x R.ord) S q R.xs.length
    (fun b hb => R.hlabel b (hSE hb)) R.hclassEnd hinj
  have heq : (∑ b ∈ S, classScanCharge x R.size R.label R.ord b) =
      66 * (∑ b ∈ S, (offset x (b + 1) - offset x b)) +
      (∑ b ∈ S, repairClassPotential
        (classStart R.size (R.label b) + R.size (R.label b))
        (classStart R.size (R.label b))
        (repairClassSlotWeight x R.ord)) + 47 * S.card := by
    simp [classScanCharge, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rw [heq]
  omega

/-- The prepared one-exception record is obtained only after the array read
has placed the current packed vertex into `repairB`. -/
def LoopInput.preDomain
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    {b : ℕ} (hb : b ∈ E) {σ' : Env}
    (r : Run B (.assign "repairB" (.get "exceptionList" (.var "exceptionIndex")))
      R.σ σ' 3)
    (hrepairB : σ'.vars "repairB" = b) :
    PreDomainInput B n s t bufferCap targetCap q b
      G x groupedB Wbase Wcurrent := by
  exact {
    σ := σ'
    bits := R.bits
    rest := R.rest
    size := R.size
    starts := R.starts
    label := R.label
    ord := R.ord
    groupActive := R.groupActive
    xs := R.xs
    hgraph := R.hgraph
    htargetCap := R.htargetCap
    hdrawDomainLength := by rw [run_array_length_eq r "drawDomain", R.hdrawDomainLength]
    hinput := (r.frame_inp (by decide)).trans R.hinput
    hn := (r.frame_var "n" (by decide)).trans R.hn
    hqpow := by rw [r.frame_var "qpow" (by decide)]; exact R.hqpow
    htarget := (r.frame_var "batchTarget" (by decide)).trans R.htarget
    hcap := (r.frame_var "drawCap" (by decide)).trans R.hdrawCap
    hrepairB := hrepairB
    hclassCount := (r.frame_var "classCount" (by decide)).trans R.hclassCount
    hkeyLength := by rw [run_array_length_eq r "key0", R.hkeyLength]
    hdrawsLength := by rw [run_array_length_eq r "sampleDraws", R.hdrawsLength]
    hsample := (r.frame_arr "sampleFlags" (by decide)).trans R.hsample
    htrialZero := (r.frame_arr "trialActive" (by decide)).trans R.htrialZero
    hrowZero := (r.frame_arr "trialRowMarks" (by decide)).trans R.hrowZero
    hdesiredZero := (r.frame_arr "trialDesiredMarks" (by decide)).trans R.hdesiredZero
    hrowLength := by rw [run_array_length_eq r "trialRowList", R.hrowLength]
    hdesiredLength := by rw [run_array_length_eq r "trialDesiredList", R.hdesiredLength]
    hdiffLength := by rw [run_array_length_eq r "trialDiffList", R.hdiffLength]
    hclassB := (r.frame_arr "classB" (by decide)).trans R.hclassB
    hclassSize := (r.frame_arr "classSize" (by decide)).trans R.hclassSize
    hclassStart := (r.frame_arr "repairClassStart" (by decide)).trans R.hclassStart
    hord := (r.frame_arr "ord" (by decide)).trans R.hord
    hoff := (r.frame_arr "off" (by decide)).trans R.hoff
    htgt := (r.frame_arr "tgt" (by decide)).trans R.htgt
    hgroupActive := (r.frame_arr "activeB" (by decide)).trans R.hgroupActive
    hxsCard := R.hxsCard
    hxsRange := R.hxsRange
    hactiveCard := R.hactiveCard
    hslice := R.hslice
    hstartTable := R.hstartTable
    hclassEnd := R.hclassEnd
    hclassFibre := R.hclassFibre b hb
    hbrange := Finset.mem_range.mp (R.hErange hb)
    hqle := R.hqLe
    hlabel := R.hlabel b hb
    hWrange := R.hWcurrentA.trans R.hA
    hWbase := R.hWbase
    hn1B := R.hn1B
    htargetCapB := R.htargetCapB
    hbuffer := R.hbuffer
    hsB := R.hsB
    htB := R.htB
    hthreeB := R.hthreeB
  }

/-- All immutable inputs and cleared support marks survive one body run. -/
def LoopInput.afterBody
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent Wnext : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    {σ' : Env} {charge : ℕ}
    (r : Run B exceptionRepairBody R.σ σ' charge)
    (newBits : List Bool)
    (hinp : σ'.inp = newBits.map Bool.toNat ++ R.rest)
    (hn : σ'.vars "n" = n)
    (hqpow : σ'.vars "qpow" = R.σ.vars "qpow")
    (hsample : σ'.arrs "sampleFlags" = arrOf n (setFlag Wnext))
    (htrial : σ'.arrs "trialActive" = arrOf n (fun _ => 0))
    (hrow : σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hdesired : σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0))
    (hBmarks : σ'.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hRmarks : σ'.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hWbase : Wbase ⊆ Wnext) (hWnextA : Wnext ⊆ A) :
    LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wnext := by
  exact {
    R with
    σ := σ'
    bits := newBits
    hinput := hinp
    hn := hn
    hqpow := by rw [hqpow]; exact R.hqpow
    htarget := (r.frame_var "batchTarget" (by decide)).trans R.htarget
    hdrawCap := (r.frame_var "drawCap" (by decide)).trans R.hdrawCap
    hclassCount := (r.frame_var "classCount" (by decide)).trans R.hclassCount
    hretryCap := (r.frame_var "repairRetryCap" (by decide)).trans R.hretryCap
    hfarBound := (r.frame_var "repairFarBound" (by decide)).trans R.hfarBound
    hexceptionCount := (r.frame_var "exceptionCount" (by decide)).trans
      R.hexceptionCount
    hexceptionList := (r.frame_arr "exceptionList" (by decide)).trans
      R.hexceptionList
    hrep := (r.frame_arr "repB" (by decide)).trans R.hrep
    hactive := (r.frame_arr "activeA" (by decide)).trans R.hactive
    hdrawDomainLength := by
      rw [run_array_length_eq r "drawDomain", R.hdrawDomainLength]
    hkeyLength := by rw [run_array_length_eq r "key0", R.hkeyLength]
    hdrawsLength := by rw [run_array_length_eq r "sampleDraws", R.hdrawsLength]
    hsample := hsample
    htrialZero := htrial
    hrowZero := hrow
    hdesiredZero := hdesired
    hrowLength := by rw [run_array_length_eq r "trialRowList", R.hrowLength]
    hdesiredLength := by
      rw [run_array_length_eq r "trialDesiredList", R.hdesiredLength]
    hdiffLength := by rw [run_array_length_eq r "trialDiffList", R.hdiffLength]
    hBListLength := by rw [run_array_length_eq r "repairBList", R.hBListLength]
    hRListLength := by rw [run_array_length_eq r "repairRList", R.hRListLength]
    hBMarksZero := hBmarks
    hRMarksZero := hRmarks
    hclassB := (r.frame_arr "classB" (by decide)).trans R.hclassB
    hclassSize := (r.frame_arr "classSize" (by decide)).trans R.hclassSize
    hclassStart := (r.frame_arr "repairClassStart" (by decide)).trans R.hclassStart
    hord := (r.frame_arr "ord" (by decide)).trans R.hord
    hoff := (r.frame_arr "off" (by decide)).trans R.hoff
    htgt := (r.frame_arr "tgt" (by decide)).trans R.htgt
    hgroupActive := (r.frame_arr "activeB" (by decide)).trans R.hgroupActive
    hWbase := hWbase
    hWcurrentA := hWnextA
  }

/-- The mathematical enumeration, class tables, and restored draw-log register
stay fixed across the source loop. -/
def SameFixed
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A W W' : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W)
    (R' : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W') : Prop :=
  R'.exceptionList = R.exceptionList ∧ R'.rep = R.rep ∧
    R'.size = R.size ∧ R'.label = R.label ∧ R'.ord = R.ord ∧
    R'.rest = R.rest ∧ R'.σ.vars "qpow" = R.σ.vars "qpow"

lemma SameFixed.qpow
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A W W' : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W}
    {R' : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W'}
    (h : SameFixed R R') :
    R'.σ.vars "qpow" = R.σ.vars "qpow" := h.2.2.2.2.2.2

private lemma SameFixed.refl
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A W : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W) : SameFixed R R := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma SameFixed.trans
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A W W' W'' : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W}
    {R' : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W'}
    {R'' : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A W''}
    (h : SameFixed R R') (h' : SameFixed R' R'') : SameFixed R R'' := by
  exact ⟨h'.1.trans h.1, h'.2.1.trans h.2.1,
    h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1,
    h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The machine's symmetric difference is a subset of the fixed ground set. -/
private lemma difference_subset_ground {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (b r : ℕ) :
    ((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G r ∩ A)) ⊆ A := by
  intro v hv
  simp only [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact (Finset.mem_inter.mp hv.1).2
  · exact (Finset.mem_inter.mp hv.1).2

private lemma difference_card_le_n {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (hA : A ⊆ Finset.range n) (b r : ℕ) :
    (((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G r ∩ A))).card ≤ n := by
  calc
    (((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G r ∩ A))).card ≤ A.card :=
        Finset.card_le_card (difference_subset_ground G A b r)
    _ ≤ (Finset.range n).card := Finset.card_le_card hA
    _ = n := by simp

private lemma pow_clog_difference_lt
    {B n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (hA : A ⊆ Finset.range n)
    (b r : ℕ) (hpow : 2 ^ Nat.clog 2 n < B) :
    2 ^ Nat.clog 2
      (((numericNeighborhood G b ∩ A) ∆
        (numericNeighborhood G r ∩ A))).card < B := by
  have hc := Nat.clog_mono_right 2 (difference_card_le_n G A hA b r)
  exact (pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) hc).trans_lt hpow

private lemma packed_exception_mem {e : ℕ} {entry : ℕ → ℕ}
    {E : Finset ℕ} (hprefix : PrefixEnumerates e entry E)
    {i : ℕ} (hi : i < e) : entry i ∈ E := by
  apply (hprefix.2 (entry i)).mp
  have hil : i < (Stack.toList e entry).length := by
    simpa [Stack.toList] using hi
  have hget : (Stack.toList e entry)[i] = entry i := by
    simp [Stack.toList]
  rw [← hget]
  exact List.getElem_mem hil

private lemma packed_exception_tail_nodup {e : ℕ} {entry : ℕ → ℕ}
    {E : Finset ℕ} (hprefix : PrefixEnumerates e entry E)
    {i : ℕ} (hi : i < e) :
    entry i ∉ (Stack.toList e entry).drop (i + 1) := by
  have hil : i < (Stack.toList e entry).length := by
    simpa [Stack.toList] using hi
  have hdrop := List.drop_eq_getElem_cons hil
  have hget : (Stack.toList e entry)[i] = entry i := by
    simp [Stack.toList, hi]
  rw [hget] at hdrop
  have htail : ((Stack.toList e entry).drop i).Nodup := hprefix.1.drop
  rw [hdrop] at htail
  exact (List.nodup_cons.mp htail).1

private lemma difference_eq_repair_domain {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset ℕ) (b r : ℕ) :
    ((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G r ∩ A)) =
    (((numericNeighborhood G b ∩ A) \
      (numericNeighborhood G r ∩ A)) ∪
      ((numericNeighborhood G r ∩ A) \
        (numericNeighborhood G b ∩ A))) := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]

private lemma near_phase3Repair {n : ℕ}
    (G : SimpleGraph (Fin n)) (A groupedB Wbase Wcur : Finset ℕ)
    (b r k s : ℕ)
    (hnear : (((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G r ∩ A))).card ≤ (2 * k) / 3) :
    phase3Repair (fun v => numericNeighborhood G v ∩ A) groupedB
      Wbase Wcur b r k s [] = some Wcur := by
  have hnotfar : ¬ 2 * k < 3 * disagreement
      (fun v => numericNeighborhood G v ∩ A) b r := by
    rw [disagreement, ← difference_eq_repair_domain G A b r]
    omega
  simp [phase3Repair, hnotfar]

private lemma far_phase3Repair {n : ℕ}
    (G : SimpleGraph (Fin n)) (A groupedB Wbase Wcur : Finset ℕ)
    (b r k s : ℕ) (D : List ℕ)
    (hWbaseA : Wbase ⊆ A)
    (hfar : (2 * k) / 3 <
      (((numericNeighborhood G b ∩ A) ∆
        (numericNeighborhood G r ∩ A))).card)
    (hlen : D.length = s)
    (hmem : ∀ v ∈ D, v ∈ ((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G r ∩ A)))
    (hiso : localTrialIsolates (numericNeighborhood G) groupedB Wbase b D) :
    ∃ trials : List (LocalTrial
      ((((numericNeighborhood G b ∩ A) \
        (numericNeighborhood G r ∩ A)) ∪
        ((numericNeighborhood G r ∩ A) \
          (numericNeighborhood G b ∩ A)))) s),
      phase3Repair (fun v => numericNeighborhood G v ∩ A)
        groupedB Wbase Wcur b r k s trials =
          some (Wcur ∪ D.toFinset) := by
  let trial : LocalTrial
      ((((numericNeighborhood G b ∩ A) \
        (numericNeighborhood G r ∩ A)) ∪
        ((numericNeighborhood G r ∩ A) \
          (numericNeighborhood G b ∩ A)))) s := {
    draws := D
    draws_length := hlen
    draws_mem := by
      intro v hv
      rw [← difference_eq_repair_domain G A b r]
      exact hmem v hv
  }
  have hdrawA : D.toFinset ⊆ A := by
    intro v hv
    exact difference_subset_ground G A b r (hmem v (List.mem_toFinset.mp hv))
  have hiso' : localTrialIsolates
      (fun v => numericNeighborhood G v ∩ A) groupedB Wbase b D :=
    (Lax457868Proofs.LocalRepairPhase3.localTrialIsolates_restricted_iff
      (numericNeighborhood G) groupedB hWbaseA b D hdrawA).mp hiso
  have hfar' : 2 * k < 3 * disagreement
      (fun v => numericNeighborhood G v ∩ A) b r := by
    rw [disagreement, ← difference_eq_repair_domain G A b r]
    omega
  exact ⟨[trial], Lax457868Proofs.LocalRepairPhase3.phase3Repair_singleton_of_isolates
    (fun v => numericNeighborhood G v ∩ A) groupedB Wbase Wcur b r k s
    trial hfar' hiso'⟩

/-- Prepare the head exception by one actual array read. -/
private lemma prepare_current
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    {i : ℕ} (hindex : R.σ.vars "exceptionIndex" = i) (hi : i < e) :
    ∃ (σload : Env)
      (P : PreDomainInput B n s t bufferCap targetCap q (R.exceptionList i)
        G x groupedB Wbase Wcurrent)
      (blist rlist : ℕ → ℕ),
      Run B (.assign "repairB" (.get "exceptionList" (.var "exceptionIndex")))
        R.σ σload 3 ∧
      P.σ = σload ∧ P.bits = R.bits ∧ P.rest = R.rest ∧
      P.scanUpper = classScanCharge x R.size R.label R.ord
        (R.exceptionList i) ∧
      σload.arrs "repB" = arrOf n R.rep ∧
      σload.arrs "activeA" = arrOf n (setFlag A) ∧
      σload.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
      σload.arrs "repairRMarks" = arrOf n (fun _ => 0) ∧
      σload.arrs "repairBList" = arrOf n blist ∧
      σload.arrs "repairRList" = arrOf n rlist ∧
      σload.vars "repairFarBound" = (2 * k) / 3 ∧
      σload.vars "repairRetryCap" = cap ∧
      R.rep (R.exceptionList i) < n := by
  have hbE : R.exceptionList i ∈ E := packed_exception_mem R.hprefix hi
  have hbN : R.exceptionList i < n := Finset.mem_range.mp (R.hErange hbE)
  have hiB : i < B := by have := R.heLe; have := R.hn1B; omega
  have hbB : R.exceptionList i < B := by have := R.hn1B; omega
  let σload := R.σ.setVar "repairB" (R.exceptionList i)
  have hloadEval : (Expr.get "exceptionList" (.var "exceptionIndex")).evalB
      B R.σ = some (R.exceptionList i) := by
    apply evalB_get (evalB_var (by rw [hindex]; exact hiB))
    · rw [R.hexceptionList, hindex,
        getElem?_arrOf R.exceptionList (by have := R.heLe; omega : i < n)]
    · exact hbB
  have rload : Run B
      (.assign "repairB" (.get "exceptionList" (.var "exceptionIndex")))
      R.σ σload 3 := by
    simpa [σload] using (Run.assign hloadEval)
  let P := R.preDomain hbE rload (by simp [σload])
  have hBLen : (σload.arrs "repairBList").length = n := by
    rw [run_array_length_eq rload "repairBList", R.hBListLength]
  have hRLen : (σload.arrs "repairRList").length = n := by
    rw [run_array_length_eq rload "repairRList", R.hRListLength]
  obtain ⟨blist, hblist⟩ := exists_arrOf_of_length hBLen
  obtain ⟨rlist, hrlist⟩ := exists_arrOf_of_length hRLen
  exact ⟨σload, P, blist, rlist, rload, rfl, rfl, rfl, rfl,
    (rload.frame_arr "repB" (by decide)).trans R.hrep,
    (rload.frame_arr "activeA" (by decide)).trans R.hactive,
    (rload.frame_arr "repairBMarks" (by decide)).trans R.hBMarksZero,
    (rload.frame_arr "repairRMarks" (by decide)).trans R.hRMarksZero,
    hblist, hrlist,
    (rload.frame_var "repairFarBound" (by decide)).trans R.hfarBound,
    (rload.frame_var "repairRetryCap" (by decide)).trans R.hretryCap,
    R.hrepRange _ hbE⟩

private lemma assemble_success
    {B n s t bufferCap targetCap q cap k e i K : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent Wnext : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    {σload σsource : Env}
    (rload : Run B
      (.assign "repairB" (.get "exceptionList" (.var "exceptionIndex")))
      R.σ σload 3)
    (rsource : Run B localRepairOneExceptionSource σload σsource K)
    (hindex : R.σ.vars "exceptionIndex" = i)
    (hstop : R.σ.vars "exceptionStop" = e)
    (hi : i < e)
    (bitsNext : List Bool)
    (hinp : σsource.inp = bitsNext.map Bool.toNat ++ R.rest)
    (hn : σsource.vars "n" = n)
    (hqpow : σsource.vars "qpow" = σload.vars "qpow")
    (hsample : σsource.arrs "sampleFlags" = arrOf n (setFlag Wnext))
    (hstatus : σsource.vars "repairRetryStatus" = 1)
    (htrial : σsource.arrs "trialActive" = arrOf n (fun _ => 0))
    (hrow : σsource.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hdesired : σsource.arrs "trialDesiredMarks" = arrOf n (fun _ => 0))
    (hBmarks : σsource.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hRmarks : σsource.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hWbase : Wbase ⊆ Wnext) (hWnextA : Wnext ⊆ A) :
    ∃ Rnext : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wnext,
      Run B exceptionRepairBody R.σ Rnext.σ (K + 11) ∧
      Rnext.bits = bitsNext ∧
      Rnext.σ.vars "exceptionIndex" = i + 1 ∧
      Rnext.σ.vars "exceptionStop" = e ∧
      Rnext.σ.vars "repairRetryStatus" = 1 ∧
      SameFixed R Rnext := by
  have hiB : i < B := by have := R.heLe; have := R.hn1B; omega
  have hi1B : i + 1 < B := by have := R.heLe; have := R.hn1B; omega
  have hindexSource : σsource.vars "exceptionIndex" = i := by
    rw [rsource.frame_var "exceptionIndex" (by decide)]
    rw [rload.frame_var "exceptionIndex" (by decide)]
    exact hindex
  have hstopSource : σsource.vars "exceptionStop" = e := by
    rw [rsource.frame_var "exceptionStop" (by decide)]
    rw [rload.frame_var "exceptionStop" (by decide)]
    exact hstop
  let σnext := σsource.setVar "exceptionIndex" (i + 1)
  have hincEval : (Expr.add (.var "exceptionIndex") (.lit 1)).evalB
      B σsource = some (i + 1) := by
    have hvar : (Expr.var "exceptionIndex").evalB B σsource = some i :=
      by simpa [hindexSource] using
        (evalB_var (by rw [hindexSource]; exact hiB :
          σsource.vars "exceptionIndex" < B))
    have hbin := evalB_bin hvar
      (evalB_lit (by have := R.hthreeB; omega : 1 < B))
      (by simpa [Bop.apply] using hi1B : Bop.apply Bop.add i 1 < B)
    simpa [Bop.apply] using hbin
  have rinc : Run B
      (.assign "exceptionIndex" (.add (.var "exceptionIndex") (.lit 1)))
      σsource σnext 4 := by
    simpa [σnext] using Run.assign hincEval
  have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
      B σsource = some true := by
    simpa [hstatus] using evalB_condEq
      (evalB_var (by rw [hstatus]; have := R.hthreeB; omega :
        σsource.vars "repairRetryStatus" < B))
      (evalB_lit (by have := R.hthreeB; omega : 1 < B))
  have rite : Run B
      (.ite (.eq (.var "repairRetryStatus") (.lit 1))
        (.assign "exceptionIndex" (.add (.var "exceptionIndex") (.lit 1)))
        (.assign "exceptionStop" (.var "exceptionIndex")))
      σsource σnext 8 := by
    simpa [Cond.size, Expr.size] using Run.ite_true hguard rinc
  have rbody : Run B exceptionRepairBody R.σ σnext (K + 11) := by
    have rseq := rload.seq (rsource.seq rite)
    have rseq' := rseq.mono (by omega : 3 + (K + 8) ≤ K + 11)
    simpa [exceptionRepairBody] using rseq'
  let Rnext := R.afterBody rbody bitsNext
    (by simpa [σnext] using hinp)
    (by simpa [σnext] using hn)
    (by
      simpa [σnext] using hqpow.trans (rload.frame_var "qpow" (by decide)))
    (by simpa [σnext] using hsample)
    (by simpa [σnext] using htrial)
    (by simpa [σnext] using hrow)
    (by simpa [σnext] using hdesired)
    (by simpa [σnext] using hBmarks)
    (by simpa [σnext] using hRmarks)
    hWbase hWnextA
  refine ⟨Rnext, rbody, rfl, ?_, ?_, ?_, ?_⟩
  · change σnext.vars "exceptionIndex" = i + 1
    simp [σnext]
  · change σnext.vars "exceptionStop" = e
    simpa [σnext] using hstopSource
  · change σnext.vars "repairRetryStatus" = 1
    simpa [σnext] using hstatus
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    change σnext.vars "qpow" = R.σ.vars "qpow"
    simpa [σnext] using hqpow.trans (rload.frame_var "qpow" (by decide))

private lemma assemble_failure
    {B n s t bufferCap targetCap q cap k e i K z : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    {σload σsource : Env}
    (rload : Run B
      (.assign "repairB" (.get "exceptionList" (.var "exceptionIndex")))
      R.σ σload 3)
    (rsource : Run B localRepairOneExceptionSource σload σsource K)
    (hindex : R.σ.vars "exceptionIndex" = i)
    (hi : i < e)
    (bitsNext : List Bool)
    (hinp : σsource.inp = bitsNext.map Bool.toNat ++ R.rest)
    (hn : σsource.vars "n" = n)
    (hqpow : σsource.vars "qpow" = σload.vars "qpow")
    (hsample : σsource.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))
    (hstatus : σsource.vars "repairRetryStatus" = z)
    (hz : z = 2 ∨ z = 3)
    (htrial : σsource.arrs "trialActive" = arrOf n (fun _ => 0))
    (hrow : σsource.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hdesired : σsource.arrs "trialDesiredMarks" = arrOf n (fun _ => 0))
    (hBmarks : σsource.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hRmarks : σsource.arrs "repairRMarks" = arrOf n (fun _ => 0)) :
    ∃ Rnext : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wcurrent,
      Run B exceptionRepairBody R.σ Rnext.σ (K + 9) ∧
      Rnext.bits = bitsNext ∧
      Rnext.σ.vars "exceptionIndex" = i ∧
      Rnext.σ.vars "exceptionStop" = i ∧
      Rnext.σ.vars "repairRetryStatus" = z ∧
      SameFixed R Rnext := by
  have hiB : i < B := by have := R.heLe; have := R.hn1B; omega
  have hzB : z < B := by
    have := R.hthreeB
    rcases hz with rfl | rfl <;> omega
  have hindexSource : σsource.vars "exceptionIndex" = i := by
    rw [rsource.frame_var "exceptionIndex" (by decide)]
    rw [rload.frame_var "exceptionIndex" (by decide)]
    exact hindex
  let σnext := σsource.setVar "exceptionStop" i
  have rstop : Run B (.assign "exceptionStop" (.var "exceptionIndex"))
      σsource σnext 2 := by
    have hvar : (Expr.var "exceptionIndex").evalB B σsource = some i := by
      simpa [hindexSource] using
        (evalB_var (by rw [hindexSource]; exact hiB :
          σsource.vars "exceptionIndex" < B))
    simpa [σnext] using Run.assign hvar
  have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
      B σsource = some false := by
    have hnot : z ≠ 1 := by rcases hz with rfl | rfl <;> omega
    simpa [hstatus, hnot] using evalB_condEq
      (evalB_var (by rw [hstatus]; exact hzB :
        σsource.vars "repairRetryStatus" < B))
      (evalB_lit (by have := R.hthreeB; omega : 1 < B))
  have rite : Run B
      (.ite (.eq (.var "repairRetryStatus") (.lit 1))
        (.assign "exceptionIndex" (.add (.var "exceptionIndex") (.lit 1)))
        (.assign "exceptionStop" (.var "exceptionIndex")))
      σsource σnext 6 := by
    simpa [Cond.size, Expr.size] using Run.ite_false hguard rstop
  have rbody : Run B exceptionRepairBody R.σ σnext (K + 9) := by
    have rseq := rload.seq (rsource.seq rite)
    have rseq' := rseq.mono (by omega : 3 + (K + 6) ≤ K + 9)
    simpa [exceptionRepairBody] using rseq'
  let Rnext := R.afterBody rbody bitsNext
    (by simpa [σnext] using hinp)
    (by simpa [σnext] using hn)
    (by simpa [σnext] using
      hqpow.trans (rload.frame_var "qpow" (by decide)))
    (by simpa [σnext] using hsample)
    (by simpa [σnext] using htrial)
    (by simpa [σnext] using hrow)
    (by simpa [σnext] using hdesired)
    (by simpa [σnext] using hBmarks)
    (by simpa [σnext] using hRmarks)
    R.hWbase R.hWcurrentA
  refine ⟨Rnext, rbody, rfl, ?_, ?_, ?_, ?_⟩
  · change σnext.vars "exceptionIndex" = i
    simpa [σnext] using hindexSource
  · change σnext.vars "exceptionStop" = i
    simp [σnext]
  · change σnext.vars "repairRetryStatus" = z
    simpa [σnext] using hstatus
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    change σnext.vars "qpow" = R.σ.vars "qpow"
    simpa [σnext] using hqpow.trans (rload.frame_var "qpow" (by decide))

/-- The actual prepared local retry run for a far exception, including every
rejected trial and the first accepted or failed selector prefix. -/
def FarStepTrace
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (i attempts used : ℕ) : Prop :=
  let b := R.exceptionList i
  let X := (numericNeighborhood G b ∩ A) ∆
    (numericNeighborhood G (R.rep b) ∩ A)
  ∃ P : ReadyInput B n X.card n s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent,
    Run B ((Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
      repairDomainSource) R.σ P.σ
        (3 + domainCharge x G A R.rep b) ∧
    P.bits = R.bits ∧ P.rest = R.rest ∧
    P.scanUpper = classScanCharge x R.size R.label R.ord b ∧
    ∃ σsource : Env,
      Run B localRepairRetriesSource P.σ σsource
        (12 * Nat.clog 2 X.card + 24 +
          ((15 * Nat.clog 2 X.card + 30) * used +
            attempts * (79 * s + P.scanUpper + 50) + 14)) ∧
      (∃ rejected : ℕ,
        rejected ≤ attempts ∧ attempts ≤ rejected + 1 ∧
        LocalFlatLaw.FlatRejectedTrials X.card t s
          (LocalFlatLaw.localBadOutputs X.card s P.domain
            (numericNeighborhood G) groupedB Wbase b)
          rejected P.bits) ∧
      (∃ accepted : ℕ,
        LocalFlatLaw.FlatRetryExecution X.card P.hpositive t s
          (LocalFlatLaw.localBadOutputs X.card s P.domain
            (numericNeighborhood G) groupedB Wbase b)
          attempts P.bits used accepted) ∧
      σsource.vars "repairRetriesLeft" + attempts = cap ∧
      σsource.inp =
        (P.bits.drop (used * Nat.clog 2 X.card)).map Bool.toNat ++ P.rest ∧
      (σsource.vars "repairRetryStatus" = 3 →
        LocalFlatLaw.FlatRejectedTrials X.card t s
          (LocalFlatLaw.localBadOutputs X.card s P.domain
            (numericNeighborhood G) groupedB Wbase b) cap P.bits) ∧
      (σsource.vars "repairRetryStatus" = 2 →
        LocalRepairRetriesSource.FlatSelectorFailed X.card P.hpositive t s
          (LocalFlatLaw.localBadOutputs X.card s P.domain
            (numericNeighborhood G) groupedB Wbase b) attempts P.bits)

/-- The failed status observed after one exception body is witnessed by the
same actual local selector/retry source and its exact stopped bit prefix. -/
def FarStepFailureTrace
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (i attempts used status : ℕ) : Prop :=
  let b := R.exceptionList i
  let X := (numericNeighborhood G b ∩ A) ∆
    (numericNeighborhood G (R.rep b) ∩ A)
  ∃ P : ReadyInput B n X.card n s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent,
    Run B ((Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
      repairDomainSource) R.σ P.σ
      (3 + domainCharge x G A R.rep b) ∧
    P.bits = R.bits ∧ P.rest = R.rest ∧
    (status = 2 →
      LocalRepairRetriesSource.FlatSelectorFailed X.card P.hpositive t s
        (LocalFlatLaw.localBadOutputs X.card s P.domain
          (numericNeighborhood G) groupedB Wbase b) attempts P.bits) ∧
    (status = 3 →
      LocalFlatLaw.FlatRejectedTrials X.card t s
        (LocalFlatLaw.localBadOutputs X.card s P.domain
          (numericNeighborhood G) groupedB Wbase b) cap P.bits)

lemma FarStepTrace.failure_of_actual
    {B n s t bufferCap targetCap q cap k e i attempts used status Kprep Klocal : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    {σprep σsource : Env}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (hfar : FarStepTrace R i attempts used)
    (rprep : Run B
      ((Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
        repairDomainSource) R.σ σprep Kprep)
    (rlocal : Run B localRepairRetriesSource σprep σsource Klocal)
    (hstatus : σsource.vars "repairRetryStatus" = status) :
    FarStepFailureTrace R i attempts used status := by
  rcases hfar with ⟨P, rprep', hbits, hrest, _hscan, σsource',
    rlocal', _hreject, _hfull, _hcount, _hinp, hexhaust, hselector⟩
  obtain ⟨_, _, hbigPrep⟩ := rprep
  have hrPrep := rprep'
  obtain ⟨_, _, hbigPrep'⟩ := rprep'
  have heqPrep : P.σ = σprep :=
    (BigStep.unique hbigPrep'.bigStep hbigPrep.bigStep).1
  obtain ⟨_, _, hbigLocal⟩ := rlocal
  obtain ⟨_, _, hbigLocal'⟩ := rlocal'
  have heqSource : σsource' = σsource := by
    rw [heqPrep] at hbigLocal'
    exact (BigStep.unique hbigLocal'.bigStep hbigLocal.bigStep).1
  refine ⟨P, hrPrep, hbits, hrest, ?_, ?_⟩
  · intro hs
    apply hselector
    rw [heqSource, hstatus]
    exact hs
  · intro hs
    apply hexhaust
    rw [heqSource, hstatus]
    exact hs

/-- Execute one packed exception. The reported charge is the actual source
charge for the near or far branch, with its actual attempts and bit use. -/
lemma one_step_run_trace
    {B n s t bufferCap targetCap q cap k e i : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (hindex : R.σ.vars "exceptionIndex" = i)
    (hstop : R.σ.vars "exceptionStop" = e)
    (hi : i < e)
    (hbudget : cap * (s * t * Nat.clog 2
      (((numericNeighborhood G (R.exceptionList i) ∩ A) ∆
        (numericNeighborhood G (R.rep (R.exceptionList i)) ∩ A))).card) ≤
        R.bits.length) :
    ∃ (Wnext : Finset ℕ)
      (Rnext : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wnext)
      (attempts used charge : ℕ),
      Run B exceptionRepairBody R.σ Rnext.σ
        (charge + if Rnext.σ.vars "repairRetryStatus" = 1 then 11 else 9) ∧
      charge = oneExceptionCharge x G A R.rep s
        (classScanCharge x R.size R.label R.ord (R.exceptionList i))
        (R.exceptionList i) k attempts used ∧
      attempts ≤ cap ∧ used ≤ attempts * (s * t) ∧
      Rnext.bits = R.bits.drop (used * Nat.clog 2
        (((numericNeighborhood G (R.exceptionList i) ∩ A) ∆
          (numericNeighborhood G (R.rep (R.exceptionList i)) ∩ A))).card) ∧
      SameFixed R Rnext ∧
      ((Rnext.σ.vars "repairRetryStatus" = 1 ∧
          Rnext.σ.vars "exceptionIndex" = i + 1 ∧
          Rnext.σ.vars "exceptionStop" = e ∧
          ∃ headTrials : List (LocalTrial
            ((((numericNeighborhood G (R.exceptionList i) ∩ A) \
              (numericNeighborhood G (R.rep (R.exceptionList i)) ∩ A)) ∪
              ((numericNeighborhood G (R.rep (R.exceptionList i)) ∩ A) \
                (numericNeighborhood G (R.exceptionList i) ∩ A)))) s),
            phase3Repair (fun v => numericNeighborhood G v ∩ A)
              groupedB Wbase Wcurrent (R.exceptionList i)
              (R.rep (R.exceptionList i)) k s headTrials = some Wnext) ∨
        ((Rnext.σ.vars "repairRetryStatus" = 2 ∨
            Rnext.σ.vars "repairRetryStatus" = 3) ∧
          Rnext.σ.vars "exceptionIndex" = i ∧
          Rnext.σ.vars "exceptionStop" = i ∧
          Wnext = Wcurrent)) ∧
      ((2 * k) / 3 <
        (((numericNeighborhood G (R.exceptionList i) ∩ A) ∆
          (numericNeighborhood G (R.rep (R.exceptionList i)) ∩ A))).card →
        FarStepTrace R i attempts used) ∧
      ((Rnext.σ.vars "repairRetryStatus" = 2 ∨
          Rnext.σ.vars "repairRetryStatus" = 3) →
        (2 * k) / 3 <
          (((numericNeighborhood G (R.exceptionList i) ∩ A) ∆
            (numericNeighborhood G (R.rep (R.exceptionList i)) ∩ A))).card) ∧
      ((Rnext.σ.vars "repairRetryStatus" = 2 ∨
          Rnext.σ.vars "repairRetryStatus" = 3) →
        FarStepFailureTrace R i attempts used
          (Rnext.σ.vars "repairRetryStatus")) := by
  let b := R.exceptionList i
  let X := ((numericNeighborhood G b ∩ A) ∆
    (numericNeighborhood G (R.rep b) ∩ A))
  obtain ⟨σload, P, blist, rlist, rload, hPσ, hPbits, hPrest, hscan,
    hrep, hactive, hBmarks, hRmarks, hblist, hrlist, hfarBound,
    hretryCap, hrange⟩ := prepare_current R hindex hi
  have hpow : 2 ^ Nat.clog 2 X.card < B :=
    pow_clog_difference_lt G A R.hA b (R.rep b) R.hpowB
  have hrepP : P.σ.arrs "repB" = arrOf n R.rep := by rw [hPσ]; exact hrep
  have hactiveP : P.σ.arrs "activeA" = arrOf n (setFlag A) := by
    rw [hPσ]; exact hactive
  have hBmarksP : P.σ.arrs "repairBMarks" = arrOf n (fun _ => 0) := by
    rw [hPσ]; exact hBmarks
  have hRmarksP : P.σ.arrs "repairRMarks" = arrOf n (fun _ => 0) := by
    rw [hPσ]; exact hRmarks
  have hblistP : P.σ.arrs "repairBList" = arrOf n blist := by
    rw [hPσ]; exact hblist
  have hrlistP : P.σ.arrs "repairRList" = arrOf n rlist := by
    rw [hPσ]; exact hrlist
  have hfarP : P.σ.vars "repairFarBound" = (2 * k) / 3 := by
    rw [hPσ]; exact hfarBound
  have hcapP : P.σ.vars "repairRetryCap" = cap := by
    rw [hPσ]; exact hretryCap
  by_cases hfar : (2 * k) / 3 < X.card
  · obtain ⟨σsource, attempts, used, rsource, hattempts, hused,
      hinp, hn, hqpow, htrial, hrow, hdesired,
      hBmarks', hRmarks', hout, Rafter, rd, hRbits,
      hRrest, hRscan, rr, hreject, hfull, hcount⟩ :=
      localRepairOneException_run_far_trace P R.hA hrepP hactiveP
        hBmarksP hRmarksP hblistP hrlistP hrange rfl
        hfarP R.hfarB hfar hcapP R.hcapB hpow
        (by simpa [hPbits, b, X] using hbudget)
    let Kfar := domainCharge x G A R.rep b +
      (4 + (12 * Nat.clog 2 X.card + 24 +
        ((15 * Nat.clog 2 X.card + 30) * used +
          attempts * (79 * s + classScanCharge x R.size R.label R.ord b + 50) + 14)))
    have rsource' : Run B localRepairOneExceptionSource σload σsource Kfar := by
      simpa [Kfar, hPσ, hscan, domainCharge, classScanCharge]
        using rsource
    have rprepActual : Run B
        ((Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
          repairDomainSource) R.σ Rafter.σ
        (3 + domainCharge x G A R.rep b) := by
      have rload' : Run B
          (.assign "repairB" (.get "exceptionList" (.var "exceptionIndex")))
          R.σ P.σ 3 := by simpa [hPσ] using rload
      simpa [domainCharge, b, X] using rload'.seq rd
    have hcharge : Kfar = oneExceptionCharge x G A R.rep s
        (classScanCharge x R.size R.label R.ord b) b k attempts used := by
      simp [Kfar, oneExceptionCharge, X, Nat.not_le.mpr hfar]
    have hFarTrace : FarStepTrace R i attempts used := by
      change ∃ Q : ReadyInput B n X.card n s t bufferCap targetCap q b
          G x X groupedB Wbase Wcurrent,
        Run B ((Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
          repairDomainSource) R.σ Q.σ
            (3 + domainCharge x G A R.rep b) ∧
        Q.bits = R.bits ∧ Q.rest = R.rest ∧
        Q.scanUpper = classScanCharge x R.size R.label R.ord b ∧
        ∃ σsource : Env,
          Run B localRepairRetriesSource Q.σ σsource
            (12 * Nat.clog 2 X.card + 24 +
              ((15 * Nat.clog 2 X.card + 30) * used +
                attempts * (79 * s + Q.scanUpper + 50) + 14)) ∧
          (∃ rejected : ℕ,
            rejected ≤ attempts ∧ attempts ≤ rejected + 1 ∧
            LocalFlatLaw.FlatRejectedTrials X.card t s
              (LocalFlatLaw.localBadOutputs X.card s Q.domain
                (numericNeighborhood G) groupedB Wbase b)
              rejected Q.bits) ∧
          (∃ accepted : ℕ,
            LocalFlatLaw.FlatRetryExecution X.card Q.hpositive t s
              (LocalFlatLaw.localBadOutputs X.card s Q.domain
                (numericNeighborhood G) groupedB Wbase b)
              attempts Q.bits used accepted) ∧
          σsource.vars "repairRetriesLeft" + attempts = cap ∧
          σsource.inp =
            (Q.bits.drop (used * Nat.clog 2 X.card)).map Bool.toNat ++ Q.rest ∧
          (σsource.vars "repairRetryStatus" = 3 →
            LocalFlatLaw.FlatRejectedTrials X.card t s
              (LocalFlatLaw.localBadOutputs X.card s Q.domain
                (numericNeighborhood G) groupedB Wbase b) cap Q.bits) ∧
          (σsource.vars "repairRetryStatus" = 2 →
            LocalRepairRetriesSource.FlatSelectorFailed X.card Q.hpositive t s
              (LocalFlatLaw.localBadOutputs X.card s Q.domain
                (numericNeighborhood G) groupedB Wbase b) attempts Q.bits)
      refine ⟨Rafter, ?_, ?_, ?_, ?_, σsource, ?_, hreject, hfull,
        hcount, ?_, ?_, ?_⟩
      · have rload' : Run B
            (.assign "repairB" (.get "exceptionList" (.var "exceptionIndex")))
            R.σ P.σ 3 := by simpa [hPσ] using rload
        simpa [domainCharge, b, X] using rload'.seq rd
      · exact hRbits.trans hPbits
      · exact hRrest.trans hPrest
      · exact hRscan.trans hscan
      · simpa [hRscan] using rr
      · simpa [hRbits, hRrest] using hinp
      · intro hstatus3
        have hcapAfter : Rafter.σ.vars "repairRetryCap" = cap := by
          rw [rd.frame_var "repairRetryCap" (by decide)]
          exact hcapP
        have hbudgetAfter : cap * (s * t * Nat.clog 2 X.card) ≤
            Rafter.bits.length := by
          simpa [hRbits, hPbits, b, X] using hbudget
        obtain ⟨σalt, aalt, ualt, ralt, _haalt, _hualt,
          _hinalt, _hnalt, _hqalt, _htalt, _hralt, _hdalt,
          _houtalt, _hrejectalt, _hfullalt, hcountalt,
          hexhaustalt, _hselectoralt⟩ :=
          localRepairRetriesSource_run_trace_failure Rafter
            hcapAfter R.hcapB hbudgetAfter
        obtain ⟨_, _, hbig⟩ := rr
        obtain ⟨_, _, hbigAlt⟩ := ralt
        have hσ : σsource = σalt :=
          (BigStep.unique hbig.bigStep hbigAlt.bigStep).1
        have ha : attempts = aalt := by
          rw [hσ] at hcount
          omega
        have hstatusAlt : σalt.vars "repairRetryStatus" = 3 := by
          rw [← hσ]
          exact hstatus3
        have haCap : attempts = cap := by
          rcases hout with hsuccess | hfailure | hexhaust
          · omega
          · omega
          · exact hexhaust.2.1
        simpa [b, X, ← ha, haCap] using hexhaustalt hstatusAlt
      · intro hstatus2
        have hcapAfter : Rafter.σ.vars "repairRetryCap" = cap := by
          rw [rd.frame_var "repairRetryCap" (by decide)]
          exact hcapP
        have hbudgetAfter : cap * (s * t * Nat.clog 2 X.card) ≤
            Rafter.bits.length := by
          simpa [hRbits, hPbits, b, X] using hbudget
        obtain ⟨σalt, aalt, ualt, ralt, _haalt, _hualt,
          _hinalt, _hnalt, _hqalt, _htalt, _hralt, _hdalt,
          _houtalt, _hrejectalt, _hfullalt, hcountalt,
          _hexhaustalt, hselectoralt⟩ :=
          localRepairRetriesSource_run_trace_failure Rafter
            hcapAfter R.hcapB hbudgetAfter
        obtain ⟨_, _, hbig⟩ := rr
        obtain ⟨_, _, hbigAlt⟩ := ralt
        have hσ : σsource = σalt :=
          (BigStep.unique hbig.bigStep hbigAlt.bigStep).1
        have ha : attempts = aalt := by
          rw [hσ] at hcount
          omega
        have hstatusAlt : σalt.vars "repairRetryStatus" = 2 := by
          rw [← hσ]
          exact hstatus2
        simpa [b, X, ← ha] using hselectoralt hstatusAlt
    let bitsNext := R.bits.drop (used * Nat.clog 2 X.card)
    have hinp' : σsource.inp = bitsNext.map Bool.toNat ++ R.rest := by
      simpa [bitsNext, hPbits, hPrest] using hinp
    have hqpow' : σsource.vars "qpow" = σload.vars "qpow" := by
      simpa [hPσ] using hqpow
    rcases hout with hsuccess | hfailure | hexhaust
    · obtain ⟨hstatus, D, hlen, hDmem, hiso, hsample⟩ := hsuccess
      let Wnext := Wcurrent ∪ D.toFinset
      have hdrawA : D.toFinset ⊆ A := by
        intro v hv
        exact difference_subset_ground G A b (R.rep b)
          (hDmem v (List.mem_toFinset.mp hv))
      have hWnextA : Wnext ⊆ A :=
        Finset.union_subset R.hWcurrentA hdrawA
      have hWbaseNext : Wbase ⊆ Wnext :=
        R.hWbase.trans Finset.subset_union_left
      obtain ⟨headTrials, hhead⟩ :=
        far_phase3Repair G A groupedB Wbase Wcurrent b (R.rep b) k s D
          (R.hWbase.trans R.hWcurrentA) hfar hlen hDmem hiso
      obtain ⟨Rnext, rbody, hbits, hindexNext, hstopNext,
        hstatusNext, hfixed⟩ :=
        assemble_success R rload rsource' hindex hstop hi bitsNext
          hinp' hn hqpow' hsample hstatus htrial hrow hdesired
          hBmarks' hRmarks' hWbaseNext hWnextA
      refine ⟨Wnext, Rnext, attempts, used, Kfar, ?_, hcharge,
        hattempts, hused, ?_, hfixed, Or.inl ?_, fun _ => hFarTrace,
        fun _ => hfar,
        fun _ => FarStepTrace.failure_of_actual R hFarTrace
          rprepActual rr (hstatus.trans hstatusNext.symm)⟩
      · simpa [hstatusNext] using rbody
      · simpa [hbits, bitsNext, b, X]
      · exact ⟨hstatusNext, hindexNext, hstopNext, headTrials, hhead⟩
    · obtain ⟨hstatus, hsample⟩ := hfailure
      obtain ⟨Rnext, rbody, hbits, hindexNext, hstopNext,
        hstatusNext, hfixed⟩ :=
        assemble_failure R rload rsource' hindex hi bitsNext
          hinp' hn hqpow' hsample hstatus (Or.inl rfl)
          htrial hrow hdesired hBmarks' hRmarks'
      refine ⟨Wcurrent, Rnext, attempts, used, Kfar, ?_, hcharge,
        hattempts, hused, ?_, hfixed, Or.inr ?_, fun _ => hFarTrace,
        fun _ => hfar,
        fun _ => FarStepTrace.failure_of_actual R hFarTrace
          rprepActual rr (hstatus.trans hstatusNext.symm)⟩
      · simpa [hstatusNext] using rbody
      · simpa [hbits, bitsNext, b, X]
      · exact ⟨Or.inl hstatusNext, hindexNext, hstopNext, rfl⟩
    · obtain ⟨hstatus, _, hsample⟩ := hexhaust
      obtain ⟨Rnext, rbody, hbits, hindexNext, hstopNext,
        hstatusNext, hfixed⟩ :=
        assemble_failure R rload rsource' hindex hi bitsNext
          hinp' hn hqpow' hsample hstatus (Or.inr rfl)
          htrial hrow hdesired hBmarks' hRmarks'
      refine ⟨Wcurrent, Rnext, attempts, used, Kfar, ?_, hcharge,
        hattempts, hused, ?_, hfixed, Or.inr ?_, fun _ => hFarTrace,
        fun _ => hfar,
        fun _ => FarStepTrace.failure_of_actual R hFarTrace
          rprepActual rr (hstatus.trans hstatusNext.symm)⟩
      · simpa [hstatusNext] using rbody
      · simpa [hbits, bitsNext, b, X]
      · exact ⟨Or.inr hstatusNext, hindexNext, hstopNext, rfl⟩
  · have hnear : X.card ≤ (2 * k) / 3 := Nat.le_of_not_gt hfar
    obtain ⟨σsource, rsource, hinp, hn, hqpow, hsample, hstatus,
      htrial, hrow, hdesired, hBmarks', hRmarks'⟩ :=
      localRepairOneException_run_near P R.hA hrepP hactiveP
        hBmarksP hRmarksP hblistP hrlistP hrange rfl
        hfarP R.hfarB hnear
    have rsource' : Run B localRepairOneExceptionSource σload σsource
        (domainCharge x G A R.rep b + 6) := by
      simpa [hPσ, domainCharge] using rsource
    have hinp' : σsource.inp = R.bits.map Bool.toNat ++ R.rest := by
      simpa [hPbits, hPrest] using hinp
    have hqpow' : σsource.vars "qpow" = σload.vars "qpow" := by
      simpa [hPσ] using hqpow
    obtain ⟨Rnext, rbody, hbits, hindexNext, hstopNext, hstatusNext,
      hfixed⟩ :=
      assemble_success R rload rsource' hindex hstop hi R.bits
        hinp' hn hqpow' hsample hstatus htrial hrow hdesired
        hBmarks' hRmarks' R.hWbase R.hWcurrentA
    have hhead := near_phase3Repair G A groupedB Wbase Wcurrent
      b (R.rep b) k s hnear
    refine ⟨Wcurrent, Rnext, 0, 0, domainCharge x G A R.rep b + 6,
      ?_, ?_, by omega, by simp, ?_, hfixed, Or.inl ?_, ?_, ?_, ?_⟩
    · simpa [hstatusNext] using rbody
    · simp [oneExceptionCharge, hnear, hscan, domainCharge,
        classScanCharge, b, X]
    · simpa [hbits]
    · exact ⟨hstatusNext, hindexNext, hstopNext, [], hhead⟩
    · intro hfar'
      exact False.elim (hfar hfar')
    · intro hstatusFail
      rcases hstatusFail with htwo | hthree <;> omega
    · intro hstatusFail
      rcases hstatusFail with htwo | hthree <;> omega

/-- A recorded source call. Every field in a produced record comes from the
checked one-exception Run; the charge is recomputed from its actual vertex,
attempt count, and draw count. -/
structure ExecutedException where
  vertex : ℕ
  attempts : ℕ
  used : ℕ
  completed : Bool

def ExecutedException.bitCost {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset ℕ)
    (rep : ℕ → ℕ) (z : ExecutedException) : ℕ :=
  z.used * Nat.clog 2
    (((numericNeighborhood G z.vertex ∩ A) ∆
      (numericNeighborhood G (rep z.vertex) ∩ A))).card

def ExecutedException.runCost {n : ℕ}
    (x : List ℕ) (G : SimpleGraph (Fin n)) (A : Finset ℕ)
    (rep size label ord : ℕ → ℕ) (s k : ℕ)
    (z : ExecutedException) : ℕ :=
  4 + oneExceptionCharge x G A rep s
    (classScanCharge x size label ord z.vertex)
    z.vertex k z.attempts z.used +
    (if z.completed then 11 else 9)

def traceBitCost {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset ℕ)
    (rep : ℕ → ℕ) (steps : List ExecutedException) : ℕ :=
  (steps.map (ExecutedException.bitCost G A rep)).sum

def traceRunCost {n : ℕ} (x : List ℕ) (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (rep size label ord : ℕ → ℕ)
    (s k : ℕ) (steps : List ExecutedException) : ℕ :=
  (steps.map (ExecutedException.runCost x G A rep size label ord s k)).sum

/-- Ordered source calls retained alongside the compact numeric exception
trace. A far call carries the actual prepared local retry Run and its stopped
rejection/selector traces; later calls start in its actual poststate. -/
inductive StepChain
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A : Finset ℕ} :
    {W : Finset ℕ} →
      LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A W → Env → List ExecutedException → Prop
  | nil (R)
      (hguard : (Cond.lt (.var "exceptionIndex")
        (.var "exceptionStop")).evalB B R.σ = some false) :
      StepChain R R.σ []
  | cons {W Wnext : Finset ℕ}
      (R : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A W)
      (Rnext : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wnext)
      (i : ℕ) (z : ExecutedException) (tail : List ExecutedException)
      (hindex : R.σ.vars "exceptionIndex" = i)
      (hguard : (Cond.lt (.var "exceptionIndex")
        (.var "exceptionStop")).evalB B R.σ = some true)
      (hvertex : z.vertex = R.exceptionList i)
      (hbody : ∃ K, Run B exceptionRepairBody R.σ Rnext.σ K)
      (hbits : Rnext.bits = R.bits.drop
        (ExecutedException.bitCost G A R.rep z))
      (hfixed : SameFixed R Rnext)
      (hfar : (2 * k) / 3 <
        (((numericNeighborhood G z.vertex ∩ A) ∆
          (numericNeighborhood G (R.rep z.vertex) ∩ A))).card →
        FarStepTrace R i z.attempts z.used)
      (hfailedFar : (Rnext.σ.vars "repairRetryStatus" = 2 ∨
          Rnext.σ.vars "repairRetryStatus" = 3) →
        (2 * k) / 3 <
          (((numericNeighborhood G z.vertex ∩ A) ∆
            (numericNeighborhood G (R.rep z.vertex) ∩ A))).card)
      (hfailureTrace : (Rnext.σ.vars "repairRetryStatus" = 2 ∨
          Rnext.σ.vars "repairRetryStatus" = 3) →
        FarStepFailureTrace R i z.attempts z.used
          (Rnext.σ.vars "repairRetryStatus"))
      (hfailedStop : (Rnext.σ.vars "repairRetryStatus" = 2 ∨
          Rnext.σ.vars "repairRetryStatus" = 3) →
        (Cond.lt (.var "exceptionIndex")
          (.var "exceptionStop")).evalB B Rnext.σ = some false)
      {σfinal : Env} (htail : StepChain Rnext σfinal tail) :
      StepChain R σfinal (z :: tail)

private lemma suffix_cons {e : ℕ} (entry : ℕ → ℕ)
    {i : ℕ} (hi : i < e) :
    (Stack.toList e entry).drop i =
      entry i :: (Stack.toList e entry).drop (i + 1) := by
  have hil : i < (Stack.toList e entry).length := by
    simpa [Stack.toList] using hi
  have hget : (Stack.toList e entry)[i] = entry i := by
    simp [Stack.toList]
  simpa [hget] using List.drop_eq_getElem_cons hil

lemma loop_guard {B : ℕ} {σ : Env} {i stop : ℕ}
    (hindex : σ.vars "exceptionIndex" = i)
    (hstop : σ.vars "exceptionStop" = stop)
    (hiB : i < B) (hstopB : stop < B) :
    (Cond.lt (.var "exceptionIndex") (.var "exceptionStop")).evalB B σ =
      some (decide (i < stop)) := by
  simpa [hindex, hstop] using evalB_condLt
    (evalB_var (by rw [hindex]; exact hiB : σ.vars "exceptionIndex" < B))
    (evalB_var (by rw [hstop]; exact hstopB : σ.vars "exceptionStop" < B))

private lemma runWhileTrue {B : ℕ} {b : Cond} {c : Com}
    {σ σ₁ σ₂ : Env} {P Q : ℕ}
    (hb : b.evalB B σ = some true)
    (hbody : Run B c σ σ₁ P)
    (hloop : Run B (.while b c) σ₁ σ₂ Q) :
    Run B (.while b c) σ σ₂ (1 + b.size + P + Q) := by
  obtain ⟨p, hp, hbs⟩ := hbody
  obtain ⟨q, hq, hbs'⟩ := hloop
  exact ⟨1 + b.size + p + q, by omega,
    BigStepB.while_true hb hbs hbs'⟩

/-- Structural induction on the remaining packed prefix. The proof runs the
same fixed while command at every stage; only the state and read index vary. -/
lemma loop_run_aux
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A : Finset ℕ}
    (fuel : ℕ) :
    ∀ {Wcurrent : Finset ℕ}
      (R : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wcurrent) (i : ℕ),
      i + fuel = e →
      R.σ.vars "exceptionIndex" = i →
      R.σ.vars "exceptionStop" = e →
      R.σ.vars "repairRetryStatus" = 1 →
      fuel * (cap * (s * t * Nat.clog 2 n)) ≤ R.bits.length →
      ∃ (Wfinal : Finset ℕ)
        (Rfinal : LoopInput B n s t bufferCap targetCap q cap k e
          G x E groupedB Wbase A Wfinal)
        (steps : List ExecutedException),
        Run B (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
          exceptionRepairBody) R.σ Rfinal.σ
          (4 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) ∧
        Rfinal.bits = R.bits.drop (traceBitCost G A R.rep steps) ∧
        SameFixed R Rfinal ∧
        steps.map ExecutedException.vertex =
          ((Stack.toList e R.exceptionList).drop i).take steps.length ∧
        (∀ z ∈ steps, z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t)) ∧
        ((Rfinal.σ.vars "repairRetryStatus" = 1 ∧
            Rfinal.σ.vars "exceptionIndex" = e ∧
            Rfinal.σ.vars "exceptionStop" = e ∧
            steps.length = fuel ∧
            ∃ trials : ∀ b : ℕ, List (LocalTrial
              ((((numericNeighborhood G b ∩ A) \
                (numericNeighborhood G (R.rep b) ∩ A)) ∪
                ((numericNeighborhood G (R.rep b) ∩ A) \
                  (numericNeighborhood G b ∩ A)))) s),
              phase3Scan (fun v => numericNeighborhood G v ∩ A)
                groupedB R.rep k s trials
                ((Stack.toList e R.exceptionList).drop i)
                Wbase Wcurrent = some Wfinal) ∨
          ((Rfinal.σ.vars "repairRetryStatus" = 2 ∨
              Rfinal.σ.vars "repairRetryStatus" = 3) ∧
            Rfinal.σ.vars "exceptionIndex" < e ∧
            Rfinal.σ.vars "exceptionStop" =
              Rfinal.σ.vars "exceptionIndex" ∧
            steps.length ≤ fuel)) ∧
        StepChain R Rfinal.σ steps := by
  induction fuel with
  | zero =>
      intro Wcurrent R i hremaining hindex hstop hstatus hbudget
      have hie : i = e := by omega
      have heB : e < B := by have := R.heLe; have := R.hn1B; omega
      have hguard : (Cond.lt (.var "exceptionIndex")
          (.var "exceptionStop")).evalB B R.σ = some false := by
        simpa [hie] using loop_guard hindex hstop (by omega : i < B) heB
      have rloop : Run B
          (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
            exceptionRepairBody) R.σ R.σ 4 := by
        simpa [Cond.size, Expr.size] using
          (Run.while_false (c := exceptionRepairBody) hguard)
      have hnil : (Stack.toList e R.exceptionList).drop i = [] := by
        exact List.drop_eq_nil_of_le (by simpa [Stack.toList] using
          (show e ≤ i by omega))
      refine ⟨Wcurrent, R, [], ?_, by simp [traceBitCost],
        SameFixed.refl R, by simp, by simp, Or.inl ?_, StepChain.nil R hguard⟩
      · simpa [traceRunCost] using rloop
      · refine ⟨hstatus, by simpa [hie] using hindex, hstop, rfl, ?_⟩
        refine ⟨fun _ => [], ?_⟩
        simp [hnil, phase3Scan]
  | succ fuel ih =>
      intro Wcurrent R i hremaining hindex hstop hstatus hbudget
      have hi : i < e := by omega
      have hiB : i < B := by have := R.heLe; have := R.hn1B; omega
      have heB : e < B := by have := R.heLe; have := R.hn1B; omega
      let b := R.exceptionList i
      let X := ((numericNeighborhood G b ∩ A) ∆
        (numericNeighborhood G (R.rep b) ∩ A))
      have hclog : Nat.clog 2 X.card ≤ Nat.clog 2 n :=
        Nat.clog_mono_right 2
          (difference_card_le_n G A R.hA b (R.rep b))
      have hcallBudget : cap * (s * t * Nat.clog 2 X.card) ≤
          R.bits.length := by
        calc
          cap * (s * t * Nat.clog 2 X.card) ≤
              cap * (s * t * Nat.clog 2 n) := by gcongr
          _ = 1 * (cap * (s * t * Nat.clog 2 n)) := by simp
          _ ≤ (fuel + 1) * (cap * (s * t * Nat.clog 2 n)) :=
            Nat.mul_le_mul_right _ (by omega)
          _ ≤ R.bits.length := hbudget
      have hguard : (Cond.lt (.var "exceptionIndex")
          (.var "exceptionStop")).evalB B R.σ = some true := by
        simpa [hi] using loop_guard hindex hstop hiB heB
      obtain ⟨Wnext, Rnext, attempts, used, charge, rbody, hcharge,
        hattempts, hused, hbits, hfixed, hout, hFarTrace, hfailedFar,
        hfailureTrace⟩ :=
        one_step_run_trace R hindex hstop hi
          (by simpa [b, X] using hcallBudget)
      let step : ExecutedException :=
        ⟨b, attempts, used, Rnext.σ.vars "repairRetryStatus" = 1⟩
      rcases hout with hsuccess | hfailure
      · obtain ⟨hstatusNext, hindexNext, hstopNext,
          headTrials, hhead⟩ := hsuccess
        have husedCap : used ≤ cap * (s * t) :=
          hused.trans (Nat.mul_le_mul_right (s * t) hattempts)
        have hbitLe : used * Nat.clog 2 X.card ≤
            cap * (s * t * Nat.clog 2 n) := by
          calc
            used * Nat.clog 2 X.card ≤
                (cap * (s * t)) * Nat.clog 2 n := by gcongr
            _ = cap * (s * t * Nat.clog 2 n) := by ring
        have hbudgetTail : fuel * (cap * (s * t * Nat.clog 2 n)) ≤
            Rnext.bits.length := by
          have hbitLe' : used * Nat.clog 2
              (((numericNeighborhood G (R.exceptionList i) ∩ A) ∆
                (numericNeighborhood G (R.rep (R.exceptionList i)) ∩ A))).card ≤
              cap * (s * t * Nat.clog 2 n) := by
            simpa [X, b] using hbitLe
          rw [hbits]
          simp only [List.length_drop]
          have hsum : fuel * (cap * (s * t * Nat.clog 2 n)) +
              cap * (s * t * Nat.clog 2 n) ≤ R.bits.length := by
            simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hbudget
          omega
        obtain ⟨Wfinal, Rfinal, tailSteps, rtail,
          hbitsTail, hfixedTail, hmapTail, hvalidTail, houtTail,
          hchainTail⟩ :=
          ih Rnext (i + 1) (by omega) hindexNext hstopNext
            hstatusNext hbudgetTail
        have hrepEq : Rnext.rep = R.rep := hfixed.2.1
        have hsizeEq : Rnext.size = R.size := hfixed.2.2.1
        have hlabelEq : Rnext.label = R.label := hfixed.2.2.2.1
        have hordEq : Rnext.ord = R.ord := hfixed.2.2.2.2.1
        have hexceptionEq : Rnext.exceptionList = R.exceptionList := hfixed.1
        have rtail' : Run B
            (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
              exceptionRepairBody) Rnext.σ Rfinal.σ
            (4 + traceRunCost x G A R.rep R.size R.label R.ord s k
              tailSteps) := by
          simpa [hrepEq, hsizeEq, hlabelEq, hordEq] using rtail
        have hbody' : Run B exceptionRepairBody R.σ Rnext.σ
            (charge + 11) := by simpa [hstatusNext] using rbody
        have rloop : Run B
            (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
              exceptionRepairBody) R.σ Rfinal.σ
            (4 + traceRunCost x G A R.rep R.size R.label R.ord s k
              (step :: tailSteps)) := by
          have rr := runWhileTrue hguard hbody' rtail'
          apply rr.mono
          simp [traceRunCost, ExecutedException.runCost,
            step, b, hstatusNext, hcharge]
          omega
        have hbitsFinal : Rfinal.bits = R.bits.drop
            (traceBitCost G A R.rep (step :: tailSteps)) := by
          rw [hbitsTail, hrepEq, hbits]
          simp [traceBitCost, ExecutedException.bitCost,
            step, b, X, List.drop_drop, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
        have hmap : (step :: tailSteps).map ExecutedException.vertex =
            ((Stack.toList e R.exceptionList).drop i).take
              (step :: tailSteps).length := by
          rw [suffix_cons R.exceptionList hi]
          simpa [step, b, hexceptionEq] using hmapTail
        have hvalid : ∀ z ∈ step :: tailSteps,
            z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t) := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | htail
          · exact ⟨hattempts, hused⟩
          · exact hvalidTail z htail
        have hfixedFinal : SameFixed R Rfinal :=
          SameFixed.trans hfixed hfixedTail
        have hchain : StepChain R Rfinal.σ (step :: tailSteps) := by
          apply StepChain.cons R Rnext i step tailSteps hindex hguard
          · rfl
          · exact ⟨_, rbody⟩
          · simpa [ExecutedException.bitCost, step, b, X] using hbits
          · exact hfixed
          · simpa [step, b, X] using hFarTrace
          · simpa [step, b, X] using hfailedFar
          · simpa [step] using hfailureTrace
          · intro hs
            rcases hs with hs | hs <;> omega
          · exact hchainTail
        refine ⟨Wfinal, Rfinal, step :: tailSteps, rloop,
          hbitsFinal, hfixedFinal, hmap, hvalid, ?_, hchain⟩
        rcases houtTail with htailSuccess | htailFailure
        · rw [hrepEq, hexceptionEq] at htailSuccess
          obtain ⟨hstatusFinal, hindexFinal, hstopFinal,
            hlenTail, trials, htail⟩ := htailSuccess
          have htail' : phase3Scan
              (fun v => numericNeighborhood G v ∩ A) groupedB R.rep k s
              trials ((Stack.toList e R.exceptionList).drop (i + 1))
              Wbase Wnext = some Wfinal := by
            exact htail
          have hnot : b ∉ (Stack.toList e R.exceptionList).drop (i + 1) :=
            packed_exception_tail_nodup R.hprefix hi
          obtain ⟨trialFamily, _, _, hscan⟩ :=
            Lax457868Proofs.LocalRepairPhase3.phase3Scan_prepend_trials
              (fun v => numericNeighborhood G v ∩ A) groupedB R.rep k s
              trials b ((Stack.toList e R.exceptionList).drop (i + 1))
              hnot Wbase Wcurrent Wnext Wfinal headTrials hhead htail'
          refine Or.inl ⟨hstatusFinal, hindexFinal, hstopFinal,
            by simp [hlenTail], trialFamily, ?_⟩
          simpa [suffix_cons R.exceptionList hi, b] using hscan
        · obtain ⟨hstatusFinal, hindexFinal, hstopFinal,
            hlenTail⟩ := htailFailure
          exact Or.inr ⟨hstatusFinal, hindexFinal, hstopFinal,
            by simp; omega⟩
      · obtain ⟨hstatusFail, hindexNext, hstopNext, hWnext⟩ := hfailure
        have hnot : Rnext.σ.vars "repairRetryStatus" ≠ 1 := by
          rcases hstatusFail with htwo | hthree <;> omega
        have hbody' : Run B exceptionRepairBody R.σ Rnext.σ
            (charge + 9) := by simpa [hnot] using rbody
        have hguardStop : (Cond.lt (.var "exceptionIndex")
            (.var "exceptionStop")).evalB B Rnext.σ = some false := by
          have h := loop_guard hindexNext hstopNext hiB hiB
          simpa [hindexNext, hstopNext] using h
        have rstop : Run B
            (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
              exceptionRepairBody) Rnext.σ Rnext.σ 4 := by
          simpa [Cond.size, Expr.size] using
            (Run.while_false (c := exceptionRepairBody) hguardStop)
        have rloop : Run B
            (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
              exceptionRepairBody) R.σ Rnext.σ
              (4 + traceRunCost x G A R.rep R.size R.label R.ord s k [step]) := by
          have rr := runWhileTrue hguard hbody' rstop
          apply rr.mono
          simp [traceRunCost, ExecutedException.runCost,
            step, b, hnot, hcharge]
          omega
        subst Wnext
        have hchain : StepChain R Rnext.σ [step] := by
          apply StepChain.cons R Rnext i step [] hindex hguard
          · rfl
          · exact ⟨_, rbody⟩
          · simpa [ExecutedException.bitCost, step, b, X] using hbits
          · exact hfixed
          · simpa [step, b, X] using hFarTrace
          · simpa [step, b, X] using hfailedFar
          · simpa [step] using hfailureTrace
          · intro _
            exact hguardStop
          · exact StepChain.nil Rnext hguardStop
        refine ⟨Wcurrent, Rnext, [step], rloop, ?_, hfixed,
          ?_, ?_, Or.inr ?_, hchain⟩
        · simpa [traceBitCost, ExecutedException.bitCost, step, b, X]
            using hbits
        · rw [suffix_cons R.exceptionList hi]
          simp [step, b]
        · intro z hz
          simp only [List.mem_singleton] at hz
          subst z
          exact ⟨hattempts, hused⟩
        · exact ⟨hstatusFail, by simpa [hindexNext] using hi,
            hstopNext.trans hindexNext.symm, by simp⟩

/-- The three scalar assignments establish the loop guard and completed
status even when the packed exception list is empty. -/
lemma initialize_loop
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent) :
    ∃ Rinit : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wcurrent,
      Run B exceptionRepairInit R.σ Rinit.σ 6 ∧
      Rinit.bits = R.bits ∧ SameFixed R Rinit ∧
      Rinit.σ.vars "exceptionIndex" = 0 ∧
      Rinit.σ.vars "exceptionStop" = e ∧
      Rinit.σ.vars "repairRetryStatus" = 1 := by
  have hzeroB : 0 < B := by have := R.hthreeB; omega
  have honeB : 1 < B := by have := R.hthreeB; omega
  have heB : e < B := by have := R.heLe; have := R.hn1B; omega
  let σ₁ := R.σ.setVar "exceptionIndex" 0
  let σ₂ := σ₁.setVar "exceptionStop" e
  let σ₃ := σ₂.setVar "repairRetryStatus" 1
  have r₁ : Run B (.assign "exceptionIndex" (.lit 0)) R.σ σ₁ 2 := by
    simpa [σ₁] using Run.assign (x := "exceptionIndex") (evalB_lit hzeroB)
  have hcount₁ : σ₁.vars "exceptionCount" = e := by
    simpa [σ₁] using R.hexceptionCount
  have r₂ : Run B (.assign "exceptionStop" (.var "exceptionCount"))
      σ₁ σ₂ 2 := by
    have hvar : (Expr.var "exceptionCount").evalB B σ₁ = some e := by
      simpa [hcount₁] using
        (evalB_var (by rw [hcount₁]; exact heB :
          σ₁.vars "exceptionCount" < B))
    simpa [σ₂] using Run.assign hvar
  have r₃ : Run B (.assign "repairRetryStatus" (.lit 1))
      σ₂ σ₃ 2 := by
    simpa [σ₃] using Run.assign (x := "repairRetryStatus")
      (evalB_lit honeB)
  have rinit : Run B exceptionRepairInit R.σ σ₃ 6 := by
    simpa [exceptionRepairInit] using r₁.seq (r₂.seq r₃)
  let Rinit : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent := {
    R with
    σ := σ₃
    hinput := by simpa [σ₃, σ₂, σ₁] using R.hinput
    hn := by simpa [σ₃, σ₂, σ₁] using R.hn
    hqpow := by simpa [σ₃, σ₂, σ₁] using R.hqpow
    htarget := by simpa [σ₃, σ₂, σ₁] using R.htarget
    hdrawCap := by simpa [σ₃, σ₂, σ₁] using R.hdrawCap
    hclassCount := by simpa [σ₃, σ₂, σ₁] using R.hclassCount
    hretryCap := by simpa [σ₃, σ₂, σ₁] using R.hretryCap
    hfarBound := by simpa [σ₃, σ₂, σ₁] using R.hfarBound
    hexceptionCount := by simpa [σ₃, σ₂, σ₁] using R.hexceptionCount
    hexceptionList := by simpa [σ₃, σ₂, σ₁] using R.hexceptionList
    hrep := by simpa [σ₃, σ₂, σ₁] using R.hrep
    hactive := by simpa [σ₃, σ₂, σ₁] using R.hactive
    hdrawDomainLength := by simpa [σ₃, σ₂, σ₁] using R.hdrawDomainLength
    hkeyLength := by simpa [σ₃, σ₂, σ₁] using R.hkeyLength
    hdrawsLength := by simpa [σ₃, σ₂, σ₁] using R.hdrawsLength
    hsample := by simpa [σ₃, σ₂, σ₁] using R.hsample
    htrialZero := by simpa [σ₃, σ₂, σ₁] using R.htrialZero
    hrowZero := by simpa [σ₃, σ₂, σ₁] using R.hrowZero
    hdesiredZero := by simpa [σ₃, σ₂, σ₁] using R.hdesiredZero
    hrowLength := by simpa [σ₃, σ₂, σ₁] using R.hrowLength
    hdesiredLength := by simpa [σ₃, σ₂, σ₁] using R.hdesiredLength
    hdiffLength := by simpa [σ₃, σ₂, σ₁] using R.hdiffLength
    hBListLength := by simpa [σ₃, σ₂, σ₁] using R.hBListLength
    hRListLength := by simpa [σ₃, σ₂, σ₁] using R.hRListLength
    hBMarksZero := by simpa [σ₃, σ₂, σ₁] using R.hBMarksZero
    hRMarksZero := by simpa [σ₃, σ₂, σ₁] using R.hRMarksZero
    hclassB := by simpa [σ₃, σ₂, σ₁] using R.hclassB
    hclassSize := by simpa [σ₃, σ₂, σ₁] using R.hclassSize
    hclassStart := by simpa [σ₃, σ₂, σ₁] using R.hclassStart
    hord := by simpa [σ₃, σ₂, σ₁] using R.hord
    hoff := by simpa [σ₃, σ₂, σ₁] using R.hoff
    htgt := by simpa [σ₃, σ₂, σ₁] using R.htgt
    hgroupActive := by simpa [σ₃, σ₂, σ₁] using R.hgroupActive
  }
  refine ⟨Rinit, rinit, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_⟩
  · change σ₃.vars "exceptionIndex" = 0
    simp [σ₃, σ₂, σ₁]
  · change σ₃.vars "exceptionStop" = e
    simp [σ₃, σ₂]
  · change σ₃.vars "repairRetryStatus" = 1
    simp [σ₃]

/-- Execute phase three from the actual packed exception array. The run
reads one entry at a time, retains the phase-two trace classes, and either
completes all entries or stops at the first explicit failure status. The
ordered trace records per-call runtime bounds and exact consumed bit blocks. -/
lemma exceptionRepairLoop_run
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (hbudget : e * (cap * (s * t * Nat.clog 2 n)) ≤ R.bits.length) :
    ∃ (Wfinal : Finset ℕ)
      (Rfinal : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wfinal)
      (steps : List ExecutedException),
      Run B exceptionRepairLoopSource R.σ Rfinal.σ
        (10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) ∧
      Rfinal.bits = R.bits.drop (traceBitCost G A R.rep steps) ∧
      SameFixed R Rfinal ∧
      steps.map ExecutedException.vertex =
        (Stack.toList e R.exceptionList).take steps.length ∧
      (∀ z ∈ steps, z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t)) ∧
      ((Rfinal.σ.vars "repairRetryStatus" = 1 ∧
          Rfinal.σ.vars "exceptionIndex" = e ∧
          Rfinal.σ.vars "exceptionStop" = e ∧
          steps.length = e ∧
          ∃ trials : ∀ b : ℕ, List (LocalTrial
            ((((numericNeighborhood G b ∩ A) \
              (numericNeighborhood G (R.rep b) ∩ A)) ∪
              ((numericNeighborhood G (R.rep b) ∩ A) \
                (numericNeighborhood G b ∩ A)))) s),
            phase3Scan (fun v => numericNeighborhood G v ∩ A)
              groupedB R.rep k s trials
              (Stack.toList e R.exceptionList) Wbase Wstart = some Wfinal ∧
            Wfinal.card ≤ Wstart.card + s * e) ∨
        ((Rfinal.σ.vars "repairRetryStatus" = 2 ∨
            Rfinal.σ.vars "repairRetryStatus" = 3) ∧
          Rfinal.σ.vars "exceptionIndex" < e ∧
          Rfinal.σ.vars "exceptionStop" =
            Rfinal.σ.vars "exceptionIndex" ∧
          steps.length ≤ e)) := by
  obtain ⟨Rinit, rinit, hbitsInit, hfixedInit,
    hindexInit, hstopInit, hstatusInit⟩ := initialize_loop R
  have hbudgetInit : e * (cap * (s * t * Nat.clog 2 n)) ≤
      Rinit.bits.length := by simpa [hbitsInit] using hbudget
  obtain ⟨Wfinal, Rfinal, steps, rloop, hbitsFinal,
    hfixedFinal, hmap, hvalid, hout, _hchain⟩ :=
    loop_run_aux e Rinit 0 (by simp) hindexInit hstopInit
      hstatusInit hbudgetInit
  have hrepEq : Rinit.rep = R.rep := hfixedInit.2.1
  have hsizeEq : Rinit.size = R.size := hfixedInit.2.2.1
  have hlabelEq : Rinit.label = R.label := hfixedInit.2.2.2.1
  have hordEq : Rinit.ord = R.ord := hfixedInit.2.2.2.2.1
  have hexceptionEq : Rinit.exceptionList = R.exceptionList := hfixedInit.1
  have rloop' : Run B
      (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
        exceptionRepairBody) Rinit.σ Rfinal.σ
      (4 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) := by
    simpa [hrepEq, hsizeEq, hlabelEq, hordEq] using rloop
  have rwhole : Run B exceptionRepairLoopSource R.σ Rfinal.σ
      (10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) := by
    have rr := rinit.seq rloop'
    have rr' := rr.mono (by omega : 6 +
      (4 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) ≤
      10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps)
    simpa [exceptionRepairLoopSource] using rr'
  refine ⟨Wfinal, Rfinal, steps, rwhole, ?_,
    SameFixed.trans hfixedInit hfixedFinal, ?_, hvalid, ?_⟩
  · simpa [hrepEq, hbitsInit] using hbitsFinal
  · simpa [hexceptionEq] using hmap
  · rcases hout with hsuccess | hfailure
    · rw [hrepEq, hexceptionEq] at hsuccess
      obtain ⟨hstatus, hindex, hstop, hlen, trials, hscan⟩ := hsuccess
      have hbound : Wfinal.card ≤ Wstart.card + s * e := by
        have hN : ∀ b ∈ Stack.toList e R.exceptionList,
            numericNeighborhood G b ∩ A ⊆ A ∧
            numericNeighborhood G (R.rep b) ∩ A ⊆ A := by
          intro b _
          exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
        have h := Lax457868Proofs.SamplerOutputSize.phase3Scan_output_bound
          (fun v => numericNeighborhood G v ∩ A) groupedB A R.rep k s
          trials (Stack.toList e R.exceptionList) Wbase Wstart
          R.hWcurrentA hN Wfinal hscan
        simpa [Stack.toList] using h.2
      exact Or.inl ⟨hstatus, hindex, hstop, hlen,
        trials, hscan, hbound⟩
    · exact Or.inr hfailure

/-- Companion to `exceptionRepairLoop_run` retaining every actual local call.
The chain starts after initialization and ends at the actual loop poststate;
each link carries its source Run, exact bit drop, and far-branch retry trace. -/
lemma exceptionRepairLoop_run_chain
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (hbudget : e * (cap * (s * t * Nat.clog 2 n)) ≤ R.bits.length) :
    ∃ (Rinit : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wstart)
      (Wfinal : Finset ℕ)
      (Rfinal : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wfinal)
      (steps : List ExecutedException),
      Run B exceptionRepairInit R.σ Rinit.σ 6 ∧
      SameFixed R Rinit ∧ Rinit.bits = R.bits ∧
      StepChain Rinit Rfinal.σ steps ∧
      Run B exceptionRepairLoopSource R.σ Rfinal.σ
        (10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) ∧
      Rfinal.bits = R.bits.drop (traceBitCost G A R.rep steps) ∧
      steps.map ExecutedException.vertex =
        (Stack.toList e R.exceptionList).take steps.length ∧
      (∀ z ∈ steps, z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t)) ∧
      ((Rfinal.σ.vars "repairRetryStatus" = 1 ∧ steps.length = e) ∨
        ((Rfinal.σ.vars "repairRetryStatus" = 2 ∨
            Rfinal.σ.vars "repairRetryStatus" = 3) ∧
          steps.length ≤ e)) := by
  obtain ⟨Rinit, rinit, hbitsInit, hfixedInit,
    hindexInit, hstopInit, hstatusInit⟩ := initialize_loop R
  have hbudgetInit : e * (cap * (s * t * Nat.clog 2 n)) ≤
      Rinit.bits.length := by simpa [hbitsInit] using hbudget
  obtain ⟨Wfinal, Rfinal, steps, rloop, hbitsFinal,
    _hfixedFinal, hmap, hvalid, hout, hchain⟩ :=
    loop_run_aux e Rinit 0 (by simp) hindexInit hstopInit
      hstatusInit hbudgetInit
  have hrepEq : Rinit.rep = R.rep := hfixedInit.2.1
  have hsizeEq : Rinit.size = R.size := hfixedInit.2.2.1
  have hlabelEq : Rinit.label = R.label := hfixedInit.2.2.2.1
  have hordEq : Rinit.ord = R.ord := hfixedInit.2.2.2.2.1
  have hexceptionEq : Rinit.exceptionList = R.exceptionList := hfixedInit.1
  have rloop' : Run B
      (.while (.lt (.var "exceptionIndex") (.var "exceptionStop"))
        exceptionRepairBody) Rinit.σ Rfinal.σ
      (4 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) := by
    simpa [hrepEq, hsizeEq, hlabelEq, hordEq] using rloop
  have rwhole : Run B exceptionRepairLoopSource R.σ Rfinal.σ
      (10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) := by
    have rr := rinit.seq rloop'
    have rr' := rr.mono (by omega : 6 +
      (4 + traceRunCost x G A R.rep R.size R.label R.ord s k steps) ≤
      10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps)
    simpa [exceptionRepairLoopSource] using rr'
  refine ⟨Rinit, Wfinal, Rfinal, steps, rinit, hfixedInit,
    hbitsInit, hchain, rwhole, ?_, ?_, hvalid, ?_⟩
  · simpa [hrepEq, hbitsInit] using hbitsFinal
  · simpa [hexceptionEq] using hmap
  · rcases hout with hsuccess | hfailure
    · exact Or.inl ⟨hsuccess.1, hsuccess.2.2.2.1⟩
    · exact Or.inr ⟨hfailure.1, hfailure.2.2.2⟩

private lemma flagged_setFlag {n : ℕ} {W : Finset ℕ}
    (hW : W ⊆ Finset.range n) :
    flaggedVertices n (setFlag W) = W := by
  ext v
  rw [show v ∈ flaggedVertices n (setFlag W) ↔
    v < n ∧ setFlag W v = 1 from mem_activeVertices]
  constructor
  · intro hv
    simpa [setFlag] using hv.2
  · intro hv
    exact ⟨Finset.mem_range.mp (hW hv), by simp [setFlag, hv]⟩

/-- The phase-three exit packs the final sample exactly once when the loop
completed. On a failed repair it leaves the already accumulated sample and
the explicit status intact, without presenting a packed successful output. -/
lemma exceptionRepairPacked_run
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (hbudget : e * (cap * (s * t * Nat.clog 2 n)) ≤ R.bits.length) :
    ∃ (Wfinal : Finset ℕ)
      (Rfinal : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wfinal)
      (steps : List ExecutedException) (σout : Env),
      Run B exceptionRepairPackedSource R.σ σout
        (10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps +
          (if Rfinal.σ.vars "repairRetryStatus" = 1 then 20 * n + 13 else 5)) ∧
      Rfinal.bits = R.bits.drop (traceBitCost G A R.rep steps) ∧
      SameFixed R Rfinal ∧
      steps.map ExecutedException.vertex =
        (Stack.toList e R.exceptionList).take steps.length ∧
      (∀ z ∈ steps, z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t)) ∧
      σout.inp = Rfinal.bits.map Bool.toNat ++ R.rest ∧
      ((Rfinal.σ.vars "repairRetryStatus" = 1 ∧
          Rfinal.σ.vars "exceptionIndex" = e ∧
          steps.length = e ∧
          ∃ packed : ℕ → ℕ, ∃ trials : ∀ b : ℕ, List (LocalTrial
              ((((numericNeighborhood G b ∩ A) \
                (numericNeighborhood G (R.rep b) ∩ A)) ∪
                ((numericNeighborhood G (R.rep b) ∩ A) \
                  (numericNeighborhood G b ∩ A)))) s),
            σout.arrs "sampleFlags" = arrOf n (setFlag Wfinal) ∧
            σout.arrs "ord" = arrOf n packed ∧
            PrefixEnumerates (σout.vars "sampleCount") packed Wfinal ∧
            σout.vars "sampleCount" = Wfinal.card ∧
            σout.vars "sampleCursor" = n ∧
            (∀ a, a ≠ "ord" → σout.arrs a = Rfinal.σ.arrs a) ∧
            (∀ v, v ≠ "sampleCount" → v ≠ "sampleCursor" →
              σout.vars v = Rfinal.σ.vars v) ∧
            σout.out = Rfinal.σ.out ∧
            phase3Scan (fun v => numericNeighborhood G v ∩ A)
              groupedB R.rep k s trials
              (Stack.toList e R.exceptionList) Wbase Wstart = some Wfinal ∧
            Wfinal.card ≤ Wstart.card + s * e) ∨
        ((Rfinal.σ.vars "repairRetryStatus" = 2 ∨
            Rfinal.σ.vars "repairRetryStatus" = 3) ∧
          Rfinal.σ.vars "exceptionIndex" < e ∧
          σout = Rfinal.σ)) := by
  obtain ⟨Wfinal, Rfinal, steps, rloop, hbits, hfixed,
    hmap, hvalid, hout⟩ := exceptionRepairLoop_run R hbudget
  have hinputFinal : Rfinal.σ.inp =
      Rfinal.bits.map Bool.toNat ++ R.rest := by
    rw [Rfinal.hinput, hfixed.2.2.2.2.2.1]
  have honeB : 1 < B := by have := R.hthreeB; omega
  rcases hout with hsuccess | hfailure
  · obtain ⟨hstatus, hindex, _hstop, hlen, trials,
      hscan, hcard⟩ := hsuccess
    have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
        B Rfinal.σ = some true := by
      simpa [hstatus] using evalB_condEq
        (evalB_var (by rw [hstatus]; exact honeB :
          Rfinal.σ.vars "repairRetryStatus" < B))
        (evalB_lit honeB)
    have hflags01 : ∀ v < n, setFlag Wfinal v ≤ 1 := by
      intro v _
      by_cases hv : v ∈ Wfinal <;> simp [setFlag, hv]
    have hnB : n < B := by have := R.hn1B; omega
    obtain ⟨σout, packed, rpack, hflags, hord, hprefix,
      hcount, hcursor, harrFrame, hvarFrame, hinpPack, houtPack,
      _hpackedCells⟩ :=
      packMarkedSamples_run Rfinal.hn Rfinal.hsample Rfinal.hord
        hflags01 hnB honeB
    have hWrange : Wfinal ⊆ Finset.range n :=
      Rfinal.hWcurrentA.trans R.hA
    have hprefix' : PrefixEnumerates (σout.vars "sampleCount") packed
        Wfinal := by simpa [flagged_setFlag hWrange] using hprefix
    have hcount' : σout.vars "sampleCount" = Wfinal.card := by
      simpa [flagged_setFlag hWrange] using hcount
    have rite : Run B
        (.ite (.eq (.var "repairRetryStatus") (.lit 1))
          packMarkedSamples .skip) Rfinal.σ σout (20 * n + 13) := by
      have hr := Run.ite_true (d := .skip) hguard rpack
      exact hr.mono (by norm_num [Cond.size, Expr.size]; omega)
    have rwhole : Run B exceptionRepairPackedSource R.σ σout
        (10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps +
          (if Rfinal.σ.vars "repairRetryStatus" = 1 then 20 * n + 13 else 5)) := by
      have rr := rloop.seq rite
      simpa [exceptionRepairPackedSource, hstatus] using rr
    refine ⟨Wfinal, Rfinal, steps, σout, rwhole,
      hbits, hfixed, hmap, hvalid, ?_, Or.inl ?_⟩
    · exact hinpPack.trans hinputFinal
    · exact ⟨hstatus, hindex, hlen, packed, trials,
        hflags, hord, hprefix', hcount', hcursor, harrFrame,
        hvarFrame, houtPack, hscan, hcard⟩
  · obtain ⟨hstatus, hindex, _hstop, _hlen⟩ := hfailure
    have hnot : Rfinal.σ.vars "repairRetryStatus" ≠ 1 := by
      rcases hstatus with htwo | hthree <;> omega
    have hzB : Rfinal.σ.vars "repairRetryStatus" < B := by
      have := R.hthreeB
      rcases hstatus with htwo | hthree <;> omega
    have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
        B Rfinal.σ = some false := by
      simpa [hnot] using evalB_condEq (evalB_var hzB)
        (evalB_lit honeB)
    have rite : Run B
        (.ite (.eq (.var "repairRetryStatus") (.lit 1))
          packMarkedSamples .skip) Rfinal.σ Rfinal.σ 5 := by
      simpa [Cond.size, Expr.size] using
        (Run.ite_false (c := packMarkedSamples) hguard Run.skip)
    have rwhole : Run B exceptionRepairPackedSource R.σ Rfinal.σ
        (10 + traceRunCost x G A R.rep R.size R.label R.ord s k steps +
          (if Rfinal.σ.vars "repairRetryStatus" = 1 then 20 * n + 13 else 5)) := by
      have rr := rloop.seq rite
      simpa [exceptionRepairPackedSource, hnot] using rr
    exact ⟨Wfinal, Rfinal, steps, Rfinal.σ, rwhole,
      hbits, hfixed, hmap, hvalid, hinputFinal,
      Or.inr ⟨hstatus, hindex, rfl⟩⟩

end
end Lax457868Proofs.ExceptionRepairLoop
