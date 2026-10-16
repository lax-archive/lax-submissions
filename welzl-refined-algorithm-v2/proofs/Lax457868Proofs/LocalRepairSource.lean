import Mathlib.Tactic
import Lax457868Proofs.RepairClassScan
import Lax457868Proofs.SequentialDraws
import Lax457868Proofs.DrawLogSetup
import Lax457868Proofs.SourceRenaming
import Lax457868Proofs.ClassRepresentativeTrace

/-! A local repair keeps the Step 2 class and the original grouping fixed.
Each trial uses private flags; only a successful scan adds its draws to the
current sample. The draw width is computed once for the whole retry loop. -/

namespace Lax457868Proofs.LocalRepairSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.SequentialDraws
open Lax457868Proofs.DrawLogSetup
open Lax457868Proofs.RepairClassScan
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.FairBitRam
open Lax457868Proofs.ClassRepresentativeTrace
open Lax11.GraphEncoding

noncomputable section

/-- The trial marker shares the draw buffer but writes only the private array. -/
def trialActiveNames : Names where
  scalar := Equiv.refl String
  array := Equiv.swap "sampleFlags" "trialActive"

def markTrialActive : Com :=
  renameCom trialActiveNames (markDrawArrayWith 1)

def clearTrialActive : Com :=
  renameCom trialActiveNames (markDrawArrayWith 0)

/-- Renaming the existing touched-entry writer gives the private marker at
exactly the same per-draw cost. -/
lemma trialActiveWith_run {B n drawCap z : ℕ} {σ : Env}
    {draws : List ℕ} {values oldActive : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hcount : σ.vars "drawCount" = draws.length)
    (hdraws : σ.arrs "sampleDraws" = arrOf drawCap values)
    (hactive : σ.arrs "trialActive" = arrOf n oldActive)
    (hcapacity : draws.length ≤ drawCap)
    (hvalues : ∀ i (hi : i < draws.length), values i = draws[i])
    (hrange : ∀ v ∈ draws, v < n)
    (hnB : n < B) (hdrawsB : draws.length < B) (hzB : z < B) :
    ∃ σ' active',
      Run B (renameCom trialActiveNames (markDrawArrayWith z)) σ σ'
        (12 * draws.length + 6) ∧
      σ'.arrs "trialActive" = arrOf n active' ∧
      (∀ i < n, active' i = if i ∈ draws then z else oldActive i) ∧
      σ'.vars "drawCursor" = draws.length ∧
      σ'.arrs "sampleFlags" = σ.arrs "sampleFlags" ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let τ := renameEnv trialActiveNames σ
  have hnτ : τ.vars "n" = n := by
    simpa [τ, trialActiveNames, renameEnv] using hn
  have hcτ : τ.vars "drawCount" = draws.length := by
    simpa [τ, trialActiveNames, renameEnv] using hcount
  have hdτ : τ.arrs "sampleDraws" = arrOf drawCap values := by
    change σ.arrs ((Equiv.swap "sampleFlags" "trialActive").symm
      "sampleDraws") = arrOf drawCap values
    have hswap : (Equiv.swap "sampleFlags" "trialActive").symm
        "sampleDraws" = "sampleDraws" := by decide
    simpa only [hswap] using hdraws
  have haτ : τ.arrs "sampleFlags" = arrOf n oldActive := by
    simpa [τ, trialActiveNames, renameEnv] using hactive
  obtain ⟨τ', active', r, ha', hp, hc, harr, _, hin, hout⟩ :=
    markDrawArrayWith_run hnτ hcτ hdτ haτ hcapacity hvalues hrange
      hnB hdrawsB hzB
  let σ' := renameEnv trialActiveNames τ'
  have hrun : Run B (renameCom trialActiveNames (markDrawArrayWith z))
      σ σ' (12 * draws.length + 6) := by
    simpa [τ, σ', trialActiveNames, renameEnv] using
      (run_rename trialActiveNames r)
  refine ⟨σ', active', hrun, ?_, hp, ?_, ?_, ?_, ?_⟩
  · simpa [σ', trialActiveNames, renameEnv] using ha'
  · simpa [σ', trialActiveNames, renameEnv] using hc
  · simpa [σ', τ, trialActiveNames, renameEnv] using
      harr "trialActive" (by decide)
  · simpa [σ', τ, renameEnv] using hin
  · simpa [σ', τ, renameEnv] using hout

/-- On a successful check, merge the touched draw support into the accumulated
sample flags. -/
def commitTrial : Com := markDrawArrayWith 1

/-- One scan result controls the only write to accumulated sample flags. -/
def repairTrialDecision : Com :=
  .ite (.eq (.var "repairScanSuccess") (.lit 1))
    (commitTrial.seq (.assign "repairRetryStatus" (.lit 1)))
    (.assign "repairRetryStatus" (.lit 0))

def localRepairAfterDraw : Com :=
  .ite (.eq (.var "batchFailed") (.lit 0))
    (markTrialActive.seq
      (repairClassLookupAndScan.seq
        (repairTrialDecision.seq clearTrialActive)))
    (.assign "repairRetryStatus" (.lit 2))

/-- The inner trial has one source draw, a complete class scan on successful
draws, and touched-entry cleanup. A capped draw failure exits with status 2;
an ordinary failed scan exits with status 0; success exits with status 1. -/
def localRepairTrial : Com :=
  sequentialDraws.seq localRepairAfterDraw

/-- The fixed bounded loop consumes its cap from a register. Its trial body
always decrements after a completed trial; zero fuel exits without reading
the random tape. -/
def localRepairRetryBody : Com :=
  .ite (.eq (.var "repairRetriesLeft") (.lit 0))
    (.assign "repairRetryStatus" (.lit 3))
    (localRepairTrial.seq
      (.assign "repairRetriesLeft"
        (.sub (.var "repairRetriesLeft") (.lit 1))))

/-- One fixed source program for all input states and all runtime caps. The
draw logarithm is set up once, before any trial or retry. -/
def localRepairRetriesSource : Com :=
  (Com.assign "repairRetriesLeft" (.var "repairRetryCap")).seq
    ((Com.assign "repairRetryStatus" (.lit 0)).seq
      (drawLogSetup.seq
        ((Com.assign "v" (.var "repairB")).seq
          (.while (.eq (.var "repairRetryStatus") (.lit 0))
            localRepairRetryBody))))

/-- The fixed domain and Step 2 grouping prepared for one exceptional vertex.
Mutable scratch buffers are recorded only by length, so completed trials can
feed the next retry without constraining their overwritten contents. -/
structure ReadyInput (B n m domainCap s t bufferCap targetCap q b : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ)
    (X groupedB Wbase Wcurrent : Finset ℕ) where
  σ : Env
  bits : List Bool
  rest : List ℕ
  domain : ℕ → ℕ
  size : ℕ → ℕ
  starts : ℕ → ℕ
  label : ℕ → ℕ
  ord : ℕ → ℕ
  groupActive : ℕ → ℕ
  xs : List ℕ
  hgraph : EncodesGraph x n G
  htargetCap : targetCap = 2 * edgeCount x
  hpositive : 0 < m
  hdomainCap : m ≤ domainCap
  hdomain : σ.arrs "drawDomain" = arrOf domainCap domain
  henum : PrefixEnumerates m domain X
  hXrange : X ⊆ Finset.range n
  hinput : σ.inp = bits.map Bool.toNat ++ rest
  hn : σ.vars "n" = n
  hqpow : σ.vars "qpow" < B
  hmodulus : σ.vars "drawModulus" = m
  htarget : σ.vars "batchTarget" = s
  hcap : σ.vars "drawCap" = t
  hrepairB : σ.vars "repairB" = b
  hclassCount : σ.vars "classCount" = q
  hkeyLength : (σ.arrs "key0").length = n
  hdrawsLength : (σ.arrs "sampleDraws").length = bufferCap
  hsample : σ.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)
  htrialZero : σ.arrs "trialActive" = arrOf n (fun _ => 0)
  hrowZero : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0)
  hdesiredZero : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0)
  hrowLength : (σ.arrs "trialRowList").length = n
  hdesiredLength : (σ.arrs "trialDesiredList").length = n
  hdiffLength : (σ.arrs "trialDiffList").length = n
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
  hclassFibre : labelClass xs label (label b) =
    groupedB.filter (fun v =>
      trace (numericNeighborhood G) Wbase b =
        trace (numericNeighborhood G) Wbase v)
  hbrange : b < n
  hqle : q ≤ n
  hlabel : label b < q
  hWrange : Wcurrent ⊆ Finset.range n
  hWbase : Wbase ⊆ Wcurrent
  hn1B : n + 1 < B
  htargetCapB : targetCap < B
  hbuffer : s ≤ bufferCap
  hsB : s < B
  htB : t < B
  hmB : m < B
  hpowB : 2 ^ Nat.clog 2 m < B
  hthreeB : 3 < B

/-- The occupied runtime draw cells are the actual selected elements of X,
including repeated selections. -/
lemma ReadyInput.draw_cells
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    (oldDraws : ℕ → ℕ) (values : List (Fin m)) :
    let drawn := values.map (fun i => R.domain i.val)
    (∀ j (hj : j < drawn.length),
      writeDraws R.domain oldDraws 0 values j = drawn[j]) ∧
    (∀ v ∈ drawn, v ∈ X ∧ v < n) := by
  constructor
  · intro j hj
    have hj' : j < values.length := by simpa using hj
    simpa using writeDraws_at R.domain oldDraws 0 values j hj'
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    have hmem : R.domain i.val ∈ X := by
      have hi' : i.val < m := i.isLt
      have hstack : R.domain i.val ∈ Stack.toList m R.domain := by
        change R.domain i.val ∈ (List.range m).map R.domain
        exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr hi', rfl⟩
      exact (R.henum.2 _).mp hstack
    exact ⟨hmem, Finset.mem_range.mp (R.hXrange hmem)⟩

def ReadyInput.scanCharge
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent) (D : List ℕ) : ℕ :=
  54 * (offset x (b + 1) - offset x b) +
    12 * (activeTargets (target x) (setFlag D.toFinset)
      (offset x b) (offset x (b + 1))).card +
    repairClassPotential
      (classStart R.size (R.label b) + R.size (R.label b))
      (classStart R.size (R.label b))
      (repairClassSlotWeight x R.ord) + 47

/-- A draw-independent bound for the fixed class slice. The trace collector
sees at most the degree of b distinct active targets. -/
def ReadyInput.scanUpper
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent) : ℕ :=
  66 * (offset x (b + 1) - offset x b) +
    repairClassPotential
      (classStart R.size (R.label b) + R.size (R.label b))
      (classStart R.size (R.label b))
      (repairClassSlotWeight x R.ord) + 47

lemma ReadyInput.scanCharge_le
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent) (D : List ℕ) :
    R.scanCharge D ≤ R.scanUpper := by
  have hcard := card_activeTargets_le_interval
    (target := target x) (active := setFlag D.toFinset)
    (lo := offset x b) (hi := offset x (b + 1))
  unfold ReadyInput.scanCharge ReadyInput.scanUpper
  omega

private lemma eq_zero_eval {B : ℕ} {σ : Env} {v : String} {z : ℕ}
    (hz : σ.vars v = z) (hzB : z < B) (hzero : 0 < B) :
    (Cond.eq (.var v) (.lit 0)).evalB B σ = some (z == 0) := by
  have hvar : (Expr.var v).evalB B σ = some z := by
    rw [evalB_var_iff]
    exact ⟨hz.symm, by rw [hz]; exact hzB⟩
  rw [evalB_condEq hvar (evalB_lit hzero)]

private lemma eq_one_eval {B : ℕ} {σ : Env} {v : String} {z : ℕ}
    (hz : σ.vars v = z) (hzB : z < B) (hone : 1 < B) :
    (Cond.eq (.var v) (.lit 1)).evalB B σ = some (z == 1) := by
  have hvar : (Expr.var v).evalB B σ = some z := by
    rw [evalB_var_iff]
    exact ⟨hz.symm, by rw [hz]; exact hzB⟩
  rw [evalB_condEq hvar (evalB_lit hone)]

private lemma raw_tape_input {L k : ℕ} {bits : List Bool}
    {tape : Fin k → Fin L → Bool} {tail : List Bool} {rest : List ℕ}
    (hsplit : bits = tapeBits tape ++ tail) :
    bits.map Bool.toNat ++ rest = flattenBitBlockList (List.ofFn tape) ++
      tail.map Bool.toNat ++ rest := by
  rw [hsplit, List.map_append, ClassRepresentativeTrace.tapeBits_words]
  have hflat : flattenBitBlocks tape = flattenBitBlockList (List.ofFn tape) := by
    simp [flattenBitBlocks, flattenBitBlockList_eq_flatMap]
  rw [hflat]

private lemma raw_tape_tail {L k used : ℕ}
    {tape : Fin k → Fin L → Bool} {tail : List Bool} {rest : List ℕ}
    (hu : used ≤ k) :
    flattenBitBlockList ((List.ofFn tape).drop used) ++
        tail.map Bool.toNat ++ rest =
      ((tapeBits tape ++ tail).drop (used * L)).map Bool.toNat ++ rest := by
  have hlen : (tapeBits tape).length = k * L :=
    ClassRepresentativeTrace.tapeBits_length tape
  have hdrop : used * L ≤ (tapeBits tape).length := by
    rw [hlen]
    exact Nat.mul_le_mul_right L hu
  rw [List.drop_append]
  have hzero : used * L - (tapeBits tape).length = 0 := by omega
  simp only [hzero, List.drop_zero, List.map_append]
  rw [ClassRepresentativeTrace.tapeWords_drop]

set_option maxHeartbeats 2000000

/-- One actual capped draw and complete Step 2 class check. The charge uses
the blocks really read, and the fixed class scan potential; it has no scan
over all n vertices per retry. -/
lemma localRepairTrial_run_blocks
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    (hL : R.σ.vars "L" = Nat.clog 2 m)
    (hv : R.σ.vars "v" = b)
    (blocks : List (Fin (Nat.clog 2 m) → Bool)) (tail : List ℕ)
    (hinput : R.σ.inp = flattenBitBlockList blocks ++ tail)
    (hlen : s * t ≤ blocks.length) :
    ∃ (values : List (Fin m)) (used : ℕ) (failed : Bool)
      (σ' : Env),
      DrawTrace m R.hpositive t s blocks values used failed ∧
      Run B localRepairTrial R.σ σ'
        ((15 * Nat.clog 2 m + 30) * used + 79 * s +
          R.scanCharge (values.map (fun i => R.domain i.val)) + 38) ∧
      σ'.inp = flattenBitBlockList (blocks.drop used) ++ tail ∧
      used ≤ blocks.length ∧
      (∀ v ∈ values.map (fun i => R.domain i.val), v ∈ X) ∧
      σ'.arrs "trialActive" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = R.σ.vars "qpow" ∧
      (failed = true →
        σ'.vars "repairRetryStatus" = 2 ∧
        σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) ∧
      (failed = false → σ'.vars "repairRetryStatus" ≤ 1) ∧
      (failed = false →
        (σ'.vars "repairRetryStatus" = 1 ↔
          localTrialIsolates (numericNeighborhood G) groupedB Wbase b
            (values.map (fun i => R.domain i.val))) ∧
        (σ'.vars "repairRetryStatus" = 1 →
          σ'.arrs "sampleFlags" = arrOf n
            (setFlag (Wcurrent ∪ (values.map (fun i => R.domain i.val)).toFinset))) ∧
        (σ'.vars "repairRetryStatus" = 0 →
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) := by
  obtain ⟨key, hkey⟩ := exists_arrOf_of_length R.hkeyLength
  obtain ⟨draws0, hdraws0⟩ := exists_arrOf_of_length R.hdrawsLength
  have hvalueB : ∀ i < m, R.domain i < B := by
    intro i hi
    have hlt := PrefixEnumerates.entry_lt R.henum
      (fun v hv => Finset.mem_range.mp (R.hXrange hv)) i hi
    have hbound := R.hn1B
    omega
  have hnB : n < B := by have := R.hn1B; omega
  have htwoB : 2 < B := by
    have := R.hn1B
    have := R.hbrange
    omega
  have honeB : 1 < B := by omega
  obtain ⟨values, used, failed, σd, key', htrace, rdraw, hkey', _,
      hdomain', hdraws', _, _, hcount', _, hbad', hcomplete,
      hused, hcalls, _, hinp', hv', hL', hmod', hcap'⟩ :=
    sequentialDraws_run_list R.hpositive hlen hkey R.hdomain R.hdomainCap
      hvalueB hdraws0 R.hbuffer R.htarget hv R.hbrange hL
      R.hmodulus R.hcap hinput R.hpowB hnB
      htwoB R.htB R.hmB R.hsB honeB
  let D := values.map (fun i => R.domain i.val)
  have hD := R.draw_cells draws0 values
  have hDlen : D.length = values.length := by simp [D]
  have hDrange : ∀ v ∈ D, v < n := fun v hv => (hD.2 v hv).2
  have hDsubset : ∀ v ∈ D, v ∈ X := fun v hv => (hD.2 v hv).1
  cases failed with
  | true =>
      have hbad : σd.vars "batchFailed" = 1 := by simpa using hbad'
      have hguard : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σd =
          some false := by
        simpa using eq_zero_eval hbad (by omega : 1 < B)
          (by omega : 0 < B)
      let σf := σd.setVar "repairRetryStatus" 2
      have rstatus : Run B (.assign "repairRetryStatus" (.lit 2)) σd σf 2 := by
        simpa [σf] using (Run.assign (evalB_lit htwoB))
      have rafter : Run B localRepairAfterDraw σd σf 6 := by
        simpa [localRepairAfterDraw, Cond.size, Expr.size] using
          (Run.ite_false hguard rstatus)
      have rtrial : Run B localRepairTrial R.σ σf
          ((15 * Nat.clog 2 m + 30) * used +
            43 * (values.length + 1) + 16) := by
        simpa [localRepairTrial] using rdraw.seq rafter
      have rfinal : Run B localRepairTrial R.σ σf
          ((15 * Nat.clog 2 m + 30) * used + 79 * s +
            R.scanCharge D + 38) := by
        exact rtrial.mono (by
          have hlen : values.length + 1 ≤ s := by simpa using hcalls
          omega)
      refine ⟨values, used, true, σf, htrace, ?_, ?_, hused,
        hDsubset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [D] using rfinal
      · simpa [σf] using hinp'
      · calc
          σf.arrs "trialActive" = σd.arrs "trialActive" := by simp [σf]
          _ = R.σ.arrs "trialActive" :=
            rdraw.frame_arr "trialActive" (by decide)
          _ = _ := R.htrialZero
      · calc
          σf.arrs "trialRowMarks" = σd.arrs "trialRowMarks" := by simp [σf]
          _ = R.σ.arrs "trialRowMarks" :=
            rdraw.frame_arr "trialRowMarks" (by decide)
          _ = _ := R.hrowZero
      · calc
          σf.arrs "trialDesiredMarks" = σd.arrs "trialDesiredMarks" := by simp [σf]
          _ = R.σ.arrs "trialDesiredMarks" :=
            rdraw.frame_arr "trialDesiredMarks" (by decide)
          _ = _ := R.hdesiredZero
      · exact (rtrial.frame_var "n" (by decide)).trans R.hn
      · exact rtrial.frame_var "qpow" (by decide)
      · intro _
        exact ⟨by simp [σf],
          by calc
            σf.arrs "sampleFlags" = σd.arrs "sampleFlags" := by simp [σf]
            _ = R.σ.arrs "sampleFlags" :=
              rdraw.frame_arr "sampleFlags" (by decide)
            _ = _ := R.hsample⟩
      · intro hfalse; cases hfalse
      · intro hfalse
        cases hfalse
  | false =>
      have hgood : σd.vars "batchFailed" = 0 := by simpa using hbad'
      have hfull : values.length = s := hcount'.symm.trans (hcomplete.mp rfl)
      have hlenB : D.length < B := by rw [hDlen, hfull]; exact R.hsB
      have hnD : σd.vars "n" = n :=
        (rdraw.frame_var "n" (by decide)).trans R.hn
      have htrialD : σd.arrs "trialActive" = arrOf n (fun _ => 0) :=
        (rdraw.frame_arr "trialActive" (by decide)).trans R.htrialZero
      obtain ⟨σm, activeM, rmark0, hactiveM, hpointM, _, hflagsFrameM,
        _, _⟩ :=
        trialActiveWith_run (draws := D) (z := 1) hnD
          (by rw [hDlen]; exact hcount') hdraws' htrialD
          (by rw [hDlen, hfull]; exact R.hbuffer)
          (by
            intro i hi
            have hi' : i < values.length := by simpa [D] using hi
            simpa [D] using (writeDraws_at R.domain draws0 0 values i hi'))
          hDrange hnB hlenB honeB
      have rmark : Run B markTrialActive σd σm (12 * s + 6) := by
        simpa [markTrialActive, D, hfull] using rmark0
      have hactiveSet : σm.arrs "trialActive" = arrOf n (setFlag D.toFinset) := by
        rw [hactiveM]
        apply arrOf_congr
        intro i hi
        rw [hpointM i hi]
        simp [setFlag]
      have hpre : Run B (sequentialDraws.seq markTrialActive) R.σ σm
          ((15 * Nat.clog 2 m + 30) * used + 43 * s + 10 +
            (12 * s + 6)) := by
        simpa [hfull] using rdraw.seq rmark
      have hrowLen : (σm.arrs "trialRowList").length = n := by
        rw [hpre.frame_arr "trialRowList" (by decide), R.hrowLength]
      have hdesiredLen : (σm.arrs "trialDesiredList").length = n := by
        rw [hpre.frame_arr "trialDesiredList" (by decide), R.hdesiredLength]
      have hdiffLen : (σm.arrs "trialDiffList").length = n := by
        rw [hpre.frame_arr "trialDiffList" (by decide), R.hdiffLength]
      obtain ⟨rowList, hrowList⟩ := exists_arrOf_of_length hrowLen
      obtain ⟨desiredList, hdesiredList⟩ := exists_arrOf_of_length hdesiredLen
      obtain ⟨diffBuffer, hdiffBuffer⟩ := exists_arrOf_of_length hdiffLen
      have hactiveB : ∀ w < n, setFlag D.toFinset w < B := by
        intro w _
        simp only [setFlag]
        split_ifs <;> omega
      have hrowM : σm.arrs "trialRowMarks" = arrOf n (fun _ => 0) :=
        (hpre.frame_arr "trialRowMarks" (by decide)).trans R.hrowZero
      have hdesiredM : σm.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) :=
        (hpre.frame_arr "trialDesiredMarks" (by decide)).trans R.hdesiredZero
      obtain ⟨σc, rscan, hscan, hscan01, hrowC, hdesiredC, _, _,
          _, _, _⟩ :=
        repairClassLookupAndScan_run R.hgraph R.htargetCap
          ((hpre.frame_var "n" (by decide)).trans R.hn)
          ((hpre.frame_var "classCount" (by decide)).trans R.hclassCount)
          ((hpre.frame_var "repairB" (by decide)).trans R.hrepairB)
          ((hpre.frame_arr "classB" (by decide)).trans R.hclassB)
          ((hpre.frame_arr "classSize" (by decide)).trans R.hclassSize)
          ((hpre.frame_arr "repairClassStart" (by decide)).trans R.hclassStart)
          ((hpre.frame_arr "ord" (by decide)).trans R.hord)
          ((hpre.frame_arr "off" (by decide)).trans R.hoff)
          ((hpre.frame_arr "tgt" (by decide)).trans R.htgt)
          hactiveSet hrowM hrowList hdesiredM hdesiredList hdiffBuffer
          R.hbrange R.hqle R.hlabel R.hstartTable R.hclassEnd
          R.hxsCard R.hxsRange R.hactiveCard R.hslice hactiveB
          R.hn1B R.htargetCapB hnB honeB
      have hSrange : D.toFinset ⊆ Finset.range n := by
        intro v hv
        exact Finset.mem_range.mpr (hDrange v (by simpa using hv))
      have hCrange : labelClass R.xs R.label (R.label b) ⊆
          Finset.range n := by
        intro v hv
        exact R.hxsRange (Finset.mem_filter.mp hv).1
      have hiso : σc.vars "repairScanSuccess" = 1 ↔
          localTrialIsolates (numericNeighborhood G) groupedB Wbase b D :=
        scanSuccess_iff_localTrialIsolates R.hgraph groupedB Wbase
          (labelClass R.xs R.label (R.label b)) b D hSrange hCrange
          R.hbrange R.hclassFibre rfl hscan
      have rscan' : Run B repairClassLookupAndScan σm σc (R.scanCharge D) := by
        simpa [ReadyInput.scanCharge] using rscan
      have hcountC : σc.vars "drawCount" = D.length := by
        rw [rscan'.frame_var "drawCount" (by decide),
          rmark.frame_var "drawCount" (by decide), hcount', hDlen]
      have hdrawsC : σc.arrs "sampleDraws" =
          arrOf bufferCap (writeDraws R.domain draws0 0 values) := by
        rw [rscan'.frame_arr "sampleDraws" (by decide),
          rmark.frame_arr "sampleDraws" (by decide)]
        exact hdraws'
      have hnC : σc.vars "n" = n := by
        rw [rscan'.frame_var "n" (by decide),
          rmark.frame_var "n" (by decide)]
        exact hnD
      have hactiveC : σc.arrs "trialActive" = arrOf n activeM := by
        rw [rscan'.frame_arr "trialActive" (by decide)]
        exact hactiveM
      have hflagsC : σc.arrs "sampleFlags" = arrOf n (setFlag Wcurrent) := by
        calc
          σc.arrs "sampleFlags" = σm.arrs "sampleFlags" :=
            rscan'.frame_arr "sampleFlags" (by decide)
          _ = σd.arrs "sampleFlags" := hflagsFrameM
          _ = R.σ.arrs "sampleFlags" :=
            rdraw.frame_arr "sampleFlags" (by decide)
          _ = _ := R.hsample
      have hbatchGuard :
          (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σd = some true := by
        simpa using eq_zero_eval hgood (by omega : 0 < B)
          (by omega : 0 < B)
      by_cases hS : σc.vars "repairScanSuccess" = 1
      · obtain ⟨σp, committed, rcommit0, hcommitted, hpointP, _,
            _, _, _, _⟩ :=
          markDrawArrayWith_run (z := 1) hnC hcountC hdrawsC hflagsC
            (by rw [hDlen, hfull]; exact R.hbuffer)
            (by
              intro i hi
              have hi' : i < values.length := by simpa [D] using hi
              simpa [D] using (writeDraws_at R.domain draws0 0 values i hi'))
            hDrange hnB hlenB honeB
        have rcommit : Run B commitTrial σc σp (12 * s + 6) := by
          simpa [commitTrial, D, hfull] using rcommit0
        have hflagsP : σp.arrs "sampleFlags" =
            arrOf n (setFlag (Wcurrent ∪ D.toFinset)) := by
          rw [hcommitted]
          apply arrOf_congr
          intro i hi
          rw [hpointP i hi]
          by_cases hm : i ∈ D <;> simp [setFlag, Finset.mem_union, hm]
        let σstatus := σp.setVar "repairRetryStatus" 1
        have rstatus : Run B (.assign "repairRetryStatus" (.lit 1))
            σp σstatus 2 := by
          simpa [σstatus] using (Run.assign (evalB_lit honeB))
        have hscanGuard :
            (Cond.eq (.var "repairScanSuccess") (.lit 1)).evalB B σc =
              some true := by
          simpa using eq_one_eval hS (by omega : 1 < B) honeB
        have rdecision : Run B repairTrialDecision σc σstatus
            (12 * s + 12) := by
          have hr := Run.ite_true
            (d := Com.assign "repairRetryStatus" (.lit 0))
            hscanGuard (rcommit.seq rstatus)
          simpa [repairTrialDecision, commitTrial] using
            (hr.mono (by simp [Cond.size, Expr.size]; omega))
        have hactiveStatus : σstatus.arrs "trialActive" =
            arrOf n activeM := by
          rw [show σstatus.arrs "trialActive" = σp.arrs "trialActive" by
            simp [σstatus], rcommit.frame_arr "trialActive" (by decide)]
          exact hactiveC
        have hnStatus : σstatus.vars "n" = n := by
          rw [show σstatus.vars "n" = σp.vars "n" by simp [σstatus],
            rcommit.frame_var "n" (by decide)]
          exact hnC
        have hcountStatus : σstatus.vars "drawCount" = D.length := by
          rw [show σstatus.vars "drawCount" = σp.vars "drawCount" by
            simp [σstatus], rcommit.frame_var "drawCount" (by decide)]
          exact hcountC
        have hdrawsStatus : σstatus.arrs "sampleDraws" =
            arrOf bufferCap (writeDraws R.domain draws0 0 values) := by
          rw [show σstatus.arrs "sampleDraws" = σp.arrs "sampleDraws" by
            simp [σstatus], rcommit.frame_arr "sampleDraws" (by decide)]
          exact hdrawsC
        obtain ⟨σf, activeF, rclear0, hactiveF, hpointF, _,
            hflagsFrameF, _, _⟩ :=
          trialActiveWith_run (draws := D) (z := 0) hnStatus
            hcountStatus hdrawsStatus hactiveStatus
            (by rw [hDlen, hfull]; exact R.hbuffer)
            (by
              intro i hi
              have hi' : i < values.length := by simpa [D] using hi
              simpa [D] using (writeDraws_at R.domain draws0 0 values i hi'))
            hDrange hnB hlenB (by omega : 0 < B)
        have rclear : Run B clearTrialActive σstatus σf (12 * s + 6) := by
          simpa [clearTrialActive, D, hfull] using rclear0
        have hzeroF : σf.arrs "trialActive" = arrOf n (fun _ => 0) := by
          rw [hactiveF]
          apply arrOf_congr
          intro i hi
          rw [hpointF i hi]
          by_cases hm : i ∈ D
          · simp [hm]
          · simp [hm, hpointM i hi]
        have rafter : Run B localRepairAfterDraw σd σf
            (36 * s + R.scanCharge D + 28) := by
          have hseq := rmark.seq (rscan'.seq (rdecision.seq rclear))
          have hr := Run.ite_true
            (d := Com.assign "repairRetryStatus" (.lit 2))
            hbatchGuard hseq
          exact (by simpa [localRepairAfterDraw] using
            (hr.mono (by simp [Cond.size, Expr.size]; omega)))
        have rtrial : Run B localRepairTrial R.σ σf
            ((15 * Nat.clog 2 m + 30) * used + 43 * s + 10 +
              (36 * s + R.scanCharge D + 28)) := by
          simpa [localRepairTrial, hfull] using rdraw.seq rafter
        have rfinal : Run B localRepairTrial R.σ σf
            ((15 * Nat.clog 2 m + 30) * used + 79 * s +
              R.scanCharge D + 38) := rtrial.mono (by omega)
        refine ⟨values, used, false, σf, htrace, ?_, ?_, hused,
          hDsubset, hzeroF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [D] using rfinal
        · exact (rafter.frame_inp (by decide)).trans hinp'
        · exact (rclear.frame_arr "trialRowMarks" (by decide)).trans
            ((rdecision.frame_arr "trialRowMarks" (by decide)).trans hrowC)
        · exact (rclear.frame_arr "trialDesiredMarks" (by decide)).trans
            ((rdecision.frame_arr "trialDesiredMarks" (by decide)).trans
              hdesiredC)
        · exact (rtrial.frame_var "n" (by decide)).trans R.hn
        · exact rtrial.frame_var "qpow" (by decide)
        · intro hfalse; cases hfalse
        · intro _
          rw [rclear.frame_var "repairRetryStatus" (by decide)]
          simp [σstatus]
        · intro _
          refine ⟨?_, ?_, ?_⟩
          · exact iff_of_true
              ((rclear.frame_var "repairRetryStatus" (by decide)).trans
                (by simp [σstatus]))
              (hiso.mp hS)
          · intro _
            exact hflagsFrameF.trans (by
              rw [show σstatus.arrs "sampleFlags" = σp.arrs "sampleFlags" by
                simp [σstatus]]
              exact hflagsP)
          · intro hzero
            have hone : σf.vars "repairRetryStatus" = 1 :=
              (rclear.frame_var "repairRetryStatus" (by decide)).trans
                (by simp [σstatus])
            omega
      · have hscanZero : σc.vars "repairScanSuccess" = 0 := by
          have := hscan01
          omega
        have hscanGuard :
            (Cond.eq (.var "repairScanSuccess") (.lit 1)).evalB B σc =
              some false := by
          simpa using eq_one_eval hscanZero (by omega : 0 < B) honeB
        let σstatus := σc.setVar "repairRetryStatus" 0
        have rstatus : Run B (.assign "repairRetryStatus" (.lit 0))
            σc σstatus 2 := by
          simpa [σstatus] using
            (Run.assign (evalB_lit (by omega : 0 < B)))
        have rdecision : Run B repairTrialDecision σc σstatus 6 := by
          have hr := Run.ite_false
            (c := commitTrial.seq (.assign "repairRetryStatus" (.lit 1)))
            hscanGuard rstatus
          simpa [repairTrialDecision, Cond.size, Expr.size] using hr
        have hactiveStatus : σstatus.arrs "trialActive" =
            arrOf n activeM := by simpa [σstatus] using hactiveC
        have hnStatus : σstatus.vars "n" = n := by
          simpa [σstatus] using hnC
        have hcountStatus : σstatus.vars "drawCount" = D.length := by
          simpa [σstatus] using hcountC
        have hdrawsStatus : σstatus.arrs "sampleDraws" =
            arrOf bufferCap (writeDraws R.domain draws0 0 values) := by
          simpa [σstatus] using hdrawsC
        obtain ⟨σf, activeF, rclear0, hactiveF, hpointF, _,
            hflagsFrameF, _, _⟩ :=
          trialActiveWith_run (draws := D) (z := 0) hnStatus
            hcountStatus hdrawsStatus hactiveStatus
            (by rw [hDlen, hfull]; exact R.hbuffer)
            (by
              intro i hi
              have hi' : i < values.length := by simpa [D] using hi
              simpa [D] using (writeDraws_at R.domain draws0 0 values i hi'))
            hDrange hnB hlenB (by omega : 0 < B)
        have rclear : Run B clearTrialActive σstatus σf (12 * s + 6) := by
          simpa [clearTrialActive, D, hfull] using rclear0
        have hzeroF : σf.arrs "trialActive" = arrOf n (fun _ => 0) := by
          rw [hactiveF]
          apply arrOf_congr
          intro i hi
          rw [hpointF i hi]
          by_cases hm : i ∈ D
          · simp [hm]
          · simp [hm, hpointM i hi]
        have rafter : Run B localRepairAfterDraw σd σf
            (36 * s + R.scanCharge D + 28) := by
          have hseq := rmark.seq (rscan'.seq (rdecision.seq rclear))
          have hr := Run.ite_true
            (d := Com.assign "repairRetryStatus" (.lit 2))
            hbatchGuard hseq
          simpa [localRepairAfterDraw] using
            (hr.mono (by simp [Cond.size, Expr.size]; omega))
        have rtrial : Run B localRepairTrial R.σ σf
            ((15 * Nat.clog 2 m + 30) * used + 43 * s + 10 +
              (36 * s + R.scanCharge D + 28)) := by
          simpa [localRepairTrial, hfull] using rdraw.seq rafter
        have rfinal : Run B localRepairTrial R.σ σf
            ((15 * Nat.clog 2 m + 30) * used + 79 * s +
              R.scanCharge D + 38) := rtrial.mono (by omega)
        have hstatusZero : σf.vars "repairRetryStatus" = 0 := by
          rw [rclear.frame_var "repairRetryStatus" (by decide)]
          simp [σstatus]
        have hflagsF : σf.arrs "sampleFlags" =
            arrOf n (setFlag Wcurrent) := by
          calc
            σf.arrs "sampleFlags" = σstatus.arrs "sampleFlags" :=
              hflagsFrameF
            _ = σc.arrs "sampleFlags" := by simp [σstatus]
            _ = _ := hflagsC
        refine ⟨values, used, false, σf, htrace, ?_, ?_, hused,
          hDsubset, hzeroF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [D] using rfinal
        · exact (rafter.frame_inp (by decide)).trans hinp'
        · exact (rclear.frame_arr "trialRowMarks" (by decide)).trans
            ((rdecision.frame_arr "trialRowMarks" (by decide)).trans hrowC)
        · exact (rclear.frame_arr "trialDesiredMarks" (by decide)).trans
            ((rdecision.frame_arr "trialDesiredMarks" (by decide)).trans
              hdesiredC)
        · exact (rtrial.frame_var "n" (by decide)).trans R.hn
        · exact rtrial.frame_var "qpow" (by decide)
        · intro hfalse; cases hfalse
        · intro _
          omega
        · intro _
          refine ⟨?_, ?_, ?_⟩
          · exact iff_of_false (by omega : σf.vars "repairRetryStatus" ≠ 1)
              (by intro his; exact hS (hiso.mpr his))
          · intro hsuccess
            omega
          · intro _
            exact hflagsF

/-- The same concrete trial reads a flat fair-bit prefix and exposes exactly
the unread suffix, including the unused part of the final capped call. -/
lemma localRepairTrial_run_bits
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    (hL : R.σ.vars "L" = Nat.clog 2 m)
    (hv : R.σ.vars "v" = b)
    (hbudget : s * t * Nat.clog 2 m ≤ R.bits.length) :
    ∃ (values : List (Fin m)) (used : ℕ) (failed : Bool)
      (σ' : Env),
      Run B localRepairTrial R.σ σ'
        ((15 * Nat.clog 2 m + 30) * used + 79 * s +
          R.scanCharge (values.map (fun i => R.domain i.val)) + 38) ∧
      used ≤ s * t ∧
      (failed = false → values.length = s) ∧
      σ'.inp = (R.bits.drop (used * Nat.clog 2 m)).map Bool.toNat ++ R.rest ∧
      (∀ v ∈ values.map (fun i => R.domain i.val), v ∈ X) ∧
      σ'.arrs "trialActive" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = R.σ.vars "qpow" ∧
      (failed = true →
        σ'.vars "repairRetryStatus" = 2 ∧
        σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) ∧
      (failed = false → σ'.vars "repairRetryStatus" ≤ 1) ∧
      (failed = false →
        (σ'.vars "repairRetryStatus" = 1 ↔
          localTrialIsolates (numericNeighborhood G) groupedB Wbase b
            (values.map (fun i => R.domain i.val))) ∧
        (σ'.vars "repairRetryStatus" = 1 →
          σ'.arrs "sampleFlags" = arrOf n
            (setFlag (Wcurrent ∪ (values.map (fun i => R.domain i.val)).toFinset))) ∧
        (σ'.vars "repairRetryStatus" = 0 →
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) := by
  obtain ⟨tape, tail, hsplit⟩ :=
    ClassRepresentativeTrace.splitTape (Nat.clog 2 m) (s * t)
      R.bits hbudget
  let blocks := List.ofFn tape
  have hlenBlocks : s * t ≤ blocks.length := by simp [blocks]
  have hinputBlocks : R.σ.inp = flattenBitBlockList blocks ++
      (tail.map Bool.toNat ++ R.rest) := by
    calc
      R.σ.inp = R.bits.map Bool.toNat ++ R.rest := R.hinput
      _ = flattenBitBlockList blocks ++ tail.map Bool.toNat ++ R.rest := by
        simpa [blocks] using raw_tape_input (rest := R.rest) hsplit
      _ = _ := by simp [List.append_assoc]
  obtain ⟨values, used, failed, σ', htrace, rtrial, hinp, hused,
      hX, htrial, hrow, hdesired, hn, hqpow, hfail, hstatus, hsuccess⟩ :=
    localRepairTrial_run_blocks R hL hv blocks
      (tail.map Bool.toNat ++ R.rest) hinputBlocks hlenBlocks
  have hu : used ≤ s * t := by simpa [blocks] using hused
  have hcomplete : failed = false → values.length = s :=
    (DrawTrace.length_and_status m R.hpositive t htrace).2.mp
  have hinpFlat : σ'.inp =
      (R.bits.drop (used * Nat.clog 2 m)).map Bool.toNat ++ R.rest := by
    calc
      σ'.inp = flattenBitBlockList (blocks.drop used) ++
          tail.map Bool.toNat ++ R.rest := by simpa [List.append_assoc] using hinp
      _ = ((tapeBits tape ++ tail).drop (used * Nat.clog 2 m)).map
          Bool.toNat ++ R.rest := by
        simpa [blocks] using raw_tape_tail (L := Nat.clog 2 m)
          (k := s * t) (used := used) (rest := R.rest) hu
      _ = _ := by rw [← hsplit]
  exact ⟨values, used, failed, σ', rtrial, hu, hcomplete, hinpFlat,
    hX, htrial, hrow, hdesired, hn, hqpow, hfail, hstatus, hsuccess⟩




end
end Lax457868Proofs.LocalRepairSource
