import Mathlib.Tactic
import Lax457868Proofs.DrawLogSetup
import Lax457868Proofs.SequentialDraws
import Lax457868Proofs.SamplePacking
import Lax457868Proofs.ClassRepresentativeTrace
import Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight
import Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
import Lax808846Proofs.Lib.Fill

/-!
The fixed initial-sample source routine clears its flags, sets up the draw
width, performs capped with-replacement draws from one flat fair-bit tape,
and packs the sample only after every requested draw succeeds.
-/

namespace Lax457868Proofs.InitialDrawSampleSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.DrawLogSetup
open Lax457868Proofs.SequentialDraws
open Lax457868Proofs.DrawBuffer
open Lax457868Proofs.IndexedDrawRam
open Lax457868Proofs.FairBitRam
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FairBitRam
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlLog

/-- The fixed prelude clears arbitrary old flags, initializes the reported
sample size, computes the exact draw width, and selects key cell zero. -/
def initialDrawSamplePrelude : Com :=
  seqs [clearArray "sampleFlags" "n",
    .assign "sampleCount" (.lit 0), drawLogSetup,
    .assign "v" (.lit 0)]

/-- Fixed full initial sample source: successful batches are packed; a failed
batch stops with cleared flags and the initialized zero sample count. -/
def initialDrawSampleSource : Com :=
  initialDrawSamplePrelude.seq
    (sequentialDraws.seq
      (.ite (.eq (.var "batchFailed") (.lit 0)) markAndPackSamples .skip))

/-- Cost charged to an execution, separating source draw work, setup and the
successful marking/packing pass. `actualCalls` includes the exhausted call
when the capped loop fails. -/
def initialDrawSampleCost (n m used actualCalls drawCount : ℕ) (failed : Bool) : ℕ :=
  (15 * Nat.clog 2 m + 30) * used + 43 * actualCalls +
    12 * Nat.clog 2 m +
    (if failed then 11 * n + 43 else 31 * n + 12 * drawCount + 57)

/-- The prelude accepts any old sample-flag contents and clears them before
the first draw. All other arrays, input and output are preserved. -/
lemma initialDrawSamplePrelude_run
    {B n m : ℕ} {σ : Env} {flags : ℕ → ℕ}
    (hn : σ.vars "n" = n) (hnB : n < B)
    (hqpow : σ.vars "qpow" < B)
    (hmod : σ.vars "drawModulus" = m) (hmB : m < B)
    (hpowB : 2 ^ Nat.clog 2 m < B)
    (hflags : σ.arrs "sampleFlags" = arrOf n flags)
    (honeB : 1 < B) :
    ∃ τ, Run B initialDrawSamplePrelude σ τ
        (11 * n + 12 * Nat.clog 2 m + 28) ∧
      τ.arrs "sampleFlags" = arrOf n (fun _ => 0) ∧
      τ.vars "n" = n ∧ τ.vars "qpow" = σ.vars "qpow" ∧
      τ.vars "drawModulus" = m ∧ τ.vars "L" = Nat.clog 2 m ∧
      τ.vars "v" = 0 ∧ τ.vars "sampleCount" = 0 ∧
      (∀ a, a ≠ "sampleFlags" → τ.arrs a = σ.arrs a) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  obtain ⟨σ₁, flags₁, hclear, hflags₁, hzero⟩ :=
    clearArray_run hflags hn (by decide) hnB
  let σ₂ := σ₁.setVar "sampleCount" 0
  have hcount : Run B (.assign "sampleCount" (.lit 0)) σ₁ σ₂ 2 := by
    simpa [σ₂] using Run.assign (evalB_lit (by omega : 0 < B))
  have hn₁ : σ₁.vars "n" = n :=
    (hclear.frame_var "n" (by simp [clearArray, Fill.put, seqs, inc, Com.wvars])).trans hn
  have hqpow₁ : σ₁.vars "qpow" = σ.vars "qpow" :=
    hclear.frame_var "qpow" (by simp [clearArray, Fill.put, seqs, inc, Com.wvars])
  have hmod₁ : σ₁.vars "drawModulus" = m := by
    rw [hclear.frame_var "drawModulus"
      (by simp [clearArray, Fill.put, seqs, inc, Com.wvars]), hmod]
  have hqpow₂ : σ₂.vars "qpow" = σ.vars "qpow" := by simp [σ₂, hqpow₁]
  have hn₂ : σ₂.vars "n" = n := by simp [σ₂, hn₁]
  have hmod₂ : σ₂.vars "drawModulus" = m := by simp [σ₂, hmod₁]
  obtain ⟨σ₃, hsetup, hn₃, hqpow₃, hL₃, hmod₃, _, _, _, harr₃, _, _⟩ :=
    drawLogSetup_run (by rw [hn₂]; exact hnB)
      (by rw [hqpow₂]; exact hqpow) hmod₂ hmB hpowB
  let σ₄ := σ₃.setVar "v" 0
  have hv : Run B (.assign "v" (.lit 0)) σ₃ σ₄ 2 := by
    simpa [σ₄] using Run.assign (evalB_lit (by omega : 0 < B))
  have hwhole : Run B initialDrawSamplePrelude σ σ₄
      (11 * n + 12 * Nat.clog 2 m + 28) := by
    have h := Run.seq hclear (Run.seq hcount (Run.seq hsetup hv))
    change Run B (seqs [clearArray "sampleFlags" "n",
      .assign "sampleCount" (.lit 0), drawLogSetup,
      .assign "v" (.lit 0)]) σ σ₄ _
    exact h.mono (by norm_num; omega)
  refine ⟨σ₄, hwhole, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      σ₄.arrs "sampleFlags" = σ₃.arrs "sampleFlags" :=
        hv.frame_arr "sampleFlags" (by decide)
      _ = arrOf n flags₁ := (harr₃ "sampleFlags").trans hflags₁
      _ = arrOf n (fun _ => 0) := arrOf_congr (by
        intro i hi; exact hzero i hi)
  · exact hn₃.trans hn₂
  · exact hqpow₃.trans hqpow₂
  · exact hmod₃
  · exact hL₃
  · simp [σ₄]
  · calc
      σ₄.vars "sampleCount" = σ₃.vars "sampleCount" :=
        hv.frame_var "sampleCount" (by decide)
      _ = σ₂.vars "sampleCount" := hsetup.frame_var "sampleCount" (by decide)
      _ = 0 := by simp [σ₂]
  · intro a ha
    exact hwhole.frame_arr a (by
      simp [initialDrawSamplePrelude, clearArray, drawLogSetup,
        computeLog,
        Fill.put, seqs, inc,
        Com.warrs, ha])
  · exact hwhole.frame_inp (by
      simp [initialDrawSamplePrelude, clearArray, drawLogSetup,
        computeLog,
        Fill.put, seqs, inc,
        Com.reads])
  · exact hwhole.out_eq (by
      simp [initialDrawSamplePrelude, clearArray, drawLogSetup,
        computeLog,
        Fill.put, seqs, inc,
        Com.NoWrite])

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

private lemma draw_range_of_enum {m n : ℕ} {domain : ℕ → ℕ}
    {A : Finset ℕ} (henum : PrefixEnumerates m domain A)
    (hA : A ⊆ Finset.range n) : ∀ i, i < m → domain i < n := by
  intro i hi
  exact PrefixEnumerates.entry_lt henum
    (by intro v hv; exact Finset.mem_range.mp (hA hv)) i hi

/-- The actual initial-sample command, given the proof-side block view of one
flat fair-bit tape. The full capacity budget is `r*t*clog₂ m` Boolean cells.
The returned input is exactly the original tape with the consumed bit prefix
removed. -/
lemma initialDrawSampleSource_run_tape
    {B n m domainCap r t bufferCap : ℕ} {σ : Env}
    {key domain oldDraws oldFlags ord : ℕ → ℕ} {A : Finset ℕ}
    {tape : Fin (r * t) → Fin (Nat.clog 2 m) → Bool}
    {tail : List Bool} {rest : List ℕ}
    (hn : σ.vars "n" = n) (hnB : n < B)
    (hqpow : σ.vars "qpow" < B)
    (hmod : σ.vars "drawModulus" = m) (hmPos : 0 < m)
    (hmCap : m ≤ domainCap) (henum : PrefixEnumerates m domain A)
    (hAnonempty : A.Nonempty) (hA : A ⊆ Finset.range n)
    (hkey : σ.arrs "key0" = arrOf n key)
    (hdomain : σ.arrs "drawDomain" = arrOf domainCap domain)
    (hdraws : σ.arrs "sampleDraws" = arrOf bufferCap oldDraws)
    (hflags : σ.arrs "sampleFlags" = arrOf n oldFlags)
    (hord : σ.arrs "ord" = arrOf n ord)
    (htarget : σ.vars "batchTarget" = r)
    (hcap : σ.vars "drawCap" = t)
    (hrBuf : r ≤ bufferCap)
    (hrB : r < B) (htB : t < B) (hmB : m < B)
    (htwoB : 2 < B) (honeB : 1 < B)
    (hbits : r * t * Nat.clog 2 m ≤
      (tapeBits tape ++ tail).length)
    (hinp : σ.inp =
      (tapeBits tape ++ tail).map Bool.toNat ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B) :
    ∃ values used failed σ' key',
      DrawTrace m hmPos t r (List.ofFn tape) values used failed ∧
      Run B initialDrawSampleSource σ σ'
        (initialDrawSampleCost n m used
          (values.length + if failed then 1 else 0) values.length failed) ∧
      σ'.vars "batchFailed" = (if failed then 1 else 0) ∧
      σ'.vars "drawCount" = values.length ∧
      values.length + (if failed then 1 else 0) ≤ r ∧
      (failed = false ↔ σ'.vars "drawCount" = r) ∧
      (failed = true → σ'.arrs "sampleFlags" = arrOf n (fun _ => 0) ∧
        σ'.vars "sampleCount" = 0) ∧
      (failed = false →
        σ'.arrs "sampleFlags" =
          arrOf n (fun v => if v ∈ (values.map (fun i => domain i.val)).toFinset then 1 else 0) ∧
        ∃ packed : ℕ → ℕ,
          σ'.arrs "ord" = arrOf n packed ∧
          PrefixEnumerates (σ'.vars "sampleCount") packed
            (values.map (fun i => domain i.val)).toFinset ∧
          σ'.vars "sampleCount" =
            (values.map (fun i => domain i.val)).toFinset.card ∧
          (∀ i (hi : i < values.length), domain values[i].val ∈ A)) ∧
      σ'.inp = ((tapeBits tape ++ tail).drop
        (used * Nat.clog 2 m)).map Bool.toNat ++ rest ∧
      σ'.out = σ.out ∧
      (∀ j < n, j ≠ 0 → key' j = key j) ∧
      σ'.arrs "key0" = arrOf n key' ∧
      σ'.arrs "drawDomain" = arrOf domainCap domain := by
  have hdomainRange := draw_range_of_enum henum hA
  have hnpos : 0 < n := by
    obtain ⟨a, ha⟩ := hAnonempty
    have := Finset.mem_range.mp (hA ha)
    omega
  obtain ⟨τ, hpre, hflags0, hnτ, hqpowτ, hmodτ, hLτ, hvτ,
      hsampleCountτ, hpreFrames, hpreInp, hpreOut⟩ :=
    initialDrawSamplePrelude_run hn hnB hqpow hmod hmB hpowB hflags honeB
  have hkeyτ : τ.arrs "key0" = arrOf n key :=
    (hpreFrames "key0" (by decide)).trans hkey
  have hdomainτ : τ.arrs "drawDomain" = arrOf domainCap domain :=
    (hpreFrames "drawDomain" (by decide)).trans hdomain
  have hdrawsτ : τ.arrs "sampleDraws" = arrOf bufferCap oldDraws :=
    (hpreFrames "sampleDraws" (by decide)).trans hdraws
  have hordτ : τ.arrs "ord" = arrOf n ord :=
    (hpreFrames "ord" (by decide)).trans hord
  have htargetτ : τ.vars "batchTarget" = r := by
    exact hpre.frame_var "batchTarget"
      (by simp [initialDrawSamplePrelude, clearArray, drawLogSetup,
        computeLog, seqs, inc, Com.wvars]) |>.trans htarget
  have hcapτ : τ.vars "drawCap" = t := by
    exact hpre.frame_var "drawCap"
      (by simp [initialDrawSamplePrelude, clearArray, drawLogSetup,
        computeLog, seqs, inc, Com.wvars]) |>.trans hcap
  have hinputτ : τ.inp = flattenBitBlockList (List.ofFn tape) ++
      (tail.map Bool.toNat ++ rest) := by
    rw [hpreInp, hinp]
    simpa [List.append_assoc] using
      raw_tape_input (L := Nat.clog 2 m) (k := r * t)
        (bits := tapeBits tape ++ tail) (tape := tape) (tail := tail)
        (rest := tail.map Bool.toNat ++ rest) rfl
  have hblockCount : r * t ≤ (List.ofFn tape).length := by simp
  obtain ⟨values, used, failed, σd, key', htrace, hdraw, hkeyD,
      hkeyOutside, hdomainD, hdrawsD, hdrawCells, hdrawTail, hcountD,
      hstopD, hbadD, hcomplete, hused, hnum, htargetD, hinpD, hvD,
      hLD, hmodD, hcapD⟩ :=
    sequentialDraws_run_list (B := B) (n := n) (v := 0) (m := m)
      (domainCap := domainCap) (t := t) (bufferCap := bufferCap) (r := r)
      (σ := τ) (g := key) (domain := domain) (draws := oldDraws)
      (blocks := List.ofFn tape) (rest := tail.map Bool.toNat ++ rest)
      hmPos hblockCount hkeyτ hdomainτ hmCap
      (by intro i hi; exact (hdomainRange i hi).trans hnB)
      hdrawsτ hrBuf htargetτ hvτ (by simpa [hvτ] using hnpos)
      hLτ hmodτ hcapτ hinputτ hpowB hnB htwoB htB hmB hrB honeB
  let drawn := values.map (fun i => domain i.val)
  have hdrawnLen : drawn.length = values.length := by simp [drawn]
  have hdrawnValues : ∀ i (hi : i < drawn.length),
      (writeDraws domain oldDraws 0 values) i = drawn[i] := by
    intro i hi
    have hi' : i < values.length := by simpa [drawn] using hi
    have hcell := writeDraws_at domain oldDraws 0 values i hi'
    simpa [drawn, List.getElem_map] using hcell
  have hdrawnRange : ∀ x ∈ drawn, x < n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
    exact hdomainRange i.val i.isLt
  have hflagsD : σd.arrs "sampleFlags" = arrOf n (fun _ => 0) := by
    exact (hdraw.frame_arr "sampleFlags" (by decide)).trans hflags0
  have hordD : σd.arrs "ord" = arrOf n ord := by
    exact (hdraw.frame_arr "ord" (by decide)).trans hordτ
  have hsampleCountD : σd.vars "sampleCount" = 0 := by
    exact (hdraw.frame_var "sampleCount" (by decide)).trans hsampleCountτ
  have hinputFinal :
      σd.inp = ((tapeBits tape ++ tail).drop (used * Nat.clog 2 m)).map
        Bool.toNat ++ rest := by
    rw [hinpD]
    have hused' : used ≤ r * t := by simpa [List.length_ofFn] using hused
    simpa [List.append_assoc] using
      raw_tape_tail (L := Nat.clog 2 m) (k := r * t) (used := used)
        (tape := tape) (tail := tail) (rest := rest) hused'
  have hcond :
      (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σd =
        some (!failed) := by
    have hbadval : σd.vars "batchFailed" = if failed then 1 else 0 := hbadD
    have hzeroB : 0 < B := by omega
    have honeB' : 1 < B := by omega
    have hv : (Expr.var "batchFailed").evalB B σd =
        some (if failed then 1 else 0) := by
      cases failed with
      | false =>
          have hbadLt : σd.vars "batchFailed" < B := by simpa [hbadD] using hzeroB
          simpa [hbadD] using (evalB_var (x := "batchFailed") hbadLt)
      | true =>
          have hbadLt : σd.vars "batchFailed" < B := by simpa [hbadD] using honeB'
          simpa [hbadD] using (evalB_var (x := "batchFailed") hbadLt)
    have hz : (Expr.lit 0).evalB B σd = some 0 := evalB_lit hzeroB
    rw [evalB_condEq hv hz]
    cases failed <;> rfl
  cases failed with
  | false =>
    have hdB : drawn.length < B := by rw [hdrawnLen]; omega
    have hnD : σd.vars "n" = n :=
      (hdraw.frame_var "n" (by decide)).trans hnτ
    obtain ⟨σf, hpack, hflagsF, packed, hordF, hprefixF, hcountF,
        hcountBoundF, hcursorF, hdrawCursorF, hpackArrayFrame, hpackVarsFrame,
        hpackInp, hpackOut⟩ :=
      markAndPackSamples_run (σ := σd) (hn := hnD)
        (hdrawCount := by simpa [hdrawnLen] using hcountD)
        (hdraws := hdrawsD) (hflags := hflagsD) (hord := hordD)
        (hcapacity := by
          rw [hdrawnLen]
          have hvlen : values.length ≤ r := by simpa using hnum
          exact hvlen.trans hrBuf)
        (hvalues := hdrawnValues) (hrange := hdrawnRange)
        hnB hdB honeB
    have hbranch : Run B
        (.ite (.eq (.var "batchFailed") (.lit 0)) markAndPackSamples .skip)
        σd σf (20 * n + 12 * drawn.length + 19) := by
      have h : Run B
          (.ite (.eq (.var "batchFailed") (.lit 0)) markAndPackSamples .skip)
          σd σf
          (1 + (Cond.eq (.var "batchFailed") (.lit 0)).size +
            (20 * n + 12 * drawn.length + 15)) :=
        Run.ite_true hcond hpack
      exact h.mono (by simp [Cond.size, Expr.size]; omega)
    have hwhole : Run B initialDrawSampleSource σ σf
        (initialDrawSampleCost n m used
          (values.length + if false then 1 else 0) values.length false) := by
      have h := Run.seq hpre (Run.seq hdraw hbranch)
      have hcost : 11 * n + 12 * Nat.clog 2 m + 28 +
          (((15 * Nat.clog 2 m + 30) * used + 43 * values.length + 10) +
            (20 * n + 12 * drawn.length + 19)) =
          initialDrawSampleCost n m used values.length values.length false := by
        simp [initialDrawSampleCost, hdrawnLen]
        omega
      exact hcost ▸ h
    have hdrawOut : σd.out = τ.out := hdraw.out_eq (by
      simp [sequentialDraws, sequentialDrawBody, countedIndexedDrawAppend,
        appendDrawIfFound, countedRejectionSelector, indexedDrawLookup,
        Com.NoWrite, seqs, inc]; decide)
    have hout : σf.out = σ.out := hpackOut.trans (hdrawOut.trans hpreOut)
    have hkeyF : σf.arrs "key0" = arrOf n key' :=
      (hpackArrayFrame "key0" (by decide) (by decide)).trans hkeyD
    have hdomainF : σf.arrs "drawDomain" = arrOf domainCap domain :=
      (hpackArrayFrame "drawDomain" (by decide) (by decide)).trans hdomainD
    refine ⟨values, used, false, σf, key', htrace, hwhole, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, hout, hkeyOutside, hkeyF, hdomainF⟩
    · calc
        σf.vars "batchFailed" = σd.vars "batchFailed" :=
          hpackVarsFrame "batchFailed" (by decide) (by decide) (by decide)
        _ = 0 := by simp [hbadD]
    · calc
        σf.vars "drawCount" = σd.vars "drawCount" :=
          hpackVarsFrame "drawCount" (by decide) (by decide) (by decide)
        _ = values.length := hcountD
    · simpa using hnum
    · have hcountFinal : σf.vars "drawCount" = r := by
        calc
          σf.vars "drawCount" = σd.vars "drawCount" :=
            hpackVarsFrame "drawCount" (by decide) (by decide) (by decide)
          _ = r := by simpa [hcountD] using hcomplete
      constructor
      · intro _; exact hcountFinal
      · intro _; rfl
    · intro hfailure; cases hfailure
    · intro _
      refine ⟨?_, packed, hordF, ?_, hcountF, ?_⟩
      · simpa [drawn] using hflagsF
      · simpa [drawn] using hprefixF
      · intro i hi
        have hmem : domain values[i].val ∈
            Stack.toList m domain := by
          simp only [Stack.toList, arrOf, List.mem_map, List.mem_range]
          exact ⟨values[i].val, (values[i]'hi).isLt, rfl⟩
        exact (henum.2 (domain values[i].val)).mp hmem
    · calc
        σf.inp = σd.inp := hpackInp
        _ = ((tapeBits tape ++ tail).drop
          (used * Nat.clog 2 m)).map Bool.toNat ++ rest := hinputFinal
  | true =>
    have hbadOne : σd.vars "batchFailed" = 1 := by simpa [hbadD]
    have hcondFalse :
        (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σd = some false := by
      simpa [hbadOne] using hcond
    have hbranch : Run B
        (.ite (.eq (.var "batchFailed") (.lit 0)) markAndPackSamples .skip)
        σd σd 5 := by
      have h : Run B
          (.ite (.eq (.var "batchFailed") (.lit 0)) markAndPackSamples .skip)
          σd σd (1 + (Cond.eq (.var "batchFailed") (.lit 0)).size + 1) :=
        Run.ite_false hcondFalse Run.skip
      simpa [Cond.size, Expr.size] using h
    have hwhole : Run B initialDrawSampleSource σ σd
        (initialDrawSampleCost n m used
          (values.length + if true then 1 else 0) values.length true) := by
      have h := Run.seq hpre (Run.seq hdraw hbranch)
      change Run B (initialDrawSamplePrelude.seq
        (sequentialDraws.seq
          (.ite (.eq (.var "batchFailed") (.lit 0)) markAndPackSamples .skip)))
        σ σd _
      have hcost : 11 * n + 12 * Nat.clog 2 m + 28 +
          (((15 * Nat.clog 2 m + 30) * used + 43 * (values.length + 1) + 10) + 5) =
          initialDrawSampleCost n m used (values.length + 1) values.length true := by
        simp [initialDrawSampleCost]
        omega
      exact hcost ▸ h
    have hdrawOut : σd.out = τ.out := hdraw.out_eq (by
      simp [sequentialDraws, sequentialDrawBody, countedIndexedDrawAppend,
        appendDrawIfFound, countedRejectionSelector, indexedDrawLookup,
        Com.NoWrite, seqs, inc]; decide)
    have hout : σd.out = σ.out := hdrawOut.trans hpreOut
    refine ⟨values, used, true, σd, key', htrace, hwhole, hbadOne,
      hcountD, ?_, ?_, ?_, ?_, ?_, hout, hkeyOutside, hkeyD, hdomainD⟩
    · simpa using hnum
    · simpa [hcountD] using hcomplete
    · intro _
      exact ⟨hflagsD, hsampleCountD⟩
    · intro hsuccess; cases hsuccess
    · exact hinputFinal

end Lax457868Proofs.InitialDrawSampleSource
