import Mathlib.Tactic
import Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
import Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
import Lax457868Proofs.ReusedOriginal.Construction.ReadKeys
import Lax808846Proofs.Frame
import Lax808846Proofs.Lib.Fill

/-!
Mark the runtime sample-draw array prefix, then pack the distinct marked
vertices into the array interface used by the round partition routine. The
marking and packing code are fixed independently of sampled values. Duplicate
draws repeat an idempotent store. The packing scan reads a zero-one flag array
and writes one entry per marked vertex in increasing vertex order.
-/

namespace Lax457868Proofs.SamplePacking

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys
open Lax808846Proofs.Reasoning.Lib

/-- Scan every vertex and append exactly those whose `sampleFlags` entry is
one to the `ord` prefix.  The cursor and count use private names so the scan
does not collide with partition scratch state. -/
private def packBody : Com :=
  seqs [
    .ite (.eq (.get "sampleFlags" (.var "sampleCursor")) (.lit 1))
      (Fill.put "ord" "sampleCount" (.var "sampleCursor")) .skip,
    inc "sampleCursor"]

/-- Scan every vertex and append exactly those whose `sampleFlags` entry is
one to the `ord` prefix.  The cursor and count use private names so the scan
does not collide with partition scratch state. -/
def packMarkedSamples : Com :=
  seqs [
    .assign "sampleCount" (.lit 0),
    .assign "sampleCursor" (.lit 0),
    .while (.lt (.var "sampleCursor") (.var "n")) packBody]

/-- One fixed-code iteration reads the next sampled vertex from the runtime
draw array, marks that vertex, then advances the cursor. -/
private def markDrawBody : Com :=
  seqs [
    .store "sampleFlags" (.get "sampleDraws" (.var "drawCursor")) (.lit 1),
    inc "drawCursor"]

/-- Fixed IMP+ code for marking the runtime draw-array prefix. The source does
not depend on the sampled values or on the requested draw count. -/
def markDrawArray : Com :=
  seqs [
    .assign "drawCursor" (.lit 0),
    .while (.lt (.var "drawCursor") (.var "drawCount")) markDrawBody]

/-- State invariant for the runtime mark loop: the flag array represents
exactly the sample list prefix scanned so far. -/
private def MarkDrawInv (n drawCount drawCap : ℕ) (draws : List ℕ)
    (values initialFlags flags : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧
  σ.vars "drawCount" = drawCount ∧
  σ.vars "drawCursor" ≤ drawCount ∧
  σ.arrs "sampleDraws" = arrOf drawCap values ∧
  σ.arrs "sampleFlags" = arrOf n flags ∧
  ∀ v < n, flags v =
    if v ∈ (draws.take (σ.vars "drawCursor")).toFinset then 1 else initialFlags v

private lemma markDrawBody_run {B n drawCount drawCap : ℕ}
    {draws : List ℕ} {values initialFlags flags : ℕ → ℕ} {σ : Env}
    (hI : MarkDrawInv n drawCount drawCap draws values initialFlags flags σ)
    (hcursorLt : σ.vars "drawCursor" < drawCount)
    (hcountLen : drawCount = draws.length)
    (hdrawCountB : drawCount < B) (hnB : n < B) (honeB : 1 < B)
    (hcap : drawCount ≤ drawCap)
    (hrange : ∀ v ∈ draws, v < n)
    (hvalues : ∀ i (hi : i < drawCount), values i = draws[i]) :
    ∃ σ' flags', Run B markDrawBody σ σ' 8 ∧
      MarkDrawInv n drawCount drawCap draws values initialFlags flags' σ' ∧
      σ'.vars "drawCursor" = σ.vars "drawCursor" + 1 := by
  rcases hI with ⟨hn, hcount, hcursor, hdraws, hflags, hseen⟩
  let k := σ.vars "drawCursor"
  have hk : k < drawCount := by simpa [k] using hcursorLt
  have hkList : k < draws.length := by simpa [hcountLen] using hk
  have hkCap : k < drawCap := lt_of_lt_of_le hk hcap
  have hd : values k = draws[k] := hvalues k hk
  have hvertex : values k < n := by
    rw [hd]
    exact hrange _ (List.getElem_mem hkList)
  have hdB : values k < B := hvertex.trans hnB
  have hcursorB : σ.vars "drawCursor" < B := hk.trans hdrawCountB
  have hcursorEval : (Expr.var "drawCursor").evalB B σ = some k := by
    simpa [k] using evalB_var hcursorB
  have hdrawGet : (σ.arrs "sampleDraws")[k]? = some (values k) := by
    rw [hdraws]
    exact getElem?_arrOf values hkCap
  have hdrawEval :
      (Expr.get "sampleDraws" (.var "drawCursor")).evalB B σ = some (values k) :=
    evalB_get hcursorEval hdrawGet hdB
  have hstore : Run B
      (.store "sampleFlags" (.get "sampleDraws" (.var "drawCursor")) (.lit 1))
      σ (σ.setArr "sampleFlags" (values k) 1) 4 := by
    apply Run.store hdrawEval (evalB_lit honeB)
    simp [hflags]
    exact hvertex
  let flags' := upd flags (values k) 1
  have hflags' : (σ.setArr "sampleFlags" (values k) 1).arrs "sampleFlags" =
      arrOf n flags' := by
    rw [arrs_setArr, if_pos rfl, hflags, set_arrOf_eq_upd]
  have hcursor' : (σ.setArr "sampleFlags" (values k) 1).vars "drawCursor" = k := by
    simp [k]
  have hincEval :
      (Expr.add (.var "drawCursor") (.lit 1)).evalB B
        (σ.setArr "sampleFlags" (values k) 1) = some (k + 1) := by
    apply evalB_bin
      (by simpa [hcursor'] using evalB_var (by omega : k < B))
      (evalB_lit honeB)
    have hnext : k + 1 < B := by omega
    simpa using hnext
  let σ' := (σ.setArr "sampleFlags" (values k) 1).setVar "drawCursor" (k + 1)
  have hinc : Run B (inc "drawCursor")
      (σ.setArr "sampleFlags" (values k) 1) σ' 4 := by
    simpa [inc, σ', Expr.size] using
      (Run.assign (x := "drawCursor") hincEval)
  have hrun : Run B markDrawBody σ σ' 8 := by
    have h := Run.seq hstore hinc
    simpa [markDrawBody, seqs] using h
  have hflagsSeen : ∀ x < n,
      flags' x = if x ∈ (draws.take (k + 1)).toFinset then 1 else initialFlags x := by
    intro x hx
    have hprev : flags x = if x ∈ (draws.take k).toFinset then 1 else initialFlags x := by
      simpa [k] using hseen x hx
    have hmem : x ∈ (draws.take (k + 1)).toFinset ↔
        x ∈ (draws.take k).toFinset ∨ x = draws[k] := by
      have ht : draws.take (k + 1) = draws.take k ++ [draws[k]] :=
        List.take_succ_eq_append_getElem hkList
      simp only [List.mem_toFinset, ht, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
    simp only [hmem]
    by_cases heq : x = values k
    · have heq' : x = draws[k] := by rw [← hd]; exact heq
      have hnextmem : x ∈ (draws.take (k + 1)).toFinset :=
        hmem.mpr (Or.inr heq')
      change (if x = values k then 1 else flags x) =
        if x ∈ (draws.take k).toFinset ∨ x = draws[k] then 1 else initialFlags x
      rcases hmem.mp hnextmem with hold | hnext
      · rw [if_pos heq, if_pos (Or.inl hold)]
      · rw [if_pos heq, if_pos (Or.inr hnext)]
    · have hne : x ≠ draws[k] := by
        intro hEq
        apply heq
        rw [hd]
        exact hEq
      change (if x = values k then 1 else flags x) =
        if x ∈ (draws.take k).toFinset ∨ x = draws[k] then 1 else initialFlags x
      rw [if_neg heq]
      by_cases hold : x ∈ (draws.take k).toFinset
      · rw [hprev, if_pos hold, if_pos (Or.inl hold)]
      · have hnot : ¬(x ∈ (draws.take k).toFinset ∨ x = draws[k]) :=
          not_or.mpr ⟨hold, hne⟩
        rw [hprev, if_neg hold, if_neg hnot]
  have hdraws' : σ'.arrs "sampleDraws" = arrOf drawCap values := by
    simp [σ', hdraws]
  have hflagsFinal : σ'.arrs "sampleFlags" = arrOf n flags' := by
    simpa [σ'] using hflags'
  have hcursorFinal : σ'.vars "drawCursor" = k + 1 := by simp [σ']
  refine ⟨σ', flags', hrun, ?_, hcursorFinal⟩
  refine ⟨?_, ?_, ?_, hdraws', hflagsFinal, ?_⟩
  · simpa [σ'] using hn
  · simpa [σ'] using hcount
  · rw [hcursorFinal]
    omega
  · simpa [hcursorFinal, k] using hflagsSeen

/-- The loop invariant for packing. `ord` contains the active vertices in
the scanned prefix, in increasing order, and `sampleCount` is its length. -/
def PackInv (n : ℕ) (flags : ℕ → ℕ) (τ : Env) : Prop :=
  τ.arrs "sampleFlags" = arrOf n flags ∧
  τ.vars "n" = n ∧
  τ.vars "sampleCursor" ≤ n ∧
  τ.vars "sampleCount" = (scanList flags 0 (τ.vars "sampleCursor")).length ∧
  Fill.Below "ord" "sampleCount" n
    (fun i => (scanList flags 0 n).getD i 0) τ

private def packTest : Cond :=
  .eq (.get "sampleFlags" (.var "sampleCursor")) (.lit 1)

private def packBodyCost : ℕ := 1 + packTest.size + 7 + 4

/-- One scan turn either appends the current marked vertex or leaves the
prefix alone, then advances the scan cursor. -/
private lemma packBody_run {B n : ℕ} {flags : ℕ → ℕ} {σ : Env}
    (hI : PackInv n flags σ)
    (hcursor : σ.vars "sampleCursor" < n)
    (hflags01 : ∀ v < n, flags v ≤ 1)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B packBody σ σ' packBodyCost ∧ PackInv n flags σ' ∧
      σ'.vars "sampleCursor" = σ.vars "sampleCursor" + 1 := by
  obtain ⟨hflags, hn, hcle, hcount, hfill⟩ := hI
  let k := σ.vars "sampleCursor"
  let count := σ.vars "sampleCount"
  have hflagsB : flags k < B := by
    have hk : k < n := by simpa [k] using hcursor
    have := hflags01 k hk
    omega
  have hkB : k < B := hcursor.trans hnB
  have hget : (Expr.get "sampleFlags" (.var "sampleCursor")).evalB B σ =
      some (flags k) := by
    apply evalB_get (evalB_var (by simpa [k] using hkB)) _ hflagsB
    rw [hflags, getElem?_arrOf _ (by simpa [k] using hcursor)]
  have htestEval : packTest.evalB B σ = some (flags k == 1) := by
    simpa [packTest] using
      evalB_condEq hget (evalB_lit (by omega : 1 < B))
  by_cases hactive : flags k = 1
  · have htestTrue : packTest.evalB B σ = some true := by
      simpa [hactive] using htestEval
    have hcountlt : count < n := by
      change σ.vars "sampleCount" < n
      rw [hcount]
      exact (scanList_length_le flags 0 k).trans_lt (by simpa [k] using hcursor)
    have hvalue : (scanList flags 0 n).getD count 0 = k := by
      change (scanList flags 0 n).getD (σ.vars "sampleCount") 0 = k
      rw [hcount]
      exact scanList_active_getD (by simpa [k] using hcursor) hactive
    let P : Env → Prop := fun τ => PackInv n flags τ ∧
      τ.vars "sampleCursor" = k ∧ τ.vars "sampleCursor" < n ∧
      packTest.evalB B τ = some true
    have hputSpec : Spec B P (Fill.put "ord" "sampleCount" (.var "sampleCursor"))
        (Fill.PutPost "ord" "sampleCount" n
          (fun i => (scanList flags 0 n).getD i 0)) 7 := by
      have hput := Fill.put_spec B n "ord" "sampleCount" (.var "sampleCursor")
        (fun i => (scanList flags 0 n).getD i 0) P
        (by
          intro τ ⟨hτ, _, hτlt, _⟩
          have hcnt : τ.vars "sampleCount" =
              (scanList flags 0 (τ.vars "sampleCursor")).length := hτ.2.2.2.1
          refine ⟨hτ.2.2.2.2, ?_⟩
          rw [hcnt]
          exact (scanList_length_le flags 0 (τ.vars "sampleCursor")).trans_lt hτlt)
        hnB
        (by
          intro τ ⟨hτ, heq, hτlt, _⟩
          have hcnt : τ.vars "sampleCount" =
              (scanList flags 0 (τ.vars "sampleCursor")).length := hτ.2.2.2.1
          have hcur : τ.vars "sampleCursor" < n := hτlt
          have hactiveτ : flags (τ.vars "sampleCursor") = 1 := by
            simpa [heq] using hactive
          have hval := scanList_active_getD hcur hactiveτ
          rw [evalB_var (by omega : τ.vars "sampleCursor" < B)]
          rw [← hcnt] at hval
          rw [hval]
            )
      simpa using hput
    have htestEvalAfter : packTest.evalB B σ = some true := htestTrue
    obtain ⟨σ₁, hputRun, ⟨hfill₁, hcount₁⟩⟩ :=
      hputSpec σ ⟨⟨hflags, hn, hcle, hcount, hfill⟩, rfl, hcursor, htestEvalAfter⟩
    let σ₂ := σ₁.setVar "sampleCursor" (k + 1)
    have hcursor₁ : σ₁.vars "sampleCursor" = k := by
      simpa [k] using hputRun.frame_var "sampleCursor" (by decide)
    have hcursorEval : (Expr.add (.var "sampleCursor") (.lit 1)).evalB B σ₁ =
        some (k + 1) := by
      have hvar : (Expr.var "sampleCursor").evalB B σ₁ = some k := by
        have hkB₁ : σ₁.vars "sampleCursor" < B := by rw [hcursor₁]; exact hkB
        simpa [hcursor₁] using evalB_var hkB₁
      have hone : (Expr.lit 1).evalB B σ₁ = some 1 := evalB_lit (by omega)
      have hadd : Bop.apply Bop.add k 1 < B := by
        change k + 1 < B
        omega
      have hbin := evalB_bin hvar hone hadd
      simpa [Bop.apply] using hbin
    have hcursorRun : Run B (inc "sampleCursor") σ₁ σ₂ 4 := by
      simpa [inc, σ₂] using Run.assign hcursorEval
    have hrun : Run B packBody σ σ₂ packBodyCost := by
      have hite : Run B
          (.ite packTest (Fill.put "ord" "sampleCount" (.var "sampleCursor")) .skip)
          σ σ₁ (1 + packTest.size + 7) :=
        Run.ite_true htestTrue hputRun
      have hseq := Run.seq hite hcursorRun
      simpa [packBody, packTest, packBodyCost, seqs, Nat.add_assoc] using hseq
    have hflags₂ : σ₂.arrs "sampleFlags" = arrOf n flags := by
      rw [hcursorRun.frame_arr "sampleFlags" (by decide)]
      exact (hputRun.frame_arr "sampleFlags" (by decide)).trans hflags
    have hn₂ : σ₂.vars "n" = n := by
      rw [hcursorRun.frame_var "n" (by decide)]
      exact (hputRun.frame_var "n" (by decide)).trans hn
    have hcount₂ : σ₂.vars "sampleCount" =
        (scanList flags 0 (σ₂.vars "sampleCursor")).length := by
      rw [show σ₂.vars "sampleCursor" = k + 1 by simp [σ₂, k]]
      rw [scanList_zero_add]
      rw [show σ₂.vars "sampleCount" = σ₁.vars "sampleCount" by simp [σ₂]]
      rw [hcount₁]
      rw [hcount]
      simp [hactive, k, σ₂]
    have hfill₂ : Fill.Below "ord" "sampleCount" n
        (fun i => (scanList flags 0 n).getD i 0) σ₂ := by
      apply hfill₁.of_eq
      · exact hcursorRun.frame_arr "ord" (by decide)
      · exact hcursorRun.frame_var "sampleCount" (by decide)
    refine ⟨σ₂, hrun, ⟨hflags₂, hn₂, ?_, hcount₂, hfill₂⟩, ?_⟩
    · simp [σ₂, k]
      omega
    · simp [σ₂, k]
  · have htestFalse : packTest.evalB B σ = some false := by
      have hflagzero : flags k = 0 := by have := hflags01 k (by simpa [k] using hcursor); omega
      simpa [hflagzero] using htestEval
    let σ₁ := σ.setVar "sampleCursor" (k + 1)
    have hcursorEval : (Expr.add (.var "sampleCursor") (.lit 1)).evalB B σ =
        some (k + 1) := by
      have hvar : (Expr.var "sampleCursor").evalB B σ = some k := by
        have hkB₀ : σ.vars "sampleCursor" < B := by simpa [k] using hkB
        simpa [k] using evalB_var hkB₀
      have hone : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by omega)
      have hadd : Bop.apply Bop.add k 1 < B := by
        change k + 1 < B
        omega
      have hbin := evalB_bin hvar hone hadd
      simpa [Bop.apply] using hbin
    have hcursorRun : Run B (inc "sampleCursor") σ σ₁ 4 := by
      simpa [inc, σ₁] using Run.assign hcursorEval
    have hrun : Run B packBody σ σ₁ packBodyCost := by
      have hite : Run B
          (.ite packTest (Fill.put "ord" "sampleCount" (.var "sampleCursor")) .skip)
          σ σ (1 + packTest.size + 1) :=
        Run.ite_false htestFalse Run.skip
      have hseq := Run.seq hite hcursorRun
      simpa [packBody, packTest, packBodyCost, seqs, Nat.add_assoc] using
        hseq.mono (by norm_num [packBodyCost, packTest, Cond.size, Expr.size])
    have hflags₁ : σ₁.arrs "sampleFlags" = arrOf n flags := by simp [σ₁, hflags]
    have hn₁ : σ₁.vars "n" = n := by simp [σ₁, hn]
    have hcount₁ : σ₁.vars "sampleCount" =
        (scanList flags 0 (σ₁.vars "sampleCursor")).length := by
      rw [show σ₁.vars "sampleCursor" = k + 1 by simp [σ₁]]
      rw [scanList_zero_add]
      rw [show σ₁.vars "sampleCount" = σ.vars "sampleCount" by simp [σ₁]]
      rw [hcount]
      simp [hactive, k]
    have hfill₁ : Fill.Below "ord" "sampleCount" n
        (fun i => (scanList flags 0 n).getD i 0) σ₁ := by
      exact hfill.of_eq (by simp [σ₁]) (by simp [σ₁])
    refine ⟨σ₁, hrun, ⟨hflags₁, hn₁, ?_, hcount₁, hfill₁⟩, ?_⟩
    · simp [σ₁, k]
      omega
    · simp [σ₁, k]

/-- The marked set represented by the supplied zero-one flag array. -/
def flaggedVertices (n : ℕ) (flags : ℕ → ℕ) : Finset ℕ :=
  activeVertices n flags

/-- This is exactly the prefix invariant expected by round partitioning. -/
abbrev SampleOrderIs (count : ℕ) (ord : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  PrefixEnumerates count ord S

/-- If the flags say exactly which in-range vertices occur in a draw list,
then the active set represented by the flags is exactly the list's set of
distinct draws. Repetitions in `draws` therefore have no effect. -/
lemma flaggedVertices_eq_draws {n : ℕ} {flags : ℕ → ℕ} {draws : List ℕ}
    (hrange : ∀ v ∈ draws, v < n)
    (hflags : ∀ v < n, flags v = 1 ↔ v ∈ draws) :
    flaggedVertices n flags = draws.toFinset := by
  ext v
  constructor
  · intro hv
    rcases (mem_activeVertices.mp hv) with ⟨hvn, hflag⟩
    exact List.mem_toFinset.mpr ((hflags v hvn).mp hflag)
  · intro hv
    have hvn : v < n := hrange v (List.mem_toFinset.mp hv)
    exact mem_activeVertices.mpr ⟨hvn, (hflags v hvn).mpr (List.mem_toFinset.mp hv)⟩

/-- The set generated by the source scan is the set of flagged in-range
vertices. -/
lemma scanList_toFinset (flags : ℕ → ℕ) (n : ℕ) :
    (scanList flags 0 n).toFinset = flaggedVertices n flags := by
  ext v
  rw [List.mem_toFinset, mem_scanList]
  simp [flaggedVertices, mem_activeVertices]

/-- A flag array describing the supplied draws gives an output set equal to
the draws after deduplication. -/
lemma scanList_toFinset_eq_draws {n : ℕ} {flags : ℕ → ℕ}
    {draws : List ℕ} (hrange : ∀ v ∈ draws, v < n)
    (hflags : ∀ v < n, flags v = 1 ↔ v ∈ draws) :
    (scanList flags 0 n).toFinset = draws.toFinset := by
  rw [scanList_toFinset, flaggedVertices_eq_draws hrange hflags]

/-- The ideal packed stack for the scan satisfies the partition contract. -/
lemma scanList_prefixEnumerates (n : ℕ) (flags : ℕ → ℕ) :
    PrefixEnumerates (scanList flags 0 n).length
      (fun i => (scanList flags 0 n).getD i 0) (flaggedVertices n flags) := by
  rw [← scanList_toFinset flags n]
  have h := PrefixEnumerates.of_list_prefix (by rfl)
      (by intro i hi; rfl) (scanList_nodup flags 0 n)
  simpa [List.take_length, List.getD_eq_getElem?_getD] using h

/-- The scan length is the cardinality of the flagged set. -/
lemma scanList_length_eq_card (n : ℕ) (flags : ℕ → ℕ) :
    (scanList flags 0 n).length = (flaggedVertices n flags).card := by
  rw [← List.toFinset_card_of_nodup (scanList_nodup flags 0 n)]
  rw [scanList_toFinset]

/-- Execute the actual IMP+ packing pass. The flags must already be a
zero-one array. The pass scans all `n` vertices, writes exactly the marked
ones to `ord` in increasing order, and consumes no input. Its cost is
`20 * n + 9` source steps. -/
lemma packMarkedSamples_run {B n : ℕ} {σ : Env} {flags ord : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hflags : σ.arrs "sampleFlags" = arrOf n flags)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hflags01 : ∀ v < n, flags v ≤ 1)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' : Env, ∃ packed : ℕ → ℕ,
      Run B packMarkedSamples σ σ' (20 * n + 9) ∧
      σ'.arrs "sampleFlags" = arrOf n flags ∧
      σ'.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ'.vars "sampleCount") packed (flaggedVertices n flags) ∧
      σ'.vars "sampleCount" = (flaggedVertices n flags).card ∧
      σ'.vars "sampleCursor" = n ∧
      (∀ a, a ≠ "ord" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "sampleCount" → v ≠ "sampleCursor" →
        σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hbody : Spec B (fun τ => PackInv n flags τ ∧ τ.vars "sampleCursor" < n)
      packBody
      (fun σ₁ σ₂ => PackInv n flags σ₂ ∧
        σ₂.vars "sampleCursor" = σ₁.vars "sampleCursor" + 1)
      packBodyCost := by
    intro τ ⟨hτ, hcur⟩
    obtain ⟨τ', hr, hτ', hcursor'⟩ :=
      packBody_run hτ hcur hflags01 hnB honeB
    exact ⟨τ', hr, hτ', hcursor'⟩
  have hloop := Spec.forRangeZero "sampleCursor" "n" (PackInv n flags)
      n packBodyCost hnB
      (fun _ h => h.2.2.1)
      (fun τ h => h.2.1)
      hbody
  let σ₁ := σ.setVar "sampleCount" 0
  have hcountRun : Run B (.assign "sampleCount" (.lit 0)) σ σ₁ 2 := by
    simpa [σ₁] using Run.assign (evalB_lit (by omega : 0 < B))
  have hstart : PackInv n flags (σ₁.setVar "sampleCursor" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₁, hflags]
    · simp [σ₁, hn]
    · simp
    · simp [σ₁, scanList]
    · have hOrd₁ : (σ₁.setVar "sampleCursor" 0).arrs "ord" = arrOf n ord := by
        simp [σ₁, hord]
      exact Fill.below_zero hOrd₁ (by simp [σ₁])
  obtain ⟨σ', hloopRun, hfinal, hcursor⟩ := hloop.run (σ := σ₁) hstart
  have hrunRaw := Run.seq hcountRun hloopRun
  have hrun : Run B packMarkedSamples σ σ' (20 * n + 9) := by
    simpa [packMarkedSamples, packBody, packBodyCost, packTest, seqs,
      Cond.size, Expr.size, Nat.add_assoc, Nat.mul_add] using
        hrunRaw.mono (by norm_num [packBodyCost, packTest, Cond.size, Expr.size]; omega)
  have hcountFinal : σ'.vars "sampleCount" = (scanList flags 0 n).length := by
    have h := hfinal.2.2.2.1
    rw [hcursor] at h
    exact h
  have hflagsFinal : σ'.arrs "sampleFlags" = arrOf n flags := by
    exact (hrun.frame_arr "sampleFlags" (by decide)).trans hflags
  have hordFinal : ∃ packed : ℕ → ℕ,
      σ'.arrs "ord" = arrOf n packed ∧
      (∀ i < σ'.vars "sampleCount", packed i = (scanList flags 0 n).getD i 0) := by
    rcases hfinal.2.2.2.2 with ⟨packed, hfill⟩
    rcases hfill with ⟨harr, hcount, hle, hcell⟩
    exact ⟨packed, harr, fun i hi => hcell i hi⟩
  obtain ⟨packed, hordPacked, hordCells⟩ := hordFinal
  have hcountBound : σ'.vars "sampleCount" ≤ n := by
    rw [hcountFinal]
    exact (scanList_length_le flags 0 n).trans (Nat.le_refl n)
  have hprefix : PrefixEnumerates (σ'.vars "sampleCount") packed
      (scanList flags 0 n).toFinset := by
    have hentry : ∀ i < σ'.vars "sampleCount",
        packed i = (scanList flags 0 n).getD i 0 := hordCells
    have h := PrefixEnumerates.of_list_prefix
      (height := σ'.vars "sampleCount") (entry := packed)
      (by rw [hcountFinal])
      (by
        intro i hi
        exact hentry i hi)
      (scanList_nodup flags 0 n)
    simpa [hcountFinal, List.take_length] using h
  have hprefix' : PrefixEnumerates (σ'.vars "sampleCount") packed
      (flaggedVertices n flags) := by
    rw [← scanList_toFinset]
    exact hprefix
  have hcard : σ'.vars "sampleCount" = (flaggedVertices n flags).card := by
    rw [hcountFinal, scanList_length_eq_card]
  have hframeVars : ∀ v, v ≠ "sampleCount" → v ≠ "sampleCursor" →
      σ'.vars v = σ.vars v := by
    intro v hv hc
    exact hrun.frame_var v (by
      simp [packMarkedSamples, packBody, seqs, Fill.put, inc, Com.wvars, hv, hc])
  have hframeArrs : ∀ a, a ≠ "ord" → σ'.arrs a = σ.arrs a := by
    intro a ha
    exact hrun.frame_arr a (by
      simp [packMarkedSamples, packBody, seqs, Fill.put, inc, Com.warrs, ha])
  have hinp := hrun.frame_inp (by simp [packMarkedSamples, packBody,
    packTest, seqs, Fill.put, inc, Com.reads])
  have hout := hrun.out_eq (by simp [packMarkedSamples, packBody,
    packTest, seqs, Fill.put, inc, Com.NoWrite])
  refine ⟨σ', packed, hrun, hflagsFinal, hordPacked, hprefix', hcard,
    hcursor, hframeArrs, hframeVars, hinp, hout⟩

/-- Execute the fixed runtime-array marking loop. The caller proves that the
array prefix contains `draws`; the code itself reads each entry dynamically.
It handles duplicates by idempotent stores and costs `12*draws.length+6`.
-/
lemma markDrawArray_run {B n drawCap : ℕ} {σ : Env} {draws : List ℕ}
    {values : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hdrawCount : σ.vars "drawCount" = draws.length)
    (hdraws : σ.arrs "sampleDraws" = arrOf drawCap values)
    {initialFlags : ℕ → ℕ}
    (hflags : σ.arrs "sampleFlags" = arrOf n initialFlags)
    (hcapacity : draws.length ≤ drawCap)
    (hvalues : ∀ i (hi : i < draws.length), values i = draws[i])
    (hrange : ∀ v ∈ draws, v < n)
    (hnB : n < B) (hdrawsB : draws.length < B) (honeB : 1 < B) :
    ∃ σ' flags', Run B markDrawArray σ σ' (12 * draws.length + 6) ∧
      σ'.arrs "sampleFlags" = arrOf n flags' ∧
      (∀ i < n, flags' i = if i ∈ draws then 1 else initialFlags i) ∧
      σ'.vars "drawCursor" = draws.length ∧
      (∀ a, a ≠ "sampleFlags" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "drawCursor" → σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let I := fun τ => ∃ flags, MarkDrawInv n draws.length drawCap draws values
      initialFlags flags τ
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "drawCursor" < draws.length)
      markDrawBody
      (fun σ₁ σ₂ => I σ₂ ∧ σ₂.vars "drawCursor" = σ₁.vars "drawCursor" + 1) 8 := by
    intro τ ⟨hIExists, hcursor⟩
    rcases hIExists with ⟨flags, hI⟩
    obtain ⟨τ', flags', hr, hI', hc⟩ := markDrawBody_run hI hcursor rfl
      hdrawsB hnB honeB hcapacity hrange
      (by intro i hi; exact hvalues i (by simpa using hi))
    exact ⟨τ', hr, ⟨flags', hI'⟩, hc⟩
  have hloop := Spec.forRangeZero "drawCursor" "drawCount" I draws.length 8
      hdrawsB
      (fun _ h => by rcases h with ⟨flags, hI⟩; exact hI.2.2.1)
      (fun τ h => by rcases h with ⟨flags, hI⟩; exact hI.2.1)
      hbody
  have hstart : I (σ.setVar "drawCursor" 0) := by
    refine ⟨initialFlags, hn, hdrawCount, by simp, ?_, ?_, ?_⟩
    · simpa using hdraws
    · simpa using hflags
    · intro i hi
      simp
  obtain ⟨σ', hloopRun, hfinal, hcursor⟩ := hloop.run (σ := σ) hstart
  have hrun : Run B markDrawArray σ σ' (12 * draws.length + 6) := by
    simpa [markDrawArray, markDrawBody, seqs] using hloopRun
  rcases hfinal with ⟨flags, hn', hcount', hcursorLe, hdraws', hflags', hseen⟩
  have hindicator : ∀ i < n, flags i = if i ∈ draws then 1 else initialFlags i := by
    intro i hi
    have hseen' := hseen i hi
    rw [hcursor] at hseen'
    simpa using hseen'
  have hframeArrs : ∀ a, a ≠ "sampleFlags" → σ'.arrs a = σ.arrs a := by
    intro a ha
    exact hrun.frame_arr a (by
      simp [markDrawArray, markDrawBody, seqs, inc, Com.warrs, ha])
  have hframeVars : ∀ v, v ≠ "drawCursor" → σ'.vars v = σ.vars v := by
    intro v hv
    exact hrun.frame_var v (by
      simp [markDrawArray, markDrawBody, seqs, inc, Com.wvars, hv])
  have hinp := hrun.frame_inp (by
    simp [markDrawArray, markDrawBody, seqs, inc, Com.reads])
  have hout := hrun.out_eq (by
    simp [markDrawArray, markDrawBody, seqs, inc, Com.NoWrite])
  refine ⟨σ', flags, hrun, hflags', hindicator, hcursor,
    hframeArrs, hframeVars, hinp, hout⟩

/-! The complete fixed source routine first marks the runtime array prefix,
then packs its distinct vertices. -/
def markAndPackSamples : Com := seqs [markDrawArray, packMarkedSamples]

/-- Full source execution from a runtime draw-array prefix. The array may have
capacity greater than the count; only its first `draws.length` values are
read. The source is fixed independently of sampled values. The exact source
cost is `20*n + 12*draws.length + 15`. -/
lemma markAndPackSamples_run {B n drawCap : ℕ} {σ : Env} {ord : ℕ → ℕ}
    {draws : List ℕ} {values : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hdrawCount : σ.vars "drawCount" = draws.length)
    (hdraws : σ.arrs "sampleDraws" = arrOf drawCap values)
    (hflags : σ.arrs "sampleFlags" = arrOf n (fun _ => 0))
    (hord : σ.arrs "ord" = arrOf n ord)
    (hcapacity : draws.length ≤ drawCap)
    (hvalues : ∀ i (hi : i < draws.length), values i = draws[i])
    (hrange : ∀ v ∈ draws, v < n)
    (hnB : n < B) (hdrawsB : draws.length < B) (honeB : 1 < B) :
    ∃ σ' : Env,
      Run B markAndPackSamples σ σ'
        (20 * n + 12 * draws.length + 15) ∧
      σ'.arrs "sampleFlags" = arrOf n (fun i => if i ∈ draws then 1 else 0) ∧
      ∃ order : ℕ → ℕ, σ'.arrs "ord" = arrOf n order ∧
        PrefixEnumerates (σ'.vars "sampleCount") order draws.toFinset ∧
        σ'.vars "sampleCount" = draws.toFinset.card ∧
        σ'.vars "sampleCount" ≤ n ∧ σ'.vars "sampleCursor" = n ∧
        σ'.vars "drawCursor" = draws.length ∧
        (∀ a, a ≠ "sampleFlags" → a ≠ "ord" →
          σ'.arrs a = σ.arrs a) ∧
        (∀ v, v ≠ "sampleCount" → v ≠ "sampleCursor" →
          v ≠ "drawCursor" →
          σ'.vars v = σ.vars v) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σm, flags, hmark, hflagsm, hmarkValues, hdrawCursor,
      -, -, hinpm, houtm⟩ :=
    markDrawArray_run hn hdrawCount hdraws hflags hcapacity hvalues hrange
      hnB hdrawsB honeB
  have hnm : σm.vars "n" = n := by
    rw [hmark.frame_var "n" (by simp [markDrawArray, markDrawBody,
      seqs, inc, Com.wvars])]
    exact hn
  have hordm : σm.arrs "ord" = arrOf n ord := by
    rw [hmark.frame_arr "ord" (by simp [markDrawArray, markDrawBody,
      seqs, inc, Com.warrs])]
    exact hord
  have hflagsIndicator : ∀ i < n, flags i = if i ∈ draws then 1 else 0 := hmarkValues
  have hflags01m : ∀ i < n, flags i ≤ 1 := by
    intro i hi
    rw [hflagsIndicator i hi]
    split_ifs <;> omega
  have hflagsMem : ∀ i < n, flags i = 1 ↔ i ∈ draws := by
    intro i hi
    rw [hflagsIndicator i hi]
    split_ifs <;> simp_all
  obtain ⟨σf, packed, hpack, hflagsf, hordf, hprefix, hcount, hcursor,
      -, -, hinpf, houtf⟩ :=
    packMarkedSamples_run hnm hflagsm hordm hflags01m hnB honeB
  have hrunRaw := Run.seq hmark hpack
  have hrun : Run B markAndPackSamples σ σf
      (20 * n + 12 * draws.length + 15) := by
    change Run B (markDrawArray.seq packMarkedSamples) σ σf
      (20 * n + 12 * draws.length + 15)
    convert hrunRaw using 1 <;> omega
  have hprefixDraws : PrefixEnumerates (σf.vars "sampleCount") packed
      draws.toFinset := by
    rw [flaggedVertices_eq_draws hrange hflagsMem] at hprefix
    exact hprefix
  have hcountDraws : σf.vars "sampleCount" = draws.toFinset.card := by
    rw [hcount, flaggedVertices_eq_draws hrange hflagsMem]
  have hcountBound : σf.vars "sampleCount" ≤ n := by
    rw [hcountDraws]
    calc
      draws.toFinset.card ≤ (Finset.range n).card := Finset.card_le_card (by
        intro v hv
        exact Finset.mem_range.mpr (hrange v (List.mem_toFinset.mp hv)))
      _ = n := Finset.card_range n
  have hframes : ∀ a, a ≠ "sampleFlags" → a ≠ "ord" →
      σf.arrs a = σ.arrs a := by
    intro a hflag hordne
    exact hrun.frame_arr a (by
      simp [markAndPackSamples, markDrawArray, markDrawBody, packMarkedSamples,
        packBody, seqs, Fill.put, inc, Com.warrs, hflag, hordne])
  have hframeVars : ∀ v, v ≠ "sampleCount" → v ≠ "sampleCursor" →
      v ≠ "drawCursor" → σf.vars v = σ.vars v := by
    intro v hcount' hcursor' hdraw'
    exact hrun.frame_var v (by
      simp [markAndPackSamples, markDrawArray, markDrawBody, packMarkedSamples,
        packBody, seqs, Fill.put, inc, Com.wvars, hcount', hcursor', hdraw'])
  have hinp := hrun.frame_inp (by
    simp [markAndPackSamples, markDrawArray, markDrawBody, packMarkedSamples,
      packBody, seqs, Fill.put, inc, Com.reads])
  have hout := hrun.out_eq (by
    simp [markAndPackSamples, markDrawArray, markDrawBody, packMarkedSamples,
      packBody, seqs, Fill.put, inc, Com.NoWrite])
  have hflagsExact : σf.arrs "sampleFlags" =
      arrOf n (fun i => if i ∈ draws then 1 else 0) := by
    rw [hflagsf]
    exact arrOf_congr hmarkValues
  have hdrawCursorFinal : σf.vars "drawCursor" = draws.length := by
    rw [hpack.frame_var "drawCursor" (by simp [packMarkedSamples, packBody,
      seqs, Fill.put, inc, Com.wvars])]
    exact hdrawCursor
  refine ⟨σf, hrun, hflagsExact, packed, hordf, hprefixDraws,
    hcountDraws, hcountBound, hcursor, hdrawCursorFinal, hframes,
    hframeVars, hinp, hout⟩

end Lax457868Proofs.SamplePacking
