import Lax235315Proofs.Construction.TapeBlocks
import Lax235315Proofs.Construction.RoundInvariant
import Lax235315Proofs.Construction.PartitionSource
import Mathlib.Tactic

/-! Sampling on a persistent successful reduction frontier. -/

namespace Lax235315Proofs.Construction.SamplingFrontier

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.BitArrays
open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.SamplingPrefixSource
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.TapeBlocks
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlSetup

private lemma sampling_workspace_preserved {B c n : ℕ} {x : List ℕ}
    {σ σ' : Env} {C : ℕ} (h : Workspace B c n x σ)
    (hr : Run B samplingPrefix σ σ' C) : Workspace B c n x σ' := by
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

private lemma sampling_frontier_preserved {B c n : ℕ} {x : List ℕ}
    {σ σ' : Env} {C : ℕ} (h : Frontier B c n x σ)
    (hr : Run B samplingPrefix σ σ' C) : Frontier B c n x σ' := by
  have hactiveA : σ'.arrs "activeA" = σ.arrs "activeA" :=
    hr.frame_arr "activeA" (by decide)
  have hactiveB : σ'.arrs "activeB" = σ.arrs "activeB" :=
    hr.frame_arr "activeB" (by decide)
  have hactiveSetA : activeVertices n (view σ' "activeA") =
      activeVertices n (view σ "activeA") := by
    have hv : view σ' "activeA" = view σ "activeA" := by
      funext i
      simp [view, hactiveA]
    rw [hv]
  have hactiveSetB : activeVertices n (view σ' "activeB") =
      activeVertices n (view σ "activeB") := by
    have hv : view σ' "activeB" = view σ "activeB" := by
      funext i
      simp [view, hactiveB]
    rw [hv]
  have hacount : σ'.vars "acount" = (activeVertices n (view σ' "activeA")).card := by
    rw [(hr.frame_var "acount" (by decide)), hactiveSetA]
    exact h.activeCount
  refine ⟨sampling_workspace_preserved h.workspace hr,
    (hr.frame_var "good" (by decide)).trans h.success,
    hacount,
    ?_, ?_, BitArrays.run_preserves hr (by decide) h.activeABits,
    BitArrays.run_preserves hr (by decide) h.activeBBits,
      BitArrays.run_preserves hr (by decide) h.nextABits,
    BitArrays.run_preserves hr (by decide) h.nextBBits, ?_, ?_⟩
  · intro hn
    rw [hactiveSetA]
    exact h.nonemptyA hn
  · intro hn
    rw [hactiveSetB]
    exact h.nonemptyB hn
  · rw [(hr.frame_var "removedCount" (by decide)),
      (hr.frame_var "acount" (by decide))]
    exact h.conservation
  · rw [(hr.frame_var "round" (by decide)),
      (hr.frame_var "acount" (by decide))]
    exact h.shrinking

/-- The random sampling prefix can be run directly from any valid frontier.
The only tape condition is enough unread bits; sample size is bounded by the
frontier's actual active count. The result includes its canonical sampled set. -/
lemma run
    {B c n sampleCount : ℕ} {x : List ℕ} {σ : Env}
    (h : Frontier B c n x σ)
    (htape : 8 * Nat.clog 2 n * σ.vars "acount" ≤ σ.inp.length)
    (hqB : 2 ^ Nat.clog 2 n < B) (hnB : n < B) (htwoB : 2 < B)
    (hsample : sampleCount ≤ σ.vars "acount") :
    ∃ bits : ℕ → Fin 8 → List ℕ,
    let vertices := scanList (view σ "activeA") 0 n
    let digits := filledKey (fun d => view σ (keyName d)) (view σ "activeA") bits n
    let sorted := radixSort8 (2 ^ Nat.clog 2 n) digits vertices
    ∃ σ' : Env, ∃ ord' : ℕ → ℕ,
      Run B samplingPrefix σ σ'
        ((120 * n + 120 * Nat.clog 2 n * σ.vars "acount" + 8) +
          512 * (σ.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
          300 * (σ.vars "acount" + 1)) ∧
      ((120 * n + 120 * Nat.clog 2 n * σ.vars "acount" + 8) +
          512 * (σ.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
          300 * (σ.vars "acount" + 1)) ≤
        2200 * (n + 1) + 120 * Nat.clog 2 n * σ.vars "acount" ∧
      Frontier B c n x σ' ∧
      σ'.inp = σ.inp.drop (8 * Nat.clog 2 n * σ.vars "acount") ∧
      σ'.arrs "ord" = arrOf n ord' ∧
      PrefixEnumerates sampleCount ord' (sorted.take sampleCount).toFinset ∧
      (∀ v ∈ (sorted.take sampleCount).toFinset, v < n) ∧
      (sorted.take sampleCount).toFinset ⊆ activeVertices n (view σ "activeA") ∧
      (sorted.take sampleCount).toFinset.card = sampleCount := by
  let L := Nat.clog 2 n
  let q := 2 ^ L
  let active := view σ "activeA"
  let original : Fin 8 → ℕ → ℕ := fun d => view σ (keyName d)
  let vertices := scanList active 0 n
  have hL : σ.vars "L" = L := by simpa [L] using h.workspace.logarithm
  have hqpow : σ.vars "qpow" = q := by
    simpa [q, L] using h.workspace.radixSize
  have hq : q = 2 ^ L := rfl
  have hcountArray : σ.arrs "count" = arrOf q (view σ "count") := by
    apply array_shape
    rw [h.workspace.lengths]
    simp [welzlExt, q, L]
  have hactiveArray : σ.arrs "activeA" = arrOf n active :=
    h.workspace.vertex_array (by decide) (by decide) (by decide)
  have hordArray : σ.arrs "ord" = arrOf n (view σ "ord") :=
    h.workspace.vertex_array (by decide) (by decide) (by decide)
  have hkeysArray : ∀ d, σ.arrs (keyName d) = arrOf n (original d) := by
    intro d
    exact h.workspace.vertex_array (by fin_cases d <;> decide)
      (by fin_cases d <;> decide) (by fin_cases d <;> decide)
  have hactiveB : ∀ v < n, active v < B := by
    intro v hv
    exact h.workspace.value_bound (by rw [hactiveArray, length_arrOf]; exact hv)
  have horiginalB : ∀ d i, i < n → original d i < B := by
    intro d i hi
    exact h.workspace.value_bound (by rw [hkeysArray d, length_arrOf]; exact hi)
  have hverticesLength : vertices.length = σ.vars "acount" := by
    rw [scanList_length_eq_activeVertices_card, h.activeCount]
  have hsampleVertices : sampleCount ≤ vertices.length := by
    rw [hverticesLength]
    exact hsample
  have htape' : 8 * L * vertices.length ≤ σ.inp.length := by
    simpa [L, hverticesLength] using htape
  have hsource : ∀ b ∈ σ.inp, b ≤ 1 := h.workspace.randomInput
  let rest := σ.inp.drop (8 * L * vertices.length)
  obtain ⟨bits, hbitsLen, hbitsBinary, hinputPrefix⟩ :=
    exists_scanTapeBits hsource htape'
  have hinp : σ.inp = keyTape bits vertices ++ rest := by
    calc
      σ.inp = keyTape bits vertices ++ σ.inp.drop (8 * L * vertices.length) := hinputPrefix
      _ = keyTape bits vertices ++ rest := by rfl
  obtain ⟨σ', ord, hrun, halen, hcollision, hord, hordval, hprefix, hinp'⟩ :=
    SamplingPrefixSource.samplingPrefix_run
      (hn := h.workspace.vertices) (hL := hL) (hqpow := hqpow) (hq := hq)
      (hactive := hactiveArray) (hord := hordArray) (hkeys := hkeysArray)
      (hcount := hcountArray) (hscratch :=
        h.workspace.vertex_array (by decide) (by decide) (by decide))
      (hinp := hinp) (hlen := hbitsLen) (hbits := hbitsBinary)
      (hactiveB := hactiveB) (horiginalB := horiginalB)
      (hsample := hsampleVertices) (hqB := hqB) (hnB := hnB) (htwoB := htwoB)
  let digits := filledKey original active bits n
  let sorted := radixSort8 q digits vertices
  have hverticesNodup : vertices.Nodup := scanList_nodup active 0 n
  have hverticesRange : ∀ v ∈ vertices, v < n := by
    intro v hv
    simpa using scanList_mem_range hv
  have hdigitQ : ∀ d v, v ∈ vertices → digits d v < q := by
    intro d v hv
    have hvn := hverticesRange v hv
    have hav := (mem_scanList.mp hv).2.2
    change (if v < n ∧ active v = 1 then bitsValue (bits v d)
      else original d v) < q
    rw [if_pos ⟨hvn, hav⟩]
    have hvalue := bitsValue_lt_pow (bits v d) (hbitsBinary v hvn d)
    rw [hbitsLen v hvn d] at hvalue
    simpa [q] using hvalue
  have hperm : List.Perm sorted vertices :=
    radixSort8_perm hverticesNodup hdigitQ
  have hsortedNodup : sorted.Nodup := hperm.symm.nodup hverticesNodup
  have hsortedLength : sorted.length = vertices.length := hperm.length_eq
  have hsortedRange : ∀ v ∈ sorted, v < n := by
    intro v hv
    exact hverticesRange v (hperm.subset hv)
  have hsampleSorted : sampleCount ≤ sorted.length := by
    rw [hsortedLength]
    exact hsampleVertices
  have hsampleNodup : (sorted.take sampleCount).Nodup := hsortedNodup.take
  have hsampleRange : ∀ v ∈ (sorted.take sampleCount).toFinset, v < n := by
    intro v hv
    exact hsortedRange v (List.mem_of_mem_take (List.mem_toFinset.mp hv))
  have hsampleSubset : (sorted.take sampleCount).toFinset ⊆
      activeVertices n active := by
    intro v hv
    apply mem_activeVertices.mpr
    have hvSorted : v ∈ sorted :=
      List.mem_of_mem_take (List.mem_toFinset.mp hv)
    exact ⟨hverticesRange v (hperm.subset hvSorted),
      (mem_scanList.mp (hperm.subset hvSorted)).2.2⟩
  have hsampleCard : (sorted.take sampleCount).toFinset.card = sampleCount := by
    rw [List.toFinset_card_of_nodup hsampleNodup]
    simp [List.length_take, Nat.min_eq_left hsampleSorted]
  have hcostEq :
      120 * n + 120 * L * vertices.length + 8 +
        512 * (vertices.length + q + 1) + 300 * (sorted.length + 1) =
      (120 * n + 120 * L * σ.vars "acount" + 8) +
        512 * (σ.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
        300 * (σ.vars "acount" + 1) := by
    simp [L, q, hverticesLength, hsortedLength]
  rw [hcostEq] at hrun
  have hacountLe : σ.vars "acount" ≤ n := by
    have hc := h.conservation
    omega
  have hcoarse :
      ((120 * n + 120 * Nat.clog 2 n * σ.vars "acount" + 8) +
          512 * (σ.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
          300 * (σ.vars "acount" + 1)) ≤
        2200 * (n + 1) + 120 * Nat.clog 2 n * σ.vars "acount" := by
    have hradix := (Lax235315Proofs.Construction.DriverSetup.radix_size_lt n).le
    nlinarith [hacountLe, hradix]
  refine ⟨bits, ?_⟩
  dsimp only
  refine ⟨σ', ord, hrun, hcoarse, sampling_frontier_preserved h hrun, ?_, hord, hprefix, ?_, ?_, ?_⟩
  · simpa [rest, L, hverticesLength] using hinp'
  · simpa [sorted] using hsampleRange
  · simpa [sorted] using hsampleSubset
  · simpa [sorted] using hsampleCard
