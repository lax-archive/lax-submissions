import Lax235315Proofs.Construction.CollisionDetection
import Lax235315Proofs.Construction.MarkingMath
import Lax235315Proofs.Construction.RadixEight
import Lax235315Proofs.Construction.ReadKeys
import Mathlib.Tactic

/-! Source-level composition of random-key reading, sorting, and collision
detection. -/

namespace Lax235315Proofs.Construction.SamplingPrefixSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.WelzlProgram

/-- The random-key prefix of one reduction round. -/
def samplingPrefix : Com :=
  seqs [readKeys, seqs ((keyNames.reverse).map radixPass), detectCollision]

theorem SortState.prefixEnumerates
    {n q sampleCount : ℕ} {digits : Fin 8 → ℕ → ℕ}
    {xs : List ℕ} {σ : Env}
    (hstate : SortState n q digits xs σ)
    (hsample : sampleCount ≤ xs.length) (hxs : xs.Nodup) :
    ∃ ord : ℕ → ℕ,
      σ.arrs "ord" = arrOf n ord ∧
      PrefixEnumerates sampleCount ord (xs.take sampleCount).toFinset := by
  rcases hstate.2.2.1 with ⟨ord, hord, hordval⟩
  exact ⟨ord, hord,
    PrefixEnumerates.of_list_prefix hsample
      (fun i hi => hordval i (hi.trans_le hsample)) hxs⟩

/-- Reading and sorting the active vertices leaves every sampled prefix as an
exact duplicate-free enumeration and reports whether two adjacent sorted keys
collide. -/
theorem samplingPrefix_run
    {B n L q sampleCount : ℕ} {σ : Env}
    {active ord count scratch : ℕ → ℕ}
    {original : Fin 8 → ℕ → ℕ} {bits : ℕ → Fin 8 → List ℕ}
    {rest : List ℕ}
    (hn : σ.vars "n" = n) (hL : σ.vars "L" = L)
    (hqpow : σ.vars "qpow" = q) (hq : q = 2 ^ L)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hkeys : ∀ d, σ.arrs (keyName d) = arrOf n (original d))
    (hcount : σ.arrs "count" = arrOf q count)
    (hscratch : σ.arrs "scratchOrder" = arrOf n scratch)
    (hinp : σ.inp = keyTape bits (scanList active 0 n) ++ rest)
    (hlen : ∀ v < n, ∀ d, (bits v d).length = L)
    (hbits : ∀ v < n, ∀ d x, x ∈ bits v d → x ≤ 1)
    (hactiveB : ∀ v < n, active v < B)
    (horiginalB : ∀ d i, i < n → original d i < B)
    (hsample : sampleCount ≤ (scanList active 0 n).length)
    (hqB : q < B) (hnB : n < B) (htwoB : 2 < B) :
    let vertices := scanList active 0 n
    let digits := filledKey original active bits n
    let sorted := radixSort8 q digits vertices
    ∃ σ' ord',
      Run B samplingPrefix σ σ'
        (((120 * L + 120) * n + 8) +
          512 * (vertices.length + q + 1) +
          300 * (sorted.length + 1)) ∧
      σ'.vars "alen" = sorted.length ∧
      σ'.vars "collision" =
        (if HasAdjacentEqualDigits digits sorted then 1 else 0) ∧
      σ'.arrs "ord" = arrOf n ord' ∧
      (∀ i < sorted.length, ord' i = sorted.getD i 0) ∧
      PrefixEnumerates sampleCount ord'
        (sorted.take sampleCount).toFinset ∧
      σ'.inp = rest := by
  dsimp only
  let vertices := scanList active 0 n
  let digits := filledKey original active bits n
  let sorted := radixSort8 q digits vertices
  obtain ⟨σ₁, ord₁, rread, halen₁, -, hn₁, hL₁, hord₁, hordval₁,
      hkeys₁, hinp₁⟩ :=
    readKeys_run hn hL hactive hord hkeys hinp hlen hbits hactiveB
      (by simpa [hq] using hqB) hnB htwoB
  have hqpow₁ : σ₁.vars "qpow" = q := by
    rw [rread.frame_var "qpow" (by decide), hqpow]
  have hcount₁ : σ₁.arrs "count" = arrOf q count := by
    rw [rread.frame_arr "count" (by decide), hcount]
  have hscratch₁ : σ₁.arrs "scratchOrder" = arrOf n scratch := by
    rw [rread.frame_arr "scratchOrder" (by decide), hscratch]
  have hstate₁ : SortState n q digits vertices σ₁ := by
    refine ⟨halen₁, hqpow₁, ⟨ord₁, hord₁, hordval₁⟩, ?_,
      ⟨count, hcount₁⟩, scratch, hscratch₁⟩
    exact hkeys₁
  have hverticesN : vertices.length ≤ n := by
    exact scanList_length_le active 0 n
  have hverticesNodup : vertices.Nodup := scanList_nodup active 0 n
  have hverticesRange : ∀ v ∈ vertices, v < n := by
    intro v hv
    simpa [vertices] using scanList_mem_range hv
  have hdigitQ : ∀ d v, v ∈ vertices → digits d v < q := by
    intro d v hv
    have hvn : v < n := hverticesRange v hv
    have hav : active v = 1 := (mem_scanList.mp hv).2.2
    have hcond : v < n ∧ active v = 1 := ⟨hvn, hav⟩
    change (if v < n ∧ active v = 1 then bitsValue (bits v d)
      else original d v) < q
    rw [if_pos hcond]
    rw [hq, ← hlen v hvn d]
    exact bitsValue_lt_pow _ (hbits v hvn d)
  obtain ⟨σ₂, rsort, hstate₂⟩ := radixEight_run hstate₁ hverticesN
    hnB hqB hverticesNodup hverticesRange hdigitQ
  have hperm : List.Perm sorted vertices := by
    exact radixSort8_perm hverticesNodup hdigitQ
  have hsortedNodup : sorted.Nodup := hperm.symm.nodup hverticesNodup
  have hsortedRange : ∀ v ∈ sorted, v < n := by
    intro v hv
    exact hverticesRange v (hperm.subset hv)
  have hsortedLength : sorted.length = vertices.length := hperm.length_eq
  rcases hstate₂.2.2.1 with ⟨ord₂, hord₂, hordval₂⟩
  have hvalueB : ∀ d, ∀ i < n, digits d i < B := by
    intro d i hi
    by_cases ha : active i = 1
    · exact (hdigitQ d i
        ((mem_scanList).2 ⟨by omega, by omega, ha⟩)).trans hqB
    · have hcond : ¬(i < n ∧ active i = 1) := by simp [ha]
      change (if i < n ∧ active i = 1 then bitsValue (bits i d)
        else original d i) < B
      rw [if_neg hcond]
      exact horiginalB d i hi
  obtain ⟨σ₃, rdetect, hcollision₃⟩ :=
    detectCollision_digits_run hstate₂.1 hord₂ hordval₂ hstate₂.2.2.2.1
      hvalueB hsortedRange (by rw [hsortedLength]; exact hverticesN)
      hnB (by omega)
  have halen₃ : σ₃.vars "alen" = sorted.length := by
    rw [rdetect.frame_var "alen" (by decide), hstate₂.1]
  have hord₃ : σ₃.arrs "ord" = arrOf n ord₂ := by
    rw [rdetect.frame_arr "ord" (by decide), hord₂]
  have hprefix₂ : PrefixEnumerates sampleCount ord₂
      (sorted.take sampleCount).toFinset := by
    have hs : sampleCount ≤ sorted.length := by
      rw [hsortedLength]
      simpa [vertices] using hsample
    exact PrefixEnumerates.of_list_prefix (xs := sorted) hs
      (fun i hi => hordval₂ i (hi.trans_le hs)) hsortedNodup
  refine ⟨σ₃, ord₂, ?_, halen₃, hcollision₃, hord₃, hordval₂,
    hprefix₂, ?_⟩
  · have rr := rread.seq (rsort.seq rdetect)
    change Run B
      (.seq readKeys
        (.seq (seqs ((keyNames.reverse).map radixPass)) detectCollision))
      σ σ₃ _
    simpa only [Nat.add_assoc, sorted] using rr
  · rw [rdetect.frame_inp (by decide), rsort.frame_inp (by decide), hinp₁]

end Lax235315Proofs.Construction.SamplingPrefixSource
