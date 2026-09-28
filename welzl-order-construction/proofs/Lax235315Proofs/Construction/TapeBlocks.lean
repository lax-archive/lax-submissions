import Lax235315Proofs.Construction.SamplingPrefixSource
import Mathlib.Tactic

/-! Exact decomposition of a binary source tape into fixed-width random-key
blocks. -/

namespace Lax235315Proofs.Construction.TapeBlocks

open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.ReadKeys
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.SamplingPrefixSource
open Lax235315Proofs.Construction.WelzlProgram

/-- The digit block at position `d` inside a fixed-width key block. -/
def digitBlock (source : List ℕ) (L : ℕ) (d : Fin 8) : List ℕ :=
  (source.drop (d.val * L)).take L

private lemma take_group (source : List ℕ) (L k : ℕ) :
    source.take (k * L) ++ (source.drop (k * L)).take L =
      source.take ((k + 1) * L) := by
  rw [← List.take_add]
  congr 1
  simp [Nat.succ_mul]

lemma joined8_digitBlock (source : List ℕ) (L : ℕ)
    (hlen : source.length = 8 * L) :
    joined8 (digitBlock source L) = source := by
  unfold joined8 digitBlock
  have h01 : source.take L ++ (source.drop L).take L = source.take (2 * L) := by
    simpa using take_group source L 1
  have h02 : source.take (2 * L) ++ (source.drop (2 * L)).take L = source.take (3 * L) := by
    simpa using take_group source L 2
  have h03 : source.take (3 * L) ++ (source.drop (3 * L)).take L = source.take (4 * L) := by
    simpa using take_group source L 3
  have h04 : source.take (4 * L) ++ (source.drop (4 * L)).take L = source.take (5 * L) := by
    simpa using take_group source L 4
  have h05 : source.take (5 * L) ++ (source.drop (5 * L)).take L = source.take (6 * L) := by
    simpa using take_group source L 5
  have h06 : source.take (6 * L) ++ (source.drop (6 * L)).take L = source.take (7 * L) := by
    simpa using take_group source L 6
  have h07 : source.take (7 * L) ++ (source.drop (7 * L)).take L = source.take (8 * L) := by
    simpa using take_group source L 7
  have h8 : source.take (8 * L) = source := by
    exact List.take_of_length_le (by omega)
  norm_num
  rw [← List.append_assoc, h01]
  rw [← List.append_assoc, h02]
  rw [← List.append_assoc, h03]
  rw [← List.append_assoc, h04]
  rw [← List.append_assoc, h05]
  rw [← List.append_assoc, h06]
  rw [h07]
  exact h8

lemma joined8_digitBlock_take (source : List ℕ) (L : ℕ)
    (hlen : 8 * L ≤ source.length) :
    joined8 (digitBlock source L) = source.take (8 * L) := by
  let p := source.take (8 * L)
  have hp : p.length = 8 * L := by simp [p, Nat.min_eq_left hlen]
  have hd : ∀ d : Fin 8, digitBlock p L d = digitBlock source L d := by
    intro d
    unfold digitBlock
    have hoff : d.val * L + L ≤ 8 * L := by nlinarith [d.isLt]
    simp [p, List.drop_take, List.take_take]
    omega
  have hfun : digitBlock p L = digitBlock source L := funext hd
  rw [← hfun, joined8_digitBlock p L hp]

/-- Choose the block at the number of active vertices preceding `v`. -/
def scanTapeBits (active : ℕ → ℕ) (L : ℕ) (source : List ℕ)
    (v : ℕ) : Fin 8 → List ℕ :=
  if active v = 1 then
    digitBlock (source.drop (8 * L * (scanList active 0 v).length)) L
  else fun _ => List.replicate L 0

lemma keyTape_scan_prefix (active : ℕ → ℕ) (L n : ℕ) (source : List ℕ)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length) :
    keyTape (scanTapeBits active L source) (scanList active 0 n) =
      source.take (8 * L * (scanList active 0 n).length) := by
  induction n with
  | zero => simp [scanList, keyTape]
  | succ n ih =>
      have hscan := scanList_zero_add active n
      by_cases ha : active n = 1
      · rw [hscan, if_pos ha]
        let xs := scanList active 0 n
        have hlenN : 8 * L * ((scanList active 0 n).length + 1) ≤ source.length := by
          simpa [hscan, ha, List.length_append, Nat.mul_add] using hlen
        have hlen' : 8 * L * xs.length ≤ source.length := by
          apply le_trans (Nat.mul_le_mul_left (8 * L) (Nat.le_add_right _ _))
          simpa [xs] using hlenN
        have hprefix := ih (by simpa [xs] using hlen')
        have htail : (scanTapeBits active L source) n =
            digitBlock (source.drop (8 * L * xs.length)) L := by
          simp [scanTapeBits, ha, xs]
        rw [keyTape_append, hprefix]
        simp only [keyTape_cons, keyTape_nil]
        rw [show scanTapeBits active L source n =
          digitBlock (source.drop (8 * L * xs.length)) L by simpa [xs] using htail]
        rw [joined8_digitBlock_take]
        · simp only [List.append_nil]
          rw [← List.take_add]
          congr 1
          simp [Nat.mul_add, Nat.add_comm]
        · have hlenTail : 8 * L ≤ (source.drop (8 * L * xs.length)).length := by
            rw [List.length_drop]
            have hsum : 8 * L * xs.length + 8 * L ≤ source.length := by
              simpa [xs, Nat.mul_add, Nat.add_mul, Nat.add_comm] using hlenN
            omega
          exact hlenTail
      · rw [hscan, if_neg ha]
        have hlenN : 8 * L * (scanList active 0 n).length ≤ source.length := by
          simpa [hscan, ha, List.length_append] using hlen
        simpa [List.length_append] using ih hlenN


private lemma scanList_prefix_length_le (active : ℕ → ℕ) {v n : ℕ}
    (hv : v < n) (hav : active v = 1) :
    (scanList active 0 v).length + 1 ≤ (scanList active 0 n).length := by
  have hpre : scanList active 0 (v + 1) = scanList active 0 v ++ [v] := by
    rw [scanList_zero_add, if_pos hav]
  have hdecomp : scanList active 0 n =
      scanList active 0 (v + 1) ++ scanList active (v + 1) (n - (v + 1)) := by
    have heq : n = (v + 1) + (n - (v + 1)) := by omega
    rw [heq, scanList_add]
    simp
  rw [hdecomp, List.length_append, hpre, List.length_append]
  simp

/-- Every binary source tape has a canonical fixed-width encoding for the
active scan, consuming exactly its eight digits per scanned vertex. -/
lemma exists_scanTapeBits {active : ℕ → ℕ} {n L : ℕ} {source : List ℕ}
    (hsource : ∀ x ∈ source, x ≤ 1)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length) :
    ∃ bits : ℕ → Fin 8 → List ℕ,
      bits = scanTapeBits active L source ∧
      (∀ v < n, ∀ d, (bits v d).length = L) ∧
      (∀ v < n, ∀ d x, x ∈ bits v d → x ≤ 1) ∧
      source = keyTape bits (scanList active 0 n) ++
        source.drop (8 * L * (scanList active 0 n).length) := by
  let bits := scanTapeBits active L source
  refine ⟨bits, rfl, ?_, ?_, ?_⟩
  · intro v hv d
    by_cases ha : active v = 1
    · have hrank := scanList_prefix_length_le active hv ha
      have hblock : 8 * L * (scanList active 0 v).length + 8 * L ≤
          8 * L * (scanList active 0 n).length := by
        simpa [Nat.mul_add, Nat.add_comm] using
          (Nat.mul_le_mul_left (8 * L) hrank)
      have hsourceDrop : 8 * L ≤
          (source.drop (8 * L * (scanList active 0 v).length)).length := by
        rw [List.length_drop]
        have htotal : 8 * L * (scanList active 0 v).length + 8 * L ≤ source.length :=
          hblock.trans hlen
        omega
      have hoff : 8 * L * (scanList active 0 v).length + (d.val * L + L) ≤ source.length := by
        have hd : d.val * L + L ≤ 8 * L := by nlinarith [d.isLt]
        exact (Nat.add_le_add_left hd _).trans (hblock.trans hlen)
      simp only [bits, scanTapeBits, if_pos ha]
      change (digitBlock (source.drop (8 * L * (scanList active 0 v).length)) L d).length = L
      unfold digitBlock
      simp only [List.length_take, List.length_drop]
      apply Nat.min_eq_left
      omega
    · simp [bits, scanTapeBits, ha]
  · intro v hv d x hx
    by_cases ha : active v = 1
    · have hx' : x ∈ source := by
        simp only [bits, scanTapeBits, if_pos ha] at hx
        change x ∈ (((source.drop (8 * L * (scanList active 0 v).length)).drop (d.val * L)).take L) at hx
        exact List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      exact hsource x hx'
    · simp [bits, scanTapeBits, ha] at hx
      rcases hx with ⟨_, rfl⟩
      exact Nat.zero_le _
  · rw [keyTape_scan_prefix active L n source hlen]
    exact (List.take_append_drop (8 * L * (scanList active 0 n).length) source).symm

/-- Run the sampling prefix directly on a sufficiently long binary tape,
choosing its fixed-width key blocks canonically and preserving the exact
unconsumed suffix. -/
lemma samplingPrefix_run_source
    {B n L q sampleCount : ℕ} {σ : Lax808846Proofs.Imp.Env}
    {active ord count scratch : ℕ → ℕ}
    {original : Fin 8 → ℕ → ℕ} {source : List ℕ}
    (hn : σ.vars "n" = n) (hL : σ.vars "L" = L)
    (hqpow : σ.vars "qpow" = q) (hq : q = 2 ^ L)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hkeys : ∀ d, σ.arrs (keyName d) = arrOf n (original d))
    (hcount : σ.arrs "count" = arrOf q count)
    (hscratch : σ.arrs "scratchOrder" = arrOf n scratch)
    (hinp : σ.inp = source)
    (hsource : ∀ x ∈ source, x ≤ 1)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length)
    (hactiveB : ∀ v < n, active v < B)
    (horiginalB : ∀ d i, i < n → original d i < B)
    (hsample : sampleCount ≤ (scanList active 0 n).length)
    (hqB : q < B) (hnB : n < B) (htwoB : 2 < B) :
    let vertices := scanList active 0 n
    ∃ bits : ℕ → Fin 8 → List ℕ,
    let digits := filledKey original active bits n
    let sorted := radixSort8 q digits vertices
    ∃ σ' ord',
      Run B samplingPrefix σ σ'
        ((120 * n + 120 * L * vertices.length + 8) +
          512 * (vertices.length + q + 1) +
          300 * (sorted.length + 1)) ∧
      σ'.vars "alen" = sorted.length ∧
      σ'.vars "collision" =
        (if HasAdjacentEqualDigits digits sorted then 1 else 0) ∧
      σ'.arrs "ord" = arrOf n ord' ∧
      (∀ i < sorted.length, ord' i = sorted.getD i 0) ∧
      PrefixEnumerates sampleCount ord' (sorted.take sampleCount).toFinset ∧
      σ'.inp = source.drop (8 * L * vertices.length) := by
  dsimp only
  let vertices := scanList active 0 n
  let bits := scanTapeBits active L source
  let rest := source.drop (8 * L * vertices.length)
  obtain ⟨bits', hbitsCanonical, hbitsLen, hbitsBinary, hprefix⟩ :=
    exists_scanTapeBits hsource (by simpa [vertices] using hlen)
  have hinput : σ.inp = keyTape bits' vertices ++ rest := by
    calc
      σ.inp = source := hinp
      _ = keyTape bits' vertices ++ rest := by simpa [rest, vertices] using hprefix
  obtain ⟨σ', ord', hr, halen, hcollision, hord', hordval, hpref, hinp'⟩ :=
    SamplingPrefixSource.samplingPrefix_run hn hL hqpow hq hactive hord hkeys
      hcount hscratch hinput
      (by simpa [vertices] using hbitsLen)
      (by simpa [vertices] using hbitsBinary)
      hactiveB horiginalB hsample hqB hnB htwoB
  refine ⟨bits', ?_⟩
  refine ⟨σ', ord', ?_, halen, hcollision, hord', hordval, hpref, ?_⟩
  · simpa [vertices] using hr
  · simpa [rest, vertices] using hinp'

end Lax235315Proofs.Construction.TapeBlocks
