import Lax235315Proofs.Construction.SamplingFrontier
import Lax808846Proofs.Reasoning
import Mathlib.Tactic

set_option maxRecDepth 4096

/-! Prefix determinism for the literal eight-key sampling frontier.

The canonical key blocks read by the sampler, and hence its sorted sample,
are functions only of the consumed source prefix. -/
namespace Lax235315Proofs.Construction.RoundPrefixDeterminism

open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.TapeBlocks
open Lax235315Proofs.Construction.RandomBits
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib

private lemma take_drop_block_eq {α : Type*} {s t : List α} {q off len : ℕ}
    (hp : s.take q = t.take q) (hbound : off + len ≤ q) :
    (s.drop off).take len = (t.drop off).take len := by
  have hsmall : s.take (off + len) = t.take (off + len) := by
    have h := congrArg (fun xs : List α => xs.take (off + len)) hp
    simpa [List.take_take, Nat.min_eq_left hbound] using h
  calc
    (s.drop off).take len = (s.take (off + len)).drop off := by
      rw [List.take_drop]
    _ = (t.take (off + len)).drop off := by rw [hsmall]
    _ = (t.drop off).take len := by rw [List.take_drop]

private lemma scanList_prefix_length_succ_le
    (active : ℕ → ℕ) {v n : ℕ} (hv : v < n) (hav : active v = 1) :
    (scanList active 0 v).length + 1 ≤ (scanList active 0 n).length := by
  have hprefix : scanList active 0 (v + 1) = scanList active 0 v ++ [v] := by
    rw [scanList_zero_add, if_pos hav]
  have hdecomp : scanList active 0 n =
      scanList active 0 (v + 1) ++ scanList active (v + 1) (n - (v + 1)) := by
    have heq : n = (v + 1) + (n - (v + 1)) := by omega
    rw [heq, scanList_add]
    simp
  rw [hdecomp, List.length_append, hprefix, List.length_append]
  simp

/-- The digit block for any active vertex below `n` depends only on the
first `8 * L * |scanList|` source bits. -/
lemma scanTapeBits_eq_of_shared_prefix
    {n L : ℕ} {active : ℕ → ℕ} {s t : List ℕ}
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length)) :
    ∀ v < n, scanTapeBits active L s v = scanTapeBits active L t v := by
  intro v hv
  by_cases hav : active v = 1
  · have hrank := scanList_prefix_length_succ_le active hv hav
    funext d
    simp only [scanTapeBits, if_pos hav, digitBlock]
    rw [List.drop_drop, List.drop_drop]
    apply take_drop_block_eq hp
    have hd : d.val * L + L ≤ 8 * L := by nlinarith [d.isLt]
    nlinarith [hrank, hd]
  · simp [scanTapeBits, hav]

/-- With the same non-random key data and activity array, both filled key
arrays agree whenever the consumed input prefixes agree. -/
lemma filledKey_eq_of_shared_prefix
    {n L : ℕ} {active : ℕ → ℕ} {s t : List ℕ}
    {original : Fin 8 → ℕ → ℕ}
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length)) :
    filledKey original active (scanTapeBits active L s) n =
      filledKey original active (scanTapeBits active L t) n := by
  have hbits := scanTapeBits_eq_of_shared_prefix hp
  funext d
  funext i
  by_cases hi : i < n ∧ active i = 1
  · simp [filledKey, hi, hbits i hi.1]
  · simp [filledKey, hi]

/-- The full radix-sorted scan is determined by the consumed source prefix. -/
lemma sorted_eq_of_shared_prefix
    {n L q : ℕ} {active : ℕ → ℕ} {s t : List ℕ}
    {original : Fin 8 → ℕ → ℕ}
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length)) :
    radixSort8 q (filledKey original active (scanTapeBits active L s) n)
      (scanList active 0 n) =
    radixSort8 q (filledKey original active (scanTapeBits active L t) n)
      (scanList active 0 n) := by
  have hfilled := filledKey_eq_of_shared_prefix
    (n := n) (L := L) (active := active) (s := s) (t := t)
    (original := original) hp
  rw [hfilled]

/-- Collision detection on the sorted scan is also determined by the
consumed source prefix. -/
lemma sortedCollision_eq_of_shared_prefix
    {n L q : ℕ} {active : ℕ → ℕ} {s t : List ℕ}
    {original : Fin 8 → ℕ → ℕ}
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length)) :
    HasAdjacentEqualDigits (filledKey original active (scanTapeBits active L s) n)
      (radixSort8 q (filledKey original active (scanTapeBits active L s) n)
        (scanList active 0 n)) =
    HasAdjacentEqualDigits (filledKey original active (scanTapeBits active L t) n)
      (radixSort8 q (filledKey original active (scanTapeBits active L t) n)
        (scanList active 0 n)) := by
  have hfilled := filledKey_eq_of_shared_prefix
    (n := n) (L := L) (active := active) (s := s) (t := t)
    (original := original) hp
  have hsorted := sorted_eq_of_shared_prefix
    (n := n) (L := L) (q := q) (active := active) (s := s) (t := t)
    (original := original) hp
  rw [hfilled]

/-- The literal sorted sample prefix selected by the sampling source is
identical for any two tapes with a common consumed prefix. -/
lemma sortedPrefix_eq_of_shared_prefix
    {n L q sampleCount : ℕ} {active : ℕ → ℕ} {s t : List ℕ}
    {original : Fin 8 → ℕ → ℕ}
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length)) :
    (radixSort8 q (filledKey original active (scanTapeBits active L s) n)
      (scanList active 0 n)).take sampleCount =
    (radixSort8 q (filledKey original active (scanTapeBits active L t) n)
      (scanList active 0 n)).take sampleCount := by
  have hsorted := sorted_eq_of_shared_prefix
    (n := n) (L := L) (q := q) (active := active) (s := s) (t := t)
    (original := original) hp
  rw [hsorted]

/-- The literal sorted sample selected by the sampling source is identical
as a finite set for any two tapes with a common consumed prefix. This is the
sample-selection interface used to make the next reduction decision depend
only on fresh bits. -/
lemma sortedSample_eq_of_shared_prefix
    {n L q sampleCount : ℕ} {active : ℕ → ℕ} {s t : List ℕ}
    {original : Fin 8 → ℕ → ℕ}
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length)) :
    ((radixSort8 q (filledKey original active (scanTapeBits active L s) n)
      (scanList active 0 n)).take sampleCount).toFinset =
    ((radixSort8 q (filledKey original active (scanTapeBits active L t) n)
      (scanList active 0 n)).take sampleCount).toFinset := by
  have hprefix := sortedPrefix_eq_of_shared_prefix
    (n := n) (L := L) (q := q) (sampleCount := sampleCount)
    (active := active) (s := s) (t := t) (original := original) hp
  rw [hprefix]


private lemma scanTapeBits_valid
    {n L : ℕ} {active : ℕ → ℕ} {source : List ℕ}
    (hsource : ∀ x ∈ source, x ≤ 1)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length) :
    (∀ v < n, ∀ d, (scanTapeBits active L source v d).length = L) ∧
    (∀ v < n, ∀ d x, x ∈ scanTapeBits active L source v d → x ≤ 1) ∧
    source = keyTape (scanTapeBits active L source) (scanList active 0 n) ++
      source.drop (8 * L * (scanList active 0 n).length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv d
    by_cases ha : active v = 1
    · have hrank := scanList_prefix_length_succ_le active hv ha
      have hblock : 8 * L * (scanList active 0 v).length + 8 * L ≤
          8 * L * (scanList active 0 n).length := by
        have hm := Nat.mul_le_mul_left (8 * L) hrank
        simpa [Nat.mul_add] using hm
      have hsourceDrop : 8 * L ≤
          (source.drop (8 * L * (scanList active 0 v).length)).length := by
        rw [List.length_drop]
        have htotal : 8 * L * (scanList active 0 v).length + 8 * L ≤ source.length :=
          hblock.trans hlen
        apply Nat.le_sub_of_add_le
        nlinarith [htotal]
      simp only [scanTapeBits, if_pos ha]
      change (digitBlock (source.drop (8 * L * (scanList active 0 v).length)) L d).length = L
      unfold digitBlock
      simp only [List.length_take, List.length_drop]
      apply Nat.min_eq_left
      have hd : d.val * L + L ≤ 8 * L := by nlinarith [d.isLt]
      omega
    · simp [scanTapeBits, ha]
  · intro v hv d x hx
    by_cases ha : active v = 1
    · have hx' : x ∈ source := by
        simp only [scanTapeBits, if_pos ha] at hx
        unfold digitBlock at hx
        exact List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      exact hsource x hx'
    · simp [scanTapeBits, ha] at hx
      rcases hx with ⟨_, rfl⟩
      exact Nat.zero_le _
  · rw [keyTape_scan_prefix active L n source hlen]
    exact (List.take_append_drop (8 * L * (scanList active 0 n).length) source).symm

/-- Two literal executions of the sampling prefix with the same initial
non-input state and the same consumed source prefix agree on every field used
by the following round decision: the collision flag and each sampled order
entry. They preserve the active and representative state arrays and expose
the exact unread input tails. -/
lemma samplingPrefix_pair_of_shared_prefix
    {B n L q sampleCount : ℕ} {σ τ : Lax808846Proofs.Imp.Env}
    {active ord count scratch : ℕ → ℕ}
    {original : Fin 8 → ℕ → ℕ} {s t : List ℕ}
    (hvars : σ.vars = τ.vars) (harrs : σ.arrs = τ.arrs)
    (hn : σ.vars "n" = n) (hL : σ.vars "L" = L)
    (hqpow : σ.vars "qpow" = q) (hq : q = 2 ^ L)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hkeys : ∀ d, σ.arrs (keyName d) = arrOf n (original d))
    (hcount : σ.arrs "count" = arrOf q count)
    (hscratch : σ.arrs "scratchOrder" = arrOf n scratch)
    (hinpS : σ.inp = s) (hinpT : τ.inp = t)
    (hsourceS : ∀ x ∈ s, x ≤ 1) (hsourceT : ∀ x ∈ t, x ≤ 1)
    (hlenS : 8 * L * (scanList active 0 n).length ≤ s.length)
    (hlenT : 8 * L * (scanList active 0 n).length ≤ t.length)
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length))
    (hactiveB : ∀ v < n, active v < B)
    (horiginalB : ∀ d i, i < n → original d i < B)
    (hsample : sampleCount ≤ (scanList active 0 n).length)
    (hqB : q < B) (hnB : n < B) (htwoB : 2 < B) :
    ∃ σ' τ' ordS ordT,
      Run B (SamplingPrefixSource.samplingPrefix) σ σ'
        ((120 * n + 120 * L * (scanList active 0 n).length + 8) +
          512 * ((scanList active 0 n).length + q + 1) +
          300 * ((scanList active 0 n).length + 1)) ∧
      Run B SamplingPrefixSource.samplingPrefix τ τ'
        ((120 * n + 120 * L * (scanList active 0 n).length + 8) +
          512 * ((scanList active 0 n).length + q + 1) +
          300 * ((scanList active 0 n).length + 1)) ∧
      σ'.vars "collision" = τ'.vars "collision" ∧
      σ'.vars "alen" = τ'.vars "alen" ∧
      σ'.arrs "activeA" = τ'.arrs "activeA" ∧
      σ'.arrs "activeB" = τ'.arrs "activeB" ∧
      σ'.arrs "nextA" = τ'.arrs "nextA" ∧
      σ'.arrs "nextB" = τ'.arrs "nextB" ∧
      σ'.arrs "repA" = τ'.arrs "repA" ∧
      σ'.arrs "repB" = τ'.arrs "repB" ∧
      σ'.arrs "ord" = arrOf n ordS ∧ τ'.arrs "ord" = arrOf n ordT ∧
      (∀ i < sampleCount, ordS i = ordT i) ∧
      (∀ i < sampleCount,
        (σ'.arrs "ord").getD i 0 = (τ'.arrs "ord").getD i 0) ∧
      σ'.inp = s.drop (8 * L * (scanList active 0 n).length) ∧
      τ'.inp = t.drop (8 * L * (scanList active 0 n).length) := by
  let vertices := scanList active 0 n
  let bitsS := scanTapeBits active L s
  let bitsT := scanTapeBits active L t
  let digitsS := filledKey original active bitsS n
  let digitsT := filledKey original active bitsT n
  let sortedS := radixSort8 q digitsS vertices
  let sortedT := radixSort8 q digitsT vertices
  have hpbits := scanTapeBits_eq_of_shared_prefix
    (n := n) (L := L) (active := active) hp
  have hdigits : digitsS = digitsT := by
    exact filledKey_eq_of_shared_prefix
      (n := n) (L := L) (active := active) (s := s) (t := t)
      (original := original) hp
  have hsorted : sortedS = sortedT := by
    exact sorted_eq_of_shared_prefix
      (n := n) (L := L) (q := q) (active := active)
      (s := s) (t := t) (original := original) hp
  have hsdata := scanTapeBits_valid (active := active) (n := n) (L := L)
    hsourceS hlenS
  have htdata := scanTapeBits_valid (active := active) (n := n) (L := L)
    hsourceT hlenT
  have hinputS : σ.inp = keyTape bitsS vertices ++ s.drop
      (8 * L * vertices.length) := by
    rw [hinpS]
    exact hsdata.2.2
  have hinputT : τ.inp = keyTape bitsT vertices ++ t.drop
      (8 * L * vertices.length) := by
    rw [hinpT]
    exact htdata.2.2
  have hlenBitsS := hsdata.1
  have hbitsS := hsdata.2.1
  have hlenBitsT := htdata.1
  have hbitsT := htdata.2.1
  have hnT : τ.vars "n" = n := by rw [← hvars]; exact hn
  have hLT : τ.vars "L" = L := by rw [← hvars]; exact hL
  have hqpowT : τ.vars "qpow" = q := by rw [← hvars]; exact hqpow
  have hactiveT : τ.arrs "activeA" = arrOf n active := by
    rw [← harrs]; exact hactive
  have hordT : τ.arrs "ord" = arrOf n ord := by rw [← harrs]; exact hord
  have hkeysT : ∀ d, τ.arrs (keyName d) = arrOf n (original d) := by
    intro d
    rw [← harrs]
    exact hkeys d
  have hcountT : τ.arrs "count" = arrOf q count := by
    rw [← harrs]; exact hcount
  have hscratchT : τ.arrs "scratchOrder" = arrOf n scratch := by
    rw [← harrs]; exact hscratch
  obtain ⟨σ', ordS, hrunS, halenS, hcollisionS, hordS, hvalueS,
      hprefixS, hinpS'⟩ := SamplingPrefixSource.samplingPrefix_run
    (hn := hn) (hL := hL) (hqpow := hqpow) (hq := hq)
    (hactive := hactive) (hord := hord) (hkeys := hkeys)
    (hcount := hcount) (hscratch := hscratch) (hinp := hinputS)
    (hlen := hlenBitsS) (hbits := hbitsS) (hactiveB := hactiveB)
    (horiginalB := horiginalB) (hsample := hsample) (hqB := hqB)
    (hnB := hnB) (htwoB := htwoB)
  obtain ⟨τ', ordT, hrunT, halenT, hcollisionT, hordT', hvalueT,
      hprefixT, hinpT'⟩ := SamplingPrefixSource.samplingPrefix_run
    (hn := hnT) (hL := hLT) (hqpow := hqpowT) (hq := hq)
    (hactive := hactiveT) (hord := hordT) (hkeys := hkeysT)
    (hcount := hcountT) (hscratch := hscratchT) (hinp := hinputT)
    (hlen := hlenBitsT) (hbits := hbitsT) (hactiveB := hactiveB)
    (horiginalB := horiginalB) (hsample := hsample) (hqB := hqB)
    (hnB := hnB) (htwoB := htwoB)
  classical
  have hcollision : σ'.vars "collision" = τ'.vars "collision" := by
    rw [hcollisionS, hcollisionT]
    have hc := sortedCollision_eq_of_shared_prefix
      (n := n) (L := L) (q := q) (active := active) (s := s) (t := t)
      (original := original) hp
    simpa [bitsS, bitsT] using congrArg (fun p : Prop => if p then 1 else 0) hc
  have halen : σ'.vars "alen" = τ'.vars "alen" := by
    rw [halenS, halenT]
    simpa [sortedS, sortedT, digitsS, digitsT] using congrArg List.length hsorted
  have hactiveAeq : σ'.arrs "activeA" = τ'.arrs "activeA" := by
    calc
      σ'.arrs "activeA" = σ.arrs "activeA" := hrunS.frame_arr "activeA" (by decide)
      _ = τ.arrs "activeA" := by rw [harrs]
      _ = τ'.arrs "activeA" := (hrunT.frame_arr "activeA" (by decide)).symm
  have hactiveBeq : σ'.arrs "activeB" = τ'.arrs "activeB" := by
    calc
      σ'.arrs "activeB" = σ.arrs "activeB" := hrunS.frame_arr "activeB" (by decide)
      _ = τ.arrs "activeB" := by rw [harrs]
      _ = τ'.arrs "activeB" := (hrunT.frame_arr "activeB" (by decide)).symm
  have hnextAeq : σ'.arrs "nextA" = τ'.arrs "nextA" := by
    calc
      σ'.arrs "nextA" = σ.arrs "nextA" := hrunS.frame_arr "nextA" (by decide)
      _ = τ.arrs "nextA" := by rw [harrs]
      _ = τ'.arrs "nextA" := (hrunT.frame_arr "nextA" (by decide)).symm
  have hnextBeq : σ'.arrs "nextB" = τ'.arrs "nextB" := by
    calc
      σ'.arrs "nextB" = σ.arrs "nextB" := hrunS.frame_arr "nextB" (by decide)
      _ = τ.arrs "nextB" := by rw [harrs]
      _ = τ'.arrs "nextB" := (hrunT.frame_arr "nextB" (by decide)).symm
  have hrepAeq : σ'.arrs "repA" = τ'.arrs "repA" := by
    calc
      σ'.arrs "repA" = σ.arrs "repA" := hrunS.frame_arr "repA" (by decide)
      _ = τ.arrs "repA" := by rw [harrs]
      _ = τ'.arrs "repA" := (hrunT.frame_arr "repA" (by decide)).symm
  have hrepBeq : σ'.arrs "repB" = τ'.arrs "repB" := by
    calc
      σ'.arrs "repB" = σ.arrs "repB" := hrunS.frame_arr "repB" (by decide)
      _ = τ.arrs "repB" := by rw [harrs]
      _ = τ'.arrs "repB" := (hrunT.frame_arr "repB" (by decide)).symm
  have hverticesNodup : vertices.Nodup := scanList_nodup active 0 n
  have hverticesRange : ∀ v ∈ vertices, v < n := by
    intro v hv
    simpa using scanList_mem_range hv
  have hdigitQ : ∀ d v, v ∈ vertices → digitsS d v < q := by
    intro d v hv
    have hvn := hverticesRange v hv
    have hav := (mem_scanList.mp hv).2.2
    change (if v < n ∧ active v = 1 then bitsValue (bitsS v d)
      else original d v) < q
    rw [if_pos ⟨hvn, hav⟩]
    have hbslen : (bitsS v d).length = L := by
      simpa [bitsS] using hlenBitsS v hvn d
    have hval := bitsValue_lt_pow (bitsS v d) (hbitsS v hvn d)
    rw [hbslen] at hval
    calc
      bitsValue (bitsS v d) < 2 ^ L := hval
      _ = q := hq.symm
  have hpermS : List.Perm sortedS vertices :=
    radixSort8_perm hverticesNodup hdigitQ
  have hsortLenS : sortedS.length = vertices.length := hpermS.length_eq
  have hsortLenT : sortedT.length = vertices.length := by
    rw [← hsorted]
    exact hsortLenS
  have hsortLen : sampleCount ≤ sortedS.length := by
    rw [hsortLenS]
    exact hsample
  have hsortLenT' : sampleCount ≤ sortedT.length := by
    rw [hsortLenT]
    exact hsample
  have hordValues : ∀ i < sampleCount, ordS i = ordT i := by
    intro i hi
    rw [hvalueS i (hi.trans_le hsortLen), hvalueT i (hi.trans_le hsortLenT')]
    change sortedS.getD i 0 = sortedT.getD i 0
    rw [hsorted]
  have hordCellValues : ∀ i < sampleCount,
      (σ'.arrs "ord").getD i 0 = (τ'.arrs "ord").getD i 0 := by
    intro i hi
    have hin : i < n := hi.trans_le
      ((hsample).trans (scanList_length_le active 0 n))
    rw [hordS, hordT']
    simp [hordValues i hi, hin]
  refine ⟨σ', τ', ordS, ordT, ?_, ?_, hcollision, halen,
    hactiveAeq, hactiveBeq, hnextAeq, hnextBeq, hrepAeq, hrepBeq,
    hordS, hordT', hordValues, hordCellValues, ?_, ?_⟩
  · apply hrunS.mono
    rw [hsortLenS]
  · apply hrunT.mono
    rw [hsortLenT]
  · simpa [vertices] using hinpS'
  · simpa [vertices] using hinpT'

end Lax235315Proofs.Construction.RoundPrefixDeterminism
