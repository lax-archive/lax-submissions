import Lax457868Proofs.FairBitIndices
import Lax457868Proofs.StoppingPrefix
import Lax457868Proofs.ReusedOriginal.Construction.AdaptiveStateProtocol
import Mathlib.Tactic

/-!
The bounded fair-bit rejection selector as an adaptive protocol. Each attempted
draw reads one `clog 2 m`-bit block. An accepted block terminates immediately;
only a rejected block enters the next attempt. At cap zero a zero-width query
with its unique block marked bad records logical exhaustion without reading
another bit. Thus a cap of `t` uses at most `t` physical blocks, although the
protocol's query index also counts the terminal exhaustion leaf.
-/

namespace Lax457868Proofs.RejectionProtocol

open FairBitIndices
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveBitBlocks
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

/-- The exact rejection sampler, with a zero-bit exhaustion leaf. -/
def rejectionProtocol (m : ℕ) (hm : 0 < m) : (t : ℕ) → Protocol (t + 1)
  | 0 => .query (k := 0) Finset.univ (fun _ => .stop 0)
  | t + 1 => .query (k := Nat.clog 2 m) ∅ (fun bits =>
      if decodeBitIndex m hm bits = none then rejectionProtocol m hm t
      else .stop (t + 1))

/-- Exhaustion has probability one but consumes no source bits. -/
lemma failureMass_zero (m : ℕ) (hm : 0 < m) :
    failureMass (rejectionProtocol m hm 0) = 1 := by
  simp [rejectionProtocol, failureMass]

/-- One attempt contributes the rejected-block fraction times the probability
of exhaustion over the remaining attempts. -/
lemma failureMass_succ (m : ℕ) (hm : 0 < m) (t : ℕ) :
    failureMass (rejectionProtocol m hm (t + 1)) =
      ((rejectedBlocks m).card : ℚ) / (2 : ℚ) ^ Nat.clog 2 m *
        failureMass (rejectionProtocol m hm t) := by
  classical
  simp only [rejectionProtocol, failureMass]
  simp only [Finset.card_empty, Nat.cast_zero, zero_add]
  simp
  have hsum :
      (∑ bits : Fin (Nat.clog 2 m) → Bool,
        if decodeBitIndex m hm bits = none then
          failureMass (rejectionProtocol m hm t) else 0) =
        ((rejectedBlocks m).card : ℚ) *
          failureMass (rejectionProtocol m hm t) := by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter fun bits : Fin (Nat.clog 2 m) → Bool =>
        decodeBitIndex m hm bits = none) = rejectedBlocks m := by
      ext bits
      simpa using (decode_rejected_iff m hm bits).symm
    rw [hfilter]
    simp
  have hpointwise (bits : Fin (Nat.clog 2 m) → Bool) :
      failureMass
        (if decodeBitIndex m hm bits = none then rejectionProtocol m hm t
         else Protocol.stop (t + 1)) =
        if decodeBitIndex m hm bits = none then
          failureMass (rejectionProtocol m hm t) else 0 := by
    split <;> simp [failureMass]
  simp_rw [hpointwise]
  rw [hsum]
  ring

/-- Exact exhaustion probability after `t` attempted draws. -/
lemma failureMass_eq_pow (m : ℕ) (hm : 0 < m) (t : ℕ) :
    failureMass (rejectionProtocol m hm t) =
      (((rejectedBlocks m).card : ℚ) / (2 : ℚ) ^ Nat.clog 2 m) ^ t := by
  induction t with
  | zero => simp [failureMass_zero]
  | succ t ih => rw [failureMass_succ, ih, pow_succ, mul_comm]

/-- Every path reads at most the `t` physical blocks supplied by the cap. -/
lemma maxConsumedBits_le (m : ℕ) (hm : 0 < m) (t : ℕ) :
    maxConsumedBits (rejectionProtocol m hm t) ≤ t * Nat.clog 2 m := by
  induction t with
  | zero => simp [rejectionProtocol, maxConsumedBits]
  | succ t ih =>
      simp only [rejectionProtocol, maxConsumedBits]
      have hsup :
          (Finset.univ.sup fun bits : Fin (Nat.clog 2 m) → Bool =>
            maxConsumedBits
              (if decodeBitIndex m hm bits = none then rejectionProtocol m hm t
               else Protocol.stop (t + 1))) ≤ t * Nat.clog 2 m := by
        apply Finset.sup_le
        intro bits _
        split
        · exact ih
        · simp [maxConsumedBits]
      simpa [Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add_left hsup (Nat.clog 2 m)

/-- The exact failure probability is bounded by the geometric half tail. -/
lemma failureMass_le_half_pow (m : ℕ) (hm : 0 < m) (t : ℕ) :
    failureMass (rejectionProtocol m hm t) ≤ (1 / 2 : ℚ) ^ t := by
  rw [failureMass_eq_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hhalf := rejectedBlocks_half m hm
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hhalf
  have hpos : (0 : ℚ) < (2 : ℚ) ^ Nat.clog 2 m := by positivity
  apply (div_le_iff₀ hpos).2
  have hcast := Nat.cast_le (α := ℚ).mpr hhalf
  push_cast at hcast
  nlinarith

/-- The protocol fits in every fixed tape long enough for all attempted
draws; the terminal exhaustion query asks for zero additional bits. -/
lemma fits (m : ℕ) (hm : 0 < m) (t T : ℕ)
    (hT : t * Nat.clog 2 m ≤ T) : Fits (rejectionProtocol m hm t) T :=
  fits_of_maxConsumedBits _ _ ((maxConsumedBits_le m hm t).trans hT)

/-- The old adaptive finite-tape theorem applies exactly to this sampler. -/
lemma failingTapes_fraction (m : ℕ) (hm : 0 < m) (t T : ℕ)
    (hT : t * Nat.clog 2 m ≤ T) :
    ((failingTapes (rejectionProtocol m hm t) T (fits m hm t T hT)).card : ℚ) /
      (2 : ℚ) ^ T =
      (((rejectedBlocks m).card : ℚ) / (2 : ℚ) ^ Nat.clog 2 m) ^ t := by
  rw [failingTapes_fraction_eq_failureMass, failureMass_eq_pow]

/-- The protocol's rational failure mass is exactly the failure fraction of
the existing `selectBitIndex` on length-`t` block tapes. This identifies the
counted event with the implemented selector's `none` outcome. -/
lemma failureMass_eq_selector_fraction (m : ℕ) (hm : 0 < m) (t : ℕ) :
    failureMass (rejectionProtocol m hm t) =
      ((allRejectedBitTapes m t).card : ℚ) /
        (Fintype.card (BitTape m t) : ℚ) := by
  rw [failureMass_eq_pow, card_allRejectedBitTapes, SamplerRetries.card_tapes]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← pow_mul, div_pow]
  push_cast
  rw [pow_mul]

/-- The same exact fraction can be stated directly with the selector's
failure predicate, without an independence assumption beyond finite counting.
-/
lemma failureMass_eq_selector_count (m : ℕ) (hm : 0 < m) (t : ℕ) :
    failureMass (rejectionProtocol m hm t) =
      ((Finset.univ.filter (fun tape : BitTape m t =>
        selectBitIndex m hm t tape = none)).card : ℚ) /
        (Fintype.card (BitTape m t) : ℚ) := by
  rw [failureMass_eq_selector_fraction]
  have hsets :
      (Finset.univ.filter (fun tape : BitTape m t =>
        selectBitIndex m hm t tape = none)) = allRejectedBitTapes m t := by
    ext tape
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (selectBitIndex_eq_none_iff m hm t tape)
  rw [hsets]

/-- Fixed bit tapes of any sufficient length and the selector's finite block
tapes have exactly the same failure fraction. Suffix bits after stopping are
counted freely on the fixed-tape side. -/
lemma failingTapes_fraction_eq_selector_count (m : ℕ) (hm : 0 < m)
    (t T : ℕ) (hT : t * Nat.clog 2 m ≤ T) :
    ((failingTapes (rejectionProtocol m hm t) T (fits m hm t T hT)).card : ℚ) /
      (2 : ℚ) ^ T =
      ((Finset.univ.filter (fun tape : BitTape m t =>
        selectBitIndex m hm t tape = none)).card : ℚ) /
        (Fintype.card (BitTape m t) : ℚ) := by
  rw [failingTapes_fraction_eq_failureMass, failureMass_eq_selector_count]

/-- The finite fixed-tape failure fraction has the same geometric bound as
the selector, including the zero-attempt case. -/
lemma failingTapes_fraction_le_half_pow (m : ℕ) (hm : 0 < m)
    (t T : ℕ) (hT : t * Nat.clog 2 m ≤ T) :
    ((failingTapes (rejectionProtocol m hm t) T (fits m hm t T hT)).card : ℚ) /
      (2 : ℚ) ^ T ≤ (1 / 2 : ℚ) ^ t := by
  rw [failingTapes_fraction_eq_failureMass]
  exact failureMass_le_half_pow m hm t

/-- An attempted draw is exactly one query with the concrete decoder's
accept/continue branches. -/
lemma rejectionProtocol_unfold (m : ℕ) (hm : 0 < m) (t : ℕ) :
    rejectionProtocol m hm (t + 1) =
      Protocol.query (Finset.empty : Finset (Fin (Nat.clog 2 m) → Bool))
        (fun bits => if decodeBitIndex m hm bits = none then
          rejectionProtocol m hm t else Protocol.stop (t + 1)) := rfl

/-- At a rejected block the protocol uses exactly the next attempt; at an
accepted block it stops before inspecting the following block. -/
lemma rejectionProtocol_step (m : ℕ) (hm : 0 < m) (t : ℕ)
    (bits : Fin (Nat.clog 2 m) → Bool) :
    (if decodeBitIndex m hm bits = none then rejectionProtocol m hm t
      else Protocol.stop (t + 1)) =
    (if bits ∈ rejectedBlocks m then rejectionProtocol m hm t
      else Protocol.stop (t + 1)) := by
  by_cases h : bits ∈ rejectedBlocks m
  · have hd := (decode_rejected_iff m hm bits).mp h
    simp [h, hd]
  · have hd : decodeBitIndex m hm bits ≠ none := by
      intro he
      exact h ((decode_rejected_iff m hm bits).mpr he)
    simp [h, hd]

/-- A capped selector reports success on attempt `v+1` exactly when its first
`v` blocks reject and the next block decodes to that index. In the protocol,
that block takes the stop continuation, so no later block is read. -/
lemma accepted_prefix_iff_stop (m : ℕ) (hm : 0 < m) (v : ℕ)
    (i : Fin m) (pre : BitTape m v)
    (block : Fin (Nat.clog 2 m) → Bool) :
    Lax457868Proofs.StoppingPrefix.stoppedEvent m hm (v + 1) (v + 1) i
        (Fin.snoc pre block) ↔
      Lax457868Proofs.StoppingPrefix.rejectedPrefix m hm v pre ∧
        decodeBitIndex m hm block = some i ∧
        (if decodeBitIndex m hm block = none then rejectionProtocol m hm v
          else Protocol.stop (v + 1)) = Protocol.stop (v + 1) := by
  rw [Lax457868Proofs.StoppingPrefix.stoppedEvent_snoc_iff]
  constructor
  · rintro ⟨hpre, hblock⟩
    exact ⟨hpre, hblock, by simp [hblock]⟩
  · rintro ⟨hpre, hblock, _⟩
    exact ⟨hpre, hblock⟩

/-- A query transcript records the width and bits supplied at each node.
Unvisited entries after an early stop are ignored. -/
abbrev QueryBlock := Σ k : ℕ, Tape k

/-- Evaluate an adaptive protocol on a concrete ordered transcript. A bad
query fails, a stop succeeds, and a missing or mismatched query fails. -/
def runProtocol : {R : ℕ} → Protocol R → List QueryBlock → Bool
  | _, .stop _, _ => true
  | _, .query (k := _) _ _, [] => false
  | _, .query (k := k) bad next, ⟨k', bits⟩ :: rest =>
      if h : k' = k then
        let observed : Tape k := Eq.mp (congrArg Tape h) bits
        if observed ∈ bad then false else runProtocol (next observed) rest
      else false

/-- Supply exactly `t` source blocks and a final zero-width exhaustion
sentinel. The sentinel is a logical protocol event, not a source-tape read. -/
def selectorTranscript (m t : ℕ) (blocks : BitTape m t) : List QueryBlock :=
  (List.ofFn blocks).map (fun bits => ⟨Nat.clog 2 m, bits⟩) ++
    [⟨0, fun i => Fin.elim0 i⟩]

/-- The protocol evaluator agrees pointwise with the concrete capped selector:
it succeeds exactly when the selector returns an index. -/
lemma runProtocol_iff_selector_some (m : ℕ) (hm : 0 < m) :
    ∀ t (blocks : BitTape m t),
      runProtocol (rejectionProtocol m hm t) (selectorTranscript m t blocks) = true ↔
        selectBitIndex m hm t blocks ≠ none := by
  intro t
  induction t with
  | zero =>
      intro blocks
      simp [runProtocol, rejectionProtocol, selectorTranscript,
        selectBitIndex, firstDecoded]
      exact Subsingleton.elim _ _
  | succ t ih =>
      intro blocks
      simp only [selectorTranscript, List.ofFn_succ, List.map_cons,
        List.cons_append, rejectionProtocol, runProtocol]
      simp only [selectBitIndex, List.ofFn_succ, List.map_cons]
      by_cases h : decodeBitIndex m hm (blocks 0) = none
      · simp only [h, firstDecoded]
        simpa [h, selectorTranscript, selectBitIndex, List.map_ofFn] using
          (ih (fun i => blocks i.succ))
      · cases hdec : decodeBitIndex m hm (blocks 0) with
        | none => exact False.elim (h hdec)
        | some i => simp [hdec, runProtocol, firstDecoded]

/-- The concrete protocol transcript fails on exactly the block tapes where
the existing selector returns `none`, including cap zero. -/
lemma runProtocol_eq_false_iff_selector_none (m : ℕ) (hm : 0 < m)
    (t : ℕ) (blocks : BitTape m t) :
    runProtocol (rejectionProtocol m hm t) (selectorTranscript m t blocks) = false ↔
      selectBitIndex m hm t blocks = none := by
  simpa using not_congr (runProtocol_iff_selector_some m hm t blocks)

end Lax457868Proofs.RejectionProtocol
