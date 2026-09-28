import Lax235315Proofs.Construction.SamplingFrontier
import Mathlib.Tactic

/-! Prefix determinism for the literal eight-key sampling frontier.

The canonical key blocks read by the sampler, and hence its sorted sample,
are functions only of the consumed source prefix. -/
namespace Lax235315Proofs.Construction.RoundPrefixDeterminism

open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.TapeBlocks

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

/-- The literal sorted sample selected by the sampling source is identical
for any two tapes with a common consumed prefix. This is the sample-selection
interface used to make the next reduction decision depend only on fresh bits. -/
lemma sortedSample_eq_of_shared_prefix
    {n L q sampleCount : ℕ} {active : ℕ → ℕ} {s t : List ℕ}
    {original : Fin 8 → ℕ → ℕ}
    (hp : s.take (8 * L * (scanList active 0 n).length) =
      t.take (8 * L * (scanList active 0 n).length)) :
    ((radixSort8 q (filledKey original active (scanTapeBits active L s) n)
      (scanList active 0 n)).take sampleCount).toFinset =
    ((radixSort8 q (filledKey original active (scanTapeBits active L t) n)
      (scanList active 0 n)).take sampleCount).toFinset := by
  have hfilled := filledKey_eq_of_shared_prefix
    (n := n) (L := L) (active := active) (s := s) (t := t)
    (original := original) hp
  simp [hfilled]

end Lax235315Proofs.Construction.RoundPrefixDeterminism
