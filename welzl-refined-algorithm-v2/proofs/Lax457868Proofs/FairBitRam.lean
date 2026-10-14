import Mathlib.Tactic
import Lax235315Proofs.Construction.RandomBits
import Lax235315Proofs.Construction.RandomKeyEquiv
import Lax457868Proofs.FairBitIndices

/-!
The IMP+ implementation of the finite fair-bit rejection selector. Each
attempt calls the existing binary key reader, so a block is consumed exactly
as one `readKeyDigit "key0"` operation.
-/

namespace Lax457868Proofs.FairBitRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax457868Proofs.FairBitIndices

/-- The finite source command that reads blocks until one is accepted or the
cap is reached. `drawStop` is shortened to the number already consumed when
an accepted block is found, so the loop halts at that exact attempt. -/
private def selectorBody : Com :=
  seqs [readKeyDigit "key0",
    .assign "drawValue" (.get "key0" (.var "v")),
    inc "drawUsed",
    .ite (.lt (.var "drawValue") (.var "drawModulus"))
      (.assign "drawFound" (.lit 1)) .skip,
    .ite (.eq (.var "drawFound") (.lit 1))
      (.assign "drawStop" (.var "drawUsed")) .skip]

/-- The capped rejection loop. Its initial stop is the cap; acceptance sets
the stop to the current draw count. -/
private def selectorLoop : Com :=
  .while (.lt (.var "drawUsed") (.var "drawStop")) selectorBody

/-- Initialize the counters and run the finite rejection loop. -/
def countedRejectionSelector : Com :=
  seqs [
    .assign "drawUsed" (.lit 0),
    .assign "drawFound" (.lit 0),
    .assign "drawValue" (.lit 0),
    .assign "drawStop" (.var "drawCap"),
    selectorLoop]

/-- Flatten a tape of independent bit blocks into the source reader's input
format: each block's most-significant-bit-first words are consecutive. -/
def flattenBitBlocks {L t : ℕ}
    (tape : Fin t → (Fin L → Bool)) : List ℕ :=
  (List.ofFn tape).flatMap Lax195003.WordRamRandomness.bitTape

/-- Splitting off the first independent block exposes precisely the input
prefix consumed by `readKeyDigit "key0"`. -/
lemma flattenBitBlocks_succ {L t : ℕ}
    (tape : Fin (t + 1) → (Fin L → Bool)) :
    flattenBitBlocks tape =
      Lax195003.WordRamRandomness.bitTape (tape 0) ++
        flattenBitBlocks (fun i => tape i.succ) := by
  simp [flattenBitBlocks, List.ofFn_succ, List.flatMap_cons]

/-- The flattened input contains exactly `L` words per block. -/
lemma flattenBitBlocks_length {L t : ℕ}
    (tape : Fin t → (Fin L → Bool)) :
    (flattenBitBlocks tape).length = t * L := by
  induction t with
  | zero => simp [flattenBitBlocks]
  | succ t ih =>
      rw [flattenBitBlocks_succ]
      simp [List.length_append, Lax195003.WordRamRandomness.bitTape, ih]
      rw [Nat.succ_mul]
      omega

/-- The reader's most-significant-bit-first value agrees exactly with the
finite fair-bit block decoder. -/
lemma bitBlockValue_eq_bitsValue {L : ℕ} (bits : Fin L → Bool) :
    bitBlockValue bits = bitsValue (Lax195003.WordRamRandomness.bitTape bits) := by
  unfold bitBlockValue
  symm
  exact bitsValue_eq_ofDigits_reverse _

/-- Reading a single fair-bit block through the existing `key0` reader stores
the value decoded by `FairBitIndices.bitBlockValue`, consumes exactly the
block, and retains the reader's exact source cost. -/
lemma readBitBlock_run {B n v L : ℕ} {σ : Env} {g : ℕ → ℕ}
    {bits : Fin L → Bool} {rest : List ℕ}
    (hkey : σ.arrs "key0" = arrOf n g)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = L)
    (hinp : σ.inp = Lax195003.WordRamRandomness.bitTape bits ++ rest)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B) :
    ∃ σ' g', Run B (readKeyDigit "key0") σ σ' (15 * L + 11) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      g' v = bitBlockValue bits ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧ σ'.inp = rest ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = L := by
  have hbs : (Lax195003.WordRamRandomness.bitTape bits).length = L := by
    simp [Lax195003.WordRamRandomness.bitTape]
  have hbits : ∀ b ∈ Lax195003.WordRamRandomness.bitTape bits, b ≤ 1 := by
    intro b hb
    simp only [Lax195003.WordRamRandomness.bitTape, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩
    cases bits i <;> decide
  obtain ⟨σ', g', hr, harr, hval, hframe, hinp', hv', hL'⟩ :=
    Lax235315Proofs.Construction.RandomBits.readKeyDigit_run
      hkey hv hvn hL hbs hinp hbits hpowB hnB htwoB
  refine ⟨σ', g', hr, harr, ?_, hframe, hinp', hv', hL'⟩
  rw [bitBlockValue_eq_bitsValue]
  exact hval

end Lax457868Proofs.FairBitRam
