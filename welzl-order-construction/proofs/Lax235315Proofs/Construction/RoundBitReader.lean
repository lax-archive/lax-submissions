import Lax235315Proofs.Construction.TapeBlocks
import Lax235315Proofs.Construction.RandomKeyEquiv
import Lax195003.WordRamRandomness
import Mathlib.Tactic

/-! The literal source tape slices agree with the row-major Boolean words
used by the existing random-key equivalence. -/

namespace Lax235315Proofs.Construction.RoundBitReader

open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.TapeBlocks

lemma tripleIndexEquiv_val {a L : ℕ} (i : Fin a) (d : Fin 8) (j : Fin L) :
    (tripleIndexEquiv a L ((i, d), j)).val =
      (8 * L * i.val + d.val * L + j.val) := by
  simp [tripleIndexEquiv, finProdFinEquiv]
  ring

/-- The `L`-word slice read for one literal round digit is exactly the source
word associated with the reshaped Boolean tape. -/
lemma digitBlock_eq_bitTape {a L : ℕ} (ρ : Fin ((a * 8) * L) → Bool)
    (i : Fin a) (d : Fin 8) :
    TapeBlocks.digitBlock ((bitTape ρ).drop (8 * L * i.val)) L d =
      bitTape (bitBlockEquiv a L ρ i d) := by
  let source := bitTape ρ
  let offset := 8 * L * i.val + d.val * L
  have hlen : source.length = (a * 8) * L := by
    simp [source, bitTape]
  have hspan : offset + L ≤ source.length := by
    have hd : d.val + 1 ≤ 8 := by omega
    have hdL : (d.val + 1) * L ≤ 8 * L := Nat.mul_le_mul_right L hd
    have hi : i.val + 1 ≤ a := by omega
    have hdecomp : offset + L = 8 * L * i.val + (d.val + 1) * L := by
      dsimp [offset]
      rw [Nat.add_mul]
      omega
    rw [hdecomp]
    calc
      8 * L * i.val + (d.val + 1) * L ≤ 8 * L * i.val + 8 * L := by omega
      _ ≤ 8 * L * a := Nat.mul_le_mul_left (8 * L) hi
      _ = (a * 8) * L := by ring
      _ = source.length := hlen.symm
  have hleftLength :
      (TapeBlocks.digitBlock ((bitTape ρ).drop (8 * L * i.val)) L d).length = L := by
    unfold TapeBlocks.digitBlock
    rw [List.drop_drop]
    change ((source.drop offset).take L).length = L
    have hrem : L ≤ source.length - offset := by omega
    have hrem' : L ≤ (a * 8) * L - offset := by simpa [hlen] using hrem
    simp [source, List.length_take, List.length_drop, hlen,
      Nat.min_eq_left hrem']
  apply List.ext_getElem
  · simpa [bitTape] using hleftLength
  · intro j hj₁ hj₂
    have hj : j < L := by simpa [bitTape] using hj₂
    have hjspan : offset + j < source.length := by omega
    have hjspan' : offset + j < (a * 8) * L := by rw [← hlen]; exact hjspan
    have hindex := tripleIndexEquiv_val i d ⟨j, hj⟩
    have hword :
        (⟨8 * L * i.val + d.val * L + j, hjspan'⟩ : Fin ((a * 8) * L)) =
          tripleIndexEquiv a L ((i, d), ⟨j, hj⟩) := by
      apply Fin.ext
      simpa using hindex.symm
    have hbit : ρ ⟨8 * L * i.val + d.val * L + j, hjspan'⟩ =
        ρ (tripleIndexEquiv a L ((i, d), ⟨j, hj⟩)) := congrArg ρ hword
    unfold TapeBlocks.digitBlock
    simp [List.getElem_take, List.getElem_drop, bitTape,
      List.getElem_ofFn, bitBlockEquiv]
    rw [hbit]
    rfl

/-- The value read from a literal digit slice is the value of the existing
`boolWordEquiv` digit. -/
lemma digitBlock_bitsValue {a L : ℕ} (ρ : Fin ((a * 8) * L) → Bool)
    (i : Fin a) (d : Fin 8) :
    bitsValue (TapeBlocks.digitBlock ((bitTape ρ).drop (8 * L * i.val)) L d) =
      (boolWordEquiv L (bitBlockEquiv a L ρ i d)).val := by
  rw [digitBlock_eq_bitTape]
  rfl

/-- The eight source slices, when packed as radix digits, are the key in the
existing round-assignment equivalence. -/
lemma packedKey_digitBlocks_eq_roundAssignmentEquiv {a L : ℕ}
    (hL : 0 < L) (ρ : Fin ((a * 8) * L) → Bool) (i : Fin a) :
    Lax235315Proofs.Construction.PackedKeys.packedKey (2 ^ L)
        (fun d _ => bitsValue
          (TapeBlocks.digitBlock ((bitTape ρ).drop (8 * L * i.val)) L d)) 0 =
      (roundAssignmentEquiv a L hL ρ i).val := by
  let literalDigits : Fin 8 → ℕ → ℕ := fun d _ => bitsValue
    (TapeBlocks.digitBlock ((bitTape ρ).drop (8 * L * i.val)) L d)
  have hdigits : literalDigits = bitDigits (bitBlockEquiv a L ρ i) := by
    funext d v
    simpa [literalDigits, bitDigits] using (digitBlock_bitsValue ρ i d)
  change Lax235315Proofs.Construction.PackedKeys.packedKey (2 ^ L)
    literalDigits 0 = (roundAssignmentEquiv a L hL ρ i).val
  rw [hdigits]
  change Lax235315Proofs.Construction.PackedKeys.packedKey (2 ^ L)
    (bitDigits (bitBlockEquiv a L ρ i)) 0 =
      Lax235315Proofs.Construction.PackedKeys.packedKey (2 ^ L)
        (bitDigits (bitBlockEquiv a L ρ i)) 0
  rfl

end Lax235315Proofs.Construction.RoundBitReader
