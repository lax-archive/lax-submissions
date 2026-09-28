import Lax235315Proofs.Construction.SamplingFrontier
import Lax235315Proofs.Construction.ScanSampleTransport
import Lax235315Proofs.Construction.RoundBitReader
import Lax235315Proofs.Construction.PackedKeys
import Lax235315Proofs.Construction.KeySampling
import Lax235315Proofs.Construction.CollisionDetection
import Mathlib.Tactic

/-! A deterministic bridge from the literal radix prefix to the abstract
bottom-key sample on positions in the source's active-vertex scan. -/

namespace Lax235315Proofs.Construction.SortedKeySampleBridge

open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.KeySampling
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PackedKeys
open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.ScanIndexEquiv
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax195003.WordRamRandomness

/-- Literal digit slices at a source scan position pack to the assignment
value used in the finite probability space. -/
lemma literal_packedKey_eq_roundAssignment
    {a L : ℕ} (hL : 0 < L) (ρ : Fin ((a * 8) * L) → Bool)
    (i : Fin a) :
    packedKey (2 ^ L)
        (fun d _ => bitsValue
          (TapeBlocks.digitBlock ((bitTape ρ).drop (8 * L * i.val)) L d)) 0 =
      (roundAssignmentEquiv a L hL ρ i).val :=
  RoundBitReader.packedKey_digitBlocks_eq_roundAssignmentEquiv hL ρ i

/-- A complete sorted list of source scan positions, ordered by an injective
random-key assignment, has as its first `s` positions exactly the abstract
key sample. This is the equality used to identify `SamplingFrontier`'s
literal sample set with `ScanSampleTransport.liftSample`. -/
lemma sortedPositionPrefix_eq_keySample
    {a L s : ℕ} (hL : 0 < L)
    (ρ : Fin ((a * 8) * L) → Bool)
    (hinj : Function.Injective (roundAssignmentEquiv a L hL ρ))
    {positions : List (Fin a)}
    (hcomplete : ∀ i : Fin a, i ∈ positions)
    (hnodup : positions.Nodup)
    (hsorted : positions.Pairwise (fun i j =>
      (roundAssignmentEquiv a L hL ρ i).val <
        (roundAssignmentEquiv a L hL ρ j).val))
    (hs : s ≤ positions.length) :
    keySample ⟨roundAssignmentEquiv a L hL ρ, hinj⟩ s =
      (positions.take s).toFinset := by
  exact keySample_eq_take_of_pairwise
    ⟨roundAssignmentEquiv a L hL ρ, hinj⟩ hcomplete hnodup hsorted hs

/-- If the literal radix output is collision-free, its key order transfers to
the source scan positions. Mapping the abstract key sample back through the
scan equivalence therefore yields precisely the literal sampled prefix.

`hpositionKey` is the concrete packed-key agreement: it follows from
`literal_packedKey_eq_roundAssignment` when `digits` are the eight slices
read by `ReadKeys`. `hpositionVertex` says that the position list is the
inverse image, under `ScanIndexEquiv`, of the vertices in the radix output. -/
lemma radixPrefix_eq_liftedKeySample
    {n L s : ℕ} {active : ℕ → ℕ}
    (hL : 0 < L) (hn : 1 < n) (hclog : Nat.clog 2 n = L)
    (ρ : Fin (((activeVertices n active).card * 8) * L) → Bool)
    (hinj : Function.Injective (roundAssignmentEquiv
      (activeVertices n active).card L hL ρ))
    {digits : Fin 8 → ℕ → ℕ} {sorted : List ℕ}
    (hsortedDef : sorted = radixSort8 (2 ^ Nat.clog 2 n) digits
      (scanList active 0 n))
    (hbound : ∀ v ∈ sorted, ∀ d, digits d v < 2 ^ Nat.clog 2 n)
    (hkeyBound : ∀ d v, v ∈ scanList active 0 n →
      digits d v < 2 ^ Nat.clog 2 n)
    (hcollision : ¬ HasAdjacentEqualDigits digits sorted)
    {positions : List (Fin (activeVertices n active).card)}
    (hcomplete : ∀ i, i ∈ positions) (hnodup : positions.Nodup)
    (hlen : positions.length = sorted.length)
    (hpositionVertex : ∀ i, (hi : i < sorted.length) →
      sorted[i] = (scanIndexEquiv active n
        (positions.get ⟨i, by simpa [hlen] using hi⟩)).val.val)
    (hpositionKey : ∀ i, (hi : i < sorted.length) →
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        (positions.get ⟨i, by simpa [hlen] using hi⟩)).val =
        packedKey (2 ^ L) digits sorted[i])
    (hs : s ≤ sorted.length) :
    (liftSample active n
        (keySample ⟨roundAssignmentEquiv
          (activeVertices n active).card L hL ρ, hinj⟩ s) =
      Finset.map (scanVertex active n) ((positions.take s).toFinset)) ∧
    sorted.take s = (positions.take s).map
      (fun i => (scanIndexEquiv active n i).val.val) := by
  let q := 2 ^ Nat.clog 2 n
  let f : KeyInjection (Fin (activeVertices n active).card) ((2 ^ L) ^ 8) :=
    ⟨roundAssignmentEquiv (activeVertices n active).card L hL ρ, hinj⟩
  have hqL : q = 2 ^ L := by simp [q, hclog]
  have hq : 1 < q := by
    dsimp [q]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt (Nat.clog_pos (by omega) hn))
  have hverticesNodup : (scanList active 0 n).Nodup := scanList_nodup active 0 n
  have hperm : List.Perm sorted (scanList active 0 n) := by
    rw [hsortedDef]
    exact radixSort8_perm hverticesNodup hkeyBound
  have hsortedNodup : sorted.Nodup := hperm.symm.nodup hverticesNodup
  have hradix : sorted.Pairwise (LexOn digits digitOrder) := by
    rw [hsortedDef]
    exact radixSort8_pairwise
  have hstrict := pairwise_packedKey_lt_of_noAdjacent hq hbound hsortedNodup
    hradix hcollision
  have hpositionsSorted : positions.Pairwise (fun i j =>
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ i).val <
        (roundAssignmentEquiv (activeVertices n active).card L hL ρ j).val) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < sorted.length := by simpa [hlen] using hi
    have hj' : j < sorted.length := by simpa [hlen] using hj
    change (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        (positions.get ⟨i, hi⟩)).val <
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        (positions.get ⟨j, hj⟩)).val
    rw [hpositionKey i hi', hpositionKey j hj', ← hqL]
    exact (List.pairwise_iff_getElem.mp hstrict) i j hi' hj' hij
  have hkeySample := sortedPositionPrefix_eq_keySample hL ρ hinj
    hcomplete hnodup hpositionsSorted (by simpa [hlen] using hs)
  constructor
  · rw [hkeySample]
    rfl
  · apply List.ext_getElem
    · simp [List.length_take, Nat.min_eq_left hs, hlen]
    · intro i hi₁ hi₂
      have hi' := hi₁
      rw [List.length_take] at hi'
      have hi : i < sorted.length := hi'.trans_le (Nat.min_le_right _ _)
      simpa [List.getElem_take, List.getElem_map] using hpositionVertex i hi

end Lax235315Proofs.Construction.SortedKeySampleBridge
