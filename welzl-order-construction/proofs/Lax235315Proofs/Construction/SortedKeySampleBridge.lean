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
the source scan positions. The position list is built canonically by
attaching each sorted vertex and applying the inverse scan equivalence.

`hactiveKey` is the concrete packed-key agreement: it follows from
`literal_packedKey_eq_roundAssignment` when `digits` are the eight slices
read by `ReadKeys`. -/
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
    (hactiveKey : ∀ v : ActiveVertex n active,
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm v)).val =
        packedKey (2 ^ L) digits v.val.val)
    (hs : s ≤ sorted.length) :
    ∃ positions : List (Fin (activeVertices n active).card),
      (∀ i : Fin (activeVertices n active).card, i ∈ positions) ∧
      positions.Nodup ∧ positions.length = sorted.length ∧
      positions.map (fun i => (scanIndexEquiv active n i).val.val) = sorted ∧
      liftSample active n
        (keySample ⟨roundAssignmentEquiv
          (activeVertices n active).card L hL ρ, hinj⟩ s) =
        Finset.map (scanVertex active n) ((positions.take s).toFinset) ∧
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
  have hvalidSorted : ∀ v ∈ sorted, v < n ∧ active v = 1 := by
    intro v hv
    have hscan := mem_scanList.mp (hperm.subset hv)
    exact ⟨by omega, hscan.2.2⟩
  have hradix : sorted.Pairwise (LexOn digits digitOrder) := by
    rw [hsortedDef]
    exact radixSort8_pairwise
  have hstrict := pairwise_packedKey_lt_of_noAdjacent hq hbound hsortedNodup
    hradix hcollision
  let posOf : ActiveVertex n active → Fin (activeVertices n active).card :=
    (scanIndexEquiv active n).symm
  let positions : List (Fin (activeVertices n active).card) :=
    sorted.attach.map fun v => posOf
      ⟨⟨v.val, (hvalidSorted v.val v.property).1⟩,
        (hvalidSorted v.val v.property).2⟩
  have hpositionsLength : positions.length = sorted.length := by
    simp [positions]
  have hpositionsNodup : positions.Nodup := by
    apply List.Nodup.map (f := fun v : {w // w ∈ sorted} => posOf
      ⟨⟨v.val, (hvalidSorted v.val v.property).1⟩,
        (hvalidSorted v.val v.property).2⟩)
    · intro v w hvw
      apply Subtype.ext
      have hinv := (Equiv.injective (scanIndexEquiv active n).symm) hvw
      exact congrArg (fun z : ActiveVertex n active => z.val.val) hinv
    · exact List.nodup_attach.mpr hsortedNodup
  have hpositionsComplete :
      ∀ i : Fin (activeVertices n active).card, i ∈ positions := by
    intro i
    let v := scanIndexEquiv active n i
    have hscan : v.val.val ∈ scanList active 0 n := by
      rw [mem_scanList]
      exact ⟨by omega, by omega, v.property⟩
    have hsortedMem : v.val.val ∈ sorted := hperm.symm.subset hscan
    apply List.mem_map.mpr
    refine ⟨⟨v.val.val, hsortedMem⟩, List.mem_attach _ _, ?_⟩
    change posOf v = i
    exact Equiv.symm_apply_apply (scanIndexEquiv active n) i
  have hpositionsVertex :
      positions.map (fun i => (scanIndexEquiv active n i).val.val) = sorted := by
    simp [positions, posOf, List.map_map]
  have hpositionKey : ∀ i, (hi : i < sorted.length) →
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        (positions.get ⟨i, by simpa [hpositionsLength] using hi⟩)).val =
        packedKey q digits sorted[i] := by
    intro i hi
    have hv := hvalidSorted sorted[i] (List.getElem_mem hi)
    let v : ActiveVertex n active := ⟨⟨sorted[i], hv.1⟩, hv.2⟩
    have hp : positions.get ⟨i, by simpa [hpositionsLength] using hi⟩ = posOf v := by
      simp [positions, posOf, v]
    rw [hp]
    simpa [q, hqL] using hactiveKey v
  have hpositionsSorted : positions.Pairwise (fun i j =>
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ i).val <
        (roundAssignmentEquiv (activeVertices n active).card L hL ρ j).val) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < sorted.length := by simpa [hpositionsLength] using hi
    have hj' : j < sorted.length := by simpa [hpositionsLength] using hj
    change (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        (positions.get ⟨i, hi⟩)).val <
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        (positions.get ⟨j, hj⟩)).val
    rw [hpositionKey i hi', hpositionKey j hj']
    exact (List.pairwise_iff_getElem.mp hstrict) i j hi' hj' hij
  have hkeySample := sortedPositionPrefix_eq_keySample hL ρ hinj
    hpositionsComplete hpositionsNodup hpositionsSorted
      (by simpa [hpositionsLength] using hs)
  have hprefix : sorted.take s = (positions.take s).map
      (fun i => (scanIndexEquiv active n i).val.val) := by
    calc
      sorted.take s = (positions.map
          (fun i => (scanIndexEquiv active n i).val.val)).take s := by
            rw [hpositionsVertex]
      _ = (positions.take s).map
          (fun i => (scanIndexEquiv active n i).val.val) := List.map_take.symm
  refine ⟨positions, hpositionsComplete, hpositionsNodup, hpositionsLength,
    hpositionsVertex, ?_, hprefix⟩
  · rw [hkeySample]
    rfl

end Lax235315Proofs.Construction.SortedKeySampleBridge
