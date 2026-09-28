import Lax235315Proofs.Construction.GoodRoundBits
import Lax235315Proofs.Construction.SortedKeySampleBridge
import Lax235315Proofs.Construction.NumericSampleLift
import Mathlib.Tactic

/-! The combinatorial good-block event applies to the actual numeric sample
at the front of the literal radix output. -/

namespace Lax235315Proofs.Construction.LiteralSampleGood

open Lax235315Proofs.Construction.GoodRoundBits
open Lax235315Proofs.Construction.PositionFailureBits
open Lax235315Proofs.Construction.SortedKeySampleBridge
open Lax235315Proofs.Construction.NumericSampleLift
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.ScanIndexEquiv
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.PackedKeys
open Lax235315Proofs.Construction.PartitionSource

noncomputable section

lemma literal_sample_good_of_nonfailing_bits
    {n L s : ℕ} {active : ℕ → ℕ}
    (hL : 0 < L) (hn : 1 < n) (hclog : Nat.clog 2 n = L)
    (ρ : Fin (((activeVertices n active).card * 8) * L) → Bool)
    (bad : Finset (Finset (Fin n)))
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
    (hs : s ≤ (activeVertices n active).card)
    (hgood : ρ ∉ badRoundBits (activeVertices n active).card L s hL
      (badPositionSamples active n bad)) :
    let W := (sorted.take s).toFinset
    let WFin := finSample n W
    WFin ⊆ activeFinset active ∧ WFin.card = s ∧ WFin ∉ bad := by
  obtain ⟨f, hf, hsub, hcard, hnotbad⟩ :=
    good_graph_sample_of_not_badRoundBits active hL bad ρ hs hgood
  have hinj : Function.Injective
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ) := by
    simpa [← hf] using f.2
  have hsortedLength : sorted.length = (activeVertices n active).card := by
    rw [hsortedDef]
    have hperm := radixSort8_perm (scanList_nodup active 0 n) hkeyBound
    rw [hperm.length_eq, scanList_length_eq_activeVertices_card]
  obtain ⟨positions, _, _, _, _, hlift, hprefix⟩ :=
    radixPrefix_eq_liftedKeySample (s := s) hL hn hclog ρ hinj hsortedDef hbound
      hkeyBound hcollision hactiveKey (by omega)
  have hfcanon : f =
      (⟨roundAssignmentEquiv (activeVertices n active).card L hL ρ, hinj⟩ :
        Lax235315Proofs.Construction.KeySampling.KeyInjection
          (Fin (activeVertices n active).card) ((2 ^ L) ^ 8)) :=
    Subtype.ext hf
  have hlift' : liftSample active n
      (Lax235315Proofs.Construction.KeySampling.keySample f s) =
      Finset.map (scanVertex active n) ((positions.take s).toFinset) := by
    simpa [hfcanon] using hlift
  have hsampleEq : finSample n (sorted.take s).toFinset =
      liftSample active n
        (Lax235315Proofs.Construction.KeySampling.keySample f s) := by
    rw [hprefix]
    exact (finSample_scan_positions active n (positions.take s)).trans hlift'.symm
  dsimp only
  rw [hsampleEq]
  exact ⟨hsub, hcard, hnotbad⟩

end

end Lax235315Proofs.Construction.LiteralSampleGood
