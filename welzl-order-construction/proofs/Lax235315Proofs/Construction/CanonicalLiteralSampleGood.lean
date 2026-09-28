import Lax235315Proofs.Construction.LiteralSampleGood
import Lax235315Proofs.Construction.TapeKeyAgreement
import Mathlib.Tactic

set_option maxHeartbeats 4000000

/-! The literal graph-sample conclusion for the canonical source-prefix key
reader, with its assignment-key premise discharged from the tape itself. -/

namespace Lax235315Proofs.Construction.CanonicalLiteralSampleGood

open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.GoodRoundBits
open Lax235315Proofs.Construction.KeySampling
open Lax235315Proofs.Construction.LiteralSampleGood
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.NumericSampleLift
open Lax235315Proofs.Construction.PackedKeys
open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.PositionFailureBits
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.ScanIndexEquiv
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.TapeBlocks
open Lax235315Proofs.Construction.TapeKeyAgreement
open Lax195003.WordRamRandomness

noncomputable section

private lemma no_adjacent_equal_of_injective_assignment
    {n L : ℕ} {active : ℕ → ℕ}
    (hL : 0 < L)
    (ρ : Fin (((activeVertices n active).card * 8) * L) → Bool)
    (hinj : Function.Injective
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ))
    {digits : Fin 8 → ℕ → ℕ} {sorted : List ℕ}
    (hsortedDef : sorted = radixSort8 (2 ^ Nat.clog 2 n) digits
      (scanList active 0 n))
    (hkeyBound : ∀ d v, v ∈ scanList active 0 n →
      digits d v < 2 ^ Nat.clog 2 n)
    (hactiveKey : ∀ v : ActiveVertex n active,
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm v)).val =
        packedKey (2 ^ L) digits v.val.val) :
    ¬ HasAdjacentEqualDigits digits sorted := by
  intro hadj
  rcases hadj with ⟨j, hj₁, hjlen, hdigits⟩
  have hperm : List.Perm sorted (scanList active 0 n) := by
    rw [hsortedDef]
    exact radixSort8_perm (scanList_nodup active 0 n) hkeyBound
  have hnodup : sorted.Nodup := hperm.symm.nodup (scanList_nodup active 0 n)
  have hprev : j - 1 < sorted.length := by omega
  let u := sorted.getD (j - 1) 0
  let v := sorted.getD j 0
  have huGet : sorted.getD (j - 1) 0 = sorted[j - 1] :=
    List.getD_eq_getElem _ _ hprev
  have hvGet : sorted.getD j 0 = sorted[j] :=
    List.getD_eq_getElem _ _ hjlen
  have huMem : u ∈ scanList active 0 n := by
    change sorted.getD (j - 1) 0 ∈ scanList active 0 n
    rw [huGet]
    exact hperm.subset (List.getElem_mem hprev)
  have hvMem : v ∈ scanList active 0 n := by
    change sorted.getD j 0 ∈ scanList active 0 n
    rw [hvGet]
    exact hperm.subset (List.getElem_mem hjlen)
  have hpack : packedKey (2 ^ L) digits u = packedKey (2 ^ L) digits v := by
    unfold packedKey
    rw [(digitList_eq_iff).2 hdigits]
  have huSpec := mem_scanList.mp huMem
  have hvSpec := mem_scanList.mp hvMem
  let huActive : ActiveVertex n active := ⟨⟨u, by omega⟩, huSpec.2.2⟩
  let hvActive : ActiveVertex n active := ⟨⟨v, by omega⟩, hvSpec.2.2⟩
  have hpack' : packedKey (2 ^ L) digits huActive.val.val =
      packedKey (2 ^ L) digits hvActive.val.val := by
    simpa [huActive, hvActive] using hpack
  have hassignValue :
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm huActive)).val =
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm hvActive)).val := by
    calc
      _ = packedKey (2 ^ L) digits huActive.val.val := hactiveKey huActive
      _ = packedKey (2 ^ L) digits hvActive.val.val := hpack'
      _ = _ := (hactiveKey hvActive).symm
  have hassign :
      roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm huActive) =
      roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm hvActive) :=
    Fin.ext hassignValue
  have hindex := hinj hassign
  have huv : u = v := by
    have hvertices := congrArg (scanIndexEquiv active n) hindex
    simpa [huActive, hvActive] using
      congrArg (fun w : ActiveVertex n active => w.val.val) hvertices
  have hget : sorted.get ⟨j - 1, hprev⟩ = sorted.get ⟨j, hjlen⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    calc
      sorted[j - 1] = u := huGet.symm
      _ = v := huv
      _ = sorted[j] := hvGet
  have hsameIndex := (hnodup.get_inj_iff).mp hget
  have hsameIndexVal := congrArg Fin.val hsameIndex
  change j - 1 = j at hsameIndexVal
  omega

/-- For the canonical eight-slice reader of a binary source prefix, a block
outside the bad-round event yields a literal sorted-prefix sample that is
active, has the requested size, and avoids the graph's bad sample family.
The assignment-key equality is obtained from the source tape rather than
assumed as a separate premise. -/
lemma canonical_source_sample_good_of_nonfailing_bits
    {n L s : ℕ} {active : ℕ → ℕ} {source : List ℕ}
    (hL : 0 < L) (hn : 1 < n) (hclog : Nat.clog 2 n = L)
    (hsource : ∀ x ∈ source, x ≤ 1)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length)
    (original : Fin 8 → ℕ → ℕ)
    (bad : Finset (Finset (Fin n)))
    (hbound : ∀ v ∈ radixSort8 (2 ^ Nat.clog 2 n)
        (filledKey original active (scanTapeBits active L source) n)
        (scanList active 0 n),
      ∀ d, filledKey original active (scanTapeBits active L source) n d v <
        2 ^ Nat.clog 2 n)
    (hkeyBound : ∀ d v, v ∈ scanList active 0 n →
      filledKey original active (scanTapeBits active L source) n d v <
        2 ^ Nat.clog 2 n)
    (hs : s ≤ (activeVertices n active).card)
    (hgood : sourceBoolTape source (((activeVertices n active).card * 8) * L) ∉
      badRoundBits (activeVertices n active).card L s hL
        (badPositionSamples active n bad)) :
    let W := (radixSort8 (2 ^ Nat.clog 2 n)
        (filledKey original active (scanTapeBits active L source) n)
        (scanList active 0 n)).take s |>.toFinset
    let WFin := finSample n W
    WFin ⊆ activeFinset active ∧ WFin.card = s ∧ WFin ∉ bad := by
  let ρ := sourceBoolTape source (((activeVertices n active).card * 8) * L)
  let bits := scanTapeBits active L source
  let digits := filledKey original active bits n
  let sorted := radixSort8 (2 ^ Nat.clog 2 n) digits (scanList active 0 n)
  have hactiveKey : ∀ v : ActiveVertex n active,
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm v)).val =
      packedKey (2 ^ L) digits v.val.val := by
    intro v
    exact canonical_filledKey_activeKey hL hsource hlen original v
  obtain ⟨f, hf, _hnotbad⟩ :=
    good_assignment_of_not_badRoundBits (activeVertices n active).card L s hL
      (badPositionSamples active n bad) ρ hgood
  have hinj : Function.Injective (roundAssignmentEquiv
      (activeVertices n active).card L hL ρ) := by
    simpa [← hf] using f.2
  have hcollision : ¬ HasAdjacentEqualDigits digits sorted :=
    no_adjacent_equal_of_injective_assignment hL ρ hinj rfl hkeyBound hactiveKey
  have hresult := literal_sample_good_of_nonfailing_bits
    (n := n) (L := L) (s := s) (active := active)
    hL hn hclog ρ bad (digits := digits) (sorted := sorted)
    rfl hbound hkeyBound hcollision hactiveKey hs hgood
  simpa [ρ, bits, digits, sorted] using hresult

end

end Lax235315Proofs.Construction.CanonicalLiteralSampleGood
