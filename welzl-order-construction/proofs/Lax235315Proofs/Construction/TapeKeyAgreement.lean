import Lax235315Proofs.Construction.SortedKeySampleBridge
import Lax235315Proofs.Construction.RoundBitReader
import Lax235315Proofs.Construction.TapeBlocks
import Lax235315Proofs.Construction.ScanIndexEquiv
import Mathlib.Tactic

/-! The canonical bit slices selected by `SamplingFrontier.run` encode the
same finite random-key assignment as the literal scan tape. -/

namespace Lax235315Proofs.Construction.TapeKeyAgreement

open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.ScanIndexEquiv
open Lax235315Proofs.Construction.TapeBlocks
open Lax195003.WordRamRandomness

/-- Interpret a bounded natural-word tape prefix as a Boolean tape. -/
def sourceBoolTape (source : List ℕ) (r : ℕ) : Fin r → Bool :=
  fun i => decide (source.getD i.val 0 = 1)

lemma bitTape_sourceBoolTape_eq_take {source : List ℕ} {r : ℕ}
    (hsource : ∀ x ∈ source, x ≤ 1) (hr : r ≤ source.length) :
    bitTape (sourceBoolTape source r) = source.take r := by
  apply List.ext_getElem
  · simp [sourceBoolTape, bitTape, Nat.min_eq_left hr]
  · intro i hi₁ hi₂
    have hi : i < r := by
      simpa [List.length_take, Nat.min_eq_left hr] using hi₂
    have his : i < source.length := hi.trans_le hr
    have hbit := hsource source[i] (List.getElem_mem his)
    simp only [sourceBoolTape, bitTape, List.getElem_ofFn,
      List.getElem_take, List.getD_eq_getElem _ _ his]
    by_cases h : source[i] = 1
    · simp [h]
    · simp [h]
      omega

private lemma take_drop_prefix_eq {source : List ℕ} {r offset L : ℕ}
    (hr : r ≤ source.length) (hspan : offset + L ≤ r) :
    ((source.take r).drop offset).take L = (source.drop offset).take L := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, Nat.min_eq_left hr]
    omega
  · intro j hj₁ hj₂
    have hj := hj₁
    rw [List.length_take] at hj
    have hjL : j < L := hj.trans_le (Nat.min_le_left _ _)
    simp [List.getElem_take, List.getElem_drop]

private lemma scanList_active_decomp {active : ℕ → ℕ} {v n : ℕ}
    (hv : v < n) (hav : active v = 1) :
    scanList active 0 n =
      (scanList active 0 v ++ [v]) ++ scanList active (v + 1) (n - (v + 1)) := by
  have hn : n = (v + 1) + (n - (v + 1)) := by omega
  calc
    scanList active 0 n = scanList active 0 ((v + 1) + (n - (v + 1))) := by
      congr 1
    _ = scanList active 0 (v + 1) ++ scanList active (0 + (v + 1))
        (n - (v + 1)) := scanList_add active 0 (v + 1) (n - (v + 1))
    _ = (scanList active 0 v ++ [v]) ++ scanList active (v + 1)
        (n - (v + 1)) := by
      rw [Nat.zero_add, scanList_zero_add, if_pos hav]

/-- The inverse scan position of an active vertex is the number of active
vertices preceding it in the literal increasing scan. -/
lemma scanPosition_rank {active : ℕ → ℕ} {n : ℕ}
    (v : ActiveVertex n active) :
    ((scanIndexEquiv active n).symm v).val =
      (scanList active 0 v.val.val).length := by
  let i := (scanIndexEquiv active n).symm v
  let xs := scanList active 0 n
  let k := (scanList active 0 v.val.val).length
  have hi : (scanIndexEquiv active n i) = v :=
    Equiv.apply_symm_apply (scanIndexEquiv active n) v
  have hival : xs.getD i.val 0 = v.val.val := by
    have hv := (scanIndexEquiv_val active n i).symm
    rw [hi] at hv
    exact hv
  have hdecomp : xs =
      (scanList active 0 v.val.val ++ [v.val.val]) ++
        scanList active (v.val.val + 1) (n - (v.val.val + 1)) := by
    simpa [xs] using scanList_active_decomp v.val.isLt v.property
  have hk : k < xs.length := by
    rw [hdecomp]
    simp [k, List.length_append]
  have hgetDk : xs.getD k 0 = v.val.val :=
    scanList_active_getD v.val.isLt v.property
  have hvals : xs.getD i.val 0 = xs.getD k 0 := hival.trans hgetDk.symm
  have hi' : i.val < xs.length := by
    change i.val < (scanList active 0 n).length
    rw [scanList_length_eq_activeVertices_card]
    exact i.isLt
  have hget : xs.get ⟨i.val, by
      exact hi'⟩ = xs.get ⟨k, hk⟩ := by
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hk] at hvals
    exact hvals
  have hidx := (scanList_nodup active 0 n).get_inj_iff.mp hget
  have hidxVal := congrArg Fin.val hidx
  exact hidxVal

/-- The actual scan tape blocks at an active vertex are precisely the round
bit-reader slices for its inverse scan position. -/
lemma scanTapeBits_eq_roundSlices
    {active : ℕ → ℕ} {n L : ℕ} {source : List ℕ}
    (hsource : ∀ x ∈ source, x ≤ 1)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length)
    (v : ActiveVertex n active) :
    ∀ d : Fin 8,
      scanTapeBits active L source v.val.val d =
        digitBlock ((bitTape (sourceBoolTape source
          (((activeVertices n active).card * 8) * L))).drop
            (8 * L * ((scanIndexEquiv active n).symm v).val)) L d := by
  intro d
  let a := (activeVertices n active).card
  let r := (a * 8) * L
  have ha : a = (scanList active 0 n).length :=
    (scanList_length_eq_activeVertices_card active n).symm
  have hr : r = 8 * L * (scanList active 0 n).length := by
    simp [r, ha]
    ring
  have hrle : r ≤ source.length := by rw [hr]; exact hlen
  have hprefix := bitTape_sourceBoolTape_eq_take hsource hrle
  have hrank := scanPosition_rank v
  have hoff : 8 * L * ((scanIndexEquiv active n).symm v).val =
      8 * L * (scanList active 0 v.val.val).length := by rw [hrank]
  have hspan : 8 * L * ((scanIndexEquiv active n).symm v).val +
      (d.val + 1) * L ≤ r := by
    rw [hoff, hr]
    have hpref := scanList_active_getD v.val.isLt v.property
    have hprelen : (scanList active 0 v.val.val).length + 1 ≤
        (scanList active 0 n).length := by
      have hdecomp : scanList active 0 n =
          (scanList active 0 v.val.val ++ [v.val.val]) ++
            scanList active (v.val.val + 1) (n - (v.val.val + 1)) :=
        scanList_active_decomp v.val.isLt v.property
      rw [hdecomp]
      simp [List.length_append]
    have hd : d.val + 1 ≤ 8 := by omega
    nlinarith [Nat.mul_le_mul_left (8 * L) hprelen,
      Nat.mul_le_mul_right L hd]
  have hoff' : 8 * L * (scanList active 0 v.val.val).length + d.val * L + L ≤ r := by
    have := hspan
    nlinarith [this]
  rw [show scanTapeBits active L source v.val.val d =
      digitBlock (source.drop (8 * L * (scanList active 0 v.val.val).length)) L d by
        simp [scanTapeBits, v.property]]
  rw [hoff]
  unfold digitBlock
  rw [hprefix, List.drop_drop, List.drop_drop]
  exact (take_drop_prefix_eq hrle hoff').symm

/-- The global inverse-scan key agreement needed by the deterministic sample
bridge, for the canonical bits selected by `exists_scanTapeBits`. -/
lemma scanTapeBits_activeKey
    {active : ℕ → ℕ} {n L : ℕ} {source : List ℕ}
    (hL : 0 < L) (hsource : ∀ x ∈ source, x ≤ 1)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length)
    (original : Fin 8 → ℕ → ℕ) (v : ActiveVertex n active) :
    (roundAssignmentEquiv (activeVertices n active).card L hL
      (sourceBoolTape source (((activeVertices n active).card * 8) * L))
      ((scanIndexEquiv active n).symm v)).val =
      PackedKeys.packedKey (2 ^ L)
        (fun d w => ReadKeys.filledKey original active
          (scanTapeBits active L source) n d w) v.val.val := by
  let ρ := sourceBoolTape source (((activeVertices n active).card * 8) * L)
  let i := (scanIndexEquiv active n).symm v
  have hbits := scanTapeBits_eq_roundSlices hsource hlen v
  have hliteral := RoundBitReader.packedKey_digitBlocks_eq_roundAssignmentEquiv
    hL ρ i
  have hpacked :
      PackedKeys.packedKey (2 ^ L)
          (fun d _ => bitsValue
            (TapeBlocks.digitBlock ((bitTape ρ).drop
              (8 * L * i.val)) L d)) 0 =
        PackedKeys.packedKey (2 ^ L)
          (fun d w => ReadKeys.filledKey original active
            (scanTapeBits active L source) n d w) v.val.val := by
    unfold PackedKeys.packedKey
    congr 1
    simp [PackedKeys.digitList, ReadKeys.filledKey, v.val.isLt,
      v.property, hbits, ρ, i]
  calc
    _ = PackedKeys.packedKey (2 ^ L)
        (fun d _ => bitsValue
          (TapeBlocks.digitBlock ((bitTape ρ).drop (8 * L * i.val)) L d)) 0 :=
          hliteral.symm
    _ = PackedKeys.packedKey (2 ^ L)
        (fun d w => ReadKeys.filledKey original active
          (scanTapeBits active L source) n d w) v.val.val := hpacked

/-- The exact digit function used by `SamplingFrontier.run` has the
inverse-scan assignment key at every active vertex. The witness from
`exists_scanTapeBits` is this canonical `scanTapeBits` function, so this is
the `hactiveKey` premise for the sorted-prefix bridge. -/
lemma canonical_filledKey_activeKey
    {active : ℕ → ℕ} {n L : ℕ} {source : List ℕ}
    (hL : 0 < L) (hsource : ∀ x ∈ source, x ≤ 1)
    (hlen : 8 * L * (scanList active 0 n).length ≤ source.length)
    (original : Fin 8 → ℕ → ℕ) :
    ∀ v : ActiveVertex n active,
      (roundAssignmentEquiv (activeVertices n active).card L hL
        (sourceBoolTape source (((activeVertices n active).card * 8) * L))
        ((scanIndexEquiv active n).symm v)).val =
      PackedKeys.packedKey (2 ^ L)
        (fun d w => ReadKeys.filledKey original active
          (scanTapeBits active L source) n d w) v.val.val := by
  intro v
  exact scanTapeBits_activeKey hL hsource hlen original v

end Lax235315Proofs.Construction.TapeKeyAgreement
