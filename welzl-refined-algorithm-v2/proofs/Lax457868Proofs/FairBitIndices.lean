import Mathlib.Tactic
import Lax195003.WordRamRandomness
import Lax457868Proofs.SamplerRetries

/-!
Finite rejection sampling of an arbitrary positive finite index from fair bits.
Each block uses exactly `Nat.clog 2 m` bits, decodes them in the same order as
the Lax word-RAM bit tape, and rejects values outside `Fin m`. Repeated blocks
are represented by a finite function, so the selector below is explicitly
capped and samples with replacement.
-/

namespace Lax457868Proofs.FairBitIndices

open Lax457868Proofs.SamplerRetries

/-- Interpret a fair-bit block as a natural number, with the first tape bit
most significant. -/
def bitBlockValue {L : ℕ} (bits : Fin L → Bool) : ℕ :=
  Nat.ofDigits 2 (Lax195003.WordRamRandomness.bitTape bits).reverse

private lemma bitTape_length {L : ℕ} (bits : Fin L → Bool) :
    (Lax195003.WordRamRandomness.bitTape bits).length = L := by
  simp [Lax195003.WordRamRandomness.bitTape]

private lemma bitTape_digits_lt_two {L : ℕ} (bits : Fin L → Bool) :
    ∀ d ∈ Lax195003.WordRamRandomness.bitTape bits, d < 2 := by
  intro d hd
  simp only [Lax195003.WordRamRandomness.bitTape, List.mem_ofFn] at hd
  rcases hd with ⟨i, rfl⟩
  cases bits i <;> decide

/-- Every block decodes to a number in the range represented by its bit count. -/
lemma bitBlockValue_lt {L : ℕ} (bits : Fin L → Bool) :
    bitBlockValue bits < 2 ^ L := by
  unfold bitBlockValue
  have hlen : (Lax195003.WordRamRandomness.bitTape bits).reverse.length = L := by
    simp [bitTape_length]
  have hdigits : ∀ d ∈ (Lax195003.WordRamRandomness.bitTape bits).reverse, d < 2 := by
    intro d hd
    apply bitTape_digits_lt_two bits
    simpa using hd
  calc
    Nat.ofDigits 2 (Lax195003.WordRamRandomness.bitTape bits).reverse <
        2 ^ (Lax195003.WordRamRandomness.bitTape bits).reverse.length :=
      Nat.ofDigits_lt_base_pow_length (by decide) hdigits
    _ = 2 ^ L := by rw [hlen]

/-- Distinct bit blocks have distinct decoded values. -/
lemma bitBlockValue_injective {L : ℕ} :
    Function.Injective (bitBlockValue (L := L)) := by
  intro a b hab
  unfold bitBlockValue at hab
  have ha : (Lax195003.WordRamRandomness.bitTape a).reverse.length = L := by
    simp [bitTape_length]
  have hb : (Lax195003.WordRamRandomness.bitTape b).reverse.length = L := by
    simp [bitTape_length]
  have hbits := Nat.ofDigits_inj_of_len_eq (b := 2) (by decide)
    (ha.trans hb.symm)
    (by intro d hd; apply bitTape_digits_lt_two a; simpa using hd)
    (by intro d hd; apply bitTape_digits_lt_two b; simpa using hd)
    hab
  have hlist : Lax195003.WordRamRandomness.bitTape a =
      Lax195003.WordRamRandomness.bitTape b := List.reverse_inj.mp hbits
  have henc : (fun i : Fin L => if a i then 1 else 0) =
      (fun i : Fin L => if b i then 1 else 0) :=
    List.ofFn_inj.mp (by simpa [Lax195003.WordRamRandomness.bitTape] using hlist)
  funext i
  have hEq := congrFun henc i
  cases ha' : a i <;> cases hb' : b i <;> simp_all

/-- A bit block is exactly one of the `2^L` possible finite values. -/
noncomputable def bitBlockEquiv (L : ℕ) : (Fin L → Bool) ≃ Fin (2 ^ L) :=
  Equiv.ofBijective (fun bits => ⟨bitBlockValue bits, bitBlockValue_lt bits⟩) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · intro a b h
      apply bitBlockValue_injective
      exact congrArg Fin.val h
    · simp

/-- Decode one block by rejection into an arbitrary positive `Fin m` range. -/
def decodeBitIndex (m : ℕ) (_hm : 0 < m)
    (bits : Fin (Nat.clog 2 m) → Bool) : Option (Fin m) :=
  if h : bitBlockValue bits < m then some ⟨bitBlockValue bits, h⟩ else none

/-- A block is rejected precisely when its decoded natural number is outside
the requested range. -/
lemma decodeBitIndex_eq_none_iff (m : ℕ) (hm : 0 < m)
    (bits : Fin (Nat.clog 2 m) → Bool) :
    decodeBitIndex m hm bits = none ↔ bitBlockValue bits ≥ m := by
  simp [decodeBitIndex, Nat.not_lt]

/-- The accepted decoder returns exactly the value represented by the block. -/
lemma decodeBitIndex_eq_some_iff (m : ℕ) (hm : 0 < m)
    (bits : Fin (Nat.clog 2 m) → Bool) (i : Fin m) :
    decodeBitIndex m hm bits = some i ↔ bitBlockValue bits = i.val := by
  unfold decodeBitIndex
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · intro heq
      exact congrArg Fin.val heq
    · intro heq
      apply Fin.ext
      exact heq
  · rename_i h
    constructor
    · intro heq
      cases heq
    · intro heq
      exact False.elim (h (heq ▸ i.isLt))

/-- Every index has one and only one accepted bit block. -/
lemma accepted_block_unique (m : ℕ) (hm : 0 < m) (i : Fin m)
    {a b : Fin (Nat.clog 2 m) → Bool}
    (ha : decodeBitIndex m hm a = some i)
    (hb : decodeBitIndex m hm b = some i) : a = b := by
  apply bitBlockValue_injective
  rw [(decodeBitIndex_eq_some_iff m hm a i).mp ha,
      (decodeBitIndex_eq_some_iff m hm b i).mp hb]

/-- The left-to-right selector returns the first successfully decoded block. -/
def firstDecoded {α : Type*} : List (Option α) → Option α
  | [] => none
  | none :: rest => firstDecoded rest
  | some x :: _ => some x

/-- The finite scan fails exactly when every listed block is rejected. -/
lemma firstDecoded_eq_none_iff {α : Type*} (xs : List (Option α)) :
    firstDecoded xs = none ↔ ∀ x ∈ xs, x = none := by
  induction xs with
  | nil => simp [firstDecoded]
  | cons x xs ih => cases x <;> simp [firstDecoded, ih]

/-- Select the first accepted value among a finite tape of independent bit
blocks. -/
def selectBitIndex (m : ℕ) (hm : 0 < m) (t : ℕ)
    (tape : Fin t → (Fin (Nat.clog 2 m) → Bool)) : Option (Fin m) :=
  firstDecoded ((List.ofFn tape).map (decodeBitIndex m hm))

/-- A length-`t` block tape is an ordered sequence and therefore allows
repeated independent draws. -/
abbrev BitTape (m t : ℕ) := Fin t → (Fin (Nat.clog 2 m) → Bool)

/-- The clog-sized block has enough values to represent every element of
`Fin m`, including the boundary case `m = 1`, where the block is empty. -/
lemma index_lt_blockCount (m : ℕ) : m ≤ 2 ^ Nat.clog 2 m := by
  exact Nat.le_pow_clog (by decide) m

/-- Every accepted index is represented by a block, and that block is unique. -/
lemma accepted_block_exists (m : ℕ) (hm : 0 < m) (i : Fin m) :
    ∃ bits : Fin (Nat.clog 2 m) → Bool,
      decodeBitIndex m hm bits = some i := by
  have hcount := index_lt_blockCount m
  let bits := (bitBlockEquiv (Nat.clog 2 m)).symm
    ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩
  refine ⟨bits, (decodeBitIndex_eq_some_iff m hm bits i).2 ?_⟩
  change Fin.val ((bitBlockEquiv (Nat.clog 2 m)) bits) = i.val
  exact congrArg Fin.val ((bitBlockEquiv (Nat.clog 2 m)).apply_symm_apply
    ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩)

/-- The finite fiber of each accepted index consists of exactly one bit block. -/
lemma accepted_block_exactly_one (m : ℕ) (hm : 0 < m) (i : Fin m) :
    ∃! bits : Fin (Nat.clog 2 m) → Bool,
      decodeBitIndex m hm bits = some i := by
  obtain ⟨bits, hbits⟩ := accepted_block_exists m hm i
  exact ⟨bits, hbits, fun other hother =>
    accepted_block_unique m hm i hother hbits⟩

/-- Blocks decoding to a value below `m`. -/
def acceptedBlocks (m : ℕ) : Finset (Fin (Nat.clog 2 m) → Bool) :=
  Finset.univ.filter fun bits => bitBlockValue bits < m

/-- Blocks rejected because their decoded value is outside `Fin m`. -/
def rejectedBlocks (m : ℕ) : Finset (Fin (Nat.clog 2 m) → Bool) :=
  Finset.univ \ acceptedBlocks m

/-- Restricting the block equivalence to accepted values gives exactly `Fin m`. -/
noncomputable def acceptedBitEquiv (m : ℕ) (hm : 0 < m) :
    {bits : Fin (Nat.clog 2 m) → Bool // bitBlockValue bits < m} ≃ Fin m :=
  Equiv.ofBijective (fun bits => ⟨bitBlockValue bits.val, bits.property⟩) <| by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply bitBlockValue_injective
      exact congrArg Fin.val hab
    · intro i
      obtain ⟨bits, hbits⟩ := accepted_block_exists m hm i
      refine ⟨⟨bits, ?_⟩, ?_⟩
      · exact ((decodeBitIndex_eq_some_iff m hm bits i).mp hbits) ▸ i.isLt
      · apply Fin.ext
        exact (decodeBitIndex_eq_some_iff m hm bits i).mp hbits

/-- Exactly `m` blocks are accepted. -/
lemma card_acceptedBlocks (m : ℕ) (hm : 0 < m) :
    (acceptedBlocks m).card = m := by
  classical
  calc
    (acceptedBlocks m).card =
        Fintype.card {bits : Fin (Nat.clog 2 m) → Bool // bitBlockValue bits < m} := by
          symm
          exact Fintype.card_of_subtype (acceptedBlocks m) (by
            intro bits
            simp [acceptedBlocks, Finset.mem_filter])
    _ = Fintype.card (Fin m) := Fintype.card_congr (acceptedBitEquiv m hm)
    _ = m := Fintype.card_fin _

/-- The rejected blocks are precisely the excess values in the power-of-two
block space. -/
lemma card_rejectedBlocks (m : ℕ) (hm : 0 < m) :
    (rejectedBlocks m).card = 2 ^ Nat.clog 2 m - m := by
  classical
  unfold rejectedBlocks
  rw [Finset.card_sdiff]
  simp [card_acceptedBlocks m hm]

/-- Rejection occurs on at most half of all blocks for every positive `m`. -/
lemma rejectedBlocks_half (m : ℕ) (hm : 0 < m) :
    2 * (rejectedBlocks m).card ≤ Fintype.card (Fin (Nat.clog 2 m) → Bool) := by
  rw [card_rejectedBlocks m hm]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  let L := Nat.clog 2 m
  by_cases hL : L = 0
  · have hmle : m ≤ 1 := by
      have hlog : Nat.clog 2 m ≤ 0 := by simpa [L] using hL.le
      simpa using (Nat.clog_le_iff_le_pow (by decide)).1 hlog
    have htotal : 2 ^ Nat.clog 2 m = 1 := by
      change Nat.clog 2 m = 0 at hL
      rw [hL]
      norm_num
    rw [htotal]
    omega
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
    have hmgt : 1 < m := by
      by_contra h
      have hmone : m = 1 := by omega
      subst m
      simp [L] at hL
    have hprev : 2 ^ L.pred < m := by
      simpa [L] using Nat.pow_pred_clog_lt_self (by decide) hmgt
    have hsucc : L.pred + 1 = L := Nat.succ_pred_eq_of_pos hLpos
    have hpow : 2 ^ L = 2 ^ L.pred * 2 := by
      calc
        2 ^ L = 2 ^ (L.pred + 1) := by rw [hsucc]
        _ = 2 ^ L.pred * 2 := by simp [Nat.pow_succ]
    rw [hpow]
    have hcount := index_lt_blockCount m
    omega

/-- The finite block tapes on which every attempt is rejected. -/
def allRejectedBitTapes (m t : ℕ) : Finset (BitTape m t) :=
  allBadTapes (rejectedBlocks m) t

/-- The selector's failure event is exactly the all-rejected tape set counted
below. -/
lemma selectBitIndex_eq_none_iff (m : ℕ) (hm : 0 < m) (t : ℕ)
    (tape : BitTape m t) :
    selectBitIndex m hm t tape = none ↔ tape ∈ allRejectedBitTapes m t := by
  simp [selectBitIndex, firstDecoded_eq_none_iff, allRejectedBitTapes,
    allBadTapes, decodeBitIndex_eq_none_iff, rejectedBlocks, acceptedBlocks,
    Finset.mem_sdiff, Finset.mem_filter]

/-- The exact failure count is the rejected-block count raised to the cap. -/
lemma card_allRejectedBitTapes (m t : ℕ) :
    (allRejectedBitTapes m t).card = (rejectedBlocks m).card ^ t := by
  exact card_allBadTapes (rejectedBlocks m) t

/-- The probability of failing all `t` attempts is at most `2^-t`, expressed
as an integer inequality over the finite uniform tape space. -/
lemma failure_tail_bound (m : ℕ) (hm : 0 < m) (t : ℕ) :
    2 ^ t * (allRejectedBitTapes m t).card ≤ Fintype.card (BitTape m t) := by
  have hpow := Nat.pow_le_pow_left (rejectedBlocks_half m hm) t
  rw [Nat.mul_pow] at hpow
  rw [card_allRejectedBitTapes, card_tapes]
  simpa [BitTape, Nat.mul_assoc] using hpow

/-- The actual capped number of inspected bit blocks, including the final
accepted block when one is found. -/
def bitTapeAttemptsUsed (m t : ℕ) (tape : BitTape m t) : ℕ :=
  tapeAttemptsUsed (rejectedBlocks m) tape

/-- The mean capped number of inspected blocks is at most two, as a finite
sum inequality. -/
lemma sum_bitTapeAttemptsUsed_le_two (m : ℕ) (hm : 0 < m) (t : ℕ) :
    ∑ tape : BitTape m t, bitTapeAttemptsUsed m t tape ≤
      2 * Fintype.card (BitTape m t) := by
  change sumTapeAttemptsUsed (rejectedBlocks m) t ≤
    2 * Fintype.card (Fin t → (Fin (Nat.clog 2 m) → Bool))
  rw [card_tapes]
  exact sumTapeAttemptsUsed_le_two (rejectedBlocks m) t (rejectedBlocks_half m hm)

/-- Number of fair bits inspected by the finite selector. -/
def bitTapeReadBits (m t : ℕ) (tape : BitTape m t) : ℕ :=
  Nat.clog 2 m * bitTapeAttemptsUsed m t tape

/-- The finite mean bit-read count is at most twice the fixed block length,
expressed as a sum bound over all equally likely tapes. -/
lemma sum_bitTapeReadBits_le_two (m : ℕ) (hm : 0 < m) (t : ℕ) :
    ∑ tape : BitTape m t, bitTapeReadBits m t tape ≤
      2 * Nat.clog 2 m * Fintype.card (BitTape m t) := by
  calc
    ∑ tape : BitTape m t, bitTapeReadBits m t tape =
        Nat.clog 2 m * ∑ tape : BitTape m t, bitTapeAttemptsUsed m t tape := by
          simp [bitTapeReadBits, Finset.mul_sum]
    _ ≤ Nat.clog 2 m * (2 * Fintype.card (BitTape m t)) :=
      Nat.mul_le_mul_left _ (sum_bitTapeAttemptsUsed_le_two m hm t)
    _ = 2 * Nat.clog 2 m * Fintype.card (BitTape m t) := by ring

/-- The deterministic scan commutes with mapping every successful outcome. -/
lemma firstDecoded_map {α β : Type*} (f : α → β) (xs : List (Option α)) :
    firstDecoded (xs.map (Option.map f)) = (firstDecoded xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [firstDecoded, ih]

/-- Swap two accepted indices in a block while leaving rejected blocks alone. -/
noncomputable def swapBitBlock (m : ℕ) (hm : 0 < m) (i j : Fin m)
    (bits : Fin (Nat.clog 2 m) → Bool) : Fin (Nat.clog 2 m) → Bool :=
  if bitBlockValue bits = i.val then Classical.choose (accepted_block_exists m hm j)
  else if bitBlockValue bits = j.val then Classical.choose (accepted_block_exists m hm i)
  else bits

/-- The canonical chosen block decodes to its requested index. -/
lemma swapBitBlock_chosen_value (m : ℕ) (hm : 0 < m) (i : Fin m) :
    bitBlockValue (Classical.choose (accepted_block_exists m hm i)) = i.val := by
  exact (decodeBitIndex_eq_some_iff m hm _ i).mp
    (Classical.choose_spec (accepted_block_exists m hm i))

/-- Swapping accepted block labels is an involution on bit blocks. -/
lemma swapBitBlock_involutive (m : ℕ) (hm : 0 < m) (i j : Fin m)
    (bits : Fin (Nat.clog 2 m) → Bool) :
    swapBitBlock m hm i j (swapBitBlock m hm i j bits) = bits := by
  by_cases hi : bitBlockValue bits = i.val
  · have hcanon : bits = Classical.choose (accepted_block_exists m hm i) :=
      bitBlockValue_injective (hi.trans (swapBitBlock_chosen_value m hm i).symm)
    by_cases hij : i = j
    · subst j
      simp [swapBitBlock, hi, hcanon, swapBitBlock_chosen_value]
    · have hji : j.val ≠ i.val := by
        intro h
        exact hij (Fin.ext h).symm
      simp [swapBitBlock, hi, hji, hcanon, swapBitBlock_chosen_value]
  · by_cases hj : bitBlockValue bits = j.val
    · have hcanon : bits = Classical.choose (accepted_block_exists m hm j) :=
        bitBlockValue_injective (hj.trans (swapBitBlock_chosen_value m hm j).symm)
      have hji : j.val ≠ i.val := by
        intro h
        exact hi (hj.trans h)
      simp [swapBitBlock, hi, hj, hji, hcanon, swapBitBlock_chosen_value]
    · simp [swapBitBlock, hi, hj]

/-- The induced involution on ordered block tapes. -/
noncomputable def swapBitTape (m : ℕ) (hm : 0 < m) (i j : Fin m) (t : ℕ) :
    BitTape m t → BitTape m t :=
  fun tape k => swapBitBlock m hm i j (tape k)

/-- Decoding a swapped block applies the same transposition to its accepted
index, while a rejected block stays rejected. -/
lemma decode_swapBitBlock (m : ℕ) (hm : 0 < m) (i j : Fin m)
    (bits : Fin (Nat.clog 2 m) → Bool) :
    decodeBitIndex m hm (swapBitBlock m hm i j bits) =
      (decodeBitIndex m hm bits).map (fun k => if k = i then j else if k = j then i else k) := by
  by_cases hi : bitBlockValue bits = i.val
  · have hj : bitBlockValue (swapBitBlock m hm i j bits) = j.val := by
      simp [swapBitBlock, hi, swapBitBlock_chosen_value]
    rw [(decodeBitIndex_eq_some_iff m hm bits i).2 hi,
      (decodeBitIndex_eq_some_iff m hm _ j).2 hj]
    simp
  · by_cases hj : bitBlockValue bits = j.val
    · have hi' : bitBlockValue (swapBitBlock m hm i j bits) = i.val := by
        by_cases hij : i = j
        · subst j
          simp [swapBitBlock, hi, hj, swapBitBlock_chosen_value]
        · have hji : j.val ≠ i.val := by
            intro h
            exact hij (Fin.ext h).symm
          simp [swapBitBlock, hi, hj, hji, swapBitBlock_chosen_value]
      have hne : i ≠ j := by
        intro he
        subst j
        exact hi hj
      have hji : j ≠ i := fun h => hne h.symm
      rw [(decodeBitIndex_eq_some_iff m hm bits j).2 hj,
        (decodeBitIndex_eq_some_iff m hm _ i).2 hi']
      simp [hi, hne, hji]
    · by_cases hlt : bitBlockValue bits < m
      · let k : Fin m := ⟨bitBlockValue bits, hlt⟩
        have hki : k ≠ i := by intro he; apply hi; exact congrArg Fin.val he
        have hkj : k ≠ j := by intro he; apply hj; exact congrArg Fin.val he
        have hsame : swapBitBlock m hm i j bits = bits := by
          simp [swapBitBlock, hi, hj]
        rw [hsame, (decodeBitIndex_eq_some_iff m hm bits k).2 rfl]
        simp [hki, hkj]
      · have hnone : decodeBitIndex m hm bits = none := by
          simp [decodeBitIndex, hlt]
        have hsame : swapBitBlock m hm i j bits = bits := by
          simp [swapBitBlock, hi, hj]
        rw [hsame, hnone]
        simp

/-- Swapping all blocks transports the selected output by the same index swap. -/
def swapFinIndex {m : ℕ} (i j k : Fin m) : Fin m :=
  if k = i then j else if k = j then i else k

lemma swapFinIndex_apply_left {m : ℕ} (i j : Fin m) : swapFinIndex i j i = j := by
  simp [swapFinIndex]

lemma swapFinIndex_apply_right {m : ℕ} (i j : Fin m) : swapFinIndex i j j = i := by
  by_cases h : i = j
  · subst j
    simp [swapFinIndex]
  · have hji : j ≠ i := fun hji => h hji.symm
    simp [swapFinIndex, h, hji]

lemma selectBitIndex_swap (m : ℕ) (hm : 0 < m) (t : ℕ)
    (i j : Fin m) (tape : BitTape m t) :
    selectBitIndex m hm t (swapBitTape m hm i j t tape) =
      (selectBitIndex m hm t tape).map (swapFinIndex i j) := by
  unfold selectBitIndex swapBitTape
  have hblocks : List.ofFn (fun k => swapBitBlock m hm i j (tape k)) =
      (List.ofFn tape).map (swapBitBlock m hm i j) := by
    rw [List.map_ofFn]
    rfl
  rw [hblocks]
  have hmap : List.map (decodeBitIndex m hm)
      (List.map (swapBitBlock m hm i j) (List.ofFn tape)) =
      (List.ofFn tape).map (fun bits =>
        (decodeBitIndex m hm bits).map (swapFinIndex i j)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro bits hmem
    exact decode_swapBitBlock m hm i j bits
  rw [hmap]
  let f : Fin m → Fin m := swapFinIndex i j
  have hseq : (List.ofFn tape).map (fun bits =>
      (decodeBitIndex m hm bits).map f) =
      ((List.ofFn tape).map (decodeBitIndex m hm)).map (Option.map f) := by
    rw [List.map_map]
    rfl
  rw [hseq]
  exact firstDecoded_map f ((List.ofFn tape).map (decodeBitIndex m hm))

/-- Applying the block swap twice restores every ordered tape. -/
lemma swapBitTape_involutive (m : ℕ) (hm : 0 < m) (i j : Fin m) (t : ℕ)
    (tape : BitTape m t) :
    swapBitTape m hm i j t (swapBitTape m hm i j t tape) = tape := by
  funext k
  exact swapBitBlock_involutive m hm i j (tape k)

/-- The block swap is a permutation of the finite tape space. -/
noncomputable def swapBitTapeEquiv (m : ℕ) (hm : 0 < m) (i j : Fin m) (t : ℕ) :
    BitTape m t ≃ BitTape m t :=
  Equiv.ofBijective (swapBitTape m hm i j t) ⟨
    fun a b hab => by
      have h := congrArg (swapBitTape m hm i j t) hab
      simpa [swapBitTape_involutive] using h,
    fun b => ⟨swapBitTape m hm i j t b, swapBitTape_involutive m hm i j t b⟩⟩

/-- The finite set of tapes selecting a fixed index. -/
def indexFiber (m : ℕ) (hm : 0 < m) (t : ℕ) (i : Fin m) :
    Finset (BitTape m t) :=
  Finset.univ.filter fun tape => selectBitIndex m hm t tape = some i

/-- For every two output indices, a coordinatewise transposition gives a
bijection between their finite-cap tape fibers. -/
lemma card_indexFiber_eq (m : ℕ) (hm : 0 < m) (t : ℕ)
    (i j : Fin m) : (indexFiber m hm t i).card = (indexFiber m hm t j).card := by
  classical
  apply Finset.card_bij (s := indexFiber m hm t i) (t := indexFiber m hm t j)
    (fun tape _ => swapBitTape m hm i j t tape)
  · intro tape ht
    simp only [indexFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [selectBitIndex_swap, ht]
    simp [swapFinIndex]
  · intro a ha b hb hab
    have h := congrArg (swapBitTape m hm i j t) hab
    simpa [swapBitTape_involutive] using h
  · intro tape ht
    simp only [indexFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    refine ⟨swapBitTape m hm i j t tape, ?_, swapBitTape_involutive m hm i j t tape⟩
    rw [selectBitIndex_swap, ht]
    simp [swapFinIndex]

/-- Every requested output occurs on at least one tape whenever the cap is
positive, so the equal-fiber statement is a genuine conditional distribution. -/
lemma indexFiber_nonempty (m : ℕ) (hm : 0 < m) {t : ℕ} (ht : 0 < t)
    (i : Fin m) : (indexFiber m hm t i).Nonempty := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  obtain ⟨bits, hbits⟩ := accepted_block_exists m hm i
  let tape : BitTape m (n + 1) := Fin.cons bits (fun _ => fun _ => false)
  refine ⟨tape, ?_⟩
  simp only [indexFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [selectBitIndex, tape, List.ofFn_succ, firstDecoded, hbits]

end Lax457868Proofs.FairBitIndices
