import Lax457868Proofs.FairBitRam

/-!
The finite rejection selector stops at its first accepted block.  These
lemmas split a capped tape at that block; the unread suffix is unrestricted.
-/

namespace Lax457868Proofs.StoppingPrefix

open FairBitIndices
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

private lemma firstDecodedWithCount_none_append {α : Type*}
    (xs ys : List (Option α)) (hxs : ∀ x ∈ xs, x = none) :
    firstDecodedWithCount (xs ++ ys) =
      ((firstDecodedWithCount ys).1, xs.length + (firstDecodedWithCount ys).2) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : x = none := hxs x (by simp)
      subst x
      have ht : ∀ z ∈ xs, z = none := by
        intro z hz
        exact hxs z (by simp [hz])
      simp [firstDecodedWithCount, ih ht, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

private lemma firstDecodedWithCount_append_single_iff {α : Type*}
    (xs : List (Option α)) (y : Option α) (i : α) :
    firstDecodedWithCount (xs ++ [y]) = (some i, xs.length + 1) ↔
      (∀ x ∈ xs, x = none) ∧ y = some i := by
  induction xs with
  | nil => cases y <;> simp [firstDecodedWithCount]
  | cons x xs ih =>
      cases x with
      | none =>
          rcases h : firstDecodedWithCount (xs ++ [y]) with ⟨a, b⟩
          simpa [firstDecodedWithCount, h] using ih
      | some z => simp [firstDecodedWithCount]

private lemma firstDecodedWithCount_pos {α : Type*}
    (xs : List (Option α)) (i : α)
    (h : (firstDecodedWithCount xs).1 = some i) :
    0 < (firstDecodedWithCount xs).2 := by
  induction xs with
  | nil => simp [firstDecodedWithCount] at h
  | cons x xs ih =>
      cases x <;> simp [firstDecodedWithCount] at *

private lemma firstDecodedWithCount_le_length {α : Type*}
    (xs : List (Option α)) :
    (firstDecodedWithCount xs).2 ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x <;> simp [firstDecodedWithCount] at *
      omega

private lemma firstDecodedWithCount_stopping_iff {α : Type*}
    (xs ys : List (Option α)) (y : Option α) (i : α) :
    firstDecodedWithCount (xs ++ y :: ys) = (some i, xs.length + 1) ↔
      (∀ x ∈ xs, x = none) ∧ y = some i := by
  induction xs with
  | nil =>
      cases y with
      | none =>
          constructor
          · intro h
            have hf : (firstDecodedWithCount ys).1 = some i :=
              congrArg Prod.fst h
            have hc : (firstDecodedWithCount ys).2 = 0 := by
              have hc' := congrArg Prod.snd h
              simp [firstDecodedWithCount] at hc'
              omega
            exact False.elim (by have hp := firstDecodedWithCount_pos ys i hf; omega)
          · simp
      | some z => simp [firstDecodedWithCount]
  | cons x xs ih =>
      cases x with
      | none =>
          rcases h : firstDecodedWithCount (xs ++ y :: ys) with ⟨a, b⟩
          simpa [firstDecodedWithCount, h] using ih
      | some z => simp [firstDecodedWithCount]

/-- A stopped draw is defined by the existing counted selector. -/
def stoppedEvent (m : ℕ) (hm : 0 < m) (t u : ℕ) (i : Fin m)
    (tape : BitTape m t) : Prop :=
  selectBitIndexWithCount m hm t tape = (some i, u)

/-- A reported successful stopping attempt lies within the cap and is
positive; in particular cap zero and attempt zero cannot report success. -/
lemma stoppedEvent_bounds (m : ℕ) (hm : 0 < m) (t u : ℕ)
    (i : Fin m) (tape : BitTape m t)
    (h : stoppedEvent m hm t u i tape) : 0 < u ∧ u ≤ t := by
  have hf : (selectBitIndexWithCount m hm t tape).1 = some i :=
    congrArg Prod.fst h
  have hc : (selectBitIndexWithCount m hm t tape).2 = u :=
    congrArg Prod.snd h
  have hp := firstDecodedWithCount_pos
    ((List.ofFn tape).map (decodeBitIndex m hm)) i hf
  have hl := firstDecodedWithCount_le_length
    ((List.ofFn tape).map (decodeBitIndex m hm))
  simp only [selectBitIndexWithCount] at hf hc
  simp only [List.length_map, List.length_ofFn] at hl
  omega

/-- All blocks before the accepted block are rejected. -/
def rejectedPrefix (m : ℕ) (hm : 0 < m) (v : ℕ)
    (pre : BitTape m v) : Prop :=
  ∀ j, decodeBitIndex m hm (pre j) = none

private lemma ofFn_snoc {α : Type*} {v : ℕ} (p : Fin v → α) (b : α) :
    List.ofFn (Fin.snoc p b) = List.ofFn p ++ [b] := by
  rw [List.ofFn_succ']
  simp

/-- The selector stops exactly after `v` rejected blocks followed by the
unique block for `i`.  In particular, this also covers `m = 1`, whose block
has zero bits. -/
lemma stoppedEvent_snoc_iff (m : ℕ) (hm : 0 < m) (v : ℕ) (i : Fin m)
    (pre : BitTape m v) (block : Fin (Nat.clog 2 m) → Bool) :
    stoppedEvent m hm (v + 1) (v + 1) i (Fin.snoc pre block) ↔
      rejectedPrefix m hm v pre ∧ decodeBitIndex m hm block = some i := by
  simp only [stoppedEvent, selectBitIndexWithCount, ofFn_snoc,
    List.map_append, List.map_cons, List.map_nil]
  have h := firstDecodedWithCount_append_single_iff
    ((List.ofFn pre).map (decodeBitIndex m hm))
    (decodeBitIndex m hm block) i
  simp only [List.length_map, List.length_ofFn] at h
  rw [h]
  simp [rejectedPrefix, List.mem_ofFn]

/-- Once a prefix has stopped, appending any later blocks leaves both the
selected index and the actual attempt count unchanged. -/
lemma stoppedEvent_append_iff (m : ℕ) (hm : 0 < m) (v r : ℕ) (i : Fin m)
    (pre : BitTape m (v + 1)) (suffix : BitTape m r) :
    stoppedEvent m hm (v + 1 + r) (v + 1) i (Fin.append pre suffix) ↔
      stoppedEvent m hm (v + 1) (v + 1) i pre := by
  induction pre using Fin.snocCases with
  | snoc p b =>
      simp only [stoppedEvent, selectBitIndexWithCount, List.ofFn_fin_append,
        ofFn_snoc, List.map_append, List.map_cons, List.map_nil]
      have hfull := firstDecodedWithCount_stopping_iff
        ((List.ofFn p).map (decodeBitIndex m hm))
        ((List.ofFn suffix).map (decodeBitIndex m hm))
        (decodeBitIndex m hm b) i
      have hpre := firstDecodedWithCount_append_single_iff
        ((List.ofFn p).map (decodeBitIndex m hm))
        (decodeBitIndex m hm b) i
      simp only [List.length_map, List.length_ofFn] at hfull hpre
      simpa [List.append_assoc] using hfull.trans hpre.symm

/-- The unread blocks in the source theorem's residual-input expression are
exactly the suffix after the accepted block, with no skipped retry blocks. -/
lemma source_residual_is_suffix (m v r : ℕ)
    (pre : BitTape m (v + 1)) (suffix : BitTape m r) :
    FairBitRam.flattenBitBlockList
      ((List.ofFn (Fin.append pre suffix)).drop (v + 1)) =
      FairBitRam.flattenBitBlocks suffix := by
  simp [List.ofFn_fin_append, FairBitRam.flattenBitBlockList_eq_flatMap,
    FairBitRam.flattenBitBlocks]

/-- The actual source command consumes exactly the stopped prefix and leaves
the flattened arbitrary suffix as its input for the next call. -/
lemma countedRejectionSelector_run_stopped
    {B n addr m v r : ℕ} {σ : Env} {g : ℕ → ℕ} {rest : List ℕ}
    (i : Fin m) (pre : BitTape m (v + 1)) (suffix : BitTape m r)
    (hm : 0 < m)
    (hp : stoppedEvent m hm (v + 1) (v + 1) i pre)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hv : σ.vars "v" = addr) (hvn : addr < n)
    (hL : σ.vars "L" = Nat.clog 2 m)
    (hmod : σ.vars "drawModulus" = m)
    (hcap : σ.vars "drawCap" = v + 1 + r)
    (hinp : σ.inp = FairBitRam.flattenBitBlocks (Fin.append pre suffix) ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B) (hnB : n < B) (htwoB : 2 < B)
    (htB : v + 1 + r < B) (hmB : m < B) :
    ∃ σ', Run B FairBitRam.countedRejectionSelector σ σ'
        ((15 * Nat.clog 2 m + 30) * (v + 1) + 12) ∧
      σ'.inp = FairBitRam.flattenBitBlocks suffix ++ rest ∧
      σ'.vars "drawUsed" = v + 1 ∧
      σ'.vars "drawFound" = 1 ∧
      σ'.vars "drawValue" = i.val := by
  let tape := Fin.append pre suffix
  have hs : stoppedEvent m hm (v + 1 + r) (v + 1) i tape :=
    (stoppedEvent_append_iff m hm v r i pre suffix).mpr hp
  have hcount : bitTapeAttemptsUsed m (v + 1 + r) tape = v + 1 := by
    have he := (selectBitIndexWithCount_eq m hm (v + 1 + r) tape).symm.trans hs
    exact congrArg Prod.snd he
  obtain ⟨σ', g', hrun, _, _, hselected, hused, hfound, hinput, _⟩ :=
    FairBitRam.countedRejectionSelector_run_tape tape hm hkey hv hvn
      hL hmod hcap hinp hpowB hnB htwoB htB hmB
  refine ⟨σ', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcount] using hrun
  · rw [hcount] at hinput
    simpa only [tape, source_residual_is_suffix] using hinput
  · simpa [hcount] using hused
  · change selectBitIndexWithCount m hm (v + 1 + r) tape =
        (some i, v + 1) at hs
    simpa [hs] using hfound
  · exact (hselected i (by simpa [tape] using congrArg Prod.fst hs)).2

/-- Splitting a tape after `u` blocks is a bijection with a prefix/suffix
pair; the inverse concatenates the two tapes without changing any block. -/
def splitTapeEquiv (m u r : ℕ) :
    BitTape m (u + r) ≃ BitTape m u × BitTape m r where
  toFun tape := (fun j => tape (Fin.castAdd r j),
    fun j => tape (Fin.natAdd u j))
  invFun pair := Fin.append pair.1 pair.2
  left_inv tape := Fin.append_castAdd_natAdd
  right_inv pair := by
    rcases pair with ⟨pre, suffix⟩
    simp [Fin.append_left, Fin.append_right]

/-- Full tapes stopping at block `v+1` are exactly stopped prefixes paired
with an arbitrary suffix. This equivalence is the finite conditional-uniformity
statement: for each stopped prefix every suffix occurs once. -/
noncomputable def stoppedEventSuffixEquiv (m : ℕ) (hm : 0 < m)
    (v r : ℕ) (i : Fin m) :
    {tape : BitTape m (v + 1 + r) //
      stoppedEvent m hm (v + 1 + r) (v + 1) i tape} ≃
      {pre : BitTape m (v + 1) //
        stoppedEvent m hm (v + 1) (v + 1) i pre} × BitTape m r where
  toFun tape :=
    (⟨(splitTapeEquiv m (v + 1) r tape.1).1, by
      have h := tape.2
      have heq : Fin.append (splitTapeEquiv m (v + 1) r tape.1).1
          (splitTapeEquiv m (v + 1) r tape.1).2 = tape.1 := by
        exact Fin.append_castAdd_natAdd
      rw [← heq] at h
      exact (stoppedEvent_append_iff m hm v r i _ _).mp h⟩,
      (splitTapeEquiv m (v + 1) r tape.1).2)
  invFun pair :=
    ⟨Fin.append pair.1.1 pair.2,
      (stoppedEvent_append_iff m hm v r i _ _).mpr pair.1.2⟩
  left_inv tape := by
    apply Subtype.ext
    exact (splitTapeEquiv m (v + 1) r).left_inv tape.1
  right_inv pair := by
    rcases pair with ⟨⟨pre, hp⟩, suffix⟩
    simp [splitTapeEquiv, Fin.append_left, Fin.append_right]

/-- Fixing a consumed prefix with its selected index and stopping count
leaves precisely one full successful tape for each possible suffix. -/
noncomputable def fixedPrefixSuffixEquiv (m : ℕ) (hm : 0 < m)
    (v r : ℕ) (i : Fin m) (pre : BitTape m (v + 1))
    (hp : stoppedEvent m hm (v + 1) (v + 1) i pre) :
    {tape : BitTape m (v + 1 + r) //
      stoppedEvent m hm (v + 1 + r) (v + 1) i tape ∧
        (splitTapeEquiv m (v + 1) r tape).1 = pre} ≃ BitTape m r where
  toFun tape := (splitTapeEquiv m (v + 1) r tape.1).2
  invFun suffix := ⟨Fin.append pre suffix,
    ⟨(stoppedEvent_append_iff m hm v r i pre suffix).mpr hp, by
      simp [splitTapeEquiv, Fin.append_left]⟩⟩
  left_inv tape := by
    apply Subtype.ext
    have hpre := tape.2.2
    have hsplit := (splitTapeEquiv m (v + 1) r).left_inv tape.1
    change Fin.append (splitTapeEquiv m (v + 1) r tape.1).1
      (splitTapeEquiv m (v + 1) r tape.1).2 = tape.1 at hsplit
    simpa [← hpre] using hsplit
  right_inv suffix := by
    simp [splitTapeEquiv, Fin.append_right]

/-- Each fixed successful prefix has the full number of suffixes, an exact
finite formulation of freshness after stopping. -/
lemma card_fixedPrefixSuffix (m : ℕ) (hm : 0 < m)
    (v r : ℕ) (i : Fin m) (pre : BitTape m (v + 1))
    (hp : stoppedEvent m hm (v + 1) (v + 1) i pre) :
    Nat.card {tape : BitTape m (v + 1 + r) //
      stoppedEvent m hm (v + 1 + r) (v + 1) i tape ∧
        (splitTapeEquiv m (v + 1) r tape).1 = pre} =
      (2 ^ Nat.clog 2 m) ^ r := by
  rw [Nat.card_congr (fixedPrefixSuffixEquiv m hm v r i pre hp),
    Nat.card_eq_fintype_card]
  simp [BitTape]

/-- Exact factorization of the full stopped event into a stopped prefix and
all possible suffix tapes. -/
lemma card_stoppedEvent_factor (m : ℕ) (hm : 0 < m)
    (v r : ℕ) (i : Fin m) :
    Nat.card {tape : BitTape m (v + 1 + r) //
      stoppedEvent m hm (v + 1 + r) (v + 1) i tape} =
    Nat.card {pre : BitTape m (v + 1) //
      stoppedEvent m hm (v + 1) (v + 1) i pre} *
        Nat.card (BitTape m r) := by
  rw [Nat.card_congr (stoppedEventSuffixEquiv m hm v r i)]
  exact Nat.card_prod _ _

private noncomputable def acceptedBitBlock (m : ℕ) (hm : 0 < m)
    (i : Fin m) : Fin (Nat.clog 2 m) → Bool :=
  Classical.choose (accepted_block_exists m hm i)

private lemma acceptedBitBlock_ok (m : ℕ) (hm : 0 < m) (i : Fin m) :
    decodeBitIndex m hm (acceptedBitBlock m hm i) = some i :=
  Classical.choose_spec (accepted_block_exists m hm i)

/-- A stopped prefix is determined by its `v` rejected blocks: its last
block is the unique encoding of the selected index. -/
noncomputable def stoppedPrefixRejectedEquiv (m : ℕ) (hm : 0 < m)
    (v : ℕ) (i : Fin m) :
    {pre : BitTape m (v + 1) //
      stoppedEvent m hm (v + 1) (v + 1) i pre} ≃
    {bad : BitTape m v // rejectedPrefix m hm v bad} where
  toFun pre := ⟨Fin.init pre.1, by
    have hs := (stoppedEvent_snoc_iff m hm v i
      (Fin.init pre.1) (pre.1 (Fin.last v))).mp (by
        simpa only [Fin.snoc_init_self] using pre.2)
    exact hs.1⟩
  invFun bad := ⟨Fin.snoc bad.1 (acceptedBitBlock m hm i),
    (stoppedEvent_snoc_iff m hm v i bad.1 (acceptedBitBlock m hm i)).mpr
      ⟨bad.2, acceptedBitBlock_ok m hm i⟩⟩
  left_inv pre := by
    apply Subtype.ext
    have hs := (stoppedEvent_snoc_iff m hm v i
      (Fin.init pre.1) (pre.1 (Fin.last v))).mp (by
        simpa only [Fin.snoc_init_self] using pre.2)
    have hlast := accepted_block_unique m hm i hs.2
      (acceptedBitBlock_ok m hm i)
    simpa [hlast] using (Fin.snoc_init_self pre.1)
  right_inv bad := by
    apply Subtype.ext
    simp

private lemma rejectedPrefix_iff_allRejected (m : ℕ) (hm : 0 < m)
    (v : ℕ) (bad : BitTape m v) :
    rejectedPrefix m hm v bad ↔ bad ∈ allRejectedBitTapes m v := by
  simp [rejectedPrefix, allRejectedBitTapes, SamplerRetries.allBadTapes,
    decode_rejected_iff m hm]

private noncomputable def rejectedPrefixAllRejectedEquiv (m : ℕ)
    (hm : 0 < m) (v : ℕ) :
    {bad : BitTape m v // rejectedPrefix m hm v bad} ≃
    {bad : BitTape m v // bad ∈ allRejectedBitTapes m v} where
  toFun bad := ⟨bad.1, (rejectedPrefix_iff_allRejected m hm v bad.1).mp bad.2⟩
  invFun bad := ⟨bad.1, (rejectedPrefix_iff_allRejected m hm v bad.1).mpr bad.2⟩
  left_inv bad := by cases bad; rfl
  right_inv bad := by cases bad; rfl

/-- The exact number of stopped prefixes is the number of choices for the
rejected blocks. This includes `v = 0` and `m = 1`. -/
lemma card_stoppedPrefix (m : ℕ) (hm : 0 < m) (v : ℕ) (i : Fin m) :
    Nat.card {pre : BitTape m (v + 1) //
      stoppedEvent m hm (v + 1) (v + 1) i pre} =
      (rejectedBlocks m).card ^ v := by
  rw [Nat.card_congr (stoppedPrefixRejectedEquiv m hm v i),
    Nat.card_congr (rejectedPrefixAllRejectedEquiv m hm v),
    Nat.card_eq_fintype_card, Fintype.card_coe, card_allRejectedBitTapes]

/-- For a tape of `v+1+r` blocks, success at attempt `v+1` with index `i`
has exactly `rejectedBlocks.card^v * blockCount^r` realizations. The suffix
factor is the complete, unrestricted tape space. -/
lemma card_stoppedEvent (m : ℕ) (hm : 0 < m)
    (v r : ℕ) (i : Fin m) :
    Nat.card {tape : BitTape m (v + 1 + r) //
      stoppedEvent m hm (v + 1 + r) (v + 1) i tape} =
    (rejectedBlocks m).card ^ v *
      (2 ^ Nat.clog 2 m) ^ r := by
  rw [card_stoppedEvent_factor, card_stoppedPrefix,
    Nat.card_eq_fintype_card]
  simp [BitTape]

private lemma firstDecodedWithCount_none_of_all {α : Type*}
    (xs : List (Option α)) (h : ∀ x ∈ xs, x = none) :
    firstDecodedWithCount xs = (none, xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : x = none := h x (by simp)
      subst x
      have ht : ∀ y ∈ xs, y = none := by
        intro y hy
        exact h y (by simp [hy])
      simp [firstDecodedWithCount, ih ht]

/-- Complete rejection returns `none` and consumes all `t` blocks. The
reverse implication also identifies precisely the existing failure event. -/
lemma selector_complete_rejection_iff (m : ℕ) (hm : 0 < m)
    (t : ℕ) (tape : BitTape m t) :
    selectBitIndexWithCount m hm t tape = (none, t) ↔
      tape ∈ allRejectedBitTapes m t := by
  constructor
  · intro h
    have hf : selectBitIndex m hm t tape = none := by
      have hh := congrArg Prod.fst h
      simpa [selectBitIndexWithCount_eq m hm t tape] using hh
    exact (selectBitIndex_eq_none_iff m hm t tape).mp hf
  · intro h
    have hb : ∀ j, decodeBitIndex m hm (tape j) = none :=
      (rejectedPrefix_iff_allRejected m hm t tape).mpr h
    unfold selectBitIndexWithCount
    have hall : ∀ x ∈ (List.ofFn tape).map (decodeBitIndex m hm), x = none := by
      simpa [List.mem_ofFn] using hb
    simpa using firstDecodedWithCount_none_of_all _ hall

/-- With cap zero no block is inspected, so no success event exists. -/
lemma selector_zero (m : ℕ) (hm : 0 < m) (tape : BitTape m 0) :
    selectBitIndexWithCount m hm 0 tape = (none, 0) := by
  simp [selectBitIndexWithCount, firstDecodedWithCount]

/-- At domain size one the block width is zero and the sole index is
accepted immediately; later zero-width blocks remain untouched. -/
lemma card_stoppedEvent_one (v r : ℕ) :
    Nat.card {tape : BitTape 1 (v + 1 + r) //
      stoppedEvent 1 (by decide) (v + 1 + r) (v + 1) (0 : Fin 1) tape} =
      if v = 0 then 1 else 0 := by
  rw [card_stoppedEvent]
  have hr : (rejectedBlocks 1).card = 0 := by
    simpa using card_rejectedBlocks 1 (by decide)
  by_cases hv : v = 0 <;> simp [hr, hv]

end Lax457868Proofs.StoppingPrefix
