import Mathlib.Tactic
import Lax457868Proofs.IndexedDrawBounds
import Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

/-!
The indexed fair-bit sampler can be interpreted through any duplicate-free
enumeration of a finite domain.  This file transports the existing counting
and work bounds to such enumerations, including the occupied-prefix array
invariant used by the reused RAM construction.

The finite product sample space below consists of independently allocated
retry tapes.  It does not model an adaptive sequence of domains or establish
independence for a single sequential flat tape.
-/

namespace Lax457868Proofs.EnumeratedDraws

open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.IndexedDraws
open Lax457868Proofs.IndexedDrawBounds
open Lax457868Proofs.SamplerUniformDraws
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

variable {α : Type*} [DecidableEq α]

/-- An enumeration of a finite domain, indexed by its cardinality. -/
abbrev DomainEnumeration (X : Finset α) := Fin X.card ≃ {x // x ∈ X}

/-- Convert the canonical list lookup into the caller's enumeration. -/
noncomputable def enumerationTransport (X : Finset α)
    (enum : DomainEnumeration X) : {x // x ∈ X} ≃ {x // x ∈ X} :=
  (indexedValueEquiv X).symm.trans enum

/-- Decode a fair-bit index through a caller-supplied enumeration. -/
noncomputable def selectEnumeratedDraw (X : Finset α) (hX : 0 < X.card)
    (t : ℕ) (enum : DomainEnumeration X) (bits : BitTape X.card t) :
    Option {x // x ∈ X} :=
  (selectIndexedDraw X hX t bits).map (enumerationTransport X enum)

/-- The enumerated selector is the indexed selector followed by `enum`. -/
lemma selectEnumeratedDraw_eq_map (X : Finset α) (hX : 0 < X.card)
    (t : ℕ) (enum : DomainEnumeration X) (bits : BitTape X.card t) :
    selectEnumeratedDraw X hX t enum bits =
      (selectIndexedDraw X hX t bits).map (enumerationTransport X enum) := by
  rfl

/-- The selected `Fin` index is interpreted directly by the supplied
enumeration. -/
lemma selectEnumeratedDraw_eq_selectedIndex (X : Finset α)
    (hX : 0 < X.card) (t : ℕ) (enum : DomainEnumeration X)
    (bits : BitTape X.card t) :
    selectEnumeratedDraw X hX t enum bits =
      (selectBitIndex X.card hX t bits).map enum := by
  unfold selectEnumeratedDraw selectIndexedDraw
  cases hs : selectBitIndex X.card hX t bits with
  | none => simp [hs, enumerationTransport]
  | some i =>
    simp only [hs, Option.map_some, Option.some.injEq]
    change enum ((indexedValueEquiv X).symm (indexedValue X i)) = enum i
    congr 1
    exact Equiv.symm_apply_apply (indexedValueEquiv X) i

/-- A specified enumerated result corresponds to its unique indexed result. -/
lemma selectEnumeratedDraw_eq_some_iff (X : Finset α) (hX : 0 < X.card)
    (t : ℕ) (enum : DomainEnumeration X) (bits : BitTape X.card t)
    (x : {x // x ∈ X}) :
    selectEnumeratedDraw X hX t enum bits = some x ↔
      selectIndexedDraw X hX t bits =
        some ((enumerationTransport X enum).symm x) := by
  rw [selectEnumeratedDraw_eq_map]
  cases hs : selectIndexedDraw X hX t bits with
  | none => simp [hs]
  | some j =>
    simp only [hs, Option.map_some, Option.some.injEq]
    change enum ((indexedValueEquiv X).symm j) = x ↔
      j = indexedValueEquiv X (enum.symm x)
    constructor
    · intro heq
      rw [← Equiv.apply_symm_apply enum x] at heq
      have hidx := enum.injective heq
      have hval := congrArg (indexedValueEquiv X) hidx
      simpa using hval
    · intro heq
      have hmap := congrArg (fun k => enum ((indexedValueEquiv X).symm k)) heq
      simpa using hmap

/-- Reindexing preserves whether a coordinate succeeds. -/
lemma selectEnumeratedDraw_succeeds_iff (X : Finset α) (hX : 0 < X.card)
    (t : ℕ) (enum : DomainEnumeration X) (bits : BitTape X.card t) :
    (∃ x, selectEnumeratedDraw X hX t enum bits = some x) ↔
      (∃ x, selectIndexedDraw X hX t bits = some x) := by
  rw [selectEnumeratedDraw_eq_map]
  cases hs : selectIndexedDraw X hX t bits <;> simp [hs]

/-- One batch of independent retry tapes, with outputs interpreted using an
arbitrary enumeration. -/
noncomputable def successfulEnumeratedDrawTape (X : Finset α)
    (hX : 0 < X.card) (r t : ℕ) (enum : DomainEnumeration X)
    (bits : DrawBitTape X r t) : Option (Tape X r) := by
  classical
  let draws : Fin r → Option {x // x ∈ X} :=
    fun i => selectEnumeratedDraw X hX t enum (bits i)
  if h : ∀ i, ∃ x, draws i = some x then
    exact some fun i => Classical.choose (h i)
  else
    exact none

/-- Each requested coordinate succeeds precisely according to the
enumerated selector. -/
lemma successfulEnumeratedDrawTape_eq_some_iff (X : Finset α)
    (hX : 0 < X.card) (r t : ℕ) (enum : DomainEnumeration X)
    (bits : DrawBitTape X r t) (draws : Tape X r) :
    successfulEnumeratedDrawTape X hX r t enum bits = some draws ↔
      ∀ i, selectEnumeratedDraw X hX t enum (bits i) = some (draws i) := by
  classical
  unfold successfulEnumeratedDrawTape
  let f : Fin r → Option {x // x ∈ X} :=
    fun i => selectEnumeratedDraw X hX t enum (bits i)
  change (if h : ∀ i, ∃ x, f i = some x then
      some (fun i => Classical.choose (h i)) else none) = some draws ↔
    ∀ i, f i = some (draws i)
  by_cases h : ∀ i, ∃ x, f i = some x
  · rw [dif_pos h]
    constructor
    · intro hout
      have hfun : (fun i => Classical.choose (h i)) = draws := Option.some.inj hout
      intro i
      rw [← hfun]
      exact Classical.choose_spec (h i)
    · intro hall
      have hfun : (fun i => Classical.choose (h i)) = draws := by
        funext i
        apply Option.some.inj
        exact (Classical.choose_spec (h i)).symm.trans (hall i)
      exact congrArg (fun f => some f) hfun
  · constructor
    · rw [dif_neg h]
      simp
    · intro hall
      have hall' : ∀ i, ∃ x, f i = some x := fun i => ⟨draws i, hall i⟩
      rw [dif_neg h]
      exact (h hall').elim

/-- Failure of the enumerated batch is unchanged by reindexing. -/
lemma successfulEnumeratedDrawTape_eq_none_iff (X : Finset α)
    (hX : 0 < X.card) (r t : ℕ) (enum : DomainEnumeration X)
    (bits : DrawBitTape X r t) :
    successfulEnumeratedDrawTape X hX r t enum bits = none ↔
      ¬ ∀ i, ∃ x, selectEnumeratedDraw X hX t enum (bits i) = some x := by
  classical
  unfold successfulEnumeratedDrawTape
  let f : Fin r → Option {x // x ∈ X} :=
    fun i => selectEnumeratedDraw X hX t enum (bits i)
  change (if h : ∀ i, ∃ x, f i = some x then
      some (fun i => Classical.choose (h i)) else none) = none ↔
    ¬ ∀ i, ∃ x, f i = some x
  by_cases h : ∀ i, ∃ x, f i = some x <;> simp [h]

/-- Tapes producing a specified ordered output under `enum`. -/
noncomputable def enumeratedDrawFiber (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (enum : DomainEnumeration X) (draws : Tape X r) :
    Finset (DrawBitTape X r t) :=
  drawFiber X hX r t (fun i =>
    indexedValueEquiv X (enum.symm (draws i)))

/-- The enumerated fiber is the existing indexed fiber at the corresponding
index tape. -/
lemma enumeratedDrawFiber_eq_indexed (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (enum : DomainEnumeration X) (draws : Tape X r) :
    enumeratedDrawFiber X hX r t enum draws =
      drawFiber X hX r t (fun i =>
        indexedValueEquiv X (enum.symm (draws i))) := rfl

/-- The enumerated fiber consists exactly of tapes whose successful batch
returns the requested outputs. -/
lemma mem_enumeratedDrawFiber_iff (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (enum : DomainEnumeration X) (draws : Tape X r)
    (bits : DrawBitTape X r t) :
    bits ∈ enumeratedDrawFiber X hX r t enum draws ↔
      successfulEnumeratedDrawTape X hX r t enum bits = some draws := by
  rw [successfulEnumeratedDrawTape_eq_some_iff]
  simp [enumeratedDrawFiber, drawFiber, selectEnumeratedDraw_eq_some_iff,
    enumerationTransport]

/-- Every enumerated outcome has the same fiber size as every other one. -/
lemma card_enumeratedDrawFiber_eq (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (enum : DomainEnumeration X) (a b : Tape X r) :
    (enumeratedDrawFiber X hX r t enum a).card =
      (enumeratedDrawFiber X hX r t enum b).card := by
  exact card_drawFiber_eq X hX r t
    (fun i => indexedValueEquiv X (enum.symm (a i)))
    (fun i => indexedValueEquiv X (enum.symm (b i)))

/-- When each coordinate has a retry block, every enumerated output has a
positive fiber. -/
lemma enumeratedDrawFiber_nonempty (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (enum : DomainEnumeration X) (ht : 0 < t)
    (draws : Tape X r) :
    (enumeratedDrawFiber X hX r t enum draws).Nonempty := by
  exact drawFiber_nonempty X hX r t ht
    (fun i => indexedValueEquiv X (enum.symm (draws i)))

/-- The failure event for arbitrary enumeration is exactly the indexed
failure event. -/
noncomputable def failedEnumeratedBatchSet (X : Finset α)
    (hX : 0 < X.card) (r t : ℕ) (enum : DomainEnumeration X) :
    Finset (DrawBitTape X r t) :=
  Finset.univ.filter fun bits =>
    successfulEnumeratedDrawTape X hX r t enum bits = none

/-- Reindexing preserves the complete failed-batch set. -/
lemma failedEnumeratedBatchSet_eq (X : Finset α)
    (hX : 0 < X.card) (r t : ℕ) (enum : DomainEnumeration X) :
    failedEnumeratedBatchSet X hX r t enum = failedBatchSet X hX r t := by
  classical
  ext bits
  simp only [failedEnumeratedBatchSet, failedBatchSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [successfulEnumeratedDrawTape_eq_none_iff,
      successfulDrawTape_eq_none_iff]
  simp_rw [selectEnumeratedDraw_succeeds_iff]

/-- The finite-batch rejection bound holds unchanged for every enumeration. -/
lemma failedEnumeratedBatch_count_bound (X : Finset α)
    (hX : 0 < X.card) (r t : ℕ) (enum : DomainEnumeration X) :
    2 ^ t * (failedEnumeratedBatchSet X hX r t enum).card ≤
      r * Fintype.card (DrawBitTape X r t) := by
  rw [failedEnumeratedBatchSet_eq]
  exact failedBatch_count_bound X hX r t

/-- Total bit reads retain the indexed sampler's read count; enumeration only
changes the interpretation of accepted indices. -/
def enumeratedBatchReadBits (X : Finset α) (r t : ℕ)
    (bits : DrawBitTape X r t) : ℕ := batchReadBits X r t bits

/-- The finite-product total read bound also holds for enumerated outputs. -/
lemma sum_enumeratedBatchReadBits_le_two (X : Finset α)
    (hX : 0 < X.card) (r t : ℕ) :
    ∑ bits : DrawBitTape X r t, enumeratedBatchReadBits X r t bits ≤
      2 * r * Nat.clog 2 X.card * Fintype.card (DrawBitTape X r t) := by
  simpa [enumeratedBatchReadBits] using sum_batchReadBits_le_two X hX r t

/-- The occupied prefix of an array gives a bijection from its positions to
the finite set it enumerates. -/
noncomputable def prefixIndexEquiv (height : ℕ) (entry : ℕ → ℕ)
    (X : Finset ℕ)
    (henum : PrefixEnumerates height entry X) :
    Fin height ≃ {x // x ∈ X} :=
  Equiv.ofBijective
    (fun i : Fin height =>
      (⟨entry i.val, (henum.2 (entry i.val)).mp (by
        change entry i.val ∈ (List.range height).map entry
        exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)⟩ :
        {x // x ∈ X})) (by
        constructor
        · intro i j hij
          apply Fin.ext
          apply PrefixEnumerates.injective_on_prefix henum i.val i.isLt j.val j.isLt
          exact congrArg Subtype.val hij
        · intro x
          have hx : x.val ∈
              Lax808846Proofs.Reasoning.Lib.Stack.toList height entry :=
            (henum.2 x.val).mpr x.property
          change x.val ∈ (List.range height).map entry at hx
          rcases List.mem_map.mp hx with ⟨i, hi, hentry⟩
          refine ⟨⟨i, List.mem_range.mp hi⟩, ?_⟩
          apply Subtype.ext
          exact hentry)

/-- A source `PrefixEnumerates` invariant with matching height and set size
therefore supplies the enumeration required by the fair-bit bridge. -/
def finEquivOfEq {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun i := ⟨i.val, h ▸ i.isLt⟩
  invFun i := ⟨i.val, h.symm ▸ i.isLt⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv i := by apply Fin.ext; rfl

/-- A duplicate-free occupied prefix has exactly as many positions as the
finite set it enumerates. -/
lemma prefixEnumerates_card (height : ℕ) (entry : ℕ → ℕ)
    (X : Finset ℕ) (henum : PrefixEnumerates height entry X) :
    height = X.card := by
  have hc := Fintype.card_congr (prefixIndexEquiv height entry X henum)
  simpa using hc

/-- A source `PrefixEnumerates` invariant itself supplies the enumeration
required by the fair-bit bridge. -/
noncomputable def prefixDomainEnumeration (height : ℕ) (entry : ℕ → ℕ)
    (X : Finset ℕ) (henum : PrefixEnumerates height entry X) : DomainEnumeration X :=
  (finEquivOfEq (prefixEnumerates_card height entry X henum).symm).trans
    (prefixIndexEquiv height entry X henum)

/-- Lookup through the enumeration reconstructed from the source array returns
the value stored at that occupied array position. -/
lemma prefixDomainEnumeration_lookup (height : ℕ) (entry : ℕ → ℕ)
    (X : Finset ℕ) (henum : PrefixEnumerates height entry X) (i : Fin height) :
    (prefixDomainEnumeration height entry X henum
      ⟨i.val, (prefixEnumerates_card height entry X henum) ▸ i.isLt⟩).val =
        entry i.val := by
  let hcard := prefixEnumerates_card height entry X henum
  change (prefixIndexEquiv height entry X henum
      (finEquivOfEq hcard.symm ⟨i.val, hcard ▸ i.isLt⟩)).val = entry i.val
  rfl

/-- On the source `PrefixEnumerates` array, the sampler's selected index is
looked up at that array position. -/
lemma selectPrefixArrayDraw_eq (height : ℕ) (entry : ℕ → ℕ)
    (X : Finset ℕ) (henum : PrefixEnumerates height entry X)
    (hX : 0 < X.card) (t : ℕ)
    (bits : BitTape X.card t) :
    selectEnumeratedDraw X hX t
        (prefixDomainEnumeration height entry X henum) bits =
      (selectBitIndex X.card hX t bits).map
        (prefixDomainEnumeration height entry X henum) := by
  exact selectEnumeratedDraw_eq_selectedIndex X hX t
    (prefixDomainEnumeration height entry X henum) bits

end Lax457868Proofs.EnumeratedDraws
