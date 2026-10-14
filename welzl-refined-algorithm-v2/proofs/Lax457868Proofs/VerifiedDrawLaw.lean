import Mathlib.Tactic
import Lax457868Proofs.EnumeratedDraws
import Lax457868Proofs.IndexedDrawRam

/-!
The concrete single-draw RAM command has the same finite output law as the
enumerated fair-bit selector. This statement concerns one fixed domain and a
finite independent retry tape; it does not assert an adaptive flat-tape law.
-/

namespace Lax457868Proofs.VerifiedDrawLaw

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FairBitRam
open Lax457868Proofs.IndexedDrawRam
open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- Fixed state and machine preconditions for one actual source draw. The
array prefix enumerates exactly the active domain `X`; the bit tape is the
only varying input. -/
structure DrawContext (X : Finset ℕ) where
  B : ℕ
  n : ℕ
  v : ℕ
  t : ℕ
  domainCap : ℕ
  base : Env
  key : ℕ → ℕ
  domain : ℕ → ℕ
  rest : List ℕ
  domainNonempty : 0 < X.card
  domainEnum : PrefixEnumerates X.card domain X
  domainCapacity : X.card ≤ domainCap
  keyArray : base.arrs "key0" = arrOf n key
  domainArray : base.arrs "drawDomain" = arrOf domainCap domain
  domainValuesBounded : ∀ i < X.card, domain i < B
  keyCell : base.vars "v" = v
  keyCellBounded : v < n
  bitWidth : base.vars "L" = Nat.clog 2 X.card
  modulus : base.vars "drawModulus" = X.card
  retryCap : base.vars "drawCap" = t
  bitRangeBounded : 2 ^ Nat.clog 2 X.card < B
  keyLengthBounded : n < B
  twoBounded : 2 < B
  capBounded : t < B
  domainSizeBounded : X.card < B

/-- Install a finite fair-bit tape as the input of the fixed RAM state. -/
def initialWithTape {X : Finset ℕ} (C : DrawContext X)
    (tape : BitTape X.card C.t) : Env :=
  { C.base with inp := flattenBitBlocks tape ++ C.rest }

/-- The source command's bound for the run on a particular retry tape. -/
def sourceDrawCost {X : Finset ℕ} (C : DrawContext X)
    (tape : BitTape X.card C.t) : ℕ :=
  (15 * Nat.clog 2 X.card + 30) *
    bitTapeAttemptsUsed X.card C.t tape + 19

/-- The sum of the valid per-run source cost upper bounds over all retry
tapes is at most `(30 * clog2 |X| + 79)` times the tape-space size. This is
a finite mean-cost bound, not a claim that these upper bounds are exact run
times. -/
lemma sum_sourceDrawCost_le {X : Finset ℕ} (C : DrawContext X) :
    ∑ tape : BitTape X.card C.t, sourceDrawCost C tape ≤
      (30 * Nat.clog 2 X.card + 79) * Fintype.card (BitTape X.card C.t) := by
  classical
  let N := Fintype.card (BitTape X.card C.t)
  have hsum :
      ∑ tape : BitTape X.card C.t, sourceDrawCost C tape =
        (15 * Nat.clog 2 X.card + 30) *
          (∑ tape : BitTape X.card C.t,
            bitTapeAttemptsUsed X.card C.t tape) + 19 * N := by
    simp [sourceDrawCost, Finset.sum_add_distrib, Finset.mul_sum, N]; ring
  have hattempts := sum_bitTapeAttemptsUsed_le_two X.card
    C.domainNonempty C.t
  rw [hsum]
  calc
    (15 * Nat.clog 2 X.card + 30) *
        (∑ tape : BitTape X.card C.t,
          bitTapeAttemptsUsed X.card C.t tape) + 19 * N
      ≤ (15 * Nat.clog 2 X.card + 30) * (2 * N) + 19 * N := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left _ hattempts) _
    _ = (30 * Nat.clog 2 X.card + 79) *
          Fintype.card (BitTape X.card C.t) := by
        simp only [N]
        ring

/-- Tapes on which the actual IMP+ source command finishes with `x` as its
draw result. -/
noncomputable def sourceDrawEvent {X : Finset ℕ} (C : DrawContext X)
    (x : {x // x ∈ X}) : Finset (BitTape X.card C.t) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ final : Env,
      Run C.B (seqs [countedRejectionSelector, indexedDrawLookup])
        (initialWithTape C tape) final (sourceDrawCost C tape) ∧
      final.vars "drawFound" = 1 ∧ final.vars "drawVertex" = x.val

/-- Run the concrete selector and array lookup from the fixed context. -/
lemma sourceDraw_run {X : Finset ℕ} (C : DrawContext X)
    (tape : BitTape X.card C.t) :
    ∃ final,
      Run C.B (seqs [countedRejectionSelector, indexedDrawLookup])
        (initialWithTape C tape) final (sourceDrawCost C tape) ∧
      (∀ i, (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 = some i →
        final.vars "drawVertex" = C.domain i.val) ∧
      ((selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 = none →
        final.vars "drawVertex" = C.base.vars "drawVertex") ∧
      final.vars "drawFound" =
        (if (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 = none
          then 0 else 1) := by
  obtain ⟨final, key', hrun, hkey, hframe, hselected, hnone,
      hused, hfound, hinp, hdomain, harrframe, hv, hL, hmod, hcap⟩ :=
    countedIndexedDraw_run_tape (B := C.B) (n := C.n) (v := C.v)
      (m := X.card) (domainCap := C.domainCap) (t := C.t)
      (σ := initialWithTape C tape) (g := C.key) (domain := C.domain)
      (rest := C.rest) tape C.domainNonempty
      (by simpa [initialWithTape] using C.keyArray)
      (by simpa [initialWithTape] using C.domainArray) C.domainCapacity
      C.domainValuesBounded C.keyCell C.keyCellBounded C.bitWidth C.modulus
      C.retryCap (by simp [initialWithTape]) C.bitRangeBounded C.keyLengthBounded C.twoBounded
      C.capBounded C.domainSizeBounded
  refine ⟨final, ?_, hselected, hnone, hfound⟩
  simpa [initialWithTape, sourceDrawCost] using hrun

/-- An enumerated output `x` is produced exactly when the selected index is
the unique position assigned to `x` by the enumeration. -/
lemma selectEnumeratedDraw_eq_some_iff_index {X : Finset ℕ}
    (hX : 0 < X.card) (t : ℕ) (enum : DomainEnumeration X)
    (tape : BitTape X.card t) (x : {x // x ∈ X}) :
    selectEnumeratedDraw X hX t enum tape = some x ↔
      selectBitIndex X.card hX t tape = some (enum.symm x) := by
  rw [selectEnumeratedDraw_eq_selectedIndex]
  cases hi : selectBitIndex X.card hX t tape with
  | none => simp
  | some i =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro hx
      have hx' := congrArg enum.symm hx
      simpa using hx'
    · intro hindex
      have hx' := congrArg enum hindex
      simpa using hx'

/-- The source event is exactly the fair-bit selector's event under the
array-derived enumeration. -/
lemma sourceDrawEvent_iff_selector {X : Finset ℕ} (C : DrawContext X)
    (x : {x // x ∈ X}) (tape : BitTape X.card C.t) :
    tape ∈ sourceDrawEvent C x ↔
      selectEnumeratedDraw X C.domainNonempty C.t
        (prefixDomainEnumeration X.card C.domain X C.domainEnum) tape = some x := by
  classical
  simp only [sourceDrawEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨final, hsource, hfound, hvertex⟩
    obtain ⟨expected, hexpected, hselected, hnone, hfoundExpected⟩ :=
      sourceDraw_run C tape
    obtain ⟨_, _, hbs⟩ := hsource.bigStep
    obtain ⟨_, _, hbsExpected⟩ := hexpected.bigStep
    have hfinal : final = expected := (BigStep.unique hbs hbsExpected).1
    rw [hfinal] at hfound hvertex
    cases hindexCount :
        (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 with
    | none =>
      rw [hindexCount] at hfoundExpected
      simp at hfoundExpected
      rw [hfoundExpected] at hfound
      norm_num at hfound
    | some i =>
      have hselectedI := hselected i hindexCount
      have hdomain : C.domain i.val = x.val := hselectedI.symm.trans hvertex
      have hcountEq :
          (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 =
            selectBitIndex X.card C.domainNonempty C.t tape := by
        simpa using congrArg Prod.fst
          (selectBitIndexWithCount_eq X.card C.domainNonempty C.t tape)
      have hindex : selectBitIndex X.card C.domainNonempty C.t tape = some i := by
        rw [← hcountEq]
        exact hindexCount
      let enum := prefixDomainEnumeration X.card C.domain X C.domainEnum
      have hlookup := prefixDomainEnumeration_lookup X.card C.domain X
        C.domainEnum i
      have henumeq : enum i = x := by
        apply Subtype.ext
        exact hlookup.trans hdomain
      rw [selectEnumeratedDraw_eq_selectedIndex]
      simp [hindex, enum, henumeq]
  · intro hselector
    let enum := prefixDomainEnumeration X.card C.domain X C.domainEnum
    have hindex : selectBitIndex X.card C.domainNonempty C.t tape = some (enum.symm x) :=
      (selectEnumeratedDraw_eq_some_iff_index C.domainNonempty C.t enum tape x).mp hselector
    obtain ⟨final, hrun, hselected, hnone, hfound⟩ := sourceDraw_run C tape
    have hcountEq :
        (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 =
          selectBitIndex X.card C.domainNonempty C.t tape := by
      simpa using congrArg Prod.fst
        (selectBitIndexWithCount_eq X.card C.domainNonempty C.t tape)
    have hindexCount :
        (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 =
          some (enum.symm x) := by
      rw [hcountEq]
      exact hindex
    have hfound' : final.vars "drawFound" = 1 := by
      simpa [hindexCount] using hfound
    have hlookup := prefixDomainEnumeration_lookup X.card C.domain X
      C.domainEnum (enum.symm x)
    have hdomain : C.domain (enum.symm x).val = x.val := by
      exact hlookup.symm.trans
        (congrArg Subtype.val (Equiv.apply_symm_apply enum x))
    have hvertex : final.vars "drawVertex" = x.val :=
      (hselected (enum.symm x) hindexCount).trans hdomain
    exact ⟨final, hrun, hfound', hvertex⟩

/-- The concrete source output fiber is the corresponding decoded-index
fiber. -/
lemma sourceDrawEvent_eq_indexFiber {X : Finset ℕ} (C : DrawContext X)
    (x : {x // x ∈ X}) :
    sourceDrawEvent C x =
      indexFiber X.card C.domainNonempty C.t
        ((prefixDomainEnumeration X.card C.domain X C.domainEnum).symm x) := by
  classical
  ext tape
  simp only [sourceDrawEvent_iff_selector,
    selectEnumeratedDraw_eq_some_iff_index, indexFiber, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Every pair of actual source output events has the same number of fair-bit
input tapes. -/
lemma sourceDrawEvent_card_eq {X : Finset ℕ} (C : DrawContext X)
    (x y : {x // x ∈ X}) :
    (sourceDrawEvent C x).card = (sourceDrawEvent C y).card := by
  rw [sourceDrawEvent_eq_indexFiber, sourceDrawEvent_eq_indexFiber]
  exact card_indexFiber_eq X.card C.domainNonempty C.t
    ((prefixDomainEnumeration X.card C.domain X C.domainEnum).symm x)
    ((prefixDomainEnumeration X.card C.domain X C.domainEnum).symm y)

/-- With at least one retry block, each actual source output event is
nonempty. -/
lemma sourceDrawEvent_nonempty {X : Finset ℕ} (C : DrawContext X)
    (ht : 0 < C.t) (x : {x // x ∈ X}) : (sourceDrawEvent C x).Nonempty := by
  rw [sourceDrawEvent_eq_indexFiber]
  exact indexFiber_nonempty X.card C.domainNonempty ht
    ((prefixDomainEnumeration X.card C.domain X C.domainEnum).symm x)

/-- Tapes on which the actual source command finishes without finding a
draw. -/
noncomputable def sourceDrawExhaustionEvent {X : Finset ℕ}
    (C : DrawContext X) : Finset (BitTape X.card C.t) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ final : Env,
      Run C.B (seqs [countedRejectionSelector, indexedDrawLookup])
        (initialWithTape C tape) final (sourceDrawCost C tape) ∧
      final.vars "drawFound" = 0

/-- Source-command exhaustion is exactly selector rejection. -/
lemma sourceDrawExhaustionEvent_iff_none {X : Finset ℕ}
    (C : DrawContext X) (tape : BitTape X.card C.t) :
    tape ∈ sourceDrawExhaustionEvent C ↔
      selectBitIndex X.card C.domainNonempty C.t tape = none := by
  classical
  simp only [sourceDrawExhaustionEvent, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨final, hsource, hfound⟩
    obtain ⟨expected, hexpected, _, _, hfoundExpected⟩ := sourceDraw_run C tape
    obtain ⟨_, _, hbs⟩ := hsource.bigStep
    obtain ⟨_, _, hbsExpected⟩ := hexpected.bigStep
    have hfinal : final = expected := (BigStep.unique hbs hbsExpected).1
    rw [hfinal] at hfound
    have hcountEq :
        (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 =
          selectBitIndex X.card C.domainNonempty C.t tape := by
      simpa using congrArg Prod.fst
        (selectBitIndexWithCount_eq X.card C.domainNonempty C.t tape)
    cases hindexCount :
        (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 with
    | none =>
      rw [← hcountEq]
      exact hindexCount
    | some i =>
      rw [hindexCount] at hfoundExpected
      simp at hfoundExpected
      rw [hfoundExpected] at hfound
      norm_num at hfound
  · intro hnone
    obtain ⟨final, hrun, _, hnoneVertex, hfound⟩ := sourceDraw_run C tape
    have hcountEq :
        (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 =
          selectBitIndex X.card C.domainNonempty C.t tape := by
      simpa using congrArg Prod.fst
        (selectBitIndexWithCount_eq X.card C.domainNonempty C.t tape)
    have hindexCount :
        (selectBitIndexWithCount X.card C.domainNonempty C.t tape).1 = none := by
      rw [hcountEq]
      exact hnone
    have hfoundZero : final.vars "drawFound" = 0 := by
      simpa [hindexCount] using hfound
    exact ⟨final, hrun, hfoundZero⟩

/-- The actual source exhaustion event is the selector's all-rejected tape
set. -/
lemma sourceDrawExhaustionEvent_eq_allRejected {X : Finset ℕ}
    (C : DrawContext X) :
    sourceDrawExhaustionEvent C = allRejectedBitTapes X.card C.t := by
  classical
  ext tape
  rw [sourceDrawExhaustionEvent_iff_none, selectBitIndex_eq_none_iff]

/-- The actual source command's exhaustion probability inherits the exact
finite-selector tail bound. -/
lemma sourceDrawExhaustion_tail_bound {X : Finset ℕ}
    (C : DrawContext X) :
    2 ^ C.t * (sourceDrawExhaustionEvent C).card ≤
      Fintype.card (BitTape X.card C.t) := by
  rw [sourceDrawExhaustionEvent_eq_allRejected]
  exact failure_tail_bound X.card C.domainNonempty C.t

end Lax457868Proofs.VerifiedDrawLaw
