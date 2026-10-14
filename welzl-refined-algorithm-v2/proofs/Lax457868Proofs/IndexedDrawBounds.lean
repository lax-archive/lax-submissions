import Mathlib.Tactic
import Lax457868Proofs.IndexedDraws

/-!
Finite-batch failure and work bounds for the actual indexed fair-bit sampler.
These are fixed-domain finite counting statements; they make no claim about an
adaptive sequence of domains or conditioning on future success.
-/

namespace Lax457868Proofs.IndexedDrawBounds

open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.IndexedDraws
open Lax457868Proofs.SamplerUniformDraws

variable {α : Type*}

private lemma card_coordinate_filter {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (i : Fin (n + 1)) (A : Finset Ω) :
    (Finset.univ.filter fun f : Fin (n + 1) → Ω => f i ∈ A).card =
      A.card * Fintype.card Ω ^ n := by
  classical
  let p := Equiv.arrowCongr (Equiv.swap i 0) (Equiv.refl Ω)
  let e0 : (Ω × (Fin n → Ω)) ≃ (Fin (n + 1) → Ω) :=
    Fin.consEquiv (fun _ : Fin (n + 1) => Ω)
  let e := p.trans e0.symm
  have he (f : Fin (n + 1) → Ω) : f i ∈ A ↔ (e f).1 ∈ A := by
    change f i ∈ A ↔ (e0.symm (p f)).1 ∈ A
    have hp : p f 0 = f i := by simp [p, Equiv.arrowCongr_apply]
    have hzero : (e0.symm (p f)).1 = p f 0 := by
      simp [e0, Fin.consEquiv]
    rw [hzero, hp]
  have hc := Fintype.card_congr (Equiv.subtypeEquiv
    (p := fun f : Fin (n + 1) → Ω => f i ∈ A)
    (q := fun x : Ω × (Fin n → Ω) => x.1 ∈ A) e he)
  have hleft : Fintype.card {f : Fin (n + 1) → Ω // f i ∈ A} =
      (Finset.univ.filter fun f : Fin (n + 1) → Ω => f i ∈ A).card := by
    rw [Fintype.card_subtype]
  let ep : {x : Ω × (Fin n → Ω) // x.1 ∈ A} ≃
      {x : Ω // x ∈ A} × (Fin n → Ω) :=
    { toFun := fun x => (⟨x.1.1, x.2⟩, x.1.2)
      invFun := fun x => ⟨(x.1.1, x.2), x.1.2⟩
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }
  have hprod : Fintype.card {x : Ω × (Fin n → Ω) // x.1 ∈ A} =
      A.card * Fintype.card Ω ^ n := by
    calc
      _ = Fintype.card ({x : Ω // x ∈ A} × (Fin n → Ω)) :=
        Fintype.card_congr ep
      _ = A.card * Fintype.card Ω ^ n := by simp
  rw [← hleft, hc, hprod]

/-- Fair-bit tapes whose value at one fixed sampler coordinate belongs to
`A`, counted as a fraction of the full product sample space. -/
private lemma sum_coordinate {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (i : Fin (n + 1)) (w : Ω → ℕ) :
    ∑ f : Fin (n + 1) → Ω, w (f i) =
      (∑ x : Ω, w x) * Fintype.card Ω ^ n := by
  classical
  let p := Equiv.arrowCongr (Equiv.swap i 0) (Equiv.refl Ω)
  let e0 : (Ω × (Fin n → Ω)) ≃ (Fin (n + 1) → Ω) :=
    Fin.consEquiv (fun _ : Fin (n + 1) => Ω)
  have hp (f : Fin (n + 1) → Ω) : p f 0 = f i := by
    simp [p, Equiv.arrowCongr_apply]
  calc
    _ = ∑ f : Fin (n + 1) → Ω, w (p f 0) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [hp]
    _ = ∑ f : Fin (n + 1) → Ω, w (f 0) :=
      Equiv.sum_comp p (fun f : Fin (n + 1) → Ω => w (f 0))
    _ = ∑ z : Ω × (Fin n → Ω), w z.1 :=
      (Equiv.sum_comp e0 (fun f : Fin (n + 1) → Ω => w (f 0))).symm
    _ = (∑ x : Ω, w x) * Fintype.card Ω ^ n := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ x : Ω, ∑ y : Fin n → Ω, w x) =
            Fintype.card Ω ^ n * (∑ x : Ω, w x) := by
              simp [Finset.mul_sum]
        _ = (∑ x : Ω, w x) * Fintype.card Ω ^ n := by ring

/-- A requested batch fails exactly when at least one independent capped
selector fails. -/
noncomputable def failedBatchSet (X : Finset α) [DecidableEq α] (hX : 0 < X.card)
    (r t : ℕ) : Finset (DrawBitTape X r t) :=
  Finset.univ.filter fun bits => successfulDrawTape X hX r t bits = none

/-- Integer form of the finite-batch union bound. -/
lemma failedBatch_count_bound (X : Finset α) [DecidableEq α] (hX : 0 < X.card)
    (r t : ℕ) :
    2 ^ t * (failedBatchSet X hX r t).card ≤
      r * Fintype.card (DrawBitTape X r t) := by
  classical
  let Bad : Finset (BitTape X.card t) := allRejectedBitTapes X.card t
  have hbad (tape : BitTape X.card t) :
      selectIndexedDraw X hX t tape = none ↔ tape ∈ Bad := by
    simp [selectIndexedDraw, Bad, selectBitIndex_eq_none_iff]
  have hevent (bits : DrawBitTape X r t) :
      successfulDrawTape X hX r t bits = none ↔
        ∃ i : Fin r, bits i ∈ Bad := by
    rw [successfulDrawTape_eq_none_iff]
    constructor
    · intro h
      by_contra hno
      push Not at hno
      apply h
      intro i
      cases hs : selectIndexedDraw X hX t (bits i) with
      | none => exact (hno i ((hbad (bits i)).mp hs)).elim
      | some x => exact ⟨x, rfl⟩
    · rintro ⟨i, hi⟩ hall
      obtain ⟨x, hx⟩ := hall i
      rw [(hbad (bits i)).mpr hi] at hx
      cases hx
  cases r with
  | zero => simp [failedBatchSet, successfulDrawTape]
  | succ n =>
    let event (i : Fin (n + 1)) : Finset (DrawBitTape X (n + 1) t) :=
      Finset.univ.filter fun bits => bits i ∈ Bad
    have heq : failedBatchSet X hX (n + 1) t =
        Finset.univ.biUnion event := by
      ext bits
      simp [failedBatchSet, event, hevent]
    calc
      2 ^ t * (failedBatchSet X hX (n + 1) t).card
          ≤ 2 ^ t * ∑ i : Fin (n + 1), (event i).card := by
            apply Nat.mul_le_mul_left
            rw [heq]
            exact Finset.card_biUnion_le
      _ = 2 ^ t * ((n + 1) * (Bad.card * Fintype.card (BitTape X.card t) ^ n)) := by
            simp [event, card_coordinate_filter]
      _ ≤ (n + 1) * Fintype.card (BitTape X.card t) ^ (n + 1) := by
            have hb := failure_tail_bound X.card hX t
            have hm := Nat.mul_le_mul_right
              ((n + 1) * Fintype.card (BitTape X.card t) ^ n) hb
            calc
              2 ^ t * ((n + 1) *
                  (Bad.card * Fintype.card (BitTape X.card t) ^ n)) =
                  (2 ^ t * Bad.card) *
                    ((n + 1) * Fintype.card (BitTape X.card t) ^ n) := by ring
              _ ≤ Fintype.card (BitTape X.card t) *
                    ((n + 1) * Fintype.card (BitTape X.card t) ^ n) := hm
              _ = (n + 1) * Fintype.card (BitTape X.card t) ^ (n + 1) := by
                    rw [Nat.pow_succ]
                    ring
      _ = (n + 1) * Fintype.card (DrawBitTape X (n + 1) t) := by
            simp [DrawBitTape, Nat.pow_succ]

/-- Total actual bit reads for one finite batch of sampler requests. -/
def batchReadBits (X : Finset α) (r t : ℕ)
    (bits : DrawBitTape X r t) : ℕ :=
  ∑ i : Fin r, bitTapeReadBits X.card t (bits i)

/-- The integer sum of total actual bit reads is at most twice the block length
per requested draw, over the full equally likely batch tape space. -/
lemma sum_batchReadBits_le_two (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) :
    ∑ bits : DrawBitTape X r t, batchReadBits X r t bits ≤
      2 * r * Nat.clog 2 X.card * Fintype.card (DrawBitTape X r t) := by
  classical
  cases r with
  | zero => simp [batchReadBits]
  | succ n =>
    have hcoord (i : Fin (n + 1)) :
        ∑ bits : DrawBitTape X (n + 1) t,
            bitTapeReadBits X.card t (bits i) =
          (∑ tape : BitTape X.card t, bitTapeReadBits X.card t tape) *
            Fintype.card (BitTape X.card t) ^ n := by
      exact sum_coordinate n i (bitTapeReadBits X.card t)
    have hmean := sum_bitTapeReadBits_le_two X.card hX t
    calc
      ∑ bits : DrawBitTape X (n + 1) t, batchReadBits X (n + 1) t bits
          = (n + 1) *
              ((∑ tape : BitTape X.card t, bitTapeReadBits X.card t tape) *
                Fintype.card (BitTape X.card t) ^ n) := by
            simp only [batchReadBits]
            rw [Finset.sum_comm]
            simp_rw [hcoord]
            simp
      _ ≤ ((n + 1) * Fintype.card (BitTape X.card t) ^ n) *
              (2 * Nat.clog 2 X.card * Fintype.card (BitTape X.card t)) := by
            have hm := Nat.mul_le_mul_right
              (Fintype.card (BitTape X.card t) ^ n) hmean
            have hm' :
                (∑ tape : BitTape X.card t, bitTapeReadBits X.card t tape) *
                    Fintype.card (BitTape X.card t) ^ n ≤
                  (2 * Nat.clog 2 X.card * Fintype.card (BitTape X.card t)) *
                    Fintype.card (BitTape X.card t) ^ n := by
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm
            calc
              _ = (n + 1) * ((∑ tape : BitTape X.card t,
                  bitTapeReadBits X.card t tape) *
                    Fintype.card (BitTape X.card t) ^ n) := by ring
              _ ≤ (n + 1) * ((2 * Nat.clog 2 X.card *
                  Fintype.card (BitTape X.card t)) *
                    Fintype.card (BitTape X.card t) ^ n) :=
                Nat.mul_le_mul_left _ hm'
              _ = _ := by ring
      _ = 2 * (n + 1) * Nat.clog 2 X.card *
              Fintype.card (DrawBitTape X (n + 1) t) := by
            simp [DrawBitTape, Nat.pow_succ]
            ring

end Lax457868Proofs.IndexedDrawBounds
