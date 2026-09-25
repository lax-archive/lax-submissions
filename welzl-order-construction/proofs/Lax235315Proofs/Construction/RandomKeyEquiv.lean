import Lax235315Proofs.Construction.PackedKeys
import Lax235315Proofs.Construction.RandomBits
import Lax195003.WordRamRandomness
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! Exact finite equivalences between random bit blocks and the `q^8`-valued
key assignments used in the per-round probability calculation. -/

namespace Lax235315Proofs.Construction.RandomKeyEquiv

open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.PackedKeys
open Lax235315Proofs.Construction.RandomBits

noncomputable section

theorem bitsValue_eq_ofDigits_reverse (xs : List ℕ) :
    bitsValue xs = Nat.ofDigits 2 xs.reverse := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs b ih =>
      rw [bitsValue_append, List.reverse_append]
      simp [Nat.ofDigits, ih]
      omega

theorem bitTape_length {r : ℕ} (ρ : Fin r → Bool) :
    (bitTape ρ).length = r := by simp [bitTape]

theorem bitTape_bounded {r : ℕ} (ρ : Fin r → Bool) :
    ∀ b ∈ bitTape ρ, b < 2 := by
  intro b hb
  obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hb
  have hieq : (bitTape ρ)[i] = (if ρ ⟨i, by simpa [bitTape] using hi⟩ then 1 else 0) := by
    simp [bitTape]
  rw [← hib, hieq]
  split <;> omega

/-- The natural represented by one most-significant-bit-first random word. -/
def boolWordValue {L : ℕ} (ρ : Fin L → Bool) : ℕ :=
  bitsValue (bitTape ρ)

theorem boolWordValue_lt {L : ℕ} (ρ : Fin L → Bool) :
    boolWordValue ρ < 2 ^ L := by
  unfold boolWordValue
  rw [bitsValue_eq_ofDigits_reverse]
  simpa [bitTape_length] using Nat.ofDigits_lt_base_pow_length
    (b := 2) (l := (bitTape ρ).reverse) (by omega)
      (fun b hb => bitTape_bounded ρ b (by simpa using hb))

theorem bitTape_injective {L : ℕ} :
    Function.Injective (bitTape : (Fin L → Bool) → List ℕ) := by
  intro ρ τ h
  unfold bitTape at h
  have hfn := List.ofFn_injective h
  funext i
  have hi := congrFun hfn i
  cases hρi : ρ i <;> cases hτi : τ i <;> simp_all

theorem boolWordValue_injective {L : ℕ} :
    Function.Injective (boolWordValue : (Fin L → Bool) → ℕ) := by
  intro ρ τ h
  apply bitTape_injective
  apply List.reverse_injective
  apply Nat.ofDigits_inj_of_len_eq (b := 2) (by omega)
  · simp [bitTape]
  · intro b hb
    exact bitTape_bounded ρ b (by simpa using hb)
  · intro b hb
    exact bitTape_bounded τ b (by simpa using hb)
  · simpa [← bitsValue_eq_ofDigits_reverse, boolWordValue] using h

/-- An `L`-bit block is exactly one value in `Fin (2^L)`. -/
def boolWordEquiv (L : ℕ) : (Fin L → Bool) ≃ Fin (2 ^ L) := by
  let f : (Fin L → Bool) → Fin (2 ^ L) := fun ρ =>
    ⟨boolWordValue ρ, boolWordValue_lt ρ⟩
  have hinj : Function.Injective f := by
    intro ρ τ h
    apply boolWordValue_injective
    exact Fin.mk.inj h
  have hcard : Fintype.card (Fin L → Bool) = Fintype.card (Fin (2 ^ L)) := by
    simp
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)

def bitDigits {L : ℕ} (ρ : Fin 8 → Fin L → Bool) : Fin 8 → ℕ → ℕ :=
  fun d _ => (boolWordEquiv L (ρ d)).val

/-- Eight consecutive `L`-bit blocks are exactly one packed key. -/
def packedBitsEquiv (L : ℕ) (hL : 0 < L) :
    (Fin 8 → Fin L → Bool) ≃ Fin ((2 ^ L) ^ 8) := by
  have hq : 1 < 2 ^ L := Nat.one_lt_two_pow (Nat.ne_of_gt hL)
  let f : (Fin 8 → Fin L → Bool) → Fin ((2 ^ L) ^ 8) := fun ρ =>
    ⟨packedKey (2 ^ L) (bitDigits ρ) 0, packedKey_lt_pow
      hq
      (fun d => (boolWordEquiv L (ρ d)).isLt)⟩
  have hinj : Function.Injective f := by
    intro ρ τ h
    have hpack : packedKey (2 ^ L) (bitDigits ρ) 0 =
        packedKey (2 ^ L) (bitDigits τ) 0 := Fin.mk.inj h
    unfold packedKey at hpack
    have hlist : digitList (bitDigits ρ) 0 = digitList (bitDigits τ) 0 := by
      apply List.reverse_injective
      exact Nat.ofDigits_inj_of_len_eq hq (by simp [digitList])
        (by simpa using (digitList_bounded
          (fun d => (boolWordEquiv L (ρ d)).isLt)))
        (by simpa using (digitList_bounded
          (fun d => (boolWordEquiv L (τ d)).isLt))) hpack
    simp only [digitList, List.cons.injEq, bitDigits] at hlist
    rcases hlist with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    rcases h7 with ⟨h7, _⟩
    have hvals : ∀ d, (boolWordEquiv L (ρ d)).val =
        (boolWordEquiv L (τ d)).val := by
      intro d
      fin_cases d <;> assumption
    funext d
    apply (boolWordEquiv L).injective
    apply Fin.ext
    exact hvals d
  have hcard : Fintype.card (Fin 8 → Fin L → Bool) =
      Fintype.card (Fin ((2 ^ L) ^ 8)) := by
    simp
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)

/-- Row-major indices for `a` vertices, eight digits, and `L` bits. -/
def tripleIndexEquiv (a L : ℕ) :
    (Fin a × Fin 8) × Fin L ≃ Fin ((a * 8) * L) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin L))).trans finProdFinEquiv

/-- A flat round bit block, reshaped in the exact vertex/digit/bit order in
which `readKeys` consumes it. -/
def bitBlockEquiv (a L : ℕ) :
    (Fin ((a * 8) * L) → Bool) ≃ (Fin a → Fin 8 → Fin L → Bool) where
  toFun ρ i d j := ρ (tripleIndexEquiv a L ((i, d), j))
  invFun bits k :=
    let p := (tripleIndexEquiv a L).symm k
    bits p.1.1 p.1.2 p.2
  left_inv := by
    intro ρ
    funext k
    simp
  right_inv := by
    intro bits
    funext i d j
    simp

/-- Consequently, a whole random round block is exactly an independent key
assignment on its `a` active positions. -/
def roundAssignmentEquiv (a L : ℕ) (hL : 0 < L) :
    (Fin ((a * 8) * L) → Bool) ≃ (Fin a → Fin ((2 ^ L) ^ 8)) :=
  (bitBlockEquiv a L).trans {
    toFun := fun bits i => packedBitsEquiv L hL (bits i)
    invFun := fun keys i => (packedBitsEquiv L hL).symm (keys i)
    left_inv := by intro bits; funext i d j; simp
    right_inv := by intro keys; funext i; simp }

end

end Lax235315Proofs.Construction.RandomKeyEquiv
