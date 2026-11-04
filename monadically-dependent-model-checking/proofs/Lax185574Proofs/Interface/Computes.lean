import Lax185574.Algorithms
import Lax185574Proofs.LegacyComputing
import Lax185574Proofs.Words.Computes

/-!
`Lax185574.Algorithms.Algorithm.Computes` and the older
`Lax185574.Computing.Computes`.

The two notions have the same two clauses, soundness at every admissible
word length and halting once the time bound fits into a word. They
differ in the admissibility of the input word `x`. The new one asks
`c · (|x| + Σx + 1)^e ≤ 2^w` for the sum `Σx` of the entries, the old one
asks `c · (|x| + v + 1)^e ≤ 2^w` for every entry `v`. The sum dominates
every entry, so the old notion gives the new one with the same exponent
and constant. Conversely `|x| + Σx + 1 ≤ (|x| + M + 1)^2` for the largest
entry `M`, so the new notion gives the old one with the exponent
doubled, provided the input word is not empty. The old time bound is a
function of the input length, the new one a real number `T`, read as
`c · T + c`.

The words of the older notion are the encodings, see
`Lax185574Proofs.Interface.encode_eq_toWord`.
-/

namespace Lax185574Proofs.Interface

open Lax808846.Ram Lax808846.RamComputes
open Lax185574.Encoding Lax185574.WordEncoding Lax185574.Computing Lax185574.Algorithms

universe u v

variable {α : Type u} {β : Type v} [Encode α] [Encode β]

/-- The old notion gives the new one, with the same exponent and a
constant `c' ≥ c` large enough that `c' · T + c'` bounds the old time. -/
theorem computes_of_old {p : Program} {e c c' : ℕ} {a : α} {b : β} {T' : ℕ → ℕ} {T : ℝ}
    (hc : c ≤ c')
    (hT : (T' (wordLength a) : ℝ) ≤ c' * T + c') (h : Computes p e c a b T') :
    (⟨p, e⟩ : Algorithm).Computes c' a b T := by
  intro w hw
  have hadm : WordAdmissible e c w (toWord a) := fun v hv =>
    le_trans (Nat.mul_le_mul hc (Nat.pow_le_pow_left
      (by have := List.le_sum_of_mem hv; omega) e)) hw
  obtain ⟨hs, ht⟩ := h w hadm
  refine ⟨hs, fun hTw => ?_⟩
  have hfit : T' (wordLength a) ≤ 2 ^ w := by exact_mod_cast hT.trans hTw
  obtain ⟨t, htle, hrun⟩ := ht hfit (toWord a) rfl
  exact ⟨t, (Nat.cast_le.mpr htle).trans hT, hrun⟩

/-- The new notion gives the old one, with the exponent doubled, for a
nonempty input word and an old time bound that dominates `c · T + c`. -/
theorem old_of_computes {A : Algorithm} {c : ℕ} {a : α} {b : β} {T : ℝ} {T' : ℕ → ℕ}
    (hne : toWord a ≠ [])
    (hT : (c : ℝ) * T + c ≤ T' (wordLength a)) (h : A.Computes c a b T) :
    Computes A.program (2 * A.wordExponent) c a b T' := by
  intro w hadm
  set x := toWord a with hx
  set M := Lax185574Proofs.Words.maxEntry x
  have hsum : x.sum ≤ x.length * M := by
    have := List.sum_le_card_nsmul x M fun v hv => Lax185574Proofs.Words.le_maxEntry hv
    simpa using this
  have hbase : x.length + x.sum + 1 ≤ (x.length + M + 1) ^ 2 := by nlinarith
  have hw : c * ((encode a).length + (encode a).sum + 1) ^ A.wordExponent ≤ 2 ^ w := by
    refine le_trans (Nat.mul_le_mul_left c ?_) (hadm M (Lax185574Proofs.Words.maxEntry_mem hne))
    rw [pow_mul]
    exact Nat.pow_le_pow_left hbase _
  obtain ⟨hs, ht⟩ := h w hw
  refine ⟨hs, fun hTw y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfit : (c : ℝ) * T + c ≤ 2 ^ w := hT.trans (by exact_mod_cast hTw)
  obtain ⟨t, htle, hrun⟩ := ht hfit
  exact ⟨t, by exact_mod_cast htle.trans hT, hrun⟩

end Lax185574Proofs.Interface
