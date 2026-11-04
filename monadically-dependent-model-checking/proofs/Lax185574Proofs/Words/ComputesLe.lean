import Lax185574Proofs.Words.Computes

/-!
`Computes` with an arbitrary time bound.

`computes_of_run` bounds the time by a power of the input length. Some
statements bound it in terms of parameters of the input instead, such
as the number of vertices of a graph. This variant takes the cost of
the run on the given input and any time bound `T` that pays for it.
-/

namespace Lax185574Proofs.Words

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning Lax808846Proofs.Machine
open Lax185574.WordEncoding Lax185574.Computing

universe u v

/-- The part of the constant of `Computes` that makes the layout fit. -/
def layoutConst (L : Layout) (A : ℕ) : ℕ :=
  L.temps + 2 + L.scalars.length + (L.arrays.length + 1) * A + 1

/-- **From an IMP+ run to `Computes`, with any time bound.** If the
command runs on the word of `a` to the word of `b` with values below
`A · (|x| + M + 1)^e` at cost `K`, and `T ‖a‖` pays for the compiled
run, then the compiled program computes `b` from `a` in time `T`. -/
theorem computes_of_run_le {α : Type u} {β : Type v} [WordEncoding α] [WordEncoding β]
    {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) {A e c : ℕ} (hA : 1 ≤ A) (he : 1 ≤ e)
    (hc : layoutConst L A ≤ c) {a : α} {b : β} {T : ℕ → ℕ} (hx : toWord a ≠ [])
    (hrun : ∃ (ext : String → ℕ) (σ' : Env) (K : ℕ),
      Run (valBound A e (toWord a)) cmd (initEnv ext (toWord a)) σ' K ∧ σ'.out = toWord b ∧
        L.const * K + 1 ≤ T (wordLength a)) :
    Computes (compileProgram L cmd) e c a b T := by
  set x := toWord a with hxdef
  set M := maxEntry x
  set X := (x.length + M + 1) ^ e with hX
  intro w hadm
  have hcX : c * X ≤ 2 ^ w := hadm M (maxEntry_mem hx)
  have hlen : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hXge : x.length + M + 1 ≤ X := by
    calc x.length + M + 1 = (x.length + M + 1) ^ 1 := (pow_one _).symm
      _ ≤ X := Nat.pow_le_pow_right (by omega) he
  set B := valBound A e x with hB
  have hBX : B = A * X := rfl
  have hspan : L.span B ≤ 2 ^ w := by
    simp only [Layout.span, hBX]
    refine le_trans ?_ hcX
    refine le_trans ?_ (Nat.mul_le_mul_right X hc)
    simp only [layoutConst]
    generalize L.temps + 2 + L.scalars.length = P
    generalize L.arrays.length = Q
    have h1 : P ≤ P * X := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : Q * (A * X) ≤ (Q + 1) * A * X := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have h3 : (P + (Q + 1) * A + 1) * X = P * X + (Q + 1) * A * X + X := by ring
    omega
  have hfit : L.FitsWords B w := by
    refine ⟨by rw [hBX]; nlinarith, ?_, hspan⟩
    refine le_trans ?_ hcX
    rw [hBX]
    refine le_trans ?_ (Nat.mul_le_mul_right X hc)
    simp only [layoutConst]
    have h3 : (L.temps + 2 + L.scalars.length + (L.arrays.length + 1) * A + 1) * X
      = (L.temps + 2 + L.scalars.length) * X + (L.arrays.length + 1) * A * X + X := by ring
    have : A * X ≤ (L.arrays.length + 1) * A * X := by
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨ext, σ', K, ⟨k, hk, hbs⟩, hout, hT⟩ := hrun
  have hinp : ∀ v ∈ x, v < B := by
    intro v hv
    have := le_maxEntry hv
    rw [hBX]; nlinarith
  obtain ⟨t, ht, hruns⟩ := compileProgram_runsTo hfit hok hinp hbs
  rw [hout] at hruns
  refine ⟨fun y t' h => (runsTo_unique h hruns).1, fun _ y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  refine ⟨t, ?_, hruns⟩
  calc t ≤ L.const * k + 1 := ht
    _ ≤ L.const * K + 1 := by gcongr
    _ ≤ T (wordLength a) := hT

end Lax185574Proofs.Words
