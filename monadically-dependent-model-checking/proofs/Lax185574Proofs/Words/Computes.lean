import Lax185574Proofs.LegacyComputing
import Lax808846Proofs.Transfer
import Lax185574Proofs.Legacy

/-!
From an IMP+ run to `Lax185574.Computing.Computes`.

An algorithm of this submission is written as a command of IMP+, the
structured language of `Lax808846Proofs.Imp`, and compiled to the word
RAM by its compiler. The command is proved correct in the bounded
semantics `Run B`, where `B` bounds every value the run produces. This
module turns such a run into the two clauses of `Computes`.

The value bound is `A · (|x| + M + 1)^e`, where `M` is the largest entry
of the input word `x`, and the cost is at most `K · (|x| + 1)^d`. The
exponent `e` is the word-length exponent of `Computes`. At a word length
where `x` is admissible for a large enough constant, the bound and the
layout fit into a word, so the compiled program halts with the right
output within `c · (|x| + 1)^d` steps. Both clauses follow, the first
because the machine is deterministic.
-/

namespace Lax185574Proofs.Words

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning Lax808846Proofs.Machine
open Lax185574.WordEncoding Lax185574.Computing

universe u v

/-- The largest entry of a word, `0` for the empty word. -/
def maxEntry (x : List ℕ) : ℕ := x.foldr max 0

theorem le_maxEntry {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v ≤ maxEntry x := by
  induction x with
  | nil => simp at hv
  | cons a x ih =>
    simp only [List.mem_cons] at hv
    simp only [maxEntry, List.foldr_cons] at ih ⊢
    rcases hv with rfl | hv
    · exact le_max_left _ _
    · exact le_trans (ih hv) (le_max_right _ _)

theorem maxEntry_mem {x : List ℕ} (hx : x ≠ []) : maxEntry x ∈ x := by
  induction x with
  | nil => exact absurd rfl hx
  | cons a x ih =>
    simp only [maxEntry, List.foldr_cons, List.mem_cons]
    rcases x with _ | ⟨b, x⟩
    · simp
    · rcases le_total a (List.foldr max 0 (b :: x)) with h | h
      · right; rw [max_eq_right h]; exact ih (by simp)
      · left; rw [max_eq_left h]

/-- The value bound of a run on the input `x`. -/
def valBound (A e : ℕ) (x : List ℕ) : ℕ := A * (x.length + maxEntry x + 1) ^ e

/-- The constant of `Computes` obtained from a layout, the factor `A`
of the value bound and the factor `K` of the cost. -/
def bridgeConst (L : Layout) (A K : ℕ) : ℕ :=
  L.temps + 2 + L.scalars.length + (L.arrays.length + 1) * A + L.const * K + 1

/-- **From an IMP+ run to `Computes`.** If the command runs on the word
of `a` to the word of `b`, with values below `A · (|x| + M + 1)^e` and
cost at most `K · (|x| + 1)^d`, then the compiled program computes `b`
from `a` with word-length exponent `e` and time `c · (m + 1)^d`. -/
theorem computes_of_run {α : Type u} {β : Type v} [WordEncoding α] [WordEncoding β]
    {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) {A e K d : ℕ} (hA : 1 ≤ A) (he : 1 ≤ e)
    {a : α} {b : β} (hx : toWord a ≠ [])
    (hrun : ∃ (ext : String → ℕ) (σ' : Env),
      Run (valBound A e (toWord a)) cmd (initEnv ext (toWord a)) σ'
        (K * ((toWord a).length + 1) ^ d) ∧ σ'.out = toWord b) :
    Computes (compileProgram L cmd) e (bridgeConst L A K) a b
      (fun m => bridgeConst L A K * (m + 1) ^ d) := by
  set x := toWord a with hxdef
  set c := bridgeConst L A K with hc
  set M := maxEntry x
  set X := (x.length + M + 1) ^ e with hX
  intro w hadm
  have hcX : c * X ≤ 2 ^ w := hadm M (maxEntry_mem hx)
  have hlen : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hX2 : 2 ≤ X := by
    calc 2 ≤ x.length + M + 1 := by omega
      _ = (x.length + M + 1) ^ 1 := (pow_one _).symm
      _ ≤ X := Nat.pow_le_pow_right (by omega) he
  have hXge : x.length + M + 1 ≤ X := by
    calc x.length + M + 1 = (x.length + M + 1) ^ 1 := (pow_one _).symm
      _ ≤ X := Nat.pow_le_pow_right (by omega) he
  set B := valBound A e x with hB
  have hBX : B = A * X := rfl
  have hspan : L.span B ≤ 2 ^ w := by
    simp only [Layout.span, hBX]
    refine le_trans ?_ hcX
    simp only [hc, bridgeConst]
    generalize L.temps + 2 + L.scalars.length = P
    generalize L.arrays.length = Q
    have h1 : P ≤ P * X := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : Q * (A * X) ≤ (Q + 1) * A * X := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have h3 : (P + (Q + 1) * A + L.const * K + 1) * X = P * X + (Q + 1) * A * X +
      (L.const * K + 1) * X := by ring
    omega
  have hAX : A * X ≤ (L.arrays.length + 1) * A * X := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hfit : L.FitsWords B w := by
    refine ⟨by rw [hBX]; nlinarith, ?_, hspan⟩
    refine le_trans ?_ hcX
    rw [hBX]
    simp only [hc, bridgeConst]
    have h3 : (L.temps + 2 + L.scalars.length + (L.arrays.length + 1) * A + L.const * K + 1) * X
      = (L.temps + 2 + L.scalars.length) * X + (L.arrays.length + 1) * A * X +
      (L.const * K + 1) * X := by ring
    omega
  obtain ⟨ext, σ', ⟨k, hk, hbs⟩, hout⟩ := hrun
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
  have hP : 1 ≤ (x.length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  show t ≤ c * (wordLength a + 1) ^ d
  have hwl : wordLength a = x.length := rfl
  rw [hwl]
  calc t ≤ L.const * k + 1 := ht
    _ ≤ L.const * (K * (x.length + 1) ^ d) + 1 := by gcongr
    _ ≤ (L.const * K + 1) * (x.length + 1) ^ d := by nlinarith
    _ ≤ c * (x.length + 1) ^ d := by
      gcongr
      simp only [hc, bridgeConst]
      omega

end Lax185574Proofs.Words
