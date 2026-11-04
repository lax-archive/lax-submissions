import Lax185574Proofs.RamLower
import Lax185574Proofs.RamPipeBack
import Lax185574Proofs.RamCat
import Lax185574Proofs.RamOut

/-!
A program with a capped output.

`capped X D` runs `X` at word length `w - 2 - D` and then copies its
output with `catProg` at the same word length. A halting run of the
composite therefore has an output of length at most
`catLim (w - 2 - D)` and entries below `2 ^ (w - 2 - D)`, whatever `X`
does. A composite needs this to hand the output of an opaque program to
a further stage that must stay faithful, since that stage can then bound
everything it reads.
-/

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim Lax185574Proofs.RamCat
open Lax808846Proofs.Machine Lax185574Proofs.RamExec

/-- The rewrite `![y, x] ↦ y`. -/
def fstRw : Rewrite 2 := [.slice 0 (.lit 0) none]

theorem fstRw_apply (xs : Fin 2 → List ℕ) : fstRw.apply xs = xs 0 := by
  simp [fstRw, Rewrite.apply, Segment.apply, HExpr.eval]

theorem fstRw_cost (xs : Fin 2 → List ℕ) : fstRw.cost xs = 3 := by
  simp [fstRw, Rewrite.cost, Segment.cost, HExpr.cost]

theorem fstRw_fits {w : ℕ} {y x : List ℕ} (hy : y.length < 2 ^ w) (hx : x.length < 2 ^ w) :
    fstRw.Fits w ![y, x] := by
  refine ⟨fun i => ?_, by rw [fstRw_apply]; exact hy, ?_⟩
  · fin_cases i <;> simpa
  · intro seg hseg
    simp only [fstRw, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    subst hseg
    exact ⟨trivial, by simp [HExpr.eval]⟩

theorem map_mod_of_lt {v : ℕ} {y : List ℕ} (h : ∀ e ∈ y, e < 2 ^ v) :
    y.map (· % 2 ^ v) = y := by
  conv_rhs => rw [← List.map_id y]
  exact List.map_congr_left fun e he => Nat.mod_eq_of_lt (h e he)

/-- **Capped output.** `X` runs at `w - 2 - D`, and a halting run of
the composite has an output of length at most
`catLim (w - 2) (D + 2) < 2 ^ (w - 4 - D)`. -/
theorem capped (X : Program) (D : ℕ) : ∃ (p : Program) (K : ℕ),
    ∀ (w : ℕ) (x : List ℕ), K ≤ 2 ^ (w - 2 - D) → x.length < 2 ^ (w - 2 - D) →
      D + 7 ≤ w →
      (∀ y t, RunsTo (w - 2 - D) X x y t → y.length ≤ catLim (w - 2) (D + 2) →
        ∃ t' ≤ K * (t + y.length + 1), RunsTo w p x y t') ∧
      (∀ o T, RunsTo w p x o T →
        ∃ t ≤ T, RunsTo (w - 2 - D) X x o t ∧ o.length ≤ catLim (w - 2) (D + 2)) := by
  obtain ⟨pX, KX, hKX, hX⟩ := lower D X
  obtain ⟨p, K, hp⟩ := pipe_sound pX (catProg (D + 2)) idRw fstRw
  refine ⟨p, K * KX + 7 * K + 6 * K + K + KX + 1, fun w x hK hx hw => ?_⟩
  have hle : 2 ^ (w - 2 - D) ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle' : 2 ^ (w - 2) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hKp : K ≤ 2 ^ (w - 2) := by
    have : K ≤ K * KX + 7 * K + 6 * K + K + KX + 1 := by omega
    omega
  have hKX' : KX ≤ 2 ^ (w - 2 - D) := by omega
  have hcat := catLim_lt (w - 2) (D + 2)
  have hw4 : 4 ≤ w - 2 := by omega
  have hE : D + 2 < w - 2 := by omega
  have hsub : w - 2 - D = (w - 2) - D := rfl
  have hmod : ∀ {y : List ℕ} {t : ℕ}, RunsTo (w - 2 - D) X x y t → y.map (· % 2 ^ (w - 2)) = y :=
    fun h => map_mod_of_lt fun e he => lt_of_lt_of_le (runsTo_out_lt h e he) hle
  obtain ⟨hpf, hpb⟩ := hp w x hKp (idRw_fits (by omega))
  obtain ⟨hXf, hXb⟩ := hX (w - 2) x hKX' hx
  simp only [idRw_apply, idRw_cost, fstRw_apply, fstRw_cost, Matrix.cons_val_zero] at hpf hpb
  refine ⟨fun y t hy hyl => ?_, fun o T ho => ?_⟩
  · obtain ⟨t₁, ht₁, h₁⟩ := hXf y t hy
    have hcf := cat_fwd hw4 hE hyl
    rw [hmod hy] at hcf
    obtain ⟨t', ht', h'⟩ := hpf y y t₁ _ (by omega) (fstRw_fits (by omega) (by omega)) h₁ hcf
    refine ⟨t', le_trans ht' ?_, h'⟩
    set S := t + y.length + 1 with hS
    have h1 : K * t₁ ≤ K * KX * S := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (le_trans ht₁ (Nat.mul_le_mul_left _ (by omega)))
    have h2 : K * (4 + 7 * y.length + 2 + 3 + 3) ≤ 13 * K * S := by
      have : 4 + 7 * y.length + 2 + 3 + 3 ≤ 13 * S := by omega
      calc K * (4 + 7 * y.length + 2 + 3 + 3) ≤ K * (13 * S) := Nat.mul_le_mul_left _ this
        _ = 13 * K * S := by ring
    have h3 : K * KX * S + 13 * K * S ≤ (K * KX + 7 * K + 6 * K + K + KX + 1) * S := by
      have : K * KX * S + 13 * K * S = (K * KX + 13 * K) * S := by ring
      rw [this]; exact Nat.mul_le_mul_right _ (by omega)
    have : K * (t₁ + (4 + 7 * y.length + 2) + 3 + 3) = K * t₁ + K * (4 + 7 * y.length + 2 + 3 + 3) := by
      ring
    omega
  · obtain ⟨y, t₁, ht₁, hyl, h₁, h₂⟩ := hpb o T ho
    obtain ⟨t₂, -, h₂⟩ := h₂ (fstRw_fits (by omega) (by omega))
    obtain ⟨t₃, ht₃, h₃⟩ := hXb y t₁ h₁
    obtain ⟨hl, rfl⟩ := cat_back hw4 hE h₂
    rw [hmod h₃]
    exact ⟨t₃, by omega, h₃, hl⟩

end Lax185574Proofs.Simulate
