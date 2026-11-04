import Lax185574Proofs.Words.ForLoop

/-!
The power test of the glue of lem:compose, in IMP+.

`powLe n` sets the scalar `pok` to `1` if `pb ^ n ≤ Wl` and to `0`
otherwise, for a literal exponent `n`. It multiplies only while the
product stays at most `Wl`, testing `Wl / pb < pp` first, so every value
of the run is at most `Wl` (`powLe_run`). The glue uses it for the guards
of its questions and for the round test, with `Wl = 2 ^ (v - sQ)`.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- One round of the power test. -/
def powStep : Com :=
  .ite (.lt (.div (.var "Wl") (.var "pb")) (.var "pp")) (.assign "pok" (.lit 0))
    (.assign "pp" (.mul (.var "pp") (.var "pb")))

/-- The power test: `pok = 1` iff `pb ^ n ≤ Wl`. -/
def powLe (n : ℕ) : Com :=
  .seq (.assign "pp" (.lit 1)) (.seq (.assign "pok" (.lit 1)) (forUp "pk" (.lit n) powStep))

/-- What the power test keeps after `k` rounds. -/
def PowInv (b W n k : ℕ) (σ τ : Env) : Prop :=
  τ.vars "pb" = b ∧ τ.vars "Wl" = W ∧ τ.out = σ.out ∧ τ.inp = σ.inp ∧ τ.arrs = σ.arrs ∧
    (∀ x, x ≠ "pp" → x ≠ "pok" → x ≠ "pk" → τ.vars x = σ.vars x) ∧ τ.vars "pp" ≤ W ∧
    ((τ.vars "pok" = 1 ∧ τ.vars "pp" = b ^ k ∧ b ^ k ≤ W) ∨ (τ.vars "pok" = 0 ∧ W < b ^ n))

theorem powStep_run {B b W n k : ℕ} {σ τ : Env} (hb : 1 ≤ b) (hbB : b < B) (hWB : W < B) (hk : k < n)
    (h : PowInv b W n k σ τ) :
    ∃ τ', Run B powStep τ τ' 12 ∧ τ'.vars "pk" = τ.vars "pk" ∧ PowInv b W n (k + 1) σ τ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hd : (Expr.div (.var "Wl") (.var "pb")).evalB B τ = some (W / b) := by
    rw [← h1, ← h2]
    exact evalB_bin (evalB_var (by omega)) (evalB_var (by omega))
      (by simp only [Bop.apply]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  have hpp : (Expr.var "pp").evalB B τ = some (τ.vars "pp") := evalB_var (by omega)
  by_cases hlt : W / b < τ.vars "pp"
  · refine ⟨τ.setVar "pok" 0, (Run.ite_true (by rw [evalB_condLt hd hpp]; simpa using hlt)
      (Run.assign (evalB_lit (by omega)))).mono (by simp [Cond.size, Expr.size]), by simp, ?_⟩
    refine ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
      fun x a b' c => by simp [b', h6 x a b' c], by simp [h7], Or.inr ⟨by simp, ?_⟩⟩
    rcases h8 with ⟨-, e, -⟩ | ⟨-, e⟩
    · rw [e] at hlt
      have : W < b ^ (k + 1) := by
        rw [pow_succ]
        have := (Nat.div_lt_iff_lt_mul (by omega)).1 hlt
        exact this
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right hb (by omega))
    · exact e
  · have hle : τ.vars "pp" * b ≤ W := by
      have := Nat.not_lt.1 hlt
      exact (Nat.le_div_iff_mul_le (by omega)).1 this
    have hm : (Expr.mul (.var "pp") (.var "pb")).evalB B τ = some (τ.vars "pp" * b) := by
      rw [← h1]
      exact evalB_bin hpp (evalB_var (by omega)) (by simp only [Bop.apply]; rw [h1]; omega)
    refine ⟨τ.setVar "pp" (τ.vars "pp" * b), (Run.ite_false (by rw [evalB_condLt hd hpp]; simpa using hlt)
      (Run.assign hm)).mono (by simp [Cond.size, Expr.size]), by simp, ?_⟩
    refine ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
      fun x a b' c => by simp [a, h6 x a b' c], by simp; exact hle, ?_⟩
    rcases h8 with ⟨e1, e2, -⟩ | ⟨e1, e2⟩
    · left
      refine ⟨by simp [e1], by simp [e2, pow_succ], ?_⟩
      rw [pow_succ, ← e2]; exact hle
    · right; exact ⟨by simp [e1], e2⟩

/-- **The power test.** -/
theorem powLe_run {B n : ℕ} {σ : Env} (hb : 1 ≤ σ.vars "pb") (hbB : σ.vars "pb" < B) (hW : 1 ≤ σ.vars "Wl")
    (hWB : σ.vars "Wl" < B) (hn : n < B) :
    ∃ σ', Run B (powLe n) σ σ' (20 * n + 30) ∧
      (σ'.vars "pok" = 1 ↔ σ.vars "pb" ^ n ≤ σ.vars "Wl") ∧
      (σ'.vars "pok" = 0 ∨ σ'.vars "pok" = 1) ∧
      (∀ x, x ≠ "pp" → x ≠ "pok" → x ≠ "pk" → σ'.vars x = σ.vars x) ∧
      σ'.out = σ.out ∧ σ'.inp = σ.inp ∧ σ'.arrs = σ.arrs := by
  set b := σ.vars "pb" with hbdef
  set W := σ.vars "Wl" with hWdef
  have r1 := Run.assign (B := B) (σ := σ) (x := "pp") (e := .lit 1) (v := 1) (evalB_lit (by omega))
  have r2 := Run.assign (B := B) (σ := σ.setVar "pp" 1) (x := "pok") (e := .lit 1) (v := 1)
    (evalB_lit (by omega))
  set σ0 := (σ.setVar "pp" 1).setVar "pok" 1 with hσ0
  have hI0 : ∀ v, PowInv b W n 0 σ (σ0.setVar "pk" v) := by
    intro v
    refine ⟨by simp [σ0, hbdef], by simp [σ0, hWdef], by simp [σ0], by simp [σ0], by simp [σ0],
      fun x a b' c => by simp [σ0, a, b', c], by simp [σ0]; omega, Or.inl ⟨by simp [σ0], by simp [σ0],
        by simp; omega⟩⟩
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := "pk") (e := .lit n) (body := powStep) (N := n)
    (K := 12) (σ := σ0) (fun k τ => PowInv b W n k σ τ) hn (fun _ _ _ _ _ => evalB_lit hn) (hI0 0)
    (fun k hk τ hτ hi => by
      obtain ⟨τ', hr, hpk, hI'⟩ := powStep_run (B := B) (by omega) hbB hWB hk hτ
      refine ⟨τ', hr, by rw [hpk, hi], ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI'
      exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
        fun x a b' c => by simp [c, h6 x a b' c], by simp [h7], by simpa using h8⟩)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI
  refine ⟨σ', (Run.seq r1 (Run.seq r2 hr)).mono (by simp [Expr.size]; omega), ?_, ?_, h6, h3, h4, h5⟩
  · rcases h8 with ⟨e1, -, e3⟩ | ⟨e1, e3⟩
    · exact ⟨fun _ => e3, fun _ => e1⟩
    · exact ⟨fun h => by omega, fun h => by omega⟩
  · rcases h8 with ⟨e1, -⟩ | ⟨e1, -⟩
    · exact Or.inr e1
    · exact Or.inl e1

/-! ### Writing with a check of the bound -/

/-- Write the value of `e` and set `ovf` if it is not below the scalar `Ob`. -/
def wChk (e : Expr) : Com :=
  .seq (.write e) (.ite (.lt e (.var "Ob")) .skip (.assign "ovf" (.lit 1)))

/-- **Writing with a check.** The value is written, and `ovf` is set
exactly when it is not below `Ob`. -/
theorem wChk_run {B v : ℕ} {e : Expr} {σ : Env} (he : ∀ o, e.evalB B { σ with out := o } = some v)
    (hO : σ.vars "Ob" < B) (hB : 1 < B) :
    ∃ σ', Run B (wChk e) σ σ' (2 * e.size + 6) ∧ σ'.out = σ.out ++ [v] ∧ σ'.inp = σ.inp ∧
      σ'.arrs = σ.arrs ∧ (∀ x, x ≠ "ovf" → σ'.vars x = σ.vars x) ∧
      (v < σ.vars "Ob" → σ'.vars "ovf" = σ.vars "ovf") ∧
      (¬ v < σ.vars "Ob" → σ'.vars "ovf" = 1) := by
  have r1 := Run.write (B := B) (σ := σ) (e := e) (v := v) (by simpa using he σ.out)
  set τ := { σ with out := σ.out ++ [v] } with hτ
  have hev : e.evalB B τ = some v := he _
  have hOv : (Expr.var "Ob").evalB B τ = some (σ.vars "Ob") := evalB_var (by simpa [hτ] using hO)
  by_cases hlt : v < σ.vars "Ob"
  · refine ⟨τ, (Run.seq r1 (Run.ite_true (by rw [evalB_condLt hev hOv]; simpa using hlt)
      Run.skip)).mono (by simp [Cond.size, Expr.size]; omega), rfl, rfl, rfl, fun x _ => rfl,
      fun _ => rfl, fun h => absurd hlt h⟩
  · refine ⟨τ.setVar "ovf" 1, (Run.seq r1 (Run.ite_false (by rw [evalB_condLt hev hOv]; simpa using hlt)
      (Run.assign (evalB_lit (by omega))))).mono (by simp [Cond.size, Expr.size]; omega),
      by simp [hτ], by simp [hτ], by simp [hτ], fun x hx => by simp [hx, hτ], fun h => absurd h hlt,
      fun _ => by simp⟩

end Lax185574Proofs.CompRam
