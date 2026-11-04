import Lax185574Proofs.MainRam.Defs
import Lax185574Proofs.Words.Computes

/-!
The unpairing program of a thread: it reads `i` and writes
`r, d, 0, 1, j`, the word of `(r, d, 1/j)`, where `i` is the double
pairing of `r`, `d` and `j - 1`. The square root in `Nat.unpair` is
found by counting up, in `O(i)` steps.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Simulation

/-- `s := ⌊√n⌋` by counting. -/
def sqrtCom : Com :=
  .seq (.assign "s" (.lit 0))
    (.while (.lt (.mul (.add (.var "s") (.lit 1)) (.add (.var "s") (.lit 1)))
        (.add (.var "n") (.lit 1)))
      (.assign "s" (.add (.var "s") (.lit 1))))

/-- `(p1, p2) := Nat.unpair n`. -/
def unpCom : Com :=
  .seq sqrtCom (.seq (.assign "d" (.sub (.var "n") (.mul (.var "s") (.var "s"))))
    (.ite (.lt (.var "d") (.var "s"))
      (.seq (.assign "p1" (.var "d")) (.assign "p2" (.var "s")))
      (.seq (.assign "p1" (.var "s")) (.assign "p2" (.sub (.var "d") (.var "s"))))))

theorem sqrtCom_run {B N : ℕ} {σ : Env} (hn : σ.vars "n" = N) (hB : (N + 2) ^ 2 < B) :
    ∃ σ', Run B sqrtCom σ σ' (16 * (N + 1) + 14) ∧ σ'.vars "s" = Nat.sqrt N ∧
      σ'.vars "n" = N ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "s" → σ'.vars y = σ.vars y := by
  have hN2 : N + 2 ≤ (N + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  set σ₀ := σ.setVar "s" 0
  have r0 : Run B (.assign "s" (.lit 0)) σ σ₀ (1 + (Expr.lit 0).size) :=
    Run.assign (evalB_lit (by omega))
  set b : Cond := .lt (.mul (.add (.var "s") (.lit 1)) (.add (.var "s") (.lit 1)))
    (.add (.var "n") (.lit 1))
  set I : Env → Prop := fun τ => τ.vars "n" = N ∧ τ.vars "s" * τ.vars "s" ≤ N ∧
    τ.inp = σ.inp ∧ τ.out = σ.out ∧ ∀ y, y ≠ "s" → τ.vars y = σ.vars y
  have hev : ∀ τ, I τ → ∃ v, b.evalB B τ = some v ∧
      (v = true ↔ (τ.vars "s" + 1) * (τ.vars "s" + 1) < N + 1) := by
    rintro τ ⟨h1, h2, -⟩
    have hs : τ.vars "s" ≤ N := by nlinarith
    have hs1 : (τ.vars "s" + 1) * (τ.vars "s" + 1) < B := by nlinarith
    have e1 : (Expr.add (.var "s") (.lit 1)).evalB B τ = some (τ.vars "s" + 1) :=
      evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega)
    have e2 : (Expr.mul (.add (.var "s") (.lit 1)) (.add (.var "s") (.lit 1))).evalB B τ =
        some ((τ.vars "s" + 1) * (τ.vars "s" + 1)) := evalB_bin e1 e1 (by simpa using hs1)
    have e3 : (Expr.add (.var "n") (.lit 1)).evalB B τ = some (N + 1) := by
      rw [← h1]; exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega)
    exact evalB_condLt_isSome e2 e3
  have hI0 : I σ₀ := by
    refine ⟨by simp [σ₀, Env.setVar, hn], by simp [σ₀, Env.setVar], rfl, rfl, ?_⟩
    intro y hy; simp [σ₀, Env.setVar, hy]
  obtain ⟨σ', hr, ⟨h1, h2, h3, h4, h5⟩, hf⟩ := Run.while_count I (fun τ => N + 1 - τ.vars "s") 4
    (fun τ hτ => (hev τ hτ).imp fun v h => h.1) (fun τ hτ ht => by
      obtain ⟨v, hv, hiff⟩ := hev τ hτ
      rw [hv] at ht; cases ht
      have hlt := hiff.1 rfl
      obtain ⟨k1, k2, k3, k4, k5⟩ := hτ
      have hs : τ.vars "s" ≤ N := by nlinarith
      have hsB : τ.vars "s" < B := by omega
      have h1B : 1 < B := by omega
      have hs1B : τ.vars "s" + 1 < B := by omega
      refine ⟨τ.setVar "s" (τ.vars "s" + 1), (Run.assign (B := B) (σ := τ) (x := "s")
        (e := .add (.var "s") (.lit 1)) (evalB_bin (evalB_var hsB) (evalB_lit h1B)
          (by simpa using hs1B))).mono (by simp), ⟨?_, ?_, k3, k4, ?_⟩, ?_⟩
      · simp [Env.setVar]; exact k1
      · have e : (τ.setVar "s" (τ.vars "s" + 1)).vars "s" = τ.vars "s" + 1 := by
          simp [Env.setVar]
        rw [e]; omega
      · intro y hy; simp [Env.setVar, hy]; exact k5 y hy
      · simp [Env.setVar]; omega) hI0
  obtain ⟨v, hv, hiff⟩ := hev σ' ⟨h1, h2, h3, h4, h5⟩
  rw [hv] at hf; cases hf
  have hnot : ¬ (σ'.vars "s" + 1) * (σ'.vars "s" + 1) < N + 1 := fun h => by
    have := hiff.2 h; cases this
  have hsq : σ'.vars "s" = Nat.sqrt N := Nat.eq_sqrt.mpr ⟨h2, by omega⟩
  have hb : b.size = 11 := rfl
  have hs0 : σ₀.vars "s" = 0 := by simp [σ₀, Env.setVar]
  refine ⟨σ', (r0.seq hr).mono ?_, hsq, h1, h3, h4, h5⟩
  rw [hb, hs0]
  simp only [Expr.size]
  omega

theorem unpCom_run {B N : ℕ} {σ : Env} (hn : σ.vars "n" = N) (hB : (N + 2) ^ 2 < B) :
    ∃ σ', Run B unpCom σ σ' (16 * N + 46) ∧ σ'.vars "p1" = (Nat.unpair N).1 ∧
      σ'.vars "p2" = (Nat.unpair N).2 ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "s" → y ≠ "d" → y ≠ "p1" → y ≠ "p2" → σ'.vars y = σ.vars y := by
  have hN2 : N + 2 ≤ (N + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨σ₁, r1, hs, hn1, hi1, ho1, hf1⟩ := sqrtCom_run hn hB
  have hsN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hsN' : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
  set q := Nat.sqrt N
  set σ₂ := σ₁.setVar "d" (N - q * q)
  have r2 : Run B (.assign "d" (.sub (.var "n") (.mul (.var "s") (.var "s")))) σ₁ σ₂ 6 := by
    have := Run.assign (B := B) (σ := σ₁) (x := "d")
      (e := .sub (.var "n") (.mul (.var "s") (.var "s")))
      (evalB_bin (evalB_var (by omega)) (evalB_bin (evalB_var (by omega)) (evalB_var (by omega))
        (by simp; rw [hs]; nlinarith)) (by simp; omega))
    simp only [Bop.apply_sub, Bop.apply_mul, hn1, hs] at this
    exact this.mono (by simp)
  have hd : σ₂.vars "d" = N - q * q := by simp [σ₂, Env.setVar]
  have hs2 : σ₂.vars "s" = q := by simp [σ₂, Env.setVar, hs]
  have hunp : Nat.unpair N = if N - q * q < q then (N - q * q, q) else (q, N - q * q - q) := rfl
  by_cases hlt : N - q * q < q
  · set σ₃ := σ₂.setVar "p1" (N - q * q)
    set σ₄ := σ₃.setVar "p2" q
    have r3 : Run B (.seq (.assign "p1" (.var "d")) (.assign "p2" (.var "s"))) σ₂ σ₄ 4 := by
      have a1 := Run.assign (B := B) (σ := σ₂) (x := "p1") (e := .var "d")
        (evalB_var (by rw [hd]; omega))
      rw [hd] at a1
      have a2 := Run.assign (B := B) (σ := σ₃) (x := "p2") (e := .var "s")
        (evalB_var (by simp [σ₃, Env.setVar, hs2]; omega))
      have : σ₃.vars "s" = q := by simp [σ₃, Env.setVar, hs2]
      rw [this] at a2
      exact (a1.seq a2).mono (by simp)
    have r4 : Run B (.ite (.lt (.var "d") (.var "s"))
        (.seq (.assign "p1" (.var "d")) (.assign "p2" (.var "s")))
        (.seq (.assign "p1" (.var "s")) (.assign "p2" (.sub (.var "d") (.var "s"))))) σ₂ σ₄ 8 :=
      (Run.ite_true (by rw [evalB_condLt (evalB_var (by rw [hd]; omega))
        (evalB_var (by rw [hs2]; omega)), hd, hs2]; simp [hlt]) r3).mono (by simp)
    refine ⟨σ₄, (r1.seq (r2.seq r4)).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₄, σ₃, Env.setVar, hunp, hlt]
    · simp [σ₄, Env.setVar, hunp, hlt]
    · simp [σ₄, σ₃, σ₂, Env.setVar, hi1]
    · simp [σ₄, σ₃, σ₂, Env.setVar, ho1]
    · intro y h1 h2 h3 h4
      simp [σ₄, σ₃, σ₂, Env.setVar, h2, h3, h4]; exact hf1 y h1
  · set σ₃ := σ₂.setVar "p1" q
    set σ₄ := σ₃.setVar "p2" (N - q * q - q)
    have r3 : Run B (.seq (.assign "p1" (.var "s")) (.assign "p2" (.sub (.var "d") (.var "s"))))
        σ₂ σ₄ 6 := by
      have a1 := Run.assign (B := B) (σ := σ₂) (x := "p1") (e := .var "s")
        (evalB_var (by rw [hs2]; omega))
      rw [hs2] at a1
      have hd3 : σ₃.vars "d" = N - q * q := by simp [σ₃, Env.setVar, hd]
      have hs3 : σ₃.vars "s" = q := by simp [σ₃, Env.setVar, hs2]
      have a2 := Run.assign (B := B) (σ := σ₃) (x := "p2") (e := .sub (.var "d") (.var "s"))
        (evalB_bin (evalB_var (by rw [hd3]; omega)) (evalB_var (by rw [hs3]; omega))
          (by simp; rw [hd3, hs3]; omega))
      simp only [Bop.apply_sub, hd3, hs3] at a2
      exact (a1.seq a2).mono (by simp)
    have r4 : Run B (.ite (.lt (.var "d") (.var "s"))
        (.seq (.assign "p1" (.var "d")) (.assign "p2" (.var "s")))
        (.seq (.assign "p1" (.var "s")) (.assign "p2" (.sub (.var "d") (.var "s"))))) σ₂ σ₄ 10 :=
      (Run.ite_false (by rw [evalB_condLt (evalB_var (by rw [hd]; omega))
        (evalB_var (by rw [hs2]; omega)), hd, hs2]; simp [hlt]) r3).mono (by simp)
    refine ⟨σ₄, (r1.seq (r2.seq r4)).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₄, σ₃, Env.setVar, hunp, hlt]
    · simp [σ₄, Env.setVar, hunp, hlt]
    · simp [σ₄, σ₃, σ₂, Env.setVar, hi1]
    · simp [σ₄, σ₃, σ₂, Env.setVar, ho1]
    · intro y h1 h2 h3 h4
      simp [σ₄, σ₃, σ₂, Env.setVar, h2, h3, h4]; exact hf1 y h1

/-- Read `i`, unpair twice, write `r, d, 0, 1, j`. -/
def uTail : Com :=
  .seq (.write (.var "p1")) (.seq (.write (.var "p2")) (.seq (.write (.lit 0))
    (.seq (.write (.lit 1)) (.write (.add (.var "jj") (.lit 1))))))

def uCom : Com :=
  .seq (.read "i") (.seq (.assign "n" (.var "i")) (.seq unpCom (.seq (.assign "a" (.var "p1"))
    (.seq (.assign "jj" (.var "p2")) (.seq (.assign "n" (.var "a")) (.seq unpCom uTail))))))

/-- The layout of the unpairing program. -/
def uLayout : Layout where
  scalars := ["i", "n", "s", "d", "p1", "p2", "a", "jj"]
  arrays := []
  temps := 4

theorem uCom_ok : Com.Ok uLayout uCom := by
  simp [uCom, uTail, unpCom, sqrtCom, uLayout, Com.Ok, Cond.Ok, Expr.Ok, condExpr]

theorem uTail_run {B : ℕ} {σ : Env} (h1 : σ.vars "p1" < B) (h2 : σ.vars "p2" < B)
    (h3 : σ.vars "jj" + 1 < B) (hB : 1 < B) :
    ∃ σ', Run B uTail σ σ' 12 ∧
      σ'.out = σ.out ++ [σ.vars "p1", σ.vars "p2", 0, 1, σ.vars "jj" + 1] := by
  have w1 := Run.write (B := B) (σ := σ) (evalB_var h1)
  set τ₁ := { σ with out := σ.out ++ [σ.vars "p1"] }
  have w2 := Run.write (B := B) (σ := τ₁) (e := .var "p2") (evalB_var h2)
  set τ₂ := { τ₁ with out := τ₁.out ++ [τ₁.vars "p2"] }
  have w3 := Run.write (B := B) (σ := τ₂) (e := .lit 0) (evalB_lit (by omega))
  set τ₃ := { τ₂ with out := τ₂.out ++ [0] }
  have w4 := Run.write (B := B) (σ := τ₃) (e := .lit 1) (evalB_lit hB)
  set τ₄ := { τ₃ with out := τ₃.out ++ [1] }
  have w5 := Run.write (B := B) (σ := τ₄) (e := .add (.var "jj") (.lit 1))
    (evalB_bin (evalB_var (by simp [τ₄, τ₃, τ₂, τ₁]; omega)) (evalB_lit hB)
      (by simp [τ₄, τ₃, τ₂, τ₁]; omega))
  refine ⟨_, (w1.seq (w2.seq (w3.seq (w4.seq w5)))).mono (by simp), ?_⟩
  simp [τ₄, τ₃, τ₂, τ₁]

/-- **The unpairing program.** -/
theorem unpairSpec : UnpairSpec (compileProgram uLayout uCom) (uLayout.const * 120 + 64) := by
  intro w i x hadm
  set c := uLayout.const * 120 + 64 with hc
  have hc64 : 64 ≤ c := by omega
  have hii := hadm i (List.mem_cons_self)
  have hsq : (i + 2) ^ 2 ≤ (i + i + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hsq1 : 1 ≤ (i + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hiB : (i + 2) ^ 2 < 2 ^ w := by
    have : 2 * (i + 2) ^ 2 ≤ c * (i + i + 2) ^ 2 := Nat.mul_le_mul (by omega) hsq
    omega
  have hi2 : i + 2 ≤ (i + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h64 : 64 ≤ 2 ^ w := le_trans hc64 (le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hii)
  set B := 2 ^ w
  -- the run
  set σ₀ := initEnv (fun _ => 0) (i :: x)
  set σ₁ := { σ₀.setVar "i" i with inp := x }
  have r1 : Run B (.read "i") σ₀ σ₁ 1 := Run.read rfl
  have hi1 : σ₁.vars "i" = i := by simp [σ₁, Env.setVar]
  set σ₂ := σ₁.setVar "n" i
  have r2 : Run B (.assign "n" (.var "i")) σ₁ σ₂ 2 := by
    have := Run.assign (B := B) (σ := σ₁) (x := "n") (e := .var "i") (evalB_var (by rw [hi1]; omega))
    rw [hi1] at this; exact this.mono (by simp)
  obtain ⟨σ₃, r3, hp1, hp2, hin3, hout3, hf3⟩ := unpCom_run (N := i) (σ := σ₂)
    (by simp [σ₂, Env.setVar]) hiB
  set a := (Nat.unpair i).1
  set jj := (Nat.unpair i).2
  have ha : a ≤ i := Nat.unpair_left_le i
  have hjj : jj ≤ i := Nat.unpair_right_le i
  set σ₄ := σ₃.setVar "a" a
  have r4 : Run B (.assign "a" (.var "p1")) σ₃ σ₄ 2 := by
    have := Run.assign (B := B) (σ := σ₃) (x := "a") (e := .var "p1")
      (evalB_var (by rw [hp1]; omega))
    rw [hp1] at this; exact this.mono (by simp)
  set σ₅ := σ₄.setVar "jj" jj
  have r5 : Run B (.assign "jj" (.var "p2")) σ₄ σ₅ 2 := by
    have e : σ₄.vars "p2" = jj := by simp [σ₄, Env.setVar, hp2]
    have := Run.assign (B := B) (σ := σ₄) (x := "jj") (e := .var "p2")
      (evalB_var (by rw [e]; omega))
    rw [e] at this; exact this.mono (by simp)
  set σ₆ := σ₅.setVar "n" a
  have r6 : Run B (.assign "n" (.var "a")) σ₅ σ₆ 2 := by
    have e : σ₅.vars "a" = a := by simp [σ₅, σ₄, Env.setVar]
    have := Run.assign (B := B) (σ := σ₅) (x := "n") (e := .var "a")
      (evalB_var (by rw [e]; omega))
    rw [e] at this; exact this.mono (by simp)
  have haB : (a + 2) ^ 2 < B := lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hiB
  obtain ⟨σ₇, r7, hq1, hq2, hin7, hout7, hf7⟩ := unpCom_run (N := a) (σ := σ₆)
    (by simp [σ₆, Env.setVar]) haB
  have hjj7 : σ₇.vars "jj" = jj := by
    rw [hf7 "jj" (by decide) (by decide) (by decide) (by decide)]
    simp [σ₆, σ₅, Env.setVar]
  have hr : (Nat.unpair a).1 ≤ i := le_trans (Nat.unpair_left_le a) ha
  have hd : (Nat.unpair a).2 ≤ i := le_trans (Nat.unpair_right_le a) ha
  obtain ⟨σ₈, r8, hout8⟩ := uTail_run (B := B) (σ := σ₇) (by rw [hq1]; omega) (by rw [hq2]; omega)
    (by rw [hjj7]; omega) (by omega)
  have hrun : Run B uCom σ₀ σ₈ (32 * i + 113) := by
    unfold uCom
    refine (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))).mono ?_
    have : 16 * a + 46 ≤ 16 * i + 46 := by omega
    omega
  have hout : σ₈.out = triWord i := by
    rw [hout8, hq1, hq2, hjj7, hout7]
    simp only [σ₆, σ₅, σ₄, Env.setVar]
    rw [hout3]
    simp [σ₂, σ₁, σ₀, initEnv, triWord, triR, triD, triJ, a, jj]
  obtain ⟨k, hk, hbs⟩ := hrun
  have hfit : uLayout.FitsWords B w :=
    ⟨by omega, le_rfl, by simp [Layout.span, uLayout]; omega⟩
  obtain ⟨t, ht, hrunT⟩ := compileProgram_runsTo hfit uCom_ok (fun v hv => by
    have h := hadm v hv
    have : v < (i + v + 2) ^ 2 := by nlinarith
    have : (i + v + 2) ^ 2 ≤ c * (i + v + 2) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega) hbs
  rw [hout] at hrunT
  refine ⟨t, le_trans ht ?_, hrunT⟩
  have h1 : uLayout.const * k ≤ uLayout.const * (32 * i + 113) := Nat.mul_le_mul_left _ hk
  have h2 : 32 * i + 113 ≤ 120 * (i + 2) ^ 2 := by nlinarith
  have h3 : uLayout.const * (32 * i + 113) ≤ uLayout.const * (120 * (i + 2) ^ 2) :=
    Nat.mul_le_mul_left _ h2
  have h4 : c * (i + 2) ^ 2 = uLayout.const * (120 * (i + 2) ^ 2) + 64 * (i + 2) ^ 2 := by
    rw [hc]; ring
  omega

end Lax185574Proofs.MainRam
