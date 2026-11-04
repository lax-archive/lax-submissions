import Lax808846Proofs.Spec
import Lax808846Proofs.Frame

/-!
Counting loops in IMP+.

`forUp i e body` sets the scalar `i` to `0` and runs `body` while `i` is
below the value of `e`, incrementing `i` after each round. The rule
`forUp_run` proves such a loop from an invariant indexed by the number
of finished rounds. The body must leave `i` alone, and the invariant is
stated for the environment after the increment.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The counting loop: set `i` to `0`, then run `body` and increment `i` while `i < e`. -/
def forUp (i : String) (e : Expr) (body : Com) : Com :=
  .seq (.assign i (.lit 0))
    (.while (.lt (.var i) e) (.seq body (.assign i (.add (.var i) (.lit 1)))))

/-- **The counting loop rule.** `I k` holds after `k` rounds, the bound
`e` evaluates to `N` throughout, and each round costs at most `K`. -/
theorem forUp_run {B : ℕ} {i : String} {e : Expr} {body : Com} {N K : ℕ}
    (I : ℕ → Env → Prop) {σ : Env} (hN : N < B)
    (he : ∀ k ≤ N, ∀ τ, I k τ → τ.vars i = k → e.evalB B τ = some N)
    (h0 : I 0 (σ.setVar i 0))
    (hstep : ∀ k < N, ∀ τ, I k τ → τ.vars i = k →
      ∃ τ', Run B body τ τ' K ∧ τ'.vars i = k ∧ I (k + 1) (τ'.setVar i (k + 1))) :
    ∃ σ', Run B (forUp i e body) σ σ' (N * (K + e.size + 7) + e.size + 5) ∧
      I N σ' ∧ σ'.vars i = N := by
  let J : Env → Prop := fun τ => ∃ k ≤ N, τ.vars i = k ∧ I k τ
  obtain ⟨σ', hrun, ⟨k, hk, hik, hI⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var i) e)
      (c := .seq body (.assign i (.add (.var i) (.lit 1)))) J (fun τ => N - τ.vars i)
      (K + 4)
      (fun τ ⟨k, hk, hik, hI⟩ => ⟨_, evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)⟩)
      (by
        rintro τ ⟨k, hk, hik, hI⟩ hc
        have hkN : k < N := by
          rw [evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)] at hc
          simp only [Option.some.injEq, decide_eq_true_eq] at hc
          omega
        obtain ⟨τ', hr, hi', hI'⟩ := hstep k hkN τ hI hik
        refine ⟨τ'.setVar i (k + 1), (Run.seq hr (Run.assign ?_)).mono (by simp),
          ⟨k + 1, hkN, by simp, hI'⟩, by simp; omega⟩
        simp [hi']; omega)
      (show J (σ.setVar i 0) from ⟨0, Nat.zero_le _, by simp, h0⟩)
  have hkN : k = N := by
    rw [evalB_condLt (evalB_var (by omega)) (he k hk σ' hI hik)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hkN] at hI hik
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono ?_, hI, hik⟩
  simp only [Cond.size, Expr.size]
  have : N - (σ.setVar i 0).vars i = N := by simp
  rw [this]
  nlinarith

/-- A command never changes the length of an array. -/
theorem bigStep_length_arrs {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStep c σ σ' k) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_length_arrs {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (a : String) : (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hbs⟩ := h.bigStep; exact bigStep_length_arrs hbs a

/-- Row-major positions of a matrix with `n` columns are distinct. -/
theorem rowMajor_inj {n t t' u u' : ℕ} (hu : u < n) (hu' : u' < n)
    (h : t * n + u = t' * n + u') : t = t' ∧ u = u' := by
  have h1 : (t * n + u) / n = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu]; simp
  have h2 : (t' * n + u') / n = t' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu']; simp
  have ht : t = t' := by rw [← h1, ← h2, h]
  subst ht
  exact ⟨rfl, by omega⟩

theorem rowMajor_lt {n m t u : ℕ} (ht : t < m) (hu : u < n) : t * n + u < m * n := by
  have : (t + 1) * n ≤ m * n := Nat.mul_le_mul_right _ ht
  rw [Nat.add_mul, one_mul] at this
  omega

end Lax185574Proofs.Words
