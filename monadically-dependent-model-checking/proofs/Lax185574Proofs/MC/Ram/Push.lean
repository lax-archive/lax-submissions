import Lax185574Proofs.Words.ForLoop

/-!
Arrays filled from the front, for the glue program of thm:mc.

`Filled a pv l τ` says that the array `a` holds the list `l` in its
first `|l|` cells and that the scalar `pv` is `|l|`. `push1 a pv e`
appends the value of `e`. `forUp_append` proves a counting loop whose
round `k` appends `f k`, so nested loops that append the members of
`flatMap`s are proved by nesting the rule.
-/

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The array `a` starts with `l`, and the scalar `pv` is `|l|`. -/
structure Filled (a pv : String) (l : List ℕ) (τ : Env) : Prop where
  pos : τ.vars pv = l.length
  get : ∀ i (h : i < l.length), (τ.arrs a)[i]? = some l[i]

theorem Filled.length_le {a pv : String} {l : List ℕ} {τ : Env} (h : Filled a pv l τ) :
    l.length ≤ (τ.arrs a).length := by
  by_contra hc
  have := h.get (τ.arrs a).length (by omega)
  rw [List.getElem?_eq_none le_rfl] at this
  exact absurd this (by simp)

theorem Filled.congr {a pv : String} {l : List ℕ} {τ τ' : Env} (h : Filled a pv l τ)
    (hp : τ'.vars pv = τ.vars pv) (ha : τ'.arrs a = τ.arrs a) : Filled a pv l τ' :=
  ⟨by rw [hp, h.pos], by rw [ha]; exact h.get⟩

theorem Filled.setVar {a pv : String} {l : List ℕ} {τ : Env} (h : Filled a pv l τ) {y : String}
    (hy : y ≠ pv) (v : ℕ) : Filled a pv l (τ.setVar y v) :=
  h.congr (by simp [Ne.symm hy]) (by simp)

theorem Filled.empty (a pv : String) (τ : Env) : Filled a pv [] (τ.setVar pv 0) :=
  ⟨by simp, fun i h => absurd h (by simp)⟩

/-- Append the value of `e`. -/
def push1 (a pv : String) (e : Expr) : Com :=
  .seq (.store a (.var pv) e) (.assign pv (.add (.var pv) (.lit 1)))

theorem push1_run {B : ℕ} {a pv : String} {e : Expr} {l : List ℕ} {τ : Env} {v : ℕ}
    (h : Filled a pv l τ) (he : e.evalB B τ = some v) (hcap : l.length < (τ.arrs a).length)
    (hB : l.length + 1 < B) :
    ∃ τ', Run B (push1 a pv e) τ τ' (6 + e.size) ∧ Filled a pv (l ++ [v]) τ' ∧
      (∀ y, y ≠ pv → τ'.vars y = τ.vars y) ∧ (∀ b, b ≠ a → τ'.arrs b = τ.arrs b) ∧
      (τ'.arrs a).length = (τ.arrs a).length ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hp := h.pos
  refine ⟨(τ.setArr a l.length v).setVar pv (l.length + 1), ?_, ⟨by simp, ?_⟩,
    fun y hy => by simp [hy], fun b hb => by simp [hb], by simp, by simp, by simp⟩
  · refine (Run.seq (Run.store (idx := l.length) (v := v) (evalB_var (by omega) |>.trans
      (by rw [hp])) he hcap) (Run.assign ?_)).mono (by simp; omega)
    simp [hp]; omega
  · intro i hi
    simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hil : l.length = i
    · subst hil; simp [hcap]
    · rw [if_neg hil, h.get i (by omega), List.getElem_append_left (by omega)]

/-- **Loops that append.** Round `k` of the loop appends `f k`, keeps
the context `P` and costs at most `K`. -/
theorem forUp_append {B : ℕ} {i : String} {e : Expr} {body : Com} {N K : ℕ} {a pv : String}
    (hi : i ≠ pv) (f : ℕ → List ℕ) (P : Env → Prop) (hPi : ∀ τ v, P τ → P (τ.setVar i v))
    {σ : Env} {l : List ℕ} (hN : N < B) (hP : P σ) (hσ : Filled a pv l σ)
    (he : ∀ τ, P τ → e.evalB B τ = some N)
    (hstep : ∀ k < N, ∀ τ, P τ → τ.vars i = k →
      Filled a pv (l ++ (List.range k).flatMap f) τ →
      ∃ τ', Run B body τ τ' K ∧ τ'.vars i = k ∧ P τ' ∧
        Filled a pv (l ++ (List.range (k + 1)).flatMap f) τ') :
    ∃ σ', Run B (forUp i e body) σ σ' (N * (K + e.size + 7) + e.size + 5) ∧ P σ' ∧
      σ'.vars i = N ∧ Filled a pv (l ++ (List.range N).flatMap f) σ' := by
  obtain ⟨σ', hr, ⟨hP', hF'⟩, hi'⟩ := forUp_run (B := B) (i := i) (e := e) (body := body) (N := N)
    (K := K) (fun k τ => P τ ∧ Filled a pv (l ++ (List.range k).flatMap f) τ) hN
    (fun k _ τ hI _ => he τ hI.1) ⟨hPi σ 0 hP, by simpa using hσ.setVar hi 0⟩
    (fun k hk τ hI hik => by
      obtain ⟨τ', hr, hik', hP', hF'⟩ := hstep k hk τ hI.1 hik hI.2
      exact ⟨τ', hr, hik', hPi τ' _ hP', hF'.setVar hi _⟩)
  exact ⟨σ', hr, hP', hi', hF'⟩

end Lax185574Proofs.MC

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- Append the values of the expressions `es`. -/
def pushL (a pv : String) : List Expr → Com
  | [] => .skip
  | e :: es => .seq (push1 a pv e) (pushL a pv es)

/-- The expressions `es` have the values `vs` in every environment that
agrees with `τ` outside `pv` and `a`. -/
def EvalsTo (B : ℕ) (a pv : String) (τ : Env) (es : List Expr) (vs : List ℕ) : Prop :=
  ∀ τ', (∀ y, y ≠ pv → τ'.vars y = τ.vars y) → (∀ b, b ≠ a → τ'.arrs b = τ.arrs b) →
    List.Forall₂ (fun e v => e.evalB B τ' = some v) es vs

theorem pushL_run {B : ℕ} {a pv : String} :
    ∀ {es : List Expr} {vs : List ℕ} {l : List ℕ} {τ : Env}, Filled a pv l τ →
      EvalsTo B a pv τ es vs → l.length + vs.length ≤ (τ.arrs a).length →
      l.length + vs.length < B →
      ∃ τ', Run B (pushL a pv es) τ τ' (1 + 7 * es.length + (es.map Expr.size).sum) ∧
        Filled a pv (l ++ vs) τ' ∧
        (∀ y, y ≠ pv → τ'.vars y = τ.vars y) ∧ (∀ b, b ≠ a → τ'.arrs b = τ.arrs b) ∧
        (τ'.arrs a).length = (τ.arrs a).length ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp
  | [], vs, l, τ, h, hev, _, _ => by
      have := hev τ (fun _ _ => rfl) (fun _ _ => rfl)
      rw [List.forall₂_nil_left_iff] at this
      subst this
      exact ⟨τ, Run.skip.mono (by simp), by simpa using h, fun _ _ => rfl, fun _ _ => rfl,
        rfl, rfl, rfl⟩
  | e :: es, vs, l, τ, h, hev, hcap, hB => by
      have h0 := hev τ (fun _ _ => rfl) (fun _ _ => rfl)
      obtain ⟨v, vs', he, hes, rfl⟩ := List.forall₂_cons_left_iff.mp h0
      simp only [List.length_cons] at hcap hB
      obtain ⟨τ₁, r₁, F₁, fv₁, fa₁, fl₁, fo₁, fi₁⟩ := push1_run h he (by omega) (by omega)
      have hev' : EvalsTo B a pv τ₁ es vs' := by
        intro τ' hv ha
        have := hev τ' (fun y hy => (hv y hy).trans (fv₁ y hy)) (fun b hb => (ha b hb).trans
          (fa₁ b hb))
        exact (List.forall₂_cons.mp this).2
      obtain ⟨τ₂, r₂, F₂, fv₂, fa₂, fl₂, fo₂, fi₂⟩ := pushL_run F₁ hev'
        (by simp [fl₁]; omega) (by simp; omega)
      refine ⟨τ₂, (Run.seq r₁ r₂).mono (by simp; omega), by simpa using F₂,
        fun y hy => (fv₂ y hy).trans (fv₁ y hy), fun b hb => (fa₂ b hb).trans (fa₁ b hb),
        fl₂.trans fl₁, fo₂.trans fo₁, fi₂.trans fi₁⟩

end Lax185574Proofs.MC
