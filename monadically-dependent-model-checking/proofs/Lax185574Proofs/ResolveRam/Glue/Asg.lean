import Lax185574Proofs.ResolveRam.Glue.TailR

/-!
Blocks of assignments for the cases of a later round.

`asgs l` assigns the expressions of `l` in order. If no expression reads
a scalar that the block assigns, the block assigns the values of the
expressions in the environment before it (`asgs_run`). `stPlan l`
stores the pairs of `l` into the array `PR` at the positions
`0, 1, 2, …` and sets `np` (`stPlan_run`), for the plan of a new state.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue

/-- The scalars that an expression reads. -/
def exRv : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get _ i => (exRv i)
  | .bin _ e f => (exRv e) ++ (exRv f)

/-- The arrays that an expression reads. -/
def exRa : Expr → List String
  | .lit _ => []
  | .var _ => []
  | .get a i => a :: (exRa i)
  | .bin _ e f => (exRa e) ++ (exRa f)

theorem evalB_congr {B : ℕ} {σ σ' : Env} (e : Expr) (hv : ∀ x ∈ (exRv e), σ'.vars x = σ.vars x)
    (ha : ∀ a ∈ (exRa e), σ'.arrs a = σ.arrs a) : e.evalB B σ' = e.evalB B σ := by
  induction e with
  | lit n => rfl
  | var x => simp only [Expr.evalB]; rw [hv x (by simp [exRv])]
  | get a i ih =>
    simp only [Expr.evalB]
    rw [ih (fun x hx => hv x (by simpa [exRv] using hx)) (fun b hb => ha b (by simp [exRa, hb])),
      ha a (by simp [exRa])]
  | bin op e f ihe ihf =>
    simp only [Expr.evalB]
    rw [ihe (fun x hx => hv x (by simp [exRv, hx])) (fun b hb => ha b (by simp [exRa, hb])),
      ihf (fun x hx => hv x (by simp [exRv, hx])) (fun b hb => ha b (by simp [exRa, hb]))]

/-- Assign the expressions in order. -/
def asgs : List (String × Expr) → Com
  | [] => .skip
  | p :: l => .seq (.assign p.1 p.2) (asgs l)

/-- The cost of a block of assignments. -/
def asgK (l : List (String × Expr)) : ℕ := (l.map fun p => 1 + p.2.size).sum + 1

/-- **A block of assignments.** -/
theorem asgs_run {B : ℕ} {l : List (String × Expr)} {f : String → ℕ} {τ : Env}
    (hev : ∀ p ∈ l, p.2.evalB B τ = some (f p.1))
    (hrd : ∀ p ∈ l, ∀ q ∈ l, q.1 ∉ (exRv p.2)) :
    ∃ τ', Run B (asgs l) τ τ' (asgK l) ∧
      (∀ y, y ∈ l.map Prod.fst → τ'.vars y = f y) ∧ (∀ y, y ∉ l.map Prod.fst → τ'.vars y = τ.vars y) ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  induction l generalizing τ with
  | nil => exact ⟨τ, Run.skip.mono (by simp [asgK]), by simp, fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    have h1 := hev p (by simp)
    set τ1 := τ.setVar p.1 (f p.1)
    have hev' : ∀ q ∈ l, q.2.evalB B τ1 = some (f q.1) := by
      intro q hq
      rw [evalB_congr (σ := τ) (σ' := τ1) q.2 (fun x hx => by
        simp only [τ1, Env.setVar]; split_ifs with h
        · subst h; exact absurd hx (hrd q (by simp [hq]) p (by simp))
        · rfl) (fun _ _ => rfl)]
      exact hev q (by simp [hq])
    obtain ⟨τ2, r2, s2, f2, a2, o2, i2⟩ := ih hev' (fun a ha b hb => hrd a (by simp [ha]) b (by simp [hb]))
    refine ⟨τ2, (Run.seq (Run.assign h1) r2).mono (by simp [asgK]; omega), fun y hy => ?_, fun y hy => ?_,
      by rw [a2]; rfl, by rw [o2]; rfl, by rw [i2]; rfl⟩
    · by_cases hy' : y ∈ l.map Prod.fst
      · exact s2 y hy'
      · rw [f2 y hy']
        simp only [List.map_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · simp [τ1]
        · exact absurd hy hy'
    · simp only [List.map_cons, List.mem_cons, not_or] at hy
      rw [f2 y hy.2]; simp [τ1, hy.1]

theorem asgK_le (l : List (String × Expr)) (M : ℕ) (h : ∀ p ∈ l, p.2.size ≤ M) :
    asgK l ≤ l.length * (M + 1) + 1 := by
  unfold asgK
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h p (by simp)
    have := ih (fun q hq => h q (by simp [hq]))
    nlinarith

/-- Store the pairs of a plan into `PR` from position `k`, then set `np`. -/
def stPlanAux : ℕ → List (Expr × Expr) → Com
  | _, [] => .skip
  | k, p :: l => .seq (.store "PR" (.lit (2 * k)) p.1) (.seq (.store "PR" (.lit (2 * k + 1)) p.2)
      (stPlanAux (k + 1) l))

/-- Store a plan. -/
def stPlan (l : List (Expr × Expr)) : Com := .seq (stPlanAux 0 l) (.assign "np" (.lit l.length))

theorem stPlanAux_run {W : ℕ} {l : List (Expr × Expr)} {ps : List (ℕ × ℕ)} {τ : Env} (k : ℕ)
    (hl : l.length = ps.length) (hlen : (τ.arrs "PR").length = W + 1) (hk : 2 * (k + l.length) ≤ W)
    (hev : ∀ i (h : i < l.length), (l[i].1.evalB (W + 1) τ = some (ps[i]'(by omega)).1) ∧
      (l[i].2.evalB (W + 1) τ = some (ps[i]'(by omega)).2))
    (hra : ∀ p ∈ l, "PR" ∉ (exRa p.1) ∧ "PR" ∉ (exRa p.2)) :
    ∃ τ', Run (W + 1) (stPlanAux k l) τ τ' (l.length * ((l.map fun p => p.1.size + p.2.size).sum + 6) + 1) ∧
      (∀ i (h : i < 2 * ps.length), (τ'.arrs "PR")[2 * k + i]? = some ((prW ps)[i]'(by
        rw [length_prW]; omega))) ∧
      (∀ j, j < 2 * k → (τ'.arrs "PR")[j]? = (τ.arrs "PR")[j]?) ∧
      (∀ b, b ≠ "PR" → τ'.arrs b = τ.arrs b) ∧ (τ'.arrs "PR").length = W + 1 ∧
      τ'.vars = τ.vars ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  induction l generalizing ps τ k with
  | nil =>
    have : ps = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    subst this
    exact ⟨τ, Run.skip.mono (by simp), by simp, fun _ _ => rfl, fun _ _ => rfl, hlen, rfl, rfl, rfl⟩
  | cons p l ih =>
    obtain ⟨q, ps', rfl⟩ : ∃ q ps', ps = q :: ps' := List.exists_cons_of_ne_nil (by
      intro h; subst h; simp at hl)
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨e1, e2⟩ := hev 0 (by simp)
    simp only [List.getElem_cons_zero] at e1 e2
    set τ1 := τ.setArr "PR" (2 * k) q.1
    have r1 : Run (W + 1) (.store "PR" (.lit (2 * k)) p.1) τ τ1 (1 + 1 + p.1.size) :=
      Run.store (evalB_lit (by simp at hk; omega)) e1 (by rw [hlen]; simp at hk; omega)
    have e2' : p.2.evalB (W + 1) τ1 = some q.2 := by
      rw [evalB_congr (σ := τ) (σ' := τ1) p.2 (fun _ _ => rfl) (fun b hb => by
        simp only [τ1, Env.setArr]; split_ifs with h
        · subst h; exact absurd hb (hra p (by simp)).2
        · rfl)]; exact e2
    set τ2 := τ1.setArr "PR" (2 * k + 1) q.2
    have r2 : Run (W + 1) (.store "PR" (.lit (2 * k + 1)) p.2) τ1 τ2 (1 + 1 + p.2.size) :=
      Run.store (evalB_lit (by simp at hk; omega)) e2' (by simp [τ1, hlen]; simp at hk; omega)
    have hl2 : (τ2.arrs "PR").length = W + 1 := by simp [τ2, τ1, hlen]
    have hne2 : ∀ b', b' ≠ "PR" → τ2.arrs b' = τ.arrs b' := fun b' hb => by simp [τ2, τ1, Env.setArr, hb]
    obtain ⟨τ3, r3, g3, k3, a3, l3, v3, o3, i3⟩ := ih (k + 1) (ps := ps') (τ := τ2) hl hl2
      (by simp at hk; omega)
      (fun i hi => by
        obtain ⟨a, b⟩ := hev (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at a b
        have hm : l[i] ∈ p :: l := by simp [List.getElem_mem]
        exact ⟨by rw [evalB_congr (σ := τ) (σ' := τ2) _ (fun _ _ => rfl)
            (fun b' hb => hne2 b' (fun h => (hra _ hm).1 (h ▸ hb)))]; exact a,
          by rw [evalB_congr (σ := τ) (σ' := τ2) _ (fun _ _ => rfl)
            (fun b' hb => hne2 b' (fun h => (hra _ hm).2 (h ▸ hb)))]; exact b⟩)
      (fun p hp => hra p (by simp [hp]))
    refine ⟨τ3, (Run.seq r1 (Run.seq r2 r3)).mono ?_, fun i hi => ?_, fun j hj => ?_,
      fun b hb => by rw [a3 b hb]; simp [τ2, τ1, hb], l3, by rw [v3]; rfl, by rw [o3]; rfl, by rw [i3]; rfl⟩
    · simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega
    · have hPR2 : τ2.arrs "PR" = ((τ.arrs "PR").set (2 * k) q.1).set (2 * k + 1) q.2 := by
        simp [τ2, τ1, Env.setArr]
      have hkl : 2 * k + 1 < (τ.arrs "PR").length := by rw [hlen]; simp at hk; omega
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
      · rw [k3 _ (by omega), hPR2]; simp only [Nat.add_zero]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
        simp [prW]
      · rw [k3 _ (by omega), hPR2, List.getElem?_set_self (by simp; omega)]
        simp [prW]
      · have := g3 (i - 2) (by simp at hi; omega)
        rw [show 2 * (k + 1) + (i - 2) = 2 * k + i by omega] at this
        rw [this]
        simp only [prW, List.flatMap_cons]
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_cons, List.length_nil]
    · have hPR2 : τ2.arrs "PR" = ((τ.arrs "PR").set (2 * k) q.1).set (2 * k + 1) q.2 := by
        simp [τ2, τ1, Env.setArr]
      rw [k3 j (by omega), hPR2, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

/-- **Storing a plan.** -/
theorem stPlan_run {W : ℕ} {l : List (Expr × Expr)} {ps : List (ℕ × ℕ)} {τ : Env}
    (hl : l.length = ps.length) (hlen : (τ.arrs "PR").length = W + 1) (hk : 2 * l.length ≤ W)
    (hev : ∀ i (h : i < l.length), (l[i].1.evalB (W + 1) τ = some (ps[i]'(by omega)).1) ∧
      (l[i].2.evalB (W + 1) τ = some (ps[i]'(by omega)).2))
    (hra : ∀ p ∈ l, "PR" ∉ (exRa p.1) ∧ "PR" ∉ (exRa p.2)) :
    ∃ τ', Run (W + 1) (stPlan l) τ τ' (l.length * ((l.map fun p => p.1.size + p.2.size).sum + 6) + 4) ∧
      PreAt "PR" (prW ps) τ' ∧ τ'.vars "np" = ps.length ∧
      (∀ y, y ≠ "np" → τ'.vars y = τ.vars y) ∧
      (∀ b, b ≠ "PR" → τ'.arrs b = τ.arrs b) ∧ (τ'.arrs "PR").length = W + 1 ∧
      τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  obtain ⟨τ1, r1, g1, -, a1, l1, v1, o1, i1⟩ := stPlanAux_run (k := 0) hl hlen (by omega) hev hra
  refine ⟨τ1.setVar "np" l.length, (Run.seq r1 (Run.assign (evalB_lit (by omega)))).mono (by simp),
    fun i hi => ?_, by simp [hl], fun y hy => by simp [hy, v1], fun b hb => by simp [a1 b hb],
    by simp [l1], by simp [o1], by simp [i1]⟩
  have := g1 i (by rw [length_prW] at hi; omega)
  simpa using this

end Lax185574Proofs.ResolveRam.Glue
