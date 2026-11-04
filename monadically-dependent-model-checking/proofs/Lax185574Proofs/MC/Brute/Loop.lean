import Lax185574Proofs.MC.Brute.Step

/-!
The loop of the evaluation machine in IMP+.

`bfLoop` runs `bfStep` while the machine is evaluating or its stack is
not empty. `loop_run` shows that the loop follows the machine to its
final configuration, one iteration per step, and `eval_run` combines
this with `machine_eval`: started on the code of a sentence, the loop
leaves its truth value in `bfb`.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax3.FirstOrder Lax185574.InstanceEncoding

/-- The condition of the loop: evaluating, or a nonempty stack. -/
def bfCond : Cond := .lt (.lit 0) (.add (.var "bfm") (.var "bfs"))

/-- The machine loop. -/
def bfLoop : Com := .while bfCond bfStep

theorem Run.while_true' {B : ℕ} {b : Cond} {c : Com} {σ σ' σ'' : Env} {K K' : ℕ}
    (hb : b.evalB B σ = some true) (h : Run B c σ σ' K) (h' : Run B (.while b c) σ' σ'' K') :
    Run B (.while b c) σ σ'' (1 + b.size + K + K') := by
  obtain ⟨k, hk, hbs⟩ := h
  obtain ⟨k', hk', hbs'⟩ := h'
  exact ⟨1 + b.size + k + k', by omega, .while_true hb hbs hbs'⟩

theorem AllSmall.succ {L n : ℕ} {A : ℕ → ℕ → Bool} {cd : List ℕ} {fe : ℕ → ℕ} {t : ℕ}
    {c c₁ : Cfg} (h : AllSmall L n A cd fe (t + 1) c) (hs : step n A cd fe c = some c₁) :
    AllSmall L n A cd fe t c₁ := by
  intro t' ht'
  obtain ⟨c', h1, h2⟩ := h (t' + 1) (by omega)
  simp only [iter, hs, Option.bind_some] at h1
  exact ⟨c', h1, h2⟩

theorem bfStep_data : "bfc" ∉ bfStep.warrs ∧ "bfe" ∉ bfStep.warrs ∧ "bfA" ∉ bfStep.warrs := by
  simp [bfStep, evalStep, retStep, retEx, pushF, Com.warrs]

theorem bfCond_eval {B n L : ℕ} {c : Cfg} {τ : Env} (hr : BRep B n c τ) (hs : Small L n c)
    (hLB : L + 3 < B) :
    bfCond.evalB B τ = some (decide (0 < τ.vars "bfm" + τ.vars "bfs")) := by
  have hm := hr.hm
  have hss := hr.hs
  have h1 := hs.2.1
  have hmB : τ.vars "bfm" ≤ 1 := by split at hm <;> omega
  exact evalB_condLt (evalB_lit (by omega))
    (evalB_bin (op := .add) (evalB_var (by omega)) (evalB_var (by omega)) (by simp; omega))

/-- **The loop follows the machine.** If the machine reaches a final
configuration in `t` steps through small configurations, the loop
reaches its representation. -/
theorem loop_run {B n L : ℕ} (hLB : L + 3 < B) (hnB : n * n < B) :
    ∀ (t : ℕ) (c cf : Cfg) (τ : Env), BRep B n c τ → BData B τ →
      AllSmall L n (adjOf τ n) (cdOf τ) (feOf τ) t c →
      iter n (adjOf τ n) (cdOf τ) (feOf τ) t c = some cf → cf.ev = false → cf.stk = [] →
      ∃ τ', Run B bfLoop τ τ' (110 * t + 6) ∧ BRep B n cf τ'
  | 0, c, cf, τ, hr, _, hsm, hit, hev, hstk => by
      simp only [iter, Option.some.injEq] at hit
      subst hit
      obtain ⟨c', h0, hs⟩ := hsm 0 le_rfl
      simp only [iter, Option.some.injEq] at h0; subst h0
      have hc := bfCond_eval hr hs hLB
      have hm := hr.hm
      have hss := hr.hs
      rw [hev] at hm; rw [hstk] at hss
      simp only [Bool.false_eq_true, if_false] at hm
      simp only [hm, hss, List.length_nil] at hc
      exact ⟨τ, (Run.while_false hc).mono (by simp [bfCond]), hr⟩
  | t + 1, c, cf, τ, hr, hD, hsm, hit, hev, hstk => by
      obtain ⟨c', h0, hs⟩ := hsm 0 (by omega)
      simp only [iter, Option.some.injEq] at h0; subst h0
      have hit' : (step n (adjOf τ n) (cdOf τ) (feOf τ) c).bind
          (iter n (adjOf τ n) (cdOf τ) (feOf τ) t) = some cf := hit
      cases hst : step n (adjOf τ n) (cdOf τ) (feOf τ) c with
      | none => rw [hst] at hit'; simp at hit'
      | some c₁ =>
        rw [hst, Option.bind_some] at hit'
        replace hit := hit'
        obtain ⟨τ₁, hr₁, hb₁⟩ := bfStep_sim ⟨hr, hD, hs, hLB, hnB⟩ hst
        obtain ⟨d1, d2, d3⟩ := bfStep_data
        have ec := hr₁.frame_arr "bfc" d1
        have ee := hr₁.frame_arr "bfe" d2
        have eA := hr₁.frame_arr "bfA" d3
        have hD₁ : BData B τ₁ := ⟨by rw [ec]; exact hD.lc, by rw [ee]; exact hD.le,
          by rw [eA]; exact hD.lA, by rw [ec]; exact hD.vc, by rw [ee]; exact hD.ve,
          by rw [eA]; exact hD.vA⟩
        have hA : adjOf τ₁ n = adjOf τ n := by unfold adjOf; rw [eA]
        have hc : cdOf τ₁ = cdOf τ := by unfold cdOf; exact ec
        have hf : feOf τ₁ = feOf τ := by unfold feOf; rw [ee]
        have hsm₁ := hsm.succ hst
        rw [← hA, ← hc, ← hf] at hsm₁ hit
        obtain ⟨τ', hr', hb'⟩ := loop_run hLB hnB t c₁ cf τ₁ hb₁ hD₁ hsm₁ hit hev hstk
        have hcond := bfCond_eval hr hs hLB
        have hpos : 0 < τ.vars "bfm" + τ.vars "bfs" := by
          have hm := hr.hm
          have hss := hr.hs
          rcases c with ⟨ev, p, b, s, a⟩
          cases ev
          · cases s with
            | nil => simp [step] at hst
            | cons f s => simp at hss; omega
          · simp at hm; omega
        simp only [hpos, decide_true] at hcond
        refine ⟨τ', (Run.while_true' hcond hr₁ hr').mono ?_, hb'⟩
        simp [bfCond]; omega

theorem asgOf_zero {n : ℕ} (m : Fin 0 → Fin n) : asgOf m = [] := by simp [asgOf]

open Classical in
/-- **The loop evaluates a sentence.** Started on the code of `φ` with
the ends of its conjuncts and the adjacency matrix of `G`, the loop
leaves `1` in `bfb` if `G ⊨ φ` and `0` otherwise, within
`110 · bsteps n φ + 6`. -/
theorem eval_run {B n : ℕ} (G : SimpleGraph (Fin n)) (φ : FO 0) {τ : Env}
    (hLB : (code φ).length + 3 < B) (hnB : n * n < B)
    (hr : BRep B n ⟨true, 0, false, [], []⟩ τ) (hD : BData B τ)
    (hcd : CodeAt (cdOf τ) 0 (code φ)) (hfe : FeOK (cdOf τ) (feOf τ) φ 0)
    (hA : ∀ u v : Fin n, adjOf τ n u v = decide (G.Adj u v)) :
    ∃ τ', Run B bfLoop τ τ' (110 * bsteps n φ + 6) ∧
      τ'.vars "bfb" = (if Sat G Fin.elim0 φ then 1 else 0) := by
  obtain ⟨t, ht, p', b', hb', hit, hsm⟩ := machine_eval G (A := adjOf τ n) (cd := cdOf τ)
    (fe := feOf τ) hA (code φ).length φ 0 hcd hfe (by omega) (by omega) Fin.elim0 [] false (by simp) (by simp)
  rw [asgOf_zero] at hit hsm
  obtain ⟨τ', hrun, hrep⟩ := loop_run hLB hnB t _ _ τ hr hD hsm hit rfl rfl
  refine ⟨τ', hrun.mono (by omega), ?_⟩
  rw [hrep.hb]
  by_cases hS : Sat G Fin.elim0 φ
  · simp [hS, hb'.mpr hS]
  · have : b' = false := by cases b' <;> simp_all
    simp [hS, this]

end Lax185574Proofs.MC.Brute
