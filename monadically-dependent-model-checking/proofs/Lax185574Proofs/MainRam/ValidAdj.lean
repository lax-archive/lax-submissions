import Lax185574Proofs.MainRam.ValidRead

/-!
The validation program, part two: the adjacency matrix `A` of the
graph from its offsets and targets. Row `u` gets a `1` at every target
in the block of `u`. The cost is linear in `n` and the number of
targets.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Classical

/-- The target `z` lies in the block of `u`. -/
def InBlock (o t : ℕ → ℕ) (u z : ℕ) : Prop := ∃ j, o u ≤ j ∧ j < o (u + 1) ∧ t j = z

def adjBody : Com :=
  .seq (.store "A" (.add (.mul (.var "a") (.var "n")) (.get "tg" (.var "j"))) (.lit 1))
    (.assign "j" (.add (.var "j") (.lit 1)))

def adjRow : Com :=
  .seq (.assign "j" (.get "of" (.var "a"))) (.seq (.assign "hi" (.get "of" (.add (.var "a") (.lit 1))))
    (.while (.lt (.var "j") (.var "hi")) adjBody))

def adjPh : Com :=
  .seq (.assign "a" (.lit 0))
    (.while (.lt (.var "a") (.var "n")) (.seq adjRow (.assign "a" (.add (.var "a") (.lit 1)))))

theorem div_mod_rm {N u v : ℕ} (hv : v < N) : (u * N + v) / N = u ∧ (u * N + v) % N = v := by
  have hN : 0 < N := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hv]; simp
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem adjRow_run {B N D u : ℕ} {o t f : ℕ → ℕ} (hB : N * N + D + 2 < B)
    (hu : u < N) (hmono : o u ≤ o (u + 1)) (hoD : o (u + 1) ≤ D) (ht : ∀ j < D, t j < N)
    (hoB : ∀ i ≤ N, o i ≤ D)
    {σ : Env} (hvu : σ.vars "a" = u) (hnN : σ.vars "n" = N) (hof : σ.arrs "of" = arrOf (N + 1) o)
    (htg : σ.arrs "tg" = arrOf D t) (hA : σ.arrs "A" = arrOf (N * N) f) :
    ∃ σ', Run B adjRow σ σ' (16 * (o (u + 1) - o u) + 12) ∧
      σ'.arrs "A" = arrOf (N * N) (fun i => if i / N = u ∧ InBlock o t u (i % N) then 1 else f i) ∧
      σ'.vars "a" = u ∧ σ'.vars "n" = N ∧
      (∀ b, b ≠ "A" → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hNB : N + 2 < B := by have := Nat.le_mul_self N; omega
  have hou : o u ≤ D := hoB u (by omega)
  have hNN : u * N + N ≤ N * N := by
    have := Nat.mul_le_mul_right N (show u + 1 ≤ N by omega); rw [Nat.add_mul] at this; omega
  set σ₁ := σ.setVar "j" (o u)
  have r₁ : Run B (.assign "j" (.get "of" (.var "a"))) σ σ₁ 3 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff, hof, hvu]
    exact ⟨u, ⟨rfl, by omega⟩, getElem?_arrOf _ (by omega), by omega⟩
  set σ₂ := σ₁.setVar "hi" (o (u + 1))
  have r₂ : Run B (.assign "hi" (.get "of" (.add (.var "a") (.lit 1)))) σ₁ σ₂ 5 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff, σ₁, arrs_setVar, hof,
      vars_setVar]
    simp only [show ("a" : String) = "j" ↔ False by decide, if_false, hvu]
    exact ⟨u + 1, ⟨u, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩,
      getElem?_arrOf _ (by omega), by omega⟩
  let I : Env → Prop := fun τ => o u ≤ τ.vars "j" ∧ τ.vars "j" ≤ o (u + 1) ∧
    τ.vars "hi" = o (u + 1) ∧ τ.vars "a" = u ∧ τ.vars "n" = N ∧ τ.arrs "tg" = arrOf D t ∧
    τ.inp = σ.inp ∧ τ.out = σ.out ∧ (∀ b, b ≠ "A" → τ.arrs b = σ.arrs b) ∧
    τ.arrs "A" = arrOf (N * N) (fun i => if i / N = u ∧
      ∃ j, o u ≤ j ∧ j < τ.vars "j" ∧ t j = i % N then 1 else f i)
  have h0 : I σ₂ := by
    refine ⟨by simp [σ₂, σ₁], by simp [σ₂, σ₁]; omega, by simp [σ₂], by simp [σ₂, σ₁, hvu],
      by simp [σ₂, σ₁, hnN], htg, rfl, rfl, fun b _ => rfl, ?_⟩
    simp only [σ₂, σ₁, arrs_setVar, hA, vars_setVar]
    simp only [show ("j" : String) = "hi" ↔ False by decide, if_false, if_true]
    exact arrOf_congr fun k _ => by
      rw [if_neg]; rintro ⟨-, j, h1, h2, -⟩; omega
  obtain ⟨σ', hr, ⟨hj1, hj2, hhi, ha, hn', htg', hinp, hout, hfr, hA'⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "j") (.var "hi")) (c := adjBody) I
      (fun τ => o (u + 1) - τ.vars "j") 12
      (fun τ hτ => evalB_condLt_vars (by have := hτ.2.1; omega) (by rw [hτ.2.2.1]; omega))
      (by
        rintro τ ⟨hj1, hj2, hhi, ha, hn, htg, hinp, hout, hfr, hA⟩ hc
        have hlt : τ.vars "j" < o (u + 1) := by have := lt_of_condLt_true hc; rwa [hhi] at this
        have hjD : τ.vars "j" < D := by omega
        have htj := ht _ hjD
        have hidx : u * N + t (τ.vars "j") < N * N := by omega
        unfold adjBody
        refine ⟨_, (Run.seq (Run.store (idx := u * N + t (τ.vars "j")) (v := 1) ?_ ?_ ?_)
          (Run.assign (v := τ.vars "j" + 1) ?_)).mono (by simp), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_⟩, ?_⟩
        · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, htg, ha, hn]
          refine ⟨u * N, t (τ.vars "j"), ⟨u, N, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, ?_⟩,
            ⟨τ.vars "j", ⟨rfl, by omega⟩, getElem?_arrOf _ hjD, by omega⟩, rfl, by omega⟩
          (try simp) <;> omega
        · simp; omega
        · simp [hA]; omega
        · simp; omega
        · simp; omega
        · simp; omega
        · simp [hhi]
        · simp [ha]
        · simp [hn]
        · simp [htg]
        · simp [hinp]
        · simp [hout]
        · intro b hb; simp [hb, hfr b hb]
        · simp only [vars_setVar, if_true, arrs_setVar, arrs_setArr, if_pos rfl, hA, set_arrOf]
          apply arrOf_congr
          intro k hk
          obtain ⟨hd, hm⟩ := div_mod_rm (N := N) (u := u) htj
          by_cases hk' : k = u * N + t (τ.vars "j")
          · subst hk'
            rw [if_pos rfl, if_pos ⟨hd, τ.vars "j", hj1, by omega, hm.symm⟩]
          · rw [if_neg hk']
            congr 1
            apply propext
            constructor
            · rintro ⟨h0, j, h1, h2, h3⟩; exact ⟨h0, j, h1, by omega, h3⟩
            · rintro ⟨h0, j, h1, h2, h3⟩
              refine ⟨h0, j, h1, ?_, h3⟩
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h2) with h | h
              · exact h
              · subst h
                exfalso; apply hk'
                have := Nat.div_add_mod k N
                rw [h0, ← h3] at this
                calc k = N * u + t (τ.vars "j") := this.symm
                  _ = u * N + t (τ.vars "j") := by ring
        · simp <;> omega)
      h0
  have hj' : σ'.vars "j" = o (u + 1) := by
    have := le_of_condLt_false hfalse; rw [hhi] at this; omega
  refine ⟨σ', (r₁.seq (r₂.seq hr)).mono ?_, ?_, ha, hn', fun b hb => ?_, ?_, ?_⟩
  · simp only [σ₂, σ₁, vars_setVar, Cond.size, Expr.size]
    simp only [show ("j" : String) = "hi" ↔ False by decide, if_false, if_true]
    nlinarith
  · rw [hA', hj']; rfl
  · rw [hfr b hb]
  · rw [hout]
  · rw [hinp]

theorem adjPh_run {B N D : ℕ} {o t : ℕ → ℕ} (hB : N * N + D + 2 < B)
    (hmono : ∀ u < N, o u ≤ o (u + 1)) (hoB : ∀ i ≤ N, o i ≤ D) (ht : ∀ j < D, t j < N)
    {σ : Env} (hn : σ.vars "n" = N) (hof : σ.arrs "of" = arrOf (N + 1) o)
    (htg : σ.arrs "tg" = arrOf D t) (hA : σ.arrs "A" = arrOf (N * N) (fun _ => 0)) :
    ∃ σ', Run B adjPh σ σ' (30 * N + 16 * D + 10) ∧
      σ'.arrs "A" = arrOf (N * N) (fun i => if InBlock o t (i / N) (i % N) then 1 else 0) ∧
      σ'.vars "n" = N ∧ (∀ b, b ≠ "A" → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧
      σ'.inp = σ.inp := by
  have hNB : N + 2 < B := by have := Nat.le_mul_self N; omega
  have hmono' : ∀ u v, u ≤ v → v ≤ N → o u ≤ o v := by
    intro u v huv hv
    induction v, huv using Nat.le_induction with
    | base => exact le_rfl
    | succ v _ ih => exact (ih (by omega)).trans (hmono v (by omega))
  let I : Env → Prop := fun τ => τ.vars "n" = N ∧ τ.vars "a" ≤ N ∧
    (∀ b, b ≠ "A" → τ.arrs b = σ.arrs b) ∧ τ.out = σ.out ∧ τ.inp = σ.inp ∧
    τ.arrs "A" = arrOf (N * N) (fun i => if i / N < τ.vars "a" ∧ InBlock o t (i / N) (i % N)
      then 1 else 0)
  obtain ⟨σ', K, hr, ⟨hn', ha', hfr, hout, hinp, hA'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "a") (.var "n"))
      (c := .seq adjRow (.assign "a" (.add (.var "a") (.lit 1)))) I
      (fun τ => 20 * (N - τ.vars "a") + 16 * (D - o (τ.vars "a")))
      (fun τ hτ => evalB_condLt_vars (by have := hτ.2.1; omega) (by rw [hτ.1]; omega))
      (by
        rintro τ ⟨hn, ha, hfr, hout, hinp, hA⟩ hc
        have hlt : τ.vars "a" < N := by have := lt_of_condLt_true hc; rwa [hn] at this
        set u := τ.vars "a" with hu
        have h1 := hmono u hlt
        have h2 := hmono' (u + 1) N (by omega) le_rfl
        obtain ⟨τ₁, r₁, hA₁, ha₁, hn₁, hfr₁, ho₁, hi₁⟩ := adjRow_run (B := B) (N := N) (D := D)
          (u := u) (o := o) (t := t) hB hlt h1 (h2.trans (hoB N le_rfl)) ht hoB rfl hn
          (by rw [hfr _ (by decide), hof]) (by rw [hfr _ (by decide), htg]) hA
        refine ⟨τ₁.setVar "a" (u + 1), _, r₁.seq (Run.assign (v := u + 1) ?_), ⟨?_, ?_, ?_, ?_, ?_,
          ?_⟩, ?_⟩
        · simp [ha₁]; omega
        · simp [hn₁]
        · simp; omega
        · intro b hb; simp [hfr₁ b hb, hfr b hb]
        · simp [ho₁, hout]
        · simp [hi₁, hinp]
        · simp only [arrs_setVar, hA₁, vars_setVar, if_true]
          apply arrOf_congr
          intro k hk
          by_cases hk' : k / N = u
          · simp [hk']
          · rw [if_neg (fun h => hk' h.1)]
            congr 1; apply propext
            constructor
            · rintro ⟨h0, h1⟩; exact ⟨by omega, h1⟩
            · rintro ⟨h0, h1⟩; exact ⟨by omega, h1⟩
        · simp only [vars_setVar, if_true, Cond.size, Expr.size]
          have e1 : N - u = (N - (u + 1)) + 1 := by omega
          have e2 : D - o u = (D - o (u + 1)) + (o (u + 1) - o u) := by
            have := hoB (u + 1) (by omega); omega
          rw [e1, e2]; ring_nf; omega)
      (show I (σ.setVar "a" 0) from ⟨by simp [hn], by simp, fun b _ => by simp, by simp, by simp,
        by simp only [arrs_setVar, hA, vars_setVar, if_true]; exact arrOf_congr fun k _ => by simp⟩)
  have haN : σ'.vars "a" = N := by
    have := le_of_condLt_false hfalse; rw [hn'] at this; omega
  refine ⟨σ', ((Run.assign (v := 0) (by simp; omega)).seq hr).mono ?_, ?_, hn', hfr, hout, hinp⟩
  · simp only [Cond.size, Expr.size, vars_setVar, if_true, Nat.sub_zero] at hK
    simp only [Expr.size]
    have := hoB 0 (by omega)
    omega
  · rw [hA', haN]
    apply arrOf_congr
    intro k hk
    have : k / N < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp at hk
      · exact Nat.div_lt_of_lt_mul hk
    simp [this]

end Lax185574Proofs.MainRam
