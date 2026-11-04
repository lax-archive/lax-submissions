import Lax185574Proofs.Chain.Ram.DampRam

/-!
The damping step as one command: `dampCom` leaves `damp G r o q A` in
`inS` and its size in `sc`. It tries `κ = 1, 2, …` until the size test
passes, so its cost is the number of tried values (`dampTries`) times
the cost of one value.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- Clear `S`. -/
def clearS : Com := .seq (rowFill "inS" (.var "b") (.lit 0)) (.assign "sc" (.lit 0))

/-- The loop over `κ`. -/
def kapLoop : Com :=
  .seq (.assign "kp" (.lit 1)) (.seq (.assign "kf" (.lit 0))
    (.while (.lt (.add (.var "kp") (.mul (.var "kf") (.var "n"))) (.add (.var "n") (.lit 1)))
      kapBody))

/-- The damping step. -/
def dampCom : Com :=
  .ite (.lt (.var "ca") (.mul (.lit 6) (.add (.var "q") (.lit 1)))) clearS
    (.seq kapLoop (.ite (.eq (.var "kf") (.lit 1)) .skip clearS))

/-- The number of values of `κ` tried. -/
noncomputable def dampTries (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (o : VOrder (Fin n)) (q : ℕ) (A : Finset (Fin n)) : ℕ :=
  match firstFrom (accK G r o q A) 1 n with
  | some a => a
  | none => n

/-- The cost of the damping step. -/
noncomputable def dampCost (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (o : VOrder (Fin n)) (q : ℕ) (A : Finset (Fin n)) : ℕ :=
  if A.card < 6 * (q + 1) then n * 30 + 100 else dampTries G r o q A * (kapCost n r + 30) + n * 30 + 100

variable {r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ}

theorem clearS_run {B' : ℕ} (hnB : n < B') {q : ℕ} {σ : Env} (hst : DampSt n r G A pf q σ) :
    ∃ σ', Run B' clearS σ σ' (n * 11 + 8) ∧ DampSt n r G A pf q σ' ∧
      Vec σ' "inS" n (fun u => ind (inBN (∅ : Finset (Fin n)) u)) ∧ σ'.vars "sc" = 0 ∧
      (∀ x, x ∉ ["b", "sc"] → σ'.vars x = σ.vars x) := by
  obtain ⟨⟨t1, t2, t3, hF⟩, hq, hca, hz, hc, hs, hm⟩ := hst
  obtain ⟨σ1, hr1, hF1, hk1, hv1, hx1⟩ :=
    zeroFill_run (B' := B') (arr := "inS") hnB (by decide) hF (hF.lvec "inS" (by simp))
  refine ⟨σ1.setVar "sc" 0, (Run.seq hr1 (Run.assign (v := 0) (by simp; omega))).mono
    (by simp), ⟨⟨t1, t2, t3, hF1.setVar (by simp [fixVars]) _⟩, by simp [hx1 "q" (by decide), hq],
      by simp [hx1 "ca" (by decide), hca], fun t ht => by
        simp only [arrs_setVar] at ht ⊢; rw [hk1 _ (by decide)] at ht ⊢; exact hz t ht,
      (hc.of_eq (hk1 _ (by decide))).of_eq rfl, (hs.of_eq (hk1 _ (by decide))).of_eq rfl,
      (hm.of_eq (hk1 _ (by decide))).of_eq rfl⟩,
    (hv1.of_eq (rfl : (σ1.setVar "sc" 0).arrs "inS" = σ1.arrs "inS")).congr fun u hu => by
      simp [ind, inBN], by simp, fun x hx => ?_⟩
  simp at hx
  simp [hx.2, hx1 x hx.1]

theorem kapLoop_wvars : kapLoop.wvars = ["kp", "kf"] ++ kapBody.wvars := rfl

theorem dampTries_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) (o : VOrder (Fin n))
    (q : ℕ) (A : Finset (Fin n)) : dampTries G r o q A ≤ n := by
  unfold dampTries
  split
  · rename_i a h; have := firstFrom_lt h; omega
  · exact le_rfl

/-- The loop over `κ`. -/
theorem kapLoop_run {B' : ℕ} (hB' : DampBound n B') (hrB : r < B') (o : VOrder (Fin n))
    (hpfo : pf = posN o) {q : ℕ} (hq : q ≤ n + 1) {σ : Env} (hst : DampSt n r G A pf q σ) :
    ∃ σ' K, Run B' kapLoop σ σ' K ∧ DampSt n r G A pf q σ' ∧
      K ≤ dampTries G r o q A * (kapCost n r + 30) + 20 ∧
      (∀ x, x ∉ kapLoop.wvars → σ'.vars x = σ.vars x) ∧
      ((∃ a, firstFrom (accK G r o q A) 1 n = some a ∧ σ'.vars "kf" = 1 ∧
          Vec σ' "inS" n (fun u => ind (inBN (predamp G (fun B => tpRel G B r) o A q a) u)) ∧
          σ'.vars "sc" = (predamp G (fun B => tpRel G B r) o A q a).card) ∨
        (firstFrom (accK G r o q A) 1 n = none ∧ σ'.vars "kf" = 0)) := by
  have hB1 := hB'.1
  unfold PdBound at hB1
  set p := accK G r o q A with hp
  set T := dampTries G r o q A with hT
  have hTn : T ≤ n := dampTries_le G r o q A
  -- the invariant
  let J : Env → Prop := fun τ => DampSt n r G A pf q τ ∧ 1 ≤ τ.vars "kp" ∧
    τ.vars "kp" ≤ T + 1 ∧ (∀ b, 1 ≤ b → b < τ.vars "kp" → p b = false) ∧
    (∀ x, x ∉ kapLoop.wvars → τ.vars x = σ.vars x) ∧
    ((τ.vars "kf" = 0 ∧ (τ.vars "kp" ≤ T ∨ firstFrom p 1 n = none)) ∨
     (τ.vars "kf" = 1 ∧ p (τ.vars "kp") = true ∧ τ.vars "kp" ≤ n ∧
      Vec τ "inS" n (fun u => ind (inBN (predamp G (fun B => tpRel G B r) o A q (τ.vars "kp")) u)) ∧
      τ.vars "sc" = (predamp G (fun B => tpRel G B r) o A q (τ.vars "kp")).card))
  let Ψ : Env → ℕ := fun τ => (kapCost n r + 30) * (T + 1 - τ.vars "kp" - τ.vars "kf")
  have hkT : ∀ k, 1 ≤ k → k ≤ n → (∀ b, 1 ≤ b → b < k → p b = false) → k ≤ T := by
    intro k hk1 hkn hb
    rw [hT]; unfold dampTries
    split
    · rename_i a ha
      obtain ⟨h1, h2, -⟩ := firstFrom_some ha
      by_contra hc
      have := hb a h2 (by omega)
      rw [hp] at this; rw [this] at h1; exact absurd h1 (by simp)
    · exact hkn
  have hnone : firstFrom p 1 n = none → ∀ k, 1 ≤ k → k ≤ n → p k = false := by
    intro h k hk1 hkn
    by_contra hc
    obtain ⟨a, ha⟩ := firstFrom_isSome (p := p) (k := 1) (f := n) (b := k) hk1 (by omega)
      (by simpa using hc)
    rw [h] at ha; exact absurd ha (by simp)
  have hJ0 : J ((σ.setVar "kp" 1).setVar "kf" 0) := by
    refine ⟨?_, by simp, by simp, fun b h1 h2 => by simp at h2; omega,
      fun x hx => ?_, Or.inl ⟨by simp, ?_⟩⟩
    · obtain ⟨⟨t1, t2, t3, hF⟩, hq', hca, hz, hc, hs, hm⟩ := hst
      exact ⟨⟨t1, t2, t3, (hF.setVar (by simp [fixVars]) _).setVar (by simp [fixVars]) _⟩,
        by simp [hq'], by simp [hca], fun t ht => hz t ht, hc.of_eq rfl, hs.of_eq rfl,
        hm.of_eq rfl⟩
    · have h1 : x ≠ "kp" := by intro e; subst e; exact hx (by decide)
      have h2 : x ≠ "kf" := by intro e; subst e; exact hx (by decide)
      simp [h1, h2]
    · simp
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · right; subst h0; rfl
      · left; exact hkT 1 le_rfl h0 (fun b h1 h2 => by omega)
  obtain ⟨σ', K, hr, ⟨hst', hk1', hkT', hbelow', hfr', hcase'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B')
      (b := .lt (.add (.var "kp") (.mul (.var "kf") (.var "n"))) (.add (.var "n") (.lit 1)))
      (c := kapBody) J Ψ
      (fun τ hJ => by
        obtain ⟨⟨t1, t2, t3, hF⟩, -⟩ := hJ.1
        have hkf : τ.vars "kf" ≤ 1 := by rcases hJ.2.2.2.2.2 with h | h <;> omega
        have hkpb := hJ.2.2.1
        have hsum : τ.vars "kp" + τ.vars "kf" * n ≤ 2 * n + 1 := by nlinarith
        exact ⟨_, evalB_condLt (evalB_bin (op := .add) (evalB_var (by have := hJ.2.2.1; omega))
          (evalB_bin (op := .mul) (evalB_var (by omega)) (evalB_var (by rw [hF.hn]; omega))
            (by simp [hF.hn]; nlinarith)) (by simp [hF.hn]; omega))
          (evalB_bin (op := .add) (evalB_var (by rw [hF.hn]; omega)) (evalB_lit (by omega))
            (by simp [hF.hn]; omega))⟩)
      (by
        rintro τ ⟨hstτ, hk1, hkTτ, hbel, hfr, hcase⟩ hc
        obtain ⟨t1, t2, t3, hF⟩ := hstτ.fix
        have hkf0 : τ.vars "kf" = 0 ∧ τ.vars "kp" ≤ n := by
          have hkf : τ.vars "kf" ≤ 1 := by rcases hcase with h | h <;> omega
          simp only [evalB_condLt_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff,
            Bop.apply_add, Bop.apply_mul] at hc
          obtain ⟨m, k, ⟨a, b, ⟨rfl, -⟩, ⟨c, d, ⟨rfl, -⟩, ⟨rfl, -⟩, rfl, -⟩, rfl, -⟩,
            ⟨e, f, ⟨rfl, -⟩, ⟨rfl, -⟩, rfl, -⟩, hlt⟩ := hc
          simp at hlt
          rw [hF.hn] at hlt
          rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact ⟨h1, by rw [h1] at hlt; omega⟩
          · rw [h1] at hlt; omega
        set k := τ.vars "kp" with hkdef
        have hkT2 : k ≤ T := hkT k hk1 hkf0.2 hbel
        obtain ⟨τ', hr, hst', hS', hsc', hacc, hrej, hfr'⟩ :=
          kapBody_run (κ := k) hB' hrB o hpfo hq hk1 hkf0.2 hstτ rfl hkf0.1
        have hfrσ : ∀ x, x ∉ kapLoop.wvars → τ'.vars x = σ.vars x := fun x hx => by
          rw [hfr' x (fun h => hx (by rw [kapLoop_wvars]; exact List.mem_append_right _ h)),
            hfr x hx]
        cases hpk : p k with
        | true =>
          obtain ⟨hkf', hkp'⟩ := hacc hpk
          refine ⟨τ', _, hr, ⟨hst', by omega, by omega, by rw [hkp']; exact hbel, hfrσ,
            Or.inr ⟨hkf', by rw [hkp']; exact hpk, by omega, by rw [hkp']; exact hS',
              by rw [hkp']; exact hsc'⟩⟩, ?_⟩
          simp only [Ψ, hkp', hkf', hkf0.1, Cond.size, Expr.size]
          have : T + 1 - k - 0 = (T + 1 - k - 1) + 1 := by omega
          rw [this, Nat.mul_add, mul_one]; omega
        | false =>
          obtain ⟨hkf', hkp'⟩ := hrej hpk
          refine ⟨τ', _, hr, ⟨hst', by omega, by omega, fun b h1 h2 => ?_, hfrσ,
            Or.inl ⟨hkf', ?_⟩⟩, ?_⟩
          · rw [hkp'] at h2
            rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
            · exact hbel b h1 h2
            · exact hpk
          · rw [hkp']
            rw [hT]; unfold dampTries
            split
            · rename_i a ha
              left
              obtain ⟨h1, h2, -⟩ := firstFrom_some ha
              have : k ≤ a := by
                have := hkT k hk1 hkf0.2 hbel; rw [hT] at this; unfold dampTries at this
                rw [ha] at this; exact this
              rcases Nat.lt_or_ge k a with h | h
              · omega
              · have : k = a := by omega
                subst this; exact absurd (h1.symm.trans hpk) (by simp)
            · rename_i hn; right; exact hn
          · simp only [Ψ, hkp', hkf', hkf0.1, Cond.size, Expr.size]
            have : T + 1 - k - 0 = (T + 1 - (k + 1) - 0) + 1 := by omega
            rw [this, Nat.mul_add, mul_one]; omega)
      hJ0
  obtain ⟨t1, t2, t3, hF'⟩ := hst'.fix
  -- the loop condition fails
  have hexit : σ'.vars "kf" = 1 ∨ n + 1 ≤ σ'.vars "kp" := by
    simp only [evalB_condLt_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff,
      Bop.apply_add, Bop.apply_mul] at hfalse
    obtain ⟨m, k, ⟨a, b, ⟨rfl, -⟩, ⟨c, d, ⟨rfl, -⟩, ⟨rfl, -⟩, rfl, -⟩, rfl, -⟩,
      ⟨e, f, ⟨rfl, -⟩, ⟨rfl, -⟩, rfl, -⟩, hlt⟩ := hfalse
    simp at hlt
    rw [hF'.hn] at hlt
    rcases hcase' with ⟨h1, -⟩ | ⟨h1, -⟩
    · right; rw [h1] at hlt; omega
    · left; exact h1
  have hrun : Run B' kapLoop σ σ' (2 + (2 + K)) :=
    Run.seq (Run.assign (v := 1) (by simp; omega)) (Run.seq (Run.assign (v := 0) (by simp; omega)) hr)
  have hK' : K ≤ T * (kapCost n r + 30) + 10 := by
    simp only [Ψ, vars_setVar, if_true, if_neg (show "kp" ≠ "kf" by decide), Cond.size,
      Expr.size] at hK
    have : T + 1 - 1 - 0 = T := by omega
    rw [this] at hK
    nlinarith
  refine ⟨σ', _, hrun, hst', by omega, hfr', ?_⟩
  rcases hcase' with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
  · right
    refine ⟨?_, h1⟩
    rcases hexit with h | h
    · omega
    · exact firstFrom_eq_none_of fun b hb1 hb2 => hbelow' b hb1 (by omega)
  · left
    exact ⟨_, firstFrom_eq_some_of hk1' (by omega) h2 hbelow', h1, h4, h5⟩

theorem dampCom_wvars : dampCom.wvars = clearS.wvars ++ (kapLoop.wvars ++ ([] ++ clearS.wvars)) :=
  rfl

/-- **The damping step.** -/
theorem dampCom_run {B' : ℕ} (hB' : DampBound n B') (hrB : r < B') (o : VOrder (Fin n))
    (hpfo : pf = posN o) {q : ℕ} (hq : q ≤ n + 1) {σ : Env} (hst : DampSt n r G A pf q σ) :
    ∃ σ' K, Run B' dampCom σ σ' K ∧ DampSt n r G A pf q σ' ∧
      K ≤ dampCost G r o q A ∧ (∀ x, x ∉ dampCom.wvars → σ'.vars x = σ.vars x) ∧
      Vec σ' "inS" n (fun u => ind (inBN (damp G r o q A) u)) ∧
      σ'.vars "sc" = (damp G r o q A).card := by
  have hB1 := hB'.1
  unfold PdBound at hB1
  have hAn : A.card ≤ n := by have := card_le_univ A; simpa using this
  have hB2 := hB'.2
  have h6 : 6 * (q + 1) < B' := by
    have : 6 * (q + 1) ≤ 15 * (n + 3) * (n + 1) * (n + 1) := by
      have h1 : 1 ≤ (n + 1) * (n + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      calc 6 * (q + 1) ≤ 15 * (n + 3) := by omega
        _ = 15 * (n + 3) * 1 := by ring
        _ ≤ 15 * (n + 3) * ((n + 1) * (n + 1)) := Nat.mul_le_mul_left _ h1
        _ = _ := by ring
    omega
  have hcond : (Cond.lt (.var "ca") (.mul (.lit 6) (.add (.var "q") (.lit 1)))).evalB B' σ =
      some (decide (A.card < 6 * (q + 1))) := by
    rw [evalB_condLt (evalB_var (by rw [hst.hca]; omega)) (evalB_bin (op := .mul)
      (evalB_lit (n := 6) (by omega)) (evalB_bin (op := .add) (evalB_var (by rw [hst.hq]; omega))
        (evalB_lit (n := 1) (by omega)) (by simp [hst.hq]; omega)) (by simp [hst.hq]; omega))]
    simp [hst.hca, hst.hq]
  have hnB : n < B' := by omega
  have hsub : ∀ x, x ∈ clearS.wvars → x ∈ dampCom.wvars := fun x h => by
    rw [dampCom_wvars]; exact List.mem_append_left _ h
  have hsub2 : ∀ x, x ∈ clearS.wvars → x ∈ dampCom.wvars := fun x h => by
    rw [dampCom_wvars]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))
  have hsubk : ∀ x, x ∈ kapLoop.wvars → x ∈ dampCom.wvars := fun x h => by
    rw [dampCom_wvars]; exact List.mem_append_right _ (List.mem_append_left _ h)
  by_cases hsmall : A.card < 6 * (q + 1)
  · have hd : damp G r o q A = ∅ := by unfold damp; rw [if_pos hsmall]
    obtain ⟨σ1, hr1, hst1, hv1, hsc1, hx1⟩ := clearS_run (q := q) hnB hst
    refine ⟨σ1, _, Run.ite_true (by rw [hcond]; simp [hsmall]) hr1, hst1, ?_,
      fun x hx => hr1.frame_var x (fun h => hx (hsub x h)), by rw [hd]; exact hv1,
      by rw [hd, hsc1]; rfl⟩
    unfold dampCost; rw [if_pos hsmall]; simp; omega
  · obtain ⟨σ1, K1, hr1, hst1, hK1, hx1, hres⟩ := kapLoop_run hB' hrB o hpfo hq hst
    have hkfev : (Cond.eq (.var "kf") (.lit 1)).evalB B' σ1 = some (decide (σ1.vars "kf" = 1)) := by
      have : σ1.vars "kf" ≤ 1 := by rcases hres with ⟨_, _, h, _⟩ | ⟨_, h⟩ <;> omega
      exact eq_lit_evalB (by omega) (by omega)
    rcases hres with ⟨a, ha, hkf, hv, hsc⟩ | ⟨hnone, hkf⟩
    · have hd : damp G r o q A = predamp G (fun B => tpRel G B r) o A q a := by
        unfold damp; rw [if_neg hsmall]
        simp only [Fintype.card_fin]
        rw [show (firstFrom (fun κ => decide (q * (predamp G (fun B => tpRel G B r) o A q κ).card ≤
          A.card)) 1 n) = firstFrom (accK G r o q A) 1 n from rfl, ha]
      have hrun : Run B' dampCom σ σ1 (K1 + 20) := by
        unfold dampCom
        exact (Run.ite_false (by rw [hcond]; simp [hsmall])
          (Run.seq hr1 (Run.ite_true (by rw [hkfev]; simp [hkf]) Run.skip))).mono (by simp; omega)
      refine ⟨σ1, _, hrun, hst1, ?_, fun x hx => hrun.frame_var x hx, by rw [hd]; exact hv,
        by rw [hd]; exact hsc⟩
      have hT : dampTries G r o q A = a := by unfold dampTries; rw [ha]
      unfold dampCost; rw [if_neg hsmall, hT]; rw [hT] at hK1; omega
    · have hd : damp G r o q A = ∅ := by
        unfold damp; rw [if_neg hsmall]
        simp only [Fintype.card_fin]
        rw [show (firstFrom (fun κ => decide (q * (predamp G (fun B => tpRel G B r) o A q κ).card ≤
          A.card)) 1 n) = firstFrom (accK G r o q A) 1 n from rfl, hnone]
      obtain ⟨σ2, hr2, hst2, hv2, hsc2, hx2⟩ := clearS_run (q := q) hnB hst1
      have hrun : Run B' dampCom σ σ2 (K1 + n * 11 + 30) := by
        unfold dampCom
        exact (Run.ite_false (by rw [hcond]; simp [hsmall])
          (Run.seq hr1 (Run.ite_false (by rw [hkfev]; simp [hkf]) hr2))).mono (by simp; omega)
      refine ⟨σ2, _, hrun, hst2, ?_, fun x hx => hrun.frame_var x hx, by rw [hd]; exact hv2,
        by rw [hd, hsc2]; rfl⟩
      have hT : dampTries G r o q A = n := by unfold dampTries; rw [hnone]
      unfold dampCost; rw [if_neg hsmall, hT]; rw [hT] at hK1; omega

end Lax185574Proofs.Chain.Ram
