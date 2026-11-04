import Lax185574Proofs.MC.Brute.Step

/-!
The ends of the subformulas, for the brute-force thread.

`endsCmd` scans the code in `bfc` from right to left and stores in `bfe`
at every position `q` the end of the subformula starting at `q`: `q + 3`
for an atom, the end of the subformula at `q + 1` for a negation or a
quantifier, and for a conjunction the end of the subformula that starts
where the left conjunct ends. Positions inside atoms get values too,
which are never used. `ends_run` gives the run, and `feOK_of_good`
turns its result into the fact `FeOK` that the machine needs.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax3.FirstOrder Lax185574.InstanceEncoding

/-- One position, from the right. -/
def endBody : Com :=
  .seq (.assign "bfq" (.sub (.var "bfq") (.lit 1))) (.seq (.assign "bfo" (.get "bfc" (.var "bfq")))
    (.ite (.lt (.var "bfo") (.lit 2)) (.store "bfe" (.var "bfq") (.add (.var "bfq") (.lit 3)))
      (.ite (.eq (.var "bfo") (.lit 3))
        (.store "bfe" (.var "bfq") (.get "bfe" (.get "bfe" (.add (.var "bfq") (.lit 1)))))
        (.store "bfe" (.var "bfq") (.get "bfe" (.add (.var "bfq") (.lit 1)))))))

/-- The ends of all positions below `bfl`. -/
def endsCmd : Com := .seq (.assign "bfq" (.var "bfl")) (.while (.lt (.lit 0) (.var "bfq")) endBody)

/-- The value stored at `q`. -/
def endVal (C E : List ℕ) (q : ℕ) : ℕ :=
  if C.getD q 0 < 2 then q + 3 else if C.getD q 0 = 3 then E.getD (E.getD (q + 1) 0) 0
  else E.getD (q + 1) 0

/-- Every subformula starting at `q` or later has its end in `E`. -/
def Good (C E : List ℕ) (L q : ℕ) : Prop :=
  ∀ (k : ℕ) (ψ : FO k) (p : ℕ), q ≤ p → CodeAt C p (code ψ) → p + (code ψ).length ≤ L →
    E.getD p 0 = p + (code ψ).length

theorem one_le_code {k : ℕ} (ψ : FO k) : 1 ≤ (code ψ).length := by cases ψ <;> simp [code]

theorem good_top (C E : List ℕ) (L : ℕ) : Good C E L L := by
  intro k ψ p hp _ hL
  have := one_le_code ψ
  omega

theorem good_set {C E : List ℕ} {L q : ℕ} (hG : Good C E L (q + 1)) (hq : q < E.length) :
    Good C (E.set q (endVal C E q)) L q := by
  intro k ψ p hp hc hL
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases he : q = p
  · subst he
    rw [if_pos rfl, if_pos hq]
    show endVal C E q = q + (code ψ).length
    cases ψ with
    | adj i j =>
      have : C.getD q 0 = 0 := by simpa [code] using hc.head
      rw [endVal, if_pos (by rw [this]; omega)]; simp [code]
    | eq i j =>
      have : C.getD q 0 = 1 := by simpa [code] using hc.head
      rw [endVal, if_pos (by rw [this]; omega)]; simp [code]
    | not ψ =>
      have : C.getD q 0 = 2 := by simpa [code] using hc.head
      have h1 := hG k ψ (q + 1) le_rfl hc.tail (by simp [code] at hL; omega)
      simp only [endVal, this, h1, code, List.length_cons]
      simp; omega
    | and ψ₁ ψ₂ =>
      have : C.getD q 0 = 3 := by simpa [code] using hc.head
      have ht := hc.tail
      have h1 := hG k ψ₁ (q + 1) le_rfl ht.left (by simp [code] at hL; omega)
      have h2 := hG k ψ₂ (q + 1 + (code ψ₁).length) (by omega) ht.right
        (by simp [code] at hL; omega)
      simp only [endVal, this, h1, h2, code, List.length_cons, List.length_append]
      simp; omega
    | ex ψ =>
      have : C.getD q 0 = 4 := by simpa [code] using hc.head
      have h1 := hG (k + 1) ψ (q + 1) le_rfl hc.tail (by simp [code] at hL; omega)
      simp only [endVal, this, h1, code, List.length_cons]
      simp; omega
  · rw [if_neg he, ← List.getD_eq_getElem?_getD]
    exact hG k ψ p (by omega) hc hL

theorem feOK_of_good {C E : List ℕ} {L : ℕ} (hG : Good C E L 0) :
    ∀ {k : ℕ} (ψ : FO k) (p : ℕ), CodeAt C p (code ψ) → p + (code ψ).length ≤ L →
      FeOK C (fun j => E.getD j 0) ψ p
  | _, .adj _ _, _, _, _ => trivial
  | _, .eq _ _, _, _, _ => trivial
  | _, .not ψ, p, hc, hL => by
      simp only [code, List.length_cons] at hL
      exact feOK_of_good hG ψ (p + 1) hc.tail (by omega)
  | k, .and ψ₁ ψ₂, p, hc, hL => by
      simp only [code, List.length_cons, List.length_append] at hL
      have ht := hc.tail
      exact ⟨hG k ψ₁ (p + 1) (by omega) ht.left (by omega),
        feOK_of_good hG ψ₁ (p + 1) ht.left (by omega),
        feOK_of_good hG ψ₂ _ ht.right (by omega)⟩
  | _, .ex ψ, p, hc, hL => by
      simp only [code, List.length_cons] at hL
      exact feOK_of_good hG ψ (p + 1) hc.tail (by omega)

theorem endVal_le {C E : List ℕ} {L q : ℕ} (hq : q < L) (hE : ∀ i, E.getD i 0 ≤ L + 2) :
    endVal C E q ≤ L + 2 := by
  unfold endVal
  split_ifs
  · omega
  · exact hE _
  · exact hE _

theorem endBody_run {B L q : ℕ} {C E : List ℕ} {τ : Env} (hLB : L + 3 < B) (hq : q < L)
    (hbq : τ.vars "bfq" = q + 1) (hC : τ.arrs "bfc" = C) (hCl : C.length = B)
    (hCB : ∀ i, C.getD i 0 < B) (hEe : τ.arrs "bfe" = E) (hEl : E.length = B)
    (hE : ∀ i, E.getD i 0 ≤ L + 2) :
    ∃ τ', Run B endBody τ τ' 40 ∧ τ'.vars "bfq" = q ∧ τ'.arrs "bfe" = E.set q (endVal C E q) := by
  have hq1 : τ.vars "bfq" - 1 = q := by omega
  have hc0 : (τ.arrs "bfc").getD (τ.vars "bfq" - 1) 0 < B := by rw [hC, hq1]; exact hCB q
  have he1 : (τ.arrs "bfe").getD (τ.vars "bfq" - 1 + 1) 0 ≤ L + 2 := by rw [hEe, hq1]; exact hE _
  have he2 : (τ.arrs "bfe").getD ((τ.arrs "bfe").getD (τ.vars "bfq" - 1 + 1) 0) 0 ≤ L + 2 := by
    rw [hEe]; exact hE _
  have hqL : τ.vars "bfq" - 1 < L := by omega
  have hcl : (τ.arrs "bfc").length = B := by rw [hC, hCl]
  have hel : (τ.arrs "bfe").length = B := by rw [hEe, hEl]
  unfold endBody
  run_vcg
  all_goals first | bdead | (bsimpa; omega) | skip
  all_goals bsimpa
  all_goals first | bdead | skip
  all_goals (refine ⟨by omega, ?_⟩)
  all_goals (rename_i hcs; rw [hEe, hC, hq1] at *)
  all_goals (congr 1; simp only [endVal]; simp_all)

/-- **The ends.** With the code of length `L` in `bfc` and zeros in
`bfe`, `endsCmd` leaves in `bfe` the ends of all subformulas. -/
theorem ends_run {B L : ℕ} {C : List ℕ} {σ : Env} (hLB : L + 3 < B) (hl : σ.vars "bfl" = L)
    (hC : σ.arrs "bfc" = C) (hCl : C.length = B) (hCB : ∀ i, C.getD i 0 < B)
    (hel : (σ.arrs "bfe").length = B) (hz : ∀ i, (σ.arrs "bfe").getD i 0 = 0) :
    ∃ σ', Run B endsCmd σ σ' (50 * L + 10) ∧ (σ'.arrs "bfe").length = B ∧
      (∀ i, (σ'.arrs "bfe").getD i 0 < B) ∧ Good C (σ'.arrs "bfe") L 0 := by
  let I : Env → Prop := fun τ => τ.vars "bfq" ≤ L ∧ τ.arrs "bfc" = C ∧
    (τ.arrs "bfe").length = B ∧ (∀ i, (τ.arrs "bfe").getD i 0 ≤ L + 2) ∧
    Good C (τ.arrs "bfe") L (τ.vars "bfq")
  have hdef : ∀ τ, I τ → ∃ v, (Cond.lt (.lit 0) (.var "bfq")).evalB B τ = some v :=
    fun τ hI => ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var (by have := hI.1; omega))⟩
  have hstep : ∀ τ, I τ → (Cond.lt (.lit 0) (.var "bfq")).evalB B τ = some true →
      ∃ τ', Run B endBody τ τ' 40 ∧ I τ' ∧ τ'.vars "bfq" < τ.vars "bfq" := by
    rintro τ ⟨h1, h2, h3, h4, h5⟩ hb
    have hpos : 0 < τ.vars "bfq" := by
      simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at hb
      obtain ⟨_, _, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := hb
      simpa using hr.symm
    obtain ⟨q, hq⟩ : ∃ q, τ.vars "bfq" = q + 1 := ⟨τ.vars "bfq" - 1, by omega⟩
    obtain ⟨τ', r, e1, e2⟩ := endBody_run hLB (by omega) hq h2 hCl hCB rfl h3 h4
    have hc' : τ'.arrs "bfc" = C := by rw [r.frame_arr "bfc" (by simp [endBody, Com.warrs]), h2]
    refine ⟨τ', r, ⟨by omega, hc', by rw [e2]; simp [h3], fun i => ?_, ?_⟩, by omega⟩
    · rw [e2, List.getD_eq_getElem?_getD, List.getElem?_set]
      split_ifs
      · exact endVal_le (by omega) h4
      · simp
      · rw [← List.getD_eq_getElem?_getD]; exact h4 i
    · rw [e2, e1]
      rw [hq] at h5
      exact good_set h5 (by omega)
  have hI0 : I (σ.setVar "bfq" L) := ⟨by simp, by simp [hC], by simp [hel],
    fun i => by simp only [arrs_setVar]; rw [hz i]; omega, by simpa using good_top C _ L⟩
  obtain ⟨σ', hrun, ⟨h1, -, h3, h4, h5⟩, hfalse⟩ := Run.while_count (B := B)
    (b := .lt (.lit 0) (.var "bfq")) (c := endBody) I (fun τ => τ.vars "bfq") 40 hdef hstep hI0
  have hq0 : σ'.vars "bfq" = 0 := by
    simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at hfalse
    obtain ⟨_, _, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := hfalse
    simp at hr; omega
  refine ⟨σ', ?_, h3, fun i => by have := h4 i; omega, by rw [hq0] at h5; exact h5⟩
  unfold endsCmd
  refine (Run.seq (Run.assign (v := L) (by simp [hl]; omega)) hrun).mono ?_
  simp only [Expr.size, Cond.size, vars_setVar, if_true]
  omega

end Lax185574Proofs.MC.Brute
