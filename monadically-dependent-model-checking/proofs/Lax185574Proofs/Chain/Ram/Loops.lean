import Lax185574Proofs.Chain.Ram.TypesRam
import Lax185574Proofs.Chain.Ram.PdRun

/-!
Two generic loops: summing an expression over `i < n` (`sumLoop`), and
scanning `w = 0, 1, …` for the first vertex passing a test (`scanFirst`).

The test of `scanFirst` is a command that leaves `ind (p w)` in `ok`.
Its cost may vary, as long as it is paid by a constant `Kt` and the
drop of a potential `Φ` of the environment: this is how the pointer
scans of the predamping rules are paid for. The scan stops at the first
vertex passing the test and leaves it in `fw`, or `n` if there is none.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram

theorem sum_ind_eq_card (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ∑ k ∈ range n, ind (p k) = ((range n).filter p).card := by
  classical
  rw [card_filter]
  refine sum_congr rfl fun k _ => ?_
  unfold ind; split_ifs <;> rfl

/-- `acc := Σ_{i < n} e`. -/
def sumLoop (i acc : String) (e : Expr) : Com :=
  .seq (.assign acc (.lit 0)) (forUp i (.var "n") (.assign acc (.add (.var acc) e)))

theorem sumLoop_run {B n K : ℕ} {i acc : String} {e : Expr} (hia : i ≠ acc)
    (Ctx : Env → Prop) (f : ℕ → ℕ) (hB : ∑ k ∈ range n, f k < B) (hnB : n < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n)
    (hCi : ∀ τ x, Ctx τ → Ctx (τ.setVar i x)) (hCa : ∀ τ x, Ctx τ → Ctx (τ.setVar acc x))
    (he : ∀ τ k, Ctx τ → τ.vars i = k → k < n → e.evalB B τ = some (f k))
    (hsz : e.size + 3 ≤ K) {σ : Env} (hσ : Ctx σ) :
    ∃ σ', Run B (sumLoop i acc e) σ σ' (n * (K + 8) + 10) ∧ Ctx σ' ∧
      σ'.vars acc = ∑ k ∈ range n, f k ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out := by
  have hmono : ∀ k ≤ n, ∑ j ∈ range k, f j ≤ ∑ j ∈ range n, f j := fun k hk =>
    sum_le_sum_of_subset (range_subset_range.2 hk)
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ τ.vars acc = ∑ j ∈ range k, f j ∧
    τ.arrs = σ.arrs ∧ τ.out = σ.out
  obtain ⟨σ', hr, ⟨hC, ha, harr, hout⟩, -⟩ :=
    forUp_run (B := B) (i := i) (e := .var "n") (body := .assign acc (.add (.var acc) e)) (N := n)
      (K := K) I hnB
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ.setVar acc 0) ⟨hCi _ _ (hCa _ _ hσ), by simp [Ne.symm hia], rfl, rfl⟩
      (by
        rintro k hk τ ⟨hC, ha, harr, hout⟩ hik
        have hfk := he τ k hC hik hk
        have hsum : ∑ j ∈ range k, f j + f k < B := by
          have := hmono (k + 1) hk; rw [sum_range_succ] at this; omega
        refine ⟨τ.setVar acc (∑ j ∈ range k, f j + f k),
          (Run.assign (x := acc) (e := .add (.var acc) e) (v := ∑ j ∈ range k, f j + f k)
            (by
              have := evalB_bin (op := .add) (evalB_var (B := B) (x := acc) (σ := τ)
                (by rw [ha]; omega)) hfk (by simp [ha]; omega)
              simpa [ha] using this)).mono (by simp; omega),
          by simp [hia, hik], hCi _ _ (hCa _ _ hC), ?_, harr, hout⟩
        simp [Ne.symm hia, sum_range_succ])
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hr).mono (by simp; ring_nf; omega),
    hC, ha, harr, hout⟩

/-- Scan `w = 0, 1, …, n - 1` for the first vertex passing `tst`, which
leaves its verdict in `ok`; the vertex goes to `fw`, or `n` if none. -/
def scanFirst (tst : Com) : Com :=
  .seq (.assign "w" (.lit 0)) (.seq (.assign "fw" (.var "n"))
    (.while (.lt (.var "w") (.var "n"))
      (.seq tst (.ite (.eq (.var "ok") (.lit 1))
        (.seq (.assign "fw" (.var "w")) (.assign "w" (.var "n")))
        (.assign "w" (.add (.var "w") (.lit 1)))))))

/-- **The scan for the first vertex.** -/
theorem scanFirst_run {B n Kt : ℕ} {tst : Com} (Inv : Env → Prop) (Φ : Env → ℕ)
    (p : ℕ → Prop) (hnB : n + 1 < B)
    (hIn : ∀ τ, Inv τ → τ.vars "n" = n)
    (hIw : ∀ τ x, Inv τ → Inv (τ.setVar "w" x)) (hIf : ∀ τ x, Inv τ → Inv (τ.setVar "fw" x))
    (hΦw : ∀ τ x, Φ (τ.setVar "w" x) = Φ τ) (hΦf : ∀ τ x, Φ (τ.setVar "fw" x) = Φ τ)
    (htst : ∀ τ k, Inv τ → τ.vars "w" = k → k < n → ∃ τ' K, Run B tst τ τ' K ∧ Inv τ' ∧
      τ'.vars "w" = k ∧ τ'.vars "fw" = τ.vars "fw" ∧ τ'.vars "ok" = ind (p k) ∧
      K + Φ τ' ≤ Kt + Φ τ)
    {σ : Env} (hσ : Inv σ) :
    ∃ σ' K, Run B (scanFirst tst) σ σ' K ∧ Inv σ' ∧ σ'.vars "fw" = (firstN n p).getD n ∧
      K + Φ σ' ≤ n * (Kt + 20) + 20 + Φ σ := by
  classical
  let J : Env → Prop := fun τ => Inv τ ∧ τ.vars "w" ≤ n ∧
    ((τ.vars "w" < n ∧ τ.vars "fw" = n ∧ ∀ v < τ.vars "w", ¬ p v) ∨
     (τ.vars "w" = n ∧ τ.vars "fw" = (firstN n p).getD n))
  let Ψ : Env → ℕ := fun τ => Φ τ + (n - τ.vars "w") * (Kt + 20)
  have hσn := hIn σ hσ
  have hJ0 : J ((σ.setVar "w" 0).setVar "fw" n) := by
    refine ⟨hIf _ _ (hIw _ _ hσ), by simp, ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · right
      subst h0; simp [firstN]
    · left; simp [hpos]
  obtain ⟨σ', K, hr, ⟨hI', hw', hst'⟩, hf', hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "w") (.var "n"))
      (c := .seq tst (.ite (.eq (.var "ok") (.lit 1))
        (.seq (.assign "fw" (.var "w")) (.assign "w" (.var "n")))
        (.assign "w" (.add (.var "w") (.lit 1))))) J Ψ
      (fun τ hJ => evalB_condLt_vars (by have := hJ.2.1; omega) (by rw [hIn τ hJ.1]; omega))
      (by
        rintro τ ⟨hIτ, hwle, hst⟩ hc
        have hwn : τ.vars "w" < n := by
          have := lt_of_condLt_true hc; rw [hIn τ hIτ] at this; exact this
        have hst' : τ.vars "fw" = n ∧ ∀ v < τ.vars "w", ¬ p v := by
          rcases hst with ⟨-, h1, h2⟩ | ⟨h1, -⟩
          · exact ⟨h1, h2⟩
          · omega
        set k := τ.vars "w" with hk
        obtain ⟨τ1, K1, hr1, hI1, hw1, hf1, hok1, hK1⟩ := htst τ k hIτ rfl hwn
        have hn1 := hIn τ1 hI1
        by_cases hp : p k
        · have hok : τ1.vars "ok" = 1 := by rw [hok1]; simp [ind, hp]
          have hfirst : firstN n p = some k := firstN_eq_some.2 ⟨hwn, hp, hst'.2⟩
          refine ⟨(τ1.setVar "fw" k).setVar "w" n, _, Run.seq hr1 (Run.ite_true
            (by rw [eq_lit_evalB (by omega) (by omega)]; simp [hok])
            (Run.seq (Run.assign (v := k) (by simp [hw1]; omega))
              (Run.assign (v := n) (by simp [hn1]; omega)))), ⟨hIw _ _ (hIf _ _ hI1), by simp,
              Or.inr ⟨by simp, by simp [hfirst]⟩⟩, ?_⟩
          simp only [Ψ, Cond.size, Expr.size, vars_setVar, if_true, hΦw, hΦf, Nat.sub_self,
            zero_mul, add_zero, ← hk]
          have : (n - k) * (Kt + 20) ≥ Kt + 20 := by
            have : 1 ≤ n - k := by omega
            nlinarith
          omega
        · have hok : τ1.vars "ok" = 0 := by rw [hok1]; simp [ind, hp]
          refine ⟨τ1.setVar "w" (k + 1), _, Run.seq hr1 (Run.ite_false
            (by rw [eq_lit_evalB (by omega) (by omega)]; simp [hok])
            (Run.assign (v := k + 1) (by simp [hw1]; omega))), ⟨hIw _ _ hI1, by simp; omega, ?_⟩,
            ?_⟩
          · have hall : ∀ v < k + 1, ¬ p v := fun v hv => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
              · exact hst'.2 v hv
              · exact hp
            rcases Nat.lt_or_ge (k + 1) n with hlt | hge
            · left; simp only [vars_setVar, if_true]; exact ⟨hlt, by simp [hf1, hst'.1], hall⟩
            · right
              have hkn : k + 1 = n := by omega
              have : firstN n p = none := firstN_eq_none.2 fun v hv => hall v (by omega)
              simp [this, hkn, hf1, hst'.1]
          · simp only [Ψ, Cond.size, Expr.size, vars_setVar, if_true, hΦw, ← hk]
            have : n - k = (n - (k + 1)) + 1 := by omega
            rw [this, Nat.add_mul, one_mul]
            omega)
      hJ0
  have hwn : σ'.vars "w" = n := by
    have := le_of_condLt_false hf'; rw [hIn σ' hI'] at this; omega
  have hfw : σ'.vars "fw" = (firstN n p).getD n := by
    rcases hst' with ⟨h1, -, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  refine ⟨σ', _, Run.seq (Run.assign (v := 0) (by simp; omega))
    (Run.seq (Run.assign (v := n) (by simp [hσn]; omega)) hr), hI', hfw, ?_⟩
  have e1 : Ψ σ' = Φ σ' := by simp only [Ψ, hwn, Nat.sub_self, zero_mul, add_zero]
  have e2 : Ψ ((σ.setVar "w" 0).setVar "fw" n) = Φ σ + n * (Kt + 20) := by
    simp only [Ψ, hΦf, hΦw]; simp
  rw [e1, e2] at hK
  simp only [Cond.size, Expr.size] at hK ⊢
  omega

end Lax185574Proofs.Chain.Ram
