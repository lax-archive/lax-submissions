import Lax185574Proofs.Conversions.Ram.Basic
import Lax185574Proofs.Words.FinsetWords

/-!
Counting and writing the vertices `w < n` that pass a test.

`countRow c` leaves in `d` the number of `w < n` for which the condition
`c` holds, and `emitRow c` writes the frames `1, w` of these `w` in
increasing order. Both use the scalar `w`, and `countRow` also `d`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The numbers below `n` with the property `p`, in increasing order. -/
noncomputable def below (n : ℕ) (p : ℕ → Prop) : List ℕ :=
  open Classical in (List.range n).filter fun w => decide (p w)

theorem below_succ (n : ℕ) (p : ℕ → Prop) :
    below (n + 1) p = below n p ++ (open Classical in if p n then [n] else []) := by
  classical
  simp only [below, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases h : p n <;> simp [h]

theorem mem_below {n : ℕ} {p : ℕ → Prop} {w : ℕ} : w ∈ below n p ↔ w < n ∧ p w := by
  classical
  simp [below]

theorem below_pairwise (n : ℕ) (p : ℕ → Prop) : (below n p).Pairwise (· < ·) := by
  classical
  exact List.Pairwise.filter _ (List.pairwise_lt_range)

/-- Count the `w < n` passing `c` into `d`. -/
def countRow (c : Cond) : Com :=
  .seq (.assign "d" (.lit 0))
    (forUp "w" (.var "n") (.ite c (.assign "d" (.add (.var "d") (.lit 1))) .skip))

/-- Write the frames `1, w` of the `w < n` passing `c`. -/
def emitRow (c : Cond) : Com :=
  forUp "w" (.var "n") (.ite c (.seq (.write (.lit 1)) (.write (.var "w"))) .skip)

theorem countRow_run {B n : ℕ} {c : Cond} (Ctx : Env → Prop) (p : ℕ → Prop) [DecidablePred p]
    (hnB : n + 1 < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n)
    (hCw : ∀ τ x, Ctx τ → Ctx (τ.setVar "w" x)) (hCd : ∀ τ x, Ctx τ → Ctx (τ.setVar "d" x))
    (hc : ∀ τ k, Ctx τ → τ.vars "w" = k → k < n → c.evalB B τ = some (decide (p k)))
    {σ : Env} (hσ : Ctx σ) :
    ∃ σ', Run B (countRow c) σ σ' (n * (c.size + 13) + 8) ∧ Ctx σ' ∧
      σ'.vars "d" = (below n p).length ∧ σ'.out = σ.out := by
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ τ.vars "d" = (below k p).length ∧ τ.out = σ.out
  have hlen : ∀ k, (below k p).length ≤ k := fun k => by
    simp only [below]; exact (List.length_filter_le _ _).trans (by simp)
  obtain ⟨σ', hr, ⟨hC, hd, ho⟩, -⟩ :=
    forUp_run (B := B) (i := "w") (e := .var "n")
      (body := .ite c (.assign "d" (.add (.var "d") (.lit 1))) .skip) (N := n)
      (K := c.size + 5) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ.setVar "d" 0) ⟨hCw _ _ (hCd _ _ hσ), by simp [below], by simp⟩
      (by
        rintro k hk τ ⟨hC, hd, ho⟩ hwk
        have hb := below_succ k p
        have hck := hc τ k hC hwk hk
        by_cases hp : p k
        · have hlk := hlen k
          have hct : c.evalB B τ = some true := by rw [hck]; simp [hp]
          refine ⟨τ.setVar "d" ((below k p).length + 1), (Run.ite_true hct
            (Run.assign (by simp [hd]; omega))).mono (by simp; omega), by simp [hwk],
            hCw _ _ (hCd _ _ hC), by simp [hb, hp], by simp [ho]⟩
        · have hcf : c.evalB B τ = some false := by rw [hck]; simp [hp]
          refine ⟨τ, (Run.ite_false hcf Run.skip).mono
            (by simp; omega), hwk, hCw _ _ hC, by simp [hd, hb, hp], by simp [ho]⟩)
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hr).mono (by simp; ring_nf; omega),
    hC, hd, ho⟩

theorem emitRow_run {B n : ℕ} {c : Cond} (Ctx : Env → Prop) (p : ℕ → Prop) [DecidablePred p]
    (hnB : n + 1 < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n)
    (hCw : ∀ τ x, Ctx τ → Ctx (τ.setVar "w" x))
    (hCo : ∀ τ o, Ctx τ → Ctx { τ with out := o })
    (hc : ∀ τ k, Ctx τ → τ.vars "w" = k → k < n → c.evalB B τ = some (decide (p k)))
    {σ : Env} (hσ : Ctx σ) :
    ∃ σ', Run B (emitRow c) σ σ' (n * (c.size + 14) + 6) ∧ Ctx σ' ∧
      σ'.out = σ.out ++ elemFrames (below n p) := by
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ τ.out = σ.out ++ elemFrames (below k p)
  obtain ⟨σ', hr, ⟨hC, ho⟩, -⟩ :=
    forUp_run (B := B) (i := "w") (e := .var "n")
      (body := .ite c (.seq (.write (.lit 1)) (.write (.var "w"))) .skip) (N := n)
      (K := c.size + 6) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ) ⟨hCw _ _ hσ, by simp [below, elemFrames]⟩
      (by
        rintro k hk τ ⟨hC, ho⟩ hwk
        have hb := below_succ k p
        have hck := hc τ k hC hwk hk
        by_cases hp : p k
        · have hct : c.evalB B τ = some true := by rw [hck]; simp [hp]
          refine ⟨{ { τ with out := τ.out ++ [1] } with out := τ.out ++ [1] ++ [k] },
            (Run.ite_true hct (Run.seq
              (Run.write (v := 1) (by simp; omega)) (Run.write (v := k) (by simp [hwk]; omega)))).mono
              (by simp; omega), by simp [hwk], hCw _ _ (hCo _ _ hC), ?_⟩
          simp [ho, hb, hp, elemFrames]
        · have hcf : c.evalB B τ = some false := by rw [hck]; simp [hp]
          refine ⟨τ, (Run.ite_false hcf Run.skip).mono
            (by simp; omega), hwk, hCw _ _ hC, by simp [ho, hb, hp]⟩)
  exact ⟨σ', hr.mono (by simp), hC, ho⟩

end Lax185574Proofs.Conversions.Ram
