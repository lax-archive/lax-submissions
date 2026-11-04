import Lax185574Proofs.StpRam.Relax
import Lax185574Proofs.Conversions.Ram.Basic

/-!
The balls of lem:compute-stp, by breadth-first search along the resolved
pairs.

The resolved pairs are given by two adjacency structures in
compressed-row form, the edges in `eo`, `et` and the non-edges in `no`,
`nt`. `ballCmd` marks in the array `dm` the vertices within distance
`br` of the vertex `bu`. It clears `dm`, marks `bu`, and runs `br`
layers. A layer copies `dm` into `dn`, marks in `dn` the targets of the
rows of all marked vertices, and copies `dn` back. So after `s` layers
the marked vertices are the ball `ballP s` of radius `s`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax808846Proofs.Reasoning.Lib.Csr Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram

/-- The adjacency of the two structures. -/
def Adj2 (oE tE oN tN : ℕ → ℕ) (w v : ℕ) : Prop := InRow oE tE w v ∨ InRow oN tN w v

/-- The ball of radius `s` around `u`, along a relation on `[0, n)`. -/
def ballP (n : ℕ) (A : ℕ → ℕ → Prop) (u : ℕ) : ℕ → ℕ → Prop
  | 0 => fun v => v = u
  | s + 1 => fun v => ballP n A u s v ∨ ∃ w < n, ballP n A u s w ∧ A w v

/-- An indicator array: entry `v` is `1` exactly if `P v`, and `0`
otherwise. -/
def IndOn (n : ℕ) (g : ℕ → ℕ) (P : ℕ → Prop) : Prop := ∀ v < n, (g v = 1 ↔ P v) ∧ g v ≤ 1

/-! ### The scan of one layer -/

def scanBody : Com :=
  .seq (.ite (.eq (.get "dm" (.var "bw")) (.lit 1)) (.seq (relaxRow "eo" "et") (relaxRow "no" "nt"))
    .skip) (.assign "bw" (.add (.var "bw") (.lit 1)))

def scanAll : Com := .seq (.assign "bw" (.lit 0)) (.while (.lt (.var "bw") (.var "n")) scanBody)

/-- The two adjacency structures and the number of vertices. -/
def GraphAt (n nsE nsN : ℕ) (oE tE oN tN : ℕ → ℕ) (τ : Env) : Prop :=
  Csr "eo" "et" n nsE n oE tE τ ∧ Csr "no" "nt" n nsN n oN tN τ ∧ τ.vars "n" = n

theorem GraphAt.setVar {n nsE nsN : ℕ} {oE tE oN tN : ℕ → ℕ} {τ : Env}
    (h : GraphAt n nsE nsN oE tE oN tN τ) {x : String} (hx : x ≠ "n") (v : ℕ) :
    GraphAt n nsE nsN oE tE oN tN (τ.setVar x v) :=
  ⟨h.1.setVar _ _, h.2.1.setVar _ _, by simp only [vars_setVar, if_neg (Ne.symm hx)]; exact h.2.2⟩

theorem GraphAt.setArr {n nsE nsN : ℕ} {oE tE oN tN : ℕ → ℕ} {τ : Env}
    (h : GraphAt n nsE nsN oE tE oN tN τ) {a : String} (h1 : a ≠ "eo") (h2 : a ≠ "et")
    (h3 : a ≠ "no") (h4 : a ≠ "nt") (i v : ℕ) :
    GraphAt n nsE nsN oE tE oN tN (τ.setArr a i v) :=
  ⟨h.1.setArr_of_ne h1 h2 _ _, h.2.1.setArr_of_ne h3 h4 _ _, by simp [h.2.2]⟩

theorem GraphAt.of_arrs {n nsE nsN : ℕ} {oE tE oN tN : ℕ → ℕ} {τ τ' : Env}
    (h : GraphAt n nsE nsN oE tE oN tN τ) (hn : τ'.vars "n" = τ.vars "n")
    (h1 : τ'.arrs "eo" = τ.arrs "eo") (h2 : τ'.arrs "et" = τ.arrs "et")
    (h3 : τ'.arrs "no" = τ.arrs "no") (h4 : τ'.arrs "nt" = τ.arrs "nt") :
    GraphAt n nsE nsN oE tE oN tN τ' := by
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩, hn'⟩ := h
  exact ⟨⟨by rw [h1, a1], by rw [h2, a2], a3, a4, a5⟩, ⟨by rw [h3, b1], by rw [h4, b2], b3, b4, b5⟩,
    by rw [hn, hn']⟩

/-- **The scan of a layer.** -/
theorem scanAll_run {B n nsE nsN : ℕ} {oE tE oN tN f g : ℕ → ℕ} {P Q : ℕ → Prop} {σ : Env}
    (hG : GraphAt n nsE nsN oE tE oN tN σ) (hnB : n + 2 < B) (hEB : nsE + 1 < B) (hNB : nsN + 1 < B)
    (hdm : σ.arrs "dm" = arrOf n f) (hf : IndOn n f P) (hdn : σ.arrs "dn" = arrOf n g)
    (hg : IndOn n g Q) :
    ∃ σ' g', Run B scanAll σ σ' (50 * n + 14 * (nsE + nsN) + 6) ∧ σ'.arrs "dn" = arrOf n g' ∧
      IndOn n g' (fun v => Q v ∨ ∃ w < n, P w ∧ Adj2 oE tE oN tN w v) := by
  set σ0 := σ.setVar "bw" 0 with hσ0
  let I : Env → Prop := fun τ => GraphAt n nsE nsN oE tE oN tN τ ∧ τ.vars "bw" ≤ n ∧
    τ.arrs "dm" = arrOf n f ∧ ∃ g', τ.arrs "dn" = arrOf n g' ∧
      IndOn n g' (fun v => Q v ∨ ∃ w < τ.vars "bw", P w ∧ Adj2 oE tE oN tN w v)
  let Φ : Env → ℕ := fun τ => 50 * (n - τ.vars "bw") +
    14 * ((oE n - oE (τ.vars "bw")) + (oN n - oN (τ.vars "bw")))
  have hI0 : I σ0 := by
    refine ⟨hG.setVar (by decide) _, by simp [hσ0], by simp [hσ0, hdm], g, by simp [hσ0, hdn],
      fun v hv => ⟨?_, (hg v hv).2⟩⟩
    rw [(hg v hv).1]; simp [hσ0]
  obtain ⟨σ', K, hrun, ⟨hG', hbw', hdm', g', hdg', hg'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "bw") (.var "n")) (c := scanBody) I Φ
      (fun τ hI => evalB_condLt_vars (by have := hI.2.1; omega) (by rw [hI.1.2.2]; omega))
      (by
        rintro τ ⟨hGτ, hbw, hdmτ, g1, hdg1, hg1⟩ hc
        set w := τ.vars "bw" with hw
        have hwn : w < n := by have := lt_of_condLt_true hc; rwa [hGτ.2.2] at this
        have hfw : f w ≤ 1 := (hf w hwn).2
        have hcond : (Cond.eq (.get "dm" (.var "bw")) (.lit 1)).evalB B τ = some (f w == 1) := by
          rw [evalB_condEq_iff]
          refine ⟨f w, 1, ?_, by simp; omega, rfl⟩
          simp only [evalB_get_iff, evalB_var_iff]
          exact ⟨w, ⟨rfl, by omega⟩, by rw [hdmτ, getElem?_arrOf _ hwn], by omega⟩
        have hEle := hGτ.1.off_le_succ hwn
        have hNle := hGτ.2.1.off_le_succ hwn
        have hEn : oE (w + 1) ≤ oE n := hGτ.1.mono (by omega) le_rfl
        have hNn : oN (w + 1) ≤ oN n := hGτ.2.1.mono (by omega) le_rfl
        -- the branch
        obtain ⟨τ2, g2, K2, hr2, hdg2, hg2, hfr2, hK2⟩ : ∃ τ2 g2 K2, Run B (.ite (.eq (.get "dm" (.var "bw"))
            (.lit 1)) (.seq (relaxRow "eo" "et") (relaxRow "no" "nt")) .skip) τ τ2 K2 ∧
            τ2.arrs "dn" = arrOf n g2 ∧
            IndOn n g2 (fun v => Q v ∨ ∃ w' < w + 1, P w' ∧ Adj2 oE tE oN tN w' v) ∧
            (τ2.vars "bw" = w ∧ GraphAt n nsE nsN oE tE oN tN τ2 ∧ τ2.arrs "dm" = arrOf n f) ∧
            K2 ≤ 14 * ((oE (w + 1) - oE w) + (oN (w + 1) - oN w)) + 33 := by
          by_cases hfw1 : f w = 1
          · have hPw : P w := (hf w hwn).1.mp hfw1
            obtain ⟨τa, ga, hra, hdga, hga⟩ := relaxRow_run (B := B) hGτ.1 (by omega) (by omega) hw.symm hwn hdg1
              (fun v hv => (hg1 v hv).2) (by decide) (by decide)
            have hfa := hra.frame_var
            have hGa : GraphAt n nsE nsN oE tE oN tN τa := hGτ.of_arrs
              (hra.frame_var "n" (by simp [relaxRow_wvars])) (hra.frame_arr _ (by simp [relaxRow_warrs]))
              (hra.frame_arr _ (by simp [relaxRow_warrs])) (hra.frame_arr _ (by simp [relaxRow_warrs]))
              (hra.frame_arr _ (by simp [relaxRow_warrs]))
            have hwa : τa.vars "bw" = w := by rw [hra.frame_var "bw" (by simp [relaxRow_wvars])]
            obtain ⟨τb, gb, hrb, hdgb, hgb⟩ := relaxRow_run (B := B) hGa.2.1 (by omega) (by omega) hwa hwn hdga
              (fun v hv => (hga v hv).2) (by decide) (by decide)
            have hGb : GraphAt n nsE nsN oE tE oN tN τb := hGa.of_arrs
              (hrb.frame_var "n" (by simp [relaxRow_wvars])) (hrb.frame_arr _ (by simp [relaxRow_warrs]))
              (hrb.frame_arr _ (by simp [relaxRow_warrs])) (hrb.frame_arr _ (by simp [relaxRow_warrs]))
              (hrb.frame_arr _ (by simp [relaxRow_warrs]))
            refine ⟨τb, gb, _, Run.ite_true (by rw [hcond]; simp [hfw1]) (Run.seq hra hrb), hdgb,
              fun v hv => ⟨?_, (hgb v hv).2⟩,
              ⟨by rw [hrb.frame_var "bw" (by simp [relaxRow_wvars]), hwa], hGb,
                by rw [hrb.frame_arr "dm" (by simp [relaxRow_warrs]),
                  hra.frame_arr "dm" (by simp [relaxRow_warrs]), hdmτ]⟩, by simp; omega⟩
            rw [(hgb v hv).1, (hga v hv).1, (hg1 v hv).1]
            constructor
            · rintro (((h | ⟨w', hw', h1, h2⟩) | h) | h)
              · exact Or.inl h
              · exact Or.inr ⟨w', by omega, h1, h2⟩
              · exact Or.inr ⟨w, by omega, hPw, Or.inl h⟩
              · exact Or.inr ⟨w, by omega, hPw, Or.inr h⟩
            · rintro (h | ⟨w', hw', h1, h2⟩)
              · exact Or.inl (Or.inl (Or.inl h))
              · rcases Nat.lt_or_ge w' w with h | h
                · exact Or.inl (Or.inl (Or.inr ⟨w', h, h1, h2⟩))
                · obtain rfl : w' = w := by omega
                  rcases h2 with h2 | h2
                  · exact Or.inl (Or.inr h2)
                  · exact Or.inr h2
          · refine ⟨τ, g1, _, Run.ite_false (by rw [hcond]; simp [hfw1]) Run.skip, hdg1,
              fun v hv => ⟨?_, (hg1 v hv).2⟩, ⟨rfl, hGτ, hdmτ⟩, by simp⟩
            rw [(hg1 v hv).1]
            constructor
            · rintro (h | ⟨w', hw', h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨w', by omega, h1, h2⟩
            · rintro (h | ⟨w', hw', h1, h2⟩)
              · exact Or.inl h
              · refine Or.inr ⟨w', ?_, h1, h2⟩
                rcases Nat.lt_or_ge w' w with h | h
                · exact h
                · have hww : w' = w := by omega
                  rw [hww] at h1
                  exact absurd ((hf w hwn).1.mpr h1) hfw1
        obtain ⟨hw2, hG2, hdm2⟩ := hfr2
        refine ⟨τ2.setVar "bw" (w + 1), _, Run.seq hr2 (Run.assign (v := w + 1) ?_),
          ⟨hG2.setVar (by decide) _, by simp; omega, by simp [hdm2], g2, by simp [hdg2], ?_⟩, ?_⟩
        · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
          exact ⟨w, 1, ⟨hw2.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
        · simpa using hg2
        · simp only [Φ, vars_setVar, if_true, Expr.size, size_condLt]
          rw [← hw]
          have : n - w = (n - (w + 1)) + 1 := by omega
          rw [this]
          have e1 : oE n - oE w = (oE n - oE (w + 1)) + (oE (w + 1) - oE w) := by omega
          have e2 : oN n - oN w = (oN n - oN (w + 1)) + (oN (w + 1) - oN w) := by omega
          rw [e1, e2]
          nlinarith)
      hI0
  have hbwn : σ'.vars "bw" = n := by
    have := le_of_condLt_false hfalse; rw [hG'.2.2] at this; omega
  refine ⟨σ', g', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono ?_, hdg', ?_⟩
  · simp only [Φ, hσ0, vars_setVar, if_true, Nat.sub_zero, size_condLt, Expr.size] at hK ⊢
    have h1 : oE n - oE 0 ≤ nsE := by rw [hG.1.last]; omega
    have h2 : oN n - oN 0 ≤ nsN := by rw [hG.2.1.last]; omega
    nlinarith
  · rw [hbwn] at hg'; exact hg'

end Lax185574Proofs.StpRam
