import Lax3Proofs.Refine.OrderActiveWork

/-!
# Compact elimination in the active order workspace

The resident compact CSR lives in `gof`/`gtg`; the level graph remains in
`off`/`tgt`.  This file prepares the landed elimination engine directly on
that resident CSR.  Every initialization is bounded by the active carrier
`mm`, and the ambient carrier is saved before `n` is changed.
-/

namespace Lax3Proofs.Refine.OrderActiveElim

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamDriver (fillUpto)
open Lax3Proofs.Refine.ScatterBlock (renEnv renEnv_arrs renEnv_vars)
open Lax3Proofs.Refine.ElimCompact (ElimPreC)
open Lax3Proofs.Refine.OrderActiveWork

/-- Initialize precisely the three live prefixes read by elimination,
then save the ambient carrier and install the compact one. -/
def elimWorkPrep : Com :=
  .seq (fillUpto "alv" (.var "mm") (.lit 1))
    (.seq (fillUpto "elm" (.var "mm") (.lit 0))
      (.seq (fillUpto "bh" (.add (.var "mm") (.lit 1)) (.lit 0))
        (.seq (.assign "kn" (.var "n")) (.assign "n" (.var "mm")))))

/-- Exact sum of the three prefix fills and two scalar assignments. -/
def elimWorkPrepCost (mm : ℕ) : ℕ := 35 * mm + 37

/-- Preparation exposes `ElimPreC` through `engineWorkSwap`: conceptual
`off`/`tgt` are the resident `gof`/`gtg`, while all engine scratch keeps
its physical carrier-sized allocation. -/
theorem elimWorkPrep_spec {B n mm W : ℕ} {O T : ℕ → ℕ} {σ : Env}
    (hnB : n < B) (hmmB : mm + 1 < B) (hmn : mm ≤ n)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hgof : σ.arrs "gof" = arrOf (n + 1) O) (hgtg : σ.arrs "gtg" = arrOf W T)
    (halv : ∃ g, σ.arrs "alv" = arrOf n g) (hdeg : ∃ g, σ.arrs "deg" = arrOf n g)
    (helm : ∃ g, σ.arrs "elm" = arrOf n g) (hrnk : ∃ g, σ.arrs "rnk" = arrOf n g)
    (hidg : ∃ g, σ.arrs "idg" = arrOf n g)
    (hbh : ∃ g, σ.arrs "bh" = arrOf (n + 1) g)
    (hbv : ∃ g, σ.arrs "bv" = arrOf (n + W + 1) g)
    (hbn : ∃ g, σ.arrs "bn" = arrOf (n + W + 1) g)
    (hioff : ∃ g, σ.arrs "ioff" = arrOf (n + 1) g)
    (hifl : ∃ g, σ.arrs "ifl" = arrOf n g)
    (hitg : ∃ g, σ.arrs "itg" = arrOf W g) :
    ∃ σ', Run B elimWorkPrep σ σ' (elimWorkPrepCost mm) ∧
      ElimPreC mm n W W O T (fun _ => 1) (renEnv engineWorkSwap σ') ∧
      σ'.vars "kn" = n ∧ σ'.vars "mm" = mm ∧
      σ'.arrs "off" = σ.arrs "off" ∧ σ'.arrs "tgt" = σ.arrs "tgt" := by
  classical
  have hp₁ := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) mm n "alv"
    (.var "mm") (.lit 1) (fun _ => 1) (fun τ => τ.vars "mm" = mm)
    (by omega) (by omega) hmn
    (fun τ τ' hQ hv _ => by rw [← hQ]; exact hv "mm" (by decide))
    (fun τ hQ => by rw [← hQ]; exact evalB_var (by rw [hQ]; omega))
    (fun _ _ _ => evalB_lit (by omega))
  obtain ⟨σ₁, r₁, ⟨A₁, hA₁, hA₁lo, -⟩, -, hmm₁⟩ := hp₁ σ ⟨halv, hmm⟩
  have hp₂ := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) mm n "elm"
    (.var "mm") (.lit 0) (fun _ => 0) (fun τ => τ.vars "mm" = mm)
    (by omega) (by omega) hmn
    (fun τ τ' hQ hv _ => by rw [← hQ]; exact hv "mm" (by decide))
    (fun τ hQ => by rw [← hQ]; exact evalB_var (by rw [hQ]; omega))
    (fun _ _ _ => evalB_lit (by omega))
  obtain ⟨σ₂, r₂, ⟨E₂, hE₂, hE₂lo, -⟩, -, hmm₂⟩ :=
    hp₂ σ₁ ⟨(by
      obtain ⟨g, hg⟩ := helm
      exact ⟨g, by rw [r₁.frame_arr "elm" (by decide), hg]⟩), hmm₁⟩
  have hp₃ := Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) (mm + 1) (n + 1) "bh"
    (.add (.var "mm") (.lit 1)) (.lit 0) (fun _ => 0) (fun τ => τ.vars "mm" = mm)
    (by omega) hmmB (by omega)
    (fun τ τ' hQ hv _ => by rw [← hQ]; exact hv "mm" (by decide))
    (fun τ hQ => by
      have h := evalB_bin (op := .add) (B := B) (σ := τ)
        (evalB_var (x := "mm") (by rw [hQ]; omega)) (evalB_lit (B := B) (n := 1) (by omega))
        (by rw [Bop.apply_add, hQ]; omega)
      rwa [Bop.apply_add, hQ] at h)
    (fun _ _ _ => evalB_lit (by omega))
  obtain ⟨σ₃, r₃, ⟨H₃, hH₃, hH₃lo, -⟩, -, hmm₃⟩ :=
    hp₃ σ₂ ⟨(by
      obtain ⟨g, hg⟩ := hbh
      exact ⟨g, by rw [r₂.frame_arr "bh" (by decide),
        r₁.frame_arr "bh" (by decide), hg]⟩), hmm₂⟩
  have hn₃ : σ₃.vars "n" = n := by
    rw [r₃.frame_var "n" (by decide), r₂.frame_var "n" (by decide),
      r₁.frame_var "n" (by decide), hn]
  have r₄ : Run B (.assign "kn" (.var "n")) σ₃ (σ₃.setVar "kn" n) 2 := by
    have h := Run.assign (B := B) (σ := σ₃) (x := "kn") (e := .var "n")
      (evalB_var (by rw [hn₃]; exact hnB))
    rw [hn₃] at h
    simpa using h
  have hmm₄ : (σ₃.setVar "kn" n).vars "mm" = mm := by simp [hmm₃]
  have r₅ : Run B (.assign "n" (.var "mm")) (σ₃.setVar "kn" n)
      ((σ₃.setVar "kn" n).setVar "n" mm) 2 := by
    have h := Run.assign (B := B) (σ := σ₃.setVar "kn" n) (x := "n") (e := .var "mm")
      (evalB_var (by rw [hmm₄]; omega))
    rw [hmm₄] at h
    simpa using h
  let σ' := (σ₃.setVar "kn" n).setVar "n" mm
  have rAll : Run B elimWorkPrep σ σ' (elimWorkPrepCost mm) := by
    change Run B elimWorkPrep σ ((σ₃.setVar "kn" n).setVar "n" mm)
      (elimWorkPrepCost mm)
    exact (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono (by
      simp only [elimWorkPrepCost, size_lit, size_var, size_add]
      omega)
  have hframe (a : String) (ha : a ∉ elimWorkPrep.warrs) : σ'.arrs a = σ.arrs a :=
    rAll.frame_arr a ha
  have hAlv : σ'.arrs "alv" = arrOf n A₁ := by
    change σ₃.arrs "alv" = arrOf n A₁
    rw [r₃.frame_arr "alv" (by decide), r₂.frame_arr "alv" (by decide), hA₁]
  have hElm : σ'.arrs "elm" = arrOf n E₂ := by
    change σ₃.arrs "elm" = arrOf n E₂
    rw [r₃.frame_arr "elm" (by decide), hE₂]
  have hBh : σ'.arrs "bh" = arrOf (n + 1) H₃ := by
    change σ₃.arrs "bh" = arrOf (n + 1) H₃
    exact hH₃
  have hfixed {a : String} {k : ℕ} (h : ∃ g, σ.arrs a = arrOf k g)
      (ha : a ∉ elimWorkPrep.warrs) : ∃ g, σ'.arrs a = arrOf k g := by
    obtain ⟨g, hg⟩ := h
    exact ⟨g, by rw [hframe a ha, hg]⟩
  refine ⟨σ', rAll, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, hmn, ⟨O, ?_, fun _ _ => rfl⟩, ?_, ⟨A₁, ?_, hA₁lo⟩,
      ?_, ⟨E₂, ?_, hE₂lo⟩, ?_, ?_,
      ⟨H₃, ?_, fun i hi => by simpa using hH₃lo i (by omega)⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [renEnv_vars, σ', vars_setVar, if_pos]
    · simpa only [renEnv_arrs, engineWorkSwap_off] using
        (show σ'.arrs "gof" = arrOf (n + 1) O by rw [hframe "gof" (by decide), hgof])
    · simpa only [renEnv_arrs, engineWorkSwap_tgt] using
        (show σ'.arrs "gtg" = arrOf W T by rw [hframe "gtg" (by decide), hgtg])
    · simpa [renEnv_arrs, engineWorkSwap] using hAlv
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hdeg (by decide)
    · simpa [renEnv_arrs, engineWorkSwap] using hElm
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hrnk (by decide)
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hidg (by decide)
    · simpa [renEnv_arrs, engineWorkSwap] using hBh
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hbv (by decide)
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hbn (by decide)
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hioff (by decide)
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hifl (by decide)
    · simpa [renEnv_arrs, engineWorkSwap] using hfixed hitg (by decide)
  · simp [σ']
  · simp [σ', hmm₃]
  · exact hframe "off" (by decide)
  · exact hframe "tgt" (by decide)

/-! ## Axioms -/

#print axioms elimWorkPrep_spec

end Lax3Proofs.Refine.OrderActiveElim
