import Lax3Proofs.Refine.OrderActiveWork
import Lax3Proofs.Refine.ElimCompactWalks

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
open Lax3Proofs.Refine.ScatterBlock (MemList renCom renEnv renEnv_arrs renEnv_vars
  renEnv_involutive renCom_run)
open Lax3Proofs.Refine.ElimCompact (ElimPreC ElimMemPost clen padArrs tailOf
  padArrs_arrs padArrs_vars getD_padArrs memGraph masked_of_all_alive scatterCom scatterCost)
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

/-! ## The resident elimination call -/

/-- Prepare the compact carrier, run elimination with its CSR redirected to
`gof`/`gtg`, scatter the compact ranks back through `mem`, and restore the
ambient carrier. -/
def elimWorkCom : Com :=
  .seq elimWorkPrep
    (.seq (renCom engineWorkSwap Lax3Proofs.RamElim.elimCom)
      (.seq scatterCom (.assign "n" (.var "kn"))))

/-- The exact composite charge.  In particular, the engine and scatter are
charged at the live carrier `mm`, not at the ambient carrier. -/
def elimWorkCost (mm ns : ℕ) : ℕ :=
  elimWorkPrepCost mm +
    (Lax3Proofs.RamElim.elimCost mm ns + (scatterCost mm + 2))

/-- Eliminate a compact member graph in the resident workspace.  The compact
rank is scattered to `ork[mem j]`, while the compact in-CSR stays in
`ioff`/`itg` for the augmentation rounds.  The level CSR is an explicit frame
and `n` is restored before returning. -/
theorem elimWork_spec {B n mm ns W : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Mem : ℕ → ℕ} {σ : Env}
    (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M))
    (hcsr : Lax3Proofs.RamElim.CsrSimple (memGraph G M hml) ns O T)
    (hB : mm + ns + 1 < B) (hnB : n < B) (hW : ns ≤ W)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hgof : σ.arrs "gof" = arrOf (n + 1) O) (hgtg : σ.arrs "gtg" = arrOf W T)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hork : ∃ g, σ.arrs "ork" = arrOf n g)
    (halv : ∃ g, σ.arrs "alv" = arrOf n g) (hdeg : ∃ g, σ.arrs "deg" = arrOf n g)
    (helm : ∃ g, σ.arrs "elm" = arrOf n g) (hrnk : ∃ g, σ.arrs "rnk" = arrOf n g)
    (hidg : ∃ g, σ.arrs "idg" = arrOf n g)
    (hbh : ∃ g, σ.arrs "bh" = arrOf (n + 1) g)
    (hbv : ∃ g, σ.arrs "bv" = arrOf (n + W + 1) g)
    (hbn : ∃ g, σ.arrs "bn" = arrOf (n + W + 1) g)
    (hioff : ∃ g, σ.arrs "ioff" = arrOf (n + 1) g)
    (hifl : ∃ g, σ.arrs "ifl" = arrOf n g)
    (hitg : ∃ g, σ.arrs "itg" = arrOf W g) :
    ∃ σ', Run B elimWorkCom σ σ' (elimWorkCost mm ns) ∧
      ElimMemPost G M Mem hml ns W σ' ∧
      σ'.vars "n" = n ∧ σ'.vars "mm" = mm ∧
      σ'.arrs "off" = σ.arrs "off" ∧ σ'.arrs "tgt" = σ.arrs "tgt" := by
  classical
  have hmn : mm ≤ n :=
    Lax3Proofs.Refine.ElimCompactWalks.card_le_of_smono
      (fun i j hij hj => hml.smono i j hij hj) (fun j hj => hml.lt j hj)
  obtain ⟨σ₁, r₁, hpre, hkn₁, hmm₁, -, -⟩ :=
    elimWorkPrep_spec hnB (by omega) hmn hn hmm hgof hgtg halv hdeg helm hrnk hidg hbh hbv
      hbn hioff hifl hitg
  obtain ⟨τ, r₂, hpost, hrnkLt⟩ :=
    Lax3Proofs.Refine.ElimCompact.elimCompact_engine hcsr hB
      (fun _ _ => show (1 : ℕ) < B by omega) hW hW hpre
  let ρ : Env := padArrs τ (tailOf (renEnv engineWorkSwap σ₁) (clen mm W W))
  let σ₂ : Env := renEnv engineWorkSwap ρ
  have r₂' : Run B (renCom engineWorkSwap Lax3Proofs.RamElim.elimCom) σ₁ σ₂
      (Lax3Proofs.RamElim.elimCost mm ns) := by
    have h := renCom_run (f := engineWorkSwap) engineWorkSwap_invol r₂
    change Run B (renCom engineWorkSwap Lax3Proofs.RamElim.elimCom) σ₁ σ₂
      (Lax3Proofs.RamElim.elimCost mm ns)
    dsimp [σ₂, ρ]
    rw [renEnv_involutive engineWorkSwap_invol σ₁] at h
    exact h
  obtain ⟨R, IO, IT, k, m, E, hrnkτ, hkτ, hioffτ, hitgτ, hm, hinj, horients,
    hindeg, hinN, htoG, hbd, hbdE, hdegE, hlow, hinc⟩ := hpost
  rw [masked_of_all_alive (memGraph G M hml) (M' := fun _ => 1)
    (fun _ _ => one_ne_zero)] at horients hinN htoG hbd hdegE hlow
  have hrnkρ : ∀ j, j < mm → (ρ.arrs "rnk").getD j 0 = R j := by
    intro j hj
    change ((padArrs τ (tailOf (renEnv engineWorkSwap σ₁) (clen mm W W))).arrs
      "rnk").getD j 0 = R j
    rw [getD_padArrs (by rw [hrnkτ]; simpa [arrOf] using hj), hrnkτ,
      getD_arrOf _ hj]
  have hrnk₂ : ∀ j, j < mm → (σ₂.arrs "rnk").getD j 0 = R j := by
    simpa only [σ₂, renEnv_arrs, engineWorkSwap] using hrnkρ
  have hRB : ∀ j, j < mm → R j < B := by
    intro j hj
    have h := hrnkLt j hj
    rw [hrnkτ, getD_arrOf _ hj] at h
    omega
  have hρlen : mm ≤ (σ₂.arrs "rnk").length := by
    dsimp [σ₂]
    simp only [engineWorkSwap]
    change mm ≤ ((padArrs τ (tailOf (renEnv engineWorkSwap σ₁) (clen mm W W))).arrs
      "rnk").length
    rw [padArrs_arrs, List.length_append, hrnkτ, length_arrOf]
    exact Nat.le_add_right _ _
  have hioffρ : ∀ i, i ≤ mm → (ρ.arrs "ioff").getD i 0 = IO i := by
    intro i hi
    change ((padArrs τ (tailOf (renEnv engineWorkSwap σ₁) (clen mm W W))).arrs
      "ioff").getD i 0 = IO i
    rw [getD_padArrs (by
      rw [hioffτ]
      simpa [arrOf] using Nat.lt_succ_of_le hi), hioffτ,
      getD_arrOf _ (Nat.lt_succ_of_le hi)]
  have hioff₂ : ∀ i, i ≤ mm → (σ₂.arrs "ioff").getD i 0 = IO i := by
    simpa only [σ₂, renEnv_arrs, engineWorkSwap] using hioffρ
  have hitgρ : ρ.arrs "itg" = arrOf W IT := by
    obtain ⟨g, hg⟩ := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have htail : ((renEnv engineWorkSwap σ₁).arrs "itg").drop
        (clen mm W W "itg") = [] := by
      rw [Lax3Proofs.Refine.ElimCompact.clen_itg, hg]
      exact List.drop_eq_nil_of_le (by simp [arrOf])
    change (padArrs τ (tailOf (renEnv engineWorkSwap σ₁) (clen mm W W))).arrs
      "itg" = arrOf W IT
    rw [padArrs_arrs, tailOf, htail, List.append_nil, hitgτ]
  have hitg₂ : σ₂.arrs "itg" = arrOf W IT := by
    simpa only [σ₂, renEnv_arrs, engineWorkSwap] using hitgρ
  have hk₂ : σ₂.vars "kmax" = k := by
    simpa only [σ₂, renEnv_vars, ρ, padArrs_vars] using hkτ
  have hmm₂ : σ₂.vars "mm" = mm := by
    rw [r₂'.frame_var "mm" (by decide), hmm₁]
  have hmem₂ : σ₂.arrs "mem" = arrOf n Mem := by
    rw [r₂'.frame_arr "mem" (by decide), r₁.frame_arr "mem" (by decide), hmem]
  have hork₂ : ∃ g, σ₂.arrs "ork" = arrOf n g := by
    obtain ⟨g, hg⟩ := hork
    exact ⟨g, by rw [r₂'.frame_arr "ork" (by decide),
      r₁.frame_arr "ork" (by decide), hg]⟩
  obtain ⟨σ₃, r₃, hork₃, hk₃, hioff₃, hitg₃⟩ :=
    Lax3Proofs.Refine.ElimCompactWalks.scatterBacksW R σ₂ hmm₂ hmem₂
      (fun j hj => hml.lt j hj) hrnk₂ hork₂
      (fun i j hij hj => hml.smono i j hij hj) hnB hRB hρlen
  have hkn₃ : σ₃.vars "kn" = n := by
    rw [r₃.frame_var "kn" (by decide), r₂'.frame_var "kn" (by decide), hkn₁]
  have r₄ : Run B (.assign "n" (.var "kn")) σ₃ (σ₃.setVar "n" n) 2 := by
    have h := Run.assign (B := B) (σ := σ₃) (x := "n") (e := .var "kn")
      (evalB_var (by rw [hkn₃]; exact hnB))
    rw [hkn₃] at h
    simpa using h
  let σ₄ := σ₃.setVar "n" n
  have rAll : Run B elimWorkCom σ σ₄ (elimWorkCost mm ns) := by
    simpa only [elimWorkCom, elimWorkCost, σ₄] using
      (r₁.seq (r₂'.seq (r₃.seq r₄)))
  refine ⟨σ₄, rAll, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨R, IO, IT, k, m, E, ?_, ?_, ?_, ?_, hm, hinj, horients, hindeg, hinN,
      htoG, hbd, hbdE, hdegE, hlow, hinc⟩
    · intro j hj
      simpa [σ₄] using hork₃ j hj
    · simpa [σ₄] using hk₃.trans hk₂
    · intro i hi
      simp only [σ₄, arrs_setVar]
      rw [hioff₃]
      exact hioff₂ i hi
    · simp only [σ₄, arrs_setVar]
      rw [hitg₃]
      exact hitg₂
  · simp [σ₄]
  · simp only [σ₄, vars_setVar, if_neg (by decide : ¬ ("mm" = "n"))]
    rw [r₃.frame_var "mm" (by decide), hmm₂]
  · exact rAll.frame_arr "off" (by decide)
  · exact rAll.frame_arr "tgt" (by decide)

/-! ## Axioms -/

#print axioms elimWorkPrep_spec
#print axioms elimWork_spec

end Lax3Proofs.Refine.OrderActiveElim
