import Lax185574Proofs.StpRam.Ball
import Lax185574Proofs.TreeAlgo.ComputeScatterType

/-!
The ball command of lem:compute-stp and its link to `ballFrom`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax808846Proofs.Reasoning.Lib.Csr Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.TreeAlgo

/-- Copy the first `n` entries of `src` into `dst`. -/
def copyArr (src dst : String) : Com := rowFill dst (.var "b") (.get src (.var "b"))

/-- One layer of the search. -/
def layer : Com := .seq (copyArr "dm" "dn") (.seq scanAll (copyArr "dn" "dm"))

/-- Mark the ball of radius `br` around `bu` in `dm`. -/
def ballCmd : Com :=
  .seq (rowFill "dm" (.var "b") (.lit 0)) (.seq (.store "dm" (.var "bu") (.lit 1))
    (forUp "bs" (.var "br") layer))

/-- The cost bound of `ballCmd`. -/
def ballCost (n m r : ℕ) : ℕ := (r + 1) * (100 * n + 14 * m + 50)

theorem arrOf_of_fill {n : ℕ} {f : ℕ → ℕ} {l l' : List ℕ} (hl : l.length = n)
    (hl' : l'.length = l.length)
    (hg : ∀ j, l'[j]? = if 0 ≤ j ∧ j < 0 + n then some (f (j - 0)) else l[j]?) :
    l' = arrOf n f := by
  refine List.ext_getElem? fun j => ?_
  rw [hg j]
  by_cases hj : j < n
  · simp [hj, getElem?_arrOf f hj]
  · simp only [Nat.zero_le, true_and, Nat.zero_add, hj, if_false]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- Copying an array. -/
theorem copyArr_run {B n nsE nsN : ℕ} {oE tE oN tN f : ℕ → ℕ} {src dst : String} {σ : Env}
    (hG : GraphAt n nsE nsN oE tE oN tN σ) (hnB : n + 2 < B) (hsrc : σ.arrs src = arrOf n f)
    (hf : ∀ v < n, f v ≤ 1) (hdst : (σ.arrs dst).length = n) (hsd : src ≠ dst)
    (h1 : dst ≠ "eo") (h2 : dst ≠ "et") (h3 : dst ≠ "no") (h4 : dst ≠ "nt") :
    ∃ σ', Run B (copyArr src dst) σ σ' (12 * n + 6) ∧ σ'.arrs dst = arrOf n f ∧
      GraphAt n nsE nsN oE tE oN tN σ' ∧ σ'.arrs src = arrOf n f := by
  obtain ⟨σ', hr, ⟨hG', hs'⟩, hl, hg⟩ := rowFill_run (B := B) (n := n) (base := 0) (K := 4)
    (arr := dst) (ie := .var "b") (e := .get src (.var "b"))
    (fun τ => GraphAt n nsE nsN oE tE oN tN τ ∧ τ.arrs src = arrOf n f) f (by omega)
    (fun τ h => h.1.2.2) (fun τ x h => ⟨h.1.setVar (by decide) _, by simp [h.2]⟩)
    (fun τ i x h => ⟨h.1.setArr h1 h2 h3 h4 _ _, by simp only [arrs_setArr, if_neg hsd]; exact h.2⟩)
    (fun τ k h hb hk => by simp only [evalB_var_iff]; exact ⟨by simp [hb], by omega⟩)
    (fun τ k h hb hk => by
      simp only [evalB_get_iff, evalB_var_iff]
      exact ⟨k, ⟨hb.symm, by omega⟩, by rw [h.2, getElem?_arrOf f hk], by have := hf k hk; omega⟩)
    (by simp) ⟨hG, hsrc⟩ (by omega)
  exact ⟨σ', hr.mono (by omega), arrOf_of_fill hdst hl hg, hG', hs'⟩

/-- **A layer.** -/
theorem layer_run {B n nsE nsN : ℕ} {oE tE oN tN f : ℕ → ℕ} {P : ℕ → Prop} {σ : Env}
    (hG : GraphAt n nsE nsN oE tE oN tN σ) (hnB : n + 2 < B) (hEB : nsE + 1 < B)
    (hNB : nsN + 1 < B) (hdm : σ.arrs "dm" = arrOf n f) (hf : IndOn n f P)
    (hdn : (σ.arrs "dn").length = n) :
    ∃ σ' f', Run B layer σ σ' (80 * n + 14 * (nsE + nsN) + 20) ∧ σ'.arrs "dm" = arrOf n f' ∧
      IndOn n f' (fun v => P v ∨ ∃ w < n, P w ∧ Adj2 oE tE oN tN w v) ∧
      GraphAt n nsE nsN oE tE oN tN σ' ∧ (σ'.arrs "dn").length = n := by
  obtain ⟨σ1, hr1, hdn1, hG1, hdm1⟩ := copyArr_run (B := B) hG hnB hdm (fun v hv => (hf v hv).2) hdn
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ2, g, hr2, hdg, hg⟩ := scanAll_run hG1 hnB hEB hNB hdm1 hf hdn1 hf
  have hG2 : GraphAt n nsE nsN oE tE oN tN σ2 := hG1.of_arrs (hr2.frame_var "n" (by decide))
    (hr2.frame_arr _ (by decide)) (hr2.frame_arr _ (by decide)) (hr2.frame_arr _ (by decide))
    (hr2.frame_arr _ (by decide))
  have hdm2 : (σ2.arrs "dm").length = n := by rw [hr2.frame_arr "dm" (by decide), hdm1]; simp
  obtain ⟨σ3, hr3, hdm3, hG3, hdn3⟩ := copyArr_run (B := B) hG2 hnB hdg (fun v hv => (hg v hv).2)
    hdm2 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ3, g, (Run.seq hr1 (Run.seq hr2 hr3)).mono (by omega), hdm3, hg, hG3,
    by rw [hdn3]; simp⟩

/-- **The ball command.** -/
theorem ballCmd_run {B n nsE nsN u r : ℕ} {oE tE oN tN : ℕ → ℕ} {σ : Env}
    (hG : GraphAt n nsE nsN oE tE oN tN σ) (hnB : n + 2 < B) (hEB : nsE + 1 < B)
    (hNB : nsN + 1 < B) (hrB : r < B) (hu : σ.vars "bu" = u) (hun : u < n)
    (hr : σ.vars "br" = r) (hdm : (σ.arrs "dm").length = n) (hdn : (σ.arrs "dn").length = n) :
    ∃ σ' f, Run B ballCmd σ σ' (ballCost n (nsE + nsN) r) ∧ σ'.arrs "dm" = arrOf n f ∧
      IndOn n f (ballP n (Adj2 oE tE oN tN) u r) ∧ GraphAt n nsE nsN oE tE oN tN σ' ∧
      (σ'.arrs "dn").length = n := by
  -- clearing
  obtain ⟨σ1, hr1, ⟨hG1, hu1, hr1', hdn1⟩, hl1, hg1⟩ := rowFill_run (B := B) (n := n) (base := 0)
    (K := 3) (arr := "dm") (ie := .var "b") (e := .lit 0)
    (fun τ => GraphAt n nsE nsN oE tE oN tN τ ∧ τ.vars "bu" = u ∧ τ.vars "br" = r ∧
      (τ.arrs "dn").length = n) (fun _ => 0) (by omega)
    (fun τ h => h.1.2.2) (fun τ x h => ⟨h.1.setVar (by decide) _, by simp [h.2.1],
      by simp [h.2.2.1], by simp [h.2.2.2]⟩)
    (fun τ i x h => ⟨h.1.setArr (by decide) (by decide) (by decide) (by decide) _ _, by simp [h.2.1],
      by simp [h.2.2.1], by simp [h.2.2.2]⟩)
    (fun τ k h hb hk => by simp only [evalB_var_iff]; exact ⟨by simp [hb], by omega⟩)
    (fun τ k h hb hk => by simp; omega) (by simp) ⟨hG, hu, hr, hdn⟩ (by omega)
  have hdm1 := arrOf_of_fill (f := fun _ => 0) hdm hl1 hg1
  -- marking the center
  set σ2 := σ1.setArr "dm" u 1 with hσ2
  have hr2 : Run B (.store "dm" (.var "bu") (.lit 1)) σ1 σ2 3 :=
    (Run.store (by simp [hu1]; omega) (by simp; omega) (by rw [hdm1]; simp; omega)).mono (by simp)
  have hdm2 : σ2.arrs "dm" = arrOf n (fun v => if v = u then 1 else 0) := by
    simp [hσ2, hdm1, set_arrOf]
  -- the layers
  let I : ℕ → Env → Prop := fun s τ => GraphAt n nsE nsN oE tE oN tN τ ∧ τ.vars "br" = r ∧
    (τ.arrs "dn").length = n ∧ ∃ f, τ.arrs "dm" = arrOf n f ∧ IndOn n f (ballP n (Adj2 oE tE oN tN) u s)
  obtain ⟨σ3, hr3, ⟨hG3, -, hdn3, f, hdm3, hf⟩, -⟩ := forUp_run (B := B) (i := "bs") (e := .var "br")
    (body := layer) (N := r) (K := 80 * n + 14 * (nsE + nsN) + 20) I (σ := σ2) hrB
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by rw [hI.2.1]; exact hrB⟩)
    ⟨(hG1.setArr (by decide) (by decide) (by decide) (by decide) _ _).setVar (by decide) _,
      by simp [hσ2, hr1'], by simp [hσ2, hdn1], fun v => if v = u then 1 else 0,
      by rw [arrs_setVar]; exact hdm2,
      fun v hv => by simp only [ballP]; by_cases h : v = u <;> simp [h]⟩
    (by
      rintro k hk τ ⟨hGτ, hrτ, hdnτ, f, hdmτ, hfτ⟩ hbs
      obtain ⟨τ', f', hr', hdm', hf', hG', hdn'⟩ := layer_run hGτ hnB hEB hNB hdmτ hfτ hdnτ
      refine ⟨τ', hr', by rw [hr'.frame_var "bs" (by decide), hbs],
        hG'.setVar (by decide) _, by simp [hr'.frame_var "br" (by decide), hrτ], by simp [hdn'],
        f', by simp [hdm'], ?_⟩
      exact hf')
  refine ⟨σ3, f, (Run.seq hr1 (Run.seq hr2 hr3)).mono ?_, hdm3, hf, hG3, hdn3⟩
  simp only [ballCost, Expr.size]
  nlinarith

/-! ### The link to `ballFrom` -/

theorem ballP_iff {n : ℕ} {adj : Fin n → List (Fin n)} {A : ℕ → ℕ → Prop}
    (hA : ∀ w v : Fin n, v ∈ adj w ↔ A w v) (hAn : ∀ w v, w < n → A w v → v < n) (u : Fin n) :
    ∀ (s : ℕ) (v : Fin n), v ∈ ballFrom adj u s ↔ ballP n A u s v
  | 0, v => by simp [ballFrom, ballP, Fin.ext_iff]
  | s + 1, v => by
    simp only [ballFrom, ballP, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      ballP_iff hA hAn u s, hA]
    constructor
    · rintro (h | ⟨w, hw, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, w.isLt, hw, h⟩
    · rintro (h | ⟨w, hw, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨w, hw⟩, h1, h2⟩

end Lax185574Proofs.StpRam
