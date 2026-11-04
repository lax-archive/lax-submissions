import Lax185574Proofs.FarRam.Radius
import Lax185574Proofs.Words.TreeBfs


/-!
The pass over the extensions of the far-tree program.

For every extension `e` of the root and every position `j`, `extPhase`
stores in `mt[e · ℓ + j]` whether the atom `dist(xⱼ, x_ℓ) ≤ r` is in the
root of the child, and in `far[e]` whether none of them is.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- **The test loop with an indexed invariant.** -/
theorem anyLoopI_run {B : ℕ} {i n flag v : String} {body : Com} (C : ℕ → Env → Prop) (f : ℕ → Bool)
    (N Kb : ℕ) (hNB : N + 1 < B) (h1 : i ≠ flag) (h2 : n ≠ flag) (h3 : n ≠ i)
    (hCi : ∀ k τ x, C k τ → C k (τ.setVar i x)) (hCf : ∀ k τ x, C k τ → C k (τ.setVar flag x))
    (hbody : ∀ c < N, Spec B (fun τ => C c τ ∧ τ.vars i = c ∧ τ.vars n = N ∧ τ.vars flag ≤ 1) body
      (fun τ τ' => C (c + 1) τ' ∧ τ'.vars i = c ∧ τ'.vars n = N ∧ τ'.vars flag = τ.vars flag ∧
        τ'.vars v = bv (f c)) Kb)
    (σ : Env) (hσ : C 0 σ ∧ σ.vars n = N ∧ σ.vars flag = 0) :
    ∃ σ', Run B (anyLoop i n flag v body) σ σ' (N * (Kb + 20) + 6) ∧ C N σ' ∧
      σ'.vars flag = bv ((List.range N).any f) ∧ σ'.vars n = N := by
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := i) (e := .var n)
    (body := .seq body (.ite (.eq (.var v) (.lit 1)) (.assign flag (.lit 1)) .skip)) (N := N)
    (K := Kb + 10)
    (fun k τ => C k τ ∧ τ.vars n = N ∧ τ.vars flag = bv ((List.range k).any f)) (σ := σ) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by omega⟩)
    ⟨hCi _ _ _ hσ.1, by simp [vars_setVar, if_neg h3, hσ.2.1], by
      simp [vars_setVar, if_neg (Ne.symm h1), hσ.2.2]⟩
    (fun k hk τ hI hik => by
      obtain ⟨hC, hn, hfl⟩ := hI
      obtain ⟨τ1, hr1, hC1, hi1, hn1, hfl1, hv1⟩ := hbody k hk τ ⟨hC, hik, hn, by rw [hfl]; exact bv_le _⟩
      have hvB : τ1.vars v < B := by rw [hv1]; have := bv_le (f k); omega
      by_cases hf : f k = true
      · have hv : τ1.vars v = 1 := by rw [hv1, hf]; rfl
        refine ⟨τ1.setVar flag 1, (Run.seq hr1 (Run.ite_true ?_ (Run.assign ?_))).mono ?_, ?_,
          hCi _ _ _ (hCf _ _ _ hC1), ?_, ?_⟩
        · rw [eq_true_iff' hvB (by omega), hv]; rfl
        · exact evalB_lit (by omega)
        · simp
        · simp [vars_setVar, if_neg h1, hi1]
        · simp [vars_setVar, if_neg h2, if_neg h3, hn1]
        · simp [vars_setVar, if_neg (Ne.symm h1), any_range_succ, hf]
      · have hv : τ1.vars v = 0 := by rw [hv1]; simp at hf; simp [hf]
        refine ⟨τ1, (Run.seq hr1 (Run.ite_false ?_ Run.skip)).mono ?_, hi1, hCi _ _ _ hC1, ?_, ?_⟩
        · rw [eq_true_iff' hvB (by omega), hv]; rfl
        · simp
        · simp [vars_setVar, if_neg h3, hn1]
        · simp only [vars_setVar, if_neg (Ne.symm h1), hfl1, hfl, any_range_succ]
          simp at hf; simp [hf])
  exact ⟨σ', hr.mono (by simp; nlinarith), hI.1, hI.2.2, hI.2.1⟩

/-! ### The program -/

def extInner : Com := anyLoop "zj" "hl" "zf" "v"
  (.seq (.assign "hi" (.var "zj")) (.seq hitC
    (.store "mt" (.add (.mul (.var "zt") (.var "hl")) (.var "zj")) (.var "v"))))

def extBody : Com :=
  .seq (.assign "hy" (.add (.var "ef") (.lit 2))) (.seq (.assign "hs" (.var "r0"))
    (.seq (.assign "hj" (.var "hl")) (.seq (.assign "zf" (.lit 0)) (.seq extInner
      (.seq (.store "far" (.var "zt") (.sub (.lit 1) (.var "zf")))
        (.assign "ef" (.add (.add (.var "ef") (.get "x" (.var "ef"))) (.lit 1))))))))

def extPhase : Com :=
  .seq (.assign "y" (.lit 0)) (.seq skipList (.seq (.assign "nR" (.get "x" (.var "y")))
    (.seq (.assign "ef" (.add (.var "y") (.lit 1))) (forUp "zt" (.var "nR") extBody))))

/-- The met bits of the rows below `t`, and the far bits. -/
def Rows (X : List ℕ) (r ℓ t : ℕ) (τ : Env) : Prop :=
  (∀ e < t, ∀ j < ℓ, (τ.arrs "mt")[e * ℓ + j]? = some (bv (mtW X r ℓ e j))) ∧
    ∀ e < t, (τ.arrs "far")[e]? = some (bv (farW X r ℓ e))

/-- The fixed facts of the pass. -/
def ExtFix (X : List ℕ) (ℓ r R : ℕ) (τ : Env) : Prop :=
  RootAt X ℓ τ ∧ τ.vars "r0" = r ∧ τ.vars "nR" = R ∧ R * ℓ ≤ (τ.arrs "mt").length ∧
    R ≤ (τ.arrs "far").length

theorem stable_extFix {c : Com} (X : List ℕ) (ℓ r R : ℕ) (hx : "x" ∉ c.warrs) (hl : "hl" ∉ c.wvars)
    (hr : "r0" ∉ c.wvars) (hn : "nR" ∉ c.wvars) : Stable (ExtFix X ℓ r R) c :=
  (stable_rootAt X ℓ hx hl).and ((stable_var "r0" r hr).and ((stable_var "nR" R hn).and
    ((stable_len "mt" (R * ℓ)).and (stable_len "far" R))))

theorem stable_rows {c : Com} (X : List ℕ) (r ℓ t : ℕ) (hm : "mt" ∉ c.warrs) (hf : "far" ∉ c.warrs) :
    Stable (Rows X r ℓ t) c := fun τ τ' _ h2 _ _ _ h => by rw [Rows, h2 "mt" hm, h2 "far" hf]; exact h

/-- The met bits of row `t` below `c`. -/
def Part (X : List ℕ) (r ℓ t c : ℕ) (τ : Env) : Prop :=
  ∀ j < c, (τ.arrs "mt")[t * ℓ + j]? = some (bv (mtW X r ℓ t j))

theorem stable_part {c : Com} (X : List ℕ) (r ℓ t k : ℕ) (hm : "mt" ∉ c.warrs) :
    Stable (Part X r ℓ t k) c := fun τ τ' _ h2 _ _ _ h => by rw [Part, h2 "mt" hm]; exact h

theorem rows_set_mt {X : List ℕ} {r ℓ t c : ℕ} {M : List ℕ} (hc : c < ℓ)
    (hM : t * ℓ + c < M.length)
    (h : (∀ e < t, ∀ j < ℓ, M[e * ℓ + j]? = some (bv (mtW X r ℓ e j)))) (v : ℕ) :
    ∀ e < t, ∀ j < ℓ, (M.set (t * ℓ + c) v)[e * ℓ + j]? = some (bv (mtW X r ℓ e j)) := by
  intro e he j hj
  rw [List.getElem?_set_ne]
  · exact h e he j hj
  · intro heq
    have := (rowMajor_inj hc hj heq).1
    omega

theorem part_set_mt {X : List ℕ} {r ℓ t c : ℕ} {M : List ℕ} (hc : c < ℓ) (hM : t * ℓ + c < M.length)
    (h : ∀ j < c, M[t * ℓ + j]? = some (bv (mtW X r ℓ t j))) :
    ∀ j < c + 1, (M.set (t * ℓ + c) (bv (mtW X r ℓ t c)))[t * ℓ + j]? = some (bv (mtW X r ℓ t j)) := by
  intro j hj
  rcases Nat.lt_or_ge j c with h' | h'
  · rw [List.getElem?_set_ne (by omega)]; exact h j h'
  · obtain rfl : j = c := by omega
    rw [List.getElem?_set_self hM]

def extInnerCost (X : List ℕ) (ℓ : ℕ) : ℕ := ℓ * (70 * X.length + 140) + 6

theorem extInner_spec (B : ℕ) (X : List ℕ) (ℓ r R t y : ℕ) (C : Env → Prop) (hC : Stable C extInner)
    (hy : y = frPos X (listEnd X 0) t + 2) (hL : ListFacts X y) (ht : t < R)
    (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hrB : r < B) (hRB : R * ℓ + ℓ + 1 < B) :
    Spec B (fun τ => C τ ∧ ExtFix X ℓ r R τ ∧ Rows X r ℓ t τ ∧ τ.vars "zt" = t ∧ τ.vars "hy" = y ∧
        τ.vars "hs" = r ∧ τ.vars "hj" = ℓ ∧ τ.vars "zf" = 0) extInner
      (fun _ τ' => C τ' ∧ ExtFix X ℓ r R τ' ∧ Rows X r ℓ t τ' ∧ τ'.vars "zt" = t ∧ τ'.vars "hy" = y ∧
        τ'.vars "hs" = r ∧ τ'.vars "hj" = ℓ ∧ Part X r ℓ t ℓ τ' ∧
        τ'.vars "zf" = bv ((List.range ℓ).any (mtW X r ℓ t))) (extInnerCost X ℓ) := by
  rintro σ ⟨hCσ, hF, hRw, hzt, hhy, hhs, hhj, hzf⟩
  let F : Env → Prop := fun ρ => C ρ ∧ ExtFix X ℓ r R ρ ∧ ρ.vars "zt" = t ∧ ρ.vars "hy" = y ∧
    ρ.vars "hs" = r ∧ ρ.vars "hj" = ℓ
  have hSF : Stable F extInner := hC.and ((stable_extFix X ℓ r R (by decide) (by decide) (by decide)
    (by decide)).and ((stable_var "zt" t (by decide)).and ((stable_var "hy" y (by decide)).and
      ((stable_var "hs" r (by decide)).and (stable_var "hj" ℓ (by decide))))))
  let Cin : ℕ → Env → Prop := fun c ρ => F ρ ∧ Rows X r ℓ t ρ ∧ Part X r ℓ t c ρ
  have hset : ∀ z, z ∈ extInner.wvars → ∀ c ρ x, Cin c ρ → Cin c (ρ.setVar z x) :=
    fun z hz c ρ x h => ⟨hSF.setVar hz ρ x h.1, by simpa [Rows] using h.2.1, by simpa [Part] using h.2.2⟩
  have hRl : R * ℓ ≤ (σ.arrs "mt").length := hF.2.2.2.1
  obtain ⟨σ', hr, ⟨hF', hRw', hP'⟩, hzf', -⟩ := anyLoopI_run (B := B) (i := "zj") (n := "hl")
    (flag := "zf") (v := "v")
    (body := .seq (.assign "hi" (.var "zj")) (.seq hitC
      (.store "mt" (.add (.mul (.var "zt") (.var "hl")) (.var "zj")) (.var "v"))))
    Cin (mtW X r ℓ t) ℓ (70 * X.length + 120) (by omega) (by decide) (by decide) (by decide)
    (hset "zj" (by decide)) (hset "zf" (by decide))
    (fun c hc ρ ⟨⟨hFρ, hRρ, hPρ⟩, hzj, hhl, hzfl⟩ => by
      set ρ1 := ρ.setVar "hi" c
      have hS1 : Stable (fun ρ' => F ρ' ∧ Rows X r ℓ t ρ' ∧ Part X r ℓ t c ρ' ∧ ρ'.vars "zj" = c ∧
          ρ'.vars "zf" = ρ.vars "zf") hitC :=
        (hSF.mono (by decide) (by decide)).and ((stable_rows X r ℓ t (by decide) (by decide)).and
          ((stable_part X r ℓ t c (by decide)).and ((stable_var "zj" c (by decide)).and
              (stable_var "zf" _ (by decide)))))
      obtain ⟨ρ2, hr2, ⟨hF2, hR2, hP2, hzj2, hzf2⟩, hv2⟩ := hitC_spec B X y r c ℓ _ hS1 hL hX hXB hrB
        (by omega) (by omega) ρ1
        ⟨⟨hSF.setVar (by decide) _ _ hFρ, by simpa [ρ1, Rows] using hRρ, by simpa [ρ1, Part] using hPρ,
          by simp [ρ1, hzj], by simp [ρ1]⟩, by simpa [ρ1] using hFρ.2.1.1.1,
          by simpa [ρ1] using hFρ.2.1.1.2.1, by simp [ρ1, hFρ.2.2.2.1], by simp [ρ1, hFρ.2.2.2.2.1],
          by simp [ρ1], by simp [ρ1, hFρ.2.2.2.2.2]⟩
      have hml : t * ℓ + c < (ρ2.arrs "mt").length := by
        have := rowMajor_lt (n := ℓ) ht hc
        have := hF2.2.1.2.2.2.1
        omega
      have hidx : (Expr.add (.mul (.var "zt") (.var "hl")) (.var "zj")).evalB B ρ2 = some (t * ℓ + c) := by
        simp only [evalB_bin_iff, evalB_var_iff]
        have hz : ρ2.vars "zt" = t := hF2.2.2.1
        have hl2 : ρ2.vars "hl" = ℓ := hF2.2.1.1.2.2
        have hrm := rowMajor_lt (n := ℓ) ht hc
        have htl : t * ℓ ≤ R * ℓ := Nat.mul_le_mul_right _ ht.le
        have htB : t < B := by
          rcases Nat.eq_zero_or_pos ℓ with h0 | h0
          · subst h0; omega
          · have : t ≤ t * ℓ := Nat.le_mul_of_pos_right _ h0
            omega
        exact ⟨t * ℓ, c, ⟨t, ℓ, ⟨hz.symm, by omega⟩, ⟨hl2.symm, by omega⟩, rfl, by omega⟩,
          ⟨hzj2.symm, by omega⟩, rfl, by omega⟩
      have hv2' : ρ2.vars "v" = bv (mtW X r ℓ t c) := by rw [hv2, hy]; rfl
      have rS : Run B (.store "mt" (.add (.mul (.var "zt") (.var "hl")) (.var "zj")) (.var "v")) ρ2
          (ρ2.setArr "mt" (t * ℓ + c) (bv (mtW X r ℓ t c))) 8 :=
        (Run.store hidx (by simp only [evalB_var_iff]; exact ⟨hv2'.symm, by rw [hv2']; have := bv_le (mtW X r ℓ t c); omega⟩) hml).mono (by simp)
      refine ⟨_, (Run.seq (Run.assign (v := c) ?_) (Run.seq hr2 rS)).mono ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simp only [evalB_var_iff]; exact ⟨hzj.symm, by omega⟩
      · simp only [Expr.size]; omega
      · exact (hSF.mono (c := .store "mt" (.add (.mul (.var "zt") (.var "hl")) (.var "zj")) (.var "v"))
          (by decide) (by decide)).run rS (by decide) (by decide) hF2
      · refine ⟨rows_set_mt hc hml hR2.1 _, fun e he => ?_⟩
        simpa [Env.setArr] using hR2.2 e he
      · intro j hj
        simpa [Env.setArr] using part_set_mt hc hml hP2 j hj
      · simpa [Env.setArr] using hzj2
      · simpa [Env.setArr] using hF2.2.1.1.2.2
      · simpa [Env.setArr] using hzf2
      · simpa [Env.setArr] using hv2')
    σ ⟨⟨⟨hCσ, hF, hzt, hhy, hhs, hhj⟩, hRw, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, hF.1.2.2, hzf⟩
  exact ⟨σ', hr.mono (by simp only [extInnerCost]; nlinarith), hF'.1, hF'.2.1, hRw', hF'.2.2.1, hF'.2.2.2.1,
    hF'.2.2.2.2.1, hF'.2.2.2.2.2, hP', hzf'⟩

def extBodyCost (X : List ℕ) (ℓ : ℕ) : ℕ := extInnerCost X ℓ + 40

theorem extBody_spec (B : ℕ) (X : List ℕ) (ℓ r R t : ℕ) (C : Env → Prop) (hC : Stable C extBody)
    (hLy : ListFacts X (frPos X (listEnd X 0) t + 2))
    (hfr : frPos X (listEnd X 0) t + 1 + xg X (frPos X (listEnd X 0) t) ≤ X.length) (ht : t < R)
    (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hrB : r < B) (hRB : R * ℓ + ℓ + 1 < B)
    (hRB' : R < B) :
    Spec B (fun τ => C τ ∧ ExtFix X ℓ r R τ ∧ Rows X r ℓ t τ ∧ τ.vars "zt" = t ∧
        τ.vars "ef" = frPos X (listEnd X 0) t) extBody
      (fun _ τ' => C τ' ∧ ExtFix X ℓ r R τ' ∧ Rows X r ℓ (t + 1) τ' ∧ τ'.vars "zt" = t ∧
        τ'.vars "ef" = frPos X (listEnd X 0) (t + 1)) (extBodyCost X ℓ) := by
  rintro σ ⟨hCσ, hF, hRw, hzt, hef⟩
  set fp := frPos X (listEnd X 0) t with hfp
  have hfpX : fp + 2 < X.length := by
    have := hLy.frPos_le 0 (Nat.zero_le _); have := hLy.end_le; omega
  set σ1 := (((σ.setVar "hy" (fp + 2)).setVar "hs" r).setVar "hj" ℓ).setVar "zf" 0
  have hr0 : σ.vars "r0" = r := hF.2.1
  have hhl : σ.vars "hl" = ℓ := hF.1.2.2
  have r1 : Run B (.assign "hy" (.add (.var "ef") (.lit 2))) σ (σ.setVar "hy" (fp + 2)) 4 :=
    (Run.assign (by simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]; exact ⟨fp, 2, ⟨hef.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩)).mono (by simp)
  have r2 : Run B (.assign "hs" (.var "r0")) (σ.setVar "hy" (fp + 2)) ((σ.setVar "hy" (fp + 2)).setVar "hs" r) 2 :=
    (Run.assign (by simp only [evalB_var_iff]; simp [hr0]; omega)).mono (by simp)
  have r3 : Run B (.assign "hj" (.var "hl")) ((σ.setVar "hy" (fp + 2)).setVar "hs" r)
      (((σ.setVar "hy" (fp + 2)).setVar "hs" r).setVar "hj" ℓ) 2 :=
    (Run.assign (by simp only [evalB_var_iff]; simp [hhl]; omega)).mono (by simp)
  have r4 : Run B (.assign "zf" (.lit 0)) (((σ.setVar "hy" (fp + 2)).setVar "hs" r).setVar "hj" ℓ) σ1 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hS : Stable (fun ρ => C ρ ∧ ρ.vars "ef" = fp) extInner :=
    (hC.mono (by decide) (by decide)).and (stable_var "ef" fp (by decide))
  have hset : ∀ z, z ∈ extBody.wvars → ∀ ρ x, ExtFix X ℓ r R ρ → z ≠ "hl" → z ≠ "r0" → z ≠ "nR" →
      ExtFix X ℓ r R (ρ.setVar z x) := fun z _ ρ x h h1 h2 h3 =>
    ⟨⟨by simpa using h.1.1, by simpa using h.1.2.1, by simp [Ne.symm h1, h.1.2.2]⟩,
      by simp [Ne.symm h2, h.2.1], by simp [Ne.symm h3, h.2.2.1], by simpa using h.2.2.2.1,
      by simpa using h.2.2.2.2⟩
  obtain ⟨σ2, hr2, ⟨hC2, hef2⟩, hF2, hRw2, hzt2, -, -, -, hP2, hzf2⟩ :=
    extInner_spec B X ℓ r R t (fp + 2) _ hS rfl hLy ht hX hXB hrB hRB σ1
    ⟨⟨hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _
      (hC.setVar (by decide) _ _ hCσ))), by simp [σ1, hef]⟩,
      hset "zf" (by decide) _ _ (hset "hj" (by decide) _ _ (hset "hs" (by decide) _ _
        (hset "hy" (by decide) _ _ hF (by decide) (by decide) (by decide)) (by decide) (by decide)
        (by decide)) (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide),
      by simpa [σ1, Rows] using hRw, by simp [σ1, hzt], by simp [σ1], by simp [σ1], by simp [σ1],
      by simp [σ1]⟩
  have hzfl : σ2.vars "zf" ≤ 1 := by rw [hzf2]; exact bv_le _
  have hfl : t < (σ2.arrs "far").length := by have := hF2.2.2.2.2; omega
  have hfar : 1 - σ2.vars "zf" = bv (farW X r ℓ t) := by rw [hzf2, farW, bv_not]
  set σ3 := σ2.setArr "far" t (bv (farW X r ℓ t))
  have r5 : Run B (.store "far" (.var "zt") (.sub (.lit 1) (.var "zf"))) σ2 σ3 6 := by
    refine (Run.store (idx := t) (by simp only [evalB_var_iff]; exact ⟨hzt2.symm, by omega⟩) ?_ hfl).mono
      (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨1, σ2.vars "zf", ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply, hfar],
      by have := bv_le (farW X r ℓ t); omega⟩
  have hx3 : σ3.arrs "x" = X := by simp [σ3, Env.setArr, hF2.1.1]
  have hef3 : σ3.vars "ef" = fp := by simp [σ3, hef2]
  have hnext : frPos X (listEnd X 0) (t + 1) = fp + xg X fp + 1 := by
    rw [hfp, frPos, frPos, skipFr_succ']; omega
  have r6 : Run B (.assign "ef" (.add (.add (.var "ef") (.get "x" (.var "ef"))) (.lit 1))) σ3
      (σ3.setVar "ef" (fp + xg X fp + 1)) 8 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, evalB_get_iff]
    have hfpl : fp < X.length := by omega
    refine ⟨fp + xg X fp, 1, ⟨fp, xg X fp, ⟨hef3.symm, by omega⟩, ⟨fp, ⟨hef3.symm, by omega⟩, ?_,
      xg_lt hX (by omega)⟩, rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
    rw [hx3, List.getElem?_eq_getElem hfpl, xg_of_lt hfpl]
  refine ⟨σ3.setVar "ef" (fp + xg X fp + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold extBody
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq hr2 (Run.seq r5 r6)))))).mono ?_
    simp only [extBodyCost]; omega
  · exact hC.setVar (by decide) _ _ ((hC.mono (c := .store "far" (.var "zt") (.sub (.lit 1) (.var "zf")))
      (by decide) (by decide)).run r5 (by decide) (by decide) hC2)
  · exact hset "ef" (by decide) _ _ ⟨⟨hx3, by simpa [σ3, Env.setArr] using hF2.1.2.1,
      by simpa [σ3] using hF2.1.2.2⟩, by simpa [σ3] using hF2.2.1, by simpa [σ3] using hF2.2.2.1,
      by simpa [σ3, Env.setArr] using hF2.2.2.2.1, by simpa [σ3, Env.setArr] using hF2.2.2.2.2⟩
      (by decide) (by decide) (by decide)
  · refine ⟨fun e he j hj => ?_, fun e he => ?_⟩
    · simp only [arrs_setVar, σ3, Env.setArr, if_neg (show ("mt" : String) ≠ "far" by decide)]
      rcases Nat.lt_or_ge e t with h | h
      · exact hRw2.1 e h j hj
      · obtain rfl : e = t := by omega
        exact hP2 j hj
    · simp only [arrs_setVar, σ3, Env.setArr, if_true]
      rcases Nat.lt_or_ge e t with h | h
      · rw [List.getElem?_set_ne (by omega)]; exact hRw2.2 e h
      · obtain rfl : e = t := by omega
        rw [List.getElem?_set_self hfl]
  · simp [σ3, hzt2]
  · simp [hnext]

theorem ext_child_facts {q ℓ : ℕ} {X : List ℕ} {t0 : Node (q + 1) ℓ} {rest : List ℕ}
    (hx : X.drop 0 = toWord t0 ++ rest) {t : ℕ} (ht : t < (Node.exts t0).words.length) :
    ListFacts X (frPos X (listEnd X 0) t + 2) ∧
      frPos X (listEnd X 0) t + 1 + xg X (frPos X (listEnd X 0) t) ≤ X.length := by
  obtain ⟨-, h2⟩ := nodeSplit hx
  obtain ⟨a, -, ha⟩ := getElem_words ht
  obtain ⟨-, r', hr'⟩ := extFrame h2 ht ha
  obtain ⟨r'', hr''⟩ := atoms_drop hr'
  refine ⟨listFacts_of hr'', ?_⟩
  have hLe := listFacts_of h2
  obtain ⟨h0, -, -⟩ := listAt h2
  have hs := skipFr_succ' X (listEnd X 0 + 1) t
  obtain ⟨-, h1⟩ := hLe.frPos_le (t + 1) (by omega)
  have := hLe.end_le
  unfold frPos at h1 ⊢
  omega

def extCost (X : List ℕ) (ℓ R : ℕ) : ℕ := 24 * X.length + 40 + R * (extBodyCost X ℓ + 10)

/-- **The pass over the extensions.** -/
theorem extPhase_spec (B : ℕ) (X : List ℕ) {q ℓ : ℕ} (t0 : Node (q + 1) ℓ) (rest : List ℕ)
    (hx : X.drop 0 = toWord t0 ++ rest) (r : ℕ) (C : Env → Prop) (hC : Stable C extPhase)
    (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hrB : r < B)
    (hRB : (Node.exts t0).words.length * ℓ + ℓ + 1 < B) (hRB' : (Node.exts t0).words.length + 1 < B) :
    Spec B (fun τ => C τ ∧ RootAt X ℓ τ ∧ τ.vars "r0" = r ∧
        (Node.exts t0).words.length * ℓ ≤ (τ.arrs "mt").length ∧
        (Node.exts t0).words.length ≤ (τ.arrs "far").length) extPhase
      (fun _ τ' => C τ' ∧ ExtFix X ℓ r (Node.exts t0).words.length τ' ∧
        Rows X r ℓ (Node.exts t0).words.length τ') (extCost X ℓ (Node.exts t0).words.length) := by
  rintro σ ⟨hCσ, hR, hr0, hml, hfl⟩
  set R := (Node.exts t0).words.length with hRdef
  set e := listEnd X 0 with he
  obtain ⟨-, h2⟩ := nodeSplit hx
  have hLe := listFacts_of h2
  have hL0 : ListFacts X 0 := by obtain ⟨r', hr'⟩ := atoms_drop hx; exact listFacts_of hr'
  have hR0 : xg X e = R := (listAt h2).1
  have heX : e < X.length := by have := hLe.frPos_le 0 (Nat.zero_le _); have := hLe.end_le; omega
  have hσ1 : (σ.setVar "y" 0).arrs "x" = X ∧ (σ.setVar "y" 0).vars "y" = 0 := ⟨by simp [hR.1], by simp⟩
  obtain ⟨σ2, hr2, hy2⟩ := (skipList_spec B X 0 hL0 (by omega) hX).frame _ hσ1
  obtain ⟨hy2, hfv2, hfa2, -, -⟩ := hy2
  have hx2 : σ2.arrs "x" = X := by rw [hfa2 "x" (by decide)]; simp [hR.1]
  set σ3 := (σ2.setVar "nR" R).setVar "ef" (e + 1)
  have rN : Run B (.assign "nR" (.get "x" (.var "y"))) σ2 (σ2.setVar "nR" R) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    refine ⟨e, ⟨hy2.symm, by omega⟩, ?_, by omega⟩
    rw [hx2, List.getElem?_eq_getElem heX, ← xg_of_lt heX, hR0]
  have rE : Run B (.assign "ef" (.add (.var "y") (.lit 1))) (σ2.setVar "nR" R) σ3 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, vars_setVar]
    exact ⟨e, 1, ⟨by simp [hy2, he], by simp [hy2, he]; omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  have hS2 : Stable C skipList := hC.mono (by decide) (by decide)
  have hC2 : C σ2 := hS2.run hr2 (by decide) (by decide) (hC.setVar (by decide) _ _ hCσ)
  have hF3 : ExtFix X ℓ r R σ3 := by
    refine ⟨⟨by simp [σ3, hx2], ?_, ?_⟩, ?_, by simp [σ3], ?_, ?_⟩
    · have := run_length_arrs hr2 "f"; simp [σ3, this, hR.2.1]
    · simp [σ3, hfv2 "hl" (by decide), hR.2.2]
    · simp [σ3, hfv2 "r0" (by decide), hr0]
    · have := run_length_arrs hr2 "mt"; simp [σ3, this]; omega
    · have := run_length_arrs hr2 "far"; simp [σ3, this]; omega
  obtain ⟨σ4, hr4, hI4, -⟩ := forUp_run (B := B) (i := "zt") (e := .var "nR") (body := extBody) (N := R)
    (K := extBodyCost X ℓ) (fun k τ => C τ ∧ ExtFix X ℓ r R τ ∧ Rows X r ℓ k τ ∧
      τ.vars "ef" = frPos X e k) (σ := σ3) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.2.2.1.symm, by rw [hI.2.1.2.2.1]; omega⟩)
    ⟨hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ hC2)),
      ⟨⟨by simpa using hF3.1.1, by simpa using hF3.1.2.1, by simpa using hF3.1.2.2⟩,
        by simpa using hF3.2.1, by simpa using hF3.2.2.1, by simpa using hF3.2.2.2.1,
        by simpa using hF3.2.2.2.2⟩,
      ⟨fun e he => absurd he (Nat.not_lt_zero _), fun e he => absurd he (Nat.not_lt_zero _)⟩,
      by simp [σ3, frPos, skipFr, he]⟩
    (fun k hk τ ⟨hCτ, hFτ, hRτ, hefτ⟩ hik => by
      obtain ⟨hLy, hfr⟩ := ext_child_facts hx hk
      obtain ⟨τ', hr', hC', hF', hR', hzt', hef'⟩ := extBody_spec B X ℓ r R k C (hC.mono (by decide) (by decide)) hLy hfr hk hX hXB
        hrB hRB (by omega) τ ⟨hCτ, hFτ, hRτ, hik, hefτ⟩
      exact ⟨τ', hr', hzt', hC.setVar (by decide) _ _ hC',
        ⟨⟨by simpa using hF'.1.1, by simpa using hF'.1.2.1, by simpa using hF'.1.2.2⟩,
          by simpa using hF'.2.1, by simpa using hF'.2.2.1, by simpa using hF'.2.2.2.1,
          by simpa using hF'.2.2.2.2⟩, by simpa [Rows] using hR', by simpa using hef'⟩)
  refine ⟨σ4, ?_, hI4.1, hI4.2.1, hI4.2.2.1⟩
  unfold extPhase
  refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq hr2 (Run.seq rN (Run.seq rE hr4)))).mono ?_
  simp only [extCost, Expr.size]
  nlinarith

end Lax185574Proofs.FarRam
