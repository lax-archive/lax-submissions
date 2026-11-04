import Lax185574Proofs.ResolveRam.Glue.Dist
import Lax185574Proofs.StpRam.BallCmd

/-!
The search from a color class in IMP+.

`cdist` marks the class of the color `bx` in `dm` (colors in `co`), clears
the table `ct` of the `nc` colors, and runs `n` rounds. Round `s` records
`s + 1` in `ct[cl[v]]` for every marked vertex `v` whose entry is still
`0` (`record`), and then runs one layer of the search of lem:compute-stp
(`StpRam.layer`). Here `cl[v]` is the index of the color of `v`. After
the rounds, entry `c` of `ct` is one more than the first layer that
reaches a vertex `v` with `cl[v] = c`, and `0` if no layer below `n`
does (`cdist_run`). With the indices of the sorted colors this is the
table `cTab` (`cdist_cTab`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax808846Proofs.Reasoning.Lib.Csr Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.StpRam Lax185574.PartialGraphs

/-- The body of the marking loop. -/
def markBody : Com :=
  .ite (.eq (.get "co" (.var "bz")) (.var "bx")) (.store "dm" (.var "bz") (.lit 1))
    (.store "dm" (.var "bz") (.lit 0))

/-- Mark the vertices of color `bx` in `dm`. -/
def markCls : Com := forUp "bz" (.var "n") markBody

/-- Clear the table. -/
def clrCt : Com := forUp "bz" (.var "nc") (.store "ct" (.var "bz") (.lit 0))

/-- The body of the recording loop. -/
def recBody : Com :=
  .ite (.eq (.get "dm" (.var "bz")) (.lit 1))
    (.ite (.eq (.get "ct" (.get "cl" (.var "bz"))) (.lit 0))
      (.store "ct" (.get "cl" (.var "bz")) (.add (.var "bs") (.lit 1))) .skip) .skip

/-- Record the colors reached in this layer. -/
def record : Com := forUp "bz" (.var "n") recBody

/-- **The search from the class of `bx`.** -/
def cdist : Com := .seq markCls (.seq clrCt (forUp "bs" (.var "n") (.seq record layer)))

/-- The table after the rounds below `s`, for the layers `M t` and the
color indices `cl`: entry `c` is `t + 1` for the first layer `t < s`
that reaches a vertex with index `c`, and `0` if there is none. -/
def TabOK (n nc s : ℕ) (cl : ℕ → ℕ) (M : ℕ → ℕ → Prop) (g : ℕ → ℕ) : Prop :=
  ∀ c < nc, (g c = 0 ↔ ∀ t < s, ¬ ∃ y < n, cl y = c ∧ M t y) ∧
    ∀ t, g c = t + 1 → t < s ∧ (∃ y < n, cl y = c ∧ M t y) ∧ ∀ t' < t, ¬ ∃ y < n, cl y = c ∧ M t' y

/-! ### The recording loop -/

open Classical in
/-- The table after `k` vertices of a recording pass. -/
noncomputable def recTab (g cl : ℕ → ℕ) (M : ℕ → Prop) (s k c : ℕ) : ℕ :=
  if g c ≠ 0 then g c else if ∃ y < k, cl y = c ∧ M y then s + 1 else 0

theorem recTab_zero (g cl : ℕ → ℕ) (M : ℕ → Prop) (s c : ℕ) : recTab g cl M s 0 c = g c := by
  unfold recTab; split_ifs with h1 h2 <;> simp_all

open Classical in
theorem recTab_succ (g cl : ℕ → ℕ) (M : ℕ → Prop) (s k c : ℕ) :
    recTab g cl M s (k + 1) c =
      if M k ∧ c = cl k ∧ recTab g cl M s k c = 0 then s + 1 else recTab g cl M s k c := by
  classical
  have hex : (∃ y < k + 1, cl y = c ∧ M y) ↔ (∃ y < k, cl y = c ∧ M y) ∨ (cl k = c ∧ M k) := by
    constructor
    · rintro ⟨y, hy, h1, h2⟩
      rcases Nat.lt_or_ge y k with h | h
      · exact Or.inl ⟨y, h, h1, h2⟩
      · obtain rfl : y = k := by omega
        exact Or.inr ⟨h1, h2⟩
    · rintro (⟨y, hy, h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨y, by omega, h1, h2⟩
      · exact ⟨k, by omega, h1, h2⟩
  unfold recTab
  by_cases hg : g c ≠ 0
  · simp [hg]
  · simp only [hg, if_false, hex]
    by_cases h1 : ∃ y < k, cl y = c ∧ M y
    · simp [h1]
    · by_cases h2 : cl k = c ∧ M k
      · simp [h1, h2]
      · simp only [h1, h2, or_self, if_false]
        split_ifs with h3
        · exact absurd ⟨h3.2.1.symm, h3.1⟩ h2
        · rfl

theorem recTab_lt {B : ℕ} {g cl : ℕ → ℕ} {M : ℕ → Prop} {s nc : ℕ} (hsB : s + 1 < B)
    (hgB : ∀ c < nc, g c < B) (k : ℕ) {c : ℕ} (hc : c < nc) : recTab g cl M s k c < B := by
  unfold recTab; split_ifs <;> first | exact hgB c hc | omega

/-- **One recording pass.** -/
theorem record_run {B n nc s : ℕ} {f g cl : ℕ → ℕ} {M : ℕ → Prop} {σ : Env} (C : Env → Prop)
    (hC : ∀ τ x, C τ → C (τ.setVar "bz" x)) (hCa : ∀ τ i x, C τ → C (τ.setArr "ct" i x))
    (hCdm : ∀ τ, C τ → τ.arrs "dm" = arrOf n f) (hCcl : ∀ τ, C τ → τ.arrs "cl" = arrOf n cl)
    (hCn : ∀ τ, C τ → τ.vars "n" = n) (hCs : ∀ τ, C τ → τ.vars "bs" = s)
    (hσ : C σ) (hct : σ.arrs "ct" = arrOf nc g) (hf : IndOn n f M) (hcl : ∀ v < n, cl v < nc)
    (hnB : n < B) (hncB : nc < B) (hsB : s + 1 < B) (hgB : ∀ c < nc, g c < B) :
    ∃ σ', Run B record σ σ' (n * 41 + 6) ∧ C σ' ∧
      σ'.arrs "ct" = arrOf nc (recTab g cl M s n) := by
  let I : ℕ → Env → Prop := fun k τ => C τ ∧ τ.arrs "ct" = arrOf nc (recTab g cl M s k)
  obtain ⟨σ', hr, ⟨hC', hct'⟩, -⟩ := forUp_run (B := B) (i := "bz") (e := .var "n") (body := recBody)
    (N := n) (K := 33) I hnB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hCn τ hI.1).symm, by rw [hCn τ hI.1]; exact hnB⟩)
    ⟨hC σ 0 hσ, by rw [arrs_setVar, hct]; congr 1; funext c; rw [recTab_zero]⟩
    (by
      rintro k hk τ ⟨hCτ, hctτ⟩ hbz
      have hclk : cl k < nc := hcl k hk
      have hdm := hCdm τ hCτ
      have hclτ := hCcl τ hCτ
      have hc1 : (Cond.eq (.get "dm" (.var "bz")) (.lit 1)).evalB B τ = some (f k == 1) := by
        rw [evalB_condEq_iff]
        refine ⟨f k, 1, ?_, by simp; omega, rfl⟩
        simp only [evalB_get_iff, evalB_var_iff]
        have := (hf k hk).2
        exact ⟨k, ⟨hbz.symm, by omega⟩, by rw [hdm, getElem?_arrOf _ hk], by omega⟩
      have hgetcl : (Expr.get "cl" (.var "bz")).evalB B τ = some (cl k) := by
        simp only [evalB_get_iff, evalB_var_iff]
        exact ⟨k, ⟨hbz.symm, by omega⟩, by rw [hclτ, getElem?_arrOf _ hk], by omega⟩
      have hc2 : (Cond.eq (.get "ct" (.get "cl" (.var "bz"))) (.lit 0)).evalB B τ =
          some (recTab g cl M s k (cl k) == 0) := by
        rw [evalB_condEq_iff]
        refine ⟨recTab g cl M s k (cl k), 0, ?_, by simp; omega, rfl⟩
        rw [evalB_get_iff]
        exact ⟨cl k, hgetcl, by rw [hctτ, getElem?_arrOf _ hclk], recTab_lt hsB hgB k hclk⟩
      by_cases hMk : M k
      · have hf1 : f k = 1 := (hf k hk).1.mpr hMk
        by_cases hz : recTab g cl M s k (cl k) = 0
        · refine ⟨τ.setArr "ct" (cl k) (s + 1), (Run.ite_true (by rw [hc1, hf1]; rfl)
            (Run.ite_true (by rw [hc2, hz]; rfl) (Run.store hgetcl ?_ ?_))).mono
            (by simp [Cond.size, Expr.size]), by simp [hbz], hC _ _ (hCa _ _ _ hCτ), ?_⟩
          · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
            exact ⟨s, 1, ⟨(hCs τ hCτ).symm, by rw [hCs τ hCτ]; omega⟩, ⟨rfl, by omega⟩, rfl, hsB⟩
          · rw [hctτ]; simp; omega
          · rw [arrs_setVar, arrs_setArr, if_pos rfl, hctτ, set_arrOf]
            congr 1; funext c
            rw [recTab_succ]
            by_cases hc : c = cl k
            · subst hc; simp [hMk, hz]
            · simp [hc]
        · refine ⟨τ, (Run.ite_true (by rw [hc1, hf1]; rfl)
            (Run.ite_false (by rw [hc2]; simp [hz]) Run.skip)).mono (by simp [Cond.size, Expr.size]),
            hbz, hC _ _ hCτ, ?_⟩
          rw [arrs_setVar, hctτ]
          congr 1; funext c
          rw [recTab_succ]
          by_cases hc : c = cl k
          · subst hc; simp [hz]
          · simp [hc]
      · have hf0 : f k ≠ 1 := fun h => hMk ((hf k hk).1.mp h)
        refine ⟨τ, (Run.ite_false (by rw [hc1]; simp [hf0]) Run.skip).mono
          (by simp [Cond.size, Expr.size]), hbz, hC _ _ hCτ, ?_⟩
        rw [arrs_setVar, hctτ]
        congr 1; funext c
        rw [recTab_succ]
        simp [hMk])
  exact ⟨σ', hr.mono (by simp [Expr.size]), hC', hct'⟩

/-! ### Marking and clearing -/

/-- **Marking the class.** -/
theorem markCls_run {B n X : ℕ} {col : ℕ → ℕ} {S : ℕ → Prop} {σ : Env} (C : Env → Prop)
    (hC : ∀ τ x, C τ → C (τ.setVar "bz" x)) (hCa : ∀ τ i x, C τ → C (τ.setArr "dm" i x))
    (hCco : ∀ τ, C τ → τ.arrs "co" = arrOf n col) (hCn : ∀ τ, C τ → τ.vars "n" = n)
    (hCx : ∀ τ, C τ → τ.vars "bx" = X) (hσ : C σ) (hdm : (σ.arrs "dm").length = n)
    (hS : ∀ v < n, S v ↔ col v = X) (hnB : n < B) (hXB : X < B) (hcolB : ∀ v < n, col v < B) :
    ∃ σ' f, Run B markCls σ σ' (n * 17 + 6) ∧ C σ' ∧ σ'.arrs "dm" = arrOf n f ∧ IndOn n f S := by
  open Classical in
  let fk : ℕ → ℕ → ℕ := fun k v => if v < k then (if col v = X then 1 else 0) else (σ.arrs "dm").getD v 0
  let I : ℕ → Env → Prop := fun k τ => C τ ∧ τ.arrs "dm" = arrOf n (fk k)
  have hdm0 : σ.arrs "dm" = arrOf n (fk 0) := by
    refine List.ext_getElem (by simp [hdm]) fun v h1 h2 => ?_
    simp [fk, arrOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  obtain ⟨σ', hr, ⟨hC', hdm'⟩, -⟩ := forUp_run (B := B) (i := "bz") (e := .var "n") (body := markBody)
    (N := n) (K := 9) I hnB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hCn τ hI.1).symm, by rw [hCn τ hI.1]; exact hnB⟩)
    ⟨hC σ 0 hσ, by rw [arrs_setVar]; exact hdm0⟩
    (by
      rintro k hk τ ⟨hCτ, hdmτ⟩ hbz
      have hco := hCco τ hCτ
      have hc : (Cond.eq (.get "co" (.var "bz")) (.var "bx")).evalB B τ = some (col k == X) := by
        rw [evalB_condEq_iff]
        refine ⟨col k, X, ?_, ?_, rfl⟩
        · simp only [evalB_get_iff, evalB_var_iff]
          exact ⟨k, ⟨hbz.symm, by omega⟩, by rw [hco, getElem?_arrOf _ hk], hcolB k hk⟩
        · simp only [evalB_var_iff]; exact ⟨(hCx τ hCτ).symm, by rw [hCx τ hCτ]; exact hXB⟩
      have hupd : ∀ b : ℕ, (b = if col k = X then 1 else 0) →
          (arrOf n (fk k)).set k b = arrOf n (fk (k + 1)) := by
        intro b hb
        rw [set_arrOf]; congr 1; funext v
        by_cases hv : v = k
        · subst hv; simp [fk, hb]
        · simp only [hv, if_false, fk]
          by_cases hvk : v < k
          · simp [hvk, show v < k + 1 by omega]
          · simp [hvk, show ¬ v < k + 1 by omega]
      by_cases hX : col k = X
      · refine ⟨τ.setArr "dm" k 1, (Run.ite_true (by rw [hc]; simp [hX])
          (Run.store (by simp [hbz]; omega) (by simp; omega) (by rw [hdmτ]; simp; omega))).mono
          (by simp [Cond.size, Expr.size]), by simp [hbz], hC _ _ (hCa _ _ _ hCτ), ?_⟩
        rw [arrs_setVar, arrs_setArr, if_pos rfl, hdmτ, hupd 1 (by simp [hX])]
      · refine ⟨τ.setArr "dm" k 0, (Run.ite_false (by rw [hc]; simp [hX])
          (Run.store (by simp [hbz]; omega) (by simp; omega) (by rw [hdmτ]; simp; omega))).mono
          (by simp [Cond.size, Expr.size]), by simp [hbz], hC _ _ (hCa _ _ _ hCτ), ?_⟩
        rw [arrs_setVar, arrs_setArr, if_pos rfl, hdmτ, hupd 0 (by simp [hX])])
  refine ⟨σ', fk n, hr.mono (by simp [Expr.size]), hC', hdm', fun v hv => ?_⟩
  simp only [fk, hv, if_true, hS v hv]
  split_ifs with h <;> simp [h]

/-- **Clearing the table.** -/
theorem clrCt_run {B nc : ℕ} {σ : Env} (C : Env → Prop)
    (hC : ∀ τ x, C τ → C (τ.setVar "bz" x)) (hCa : ∀ τ i x, C τ → C (τ.setArr "ct" i x))
    (hCn : ∀ τ, C τ → τ.vars "nc" = nc) (hσ : C σ) (hct : (σ.arrs "ct").length = nc)
    (hncB : nc < B) :
    ∃ σ', Run B clrCt σ σ' (nc * 12 + 6) ∧ C σ' ∧ σ'.arrs "ct" = arrOf nc (fun _ => 0) := by
  let fk : ℕ → ℕ → ℕ := fun k v => if v < k then 0 else (σ.arrs "ct").getD v 0
  let I : ℕ → Env → Prop := fun k τ => C τ ∧ τ.arrs "ct" = arrOf nc (fk k)
  have hct0 : σ.arrs "ct" = arrOf nc (fk 0) := by
    refine List.ext_getElem (by simp [hct]) fun v h1 h2 => ?_
    simp [fk, arrOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  obtain ⟨σ', hr, ⟨hC', hct'⟩, -⟩ := forUp_run (B := B) (i := "bz") (e := .var "nc")
    (body := .store "ct" (.var "bz") (.lit 0)) (N := nc) (K := 4) I hncB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hCn τ hI.1).symm, by rw [hCn τ hI.1]; exact hncB⟩)
    ⟨hC σ 0 hσ, by rw [arrs_setVar]; exact hct0⟩
    (by
      rintro k hk τ ⟨hCτ, hctτ⟩ hbz
      refine ⟨τ.setArr "ct" k 0, (Run.store (by simp [hbz]; omega) (by simp; omega)
        (by rw [hctτ]; simp; omega)).mono (by simp [Expr.size]), by simp [hbz],
        hC _ _ (hCa _ _ _ hCτ), ?_⟩
      rw [arrs_setVar, arrs_setArr, if_pos rfl, hctτ, set_arrOf]
      congr 1; funext v
      by_cases hv : v = k
      · subst hv; simp [fk]
      · simp only [hv, if_false, fk]
        by_cases hvk : v < k
        · simp [hvk, show v < k + 1 by omega]
        · simp [hvk, show ¬ v < k + 1 by omega])
  refine ⟨σ', hr.mono (by simp [Expr.size]), hC', ?_⟩
  rw [hct']; simp only [arrOf]
  exact List.map_congr_left fun v hv => by simp [fk, List.mem_range.1 hv]

/-! ### The rounds -/

theorem tabOK_zero (n nc : ℕ) (cl : ℕ → ℕ) (M : ℕ → ℕ → Prop) :
    TabOK n nc 0 cl M (fun _ => 0) := fun c _ => ⟨by simp, fun t h => absurd (show (0 : ℕ) = t + 1 from h) (by omega)⟩

theorem tabOK_succ {n nc s : ℕ} {cl g : ℕ → ℕ} {M : ℕ → ℕ → Prop} (h : TabOK n nc s cl M g) :
    TabOK n nc (s + 1) cl M (recTab g cl (M s) s n) := by
  intro c hc
  obtain ⟨h0, h1⟩ := h c hc
  unfold recTab
  by_cases hg : g c = 0
  · rw [if_neg (not_not.2 hg)]
    have hpre := h0.1 hg
    by_cases hR : ∃ y < n, cl y = c ∧ M s y
    · rw [if_pos hR]
      refine ⟨⟨fun h' => absurd h' (by omega), fun h' => absurd hR (h' s (by omega))⟩,
        fun t ht => ?_⟩
      obtain rfl : t = s := by omega
      exact ⟨by omega, hR, hpre⟩
    · rw [if_neg hR]
      refine ⟨⟨fun _ t ht => ?_, fun _ => rfl⟩, fun t ht => absurd ht (by omega)⟩
      rcases Nat.lt_or_ge t s with h | h
      · exact hpre t h
      · obtain rfl : t = s := by omega
        exact hR
  · rw [if_pos hg]
    refine ⟨⟨fun h' => absurd h' hg, fun h' => absurd (h0.2 fun t ht => h' t (by omega)) hg⟩,
      fun t ht => ?_⟩
    obtain ⟨a, b, d⟩ := h1 t ht
    exact ⟨by omega, b, d⟩

/-- The cost of `cdist`. -/
def cdCost (n nc m : ℕ) : ℕ := n * (130 * n + 14 * m + 60) + 12 * nc + 40

/-- **The search from a color class.** -/
theorem cdist_run {B n nc nsE nsN X : ℕ} {oE tE oN tN col cl : ℕ → ℕ} {S : ℕ → Prop} {σ : Env}
    (hG : GraphAt n nsE nsN oE tE oN tN σ) (hco : σ.arrs "co" = arrOf n col)
    (hcl : σ.arrs "cl" = arrOf n cl) (hx : σ.vars "bx" = X) (hnc : σ.vars "nc" = nc)
    (hdm : (σ.arrs "dm").length = n) (hdn : (σ.arrs "dn").length = n)
    (hct : (σ.arrs "ct").length = nc) (hS : ∀ v < n, S v ↔ col v = X)
    (hclc : ∀ v < n, cl v < nc) (hnB : n + 2 < B) (hEB : nsE + 1 < B) (hNB : nsN + 1 < B)
    (hncB : nc < B) (hXB : X < B) (hcolB : ∀ v < n, col v < B) :
    ∃ σ' g, Run B cdist σ σ' (cdCost n nc (nsE + nsN)) ∧ σ'.arrs "ct" = arrOf nc g ∧
      TabOK n nc n cl (msP n (Adj2 oE tE oN tN) S) g ∧ GraphAt n nsE nsN oE tE oN tN σ' ∧
      σ'.arrs "co" = σ.arrs "co" ∧ σ'.arrs "cl" = σ.arrs "cl" ∧
      ∀ z, z ∉ cdist.wvars → σ'.vars z = σ.vars z := by
  -- marking
  let C1 : Env → Prop := fun τ => GraphAt n nsE nsN oE tE oN tN τ ∧ τ.arrs "co" = arrOf n col ∧
    τ.arrs "cl" = arrOf n cl ∧ τ.vars "bx" = X ∧ τ.vars "nc" = nc ∧ (τ.arrs "dn").length = n ∧
    (τ.arrs "ct").length = nc
  obtain ⟨σ1, f1, hr1, hC1, hdm1, hf1⟩ := markCls_run (B := B) (X := X) (S := S) (σ := σ) C1
    (fun τ x h => ⟨h.1.setVar (by decide) _, by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
      by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2]⟩)
    (fun τ i x h => ⟨h.1.setArr (by decide) (by decide) (by decide) (by decide) _ _, by simp [h.2.1],
      by simp [h.2.2.1], by simp [h.2.2.2.1], by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2.1],
      by simp [h.2.2.2.2.2.2]⟩)
    (fun τ h => h.2.1) (fun τ h => h.1.2.2) (fun τ h => h.2.2.2.1)
    ⟨hG, hco, hcl, hx, hnc, hdn, hct⟩ hdm hS (by omega) hXB hcolB
  -- clearing
  let C2 : Env → Prop := fun τ => C1 τ ∧ τ.arrs "dm" = arrOf n f1
  obtain ⟨σ2, hr2, hC2, hct2⟩ := clrCt_run (B := B) (nc := nc) (σ := σ1) C2
    (fun τ x h => ⟨⟨h.1.1.setVar (by decide) _, by simp [h.1.2.1], by simp [h.1.2.2.1],
      by simp [h.1.2.2.2.1], by simp [h.1.2.2.2.2.1], by simp [h.1.2.2.2.2.2.1],
      by simp [h.1.2.2.2.2.2.2]⟩, by simp [h.2]⟩)
    (fun τ i x h => ⟨⟨h.1.1.setArr (by decide) (by decide) (by decide) (by decide) _ _,
      by simp [h.1.2.1], by simp [h.1.2.2.1], by simp [h.1.2.2.2.1], by simp [h.1.2.2.2.2.1],
      by simp [h.1.2.2.2.2.2.1], by simp [h.1.2.2.2.2.2.2]⟩, by simp [h.2]⟩)
    (fun τ h => h.1.2.2.2.2.1) ⟨hC1, hdm1⟩ hC1.2.2.2.2.2.2 hncB
  -- the rounds
  let M := msP n (Adj2 oE tE oN tN) S
  let I : ℕ → Env → Prop := fun s τ => C1 τ ∧ ∃ f g, τ.arrs "dm" = arrOf n f ∧ IndOn n f (M s) ∧
    τ.arrs "ct" = arrOf nc g ∧ TabOK n nc s cl M g
  have hstepK : ∀ s < n, ∀ τ, I s τ → τ.vars "bs" = s → ∃ τ', Run B (.seq record layer) τ τ'
      (121 * n + 14 * (nsE + nsN) + 26) ∧ τ'.vars "bs" = s ∧ I (s + 1) (τ'.setVar "bs" (s + 1)) := by
    rintro s hs τ ⟨hC, f, g, hdmτ, hf, hctτ, hg⟩ hbs
    have hgB : ∀ c < nc, g c < B := by
      intro c hc
      have := (hg c hc).2
      cases h : g c with
      | zero => omega
      | succ t => have := (this t h).1; omega
    let C3 : Env → Prop := fun τ' => C1 τ' ∧ τ'.arrs "dm" = arrOf n f ∧ τ'.vars "bs" = s
    obtain ⟨τ1, hr1', hC3, hct1⟩ := record_run (B := B) (n := n) (nc := nc) (s := s) (f := f) (g := g)
      (cl := cl) (M := M s) (σ := τ) C3
      (fun τ x h => ⟨⟨h.1.1.setVar (by decide) _, by simp [h.1.2.1], by simp [h.1.2.2.1],
        by simp [h.1.2.2.2.1], by simp [h.1.2.2.2.2.1], by simp [h.1.2.2.2.2.2.1],
        by simp [h.1.2.2.2.2.2.2]⟩, by simp [h.2.1], by simp [h.2.2]⟩)
      (fun τ i x h => ⟨⟨h.1.1.setArr (by decide) (by decide) (by decide) (by decide) _ _,
        by simp [h.1.2.1], by simp [h.1.2.2.1], by simp [h.1.2.2.2.1], by simp [h.1.2.2.2.2.1],
        by simp [h.1.2.2.2.2.2.1], by simp [h.1.2.2.2.2.2.2]⟩, by simp [h.2.1], by simp [h.2.2]⟩)
      (fun τ h => h.2.1) (fun τ h => h.1.2.2.1) (fun τ h => h.1.1.2.2) (fun τ h => h.2.2)
      ⟨hC, hdmτ, hbs⟩ hctτ hf hclc (by omega) hncB (by omega) hgB
    obtain ⟨⟨hG1, hco1, hcl1, hx1, hnc1, hdn1, hctl1⟩, hdm1', hbs1⟩ := hC3
    obtain ⟨τ2, f2, hr2', hdm2, hf2, hG2, hdn2⟩ := layer_run hG1 hnB hEB hNB hdm1' hf hdn1
    have hfa := hr2'.frame_arr
    have hfv := hr2'.frame_var
    refine ⟨τ2, (Run.seq hr1' hr2').mono (by omega), by rw [hfv "bs" (by decide), hbs1],
      ⟨hG2.setVar (by decide) _, by simp [hfa "co" (by decide), hco1],
        by simp [hfa "cl" (by decide), hcl1], by simp [hfv "bx" (by decide), hx1],
        by simp [hfv "nc" (by decide), hnc1], by simp [hdn2],
        by simp [hfa "ct" (by decide), hctl1]⟩,
      f2, recTab g cl (M s) s n, by simp [hdm2], hf2, by simp [hfa "ct" (by decide), hct1],
      tabOK_succ hg⟩
  obtain ⟨σ3, hr3, ⟨hC3, f3, g3, -, -, hct3, hg3⟩, -⟩ := forUp_run (B := B) (i := "bs")
    (e := .var "n") (body := .seq record layer) (N := n) (K := 121 * n + 14 * (nsE + nsN) + 26) I
    (by omega)
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hI.1.1.2.2).symm, by rw [hI.1.1.2.2]; omega⟩)
    ⟨by
      obtain ⟨h, _⟩ := hC2
      exact ⟨h.1.setVar (by decide) _, by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2.1],
        by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2]⟩,
      f1, fun _ => 0, by simp [hC2.2], hf1, by simp [hct2], tabOK_zero n nc cl M⟩
    hstepK
  refine ⟨σ3, g3, ?_, hct3, hg3, hC3.1, by rw [hC3.2.1, hco], by rw [hC3.2.2.1, hcl], ?_⟩
  · refine (Run.seq hr1 (Run.seq hr2 hr3)).mono ?_
    simp only [cdCost, Expr.size]
    nlinarith
  · intro z hz
    simp only [cdist, Com.wvars, List.mem_append, not_or] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [hr3.frame_var z h3, hr2.frame_var z h2, hr1.frame_var z h1]

/-! ### The link to the table of `G` -/

/-- The color of a vertex, as a function on numbers. -/
noncomputable def colN {n : ℕ} (G : PartialGraph (Fin n)) (v : ℕ) : ℕ :=
  if h : v < n then G.color ⟨v, h⟩ else 0

theorem clsP_iff {n : ℕ} (G : PartialGraph (Fin n)) (X : ℕ) : ∀ v < n, clsP G X v ↔ colN G v = X := by
  intro v hv; simp [clsP, colN, hv]

/-- **The search computes the table of `G`.** If `cl` gives the vertices
of color `Y` the index `c`, entry `c` of the table is `cTab G X Y`. -/
theorem tab_cTab {n nc : ℕ} {G : PartialGraph (Fin n)} {cl g : ℕ → ℕ} {X : ℕ}
    (hg : TabOK n nc n cl (msP n (adjG G) (clsP G X)) g) {c Y : ℕ} (hc : c < nc)
    (hcY : ∀ y < n, cl y = c ↔ colN G y = Y) : g c = cTab G X Y := by
  have hR : ∀ t, (∃ y < n, cl y = c ∧ msP n (adjG G) (clsP G X) t y) ↔
      ∃ y : Fin n, G.color y = Y ∧ msP n (adjG G) (clsP G X) t y := by
    intro t
    constructor
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨⟨y, hy⟩, ?_, h2⟩
      have := (hcY y hy).1 h1
      simpa [colN, hy] using this
    · rintro ⟨y, h1, h2⟩
      exact ⟨y.val, y.isLt, (hcY y y.isLt).2 (by simp [colN, h1]), h2⟩
  obtain ⟨h0, h1⟩ := hg c hc
  cases h : g c with
  | zero =>
    symm
    exact (cTab_eq_zero G X Y).2 fun t ht => (hR t).not.1 (h0.1 h t ht)
  | succ t =>
    obtain ⟨-, ht, hmin⟩ := h1 t h
    symm
    exact (cTab_eq_succ G X Y t).2 ⟨(hR t).1 ht, fun t' h' => (hR t').not.1 (hmin t' h')⟩

end Lax185574Proofs.ResolveRam.Glue
