import Lax185574Proofs.MC.Ram.InitRun

/-!
One level of the initial tree: `wLevel` writes level `d` into `tb`.
-/

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

variable {B K q ℓ c cap : ℕ}

theorem cost_aux {rm rp A L T : ℕ} (h : T ≤ 100 * ((rm + rp + 2) * ((A + 1) * (A + 1))))
    (h1 : rm ≤ L) (h2 : rp ≤ L) (h3 : A ≤ L) : T ≤ 200 * ((L + 1) * ((L + 1) * (L + 1))) := by
  have e1 : rm + rp + 2 ≤ 2 * (L + 1) := by omega
  have e2 : (A + 1) * (A + 1) ≤ (L + 1) * (L + 1) := Nat.mul_le_mul (by omega) (by omega)
  have := Nat.mul_le_mul e1 e2
  nlinarith

/-- The cost bound of one level. -/
def lvlCost (L : ℕ) : ℕ := 300 * ((L + 1) * ((L + 1) * (L + 1)))

theorem lvl_bounds (hℓ : 1 ≤ ℓ) {d : ℕ} (hdq : d ≤ q) :
    rmD K d ≤ lvlLen K q ℓ q ∧ rpD K d ≤ lvlLen K q ℓ q ∧ ℓ + q ≤ lvlLen K q ℓ q ∧
      lvlLen K q ℓ d ≤ lvlLen K q ℓ q := by
  have hm := lvlLen_mono K q ℓ hℓ d q hdq le_rfl
  have h0 := lvlLen_mono K q ℓ hℓ 0 q (Nat.zero_le _) le_rfl
  have hs := sum_le_alen (a := ℓ + q - 0) (rm := rmD K 0) (rp := rpD K 0) (by omega)
  have ha := alen_le K q ℓ 0
  exact ⟨le_trans (rmD_le K q ℓ d hdq hℓ) hm, le_trans (rpD_le K q ℓ d hdq hℓ) hm,
    by simp only [Nat.sub_zero] at hs ha; omega, hm⟩

theorem lvlWord_succ_form (K q ℓ c d : ℕ) :
    lvlWord K q ℓ c (d + 1) = atomsCnt (ℓ + q - (d + 1)) (rmD K (d + 1)) (rpD K (d + 1)) ::
      atomsOut (ℓ + q - (d + 1)) (rmD K (d + 1)) (rpD K (d + 1)) c ++ [ℓ + q - (d + 1)] ++
      extsOut (ℓ + q - (d + 1)) (lvlWord K q ℓ c d) := by
  simp [lvlWord, levelWord]

theorem arithB {x A n L c B : ℕ} (hx : x ≤ L) (hA : A ≤ L) (hn : n ≤ L)
    (hB : 4 * L + c + 20 < B) : x + A + n + 4 < B := by omega

theorem arithW {v n L c B : ℕ} (hv : v ≤ n + c + 5) (hn : n ≤ L) (hB : 4 * L + c + 20 < B) :
    v < B := by omega

set_option maxHeartbeats 1000000 in
/-- The common part of a level: position zero, the count and the atoms. -/
theorem wLevel_pre {d : ℕ} {τ : Env} (hC : BCtx K q ℓ c cap τ) (hℓ : 1 ≤ ℓ) (hdq : d ≤ q)
    (hd : τ.vars "iwd" = d) (ha : τ.vars "iwa" = ℓ + q - d) (hrm : τ.vars "iwrm" = rmD K d)
    (hrp : τ.vars "iwrp" = rpD K d)
    (hcap : lvlLen K q ℓ q ≤ cap) (hB : 4 * lvlLen K q ℓ q + c + 20 < B) :
    ∃ τ₀ τ₁ τ₂ T₂, Run B (.assign "iwp" (.lit 0)) τ τ₀ 2 ∧
      Run B (pushL "tb" "iwp" [cntE]) τ₀ τ₁ 25 ∧ Run B wAtoms τ₁ τ₂ T₂ ∧
      T₂ ≤ 200 * ((lvlLen K q ℓ q + 1) * ((lvlLen K q ℓ q + 1) * (lvlLen K q ℓ q + 1))) ∧
      BCtx K q ℓ c cap τ₂ ∧ τ₂.vars "iwd" = d ∧ τ₂.vars "iwa" = ℓ + q - d ∧
      τ₂.arrs "ta" = τ.arrs "ta" ∧ τ₂.vars "iwn" = τ.vars "iwn" ∧
      Filled "tb" "iwp" (atomsCnt (ℓ + q - d) (rmD K d) (rpD K d) ::
        atomsOut (ℓ + q - d) (rmD K d) (rpD K d) c) τ₂ := by
  have hLd := lvlLen_mono K q ℓ hℓ d q hdq le_rfl
  have hrmL := rmD_le K q ℓ d hdq hℓ
  have hrpL := rpD_le K q ℓ d hdq hℓ
  have hal := alen_le K q ℓ d
  obtain ⟨A, hA⟩ : ∃ A, A = ℓ + q - d := ⟨_, rfl⟩
  rw [← hA] at hal ha ⊢
  have hA1 : 1 ≤ A := by omega
  have hsum := sum_le_alen (a := A) (rm := rmD K d) (rp := rpD K d) hA1
  have hcntA : 1 + (atomsOut A (rmD K d) (rpD K d) c).length = alen A (rmD K d) (rpD K d) := by
    rw [length_atomsOut]; simp only [alen]; ring
  have hcnt : atomsCnt A (rmD K d) (rpD K d) ≤ alen A (rmD K d) (rpD K d) := by
    simp only [atomsCnt, alen]; nlinarith
  have r₀ := Run.assign (B := B) (σ := τ) (x := "iwp") (e := .lit 0) (v := 0) (evalB_lit (by omega))
  have F₀ := Filled.empty "tb" "iwp" τ
  have C₀ := hC.setVar (y := "iwp") (by decide) (by decide) (by decide) (by decide) 0
  obtain ⟨τ₁, r₁, F₁, fv₁, fa₁, fl₁, -, -⟩ := pushL_run (B := B) (es := [cntE])
    (vs := [atomsCnt A (rmD K d) (rpD K d)]) F₀
    (fun τ' hv _ => .cons (cntE_eval (by rw [hv _ (by decide)]; simp [ha])
      (by rw [hv _ (by decide)]; simp [hrm]) (by rw [hv _ (by decide)]; simp [hrp]) (by omega)) .nil)
    (by simp [hC.ltb]; omega) (by simp; omega)
  have C₁ := C₀.push (by decide) (by decide) (by decide) (by decide) fv₁ fa₁ fl₁
  have AC₁ : ACtx A (rmD K d) (rpD K d) c cap τ₁ :=
    ⟨by rw [fv₁ _ (by decide)]; simp [ha], by rw [fv₁ _ (by decide)]; simp [hrm],
      by rw [fv₁ _ (by decide)]; simp [hrp], C₁.hc, C₁.ltb⟩
  have hl1 : ([] ++ [atomsCnt A (rmD K d) (rpD K d)] : List ℕ).length = 1 := rfl
  obtain ⟨τ₂, T₂, r₂, hT₂, AC₂, F₂⟩ := wAtoms_run (B := B) AC₁ F₁ (by rw [hl1]; omega)
    (by rw [hl1]; omega)
  have hta₂' : τ₂.arrs "ta" = τ₁.arrs "ta" := r₂.frame_arr "ta" (by decide)
  have e1 : τ₂.vars "iwK" = τ₁.vars "iwK" := r₂.frame_var _ (by decide)
  have e2 : τ₂.vars "iwq" = τ₁.vars "iwq" := r₂.frame_var _ (by decide)
  have e3 : τ₂.vars "iwl" = τ₁.vars "iwl" := r₂.frame_var _ (by decide)
  have e4 : τ₂.vars "iwc" = τ₁.vars "iwc" := r₂.frame_var _ (by decide)
  have e5 : τ₂.vars "iwd" = τ₁.vars "iwd" := r₂.frame_var _ (by decide)
  have e6 : τ₂.vars "iwn" = τ₁.vars "iwn" := r₂.frame_var _ (by decide)
  refine ⟨_, τ₁, τ₂, T₂, r₀.mono (by simp), r₁.mono (by norm_num [cntE, Expr.size]), r₂,
    cost_aux hT₂ (by omega) (by omega) (by omega),
    ⟨by rw [e1, C₁.hK], by rw [e2, C₁.hq], by rw [e3, C₁.hl], by rw [e4, C₁.hc],
      by rw [hta₂', C₁.lta], AC₂.hcap⟩,
    by rw [e5, fv₁ _ (by decide)]; simp [hd], AC₂.ha,
    by rw [hta₂', fa₁ _ (by decide)]; simp, by rw [e6, fv₁ _ (by decide)]; simp,
    by simpa using F₂⟩

theorem cost_bot {T₂ X : ℕ} (h : T₂ ≤ 200 * X) (hX : 1 ≤ X) : 2 + (25 + (T₂ + (1 + 3 + 1))) ≤ 300 * X := by
  omega

theorem cost_top {T₂ A n L : ℕ} (h : T₂ ≤ 200 * ((L + 1) * ((L + 1) * (L + 1)))) (hA : A ≤ L)
    (hn : n ≤ L) :
    2 + (25 + (T₂ + (1 + 3 + (9 + (A * ((1 + 7 * 2 + 4) + (n * (8 + 1 + 7) + 1 + 5) + 1 + 7) +
      1 + 5))))) ≤ lvlCost L := by
  have h1 : A * n ≤ L * L := Nat.mul_le_mul hA hn
  have h2 : L * L ≤ (L + 1) * ((L + 1) * (L + 1)) := by nlinarith
  have h3 : L ≤ (L + 1) * ((L + 1) * (L + 1)) := by nlinarith
  have h4 : 1 ≤ (L + 1) * ((L + 1) * (L + 1)) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have : A * ((1 + 7 * 2 + 4) + (n * (8 + 1 + 7) + 1 + 5) + 1 + 7) = 16 * (A * n) + 33 * A := by ring
  simp only [lvlCost]
  omega

set_option maxHeartbeats 1000000 in
theorem wLevel_run {d : ℕ} {τ : Env} (hC : BCtx K q ℓ c cap τ) (hℓ : 1 ≤ ℓ) (hdq : d ≤ q)
    (hd : τ.vars "iwd" = d) (ha : τ.vars "iwa" = ℓ + q - d) (hrm : τ.vars "iwrm" = rmD K d)
    (hrp : τ.vars "iwrp" = rpD K d)
    (hprev : d = 0 ∨ ∃ d', d = d' + 1 ∧ Filled "ta" "iwn" (lvlWord K q ℓ c d') τ)
    (hcap : lvlLen K q ℓ q ≤ cap) (hB : 4 * lvlLen K q ℓ q + c + 20 < B) :
    ∃ τ' T, Run B wLevel τ τ' T ∧ T ≤ lvlCost (lvlLen K q ℓ q) ∧ BCtx K q ℓ c cap τ' ∧
      Filled "tb" "iwp" (lvlWord K q ℓ c d) τ' := by
  obtain ⟨τ₀, τ₁, τ₂, T₂, r₀, r₁, r₂, hT₂, C₂, hd₂, ha₂, hta₂, hn₂, F₂⟩ :=
    wLevel_pre (B := B) hC hℓ hdq hd ha hrm hrp hcap hB
  have hX : 1 ≤ (lvlLen K q ℓ q + 1) * ((lvlLen K q ℓ q + 1) * (lvlLen K q ℓ q + 1)) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨-, -, hqL, -⟩ := lvl_bounds (K := K) hℓ hdq
  rcases hprev with rfl | ⟨d', rfl, hW⟩
  · refine ⟨τ₂, _, Run.seq r₀ (Run.seq r₁ (Run.seq r₂ (Run.ite_true ?_ Run.skip))),
      cost_bot hT₂ hX, C₂, by simpa [lvlWord] using F₂⟩
    rw [evalB_condEq (evalB_var_of hd₂ (by omega)) (evalB_lit (by omega))]; rfl
  · have hW₂ : Filled "ta" "iwn" (lvlWord K q ℓ c d') τ₂ := hW.congr hn₂ hta₂
    obtain ⟨A, hA⟩ : ∃ A, A = ℓ + q - (d' + 1) := ⟨_, rfl⟩
    rw [← hA] at ha₂ F₂
    have hlenW := length_lvlWord K q ℓ c d'
    have hLd := lvlLen_mono K q ℓ hℓ (d' + 1) q hdq le_rfl
    have hext : lvlLen K q ℓ (d' + 1) =
        alen A (rmD K (d' + 1)) (rpD K (d' + 1)) + 1 + A * (lvlLen K q ℓ d' + 2) := by
      simp only [lvlLen, hA]
    have hcntA : 1 + (atomsOut A (rmD K (d' + 1)) (rpD K (d' + 1)) c).length =
        alen A (rmD K (d' + 1)) (rpD K (d' + 1)) := by
      rw [length_atomsOut]; simp only [alen]; ring
    have hentries := lvlWord_entries K q ℓ c hℓ d' (by omega)
    have hA1 : 1 ≤ A := by omega
    have hAn : A ≤ A * (lvlLen K q ℓ d' + 2) := Nat.le_mul_of_pos_right _ (by omega)
    have hnn : lvlLen K q ℓ d' ≤ A * (lvlLen K q ℓ d' + 2) := by nlinarith
    have hpos₂ : (atomsCnt A (rmD K (d' + 1)) (rpD K (d' + 1)) ::
        atomsOut A (rmD K (d' + 1)) (rpD K (d' + 1)) c).length =
        alen A (rmD K (d' + 1)) (rpD K (d' + 1)) := by simp only [List.length_cons]; omega
    obtain ⟨τ₃, r₃, F₃, fv₃, fa₃, fl₃, -, -⟩ := pushL_run (B := B) (es := [.var "iwa"]) (vs := [A]) F₂
      (fun τ' hv _ => .cons (evalB_var_of ((hv _ (by decide)).trans ha₂) (by omega)) .nil)
      (by rw [hpos₂, C₂.ltb]; simp; omega) (by rw [hpos₂]; simp; omega)
    have C₃ := C₂.push (by decide) (by decide) (by decide) (by decide) fv₃ fa₃ fl₃
    have ha₃ : τ₃.vars "iwa" = A := by rw [fv₃ _ (by decide), ha₂]
    have hW₃ : Filled "ta" "iwn" (lvlWord K q ℓ c d') τ₃ :=
      hW₂.congr (fv₃ _ (by decide)) (fa₃ _ (by decide))
    have hpos₃ : (atomsCnt A (rmD K (d' + 1)) (rpD K (d' + 1)) ::
        atomsOut A (rmD K (d' + 1)) (rpD K (d' + 1)) c ++ [A]).length =
        alen A (rmD K (d' + 1)) (rpD K (d' + 1)) + 1 := by
      rw [List.length_append, hpos₂]; rfl
    have hAL : A ≤ lvlLen K q ℓ q := hA ▸ le_trans (Nat.sub_le _ _) hqL
    have hd'L : lvlLen K q ℓ d' ≤ lvlLen K q ℓ q :=
      lvlLen_mono K q ℓ hℓ d' q (Nat.le_of_succ_le hdq) le_rfl
    obtain ⟨lst, hlst⟩ : ∃ lst, lst = atomsCnt A (rmD K (d' + 1)) (rpD K (d' + 1)) ::
        atomsOut A (rmD K (d' + 1)) (rpD K (d' + 1)) c ++ [A] := ⟨_, rfl⟩
    rw [← hlst] at F₃ hpos₃
    have hsum₄ : lst.length + A * (lvlLen K q ℓ d' + 2) = lvlLen K q ℓ (d' + 1) := by
      rw [hpos₃, hext]
    have hcap₄ : lst.length + A * (lvlLen K q ℓ d' + 2) ≤ cap := by
      rw [hsum₄]; exact Nat.le_trans hLd hcap
    have hB₄ : lst.length + A * (lvlLen K q ℓ d' + 2) + A + lvlLen K q ℓ d' + 4 < B := by
      rw [hsum₄]; exact arithB hLd hAL hd'L hB
    have hWB : ∀ v ∈ lvlWord K q ℓ c d', v < B := fun v hv => arithW (hentries v hv) hd'L hB
    obtain ⟨τ₄, r₄, C₄, -, -, F₄⟩ := wExts_run (B := B) (a := A) (n := lvlLen K q ℓ d')
      (W := lvlWord K q ℓ c d') C₃ ha₃ hW₃ hlenW F₃ hcap₄ hB₄ hWB
    refine ⟨τ₄, _, Run.seq r₀ (Run.seq r₁ (Run.seq r₂ (Run.ite_false ?_
      (Run.seq (r₃.mono (show 1 + 7 * [Expr.var "iwa"].length + ([Expr.var "iwa"].map Expr.size).sum ≤ 9
        by simp)) r₄)))), cost_top hT₂ hAL hd'L, C₄, ?_⟩
    · rw [evalB_condEq (evalB_var_of hd₂ (by omega)) (evalB_lit (by omega))]; rfl
    · subst hA hlst
      rw [lvlWord_succ_form]; exact F₄

end Lax185574Proofs.MC
