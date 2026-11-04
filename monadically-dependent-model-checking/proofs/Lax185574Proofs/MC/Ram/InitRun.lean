import Lax185574Proofs.MC.Ram.InitBuild

/-!
The run of `buildInit`: after it, the array `ta` holds the word of the
initial tree, `lvlWord K q ℓ c q`, and the scalar `iwn` its length.
-/

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

variable {B K q ℓ c cap : ℕ}

/-- The extensions. -/
theorem wExts_run {a n : ℕ} {W l : List ℕ} {τ : Env} (hC : BCtx K q ℓ c cap τ)
    (ha : τ.vars "iwa" = a) (hW : Filled "ta" "iwn" W τ) (hn : W.length = n)
    (hF : Filled "tb" "iwp" l τ) (hcap : l.length + a * (n + 2) ≤ cap)
    (hB : l.length + a * (n + 2) + a + n + 4 < B) (hWB : ∀ v ∈ W, v < B) :
    ∃ τ', Run B wExts τ τ' (a * ((1 + 7 * 2 + 4) + (n * (8 + 1 + 7) + 1 + 5) + 1 + 7) + 1 + 5) ∧
      BCtx K q ℓ c cap τ' ∧ τ'.vars "iwa" = a ∧ Filled "ta" "iwn" W τ' ∧
      Filled "tb" "iwp" (l ++ extsOut a W) τ' := by
  have hnv : τ.vars "iwn" = n := by rw [hW.pos, hn]
  obtain ⟨τ', r, ⟨⟨C', ha', hW'⟩, -⟩, -, F'⟩ := forUp_append (B := B) (i := "iwi")
    (e := .var "iwa") (body := .seq (pushL "tb" "iwp" [.add (.var "iwn") (.lit 1), .var "iwi"]) copyTa)
    (N := a) (K := (1 + 7 * 2 + 4) + (n * (8 + 1 + 7) + 1 + 5)) (a := "tb") (pv := "iwp") (by decide)
    (fun i => [n + 1, i] ++ W)
    (fun τ => (BCtx K q ℓ c cap τ ∧ τ.vars "iwa" = a ∧ Filled "ta" "iwn" W τ) ∧ True)
    (fun τ v h => ⟨⟨h.1.1.setVar (by decide) (by decide) (by decide) (by decide) v,
      by simp [h.1.2.1], h.1.2.2.setVar (by decide) v⟩, trivial⟩)
    (by omega) ⟨⟨hC, ha, hW⟩, trivial⟩ hF (fun τ h => evalB_var_of h.1.2.1 (by omega))
    (by
      rintro i hi ρ ⟨⟨hρ, hρa, hρW⟩, -⟩ hρi hFi
      have hl : (l ++ (List.range i).flatMap fun i => [n + 1, i] ++ W).length =
          l.length + i * (n + 2) := by
        rw [List.length_append, length_flatMap_const (m := n + 2)]
        intro k; simp [hn]
      have hpre := prefix_le (m := n + 2) hi
      have hρn : ρ.vars "iwn" = n := by rw [hρW.pos, hn]
      obtain ⟨ρ₁, r₁, F₁, fv₁, fa₁, fl₁, -, -⟩ := pushL_run (B := B)
        (es := [.add (.var "iwn") (.lit 1), .var "iwi"]) (vs := [n + 1, i]) hFi
        (fun ρ' hv _ => .cons (evalB_bin (evalB_var_of ((hv _ (by decide)).trans hρn) (by omega))
          (evalB_lit (by omega)) (by simp; omega))
          (.cons (evalB_var_of ((hv _ (by decide)).trans hρi) (by omega)) .nil))
        (by rw [hρ.ltb, hl]; simp; omega) (by rw [hl]; simp; omega)
      have C₁ : BCtx K q ℓ c cap ρ₁ :=
        hρ.push (by decide) (by decide) (by decide) (by decide) fv₁ fa₁ fl₁
      have W₁ : Filled "ta" "iwn" W ρ₁ := hρW.congr (fv₁ _ (by decide)) (fa₁ _ (by decide))
      obtain ⟨ρ₂, r₂, ⟨C₂, ha₂, W₂⟩, F₂⟩ := copy_run (B := B) (j := "iwj") (src := "ta")
        (dst := "tb") (pv := "iwp") (by decide) (e := .var "iwn") (W := W)
        (fun τ => BCtx K q ℓ c cap τ ∧ τ.vars "iwa" = a ∧ Filled "ta" "iwn" W τ)
        (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v,
          by simp [h.2.1], h.2.2.setVar (by decide) v⟩)
        (fun τ τ' h hv ha hl => ⟨h.1.push (by decide) (by decide) (by decide) (by decide) hv ha hl,
          by rw [hv _ (by decide), h.2.1], h.2.2.congr (hv _ (by decide)) (ha _ (by decide))⟩)
        (fun τ h => h.2.2.get) (fun τ h => by rw [h.1.ltb, List.length_append, hl]; simp; omega)
        (fun τ h => evalB_var_of h.2.2.pos (by omega)) ⟨C₁, by rw [fv₁ _ (by decide), hρa], W₁⟩ F₁
        (by rw [List.length_append, hl]; simp; omega) hWB
      refine ⟨ρ₂, (Run.seq r₁ r₂).mono (by simp [copyTa]; omega), ?_, ⟨⟨C₂, ha₂, W₂⟩, trivial⟩, ?_⟩
      · rw [r₂.frame_var "iwi" (by decide), fv₁ _ (by decide), hρi]
      · rw [flatMap_range_succ', ← List.append_assoc]; simpa using F₂)
  refine ⟨τ', r, C', ha', hW', ?_⟩
  have : extsOut a W = (List.range a).flatMap fun i => [n + 1, i] ++ W := by
    simp [extsOut, hn]
  rw [this]; exact F'

theorem cntE_eval {τ : Env} {A rm rp : ℕ} (ha : τ.vars "iwa" = A) (hrm : τ.vars "iwrm" = rm)
    (hrp : τ.vars "iwrp" = rp) (hB : atomsCnt A rm rp + rm + rp + 2 < B) :
    cntE.evalB B τ = some (atomsCnt A rm rp) := by
  have h1 : A * A + A ≤ atomsCnt A rm rp := by simp only [atomsCnt]; omega
  have h2 : (rm + 1) * (A * A) ≤ atomsCnt A rm rp := by simp only [atomsCnt]; omega
  have h3 : rp * A ≤ atomsCnt A rm rp := by simp only [atomsCnt]; omega
  have h5 : A ≤ atomsCnt A rm rp := by simp only [atomsCnt]; omega
  have h12 : A * A + A + (rm + 1) * (A * A) ≤ atomsCnt A rm rp := by simp only [atomsCnt]; omega
  have eA := evalB_var_of (B := B) ha (by omega)
  have eAA := evalB_bin (op := .mul) eA eA (by simp; omega)
  have e1 := evalB_bin (op := .add) eAA eA (by simp; omega)
  have eR := evalB_bin (op := .add) (evalB_var_of (B := B) hrm (by omega)) (evalB_lit (n := 1)
    (by omega)) (by simp; omega)
  have e2 := evalB_bin (op := .mul) eR eAA (by simp; omega)
  have e3 := evalB_bin (op := .add) e1 e2 (by simp; omega)
  have e4 := evalB_bin (op := .mul) (evalB_var_of (B := B) hrp (by omega)) eA (by simp; omega)
  have e5 := evalB_bin (op := .add) e3 e4 (by simp [atomsCnt] at hB ⊢; omega)
  simpa [cntE, atomsCnt] using e5

end Lax185574Proofs.MC
