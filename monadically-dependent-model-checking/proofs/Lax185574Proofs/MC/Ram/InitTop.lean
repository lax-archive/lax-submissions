import Lax185574Proofs.MC.Ram.InitLevel

/-!
The whole run of `buildInit`: afterwards the array `ta` holds the word
`initWord k q ℓ c` of the initial tree, in time depending only on the
rank and the arity.
-/

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

variable {B K q ℓ c cap : ℕ}

theorem copyBack_run {V : List ℕ} {τ : Env} (hC : BCtx K q ℓ c cap τ)
    (hF : Filled "tb" "iwp" V τ) (hV : V.length ≤ cap) (hB : V.length + 1 < B)
    (hVB : ∀ v ∈ V, v < B) :
    ∃ τ', Run B copyBack τ τ' (2 + (V.length * (8 + 1 + 7) + 1 + 5)) ∧ BCtx K q ℓ c cap τ' ∧
      Filled "ta" "iwn" V τ' := by
  have r₀ := Run.assign (B := B) (σ := τ) (x := "iwn") (e := .lit 0) (v := 0) (evalB_lit (by omega))
  obtain ⟨τ', r, ⟨C', -⟩, F'⟩ := copy_run (B := B) (j := "iwj") (src := "tb") (dst := "ta")
    (pv := "iwn") (by decide) (e := .var "iwp") (W := V) (l := [])
    (fun τ => BCtx K q ℓ c cap τ ∧ Filled "tb" "iwp" V τ)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v,
      h.2.setVar (by decide) v⟩)
    (fun τ τ' h hv ha hl => ⟨h.1.push (by decide) (by decide) (by decide) (by decide) hv ha hl,
      h.2.congr (hv _ (by decide)) (ha _ (by decide))⟩)
    (fun τ h => h.2.get) (fun τ h => by rw [h.1.lta]; simpa using hV)
    (fun τ h => evalB_var_of h.2.pos (by omega))
    ⟨hC.setVar (by decide) (by decide) (by decide) (by decide) 0, hF.setVar (by decide) 0⟩
    (Filled.empty "ta" "iwn" τ) (by simp; omega) hVB
  exact ⟨τ', (Run.seq r₀ r).mono (by simp), C', by simpa using F'⟩

theorem powers_run {d : ℕ} {τ : Env} (hC : BCtx K q ℓ c cap τ) (hd : τ.vars "iwd" = d)
    (h1 : rmD K d < B) (h2 : rpD K d < B) (h9 : 9 < B) :
    ∃ τ', Run B powers τ τ' (40 * (rmD K d + rpD K d + 1)) ∧ BCtx K q ℓ c cap τ' ∧
      τ'.vars "iwrm" = rmD K d ∧ τ'.vars "iwrp" = rpD K d ∧ τ'.vars "iwd" = d := by
  have e1 := lt_nine_pow ((K + 1) * d)
  have e2 := lt_nine_pow (K * (d + 1))
  have hK1 : K + 1 ≤ rpD K d + 1 := by
    have : K ≤ K * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    show K + 1 ≤ 9 ^ (K * (d + 1)) + 1
    omega
  have hd1 : d + 1 ≤ rmD K d + 1 := by
    have : d ≤ (K + 1) * d := Nat.le_mul_of_pos_left _ (by omega)
    show d + 1 ≤ 9 ^ ((K + 1) * d) + 1
    omega
  have hE1 : (K + 1) * d < rmD K d := e1
  have hE2 : K * (d + 1) < rpD K d := e2
  have hKK : K ≤ K * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hdd : d ≤ (K + 1) * d := Nat.le_mul_of_pos_left _ (by omega)
  have r₀ := Run.assign (B := B) (σ := τ) (x := "iwrm") (e := .lit 1) (v := 1) (evalB_lit (by omega))
  obtain ⟨τ₁, r₁, ⟨C₁, hd₁⟩, hrm₁⟩ := pow9_run (B := B) (x := "iwrm") (i := "iwe") (by decide)
    (e := .mul (.add (.var "iwK") (.lit 1)) (.var "iwd")) (E := (K + 1) * d) (σ := τ)
    (fun τ => BCtx K q ℓ c cap τ ∧ τ.vars "iwd" = d)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, by simp [h.2]⟩)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, by simp [h.2]⟩)
    (fun τ h => evalB_bin (evalB_bin (evalB_var_of h.1.hK (by omega)) (evalB_lit (by omega))
      (by simp; omega)) (evalB_var_of h.2 (by omega)) (by simp; omega))
    (by simpa [rmD] using h1) h9 ⟨hC, hd⟩
  have r₂ := Run.assign (B := B) (σ := τ₁) (x := "iwrp") (e := .lit 1) (v := 1) (evalB_lit (by omega))
  obtain ⟨τ₂, r₃, ⟨C₂, hd₂, hrm₂⟩, hrp₂⟩ := pow9_run (B := B) (x := "iwrp") (i := "iwe") (by decide)
    (e := .mul (.var "iwK") (.add (.var "iwd") (.lit 1))) (E := K * (d + 1)) (σ := τ₁)
    (fun τ => BCtx K q ℓ c cap τ ∧ τ.vars "iwd" = d ∧ τ.vars "iwrm" = rmD K d)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, by simp [h.2.1],
      by simp [h.2.2]⟩)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, by simp [h.2.1],
      by simp [h.2.2]⟩)
    (fun τ h => evalB_bin (evalB_var_of h.1.hK (by omega)) (evalB_bin (evalB_var_of h.2.1 (by omega))
      (evalB_lit (by omega)) (by simp; omega)) (by simp; omega))
    (by simpa [rpD] using h2) h9 ⟨C₁, hd₁, by rw [hrm₁]; rfl⟩
  refine ⟨τ₂, (Run.seq r₀ (Run.seq r₁ (Run.seq r₂ r₃))).mono ?_, C₂, hrm₂, by rw [hrp₂]; rfl, hd₂⟩
  simp only [size_mul, size_add, size_var, size_lit]
  simp only [rmD, rpD] at e1 e2 ⊢
  nlinarith

end Lax185574Proofs.MC

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

variable {B K q ℓ c cap : ℕ}

theorem levelBody_run {d : ℕ} {τ : Env} (hC : BCtx K q ℓ c cap τ) (hℓ : 1 ≤ ℓ) (hdq : d ≤ q)
    (hd : τ.vars "iwd" = d)
    (hprev : d = 0 ∨ ∃ d', d = d' + 1 ∧ Filled "ta" "iwn" (lvlWord K q ℓ c d') τ)
    (hcap : lvlLen K q ℓ q ≤ cap) (hB : 4 * lvlLen K q ℓ q + c + 20 < B) :
    ∃ τ' T, Run B levelBody τ τ' T ∧
      T ≤ lvlCost (lvlLen K q ℓ q) + 100 * (lvlLen K q ℓ q + 1) + 50 ∧
      BCtx K q ℓ c cap τ' ∧ τ'.vars "iwd" = d ∧ Filled "ta" "iwn" (lvlWord K q ℓ c d) τ' := by
  obtain ⟨b1, b2, b3, b4⟩ := lvl_bounds (K := K) hℓ hdq
  -- the arity
  have r₀ := Run.assign (B := B) (σ := τ) (x := "iwa")
    (e := .sub (.add (.var "iwl") (.var "iwq")) (.var "iwd")) (v := ℓ + q - d)
    (evalB_bin (evalB_bin (evalB_var_of hC.hl (by omega)) (evalB_var_of hC.hq (by omega))
      (by simp; omega)) (evalB_var_of hd (by omega)) (by simp; omega))
  have C₀ := hC.setVar (y := "iwa") (by decide) (by decide) (by decide) (by decide) (ℓ + q - d)
  obtain ⟨τ₁, r₁, C₁, hrm₁, hrp₁, hd₁⟩ := powers_run (B := B) (d := d) C₀ (by simp [hd]) (by omega)
    (by omega) (by omega)
  have ha₁ : τ₁.vars "iwa" = ℓ + q - d := by rw [r₁.frame_var "iwa" (by decide)]; simp
  have hprev₁ : d = 0 ∨ ∃ d', d = d' + 1 ∧ Filled "ta" "iwn" (lvlWord K q ℓ c d') τ₁ := by
    rcases hprev with h | ⟨d', h, hW⟩
    · exact Or.inl h
    · refine Or.inr ⟨d', h, hW.congr ?_ ?_⟩
      · rw [r₁.frame_var "iwn" (by decide)]; simp
      · rw [r₁.frame_arr "ta" (by decide)]; simp
  obtain ⟨τ₂, T₂, r₂, hT₂, C₂, F₂⟩ := wLevel_run (B := B) C₁ hℓ hdq hd₁ ha₁ hrm₁ hrp₁ hprev₁ hcap hB
  have hlen := length_lvlWord K q ℓ c d
  obtain ⟨τ₃, r₃, C₃, F₃⟩ := copyBack_run (B := B) C₂ F₂ (by omega) (by omega)
    (fun v hv => by have := lvlWord_entries K q ℓ c hℓ d hdq v hv; omega)
  refine ⟨τ₃, _, Run.seq r₀ (Run.seq r₁ (Run.seq r₂ r₃)), ?_, C₃, ?_, F₃⟩
  · simp only [size_sub, size_add, size_var]
    rw [hlen]
    omega
  · rw [r₃.frame_var "iwd" (by decide), r₂.frame_var "iwd" (by decide), hd₁]

/-- **The initial tree, into `ta`.** -/
theorem buildInit_run {τ : Env} (hC : BCtx K q ℓ c cap τ) (hℓ : 1 ≤ ℓ)
    (hcap : lvlLen K q ℓ q ≤ cap) (hB : 4 * lvlLen K q ℓ q + c + 20 < B) :
    ∃ τ', Run B buildInit τ τ' ((q + 1) * (lvlCost (lvlLen K q ℓ q) + 100 * (lvlLen K q ℓ q + 1) +
        50 + 3 + 7) + 3 + 5) ∧
      BCtx K q ℓ c cap τ' ∧ Filled "ta" "iwn" (lvlWord K q ℓ c q) τ' := by
  obtain ⟨-, -, b3, -⟩ := lvl_bounds (K := K) hℓ (le_refl q)
  obtain ⟨τ', r, ⟨C', hF'⟩, -⟩ := forUp_run (B := B) (i := "iwd")
    (e := .add (.var "iwq") (.lit 1)) (body := levelBody) (N := q + 1)
    (K := lvlCost (lvlLen K q ℓ q) + 100 * (lvlLen K q ℓ q + 1) + 50)
    (fun d τ => BCtx K q ℓ c cap τ ∧
      (d = 0 ∨ ∃ d', d = d' + 1 ∧ Filled "ta" "iwn" (lvlWord K q ℓ c d') τ))
    (by omega)
    (fun k _ τ h _ => evalB_bin (evalB_var_of h.1.hq (by omega)) (evalB_lit (by omega))
      (by simp; omega))
    ⟨hC.setVar (by decide) (by decide) (by decide) (by decide) 0, Or.inl rfl⟩
    (by
      rintro d hd τ ⟨hτ, hprev⟩ hτd
      obtain ⟨τ₁, T, r, hT, C₁, hd₁, F₁⟩ := levelBody_run (B := B) hτ hℓ (by omega) hτd hprev hcap hB
      exact ⟨τ₁, r.mono hT, hd₁, C₁.setVar (by decide) (by decide) (by decide) (by decide) _,
        Or.inr ⟨d, rfl, F₁.setVar (by decide) _⟩⟩)
  refine ⟨τ', r.mono (by simp), C', ?_⟩
  rcases hF' with h | ⟨d', h, hW⟩
  · omega
  · obtain rfl : d' = q := by omega
    exact hW

/-- The word of the type tree of rank `(k, q)` of a constant tuple of
arity `ℓ ≥ 1` with color `c`, in `ta`. -/
theorem buildInit_initWord {k : ℕ} {τ : Env} (hC : BCtx (k + q) q ℓ c cap τ) (hℓ : 1 ≤ ℓ)
    (hcap : lvlLen (k + q) q ℓ q ≤ cap) (hB : 4 * lvlLen (k + q) q ℓ q + c + 20 < B) :
    ∃ τ', Run B buildInit τ τ' ((q + 1) * (lvlCost (lvlLen (k + q) q ℓ q) +
        100 * (lvlLen (k + q) q ℓ q + 1) + 60) + 8) ∧
      BCtx (k + q) q ℓ c cap τ' ∧ Filled "ta" "iwn" (initWord k q ℓ c) τ' := by
  obtain ⟨τ', r, C', F'⟩ := buildInit_run (B := B) hC hℓ hcap hB
  rw [lvlWord_top] at F'
  exact ⟨τ', r.mono (Nat.le_of_eq (by ring)), C', F'⟩

end Lax185574Proofs.MC
