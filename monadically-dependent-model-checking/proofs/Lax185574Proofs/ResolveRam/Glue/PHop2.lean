import Lax185574Proofs.ResolveRam.Glue.PHop

/-!
The test `hop2W` on two atom lists held in arrays.

`hop2C A₁ A₂` runs the pair test `pairC` over all radii `s₁, s₂ ≤ s`
(`ta`, `tb`, with `s` in `ts`) and leaves in `tw` the value of `hop2W`
between position `ti1` of the atom list at `tp1` of `A₁` and position
`ti2` of the atom list at `tp2` of `A₂` (`hop2C_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

/-- The loop over the second radius. -/
def innerC (A₁ A₂ : String) : Com := anyLoop "tb" "tn" "tu" "tv" (pairC A₁ A₂)

/-- One round of the loop over the first radius. -/
def outerB (A₁ A₂ : String) : Com := .seq (.assign "tu" (.lit 0)) (innerC A₁ A₂)

/-- **The test `hop2W`.** -/
def hop2C (A₁ A₂ : String) : Com :=
  .seq (.assign "tn" (.add (.var "ts") (.lit 1))) (.seq (.assign "tw" (.lit 0))
    (anyLoop "ta" "tn" "tw" "tu" (outerB A₁ A₂)))

/-- The scalars that `hop2C` writes. -/
def hV : List String := pV ++ ["ta", "tb", "tn", "tu", "tw"]

theorem hop2C_wvars (A₁ A₂ : String) : ∀ y ∈ (hop2C A₁ A₂).wvars, y ∈ hV := by
  have := pairC_wvars A₁ A₂
  intro y hy
  by_cases hp : y ∈ (pairC A₁ A₂).wvars
  · exact List.mem_append_left _ (this y hp)
  · simp only [hop2C, outerB, innerC, anyLoop, forUp, Com.wvars, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.append_nil, hp, false_or] at hy
    simp only [hV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

theorem hop2C_warrs (A₁ A₂ : String) : (hop2C A₁ A₂).warrs = [] := by
  simp [hop2C, outerB, innerC, anyLoop, forUp, Com.warrs, pairC_warrs]

theorem hop2C_reads (A₁ A₂ : String) : ¬ (hop2C A₁ A₂).reads := by
  have := pairC_reads A₁ A₂
  simp_all [hop2C, outerB, innerC, anyLoop, forUp, Com.reads]

theorem hop2C_noWrite (A₁ A₂ : String) : (hop2C A₁ A₂).NoWrite := by
  have := pairC_noWrite A₁ A₂
  simp_all [hop2C, outerB, innerC, anyLoop, forUp, Com.NoWrite]

theorem hopAt_setVar {A₁ A₂ : String} {X₁ X₂ : List ℕ} {ws₁ ws₂ : List (List ℕ)} {p₁ p₂ : ℕ}
    {Dw : DW} {i j s : ℕ} {τ : Env} (h : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ) {z : String}
    (hz : z ∉ rN) (x : ℕ) : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s (τ.setVar z x) :=
  h.congr (fun y hy => by
    have : y ≠ z := fun e => hz (e ▸ hy)
    simp [this]) (by simp)

/-- The cost of `hop2C`. -/
def hopK (L s : ℕ) : ℕ := (s + 2) * (s + 2) * (140 * L + 500)

/-- **The test `hop2W`.** -/
theorem hop2C_run {B : ℕ} {A₁ A₂ : String} {X₁ X₂ : List ℕ} {ws₁ ws₂ : List (List ℕ)}
    {p₁ p₂ : ℕ} {r₁ r₂ : List ℕ} {Dw : DW} {i j s : ℕ} {τ : Env}
    (hH : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ) (hd₁ : X₁.drop p₁ = toWord ws₁ ++ r₁)
    (hd₂ : X₂.drop p₂ = toWord ws₂ ++ r₂) (hb : HopB B p₁ p₂ ws₁ ws₂ Dw i j s) :
    ∃ τ', Run B (hop2C A₁ A₂) τ τ' (hopK (ws₁.length + ws₂.length) s) ∧
      τ'.vars "tw" = bv (hop2W Dw ws₁ i ws₂ j s) ∧
      (∀ y, y ∉ hV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hsB := hb.s
  set L := ws₁.length + ws₂.length
  set N := s + 1
  set Kp := 140 * L + 400
  set f : ℕ → ℕ → Bool := fun s₁ s₂ => pairB ws₁ ws₂ Dw.P Dw.Q Dw.cP Dw.cQ i j s s₁ s₂
  -- the inner loop
  have hin : ∀ (c : ℕ) (w0 : ℕ), c < N → Spec B (fun τ => HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ ∧
        τ.vars "ta" = c ∧ τ.vars "tn" = N ∧ τ.vars "tw" = w0) (outerB A₁ A₂)
      (fun τ τ' => HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ' ∧ τ'.vars "ta" = c ∧
        τ'.vars "tn" = N ∧ τ'.vars "tw" = τ.vars "tw" ∧
        τ'.vars "tu" = bv ((List.range N).any (f c))) (N * (Kp + 20) + 9) := by
    rintro c w0 hc τ0 ⟨H0, a0, n0, w00⟩
    let C : Env → Prop := fun τ => HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ ∧
      τ.vars "ta" = c ∧ τ.vars "tw" = w0
    have hCs : ∀ τ (z : String) x, z ∈ ["tb", "tu"] → C τ → C (τ.setVar z x) := by
      intro τ z x hz ⟨h1, h2, h3⟩
      have h4 : z ≠ "ta" := by simp at hz; rcases hz with rfl | rfl <;> decide
      have h5 : z ≠ "tw" := by simp at hz; rcases hz with rfl | rfl <;> decide
      exact ⟨hopAt_setVar h1 (by simp at hz; rcases hz with rfl | rfl <;> decide) x,
        by simp [Ne.symm h4, h2], by simp [Ne.symm h5, h3]⟩
    set τ1 := τ0.setVar "tu" 0
    have r1 : Run B (.assign "tu" (.lit 0)) τ0 τ1 2 := Run.assign (evalB_lit (by omega))
    obtain ⟨τ2, r2, ⟨H2, a2, w2⟩, u2, n2⟩ := anyLoop_run (B := B) (i := "tb") (n := "tn") (flag := "tu")
      (v := "tv") (body := pairC A₁ A₂) C (f c) N Kp (by omega) (by decide) (by decide) (by decide)
      (fun τ x h => hCs τ "tb" x (by simp) h) (fun τ x h => hCs τ "tu" x (by simp) h)
      (by
        rintro c2 hc2 τ ⟨⟨Hτ, aτ, wτ⟩, bτ, nτ, -⟩
        obtain ⟨τ', r', v', f', a', o', i'⟩ := pairC_run Hτ hd₁ hd₂ hb aτ bτ (by omega) (by omega)
        have k : ∀ y ∈ rN ++ ["ta", "tb", "tn", "tu", "tw"], y ∉ pV := by decide
        exact ⟨τ', r', ⟨Hτ.congr (fun y hy => f' y (k y (List.mem_append_left _ hy))) a',
          by rw [f' _ (k _ (by simp)), aτ], by rw [f' _ (k _ (by simp)), wτ]⟩,
          by rw [f' _ (k _ (by simp)), bτ], by rw [f' _ (k _ (by simp)), nτ],
          f' _ (k _ (by simp)), v'⟩)
      τ1 ⟨hCs τ0 "tu" 0 (by simp) ⟨H0, a0, w00⟩, by simp [τ1, n0], by simp [τ1]⟩
    refine ⟨τ2, ?_, H2, a2, n2, by rw [w2, w00], u2⟩
    unfold outerB innerC
    exact (Run.seq r1 r2).mono (by omega)
  -- the outer loop
  set τ1 := τ.setVar "tn" N
  set τ2 := τ1.setVar "tw" 0
  have r1 : Run B (.assign "tn" (.add (.var "ts") (.lit 1))) τ τ1 4 :=
    (Run.assign (ev_add (ev_var hH.s (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have r2 : Run B (.assign "tw" (.lit 0)) τ1 τ2 2 := Run.assign (evalB_lit (by omega))
  have hτ2 : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ2 :=
    hopAt_setVar (hopAt_setVar hH (by decide) N) (by decide) 0
  obtain ⟨τ3, r3, H3, w3, n3⟩ := anyLoop_run (B := B) (i := "ta") (n := "tn") (flag := "tw")
    (v := "tu") (body := outerB A₁ A₂) (HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s)
    (fun c => (List.range N).any (f c)) N (N * (Kp + 20) + 9) (by omega) (by decide) (by decide)
    (by decide) (fun τ x h => hopAt_setVar h (by decide) x) (fun τ x h => hopAt_setVar h (by decide) x)
    (by
      rintro c hc τ' ⟨Hτ, aτ, nτ, -⟩
      obtain ⟨τ'', r'', H'', a'', n'', w'', u''⟩ := hin c (τ'.vars "tw") hc τ' ⟨Hτ, aτ, nτ, rfl⟩
      exact ⟨τ'', r'', H'', a'', n'', w'', u''⟩)
    τ2 ⟨hτ2, by simp [τ2, τ1], by simp [τ2]⟩
  have hrun : Run B (hop2C A₁ A₂) τ τ3 (hopK L s) := by
    unfold hop2C
    refine (Run.seq r1 (Run.seq r2 r3)).mono ?_
    simp only [hopK, Kp, N]
    nlinarith
  obtain ⟨fa, fo, fi⟩ := run_frame hrun (hop2C_warrs A₁ A₂) (hop2C_reads A₁ A₂) (hop2C_noWrite A₁ A₂)
  refine ⟨τ3, hrun, by rw [w3, hop2W_pairB], fun y hy => hrun.frame_var y
    (fun h => hy (hop2C_wvars A₁ A₂ y h)), fa, fo, fi⟩

end Lax185574Proofs.ResolveRam.Glue
