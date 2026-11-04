import Lax185574Proofs.RamSwitch

/-!
Five callees in one program.

The resolve lift calls five opaque programs: the scatter type, the rank
shift, the far tree, the composition and the canonical form. Its callee
runs all five, each on its own query, and returns the five outputs one
after the other. A caller that needs only one of them gives the others
small fixed queries.

The program is `switch (switch A B C D) E F D`. The query is
`sw5In qA qB qC qE qF = swIn (swIn qA qB qC) qE qF`. The inner switch runs
at word length `w − 4 − D`, so `A`, `B` and `C` run at `w − 8 − 2D`,
`w − 10 − 2D` and `w − 12 − 2D`, and `E`, `F` at `w − 6 − D` and
`w − 8 − D`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574Proofs.RamCat Lax185574Proofs.Simulate

/-- The query of the five callees. -/
def sw5In (qA qB qC qE qF : List ℕ) : List ℕ := swIn (swIn qA qB qC) qE qF

theorem catLim_ge {v E : ℕ} (h : E ≤ v) : 2 ^ (v - E) - 1 ≤ catLim v E := by
  have hv : 2 ^ v = 2 ^ E * 2 ^ (v - E) := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (v - E) := Nat.one_le_two_pow
  simp only [catLim]
  rw [Nat.le_div_iff_mul_le (by positivity), hv]
  have : (2 ^ (v - E) - 1) * 2 ^ E = 2 ^ E * 2 ^ (v - E) - 2 ^ E := by
    rw [Nat.sub_mul, one_mul, Nat.mul_comm]
  omega

theorem length_swIn_le (qA qB qC qE qF : List ℕ) :
    (swIn qA qB qC).length ≤ (sw5In qA qB qC qE qF).length := by
  simp only [sw5In, swIn, List.length_append, List.length_cons, List.length_nil]; omega

/-- **Five callees.** -/
theorem switch5 (A B C E F : Program) (D : ℕ) (hD : 4 ≤ D) : ∃ (p : Program) (K : ℕ),
    ∀ (w : ℕ) (qA qB qC qE qF : List ℕ), K ≤ 2 ^ (w - 12 - 2 * D) →
      (sw5In qA qB qC qE qF).length < 2 ^ (w - 14 - 2 * D) → 2 * D + 18 ≤ w →
      (∀ yA yB yC yE yF tA tB tC tE tF,
        RunsTo (w - 8 - 2 * D) A qA yA tA → RunsTo (w - 10 - 2 * D) B qB yB tB →
        RunsTo (w - 12 - 2 * D) C qC yC tC → RunsTo (w - 6 - D) E qE yE tE →
        RunsTo (w - 8 - D) F qF yF tF →
        yA.length ≤ catLim (w - 8 - D) (D + 2) → yB.length ≤ catLim (w - 10 - D) (D + 2) →
        yC.length ≤ catLim (w - 12 - D) (D + 2) → yE.length ≤ catLim (w - 6) (D + 2) →
        yF.length ≤ catLim (w - 8) (D + 2) →
        ∃ t ≤ K * (tA + tB + tC + tE + tF + yA.length + yB.length + yC.length + yE.length +
            yF.length + 1),
          RunsTo w p (sw5In qA qB qC qE qF) (yA ++ yB ++ yC ++ yE ++ yF) t) ∧
      (∀ o T, RunsTo w p (sw5In qA qB qC qE qF) o T →
        ∃ yA yB yC yE yF tA tB tC tE tF,
          RunsTo (w - 8 - 2 * D) A qA yA tA ∧ RunsTo (w - 10 - 2 * D) B qB yB tB ∧
          RunsTo (w - 12 - 2 * D) C qC yC tC ∧ RunsTo (w - 6 - D) E qE yE tE ∧
          RunsTo (w - 8 - D) F qF yF tF ∧ o = yA ++ yB ++ yC ++ yE ++ yF ∧
          yA.length ≤ catLim (w - 8 - D) (D + 2) ∧ yB.length ≤ catLim (w - 10 - D) (D + 2) ∧
          yC.length ≤ catLim (w - 12 - D) (D + 2) ∧ yE.length ≤ catLim (w - 6) (D + 2) ∧
          yF.length ≤ catLim (w - 8) (D + 2)) := by
  obtain ⟨pX, K₁, h₁⟩ := switch A B C D hD
  obtain ⟨p, K₂, h₂⟩ := switch pX E F D hD
  refine ⟨p, K₂ * (K₁ + 2) + K₁ + K₂ + 1, fun w qA qB qC qE qF hK hx hw => ?_⟩
  have e12 : 2 ^ (w - 12 - 2 * D) ≤ 2 ^ (w - 8 - D) := pow_mono (by omega)
  have e14 : 2 ^ (w - 14 - 2 * D) ≤ 2 ^ (w - 10 - D) := pow_mono (by omega)
  have hin := length_swIn_le qA qB qC qE qF
  obtain ⟨hif, hib⟩ := h₁ (w - 4 - D) qA qB qC
    (by rw [show w - 4 - D - 8 - D = w - 12 - 2 * D by omega]; omega)
    (by rw [show w - 4 - D - 10 - D = w - 14 - 2 * D by omega]; omega) (by omega)
  simp only [show w - 4 - D - 4 = w - 8 - D by omega, show w - 4 - D - 6 = w - 10 - D by omega,
    show w - 4 - D - 8 = w - 12 - D by omega, show w - 8 - D - D = w - 8 - 2 * D by omega,
    show w - 10 - D - D = w - 10 - 2 * D by omega,
    show w - 12 - D - D = w - 12 - 2 * D by omega] at hif hib
  have hxo : (swIn (swIn qA qB qC) qE qF).length < 2 ^ (w - 10 - D) := lt_of_lt_of_le hx e14
  obtain ⟨hof, hob⟩ := h₂ w (swIn qA qB qC) qE qF (by omega) hxo (by omega)
  -- the inner outputs fit the cap of the outer switch
  have cA := catLim_lt_pow (v := w - 8 - D) (E := D + 2) (by omega)
  have cB := catLim_lt_pow (v := w - 10 - D) (E := D + 2) (by omega)
  have cC := catLim_lt_pow (v := w - 12 - D) (E := D + 2) (by omega)
  have cX := catLim_ge (v := w - 4) (E := D + 2) (by omega)
  have pB : 2 ^ (w - 10 - D - (D + 2)) ≤ 2 ^ (w - 8 - D - (D + 2)) := pow_mono (by omega)
  have pC : 2 ^ (w - 12 - D - (D + 2)) ≤ 2 ^ (w - 8 - D - (D + 2)) := pow_mono (by omega)
  have p16 : 2 ^ (w - 4 - (D + 2)) = 2 ^ (D + 4) * 2 ^ (w - 8 - D - (D + 2)) := by
    rw [← pow_add]; congr 1; omega
  have p16' : 16 ≤ 2 ^ (D + 4) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (D + 4) := pow_mono (by omega)
  have hsum : ∀ yA yB yC : List ℕ, yA.length ≤ catLim (w - 8 - D) (D + 2) →
      yB.length ≤ catLim (w - 10 - D) (D + 2) → yC.length ≤ catLim (w - 12 - D) (D + 2) →
      (yA ++ yB ++ yC).length ≤ catLim (w - 4) (D + 2) := by
    intro yA yB yC ha hb hc
    simp only [List.length_append]
    have := Nat.mul_le_mul_right (2 ^ (w - 8 - D - (D + 2))) p16'
    omega
  refine ⟨fun yA yB yC yE yF tA tB tC tE tF rA rB rC rE rF la lb lc lE lf => ?_,
    fun o T ho => ?_⟩
  · obtain ⟨tX, htX, rX⟩ := hif yA yB yC tA tB tC rA rB rC la lb lc
    obtain ⟨t, ht, r⟩ :=
      hof (yA ++ yB ++ yC) yE yF tX tE tF rX rE rF (hsum _ _ _ la lb lc) lE lf
    refine ⟨t, le_trans ht ?_, r⟩
    simp only [List.length_append]
    obtain ⟨S, hS⟩ : ∃ S, tA + tB + tC + tE + tF + yA.length + yB.length + yC.length +
        yE.length + yF.length + 1 = S := ⟨_, rfl⟩
    rw [hS]
    have hX : tX ≤ K₁ * S := le_trans htX (Nat.mul_le_mul_left _ (by omega))
    have : tX + tE + tF + (yA.length + yB.length + yC.length) + yE.length + yF.length + 1 ≤
        (K₁ + 2) * S := by
      have : (K₁ + 2) * S = K₁ * S + 2 * S := by ring
      omega
    calc K₂ * (tX + tE + tF + (yA.length + yB.length + yC.length) + yE.length + yF.length + 1)
        ≤ K₂ * ((K₁ + 2) * S) := Nat.mul_le_mul_left _ this
      _ = (K₂ * (K₁ + 2)) * S := by ring
      _ ≤ (K₂ * (K₁ + 2) + K₁ + K₂ + 1) * S := Nat.mul_le_mul_right _ (by omega)
  · obtain ⟨y, yE, yF, tX, tE, tF, rX, rE, rF, rfl, -, lE, lf⟩ := hob o T ho
    obtain ⟨yA, yB, yC, tA, tB, tC, rA, rB, rC, rfl, la, lb, lc⟩ := hib y tX rX
    exact ⟨yA, yB, yC, yE, yF, tA, tB, tC, tE, tF, rA, rB, rC, rE, rF, rfl, la, lb, lc, lE, lf⟩

end Lax185574Proofs.ResolveRam
