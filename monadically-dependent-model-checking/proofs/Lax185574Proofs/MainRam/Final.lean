import Lax185574Proofs.MainRam.WordLength
import Lax185574Proofs.Interface.Shim.FewTypes
import Lax185574Proofs.Interface.Shim.ConstructionModelChecking

/-!
The assembly of thm:main from thm:skel-few-types and thm:mc, given the
glue programs by their specifications.

The program is the dovetailer over the threads. For a class, a sentence
and `ε`, the good thread is `(r, d, j)` with `r, d` from thm:mc and `j`
so large that `a (b + 1) / j ≤ min ε 1`, where `a` comes from
thm:skel-few-types and `b` from thm:mc. It accepts within
`O(n^(3+ε) + |x|)` steps. The dovetailer returns the answer of some
accepting thread, which ran within a polynomial of degree five in
`|x|`, and so at a word length where its own run of thm:mc is
admissible. That answer is the right one by `thread_sound`.

Both theorems are used in their older forms,
`Shim.FewTypes.exists_program_fewTypes` and the weak form
`Shim.ConstructionModelChecking.exists_program_modelChecking_sequence_weak`
of thm:mc. The time of the latter has a term linear in the length of its
input, which is `O(n^(3+ε) + |x|)` on the good thread.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Machine Lax185574Proofs.RamExec
open Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax3.FirstOrder Lax271696.GraphEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionSequences Lax185574.PartialGraphs Lax185574.InstanceEncoding
open Lax199508.GraphClasses Lax710763.MonadicDependence Lax185574.Width

/-- The choice of `j`: `a (b + 1) / j ≤ ε'`. -/
theorem exists_j {a b : ℕ} {ε' : ℝ} (hε' : 0 < ε') :
    1 ≤ a * (b + 1) * ⌈1 / ε'⌉₊ + 1 ∧
      (a : ℝ) * (b + 1) / ((a * (b + 1) * ⌈1 / ε'⌉₊ + 1 : ℕ) : ℝ) ≤ ε' := by
  refine ⟨by omega, ?_⟩
  set q : ℕ := a * (b + 1) * ⌈1 / ε'⌉₊ + 1
  have hq : (0 : ℝ) < q := by positivity
  rw [div_le_iff₀ hq]
  have hc : 1 / ε' ≤ (⌈1 / ε'⌉₊ : ℝ) := Nat.le_ceil _
  have hab : (0 : ℝ) ≤ (a : ℝ) * (b + 1) := by positivity
  have h1 : (a : ℝ) * (b + 1) = ε' * ((a : ℝ) * (b + 1) * (1 / ε')) := by
    field_simp
  have h2 : (a : ℝ) * (b + 1) * (1 / ε') ≤ q := by
    have : (a : ℝ) * (b + 1) * (1 / ε') ≤ (a : ℝ) * (b + 1) * ⌈1 / ε'⌉₊ :=
      mul_le_mul_of_nonneg_left hc hab
    have hq' : (q : ℝ) = (a : ℝ) * (b + 1) * ⌈1 / ε'⌉₊ + 1 := by simp [q]
    linarith
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 hε'.le

open Classical in
/-- Every halting run of the model-checking program on an admissible
instance outputs the answer. -/
theorem mcSound_of {M : Program} {e₂ : ℕ} {φ : FO 0} {r d c₂ b : ℕ}
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : List (PartialGraph (Fin n))) (K w : ℕ)
      (x : List ℕ), IsConstructionSequence G s → width r d s ≤ K →
      Lax185574.ConstructionModelChecking.EncodesInput x n G s φ →
      (∀ v ∈ x, c₂ * (x.length + v + 1) ^ e₂ ≤ 2 ^ w) →
        (∀ z t, RunsTo w M x z t → z = if Sat G Fin.elim0 φ then [1] else [0]) ∧
        (c₂ * s.length * (n + 1) ^ 2 * (K + 1) ^ b + c₂ * x.length ≤ 2 ^ w →
          ∃ t ≤ c₂ * s.length * (n + 1) ^ 2 * (K + 1) ^ b + c₂ * x.length,
            RunsTo w M x (if Sat G Fin.elim0 φ then [1] else [0]) t)) :
    MCSound M φ c₂ e₂ :=
  fun n G s z w hcs henc hadm => (h n G s (width r d s) w z hcs le_rfl henc hadm).1

/-- The last step of the time bound: a larger constant. -/
theorem conclude_le {T c₀ c n X : ℕ} {ε : ℝ} (hc : c₀ ≤ c)
    (h : T ≤ ⌊((c₀ : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + ε)⌋₊ + c₀ * X) :
    T ≤ ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + ε)⌋₊ + c * X := by
  have hP0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ ((3 : ℝ) + ε) := Real.rpow_nonneg (by positivity) _
  have hc' : ((c₀ : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hN1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hfl : ⌊((c₀ : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + ε)⌋₊ ≤
      ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + ε)⌋₊ := by
    rw [hN1]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hc' hP0)
  have hcX : c₀ * X ≤ c * X := Nat.mul_le_mul_right _ hc
  omega

set_option maxHeartbeats 1000000 in
open Classical in
/-- **thm:main from thm:skel-few-types and thm:mc**, given the glue
programs. -/
theorem modelChecking_of_glue {U Cl V Wr : Program} {cU cC cV cW : ℕ}
    (hU : UnpairSpec U cU) (hCl : ClipSpec Cl cC) (hV : ValidSpec V cV) (hWr : WrapSpec Wr cW) :
    ∃ (p : Program) (e : ℕ),
      ∀ (C : GraphClass), MonadicallyDependent C →
      ∀ (φ : FO 0) (ε : ℝ), 0 < ε →
        ∃ c : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
            ComputesInTime w p
              {x | EncodesInstance x n G φ ∧
                ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
              (fun _ => if Sat G Fin.elim0 φ then [1] else [0])
              (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + ε)⌋₊ + c * x.length) := by
  obtain ⟨pF, f, eF, hfc, hFcl⟩ := Lax185574Proofs.Shim.FewTypes.exists_program_fewTypes
  obtain ⟨pM, e₂, hMC⟩ :=
    Lax185574Proofs.Shim.ConstructionModelChecking.exists_program_modelChecking_sequence_weak
  obtain ⟨p, KD, hdv⟩ := dovetail 1 (threadProg U pF Cl V pM Wr)
  refine ⟨p, eF + 5 * e₂ + 20, fun C hC φ ε hε => ?_⟩
  set e := eF + 5 * e₂ + 20 with he
  obtain ⟨r₂, d₂, c₂, b, hmc⟩ := hMC φ
  have hMH : MCSound pM φ c₂ e₂ := mcSound_of hmc
  obtain ⟨a, ha1, ha⟩ := hFcl C hC d₂
  -- the good thread
  set ε' : ℝ := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨hj1, hab⟩ := exists_j (a := a) (b := b) hε'0
  set j : ℕ := a * (b + 1) * ⌈1 / ε'⌉₊ + 1 with hj
  set εq : ℚ := ((j : ℚ))⁻¹ with hεq
  have hεq0 : 0 < εq := by positivity
  have hεqr : ((εq : ℚ) : ℝ) = ((j : ℝ))⁻¹ := by simp [hεq]
  have hjinv : ((j : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hj1)
  -- the time exponent `3 + η` of thm:skel-few-types is taken with `η = ε = 1/j`
  obtain ⟨cF, hcF⟩ := ha r₂ εq hεq0 ((εq : ℚ) : ℝ) (by exact_mod_cast hεq0)
  set i := triIdx r₂ d₂ j with hi
  obtain ⟨hiR, hiD, hiJ⟩ := tri_idx r₂ d₂ j hj1
  -- the constants
  obtain ⟨CW, hCW⟩ : ∃ CW, CW = cU * (i + 2) ^ 2 + 9 * cF + c₂ * cF * (cF + 1) ^ b + 6 +
    c₂ * (3 * cF + 7) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = KD * 2 ^ i := ⟨_, rfl⟩
  obtain ⟨Kt, hKt⟩ : ∃ Kt, Kt = thK cC cV cW := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = A * (Kt * CW + 1) := ⟨_, rfl⟩
  obtain ⟨Cg₀, hCg₀⟩ : ∃ Cg₀, Cg₀ = thC cV * (6 * cF + 11) ^ 2 + c₂ * (12 * cF + 14) ^ e₂ +
    pipeK ρid ρU := ⟨_, rfl⟩
  obtain ⟨Cg, hCg⟩ : ∃ Cg, Cg = Cg₀ + 2 * CW := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = thC cV * (2 * c₀ + 11) ^ 2 + c₂ * (4 * c₀ + 14) ^ e₂ + 2 ^ 12 := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = Cg * 2 ^ (i + KD + 8) := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2, P2 = (cU * (i + 2) ^ 2 + cF * (i + 7) ^ eF) * 2 ^ (i + KD + 4) :=
    ⟨_, rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ P3, P3 = Cs * 2 ^ (KD + 8) * (2 * c₀) := ⟨_, rfl⟩
  have hP2U : cU * (i + 2) ^ 2 * 2 ^ (i + KD + 4) ≤ P2 := by
    rw [hP2]; exact Nat.mul_le_mul_right _ (by omega)
  have hP2F : cF * (i + 7) ^ eF * 2 ^ (i + KD + 4) ≤ P2 := by
    rw [hP2]; exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨c, hc⟩ : ∃ c, c = c₀ + P1 + P2 + P3 + 2 ^ (i + KD + 20) := ⟨_, rfl⟩
  have hcP : c₀ ≤ c ∧ P1 ≤ c ∧ P2 ≤ c ∧ P3 ≤ c ∧ 2 ^ (i + KD + 20) ≤ c := by
    have key : ∀ a₁ a₂ a₃ a₄ a₅ : ℕ, a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ ∧ a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ ∧
        a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ ∧ a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ ∧
        a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := by intros; omega
    rw [hc]; exact key _ _ _ _ _
  refine ⟨c, fun n G w hG x ⟨hx, hadm⟩ => ?_⟩
  obtain ⟨g, hg, rfl⟩ := hx
  set x := g ++ toWord φ with hxdef
  set X := x.length with hX
  have hgl := hg.length_eq
  have hng : n ≤ g.length := vertexCount_le hg
  have hXg : X = g.length + (toWord φ).length := by simp [hX, hxdef]
  -- admissibility of `x`
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ ∈ x := ⟨g.getD 0 0, by
    simp only [hxdef, List.mem_append]; left
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _⟩
  have hX1e : ∀ u ∈ x, (X + 1) ^ e ≤ (X + u + 1) ^ e := fun u _ =>
    Nat.pow_le_pow_left (by omega) _
  have hcw : c * (X + 1) ^ e ≤ 2 ^ w :=
    le_trans (Nat.mul_le_mul_left _ (hX1e g₀ hg₀)) (hadm g₀ hg₀)
  have hX1 : 1 ≤ (X + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hcpos : 2 ^ (i + KD + 20) ≤ c := hcP.2.2.2.2
  have hw20 : i + KD + 20 ≤ w :=
    le_of_two_pow_le (le_trans hcpos (le_trans (Nat.le_mul_of_pos_right _ hX1) hcw))
  have hXe : ∀ k ≤ e, (X + 1) ^ k ≤ (X + 1) ^ e := fun k hk => Nat.pow_le_pow_right (by omega) hk
  obtain ⟨wG, hwG⟩ : ∃ wG, wG = w - i - KD := ⟨_, rfl⟩
  -- the program of thm:skel-few-types on the good thread
  obtain ⟨xFT, hxFT⟩ : ∃ xFT, xFT = triWord i ++ g := ⟨_, rfl⟩
  have hxFTl : xFT.length = g.length + 5 := by simp [hxFT, triWord] <;> omega
  have hencFT : Lax185574.FewTypes.EncodesInput xFT r₂ d₂ εq n G := by
    refine ⟨g, hg, ?_⟩
    rw [hxFT, triWord_eq, hiR, hiD, hiJ]
  have hadmFT : ∀ v ∈ xFT, cF * (xFT.length + v + 1) ^ eF ≤ 2 ^ (wG - 4) := by
    intro v hv
    obtain ⟨u, hu, huv⟩ : ∃ u ∈ x, xFT.length + v + 1 ≤ (i + 7) * (X + u + 1) := by
      rw [hxFT, List.mem_append] at hv
      rcases hv with hv | hv
      · refine ⟨g₀, hg₀, ?_⟩
        have := triWord_le i v hv
        have h1 : X + g₀ ≤ (i + 7) * (X + g₀) := Nat.le_mul_of_pos_left _ (by omega)
        have h2 : (i + 7) * (X + g₀ + 1) = (i + 7) * (X + g₀) + (i + 7) := by ring
        omega
      · refine ⟨v, by simp [hxdef, hv], ?_⟩
        have h1 : 6 * (X + v + 1) ≤ (i + 7) * (X + v + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
    rw [hwG]
    apply good_fits
    calc cF * (xFT.length + v + 1) ^ eF * 2 ^ (i + KD + 4)
        ≤ cF * ((i + 7) * (X + u + 1)) ^ eF * 2 ^ (i + KD + 4) := by gcongr
      _ = cF * (i + 7) ^ eF * 2 ^ (i + KD + 4) * (X + u + 1) ^ eF := by rw [mul_pow]; ring
      _ ≤ c * (X + u + 1) ^ e := by
          apply Nat.mul_le_mul
          · exact le_trans hP2F hcP.2.2.1
          · exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 2 ^ w := hadm u hu
  obtain ⟨tF, htF, hrF⟩ := (hcF n G hG).1 (wG - 4) xFT ⟨hencFT, hadmFT⟩
  simp only at htF
  set y := f xFT with hy
  obtain ⟨⟨s, hs, hcs⟩, hye⟩ := hfc r₂ d₂ εq n G xFT hεq0 hencFT
  obtain ⟨hsl, hsw⟩ := (hcF n G hG).2 xFT s hencFT hs
  -- the length of the computed word
  have hyt : y.length ≤ tF := runsTo_out_length hrF
  have htF4 : tF ≤ 6 * cF * (X + 1) ^ 4 := by
    have h1 := floor_le_pow_four (cF := cF) (n := n) (δ := ((εq : ℚ) : ℝ)) (by rw [hεqr]; exact hjinv)
    have h2 : (n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h3 : X + 5 ≤ 5 * (X + 1) ^ 4 := by
      have : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
      omega
    have h4 : cF * xFT.length ≤ cF * (5 * (X + 1) ^ 4) := Nat.mul_le_mul_left _ (by omega)
    have h5 : cF * (n + 1) ^ 4 ≤ cF * (X + 1) ^ 4 := Nat.mul_le_mul_left _ h2
    have : 6 * cF * (X + 1) ^ 4 = cF * (X + 1) ^ 4 + cF * (5 * (X + 1) ^ 4) := by ring
    omega
  -- the width bound
  obtain ⟨Kw, hKw⟩ : ∃ Kw, Kw = ⌊(cF : ℝ) * ((n : ℝ) + 1) ^ ((a : ℝ) * ((εq : ℚ) : ℝ))⌋₊ := ⟨_, rfl⟩
  have hwK : width r₂ d₂ s ≤ Kw := by rw [hKw]; exact Nat.le_floor hsw
  obtain ⟨tMb, htMb⟩ : ∃ tMb, tMb = c₂ * s.length * (n + 1) ^ 2 * (Kw + 1) ^ b +
    c₂ * (mcIn n G φ g y).length := ⟨_, rfl⟩
  have hval : ValidScript n G y := by
    obtain ⟨σ, hσ, rfl⟩ := hs
    exact ⟨σ, hσ, hcs⟩
  obtain ⟨s', hs', -, hss'⟩ := mcIn_valid hg φ y hval
  rw [Lax185574Proofs.Compose.encodesSequence_unique hss' hs] at hs'
  have hMT : ∀ w' : ℕ,
      (∀ a ∈ mcIn n G φ g y, c₂ * ((mcIn n G φ g y).length + a + 1) ^ e₂ ≤ 2 ^ w') →
      tMb ≤ 2 ^ w' → ∃ t ≤ tMb, RunsTo w' pM (mcIn n G φ g y) (ansW G φ) t := by
    intro w' hadm' hfit
    rw [htMb] at hfit ⊢
    exact (hmc n G s Kw w' _ hcs hwK hs' hadm').2 hfit
  -- the size conditions of the good thread
  have hyX : y.length + X + 10 ≤ (6 * cF + 11) * (X + 1) ^ 4 := by
    have : X + 10 ≤ 11 * (X + 1) ^ 4 := by
      have : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
      omega
    have : (6 * cF + 11) * (X + 1) ^ 4 = 6 * cF * (X + 1) ^ 4 + 11 * (X + 1) ^ 4 := by ring
    omega
  have hBg : thC cV * (y.length + X + 10) ^ 2 + c₂ * (2 * (y.length + X) + 12) ^ e₂ +
      pipeK ρid ρU ≤ Cg * (X + 1) ^ e := by
    have h1 : (y.length + X + 10) ^ 2 ≤ (6 * cF + 11) ^ 2 * (X + 1) ^ e := by
      calc (y.length + X + 10) ^ 2 ≤ ((6 * cF + 11) * (X + 1) ^ 4) ^ 2 :=
            Nat.pow_le_pow_left hyX 2
        _ = (6 * cF + 11) ^ 2 * (X + 1) ^ 8 := by ring
        _ ≤ (6 * cF + 11) ^ 2 * (X + 1) ^ e := Nat.mul_le_mul_left _ (hXe 8 (by omega))
    have h2 : (2 * (y.length + X) + 12) ^ e₂ ≤ (12 * cF + 14) ^ e₂ * (X + 1) ^ e := by
      calc (2 * (y.length + X) + 12) ^ e₂ ≤ ((12 * cF + 14) * (X + 1) ^ 4) ^ e₂ := by
            apply Nat.pow_le_pow_left
            have : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
            have : (12 * cF + 14) * (X + 1) ^ 4 = 2 * (6 * cF * (X + 1) ^ 4) + 14 * (X + 1) ^ 4 := by
              ring
            omega
        _ = (12 * cF + 14) ^ e₂ * (X + 1) ^ (4 * e₂) := by rw [mul_pow, ← pow_mul]
        _ ≤ (12 * cF + 14) ^ e₂ * (X + 1) ^ e := Nat.mul_le_mul_left _ (hXe _ (by omega))
    have h3 : pipeK ρid ρU ≤ pipeK ρid ρU * (X + 1) ^ e := Nat.le_mul_of_pos_right _ hX1
    calc thC cV * (y.length + X + 10) ^ 2 + c₂ * (2 * (y.length + X) + 12) ^ e₂ + pipeK ρid ρU
        ≤ thC cV * ((6 * cF + 11) ^ 2 * (X + 1) ^ e) +
            c₂ * ((12 * cF + 14) ^ e₂ * (X + 1) ^ e) + pipeK ρid ρU * (X + 1) ^ e := by
          gcongr
      _ = Cg₀ * (X + 1) ^ e := by rw [hCg₀]; ring
      _ ≤ Cg * (X + 1) ^ e := Nat.mul_le_mul_right _ (by omega)
  have hgood : ∀ B, B ≤ Cg * (X + 1) ^ e → B ≤ 2 ^ (wG - 8) := by
    intro B hB
    rw [hwG]
    apply good_fits
    calc B * 2 ^ (i + KD + 8) ≤ Cg * (X + 1) ^ e * 2 ^ (i + KD + 8) := Nat.mul_le_mul_right _ hB
      _ = Cg * 2 ^ (i + KD + 8) * (X + 1) ^ e := by ring
      _ ≤ c * (X + 1) ^ e := Nat.mul_le_mul_right _ (by rw [← hP1]; exact hcP.2.1)
      _ ≤ 2 ^ w := hcw
  have hUadm : ∀ v ∈ i :: x, cU * (i + v + 2) ^ 2 ≤ 2 ^ (wG - 4) := by
    intro v hv
    obtain ⟨u, hu, huv⟩ : ∃ u ∈ x, i + v + 2 ≤ (i + 2) * (X + u + 1) := by
      rcases List.mem_cons.mp hv with rfl | hv
      · refine ⟨g₀, hg₀, ?_⟩
        have h1 : 2 * (i + 2) ≤ (i + 2) * (X + g₀ + 1) := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      · refine ⟨v, hv, ?_⟩
        have h1 : (i + 2) * (v + 1) ≤ (i + 2) * (X + v + 1) := Nat.mul_le_mul_left _ (by omega)
        have h2 : (i + 2) * (v + 1) = i * v + i + 2 * v + 2 := by ring
        have h3 : 0 ≤ i * v := Nat.zero_le _
        omega
    rw [hwG]
    apply good_fits
    calc cU * (i + v + 2) ^ 2 * 2 ^ (i + KD + 4) ≤ cU * ((i + 2) * (X + u + 1)) ^ 2 *
          2 ^ (i + KD + 4) := by gcongr
      _ = cU * (i + 2) ^ 2 * 2 ^ (i + KD + 4) * (X + u + 1) ^ 2 := by rw [mul_pow]; ring
      _ ≤ c * (X + u + 1) ^ e := by
          apply Nat.mul_le_mul
          · exact le_trans hP2U hcP.2.2.1
          · exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 2 ^ w := hadm u hu
  -- the good thread accepts
  have hb1 : thC cV * (y.length + X + 10) ^ 2 ≤ 2 ^ (wG - 8) := hgood _ (by omega)
  have hb2 : pipeK ρid ρU ≤ 2 ^ (wG - 8) := hgood _ (by omega)
  have hb3 : c₂ * (2 * (y.length + X) + 12) ^ e₂ ≤ 2 ^ (wG - 8) := hgood _ (by omega)
  -- the work of the good thread
  have hN1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have htF' : tF ≤ ⌊(cF : ℝ) * ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + ((j : ℝ))⁻¹)⌋₊ + cF * (X + 5) := by
    rw [hN1, ← hεqr]
    have : cF * xFT.length ≤ cF * (X + 5) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hm' : (s.length : ℝ) ≤ cF * ((n + 1 : ℕ) : ℝ) ^ (1 + (a : ℝ) * ((j : ℝ))⁻¹) := by
    rw [hN1, ← hεqr]; exact hsl
  have hKw' : Kw = ⌊(cF : ℝ) * ((n + 1 : ℕ) : ℝ) ^ ((a : ℝ) * ((j : ℝ))⁻¹)⌋₊ := by
    rw [hN1, ← hεqr]; exact hKw
  have hyl : y.length ≤ 3 * s.length + (n + 1) := by
    have : y.length ≤ 3 * s.length + n := length_le_of_encodesSequence hs
    omega
  have hWg := good_time_le (N := n + 1) (X := X) (i := i) (cU := cU) (tMb := tMb) (yl := y.length)
    (by omega) hj1 hε'1 ha1 hab hε'0 htF' hm' hKw' hyl (by
      rw [htMb]
      have := mcIn_length_le n G φ g y
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left c₂ (show (mcIn n G φ g y).length ≤ X + y.length + 5 by omega)) _)
  rw [← hCW] at hWg
  have hNX : n + 1 ≤ X + 1 := by omega
  -- the time bound of thm:mc fits on the good thread
  have htMbX : tMb ≤ 2 * CW * (X + 1) ^ 4 := by
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hPn : ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + ε') ≤ (((X + 1) ^ 4 : ℕ) : ℝ) := by
      calc ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) + ε') ≤ ((n + 1 : ℕ) : ℝ) ^ ((4 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
        _ = (((n + 1) ^ 4 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
        _ ≤ (((X + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast Nat.pow_le_pow_left hNX 4
    have hX4 : X ≤ (X + 1) ^ 4 := le_trans (Nat.le_succ X) (Nat.le_self_pow (by norm_num) _)
    have hX4r : (X : ℝ) ≤ (((X + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hX4
    have hle : ((tMb : ℕ) : ℝ) ≤
        ((cU * (i + 2) ^ 2 + tF + (y.length + 1) * (n + 1) ^ 2 + X + tMb + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    have hCW0 : (0 : ℝ) ≤ CW := Nat.cast_nonneg _
    have h1 : ((tMb : ℕ) : ℝ) ≤ CW * ((((X + 1) ^ 4 : ℕ) : ℝ) + (((X + 1) ^ 4 : ℕ) : ℝ)) := by
      refine le_trans hle (le_trans hWg ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) hCW0
    have h2 : ((tMb : ℕ) : ℝ) ≤ ((2 * CW * (X + 1) ^ 4 : ℕ) : ℝ) := by
      push_cast at h1 ⊢; linarith
    exact_mod_cast h2
  have hfitM : tMb ≤ 2 ^ (wG - 8) := hgood _ (by
    have h1 : 2 * CW * (X + 1) ^ 4 ≤ 2 * CW * (X + 1) ^ e := Nat.mul_le_mul_left _ (hXe 4 (by omega))
    have h2 : Cg * (X + 1) ^ e = Cg₀ * (X + 1) ^ e + 2 * CW * (X + 1) ^ e := by rw [hCg]; ring
    omega)
  obtain ⟨tQ, htQ, hrQ⟩ := thread_complete hU hCl hV hWr hg i wG (by omega) y tF
    (by rw [← hxFT]; exact hrF) s hs hcs hye tMb hMT hfitM hUadm hb1 hb2 hb3
  -- the dovetailer halts
  have hxw : x.length < 2 ^ (w - 1) := by
    have h1 : 2 ^ 20 * (X + 1) ≤ 2 ^ w := by
      calc 2 ^ 20 * (X + 1) ≤ c * (X + 1) ^ e := by
            apply Nat.mul_le_mul
            · exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcpos
            · exact Nat.le_self_pow (by omega) _
        _ ≤ 2 ^ w := hcw
    have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  obtain ⟨i', y', t', T, hi', -, hR', hbd, hpT, hTb⟩ :=
    hdv w x i [ansB G φ] tQ (by omega) hxw (by simp) (by rw [← hwG]; exact hrQ)
  rw [← hA] at hbd hTb
  have hfin := final_time_le (N := n + 1) (X := X) (K := Kt) (CW := CW) (by omega) hNX hε'0 hε'1
    hε'ε (by exact_mod_cast hWg) (by rw [hKt]; exact htQ) hTb
  have hfinD := final_time_le (N := n + 1) (X := X) (K := Kt) (CW := CW) (T := A * (tQ + 1))
    (by omega) hNX hε'0 hε'1 hε'ε (by exact_mod_cast hWg) (by rw [hKt]; exact htQ) le_rfl
  rw [← hc₀] at hfin hfinD
  -- the accepting thread is sound
  have ht'0 : 0 < t' := alive_lt (c := 0) rfl (Or.inr rfl) hR'
  set Dn := 2 * c₀ * (X + 1) ^ 5 with hDn
  have hD : A * (tQ + 1) ≤ Dn := hfinD.2
  have h2i : 2 ^ i' ≤ A * (tQ + 1) :=
    le_trans (Nat.le_mul_of_pos_right _ ht'0) hbd
  have ht'D : t' ≤ Dn :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hbd) hD
  have hX5 : X + 1 ≤ (X + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  obtain ⟨E, hE⟩ : ∃ E, E = (X + 1) ^ (10 + 5 * e₂) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Nat.one_le_pow _ _ (by omega)
  have hE10 : (X + 1) ^ 10 ≤ E := by rw [hE]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hE5 : (X + 1) ^ (5 * e₂) ≤ E := by rw [hE]; exact Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = thC cV * (t' + X + 10) ^ 2 + c₂ * (2 * (t' + X) + 12) ^ e₂ +
    2 ^ 12 := ⟨_, rfl⟩
  have hBs' : Bs ≤ Cs * E := by
    have k1 : t' + X + 10 ≤ (2 * c₀ + 11) * (X + 1) ^ 5 := by
      have : (2 * c₀ + 11) * (X + 1) ^ 5 = Dn + 11 * (X + 1) ^ 5 := by rw [hDn]; ring
      omega
    have k2 : 2 * (t' + X) + 12 ≤ (4 * c₀ + 14) * (X + 1) ^ 5 := by
      have : (4 * c₀ + 14) * (X + 1) ^ 5 = 2 * Dn + 14 * (X + 1) ^ 5 := by rw [hDn]; ring
      omega
    have q1 : (t' + X + 10) ^ 2 ≤ (2 * c₀ + 11) ^ 2 * E :=
      calc (t' + X + 10) ^ 2 ≤ ((2 * c₀ + 11) * (X + 1) ^ 5) ^ 2 := Nat.pow_le_pow_left k1 2
        _ = (2 * c₀ + 11) ^ 2 * (X + 1) ^ 10 := by ring
        _ ≤ (2 * c₀ + 11) ^ 2 * E := Nat.mul_le_mul_left _ hE10
    have q2 : (2 * (t' + X) + 12) ^ e₂ ≤ (4 * c₀ + 14) ^ e₂ * E :=
      calc (2 * (t' + X) + 12) ^ e₂ ≤ ((4 * c₀ + 14) * (X + 1) ^ 5) ^ e₂ :=
            Nat.pow_le_pow_left k2 _
        _ = (4 * c₀ + 14) ^ e₂ * (X + 1) ^ (5 * e₂) := by rw [mul_pow, ← pow_mul]
        _ ≤ (4 * c₀ + 14) ^ e₂ * E := Nat.mul_le_mul_left _ hE5
    have q3 : (2 : ℕ) ^ 12 ≤ 2 ^ 12 * E := Nat.le_mul_of_pos_right _ hE1
    have q4 : thC cV * (t' + X + 10) ^ 2 ≤ thC cV * ((2 * c₀ + 11) ^ 2 * E) :=
      Nat.mul_le_mul_left _ q1
    have q5 : c₂ * (2 * (t' + X) + 12) ^ e₂ ≤ c₂ * ((4 * c₀ + 14) ^ e₂ * E) :=
      Nat.mul_le_mul_left _ q2
    have q6 : Cs * E = thC cV * ((2 * c₀ + 11) ^ 2 * E) + c₂ * ((4 * c₀ + 14) ^ e₂ * E) +
        2 ^ 12 * E := by rw [hCs]; ring
    rw [hBs, q6]
    omega
  have hBw : Bs * 2 ^ (KD + 8) * (A * (tQ + 1)) ≤ 2 ^ w := by
    calc Bs * 2 ^ (KD + 8) * (A * (tQ + 1)) ≤ Cs * E * 2 ^ (KD + 8) * Dn := by
          gcongr
      _ = P3 * (X + 1) ^ (15 + 5 * e₂) := by rw [hP3, hDn, hE]; ring
      _ ≤ c * (X + 1) ^ e := Nat.mul_le_mul hcP.2.2.2.1 (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ 2 ^ w := hcw
  obtain ⟨hw20', hBfit⟩ := sound_fits hi' h2i (by rw [hBs]; omega) hBw
  have hy' : y' = [ansB G φ] := thread_sound hCl hV hWr hMH hg i' (w - i' - KD) t' y' (by omega)
    (le_trans (show thC cV * (t' + X + 10) ^ 2 ≤ Bs by rw [hBs]; omega) hBfit)
    (le_trans (show c₂ * (2 * (t' + X) + 12) ^ e₂ ≤ Bs by rw [hBs]; omega) hBfit) hR'
  -- the conclusion
  rw [hy', ← ansW_eq] at hpT
  exact ⟨T, conclude_le hcP.1 hfin.1, hpT⟩

end Lax185574Proofs.MainRam
