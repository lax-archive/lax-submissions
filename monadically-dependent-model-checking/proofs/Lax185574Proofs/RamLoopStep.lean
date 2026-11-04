import Lax185574Proofs.RamLoopSwap

/-!
A whole round of the loop driver, forward and backward.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ}

section

variable (G P : Program)

/-- The run of `P` in a round, forward. -/
theorem lp_P_fwd {x a b o r : List ℕ} {i t : ℕ} {S S2 : State} (hw : 8 ≤ w)
    (Q : PreP w x a b o i S S2) (hpc : S2.pc = lpStartP G) (hs : lpSize w (i + 1) ≠ 0)
    (ho : o.length ≤ lpCap w) (hlt : ∀ e ∈ o, e < 2 ^ lpV w i)
    (hrun : RunsTo (lpV w (i + 1)) P (lpQ o) r t) (hr : r.length ≤ lpCap w) :
    ∃ n ≤ lpCostP * (t + 1), ∃ S3, Exec w (lpProg G P) n S2 S3 ∧ S3.pc = lpExitP G P ∧
      PhaseOut w (i + 1) (S2.mem 46) S2 S3 r := by
  rw [← lpRhoP_apply] at hrun
  obtain ⟨n, hn, S3, e, hpc', hO⟩ := lp_phase_fwd lpSrcsP lpRhoP ![o] (lpCodeP G P)
    (lp_fits_phP G P) rfl (lpProg_P G P) (lpPreP_length G P) rfl rfl rfl rfl (fun l => rfl) rfl
    hpc hw (Q.pre hw hs) (by decide) (by decide) (Q.src hw hs ho)
    (lpRhoP_fit hw (by simp only [lpV]; omega) ho hlt) lpRhoP_seg (by simp [lpRhoP]) hrun hr
  refine ⟨n, le_trans hn ?_, S3, e, hpc', hO⟩
  have := lpRhoP_cost ![o]
  simp only [lpCostP, lpCodeP] at *
  nlinarith

/-- **A round with a call, forward.** -/
theorem lp_round_call {x a b o r : List ℕ} {i t₁ t₂ : ℕ} {S : State}
    (L : LInv w x a b i S) (hpc : S.pc = lpLoop) (hw : 8 ≤ w) (hx : x.length < 4 * lpCap w)
    (hs : lpSize w i ≠ 0) (hG : RunsTo (lpV w i) G (lpU x a b) o t₁) (hne : o ≠ [])
    (h0 : o.head? ≠ some 0) (ho : o.length ≤ lpCap w) (hs' : lpSize w (i + 1) ≠ 0)
    (hP : RunsTo (lpV w (i + 1)) P (lpQ o) r t₂) (hr : r.length ≤ lpCap w) :
    ∃ n ≤ lpCostG * (t₁ + 1) + lpCostP * (t₂ + 1) + 13, ∃ S',
      Exec w (lpProg G P) n S S' ∧ S'.pc = lpLoop ∧ LInv w x o r (i + 2) S' := by
  have hC := lpCap_bounds hw
  obtain ⟨n₁, hn₁, S1, e1, hpc1, hO1⟩ := lp_G_fwd G P L hpc hw hx hs hG ho
  have hob : 64 ≤ S.mem 44 ∧ S.mem 44 + lpCap w ≤ 2 ^ w := by
    rcases L.acur with h | h <;> rw [h] <;> omega
  obtain ⟨S2, e2, hpc2, h45, hfr, hi2, ho2⟩ := lp_exitG_call G P hw hpc1 hob hO1 hne h0
  have Q := PreP.of_call G P L hO1 e2 h45 hfr hi2 ho2 hw
  obtain ⟨n₃, hn₃, S3, e3, hpc3, hO3⟩ := lp_P_fwd G P hw Q hpc2 hs' ho (runsTo_out_lt hG) hP hr
  obtain ⟨S4, e4, hpc4, L4⟩ := lp_swap G P hw Q hO3 hpc3 ho hr hs'
  exact ⟨n₁ + 4 + n₃ + 9, by omega, S4, ((e1.trans e2).trans e3).trans e4, hpc4, L4⟩

theorem lp_out_halt : (lpProg G P)[lpOut G P + 8]? = some .halt :=
  fetch (lp_fits_out G P) (s := ⟨lpOut G P + 8, fun _ => 0, [], [], []⟩) rfl rfl

/-- **A final round, forward.** -/
theorem lp_round_done {x a b z : List ℕ} {i t : ℕ} {S : State}
    (L : LInv w x a b i S) (hpc : S.pc = lpLoop) (hw : 8 ≤ w) (hx : x.length < 4 * lpCap w)
    (hs : lpSize w i ≠ 0) (hG : RunsTo (lpV w i) G (lpU x a b) (0 :: z) t)
    (ho : (0 :: z).length ≤ lpCap w) :
    ∃ n ≤ lpCostG * (t + 1) + 7 * z.length + 6, ∃ S', Exec w (lpProg G P) n S S' ∧
      (lpProg G P)[S'.pc]? = some .halt ∧ S'.out = z := by
  have hC := lpCap_bounds hw
  obtain ⟨n₁, hn₁, S1, e1, hpc1, hO1⟩ := lp_G_fwd G P L hpc hw hx hs hG ho
  have hob : 64 ≤ S.mem 44 := by rcases L.acur with h | h <;> rw [h] <;> omega
  have hob' : S.mem 44 + lpCap w ≤ 2 ^ w := by rcases L.acur with h | h <;> rw [h] <;> omega
  obtain ⟨S2, e2, hpc2, hrob, hroc, hone, hbuf, hW2, ho2⟩ := lp_exitG_done G P hw hpc1 hob hO1
  obtain ⟨S3, e3, hpc3, hm3, -, -, ho3⟩ := (x_set (w := w) (s := S2)
    (fetch (lp_fits_out G P) (i := 0) (by simp [hpc2]) rfl) (by omega)).upd
  have f3 : ∀ c, c ≠ rC → S3.mem c = S2.mem c := fun c h => by rw [hm3, if_neg h]
  obtain ⟨S4, e4, hpc4, ho4⟩ := lp_write_loop G P (ob := S.mem 44) (out := 0 :: z) hw
    (by omega) (by
      rcases L.acur with h | h <;> rw [h] <;> simp only [List.length_cons] at ho ⊢ <;> omega)
    z.length 1 S3 (by simp)
    le_rfl (by simp) (hW2.exec e3) (by rw [f3 _ (by decide)]; exact hone)
    (by rw [f3 _ (by decide)]; exact hrob) (by rw [f3 _ (by decide), hroc]; rfl)
    (fun k hk => by rw [f3 _ (by omega)]; exact hbuf k hk) (by rw [hpc3, hpc2]) (by
      rw [hm3, if_pos rfl, Nat.mod_eq_of_lt (by omega)])
  refine ⟨n₁ + 3 + 1 + (7 * z.length + 2), by omega, S4, ((e1.trans e2).trans e3).trans e4,
    by rw [hpc4]; exact lp_out_halt G P, ?_⟩
  rw [ho4, ho3, ho2, hO1.out, L.out]
  simp

end

end Lax185574Proofs.RamSim
