import Lax185574Proofs.RamLoopInv

/-!
The run of `G` in a round of the loop driver: its sources, forward and
backward.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program}

theorem lpBusy_mid {i ob N c : ℕ} (h1 : 36 ≤ c ∨ c = 15) (h2 : c < 64) (h3 : c < 47 ∨ 50 < c)
    (hob : 64 ≤ ob) (hN : N ≤ 6) : ¬ LpBusy w i ob N c := by
  have := lpAlloc_next_ge (lpCap w) i
  simp only [LpBusy, lpGeo, Geo.W, LaunchW, lpBase]
  omega

theorem lpBusy_hi {i ob N c : ℕ} (hw : 8 ≤ w) (hs : lpSize w i ≠ 0) (h1 : 4 * lpCap w ≤ c)
    (h2 : c < ob ∨ ob + lpCap w ≤ c) (hN : N ≤ 6) : ¬ LpBusy w i ob N c := by
  have := lpAlloc_room (lpCap w) i
  have := lpCap_bounds hw
  have hsz := lpSize_eq hs
  simp only [lpSize] at hsz
  simp only [LpBusy, lpGeo, Geo.W, LaunchW, lpBase]
  rw [← hsz]; omega

theorem srcOK_mem {Q : ℕ → Prop} {S : State} {bc lc : ℕ} {xs : List ℕ}
    (hword : WordMem w S.mem) (hlc : S.mem lc = xs.length) (hlen : xs.length < 2 ^ w)
    (hlcw : lc < 2 ^ w) (hQlc : ¬ Q lc) (hbc : bc < 2 ^ w) (hQbc : ¬ Q bc)
    (hroom : S.mem bc + xs.length ≤ 2 ^ w)
    (hval : ∀ k < xs.length, S.mem (S.mem bc + k) = xs.getD k 0)
    (hQ : ∀ k < xs.length, ¬ Q (S.mem bc + k)) : SrcOK w Q S ⟨.mem bc, lc⟩ xs :=
  ⟨hlc, hlen, hlcw, hQlc, hbc, hQbc, hroom, fun k hk =>
    ⟨by rw [hval k hk, Nat.mod_eq_of_lt (hval k hk ▸ hword _)], hQ k hk⟩⟩

theorem LInv.pre {x a b : List ℕ} {i : ℕ} {S : State} (L : LInv w x a b i S) (hw : 8 ≤ w)
    (hs : lpSize w i ≠ 0) : PhasePre w i 44 S := by
  have := lpCap_bounds hw
  exact ⟨L.word, L.zero, L.one, L.four, L.cap, L.alloc, hs, L.fresh,
    by rcases L.acur with h | h <;> rw [h] <;> omega⟩

theorem LInv.src {x a b : List ℕ} {i : ℕ} {S : State} (L : LInv w x a b i S) (hw : 8 ≤ w)
    (hs : lpSize w i ≠ 0) (hx : x.length < 2 ^ w) :
    ∀ j, SrcOK w (LpBusy w i (S.mem 44) lpRhoG.length) S (lpSrcsG j) (![x, a, b] j) := by
  have hC := lpCap_bounds hw
  have hN : lpRhoG.length ≤ 6 := by simp [lpRhoG]
  have hob : 64 ≤ S.mem 44 := by rcases L.acur with h | h <;> rw [h] <;> omega
  intro j
  fin_cases j
  · show SrcOK w _ S ⟨.input, 15⟩ x
    exact ⟨L.len, hx, (show (15 : ℕ) < 2 ^ w by omega),
      lpBusy_mid (c := 15) (Or.inr rfl) (by omega) (by omega) hob hN, L.input⟩
  · show SrcOK w _ S ⟨.mem 40, 41⟩ a
    refine srcOK_mem L.word L.alen (by have := L.ale; omega) (by omega)
      (lpBusy_mid (by omega) (by omega) (by omega) hob hN) (by omega)
      (lpBusy_mid (by omega) (by omega) (by omega) hob hN) ?_ L.aval ?_
    · rcases L.abuf with ⟨h, -⟩ | h
      · rw [h]; have := L.ale; omega
      · rw [h]; have := L.ale; rcases L.acur with h' | h' <;> rw [h'] <;> omega
    · intro k hk
      rcases L.abuf with ⟨h, h3⟩ | h
      · rw [h]; exact lpBusy_mid (by omega) (by omega) (by omega) hob hN
      · rw [h]
        have := L.ale
        rcases L.acur with h' | h' <;> rw [h'] <;>
          exact lpBusy_hi hw hs (by omega) (by omega) hN
  · show SrcOK w _ S ⟨.mem 42, 43⟩ b
    refine srcOK_mem L.word L.blen (by have := L.ble; omega) (by omega)
      (lpBusy_mid (by omega) (by omega) (by omega) hob hN) (by omega)
      (lpBusy_mid (by omega) (by omega) (by omega) hob hN) ?_ L.bval ?_
    · rcases L.bbuf with h | h
      · rw [h, Nat.add_zero]; exact le_of_lt (L.word 42)
      · rw [h]; have := L.ble; rcases L.pcur with h' | h' <;> rw [h'] <;> omega
    · intro k hk
      rcases L.bbuf with h | h
      · omega
      · rw [h]
        have := L.ble
        rcases L.pcur with h' | h' <;> rw [h'] <;>
          rcases L.acur with h'' | h'' <;> rw [h''] <;>
          exact lpBusy_hi hw hs (by omega) (by omega) hN

/-- The entries of `a` are words. -/
theorem LInv.a_lt {x a b : List ℕ} {i : ℕ} {S : State} (L : LInv w x a b i S) (k : ℕ) :
    a.getD k 0 < 2 ^ w := by
  by_cases hk : k < a.length
  · rw [← L.aval k hk]; exact L.word _
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.two_pow_pos w

theorem LInv.fit {x a b : List ℕ} {i : ℕ} {S : State} (L : LInv w x a b i S) (hw : 8 ≤ w)
    (hx : x.length < 4 * lpCap w) : lpRhoG.Fits w ![x, a, b] := by
  have hC := lpCap_bounds hw
  have ha := L.ale
  have hb := L.ble
  refine ⟨fun j => ?_, ?_, ?_⟩
  · fin_cases j <;> simp <;> omega
  · rw [lpRhoG_apply]
    simp only [lpU, List.length_append, List.length_cons, List.length_nil, List.length_take,
      List.length_drop]
    omega
  · intro seg hseg
    simp only [lpRhoG, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    rcases hseg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Segment.Fits, HExpr.Fits, HExpr.eval, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_zero] <;> and_intros <;>
      first
        | trivial
        | omega
        | exact L.a_lt 1
        | exact L.a_lt 2
        | exact L.a_lt 3

theorem lpRhoG_seg : ∀ seg ∈ lpRhoG, seg.size + 3 ≤ 8 := by
  intro seg h
  simp only [lpRhoG, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Segment.size, HExpr.size]

theorem lpRhoP_seg : ∀ seg ∈ lpRhoP, seg.size + 3 ≤ 8 := by
  intro seg h
  simp only [lpRhoP, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl; simp [Segment.size, HExpr.size]

def lpCostG : ℕ := 16 + 11 * 20 + stepBound lpKsG
def lpCostP : ℕ := 16 + 11 * 20 + stepBound lpKsP

theorem lpRhoG_cost (xs : Fin 3 → List ℕ) : (lpRhoG.map (·.cost xs)).sum ≤ 20 := by
  simp [lpRhoG, Segment.cost, HExpr.cost]

theorem lpRhoP_cost (xs : Fin 1 → List ℕ) : (lpRhoP.map (·.cost xs)).sum ≤ 20 := by
  simp [lpRhoP, Segment.cost, HExpr.cost]

/-- **The run of `G`, forward.** -/
theorem lp_G_fwd (G P : Program) {x a b o : List ℕ} {i t : ℕ} {S : State}
    (L : LInv w x a b i S) (hpc : S.pc = lpLoop) (hw : 8 ≤ w) (hx : x.length < 4 * lpCap w)
    (hs : lpSize w i ≠ 0) (hrun : RunsTo (lpV w i) G (lpU x a b) o t)
    (ho : o.length ≤ lpCap w) :
    ∃ n ≤ lpCostG * (t + 1), ∃ S', Exec w (lpProg G P) n S S' ∧ S'.pc = lpExitG G ∧
      PhaseOut w i (S.mem 44) S S' o := by
  have hC := lpCap_bounds hw
  rw [← lpRhoG_apply] at hrun
  obtain ⟨n, hn, S', e, hpc', hO⟩ := lp_phase_fwd lpSrcsG lpRhoG ![x, a, b] (lpCodeG G P)
    (lp_fits_phG G P) rfl (lpProg_G G P) (lpPreG_length G P) rfl rfl rfl rfl (fun l => rfl) rfl
    hpc hw (L.pre hw hs) (by decide) (by decide) (L.src hw hs (by omega)) (L.fit hw hx)
    lpRhoG_seg (by simp [lpRhoG]) hrun ho
  refine ⟨n, le_trans hn ?_, S', e, hpc', hO⟩
  have := lpRhoG_cost ![x, a, b]
  simp only [lpCostG, lpCodeG] at *
  nlinarith

/-- **The run of `G`, backward.** -/
theorem lp_G_back (G P : Program) {x a b : List ℕ} {i N : ℕ} {S S_end : State}
    (L : LInv w x a b i S) (hpc : S.pc = lpLoop) (hw : 8 ≤ w) (hx : x.length < 4 * lpCap w)
    (hhalt : Halts w (lpProg G P) S N S_end) :
    lpSize w i ≠ 0 ∧
      ∃ o t, RunsTo (lpV w i) G (lpU x a b) o t ∧ t ≤ N ∧ o.length ≤ lpCap w := by
  have hC := lpCap_bounds hw
  have hs : lpSize w i ≠ 0 := by
    intro h0
    have hf := lp_fits_phG G P
    rw [fits_append, fits_append] at hf
    exact not_halts_of_loop (lp_die_instr G P) rfl
      (hhalt.rest (lp_alloc_die hf.1.1 hpc L.alloc h0 (by omega)))
  refine ⟨hs, ?_⟩
  obtain ⟨o, t, hr, ht, ho⟩ := lp_phase_back lpSrcsG lpRhoG ![x, a, b] (lpCodeG G P)
    (lp_fits_phG G P) rfl (lpProg_G G P) (lpPreG_length G P) rfl rfl rfl rfl (fun l => rfl) rfl
    (lp_die_instr G P) hpc hw (L.pre hw hs) (by decide) (by decide) (L.src hw hs (by omega))
    (L.fit hw hx) lpRhoG_seg (by simp [lpRhoG]) hhalt
  rw [lpRhoG_apply] at hr
  exact ⟨o, t, hr, ht, ho⟩

end Lax185574Proofs.RamSim
