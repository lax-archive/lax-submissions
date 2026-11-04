import Lax185574Proofs.RamLoopStep

/-!
# The loop driver (call combinator)

`loop_sound` runs a glue program `G` and a callee `P` in alternation,
see `RamLoopCode` for the protocol. Its runs are described by
`LoopTrace`, which lists the runs of `G` and `P` round by round. The
driver halts with output `z` exactly when there is a trace ending in
`z`: forward with a time bound, and backward for every halting run.
So a composite whose glue and callee are right whenever they halt is
right whenever it halts.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

/-- The rounds of the loop driver from the round that uses region `i`,
with `a` and `b` the last outputs of `G` and `P`, to the output `z`.
The last index is the sum of the times of the runs, plus one per run.
Round `j` of a run from the start uses regions `2 j` and `2 j + 1`. -/
inductive LoopTrace (w : ℕ) (G P : Program) (x : List ℕ) :
    ℕ → List ℕ → List ℕ → List ℕ → ℕ → Prop
  | done {i : ℕ} {a b z : List ℕ} {t : ℕ} : lpSize w i ≠ 0 →
      RunsTo (lpV w i) G (lpU x a b) (0 :: z) t → (0 :: z).length ≤ lpCap w →
      LoopTrace w G P x i a b z (t + 1)
  | call {i : ℕ} {a b o r z : List ℕ} {t₁ t₂ T : ℕ} : lpSize w i ≠ 0 →
      RunsTo (lpV w i) G (lpU x a b) o t₁ → o ≠ [] → o.head? ≠ some 0 →
      o.length ≤ lpCap w → lpSize w (i + 1) ≠ 0 →
      RunsTo (lpV w (i + 1)) P (lpQ o) r t₂ → r.length ≤ lpCap w →
      LoopTrace w G P x (i + 2) o r z T → LoopTrace w G P x i a b z (t₁ + t₂ + 2 + T)

variable {w : ℕ}

/-- The constant of the loop driver. -/
def lpK : ℕ := lpCostG + lpCostP + 40

theorem lp_trace_fwd (G P : Program) {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 4 * lpCap w) :
    ∀ {i : ℕ} {a b z : List ℕ} {T : ℕ}, LoopTrace w G P x i a b z T →
      ∀ {S : State}, LInv w x a b i S → S.pc = lpLoop →
        ∃ n ≤ lpK * (T + z.length), ∃ S', Exec w (lpProg G P) n S S' ∧
          (lpProg G P)[S'.pc]? = some .halt ∧ S'.out = z := by
  intro i a b z T h
  induction h with
  | done hs hG ho =>
      intro S L hpc
      obtain ⟨n, hn, S', e, hh, hout⟩ := lp_round_done G P L hpc hw hx hs hG ho
      refine ⟨n, le_trans hn ?_, S', e, hh, hout⟩
      simp only [lpK]
      nlinarith
  | call hs hG hne h0 ho hs' hP hr _ ih =>
      intro S L hpc
      obtain ⟨n, hn, S', e, hpc', L'⟩ := lp_round_call G P L hpc hw hx hs hG hne h0 ho hs' hP hr
      obtain ⟨n', hn', S'', e', hh, hout⟩ := ih L' hpc'
      refine ⟨n + n', ?_, S'', e.trans e', hh, hout⟩
      simp only [lpK] at *
      nlinarith

/-- **A round, backward.** A halting machine at the start of a round
either finishes in this round with the output of `G`, or makes a call
and reaches the next round. -/
theorem lp_round_back (G P : Program) {x a b : List ℕ} {i N : ℕ} {S S_end : State}
    (L : LInv w x a b i S) (hpc : S.pc = lpLoop) (hw : 8 ≤ w) (hx : x.length < 4 * lpCap w)
    (hH : Halts w (lpProg G P) S N S_end) :
    (∃ z t, lpSize w i ≠ 0 ∧ RunsTo (lpV w i) G (lpU x a b) (0 :: z) t ∧
      (0 :: z).length ≤ lpCap w ∧ S_end.out = z) ∨
    (∃ o t₁ r t₂ n S', lpSize w i ≠ 0 ∧ RunsTo (lpV w i) G (lpU x a b) o t₁ ∧ o ≠ [] ∧
      o.head? ≠ some 0 ∧ o.length ≤ lpCap w ∧ lpSize w (i + 1) ≠ 0 ∧
      RunsTo (lpV w (i + 1)) P (lpQ o) r t₂ ∧ r.length ≤ lpCap w ∧
      Exec w (lpProg G P) n S S' ∧ 1 ≤ n ∧ S'.pc = lpLoop ∧ LInv w x o r (i + 2) S') := by
  have hC := lpCap_bounds hw
  obtain ⟨hs, o, t₁, hG, -, ho⟩ := lp_G_back G P L hpc hw hx hH
  obtain ⟨n₁, -, S1, e1, hpc1, hO1⟩ := lp_G_fwd G P L hpc hw hx hs hG ho
  have hH1 := hH.rest e1
  have hob : 64 ≤ S.mem 44 ∧ S.mem 44 + lpCap w ≤ 2 ^ w := by
    rcases L.acur with h | h <;> rw [h] <;> omega
  rcases o with _ | ⟨u, z⟩
  · exfalso
    exact not_halts_of_loop (lp_die_instr G P) rfl
      (hH1.rest (lp_exitG_die G P (x := x) (a := a) (b := b) hw hpc1 hO1))
  by_cases hu : u = 0
  · subst hu
    left
    obtain ⟨n, -, S', e, hh, hout⟩ := lp_round_done G P L hpc hw hx hs hG ho
    obtain ⟨-, rfl⟩ := terminal_run_unique hH.1 hH.2 e (step_halt hh)
    exact ⟨z, t₁, hs, hG, ho, hout⟩
  · right
    have h0 : (u :: z).head? ≠ some 0 := by simpa using hu
    obtain ⟨S2, e2, hpc2, h45, hfr, hi2, ho2⟩ := lp_exitG_call G P hw hpc1 hob hO1 (by simp) h0
    have Q := PreP.of_call G P L hO1 e2 h45 hfr hi2 ho2 hw
    have hH2 := hH1.rest e2
    have hs' : lpSize w (i + 1) ≠ 0 := by
      intro h0'
      have hf := lp_fits_phP G P
      rw [fits_append, fits_append] at hf
      exact not_halts_of_loop (lp_die_instr G P) rfl
        (hH2.rest (lp_alloc_die hf.1.1 hpc2 Q.alloc h0' (by omega)))
    obtain ⟨r, t₂, hP, -, hr⟩ := lp_phase_back lpSrcsP lpRhoP ![u :: z] (lpCodeP G P)
      (lp_fits_phP G P) rfl (lpProg_P G P) (lpPreP_length G P) rfl rfl rfl rfl (fun l => rfl) rfl
      (lp_die_instr G P) hpc2 hw (Q.pre hw hs') (by decide) (by decide) (Q.src hw hs' ho)
      (lpRhoP_fit hw (by simp only [lpV]; omega) ho (runsTo_out_lt hG)) lpRhoP_seg
      (by simp [lpRhoP]) hH2
    rw [lpRhoP_apply] at hP
    obtain ⟨n, -, S', e, hpc', L'⟩ :=
      lp_round_call G P L hpc hw hx hs hG (by simp) h0 ho hs' hP hr
    have hn : 1 ≤ n := by
      by_contra hn0
      have : n = 0 := by omega
      subst this
      have hSS : S' = S := by
        have := e; simp only [Exec, run_zero, Option.some.injEq] at this; exact this.symm
      subst hSS
      have h1 := L.alloc.1
      have h2 := L'.alloc.1
      have m1 := lpAlloc_next_mono (lpCap w) i
      have m2 : (lpAlloc (lpCap w) (i + 1)).next + (lpAlloc (lpCap w) (i + 1)).size ≤
          (lpAlloc (lpCap w) (i + 2)).next := lpAlloc_next_mono (lpCap w) (i + 1)
      have : (lpAlloc (lpCap w) i).size ≠ 0 := hs
      omega
    exact ⟨u :: z, t₁, r, t₂, n, S', hs, hG, by simp, h0, ho, hs', hP, hr, e, hn, hpc', L'⟩

theorem lp_trace_back (G P : Program) {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 4 * lpCap w) :
    ∀ (N : ℕ) {i : ℕ} {a b : List ℕ} {S S_end : State}, LInv w x a b i S → S.pc = lpLoop →
      Halts w (lpProg G P) S N S_end → ∃ T, LoopTrace w G P x i a b S_end.out T := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      intro i a b S S_end L hpc hH
      rcases lp_round_back G P L hpc hw hx hH with ⟨z, t, hs, hG, ho, hout⟩ |
        ⟨o, t₁, r, t₂, n, S', hs, hG, hne, h0, ho, hs', hP, hr, e, hn, hpc', L'⟩
      · exact ⟨t + 1, hout ▸ LoopTrace.done hs hG ho⟩
      · have hnN := e.le_of_halts hH
        obtain ⟨T, hT⟩ := ih (N - n) (by omega) L' hpc' (hH.rest e)
        exact ⟨_, LoopTrace.call hs hG hne h0 ho hs' hP hr hT⟩

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.RamSim

/-- **The loop driver, both directions.** For a glue program `G` and a
callee `P` there is a program `p` such that, at every word length
`w ≥ 8` and on every input `x` with `|x| < 2 ^ (w - 1)`, `p` halts with
output `z` within `K (T + |z| + 1)` steps if there is a trace of the
rounds of `G` and `P` of total time `T` ending in `z`, and every halting
run of `p` comes from such a trace. -/
theorem loop_sound (G P : Program) : ∃ (p : Program) (K : ℕ),
    ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      (∀ z T, LoopTrace w G P x 0 (lpA0 x) [] z T →
        ∃ t ≤ K * (T + z.length + 1), RunsTo w p x z t) ∧
      (∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T) := by
  refine ⟨lpProg G P, lpK + 22, fun w x hw hx => ⟨fun z T h => ?_, fun z t h => ?_⟩⟩
  · have hC := lpCap_bounds hw
    have hx' : x.length < 4 * lpCap w := by
      have : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    obtain ⟨S, e, hpc, L⟩ := lp_init G P (x := x) hw (by omega)
    obtain ⟨n, hn, S', e', hh, hout⟩ := lp_trace_fwd G P hw hx' h L hpc
    refine ⟨21 + n + 1, ?_, ?_⟩
    · nlinarith
    · have := runsTo_of_exec (e.trans e') (step_halt hh) hout
      rwa [terminalCost_of_getElem? hh] at this
  · have hC := lpCap_bounds hw
    have hx' : x.length < 4 * lpCap w := by
      have : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    obtain ⟨S, e, hpc, L⟩ := lp_init G P (x := x) hw (by omega)
    obtain ⟨N, S_end, hr, hs, hz, -⟩ := h
    have hH : Halts w (lpProg G P) (initState x) N S_end := ⟨hr, hs⟩
    obtain ⟨T, hT⟩ := lp_trace_back G P hw hx' (N - 21) L hpc (hH.rest e)
    exact ⟨T, hz ▸ hT⟩

end Lax185574Proofs.Simulate
