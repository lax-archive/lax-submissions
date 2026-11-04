import Lax185574Proofs.RamParStep

/-!
The parallel combinator: one turn, the run, and both directions.

A turn starts at the block of the active thread. It simulates one step
of that thread, and then switches to the other thread, handles a halt,
or handles an overflow of the buffer. The number of steps of the
threads goes up by one per turn, and a turn costs between `1` and `60`
machine steps (`slot_spec`). As long as both threads are alive they
take turns, so neither thread is more than one step ahead
(`Entry`). The forward direction follows: a thread that halts with an
answer after `t` steps is found within `2 t` turns. The backward
direction: a machine that halts after `N` steps has made at most `N`
turns, and the only halting state is the one after an answer.
-/

namespace Lax185574Proofs.RamPar

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.RamSim

variable {w K : ℕ} {P₀ P₁ : Program} {x : List ℕ}

/-- One more step of thread `b`. -/
def bump (k : Bool → ℕ) (b : Bool) : Bool → ℕ := Function.update k b (k b + 1)

@[simp] theorem bump_self (k : Bool → ℕ) (b : Bool) : bump k b b = k b + 1 := by
  simp [bump]

@[simp] theorem bump_ne (k : Bool → ℕ) (b : Bool) : bump k b (!b) = k (!b) := by
  cases b <;> simp [bump]

theorem bump_sum (k : Bool → ℕ) (b : Bool) :
    bump k b false + bump k b true = k false + k true + 1 := by
  cases b <;> simp [bump] <;> omega

/-- The machine is at the block of the active thread `b`, the other
thread is at `o` (the length of its program once it is dead), and
thread `c` has made `k c` steps. -/
def Entry (w K : ℕ) (P₀ P₁ : Program) (x : List ℕ) (b : Bool) (o : ℕ) (k : Bool → ℕ)
    (S : State) : Prop :=
  WordMem w S.mem ∧ o ≤ nT P₀ P₁ (!b) ∧
  (∃ sb, run (w - K) (thr P₀ P₁ b) (k b) (initState x) = some sb ∧ sb.pc < nT P₀ P₁ b ∧
    S.pc = slotA P₀ P₁ b sb.pc o ∧ TRel w K x b (deadA P₀ P₁ b o) sb S) ∧
  (o < nT P₀ P₁ (!b) → ∃ so, run (w - K) (thr P₀ P₁ (!b)) (k (!b)) (initState x) = some so ∧
    so.pc = o ∧ Other w K x (!b) so S ∧ k b ≤ k (!b) ∧ k (!b) ≤ k b + 1) ∧
  (nT P₀ P₁ (!b) ≤ o → Never (w - K) (thr P₀ P₁ (!b)) x ∧ k (!b) ≤ k b + 1)

/-- The machine is about to halt with the answer of a thread. -/
def Halted (w K : ℕ) (P₀ P₁ : Program) (x : List ℕ) (S : State) : Prop :=
  (parProg K P₀ P₁)[S.pc]? = some .halt ∧ ∃ b y t, y.length ≤ 1 ∧
    RunsTo (w - K) (thr P₀ P₁ b) x (1 :: y) t ∧ S.out = y

/-- Both threads are dead and the machine loops. -/
def Loop (w K : ℕ) (P₀ P₁ : Program) (x : List ℕ) (S : State) : Prop :=
  (parProg K P₀ P₁)[S.pc]? = some (.jump S.pc) ∧ ∀ c, Never (w - K) (thr P₀ P₁ c) x

theorem TRel.out_nil {b : Bool} {ovf : ℕ} {s S : State} (R : TRel w K x b ovf s S) :
    S.out = [] := by
  obtain ⟨h, -⟩ := R.out
  exact h

theorem osup_temps (G : Glob w K x) {c : Bool} {a : ℕ} (h : OSup w K c a) : a < 9 ∨ 14 < a := by
  have hB := base_facts G c
  have hsv := sv_ge c
  have hob := ob_ge c
  simp only [OSup] at h
  omega

/-- A dead thread `b` hands over, or the machine loops. -/
theorem die (G : Glob w K x) {b : Bool} {o : ℕ} {k : Bool → ℕ} {S : State}
    (hpc : S.pc = deadA P₀ P₁ b o) (hm : WordMem w S.mem) (hob : o ≤ nT P₀ P₁ (!b))
    (hnb : Never (w - K) (thr P₀ P₁ b) x)
    (hA : o < nT P₀ P₁ (!b) → ∃ so, run (w - K) (thr P₀ P₁ (!b)) (k (!b)) (initState x) = some so ∧
      so.pc = o ∧ Other w K x (!b) so S ∧ k b ≤ k (!b))
    (hD : nT P₀ P₁ (!b) ≤ o → Never (w - K) (thr P₀ P₁ (!b)) x) :
    ∃ n ≤ 5, ∃ S', Exec w (parProg K P₀ P₁) n S S' ∧
      ((1 ≤ n ∧ Entry w K P₀ P₁ x (!b) (nT P₀ P₁ b) (bump k b) S') ∨ Loop w K P₀ P₁ x S') := by
  by_cases ho : o < nT P₀ P₁ (!b)
  · obtain ⟨so, hrun, hpo, hO, hk⟩ := hA ho
    obtain ⟨S', e, hpc', R', hm'⟩ := dead_switch G ho hpc hm hO
    refine ⟨5, le_rfl, S', e, Or.inl ⟨by omega, hm', by simp,
      ⟨so, by rw [bump_ne]; exact hrun, by rw [hpo]; exact ho, by rw [hpc', hpo], R'⟩,
      fun h => absurd h (by simp), fun _ => ⟨by simpa using hnb, ?_⟩⟩⟩
    simp only [Bool.not_not, bump_self, bump_ne]
    omega
  · refine ⟨0, by omega, S, Exec.refl S, Or.inr ⟨dead_loop (K := K) (by omega)
      (lt_of_le_of_lt hob (nT_lt _ _ _)) hpc, fun c => ?_⟩⟩
    have hd := hD (by omega)
    cases b <;> cases c <;> assumption

/-- **One turn.** -/
theorem slot_spec (G : Glob w K x) {b : Bool} {o : ℕ} {k : Bool → ℕ} {S : State}
    (hE : Entry w K P₀ P₁ x b o k S) :
    ∃ n ≤ 60, ∃ S', Exec w (parProg K P₀ P₁) n S S' ∧
      ((1 ≤ n ∧ ∃ b' o', Entry w K P₀ P₁ x b' o' (bump k b) S') ∨ Halted w K P₀ P₁ x S' ∨
        Loop w K P₀ P₁ x S') := by
  obtain ⟨hm, hob, ⟨sb, hrun, hlt, hpc, R⟩, hA, hD⟩ := hE
  have hon : o < nN P₀ P₁ := lt_of_le_of_lt hob (nT_lt _ _ _)
  obtain ⟨ins, hins⟩ : ∃ ins, (thr P₀ P₁ b)[sb.pc]? = some ins :=
    ⟨_, List.getElem?_eq_getElem (by simpa [nT] using hlt)⟩
  have hf := block_fits (K := K) hins hon
  have B := block_spec (code P₀ P₁ b o) R hpc hf
  have hsb : stepBound (code P₀ P₁ b o).ks = 22 := rfl
  have transport : ∀ S1 : State, Frame (geo w K b) S S1 → WordMem w S1.mem → S1.out = S.out →
      o < nT P₀ P₁ (!b) → ∃ so, run (w - K) (thr P₀ P₁ (!b)) (k (!b)) (initState x) = some so ∧
        so.pc = o ∧ Other w K x (!b) so S1 ∧ k b ≤ k (!b) ∧ k (!b) ≤ k b + 1 := by
    intro S1 fr hm1 ho1 ho
    obtain ⟨so, h1, h2, hO, h3, h4⟩ := hA ho
    refine ⟨so, h1, h2, hO.frame hm1 fr.1 ho1 (fun a ha => fr.2.2 a ?_), h3, h4⟩
    have := osup_not_W G ha
    simpa using this
  -- after a halt of thread `b` at `s` with `k'` steps
  have finish : ∀ (k' : ℕ) (s : State) (S1 : State) (n1 : ℕ), n1 ≤ 22 →
      Exec w (parProg K P₀ P₁) n1 S S1 → S1.pc = exitA P₀ P₁ b o →
      TRel w K x b (deadA P₀ P₁ b o) s S1 → Frame (geo w K b) S S1 → k' = k b ∨ k' = k b + 1 →
      run (w - K) (thr P₀ P₁ b) k' (initState x) = some s →
      step (w - K) (thr P₀ P₁ b) s = none →
      ∃ n ≤ 60, ∃ S', Exec w (parProg K P₀ P₁) n S S' ∧
        ((1 ≤ n ∧ ∃ b' o', Entry w K P₀ P₁ x b' o' (bump k b) S') ∨ Halted w K P₀ P₁ x S' ∨
          Loop w K P₀ P₁ x S') := by
    intro k' s S1 n1 hn1 e1 hpc1 R1 fr1 _ hrun1 hs
    rcases exit_spec G hon hpc1 R1 hrun1 hs with ⟨n2, hn2, S2, e2, hh, y, hy, hR, hout⟩ |
      ⟨hnb, n2, hn2, S2, e2, hpc2, fr2, hm2, hi2, ho2⟩
    · exact ⟨n1 + n2, by omega, S2, e1.trans e2, Or.inr (Or.inl ⟨hh, b, y, _, hy, hR, hout⟩)⟩
    · have hm1 : WordMem w S1.mem := R1.env.word
      have hA1 := transport S1 fr1 hm1 (by rw [TRel.out_nil R1, TRel.out_nil R])
      have hA2 : o < nT P₀ P₁ (!b) → ∃ so, run (w - K) (thr P₀ P₁ (!b)) (k (!b)) (initState x) =
          some so ∧ so.pc = o ∧ Other w K x (!b) so S2 ∧ k b ≤ k (!b) := by
        intro ho
        obtain ⟨so, h1, h2, hO, h3, -⟩ := hA1 ho
        exact ⟨so, h1, h2, hO.frame hm2 hi2 ho2 (fun a ha => fr2 a (osup_temps G ha)), h3⟩
      obtain ⟨n3, hn3, S3, e3, hres⟩ := die G hpc2 hm2 hob hnb hA2 (fun h => (hD h).1)
      refine ⟨n1 + n2 + n3, by omega, S3, (e1.trans e2).trans e3, ?_⟩
      rcases hres with ⟨h1, hE3⟩ | hL
      · exact Or.inl ⟨by omega, _, _, hE3⟩
      · exact Or.inr (Or.inr hL)
  cases hE' : ins.effect (w - K) sb with
  | none =>
      have hs : step (w - K) (thr P₀ P₁ b) sb = none := by simp [step_eq, hins, hE']
      obtain ⟨n1, hn1, S1, e1, hpc1, R1, fr1⟩ := B.2.1 hE'
      exact finish (k b) sb S1 n1 (by rw [hsb] at hn1; exact hn1) e1 hpc1 R1 fr1 (Or.inl rfl)
        hrun hs
  | some s' =>
      have hrun' := run_snoc hrun (by simp [step_eq, hins, hE'] :
        step (w - K) (thr P₀ P₁ b) sb = some s')
      by_cases hcap : s'.out.length ≤ 2
      · obtain ⟨n1, hn1, S1, e1, hpc1, R1, fr1⟩ := B.1 s' hE' (fun _ _ => hcap)
        rw [hsb] at hn1
        have hm1 : WordMem w S1.mem := R1.env.word
        have hA1 := transport S1 fr1 hm1 (by rw [TRel.out_nil R1, TRel.out_nil R])
        have htgt : (code P₀ P₁ b o).tgt s'.pc =
            if s'.pc < nT P₀ P₁ b then slotA P₀ P₁ b s'.pc o + 23 else exitA P₀ P₁ b o := rfl
        rw [htgt] at hpc1
        by_cases hl : s'.pc < nT P₀ P₁ b
        · rw [if_pos hl] at hpc1
          by_cases ho : o < nT P₀ P₁ (!b)
          · obtain ⟨so, h1, h2, hO, h3, h4⟩ := hA1 ho
            obtain ⟨S2, e2, hpc2, R2, hO2, hm2⟩ := stub_switch G hl ho hpc1 R1 hO
            refine ⟨n1 + 9, by omega, S2, e1.trans e2, Or.inl ⟨by omega, !b, s'.pc, hm2,
              by simpa using hl.le, ⟨so, by rw [bump_ne]; exact h1, by rw [h2]; exact ho,
                by rw [hpc2, h2], R2⟩, fun _ => ⟨s', by simpa using hrun', rfl,
                by simpa using hO2, ?_, ?_⟩, fun h => absurd h (by simpa using hl)⟩⟩
            · simp only [Bool.not_not, bump_self, bump_ne]; omega
            · simp only [Bool.not_not, bump_self, bump_ne]; omega
          · have e2 := stub_stay (K := K) (w := w) hl (by omega) hon hpc1
            refine ⟨n1 + 1, by omega, _, e1.trans e2, Or.inl ⟨by omega, b, o, hm1, hob,
              ⟨s', by rw [bump_self]; exact hrun', hl, rfl, Rel.congr R1 hm1 rfl rfl
                (fun _ _ => rfl)⟩, fun h => absurd h ho, fun h => ⟨(hD h).1, ?_⟩⟩⟩
            have := (hD h).2
            rw [bump_self, bump_ne]; omega
        · rw [if_neg hl] at hpc1
          have hs : step (w - K) (thr P₀ P₁ b) s' = none :=
            step_none_of_length_le (by simp only [nT] at hl; omega)
          exact finish (k b + 1) s' S1 n1 hn1 e1 hpc1 R1 fr1 (Or.inr rfl) hrun' hs
      · have hcap' : (geo w K b).cap < s'.out.length := by
          show 2 < s'.out.length; omega
        obtain ⟨n1, hn1, S1, e1, hpc1, fr1, ho1⟩ := B.2.2 s' (deadA P₀ P₁ b o) rfl hE' hcap'
        rw [hsb] at hn1
        have hnb := never_of_long hrun' (by omega)
        have hm1 : WordMem w S1.mem := hm.exec e1
        have hA1 := transport S1 fr1 hm1 ho1
        obtain ⟨n3, hn3, S3, e3, hres⟩ := die (k := k) G hpc1 hm1 hob hnb
          (fun ho => by
            obtain ⟨so, h1, h2, hO, h3, -⟩ := hA1 ho
            exact ⟨so, h1, h2, hO, h3⟩) (fun h => (hD h).1)
        refine ⟨n1 + n3, by omega, S3, e1.trans e3, ?_⟩
        rcases hres with ⟨h1, hE3⟩ | hL
        · exact Or.inl ⟨by omega, _, _, hE3⟩
        · exact Or.inr (Or.inr hL)

/-- After the initialization and `M` turns: at a block after at least
`M` steps of the threads, halting, or looping. -/
theorem iter (G : Glob w K x) : ∀ M : ℕ, ∃ n S, Exec w (parProg K P₀ P₁) n (initState x) S ∧
    ((∃ b o k, Entry w K P₀ P₁ x b o k S ∧ M ≤ k false + k true ∧ k false + k true ≤ n ∧
        n ≤ 60 * (k false + k true) + 40) ∨
      (Halted w K P₀ P₁ x S ∧ n ≤ 60 * M + 40) ∨ Loop w K P₀ P₁ x S)
  | 0 => by
      obtain ⟨S0, e0, hpc0, R0, hO0, hm0⟩ := init_spec (P₀ := P₀) (P₁ := P₁) G
      have hD0 : nT P₀ P₁ (!false) ≤ 0 → Never (w - K) (thr P₀ P₁ (!false)) x :=
        fun h => never_empty (Nat.le_zero.mp h)
      by_cases h0 : 0 < nT P₀ P₁ false
      · refine ⟨15, S0, e0, Or.inl ⟨false, 0, fun _ => 0, ⟨hm0, Nat.zero_le _,
          ⟨initState x, rfl, h0, hpc0, R0⟩, fun _ => ⟨initState x, rfl, rfl, hO0, le_rfl,
            Nat.zero_le _⟩, fun h => ⟨hD0 h, Nat.zero_le _⟩⟩, Nat.zero_le _, Nat.zero_le _,
          by norm_num⟩⟩
      · have hn0 : nT P₀ P₁ false = 0 := by omega
        have hpcE : S0.pc = exitA P₀ P₁ false 0 := by rw [hpc0, exitA, hn0]
        have hs : step (w - K) (thr P₀ P₁ false) (initState x) = none :=
          step_none_of_length_le (Nat.le_of_eq hn0)
        have hon : 0 < nN P₀ P₁ := lt_of_le_of_lt (Nat.zero_le _) (nT_lt P₀ P₁ true)
        rcases exit_spec G hon hpcE R0 (k := 0) rfl hs with
          ⟨n2, hn2, S2, e2, hh, y, hy, hR, hout⟩ | ⟨hnb, n2, hn2, S2, e2, hpc2, fr2, hm2, hi2, ho2⟩
        · exact ⟨15 + n2, S2, e0.trans e2, Or.inr (Or.inl ⟨⟨hh, false, y, _, hy, hR, hout⟩,
            by omega⟩)⟩
        · obtain ⟨n3, hn3, S3, e3, hres⟩ := die (k := fun _ => 0) G hpc2 hm2 (Nat.zero_le _) hnb
            (fun _ => ⟨initState x, rfl, rfl,
              hO0.frame hm2 hi2 ho2 (fun a ha => fr2 a (osup_temps G ha)), le_rfl⟩) hD0
          rcases hres with ⟨h1, hE3⟩ | hL
          · have hs3 := bump_sum (fun _ => 0) false
            refine ⟨15 + n2 + n3, S3, (e0.trans e2).trans e3, Or.inl ⟨_, _, _, hE3, Nat.zero_le _,
              by omega, by omega⟩⟩
          · exact ⟨15 + n2 + n3, S3, (e0.trans e2).trans e3, Or.inr (Or.inr hL)⟩
  | M + 1 => by
      obtain ⟨n, S, e, h⟩ := iter G M
      rcases h with ⟨b, o, k, hE, h1, h2, h3⟩ | ⟨hH, hn⟩ | hL
      · by_cases hM : M + 1 ≤ k false + k true
        · exact ⟨n, S, e, Or.inl ⟨b, o, k, hE, hM, h2, h3⟩⟩
        · obtain ⟨n', hn', S', e', hres⟩ := slot_spec G hE
          have hs := bump_sum k b
          rcases hres with ⟨h1', b', o', hE'⟩ | hH | hL
          · exact ⟨n + n', S', e.trans e', Or.inl ⟨b', o', bump k b, hE', by omega, by omega,
              by omega⟩⟩
          · exact ⟨n + n', S', e.trans e', Or.inr (Or.inl ⟨hH, by omega⟩)⟩
          · exact ⟨n + n', S', e.trans e', Or.inr (Or.inr hL)⟩
      · exact ⟨n, S, e, Or.inr (Or.inl ⟨hH, by omega⟩)⟩
      · exact ⟨n, S, e, Or.inr (Or.inr hL)⟩

/-- The constant of the combinator. -/
abbrev parK : ℕ := 200

/-- **Two threads in parallel.** Both threads run on `x` at word length
`w - parK`. If one of them halts with `1 :: y`, `y` of length at most
one, after `t` steps, the combinator halts within `parK (t + 1)` steps.
Every halting run of the combinator outputs `z` such that one of the
threads halts with `1 :: z`. -/
theorem par_spec (P₀ P₁ : Program) (w : ℕ) (x : List ℕ) (hw : parK < w)
    (hx : x.length < 2 ^ (w - parK)) :
    (∀ (b : Bool) (y : List ℕ) (t : ℕ), RunsTo (w - parK) (cond b P₁ P₀) x (1 :: y) t →
      y.length ≤ 1 → ∃ T ≤ parK * (t + 1), ∃ y', RunsTo w (parProg parK P₀ P₁) x y' T) ∧
    (∀ z T, RunsTo w (parProg parK P₀ P₁) x z T →
      ∃ (b : Bool) (t : ℕ), RunsTo (w - parK) (cond b P₁ P₀) x (1 :: z) t) := by
  have G : Glob w parK x :=
    ⟨by norm_num, hw, lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  refine ⟨fun g y t hR hy => ?_, fun z T hz => ?_⟩
  · have hR' : RunsTo (w - parK) (thr P₀ P₁ g) x (1 :: y) t := hR
    have ht : 0 < t := alive_lt (c := 0) rfl (Or.inr rfl) hR'
    obtain ⟨n, S, e, hres⟩ := iter (P₀ := P₀) (P₁ := P₁) G (2 * t)
    rcases hres with ⟨b, o, k, hE, h1, -, -⟩ | ⟨⟨hh, -⟩, hn⟩ | ⟨-, hL⟩
    · exfalso
      obtain ⟨-, -, ⟨sb, hrun, hlt, -, -⟩, hA, hD⟩ := hE
      have hsum : k false + k true = k b + k (!b) := by
        cases b
        · rfl
        · show k false + k true = k true + k false; omega
      by_cases hg : g = b
      · subst hg
        have := alive_lt hrun (Or.inl hlt) hR'
        by_cases ho : o < nT P₀ P₁ (!g)
        · obtain ⟨-, -, -, -, -, h5⟩ := hA ho; omega
        · obtain ⟨-, h5⟩ := hD (by omega); omega
      · have hg' : g = !b := by cases g <;> cases b <;> simp_all
        subst hg'
        by_cases ho : o < nT P₀ P₁ (!b)
        · obtain ⟨so, hrun', hpo, -, h4, -⟩ := hA ho
          have := alive_lt hrun' (Or.inl (by rw [hpo]; exact ho)) hR'
          omega
        · exact (hD (by omega)).1 y t hy hR'
    · refine ⟨n + 1, by show n + 1 ≤ 200 * (t + 1); omega, S.out, ?_⟩
      have := runsTo_of_exec e (step_halt hh) rfl
      rwa [terminalCost_of_getElem? hh] at this
    · exact (hL g y t hy hR').elim
  · obtain ⟨kk, sE, h1, h2, h3, h4⟩ := hz
    have hH : Halts w (parProg parK P₀ P₁) (initState x) kk sE := ⟨h1, h2⟩
    obtain ⟨n, S, e, hres⟩ := iter (P₀ := P₀) (P₁ := P₁) G (kk + 1)
    rcases hres with ⟨b, o, k, -, h1', h2', -⟩ | ⟨⟨hh, b, y, t, -, hR, hout⟩, -⟩ | ⟨hL, -⟩
    · have := e.le_of_halts hH; omega
    · have hR2 := runsTo_of_exec e (step_halt hh) rfl
      have := (runsTo_unique ⟨kk, sE, h1, h2, h3, h4⟩ hR2).1
      exact ⟨b, t, by rw [this, hout]; exact hR⟩
    · exact absurd (hH.rest e) (not_halts_of_loop hL rfl)

end Lax185574Proofs.RamPar
