import Lax185574Proofs.RamParRel

/-!
The parallel combinator: the switch code, the exit handler, the handler
of a dead thread, and the initialization.
-/

namespace Lax185574Proofs.RamPar

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.RamSim

variable {w K : ℕ} {P₀ P₁ : Program} {x : List ℕ}

theorem geo_v (w K : ℕ) (b : Bool) : (geo w K b).v = w - K := rfl
theorem geo_ob (w K : ℕ) (b : Bool) : (geo w K b).ob = ob b := rfl
theorem geo_cap (w K : ℕ) (b : Bool) : (geo w K b).cap = 2 := rfl

theorem Exec.pcu {p : Program} {n l : ℕ} {s : State} (h : Exec w p n s { s with pc := l }) :
    ∃ s', Exec w p n s s' ∧ s'.pc = l ∧ s'.mem = s.mem ∧ s'.input = s.input ∧
      s'.inp = s.inp ∧ s'.out = s.out :=
  ⟨_, h, rfl, rfl, rfl, rfl, rfl⟩

theorem swapL_ok (b : Bool) : ∀ c ∈ svL b ++ ldL (!b), c.1 ≠ 0 ∧ c.1 < 64 ∧ c.2 < 64 := by
  cases b <;> decide

theorem ldL_ok (b : Bool) : ∀ c ∈ ldL b, c.1 ≠ 0 ∧ c.1 < 64 ∧ c.2 < 64 := by
  cases b <;> decide

theorem small_ok {cs : List (ℕ × ℕ)} (h : ∀ c ∈ cs, c.1 ≠ 0 ∧ c.1 < 64 ∧ c.2 < 64)
    (hw : 64 ≤ 2 ^ w) : ∀ c ∈ cs, c.1 ≠ 0 ∧ c.1 < 2 ^ w ∧ c.2 < 2 ^ w := fun c hc => by
  have := h c hc; omega

theorem w64 (G : Glob w K x) : 64 ≤ 2 ^ w := by
  obtain ⟨h1, -, h3⟩ := lay G; omega

theorem swap_frame (b : Bool) (m : ℕ → ℕ) {a : ℕ} (h3 : ¬ a = 3) (h4 : ¬ a = 4) (h6 : ¬ a = 6)
    (h7 : ¬ a = 7) (hr : a < sv b ∨ sv b + 4 ≤ a) : cpMem (svL b ++ ldL (!b)) m a = m a := by
  apply cpMem_of_not_mem
  intro c hc
  simp only [svL, ldL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ne_eq] <;> omega

theorem load_frame (b : Bool) (m : ℕ → ℕ) {a : ℕ} (h3 : ¬ a = 3) (h4 : ¬ a = 4) (h6 : ¬ a = 6)
    (h7 : ¬ a = 7) : cpMem (ldL b) m a = m a := by
  apply cpMem_of_not_mem
  intro c hc
  simp only [ldL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp only [ne_eq] <;> omega

theorem swp_of_ne (b : Bool) (m : ℕ → ℕ) {a : ℕ} (h3 : a ≠ 3) (h4 : a ≠ 4) (h6 : a ≠ 6)
    (h7 : a ≠ 7) : swp b m a = m a := by
  simp [swp, h3, h4, h6, h7]

theorem swp_word {b : Bool} {m : ℕ → ℕ} (hm : WordMem w m) : WordMem w (swp b m) := by
  intro a; simp only [swp]; split_ifs <;> exact hm _

/-! ### Switching threads -/

/-- The switch after a step of thread `b` to `l`, the other thread being
alive at `o`. -/
theorem stub_switch (G : Glob w K x) {b : Bool} {l o : ℕ} {s so S : State} {ovf : ℕ}
    (hl : l < nT P₀ P₁ b) (ho : o < nT P₀ P₁ (!b))
    (hpc : S.pc = slotA P₀ P₁ b l o + 23) (R : TRel w K x b ovf s S)
    (hO : Other w K x (!b) so S) :
    ∃ S', Exec w (parProg K P₀ P₁) 9 S S' ∧ S'.pc = slotA P₀ P₁ (!b) o l ∧
      TRel w K x (!b) (deadA P₀ P₁ (!b) l) so S' ∧ Other w K x b s S' ∧ WordMem w S'.mem := by
  have hf := stub_fits (K := K) hl (lt_trans ho (nT_lt _ _ _))
  simp only [stubCode, if_pos ho] at hf
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := w64 G
  have e1 := cp_spec (w := w) _ _ S hf1 hpc E.word E.zero (small_ok (swapL_ok b) hw)
  have hlen : (svL b ++ ldL (!b)).length = 8 := by cases b <;> rfl
  rw [hlen] at e1
  have hj := fits_singleton.1 hf2
  rw [cpCode_length, hlen] at hj
  have e12 := e1.trans (x_jump hj)
  have hm' : WordMem w (cpMem (svL b ++ ldL (!b)) S.mem) := E.word.exec e1
  obtain ⟨c3, c4, c6, c7, d0, d1, d2, d3⟩ := cpMem_swap b S.mem
  have hsv := sv_ge b
  have hB := base_facts G b
  have hB' := base_facts G (!b)
  have hob := ob_ge b
  have hob' := ob_ge (!b)
  refine ⟨_, e12, rfl, ?_, ?_, hm'⟩
  · refine Rel.congr hO hm' rfl rfl (fun a ha => ?_)
    simp only [Sup, geo_v, geo_ob, geo_cap] at ha
    simp only [swpS, swp]
    split_ifs with h3 h4 h6 h7
    · subst h3; exact c3
    · subst h4; exact c4
    · subst h6; exact c6
    · subst h7; exact c7
    · exact swap_frame b _ h3 h4 h6 h7 (by omega)
  · refine Rel.congr R (swp_word hm') rfl rfl (fun a ha => ?_)
    simp only [Sup, geo_v, geo_ob, geo_cap] at ha
    simp only [swpS, swp]
    split_ifs with h3 h4 h6 h7
    · subst h3; exact d0
    · subst h4; exact d1
    · subst h6; exact d2
    · subst h7; exact d3
    · exact swap_frame b _ h3 h4 h6 h7 (by omega)

/-- The switch code when the other thread is dead: continue. -/
theorem stub_stay {b : Bool} {l o : ℕ} {S : State}
    (hl : l < nT P₀ P₁ b) (ho : nT P₀ P₁ (!b) ≤ o) (hon : o < nN P₀ P₁)
    (hpc : S.pc = slotA P₀ P₁ b l o + 23) :
    Exec w (parProg K P₀ P₁) 1 S { S with pc := slotA P₀ P₁ b l o } := by
  have hf := stub_fits (K := K) hl hon
  simp only [stubCode, if_neg (by omega : ¬ o < nT P₀ P₁ (!b))] at hf
  exact x_jump (by rw [hpc]; exact fits_singleton.1 hf)

/-! ### Dead threads -/

/-- A dead thread hands over to the other thread. -/
theorem dead_switch (G : Glob w K x) {b : Bool} {o : ℕ} {so S : State}
    (ho : o < nT P₀ P₁ (!b)) (hpc : S.pc = deadA P₀ P₁ b o) (hm : WordMem w S.mem)
    (hO : Other w K x (!b) so S) :
    ∃ S', Exec w (parProg K P₀ P₁) 5 S S' ∧ S'.pc = slotA P₀ P₁ (!b) o (nT P₀ P₁ b) ∧
      TRel w K x (!b) (deadA P₀ P₁ (!b) (nT P₀ P₁ b)) so S' ∧ WordMem w S'.mem := by
  have hf := dead_fits (K := K) (b := b) (lt_trans ho (nT_lt _ _ _))
  simp only [deadCode, if_pos ho] at hf
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have hw := w64 G
  have h0 : S.mem 0 = 0 := by
    have := hO.env.zero; simpa [swpS, swp] using this
  have e1 := cp_spec (w := w) _ _ S hf1 hpc hm h0 (small_ok (ldL_ok (!b)) hw)
  have hlen : (ldL (!b)).length = 4 := rfl
  rw [hlen] at e1
  have hj := fits_singleton.1 hf2
  rw [cpCode_length, hlen] at hj
  have e12 := e1.trans (x_jump hj)
  have hm' : WordMem w (cpMem (ldL (!b)) S.mem) := hm.exec e1
  obtain ⟨c3, c4, c6, c7⟩ := cpMem_load (!b) S.mem
  refine ⟨_, e12, rfl, ?_, hm'⟩
  refine Rel.congr hO hm' rfl rfl (fun a _ => ?_)
  simp only [swpS, swp]
  split_ifs with h3 h4 h6 h7
  · subst h3; exact c3
  · subst h4; exact c4
  · subst h6; exact c6
  · subst h7; exact c7
  · exact load_frame (!b) _ h3 h4 h6 h7

/-- With both threads dead the machine loops. -/
theorem dead_loop {b : Bool} {o : ℕ} {S : State} (ho : nT P₀ P₁ (!b) ≤ o) (hon : o < nN P₀ P₁)
    (hpc : S.pc = deadA P₀ P₁ b o) : (parProg K P₀ P₁)[S.pc]? = some (.jump S.pc) := by
  have hf := dead_fits (K := K) (b := b) hon
  simp only [deadCode, if_neg (by omega : ¬ o < nT P₀ P₁ (!b))] at hf
  rw [hpc]; exact fits_singleton.1 hf

/-! ### The exit handler -/

/-- A halted thread either ends the machine with its answer, or it is
dead. -/
theorem exit_spec (G : Glob w K x) {b : Bool} {o k : ℕ} {s S : State} {ovf : ℕ}
    (ho : o < nN P₀ P₁) (hpc : S.pc = exitA P₀ P₁ b o) (R : TRel w K x b ovf s S)
    (hrun : run (w - K) (thr P₀ P₁ b) k (initState x) = some s)
    (hs : step (w - K) (thr P₀ P₁ b) s = none) :
    (∃ n ≤ 13, ∃ S', Exec w (parProg K P₀ P₁) n S S' ∧
      (parProg K P₀ P₁)[S'.pc]? = some .halt ∧ ∃ y, y.length ≤ 1 ∧
        RunsTo (w - K) (thr P₀ P₁ b) x (1 :: y) (k + terminalCost (thr P₀ P₁ b) s) ∧
        S'.out = y) ∨
    (Never (w - K) (thr P₀ P₁ b) x ∧ ∃ n ≤ 7, ∃ S', Exec w (parProg K P₀ P₁) n S S' ∧
      S'.pc = deadA P₀ P₁ b o ∧ (∀ a, (a < 9 ∨ 14 < a) → S'.mem a = S.mem a) ∧
      WordMem w S'.mem ∧ S'.input = S.input ∧ S'.out = S.out) := by
  obtain ⟨E, hE⟩ : ∃ E, E = exitA P₀ P₁ b o := ⟨_, rfl⟩
  have hdead : deadA P₀ P₁ b o = E + 13 := by rw [hE]; rfl
  have hf0 := exit_fits (K := K) (b := b) ho
  rw [← hE] at hf0 hpc
  unfold exitCode at hf0
  have hf := (fits_append.1 hf0).1
  have Ev := R.env
  have hw := w64 G
  have hm := Ev.word
  have hone : S.mem 1 = 1 := Ev.one
  obtain ⟨hout, h6, h7, -, hcap, -, -, -, hbuf⟩ := R.out
  have h6' : S.mem 6 = ob b := h6
  have hcap' : s.out.length ≤ 2 := hcap
  have hbuf' : ∀ j < s.out.length, S.mem (ob b + j) = s.out.getD j 0 := hbuf
  have hR : RunsTo (w - K) (thr P₀ P₁ b) x s.out (k + terminalCost (thr P₀ P₁ b) s) :=
    ⟨k, s, hrun, hs, rfl, rfl⟩
  have hobb := ob_ge b
  rcases hso : s.out with _ | ⟨u, rest⟩
  · right
    refine ⟨never_of_terminal hrun hs (fun y _ h => by rw [hso] at h; cases h), 1, by omega, _,
      x_jzero_pos (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega) (by rw [h7, hso]; rfl),
      by rw [hdead], fun a _ => rfl, hm, rfl, rfl⟩
  have hlen : s.out.length = rest.length + 1 := by rw [hso]; rfl
  have hu : S.mem (ob b) = u := by
    have := hbuf' 0 (by omega); rw [hso] at this; simpa using this
  -- the length is not zero
  obtain ⟨S1, e1, hpc1, hm1, hi1, -, ho1⟩ := Exec.pcu
    (x_jzero_neg (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)
      (by rw [h7, hlen]; omega))
  have hW1 : WordMem w S1.mem := by rw [hm1]; exact hm
  -- the first entry
  obtain ⟨S2, e2, hpc2, hm2, hi2, -, ho2⟩ := (x_load (w := w) (s := S1)
    (fetch hf (i := 1) (by omega) rfl) hW1 (by omega) (by omega)).upd
  have hW2 : WordMem w S2.mem := hm.exec (e1.trans e2)
  obtain ⟨S3, e3, hpc3, hm3, hi3, -, ho3⟩ := (x_sub (w := w) (s := S2)
    (fetch hf (i := 2) (by omega) rfl) hW2 (by omega) (by omega) (by omega)).upd
  have hW3 : WordMem w S3.mem := hm.exec ((e1.trans e2).trans e3)
  obtain ⟨S4, e4, hpc4, hm4, hi4, -, ho4⟩ := (x_sub (w := w) (s := S3)
    (fetch hf (i := 3) (by omega) rfl) hW3 (by omega) (by omega) (by omega)).upd
  obtain ⟨S5, e5, hpc5, hm5, hi5, -, ho5⟩ := (x_add (w := w) (s := S4)
    (fetch hf (i := 4) (by omega) rfl) (by omega) (by omega) (by omega)).upd
  have c5 := (((e1.trans e2).trans e3).trans e4).trans e5
  have hW5 : WordMem w S5.mem := hm.exec c5
  have fr5 : ∀ c, c ≠ 9 → c ≠ 12 → c ≠ 14 → S5.mem c = S.mem c := by
    intro c h9 h12 h14
    rw [hm5, if_neg h9, hm4, if_neg h14, hm3, if_neg h9, hm2, if_neg h12, hm1]
  have v12 : S2.mem 12 = u := by rw [hm2, if_pos rfl, hm1, h6', hu]
  have v1 : S2.mem 1 = 1 := by rw [hm2, if_neg (by decide), hm1, hone]
  have v9 : S3.mem 9 = u - 1 := by rw [hm3, if_pos rfl, v12, v1]
  have v14 : S4.mem 14 = 1 - u := by
    rw [hm4, if_pos rfl, hm3, if_neg (by decide), hm3, if_neg (by decide), v12, v1]
  have v9' : S5.mem 9 = (u - 1 + (1 - u)) % 2 ^ w := by
    rw [hm5, if_pos rfl, hm4, if_neg (by decide), v9, v14]
  have hu' : u < 2 ^ w := hu ▸ hm _
  have hio5 : S5.input = S.input ∧ S5.out = S.out := by
    refine ⟨?_, ?_⟩
    · rw [hi5, hi4, hi3, hi2, hi1]
    · rw [ho5, ho4, ho3, ho2, ho1]
  by_cases hu1 : u = 1
  · subst hu1
    have z9 : S5.mem 9 = 0 := by rw [v9']; simp
    obtain ⟨S6, e6, hpc6, hm6, hi6, -, ho6⟩ := Exec.pcu
      (x_jzero_pos (w := w) (s := S5) (fetch hf (i := 5) (by omega) rfl) (by omega) z9)
    have hW6 : WordMem w S6.mem := by rw [hm6]; exact hW5
    obtain ⟨S7, e7, hpc7, hm7, hi7, -, ho7⟩ := (x_sub (w := w) (s := S6)
      (fetch hf (i := 7) (by omega) rfl) hW6 (by omega) (by omega) (by omega)).upd
    have v14' : S7.mem 14 = rest.length := by
      rw [hm7, if_pos rfl, hm6, fr5 _ (by decide) (by decide) (by decide),
        fr5 _ (by decide) (by decide) (by decide), h7, hlen, hone]; omega
    have c7 := (c5.trans e6).trans e7
    rcases rest with _ | ⟨u2, rest2⟩
    · obtain ⟨S8, e8, hpc8, -, -, -, ho8⟩ := Exec.pcu
        (x_jzero_pos (w := w) (s := S7) (fetch hf (i := 8) (by omega) rfl) (by omega)
          (by rw [v14']; rfl))
      left
      refine ⟨_, by omega, S8, c7.trans e8, fetch hf (i := 12) (by omega) rfl, [], by simp,
        by rw [hso] at hR; exact hR, ?_⟩
      rw [ho8, ho7, ho6, hio5.2, hout]
    · rcases rest2 with _ | ⟨u3, rest3⟩
      · obtain ⟨S8, e8, hpc8, hm8, hi8, -, ho8⟩ := Exec.pcu
          (x_jzero_neg (w := w) (s := S7) (fetch hf (i := 8) (by omega) rfl) (by omega)
            (by rw [v14']; simp))
        obtain ⟨S9, e9, hpc9, hm9, hi9, -, ho9⟩ := (x_add (w := w) (s := S8)
          (fetch hf (i := 9) (by omega) rfl) (by omega) (by omega) (by omega)).upd
        have hW9 : WordMem w S9.mem := hm.exec ((c7.trans e8).trans e9)
        have fr8 : ∀ c, c ≠ 9 → c ≠ 12 → c ≠ 14 → S8.mem c = S.mem c := by
          intro c h9 h12 h14
          rw [hm8, hm7, if_neg h14, hm6, fr5 c h9 h12 h14]
        have v9'' : S9.mem 9 = ob b + 1 := by
          rw [hm9, if_pos rfl, fr8 _ (by decide) (by decide) (by decide),
            fr8 _ (by decide) (by decide) (by decide), h6', hone, Nat.mod_eq_of_lt (by omega)]
        obtain ⟨S10, e10, hpc10, hm10, hi10, -, ho10⟩ := (x_load (w := w) (s := S9)
          (fetch hf (i := 10) (by omega) rfl) hW9 (by omega) (by omega)).upd
        have hW10 : WordMem w S10.mem := hm.exec (((c7.trans e8).trans e9).trans e10)
        have v12' : S10.mem 12 = u2 := by
          rw [hm10, if_pos rfl, v9'', hm9, if_neg (by omega),
            fr8 _ (by omega) (by omega) (by omega)]
          have := hbuf' 1 (by rw [hso]; simp)
          rw [hso] at this
          simpa using this
        have e11 := x_write (w := w) (s := S10) (fetch hf (i := 11) (by omega) rfl) hW10
          (by omega)
        left
        refine ⟨_, by omega, _, (((c7.trans e8).trans e9).trans e10).trans e11,
          fetch hf (i := 12) (by simp only; omega) rfl, [u2], by simp,
          by rw [hso] at hR; exact hR, ?_⟩
        simp only
        rw [ho10, ho9, ho8, ho7, ho6, hio5.2, hout, v12']
        rfl
      · exfalso
        rw [hso] at hcap'
        simp at hcap'
  · -- the first entry is not `1`
    have nz : S5.mem 9 ≠ 0 := by
      have h1 : u - 1 + (1 - u) ≠ 0 := by omega
      have h2 : u - 1 + (1 - u) < 2 ^ w := by omega
      rw [v9', Nat.mod_eq_of_lt h2]; exact h1
    obtain ⟨S6, e6, hpc6, hm6, hi6, -, ho6⟩ := Exec.pcu
      (x_jzero_neg (w := w) (s := S5) (fetch hf (i := 5) (by omega) rfl) (by omega) nz)
    obtain ⟨S7, e7, hpc7, hm7, hi7, -, ho7⟩ := Exec.pcu
      (x_jump (w := w) (s := S6) (fetch hf (i := 6) (by omega) rfl))
    right
    refine ⟨never_of_terminal hrun hs (fun y _ h => by rw [hso] at h; cases h; exact hu1 rfl),
      7, le_rfl, S7, (c5.trans e6).trans e7, by rw [hpc7, hdead], fun a ha => ?_,
      by rw [hm7, hm6]; exact hW5, by rw [hi7, hi6, hio5.1], by rw [ho7, ho6, hio5.2]⟩
    rw [hm7, hm6, fr5 a (by omega) (by omega) (by omega)]

/-! ### Initialization -/

theorem pow_sub_one_div {w a : ℕ} (h : a ≤ w) : (2 ^ w - 1) / 2 ^ a = 2 ^ (w - a) - 1 := by
  have e : 2 ^ w = 2 ^ (w - a) * 2 ^ a := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (w - a) := Nat.one_le_two_pow
  rw [e]
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, one_mul]; omega
  · rw [Nat.sub_add_cancel h2, ← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (by positivity : 2 ^ (w - a) * 2 ^ a ≠ 0))]
    have : 2 ^ (w - a) * 2 ^ a ≥ 2 ^ (w - a) := Nat.le_mul_of_pos_right _ (by positivity)
    omega

/-- A thread at the start of its run. -/
theorem rel_fresh (G : Glob w K x) (b : Bool) (ovf : ℕ) (S : State) (hm : WordMem w S.mem)
    (h0 : S.mem 0 = 0) (h1 : S.mem 1 = 1) (h2 : S.mem 2 = 2 ^ (w - K) - 1)
    (h3 : S.mem 3 = (geo w K b).base) (h4 : S.mem 4 = 0) (h5 : S.mem 5 = x.length)
    (h6 : S.mem 6 = ob b) (h7 : S.mem 7 = 0) (h8 : S.mem 8 = 2) (h16 : S.mem 16 = x.length)
    (h17 : S.mem 17 = 0) (hz : ∀ a, 64 ≤ a → S.mem a = 0) (hi : S.input = x)
    (ho : S.out = []) : TRel w K x b ovf (initState x) S := by
  obtain ⟨hB1, hB2, -⟩ := base_facts G b
  have hob := ob_ge b
  have hw := w64 G
  have hxl := G.xl
  have hnW : ∀ a, a = 16 ∨ a = 17 → ¬ (geo w K b).W a := by
    intro a ha
    simp only [Geo.W, geo_v, geo_ob, geo_cap]
    omega
  refine
    { env := ⟨hm, h0, h1, h2, h3, hB2, by omega, by simp only [geo_v]; omega⟩
      cword := fun a => Nat.two_pow_pos _
      mem := fun a ha => by rw [hz _ (by omega)]; rfl
      input := rfl
      cur := by rw [h4]; exact Nat.zero_le _
      inp := by rw [h4]; rfl
      tot := h5
      table := ⟨[x], ⟨hnW 16 (Or.inl rfl), hnW 17 (Or.inr rfl), ?_, trivial⟩, by simp⟩
      tb16 := le_rfl
      tbw := by simp only [List.length_cons, List.length_nil]; omega
      out := ⟨ho, h6, by rw [h7]; rfl, h8, Nat.zero_le _, by simp only [geo_ob]; omega,
        by simp only [geo_ob, geo_cap]; omega,
        Or.inl (by simp only [geo_ob, geo_cap]; omega), fun j hj => absurd hj (by simp [initState])⟩ }
  show x = (S.input.drop (S.mem (16 + 1))).take (S.mem 16) ∧
    (0 < S.mem 16 → S.mem (16 + 1) + S.mem 16 ≤ S.input.length) ∧ S.input.length < 2 ^ w
  rw [h16, show S.mem (16 + 1) = 0 from h17, hi]
  exact ⟨by simp, by omega, hxl⟩

/-- The initialization: thread `0` is loaded and thread `1` is saved,
both at the start of their runs. -/
theorem init_spec (G : Glob w K x) :
    ∃ S, Exec w (parProg K P₀ P₁) 15 (initState x) S ∧ S.pc = slotA P₀ P₁ false 0 0 ∧
      TRel w K x false (deadA P₀ P₁ false 0) (initState x) S ∧
      Other w K x true (initState x) S ∧ WordMem w S.mem := by
  have hf : Fits (parProg K P₀ P₁) 0 (initCode K) := by
    intro i hi; simp only [parProg, Nat.zero_add]; exact List.getElem?_append_left hi
  have kw := G.kw
  have k8 := G.k8
  have hxl := G.xl
  obtain ⟨hP, hV, h4P⟩ := lay G
  have hw := w64 G
  have hm0 : WordMem w (initState x).mem := fun _ => two_pow_pos w
  have hpc0 : (initState x).pc = 0 := rfl
  obtain ⟨S1, e1, hpc1, hm1, hi1, -, ho1⟩ := (x_set (w := w) (s := initState x)
    (fetch hf (i := 0) (by simp [hpc0]) rfl) (by omega)).upd
  obtain ⟨S2, e2, hpc2, hm2, hi2, -, ho2⟩ := (x_not (w := w) (s := S1)
    (fetch hf (i := 1) (by omega) rfl) (by omega) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, -, ho3⟩ := (x_set (w := w) (s := S2)
    (fetch hf (i := 2) (by omega) rfl) (by omega)).upd
  obtain ⟨S4, e4, hpc4, hm4, hi4, -, ho4⟩ := (x_shiftl (w := w) (s := S3)
    (fetch hf (i := 3) (by omega) rfl) (by omega) (by omega) (by omega)).upd
  have c4 := ((e1.trans e2).trans e3).trans e4
  obtain ⟨S5, e5, hpc5, hm5, hi5, -, ho5⟩ := (x_div (w := w) (s := S4)
    (fetch hf (i := 4) (by omega) rfl) (hm0.exec c4) (by omega) (by omega) (by omega)).upd
  obtain ⟨S6, e6, hpc6, hm6, hi6, -, ho6⟩ := (x_inputLength (w := w) (s := S5)
    (fetch hf (i := 5) (by omega) rfl) (by omega)).upd
  obtain ⟨S7, e7, hpc7, hm7, hi7, -, ho7⟩ := (x_set (w := w) (s := S6)
    (fetch hf (i := 6) (by omega) rfl) (by omega)).upd
  obtain ⟨S8, e8, hpc8, hm8, hi8, -, ho8⟩ := (x_add (w := w) (s := S7)
    (fetch hf (i := 7) (by omega) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S9, e9, hpc9, hm9, hi9, -, ho9⟩ := (x_not (w := w) (s := S8)
    (fetch hf (i := 8) (by omega) rfl) (by omega) (by omega)).upd
  obtain ⟨S10, e10, hpc10, hm10, hi10, -, ho10⟩ := (x_set (w := w) (s := S9)
    (fetch hf (i := 9) (by omega) rfl) (by omega)).upd
  have c10 := (((((c4.trans e5).trans e6).trans e7).trans e8).trans e9).trans e10
  obtain ⟨S11, e11, hpc11, hm11, hi11, -, ho11⟩ := (x_div (w := w) (s := S10)
    (fetch hf (i := 10) (by omega) rfl) (hm0.exec c10) (by omega) (by omega) (by omega)).upd
  obtain ⟨S12, e12, hpc12, hm12, hi12, -, ho12⟩ := (x_add (w := w) (s := S11)
    (fetch hf (i := 11) (by omega) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S13, e13, hpc13, hm13, hi13, -, ho13⟩ := (x_add (w := w) (s := S12)
    (fetch hf (i := 12) (by omega) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S14, e14, hpc14, hm14, hi14, -, ho14⟩ := (x_set (w := w) (s := S13)
    (fetch hf (i := 13) (by omega) rfl) (by omega)).upd
  obtain ⟨S15, e15, hpc15, hm15, hi15, -, ho15⟩ := (x_set (w := w) (s := S14)
    (fetch hf (i := 14) (by omega) rfl) (by omega)).upd
  have c15 := ((((c10.trans e11).trans e12).trans e13).trans e14).trans e15
  have hW : WordMem w S15.mem := hm0.exec c15
  -- the values
  have z0 : (initState x).mem = fun _ => 0 := rfl
  have a1 : S1.mem 1 = 1 := by rw [hm1, if_pos rfl]; exact Nat.mod_eq_of_lt (by omega)
  have a2 : S2.mem 2 = 2 ^ w - 1 := by simp [hm2, hm1, z0]
  have hKw : K < 2 ^ w := lt_trans kw Nat.lt_two_pow_self
  have a3 : S3.mem 9 = K := by rw [hm3, if_pos rfl]; exact Nat.mod_eq_of_lt hKw
  have a4 : S4.mem 10 = 2 ^ K := by
    have : S3.mem 1 = 1 := by simp [hm3, hm2, a1]
    rw [hm4, if_pos rfl, this, a3, one_mul,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) kw)]
  have a5 : S5.mem 2 = 2 ^ (w - K) - 1 := by
    have : S4.mem 2 = 2 ^ w - 1 := by simp [hm4, hm3, a2]
    rw [hm5, if_pos rfl, this, a4, pow_sub_one_div (by omega)]
  have hin5 : S5.input = x := by rw [hi5, hi4, hi3, hi2, hi1]; rfl
  have a6 : S6.mem 5 = x.length := by
    rw [hm6, if_pos rfl, hin5]; exact Nat.mod_eq_of_lt (by omega)
  have a7 : S7.mem 8 = 2 := by rw [hm7, if_pos rfl]; exact Nat.mod_eq_of_lt (by omega)
  have a8 : S8.mem 16 = x.length := by
    have h1 : S7.mem 5 = x.length := by simp [hm7, a6]
    have h2 : S7.mem 0 = 0 := by simp [hm7, hm6, hm5, hm4, hm3, hm2, hm1, z0]
    rw [hm8, if_pos rfl, h1, h2, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
  have a9 : S9.mem 9 = 2 ^ w - 1 := by
    simp [hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, z0]
  have a10 : S10.mem 10 = 4 := by rw [hm10, if_pos rfl]; exact Nat.mod_eq_of_lt (by omega)
  have a11 : S11.mem 9 = 2 ^ (w - 2) - 1 := by
    have : S10.mem 9 = 2 ^ w - 1 := by simp [hm10, a9]
    rw [hm11, if_pos rfl, this, a10, show (4 : ℕ) = 2 ^ 2 by norm_num, pow_sub_one_div (by omega)]
  have a12 : S12.mem 3 = 2 ^ (w - 2) := by
    have : S11.mem 1 = 1 := by simp [hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, a1]
    rw [hm12, if_pos rfl, a11, this, Nat.sub_add_cancel Nat.one_le_two_pow]
    exact Nat.mod_eq_of_lt (by omega)
  have a13 : S13.mem 44 = 2 ^ (w - 2) * 2 := by
    have : S12.mem 3 = 2 ^ (w - 2) := a12
    rw [hm13, if_pos rfl, this, Nat.mod_eq_of_lt (by omega)]; ring
  have a14 : S14.mem 6 = 48 := by rw [hm14, if_pos rfl]; exact Nat.mod_eq_of_lt (by omega)
  have a15 : S15.mem 46 = 52 := by rw [hm15, if_pos rfl]; exact Nat.mod_eq_of_lt (by omega)
  have zz : ∀ a, a ≠ 1 → a ≠ 2 → a ≠ 3 → a ≠ 5 → a ≠ 6 → a ≠ 8 → a ≠ 9 → a ≠ 10 → a ≠ 16 →
      a ≠ 44 → a ≠ 46 → S15.mem a = 0 := by
    intro a n1 n2 n3 n5 n6 n8 n9 n10 n16 n44 n46
    simp [hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, z0,
      n1, n2, n3, n5, n6, n8, n9, n10, n16, n44, n46]
  have f1 : S15.mem 1 = 1 := by
    simp [hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, a1]
  have f2 : S15.mem 2 = 2 ^ (w - K) - 1 := by
    simp [hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, a5]
  have f3 : S15.mem 3 = 2 ^ (w - 2) := by simp [hm15, hm14, hm13, a12]
  have f5 : S15.mem 5 = x.length := by
    simp [hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, a6]
  have f6 : S15.mem 6 = 48 := by simp [hm15, a14]
  have f8 : S15.mem 8 = 2 := by simp [hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, a7]
  have f16 : S15.mem 16 = x.length := by
    simp [hm15, hm14, hm13, hm12, hm11, hm10, hm9, a8]
  have f44 : S15.mem 44 = 2 ^ (w - 2) * 2 := by simp [hm15, hm14, a13]
  have f46 : S15.mem 46 = 52 := a15
  have fz : ∀ a, 64 ≤ a → S15.mem a = 0 := fun a ha =>
    zz a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have zc : ∀ a, a = 0 ∨ a = 4 ∨ a = 7 ∨ a = 17 ∨ a = 45 ∨ a = 47 → S15.mem a = 0 := by
    intro a ha
    apply zz <;> omega
  have hin : S15.input = x := by
    rw [hi15, hi14, hi13, hi12, hi11, hi10, hi9, hi8, hi7, hi6, hin5]
  have hout : S15.out = [] := by
    rw [ho15, ho14, ho13, ho12, ho11, ho10, ho9, ho8, ho7, ho6, ho5, ho4, ho3, ho2, ho1]; rfl
  refine ⟨S15, c15, ?_, ?_, ?_, hW⟩
  · rw [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2,
      hpc1, hpc0]; simp [slotA, idx]
  · exact rel_fresh G false _ S15 hW (zc 0 (by omega)) f1 f2 (by rw [geo_base, f3]; simp)
      (zc 4 (by omega)) f5 (by rw [f6]; rfl) (zc 7 (by omega)) f8 f16 (zc 17 (by omega)) fz
      hin hout
  · have s3 : swp true S15.mem 3 = 2 ^ (w - 2) * 2 := by simp [swp, sv, f44]
    have s4 : swp true S15.mem 4 = 0 := by simp [swp, sv]; exact zc 45 (by omega)
    have s6 : swp true S15.mem 6 = 52 := by simp [swp, sv, f46]
    have s7 : swp true S15.mem 7 = 0 := by simp [swp, sv]; exact zc 47 (by omega)
    have so : ∀ a, a ≠ 3 → a ≠ 4 → a ≠ 6 → a ≠ 7 → swp true S15.mem a = S15.mem a :=
      fun a h3 h4 h6 h7 => swp_of_ne true _ h3 h4 h6 h7
    exact rel_fresh G true _ (swpS true S15) (swp_word hW)
      (by show swp true S15.mem 0 = 0; rw [so 0 (by omega) (by omega) (by omega) (by omega)];
          exact zc 0 (by omega))
      (by show swp true S15.mem 1 = 1; rw [so 1 (by omega) (by omega) (by omega) (by omega)];
          exact f1)
      (by show swp true S15.mem 2 = _; rw [so 2 (by omega) (by omega) (by omega) (by omega)];
          exact f2)
      (by show swp true S15.mem 3 = _; rw [s3, geo_base]; simp)
      s4
      (by show swp true S15.mem 5 = _; rw [so 5 (by omega) (by omega) (by omega) (by omega)];
          exact f5)
      (by show swp true S15.mem 6 = _; rw [s6]; rfl)
      s7
      (by show swp true S15.mem 8 = _; rw [so 8 (by omega) (by omega) (by omega) (by omega)];
          exact f8)
      (by show swp true S15.mem 16 = _; rw [so 16 (by omega) (by omega) (by omega) (by omega)];
          exact f16)
      (by show swp true S15.mem 17 = _; rw [so 17 (by omega) (by omega) (by omega) (by omega)];
          exact zc 17 (by omega))
      (fun a ha => by
        show swp true S15.mem a = 0
        rw [so a (by omega) (by omega) (by omega) (by omega)]; exact fz a ha)
      hin hout

end Lax185574Proofs.RamPar
