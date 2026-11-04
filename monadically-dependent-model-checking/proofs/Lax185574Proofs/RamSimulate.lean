import Lax185574Proofs.RamRewrite

/-!
Simulation of a program one word bit lower on a rewritten input.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program} {s : ℕ}

/-- The cells a launch writes: temporaries, the total, the table and the
evaluation cells. -/
def LaunchW (tb N te D : ℕ) (a : ℕ) : Prop :=
  a = rT ∨ a = rU ∨ a = rTot ∨ (tb ≤ a ∧ a < tb + 2 * N) ∨ (te ≤ a ∧ a < te + D)

/-- Starting a simulation: compute the segment table of `ρ`. Afterwards
the machine represents the initial state of the simulated program on
`ρ xs`. -/
theorem launch_spec (srcs : Fin s → Src) (tb te D : ℕ) (g : Geo) (mode : OutMode)
    (xs : Fin s → List ℕ) (ρ : Rewrite s) (A : ℕ) (S : State)
    (hf : Fits p A (rwCode srcs te tb ρ 0 A)) (hpc : S.pc = A)
    (E : Env w g.v g.base S) (hsrc : ∀ j, SrcOK w (fun a => g.W a ∨ LaunchW tb ρ.length te D a)
      S (srcs j) (xs j))
    (hfit : ρ.Fits w xs) (hseg : ∀ seg ∈ ρ, seg.size + 3 ≤ D)
    (htb : 16 ≤ tb) (hte : tb + 2 * ρ.length ≤ te) (hD : te + D < 2 ^ w)
    (htab : ∀ a, tb ≤ a → a < tb + 2 * ρ.length → ¬ g.W a)
    (hcur : S.mem rCur = 0) (htot : S.mem rTot = 0)
    (hreg : ∀ a < 2 ^ g.v, S.mem (g.base + a) = 0)
    (hregL : ∀ a, LaunchW tb ρ.length te D a → ¬ (g.base ≤ a ∧ a < g.base + 2 ^ g.v))
    (hout : OutRel w g S.out (initState (ρ.apply xs)) S mode)
    (houtL : ∀ a, LaunchW tb ρ.length te D a → ¬ (g.ob ≤ a ∧ a < g.ob + g.cap)) :
    ∃ n ≤ 11 * (ρ.map (·.cost xs)).sum, ∃ S', Exec w p n S S' ∧
      S'.pc = A + (rwCode srcs te tb ρ 0 A).length ∧
      Rel w g (ρ.map (segKind srcs)) tb mode (ρ.apply xs) S.out (initState (ρ.apply xs)) S' ∧
      (∀ c, ¬ LaunchW tb ρ.length te D c → S'.mem c = S.mem c) ∧
      S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out := by
  obtain ⟨hlen, happ, hsegs⟩ := hfit
  have hw := E.hw
  obtain ⟨n, hn, S1, e1, hpc1, htab1, htot1, fr1, hi1, hn1, ho1⟩ :=
    rw_spec srcs te tb D xs (fun a => g.W a ∨ LaunchW tb ρ.length te D a) g.W
      (fun a h => Or.inl h) (by omega) htb hD ρ 0 A 0 S hf hpc E.word E.zero E.one hsrc
      (fun seg hs => ⟨hsegs seg hs, hseg seg hs⟩)
      (fun a ha => Or.inr (by simp only [LaunchW]; omega)) (fun a h1 h2 => htab a h1 (by omega))
      (by omega) htot (by omega)
  have hfr : ∀ c, ¬ LaunchW tb ρ.length te D c → S1.mem c = S.mem c := by
    intro c hc
    simp only [LaunchW] at hc
    exact fr1 c (by omega) (by omega) (by omega) (by omega) (by omega)
  have hL : ∀ c, c < 16 → c ≠ rT → c ≠ rU → c ≠ rTot → S1.mem c = S.mem c := by
    intro c h1 h2 h3 h4
    exact hfr c (by simp only [LaunchW]; omega)
  refine ⟨n, by simpa using hn, S1, e1, hpc1, ?_, hfr, hi1, hn1, ho1⟩
  refine
    { env := ⟨E.word.exec e1, by rw [hL _ (by omega) (by omega) (by omega) (by omega)]; exact E.zero,
        by rw [hL _ (by omega) (by omega) (by omega) (by omega)]; exact E.one,
        by rw [hL _ (by omega) (by omega) (by omega) (by omega)]; exact E.mask,
        by rw [hL _ (by omega) (by omega) (by omega) (by omega)]; exact E.baseCell,
        E.room, E.low, E.hv⟩
      cword := fun a => by simp [initState]
      mem := fun a ha => by
        rw [hfr _ (fun h => hregL _ h ⟨by omega, by omega⟩), hreg a ha]; rfl
      input := rfl
      cur := by rw [hL _ (by omega) (by omega) (by omega) (by omega), hcur]; omega
      inp := by rw [hL _ (by omega) (by omega) (by omega) (by omega), hcur]; rfl
      tot := by rw [htot1]; simp
      table := ⟨_, htab1, by simp [Rewrite.apply]⟩
      tb16 := htb
      tbw := by simp; omega
      out := ?_ }
  cases mode with
  | direct => simp [OutRel, initState, ho1]
  | buffer ovf =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hout
      refine ⟨ho1, by rw [hL _ (by omega) (by omega) (by omega) (by omega)]; exact h2,
        by rw [hL _ (by omega) (by omega) (by omega) (by omega)]; exact h3,
        by rw [hL _ (by omega) (by omega) (by omega) (by omega)]; exact h4, h5, h6, h7, h8,
        fun j hj => by simp [initState] at hj⟩

/-! ### The simulator -/

/-- The only source: the machine's input, its length in cell 15. -/
def simSrcs : Fin 1 → Src := fun _ => ⟨.input, 15⟩

def simD (ρ : Rewrite 1) : ℕ := (ρ.map Segment.size).sum + 3
def simTe (ρ : Rewrite 1) : ℕ := 16 + 2 * ρ.length
def simBase (ρ : Rewrite 1) : ℕ := simTe ρ + simD ρ + 1
def simKs (ρ : Rewrite 1) : List SegKind := ρ.map (segKind simSrcs)

/-- Constants one and two, the mask `(2 ^ w - 1) / 2`, the base of the
simulated memory, and the input length. -/
def simInit (ρ : Rewrite 1) : Program :=
  [.set rOne 1, .set rT 2, .not rMask rZ, .div rMask rMask rT, .set rBase (simBase ρ),
    .inputLength 15]

def simH (ρ : Rewrite 1) : ℕ := 6 + (rwCode simSrcs (simTe ρ) 16 ρ 0 6).length

def simExit (p₀ : Program) (ρ : Rewrite 1) : ℕ := simH ρ + blockLen (simKs ρ) * p₀.length

def simCode (p₀ : Program) (ρ : Rewrite 1) : Code where
  ks := simKs ρ
  tb := 16
  mode := .direct
  tgt := fun l => if l < p₀.length then simH ρ + blockLen (simKs ρ) * l else simExit p₀ ρ
  exit := simExit p₀ ρ

def simProg (p₀ : Program) (ρ : Rewrite 1) : Program :=
  simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6 ++
    blocks (simCode p₀ ρ) (simH ρ) (blockLen (simKs ρ)) p₀ ++ [.halt]

theorem segment_size_le (ρ : Rewrite 1) : ∀ seg ∈ ρ, seg.size + 3 ≤ simD ρ := by
  intro seg hs
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Segment.size) hs)
  simp only [simD]; omega

theorem two_pow_sub_one_div {w : ℕ} (hw : 1 ≤ w) : (2 ^ w - 1) / 2 = 2 ^ (w - 1) - 1 := by
  have h : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
  have : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
  omega

theorem simPre_length (ρ : Rewrite 1) :
    (simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6).length = simH ρ := by
  simp [simInit, simH]; omega

theorem simProg_eq (p₀ : Program) (ρ : Rewrite 1) :
    simProg p₀ ρ = (simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6) ++
      blocks (simCode p₀ ρ) (simH ρ) (blockLen (simKs ρ)) p₀ ++ [.halt] := rfl

theorem simCode_tgt (p₀ : Program) (ρ : Rewrite 1) (l : ℕ) :
    (simCode p₀ ρ).tgt l =
      if l < p₀.length then simH ρ + blockLen (simKs ρ) * l else (simCode p₀ ρ).exit := rfl

/-- The start of the simulator: after the initialization and the
launch, the machine represents the initial state of `p₀` on the
rewritten input, at the block of counter `0`. -/
theorem sim_start (p₀ : Program) (ρ : Rewrite 1) (w : ℕ) (x : List ℕ)
    (hK : simBase ρ ≤ 2 ^ (w - 1)) (hfit : ρ.Fits w (fun _ => x)) :
    ∃ n₀ ≤ 6 + 11 * (ρ.map (·.cost (fun _ => x))).sum, ∃ S7,
      Exec w (simProg p₀ ρ) n₀ (initState x) S7 ∧
      S7.pc = (simCode p₀ ρ).tgt (initState (ρ.apply fun _ => x)).pc ∧
      Rel w ⟨w - 1, simBase ρ, 0, 0⟩ (simKs ρ) 16 .direct (ρ.apply fun _ => x) []
        (initState (ρ.apply fun _ => x)) S7 := by
  set p := simProg p₀ ρ with hp
  set base := simBase ρ
  have hbase : 19 ≤ base := by simp only [base, simBase, simTe, simD]; omega
  have hw1 : 1 ≤ w := by
    by_contra h
    simp only [show w = 0 by omega, Nat.zero_sub, pow_zero] at hK
    omega
  have h2w : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
  have hw16 : 16 < 2 ^ w := by omega
  set x' := ρ.apply fun _ => x
  -- the initialization
  have hfI : Fits p 0 (simInit ρ) := by
    rw [hp, simProg, List.append_assoc, List.append_assoc]; exact fits_self _ _
  set S0 := initState x
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_set (w := w) (s := S0)
    (fetch hfI (i := 0) rfl rfl) (by omega)).upd
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_set (w := w) (s := S1)
    (fetch hfI (i := 1) (by simp [hpc1, S0, initState]) rfl) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_not (w := w) (s := S2)
    (fetch hfI (i := 2) (by simp [hpc2, hpc1, S0, initState]) rfl) (by omega) (by omega)).upd
  have hW2 : WordMem w S2.mem := fun c => by
    rw [hm2, hm1]; split_ifs <;> first | exact Nat.mod_lt _ (by positivity) | simp [S0, initState]
  obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_div (w := w) (s := S3)
    (fetch hfI (i := 3) (by simp [hpc3, hpc2, hpc1, S0, initState]) rfl)
    (hW2.exec e3) (by omega) (by omega) (by omega)).upd
  obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_set (w := w) (s := S4)
    (fetch hfI (i := 4) (by simp [hpc4, hpc3, hpc2, hpc1, S0, initState]) rfl) (by omega)).upd
  obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_inputLength (w := w) (s := S5)
    (fetch hfI (i := 5) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, S0, initState]) rfl)
    (by omega)).upd
  have hx : x.length < 2 ^ w := hfit.1 0
  have hmask : S6.mem rMask = 2 ^ (w - 1) - 1 := by
    simp [hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]
    rw [Nat.mod_eq_of_lt (show 2 < 2 ^ w by omega), two_pow_sub_one_div hw1]
  have hm6' : ∀ c, c ≠ rOne → c ≠ rT → c ≠ rMask → c ≠ rBase → c ≠ 15 → S6.mem c = 0 := by
    intro c h1 h2 h3 h4 h5
    rw [hm6, if_neg h5, hm5, if_neg h4, hm4, if_neg h3, hm3, if_neg h3, hm2, if_neg h2, hm1,
      if_neg h1]; rfl
  have hW6 : WordMem w S6.mem := (hW2.exec e3).exec ((e4.trans e5).trans e6)
  have hin6 : S6.input = x := by rw [hi6, hi5, hi4, hi3, hi2, hi1]; rfl
  have E6 : Env w (w - 1) base S6 :=
    ⟨hW6, hm6' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      by rw [hm6, if_neg (by decide), hm5, if_neg (by decide), hm4, if_neg (by decide), hm3,
        if_neg (by decide), hm2, if_neg (by decide), hm1, if_pos rfl,
        Nat.mod_eq_of_lt (by omega)],
      hmask, by rw [hm6, if_neg (by decide), hm5, if_pos rfl, Nat.mod_eq_of_lt (by omega)],
      by omega, by omega, by omega⟩
  -- the launch
  have hsrc0 : SrcOK w (fun a => (⟨w - 1, base, 0, 0⟩ : Geo).W a ∨
      LaunchW 16 ρ.length (simTe ρ) (simD ρ) a) S6 ⟨.input, 15⟩ x := by
    have hin5 : S5.input = x := by rw [hi5, hi4, hi3, hi2, hi1]; rfl
    refine ⟨by rw [hm6, if_pos rfl, Nat.mod_eq_of_lt (by rw [hin5]; exact hx), hin5], hx,
      by show 15 < 2 ^ w; omega, ?_, hin6⟩
    simp only [Geo.W, LaunchW, simTe]
    simp only [base, simBase, simTe] at hbase ⊢
    omega
  have hreg : ∀ a < 2 ^ (w - 1), S6.mem (base + a) = 0 := fun a ha =>
    hm6' _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have hfR : Fits p 6 (rwCode simSrcs (simTe ρ) 16 ρ 0 6) := by
    have := fits_self (simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6)
      (blocks (simCode p₀ ρ) (simH ρ) (blockLen (simKs ρ)) p₀ ++ [.halt])
    rw [← List.append_assoc] at this
    exact (fits_append.1 this).2
  obtain ⟨n₁, hn₁, S7, e7, hpc7, R7, -, -, -, ho7⟩ := launch_spec simSrcs 16 (simTe ρ) (simD ρ)
    ⟨w - 1, base, 0, 0⟩ .direct (fun _ => x) ρ 6 S6 hfR
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; rfl) E6 (fun _ => hsrc0)
    hfit (segment_size_le ρ) le_rfl (by simp [simTe])
    (by simp only [simTe, simBase, base] at *; omega)
    (fun a h1 h2 => by simp only [Geo.W, base, simBase, simTe] at *; omega)
    (hm6' _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (hm6' _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hreg (fun a ha => by simp only [LaunchW, base, simBase, simTe] at *; omega)
    (by simp [OutRel, initState]) (fun a _ => by simp)
  have hpc7' : S7.pc = (simCode p₀ ρ).tgt (initState x').pc := by
    rw [hpc7]
    simp only [simCode, initState, simExit, Nat.mul_zero, Nat.add_zero]
    split_ifs with h
    · simp [simH]
    · have : p₀.length = 0 := by omega
      simp [simH, this]
  have e := (((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7
  refine ⟨_, ?_, S7, e, hpc7', ?_⟩
  · omega
  · have hout : S6.out = [] := by simp [ho6, ho5, ho4, ho3, ho2, ho1, S0, initState]
    rw [hout] at R7
    exact R7

theorem simulate_run (p₀ : Program) (ρ : Rewrite 1) (w : ℕ) (x y : List ℕ) (t : ℕ)
    (hK : simBase ρ ≤ 2 ^ (w - 1)) (hfit : ρ.Fits w (fun _ => x))
    (hrun : RunsTo (w - 1) p₀ (ρ.apply fun _ => x) y t) :
    ∃ t' ≤ (stepBound (simKs ρ) + 20) * t + (stepBound (simKs ρ) + 20) * ρ.cost (fun _ => x),
      RunsTo w (simProg p₀ ρ) x y t' := by
  set p := simProg p₀ ρ with hp
  set x' := ρ.apply fun _ => x
  obtain ⟨k, s_end, hr, hs, hy, ht⟩ := hrun
  obtain ⟨n₀, hn₀, S7, e7, hpc7', R7⟩ := sim_start p₀ ρ w x hK hfit
  -- the simulation
  have hpre := simPre_length ρ
  obtain ⟨n₂, hn₂, S8, e8, hpc8, R8, -⟩ := sim_run (simCode p₀ ρ) (g := ⟨w - 1, simBase ρ, 0, 0⟩)
    (p := p) (pre := simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6) (post := [.halt])
    rfl hpre le_rfl (fun l => rfl) k (initState x') s_end S7 hr hs (fun ovf h => by cases h)
    R7 hpc7'
  have hout8 : S8.out = y := by
    have := R8.out
    simp only [OutRel, simCode] at this
    rw [this]
    simp [hy]
  have hlen : (simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6 ++
      blocks (simCode p₀ ρ) (simH ρ) (blockLen (simKs ρ)) p₀).length = simExit p₀ ρ := by
    rw [List.length_append, hpre,
      blocks_length (simCode p₀ ρ) (simH ρ) (blockLen (simKs ρ)) p₀ le_rfl]; rfl
  have hhalt : p[S8.pc]? = some .halt := by
    rw [hpc8]
    show (simInit ρ ++ rwCode simSrcs (simTe ρ) 16 ρ 0 6 ++
      blocks (simCode p₀ ρ) (simH ρ) (blockLen (simKs ρ)) p₀ ++ [.halt])[simExit p₀ ρ]? = _
    rw [← hlen, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
  have e := e7.trans e8
  refine ⟨_, ?_, runsTo_of_exec e (step_halt hhalt) hout8⟩
  rw [terminalCost_of_getElem? hhalt]
  have hcost : ρ.cost (fun _ => x) = (ρ.map (·.cost (fun _ => x))).sum + 1 := rfl
  have hkt : k ≤ t := by rw [ht]; omega
  have hn₂' : n₂ ≤ stepBound (simKs ρ) * (k + 1) := hn₂
  have h1 := Nat.mul_le_mul_left (stepBound (simKs ρ)) hkt
  rw [hcost]
  generalize stepBound (simKs ρ) = SB at *
  generalize (ρ.map (·.cost (fun _ => x))).sum = C at *
  have h2 : SB * (k + 1) = SB * k + SB := by ring
  have h3 : (SB + 20) * t = SB * t + 20 * t := by ring
  have h4 : (SB + 20) * (C + 1) = SB * C + SB + 20 * C + 20 := by ring
  rw [h3, h4]
  omega

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim

/-- **Simulation** one word bit lower, on a rewrite of the input. Each
instruction of `p₀` becomes a block of `O(|ρ|)` instructions. `K`
depends on `p₀` and `ρ`, and the room hypothesis `K ≤ 2 ^ (w - 1)`
makes the simulator's own cells fit below the simulated memory. -/
theorem simulate :
    ∀ (p₀ : Program) (ρ : Rewrite 1), ∃ (p : Program) (K : ℕ),
      ∀ (w : ℕ) (x y : List ℕ) (t : ℕ),
        K ≤ 2 ^ (w - 1) → ρ.Fits w (fun _ => x) →
        RunsTo (w - 1) p₀ (ρ.apply fun _ => x) y t →
        ∃ t' ≤ K * t + K * ρ.cost (fun _ => x), RunsTo w p x y t' := by
  intro p₀ ρ
  refine ⟨simProg p₀ ρ, simBase ρ + stepBound (simKs ρ) + 20, fun w x y t hK hfit hrun => ?_⟩
  obtain ⟨t', ht', hr⟩ := simulate_run p₀ ρ w x y t (by omega) hfit hrun
  refine ⟨t', le_trans ht' ?_, hr⟩
  have h1 := Nat.mul_le_mul_right t
    (show stepBound (simKs ρ) + 20 ≤ simBase ρ + stepBound (simKs ρ) + 20 by omega)
  have h2 := Nat.mul_le_mul_right (ρ.cost fun _ => x)
    (show stepBound (simKs ρ) + 20 ≤ simBase ρ + stepBound (simKs ρ) + 20 by omega)
  omega

end Lax185574Proofs.Simulate
