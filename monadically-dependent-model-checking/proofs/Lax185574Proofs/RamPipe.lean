import Lax185574Proofs.RamSimulate

/-!
Piping one simulated program into another: the first runs on a rewrite
of the input with its output captured in memory, the second runs on a
rewrite of that output and the input.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program} {s : ℕ}

/-- One phase: launch the simulation of `p₀` on `ρ xs` and run it to its
exit. -/
theorem phase_spec (srcs : Fin s → Src) (tb te D : ℕ) (g : Geo) (mode : OutMode)
    (tgt : ℕ → ℕ) (exit : ℕ) (xs : Fin s → List ℕ) (ρ : Rewrite s) (p₀ pre post : Program)
    (H L A : ℕ)
    (hp : p = pre ++ blocks ⟨ρ.map (segKind srcs), tb, mode, tgt, exit⟩ H L p₀ ++ post)
    (hpre : pre.length = H) (hL : blockLen (ρ.map (segKind srcs)) ≤ L)
    (htgt : ∀ l, tgt l = if l < p₀.length then H + L * l else exit)
    (hexit : exit = H + L * p₀.length)
    (hA : A + (rwCode srcs te tb ρ 0 A).length = H)
    (hf : Fits p A (rwCode srcs te tb ρ 0 A)) (S : State) (hpc : S.pc = A)
    (E : Env w g.v g.base S) (hsrc : ∀ j, SrcOK w (fun a => g.W a ∨ LaunchW tb ρ.length te D a)
      S (srcs j) (xs j))
    (hfit : ρ.Fits w xs) (hseg : ∀ seg ∈ ρ, seg.size + 3 ≤ D)
    (htb : 16 ≤ tb) (hte : tb + 2 * ρ.length ≤ te) (hD : te + D < 2 ^ w)
    (htab : ∀ a, tb ≤ a → a < tb + 2 * ρ.length → ¬ g.W a)
    (hcur : S.mem rCur = 0) (htot : S.mem rTot = 0)
    (hreg : ∀ a < 2 ^ g.v, S.mem (g.base + a) = 0)
    (hregL : ∀ a, LaunchW tb ρ.length te D a → ¬ (g.base ≤ a ∧ a < g.base + 2 ^ g.v))
    (hout : OutRel w g S.out (initState (ρ.apply xs)) S mode)
    (houtL : ∀ a, LaunchW tb ρ.length te D a → ¬ (g.ob ≤ a ∧ a < g.ob + g.cap))
    (k : ℕ) (s_end : State) (hr : run g.v p₀ k (initState (ρ.apply xs)) = some s_end)
    (hs : step g.v p₀ s_end = none)
    (hcap : ∀ ovf, mode = .buffer ovf → s_end.out.length ≤ g.cap) :
    ∃ n ≤ 11 * (ρ.map (·.cost xs)).sum + stepBound (ρ.map (segKind srcs)) * (k + 1),
      ∃ S', Exec w p n S S' ∧ S'.pc = exit ∧
        Rel w g (ρ.map (segKind srcs)) tb mode (ρ.apply xs) S.out s_end S' ∧
        (∀ c, ¬ LaunchW tb ρ.length te D c → ¬ g.W c → S'.mem c = S.mem c) ∧
        S'.input = S.input ∧ S'.inp = S.inp := by
  obtain ⟨n₁, hn₁, S1, e1, hpc1, R1, fr1, hi1, hn1, ho1⟩ := launch_spec srcs tb te D g mode xs ρ
    A S hf hpc E hsrc hfit hseg htb hte hD htab hcur htot hreg hregL hout houtL
  have hpc1' : S1.pc = tgt (initState (ρ.apply xs)).pc := by
    rw [hpc1, hA, htgt]
    show H = if 0 < p₀.length then H + L * 0 else exit
    split_ifs with h
    · simp
    · rw [hexit, show p₀.length = 0 by omega, Nat.mul_zero, Nat.add_zero]
  obtain ⟨n₂, hn₂, S2, e2, hpc2, R2, fr2⟩ := sim_run (g := g)
    ⟨ρ.map (segKind srcs), tb, mode, tgt, exit⟩ hp hpre hL htgt k _ s_end S1 hr hs hcap R1 hpc1'
  exact ⟨n₁ + n₂, by simpa using Nat.add_le_add hn₁ hn₂, S2, e1.trans e2, hpc2, R2,
    fun c h1 h2 => (fr2.2.2 c h2).trans (fr1 c h1), fr2.1.trans hi1, fr2.2.1.trans hn1⟩

theorem fits_mid (a b c : Program) : Fits (a ++ b ++ c) a.length b := by
  have := fits_self (a ++ b) c
  exact (fits_append.1 this).2.congr (by simp)

/-! ### The pipe program -/

section pipe

variable (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2)

/-- The sources of the second phase: the captured output, from the
address in `rOB` with its length in cell 8, and the input. -/
def pipeSrcs : Fin 2 → Src := ![⟨.mem rOB, 8⟩, ⟨.input, 15⟩]

def pipeD : ℕ := max ((ρ.map Segment.size).sum + 3) ((ρ'.map Segment.size).sum + 3)
def pipeTe : ℕ := 16 + 2 * max ρ.length ρ'.length
def pipeBase : ℕ := pipeTe ρ ρ' + pipeD ρ ρ' + 1
def pipeKs₁ : List SegKind := ρ.map (segKind simSrcs)
def pipeKs₂ : List SegKind := ρ'.map (segKind pipeSrcs)

/-- Constants, the mask `(2 ^ w - 1) / 4`, the memory of the first
phase, the input length, and the output buffer right above. -/
def pipeInit : Program :=
  [.set rOne 1, .set rT 4, .not rMask rZ, .div rMask rMask rT, .set rBase (pipeBase ρ ρ'),
    .inputLength 15, .add rCap rMask rOne, .add rOB rBase rCap]

def pipeRw₁ : Program := rwCode simSrcs (pipeTe ρ ρ') 16 ρ 0 8
def pipeH₁ : ℕ := 8 + (pipeRw₁ ρ ρ').length
def pipeExit₁ : ℕ := pipeH₁ ρ ρ' + blockLen (pipeKs₁ ρ) * P.length

/-- Between the phases: the memory of the second phase above the
buffer, the length of the captured output, and a fresh cursor. -/
def pipeGlue : Program := [.add rBase rOB rCap, .add 8 rOC rZ, .set rCur 0, .set rTot 0]

def pipeRw₂ : Program := rwCode pipeSrcs (pipeTe ρ ρ') 16 ρ' 0 (pipeExit₁ P ρ ρ' + 4)
def pipeH₂ : ℕ := pipeExit₁ P ρ ρ' + 4 + (pipeRw₂ P ρ ρ').length
def pipeExit₂ : ℕ := pipeH₂ P ρ ρ' + blockLen (pipeKs₂ ρ') * M.length

/-- An overflow of the buffer in the first phase ends in a loop at this
address, so that a halting run never comes from a truncated output. -/
def pipeDie : ℕ := pipeExit₂ P M ρ ρ' + 1

def pipeCode₁ : Code where
  ks := pipeKs₁ ρ
  tb := 16
  mode := .buffer (pipeDie P M ρ ρ')
  tgt := fun l => if l < P.length then pipeH₁ ρ ρ' + blockLen (pipeKs₁ ρ) * l
    else pipeExit₁ P ρ ρ'
  exit := pipeExit₁ P ρ ρ'

def pipeCode₂ : Code where
  ks := pipeKs₂ ρ'
  tb := 16
  mode := .direct
  tgt := fun l => if l < M.length then pipeH₂ P ρ ρ' + blockLen (pipeKs₂ ρ') * l
    else pipeExit₂ P M ρ ρ'
  exit := pipeExit₂ P M ρ ρ'

def pipeProg : Program :=
  pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++ blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++
    (pipeGlue ++ pipeRw₂ P ρ ρ' ++
      blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M ++
        [.halt, .jump (pipeDie P M ρ ρ')])

end pipe

theorem two_pow_sub_one_div_four {w : ℕ} (hw : 2 ≤ w) : (2 ^ w - 1) / 4 = 2 ^ (w - 2) - 1 := by
  have h : 2 ^ w = 4 * 2 ^ (w - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have : 1 ≤ 2 ^ (w - 2) := Nat.one_le_two_pow
  omega

/-- The pipe up to the launch of each phase: the launch of the first
phase, and, once the first phase has halted, the machine before the
launch of the second phase. -/
theorem pipe_mid (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2) (w : ℕ) (x : List ℕ)
    (hK : pipeBase ρ ρ' ≤ 2 ^ (w - 2)) (hfit : ρ.Fits w (fun _ => x)) :
    (∃ nL SL, Exec w (pipeProg P M ρ ρ') nL (initState x) SL ∧
      SL.pc = (pipeCode₁ P M ρ ρ').tgt (initState (ρ.apply fun _ => x)).pc ∧
      Rel w ⟨w - 2, pipeBase ρ ρ', pipeBase ρ ρ' + 2 ^ (w - 2), 2 ^ (w - 2)⟩ (pipeKs₁ ρ) 16
        (.buffer (pipeDie P M ρ ρ')) (ρ.apply fun _ => x) [] (initState (ρ.apply fun _ => x)) SL) ∧
    (∀ (y : List ℕ) (t₁ : ℕ), y.length ≤ 2 ^ (w - 2) →
      RunsTo (w - 2) P (ρ.apply fun _ => x) y t₁ →
      ∃ n ≤ 12 + 11 * (ρ.map (·.cost fun _ => x)).sum + stepBound (pipeKs₁ ρ) * (t₁ + 1),
        ∃ S13, Exec w (pipeProg P M ρ ρ') n (initState x) S13 ∧
          S13.pc = pipeExit₁ P ρ ρ' + 4 ∧
          Env w (w - 2) (pipeBase ρ ρ' + 2 * 2 ^ (w - 2)) S13 ∧
          (∀ j, SrcOK w (fun a => (⟨w - 2, pipeBase ρ ρ' + 2 * 2 ^ (w - 2), 0, 0⟩ : Geo).W a ∨
            LaunchW 16 ρ'.length (pipeTe ρ ρ') (pipeD ρ ρ') a) S13 (pipeSrcs j) (![y, x] j)) ∧
          S13.mem rCur = 0 ∧ S13.mem rTot = 0 ∧
          (∀ a < 2 ^ (w - 2), S13.mem (pipeBase ρ ρ' + 2 * 2 ^ (w - 2) + a) = 0) ∧
          S13.out = []) := by
  set p := pipeProg P M ρ ρ' with hp
  set base := pipeBase ρ ρ'
  have hbase : 19 ≤ base := by simp only [base, pipeBase, pipeTe, pipeD]; omega
  have hw2 : 2 ≤ w := by
    by_contra h
    rw [show w - 2 = 0 by omega, pow_zero] at hK
    omega
  set V := 2 ^ (w - 2) with hV
  have h4w : 2 ^ w = 4 * V := by
    rw [hV, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hw16 : 16 < 2 ^ w := by omega
  -- the initialization
  have hfI : Fits p 0 (pipeInit ρ ρ') := by
    rw [hp, pipeProg, List.append_assoc, List.append_assoc]; exact fits_self _ _
  set S0 := initState x
  have hpc0 : S0.pc = 0 := rfl
  obtain ⟨S1, e1, hpc1, hm1, hi1, hn1, ho1⟩ := (x_set (w := w) (s := S0)
    (fetch hfI (i := 0) rfl rfl) (by omega)).upd
  obtain ⟨S2, e2, hpc2, hm2, hi2, hn2, ho2⟩ := (x_set (w := w) (s := S1)
    (fetch hfI (i := 1) (by simp [hpc1, hpc0]) rfl) (by omega)).upd
  obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_not (w := w) (s := S2)
    (fetch hfI (i := 2) (by simp [hpc2, hpc1, hpc0]) rfl) (by omega) (by omega)).upd
  have hW2 : WordMem w S2.mem := fun c => by
    rw [hm2, hm1]; split_ifs <;> first | exact Nat.mod_lt _ (by positivity) | simp [S0, initState]
  obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_div (w := w) (s := S3)
    (fetch hfI (i := 3) (by simp [hpc3, hpc2, hpc1, hpc0]) rfl)
    (hW2.exec e3) (by omega) (by omega) (by omega)).upd
  obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_set (w := w) (s := S4)
    (fetch hfI (i := 4) (by simp [hpc4, hpc3, hpc2, hpc1, hpc0]) rfl) (by omega)).upd
  obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_inputLength (w := w) (s := S5)
    (fetch hfI (i := 5) (by simp [hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl)
    (by omega)).upd
  obtain ⟨S7, e7, hpc7, hm7, hi7, hn7, ho7⟩ := (x_add (w := w) (s := S6)
    (fetch hfI (i := 6) (by simp [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl)
    (by omega) (by omega) (by omega)).upd
  obtain ⟨S8, e8, hpc8, hm8, hi8, hn8, ho8⟩ := (x_add (w := w) (s := S7)
    (fetch hfI (i := 7) (by simp [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]) rfl)
    (by omega) (by omega) (by omega)).upd
  have hx : x.length < 2 ^ w := hfit.1 0
  have hmask6 : S6.mem rMask = V - 1 := by
    simp [hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]
    rw [Nat.mod_eq_of_lt (show 4 < 2 ^ w by omega), two_pow_sub_one_div_four hw2]
  have hbase6 : S6.mem rBase = base := by
    simp [hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]; exact Nat.mod_eq_of_lt (by omega)
  have hone6 : S6.mem rOne = 1 := by
    simp [hm6, hm5, hm4, hm3, hm2, hm1, S0, initState]; omega
  have hcap8 : S8.mem rCap = V := by
    have : 1 ≤ V := Nat.one_le_two_pow
    rw [hm8, if_neg (by decide), hm7, if_pos rfl, hmask6, hone6,
      Nat.mod_eq_of_lt (show V - 1 + 1 < 2 ^ w by omega)]
    omega
  have hV1 : 1 ≤ V := Nat.one_le_two_pow
  have hob8 : S8.mem rOB = base + V := by
    rw [hm8, if_pos rfl, hm7 rBase, if_neg (by decide), hbase6, hm7 rCap, if_pos rfl, hmask6,
      hone6, Nat.mod_eq_of_lt (show V - 1 + 1 < 2 ^ w by omega),
      Nat.mod_eq_of_lt (show base + (V - 1 + 1) < 2 ^ w by omega)]
    omega
  have hm8' : ∀ c, c ≠ rOne → c ≠ rT → c ≠ rMask → c ≠ rBase → c ≠ 15 → c ≠ rCap → c ≠ rOB →
      S8.mem c = 0 := by
    intro c h1 h2 h3 h4 h5 h6 h7
    rw [hm8, if_neg h7, hm7, if_neg h6, hm6, if_neg h5, hm5, if_neg h4, hm4, if_neg h3, hm3,
      if_neg h3, hm2, if_neg h2, hm1, if_neg h1]; rfl
  have h8 : ∀ c, c ≠ rCap → c ≠ rOB → S8.mem c = S6.mem c := by
    intro c h1 h2; rw [hm8, if_neg h2, hm7, if_neg h1]
  have hW8 : WordMem w S8.mem := (hW2.exec e3).exec ((((e4.trans e5).trans e6).trans e7).trans e8)
  have hin8 : S8.input = x := by rw [hi8, hi7, hi6, hi5, hi4, hi3, hi2, hi1]; rfl
  have hout8 : S8.out = [] := by rw [ho8, ho7, ho6, ho5, ho4, ho3, ho2, ho1]; rfl
  have hin5 : S5.input = x := by rw [hi5, hi4, hi3, hi2, hi1]; rfl
  have hlen8 : S8.mem 15 = x.length := by
    rw [h8 _ (by decide) (by decide), hm6, if_pos rfl, hin5, Nat.mod_eq_of_lt hx]
  have hD : pipeTe ρ ρ' + pipeD ρ ρ' < base := by simp only [base, pipeBase]; omega
  have hteN : 16 + 2 * ρ.length ≤ pipeTe ρ ρ' := by simp only [pipeTe]; omega
  have hteN' : 16 + 2 * ρ'.length ≤ pipeTe ρ ρ' := by simp only [pipeTe]; omega
  have hsz : ∀ seg ∈ ρ, seg.size + 3 ≤ pipeD ρ ρ' := fun seg hs => by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := Segment.size) hs)
    simp only [pipeD]; omega
  have hsz' : ∀ seg ∈ ρ', seg.size + 3 ≤ pipeD ρ ρ' := fun seg hs => by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := Segment.size) hs)
    simp only [pipeD]; omega
  -- the first phase
  have E8 : Env w (w - 2) base S8 :=
    ⟨hW8, hm8' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      by rw [h8 _ (by decide) (by decide)]; exact hone6,
      by rw [h8 _ (by decide) (by decide)]; exact hmask6,
      by rw [h8 _ (by decide) (by decide)]; exact hbase6, by omega, by omega, by omega⟩
  have hfR₁ : Fits p 8 (pipeRw₁ ρ ρ') := by
    have e : p = pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++
        (blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++
        (pipeGlue ++ pipeRw₂ P ρ ρ' ++
          blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M ++ [.halt, .jump (pipeDie P M ρ ρ')])) := by
      rw [hp, pipeProg]; simp only [List.append_assoc]
    rw [e]; exact fits_mid _ _ _
  have hsrc₁ : SrcOK w (fun a => (⟨w - 2, base, base + V, V⟩ : Geo).W a ∨
      LaunchW 16 ρ.length (pipeTe ρ ρ') (pipeD ρ ρ') a) S8 ⟨.input, 15⟩ x := by
    refine ⟨hlen8, hx, by show 15 < 2 ^ w; omega, ?_, hin8⟩
    simp only [Geo.W, LaunchW]; omega
  have hreg₁ : ∀ a < 2 ^ (w - 2), S8.mem (base + a) = 0 := fun a ha =>
    hm8' _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have htab₁ : ∀ a, 16 ≤ a → a < 16 + 2 * ρ.length →
      ¬ (⟨w - 2, base, base + V, V⟩ : Geo).W a := fun a h1 h2 => by
    simp only [Geo.W]; omega
  have hregL₁ : ∀ a, LaunchW 16 ρ.length (pipeTe ρ ρ') (pipeD ρ ρ') a →
      ¬ (base ≤ a ∧ a < base + 2 ^ (w - 2)) := fun a ha => by simp only [LaunchW] at ha; omega
  have houtL₁ : ∀ a, LaunchW 16 ρ.length (pipeTe ρ ρ') (pipeD ρ ρ') a →
      ¬ (base + V ≤ a ∧ a < base + V + V) := fun a ha => by simp only [LaunchW] at ha; omega
  have hz8 : S8.mem rZ = 0 :=
    hm8' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcur8 : S8.mem rCur = 0 :=
    hm8' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have htot8 : S8.mem rTot = 0 :=
    hm8' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hoc8 : S8.mem rOC = 0 :=
    hm8' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpre₁ : (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ').length = pipeH₁ ρ ρ' := by
    simp [pipeInit, pipeH₁]; omega
  have e8 := (((((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8)
  have hpc8' : S8.pc = 8 := by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]
  have hout8L : OutRel w ⟨w - 2, base, base + V, V⟩ S8.out (initState (ρ.apply fun _ => x)) S8
      (.buffer (pipeDie P M ρ ρ')) :=
    ⟨rfl, hob8, by rw [hoc8]; rfl, hcap8, by simp [initState], show 16 ≤ base + V by omega,
      show base + V + V ≤ 2 ^ w by omega,
      Or.inr le_rfl, fun j hj => by simp [initState] at hj⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨nL, -, SL, eL, hpcL, RL, -, -, -, -⟩ := launch_spec simSrcs 16 (pipeTe ρ ρ')
      (pipeD ρ ρ') ⟨w - 2, base, base + V, V⟩ (.buffer (pipeDie P M ρ ρ')) (fun _ => x) ρ 8 S8
      hfR₁ hpc8' E8 (fun _ => hsrc₁) hfit hsz le_rfl hteN (by omega) htab₁ hcur8 htot8 hreg₁
      hregL₁ hout8L houtL₁
    refine ⟨8 + nL, SL, e8.trans eL, ?_, by rw [hout8] at RL; exact RL⟩
    rw [hpcL]
    show pipeH₁ ρ ρ' = if 0 < P.length then pipeH₁ ρ ρ' + blockLen (pipeKs₁ ρ) * 0
      else pipeExit₁ P ρ ρ'
    split_ifs with h
    · simp
    · simp [pipeExit₁, show P.length = 0 by omega]
  intro y t₁ hy hrun₁
  obtain ⟨k₁, s₁, hr₁, hs₁, hy₁, ht₁⟩ := hrun₁
  obtain ⟨n₁, hn₁, S9, e9, hpc9, R9, fr9, hi9, hn9⟩ := phase_spec simSrcs 16 (pipeTe ρ ρ')
    (pipeD ρ ρ') ⟨w - 2, base, base + V, V⟩ (.buffer (pipeDie P M ρ ρ'))
    (pipeCode₁ P M ρ ρ').tgt (pipeExit₁ P ρ ρ') (fun _ => x) ρ P
    (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ')
    (pipeGlue ++ pipeRw₂ P ρ ρ' ++
      blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M ++ [.halt, .jump (pipeDie P M ρ ρ')])
    (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) 8 rfl hpre₁ le_rfl (fun l => rfl) rfl rfl hfR₁ S8
    hpc8' E8
    (fun _ => hsrc₁) hfit hsz le_rfl hteN (by omega) htab₁ hcur8 htot8 hreg₁ hregL₁ hout8L
    houtL₁ k₁ s₁ hr₁ hs₁ (fun _ _ => by rw [hy₁]; exact hy)
  have E9 := R9.env
  obtain ⟨ho9, hob9, hoc9, hcap9, -, -, -, -, hbuf9⟩ := R9.out
  rw [hy₁] at hoc9 hbuf9
  have hob9' : S9.mem rOB = base + V := hob9
  have hcap9' : S9.mem rCap = V := hcap9
  have hbuf9' : ∀ j < y.length, S9.mem (base + V + j) = y.getD j 0 := hbuf9
  -- the glue
  set B1 := blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P
  set B2 := blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M
  have hB1 : B1.length = blockLen (pipeKs₁ ρ) * P.length :=
    blocks_length (pipeCode₁ P M ρ ρ') _ _ _ le_rfl
  have hB2 : B2.length = blockLen (pipeKs₂ ρ') * M.length :=
    blocks_length (pipeCode₂ P M ρ ρ') _ _ _ le_rfl
  have hlenA : (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++ B1).length = pipeExit₁ P ρ ρ' := by
    rw [List.length_append, hpre₁, hB1]; rfl
  have hfG : Fits p (pipeExit₁ P ρ ρ') pipeGlue := by
    have e : p = pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++ B1 ++ pipeGlue ++ (pipeRw₂ P ρ ρ' ++ B2 ++
        [.halt, .jump (pipeDie P M ρ ρ')]) := by
      rw [hp, pipeProg]; simp only [List.append_assoc]; rfl
    rw [e, ← hlenA]; exact fits_mid _ _ _
  have hm9 := E9.word
  obtain ⟨S10, e10, hpc10, hm10, hi10, hn10, ho10⟩ := (x_add (w := w) (s := S9)
    (fetch hfG (i := 0) (by simp [hpc9]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S11, e11, hpc11, hm11, hi11, hn11, ho11⟩ := (x_add (w := w) (s := S10)
    (fetch hfG (i := 1) (by simp [hpc10, hpc9]) rfl) (by omega) (by omega) (by omega)).upd
  obtain ⟨S12, e12, hpc12, hm12, hi12, hn12, ho12⟩ := (x_set (w := w) (s := S11)
    (fetch hfG (i := 2) (by simp [hpc11, hpc10, hpc9]) rfl) (by omega)).upd
  obtain ⟨S13, e13, hpc13, hm13, hi13, hn13, ho13⟩ := (x_set (w := w) (s := S12)
    (fetch hfG (i := 3) (by simp [hpc12, hpc11, hpc10, hpc9]) rfl) (by omega)).upd
  have h139 : ∀ c, c ≠ rTot → c ≠ rCur → c ≠ 8 → c ≠ rBase → S13.mem c = S9.mem c := by
    intro c h1 h2 h3 h4
    rw [hm13, if_neg h1, hm12, if_neg h2, hm11, if_neg h3, hm10, if_neg h4]
  have hbase13 : S13.mem rBase = base + 2 * V := by
    rw [hm13, if_neg (by decide), hm12, if_neg (by decide), hm11, if_neg (by decide), hm10,
      if_pos rfl, hob9', hcap9', Nat.mod_eq_of_lt (by omega)]
    omega
  have hy13 : S13.mem 8 = y.length := by
    rw [hm13, if_neg (by decide), hm12, if_neg (by decide), hm11, if_pos rfl, hm10, hm10,
      if_neg (by decide), if_neg (by decide), hoc9, E9.zero, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega)]
  have hcur13 : S13.mem rCur = 0 := by
    rw [hm13, if_neg (by decide), hm12, if_pos rfl, Nat.zero_mod]
  have htot13 : S13.mem rTot = 0 := by rw [hm13, if_pos rfl, Nat.zero_mod]
  have hW13 : WordMem w S13.mem := hm9.exec (((e10.trans e11).trans e12).trans e13)
  have hin13 : S13.input = x := by rw [hi13, hi12, hi11, hi10, hi9, hin8]
  have hout13 : S13.out = [] := by rw [ho13, ho12, ho11, ho10, ho9, hout8]
  have hpc13' : S13.pc = pipeExit₁ P ρ ρ' + 4 := by rw [hpc13, hpc12, hpc11, hpc10, hpc9]
  -- the second phase
  have h98 : ∀ c, base + 2 * V ≤ c → S9.mem c = S8.mem c := by
    intro c hc
    exact fr9 c (by simp only [LaunchW]; omega) (by simp only [Geo.W]; omega)
  have hsrcY : SrcOK w (fun a => (⟨w - 2, base + 2 * V, 0, 0⟩ : Geo).W a ∨
      LaunchW 16 ρ'.length (pipeTe ρ ρ') (pipeD ρ ρ') a) S13 ⟨.mem rOB, 8⟩ y := by
    have h6 : S13.mem rOB = base + V := by
      rw [h139 _ (by decide) (by decide) (by decide) (by decide), hob9']
    refine ⟨hy13, by omega, by show 8 < 2 ^ w; omega, by simp only [Geo.W, LaunchW]; omega, ?_⟩
    refine ⟨by show 6 < 2 ^ w; omega, by simp only [Geo.W, LaunchW]; omega, by rw [h6]; omega,
      fun i hi => ⟨?_, ?_⟩⟩
    · rw [h6, h139 _ (by omega) (by omega) (by omega) (by omega), hbuf9' i hi,
        Nat.mod_eq_of_lt]
      rw [← hbuf9' i hi]; exact hm9 _
    · rw [h6]; simp only [Geo.W, LaunchW]; omega
  have hsrcX : SrcOK w (fun a => (⟨w - 2, base + 2 * V, 0, 0⟩ : Geo).W a ∨
      LaunchW 16 ρ'.length (pipeTe ρ ρ') (pipeD ρ ρ') a) S13 ⟨.input, 15⟩ x := by
    refine ⟨?_, hx, by show 15 < 2 ^ w; omega, by simp only [Geo.W, LaunchW]; omega, hin13⟩
    rw [h139 _ (by decide) (by decide) (by decide) (by decide),
      fr9 15 (by simp only [LaunchW]; omega) (by simp only [Geo.W]; omega), hlen8]
  have hsrc₂ : ∀ j, SrcOK w (fun a => (⟨w - 2, base + 2 * V, 0, 0⟩ : Geo).W a ∨
      LaunchW 16 ρ'.length (pipeTe ρ ρ') (pipeD ρ ρ') a) S13 (pipeSrcs j) (![y, x] j) := by
    intro j; fin_cases j
    · exact hsrcY
    · exact hsrcX
  have E13 : Env w (w - 2) (base + 2 * V) S13 :=
    ⟨hW13, by rw [h139 _ (by decide) (by decide) (by decide) (by decide)]; exact E9.zero,
      by rw [h139 _ (by decide) (by decide) (by decide) (by decide)]; exact E9.one,
      by rw [h139 _ (by decide) (by decide) (by decide) (by decide)]; exact E9.mask,
      hbase13, by omega, by omega, by omega⟩
  have hreg₂ : ∀ a < 2 ^ (w - 2), S13.mem (base + 2 * V + a) = 0 := fun a ha => by
    rw [h139 _ (by omega) (by omega) (by omega) (by omega), h98 _ (by omega)]
    exact hm8' _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have htab₂ : ∀ a, 16 ≤ a → a < 16 + 2 * ρ'.length →
      ¬ (⟨w - 2, base + 2 * V, 0, 0⟩ : Geo).W a := fun a h1 h2 => by
    simp only [Geo.W]; omega
  have hregL₂ : ∀ a, LaunchW 16 ρ'.length (pipeTe ρ ρ') (pipeD ρ ρ') a →
      ¬ (base + 2 * V ≤ a ∧ a < base + 2 * V + 2 ^ (w - 2)) := fun a ha => by
    simp only [LaunchW] at ha; omega
  refine ⟨8 + n₁ + 4, ?_, S13, e8.trans (e9.trans (((e10.trans e11).trans e12).trans e13)),
    hpc13', E13, hsrc₂, hcur13, htot13, hreg₂, hout13⟩
  have hk₁ : k₁ ≤ t₁ := by rw [ht₁]; omega
  have h1 := Nat.mul_le_mul_left (stepBound (pipeKs₁ ρ)) (Nat.add_le_add_right hk₁ 1)
  have hn₁' : n₁ ≤ 11 * (ρ.map (·.cost fun _ => x)).sum + stepBound (pipeKs₁ ρ) * (k₁ + 1) :=
    hn₁
  omega

theorem pipe_run (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2) (w : ℕ) (x y z : List ℕ)
    (t₁ t₂ : ℕ) (hK : pipeBase ρ ρ' ≤ 2 ^ (w - 2)) (hy : y.length ≤ 2 ^ (w - 2))
    (hfit : ρ.Fits w (fun _ => x)) (hfit' : ρ'.Fits w ![y, x])
    (hrun₁ : RunsTo (w - 2) P (ρ.apply fun _ => x) y t₁)
    (hrun₂ : RunsTo (w - 2) M (ρ'.apply ![y, x]) z t₂) :
    ∃ t ≤ 13 + 11 * (ρ.map (·.cost fun _ => x)).sum + stepBound (pipeKs₁ ρ) * (t₁ + 1) +
        11 * (ρ'.map (·.cost ![y, x])).sum + stepBound (pipeKs₂ ρ') * (t₂ + 1),
      RunsTo w (pipeProg P M ρ ρ') x z t := by
  set p := pipeProg P M ρ ρ' with hp
  set base := pipeBase ρ ρ'
  have hbase : 19 ≤ base := by simp only [base, pipeBase, pipeTe, pipeD]; omega
  have hw2 : 2 ≤ w := by
    by_contra h
    rw [show w - 2 = 0 by omega, pow_zero] at hK
    omega
  set V := 2 ^ (w - 2) with hV
  have h4w : 2 ^ w = 4 * V := by
    rw [hV, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hw16 : 16 < 2 ^ w := by omega
  obtain ⟨k₂, s₂, hr₂, hs₂, hz₂, ht₂⟩ := hrun₂
  obtain ⟨n₁, hn₁, S13, e13, hpc13', E13, hsrc₂, hcur13, htot13, hreg₂, hout13⟩ :=
    (pipe_mid P M ρ ρ' w x hK hfit).2 y t₁ hy hrun₁
  have hD : pipeTe ρ ρ' + pipeD ρ ρ' < base := by simp only [base, pipeBase]; omega
  have hteN' : 16 + 2 * ρ'.length ≤ pipeTe ρ ρ' := by simp only [pipeTe]; omega
  have hsz' : ∀ seg ∈ ρ', seg.size + 3 ≤ pipeD ρ ρ' := fun seg hs => by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := Segment.size) hs)
    simp only [pipeD]; omega
  have htab₂ : ∀ a, 16 ≤ a → a < 16 + 2 * ρ'.length →
      ¬ (⟨w - 2, base + 2 * V, 0, 0⟩ : Geo).W a := fun a h1 h2 => by
    simp only [Geo.W]; omega
  have hregL₂ : ∀ a, LaunchW 16 ρ'.length (pipeTe ρ ρ') (pipeD ρ ρ') a →
      ¬ (base + 2 * V ≤ a ∧ a < base + 2 * V + 2 ^ (w - 2)) := fun a ha => by
    simp only [LaunchW] at ha; omega
  set B1 := blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P
  set B2 := blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M
  have hB1 : B1.length = blockLen (pipeKs₁ ρ) * P.length :=
    blocks_length (pipeCode₁ P M ρ ρ') _ _ _ le_rfl
  have hB2 : B2.length = blockLen (pipeKs₂ ρ') * M.length :=
    blocks_length (pipeCode₂ P M ρ ρ') _ _ _ le_rfl
  have hpre₁ : (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ').length = pipeH₁ ρ ρ' := by
    simp [pipeInit, pipeH₁]; omega
  have hlenA : (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++ B1).length = pipeExit₁ P ρ ρ' := by
    rw [List.length_append, hpre₁, hB1]; rfl
  set pre₂ := pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++ B1 ++ pipeGlue ++ pipeRw₂ P ρ ρ'
  have hp₂ : p = pre₂ ++ B2 ++ [.halt, .jump (pipeDie P M ρ ρ')] := by
    rw [hp, pipeProg]; simp only [pre₂, List.append_assoc]; rfl
  have hpre₂ : pre₂.length = pipeH₂ P ρ ρ' := by
    simp only [pre₂, List.length_append]
    rw [← List.length_append, ← List.length_append, hlenA]
    simp [pipeH₂, pipeGlue]
  have hfR₂ : Fits p (pipeExit₁ P ρ ρ' + 4) (pipeRw₂ P ρ ρ') := by
    have e : p = pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++ B1 ++ pipeGlue ++ pipeRw₂ P ρ ρ' ++
        (B2 ++ [.halt, .jump (pipeDie P M ρ ρ')]) := by
      rw [hp₂]; simp only [pre₂, List.append_assoc]
    rw [e]
    exact (fits_mid _ _ _).congr (by rw [List.length_append, hlenA]; rfl)
  obtain ⟨n₂, hn₂, S14, e14, hpc14, R14, -, -, -⟩ := phase_spec pipeSrcs 16 (pipeTe ρ ρ')
    (pipeD ρ ρ') ⟨w - 2, base + 2 * V, 0, 0⟩ .direct (pipeCode₂ P M ρ ρ').tgt
    (pipeExit₂ P M ρ ρ') ![y, x] ρ' M pre₂ [.halt, .jump (pipeDie P M ρ ρ')] (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ'))
    (pipeExit₁ P ρ ρ' + 4) hp₂ hpre₂ le_rfl (fun l => rfl) rfl rfl hfR₂ S13 hpc13' E13 hsrc₂
    hfit' hsz' le_rfl hteN' (by omega) htab₂ hcur13 htot13 hreg₂ hregL₂
    (by simp [OutRel, initState]) (fun a _ => by simp) k₂ s₂ hr₂ hs₂ (fun _ h => by cases h)
  have hout14 : S14.out = z := by
    have := R14.out
    simp only [OutRel] at this
    rw [this, hout13, hz₂]; rfl
  have hhalt : p[S14.pc]? = some .halt := by
    rw [hpc14, hp₂, List.getElem?_append_right (by
      rw [List.length_append, hpre₂, hB2]; rfl)]
    rw [List.length_append, hpre₂, hB2]; simp [pipeExit₂]
  have e := e13.trans e14
  refine ⟨_, ?_, runsTo_of_exec e (step_halt hhalt) hout14⟩
  rw [terminalCost_of_getElem? hhalt]
  have hk₂ : k₂ ≤ t₂ := by rw [ht₂]; omega
  have h2 := Nat.mul_le_mul_left (stepBound (pipeKs₂ ρ')) (Nat.add_le_add_right hk₂ 1)
  have hn₂' : n₂ ≤ 11 * (ρ'.map (·.cost ![y, x])).sum + stepBound (pipeKs₂ ρ') * (k₂ + 1) :=
    hn₂
  omega

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim

/-- **Pipe.** Run `P` on `ρ x`, capture its output `y` in a buffer,
then run `M` on `ρ' (y, x)`. Both at `w - 2`: two fresh simulated
regions plus the buffer. Anything a rewrite cannot compute (for example
`unpair`) is done by a preprocessing `P` that writes it. -/
theorem pipe :
    ∀ (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2), ∃ (p : Program) (K : ℕ),
      ∀ (w : ℕ) (x y z : List ℕ) (t₁ t₂ : ℕ),
        K ≤ 2 ^ (w - 2) → y.length < 2 ^ (w - 2) →
        ρ.Fits w (fun _ => x) → ρ'.Fits w ![y, x] →
        RunsTo (w - 2) P (ρ.apply fun _ => x) y t₁ →
        RunsTo (w - 2) M (ρ'.apply ![y, x]) z t₂ →
        ∃ t ≤ K * (t₁ + t₂ + ρ.cost (fun _ => x) + ρ'.cost ![y, x]),
          RunsTo w p x z t := by
  intro P M ρ ρ'
  refine ⟨pipeProg P M ρ ρ', pipeBase ρ ρ' + stepBound (pipeKs₁ ρ) + stepBound (pipeKs₂ ρ') + 24,
    fun w x y z t₁ t₂ hK hy hfit hfit' h₁ h₂ => ?_⟩
  obtain ⟨t, ht, hr⟩ := pipe_run P M ρ ρ' w x y z t₁ t₂ (by omega) hy.le hfit hfit' h₁ h₂
  refine ⟨t, le_trans ht ?_, hr⟩
  have hc₁ : ρ.cost (fun _ => x) = (ρ.map (·.cost fun _ => x)).sum + 1 := rfl
  have hc₂ : ρ'.cost ![y, x] = (ρ'.map (·.cost ![y, x])).sum + 1 := rfl
  rw [hc₁, hc₂]
  generalize (ρ.map (·.cost fun _ => x)).sum = C₁
  generalize (ρ'.map (·.cost ![y, x])).sum = C₂
  generalize stepBound (pipeKs₁ ρ) = B₁
  generalize stepBound (pipeKs₂ ρ') = B₂
  generalize pipeBase ρ ρ' = B₀
  set T := t₁ + t₂ + (C₁ + 1) + (C₂ + 1)
  have a1 : B₁ * (t₁ + 1) ≤ B₁ * T := Nat.mul_le_mul_left _ (by omega)
  have a2 : B₂ * (t₂ + 1) ≤ B₂ * T := Nat.mul_le_mul_left _ (by omega)
  have a3 : (B₀ + B₁ + B₂ + 24) * T = B₀ * T + B₁ * T + B₂ * T + 24 * T := by ring
  rw [a3]
  omega

end Lax185574Proofs.Simulate
