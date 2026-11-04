import Lax185574Proofs.RamSimBack
import Lax185574Proofs.RamPipe

/-!
Backward soundness of `pipe`: if the pipe halts with output `z`, then
the first program halted with an output `y` that fits the buffer, and
the second program halted on the rewrite of `y` and the input with
output `z`. An overflow of the buffer never leads to a halting run,
since it ends in a loop.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

section

variable (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2)

theorem pipeProg_split :
    pipeProg P M ρ ρ' = (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++
      blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++ pipeGlue ++
      pipeRw₂ P ρ ρ') ++ blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M ++
      [.halt, .jump (pipeDie P M ρ ρ')] := by
  rw [pipeProg]; simp only [List.append_assoc]

theorem pipeB1_length :
    (blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P).length =
      blockLen (pipeKs₁ ρ) * P.length :=
  blocks_length (pipeCode₁ P M ρ ρ') _ _ _ le_rfl

theorem pipeB2_length :
    (blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M).length =
      blockLen (pipeKs₂ ρ') * M.length :=
  blocks_length (pipeCode₂ P M ρ ρ') _ _ _ le_rfl

theorem pipePre₁_length :
    (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++
      blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++ pipeGlue).length =
      pipeExit₁ P ρ ρ' + 4 := by
  simp only [List.length_append, pipeB1_length]
  rfl

theorem pipePre₂_length :
    (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++
      blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++ pipeGlue ++
      pipeRw₂ P ρ ρ').length = pipeH₂ P ρ ρ' := by
  rw [List.length_append, pipePre₁_length]
  rfl

theorem pipeProg_die :
    (pipeProg P M ρ ρ')[pipeDie P M ρ ρ']? = some (.jump (pipeDie P M ρ ρ')) := by
  have h : (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++
      blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++ pipeGlue ++
      pipeRw₂ P ρ ρ' ++ blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M).length
      = pipeExit₂ P M ρ ρ' := by
    rw [List.length_append, pipePre₂_length, pipeB2_length]; rfl
  rw [pipeProg_split, List.getElem?_append_right (by rw [h]; simp [pipeDie]), h]
  simp [pipeDie]

end

theorem pipe_back (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2) (w : ℕ) (x z : List ℕ)
    (T : ℕ) (hK : pipeBase ρ ρ' ≤ 2 ^ (w - 2)) (hfit : ρ.Fits w (fun _ => x))
    (hrun : RunsTo w (pipeProg P M ρ ρ') x z T) :
    ∃ y t₁, t₁ ≤ T ∧ y.length ≤ 2 ^ (w - 2) ∧ RunsTo (w - 2) P (ρ.apply fun _ => x) y t₁ ∧
      (ρ'.Fits w ![y, x] → ∃ t₂ ≤ T, RunsTo (w - 2) M (ρ'.apply ![y, x]) z t₂) := by
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
  obtain ⟨N, S_end, hr, hs, hz, hT⟩ := hrun
  have hH : Halts w p (initState x) N S_end := ⟨hr, hs⟩
  obtain ⟨hstart, hmid⟩ := pipe_mid P M ρ ρ' w x hK hfit
  obtain ⟨nL, SL, eL, hpcL, RL⟩ := hstart
  have hnL := eL.le_of_halts hH
  -- the first phase halts
  have hp₁ : p = (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ') ++
      blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++
      (pipeGlue ++ pipeRw₂ P ρ ρ' ++
        blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M ++
        [.halt, .jump (pipeDie P M ρ ρ')]) := by
    rw [hp, pipeProg]
  have hpre₁ : (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ').length = pipeH₁ ρ ρ' := by
    rw [List.length_append]; rfl
  obtain ⟨j₁, s₁, h1, h2, hj₁, hcap₁⟩ := sim_back (pipeCode₁ P M ρ ρ') hp₁ hpre₁ le_rfl
    (fun l => rfl) le_rfl (fun ovf h => by cases h; exact pipeProg_die P M ρ ρ') RL hpcL
    (hH.rest eL)
  have hy : s₁.out.length ≤ V := hcap₁ _ rfl
  have hR₁ : RunsTo (w - 2) P (ρ.apply fun _ => x) s₁.out (j₁ + terminalCost P s₁) :=
    ⟨j₁, s₁, h1, h2, rfl, rfl⟩
  refine ⟨s₁.out, _, by omega, hy, hR₁, fun hfit' => ?_⟩
  -- the second phase halts
  obtain ⟨n, -, S13, e13, hpc13, E13, hsrc₂, hcur13, htot13, hreg₂, hout13⟩ :=
    hmid s₁.out _ hy hR₁
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
  set pre₂ := pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++
    blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++ pipeGlue ++
    pipeRw₂ P ρ ρ'
  have hp₂ : p = pre₂ ++ blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M ++
      [.halt, .jump (pipeDie P M ρ ρ')] := pipeProg_split P M ρ ρ'
  have hpre₂ : pre₂.length = pipeH₂ P ρ ρ' := pipePre₂_length P M ρ ρ'
  have hfR₂ : Fits p (pipeExit₁ P ρ ρ' + 4) (pipeRw₂ P ρ ρ') := by
    have e : p = (pipeInit ρ ρ' ++ pipeRw₁ ρ ρ' ++
        blocks (pipeCode₁ P M ρ ρ') (pipeH₁ ρ ρ') (blockLen (pipeKs₁ ρ)) P ++ pipeGlue) ++
        pipeRw₂ P ρ ρ' ++
        (blocks (pipeCode₂ P M ρ ρ') (pipeH₂ P ρ ρ') (blockLen (pipeKs₂ ρ')) M ++
        [.halt, .jump (pipeDie P M ρ ρ')]) := by
      rw [hp₂]; simp only [pre₂, List.append_assoc]
    rw [e]
    exact (fits_mid _ _ _).congr (pipePre₁_length P M ρ ρ')
  obtain ⟨nL₂, -, SL₂, eL₂, hpcL₂, RL₂, -, -, -, -⟩ := launch_spec pipeSrcs 16 (pipeTe ρ ρ')
    (pipeD ρ ρ') ⟨w - 2, base + 2 * V, 0, 0⟩ .direct ![s₁.out, x] ρ' (pipeExit₁ P ρ ρ' + 4) S13
    hfR₂ hpc13 E13 hsrc₂ hfit' hsz' le_rfl hteN' (by omega) htab₂ hcur13 htot13 hreg₂ hregL₂
    (by simp [OutRel, initState]) (fun a _ => by simp)
  rw [hout13] at RL₂
  have hpcL₂' : SL₂.pc = (pipeCode₂ P M ρ ρ').tgt (initState (ρ'.apply ![s₁.out, x])).pc := by
    rw [hpcL₂]
    show pipeH₂ P ρ ρ' = if 0 < M.length then pipeH₂ P ρ ρ' + blockLen (pipeKs₂ ρ') * 0
      else pipeExit₂ P M ρ ρ'
    split_ifs with h
    · simp
    · simp [pipeExit₂, show M.length = 0 by omega]
  have e₂ := e13.trans eL₂
  obtain ⟨j₂, s₂, h3, h4, hj₂, -⟩ := sim_back (pipeCode₂ P M ρ ρ') hp₂ hpre₂ le_rfl
    (fun l => rfl) le_rfl (fun ovf h => by cases h) RL₂ hpcL₂' (hH.rest e₂)
  have hR₂ : RunsTo (w - 2) M (ρ'.apply ![s₁.out, x]) s₂.out (j₂ + terminalCost M s₂) :=
    ⟨j₂, s₂, h3, h4, rfl, rfl⟩
  obtain ⟨t, -, hR⟩ := pipe_run P M ρ ρ' w x s₁.out s₂.out _ _ hK hy hfit hfit' hR₁ hR₂
  have heq := (runsTo_unique ⟨N, S_end, hr, hs, hz, hT⟩ hR).1
  have hn := e₂.le_of_halts hH
  exact ⟨_, by omega, heq ▸ hR₂⟩

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim

/-- **Pipe, both directions.** The forward half is `pipe`. Conversely,
every halting run of the pipe comes from a halting run of `P` whose
output `y` fits the buffer, followed, when the rewrite `ρ'` fits on
`(y, x)`, by a halting run of `M` with the same output. Both runs take
no more steps than the pipe. -/
theorem pipe_sound :
    ∀ (P M : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2), ∃ (p : Program) (K : ℕ),
      ∀ (w : ℕ) (x : List ℕ), K ≤ 2 ^ (w - 2) → ρ.Fits w (fun _ => x) →
        (∀ (y z : List ℕ) (t₁ t₂ : ℕ), y.length ≤ 2 ^ (w - 2) → ρ'.Fits w ![y, x] →
          RunsTo (w - 2) P (ρ.apply fun _ => x) y t₁ →
          RunsTo (w - 2) M (ρ'.apply ![y, x]) z t₂ →
          ∃ t ≤ K * (t₁ + t₂ + ρ.cost (fun _ => x) + ρ'.cost ![y, x]), RunsTo w p x z t) ∧
        (∀ (z : List ℕ) (T : ℕ), RunsTo w p x z T →
          ∃ y t₁, t₁ ≤ T ∧ y.length ≤ 2 ^ (w - 2) ∧ RunsTo (w - 2) P (ρ.apply fun _ => x) y t₁ ∧
            (ρ'.Fits w ![y, x] → ∃ t₂ ≤ T, RunsTo (w - 2) M (ρ'.apply ![y, x]) z t₂)) := by
  intro P M ρ ρ'
  refine ⟨pipeProg P M ρ ρ', pipeBase ρ ρ' + stepBound (pipeKs₁ ρ) + stepBound (pipeKs₂ ρ') + 24,
    fun w x hK hfit => ⟨fun y z t₁ t₂ hy hfit' h₁ h₂ => ?_, fun z T h => ?_⟩⟩
  · obtain ⟨t, ht, hr⟩ := pipe_run P M ρ ρ' w x y z t₁ t₂ (by omega) hy hfit hfit' h₁ h₂
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
  · exact pipe_back P M ρ ρ' w x z T (by omega) hfit h

end Lax185574Proofs.Simulate
