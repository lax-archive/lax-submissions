import Lax185574Proofs.RamLoop

/-!
Scripted runs of the loop driver.

A composite built with `Lax185574Proofs.Simulate.loop_sound` is usually
analysed along a script: the states `A j` that the glue program `G`
writes, the answers `B j` of the callee `P`, a number `R` of calls, and
the final output `z`. If at the word lengths of the rounds every run of
`G` and of `P` halts with the scripted output, and no other output, then
the driver halts with `z`, and every halting run of the driver outputs
`z`. This is `loop_script`. The hypotheses are exactly what the clauses
of `Computes` give for `P` at admissible word lengths, and what the
bridge from IMP+ gives for `G`.
-/

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim

/-- The rounds of a script, from round `j` on: the runs of `G` and `P` of
the calls `j, …, R − 1`, then the last run of `G`. -/
def scriptTime (tG tP : ℕ → ℕ) (R j : ℕ) : ℕ :=
  (∑ i ∈ Finset.Ico j R, (tG i + tP i + 2)) + (tG R + 1)

/-- The facts about one call of the script. -/
structure CallOK (w : ℕ) (G P : Program) (x : List ℕ) (A B : ℕ → List ℕ) (tG tP : ℕ → ℕ)
    (j : ℕ) : Prop where
  sizeG : lpSize w (2 * j) ≠ 0
  runG : RunsTo (lpV w (2 * j)) G (lpU x (A j) (B j)) (A (j + 1)) (tG j)
  uniqG : ∀ o t, RunsTo (lpV w (2 * j)) G (lpU x (A j) (B j)) o t → o = A (j + 1)
  ne : A (j + 1) ≠ []
  head : (A (j + 1)).head? ≠ some 0
  capG : (A (j + 1)).length ≤ lpCap w
  sizeP : lpSize w (2 * j + 1) ≠ 0
  runP : RunsTo (lpV w (2 * j + 1)) P (lpQ (A (j + 1))) (B (j + 1)) (tP j)
  uniqP : ∀ r t, RunsTo (lpV w (2 * j + 1)) P (lpQ (A (j + 1))) r t → r = B (j + 1)
  capP : (B (j + 1)).length ≤ lpCap w

/-- The facts about the last round of the script. -/
structure DoneOK (w : ℕ) (G : Program) (x : List ℕ) (A B : ℕ → List ℕ) (tG : ℕ → ℕ) (R : ℕ)
    (z : List ℕ) : Prop where
  sizeG : lpSize w (2 * R) ≠ 0
  runG : RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) (0 :: z) (tG R)
  uniqG : ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z
  cap : (0 :: z).length ≤ lpCap w

theorem script_fwd {w : ℕ} {G P : Program} {x : List ℕ} {A B : ℕ → List ℕ} {tG tP : ℕ → ℕ}
    {R : ℕ} {z : List ℕ} (hC : ∀ j < R, CallOK w G P x A B tG tP j)
    (hD : DoneOK w G x A B tG R z) :
    ∀ m ≤ R, LoopTrace w G P x (2 * (R - m)) (A (R - m)) (B (R - m)) z
      (scriptTime tG tP R (R - m)) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [Nat.sub_zero, scriptTime, Finset.Ico_self, Finset.sum_empty, Nat.zero_add]
    exact LoopTrace.done hD.sizeG hD.runG hD.cap
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    set j := R - (m + 1) with hj
    have hj1 : R - m = j + 1 := by omega
    rw [hj1] at ih'
    have c := hC j (by omega)
    have hT : scriptTime tG tP R j = tG j + tP j + 2 + scriptTime tG tP R (j + 1) := by
      simp only [scriptTime]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      ring
    rw [hT]
    exact LoopTrace.call c.sizeG c.runG c.ne c.head c.capG c.sizeP c.runP c.capP
      (by rw [show 2 * (j + 1) = 2 * j + 2 by ring] at ih'; exact ih')

/-- What the soundness half needs of a call: the outputs of `G` and of
`P` are unique, and the call is not the last round. -/
structure CallUniq (w : ℕ) (G P : Program) (x : List ℕ) (A B : ℕ → List ℕ) (j : ℕ) : Prop where
  uniqG : ∀ o t, RunsTo (lpV w (2 * j)) G (lpU x (A j) (B j)) o t → o = A (j + 1)
  head : (A (j + 1)).head? ≠ some 0
  uniqP : ∀ r t, RunsTo (lpV w (2 * j + 1)) P (lpQ (A (j + 1))) r t → r = B (j + 1)

theorem CallOK.uniq {w : ℕ} {G P : Program} {x : List ℕ} {A B : ℕ → List ℕ} {tG tP : ℕ → ℕ}
    {j : ℕ} (h : CallOK w G P x A B tG tP j) : CallUniq w G P x A B j :=
  ⟨h.uniqG, h.head, h.uniqP⟩

theorem script_back {w : ℕ} {G P : Program} {x : List ℕ} {A B : ℕ → List ℕ}
    {R : ℕ} {z : List ℕ} (hC : ∀ j < R, CallUniq w G P x A B j)
    (hD : ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) {i : ℕ}
    {a b z' : List ℕ} {T : ℕ} (h : LoopTrace w G P x i a b z' T) :
    ∀ j ≤ R, i = 2 * j → a = A j → b = B j → z' = z := by
  induction h with
  | done hs hG ho =>
    intro j hj hi ha hb
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · have := (hC j hlt).uniqG _ _ hG
      have h0 := (hC j hlt).head
      rw [← this] at h0; simp at h0
    · have := hD _ _ hG
      exact (List.cons.inj this).2
  | call hs hG hne h0 ho hs' hP hr _ ih =>
    intro j hj hi ha hb
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · have c := hC j hlt
      have e1 := c.uniqG _ _ hG
      subst e1
      have e2 := c.uniqP _ _ hP
      subst e2
      exact ih (j + 1) (by omega) (by ring) rfl rfl
    · have := hD _ _ hG
      rw [this] at h0; simp at h0

/-- **Soundness of a script.** If the outputs of the rounds are unique
along the script, every halting run of the driver outputs `z`. -/
theorem loop_script_sound {G P p : Program}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)
    {w : ℕ} {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1)) {A B : ℕ → List ℕ}
    {R : ℕ} {z : List ℕ} (hA0 : A 0 = lpA0 x) (hB0 : B 0 = [])
    (hC : ∀ j < R, CallUniq w G P x A B j)
    (hD : ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) :
    ∀ z' t, RunsTo w p x z' t → z' = z := by
  intro z' t h
  obtain ⟨T, hT⟩ := hp w x hw hx z' t h
  exact script_back hC hD hT 0 (Nat.zero_le _) rfl hA0.symm hB0.symm

/-- **Running a script.** If the rounds follow the script, the driver
halts with `z` within the cost of the script. -/
theorem loop_script_run {G P p : Program} {K : ℕ}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z T, LoopTrace w G P x 0 (lpA0 x) [] z T → ∃ t ≤ K * (T + z.length + 1), RunsTo w p x z t)
    {w : ℕ} {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1)) {A B : ℕ → List ℕ}
    {tG tP : ℕ → ℕ} {R : ℕ} {z : List ℕ} (hA0 : A 0 = lpA0 x) (hB0 : B 0 = [])
    (hC : ∀ j < R, CallOK w G P x A B tG tP j) (hD : DoneOK w G x A B tG R z) :
    ∃ t ≤ K * (scriptTime tG tP R 0 + z.length + 1), RunsTo w p x z t := by
  have htr := script_fwd hC hD R le_rfl
  rw [Nat.sub_self, hA0, hB0] at htr
  exact hp w x hw hx z _ htr

end Lax185574Proofs.Simulate
