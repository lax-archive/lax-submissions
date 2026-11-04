import Lax185574Proofs.LoopScript

/-!
Soundness of a script of the loop driver whose callee is only known to
be right after a halting run of the glue program.

In `loop_script_sound` every call of the script must have a unique
callee output. Here the callee output of call `j` needs to be unique
only when the glue program halted in round `j` with the scripted
output. This is the situation of a guarded glue program, which halts
only after it has checked that its query is admissible for the callee.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.RamSim Lax185574Proofs.Simulate

/-- What soundness needs of round `j < R`: a halting run of `G` has the
scripted output, which is not the last one, and then every halting run
of `P` on its query has the scripted answer. -/
def CondCall (w : ℕ) (G P : Program) (x : List ℕ) (A B : ℕ → List ℕ) (j : ℕ) : Prop :=
  ∀ o t, RunsTo (lpV w (2 * j)) G (lpU x (A j) (B j)) o t →
    o = A (j + 1) ∧ (A (j + 1)).head? ≠ some 0 ∧
      ∀ r t', RunsTo (lpV w (2 * j + 1)) P (lpQ o) r t' → r = B (j + 1)

theorem cond_script_back {w : ℕ} {G P : Program} {x : List ℕ} {A B : ℕ → List ℕ}
    {R : ℕ} {z : List ℕ} (hC : ∀ j < R, CondCall w G P x A B j)
    (hD : ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) {i : ℕ}
    {a b z' : List ℕ} {T : ℕ} (h : LoopTrace w G P x i a b z' T) :
    ∀ j ≤ R, i = 2 * j → a = A j → b = B j → z' = z := by
  induction h with
  | done hs hG ho =>
    intro j hj hi ha hb
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e1, h0, -⟩ := hC j hlt _ _ hG
      rw [← e1] at h0; simp at h0
    · exact (List.cons.inj (hD _ _ hG)).2
  | call hs hG hne h0 ho hs' hP hr _ ih =>
    intro j hj hi ha hb
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e1, -, hPu⟩ := hC j hlt _ _ hG
      have e2 := hPu _ _ hP
      subst e1 e2
      exact ih (j + 1) (by omega) (by ring) rfl rfl
    · have := hD _ _ hG
      rw [this] at h0; simp at h0

/-- **Soundness of a conditional script.** Every halting run of the
driver outputs the scripted `z`. -/
theorem cond_script_sound {G P p : Program}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)
    {w : ℕ} {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1)) {A B : ℕ → List ℕ}
    {R : ℕ} {z : List ℕ} (hA0 : A 0 = lpA0 x) (hB0 : B 0 = [])
    (hC : ∀ j < R, CondCall w G P x A B j)
    (hD : ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) :
    ∀ z' t, RunsTo w p x z' t → z' = z := by
  intro z' t h
  obtain ⟨T, hT⟩ := hp w x hw hx z' t h
  exact cond_script_back hC hD hT 0 (Nat.zero_le _) rfl hA0.symm hB0.symm

/-- A driver whose first round never halts never halts. -/
theorem loop_never {G P p : Program}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)
    {w : ℕ} {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1))
    (h0 : ∀ o t, ¬ RunsTo (lpV w 0) G (lpU x (lpA0 x) []) o t) :
    ∀ z t, ¬ RunsTo w p x z t := by
  intro z t h
  obtain ⟨T, hT⟩ := hp w x hw hx z t h
  cases hT with
  | done _ hG _ => exact h0 _ _ hG
  | call _ hG => exact h0 _ _ hG

end Lax185574Proofs.MC
