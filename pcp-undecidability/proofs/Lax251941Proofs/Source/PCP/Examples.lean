/-
# Sanity checks

Two small checks that the definitions say what they are meant to say, and in particular
that the main equivalence `hasMatch_sipserPCP_iff` is not vacuous: for one machine both
sides hold, for another both sides fail.
-/
import Lax251941Proofs.Source.PCP.Reduction

namespace Lax251941Proofs.PCP

/-- A one-domino instance whose top and bottom strings agree has a match. -/
example : HasMatch ([([0], [0])] : Inst ℕ) :=
  ⟨[([0], [0])], by simp, by simp, rfl⟩

/-! ## A machine that accepts -/

/-- A machine whose start state is already its accept state. -/
def trivialTM : TM := ⟨[], 0, 0⟩

lemma trivialTM_accepts (w : List ℕ) : trivialTM.Accepts w :=
  ⟨trivialTM.startCfg w, Reaches.refl _ _, by simp [TM.startCfg, trivialTM]⟩

/-- The PCP instance built from a machine that accepts really does have a match. -/
theorem hasMatch_sipserPCP_trivialTM (w : List ℕ) : HasMatch (sipserPCP trivialTM w) :=
  (hasMatch_sipserPCP_iff trivialTM w).2 (trivialTM_accepts w)

/-! ## A machine that does not accept -/

/-- A machine with no transitions at all, whose accept state differs from its start
state; it accepts nothing. -/
def emptyTM : TM := ⟨[], 0, 1⟩

lemma emptyTM_rules (w : List ℕ) : (emptyTM.machineSRS w).rules = [] := by
  simp [TM.machineSRS, TM.transRules, TM.rightRules, TM.leftRules, emptyTM]

lemma emptyTM_ext (w : List ℕ) : (emptyTM.machineSRS w).ext = [Sym.tape 0] := rfl

/-- A system without rules admits no rule step. -/
lemma not_stepRule_nil {α : Type*} {a b : List α} (h : StepRule [] a b) : False := by
  cases h with
  | mk l u v r hmem => simp at hmem

/-- Every configuration reachable by the transition-free machine consists of the start
state followed by blanks. -/
lemma emptyTM_reachable {C : List Sym}
    (h : Reaches (emptyTM.machineSRS []) (emptyTM.startCfg []) C) :
    ∃ n, C = Sym.state 0 :: List.replicate n (Sym.tape 0) := by
  induction h with
  | refl => exact ⟨0, by simp [TM.startCfg, emptyTM]⟩
  | @tail D E _ hstep ih =>
    obtain ⟨n, rfl⟩ := ih
    cases hstep with
    | rule hr =>
      rw [emptyTM_rules] at hr
      exact (not_stepRule_nil hr).elim
    | @ext x hx =>
      have hx' : x = Sym.tape 0 := by
        simpa [emptyTM_ext] using hx
      subst hx'
      exact ⟨n + 1, by simp [List.replicate_succ']⟩

/-- The transition-free machine does not accept the empty word. -/
theorem emptyTM_not_accepts : ¬ emptyTM.Accepts [] := by
  rintro ⟨C, hreach, hC⟩
  obtain ⟨n, rfl⟩ := emptyTM_reachable hreach
  simp only [List.mem_cons, List.mem_replicate] at hC
  rcases hC with h | ⟨-, h⟩ <;> exact absurd h (by simp [emptyTM])

/-- The PCP instance built from a machine that does not accept really has no match. -/
theorem not_hasMatch_sipserPCP_emptyTM : ¬ HasMatch (sipserPCP emptyTM []) :=
  fun h => emptyTM_not_accepts ((hasMatch_sipserPCP_iff emptyTM []).1 h)

end Lax251941Proofs.PCP
