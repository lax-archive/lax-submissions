/-
# Counter machines

A counter machine is a finite list of instructions operating on registers holding natural
numbers.  There are three instructions: increment a register, decrement a register (or
jump, if it is zero), and jump.  Execution is deterministic and the machine halts when the
program counter runs past the end of the program.

This file develops the small amount of machinery needed to *compose* counter machine
programs: relocation of jump targets, the behaviour of a program embedded in a larger one,
a sequencing combinator, a loop combinator, and criteria for termination and divergence.
-/
import Lax251941Proofs.Source.PCP.Basic

namespace Lax251941Proofs.PCP
namespace Sim

/-- An instruction of a counter machine. -/
inductive Instr where
  /-- Increment a register and continue with the next instruction. -/
  | inc (r : ℕ) : Instr
  /-- If the register is zero, jump; otherwise decrement it and continue. -/
  | dec (r : ℕ) (j : ℕ) : Instr
  /-- Jump. -/
  | jmp (j : ℕ) : Instr
deriving DecidableEq, Repr

/-- A counter machine program. -/
abbrev Prog := List Instr

/-- The registers of a counter machine. -/
abbrev Regs := ℕ → ℕ

/-- A configuration of a counter machine: a program counter and the registers. -/
abbrev CCfg := ℕ × Regs

/-- The effect of a single instruction. -/
def instrStep : Instr → CCfg → CCfg
  | .inc r, (pc, s) => (pc + 1, Function.update s r (s r + 1))
  | .dec r j, (pc, s) => if s r = 0 then (j, s) else (pc + 1, Function.update s r (s r - 1))
  | .jmp j, (_, s) => (j, s)

/-- One step of a counter machine.  A configuration whose program counter is past the end
of the program is a fixed point: the machine has halted. -/
def cstep (P : Prog) (c : CCfg) : CCfg :=
  match P[c.1]? with
  | none => c
  | some i => instrStep i c

lemma cstep_of_getElem? {P : Prog} {c : CCfg} {i : Instr} (h : P[c.1]? = some i) :
    cstep P c = instrStep i c := by
  rw [cstep, h]

lemma cstep_of_halted {P : Prog} {c : CCfg} (h : P.length ≤ c.1) : cstep P c = c := by
  rw [cstep, List.getElem?_eq_none h]

lemma iterate_of_halted {P : Prog} {c : CCfg} (h : P.length ≤ c.1) (t : ℕ) :
    (cstep P)^[t] c = c := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', ih, cstep_of_halted h]

lemma iter_add (f : CCfg → CCfg) (a b : ℕ) (x : CCfg) : f^[a + b] x = f^[b] (f^[a] x) := by
  rw [Nat.add_comm, Function.iterate_add_apply]

/-! ## Relocation -/

/-- Add an offset to the jump targets of an instruction. -/
def shiftI (k : ℕ) : Instr → Instr
  | .inc r => .inc r
  | .dec r j => .dec r (k + j)
  | .jmp j => .jmp (k + j)

/-- Add an offset to the jump targets of a program. -/
def shift (k : ℕ) (P : Prog) : Prog := P.map (shiftI k)

@[simp] lemma shift_length (k : ℕ) (P : Prog) : (shift k P).length = P.length := by
  simp [shift]

lemma instrStep_shift (k : ℕ) (i : Instr) (pc : ℕ) (s : Regs) :
    instrStep (shiftI k i) (k + pc, s) =
      (k + (instrStep i (pc, s)).1, (instrStep i (pc, s)).2) := by
  cases i with
  | inc r => simp [instrStep, shiftI, Nat.add_assoc]
  | dec r j =>
    by_cases h : s r = 0 <;> simp [instrStep, shiftI, h, Nat.add_assoc]
  | jmp j => simp [instrStep, shiftI]

/-! ## Embedding a program into a larger one -/

lemma cstep_append_left (P B : Prog) {c : CCfg} (h : c.1 < P.length) :
    cstep (P ++ B) c = cstep P c := by
  rw [cstep, cstep, List.getElem?_append_left h]

lemma iterate_append_left (P B : Prog) (c : CCfg) (t : ℕ)
    (h : ∀ u < t, ((cstep P)^[u] c).1 < P.length) :
    (cstep (P ++ B))^[t] c = (cstep P)^[t] c := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun u hu => h u (by omega))]
    exact cstep_append_left P B (h t (by omega))

lemma cstep_append_right (A Q : Prog) {c : CCfg} (h : c.1 < Q.length) :
    cstep (A ++ shift A.length Q) (A.length + c.1, c.2)
      = (A.length + (cstep Q c).1, (cstep Q c).2) := by
  obtain ⟨pc, s⟩ := c
  simp only at h ⊢
  have hget : (A ++ shift A.length Q)[A.length + pc]? = (shift A.length Q)[pc]? := by
    rw [List.getElem?_append_right (by omega)]
    congr 1
    omega
  have hq : ∃ i, Q[pc]? = some i := by
    exact ⟨Q[pc]'h, List.getElem?_eq_getElem h⟩
  obtain ⟨i, hi⟩ := hq
  have hget2 : (shift A.length Q)[pc]? = some (shiftI A.length i) := by
    rw [shift, List.getElem?_map, hi]
    rfl
  rw [cstep_of_getElem? (by rw [hget, hget2]), cstep_of_getElem? hi]
  exact instrStep_shift _ _ _ _

lemma iterate_append_right (A Q : Prog) (c : CCfg) (t : ℕ)
    (h : ∀ u < t, ((cstep Q)^[u] c).1 < Q.length) :
    (cstep (A ++ shift A.length Q))^[t] (A.length + c.1, c.2)
      = (A.length + ((cstep Q)^[t] c).1, ((cstep Q)^[t] c).2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun u hu => h u (by omega))]
    exact cstep_append_right A Q (h t (by omega))

/-! ## Running a program -/

/-- `Runs P s s'` says that the program `P`, started with registers `s`, halts with
registers `s'`, having passed through no configuration whose program counter lies outside
the program. -/
def Runs (P : Prog) (s s' : Regs) : Prop :=
  ∃ t, (cstep P)^[t] (0, s) = (P.length, s') ∧ ∀ u < t, ((cstep P)^[u] (0, s)).1 < P.length

/-- `CHalts P s` says that the program `P` started with registers `s` halts. -/
def CHalts (P : Prog) (s : Regs) : Prop := ∃ t, P.length ≤ ((cstep P)^[t] (0, s)).1

lemma CHalts.of_runs {P : Prog} {s s' : Regs} (h : Runs P s s') : CHalts P s := by
  obtain ⟨t, ht, -⟩ := h
  exact ⟨t, by rw [ht]⟩

/-! ## A criterion for divergence -/

/-- If from every configuration of a set `X` the machine returns, after at least one step,
to a configuration of `X` without leaving the program, then it never halts. -/
lemma not_halts_of_invariant {P : Prog} {s : Regs} (X : CCfg → Prop) (hs : X (0, s))
    (hX : ∀ c, X c → ∃ k, 0 < k ∧ X ((cstep P)^[k] c) ∧
      ∀ u < k, ((cstep P)^[u] c).1 < P.length) :
    ¬ CHalts P s := by
  have key : ∀ t (c : CCfg), X c → ((cstep P)^[t] c).1 < P.length := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro c hc
      obtain ⟨k, hk, hXk, hlt⟩ := hX c hc
      by_cases h : t < k
      · exact hlt t h
      · obtain ⟨t', rfl⟩ : ∃ t', t = k + t' := ⟨t - k, by omega⟩
        rw [iter_add]
        exact ih t' (by omega) _ hXk
  rintro ⟨t, ht⟩
  exact absurd (key t (0, s) hs) (by omega)

/-! ## Sequencing -/

/-- Run one program and then another. -/
def pseq (P Q : Prog) : Prog := P ++ shift P.length Q

@[simp] lemma pseq_length (P Q : Prog) : (pseq P Q).length = P.length + Q.length := by
  simp [pseq]

lemma runs_pseq {P Q : Prog} {s s₁ s₂ : Regs} (h₁ : Runs P s s₁) (h₂ : Runs Q s₁ s₂) :
    Runs (pseq P Q) s s₂ := by
  obtain ⟨t₁, ht₁, hlt₁⟩ := h₁
  obtain ⟨t₂, ht₂, hlt₂⟩ := h₂
  refine ⟨t₁ + t₂, ?_, ?_⟩
  · rw [iter_add]
    have e1 : (cstep (pseq P Q))^[t₁] (0, s) = (P.length, s₁) := by
      rw [pseq, iterate_append_left P _ _ _ hlt₁, ht₁]
    rw [e1]
    have e2 := iterate_append_right P Q (0, s₁) t₂ hlt₂
    simp only [Nat.add_zero] at e2
    rw [pseq, e2, ht₂]
    simp
  · intro u hu
    by_cases h : u < t₁
    · have : (cstep (pseq P Q))^[u] (0, s) = (cstep P)^[u] (0, s) := by
        rw [pseq, iterate_append_left P _ _ _ (fun v hv => hlt₁ v (by omega))]
      rw [this]
      have := hlt₁ u h
      simp only [pseq_length]
      omega
    · obtain ⟨u', rfl⟩ : ∃ u', u = t₁ + u' := ⟨u - t₁, by omega⟩
      have hu' : u' < t₂ := by omega
      rw [iter_add]
      have e1 : (cstep (pseq P Q))^[t₁] (0, s) = (P.length, s₁) := by
        rw [pseq, iterate_append_left P _ _ _ hlt₁, ht₁]
      rw [e1]
      have e2 := iterate_append_right P Q (0, s₁) u' (fun v hv => hlt₂ v (by omega))
      simp only [Nat.add_zero] at e2
      rw [pseq, e2]
      have := hlt₂ u' hu'
      simp only [List.length_append, shift_length]
      omega

lemma not_halts_pseq_left {P Q : Prog} {s : Regs} (h : ¬ CHalts P s) : ¬ CHalts (pseq P Q) s := by
  have hall : ∀ t, ((cstep P)^[t] (0, s)).1 < P.length := by
    intro t
    by_contra hc
    exact h ⟨t, by omega⟩
  rintro ⟨t, ht⟩
  rw [pseq, iterate_append_left P _ _ _ (fun u _ => hall u)] at ht
  have := hall t
  simp only [List.length_append, shift_length] at ht
  omega

lemma not_halts_pseq_right {P Q : Prog} {s s₁ : Regs} (h₁ : Runs P s s₁) (h : ¬ CHalts Q s₁) :
    ¬ CHalts (pseq P Q) s := by
  obtain ⟨t₁, ht₁, hlt₁⟩ := h₁
  have hall : ∀ t, ((cstep Q)^[t] (0, s₁)).1 < Q.length := by
    intro t
    by_contra hc
    exact h ⟨t, by omega⟩
  rintro ⟨t, ht⟩
  have e1 : (cstep (pseq P Q))^[t₁] (0, s) = (P.length, s₁) := by
    rw [pseq, iterate_append_left P _ _ _ hlt₁, ht₁]
  by_cases hle : t ≤ t₁
  · have : (cstep (pseq P Q))^[t] (0, s) = (cstep P)^[t] (0, s) := by
      rw [pseq, iterate_append_left P _ _ _ (fun v hv => hlt₁ v (by omega))]
    rw [this] at ht
    rcases Nat.lt_or_ge t t₁ with hlt | hge
    · have := hlt₁ t hlt
      simp only [pseq_length] at ht
      omega
    · have ht' : t = t₁ := by omega
      subst ht'
      rw [ht₁] at ht
      simp only [pseq_length] at ht
      have : 0 < Q.length := by
        by_contra hq
        have hq0 : Q.length = 0 := by omega
        have := hall 0
        omega
      omega
  · obtain ⟨u, rfl⟩ : ∃ u, t = t₁ + u := ⟨t - t₁, by omega⟩
    rw [iter_add, e1] at ht
    have e2 := iterate_append_right P Q (0, s₁) u (fun v _ => hall v)
    simp only [Nat.add_zero] at e2
    rw [pseq, e2] at ht
    have := hall u
    simp only [List.length_append, shift_length] at ht
    omega

/-! ## The loop combinator -/

/-- `loopDec r B`: while the register `r` is nonzero, decrement it and run `B`. -/
def loopDec (r : ℕ) (B : Prog) : Prog :=
  Instr.dec r (B.length + 2) :: (shift 1 B ++ [Instr.jmp 0])

@[simp] lemma loopDec_length (r : ℕ) (B : Prog) : (loopDec r B).length = B.length + 2 := by
  simp [loopDec]

lemma loopDec_eq (r : ℕ) (B : Prog) :
    loopDec r B = ([Instr.dec r (B.length + 2)] ++ shift 1 B) ++ [Instr.jmp 0] := rfl

lemma iterate_loop_body (r : ℕ) (B : Prog) (c : CCfg) (t : ℕ)
    (h : ∀ u < t, ((cstep B)^[u] c).1 < B.length) :
    (cstep (loopDec r B))^[t] (1 + c.1, c.2) = (1 + ((cstep B)^[t] c).1, ((cstep B)^[t] c).2) := by
  have hlen : ([Instr.dec r (B.length + 2)] : Prog).length = 1 := rfl
  have key : ∀ u ≤ t, (cstep ([Instr.dec r (B.length + 2)] ++ shift 1 B))^[u] (1 + c.1, c.2)
      = (1 + ((cstep B)^[u] c).1, ((cstep B)^[u] c).2) := by
    intro u hu
    have := iterate_append_right [Instr.dec r (B.length + 2)] B c u
      (fun v hv => h v (by omega))
    rw [hlen] at this
    exact this
  have hb : ∀ u < t, ((cstep ([Instr.dec r (B.length + 2)] ++ shift 1 B))^[u]
      (1 + c.1, c.2)).1 < ([Instr.dec r (B.length + 2)] ++ shift 1 B).length := by
    intro u hu
    rw [key u (by omega)]
    have := h u hu
    simp only [List.length_append, shift_length, hlen]
    omega
  rw [loopDec_eq, iterate_append_left _ _ _ t hb, key t le_rfl]

lemma runs_nil (s : Regs) : Runs [] s s := ⟨0, by simp, by omega⟩

lemma runs_inc (r : ℕ) (s : Regs) : Runs [Instr.inc r] s (Function.update s r (s r + 1)) := by
  refine ⟨1, ?_, ?_⟩
  · show cstep [Instr.inc r] (0, s) = _
    simp [cstep, instrStep]
  · intro u hu
    interval_cases u
    · simp

/-- One turn of the loop: the register is decremented, the body is run, and control
returns to the top of the loop. -/
lemma loopDec_turn (r : ℕ) (B : Prog) {s s₁ : Regs} (hz : s r ≠ 0)
    (hB : Runs B (Function.update s r (s r - 1)) s₁) :
    ∃ k, 0 < k ∧ (cstep (loopDec r B))^[k] (0, s) = (0, s₁) ∧
      ∀ u < k, ((cstep (loopDec r B))^[u] (0, s)).1 < (loopDec r B).length := by
  obtain ⟨t, ht, hlt⟩ := hB
  refine ⟨t + 2, by omega, ?_, ?_⟩
  · -- first the decrement, then the body, then the jump back
    have h0 : cstep (loopDec r B) (0, s) = (1, Function.update s r (s r - 1)) := by
      have hget : (loopDec r B)[(0 : ℕ)]? = some (Instr.dec r (B.length + 2)) := rfl
      rw [cstep_of_getElem? hget]
      simp [instrStep, hz]
    have h1 : (cstep (loopDec r B))^[t] (1, Function.update s r (s r - 1))
        = (1 + B.length, s₁) := by
      have := iterate_loop_body r B (0, Function.update s r (s r - 1)) t hlt
      simp only [Nat.add_zero] at this
      rw [this, ht]
    have h2 : cstep (loopDec r B) (1 + B.length, s₁) = (0, s₁) := by
      have hget : (loopDec r B)[1 + B.length]? = some (Instr.jmp 0) := by
        rw [loopDec_eq]
        rw [List.getElem?_append_right (by simp)]
        simp only [List.length_append, shift_length, List.length_cons, List.length_nil,
          show 1 + B.length - (0 + 1 + B.length) = 0 from by omega]
        rfl
      rw [cstep_of_getElem? hget]
      rfl
    have : t + 2 = 1 + t + 1 := by omega
    rw [this, iter_add, iter_add, Function.iterate_one, h0, h1]
    exact h2
  · intro u hu
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · simp [loopDec]
    · obtain ⟨u', rfl⟩ : ∃ u', u = 1 + u' := ⟨u - 1, by omega⟩
      have h0 : cstep (loopDec r B) (0, s) = (1, Function.update s r (s r - 1)) := by
        have hget : (loopDec r B)[(0 : ℕ)]? = some (Instr.dec r (B.length + 2)) := rfl
        rw [cstep_of_getElem? hget]
        simp [instrStep, hz]
      rw [iter_add, Function.iterate_one, h0]
      rcases Nat.lt_or_ge u' t with hlt' | hge
      · have := iterate_loop_body r B (0, Function.update s r (s r - 1)) u'
          (fun v hv => hlt v (by omega))
        simp only [Nat.add_zero] at this
        rw [this]
        have := hlt u' hlt'
        simp only [loopDec_length]
        omega
      · have hu' : u' = t := by omega
        subst hu'
        have h1 : (cstep (loopDec r B))^[u'] (1, Function.update s r (s r - 1))
            = (1 + B.length, s₁) := by
          have := iterate_loop_body r B (0, Function.update s r (s r - 1)) u' hlt
          simp only [Nat.add_zero] at this
          rw [this, ht]
        rw [h1]
        simp only [loopDec_length]
        omega

lemma loopDec_exit (r : ℕ) (B : Prog) {s : Regs} (hz : s r = 0) :
    Runs (loopDec r B) s s := by
  refine ⟨1, ?_, ?_⟩
  · have hget : (loopDec r B)[(0 : ℕ)]? = some (Instr.dec r (B.length + 2)) := rfl
    rw [Function.iterate_one, cstep_of_getElem? hget]
    simp [instrStep, hz]
  · intro u hu
    interval_cases u
    · simp [loopDec]

/-- The intended semantics of the loop: it terminates after finitely many turns. -/
inductive LoopRuns (r : ℕ) (B : Prog) : Regs → Regs → Prop
  | zero {s : Regs} : s r = 0 → LoopRuns r B s s
  | step {s s₁ s₂ : Regs} : s r ≠ 0 → Runs B (Function.update s r (s r - 1)) s₁ →
      LoopRuns r B s₁ s₂ → LoopRuns r B s s₂

lemma runs_loopDec {r : ℕ} {B : Prog} {s s' : Regs} (h : LoopRuns r B s s') :
    Runs (loopDec r B) s s' := by
  induction h with
  | zero hz => exact loopDec_exit r B hz
  | @step s s₁ s₂ hz hB _ ih =>
    obtain ⟨k, hk, hkeq, hklt⟩ := loopDec_turn r B hz hB
    obtain ⟨t, ht, hlt⟩ := ih
    refine ⟨k + t, ?_, ?_⟩
    · rw [iter_add, hkeq, ht]
    · intro u hu
      rcases Nat.lt_or_ge u k with h1 | h1
      · exact hklt u h1
      · obtain ⟨u', rfl⟩ : ∃ u', u = k + u' := ⟨u - k, by omega⟩
        rw [iter_add, hkeq]
        exact hlt u' (by omega)

/-- If the loop condition is maintained by an invariant, the loop never terminates. -/
lemma not_halts_loopDec {r : ℕ} {B : Prog} (I : Regs → Prop)
    (hI : ∀ s, I s → s r ≠ 0)
    (hstep : ∀ s, I s → ∃ s', Runs B (Function.update s r (s r - 1)) s' ∧ I s')
    {s : Regs} (hs : I s) : ¬ CHalts (loopDec r B) s := by
  refine not_halts_of_invariant (fun c => c.1 = 0 ∧ I c.2) ⟨rfl, hs⟩ ?_
  rintro ⟨pc, s'⟩ ⟨rfl, hI'⟩
  obtain ⟨s'', hB, hI''⟩ := hstep s' hI'
  obtain ⟨k, hk, hkeq, hklt⟩ := loopDec_turn r B (hI s' hI') hB
  exact ⟨k, hk, by rw [hkeq]; exact ⟨rfl, hI''⟩, hklt⟩

/-- Clearing a register. -/
def pclear (r : ℕ) : Prog := loopDec r []

lemma runs_pclear (r : ℕ) (s : Regs) : Runs (pclear r) s (Function.update s r 0) := by
  have key : ∀ n (s : Regs), s r = n → LoopRuns r [] s (Function.update s r 0) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have : Function.update s r 0 = s := by
        funext x
        by_cases hx : x = r
        · subst hx; simp [hs]
        · simp [Function.update_of_ne hx]
      rw [this]
      exact LoopRuns.zero hs
    | succ n ih =>
      intro s hs
      refine LoopRuns.step (by omega) (runs_nil _) ?_
      have h1 : (Function.update s r (s r - 1)) r = n := by simp [hs]
      have := ih _ h1
      have h2 : Function.update (Function.update s r (s r - 1)) r 0 = Function.update s r 0 := by
        funext x
        by_cases hx : x = r
        · subst hx; simp
        · simp [Function.update_of_ne hx]
      rwa [h2] at this
  exact runs_loopDec (key (s r) s rfl)

end Sim
end Lax251941Proofs.PCP
