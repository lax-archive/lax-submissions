/-
# Turing machines, configurations and computation histories

Following Sipser, Section 5.2, we view a configuration of a single-tape Turing machine as
a string `u q v`, where `u` and `v` are the tape contents to the left and to the right of
the head and `q` is the current state.  A single computation step then rewrites the
configuration string locally, around the state symbol:

* `q a ⟶ b r` if `δ(q,a) = (r,b,R)` (Sipser's part 2);
* `c q a ⟶ r c b` if `δ(q,a) = (r,b,L)` (Sipser's part 3);

and a blank may be appended at the right-hand end of the configuration, which models the
infinitely many blanks that are suppressed when a configuration is written down.

As in Sipser, a left move is possible only if there is a tape symbol to the left of the
head, i.e. the machine never moves its head off the left-hand end of the tape.

The machine accepts `w` if some configuration containing the accept state is reachable
from the starting configuration `q₀ w`.
-/
import Lax251941.TuringMachines
import Lax251941Proofs.Source.PCP.SRtoMPCP
import Lax251941Proofs.Source.PCP.StarTrick

namespace Lax251941Proofs.PCP

/-- The symbols used to write configurations: the alphabet `Sym` of the concept
`Lax251941.TuringMachines`, shared with the concept package so that the statements
about machines need no translation of alphabets; the constructors are re-exported as
pattern-matchable abbreviations. -/
abbrev Sym := Lax251941.TuringMachines.Sym

/-- A tape symbol; `Sym.tape 0` is the blank `␣`. -/
@[match_pattern] abbrev Sym.tape : ℕ → Sym := Lax251941.TuringMachines.Sym.tape
/-- A state of the machine. -/
@[match_pattern] abbrev Sym.state : ℕ → Sym := Lax251941.TuringMachines.Sym.state
/-- The separator `#` between consecutive configurations. -/
@[match_pattern] abbrev Sym.hash : Sym := Lax251941.TuringMachines.Sym.hash
/-- The marker opening a computation history. -/
@[match_pattern] abbrev Sym.start : Sym := Lax251941.TuringMachines.Sym.start
/-- The symbol `∗` of the `⋆` construction. -/
@[match_pattern] abbrev Sym.star : Sym := Lax251941.TuringMachines.Sym.star
/-- The symbol `◇` of the `⋆` construction. -/
@[match_pattern] abbrev Sym.diamond : Sym := Lax251941.TuringMachines.Sym.diamond

@[simp] theorem Sym.tape.injEq (a b : ℕ) : (Sym.tape a = Sym.tape b) = (a = b) :=
  Lax251941.TuringMachines.Sym.tape.injEq a b

@[simp] theorem Sym.state.injEq (a b : ℕ) : (Sym.state a = Sym.state b) = (a = b) :=
  Lax251941.TuringMachines.Sym.state.injEq a b

/-- A (possibly nondeterministic) single-tape Turing machine: a finite transition table
together with a start state and an accept state.  An entry `(q, a, r, b, dir)` of the
table means `δ(q,a) = (r, b, dir)`, where `dir = true` stands for a move to the right and
`dir = false` for a move to the left. -/
structure TM where
  /-- The transition table. -/
  trans : List (ℕ × ℕ × ℕ × ℕ × Bool)
  /-- The start state. -/
  q0 : ℕ
  /-- The accept state. -/
  qacc : ℕ

namespace TM

variable (M : TM) (w : List ℕ)

/-- The tape alphabet: the blank, the symbols of the input, and all symbols mentioned in
the transition table. -/
def tapeSyms : List ℕ :=
  0 :: (w ++ M.trans.map (fun x => x.2.1) ++ M.trans.map (fun x => x.2.2.2.1))

/-- The state set: the start state, the accept state and all states mentioned in the
transition table. -/
def states : List ℕ :=
  M.q0 :: M.qacc :: (M.trans.map (fun x => x.1) ++ M.trans.map (fun x => x.2.2.1))

/-- The alphabet in which configurations are written. -/
def alphabet : List Sym :=
  (M.tapeSyms w).map Sym.tape ++ M.states.map Sym.state

lemma tape_mem_alphabet {a : ℕ} (h : a ∈ M.tapeSyms w) : Sym.tape a ∈ M.alphabet w :=
  List.mem_append_left _ (List.mem_map_of_mem h)

lemma state_mem_alphabet {q : ℕ} (h : q ∈ M.states) : Sym.state q ∈ M.alphabet w :=
  List.mem_append_right _ (List.mem_map_of_mem h)

lemma blank_mem_tapeSyms : 0 ∈ M.tapeSyms w := List.mem_cons_self

lemma input_mem_tapeSyms {a : ℕ} (h : a ∈ w) : a ∈ M.tapeSyms w :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h))

lemma read_mem_tapeSyms {q a r b : ℕ} {dir : Bool} (h : (q, a, r, b, dir) ∈ M.trans) :
    a ∈ M.tapeSyms w :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (f := fun x : ℕ × ℕ × ℕ × ℕ × Bool => x.2.1) h)))

lemma write_mem_tapeSyms {q a r b : ℕ} {dir : Bool} (h : (q, a, r, b, dir) ∈ M.trans) :
    b ∈ M.tapeSyms w :=
  List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_map_of_mem (f := fun x : ℕ × ℕ × ℕ × ℕ × Bool => x.2.2.2.1) h))

lemma source_mem_states {q a r b : ℕ} {dir : Bool} (h : (q, a, r, b, dir) ∈ M.trans) :
    q ∈ M.states :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_map_of_mem (f := fun x : ℕ × ℕ × ℕ × ℕ × Bool => x.1) h)))

lemma target_mem_states {q a r b : ℕ} {dir : Bool} (h : (q, a, r, b, dir) ∈ M.trans) :
    r ∈ M.states :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_map_of_mem (f := fun x : ℕ × ℕ × ℕ × ℕ × Bool => x.2.2.1) h)))

lemma q0_mem_states : M.q0 ∈ M.states := List.mem_cons_self

lemma qacc_mem_states : M.qacc ∈ M.states := List.mem_cons_of_mem _ List.mem_cons_self

/-- Sipser's part 2: the rewriting rules for moves to the right. -/
def rightRules : List (List Sym × List Sym) :=
  M.trans.filterMap fun x =>
    if x.2.2.2.2 then
      some ([Sym.state x.1, Sym.tape x.2.1], [Sym.tape x.2.2.2.1, Sym.state x.2.2.1])
    else none

/-- Sipser's part 3: the rewriting rules for moves to the left. -/
def leftRules : List (List Sym × List Sym) :=
  (M.tapeSyms w).flatMap fun c =>
    M.trans.filterMap fun x =>
      if x.2.2.2.2 then none
      else some ([Sym.tape c, Sym.state x.1, Sym.tape x.2.1],
        [Sym.state x.2.2.1, Sym.tape c, Sym.tape x.2.2.2.1])

/-- The rewriting rules describing single steps of the machine. -/
def transRules : List (List Sym × List Sym) := M.rightRules ++ M.leftRules w

/-- Sipser's part 6: once the accept state has been reached, it "eats" the adjacent
symbols. -/
def eatRules : List (List Sym × List Sym) :=
  (M.alphabet w).flatMap fun x =>
    [([x, Sym.state M.qacc], [Sym.state M.qacc]), ([Sym.state M.qacc, x], [Sym.state M.qacc])]

/-- The rewriting system describing the machine itself. -/
def machineSRS : SRS Sym where
  alphabet := M.alphabet w
  rules := M.transRules w
  ext := [Sym.tape 0]

/-- The rewriting system describing the machine together with the "eating" rules that
collapse an accepting configuration to the single symbol `q_accept`. -/
def fullSRS : SRS Sym where
  alphabet := M.alphabet w
  rules := M.transRules w ++ M.eatRules w
  ext := [Sym.tape 0]

/-- The starting configuration `q₀ w`. -/
def startCfg : List Sym := Sym.state M.q0 :: w.map Sym.tape

/-- The machine accepts `w` if a configuration containing the accept state is reachable
from the starting configuration. -/
def Accepts : Prop :=
  ∃ C, Reaches (M.machineSRS w) (M.startCfg w) C ∧ Sym.state M.qacc ∈ C

end TM

section WellFormed

variable (M : TM) (w : List ℕ)

lemma mem_rightRules {u v : List Sym} (h : (u, v) ∈ M.rightRules) :
    (∀ a ∈ u, a ∈ M.alphabet w) ∧ (∀ a ∈ v, a ∈ M.alphabet w) ∧ u ≠ [] ∧ v ≠ [] := by
  simp only [TM.rightRules, List.mem_filterMap] at h
  obtain ⟨x, hx, hx'⟩ := h
  obtain ⟨q, a, r, b, dir⟩ := x
  by_cases hdir : dir
  · simp only [hdir, if_true, Option.some.injEq, Prod.mk.injEq] at hx'
    obtain ⟨hu, hv⟩ := hx'
    subst hu; subst hv
    refine ⟨?_, ?_, by simp, by simp⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact M.state_mem_alphabet w (M.source_mem_states (dir := dir) (by simpa [hdir] using hx))
      · exact M.tape_mem_alphabet w (M.read_mem_tapeSyms w (dir := dir) (by simpa [hdir] using hx))
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact M.tape_mem_alphabet w (M.write_mem_tapeSyms w (dir := dir) (by simpa [hdir] using hx))
      · exact M.state_mem_alphabet w (M.target_mem_states (dir := dir) (by simpa [hdir] using hx))
  · simp [hdir] at hx'

lemma mem_leftRules {u v : List Sym} (h : (u, v) ∈ M.leftRules w) :
    (∀ a ∈ u, a ∈ M.alphabet w) ∧ (∀ a ∈ v, a ∈ M.alphabet w) ∧ u ≠ [] ∧ v ≠ [] := by
  simp only [TM.leftRules, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨c, hc, x, hx, hx'⟩ := h
  obtain ⟨q, a, r, b, dir⟩ := x
  by_cases hdir : dir
  · simp [hdir] at hx'
  · simp only [hdir, if_false, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true] at hx'
    obtain ⟨hu, hv⟩ := hx'
    subst hu; subst hv
    have hx' : (q, a, r, b, false) ∈ M.trans := by simpa [hdir] using hx
    refine ⟨?_, ?_, by simp, by simp⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact M.tape_mem_alphabet w hc
      · exact M.state_mem_alphabet w (M.source_mem_states hx')
      · exact M.tape_mem_alphabet w (M.read_mem_tapeSyms w hx')
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact M.state_mem_alphabet w (M.target_mem_states hx')
      · exact M.tape_mem_alphabet w hc
      · exact M.tape_mem_alphabet w (M.write_mem_tapeSyms w hx')

lemma mem_eatRules {u v : List Sym} (h : (u, v) ∈ M.eatRules w) :
    (∀ a ∈ u, a ∈ M.alphabet w) ∧ (∀ a ∈ v, a ∈ M.alphabet w) ∧ u ≠ [] ∧ v ≠ [] := by
  simp only [TM.eatRules, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨x, hx, hx'⟩ := h
  have hqacc : Sym.state M.qacc ∈ M.alphabet w :=
    M.state_mem_alphabet w M.qacc_mem_states
  rcases hx' with hx' | hx' <;>
    · simp only [Prod.mk.injEq] at hx'
      obtain ⟨hu, hv⟩ := hx'
      subst hu; subst hv
      refine ⟨?_, ?_, by simp, by simp⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · first | exact hx | exact hqacc
        · first | exact hqacc | exact hx
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst hs
        exact hqacc

/-- The rewriting system of a machine is well formed. -/
lemma machineSRS_wf : (M.machineSRS w).WF := by
  constructor <;>
  · intro p hp
    simp only [TM.machineSRS, TM.transRules, List.mem_append] at hp
    first
      | (rcases hp with hp | hp
         · first
             | exact fun a ha => (mem_rightRules M w hp).1 a ha
             | exact fun a ha => (mem_rightRules M w hp).2.1 a ha
             | exact (mem_rightRules M w hp).2.2.1
             | exact (mem_rightRules M w hp).2.2.2
         · first
             | exact fun a ha => (mem_leftRules M w hp).1 a ha
             | exact fun a ha => (mem_leftRules M w hp).2.1 a ha
             | exact (mem_leftRules M w hp).2.2.1
             | exact (mem_leftRules M w hp).2.2.2)
      | (simp only [List.mem_singleton] at hp
         subst hp
         exact M.tape_mem_alphabet w (M.blank_mem_tapeSyms w))

/-- The rewriting system of a machine together with the eating rules is well formed. -/
lemma fullSRS_wf : (M.fullSRS w).WF := by
  constructor <;>
  · intro p hp
    simp only [TM.fullSRS, TM.transRules, List.mem_append] at hp
    first
      | (rcases hp with (hp | hp) | hp
         · first
             | exact fun a ha => (mem_rightRules M w hp).1 a ha
             | exact fun a ha => (mem_rightRules M w hp).2.1 a ha
             | exact (mem_rightRules M w hp).2.2.1
             | exact (mem_rightRules M w hp).2.2.2
         · first
             | exact fun a ha => (mem_leftRules M w hp).1 a ha
             | exact fun a ha => (mem_leftRules M w hp).2.1 a ha
             | exact (mem_leftRules M w hp).2.2.1
             | exact (mem_leftRules M w hp).2.2.2
         · first
             | exact fun a ha => (mem_eatRules M w hp).1 a ha
             | exact fun a ha => (mem_eatRules M w hp).2.1 a ha
             | exact (mem_eatRules M w hp).2.2.1
             | exact (mem_eatRules M w hp).2.2.2)
      | (simp only [List.mem_singleton] at hp
         subst hp
         exact M.tape_mem_alphabet w (M.blank_mem_tapeSyms w))

lemma startCfg_mem_alphabet : ∀ a ∈ M.startCfg w, a ∈ M.alphabet w := by
  intro a ha
  simp only [TM.startCfg, List.mem_cons, List.mem_map] at ha
  rcases ha with rfl | ⟨x, hx, rfl⟩
  · exact M.state_mem_alphabet w M.q0_mem_states
  · exact M.tape_mem_alphabet w (M.input_mem_tapeSyms w hx)

end WellFormed

section EatRules

variable (M : TM) (w : List ℕ)

/-- Applying an eating rule requires the accept state to be present. -/
lemma step_machineSRS_of_step_fullSRS {C D : List Sym}
    (h : Step (M.fullSRS w) C D) (hC : Sym.state M.qacc ∉ C) : Step (M.machineSRS w) C D := by
  cases h with
  | rule hr =>
    cases hr with
    | mk l u v r hmem =>
      simp only [TM.fullSRS, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact Step.rule (StepRule.mk l u v r (by simpa [TM.machineSRS] using hmem))
      · exfalso
        simp only [TM.eatRules, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
          or_false] at hmem
        obtain ⟨x, -, hx⟩ := hmem
        refine hC ?_
        rcases hx with hx | hx <;>
          · have : u = _ := congrArg Prod.fst hx
            simp only at this
            subst this
            simp
  | @ext x hx =>
    exact Step.ext (by simpa [TM.machineSRS] using (by simpa [TM.fullSRS] using hx :
      x ∈ [Sym.tape 0]))

/-- If a configuration containing the accept state is reachable in the full system, then
the machine accepts: no eating rule can have been used before the accept state appeared. -/
lemma accepts_of_reaches_fullSRS {C : List Sym}
    (h : Reaches (M.fullSRS w) (M.startCfg w) C) (hC : Sym.state M.qacc ∈ C) :
    M.Accepts w := by
  have key : ∀ {D : List Sym}, Reaches (M.fullSRS w) (M.startCfg w) D →
      M.Accepts w ∨ (Reaches (M.machineSRS w) (M.startCfg w) D ∧ Sym.state M.qacc ∉ D) := by
    intro D hD
    induction hD with
    | refl =>
      by_cases hq : Sym.state M.qacc ∈ M.startCfg w
      · exact Or.inl ⟨M.startCfg w, Reaches.refl _ _, hq⟩
      · exact Or.inr ⟨Reaches.refl _ _, hq⟩
    | @tail E F _ hstep ih =>
      rcases ih with hacc | ⟨hreach, hE⟩
      · exact Or.inl hacc
      · have hstep' : Step (M.machineSRS w) E F := step_machineSRS_of_step_fullSRS M w hstep hE
        by_cases hq : Sym.state M.qacc ∈ F
        · exact Or.inl ⟨F, hreach.trans (Reaches.single hstep'), hq⟩
        · exact Or.inr ⟨hreach.trans (Reaches.single hstep'), hq⟩
  rcases key h with hacc | ⟨-, hnot⟩
  · exact hacc
  · exact absurd hC hnot

/-- The eating rules collapse any configuration containing the accept state to the single
symbol `q_accept`. -/
lemma reaches_qacc_of_mem {C : List Sym} (hC : ∀ a ∈ C, a ∈ M.alphabet w)
    (h : Sym.state M.qacc ∈ C) :
    Reaches (M.fullSRS w) C [Sym.state M.qacc] := by
  have eat_right : ∀ (post pre : List Sym), (∀ a ∈ post, a ∈ M.alphabet w) →
      Reaches (M.fullSRS w) (pre ++ Sym.state M.qacc :: post) (pre ++ [Sym.state M.qacc]) := by
    intro post
    induction post with
    | nil => intro pre _; exact Reaches.refl _ _
    | cons x post ih =>
      intro pre hpost
      have hx : x ∈ M.alphabet w := hpost x (by simp)
      have hrule : ([Sym.state M.qacc, x], [Sym.state M.qacc]) ∈ (M.fullSRS w).rules := by
        simp only [TM.fullSRS, List.mem_append]
        refine Or.inr ?_
        simp only [TM.eatRules, List.mem_flatMap]
        exact ⟨x, hx, by simp⟩
      have hstep : Step (M.fullSRS w) (pre ++ Sym.state M.qacc :: x :: post)
          (pre ++ Sym.state M.qacc :: post) := by
        have := StepRule.mk pre [Sym.state M.qacc, x] [Sym.state M.qacc] post hrule
        simpa using Step.rule this
      exact (Reaches.single hstep).trans (ih pre fun a ha => hpost a (by simp [ha]))
  have eat_left : ∀ pre : List Sym, (∀ a ∈ pre, a ∈ M.alphabet w) →
      Reaches (M.fullSRS w) (pre ++ [Sym.state M.qacc]) [Sym.state M.qacc] := by
    intro pre
    induction pre using List.reverseRecOn with
    | nil => intro _; exact Reaches.refl _ _
    | append_singleton pre x ih =>
      intro hpre
      have hx : x ∈ M.alphabet w := hpre x (by simp)
      have hrule : ([x, Sym.state M.qacc], [Sym.state M.qacc]) ∈ (M.fullSRS w).rules := by
        simp only [TM.fullSRS, List.mem_append]
        refine Or.inr ?_
        simp only [TM.eatRules, List.mem_flatMap]
        exact ⟨x, hx, by simp⟩
      have hstep : Step (M.fullSRS w) (pre ++ [x] ++ [Sym.state M.qacc])
          (pre ++ [Sym.state M.qacc]) := by
        have := StepRule.mk pre [x, Sym.state M.qacc] [Sym.state M.qacc] [] hrule
        simpa using Step.rule this
      exact (Reaches.single hstep).trans (ih fun a ha => hpre a (by simp [ha]))
  obtain ⟨pre, post, hsplit⟩ : ∃ pre post, C = pre ++ Sym.state M.qacc :: post := by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem h
    exact ⟨pre, post, hsplit⟩
  subst hsplit
  refine (eat_right post pre fun a ha => hC a (by simp [ha])).trans
    (eat_left pre fun a ha => hC a (by simp [ha]))

/-- **The machine accepts `w` if and only if the full rewriting system rewrites the
starting configuration to the single symbol `q_accept`.** -/
theorem reaches_qacc_iff_accepts :
    Reaches (M.fullSRS w) (M.startCfg w) [Sym.state M.qacc] ↔ M.Accepts w := by
  constructor
  · intro h
    exact accepts_of_reaches_fullSRS M w h (by simp)
  · rintro ⟨C, hreach, hC⟩
    have hstep : ∀ {A B : List Sym}, Step (M.machineSRS w) A B → Step (M.fullSRS w) A B := by
      intro A B hAB
      cases hAB with
      | rule hr =>
        cases hr with
        | mk l u v r hmem =>
          exact Step.rule (StepRule.mk l u v r (by
            simp only [TM.fullSRS, List.mem_append]
            exact Or.inl (by simpa [TM.machineSRS] using hmem)))
      | @ext x hx => exact Step.ext (by simpa [TM.fullSRS] using (by simpa [TM.machineSRS] using hx :
          x ∈ [Sym.tape 0]))
    have hmono : ∀ {A B : List Sym}, Reaches (M.machineSRS w) A B → Reaches (M.fullSRS w) A B := by
      intro A B hAB
      induction hAB with
      | refl => exact Reaches.refl _ _
      | tail _ hs ih => exact ih.trans (Reaches.single (hstep hs))
    have hreach' : Reaches (M.fullSRS w) (M.startCfg w) C := hmono hreach
    have hCalpha : ∀ a ∈ C, a ∈ M.alphabet w :=
      Reaches.mem_alphabet (machineSRS_wf M w) hreach (startCfg_mem_alphabet M w)
    exact hreach'.trans (reaches_qacc_of_mem M w hCalpha hC)

end EatRules

end Lax251941Proofs.PCP
