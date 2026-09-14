/-
# Configurations of a tape machine as a deterministic step function

The tape machines of `RequestProject/PCP/TuringMachine.lean` are described by a string
rewriting system: a configuration is a string `u q v` and a step rewrites it locally.
For a machine whose transition table is *deterministic* — at most one entry for each
pair (state, scanned symbol) — this rewriting is completely described by a step
*function* on triples `(u, q, v)`, up to the blanks that may be appended at the right
end.  This file sets up that description; it turns the analysis of a machine into
ordinary reasoning about the iterates of a function.
-/
import Lax251941Proofs.Source.PCP.Reduction

namespace Lax251941Proofs.PCP
namespace Sim

/-- A configuration of a tape machine: the part of the tape to the left of the head
(stored in reverse order, so that its head is the cell immediately left of the machine's
head), the current state, and the part of the tape from the head onwards. -/
structure Cfg where
  /-- The tape to the left of the head, in reverse order. -/
  left : List ℕ
  /-- The current state. -/
  st : ℕ
  /-- The tape from the head onwards. -/
  right : List ℕ
deriving DecidableEq, Repr

namespace Cfg

/-- The configuration string of a configuration. -/
def toStr (c : Cfg) : List Sym :=
  c.left.reverse.map Sym.tape ++ Sym.state c.st :: c.right.map Sym.tape

/-- Append `k` blanks at the right end of a configuration. -/
def pad (c : Cfg) (k : ℕ) : Cfg := ⟨c.left, c.st, c.right ++ List.replicate k 0⟩

@[simp] lemma pad_zero (c : Cfg) : c.pad 0 = c := by
  cases c; simp [pad]

lemma pad_add (c : Cfg) (k l : ℕ) : (c.pad k).pad l = c.pad (k + l) := by
  cases c
  simp [pad]

lemma toStr_pad_succ (c : Cfg) (k : ℕ) :
    (c.pad (k + 1)).toStr = (c.pad k).toStr ++ [Sym.tape 0] := by
  cases c
  simp only [pad, toStr, List.replicate_succ', List.append_assoc, List.map_append,
    List.map_cons, List.map_nil, List.cons_append]

@[simp] lemma mem_toStr_state {c : Cfg} {q : ℕ} :
    Sym.state q ∈ c.toStr ↔ q = c.st := by
  constructor
  · intro h
    simp only [toStr, List.mem_append, List.mem_cons, List.mem_map] at h
    rcases h with ⟨x, _, hx⟩ | h | ⟨x, _, hx⟩
    · exact absurd hx (by simp)
    · exact (Sym.state.injEq _ _ ▸ h)
    · exact absurd hx (by simp)
  · rintro rfl
    simp [toStr]

lemma not_state_of_mem_map_tape {l : List ℕ} {x : Sym} (h : x ∈ l.map Sym.tape) :
    ∀ q, x ≠ Sym.state q := by
  simp only [List.mem_map] at h
  obtain ⟨y, _, rfl⟩ := h
  intro q
  simp

end Cfg

/-- Uniqueness of the position of the state symbol in a configuration string. -/
lemma state_split_unique {A B A' B' : List Sym} {q q' : ℕ}
    (hA : ∀ x ∈ A, ∀ n, x ≠ Sym.state n) (hB : ∀ x ∈ B, ∀ n, x ≠ Sym.state n)
    (h : A ++ Sym.state q :: B = A' ++ Sym.state q' :: B') :
    A = A' ∧ q = q' ∧ B = B' := by
  induction A generalizing A' with
  | nil =>
    cases A' with
    | nil => simpa using h
    | cons a A'' =>
      exfalso
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have hmem : Sym.state q' ∈ B := by rw [h2]; simp
      exact hB _ hmem q' rfl
  | cons a A₁ ih =>
    cases A' with
    | nil =>
      exfalso
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact hA a (by simp) q' h.1
    | cons a' A₁' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨h3, h4, h5⟩ := ih (fun x hx => hA x (by simp [hx])) h2
      exact ⟨by rw [h3], h4, h5⟩

/-- A machine is deterministic when its transition table has at most one entry for each
pair of a state and a scanned symbol. -/
def Det (M : TM) : Prop :=
  ∀ x ∈ M.trans, ∀ y ∈ M.trans, x.1 = y.1 → x.2.1 = y.2.1 → x = y

/-- The (unique, for a deterministic machine) transition for a state and a symbol. -/
def entry (M : TM) (q a : ℕ) : Option (ℕ × ℕ × Bool) :=
  (M.trans.find? fun x => decide (x.1 = q ∧ x.2.1 = a)).map fun x => x.2.2

variable {M : TM}

lemma entry_eq_some_iff (hdet : Det M) {q a r b : ℕ} {d : Bool} :
    entry M q a = some (r, b, d) ↔ (q, a, r, b, d) ∈ M.trans := by
  constructor
  · intro h
    simp only [entry, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, hx2⟩ := h
    have hmem := List.mem_of_find?_eq_some hx
    have hp := List.find?_some hx
    simp only [decide_eq_true_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    obtain ⟨x1, x2, x3⟩ := x
    simp only at h1 h2 hx2
    subst h1; subst h2; subst hx2
    exact hmem
  · intro h
    have hne : (M.trans.find? fun x => decide (x.1 = q ∧ x.2.1 = a)) ≠ none := by
      intro hnone
      rw [List.find?_eq_none] at hnone
      exact absurd (hnone _ h) (by simp)
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
    have hmem := List.mem_of_find?_eq_some hx
    have hp := List.find?_some hx
    simp only [decide_eq_true_eq] at hp
    have hxe : x = (q, a, r, b, d) := hdet x hmem _ h hp.1 hp.2
    rw [entry, hx]
    simp [hxe]

lemma entry_eq_none_iff (hdet : Det M) {q a : ℕ} :
    entry M q a = none ↔ ∀ r b d, (q, a, r, b, d) ∉ M.trans := by
  constructor
  · intro h r b d hmem
    rw [← entry_eq_some_iff hdet] at hmem
    rw [h] at hmem
    exact absurd hmem (by simp)
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨r, b, d⟩ := x
    exact h r b d ((entry_eq_some_iff hdet).mp hx)

/-- The deterministic step function on configurations: the machine reads the symbol under
the head (a blank if the written part of the tape has been exhausted), writes and moves.
A configuration with no applicable transition, or one that would move left at the left end
of the tape, is a fixed point. -/
def dstep (M : TM) (c : Cfg) : Cfg :=
  match entry M c.st c.right.headI with
  | none => c
  | some (r, b, true) => ⟨b :: c.left, r, c.right.tail⟩
  | some (r, b, false) =>
      match c.left with
      | [] => c
      | x :: l => ⟨l, r, x :: b :: c.right.tail⟩

/-! ## Inversion of a rewriting step -/

lemma stepRule_inv {α : Type*} {rules : List (List α × List α)} {a b : List α}
    (h : StepRule rules a b) :
    ∃ l u v r, (u, v) ∈ rules ∧ a = l ++ u ++ r ∧ b = l ++ v ++ r := by
  cases h with
  | mk l u v r hm => exact ⟨l, u, v, r, hm, rfl, rfl⟩

lemma step_inv {α : Type*} {S : SRS α} {a b : List α} (h : Step S a b) :
    (∃ l u v r, (u, v) ∈ S.rules ∧ a = l ++ u ++ r ∧ b = l ++ v ++ r) ∨
      (∃ x ∈ S.ext, b = a ++ [x]) := by
  cases h with
  | rule hr => exact Or.inl (stepRule_inv hr)
  | ext hx => exact Or.inr ⟨_, hx, rfl⟩

/-! ## The rewriting rules of a machine -/

variable {M : TM} {w : List ℕ}

lemma mem_rightRules_iff {u v : List Sym} :
    (u, v) ∈ M.rightRules ↔ ∃ q a r b, (q, a, r, b, true) ∈ M.trans ∧
      u = [Sym.state q, Sym.tape a] ∧ v = [Sym.tape b, Sym.state r] := by
  simp only [TM.rightRules, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hx2⟩
    obtain ⟨q, a, r, b, dir⟩ := x
    cases dir with
    | false => simp at hx2
    | true =>
      simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hx2
      exact ⟨q, a, r, b, hx, hx2.1.symm, hx2.2.symm⟩
  · rintro ⟨q, a, r, b, hmem, rfl, rfl⟩
    exact ⟨(q, a, r, b, true), hmem, by simp⟩

lemma mem_leftRules_iff {u v : List Sym} :
    (u, v) ∈ M.leftRules w ↔ ∃ c q a r b, c ∈ M.tapeSyms w ∧ (q, a, r, b, false) ∈ M.trans ∧
      u = [Sym.tape c, Sym.state q, Sym.tape a] ∧
      v = [Sym.state r, Sym.tape c, Sym.tape b] := by
  simp only [TM.leftRules, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, x, hx, hx2⟩
    obtain ⟨q, a, r, b, dir⟩ := x
    cases dir with
    | true => simp at hx2
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at hx2
      exact ⟨c, q, a, r, b, hc, hx, hx2.1.symm, hx2.2.symm⟩
  · rintro ⟨c, q, a, r, b, hc, hmem, rfl, rfl⟩
    exact ⟨c, hc, (q, a, r, b, false), hmem, by simp⟩

lemma mem_machineSRS_rules_iff {u v : List Sym} :
    (u, v) ∈ (M.machineSRS w).rules ↔ (u, v) ∈ M.rightRules ∨ (u, v) ∈ M.leftRules w := by
  simp [TM.machineSRS, TM.transRules]

/-! ## The step characterization -/

/-- All symbols of a configuration belong to the tape alphabet. -/
def CfgOK (M : TM) (w : List ℕ) (c : Cfg) : Prop :=
  (∀ x ∈ c.left, x ∈ M.tapeSyms w) ∧ (∀ x ∈ c.right, x ∈ M.tapeSyms w)

lemma toStr_left_no_state (c : Cfg) :
    ∀ x ∈ c.left.reverse.map Sym.tape, ∀ n, x ≠ Sym.state n := by
  intro x hx n
  exact Cfg.not_state_of_mem_map_tape hx n

lemma toStr_right_no_state (c : Cfg) :
    ∀ x ∈ c.right.map Sym.tape, ∀ n, x ≠ Sym.state n := by
  intro x hx n
  exact Cfg.not_state_of_mem_map_tape hx n

/-- A single rewriting step from a configuration string either appends a blank at the
right end or performs the (unique) transition of the machine. -/
lemma step_char (hdet : Det M) {c : Cfg} {D : List Sym}
    (h : Step (M.machineSRS w) c.toStr D) :
    D = (c.pad 1).toStr ∨ D = (dstep M c).toStr := by
  rcases step_inv h with ⟨l, u, v, r, hmem, heq, hD⟩ | ⟨x, hx, hD⟩
  · right
    rcases mem_machineSRS_rules_iff.mp hmem with hr | hr
    · -- a move to the right
      obtain ⟨q, a, r', b, htrans, rfl, rfl⟩ := mem_rightRules_iff.mp hr
      have heq' : c.left.reverse.map Sym.tape ++ Sym.state c.st :: c.right.map Sym.tape
          = l ++ Sym.state q :: (Sym.tape a :: r) := by
        have h2 := heq
        rw [Cfg.toStr] at h2
        simpa using h2
      obtain ⟨hl, hq, hrgt⟩ :=
        state_split_unique (toStr_left_no_state c) (toStr_right_no_state c) heq'
      obtain ⟨a₀, rest, hcr, ha₀, hrest⟩ := List.map_eq_cons_iff.mp hrgt
      have ha : a₀ = a := by simpa using ha₀
      subst ha
      have hentry : entry M c.st a₀ = some (r', b, true) := by
        rw [entry_eq_some_iff hdet]
        rw [hq]; exact htrans
      have hd : dstep M c = ⟨b :: c.left, r', rest⟩ := by
        rw [dstep]
        simp only [hcr, List.headI_cons, List.tail_cons, hentry]
      rw [hD, hd, ← hl, ← hrest]
      simp [Cfg.toStr]
    · -- a move to the left
      obtain ⟨cc, q, a, r', b, hcc, htrans, rfl, rfl⟩ := mem_leftRules_iff.mp hr
      have heq' : c.left.reverse.map Sym.tape ++ Sym.state c.st :: c.right.map Sym.tape
          = (l ++ [Sym.tape cc]) ++ Sym.state q :: (Sym.tape a :: r) := by
        have h2 := heq
        rw [Cfg.toStr] at h2
        simpa using h2
      obtain ⟨hl, hq, hrgt⟩ :=
        state_split_unique (toStr_left_no_state c) (toStr_right_no_state c) heq'
      obtain ⟨a₀, rest, hcr, ha₀, hrest⟩ := List.map_eq_cons_iff.mp hrgt
      have ha : a₀ = a := by simpa using ha₀
      subst ha
      obtain ⟨l₁, l₂, hrev, hl₁, hl₂⟩ := List.map_eq_append_iff.mp hl
      obtain ⟨cc₀, rest₂, hl₂', hcc₀, -⟩ := List.map_eq_cons_iff.mp hl₂
      have hcc' : cc₀ = cc := by simpa using hcc₀
      subst hcc'
      have hl₂nil : rest₂ = [] := by
        have : rest₂.map Sym.tape = [] := by
          have := hl₂
          rw [hl₂'] at this
          simpa using this
        simpa using this
      subst hl₂nil
      have hleft : c.left = cc₀ :: l₁.reverse := by
        have : c.left.reverse = l₁ ++ [cc₀] := by rw [hrev, hl₂']
        have := congrArg List.reverse this
        simpa using this
      have hentry : entry M c.st a₀ = some (r', b, false) := by
        rw [entry_eq_some_iff hdet]
        rw [hq]; exact htrans
      have hd : dstep M c = ⟨l₁.reverse, r', cc₀ :: b :: rest⟩ := by
        rw [dstep]
        simp only [hcr, List.headI_cons, List.tail_cons, hentry, hleft]
      rw [hD, hd, ← hl₁, ← hrest]
      simp [Cfg.toStr]
  · left
    have hx0 : x = Sym.tape 0 := by simpa [TM.machineSRS] using hx
    subst hx0
    rw [hD, show (1 : ℕ) = 0 + 1 from rfl, Cfg.toStr_pad_succ, Cfg.pad_zero]

/-! ## Computing the step function -/

lemma dstep_none {c : Cfg} (hE : entry M c.st c.right.headI = none) : dstep M c = c := by
  rw [dstep, hE]

lemma dstep_right {c : Cfg} {r b : ℕ} (hE : entry M c.st c.right.headI = some (r, b, true)) :
    dstep M c = ⟨b :: c.left, r, c.right.tail⟩ := by
  rw [dstep, hE]

lemma dstep_left_nil {c : Cfg} {r b : ℕ} (hE : entry M c.st c.right.headI = some (r, b, false))
    (hL : c.left = []) : dstep M c = c := by
  rw [dstep, hE, hL]

lemma dstep_left {c : Cfg} {r b y : ℕ} {l : List ℕ}
    (hE : entry M c.st c.right.headI = some (r, b, false)) (hL : c.left = y :: l) :
    dstep M c = ⟨l, r, y :: b :: c.right.tail⟩ := by
  rw [dstep, hE, hL]

lemma dstep_pad (M : TM) (c : Cfg) (k : ℕ) : ∃ k', dstep M (c.pad k) = (dstep M c).pad k' := by
  have hst : (c.pad k).st = c.st := rfl
  have hleft : (c.pad k).left = c.left := rfl
  cases hR : c.right with
  | cons x rest =>
    have hpr : (c.pad k).right = x :: (rest ++ List.replicate k 0) := by simp [Cfg.pad, hR]
    have hh : (c.pad k).right.headI = c.right.headI := by rw [hpr, hR]; rfl
    refine ⟨k, ?_⟩
    rcases hE : entry M c.st c.right.headI with _ | ⟨r, b, d⟩
    · rw [dstep_none (by rw [hst, hh]; exact hE), dstep_none hE]
    · have hE' : entry M (c.pad k).st (c.pad k).right.headI = some (r, b, d) := by
        rw [hst, hh]; exact hE
      cases d with
      | true =>
        rw [dstep_right hE', dstep_right hE, hpr, hR, hleft]
        simp [Cfg.pad]
      | false =>
        cases hL : c.left with
        | nil => rw [dstep_left_nil hE' (by rw [hleft, hL]), dstep_left_nil hE hL]
        | cons y l =>
          rw [dstep_left hE' (by rw [hleft, hL]), dstep_left hE hL, hpr, hR]
          simp [Cfg.pad]
  | nil =>
    cases k with
    | zero => exact ⟨0, by simp⟩
    | succ k =>
      have hpr : (c.pad (k + 1)).right = 0 :: List.replicate k 0 := by
        simp [Cfg.pad, hR, List.replicate_succ]
      have hh : (c.pad (k + 1)).right.headI = c.right.headI := by rw [hpr, hR]; rfl
      rcases hE : entry M c.st c.right.headI with _ | ⟨r, b, d⟩
      · exact ⟨k + 1, by rw [dstep_none (by rw [hst, hh]; exact hE), dstep_none hE]⟩
      · have hE' : entry M (c.pad (k + 1)).st (c.pad (k + 1)).right.headI = some (r, b, d) := by
          rw [hst, hh]; exact hE
        cases d with
        | true =>
          refine ⟨k, ?_⟩
          rw [dstep_right hE', dstep_right hE, hpr, hR, hleft]
          simp [Cfg.pad]
        | false =>
          cases hL : c.left with
          | nil =>
            exact ⟨k + 1, by rw [dstep_left_nil hE' (by rw [hleft, hL]), dstep_left_nil hE hL]⟩
          | cons y l =>
            refine ⟨k, ?_⟩
            rw [dstep_left hE' (by rw [hleft, hL]), dstep_left hE hL, hpr, hR]
            simp [Cfg.pad]

/-! ## Reachable strings -/

/-- Every string reachable from a configuration is a later configuration of the
deterministic run of the machine, with some blanks appended at the right end. -/
lemma reaches_char (hdet : Det M) {c : Cfg} {D : List Sym}
    (h : Reaches (M.machineSRS w) c.toStr D) :
    ∃ t k, D = (((dstep M)^[t] c).pad k).toStr := by
  induction h with
  | refl => exact ⟨0, 0, by simp⟩
  | tail _ hstep ih =>
    obtain ⟨t, k, rfl⟩ := ih
    rcases step_char hdet hstep with hD | hD
    · exact ⟨t, k + 1, by rw [hD, Cfg.pad_add]⟩
    · obtain ⟨k', hk'⟩ := dstep_pad M ((dstep M)^[t] c) k
      exact ⟨t + 1, k', by rw [hD, hk', Function.iterate_succ_apply']⟩

/-! ## Configurations over the tape alphabet -/

lemma cfgOK_pad {c : Cfg} (h : CfgOK M w c) (k : ℕ) : CfgOK M w (c.pad k) := by
  refine ⟨h.1, ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h.2 x hx
  · have : x = 0 := List.eq_of_mem_replicate hx
    subst this
    exact M.blank_mem_tapeSyms w

lemma cfgOK_dstep (hdet : Det M) {c : Cfg} (h : CfgOK M w c) : CfgOK M w (dstep M c) := by
  rcases hE : entry M c.st c.right.headI with _ | ⟨r, b, d⟩
  · rw [dstep_none hE]; exact h
  · have htrans : (c.st, c.right.headI, r, b, d) ∈ M.trans := (entry_eq_some_iff hdet).mp hE
    have hb : b ∈ M.tapeSyms w := M.write_mem_tapeSyms w htrans
    cases d with
    | true =>
      rw [dstep_right hE]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact h.1 x hx
      · intro x hx
        exact h.2 x (List.mem_of_mem_tail hx)
    | false =>
      cases hL : c.left with
      | nil => rw [dstep_left_nil hE hL]; exact h
      | cons y l =>
        rw [dstep_left hE hL]
        refine ⟨?_, ?_⟩
        · intro x hx
          exact h.1 x (by rw [hL]; exact List.mem_cons_of_mem _ hx)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h.1 x (by rw [hL]; exact List.mem_cons_self)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hb
            · exact h.2 x (List.mem_of_mem_tail hx)

lemma cfgOK_iterate (hdet : Det M) {c : Cfg} (h : CfgOK M w c) (t : ℕ) :
    CfgOK M w ((dstep M)^[t] c) := by
  induction t with
  | zero => simpa using h
  | succ t ih => rw [Function.iterate_succ_apply']; exact cfgOK_dstep hdet ih

/-! ## The deterministic run is realized by the rewriting system -/

lemma reaches_pad_one (c : Cfg) : Reaches (M.machineSRS w) c.toStr (c.pad 1).toStr := by
  have h : Step (M.machineSRS w) c.toStr (c.toStr ++ [Sym.tape 0]) :=
    Step.ext (by simp [TM.machineSRS])
  have he : (c.pad 1).toStr = c.toStr ++ [Sym.tape 0] := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Cfg.toStr_pad_succ, Cfg.pad_zero]
  rw [he]
  exact Reaches.single h

lemma reaches_dstep_cons (hdet : Det M) {c : Cfg} (hOK : CfgOK M w c) {a : ℕ} {rest : List ℕ}
    (hR : c.right = a :: rest) :
    Reaches (M.machineSRS w) c.toStr (dstep M c).toStr := by
  have hhead : c.right.headI = a := by rw [hR]; rfl
  rcases hE : entry M c.st c.right.headI with _ | ⟨r, b, d⟩
  · rw [dstep_none hE]
    exact Reaches.refl _ _
  · have htrans : (c.st, a, r, b, d) ∈ M.trans := by
      have := (entry_eq_some_iff hdet).mp hE
      rwa [hhead] at this
    cases d with
    | true =>
      have hrule : ([Sym.state c.st, Sym.tape a], [Sym.tape b, Sym.state r])
          ∈ (M.machineSRS w).rules :=
        mem_machineSRS_rules_iff.mpr (Or.inl (mem_rightRules_iff.mpr
          ⟨c.st, a, r, b, htrans, rfl, rfl⟩))
      have h1 : c.toStr = c.left.reverse.map Sym.tape ++ [Sym.state c.st, Sym.tape a]
          ++ rest.map Sym.tape := by
        simp [Cfg.toStr, hR]
      have h2 : (dstep M c).toStr = c.left.reverse.map Sym.tape ++ [Sym.tape b, Sym.state r]
          ++ rest.map Sym.tape := by
        rw [dstep_right hE]
        simp [Cfg.toStr, hR]
      rw [h1, h2]
      exact Reaches.single (Step.rule (StepRule.mk _ _ _ _ hrule))
    | false =>
      cases hL : c.left with
      | nil =>
        rw [dstep_left_nil hE hL]
        exact Reaches.refl _ _
      | cons y l =>
        have hy : y ∈ M.tapeSyms w := hOK.1 y (by rw [hL]; exact List.mem_cons_self)
        have hrule : ([Sym.tape y, Sym.state c.st, Sym.tape a],
            [Sym.state r, Sym.tape y, Sym.tape b]) ∈ (M.machineSRS w).rules :=
          mem_machineSRS_rules_iff.mpr (Or.inr (mem_leftRules_iff.mpr
            ⟨y, c.st, a, r, b, hy, htrans, rfl, rfl⟩))
        have h1 : c.toStr = l.reverse.map Sym.tape ++ [Sym.tape y, Sym.state c.st, Sym.tape a]
            ++ rest.map Sym.tape := by
          simp [Cfg.toStr, hR, hL]
        have h2 : (dstep M c).toStr = l.reverse.map Sym.tape
            ++ [Sym.state r, Sym.tape y, Sym.tape b] ++ rest.map Sym.tape := by
          rw [dstep_left hE hL]
          simp [Cfg.toStr, hR]
        rw [h1, h2]
        exact Reaches.single (Step.rule (StepRule.mk _ _ _ _ hrule))

lemma reaches_dstep (hdet : Det M) {c : Cfg} (hOK : CfgOK M w c) :
    Reaches (M.machineSRS w) c.toStr (dstep M c).toStr := by
  cases hR : c.right with
  | cons a rest => exact reaches_dstep_cons hdet hOK hR
  | nil =>
    have hpadR : (c.pad 1).right = 0 :: [] := by simp [Cfg.pad, hR]
    have hhead : c.right.headI = 0 := by rw [hR]; rfl
    have hhead' : (c.pad 1).right.headI = 0 := by rw [hpadR]; rfl
    have hst : (c.pad 1).st = c.st := rfl
    rcases hE : entry M c.st c.right.headI with _ | ⟨r, b, d⟩
    · rw [dstep_none hE]
      exact Reaches.refl _ _
    · have hE' : entry M (c.pad 1).st (c.pad 1).right.headI = some (r, b, d) := by
        rw [hst, hhead', ← hhead]; exact hE
      have hstep := reaches_dstep_cons hdet (cfgOK_pad hOK 1) hpadR
      cases d with
      | true =>
        have heq : dstep M (c.pad 1) = dstep M c := by
          rw [dstep_right hE', dstep_right hE, hpadR, hR]
          rfl
        rw [← heq]
        exact (reaches_pad_one c).trans hstep
      | false =>
        cases hL : c.left with
        | nil =>
          rw [dstep_left_nil hE hL]
          exact Reaches.refl _ _
        | cons y l =>
          have hL' : (c.pad 1).left = y :: l := by rw [← hL]; rfl
          have heq : dstep M (c.pad 1) = dstep M c := by
            rw [dstep_left hE' hL', dstep_left hE hL, hpadR, hR]
            rfl
          rw [← heq]
          exact (reaches_pad_one c).trans hstep

lemma reaches_iterate (hdet : Det M) {c : Cfg} (hOK : CfgOK M w c) (t : ℕ) :
    Reaches (M.machineSRS w) c.toStr (((dstep M)^[t] c)).toStr := by
  induction t with
  | zero => simpa using Reaches.refl _ _
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (reaches_dstep hdet (cfgOK_iterate hdet hOK t))

/-! ## Acceptance in terms of the step function -/

/-- The initial configuration of a machine on an input word. -/
def initCfg (M : TM) (w : List ℕ) : Cfg := ⟨[], M.q0, w⟩

lemma toStr_initCfg (M : TM) (w : List ℕ) : (initCfg M w).toStr = M.startCfg w := by
  simp [Cfg.toStr, initCfg, TM.startCfg]

lemma cfgOK_initCfg (M : TM) (w : List ℕ) : CfgOK M w (initCfg M w) :=
  ⟨by simp [initCfg], fun x hx => M.input_mem_tapeSyms w hx⟩

/-- **A deterministic machine accepts an input exactly when its deterministic run reaches
the accept state.** -/
theorem accepts_iff_dstep (hdet : Det M) (w : List ℕ) :
    M.Accepts w ↔ ∃ t, ((dstep M)^[t] (initCfg M w)).st = M.qacc := by
  constructor
  · rintro ⟨C, hreach, hC⟩
    rw [← toStr_initCfg] at hreach
    obtain ⟨t, k, rfl⟩ := reaches_char hdet hreach
    refine ⟨t, ?_⟩
    rw [Cfg.mem_toStr_state] at hC
    exact hC.symm
  · rintro ⟨t, ht⟩
    refine ⟨(((dstep M)^[t] (initCfg M w))).toStr, ?_, ?_⟩
    · rw [← toStr_initCfg]
      exact reaches_iterate hdet (cfgOK_initCfg M w) t
    · rw [Cfg.mem_toStr_state]
      exact ht.symm

end Sim
end Lax251941Proofs.PCP
