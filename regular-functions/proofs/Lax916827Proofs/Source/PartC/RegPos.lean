/-
A *positional* description of the run of a two-way transducer, used by the
effective equivalence bound of Theorem `thm:decidable-equivalence-regular`
(`RequestProject/PartC/RegEffBound.lean`).

A configuration `Cfg.conf u q v` of a two-way transducer on the input `w` always
has `u ++ v = w`, so it is determined by the *cut* `p = |u|` and the state `q`;
and the halting vertex is then the value `none` of `Option (ℕ × Q)`.  This file
replaces `Transducers.TwoWay.stepCfg` by the step function
`Transducers.RegPos.stepP` on such pairs and proves that the two agree
(`Transducers.RegPos.stepCfg_cfgP`), so that a run becomes a sequence of pairs
`(cut, state)` and everything about it becomes arithmetic on the cut.

That is what makes the two *locality* statements of
`RequestProject/PartC/RegBlock.lean` immediate: a step at a cut `p` reads only
the letters at the positions `p - 1` and `p`, so two inputs that agree there
have the same step.  The decomposition of a run at a cut of the input into the
maximal pieces that stay on one side of the cut, which is the combinatorial
heart of the bound, is then stated in `RequestProject/PartC/RegCross.lean`.
-/
import Lax916827Proofs.Source.PartC.TwoWayRun
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegPos

open TwoWay

variable {A B Q : Type}

/-! ## Cuts and steps -/

/-- The letter immediately to the left of the cut `p` of `w`. -/
def leftLet (w : List A) (p : ℕ) : Option A := if p = 0 then none else w[p - 1]?

/-- The configuration of `w` with the head at the cut `p` in the state `q`; the
value `none` is the halting vertex. -/
def cfgP (w : List A) : Option (ℕ × Q) → Cfg A Q
  | none => Cfg.halt
  | some (p, q) => Cfg.conf (w.take p) q (w.drop p)

/-- One step of a two-way transducer, described by the cut and the state: the
produced output together with the next cut and state, or `none` if the run gets
stuck (it tries to move off the input). -/
def stepP (M : TwoWay A B Q) (w : List A) (x : ℕ × Q) : Option (List B × Option (ℕ × Q)) :=
  match M.step (leftLet w x.1) x.2 w[x.1]? with
  | Sum.inl o => some (o, none)
  | Sum.inr (q', o, true) => if x.1 < w.length then some (o, some (x.1 + 1, q')) else none
  | Sum.inr (q', o, false) => if 0 < x.1 then some (o, some (x.1 - 1, q')) else none

@[simp] lemma cfgP_none (w : List A) : cfgP (Q := Q) w none = Cfg.halt := rfl

@[simp] lemma cfgP_some (w : List A) (p : ℕ) (q : Q) :
    cfgP w (some (p, q)) = Cfg.conf (w.take p) q (w.drop p) := rfl

lemma cfgP_injective {w : List A} {x y : Option (ℕ × Q)}
    (hx : ∀ z ∈ x, z.1 ≤ w.length) (hy : ∀ z ∈ y, z.1 ≤ w.length)
    (h : cfgP w x = cfgP w y) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some z => exact absurd h.symm (by simp [cfgP])
  | some z => cases y with
    | none => exact absurd h (by simp [cfgP])
    | some z' =>
        obtain ⟨p, q⟩ := z
        obtain ⟨p', q'⟩ := z'
        simp only [cfgP_some, Cfg.conf.injEq] at h
        obtain ⟨h1, h2, -⟩ := h
        have e1 : (w.take p).length = p := by
          simpa using hx (p, q) rfl
        have e2 : (w.take p').length = p' := by
          simpa using hy (p', q') rfl
        rw [h1] at e1
        rw [e1] at e2
        simp [e2, h2]

lemma getLast?_take {w : List A} {p : ℕ} (hp : p ≤ w.length) :
    (w.take p).getLast? = leftLet w p := by
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · simp [leftLet]
  · have hlen : (w.take p).length = p := by simpa using hp
    rw [List.getLast?_eq_getElem?, hlen, leftLet, if_neg (by omega),
      List.getElem?_take, if_pos (by omega)]

lemma head?_drop (w : List A) (p : ℕ) : (w.drop p).head? = w[p]? := by
  rw [List.head?_eq_getElem?, List.getElem?_drop]
  simp

lemma take_append_getElem {w : List A} {p : ℕ} (h : p < w.length) :
    w.take p ++ [w[p]] = w.take (p + 1) := by
  rw [List.take_add_one]
  simp [List.getElem?_eq_getElem h]

lemma dropLast_take {w : List A} {p : ℕ} (h : p ≤ w.length) :
    (w.take p).dropLast = w.take (p - 1) := by
  rw [List.dropLast_eq_take]
  have hlen : (w.take p).length = p := by simpa using h
  rw [hlen, List.take_take]
  congr 1
  omega

/-- The step function on cuts agrees with the step function on configurations. -/
lemma stepCfg_cfgP (M : TwoWay A B Q) (w : List A) {p : ℕ} (hp : p ≤ w.length) (q : Q) :
    M.stepCfg (cfgP w (some (p, q)))
      = (stepP M w (p, q)).map (fun z => (z.1, cfgP w z.2)) := by
  have hl : (w.take p).getLast? = leftLet w p := getLast?_take hp
  have hr : (w.drop p).head? = w[p]? := head?_drop w p
  have hstepeq : M.step (w.take p).getLast? q (w.drop p).head?
      = M.step (leftLet w p) q w[p]? := by rw [hl, hr]
  rw [cfgP_some]
  rcases hstep : M.step (leftLet w p) q w[p]? with o | ⟨q', o, d⟩
  · rw [M.stepCfg_halt_eq (by rw [hstepeq, hstep])]
    simp [stepP, hstep]
  · cases d with
    | true =>
        by_cases hlt : p < w.length
        · have hd : w.drop p = w[p] :: w.drop (p + 1) := List.drop_eq_getElem_cons hlt
          have hh : M.step (w.take p).getLast? q (w[p] :: w.drop (p + 1)).head?
              = Sum.inr (q', o, true) := by
            rw [hl, List.head?_cons, ← List.getElem?_eq_getElem hlt]
            exact hstep
          rw [hd, M.stepCfg_right_cons hh, take_append_getElem hlt]
          simp [stepP, hstep, if_pos hlt]
        · have hd : w.drop p = [] := by
            simp only [List.drop_eq_nil_iff]; omega
          have hh : M.step (w.take p).getLast? q ([] : List A).head?
              = Sum.inr (q', o, true) := by
            rw [hl, ← hd, hr]; exact hstep
          rw [hd, M.stepCfg_right_nil hh]
          simp [stepP, hstep, if_neg hlt]
    | false =>
        by_cases hpos : 0 < p
        · have hple : p - 1 < w.length := by omega
          have ha : leftLet w p = some (w[p - 1]'hple) := by
            rw [leftLet, if_neg (by omega), List.getElem?_eq_getElem hple]
          rw [M.stepCfg_left_some (a := w[p - 1]'hple) (by rw [hl, ha])
            (by rw [hstepeq, hstep]), dropLast_take hp]
          have hcons : (w[p - 1]'hple) :: w.drop p = w.drop (p - 1) := by
            rw [List.drop_eq_getElem_cons hple]
            congr 2
            omega
          rw [hcons]
          simp [stepP, hstep, if_pos hpos]
        · have hp0 : p = 0 := by omega
          subst hp0
          rw [M.stepCfg_left_none (by simp) (by rw [hstepeq, hstep])]
          simp [stepP, hstep]

/-! ## Runs described by cuts -/

/-- A run of `n` steps, described by cuts and states. -/
inductive RunP (M : TwoWay A B Q) (w : List A) :
    ℕ → Option (ℕ × Q) → List B → Option (ℕ × Q) → Prop
  | refl (x : Option (ℕ × Q)) : RunP M w 0 x [] x
  | step {n : ℕ} {x : ℕ × Q} {o o' : List B} {y z : Option (ℕ × Q)} :
      stepP M w x = some (o, y) → RunP M w n y o' z → RunP M w (n + 1) (some x) (o ++ o') z

/-- The cut of a reachable configuration is at most the length of the input. -/
lemma stepP_le {M : TwoWay A B Q} {w : List A} {x : ℕ × Q} {o : List B} {y : Option (ℕ × Q)}
    (hx : x.1 ≤ w.length) (h : stepP M w x = some (o, y)) : ∀ z ∈ y, z.1 ≤ w.length := by
  rw [stepP] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; simp
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      rintro z hz
      simp only [Option.mem_def, Option.some.injEq] at hz
      subst hz
      simp only
      omega
    · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      rintro z hz
      simp only [Option.mem_def, Option.some.injEq] at hz
      subst hz
      simp only
      omega
    · exact absurd h (by simp)

lemma RunP.le_length {M : TwoWay A B Q} {w : List A} {n : ℕ} {x : Option (ℕ × Q)} {o : List B}
    {y : Option (ℕ × Q)} (h : RunP M w n x o y) (hx : ∀ z ∈ x, z.1 ≤ w.length) :
    ∀ z ∈ y, z.1 ≤ w.length := by
  induction h with
  | refl x => exact hx
  | step hs _ ih => exact ih (stepP_le (hx _ rfl) hs)

/-- A positional run gives a run on configurations. -/
lemma reaches_of_runP {M : TwoWay A B Q} {w : List A} {n : ℕ} {x : Option (ℕ × Q)} {o : List B}
    {y : Option (ℕ × Q)} (h : RunP M w n x o y) (hx : ∀ z ∈ x, z.1 ≤ w.length) :
    M.Reaches (cfgP w x) o (cfgP w y) := by
  induction h with
  | refl x => exact TwoWay.Reaches.refl _
  | @step n x o o' y z hs _ ih =>
      have hx1 : x.1 ≤ w.length := hx _ rfl
      have hstep : M.stepCfg (cfgP w (some x)) = some (o, cfgP w y) := by
        rw [stepCfg_cfgP M w hx1 x.2]
        · simp [hs]
      exact TwoWay.Reaches.step hstep (ih (stepP_le hx1 hs))

/-- A run on configurations, started at a configuration described by a cut,
gives a positional run. -/
lemma runP_of_reaches {M : TwoWay A B Q} {w : List A} {x : Option (ℕ × Q)} {o : List B}
    {c : Cfg A Q} (h : M.Reaches (cfgP w x) o c) (hx : ∀ z ∈ x, z.1 ≤ w.length) :
    ∃ (n : ℕ) (y : Option (ℕ × Q)), RunP M w n x o y ∧ c = cfgP w y ∧
      ∀ z ∈ y, z.1 ≤ w.length := by
  generalize hc0 : cfgP w x = c0 at h
  induction h generalizing x with
  | refl c => exact ⟨0, x, RunP.refl x, hc0.symm, hx⟩
  | @step c c' c'' o o' hs _ ih =>
      subst hc0
      cases x with
      | none => rw [cfgP_none] at hs; simp [TwoWay.stepCfg] at hs
      | some x =>
          have hx1 : x.1 ≤ w.length := hx _ rfl
          rw [stepCfg_cfgP M w hx1 x.2] at hs
          rcases hsp : stepP M w x with _ | ⟨oo, y⟩
          · rw [hsp] at hs; simp at hs
          · rw [hsp] at hs
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, hc'⟩ := hs
            obtain ⟨n, z, hrun, hz, hzle⟩ := ih (stepP_le hx1 hsp) hc'
            exact ⟨n + 1, z, RunP.step hsp hrun, hz, hzle⟩

/-- The relation computed by a two-way transducer, in positional form. -/
lemma computes_iff_runP (M : TwoWay A B Q) (w : List A) (v : List B) :
    M.Computes w v ↔ ∃ n, RunP M w n (some (0, M.init)) v none := by
  constructor
  · intro h
    have hx : ∀ z ∈ (some (0, M.init) : Option (ℕ × Q)), z.1 ≤ w.length := by simp
    have h' : M.Reaches (cfgP w (some (0, M.init))) v Cfg.halt := by
      simpa [TwoWay.Computes] using h
    obtain ⟨n, y, hrun, hy, hyle⟩ := runP_of_reaches h' hx
    have : y = none := by
      cases y with
      | none => rfl
      | some z => exact absurd hy.symm (by simp [cfgP])
    exact ⟨n, this ▸ hrun⟩
  · rintro ⟨n, h⟩
    have hx : ∀ z ∈ (some (0, M.init) : Option (ℕ × Q)), z.1 ≤ w.length := by simp
    have := reaches_of_runP h hx
    simpa [TwoWay.Computes] using this

end RegPos

end Lax916827Proofs.Transducers
