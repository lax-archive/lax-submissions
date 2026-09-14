/- Two-way transducers (Definition `def:two-way-transducer` of *Transducers*, M. Bojańczyk)
and the proof that they compute continuous functions (Theorem `thm:continuity-2dfas`).

The definitions of two-way transducers are in this file, so that the
construction below can be developed before the statements of Part C.

Running a deterministic automaton `D` on the output of a two-way transducer `M`
turns `M` into a deterministic two-way *automaton*: its states are pairs
consisting of a state of `M` and a state of `D`, and the second component is
updated with the output produced by each transition.  The inverse image of the
language of `D` is the language of that two-way automaton, which is regular by
Shepherdson's Theorem (`TwoDFA.accepts_isRegular`).
-/
import Lax916827Proofs.Source.PartC.TwoDFA
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- **Definition `def:two-way-transducer`.**  A two-way transducer: based on the letters
adjacent to the head and the current state, it either produces an output string and halts
(`Sum.inl`), or produces an output string, changes state, and moves the head left (`false`) or right
(`true`). -/
structure TwoWay (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Option A → Q → Option A → List B ⊕ (Q × List B × Bool)

/-- A configuration of a two-way transducer: the input to the left of the head,
the state, and the input to the right of the head; plus a halting vertex. -/
inductive Cfg (A Q : Type) : Type
  | conf : List A → Q → List A → Cfg A Q
  | halt : Cfg A Q

namespace TwoWay

variable {A B Q : Type}

/-- One step of the computation: the produced output and the next
configuration, if any. -/
def stepCfg (M : TwoWay A B Q) : Cfg A Q → Option (List B × Cfg A Q)
  | Cfg.halt => none
  | Cfg.conf u q v =>
      match M.step u.getLast? q v.head? with
      | Sum.inl o => some (o, Cfg.halt)
      | Sum.inr (q', o, true) =>
          match v with
          | [] => none
          | a :: v' => some (o, Cfg.conf (u ++ [a]) q' v')
      | Sum.inr (q', o, false) =>
          match u.getLast? with
          | none => none
          | some a => some (o, Cfg.conf u.dropLast q' (a :: v))

/-- Reachability in the configuration graph, recording the produced output. -/
inductive Reaches (M : TwoWay A B Q) : Cfg A Q → List B → Cfg A Q → Prop
  | refl (c : Cfg A Q) : Reaches M c [] c
  | step {c c' c'' : Cfg A Q} {o o' : List B} :
      M.stepCfg c = some (o, c') → Reaches M c' o' c'' → Reaches M c (o ++ o') c''

/-- The transducer produces the output `v` on the input `w`: the run started in
the initial configuration reaches the halting vertex, producing `v`. -/
def Computes (M : TwoWay A B Q) (w : List A) (v : List B) : Prop :=
  M.Reaches (Cfg.conf [] M.init w) v Cfg.halt

end TwoWay

/-- A (total) function computed by a two-way transducer. -/
def IsTwoWay {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : TwoWay A B Q), ∀ w, M.Computes w (f w)
/-! ## Running a deterministic automaton on the output -/

namespace TwoWay

variable {A B Q : Type} (M : TwoWay A B Q) {σ : Type} (D : DFA B σ)

open scoped Classical in
/-- The two-way automaton that runs the deterministic automaton `D` on the
output of the two-way transducer `M`. -/
noncomputable def outAut : TwoDFA A (Q × σ) where
  init := (M.init, D.start)
  step := fun l qd r =>
    match M.step l qd.1 r with
    | Sum.inl o => Sum.inl (decide (D.evalFrom qd.2 o ∈ D.accept))
    | Sum.inr (q', o, dir) => Sum.inr ((q', D.evalFrom qd.2 o), dir)

open scoped Classical in
/-- The configuration of `outAut D` corresponding to a configuration of `M` and
a state of `D`. -/
noncomputable def cfgPos : Cfg A Q → σ → TwoCfg (Q × σ)
  | Cfg.conf u q _, d => Sum.inl (u.length, (q, d))
  | Cfg.halt, d => Sum.inr (decide (d ∈ D.accept))

open scoped Classical

/-! ### Equations for one step of a two-way transducer -/

lemma stepCfg_halt_eq {u v : List A} {q : Q} {o : List B}
    (h : M.step u.getLast? q v.head? = Sum.inl o) :
    M.stepCfg (Cfg.conf u q v) = some (o, Cfg.halt) := by
  simp only [stepCfg, h]

lemma stepCfg_right_nil {u : List A} {q q' : Q} {o : List B}
    (h : M.step u.getLast? q ([] : List A).head? = Sum.inr (q', o, true)) :
    M.stepCfg (Cfg.conf u q []) = none := by
  simp only [stepCfg, h]

lemma stepCfg_right_cons {u v : List A} {a : A} {q q' : Q} {o : List B}
    (h : M.step u.getLast? q (a :: v).head? = Sum.inr (q', o, true)) :
    M.stepCfg (Cfg.conf u q (a :: v)) = some (o, Cfg.conf (u ++ [a]) q' v) := by
  simp only [stepCfg, h]

lemma stepCfg_left_none {u v : List A} {q q' : Q} {o : List B} (hu : u.getLast? = none)
    (h : M.step u.getLast? q v.head? = Sum.inr (q', o, false)) :
    M.stepCfg (Cfg.conf u q v) = none := by
  rw [hu] at h
  simp only [stepCfg, hu, h]

lemma stepCfg_left_some {u v : List A} {a : A} {q q' : Q} {o : List B} (hu : u.getLast? = some a)
    (h : M.step u.getLast? q v.head? = Sum.inr (q', o, false)) :
    M.stepCfg (Cfg.conf u q v) = some (o, Cfg.conf u.dropLast q' (a :: v)) := by
  rw [hu] at h
  simp only [stepCfg, hu, h]

lemma exists_conf_of_stepCfg {c c' : Cfg A Q} {o : List B} (h : M.stepCfg c = some (o, c')) :
    ∃ u q v, c = Cfg.conf u q v := by
  cases c with
  | halt => simp [stepCfg] at h
  | conf u q v => exact ⟨u, q, v, rfl⟩

/-! ### The correspondence between the runs -/

/-- One step of `M` is one step of `outAut D`. -/
lemma next_cfgPos {w : List A} {u v : List A} {q : Q} {o : List B} {c' : Cfg A Q} (d : σ)
    (huv : u ++ v = w) (hstep : M.stepCfg (Cfg.conf u q v) = some (o, c')) :
    (M.outAut D).next w (cfgPos D (Cfg.conf u q v) d) = cfgPos D c' (D.evalFrom d o) := by
  have hleft : (if u.length = 0 then none else w[u.length - 1]?) = u.getLast? := by
    by_cases hu : u = []
    · simp [hu]
    · have hpos : 0 < u.length := List.length_pos_iff.mpr hu
      rw [if_neg (by omega), ← huv, List.getElem?_append_left (by omega),
        List.getLast?_eq_getElem?]
  have hright : w[u.length]? = v.head? := by
    rw [← huv, List.getElem?_append_right (le_refl _), Nat.sub_self, ← List.head?_eq_getElem?]
  have hlen : w.length = u.length + v.length := by rw [← huv]; simp
  rcases hM : M.step u.getLast? q v.head? with o' | ⟨q', o', dir⟩
  · rw [stepCfg_halt_eq M hM] at hstep
    have hpair := Option.some_injective _ hstep
    have h1 : o' = o := congrArg Prod.fst hpair
    have h2 : Cfg.halt = c' := congrArg Prod.snd hpair
    subst h1; subst h2
    simp only [cfgPos, TwoDFA.next, hleft, hright, outAut, hM]
  · cases dir with
    | true =>
        cases v with
        | nil =>
            rw [stepCfg_right_nil M hM] at hstep
            exact absurd hstep (by simp)
        | cons a v' =>
            rw [stepCfg_right_cons M hM] at hstep
            have hpair := Option.some_injective _ hstep
            have h1 : o' = o := congrArg Prod.fst hpair
            have h2 : Cfg.conf (u ++ [a]) q' v' = c' := congrArg Prod.snd hpair
            subst h1; subst h2
            have hlt : u.length < w.length := by simp at hlen ⊢; omega
            simp only [cfgPos, TwoDFA.next, hleft, hright, outAut, hM, if_pos hlt]
            simp
    | false =>
        rcases hu : u.getLast? with _ | a
        · rw [stepCfg_left_none M hu hM] at hstep
          exact absurd hstep (by simp)
        · rw [stepCfg_left_some M hu hM] at hstep
          have hpair := Option.some_injective _ hstep
          have h1 : o' = o := congrArg Prod.fst hpair
          have h2 : Cfg.conf u.dropLast q' (a :: v) = c' := congrArg Prod.snd hpair
          subst h1; subst h2
          have hupos : 0 < u.length := by
            rcases u with _ | ⟨b, u'⟩
            · simp at hu
            · simp
          simp only [cfgPos, TwoDFA.next, hleft, hright, outAut, hM, if_pos hupos]
          simp

/-- The two parts of a configuration always concatenate to the input. -/
lemma stepCfg_append {w u v : List A} {q : Q} {o : List B} {c' : Cfg A Q}
    (huv : u ++ v = w) (hstep : M.stepCfg (Cfg.conf u q v) = some (o, c'))
    {u' : List A} {q' : Q} {v' : List A} (hc' : c' = Cfg.conf u' q' v') : u' ++ v' = w := by
  subst hc'
  rcases hM : M.step u.getLast? q v.head? with o'' | ⟨q'', o'', dir⟩
  · rw [stepCfg_halt_eq M hM] at hstep
    exact absurd (congrArg Prod.snd (Option.some_injective _ hstep)) (by simp)
  · cases dir with
    | true =>
        cases v with
        | nil =>
            rw [stepCfg_right_nil M hM] at hstep
            exact absurd hstep (by simp)
        | cons a v₀ =>
            rw [stepCfg_right_cons M hM] at hstep
            have h2 : Cfg.conf (u ++ [a]) q'' v₀ = Cfg.conf u' q' v' :=
              congrArg Prod.snd (Option.some_injective _ hstep)
            simp only [Cfg.conf.injEq] at h2
            obtain ⟨rfl, -, rfl⟩ := h2
            rw [← huv]
            simp
    | false =>
        rcases hu : u.getLast? with _ | a
        · rw [stepCfg_left_none M hu hM] at hstep
          exact absurd hstep (by simp)
        · rw [stepCfg_left_some M hu hM] at hstep
          have h2 : Cfg.conf u.dropLast q'' (a :: v) = Cfg.conf u' q' v' :=
            congrArg Prod.snd (Option.some_injective _ hstep)
          simp only [Cfg.conf.injEq] at h2
          obtain ⟨rfl, -, rfl⟩ := h2
          rw [← huv, show u.dropLast ++ (a :: v) = (u.dropLast ++ [a]) ++ v by simp,
            List.dropLast_append_getLast? a hu]

/-- A halting run of `M` corresponds to a halting run of `outAut D`, whose
answer says whether the output produced is accepted by `D`. -/
lemma reaches_outAut {w : List A} {c t : Cfg A Q} {out : List B} (hreach : M.Reaches c out t) :
    t = Cfg.halt → (∀ u q v, c = Cfg.conf u q v → u ++ v = w) →
      ∀ d : σ, ∃ n, ((M.outAut D).next w)^[n] (cfgPos D c d)
        = Sum.inr (decide (D.evalFrom d out ∈ D.accept)) := by
  induction hreach with
  | refl c =>
      rintro rfl _ d
      exact ⟨0, by simp [cfgPos]⟩
  | @step c c' c'' o o' hstep _ ih =>
      rintro rfl hw d
      obtain ⟨u, q, v, rfl⟩ := exists_conf_of_stepCfg M hstep
      have huv := hw u q v rfl
      have hnext := next_cfgPos M D d huv hstep
      have hw' : ∀ u' q' v', c' = Cfg.conf u' q' v' → u' ++ v' = w :=
        fun u' q' v' hc' => stepCfg_append M huv hstep hc'
      obtain ⟨n, hn⟩ := ih rfl hw' (D.evalFrom d o)
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_add_apply, Function.iterate_one, hnext, hn, DFA.evalFrom_of_append]

/-- The automaton `outAut D` accepts exactly the inputs whose output is accepted
by `D`. -/
lemma outAut_accepts_iff {f : List A → List B} (hf : ∀ w, M.Computes w (f w)) (w : List A) :
    (M.outAut D).Accepts w ↔ D.evalFrom D.start (f w) ∈ D.accept := by
  obtain ⟨n, hn⟩ := reaches_outAut (w := w) M D (hf w) rfl (by intro u q v hc; cases hc; simp) D.start
  have hstart : cfgPos D (Cfg.conf [] M.init w) D.start = Sum.inl (0, (M.outAut D).init) := by
    simp [cfgPos, outAut]
  rw [hstart] at hn
  constructor
  · rintro ⟨n', hn'⟩
    have hdec := TwoDFA.answer_unique hn' hn
    simpa using hdec.symm
  · intro hmem
    exact ⟨n, by rw [hn]; simp [hmem]⟩

end TwoWay

/-- **Theorem `thm:continuity-2dfas`.**  Every function computed by a two-way transducer is
continuous. -/
theorem twoWay_continuous_aux {A B : Type} [Finite A] {f : List A → List B}
    (hf : IsTwoWay f) : Continuous f := by
  classical
  rintro L ⟨σ, hσ, D, rfl⟩
  obtain ⟨Q, hQ, M, hM⟩ := hf
  haveI : Finite Q := hQ
  have hset : {w : List A | f w ∈ D.accepts} = {w : List A | (M.outAut D).Accepts w} := by
    ext w
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, TwoWay.outAut_accepts_iff M D hM w]
    simp [DFA.mem_accepts, DFA.eval]
  rw [hset]
  exact TwoDFA.accepts_isRegular _

end Lax916827Proofs.Transducers
