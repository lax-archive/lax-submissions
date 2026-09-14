/-
The halting completion of a two-way transducer.

`Transducers.IsTwoWay` -- like `Transducers.IsRegularFun`, `Transducers.IsSST` and
`Transducers.IsPebbleTransducer` -- speaks about *total* functions: the transducer must halt on
every input.  A two-way transducer that is built to simulate something else usually halts only on
the inputs of the expected shape, and on the other ones it may loop for ever; the set of those
inputs is in general not regular, so it cannot simply be tested first.

This file shows that this is not an obstacle: for every two-way transducer `M` there is a *total*
function `F` which is a regular function and which agrees with `M` wherever `M` halts
(`Transducers.TwoWay.exists_regularFun_of_twoWay`).  The point is that the set of inputs on which
`M` halts *is* regular -- it is the language of the two-way automaton underlying `M`, so
Shepherdson's Theorem (`Transducers.TwoDFA.accepts_isRegular`) applies -- and that a two-way
transducer can test a regular language by one left-to-right pass, rewind, and then run `M`, which
by the choice of the test is guaranteed to halt.
-/
import Lax916827Proofs
import Lax314295Proofs
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace TwoWay
open Lax916827Proofs.Transducers.TwoWay

variable {A B Q : Type}

/-! ## The inputs on which a two-way transducer halts -/

/-- The automaton that accepts every string. -/
def trivDFA (B : Type) : DFA B Unit where
  step := fun _ _ => ()
  start := ()
  accept := Set.univ

@[simp] lemma trivDFA_mem (s : Unit) : s ∈ (trivDFA B).accept := Set.mem_univ s

section Halt

variable (M : TwoWay A B Q) {σ : Type} (D : DFA B σ)

open scoped Classical in
/-- A configuration with no outgoing step is a configuration from which the two-way automaton
`outAut D` dies. -/
lemma next_cfgPos_none {w u v : List A} {q : Q} (d : σ) (huv : u ++ v = w)
    (hstep : M.stepCfg (Cfg.conf u q v) = none) :
    (M.outAut D).next w (cfgPos D (Cfg.conf u q v) d) = Sum.inr false := by
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
  · rw [stepCfg_halt_eq M hM] at hstep; exact absurd hstep (by simp)
  · cases dir with
    | true =>
        cases v with
        | nil =>
            have hnot : ¬ u.length < w.length := by simp at hlen; omega
            simp only [cfgPos, TwoDFA.next, hleft, hright, outAut, hM, if_neg hnot]
        | cons a v' =>
            rw [stepCfg_right_cons M hM] at hstep; exact absurd hstep (by simp)
    | false =>
        rcases hu : u.getLast? with _ | a
        · have hu0 : u = [] := by
            cases u with
            | nil => rfl
            | cons b u' => simp at hu
          subst hu0
          simp only [cfgPos, TwoDFA.next, hleft, hright, outAut, hM]
          simp
        · rw [stepCfg_left_some M hu hM] at hstep; exact absurd hstep (by simp)

open scoped Classical in
/-- An accepting run of `outAut D` comes from a halting run of `M`. -/
lemma exists_reaches_of_iterate {w : List A} :
    ∀ (n : ℕ) (c : Cfg A Q) (d : σ),
      (∀ u q v, c = Cfg.conf u q v → u ++ v = w) →
      ((M.outAut D).next w)^[n] (cfgPos D c d) = Sum.inr true →
      ∃ out, M.Reaches c out Cfg.halt := by
  intro n
  induction n with
  | zero =>
      intro c d _ hc
      cases c with
      | halt => exact ⟨[], Reaches.refl _⟩
      | conf u q v => simp [cfgPos] at hc
  | succ n ih =>
      intro c d hw hc
      cases c with
      | halt => exact ⟨[], Reaches.refl _⟩
      | conf u q v =>
          have huv := hw u q v rfl
          rcases hstep : M.stepCfg (Cfg.conf u q v) with _ | ⟨o, c'⟩
          · rw [Function.iterate_succ_apply, next_cfgPos_none M D d huv hstep] at hc
            simp at hc
          · rw [Function.iterate_succ_apply, next_cfgPos M D d huv hstep] at hc
            have hw' : ∀ u' q' v', c' = Cfg.conf u' q' v' → u' ++ v' = w :=
              fun u' q' v' hc' => stepCfg_append M huv hstep hc'
            obtain ⟨out, hout⟩ := ih c' _ hw' hc
            exact ⟨o ++ out, Reaches.step hstep hout⟩

open scoped Classical in
/-- The two-way automaton `outAut (trivDFA B)` accepts exactly the inputs on which `M` halts. -/
lemma outAut_triv_accepts_iff (w : List A) :
    (M.outAut (trivDFA B)).Accepts w ↔ ∃ v, M.Computes w v := by
  constructor
  · rintro ⟨n, hn⟩
    have hstart : cfgPos (trivDFA B) (Cfg.conf [] M.init w) ()
        = Sum.inl (0, (M.outAut (trivDFA B)).init) := by
      simp [cfgPos, outAut]
    rw [← hstart] at hn
    exact exists_reaches_of_iterate M (trivDFA B) n _ () (by intro u q v hc; cases hc; simp) hn
  · rintro ⟨v, hv⟩
    obtain ⟨n, hn⟩ := reaches_outAut (w := w) M (trivDFA B) hv rfl
      (by intro u q v hc; cases hc; simp) ()
    refine ⟨n, ?_⟩
    have hstart : cfgPos (trivDFA B) (Cfg.conf [] M.init w) ()
        = Sum.inl (0, (M.outAut (trivDFA B)).init) := by
      simp [cfgPos, outAut]
    rw [hstart] at hn
    simpa using hn

/-- The set of inputs on which a two-way transducer halts is a regular language. -/
theorem isRegular_halting [Finite A] [Finite Q] :
    Language.IsRegular ({w : List A | ∃ v, M.Computes w v} : Language A) := by
  classical
  have h := TwoDFA.accepts_isRegular (M.outAut (trivDFA B))
  refine RegAut.isRegular_of_eq (L₂ := {w : List A | ∃ v, M.Computes w v}) h ?_
  intro u
  exact (outAut_triv_accepts_iff M u).symm

end Halt

/-! ## The completed transducer -/

/-- The states of the completed transducer: testing the regular language of the inputs on which
`M` halts by a left-to-right pass, rewinding, and running `M`. -/
inductive TotSt (σ Q : Type) : Type
  /-- The left-to-right pass, carrying the state of the automaton. -/
  | scan : σ → TotSt σ Q
  /-- The rewinding pass. -/
  | rew : TotSt σ Q
  /-- Running `M`. -/
  | run : Q → TotSt σ Q

instance {σ Q : Type} [Finite σ] [Finite Q] : Finite (TotSt σ Q) := by
  have h : Function.Injective
      (fun z : TotSt σ Q => match z with
        | TotSt.scan s => (Sum.inl s : σ ⊕ Option Q)
        | TotSt.rew => Sum.inr none
        | TotSt.run q => Sum.inr (some q)) := by
    intro z z' h
    cases z <;> cases z' <;> simp_all
  exact Finite.of_injective _ h

section Total

variable (M : TwoWay A B Q) {σ : Type} (D : DFA B σ)

/-- The rewinding step: move left, or, at the left end, perform the first step of `M`. -/
def rewStep (l : Option A) (r : Option A) : List B ⊕ (TotSt σ Q × List B × Bool) :=
  match l with
  | none =>
      match M.step none M.init r with
      | Sum.inl o => Sum.inl o
      | Sum.inr (q', o, dir) => Sum.inr (TotSt.run q', o, dir)
  | some _ => Sum.inr (TotSt.rew, [], false)

open scoped Classical in
/-- The completed transducer: it tests, by a left-to-right pass, whether the input is accepted by
the automaton `C`; if it is not, it halts with the empty output, and if it is, it rewinds and runs
`M`. -/
noncomputable def total (C : DFA A σ) : TwoWay A B (TotSt σ Q) where
  init := TotSt.scan C.start
  step := fun l s r =>
    match s with
    | TotSt.scan d =>
        match r with
        | some a => Sum.inr (TotSt.scan (C.step d a), [], true)
        | none => if d ∈ C.accept then rewStep M l r else Sum.inl []
    | TotSt.rew => rewStep M l r
    | TotSt.run q =>
        match M.step l q r with
        | Sum.inl o => Sum.inl o
        | Sum.inr (q', o, dir) => Sum.inr (TotSt.run q', o, dir)

variable (C : DFA A σ)

open scoped Classical in
/-- The left-to-right pass reaches the right end of the input in the state that the automaton
reaches. -/
lemma reaches_scan : ∀ (v u : List A) (d : σ),
    (total M C).Reaches (Cfg.conf u (TotSt.scan d) v) []
      (Cfg.conf (u ++ v) (TotSt.scan (C.evalFrom d v)) []) := by
  intro v
  induction v with
  | nil => intro u d; simpa using Reaches.refl _
  | cons a v ih =>
      intro u d
      have hstep : (total M C).stepCfg (Cfg.conf u (TotSt.scan d) (a :: v))
          = some ([], Cfg.conf (u ++ [a]) (TotSt.scan (C.step d a)) v) := by
        apply stepCfg_right_cons
        simp [total]
      have := ih (u ++ [a]) (C.step d a)
      have h2 : (total M C).Reaches (Cfg.conf u (TotSt.scan d) (a :: v)) ([] ++ [])
          (Cfg.conf (u ++ [a] ++ v) (TotSt.scan (C.evalFrom (C.step d a) v)) []) :=
        Reaches.step hstep this
      simpa [DFA.evalFrom, List.append_assoc] using h2

open scoped Classical in
/-- The rewinding pass reaches the left end of the input. -/
lemma reaches_rew : ∀ (u v : List A),
    (total M C).Reaches (Cfg.conf u TotSt.rew v) [] (Cfg.conf [] TotSt.rew (u ++ v)) := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro v; simpa using Reaches.refl _
  | append_singleton u a ih =>
      intro v
      have hlast : (u ++ [a]).getLast? = some a := by simp
      have hstep : (total M C).stepCfg (Cfg.conf (u ++ [a]) TotSt.rew v)
          = some ([], Cfg.conf u TotSt.rew (a :: v)) := by
        have h := stepCfg_left_some (M := total M C) (u := u ++ [a]) (v := v)
          (q := TotSt.rew) (q' := TotSt.rew) (o := []) (a := a) hlast (by simp [total, rewStep, hlast])
        simpa using h
      have h2 := Reaches.step hstep (ih (a :: v))
      simpa using h2

open scoped Classical in
/-- Once `M` is being run, the completed transducer mirrors it step by step. -/
lemma reaches_run {c t : Cfg A Q} {out : List B} (h : M.Reaches c out t) :
    t = Cfg.halt → ∀ u q v, c = Cfg.conf u q v →
      (total M C).Reaches (Cfg.conf u (TotSt.run q) v) out Cfg.halt := by
  induction h with
  | refl c => rintro rfl u q v hc; exact absurd hc (by simp)
  | @step c c' c'' o o' hstep hrest ih =>
      rintro rfl u q v hc
      subst hc
      rcases hM : M.step u.getLast? q v.head? with o₀ | ⟨q₀, o₀, dir⟩
      · rw [stepCfg_halt_eq M hM] at hstep
        have hpair := Option.some_injective _ hstep
        have h1 : o₀ = o := congrArg Prod.fst hpair
        have h2 : Cfg.halt = c' := congrArg Prod.snd hpair
        subst h1
        have hstep' : (total M C).stepCfg (Cfg.conf u (TotSt.run q) v) = some (o₀, Cfg.halt) := by
          apply stepCfg_halt_eq; simp [total, hM]
        have ho' : o' = [] := by
          rw [← h2] at hrest
          cases hrest with
          | refl _ => rfl
          | step hs _ => simp [stepCfg] at hs
        rw [ho']
        simpa using Reaches.step hstep' (Reaches.refl (M := total M C) Cfg.halt)
      · cases dir with
        | true =>
            cases v with
            | nil => rw [stepCfg_right_nil M hM] at hstep; exact absurd hstep (by simp)
            | cons a v' =>
                rw [stepCfg_right_cons M hM] at hstep
                have hpair := Option.some_injective _ hstep
                have h1 : o₀ = o := congrArg Prod.fst hpair
                have h2 : Cfg.conf (u ++ [a]) q₀ v' = c' := congrArg Prod.snd hpair
                subst h1
                have hstep' : (total M C).stepCfg (Cfg.conf u (TotSt.run q) (a :: v'))
                    = some (o₀, Cfg.conf (u ++ [a]) (TotSt.run q₀) v') := by
                  apply stepCfg_right_cons; simp only [total, hM]
                exact Reaches.step hstep' (ih rfl (u ++ [a]) q₀ v' h2.symm)
        | false =>
            rcases hu : u.getLast? with _ | a
            · rw [stepCfg_left_none M hu hM] at hstep; exact absurd hstep (by simp)
            · rw [stepCfg_left_some M hu hM] at hstep
              have hpair := Option.some_injective _ hstep
              have h1 : o₀ = o := congrArg Prod.fst hpair
              have h2 : Cfg.conf u.dropLast q₀ (a :: v) = c' := congrArg Prod.snd hpair
              subst h1
              have hstep' : (total M C).stepCfg (Cfg.conf u (TotSt.run q) v)
                  = some (o₀, Cfg.conf u.dropLast (TotSt.run q₀) (a :: v)) := by
                refine stepCfg_left_some (total M C) hu ?_
                simp only [total, hM]
              exact Reaches.step hstep' (ih rfl u.dropLast q₀ (a :: v) h2.symm)

open scoped Classical in
/-- From the left end in the rewinding state, the completed transducer runs `M`. -/
lemma reaches_rew_start {c t : Cfg A Q} {out : List B} (h : M.Reaches c out t) :
    t = Cfg.halt → ∀ w, c = Cfg.conf [] M.init w →
      (total M C).Reaches (Cfg.conf [] TotSt.rew w) out Cfg.halt := by
  induction h with
  | refl c => rintro rfl w hc; exact absurd hc (by simp)
  | @step c c' c'' o o' hstep hrest _ =>
      rintro rfl w hc
      subst hc
      rcases hM : M.step (([] : List A).getLast?) M.init w.head? with o₀ | ⟨q₀, o₀, dir⟩
      · have hMn : M.step (none : Option A) M.init w.head? = Sum.inl o₀ := by simpa using hM
        rw [stepCfg_halt_eq M hM] at hstep
        have hpair := Option.some_injective _ hstep
        have h1 : o₀ = o := congrArg Prod.fst hpair
        have h2 : Cfg.halt = c' := congrArg Prod.snd hpair
        subst h1
        have hstep' : (total M C).stepCfg (Cfg.conf [] TotSt.rew w) = some (o₀, Cfg.halt) := by
          apply stepCfg_halt_eq
          simp only [total, rewStep, List.getLast?_nil, hMn]
        have ho' : o' = [] := by
          rw [← h2] at hrest
          cases hrest with
          | refl _ => rfl
          | step hs _ => simp [stepCfg] at hs
        rw [ho']
        simpa using Reaches.step hstep' (Reaches.refl (M := total M C) Cfg.halt)
      · have hMn : M.step (none : Option A) M.init w.head? = Sum.inr (q₀, o₀, dir) := by
          simpa using hM
        cases dir with
        | true =>
            cases w with
            | nil =>
                rw [stepCfg_right_nil M hM] at hstep
                exact absurd hstep (by simp)
            | cons a v' =>
                rw [stepCfg_right_cons M hM] at hstep
                have hpair := Option.some_injective _ hstep
                have h1 : o₀ = o := congrArg Prod.fst hpair
                have h2 : Cfg.conf ([] ++ [a]) q₀ v' = c' := congrArg Prod.snd hpair
                subst h1
                have hstep' : (total M C).stepCfg (Cfg.conf [] TotSt.rew (a :: v'))
                    = some (o₀, Cfg.conf ([] ++ [a]) (TotSt.run q₀) v') := by
                  apply stepCfg_right_cons
                  simp only [total, rewStep, List.getLast?_nil, hMn]
                exact Reaches.step hstep' (reaches_run M C hrest rfl ([] ++ [a]) q₀ v' h2.symm)
        | false =>
            rw [stepCfg_left_none M (by simp) hM] at hstep
            exact absurd hstep (by simp)

end Total

open scoped Classical in
/-- **The halting completion of a two-way transducer.**  For every two-way transducer `M` there is
a total function `F`, computed by a two-way transducer -- hence a regular function -- which
agrees with `M` on every input on which `M` halts. -/
theorem exists_regularFun_of_twoWay [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) :
    ∃ F : List A → List B, IsRegularFun F ∧ ∀ u v, M.Computes u v → F u = v := by
  classical
  obtain ⟨σ, hσ, C, hC⟩ := isRegular_halting M
  haveI := hσ
  set F : List A → List B := fun u =>
    if h : ∃ v, M.Computes u v then h.choose else [] with hF
  have hFspec : ∀ u v, M.Computes u v → F u = v := by
    intro u v hv
    have hex : ∃ v, M.Computes u v := ⟨v, hv⟩
    rw [hF]
    simp only [dif_pos hex]
    exact computes_unique hex.choose_spec hv
  refine ⟨F, ?_, hFspec⟩
  refine isRegularFun_of_isTwoWay ⟨TotSt σ Q, inferInstance, total M C, ?_⟩
  intro u
  have h1 : (total M C).Reaches (Cfg.conf [] (TotSt.scan C.start) u) []
      (Cfg.conf u (TotSt.scan (C.evalFrom C.start u)) []) := by
    simpa using reaches_scan M C u [] C.start
  by_cases hu : ∃ v, M.Computes u v
  · obtain ⟨v, hv⟩ := hu
    have hmem : u ∈ C.accepts := by rw [hC]; exact ⟨v, hv⟩
    have hacc : C.evalFrom C.start u ∈ C.accept := hmem
    have h2 : (total M C).stepCfg (Cfg.conf u (TotSt.scan (C.evalFrom C.start u)) [])
        = (total M C).stepCfg (Cfg.conf u TotSt.rew []) := by
      simp [stepCfg, total, hacc]
    have h3 : (total M C).Reaches (Cfg.conf u TotSt.rew []) v Cfg.halt := by
      have hr := reaches_rew M C u []
      rw [List.append_nil] at hr
      simpa using hr.trans (reaches_rew_start M C hv rfl u rfl)
    have h4 : (total M C).Reaches (Cfg.conf u (TotSt.scan (C.evalFrom C.start u)) []) v
        Cfg.halt := by
      cases h3 with
      | step hs hrest => exact Reaches.step (h2.trans hs) hrest
    have : (total M C).Computes u ([] ++ v) := h1.trans h4
    rw [hFspec u v hv]
    simpa using this
  · have hacc : C.evalFrom C.start u ∉ C.accept := by
      intro hmem
      exact hu (by have : u ∈ C.accepts := hmem; rw [hC] at this; exact this)
    have h2 : (total M C).stepCfg (Cfg.conf u (TotSt.scan (C.evalFrom C.start u)) [])
        = some ([], Cfg.halt) := by
      apply stepCfg_halt_eq
      simp [total, hacc]
    have hF : F u = [] := by rw [hF]; simp only [dif_neg hu]
    rw [hF]
    have : (total M C).Computes u ([] ++ ([] ++ [])) :=
      h1.trans (Reaches.step h2 (Reaches.refl _))
    simpa using this

end TwoWay

end Lax194892Proofs.Transducers
