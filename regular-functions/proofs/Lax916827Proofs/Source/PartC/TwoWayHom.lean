/-
Pre-composition of two-way transducers with homomorphisms and with appending a
letter (the constructions that are "left to the reader" in the proof of
Corollary `cor:2dfa-closure-under-composition` of *Transducers*, M. Bojańczyk).

The file begins with a general simulation principle: if a relation between the
configurations of a two-way transducer `aut` over the input `w` and the
configurations of a two-way transducer `N` over the input `f w` is preserved by
the steps of `N`, then `aut` computes the composition of the function computed
by `N` with `f`.

The difficulty of these constructions is that a two-way transducer must move its
head at every step, while the simulated transducer may make several steps
without leaving the block of the output that corresponds to one input letter.
The solution is a *bouncing* mode: a step in which the head should stay in place
is implemented by a step to the left followed by a step to the right.  This is
impossible when the input is empty, so the value of the composition on the empty
input is hard-coded in the transition that sees no letter at all.
-/
import Lax916827Proofs.Source.PartC.TwoWayPrecomp
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

/-! ## A general simulation principle -/

section Sim

variable {A B C S P : Type} {aut : TwoWay A C S} {N : TwoWay B C P}

/-- If `R` relates a configuration of `aut` to a configuration of `N`, and every
step of `N` from a related configuration is matched by a run of `aut` between
related configurations, then a run of `N` is matched by a run of `aut`. -/
lemma sim_reaches (R : Cfg A S → Cfg B P → Prop)
    (H : ∀ (X : Cfg A S) (c : Cfg B P) (o : List C) (c' : Cfg B P), R X c →
      N.stepCfg c = some (o, c') → ∃ Y, aut.Reaches X o Y ∧ R Y c')
    {c c' : Cfg B P} {o : List C} (h : N.Reaches c o c') :
    ∀ X, R X c → ∃ Y, aut.Reaches X o Y ∧ R Y c' := by
  induction h with
  | refl c => intro X hX; exact ⟨X, Reaches.refl X, hX⟩
  | step hs _ ih =>
      intro X hX
      obtain ⟨Y, hY, hRY⟩ := H _ _ _ _ hX hs
      obtain ⟨Z, hZ, hRZ⟩ := ih Y hRY
      exact ⟨Z, hY.trans hZ, hRZ⟩

/-- The simulation principle: `aut` computes on `w` whatever `N` computes on the
input `v`, provided that the initial configurations are related and that only
the halting vertex is related to the halting vertex. -/
lemma computes_of_sim (R : Cfg A S → Cfg B P → Prop)
    (H : ∀ (X : Cfg A S) (c : Cfg B P) (o : List C) (c' : Cfg B P), R X c →
      N.stepCfg c = some (o, c') → ∃ Y, aut.Reaches X o Y ∧ R Y c')
    {w : List A} {v : List B} {out : List C}
    (hinit : R (Cfg.conf [] aut.init w) (Cfg.conf [] N.init v))
    (hhalt : ∀ Y, R Y Cfg.halt → Y = Cfg.halt)
    (hN : N.Computes v out) : aut.Computes w out := by
  obtain ⟨Y, hY, hRY⟩ := sim_reaches R H hN _ hinit
  rw [hhalt Y hRY] at hY
  exact hY

/-- A variant of the simulation principle in which `aut` first makes a run
without output, reaching a configuration related to the initial configuration
of `N`. -/
lemma computes_of_sim' (R : Cfg A S → Cfg B P → Prop)
    (H : ∀ (X : Cfg A S) (c : Cfg B P) (o : List C) (c' : Cfg B P), R X c →
      N.stepCfg c = some (o, c') → ∃ Y, aut.Reaches X o Y ∧ R Y c')
    {w : List A} {v : List B} {out : List C} {X₀ : Cfg A S}
    (hpre : aut.Reaches (Cfg.conf [] aut.init w) [] X₀)
    (hinit : R X₀ (Cfg.conf [] N.init v))
    (hhalt : ∀ Y, R Y Cfg.halt → Y = Cfg.halt)
    (hN : N.Computes v out) : aut.Computes w out := by
  obtain ⟨Y, hY, hRY⟩ := sim_reaches R H hN _ hinit
  rw [hhalt Y hRY] at hY
  simpa using hpre.trans hY

end Sim

end TwoWay

/-! ## Appending a letter to the input -/

section Append

variable {B C P : Type} (N : TwoWay B C P) (c₀ : B) (out₀ : List C)

/-- The transition of the simulating transducer when the head of `N` is inside
the original input. -/
def appStepNormal (la rb : Option B) (p : P) :
    List C ⊕ ((P × Bool × Bool) × List C × Bool) :=
  match N.step la p (some (rb.getD c₀)) with
  | Sum.inl o => Sum.inl o
  | Sum.inr (p', o, true) =>
      match rb with
      | some _ => Sum.inr ((p', false, false), o, true)
      | none => Sum.inr ((p', true, true), o, false)
  | Sum.inr (p', o, false) => Sum.inr ((p', false, false), o, false)

/-- The transition of the simulating transducer when the head of `N` is to the
right of the appended letter. -/
def appStepPast (p : P) : List C ⊕ ((P × Bool × Bool) × List C × Bool) :=
  match N.step (some c₀) p none with
  | Sum.inl o => Sum.inl o
  | Sum.inr (_, _, true) => Sum.inl []
  | Sum.inr (p', o, false) => Sum.inr ((p', false, true), o, false)

/-- The transducer simulating `N` on the input with the letter `c₀` appended.
Its state is a triple: a state of `N`, a flag telling whether the head of `N` is
to the right of the appended letter, and a flag telling whether the head has
just bounced to the left and has to come back. -/
def appAut : TwoWay B C (P × Bool × Bool) where
  init := (N.init, false, false)
  step := fun la s rb =>
    if s.2.2 then Sum.inr ((s.1, s.2.1, false), [], true)
    else
      match la, rb with
      | none, none => Sum.inl out₀
      | some z, rb => if s.2.1 then appStepPast N c₀ s.1 else appStepNormal N c₀ (some z) rb s.1
      | none, some b => if s.2.1 then appStepPast N c₀ s.1 else appStepNormal N c₀ none (some b) s.1

variable {N c₀ out₀}

@[simp] lemma appAut_bounce (la rb : Option B) (p : P) (pst : Bool) :
    (appAut N c₀ out₀).step la (p, pst, true) rb = Sum.inr ((p, pst, false), [], true) := by
  simp [appAut]

lemma appAut_normal {la rb : Option B} (p : P) (h : ¬ (la = none ∧ rb = none)) :
    (appAut N c₀ out₀).step la (p, false, false) rb = appStepNormal N c₀ la rb p := by
  cases la with
  | none => cases rb with
      | none => exact absurd ⟨rfl, rfl⟩ h
      | some b => simp [appAut]
  | some z => cases rb <;> simp [appAut]

lemma appAut_past {la rb : Option B} (p : P) (h : ¬ (la = none ∧ rb = none)) :
    (appAut N c₀ out₀).step la (p, true, false) rb = appStepPast N c₀ p := by
  cases la with
  | none => cases rb with
      | none => exact absurd ⟨rfl, rfl⟩ h
      | some b => simp [appAut]
  | some z => cases rb <;> simp [appAut]

lemma appAut_empty (p : P) (pst : Bool) :
    (appAut N c₀ out₀).step none (p, pst, false) none = Sum.inl out₀ := by
  simp [appAut]

/-- The relation between the configurations of `appAut` on `w` and the
configurations of `N` on `w ++ [c₀]`. -/
def appRel {P : Type} (c₀ : B) (w : List B) :
    Cfg B (P × Bool × Bool) → Cfg B P → Prop := fun X c =>
  (X = Cfg.halt ∧ c = Cfg.halt) ∨
    ∃ (u v : List B) (p : P), u ++ v = w ∧
      ((X = Cfg.conf u (p, false, false) v ∧ c = Cfg.conf u p (v ++ [c₀])) ∨
        (v = [] ∧ X = Cfg.conf u (p, true, false) [] ∧ c = Cfg.conf (u ++ [c₀]) p []))

lemma head?_append_singleton (v : List B) (c₀ : B) :
    (v ++ [c₀]).head? = some (v.head?.getD c₀) := by
  cases v with
  | nil => simp
  | cons a v => simp

/-- The one-step condition of the simulation principle for `appAut`. -/
lemma appAut_step {w : List B} (hw : w ≠ [])
    (X : Cfg B (P × Bool × Bool)) (c : Cfg B P) (o : List C) (c' : Cfg B P)
    (hR : appRel c₀ w X c) (hs : N.stepCfg c = some (o, c')) :
    ∃ Y, (appAut N c₀ out₀).Reaches X o Y ∧ appRel c₀ w Y c' := by
  rcases hR with ⟨-, rfl⟩ | ⟨u, v, p, huv, hcase⟩
  · simp [TwoWay.stepCfg] at hs
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- the head of `N` is inside the original input
    have hne : ¬ (u.getLast? = none ∧ v.head? = none) := by
      rintro ⟨h1, h2⟩
      have hu : u = [] := List.getLast?_eq_none_iff.mp h1
      have hv : v = [] := List.head?_eq_none_iff.mp h2
      exact hw (by rw [← huv, hu, hv, List.append_nil])
    have hb : (v ++ [c₀]).head? = some (v.head?.getD c₀) := head?_append_singleton v c₀
    rcases hstep : N.step u.getLast? p (v ++ [c₀]).head? with o₁ | ⟨p', o₁, dir⟩
    · rw [TwoWay.stepCfg_halt_eq N hstep] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨Cfg.halt, TwoWay.reaches_one ?_, Or.inl ⟨rfl, rfl⟩⟩
      refine TwoWay.stepCfg_halt_eq _ ?_
      rw [appAut_normal (out₀ := out₀) p hne]
      rw [hb] at hstep
      simp only [appStepNormal, hstep]
    · cases dir with
      | true =>
          cases v with
          | nil =>
              -- the head of `N` moves past the appended letter, and the head of
              -- the simulating transducer bounces to the left
              simp only [List.nil_append] at hs hstep
              rw [TwoWay.stepCfg_right_cons N hstep] at hs
              simp only [List.head?_cons] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨rfl, rfl⟩ := hs
              have hu : u ≠ [] := by
                intro h; exact hw (by rw [← huv, h]; simp)
              obtain ⟨u', z, rfl⟩ : ∃ u' z, u = u' ++ [z] := by
                rcases List.eq_nil_or_concat u with h | ⟨u', z, h⟩
                · exact absurd h hu
                · exact ⟨u', z, by simpa using h⟩
              have hlast : (u' ++ [z]).getLast? = some z := by simp
              have h1 : (appAut N c₀ out₀).stepCfg
                  (Cfg.conf (u' ++ [z]) (p, false, false) []) =
                  some (o₁, Cfg.conf u' (p', true, true) [z]) := by
                have := TwoWay.stepCfg_left_some (M := appAut N c₀ out₀) (v := ([] : List B))
                  hlast (q := (p, false, false)) (q' := (p', true, true)) (o := o₁) ?_
                · simpa using this
                · rw [appAut_normal (out₀ := out₀) p hne]
                  simp only [appStepNormal, hstep, List.head?_nil, Option.getD_none]
              have h2 : (appAut N c₀ out₀).stepCfg (Cfg.conf u' (p', true, true) [z]) =
                  some ([], Cfg.conf (u' ++ [z]) (p', true, false) []) := by
                refine TwoWay.stepCfg_right_cons _ ?_
                simp
              refine ⟨Cfg.conf (u' ++ [z]) (p', true, false) [], ?_, ?_⟩
              · simpa using TwoWay.Reaches.step h1 (TwoWay.reaches_one h2)
              · exact Or.inr ⟨u' ++ [z], [], p', huv, Or.inr ⟨rfl, rfl, rfl⟩⟩
          | cons a v' =>
              simp only [List.cons_append] at hs hstep
              rw [TwoWay.stepCfg_right_cons N hstep] at hs
              simp only [List.head?_cons] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨rfl, rfl⟩ := hs
              refine ⟨Cfg.conf (u ++ [a]) (p', false, false) v', TwoWay.reaches_one ?_, ?_⟩
              · refine TwoWay.stepCfg_right_cons _ ?_
                rw [appAut_normal (out₀ := out₀) p hne]
                simp only [appStepNormal, hstep, List.head?_cons, Option.getD_some]
              · exact Or.inr ⟨u ++ [a], v', p', by simpa using huv, Or.inl ⟨rfl, rfl⟩⟩
      | false =>
          rcases hu : u.getLast? with _ | z
          · rw [TwoWay.stepCfg_left_none N hu hstep] at hs; simp at hs
          · rw [TwoWay.stepCfg_left_some N hu hstep] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            have hdrop : u.dropLast ++ [z] = u := List.dropLast_append_getLast? _ hu
            refine ⟨Cfg.conf u.dropLast (p', false, false) (z :: v), TwoWay.reaches_one ?_, ?_⟩
            · refine TwoWay.stepCfg_left_some _ hu ?_
              rw [appAut_normal (out₀ := out₀) p hne]
              rw [hb] at hstep
              simp only [appStepNormal, hstep]
            · refine Or.inr ⟨u.dropLast, z :: v, p', ?_, Or.inl ⟨rfl, ?_⟩⟩
              · rw [← huv, ← hdrop]; simp
              · simp
  · -- the head of `N` is to the right of the appended letter
    have hu : u ≠ [] := by intro h; exact hw (by rw [← huv, h]; simp)
    obtain ⟨u', z, rfl⟩ : ∃ u' z, u = u' ++ [z] := by
      rcases List.eq_nil_or_concat u with h | ⟨u', z, h⟩
      · exact absurd h hu
      · exact ⟨u', z, by simpa using h⟩
    have hlast : (u' ++ [z]).getLast? = some z := by simp
    have hne : ¬ ((u' ++ [z]).getLast? = none ∧ (([] : List B)).head? = none) := by
      simp [hlast]
    have hlastc : ((u' ++ [z]) ++ [c₀]).getLast? = some c₀ := by simp
    rcases hstep : N.step ((u' ++ [z]) ++ [c₀]).getLast? p (([] : List B)).head? with
      o₁ | ⟨p', o₁, dir⟩ <;> simp only [List.head?_nil] at hstep
    · rw [TwoWay.stepCfg_halt_eq N hstep] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨Cfg.halt, TwoWay.reaches_one ?_, Or.inl ⟨rfl, rfl⟩⟩
      refine TwoWay.stepCfg_halt_eq _ ?_
      rw [appAut_past (out₀ := out₀) p hne]
      rw [hlastc] at hstep
      simp only [appStepPast, hstep]
    · cases dir with
      | true => rw [TwoWay.stepCfg_right_nil N hstep] at hs; simp at hs
      | false =>
          rw [TwoWay.stepCfg_left_some N hlastc hstep] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have h1 : (appAut N c₀ out₀).stepCfg (Cfg.conf (u' ++ [z]) (p, true, false) []) =
              some (o₁, Cfg.conf u' (p', false, true) [z]) := by
            have := TwoWay.stepCfg_left_some (M := appAut N c₀ out₀) (v := ([] : List B))
              hlast (q := (p, true, false)) (q' := (p', false, true)) (o := o₁) ?_
            · simpa using this
            · rw [appAut_past (out₀ := out₀) p hne]
              rw [hlastc] at hstep
              simp only [appStepPast, hstep]
          have h2 : (appAut N c₀ out₀).stepCfg (Cfg.conf u' (p', false, true) [z]) =
              some ([], Cfg.conf (u' ++ [z]) (p', false, false) []) := by
            refine TwoWay.stepCfg_right_cons _ ?_
            simp
          refine ⟨Cfg.conf (u' ++ [z]) (p', false, false) [], ?_, ?_⟩
          · simpa using TwoWay.Reaches.step h1 (TwoWay.reaches_one h2)
          · refine Or.inr ⟨u' ++ [z], [], p', huv, Or.inl ⟨rfl, ?_⟩⟩
            simp

/-- The transducer `appAut` computes the composition with appending a letter. -/
theorem appAut_computes {g : List B → List C} (hN : ∀ v, N.Computes v (g v))
    (hout : out₀ = g [c₀]) (w : List B) :
    (appAut N c₀ out₀).Computes w (g (w ++ [c₀])) := by
  rcases List.eq_nil_or_concat w with rfl | ⟨w', a, rfl⟩
  · have h1 : (appAut N c₀ out₀).stepCfg (Cfg.conf [] (appAut N c₀ out₀).init []) =
        some (out₀, Cfg.halt) := by
      refine TwoWay.stepCfg_halt_eq _ ?_
      simpa using appAut_empty (out₀ := out₀) N.init false
    simpa [TwoWay.Computes, hout] using TwoWay.reaches_one h1
  · refine TwoWay.computes_of_sim (appRel c₀ (w'.concat a))
      (appAut_step (N := N) (out₀ := out₀) (by simp)) ?_ ?_ (hN _)
    · exact Or.inr ⟨[], w'.concat a, N.init, by simp, Or.inl ⟨rfl, rfl⟩⟩
    · rintro Y (⟨rfl, -⟩ | ⟨u, v, p, -, ⟨-, h⟩ | ⟨-, -, h⟩⟩)
      · rfl
      · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- Two-way transducers are closed under pre-composition with appending a fixed
letter. -/
theorem isTwoWay_comp_append {g : List B → List C} (hg : IsTwoWay g) (c₀ : B) :
    IsTwoWay (fun w => g (w ++ [c₀])) := by
  obtain ⟨P, hP, N, hN⟩ := hg
  haveI := hP
  exact ⟨P × Bool × Bool, inferInstance, appAut N c₀ (g [c₀]), fun w => appAut_computes hN rfl w⟩

end Append

end Lax916827Proofs.Transducers
