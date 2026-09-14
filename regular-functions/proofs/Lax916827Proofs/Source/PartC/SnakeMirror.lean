/-
Mirroring a two-way transducer.

In the proof of the book's snake lemma (the induction step
`Transducers.boundedWidth_isRegular_step`, cf.
`RequestProject/PartC/SnakeReg.lean`) the general case is reduced to the case
where the source column of the snake is to the left of its target column, by
*reversing the snake*: "when reversing a snake, we need to change the direction
of the arrows in the letters that represent the snake".

Since a snake graph is presented in this formalisation as the run of a two-way
transducer rather than as a string over an alphabet of snake letters, reversing
a snake is mirroring the transducer: `mirror M` swaps the roles of the two
letters adjacent to the head and swaps the two directions.  The run of `mirror M`
on the reversed input is then the mirror image of the run of `M`, with the *same*
output (`stepCfg_mirror`, `reaches_mirror_iff`).

The construction is an involution (`mirror_mirror`), and it is stated for
arbitrary configurations, not only for the initial one, because that is how the
snake lemma uses it: the pieces of a run start and end in the middle of it.
-/
import Lax916827Proofs.Source.PartC.TwoWayRun
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- The mirror image of a configuration: the head keeps its state, and the two
sides of the input are exchanged and reversed. -/
def mirrorCfg : Cfg A Q → Cfg A Q
  | Cfg.conf u q v => Cfg.conf v.reverse q u.reverse
  | Cfg.halt => Cfg.halt

@[simp] lemma mirrorCfg_halt : mirrorCfg (Cfg.halt : Cfg A Q) = Cfg.halt := rfl

@[simp] lemma mirrorCfg_conf (u : List A) (q : Q) (v : List A) :
    mirrorCfg (Cfg.conf u q v) = Cfg.conf v.reverse q u.reverse := rfl

@[simp] lemma mirrorCfg_mirrorCfg (c : Cfg A Q) : mirrorCfg (mirrorCfg c) = c := by
  cases c <;> simp

/-- The mirror image of a two-way transducer: it reads the letter to the left of
the head where `M` reads the letter to its right and conversely, and it moves in
the opposite direction. -/
def mirror (M : TwoWay A B Q) : TwoWay A B Q where
  init := M.init
  step := fun l q r =>
    match M.step r q l with
    | Sum.inl o => Sum.inl o
    | Sum.inr (q', o, d) => Sum.inr (q', o, !d)

@[simp] lemma mirror_init (M : TwoWay A B Q) : (mirror M).init = M.init := rfl

lemma mirror_step (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) :
    (mirror M).step l q r =
      match M.step r q l with
      | Sum.inl o => Sum.inl o
      | Sum.inr (q', o, d) => Sum.inr (q', o, !d) := rfl

/-- Mirroring is an involution. -/
lemma mirror_mirror (M : TwoWay A B Q) : mirror (mirror M) = M := by
  cases M with
  | mk init step =>
      simp only [mirror, TwoWay.mk.injEq, true_and]
      funext l q r
      rcases step l q r with o | ⟨q', o, d⟩ <;> simp

/-- **One step of the mirrored transducer is the mirror image of one step of the
transducer**, with the same output. -/
theorem stepCfg_mirror (M : TwoWay A B Q) (c : Cfg A Q) :
    (mirror M).stepCfg (mirrorCfg c) = (M.stepCfg c).map (fun p => (p.1, mirrorCfg p.2)) := by
  cases c with
  | halt => simp [stepCfg]
  | conf u q v =>
      have hl : (v.reverse).getLast? = v.head? := List.getLast?_reverse
      have hr : (u.reverse).head? = u.getLast? := List.head?_reverse
      rcases hs : M.step u.getLast? q v.head? with o | ⟨q', o, d⟩
      · have h1 : (mirror M).step (v.reverse).getLast? q (u.reverse).head? = Sum.inl o := by
          rw [mirror_step, hl, hr, hs]
        rw [mirrorCfg_conf, stepCfg_halt_eq _ h1, stepCfg_halt_eq _ hs]
        simp
      · cases d with
        | true =>
            have h1 : (mirror M).step (v.reverse).getLast? q (u.reverse).head?
                = Sum.inr (q', o, false) := by
              rw [mirror_step, hl, hr, hs]; rfl
            cases v with
            | nil =>
                rw [mirrorCfg_conf, stepCfg_right_nil _ hs]
                simp only [List.reverse_nil]
                rw [stepCfg_left_none _ (by simp) (by simpa using h1)]
                simp
            | cons a v' =>
                have hva : (v'.reverse ++ [a]).getLast? = some a := by simp
                rw [mirrorCfg_conf, stepCfg_right_cons _ hs]
                simp only [List.reverse_cons]
                rw [stepCfg_left_some _ hva (by simpa using h1)]
                simp
        | false =>
            have h1 : (mirror M).step (v.reverse).getLast? q (u.reverse).head?
                = Sum.inr (q', o, true) := by
              rw [mirror_step, hl, hr, hs]; rfl
            rcases hu : u.getLast? with _ | a
            · have hun : u = [] := List.getLast?_eq_none_iff.1 hu
              subst hun
              rw [mirrorCfg_conf, stepCfg_left_none _ hu hs]
              simp only [List.reverse_nil]
              rw [stepCfg_right_nil _ (by simpa using h1)]
              simp
            · obtain ⟨u', rfl⟩ := List.getLast?_eq_some_iff.1 hu
              rw [mirrorCfg_conf, stepCfg_left_some _ hu hs]
              simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
                List.nil_append, List.cons_append]
              rw [stepCfg_right_cons _ (by simpa using h1)]
              simp

/-- **The mirrored transducer reaches the mirror image of what the transducer
reaches, with the same output.** -/
theorem reaches_mirror {M : TwoWay A B Q} {c c' : Cfg A Q} {o : List B}
    (h : M.Reaches c o c') : (mirror M).Reaches (mirrorCfg c) o (mirrorCfg c') := by
  induction h with
  | refl c => exact Reaches.refl _
  | step hstep _ ih =>
      refine Reaches.step ?_ ih
      rw [stepCfg_mirror, hstep]
      rfl

/-- Reversing a snake does not change its output. -/
theorem reaches_mirror_iff {M : TwoWay A B Q} {c c' : Cfg A Q} {o : List B} :
    (mirror M).Reaches (mirrorCfg c) o (mirrorCfg c') ↔ M.Reaches c o c' := by
  refine ⟨fun h => ?_, reaches_mirror⟩
  have := reaches_mirror h
  rwa [mirror_mirror, mirrorCfg_mirrorCfg, mirrorCfg_mirrorCfg] at this

/-- A run of `M` that starts at the right end of the input and halts is the same
thing, with the same output, as a run of `mirror M` that starts at the left end
of the reversed input and halts. -/
theorem reaches_mirror_reverse {M : TwoWay A B Q} {w : List A} {q : Q} {o : List B} :
    (mirror M).Reaches (Cfg.conf [] q w.reverse) o Cfg.halt ↔
      M.Reaches (Cfg.conf w q []) o Cfg.halt := by
  have h := reaches_mirror_iff (M := M) (c := Cfg.conf w q []) (c' := Cfg.halt) (o := o)
  simpa using h

end TwoWay

end Lax916827Proofs.Transducers
