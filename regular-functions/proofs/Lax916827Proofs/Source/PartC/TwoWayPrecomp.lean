/- Pre-composition of two-way transducers with Mealy machines (Lemma
`lem:2dfa-precomposition-with-mealy` of *Transducers*, M. Bojańczyk).

A two-way transducer that reads the output of a Mealy machine has to know, at
every gap of the input, the state of the Mealy machine at that gap.  Moving to
the right this state is updated by the transition function, but moving to the
left it cannot be updated, since several states may go to the current one.
Following the book, the problem is solved by the Krohn-Rhodes Theorem: it is
enough to treat the case of a *prime* Mealy machine.  For a reversible machine
the state transformation of a letter is invertible, so the state can be updated
in both directions.  For a flip-flop machine the state transformation of a
letter is the identity or a constant; when the letter to the left of the gap is
a constant one, the transducer runs a subroutine that looks for the previous
constant letter and then returns to its place, which is recognisable because it
is the first constant letter met on the way back.

The file first sets up the common part of the two constructions: a two-way
transducer over the input alphabet whose states are triples consisting of a
state of the two-way transducer, a state of the Mealy machine, and a mode.  In
the *normal* mode the Mealy state is the one of the gap *before* the letter to
the left of the head, which is exactly the information needed to compute the two
letters adjacent to the head in the output of the Mealy machine.  A step to the
left leads to the *pending* mode, in which the stored Mealy state is the one of
the current gap; the hypothesis `hpnd` of `precomp_computes` says that the
pending mode eventually behaves like the normal mode.
-/
import Lax765601Proofs.Source.PartA.Statements
import Lax916827Proofs.Source.PartC.TwoWayCont
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- Reachability in the configuration graph is transitive. -/
lemma Reaches.trans {M : TwoWay A B Q} {c c' c'' : Cfg A Q} {o o' : List B}
    (h : M.Reaches c o c') : M.Reaches c' o' c'' → M.Reaches c (o ++ o') c'' := by
  induction h with
  | refl c => intro h'; simpa using h'
  | step hs _ ih =>
      intro h'
      rw [List.append_assoc]
      exact Reaches.step hs (ih h')

/-- Nothing happens after the halting vertex. -/
lemma reaches_halt {M : TwoWay A B Q} {o : List B} {c : Cfg A Q}
    (h : M.Reaches Cfg.halt o c) : o = [] ∧ c = Cfg.halt := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => simp [stepCfg] at hs

/-- A single step, as a reachability statement. -/
lemma reaches_one {M : TwoWay A B Q} {c c' : Cfg A Q} {o : List B}
    (h : M.stepCfg c = some (o, c')) : M.Reaches c o c' := by
  simpa using Reaches.step h (Reaches.refl c')

end TwoWay

/-! ## The Mealy states at a gap -/

variable {A B C Q P : Type}

/-- The state of the Mealy machine `M` at the gap *before* the last letter of
`u`; equivalently, after reading `u` without its last letter. -/
def preSt (M : Mealy A B Q) (u : List A) : Q := M.trans u.dropLast M.init

/-- The state of the Mealy machine `M` at the gap after `u`. -/
def gapSt (M : Mealy A B Q) (u : List A) : Q := M.trans u M.init

@[simp] lemma preSt_nil (M : Mealy A B Q) : preSt M [] = M.init := rfl

@[simp] lemma gapSt_nil (M : Mealy A B Q) : gapSt M [] = M.init := rfl

lemma gapSt_concat (M : Mealy A B Q) (u : List A) (a : A) :
    gapSt M (u ++ [a]) = (M.step (gapSt M u) a).1 := by
  simp [gapSt, Mealy.trans_append, Mealy.trans_cons, Mealy.letterTrans]

lemma preSt_concat (M : Mealy A B Q) (u : List A) (a : A) :
    preSt M (u ++ [a]) = gapSt M u := by
  simp [preSt, gapSt]

/-- If the last letter of `u` is `a`, the state at the gap after `u` is obtained
from the state at the gap before `a` by reading `a`. -/
lemma gapSt_eq_of_getLast (M : Mealy A B Q) {u : List A} {a : A} (h : u.getLast? = some a) :
    gapSt M u = (M.step (preSt M u) a).1 := by
  obtain ⟨u', rfl⟩ : ∃ u', u = u' ++ [a] := by
    induction u using List.reverseRecOn with
    | nil => simp at h
    | append_singleton u' b _ =>
        simp only [List.getLast?_concat, Option.some.injEq] at h
        exact ⟨u', by rw [h]⟩
  rw [preSt_concat, gapSt_concat]

lemma gapSt_eq_preSt_of_nil (M : Mealy A B Q) {u : List A} (h : u.getLast? = none) :
    gapSt M u = preSt M u := by
  have : u = [] := List.getLast?_eq_none_iff.mp h
  subst this; rfl

/-- The last letter of the output of the Mealy machine. -/
lemma eval_getLast? (M : Mealy A B Q) (u : List A) :
    (M.eval u).getLast? = u.getLast?.map (fun a => (M.step (preSt M u) a).2) := by
  induction u using List.reverseRecOn with
  | nil => simp [Mealy.eval]
  | append_singleton u' a _ =>
      rw [Mealy.eval_append]
      simp [preSt, Mealy.run]

/-- The output of the Mealy machine on a prefix without its last letter. -/
lemma eval_dropLast (M : Mealy A B Q) (u : List A) :
    (M.eval u).dropLast = M.eval u.dropLast := by
  induction u using List.reverseRecOn with
  | nil => simp [Mealy.eval]
  | append_singleton u' a _ =>
      rw [Mealy.eval_append]
      simp [Mealy.run]

/-- The first letter of a run of the Mealy machine. -/
lemma run_head? (M : Mealy A B Q) (q : Q) (v : List A) :
    (M.run q v).head? = v.head?.map (fun a => (M.step q a).2) := by
  cases v with
  | nil => simp
  | cons a v => simp [Mealy.run]

/-! ## The common part of the two constructions -/

section Precomp

variable (M : Mealy A B Q) (N : TwoWay B C P) {S : Type} (nrm pnd : P → Q → S)

/-- The action of the simulating transducer at a gap whose *pre-state* is `t`:
it computes the two letters of the output of the Mealy machine that are adjacent
to the gap, applies the transition function of `N`, and moves in the same
direction; a step to the left leaves the machine in the pending mode. -/
def actStep (la rb : Option A) (t : Q) (p : P) : List C ⊕ (S × List C × Bool) :=
  match N.step (la.map fun a => (M.step t a).2) p
      (rb.map fun a =>
        (M.step (match la with | none => t | some x => (M.step t x).1) a).2) with
  | Sum.inl o => Sum.inl o
  | Sum.inr (p', o, true) =>
      Sum.inr (nrm p' (match la with | none => t | some x => (M.step t x).1), o, true)
  | Sum.inr (p', o, false) => Sum.inr (pnd p' t, o, false)

/-- The configuration of `N` on the output of `M` that corresponds to the gap
between `u` and `v`. -/
def simCfg (u v : List A) (p : P) : Cfg B P :=
  Cfg.conf (M.eval u) p (M.run (gapSt M u) v)

omit N in
@[simp] lemma simCfg_ne_halt (u v : List A) (p : P) : simCfg M u v p ≠ Cfg.halt := by
  simp [simCfg]

variable {M N nrm pnd} {aut : TwoWay A C S}

/-- The pending mode reaches the halting vertex whenever the normal mode does. -/
lemma pending_reaches
    (hpnd : ∀ (u v : List A) (p : P) (o : List C) (c : Cfg A S),
      aut.stepCfg (Cfg.conf u (nrm p (preSt M u)) v) = some (o, c) →
      aut.Reaches (Cfg.conf u (pnd p (gapSt M u)) v) o c)
    {u v : List A} {p : P} {out : List C}
    (h : aut.Reaches (Cfg.conf u (nrm p (preSt M u)) v) out Cfg.halt) :
    aut.Reaches (Cfg.conf u (pnd p (gapSt M u)) v) out Cfg.halt := by
  cases h with
  | step hs hr => exact (hpnd _ _ _ _ _ hs).trans hr

/-- The simulation: whenever `N` reaches the halting vertex from a configuration
of the form `simCfg`, the simulating transducer reaches the halting vertex from
the corresponding configuration in the normal mode, with the same output. -/
lemma precomp_sim
    (hnrm : ∀ (la rb : Option A) (t : Q) (p : P),
      aut.step la (nrm p t) rb = actStep M N nrm pnd la rb t p)
    (hpnd : ∀ (u v : List A) (p : P) (o : List C) (c : Cfg A S),
      aut.stepCfg (Cfg.conf u (nrm p (preSt M u)) v) = some (o, c) →
      aut.Reaches (Cfg.conf u (pnd p (gapSt M u)) v) o c)
    {cN cE : Cfg B P} {out : List C} (h : N.Reaches cN out cE) :
    ∀ (u v : List A) (p : P), cN = simCfg M u v p → cE = Cfg.halt →
      aut.Reaches (Cfg.conf u (nrm p (preSt M u)) v) out Cfg.halt := by
  induction h with
  | refl c => intro u v p hc hE; exact absurd (hc.symm.trans hE) (by simp)
  | @step c c' c'' o o' hs _ ih =>
      intro u v p hc hE
      subst hc
      subst hE
      -- the letters adjacent to the head, in the input and in the output
      have hlast : (M.eval u).getLast? = u.getLast?.map (fun a => (M.step (preSt M u) a).2) :=
        eval_getLast? M u
      have hhead : (M.run (gapSt M u) v).head? =
          v.head?.map (fun a => (M.step (gapSt M u) a).2) := run_head? M _ v
      have hgap : (match u.getLast? with | none => preSt M u | some x => (M.step (preSt M u) x).1)
          = gapSt M u := by
        cases hu : u.getLast? with
        | none => simpa [hu] using (gapSt_eq_preSt_of_nil M hu).symm
        | some a => simpa [hu] using (gapSt_eq_of_getLast M hu).symm
      have hact : actStep M N nrm pnd u.getLast? v.head? (preSt M u) p =
          match N.step ((M.eval u).getLast?) p ((M.run (gapSt M u) v).head?) with
          | Sum.inl o => Sum.inl o
          | Sum.inr (p', o, true) => Sum.inr (nrm p' (gapSt M u), o, true)
          | Sum.inr (p', o, false) => Sum.inr (pnd p' (preSt M u), o, false) := by
        unfold actStep
        rw [hlast, hhead, hgap]
      rcases hstep : N.step ((M.eval u).getLast?) p ((M.run (gapSt M u) v).head?) with
        oh | ⟨p', o₁, dir⟩
      · -- halting step
        rw [simCfg, TwoWay.stepCfg] at hs
        simp only [hstep] at hs
        have hoh : o = oh ∧ c' = Cfg.halt := by
          simpa [Prod.ext_iff] using hs.symm
        obtain ⟨rfl, rfl⟩ := hoh
        obtain ⟨rfl, -⟩ := TwoWay.reaches_halt ‹N.Reaches Cfg.halt o' Cfg.halt›
        have hstep' : aut.stepCfg (Cfg.conf u (nrm p (preSt M u)) v) = some (o, Cfg.halt) := by
          rw [TwoWay.stepCfg, hnrm, hact, hstep]
        simpa using TwoWay.reaches_one hstep'
      · cases dir with
        | true =>
            -- a step to the right
            rw [simCfg, TwoWay.stepCfg] at hs
            simp only [hstep] at hs
            cases v with
            | nil => simp [Mealy.run] at hs
            | cons a v₁ =>
                rw [show M.run (gapSt M u) (a :: v₁)
                    = (M.step (gapSt M u) a).2 :: M.run (M.step (gapSt M u) a).1 v₁ from rfl] at hs
                have hs' : o = o₁ ∧ c' = Cfg.conf (M.eval u ++ [(M.step (gapSt M u) a).2]) p'
                    (M.run (M.step (gapSt M u) a).1 v₁) := by
                  simpa [Prod.ext_iff] using hs.symm
                obtain ⟨rfl, rfl⟩ := hs'
                have hc'sim : Cfg.conf (M.eval u ++ [(M.step (gapSt M u) a).2]) p'
                    (M.run (M.step (gapSt M u) a).1 v₁) = simCfg M (u ++ [a]) v₁ p' := by
                  rw [simCfg, Mealy.eval_append, gapSt_concat]
                  rfl
                have ihr := ih (u ++ [a]) v₁ p' hc'sim rfl
                rw [preSt_concat] at ihr
                have hstep' : aut.stepCfg (Cfg.conf u (nrm p (preSt M u)) (a :: v₁)) =
                    some (o, Cfg.conf (u ++ [a]) (nrm p' (gapSt M u)) v₁) := by
                  rw [TwoWay.stepCfg, hnrm, hact, hstep]
                exact TwoWay.Reaches.step hstep' ihr
        | false =>
            -- a step to the left
            rw [simCfg, TwoWay.stepCfg] at hs
            simp only [hstep] at hs
            rcases hu : u.getLast? with _ | a
            · rw [hlast, hu] at hs; simp at hs
            · rw [hlast, hu] at hs
              simp only [Option.map_some] at hs
              have hs' : o = o₁ ∧ c' = Cfg.conf (M.eval u).dropLast p'
                  ((M.step (preSt M u) a).2 :: M.run (gapSt M u) v) := by
                simpa [Prod.ext_iff] using hs.symm
              obtain ⟨rfl, rfl⟩ := hs'
              have hpre : gapSt M u.dropLast = preSt M u := rfl
              have hc'sim : Cfg.conf (M.eval u).dropLast p'
                  ((M.step (preSt M u) a).2 :: M.run (gapSt M u) v)
                  = simCfg M u.dropLast (a :: v) p' := by
                rw [simCfg, eval_dropLast, hpre]
                rw [show M.run (preSt M u) (a :: v)
                  = (M.step (preSt M u) a).2 :: M.run (M.step (preSt M u) a).1 v from rfl,
                  ← gapSt_eq_of_getLast M hu]
              have ihr := ih u.dropLast (a :: v) p' hc'sim rfl
              have hstep' : aut.stepCfg (Cfg.conf u (nrm p (preSt M u)) v) =
                  some (o, Cfg.conf u.dropLast (pnd p' (preSt M u)) (a :: v)) := by
                rw [TwoWay.stepCfg, hnrm, hact, hstep]
                simp [hu]
              refine TwoWay.Reaches.step hstep' ?_
              rw [← hpre]
              exact pending_reaches hpnd ihr

/-- The simulating transducer computes the composition. -/
theorem precomp_computes
    (hinit : aut.init = nrm N.init M.init)
    (hnrm : ∀ (la rb : Option A) (t : Q) (p : P),
      aut.step la (nrm p t) rb = actStep M N nrm pnd la rb t p)
    (hpnd : ∀ (u v : List A) (p : P) (o : List C) (c : Cfg A S),
      aut.stepCfg (Cfg.conf u (nrm p (preSt M u)) v) = some (o, c) →
      aut.Reaches (Cfg.conf u (pnd p (gapSt M u)) v) o c)
    {w : List A} {out : List C} (h : N.Computes (M.eval w) out) : aut.Computes w out := by
  have h' : N.Reaches (simCfg M [] w N.init) out Cfg.halt := by
    simpa [simCfg, Mealy.eval] using h
  have := precomp_sim hnrm hpnd h' [] w N.init rfl rfl
  simpa [TwoWay.Computes, hinit] using this

end Precomp

/-! ## Two configurations that differ only in the state -/

lemma stepCfg_congr {A C S : Type} {aut : TwoWay A C S} {u v : List A} {s s' : S}
    (h : aut.step u.getLast? s v.head? = aut.step u.getLast? s' v.head?) :
    aut.stepCfg (Cfg.conf u s v) = aut.stepCfg (Cfg.conf u s' v) := by
  simp only [TwoWay.stepCfg]
  rw [h]

/-- Two configurations that differ only in the state, and whose steps agree,
reach the halting vertex with the same output. -/
lemma reaches_of_stepCfg_eq {A C S : Type} {aut : TwoWay A C S} {u v : List A} {s s' : S}
    {o : List C} (h : aut.stepCfg (Cfg.conf u s v) = aut.stepCfg (Cfg.conf u s' v))
    (hr : aut.Reaches (Cfg.conf u s' v) o Cfg.halt) : aut.Reaches (Cfg.conf u s v) o Cfg.halt := by
  cases hr with
  | step hs hr' => exact TwoWay.Reaches.step (h.trans hs) hr'

/-! ## Reading the input from right to left -/

section Mirror

variable {A C P : Type}

/-- The mirror image of a two-way transducer: it first walks to the right end of
the input, and then simulates the given transducer on the reversed input, with
the two directions exchanged. -/
def mirrorAut (N : TwoWay A C P) : TwoWay A C (P × Bool) where
  init := (N.init, false)
  step := fun la s rb =>
    if s.2 = false ∧ rb ≠ none then Sum.inr ((s.1, false), [], true)
    else
      match N.step rb s.1 la with
      | Sum.inl o => Sum.inl o
      | Sum.inr (p', o, dir) => Sum.inr ((p', true), o, !dir)

/-- The initial walk to the right end of the input. -/
lemma mirror_walk (N : TwoWay A C P) (p : P) :
    ∀ (v u : List A), (mirrorAut N).Reaches (Cfg.conf u (p, false) v) []
      (Cfg.conf (u ++ v) (p, false) []) := by
  intro v
  induction v with
  | nil => intro u; simpa using TwoWay.Reaches.refl (Cfg.conf u (p, false) ([] : List A))
  | cons a v ih =>
      intro u
      have h1 : (mirrorAut N).stepCfg (Cfg.conf u (p, false) (a :: v))
          = some ([], Cfg.conf (u ++ [a]) (p, false) v) := by
        rw [TwoWay.stepCfg]
        simp only [mirrorAut, List.head?_cons, ne_eq, reduceCtorEq, not_false_eq_true, and_self,
          if_pos]
      have := ih (u ++ [a])
      rw [List.append_assoc] at this
      simpa using TwoWay.Reaches.step h1 this

/-- The simulation of the reversed run. -/
lemma mirror_sim {N : TwoWay A C P} {cN cE : Cfg A P} {o : List C}
    (h : N.Reaches cN o cE) :
    ∀ (u v : List A) (p : P), cN = Cfg.conf v.reverse p u.reverse → cE = Cfg.halt →
      (mirrorAut N).Reaches (Cfg.conf u (p, true) v) o Cfg.halt := by
  induction h with
  | refl c => intro u v p hc hE; exact absurd (hc.symm.trans hE) (by simp)
  | @step c c' c'' o o' hs _ ih =>
      intro u v p hc hE
      subst hc
      subst hE
      have hl : (v.reverse).getLast? = v.head? := by
        rw [List.getLast?_reverse]
      have hr : (u.reverse).head? = u.getLast? := by
        rw [← List.getLast?_reverse, List.reverse_reverse]
      rcases hstep : N.step v.head? p u.getLast? with oh | ⟨p', o₁, dir⟩
      · rw [TwoWay.stepCfg] at hs
        rw [hl, hr, hstep] at hs
        have hs' : o = oh ∧ c' = Cfg.halt := by simpa [Prod.ext_iff] using hs.symm
        obtain ⟨rfl, rfl⟩ := hs'
        obtain ⟨rfl, -⟩ := TwoWay.reaches_halt ‹N.Reaches Cfg.halt o' Cfg.halt›
        have hstep' : (mirrorAut N).stepCfg (Cfg.conf u (p, true) v) = some (o, Cfg.halt) := by
          rw [TwoWay.stepCfg]
          simp [mirrorAut, hstep]
        simpa using TwoWay.reaches_one hstep'
      · cases dir with
        | true =>
            rw [TwoWay.stepCfg] at hs
            rw [hl, hr, hstep] at hs
            rcases hu : u.reverse with _ | ⟨a, t⟩
            · rw [hu] at hs; simp at hs
            · rw [hu] at hs
              have hs' : o = o₁ ∧ c' = Cfg.conf (v.reverse ++ [a]) p' t := by
                simpa [Prod.ext_iff] using hs.symm
              obtain ⟨rfl, rfl⟩ := hs'
              have hua : u = t.reverse ++ [a] := by
                have := congrArg List.reverse hu
                simpa using this
              have hlast : u.getLast? = some a := by rw [hua]; simp
              have hdrop : u.dropLast = t.reverse := by rw [hua]; simp
              have hc'eq : Cfg.conf (v.reverse ++ [a]) p' t
                  = Cfg.conf ((a :: v).reverse) p' ((u.dropLast).reverse) := by
                rw [hdrop]; simp
              have ihr := ih u.dropLast (a :: v) p' hc'eq rfl
              have hstep' : (mirrorAut N).stepCfg (Cfg.conf u (p, true) v)
                  = some (o, Cfg.conf u.dropLast (p', true) (a :: v)) := by
                have hs2 : N.step v.head? p (some a) = Sum.inr (p', o, true) := by
                  rw [← hlast]; exact hstep
                rw [TwoWay.stepCfg]
                simp [mirrorAut, hlast, hs2]
              exact TwoWay.Reaches.step hstep' ihr
        | false =>
            rw [TwoWay.stepCfg] at hs
            rw [hl, hr, hstep] at hs
            rcases hv : v with _ | ⟨a, v'⟩
            · rw [hv] at hs; simp at hs
            · rw [hv] at hs
              simp only [List.head?_cons] at hs
              have hs' : o = o₁ ∧ c' = Cfg.conf ((a :: v').reverse).dropLast p'
                  (a :: u.reverse) := by
                simpa [Prod.ext_iff] using hs.symm
              obtain ⟨rfl, rfl⟩ := hs'
              have hc'eq : Cfg.conf ((a :: v').reverse).dropLast p' (a :: u.reverse)
                  = Cfg.conf (v'.reverse) p' ((u ++ [a]).reverse) := by
                simp
              have ihr := ih (u ++ [a]) v' p' hc'eq rfl
              have hstep' : (mirrorAut N).stepCfg (Cfg.conf u (p, true) (a :: v'))
                  = some (o, Cfg.conf (u ++ [a]) (p', true) v') := by
                rw [TwoWay.stepCfg]
                rw [hv] at hstep
                simp only [List.head?_cons] at hstep
                simp [mirrorAut, hstep]
              exact TwoWay.Reaches.step hstep' ihr

/-- The mirror transducer computes the given function on the reversed input. -/
lemma mirror_computes {N : TwoWay A C P} {g : List A → List C} (hN : ∀ v, N.Computes v (g v))
    (w : List A) : (mirrorAut N).Computes w (g w.reverse) := by
  have hsim : (mirrorAut N).Reaches (Cfg.conf w (N.init, true) []) (g w.reverse) Cfg.halt := by
    refine mirror_sim (hN w.reverse) w [] N.init ?_ rfl
    simp
  have hflag : (mirrorAut N).Reaches (Cfg.conf w (N.init, false) []) (g w.reverse) Cfg.halt := by
    refine reaches_of_stepCfg_eq ?_ hsim
    refine stepCfg_congr ?_
    simp only [mirrorAut, List.head?_nil, ne_eq, not_true_eq_false, and_false]
  have := (mirror_walk N N.init w []).trans hflag
  simpa [TwoWay.Computes, mirrorAut] using this

/-- Two-way transducers are closed under pre-composition with reversal. -/
lemma isTwoWay_comp_reverse {g : List A → List C} (hg : IsTwoWay g) :
    IsTwoWay (fun w => g w.reverse) := by
  obtain ⟨P, hP, N, hN⟩ := hg
  haveI := hP
  exact ⟨P × Bool, inferInstance, mirrorAut N, fun w => mirror_computes hN w⟩

end Mirror

/-! ## Reversible Mealy machines -/

section Reversible

variable {A B C Q P : Type}

/-- The inverse of the state transformation of a letter, for a reversible Mealy
machine. -/
noncomputable def revBack (M : Mealy A B Q) (a : A) (q : Q) : Q :=
  @Function.invFun Q Q ⟨M.init⟩ (M.letterTrans a) q

lemma revBack_apply {M : Mealy A B Q} (hM : M.Reversible) (a : A) (q : Q) :
    revBack M a (M.letterTrans a q) = q :=
  @Function.leftInverse_invFun Q Q ⟨M.init⟩ _ (hM a).injective q

/-- The two-way transducer simulating `N` on the output of a reversible Mealy
machine `M`: in the pending mode the stored state is the one of the current
gap, from which the state before the letter to the left is recovered by
inverting the state transformation of that letter. -/
noncomputable def revAut (M : Mealy A B Q) (N : TwoWay B C P) :
    TwoWay A C (P × Q × Bool) where
  init := (N.init, M.init, true)
  step := fun la s rb =>
    let nrm : P → Q → P × Q × Bool := fun p t => (p, t, true)
    let pnd : P → Q → P × Q × Bool := fun p t => (p, t, false)
    if s.2.2 then actStep M N nrm pnd la rb s.2.1 s.1
    else
      match la with
      | none => actStep M N nrm pnd la rb s.2.1 s.1
      | some b => actStep M N nrm pnd la rb (revBack M b s.2.1) s.1

/-- A two-way transducer pre-composed with a reversible Mealy machine. -/
theorem isTwoWay_comp_reversible [Finite Q] [Finite P] {M : Mealy A B Q}
    (hM : M.Reversible) {N : TwoWay B C P} {g : List B → List C}
    (hN : ∀ v, N.Computes v (g v)) :
    ∀ w, (revAut M N).Computes w (g (M.eval w)) := by
  intro w
  refine precomp_computes (nrm := fun p t => (p, t, true)) (pnd := fun p t => (p, t, false))
    rfl (fun la rb t p => rfl) ?_ (hN (M.eval w))
  intro u v p o c hs
  refine TwoWay.reaches_one ?_
  rw [← hs]
  refine stepCfg_congr ?_
  cases hu : u.getLast? with
  | none =>
      have hg : gapSt M u = preSt M u := gapSt_eq_preSt_of_nil M hu
      simp [revAut, hg]
  | some b =>
      have hg : gapSt M u = M.letterTrans b (preSt M u) := gapSt_eq_of_getLast M hu
      simp [revAut, hg, revBack_apply hM]

end Reversible

/-! ## Flip-flop Mealy machines -/

/-- The four modes of the transducer simulating a two-way transducer on the
output of a flip-flop Mealy machine. -/
inductive PMode : Type
  /-- The stored Mealy state is the one before the letter to the left. -/
  | normal : PMode
  /-- The stored Mealy state is the one of the current gap. -/
  | pending : PMode
  /-- Looking for the previous resetting letter. -/
  | scanL : PMode
  /-- Returning to the place where the scan started. -/
  | scanR : PMode
  deriving DecidableEq, Fintype

section FlipFlop

variable {A B C Q P : Type}

open scoped Classical in
/-- The value to which a resetting letter sets the state. -/
noncomputable def resetVal (M : Mealy A B Q) (a : A) : Q :=
  if h : ∃ q₀ : Q, ∀ q : Q, M.letterTrans a q = q₀ then h.choose else M.init

lemma letterTrans_eq_resetVal {M : Mealy A B Q} (hM : M.FlipFlop) {a : A}
    (ha : M.letterTrans a ≠ id) (q : Q) : M.letterTrans a q = resetVal M a := by
  have h : ∃ q₀ : Q, ∀ q : Q, M.letterTrans a q = q₀ := by
    rcases hM a with h | h
    · exact absurd h ha
    · exact h
  rw [resetVal, dif_pos h]
  exact h.choose_spec q

/-- Reading letters whose state transformation is the identity does not change
the state. -/
lemma gapSt_append_id {M : Mealy A B Q} {l : List A} (hl : ∀ y ∈ l, M.letterTrans y = id)
    (x : List A) : gapSt M (x ++ l) = gapSt M x := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih =>
      have hy : M.letterTrans y = id := hl y (by simp)
      have := ih (fun z hz => hl z (by simp [hz])) (x ++ [y])
      rw [show x ++ y :: l = (x ++ [y]) ++ l by simp] at *
      rw [this, gapSt_concat]
      have : (M.step (gapSt M x) y).1 = M.letterTrans y (gapSt M x) := rfl
      rw [this, hy]
      rfl

open scoped Classical in
/-- The two-way transducer simulating `N` on the output of a flip-flop Mealy
machine `M`. -/
noncomputable def ffAut (M : Mealy A B Q) (N : TwoWay B C P) :
    TwoWay A C (P × Q × PMode) where
  init := (N.init, M.init, PMode.normal)
  step := fun la s rb =>
    let nrm : P → Q → P × Q × PMode := fun p t => (p, t, PMode.normal)
    let pnd : P → Q → P × Q × PMode := fun p t => (p, t, PMode.pending)
    match s.2.2 with
    | PMode.normal => actStep M N nrm pnd la rb s.2.1 s.1
    | PMode.pending =>
        match la with
        | none => actStep M N nrm pnd la rb s.2.1 s.1
        | some b =>
            if M.letterTrans b = id then actStep M N nrm pnd la rb s.2.1 s.1
            else Sum.inr ((s.1, s.2.1, PMode.scanL), [], false)
    | PMode.scanL =>
        match la with
        | none => Sum.inr ((s.1, M.init, PMode.scanR), [], true)
        | some b =>
            if M.letterTrans b = id then Sum.inr ((s.1, s.2.1, PMode.scanL), [], false)
            else Sum.inr ((s.1, resetVal M b, PMode.scanR), [], true)
    | PMode.scanR =>
        match la with
        | none => Sum.inl []
        | some b =>
            if M.letterTrans b = id then Sum.inr ((s.1, s.2.1, PMode.scanR), [], true)
            else actStep M N nrm pnd la rb s.2.1 s.1

/-! ### The subroutine looking for the previous resetting letter -/

variable {M : Mealy A B Q} {N : TwoWay B C P}

/-- The way back: the head moves to the right until the letter it has just
crossed is a resetting one, which happens exactly at the gap where the
subroutine was started. -/
lemma ffAut_scanR {p : P} {b : A} (hb : M.letterTrans b ≠ id) {v : List A}
    {o : List C} {c : Cfg A (P × Q × PMode)} :
    ∀ (rest pre : List A) (z : A), M.letterTrans z = id →
      (∀ y ∈ rest, M.letterTrans y = id) →
      (ffAut M N).stepCfg (Cfg.conf (pre ++ [z] ++ rest ++ [b])
          (p, preSt M (pre ++ [z] ++ rest ++ [b]), PMode.normal) v) = some (o, c) →
      (ffAut M N).Reaches
        (Cfg.conf (pre ++ [z]) (p, gapSt M (pre ++ [z]), PMode.scanR) (rest ++ [b] ++ v)) o c := by
  intro rest
  induction rest with
  | nil =>
      intro pre z hz _ hs
      simp only [List.append_nil] at hs
      have hlast : (pre ++ [z]).getLast? = some z := by simp
      have h1 : (ffAut M N).stepCfg
          (Cfg.conf (pre ++ [z]) (p, gapSt M (pre ++ [z]), PMode.scanR) ([] ++ [b] ++ v))
          = some ([], Cfg.conf (pre ++ [z] ++ [b]) (p, gapSt M (pre ++ [z]), PMode.scanR) v) := by
        simp only [List.nil_append, List.cons_append]
        rw [TwoWay.stepCfg]
        simp [ffAut, hlast, hz]
      have h2 : (ffAut M N).stepCfg
          (Cfg.conf (pre ++ [z] ++ [b]) (p, gapSt M (pre ++ [z]), PMode.scanR) v) = some (o, c) := by
        rw [← hs]
        have hpre : preSt M (pre ++ [z, b]) = gapSt M (pre ++ [z]) := by
          rw [show pre ++ [z, b] = pre ++ [z] ++ [b] by simp]
          exact preSt_concat M _ b
        refine stepCfg_congr ?_
        simp [ffAut, hb, hpre]
      simpa using TwoWay.Reaches.step h1 (TwoWay.Reaches.step h2 (TwoWay.Reaches.refl c))
  | cons y rest ih =>
      intro pre z hz hrest hs
      have hy : M.letterTrans y = id := hrest y (by simp)
      have hlast : (pre ++ [z]).getLast? = some z := by simp
      have h1 : (ffAut M N).stepCfg
          (Cfg.conf (pre ++ [z]) (p, gapSt M (pre ++ [z]), PMode.scanR) (y :: rest ++ [b] ++ v))
          = some ([], Cfg.conf (pre ++ [z] ++ [y]) (p, gapSt M (pre ++ [z]), PMode.scanR)
              (rest ++ [b] ++ v)) := by
        rw [TwoWay.stepCfg]
        simp [ffAut, hlast, hz]
      have hgap : gapSt M (pre ++ [z] ++ [y]) = gapSt M (pre ++ [z]) := by
        rw [gapSt_concat]
        show M.letterTrans y (gapSt M (pre ++ [z])) = _
        rw [hy]; rfl
      have hs' : (ffAut M N).stepCfg (Cfg.conf (pre ++ [z] ++ [y] ++ rest ++ [b])
          (p, preSt M (pre ++ [z] ++ [y] ++ rest ++ [b]), PMode.normal) v) = some (o, c) := by
        have : pre ++ [z] ++ [y] ++ rest ++ [b] = pre ++ [z] ++ (y :: rest) ++ [b] := by simp
        rw [this]; exact hs
      have := ih (pre ++ [z]) y hy (fun w hw => hrest w (by simp [hw])) hs'
      rw [hgap] at this
      simpa using TwoWay.Reaches.step h1 this

/-- Entering the way back: the head crosses the first letter to its right, and
then follows `ffAut_scanR`. -/
lemma ffAut_scanR_start {p : P} {b : A} (hb : M.letterTrans b ≠ id)
    {v : List A} {o : List C} {c : Cfg A (P × Q × PMode)} (pre mid : List A)
    (hmid : ∀ y ∈ mid, M.letterTrans y = id)
    (hs : (ffAut M N).stepCfg (Cfg.conf (pre ++ mid ++ [b])
      (p, preSt M (pre ++ mid ++ [b]), PMode.normal) v) = some (o, c))
    (s : P × Q × PMode)
    (hstep : (ffAut M N).step pre.getLast? s (mid ++ [b] ++ v).head?
      = Sum.inr ((p, gapSt M pre, PMode.scanR), [], true)) :
    (ffAut M N).Reaches (Cfg.conf pre s (mid ++ [b] ++ v)) o c := by
  cases mid with
  | nil =>
      have h1 : (ffAut M N).stepCfg (Cfg.conf pre s ([] ++ [b] ++ v))
          = some ([], Cfg.conf (pre ++ [b]) (p, gapSt M pre, PMode.scanR) v) := by
        rw [TwoWay.stepCfg]
        simp only [List.nil_append, List.cons_append] at hstep ⊢
        rw [hstep]
      have h2 : (ffAut M N).stepCfg (Cfg.conf (pre ++ [b]) (p, gapSt M pre, PMode.scanR) v)
          = some (o, c) := by
        rw [← (by simpa using hs : (ffAut M N).stepCfg (Cfg.conf (pre ++ [b])
          (p, preSt M (pre ++ [b]), PMode.normal) v) = some (o, c))]
        refine stepCfg_congr ?_
        simp [ffAut, hb, preSt_concat]
      simpa using TwoWay.Reaches.step h1 (TwoWay.Reaches.step h2 (TwoWay.Reaches.refl c))
  | cons y mid =>
      have hy : M.letterTrans y = id := hmid y (by simp)
      have h1 : (ffAut M N).stepCfg (Cfg.conf pre s (y :: mid ++ [b] ++ v))
          = some ([], Cfg.conf (pre ++ [y]) (p, gapSt M pre, PMode.scanR) (mid ++ [b] ++ v)) := by
        rw [TwoWay.stepCfg]
        simp only [List.cons_append] at hstep ⊢
        rw [hstep]
      have hgap : gapSt M (pre ++ [y]) = gapSt M pre := by
        rw [gapSt_concat]
        show M.letterTrans y (gapSt M pre) = _
        rw [hy]; rfl
      have hs' : (ffAut M N).stepCfg (Cfg.conf (pre ++ [y] ++ mid ++ [b])
          (p, preSt M (pre ++ [y] ++ mid ++ [b]), PMode.normal) v) = some (o, c) := by
        have : pre ++ [y] ++ mid ++ [b] = pre ++ (y :: mid) ++ [b] := by simp
        rw [this]; exact hs
      have := ffAut_scanR hb mid pre y hy (fun w hw => hmid w (by simp [hw])) hs'
      rw [hgap] at this
      simpa using TwoWay.Reaches.step h1 this

/-- The subroutine looking for the previous resetting letter: the head moves to
the left until it finds a resetting letter (or the beginning of the input),
which gives the state of the Mealy machine at the gap where the subroutine was
started, and then returns there. -/
lemma ffAut_scanL (hM : M.FlipFlop) {p : P} {b : A} (hb : M.letterTrans b ≠ id) {v : List A}
    {o : List C} {c : Cfg A (P × Q × PMode)} :
    ∀ (pre mid : List A) (x : Q), (∀ y ∈ mid, M.letterTrans y = id) →
      (ffAut M N).stepCfg (Cfg.conf (pre ++ mid ++ [b])
        (p, preSt M (pre ++ mid ++ [b]), PMode.normal) v) = some (o, c) →
      (ffAut M N).Reaches (Cfg.conf pre (p, x, PMode.scanL) (mid ++ [b] ++ v)) o c := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
      intro mid x hmid hs
      refine ffAut_scanR_start hb [] mid hmid hs _ ?_
      simp only [List.getLast?_nil, ffAut]
      rfl
  | append_singleton pre a ih =>
      intro mid x hmid hs
      by_cases ha : M.letterTrans a = id
      · have h1 : (ffAut M N).stepCfg
            (Cfg.conf (pre ++ [a]) (p, x, PMode.scanL) (mid ++ [b] ++ v))
            = some ([], Cfg.conf pre (p, x, PMode.scanL) (a :: (mid ++ [b] ++ v))) := by
          rw [TwoWay.stepCfg]
          simp only [List.getLast?_concat, ffAut, ha, if_pos]
          simp
        have hs' : (ffAut M N).stepCfg (Cfg.conf (pre ++ (a :: mid) ++ [b])
            (p, preSt M (pre ++ (a :: mid) ++ [b]), PMode.normal) v) = some (o, c) := by
          have : pre ++ (a :: mid) ++ [b] = pre ++ [a] ++ mid ++ [b] := by simp
          rw [this]; exact hs
        have hmid' : ∀ y ∈ a :: mid, M.letterTrans y = id := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ha
          · exact hmid y hy
        have := ih (a :: mid) x hmid' hs'
        simp only [List.cons_append] at this
        simpa using TwoWay.Reaches.step h1 this
      · have hgap : gapSt M (pre ++ [a]) = resetVal M a := by
          rw [gapSt_concat]
          show M.letterTrans a (gapSt M pre) = _
          exact letterTrans_eq_resetVal hM ha _
        refine ffAut_scanR_start hb (pre ++ [a]) mid hmid hs _ ?_
        simp [ffAut, ha, hgap]

/-! ### The transducer for a flip-flop Mealy machine -/

/-- A two-way transducer pre-composed with a flip-flop Mealy machine. -/
theorem isTwoWay_comp_flipFlop [Finite Q] [Finite P] (hM : M.FlipFlop)
    {g : List B → List C} (hN : ∀ v, N.Computes v (g v)) :
    ∀ w, (ffAut M N).Computes w (g (M.eval w)) := by
  intro w
  refine precomp_computes (nrm := fun p t => (p, t, PMode.normal))
    (pnd := fun p t => (p, t, PMode.pending)) rfl (fun la rb t p => rfl) ?_ (hN (M.eval w))
  intro u v p o c hs
  cases hu : u.getLast? with
  | none =>
      refine TwoWay.reaches_one ?_
      rw [← hs]
      refine stepCfg_congr ?_
      have hg : gapSt M u = preSt M u := gapSt_eq_preSt_of_nil M hu
      simp only [hu, ffAut, hg]
  | some b =>
      have hub : u.dropLast ++ [b] = u := List.dropLast_append_getLast? _ hu
      by_cases hb : M.letterTrans b = id
      · refine TwoWay.reaches_one ?_
        rw [← hs]
        refine stepCfg_congr ?_
        have hg : gapSt M u = preSt M u := by
          rw [gapSt_eq_of_getLast M hu]
          show M.letterTrans b (preSt M u) = preSt M u
          rw [hb]; rfl
        simp only [hu, ffAut, hb, if_pos, hg]
      · have h1 : (ffAut M N).stepCfg (Cfg.conf u (p, gapSt M u, PMode.pending) v)
            = some ([], Cfg.conf u.dropLast (p, gapSt M u, PMode.scanL) (b :: v)) := by
          rw [TwoWay.stepCfg]
          simp [hu, ffAut, hb]
        have hs' : (ffAut M N).stepCfg (Cfg.conf (u.dropLast ++ [] ++ [b])
            (p, preSt M (u.dropLast ++ [] ++ [b]), PMode.normal) v) = some (o, c) := by
          simpa [hub] using hs
        have := ffAut_scanL hM hb u.dropLast [] (gapSt M u) (by simp) hs'
        simp only [List.nil_append] at this
        simpa using TwoWay.Reaches.step h1 this

end FlipFlop

/-! ## Pre-composition with a Mealy machine -/

/-- Pre-composition of a two-way transducer with a prime Mealy machine. -/
lemma isTwoWay_comp_prime {A B C : Type} {f : List A → List B} (hf : PrimeMealyFam A B f)
    {g : List B → List C} (hg : IsTwoWay g) : IsTwoWay (g ∘ f) := by
  obtain ⟨P, hP, N, hN⟩ := hg
  haveI := hP
  rcases hf with ⟨Q, hQ, M, rfl, hMr⟩ | ⟨Q, hQ, M, rfl, hMf⟩
  · haveI := hQ
    exact ⟨P × Q × Bool, inferInstance, revAut M N,
      fun w => isTwoWay_comp_reversible hMr hN w⟩
  · haveI := hQ
    exact ⟨P × Q × PMode, inferInstance, ffAut M N,
      fun w => isTwoWay_comp_flipFlop hMf hN w⟩

/-- Pre-composition of a two-way transducer with a composition of prime Mealy
machines. -/
lemma isTwoWay_comp_compClosure {A B : Type} {f : List A → List B}
    (hf : CompClosure PrimeMealyFam A B f) :
    ∀ {C : Type} {g : List B → List C}, IsTwoWay g → IsTwoWay (g ∘ f) := by
  induction hf with
  | base h => exact fun hg => isTwoWay_comp_prime h hg
  | id A => exact fun hg => by simpa using hg
  | comp _ _ ih₁ ih₂ =>
      intro C g hg
      have : IsTwoWay ((g ∘ _) ∘ _) := ih₁ (ih₂ hg)
      simpa [Function.comp_assoc] using this

end Lax916827Proofs.Transducers
