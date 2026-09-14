/-
Probing the run of a two-way transducer with a two-way automaton.

This file is part of the proof of Theorem `thm:logic-regular-functions` of *Transducers*
(M. Bojańczyk).  For the inclusion "regular ⊆ mso transductions" one has to say,
in monadic second-order logic, things such as

  "the run of the two-way transducer `M` visits the state `q` at the position
  `x`", or "it visits `(q, x)` before it visits `(q', y)`",

where `x` and `y` are positions marked in the input string.  All these
properties are properties of the marked input string that a *deterministic
two-way automaton* can check, simply by simulating the run of `M`: it stops at
the first configuration satisfying a trigger condition and answers there.  By
Shepherdson's Theorem (`TwoDFA.accepts_isRegular`) the resulting language is
regular, and Theorem `thm:mso-logic-languages` then turns it into a formula.

The alphabet of the automaton is an arbitrary alphabet `A'` mapped to the
alphabet `A` of the transducer by a letter-to-letter projection `π` (in the
application, `A'` is the doubly marked alphabet and `π` forgets the marks); the
trigger and the answer may look at the marks, that is, at the two letters of
`A'` adjacent to the head, and at the state.
-/
import Lax916827Proofs.Source.PartC.TwoWayRun
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- The run of `M` on `w` is, at time `t`, in the state `q` with the head at the
position `p` (that is, with `p` letters to the left of the head). -/
def RunAt (M : TwoWay A B Q) (w : List A) (q : Q) (p t : ℕ) : Prop :=
  ∃ x y, cfgAt M w t = some (Cfg.conf x q y) ∧ x.length = p

lemma runAt_zero (M : TwoWay A B Q) (w : List A) : RunAt M w M.init 0 0 :=
  ⟨[], w, rfl, rfl⟩

lemma RunAt.le_length {M : TwoWay A B Q} {w : List A} {q : Q} {p t : ℕ}
    (h : RunAt M w q p t) : p ≤ w.length := by
  obtain ⟨x, y, hc, rfl⟩ := h
  have := cfgAt_append M w t hc
  rw [← this, List.length_append]
  omega

lemma RunAt.take_drop {M : TwoWay A B Q} {w : List A} {q : Q} {p t : ℕ}
    (h : RunAt M w q p t) : cfgAt M w t = some (Cfg.conf (w.take p) q (w.drop p)) := by
  obtain ⟨x, y, hc, rfl⟩ := h
  have happ := cfgAt_append M w t hc
  have h1 : w.take x.length = x := by rw [← happ, List.take_left]
  have h2 : w.drop x.length = y := by rw [← happ, List.drop_left]
  rw [h1, h2]
  exact hc

/-- The state and the position at a given time are unique. -/
lemma RunAt.unique {M : TwoWay A B Q} {w : List A} {q q' : Q} {p p' t : ℕ}
    (h : RunAt M w q p t) (h' : RunAt M w q' p' t) : q = q' ∧ p = p' := by
  obtain ⟨x, y, hc, rfl⟩ := h
  obtain ⟨x', y', hc', rfl⟩ := h'
  rw [hc] at hc'
  simp only [Option.some.injEq, Cfg.conf.injEq] at hc'
  exact ⟨hc'.2.1, by rw [hc'.1]⟩

/-- If the run halts, a configuration `(q, p)` is visited at most once. -/
lemma RunAt.time_unique {M : TwoWay A B Q} {w : List A} {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) {q : Q} {p t t' : ℕ}
    (h : RunAt M w q p t) (h' : RunAt M w q p t') : t = t' :=
  run_inj M w hT h.take_drop h'.take_drop

end TwoWay

namespace RunProbe

open TwoWay

variable {A A' B Q : Type}

/-- The letter to the left of the head at the position `p`. -/
def leftLet (u : List A') (p : ℕ) : Option A' := if p = 0 then none else u[p - 1]?

lemma getLast?_take (u : List A') {p : ℕ} (hp : p ≤ u.length) :
    (u.take p).getLast? = leftLet u p := by
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · simp [leftLet]
  · have hlen : (u.take p).length = p := by rw [List.length_take]; omega
    rw [List.getLast?_eq_getElem?, hlen, leftLet, if_neg (by omega),
      List.getElem?_take, if_pos (by omega)]

lemma head?_drop (u : List A') (p : ℕ) : (u.drop p).head? = u[p]? := by
  rw [List.head?_drop]

lemma map_leftLet (π : A' → A) (u : List A') (p : ℕ) :
    (leftLet u p).map π = leftLet (u.map π) p := by
  rw [leftLet, leftLet]
  split
  · rfl
  · rw [List.getElem?_map]

lemma map_take (π : A' → A) (u : List A') (p : ℕ) :
    (u.map π).take p = (u.take p).map π := by
  rw [List.map_take]

lemma map_drop (π : A' → A) (u : List A') (p : ℕ) :
    (u.map π).drop p = (u.drop p).map π := by
  rw [List.map_drop]

/-- The two-way automaton that simulates the run of `M` on the projection of its
input, and stops at the first configuration where the trigger holds, answering
there according to `ans`.  If the run of `M` halts or gets stuck before any
trigger, the automaton rejects. -/
def probeAut (M : TwoWay A B Q) (π : A' → A) (Trig ans : Option A' → Q → Option A' → Bool) :
    TwoDFA A' Q where
  init := M.init
  step := fun l q r =>
    if Trig l q r then Sum.inl (ans l q r)
    else
      match M.step (l.map π) q (r.map π) with
      | Sum.inl _ => Sum.inl false
      | Sum.inr (q', _, dir) => Sum.inr (q', dir)

variable (M : TwoWay A B Q) (π : A' → A) (Trig ans : Option A' → Q → Option A' → Bool)

/-- One step of the probing automaton, unfolded. -/
lemma next_unfold (u : List A') (p : ℕ) (q : Q) :
    (probeAut M π Trig ans).next u (Sum.inl (p, q)) =
      (match (probeAut M π Trig ans).step (leftLet u p) q u[p]? with
        | Sum.inl b => Sum.inr b
        | Sum.inr (r', true) => if p < u.length then Sum.inl (p + 1, r') else Sum.inr false
        | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false) := rfl

/-- One step of the probing automaton at a triggering configuration. -/
lemma next_of_trig (u : List A') (p : ℕ) (q : Q)
    (htrig : Trig (leftLet u p) q u[p]? = true) :
    (probeAut M π Trig ans).next u (Sum.inl (p, q)) = Sum.inr (ans (leftLet u p) q u[p]?) := by
  rw [next_unfold]
  show (match (if Trig (leftLet u p) q u[p]? then Sum.inl (ans (leftLet u p) q u[p]?)
      else (match M.step ((leftLet u p).map π) q ((u[p]?).map π) with
        | Sum.inl _ => Sum.inl false
        | Sum.inr (q', _, dir) => Sum.inr (q', dir)) : Bool ⊕ (Q × Bool)) with
    | Sum.inl b => Sum.inr b
    | Sum.inr (r', true) => if p < u.length then Sum.inl (p + 1, r') else Sum.inr false
    | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false) = _
  rw [if_pos htrig]

/-- The trigger holds at the time `t` of the run on the projected input. -/
def TrigAt (u : List A') (t : ℕ) : Prop :=
  ∃ q p, RunAt M (u.map π) q p t ∧ Trig (leftLet u p) q u[p]? = true

/-- The answer given at the time `t` of the run on the projected input. -/
def AnsAt (u : List A') (t : ℕ) : Prop :=
  ∃ q p, RunAt M (u.map π) q p t ∧ ans (leftLet u p) q u[p]? = true

lemma trig_letters {u : List A'} {q : Q} {p t : ℕ} (h : RunAt M (u.map π) q p t) :
    ((u.map π).take p).getLast? = (leftLet u p).map π ∧
      ((u.map π).drop p).head? = (u[p]?).map π := by
  have hp : p ≤ u.length := by
    have := h.le_length
    simpa using this
  constructor
  · rw [map_take, List.getLast?_map, getLast?_take u hp]
  · rw [map_drop, List.head?_map, head?_drop]

/-- One step of the probing automaton, at a configuration where the trigger does
not hold: it follows the run of `M`, and rejects if the run halts or gets
stuck. -/
lemma next_of_runAt {u : List A'} {q : Q} {p t : ℕ}
    (hrun : RunAt M (u.map π) q p t) (hnt : ¬ TrigAt M π Trig u t) :
    (∃ q' p', RunAt M (u.map π) q' p' (t + 1) ∧
        (probeAut M π Trig ans).next u (Sum.inl (p, q)) = Sum.inl (p', q')) ∨
      ((∀ q' p', ¬ RunAt M (u.map π) q' p' (t + 1)) ∧
        (probeAut M π Trig ans).next u (Sum.inl (p, q)) = Sum.inr false) := by
  classical
  have hTrig : Trig (leftLet u p) q u[p]? = false := by
    by_contra hcon
    exact hnt ⟨q, p, hrun, by simpa using hcon⟩
  have hulen : (u.map π).length = u.length := List.length_map ..
  have hple : p ≤ u.length := by rw [← hulen]; exact hrun.le_length
  obtain ⟨hstepArg, hstepArg'⟩ := trig_letters M π hrun
  have hcfg := hrun.take_drop
  have hlenp : ((u.map π).take p).length = p := by rw [List.length_take]; omega
  -- unfold one step of the automaton
  have hnext : (probeAut M π Trig ans).next u (Sum.inl (p, q)) =
      (match M.step ((leftLet u p).map π) q ((u[p]?).map π) with
        | Sum.inl _ => Sum.inr false
        | Sum.inr (q', _, true) => if p < u.length then Sum.inl (p + 1, q') else Sum.inr false
        | Sum.inr (q', _, false) => if 0 < p then Sum.inl (p - 1, q') else Sum.inr false) := by
    rw [next_unfold]
    show (match (if Trig (leftLet u p) q u[p]? then Sum.inl (ans (leftLet u p) q u[p]?)
        else (match M.step ((leftLet u p).map π) q ((u[p]?).map π) with
          | Sum.inl _ => Sum.inl false
          | Sum.inr (q', _, dir) => Sum.inr (q', dir)) : Bool ⊕ (Q × Bool)) with
      | Sum.inl b => Sum.inr b
      | Sum.inr (r', true) => if p < u.length then Sum.inl (p + 1, r') else Sum.inr false
      | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false) = _
    rw [hTrig]
    simp only [Bool.false_eq_true, if_false]
    rcases hs : M.step ((leftLet u p).map π) q ((u[p]?).map π) with o | ⟨q', o, dir⟩
    · simp
    · rcases dir with _ | _ <;> simp
  rw [hnext]
  rcases hs : M.step ((leftLet u p).map π) q ((u[p]?).map π) with o | ⟨q', o, dir⟩
  · -- the transducer halts
    right
    have hstep : M.stepCfg (Cfg.conf ((u.map π).take p) q ((u.map π).drop p)) =
        some (o, Cfg.halt) := by
      refine stepCfg_halt_eq _ ?_
      rw [hstepArg, hstepArg']
      exact hs
    have hnextc : cfgAt M (u.map π) (t + 1) = some Cfg.halt :=
      cfgAt_succ_of_step M (u.map π) hcfg hstep
    refine ⟨?_, by simp⟩
    rintro q' p' ⟨x, y, hc, -⟩
    rw [hnextc] at hc
    simp at hc
  · rcases dir with _ | _
    · -- moving left
      rcases Nat.eq_zero_or_pos p with rfl | hpos
      · right
        have hgl : ((u.map π).take 0).getLast? = none := by simp
        have hstep : M.stepCfg (Cfg.conf ((u.map π).take 0) q ((u.map π).drop 0)) = none := by
          refine stepCfg_left_none (q' := q') (o := o) _ hgl ?_
          rw [hstepArg, hstepArg']
          exact hs
        have hnone : cfgAt M (u.map π) (t + 1) = none := by
          rw [cfgAt_succ, hcfg, Option.bind_some, hstep]
          rfl
        refine ⟨?_, by simp⟩
        rintro q'' p'' ⟨x, y, hc, -⟩
        rw [hnone] at hc
        simp at hc
      · left
        have hne : leftLet u p ≠ none := by
          rw [leftLet, if_neg (by omega), ne_eq, List.getElem?_eq_none_iff]
          omega
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
        have hgl : ((u.map π).take p).getLast? = some (π a) := by rw [hstepArg, ha]; rfl
        have hstep : M.stepCfg (Cfg.conf ((u.map π).take p) q ((u.map π).drop p)) =
            some (o, Cfg.conf ((u.map π).take p).dropLast q' (π a :: (u.map π).drop p)) := by
          refine stepCfg_left_some _ hgl ?_
          rw [hstepArg, hstepArg']
          exact hs
        have hnextc := cfgAt_succ_of_step M (u.map π) hcfg hstep
        refine ⟨q', p - 1, ⟨_, _, hnextc, ?_⟩, by simp [hpos]⟩
        rw [List.length_dropLast, hlenp]
    · -- moving right
      rcases Nat.lt_or_ge p u.length with hlt | hge
      · left
        have hne : u[p]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]; omega
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
        have hplt : p < (u.map π).length := by omega
        have hwp : (u.map π)[p]? = some (π a) := by rw [List.getElem?_map, ha]; rfl
        have hdr : (u.map π).drop p = π a :: ((u.map π).drop (p + 1)) := by
          rw [List.drop_eq_getElem_cons hplt]
          congr 1
          rw [List.getElem?_eq_getElem hplt] at hwp
          exact Option.some.inj hwp
        have hstep : M.stepCfg (Cfg.conf ((u.map π).take p) q ((u.map π).drop p)) =
            some (o, Cfg.conf (((u.map π).take p) ++ [π a]) q' ((u.map π).drop (p + 1))) := by
          rw [hdr]
          refine stepCfg_right_cons _ ?_
          rw [ha] at hs
          rw [hstepArg, List.head?_cons]
          simpa using hs
        have hnextc := cfgAt_succ_of_step M (u.map π) hcfg hstep
        refine ⟨q', p + 1, ⟨_, _, hnextc, ?_⟩, by simp [hlt]⟩
        rw [List.length_append, hlenp]
        simp
      · right
        have hpu : p = u.length := by omega
        have hdr : (u.map π).drop p = [] := by
          rw [List.drop_eq_nil_iff]
          omega
        have hnil : u[p]? = none := List.getElem?_eq_none (by omega)
        have hstep : M.stepCfg (Cfg.conf ((u.map π).take p) q ((u.map π).drop p)) = none := by
          rw [hdr]
          refine stepCfg_right_nil (q' := q') (o := o) _ ?_
          rw [hnil] at hs
          rw [hstepArg, List.head?_nil]
          simpa using hs
        have hnone : cfgAt M (u.map π) (t + 1) = none := by
          rw [cfgAt_succ, hcfg, Option.bind_some, hstep]
          rfl
        refine ⟨?_, by simp [hpu]⟩
        rintro q'' p'' ⟨x, y, hc, -⟩
        rw [hnone] at hc
        simp at hc


/-- As long as the trigger has not fired, the automaton follows the run. -/
lemma iterate_of_runAt (u : List A') :
    ∀ (t : ℕ), (∀ s < t, ¬ TrigAt M π Trig u s) → ∀ q p, RunAt M (u.map π) q p t →
      ((probeAut M π Trig ans).next u)^[t] (Sum.inl (0, M.init)) = Sum.inl (p, q) := by
  intro t
  induction t with
  | zero =>
      intro _ q p hrun
      obtain ⟨hq, hp⟩ := (runAt_zero M (u.map π)).unique hrun
      subst hq
      subst hp
      simp
  | succ t ih =>
      intro hnt q p hrun
      -- the run is alive at time `t`
      obtain ⟨x, y, hc, hx⟩ := hrun
      obtain ⟨c', hc', hs⟩ := exists_pred M (u.map π) hc
      obtain ⟨x₀, q₀, y₀, rfl⟩ := exists_conf_of_stepCfg M hs
      have hrun₀ : RunAt M (u.map π) q₀ x₀.length t := ⟨x₀, y₀, hc', rfl⟩
      have hnt₀ : ¬ TrigAt M π Trig u t := hnt t (by omega)
      have hiter := ih (fun s hs' => hnt s (by omega)) q₀ x₀.length hrun₀
      rw [Function.iterate_succ_apply', hiter]
      rcases next_of_runAt M π Trig ans hrun₀ hnt₀ with ⟨q', p', hrun', hnext⟩ | ⟨hno, -⟩
      · rw [hnext]
        obtain ⟨hq, hp⟩ := hrun'.unique ⟨x, y, hc, hx⟩
        rw [hq, hp]
      · exact absurd ⟨x, y, hc, hx⟩ (hno q p)

/-- If the trigger never fires and the run is over, the automaton rejects. -/
lemma iterate_of_dead (u : List A') :
    ∀ (t : ℕ), (∀ s < t, ¬ TrigAt M π Trig u s) → (∀ q p, ¬ RunAt M (u.map π) q p t) →
      ((probeAut M π Trig ans).next u)^[t] (Sum.inl (0, M.init)) = Sum.inr false := by
  intro t
  induction t with
  | zero =>
      intro _ hno
      exact absurd (runAt_zero M (u.map π)) (hno _ _)
  | succ t ih =>
      intro hnt hno
      by_cases hex : ∃ q p, RunAt M (u.map π) q p t
      · obtain ⟨q, p, hrun⟩ := hex
        have hiter := iterate_of_runAt M π Trig ans u t (fun s hs => hnt s (by omega)) q p hrun
        rw [Function.iterate_succ_apply', hiter]
        rcases next_of_runAt M π Trig ans hrun (hnt t (by omega)) with
          ⟨q', p', hrun', -⟩ | ⟨-, hnext⟩
        · exact absurd hrun' (hno q' p')
        · exact hnext
      · have hiter := ih (fun s hs => hnt s (by omega)) (by
          intro q p hrun
          exact hex ⟨q, p, hrun⟩)
        rw [Function.iterate_succ_apply', hiter]
        rfl

/-- **The probing automaton is correct**: it accepts if and only if the first
configuration of the run at which the trigger fires gives the answer `true`. -/
theorem accepts_probeAut_iff (u : List A') :
    (probeAut M π Trig ans).Accepts u ↔
      ∃ t, TrigAt M π Trig u t ∧ (∀ s < t, ¬ TrigAt M π Trig u s) ∧ AnsAt M π ans u t := by
  classical
  constructor
  · rintro ⟨N, hN⟩
    rw [show (probeAut M π Trig ans).init = M.init from rfl] at hN
    by_cases hex : ∃ t, TrigAt M π Trig u t
    · have hdec : DecidablePred (fun t => TrigAt M π Trig u t) := fun _ => Classical.dec _
      set t := @Nat.find _ hdec hex with hteq
      have ht : TrigAt M π Trig u t := @Nat.find_spec _ hdec hex
      have hlt : ∀ s < t, ¬ TrigAt M π Trig u s := fun s hs => @Nat.find_min _ hdec hex s hs
      obtain ⟨q, p, hrun, htrig⟩ := ht
      have hiter := iterate_of_runAt M π Trig ans u t hlt q p hrun
      have hstep : ((probeAut M π Trig ans).next u)^[t + 1] (Sum.inl (0, M.init))
          = Sum.inr (ans (leftLet u p) q u[p]?) := by
        rw [Function.iterate_succ_apply', hiter, next_of_trig M π Trig ans u p q htrig]
      have hb := TwoDFA.answer_unique hN hstep
      exact ⟨t, ⟨q, p, hrun, htrig⟩, hlt, ⟨q, p, hrun, hb.symm⟩⟩
    · exfalso
      push_neg at hex
      by_cases hrun : ∃ q p, RunAt M (u.map π) q p N
      · obtain ⟨q, p, hr⟩ := hrun
        have := iterate_of_runAt M π Trig ans u N (fun s _ => hex s) q p hr
        rw [this] at hN
        simp at hN
      · push_neg at hrun
        have := iterate_of_dead M π Trig ans u N (fun s _ => hex s) (by
          intro q p hr; exact hrun q p hr)
        rw [this] at hN
        simp at hN
  · rintro ⟨t, ⟨q, p, hrun, htrig⟩, hlt, hans⟩
    refine ⟨t + 1, ?_⟩
    rw [show (probeAut M π Trig ans).init = M.init from rfl]
    have hiter := iterate_of_runAt M π Trig ans u t hlt q p hrun
    rw [Function.iterate_succ_apply', hiter]
    obtain ⟨q', p', hrun', hansv⟩ := hans
    obtain ⟨hq, hp⟩ := hrun.unique hrun'
    subst hq; subst hp
    rw [next_of_trig M π Trig ans u p q htrig, hansv]

/-- The language recognised by the probing automaton is regular. -/
theorem isRegular_probeLang [Finite A'] [Finite Q] :
    Language.IsRegular {u : List A' | (probeAut M π Trig ans).Accepts u} :=
  TwoDFA.accepts_isRegular _

end RunProbe
end Lax916827Proofs.Transducers
