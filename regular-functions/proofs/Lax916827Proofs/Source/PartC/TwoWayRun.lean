/-
The run of a two-way transducer, indexed by time.

This file is part of the proof of Theorem `thm:composition-of-two-way-transducers` (closure of
two-way transducers under composition) of *Transducers* (M. Bojańczyk).  The configuration graph of
a deterministic two-way transducer on a fixed input is a partial function, so the run started in the
initial configuration is a sequence of configurations `cfgAt 0, cfgAt 1, …` which is defined until
the run halts or gets stuck.  The two facts that matter for the composition construction are:

* the run is *injective* up to the halting time -- otherwise it would cycle and
  never halt;
* consequently, a configuration on the run has a *unique* predecessor among the
  configurations that lie on the run.

The second fact is what makes it possible to walk backwards along the run, which
is what the composed transducer has to do in order to move the head of the
second transducer to the left.
-/
import Lax916827Proofs.Source.PartC.TwoWayCont
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- The configuration of the run of `M` on `w` after `n` steps; `none` if the
run has already halted or got stuck. -/
def cfgAt (M : TwoWay A B Q) (w : List A) : ℕ → Option (Cfg A Q)
  | 0 => some (Cfg.conf [] M.init w)
  | n + 1 => (cfgAt M w n).bind fun c => (M.stepCfg c).map Prod.snd

/-- The output produced by the `n`-th step of the run of `M` on `w`. -/
def outAt (M : TwoWay A B Q) (w : List A) (n : ℕ) : List B :=
  ((cfgAt M w n).bind fun c => (M.stepCfg c).map Prod.fst).getD []

/-- The output produced by the steps `a, a+1, …, b-1` of the run. -/
def outRange (M : TwoWay A B Q) (w : List A) (a b : ℕ) : List B :=
  ((List.range' a (b - a)).map (outAt M w)).flatten

/-- A configuration lies on the run of `M` on `w`. -/
def Visits (M : TwoWay A B Q) (w : List A) (c : Cfg A Q) : Prop :=
  ∃ n, cfgAt M w n = some c

variable (M : TwoWay A B Q) (w : List A)

@[simp] lemma cfgAt_zero : cfgAt M w 0 = some (Cfg.conf [] M.init w) := rfl

lemma cfgAt_succ (n : ℕ) :
    cfgAt M w (n + 1) = (cfgAt M w n).bind fun c => (M.stepCfg c).map Prod.snd := rfl

lemma cfgAt_succ_of_step {n : ℕ} {c c' : Cfg A Q} {o : List B}
    (hc : cfgAt M w n = some c) (hs : M.stepCfg c = some (o, c')) :
    cfgAt M w (n + 1) = some c' := by
  rw [cfgAt_succ, hc]
  simp [hs]

lemma outAt_of_step {n : ℕ} {c c' : Cfg A Q} {o : List B}
    (hc : cfgAt M w n = some c) (hs : M.stepCfg c = some (o, c')) :
    outAt M w n = o := by
  simp [outAt, hc, hs]

lemma cfgAt_none_succ {n : ℕ} (h : cfgAt M w n = none) : cfgAt M w (n + 1) = none := by
  rw [cfgAt_succ, h]; rfl

lemma cfgAt_none_mono {m n : ℕ} (hmn : m ≤ n) (h : cfgAt M w m = none) : cfgAt M w n = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => simpa using h
  | succ d ih => rw [show m + (d + 1) = (m + d) + 1 by omega]; exact cfgAt_none_succ M w ih

lemma cfgAt_isSome_of_le {m n : ℕ} (hmn : m ≤ n) (h : (cfgAt M w n).isSome) :
    (cfgAt M w m).isSome := by
  rcases hm : cfgAt M w m with _ | c
  · rw [cfgAt_none_mono M w hmn hm] at h; simp at h
  · simp

lemma cfgAt_halt_succ {n : ℕ} (h : cfgAt M w n = some Cfg.halt) : cfgAt M w (n + 1) = none := by
  rw [cfgAt_succ, h]
  rfl

/-! ### The run and the reachability relation -/

/-- A run in the configuration graph is a stretch of the time-indexed run. -/
lemma reaches_iff_cfgAt {c c' : Cfg A Q} {o : List B} (h : M.Reaches c o c') :
    ∀ t, cfgAt M w t = some c → ∃ k, cfgAt M w (t + k) = some c' ∧ outRange M w t (t + k) = o := by
  induction h with
  | refl c => intro t ht; exact ⟨0, by simpa using ht, by simp [outRange]⟩
  | @step c c₁ c₂ o o' hs _ ih =>
      intro t ht
      have h1 : cfgAt M w (t + 1) = some c₁ := cfgAt_succ_of_step M w ht hs
      obtain ⟨k, hk, hko⟩ := ih (t + 1) h1
      refine ⟨k + 1, by rw [show t + (k + 1) = (t + 1) + k by omega]; exact hk, ?_⟩
      have hsplit : outRange M w t (t + (k + 1)) = outAt M w t ++ outRange M w (t + 1) (t + 1 + k) := by
        rw [outRange, outRange]
        rw [show t + (k + 1) - t = (k + 1) by omega, show t + 1 + k - (t + 1) = k by omega]
        rw [List.range'_succ]
        simp
      rw [hsplit, outAt_of_step M w ht hs, show t + 1 + k = t + (k+1) - 1 + 1 by omega]
      rw [show t + (k+1) - 1 + 1 = t + 1 + k by omega, hko]

/-- The halting time of the run, and the output it produces. -/
lemma exists_halt_time {v : List B} (h : M.Computes w v) :
    ∃ T, cfgAt M w T = some Cfg.halt ∧ outRange M w 0 T = v := by
  obtain ⟨k, hk, hko⟩ := reaches_iff_cfgAt M w h 0 (by simp)
  exact ⟨k, by simpa using hk, by simpa using hko⟩

/-- The step of the run that leads to a configuration reached at a positive
time. -/
lemma exists_pred {t : ℕ} {c : Cfg A Q} (ht : cfgAt M w (t + 1) = some c) :
    ∃ c', cfgAt M w t = some c' ∧ M.stepCfg c' = some (outAt M w t, c) := by
  rw [cfgAt_succ] at ht
  rcases hc : cfgAt M w t with _ | c'
  · rw [hc] at ht; simp at ht
  · refine ⟨c', rfl, ?_⟩
    rw [hc] at ht
    simp only [Option.bind_some] at ht
    rcases hs : M.stepCfg c' with _ | ⟨o, c''⟩
    · rw [hs] at ht; simp at ht
    · rw [hs] at ht
      simp only [Option.map_some] at ht
      have : c'' = c := Option.some_injective _ ht
      subst this
      rw [outAt_of_step M w hc hs]

/-- The two halves of a configuration on the run concatenate to the input. -/
lemma cfgAt_append : ∀ (t : ℕ) {u v : List A} {q : Q},
    cfgAt M w t = some (Cfg.conf u q v) → u ++ v = w := by
  intro t
  induction t with
  | zero =>
      intro u v q h
      simp only [cfgAt_zero, Option.some.injEq, Cfg.conf.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      simp
  | succ t ih =>
      intro u v q h
      obtain ⟨c', hc', hs⟩ := exists_pred M w h
      obtain ⟨u', q', v', rfl⟩ := exists_conf_of_stepCfg M hs
      exact stepCfg_append M (ih hc') hs rfl

lemma visits_append {u v : List A} {q : Q} (h : Visits M w (Cfg.conf u q v)) : u ++ v = w := by
  obtain ⟨t, ht⟩ := h
  exact cfgAt_append M w t ht

/-! ### Injectivity of the run -/

lemma cfgAt_shift {s t : ℕ} (h : cfgAt M w s = cfgAt M w t) :
    ∀ k, cfgAt M w (s + k) = cfgAt M w (t + k) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [show s + (k + 1) = (s + k) + 1 by omega, show t + (k + 1) = (t + k) + 1 by omega,
        cfgAt_succ, cfgAt_succ, ih]

/-- The halting time is unique. -/
lemma halt_time_unique {T T' : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    (hT' : cfgAt M w T' = some Cfg.halt) : T = T' := by
  by_contra hne
  rcases Nat.lt_or_ge T T' with h | h
  · have := cfgAt_none_mono M w (show T + 1 ≤ T' by omega) (cfgAt_halt_succ M w hT)
    rw [hT'] at this; simp at this
  · have hlt : T' < T := by omega
    have := cfgAt_none_mono M w (show T' + 1 ≤ T by omega) (cfgAt_halt_succ M w hT')
    rw [hT] at this; simp at this

/-- Before halting, the run does not repeat a configuration. -/
lemma run_inj {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) {s t : ℕ} {c : Cfg A Q}
    (hs : cfgAt M w s = some c) (ht : cfgAt M w t = some c) : s = t := by
  -- both `s` and `t` are at most `T`
  have hle : ∀ r : ℕ, (cfgAt M w r).isSome → r ≤ T := by
    intro r hr
    by_contra hcon
    have : cfgAt M w r = none := cfgAt_none_mono M w (by omega) (cfgAt_halt_succ M w hT)
    rw [this] at hr; simp at hr
  have hsT : s ≤ T := hle s (by rw [hs]; simp)
  have htT : t ≤ T := hle t (by rw [ht]; simp)
  have heq : cfgAt M w s = cfgAt M w t := by rw [hs, ht]
  rcases Nat.le_total s t with hst | hst
  · -- shift by `T - t`
    have := cfgAt_shift M w heq (T - t)
    rw [show t + (T - t) = T by omega] at this
    rw [hT] at this
    have h2 : s + (T - t) = T := halt_time_unique M w this hT
    omega
  · have := cfgAt_shift M w heq.symm (T - s)
    rw [show s + (T - s) = T by omega] at this
    rw [hT] at this
    have h2 : t + (T - s) = T := halt_time_unique M w this hT
    omega

/-! ### Predecessors -/

/-- The predecessor of a configuration on the run is the *unique* configuration
on the run that steps to it. -/
lemma pred_unique {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) {t : ℕ} {c c' : Cfg A Q}
    {o : List B} (ht : cfgAt M w (t + 1) = some c) (hv : Visits M w c')
    (hs : M.stepCfg c' = some (o, c)) : cfgAt M w t = some c' := by
  obtain ⟨s, hsv⟩ := hv
  have h1 : cfgAt M w (s + 1) = some c := cfgAt_succ_of_step M w hsv hs
  have : s + 1 = t + 1 := run_inj M w hT h1 ht
  rw [show t = s by omega]
  exact hsv

end TwoWay

end Lax916827Proofs.Transducers
