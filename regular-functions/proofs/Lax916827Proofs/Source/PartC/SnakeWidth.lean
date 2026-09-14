/- The *width* of the run of a two-way transducer, and the reduction of the hard half of Theorem
`thm:2dfa-decomposition-into-primes` (`two-way ⊆ regular`) to the width-bounded case, which is the
book's Lemma "the output of a snake graph is regular".

The book represents a run of a two-way transducer by a *snake graph*: a graph
whose vertices are pairs (state, column) and whose edges, labelled by output
letters, form a single directed path.  Snake graphs over a fixed state set are
strings over a finite alphabet, and the map that sends an input string to the
snake graph of the run is a rational function -- indeed the snake graph is just
the table of the transitions of the transducer at the individual columns.
Rather than introducing that alphabet, we keep the transducer itself as the
description of the snake: *every* snake graph over the states `Q` with output
alphabet `B` is the run of a two-way transducer over a suitable finite input
alphabet, so quantifying over all two-way transducers, over all finite input
alphabets, is the same as quantifying over all snake graphs.

The *width* of a run is the maximal number of times a single column (= cut of
the input string) is visited.  This file proves the two facts that make the
reduction work:

* a run that halts has width at most the number of states (`widthLe_card`),
  since a repeated (column, state) pair means a repeated configuration, and the
  run of a deterministic transducer does not repeat a configuration before
  halting;
* consequently, a function computed by a two-way transducer with state set `Q`
  is the width-`|Q|` output function `widthOut M |Q|` of that transducer.

The snake lemma itself -- that `widthOut M k` is a regular function for every
`k` -- is `Transducers.boundedWidth_isRegular`, in
`RequestProject/PartC/SnakeReg.lean`; its base cases `k ≤ 1` are proved in
`RequestProject/PartC/SnakeBase.lean`.
-/
import Lax916827Proofs.Source.PartC.TwoWayRun
import Lax916827Proofs.Source.PartC.RegularDef
import Lax916827Proofs.Source.PartC.SnakeWalk
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- The column (cut of the input string) at which the head stands at time `t`;
`none` if the run has halted, got stuck, or is already over. -/
def posAt (M : TwoWay A B Q) (w : List A) (t : ℕ) : Option ℕ :=
  (cfgAt M w t).bind fun c => match c with
    | Cfg.conf u _ _ => some u.length
    | Cfg.halt => none

/-- The state of the run at time `t`. -/
def stateAt (M : TwoWay A B Q) (w : List A) (t : ℕ) : Option Q :=
  (cfgAt M w t).bind fun c => match c with
    | Cfg.conf _ q _ => some q
    | Cfg.halt => none

variable (M : TwoWay A B Q) (w : List A)

/-- A configuration on the run is determined by the column and the state. -/
lemma cfgAt_of_posAt_stateAt {t x : ℕ} {q : Q} (hx : posAt M w t = some x)
    (hq : stateAt M w t = some q) :
    cfgAt M w t = some (Cfg.conf (w.take x) q (w.drop x)) := by
  rcases hc : cfgAt M w t with _ | (⟨u, q', v⟩ | _)
  · rw [posAt, hc] at hx; simp at hx
  · rw [posAt, hc] at hx
    rw [stateAt, hc] at hq
    simp only [Option.bind_some, Option.some.injEq] at hx hq
    subst hq
    have huv : u ++ v = w := cfgAt_append M w t hc
    subst huv
    subst hx
    simp
  · rw [posAt, hc] at hx; simp at hx

/-- The run has width at most `k`: no column is visited more than `k` times. -/
def WidthLe (M : TwoWay A B Q) (w : List A) (k : ℕ) : Prop :=
  ∀ x : ℕ, ∀ s : Finset ℕ, (∀ t ∈ s, posAt M w t = some x) → s.card ≤ k

/-- A halting run visits every column at most `|Q|` times: a column visited
twice in the same state gives a repeated configuration. -/
theorem widthLe_card [Finite Q] {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) :
    WidthLe M w (Nat.card Q) := by
  classical
  intro x s hs
  have hstate : ∀ t ∈ s, ∃ q, stateAt M w t = some q := by
    intro t ht
    rcases hc : cfgAt M w t with _ | (⟨u, q', v⟩ | _)
    · have := hs t ht; rw [posAt, hc] at this; simp at this
    · exact ⟨q', by simp [stateAt, hc]⟩
    · have := hs t ht; rw [posAt, hc] at this; simp at this
  -- the map sending a time to its state is injective on `s`
  have hinj0 : ∀ t ∈ s, ∀ t' ∈ s, (stateAt M w t = stateAt M w t') → t = t' := by
    intro t ht t' ht' heq
    obtain ⟨q, hq⟩ := hstate t ht
    have hq' : stateAt M w t' = some q := by rw [← heq]; exact hq
    have h1 := cfgAt_of_posAt_stateAt M w (hs t ht) hq
    have h2 := cfgAt_of_posAt_stateAt M w (hs t' ht') hq'
    exact run_inj M w hT h1 h2
  haveI : Fintype Q := Fintype.ofFinite Q
  rcases s.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  obtain ⟨q₀, hq₀⟩ := hstate t₀ ht₀
  set g : ℕ → Q := fun t => (stateAt M w t).getD q₀ with hg
  have hginj : Set.InjOn g ↑s := by
    intro t ht t' ht' h
    obtain ⟨q, hq⟩ := hstate t (by simpa using ht)
    obtain ⟨q', hq'⟩ := hstate t' (by simpa using ht')
    simp only [hg, hq, hq', Option.getD_some] at h
    exact hinj0 t (by simpa using ht) t' (by simpa using ht') (by rw [hq, hq', h])
  have := Finset.card_le_card_of_injOn g (fun t _ => Finset.mem_univ (g t)) hginj
  simpa [Nat.card_eq_fintype_card] using this


/-! ### The trajectory of a run is a walk -/

/-- Before the halting time, the run is at a column. -/
lemma exists_posAt {T t : ℕ} (hT : cfgAt M w T = some Cfg.halt) (ht : t < T) :
    ∃ x, posAt M w t = some x := by
  rcases hc : cfgAt M w t with _ | (⟨u, q, v⟩ | _)
  · have : (cfgAt M w t).isSome := cfgAt_isSome_of_le M w (le_of_lt ht) (by rw [hT]; simp)
    rw [hc] at this; simp at this
  · exact ⟨u.length, by simp [posAt, hc]⟩
  · exfalso
    have h1 : cfgAt M w (t + 1) = none := cfgAt_halt_succ M w hc
    have : cfgAt M w T = none := cfgAt_none_mono M w (by omega) h1
    rw [hT] at this; simp at this

/-- Consecutive columns of a run differ by one. -/
lemma posAt_succ {t x y : ℕ} (hx : posAt M w t = some x) (hy : posAt M w (t + 1) = some y) :
    y = x + 1 ∨ x = y + 1 := by
  rcases hc : cfgAt M w t with _ | (⟨u, q, v⟩ | _)
  · rw [posAt, hc] at hx; simp at hx
  · rw [posAt, hc] at hx
    simp only [Option.bind_some, Option.some.injEq] at hx
    subst hx
    rcases hstep : M.step u.getLast? q v.head? with o | ⟨q', o, dir⟩
    · exfalso
      have h1 : cfgAt M w (t + 1) = some Cfg.halt :=
        cfgAt_succ_of_step M w hc (stepCfg_halt_eq M hstep)
      rw [posAt, h1] at hy; simp at hy
    · cases dir with
      | true =>
          rcases hv : v with _ | ⟨a, v'⟩
          · exfalso
            subst hv
            have h1 : M.stepCfg (Cfg.conf u q []) = none := stepCfg_right_nil M hstep
            have h2 : cfgAt M w (t + 1) = none := by rw [cfgAt_succ, hc]; simp [h1]
            rw [posAt, h2] at hy; simp at hy
          · subst hv
            have h1 := stepCfg_right_cons M hstep
            have h2 : cfgAt M w (t + 1) = some (Cfg.conf (u ++ [a]) q' v') :=
              cfgAt_succ_of_step M w hc h1
            rw [posAt, h2] at hy
            simp only [Option.bind_some, Option.some.injEq, List.length_append,
              List.length_cons, List.length_nil] at hy
            omega
      | false =>
          rcases hu : u.getLast? with _ | a
          · exfalso
            have h1 : M.stepCfg (Cfg.conf u q v) = none := stepCfg_left_none M hu hstep
            have h2 : cfgAt M w (t + 1) = none := by rw [cfgAt_succ, hc]; simp [h1]
            rw [posAt, h2] at hy; simp at hy
          · have h1 := stepCfg_left_some M hu hstep
            have h2 : cfgAt M w (t + 1) = some (Cfg.conf u.dropLast q' (a :: v)) :=
              cfgAt_succ_of_step M w hc h1
            rw [posAt, h2] at hy
            simp only [Option.bind_some, Option.some.injEq] at hy
            have hune : u ≠ [] := by
              intro h; rw [h] at hu; simp at hu
            have : u.dropLast.length + 1 = u.length := by
              rw [List.length_dropLast]
              have : u.length ≠ 0 := by simpa using hune
              omega
            omega
  · rw [posAt, hc] at hx; simp at hx

/-- The trajectory of the run of `M` on `w`: the column of the head at each
time (an arbitrary value once the run is over). -/
noncomputable def traj (M : TwoWay A B Q) (w : List A) (t : ℕ) : ℕ := (posAt M w t).getD 0

lemma traj_eq {t x : ℕ} (h : posAt M w t = some x) : traj M w t = x := by
  simp [traj, h]

/-- The trajectory of a halting run is a walk of length `T - 1`, where `T` is
the halting time. -/
lemma isWalk_traj {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) :
    Walk.IsWalk (traj M w) (T - 1) := by
  intro t ht
  obtain ⟨x, hx⟩ := exists_posAt (t := t) M w hT (by omega)
  obtain ⟨y, hy⟩ := exists_posAt (t := t + 1) M w hT (by omega)
  rw [traj_eq M w hx, traj_eq M w hy]
  exact posAt_succ M w hx hy

/-- The width of a run, read on its trajectory. -/
lemma visitsLe_of_widthLe {T k : ℕ} (hT : cfgAt M w T = some Cfg.halt) (h : WidthLe M w k) :
    Walk.VisitsLe (traj M w) 0 (T - 1) k := by
  have hT1 : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with rfl | h
    · rw [cfgAt_zero] at hT; simp at hT
    · exact h
  intro x s hs
  refine h x s ?_
  intro t ht
  obtain ⟨-, h2, h3⟩ := hs t ht
  obtain ⟨z, hz⟩ := exists_posAt (t := t) M w hT (by omega)
  rw [traj_eq M w hz] at h3
  rw [hz, h3]

open Classical in
/-- The output of the run of `M` on `w`, if that run halts, and the empty string
otherwise. -/
noncomputable def runOut (M : TwoWay A B Q) (w : List A) : List B :=
  if h : ∃ T, cfgAt M w T = some Cfg.halt then outRange M w 0 h.choose else []

lemma runOut_eq {v : List B} (h : M.Computes w v) : runOut M w = v := by
  classical
  obtain ⟨T, hT, hout⟩ := exists_halt_time M w h
  have hex : ∃ T, cfgAt M w T = some Cfg.halt := ⟨T, hT⟩
  rw [runOut, dif_pos hex, halt_time_unique M w hex.choose_spec hT, hout]

open Classical in
/-- The output of the run of `M`, restricted to the inputs on which that run has
width at most `k`.  This is the book's "output of a snake graph of width at most
`k`", with the snake graph presented as the run of `M`. -/
noncomputable def widthOut (M : TwoWay A B Q) (k : ℕ) (w : List A) : List B :=
  if WidthLe M w k then runOut M w else []

end TwoWay

end Lax916827Proofs.Transducers
