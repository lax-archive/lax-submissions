/-
**From the window run back to the run**: the converse of the locality results of
`RequestProject/PartC/SnakeLocal.lean`, `RequestProject/PartC/SnakePiece.lean`
and `RequestProject/PartC/SnakePieceRev.lean`.

Those files start from a piece of a run of `M` that is confined to a window of
the input and identify it with the whole run of a window transducer on that
window.  Stage 1 of the induction step of the book's snake lemma needs the other
direction: the *checking* automaton of stage 1 verifies properties of the window
transducers on the windows that the annotation marks, and from those properties
the run of `M` itself has to be reconstructed -- the piece of the run of `M` is
then confined to the window automatically, because the window run is.

The results are, for the four kinds of pieces that
`TwoWay.pieceOut` (`RequestProject/PartC/SnakeBlock.lean`) knows about:

* `TwoWay.exists_outRange_kind_one`, `TwoWay.exists_outRange_kind_two`: if the
  run of `M` on `w` is, at some time, at the cut `x` (resp. `y`) in the state
  `q`, and the window transducer of the piece reaches its stopping configuration
  on the window `seg w x y` with width at most `k`, then the run of `M` is later
  at the cut `y` (resp. `x`) in the state `f`, and the output produced in
  between is the value of `TwoWay.pieceOut`;
* `TwoWay.exists_outRange_kind_three`, `TwoWay.exists_outRange_kind_four`: the
  same for the two kinds of last pieces, whose window run *halts*; there the run
  of `M` halts as well.

These are exactly the four facts that the soundness of the checking language of
stage 1 telescopes along the chain of pieces.
-/
import Lax916827Proofs.Source.PartC.SnakeData
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-! ## One step of the window run is one step of the run -/

/-- **The converse of `TwoWay.stepCfg_window`**: a step of the window run is a
step of the run of `M` on the whole input. -/
lemma stepCfg_of_window (M : TwoWay A B Q) (u m z : List A) (q₀ : Q) {p s p' s' : List A}
    {q q' : Q} {o : List B} (hps' : p' ++ s' = m)
    (h : (M.withContext u.getLast? z.head? q₀).stepCfg (Cfg.conf p q s)
      = some (o, Cfg.conf p' q' s')) :
    M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.conf (u ++ p') q' (s' ++ z)) := by
  have hstep := step_window M u z q₀ p s q
  rcases hM : (M.withContext u.getLast? z.head? q₀).step p.getLast? q s.head? with o'' | ⟨q'', o'', dir⟩
  · rw [stepCfg_halt_eq _ hM] at h
    simp at h
  · have hreal : M.step (u ++ p).getLast? q (s ++ z).head? = Sum.inr (q'', o'', dir) := by
      rw [← hstep]; exact hM
    cases dir with
    | true =>
        rcases hs : s with _ | ⟨b, s₀⟩
        · rw [hs, stepCfg_right_nil _ (by rw [← hs]; exact hM)] at h
          simp at h
        · rw [hs, stepCfg_right_cons _ (by rw [← hs]; exact hM)] at h
          simp only [Option.some.injEq, Prod.mk.injEq, Cfg.conf.injEq] at h
          obtain ⟨ho, hp', hq', hs'⟩ := h
          subst ho; subst hq'; subst hs'
          rw [hs] at hreal
          rw [List.cons_append, stepCfg_right_cons _
            (show M.step (u ++ p).getLast? q (b :: (s₀ ++ z)).head? = Sum.inr (q'', o'', true) by
              simpa using hreal), ← hp']
          simp
    | false =>
        rcases hp : p.getLast? with _ | c
        · rw [stepCfg_left_none _ hp hM] at h
          simp at h
        · rw [stepCfg_left_some _ hp hM] at h
          simp only [Option.some.injEq, Prod.mk.injEq, Cfg.conf.injEq] at h
          obtain ⟨ho, hp', hq', hs'⟩ := h
          subst ho; subst hq'; subst hs'
          have hpne : p ≠ [] := by
            intro hcon; rw [hcon] at hp; simp at hp
          have hup : (u ++ p).getLast? = some c := by
            rw [List.getLast?_append, hp]; rfl
          rw [stepCfg_left_some _ hup hreal, ← hp', List.dropLast_append_of_ne_nil hpne]
          simp

/-- **The converse of `TwoWay.stepCfg_window_halt`**: a halting step of the
window run is a halting step of the run of `M`. -/
lemma stepCfg_of_window_halt (M : TwoWay A B Q) (u z : List A) (q₀ : Q) {p s : List A}
    {q : Q} {o : List B}
    (h : (M.withContext u.getLast? z.head? q₀).stepCfg (Cfg.conf p q s) = some (o, Cfg.halt)) :
    M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.halt) := by
  have hstep := step_window M u z q₀ p s q
  rcases hM : (M.withContext u.getLast? z.head? q₀).step p.getLast? q s.head? with o'' | ⟨q'', o'', dir⟩
  · rw [stepCfg_halt_eq _ hM] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [stepCfg_halt_eq _ (show M.step (u ++ p).getLast? q (s ++ z).head? = Sum.inl o by
      rw [← hstep, hM, h.1])]
  · exfalso
    cases dir with
    | true =>
        rcases hs : s with _ | ⟨b, s₀⟩
        · rw [hs, stepCfg_right_nil _ (by rw [← hs]; exact hM)] at h
          simp at h
        · rw [hs, stepCfg_right_cons _ (by rw [← hs]; exact hM)] at h
          simp at h
    | false =>
        rcases hp : p.getLast? with _ | c
        · rw [stepCfg_left_none _ hp hM] at h
          simp at h
        · rw [stepCfg_left_some _ hp hM] at h
          simp at h

/-- **The run of `M` follows the window run**: if the run of `M` on `u ++ m ++ z`
is at time `a` at the left end of the window in the state `q₀`, then every
configuration of the window run is a configuration of the run of `M`. -/
lemma cfgAt_of_window (M : TwoWay A B Q) (u m z : List A) (q₀ : Q) {a : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z))) :
    ∀ (i : ℕ) (p s : List A) (q : Q),
      cfgAt (M.withContext u.getLast? z.head? q₀) m i = some (Cfg.conf p q s) →
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) := by
  intro i
  induction i with
  | zero =>
      intro p s q hc
      simp only [cfgAt_zero, Option.some.injEq, Cfg.conf.injEq, withContext_init] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simpa using hstart
  | succ i ih =>
      intro p s q hc
      obtain ⟨c', hc', hstepc⟩ := exists_pred _ _ hc
      obtain ⟨p₀, q₀', s₀, rfl⟩ := exists_conf_of_stepCfg _ hstepc
      have hps : p ++ s = m := cfgAt_append _ _ (i + 1) hc
      have hreal := ih p₀ s₀ q₀' hc'
      have hst := stepCfg_of_window M u m z q₀ hps hstepc
      rw [show a + (i + 1) = (a + i) + 1 by omega]
      exact cfgAt_succ_of_step _ _ hreal hst

/-! ## The pieces that end at a marked column -/

/-- Before it stops, the run of `stopRight` is not at its stopping
configuration. -/
lemma stopRight_not_stop_before (M : TwoWay A B Q) (l r : Option A) (q₀ fin : Q) (m : List A)
    {n : ℕ} (hend : cfgAt (stopRight M l r q₀ fin) m n = some (Cfg.conf m fin []))
    {i : ℕ} (hi : i < n) : cfgAt (stopRight M l r q₀ fin) m i ≠ some (Cfg.conf m fin []) := by
  intro hcon
  have hhalt : cfgAt (stopRight M l r q₀ fin) m (i + 1) = some Cfg.halt :=
    cfgAt_succ_of_step _ _ hcon (stopRight_stepCfg_stop M)
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · have : cfgAt (stopRight M l r q₀ fin) m n = none :=
      cfgAt_none_mono _ _ (show i + 1 + 1 ≤ n by omega) (cfgAt_halt_succ _ _ hhalt)
    rw [hend] at this; simp at this
  · have hn : n = i + 1 := by omega
    rw [hn, hhalt] at hend
    simp at hend

/-- Up to the time at which it stops, the run of `stopRight` is the run of the
window transducer. -/
lemma cfgAt_stopRight_eq_withContext (M : TwoWay A B Q) (l r : Option A) (m : List A) (q₀ fin : Q)
    {n : ℕ} (hend : cfgAt (stopRight M l r q₀ fin) m n = some (Cfg.conf m fin [])) :
    ∀ i ≤ n, cfgAt (stopRight M l r q₀ fin) m i = cfgAt (M.withContext l r q₀) m i := by
  intro i
  induction i with
  | zero => intro _; simp [cfgAt]
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      rcases hc : cfgAt (stopRight M l r q₀ fin) m i with _ | (⟨p, q, s⟩ | _)
      · exfalso
        have := cfgAt_none_mono _ _ (show i ≤ n by omega) hc
        rw [hend] at this; simp at this
      · have hps : p ++ s = m := cfgAt_append _ _ i hc
        have hne : ¬ (s = [] ∧ q = fin) := by
          rintro ⟨rfl, rfl⟩
          simp only [List.append_nil] at hps
          subst hps
          exact stopRight_not_stop_before M l r q₀ q p hend (by omega) hc
        rw [cfgAt_succ, cfgAt_succ, ← hprev, hc, Option.bind_some, Option.bind_some,
          stopRight_stepCfg_eq M hne]
      · exfalso
        have := cfgAt_none_mono _ _ (show i + 1 ≤ n by omega) (cfgAt_halt_succ _ _ hc)
        rw [hend] at this; simp at this

/-- **A run of `stopRight` that reaches its stopping configuration is a piece of
the run of `M`.** -/
theorem isPiece_of_stopRight (M : TwoWay A B Q) (u m z : List A) (q₀ fin : Q) {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hend : cfgAt (stopRight M u.getLast? z.head? q₀ fin) m n = some (Cfg.conf m fin [])) :
    IsPiece M u m z q₀ fin a n := by
  have hwin : ∀ i ≤ n, cfgAt (M.withContext u.getLast? z.head? q₀) m i
      = cfgAt (stopRight M u.getLast? z.head? q₀ fin) m i :=
    fun i hi => (cfgAt_stopRight_eq_withContext M u.getLast? z.head? m q₀ fin hend i hi).symm
  have hcfg : ∀ i ≤ n, ∃ p s q, p ++ s = m ∧
      cfgAt (stopRight M u.getLast? z.head? q₀ fin) m i = some (Cfg.conf p q s) ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) := by
    intro i hi
    rcases hc : cfgAt (stopRight M u.getLast? z.head? q₀ fin) m i with _ | (⟨p, q, s⟩ | _)
    · exfalso
      have := cfgAt_none_mono _ _ hi hc
      rw [hend] at this; simp at this
    · exact ⟨p, s, q, cfgAt_append _ _ i hc, rfl,
        cfgAt_of_window M u m z q₀ hstart i p s q (by rw [hwin i hi]; exact hc)⟩
    · exfalso
      rcases Nat.lt_or_ge i n with h | h
      · have := cfgAt_none_mono _ _ (show i + 1 ≤ n by omega) (cfgAt_halt_succ _ _ hc)
        rw [hend] at this; simp at this
      · have hn : i = n := by omega
        rw [hn, hend] at hc; simp at hc
  have hstop : cfgAt M (u ++ m ++ z) (a + n) = some (Cfg.conf (u ++ m) fin z) := by
    have := cfgAt_of_window M u m z q₀ hstart n m [] fin (by rw [hwin n (le_refl n)]; exact hend)
    simpa using this
  refine ⟨hstart, ?_, ?_, hstop⟩
  · intro i hi
    obtain ⟨p, s, q, hps, -, hreal⟩ := hcfg i hi
    refine ⟨u.length + p.length, by rw [posAt, hreal]; simp, by omega, ?_⟩
    have : p.length ≤ m.length := by
      rw [← hps, List.length_append]; omega
    omega
  · intro i hi hcon
    obtain ⟨p, s, q, hps, hstop', hreal⟩ := hcfg i (by omega)
    rw [hcon] at hreal
    simp only [Option.some.injEq, Cfg.conf.injEq] at hreal
    obtain ⟨h1, h2, h3⟩ := hreal
    have hp : p = m := (List.append_cancel_left h1).symm
    subst hp
    have hs : s = [] := by
      have := hps
      simpa using this
    subst hs
    subst h2
    exact stopRight_not_stop_before M u.getLast? z.head? q₀ fin _ hend hi hstop'

/-! ### The mirrored window run -/

/-- **The converse of `TwoWay.stepCfg_pieceRev`**: a step of the mirrored window
run is a step of the run of `M`. -/
lemma stepCfg_of_windowRev (M : TwoWay A B Q) (u m z : List A) (q₀ : Q) {p s p' s' : List A}
    {q q' : Q} {o : List B} (hps' : p' ++ s' = m)
    (h : ((mirror M).withContext z.head? u.getLast? q₀).stepCfg (Cfg.conf s.reverse q p.reverse)
      = some (o, Cfg.conf s'.reverse q' p'.reverse)) :
    M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.conf (u ++ p') q' (s' ++ z)) := by
  have hmir := stepCfg_mirror (M.withContext u.getLast? z.head? q₀) (Cfg.conf p q s)
  rw [mirrorCfg_conf, mirror_withContext, h] at hmir
  rcases hw : (M.withContext u.getLast? z.head? q₀).stepCfg (Cfg.conf p q s) with _ | ⟨o'', c''⟩
  · rw [hw] at hmir; simp at hmir
  · rw [hw] at hmir
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmir
    obtain ⟨ho, hc⟩ := hmir
    have hc'' : c'' = Cfg.conf p' q' s' := by
      have h2 := congrArg mirrorCfg hc
      simpa using h2.symm
    subst hc''
    subst ho
    exact stepCfg_of_window M u m z q₀ hps' hw

/-- A halting step of the mirrored window run is a halting step of the run of
`M`. -/
lemma stepCfg_of_windowRev_halt (M : TwoWay A B Q) (u z : List A) (q₀ : Q) {p s : List A}
    {q : Q} {o : List B}
    (h : ((mirror M).withContext z.head? u.getLast? q₀).stepCfg (Cfg.conf s.reverse q p.reverse)
      = some (o, Cfg.halt)) :
    M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.halt) := by
  have hmir := stepCfg_mirror (M.withContext u.getLast? z.head? q₀) (Cfg.conf p q s)
  rw [mirrorCfg_conf, mirror_withContext, h] at hmir
  rcases hw : (M.withContext u.getLast? z.head? q₀).stepCfg (Cfg.conf p q s) with _ | ⟨o'', c''⟩
  · rw [hw] at hmir; simp at hmir
  · rw [hw] at hmir
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmir
    obtain ⟨ho, hc⟩ := hmir
    have hc'' : c'' = Cfg.halt := by
      have h2 := congrArg mirrorCfg hc
      simpa using h2.symm
    subst hc''
    subst ho
    exact stepCfg_of_window_halt M u z q₀ hw

/-- **The run of `M` follows the mirrored window run**: if the run of `M` on
`u ++ m ++ z` is at time `a` at the right end of the window in the state `q₀`,
then every configuration of the mirrored window run on the reversed window is a
configuration of the run of `M`. -/
lemma cfgAt_of_windowRev (M : TwoWay A B Q) (u m z : List A) (q₀ : Q) {a : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf (u ++ m) q₀ z)) :
    ∀ (i : ℕ) (P S : List A) (q : Q),
      cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse i = some (Cfg.conf P q S) →
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ S.reverse) q (P.reverse ++ z)) := by
  intro i
  induction i with
  | zero =>
      intro P S q hc
      simp only [cfgAt_zero, Option.some.injEq, Cfg.conf.injEq, withContext_init] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simpa using hstart
  | succ i ih =>
      intro P S q hc
      obtain ⟨c', hc', hstepc⟩ := exists_pred _ _ hc
      obtain ⟨P₀, q₀', S₀, rfl⟩ := exists_conf_of_stepCfg _ hstepc
      have hPS : P ++ S = m.reverse := cfgAt_append _ _ (i + 1) hc
      have hreal := ih P₀ S₀ q₀' hc'
      have h2 : S.reverse ++ P.reverse = m := by
        rw [← List.reverse_append, hPS, List.reverse_reverse]
      have hstep := stepCfg_of_windowRev M u m z q₀ (p := S₀.reverse) (s := P₀.reverse)
        (p' := S.reverse) (s' := P.reverse) h2 (by simpa using hstepc)
      rw [show a + (i + 1) = (a + i) + 1 by omega]
      exact cfgAt_succ_of_step _ _ hreal hstep

/-- **A run of the mirrored `stopRight` that reaches its stopping configuration
is a piece of the run of `M` that goes from right to left.** -/
theorem isPieceRev_of_stopRight (M : TwoWay A B Q) (u m z : List A) (q₀ fin : Q) {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf (u ++ m) q₀ z))
    (hend : cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse n
      = some (Cfg.conf m.reverse fin [])) :
    IsPieceRev M u m z q₀ fin a n := by
  have hwin : ∀ i ≤ n, cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse i
      = cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse i :=
    fun i hi => (cfgAt_stopRight_eq_withContext (mirror M) z.head? u.getLast? m.reverse q₀ fin
      hend i hi).symm
  have hcfg : ∀ i ≤ n, ∃ P S q, P ++ S = m.reverse ∧
      cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse i = some (Cfg.conf P q S) ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ S.reverse) q (P.reverse ++ z)) := by
    intro i hi
    rcases hc : cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse i
      with _ | (⟨P, q, S⟩ | _)
    · exfalso
      have := cfgAt_none_mono _ _ hi hc
      rw [hend] at this; simp at this
    · exact ⟨P, S, q, cfgAt_append _ _ i hc, rfl,
        cfgAt_of_windowRev M u m z q₀ hstart i P S q (by rw [hwin i hi]; exact hc)⟩
    · exfalso
      rcases Nat.lt_or_ge i n with h | h
      · have := cfgAt_none_mono _ _ (show i + 1 ≤ n by omega) (cfgAt_halt_succ _ _ hc)
        rw [hend] at this; simp at this
      · have hn : i = n := by omega
        rw [hn, hend] at hc; simp at hc
  have hstop : cfgAt M (u ++ m ++ z) (a + n) = some (Cfg.conf u fin (m ++ z)) := by
    have := cfgAt_of_windowRev M u m z q₀ hstart n m.reverse [] fin
      (by rw [hwin n (le_refl n)]; exact hend)
    simpa using this
  refine ⟨hstart, ?_, ?_, hstop⟩
  · intro i hi
    obtain ⟨P, S, q, hPS, -, hreal⟩ := hcfg i hi
    refine ⟨u.length + S.length, by rw [posAt, hreal]; simp, by omega, ?_⟩
    have : S.length ≤ m.length := by
      have := congrArg List.length hPS
      simp only [List.length_append, List.length_reverse] at this
      omega
    omega
  · intro i hi hcon
    obtain ⟨P, S, q, hPS, hstop', hreal⟩ := hcfg i (by omega)
    rw [hcon] at hreal
    simp only [Option.some.injEq, Cfg.conf.injEq] at hreal
    obtain ⟨h1, h2, h3⟩ := hreal
    have hS : S = [] := by
      have := h1.symm
      have hlen := congrArg List.length this
      simp only [List.length_append, List.length_reverse] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hS
    have hP : P = m.reverse := by
      simpa using hPS
    subst hP
    subst h2
    exact stopRight_not_stop_before (mirror M) z.head? u.getLast? q₀ fin _ hend hi hstop'

/-! ## The last pieces -/

/-- **A window run that halts is the last piece of the run of `M`.** -/
theorem isLastPiece_of_halt (M : TwoWay A B Q) (u m z : List A) (q₀ : Q) {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hend : cfgAt (M.withContext u.getLast? z.head? q₀) m (n + 1) = some Cfg.halt) :
    IsLastPiece M u m z q₀ a n := by
  have hcfg : ∀ i ≤ n, ∃ p s q, p ++ s = m ∧
      cfgAt (M.withContext u.getLast? z.head? q₀) m i = some (Cfg.conf p q s) ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) := by
    intro i hi
    rcases hc : cfgAt (M.withContext u.getLast? z.head? q₀) m i with _ | (⟨p, q, s⟩ | _)
    · exfalso
      have := cfgAt_none_mono _ _ (show i ≤ n + 1 by omega) hc
      rw [hend] at this; simp at this
    · exact ⟨p, s, q, cfgAt_append _ _ i hc, rfl, cfgAt_of_window M u m z q₀ hstart i p s q hc⟩
    · exfalso
      have := cfgAt_none_mono _ _ (show i + 1 ≤ n + 1 by omega) (cfgAt_halt_succ _ _ hc)
      rw [hend] at this; simp at this
  refine ⟨hstart, ?_, ?_⟩
  · intro i hi
    obtain ⟨p, s, q, hps, -, hreal⟩ := hcfg i hi
    refine ⟨u.length + p.length, by rw [posAt, hreal]; simp, by omega, ?_⟩
    have : p.length ≤ m.length := by
      rw [← hps, List.length_append]; omega
    omega
  · obtain ⟨p, s, q, hps, hw, hreal⟩ := hcfg n (le_refl n)
    obtain ⟨c', hc', hstepc⟩ := exists_pred _ _ hend
    rw [hw] at hc'
    have hc'' : c' = Cfg.conf p q s := (Option.some_injective _ hc').symm
    subst hc''
    exact cfgAt_succ_of_step _ _ hreal (stepCfg_of_window_halt M u z q₀ hstepc)

/-- **A mirrored window run that halts is the last piece of the run of `M`,
entered at the right end of the window.** -/
theorem isLastPieceRev_of_halt (M : TwoWay A B Q) (u m z : List A) (q₀ : Q) {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf (u ++ m) q₀ z))
    (hend : cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse (n + 1)
      = some Cfg.halt) :
    IsLastPieceRev M u m z q₀ a n := by
  have hcfg : ∀ i ≤ n, ∃ P S q, P ++ S = m.reverse ∧
      cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse i = some (Cfg.conf P q S) ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ S.reverse) q (P.reverse ++ z)) := by
    intro i hi
    rcases hc : cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse i
      with _ | (⟨P, q, S⟩ | _)
    · exfalso
      have := cfgAt_none_mono _ _ (show i ≤ n + 1 by omega) hc
      rw [hend] at this; simp at this
    · exact ⟨P, S, q, cfgAt_append _ _ i hc, rfl,
        cfgAt_of_windowRev M u m z q₀ hstart i P S q hc⟩
    · exfalso
      have := cfgAt_none_mono _ _ (show i + 1 ≤ n + 1 by omega) (cfgAt_halt_succ _ _ hc)
      rw [hend] at this; simp at this
  refine ⟨hstart, ?_, ?_⟩
  · intro i hi
    obtain ⟨P, S, q, hPS, -, hreal⟩ := hcfg i hi
    refine ⟨u.length + S.length, by rw [posAt, hreal]; simp, by omega, ?_⟩
    have : S.length ≤ m.length := by
      have := congrArg List.length hPS
      simp only [List.length_append, List.length_reverse] at this
      omega
    omega
  · obtain ⟨P, S, q, -, hw, hreal⟩ := hcfg n (le_refl n)
    obtain ⟨c', hc', hstepc⟩ := exists_pred _ _ hend
    rw [hw] at hc'
    have hc'' : c' = Cfg.conf P q S := (Option.some_injective _ hc').symm
    subst hc''
    exact cfgAt_succ_of_step _ _ hreal
      (stepCfg_of_windowRev_halt M u z q₀ (p := S.reverse) (s := P.reverse)
        (by simpa using hstepc))

/-! ## The four kinds of pieces, in the form in which the chain of stage 1 uses
them -/

variable (M : TwoWay A B Q) (w : List A)

/-- **A piece of kind `1`**: the run enters the window at its left end and
leaves it at its right end. -/
theorem exists_outRange_kind_one {x y a k : ℕ} {q f : Q} (hxy : x ≤ y)
    (hstart : cfgAt M w a = some (Cfg.conf (w.take x) q (w.drop x)))
    (hend : ∃ n, cfgAt (stopRight M (w.take x).getLast? (w.drop y).head? q f) (seg w x y) n
      = some (Cfg.conf (seg w x y) f []))
    (hwidth : WidthLe (stopRight M (w.take x).getLast? (w.drop y).head? q f) (seg w x y) k) :
    ∃ n, cfgAt M w (a + n) = some (Cfg.conf (w.take y) f (w.drop y)) ∧
      outRange M w a (a + n)
        = pieceOut M k ((1 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q, f))
            (seg w x y) := by
  obtain ⟨n, hn⟩ := hend
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hstart' : cfgAt M (w.take x ++ seg w x y ++ w.drop y) a
      = some (Cfg.conf (w.take x) q (seg w x y ++ w.drop y)) := by
    rw [hw, ← drop_eq_seg_append w hxy]; exact hstart
  have hp := isPiece_of_stopRight M (w.take x) (seg w x y) (w.drop y) q f hstart' hn
  refine ⟨n, ?_, ?_⟩
  · have h := hp.stop
    rw [hw, take_append_seg w hxy] at h
    exact h
  · rw [pieceOut_kind_one, widthOut, if_pos hwidth, runOut_stopRight hp, hw]

/-- **A piece of kind `2`**: the run enters the window at its right end and
leaves it at its left end. -/
theorem exists_outRange_kind_two {x y a k : ℕ} (hxy : x ≤ y) {q f : Q}
    (hstart : cfgAt M w a = some (Cfg.conf (w.take y) q (w.drop y)))
    (hend : ∃ n, cfgAt (stopRight (mirror M) (w.drop y).head? (w.take x).getLast? q f)
        (seg w x y).reverse n = some (Cfg.conf (seg w x y).reverse f []))
    (hwidth : WidthLe (stopRight (mirror M) (w.drop y).head? (w.take x).getLast? q f)
      (seg w x y).reverse k) :
    ∃ n, cfgAt M w (a + n) = some (Cfg.conf (w.take x) f (w.drop x)) ∧
      outRange M w a (a + n)
        = pieceOut M k ((2 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q, f))
            (seg w x y) := by
  obtain ⟨n, hn⟩ := hend
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hstart' : cfgAt M (w.take x ++ seg w x y ++ w.drop y) a
      = some (Cfg.conf (w.take x ++ seg w x y) q (w.drop y)) := by
    rw [hw, take_append_seg w hxy]; exact hstart
  have hp := isPieceRev_of_stopRight M (w.take x) (seg w x y) (w.drop y) q f hstart' hn
  refine ⟨n, ?_, ?_⟩
  · have h := hp.stop
    rw [hw, ← drop_eq_seg_append w hxy] at h
    exact h
  · rw [pieceOut_kind_two, widthOut, if_pos hwidth, runOut_pieceRev hp, hw]

/-- **A piece of kind `3`**: the last piece of the run, entered at the left end
of the window, out of which the run does not leave. -/
theorem exists_outRange_kind_three {x y a k : ℕ} (hxy : x ≤ y) {q : Q}
    (hstart : cfgAt M w a = some (Cfg.conf (w.take x) q (w.drop x)))
    (hend : ∃ n, cfgAt (M.withContext (w.take x).getLast? (w.drop y).head? q) (seg w x y) n
      = some Cfg.halt)
    (hwidth : WidthLe (M.withContext (w.take x).getLast? (w.drop y).head? q) (seg w x y) k) :
    ∃ n, cfgAt M w (a + n) = some Cfg.halt ∧
      outRange M w a (a + n)
        = pieceOut M k ((3 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q, q))
            (seg w x y) := by
  obtain ⟨N, hN⟩ := hend
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  rcases N with _ | n
  · exact absurd hN (by simp [cfgAt])
  · have hstart' : cfgAt M (w.take x ++ seg w x y ++ w.drop y) a
        = some (Cfg.conf (w.take x) q (seg w x y ++ w.drop y)) := by
      rw [hw, ← drop_eq_seg_append w hxy]; exact hstart
    have hp := isLastPiece_of_halt M (w.take x) (seg w x y) (w.drop y) q hstart' hN
    refine ⟨n + 1, ?_, ?_⟩
    · have h := hp.halts
      rw [hw] at h
      exact h
    · have hr := runOut_lastPiece hp
      rw [hw] at hr
      rw [pieceOut_kind_three, widthOut, if_pos hwidth]
      simpa using hr.symm

/-- **A piece of kind `4`**: the last piece of the run, entered at the right end
of the window, out of which the run does not leave. -/
theorem exists_outRange_kind_four {x y a k : ℕ} (hxy : x ≤ y) {q : Q}
    (hstart : cfgAt M w a = some (Cfg.conf (w.take y) q (w.drop y)))
    (hend : ∃ n, cfgAt ((mirror M).withContext (w.drop y).head? (w.take x).getLast? q)
      (seg w x y).reverse n = some Cfg.halt)
    (hwidth : WidthLe ((mirror M).withContext (w.drop y).head? (w.take x).getLast? q)
      (seg w x y).reverse k) :
    ∃ n, cfgAt M w (a + n) = some Cfg.halt ∧
      outRange M w a (a + n)
        = pieceOut M k ((4 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q, q))
            (seg w x y) := by
  obtain ⟨N, hN⟩ := hend
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  rcases N with _ | n
  · exact absurd hN (by simp [cfgAt])
  · have hstart' : cfgAt M (w.take x ++ seg w x y ++ w.drop y) a
        = some (Cfg.conf (w.take x ++ seg w x y) q (w.drop y)) := by
      rw [hw, take_append_seg w hxy]; exact hstart
    have hp := isLastPieceRev_of_halt M (w.take x) (seg w x y) (w.drop y) q hstart' hN
    refine ⟨n + 1, ?_, ?_⟩
    · have h := hp.halts
      rw [hw] at h
      exact h
    · have hr := runOut_lastPieceRev hp
      rw [hw] at hr
      rw [pieceOut_kind_four, widthOut, if_pos hwidth]
      simpa using hr.symm

end TwoWay

end Lax916827Proofs.Transducers
