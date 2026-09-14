/-
Identification of the named pieces of the record-breaker decomposition with the
whole runs of window transducers.

`RequestProject/PartC/SnakeParts.lean` names the pieces of the decomposition of
a halting run of width at most `k` -- the two halves of each excursion of each
record-breaking column, the progress parts, and the final piece -- and proves
that the output of the run is the concatenation of their outputs and that each
of them visits every column at most `k - 1` times.

`RequestProject/PartC/SnakePiece.lean` and
`RequestProject/PartC/SnakePieceRev.lean` show that a piece of a run which
enters a window of the input at one end and leaves it, for the first time, at
the other end *is* the whole run of a window transducer on that window (or on
its reverse, after mirroring).  This file combines the two: it proves that every
piece of the record-breaker decomposition is of that shape, so that its output
is a value of the width-`(k-1)` output function of a two-way transducer over a
finite state set -- which is exactly the function that the induction hypothesis
of the book's snake lemma applies to.

The results are stated existentially: the source and the target state of the
piece, and the two columns that delimit its window, are what the *marking* of
the input (the book's first stage) has to provide, and they do not appear in the
statement of the induction step.
-/
import Lax916827Proofs.Source.PartC.SnakeParts
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-! ### From a position to a configuration -/

lemma exists_cfg_of_posAt (M : TwoWay A B Q) (w : List A) {t x : ℕ}
    (hx : posAt M w t = some x) :
    ∃ q : Q, cfgAt M w t = some (Cfg.conf (w.take x) q (w.drop x)) := by
  rcases hc : cfgAt M w t with _ | (⟨u, q', v⟩ | _)
  · rw [posAt, hc] at hx; simp at hx
  · rw [posAt, hc] at hx
    simp only [Option.bind_some, Option.some.injEq] at hx
    have huv : u ++ v = w := cfgAt_append M w t hc
    subst huv; subst hx
    exact ⟨q', by simp⟩
  · rw [posAt, hc] at hx; simp at hx

lemma posAt_le_length (M : TwoWay A B Q) (w : List A) {t x : ℕ}
    (hx : posAt M w t = some x) : x ≤ w.length := by
  rcases hc : cfgAt M w t with _ | (⟨u, q', v⟩ | _)
  · rw [posAt, hc] at hx; simp at hx
  · rw [posAt, hc] at hx
    simp only [Option.bind_some, Option.some.injEq] at hx
    have huv : u ++ v = w := cfgAt_append M w t hc
    subst huv; subst hx; simp
  · rw [posAt, hc] at hx; simp at hx

lemma posAt_of_cfgAt (M : TwoWay A B Q) (w : List A) {t x : ℕ} {q : Q}
    (hc : cfgAt M w t = some (Cfg.conf (w.take x) q (w.drop x))) (hx : x ≤ w.length) :
    posAt M w t = some x := by
  rw [posAt, hc]
  simp only [Option.bind_some, Option.some.injEq, List.length_take]
  omega

/-! ### The window of a piece -/

lemma seg_len_add {w : List A} {x y : ℕ} (hxy : x ≤ y) (hyw : y ≤ w.length) :
    (w.take x).length + (seg w x y).length = y := by
  rw [List.length_take, seg_length w hyw]
  omega

/-- **A piece of a run that crosses its window from left to right is the whole
run of a window transducer.** -/
theorem exists_isPiece_of_run (M : TwoWay A B Q) (w : List A) {a b x y : ℕ}
    (hab : a ≤ b) (hxy : x ≤ y) (hyw : y ≤ w.length)
    (hpa : posAt M w a = some x) (hpb : posAt M w b = some y)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hearly : ∀ t, a ≤ t → t < b → posAt M w t ≠ some y) :
    ∃ q₀ fin : Q, IsPiece M (w.take x) (seg w x y) (w.drop y) q₀ fin a (b - a) := by
  have hxw : x ≤ w.length := le_trans hxy hyw
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hly : (w.take y).length = y := by rw [List.length_take]; omega
  have hlxy : (w.take x).length + (seg w x y).length = y := seg_len_add hxy hyw
  have hmz : seg w x y ++ w.drop y = w.drop x := (drop_eq_seg_append w hxy).symm
  have hum : w.take x ++ seg w x y = w.take y := take_append_seg w hxy
  obtain ⟨q₀, hq₀⟩ := exists_cfg_of_posAt M w hpa
  obtain ⟨fin, hfin⟩ := exists_cfg_of_posAt M w hpb
  refine ⟨q₀, fin, ?_, ?_, ?_, ?_⟩
  · rw [hw, hmz]; exact hq₀
  · intro i hi
    rw [hw]
    obtain ⟨c, hc, h1, h2⟩ := hconf (a + i) (by omega) (by omega)
    exact ⟨c, hc, by omega, by omega⟩
  · intro i hi hcon
    rw [hw, hum] at hcon
    exact hearly (a + i) (by omega) (by omega)
      (posAt_of_cfgAt M w (by rw [hcon]) hyw)
  · rw [hw, hum, show a + (b - a) = b from by omega]; exact hfin

/-- **A piece of a run that crosses its window from right to left is, after
mirroring, the whole run of a window transducer on the reversed window.** -/
theorem exists_isPieceRev_of_run (M : TwoWay A B Q) (w : List A) {a b x y : ℕ}
    (hab : a ≤ b) (hxy : x ≤ y) (hyw : y ≤ w.length)
    (hpa : posAt M w a = some y) (hpb : posAt M w b = some x)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hearly : ∀ t, a ≤ t → t < b → posAt M w t ≠ some x) :
    ∃ q₀ fin : Q, IsPieceRev M (w.take x) (seg w x y) (w.drop y) q₀ fin a (b - a) := by
  have hxw : x ≤ w.length := le_trans hxy hyw
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hly : (w.take y).length = y := by rw [List.length_take]; omega
  have hlxy : (w.take x).length + (seg w x y).length = y := seg_len_add hxy hyw
  have hmz : seg w x y ++ w.drop y = w.drop x := (drop_eq_seg_append w hxy).symm
  have hum : w.take x ++ seg w x y = w.take y := take_append_seg w hxy
  obtain ⟨q₀, hq₀⟩ := exists_cfg_of_posAt M w hpa
  obtain ⟨fin, hfin⟩ := exists_cfg_of_posAt M w hpb
  refine ⟨q₀, fin, ?_, ?_, ?_, ?_⟩
  · rw [hw, hum]; exact hq₀
  · intro i hi
    rw [hw]
    obtain ⟨c, hc, h1, h2⟩ := hconf (a + i) (by omega) (by omega)
    exact ⟨c, hc, by omega, by omega⟩
  · intro i hi hcon
    rw [hw, hmz] at hcon
    exact hearly (a + i) (by omega) (by omega)
      (posAt_of_cfgAt M w (by rw [hcon]) hxw)
  · rw [hw, hmz, show a + (b - a) = b from by omega]; exact hfin

/-- **The last piece of a run is the whole run of a window transducer**, on the
suffix of the input to the right of the column where it starts. -/
theorem exists_isLastPiece_of_run (M : TwoWay A B Q) (w : List A) {a b x : ℕ}
    (hab : a ≤ b) (hxw : x ≤ w.length) (hpa : posAt M w a = some x)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c)
    (hhalt : cfgAt M w (b + 1) = some Cfg.halt) :
    ∃ q₀ : Q, IsLastPiece M (w.take x) (w.drop x) [] q₀ a (b - a) := by
  have hw : w.take x ++ w.drop x ++ [] = w := by simp
  have hlx : (w.take x).length = x := by rw [List.length_take]; omega
  have hlen : (w.take x).length + (w.drop x).length = w.length := by
    rw [List.length_take, List.length_drop]; omega
  obtain ⟨q₀, hq₀⟩ := exists_cfg_of_posAt M w hpa
  refine ⟨q₀, ?_, ?_, ?_⟩
  · rw [hw]; simpa using hq₀
  · intro i hi
    rw [hw]
    obtain ⟨c, hc, h1⟩ := hconf (a + i) (by omega) (by omega)
    refine ⟨c, hc, by omega, ?_⟩
    rw [hlen]
    exact posAt_le_length M w hc
  · rw [hw, show a + (b - a) + 1 = b + 1 from by omega]; exact hhalt


/-! ### The output of a piece as a value of a width-bounded output function -/

/-- **The output of a piece that crosses its window from left to right is a
value of the width-`k` output function of a window transducer.** -/
theorem exists_widthOut_piece (M : TwoWay A B Q) (w : List A) {a b x y k : ℕ}
    (hab : a ≤ b) (hxy : x ≤ y) (hyw : y ≤ w.length)
    (hpa : posAt M w a = some x) (hpb : posAt M w b = some y)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hearly : ∀ t, a ≤ t → t < b → posAt M w t ≠ some y)
    (hk : Walk.VisitsLe (traj M w) a b k) :
    ∃ q₀ fin : Q, outRange M w a b
      = widthOut (stopRight M (w.take x).getLast? (w.drop y).head? q₀ fin) k (seg w x y) := by
  obtain ⟨q₀, fin, hp⟩ := exists_isPiece_of_run M w hab hxy hyw hpa hpb hconf hearly
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hba : a + (b - a) = b := by omega
  refine ⟨q₀, fin, ?_⟩
  have hk' : Walk.VisitsLe (traj M (w.take x ++ seg w x y ++ w.drop y)) a (a + (b - a)) k := by
    rw [hw, hba]; exact hk
  have h := widthOut_stopRight hp hk'
  rw [hw, hba] at h
  exact h.symm

/-- **The output of a piece that crosses its window from right to left is a
value of the width-`k` output function of the mirrored window transducer on the
reversed window.** -/
theorem exists_widthOut_pieceRev (M : TwoWay A B Q) (w : List A) {a b x y k : ℕ}
    (hab : a ≤ b) (hxy : x ≤ y) (hyw : y ≤ w.length)
    (hpa : posAt M w a = some y) (hpb : posAt M w b = some x)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c ∧ c ≤ y)
    (hearly : ∀ t, a ≤ t → t < b → posAt M w t ≠ some x)
    (hk : Walk.VisitsLe (traj M w) a b k) :
    ∃ q₀ fin : Q, outRange M w a b
      = widthOut (stopRight (mirror M) (w.drop y).head? (w.take x).getLast? q₀ fin) k
          (seg w x y).reverse := by
  obtain ⟨q₀, fin, hp⟩ := exists_isPieceRev_of_run M w hab hxy hyw hpa hpb hconf hearly
  have hw : w.take x ++ seg w x y ++ w.drop y = w := take_seg_drop w hxy
  have hba : a + (b - a) = b := by omega
  refine ⟨q₀, fin, ?_⟩
  have hk' : Walk.VisitsLe (traj M (w.take x ++ seg w x y ++ w.drop y)) a (a + (b - a)) k := by
    rw [hw, hba]; exact hk
  have h := widthOut_pieceRev hp hk'
  rw [hw, hba] at h
  exact h.symm

/-- **The output of the last piece of a run is a value of the width-`k` output
function of a window transducer.** -/
theorem exists_widthOut_lastPiece (M : TwoWay A B Q) (w : List A) {a b x k : ℕ}
    (hab : a ≤ b) (hxw : x ≤ w.length) (hpa : posAt M w a = some x)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ x ≤ c)
    (hhalt : cfgAt M w (b + 1) = some Cfg.halt)
    (hk : Walk.VisitsLe (traj M w) a b k) :
    ∃ q₀ : Q, outRange M w a (b + 1)
      = widthOut (M.withContext (w.take x).getLast? none q₀) k (w.drop x) := by
  obtain ⟨q₀, hp⟩ := exists_isLastPiece_of_run M w hab hxw hpa hconf hhalt
  have hw : w.take x ++ w.drop x ++ ([] : List A) = w := by simp
  have hba : a + (b - a) = b := by omega
  refine ⟨q₀, ?_⟩
  have hk' : Walk.VisitsLe (traj M (w.take x ++ w.drop x ++ ([] : List A))) a (a + (b - a)) k := by
    rw [hw, hba]; exact hk
  have h := widthOut_lastPiece hp hk'
  rw [hw, hba] at h
  simpa using h.symm

/-- A window transducer that stops in its initial state on the empty window
produces no output. -/
lemma widthOut_stopRight_nil (M : TwoWay A B Q) (l r : Option A) (q : Q) (k : ℕ) :
    widthOut (stopRight M l r q q) k [] = [] := by
  classical
  have h0 : cfgAt (stopRight M l r q q) ([] : List A) 0 = some (Cfg.conf [] q []) := rfl
  have hstep : (stopRight M l r q q).stepCfg (Cfg.conf ([] : List A) q []) = some ([], Cfg.halt) :=
    stopRight_stepCfg_stop M
  have h1 : cfgAt (stopRight M l r q q) ([] : List A) 1 = some Cfg.halt :=
    cfgAt_succ_of_step _ _ h0 hstep
  have hex : ∃ T, cfgAt (stopRight M l r q q) ([] : List A) T = some Cfg.halt := ⟨1, h1⟩
  have hrun : runOut (stopRight M l r q q) ([] : List A) = [] := by
    rw [runOut, dif_pos hex, halt_time_unique _ _ hex.choose_spec h1]
    simp [outRange, outAt, h0, hstep]
  rw [widthOut]
  split
  · exact hrun
  · rfl

/-! ### The last piece of a run, entering its window at the right end

The final progress part of the record-breaker decomposition -- from the last
visit to the last record-breaking column to the halting of the run -- need not
stay to the right of that column: once the column is left for the last time the
run stays on one side of it, but that side may be the left one.  In that case
the piece enters its window at the *right* end, which the `IsLastPiece` of
`RequestProject/PartC/SnakePiece.lean` does not cover.  This section provides
the mirrored variant, in the same way as `RequestProject/PartC/SnakePieceRev.lean`
does for the pieces that end at a marked column. -/

section LastRev

variable (M : TwoWay A B Q) (u m z : List A) (q₀ : Q)

/-- The hypotheses under which the last piece of a run of `M` enters its window
at the *right* end: it starts at time `a` at the right end of the window in the
state `q₀`, stays inside the window, and `M` halts at time `a + n + 1`. -/
structure IsLastPieceRev (a n : ℕ) : Prop where
  /-- The piece starts at the right end of the window, in the state `q₀`. -/
  start : cfgAt M (u ++ m ++ z) a = some (Cfg.conf (u ++ m) q₀ z)
  /-- The piece stays inside the window. -/
  confined : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
    u.length ≤ x ∧ x ≤ u.length + m.length
  /-- The run of `M` halts at the end of the piece. -/
  halts : cfgAt M (u ++ m ++ z) (a + n + 1) = some Cfg.halt

variable {M u m z q₀}

/-- One step of the piece, in the mirrored window transducer. -/
lemma stepCfg_mirrorWindow {p s p' s' : List A} {q q' : Q} {o : List B}
    (hps : p ++ s = m) (hps' : p' ++ s' = m)
    (h : M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.conf (u ++ p') q' (s' ++ z))) :
    ((mirror M).withContext z.head? u.getLast? q₀).stepCfg (Cfg.conf s.reverse q p.reverse)
      = some (o, Cfg.conf s'.reverse q' p'.reverse) := by
  have hN := stepCfg_window M u m z q₀ hps hps' h
  have hmir := stepCfg_mirror (M.withContext u.getLast? z.head? q₀) (Cfg.conf p q s)
  rw [hN, mirrorCfg_conf, mirror_withContext] at hmir
  simp only [Option.map_some, mirrorCfg_conf] at hmir
  exact hmir

/-- The halting step of the piece, in the mirrored window transducer. -/
lemma stepCfg_mirrorWindow_halt {p s : List A} {q : Q} {o : List B}
    (h : M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.halt)) :
    ((mirror M).withContext z.head? u.getLast? q₀).stepCfg (Cfg.conf s.reverse q p.reverse)
      = some (o, Cfg.halt) := by
  have hN := stepCfg_window_halt M u z q₀ h
  have hmir := stepCfg_mirror (M.withContext u.getLast? z.head? q₀) (Cfg.conf p q s)
  rw [hN, mirrorCfg_conf, mirror_withContext] at hmir
  simp only [Option.map_some, mirrorCfg_halt] at hmir
  exact hmir

/-- **The last piece of a run, seen in the mirrored window transducer.** -/
theorem cfgAt_lastPieceRev {a n : ℕ} (hp : IsLastPieceRev M u m z q₀ a n) :
    ∀ i ≤ n, ∀ p s q, p ++ s = m →
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) →
      cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse i
        = some (Cfg.conf s.reverse q p.reverse) := by
  intro i
  induction i with
  | zero =>
      intro _ p s q hps hc
      rw [Nat.add_zero, hp.start] at hc
      simp only [Option.some.injEq, Cfg.conf.injEq] at hc
      obtain ⟨h1, h2, h3⟩ := hc
      have hp' : p = m := (List.append_cancel_left h1).symm
      subst hp'
      have hs : s = [] := by
        have : s ++ z = [] ++ z := by simpa using h3
        exact List.append_cancel_right this
      subst hs; subst h2
      simp [cfgAt]
  | succ i ih =>
      intro hin p s q hps hc
      obtain ⟨p₀, s₀, q'', hps₀, hc₀⟩ := window_conf_of_posAt M u m z hp.confined i (by omega)
      have hIH := ih (by omega) p₀ s₀ q'' hps₀ hc₀
      have hc2 : cfgAt M (u ++ m ++ z) ((a + i) + 1) = some (Cfg.conf (u ++ p) q (s ++ z)) := by
        rw [show (a + i) + 1 = a + (i + 1) from by omega]; exact hc
      obtain ⟨c', hc', hstepc⟩ := exists_pred M (u ++ m ++ z) hc2
      rw [hc₀] at hc'
      have hcc : c' = Cfg.conf (u ++ p₀) q'' (s₀ ++ z) := (Option.some_injective _ hc').symm
      subst hcc
      exact cfgAt_succ_of_step _ _ hIH (stepCfg_mirrorWindow hps₀ hps hstepc)

/-- The outputs of the last piece and of the mirrored window run agree, step by
step, before the halting step. -/
theorem outAt_lastPieceRev {a n : ℕ} (hp : IsLastPieceRev M u m z q₀ a n) :
    ∀ i < n, outAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse i
      = outAt M (u ++ m ++ z) (a + i) := by
  intro i hi
  obtain ⟨p, s, q, hps, hc⟩ := window_conf_of_posAt M u m z hp.confined i (by omega)
  obtain ⟨p', s', q', hps', hc'⟩ := window_conf_of_posAt M u m z hp.confined (i + 1) (by omega)
  have hS := cfgAt_lastPieceRev hp i (by omega) p s q hps hc
  obtain ⟨c', hcc, hstepc⟩ :=
    exists_pred M (u ++ m ++ z) (show cfgAt M (u ++ m ++ z) ((a + i) + 1) = _ by
      rw [Nat.add_assoc]; exact hc')
  rw [hc] at hcc
  have hcc' : c' = Cfg.conf (u ++ p) q (s ++ z) := (Option.some_injective _ hcc).symm
  subst hcc'
  rw [outAt_of_step _ _ hS (stepCfg_mirrorWindow hps hps' hstepc)]

/-- The halting step of the last piece, in the mirrored window run. -/
lemma IsLastPieceRev.stepCfg_last {a n : ℕ} (hp : IsLastPieceRev M u m z q₀ a n) :
    ∃ (p s : List A) (q : Q), cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse n
        = some (Cfg.conf s.reverse q p.reverse) ∧
      ((mirror M).withContext z.head? u.getLast? q₀).stepCfg (Cfg.conf s.reverse q p.reverse)
        = some (outAt M (u ++ m ++ z) (a + n), Cfg.halt) := by
  obtain ⟨p, s, q, hps, hc⟩ := window_conf_of_posAt M u m z hp.confined n (le_refl n)
  have hS := cfgAt_lastPieceRev hp n (le_refl n) p s q hps hc
  obtain ⟨c', hc', hstepc⟩ := exists_pred M (u ++ m ++ z) hp.halts
  rw [hc] at hc'
  have hcc : c' = Cfg.conf (u ++ p) q (s ++ z) := (Option.some_injective _ hc').symm
  subst hcc
  exact ⟨p, s, q, hS, stepCfg_mirrorWindow_halt hstepc⟩

theorem lastPieceRev_halt {a n : ℕ} (hp : IsLastPieceRev M u m z q₀ a n) :
    cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse (n + 1) = some Cfg.halt := by
  obtain ⟨p, s, q, hS, hstep⟩ := hp.stepCfg_last
  exact cfgAt_succ_of_step _ _ hS hstep

theorem outAt_lastPieceRev_last {a n : ℕ} (hp : IsLastPieceRev M u m z q₀ a n) :
    outAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse n
      = outAt M (u ++ m ++ z) (a + n) := by
  obtain ⟨p, s, q, hS, hstep⟩ := hp.stepCfg_last
  exact outAt_of_step _ _ hS hstep

/-- Two runs whose steps produce the same output produce the same output over a
range. -/
lemma outRange_shift_eq {N : TwoWay A B Q} {m' : List A} {M' : TwoWay A B Q} {w' : List A}
    (a : ℕ) : ∀ n : ℕ, (∀ i < n, outAt N m' i = outAt M' w' (a + i)) →
      outRange N m' 0 n = outRange M' w' a (a + n) := by
  intro n
  induction n with
  | zero => intro _; simp [outRange]
  | succ n ih =>
      intro h
      have h1 : outRange N m' 0 (n + 1) = outRange N m' 0 n ++ outAt N m' n := by
        rw [outRange, outRange, Nat.sub_zero, Nat.sub_zero, List.range'_concat]
        simp
      have h2 : outRange M' w' a (a + (n + 1))
          = outRange M' w' a (a + n) ++ outAt M' w' (a + n) := by
        rw [outRange, outRange, show a + (n + 1) - a = (a + n - a) + 1 from by omega,
          List.range'_concat]
        simp
      rw [h1, h2, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- **The output of the last piece of a run that enters its window at the right
end is the output of the mirrored window transducer on the reversed window.** -/
theorem runOut_lastPieceRev {a n : ℕ} (hp : IsLastPieceRev M u m z q₀ a n) :
    runOut ((mirror M).withContext z.head? u.getLast? q₀) m.reverse
      = outRange M (u ++ m ++ z) a (a + n + 1) := by
  classical
  have hhalt := lastPieceRev_halt hp
  have hex : ∃ T, cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse T
      = some Cfg.halt := ⟨n + 1, hhalt⟩
  rw [runOut, dif_pos hex,
    halt_time_unique ((mirror M).withContext z.head? u.getLast? q₀) m.reverse
      hex.choose_spec hhalt]
  have hstep : ∀ i < n + 1,
      outAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse i
        = outAt M (u ++ m ++ z) (a + i) := by
    intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · exact outAt_lastPieceRev hp i h
    · have : i = n := by omega
      subst this
      exact outAt_lastPieceRev_last hp
  rw [outRange_shift_eq a (n + 1) hstep, show a + (n + 1) = a + n + 1 from by omega]

/-- The mirrored window run of the last piece has the width of the piece. -/
theorem widthLe_lastPieceRev {a n k : ℕ} (hp : IsLastPieceRev M u m z q₀ a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    WidthLe ((mirror M).withContext z.head? u.getLast? q₀) m.reverse k := by
  classical
  intro y s hs
  have hmem : ∀ t ∈ s, t ≤ n ∧ ∃ x, posAt M (u ++ m ++ z) (a + t) = some x ∧
      u.length ≤ x ∧ x ≤ u.length + m.length ∧ x + y = u.length + m.length := by
    intro t ht
    have hpos := hs t ht
    have htn : t ≤ n := by
      by_contra hcon
      have h1 : cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse t = none ∨
          cfgAt ((mirror M).withContext z.head? u.getLast? q₀) m.reverse t = some Cfg.halt := by
        rcases Nat.lt_or_ge (n + 1) t with h | h
        · exact Or.inl (cfgAt_none_mono _ _ (show n + 1 + 1 ≤ t by omega)
            (cfgAt_halt_succ _ _ (lastPieceRev_halt hp)))
        · have ht1 : t = n + 1 := by omega
          rw [ht1]
          exact Or.inr (lastPieceRev_halt hp)
      rcases h1 with h1 | h1 <;> rw [posAt, h1] at hpos <;> simp at hpos
    obtain ⟨x, hx, h1, h2⟩ := hp.confined t htn
    obtain ⟨p, ss, q, hps, hlen, hc⟩ := window_of_posAt M u m z hx h1 h2
    have hS := cfgAt_lastPieceRev hp t htn p ss q hps hc
    rw [posAt, hS] at hpos
    simp only [Option.bind_some, Option.some.injEq] at hpos
    have hlen2 : p.length + ss.length = m.length := by
      rw [← hps]; simp
    refine ⟨htn, x, hx, h1, h2, ?_⟩
    simp only [List.length_reverse] at hpos
    omega
  refine le_trans (le_of_eq ?_) (hk (u.length + m.length - y) (s.image (fun i => a + i)) ?_)
  · exact (Finset.card_image_of_injective s (fun i j hij => by omega)).symm
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨hin, x, hx, h1, h2, h3⟩ := hmem i hi
    refine ⟨by omega, by omega, ?_⟩
    rw [traj_eq M _ hx]
    omega

/-- **The output of the last piece of a run that enters its window at the right
end is a value of the width-`k` output function of the mirrored window
transducer.** -/
theorem widthOut_lastPieceRev {a n k : ℕ} (hp : IsLastPieceRev M u m z q₀ a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    widthOut ((mirror M).withContext z.head? u.getLast? q₀) k m.reverse
      = outRange M (u ++ m ++ z) a (a + n + 1) := by
  classical
  rw [widthOut, if_pos (widthLe_lastPieceRev hp hk), runOut_lastPieceRev hp]

end LastRev

/-- **The last piece of a run that enters its window at the right end is the
whole run of the mirrored window transducer.** -/
theorem exists_isLastPieceRev_of_run (M : TwoWay A B Q) (w : List A) {a b y : ℕ}
    (hab : a ≤ b) (hyw : y ≤ w.length) (hpa : posAt M w a = some y)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ c ≤ y)
    (hhalt : cfgAt M w (b + 1) = some Cfg.halt) :
    ∃ q₀ : Q, IsLastPieceRev M [] (w.take y) (w.drop y) q₀ a (b - a) := by
  have hw : ([] : List A) ++ w.take y ++ w.drop y = w := by simp
  have hly : (w.take y).length = y := by rw [List.length_take]; omega
  obtain ⟨q₀, hq₀⟩ := exists_cfg_of_posAt M w hpa
  refine ⟨q₀, ?_, ?_, ?_⟩
  · rw [hw]; simpa using hq₀
  · intro i hi
    rw [hw]
    obtain ⟨c, hc, h1⟩ := hconf (a + i) (by omega) (by omega)
    exact ⟨c, hc, by simp, by simpa [hly] using h1⟩
  · rw [hw, show a + (b - a) + 1 = b + 1 from by omega]; exact hhalt

/-- **The output of the last piece of a run that enters its window at the right
end is a value of the width-`k` output function of the mirrored window
transducer.** -/
theorem exists_widthOut_lastPieceRev (M : TwoWay A B Q) (w : List A) {a b y k : ℕ}
    (hab : a ≤ b) (hyw : y ≤ w.length) (hpa : posAt M w a = some y)
    (hconf : ∀ t, a ≤ t → t ≤ b → ∃ c, posAt M w t = some c ∧ c ≤ y)
    (hhalt : cfgAt M w (b + 1) = some Cfg.halt)
    (hk : Walk.VisitsLe (traj M w) a b k) :
    ∃ q₀ : Q, outRange M w a (b + 1)
      = widthOut ((mirror M).withContext (w.drop y).head? none q₀) k (w.take y).reverse := by
  obtain ⟨q₀, hp⟩ := exists_isLastPieceRev_of_run M w hab hyw hpa hconf hhalt
  have hw : ([] : List A) ++ w.take y ++ w.drop y = w := by simp
  have hba : a + (b - a) = b := by omega
  refine ⟨q₀, ?_⟩
  have hk' : Walk.VisitsLe (traj M (([] : List A) ++ w.take y ++ w.drop y)) a (a + (b - a)) k := by
    rw [hw, hba]; exact hk
  have h := widthOut_lastPieceRev hp hk'
  rw [hw, hba] at h
  simpa using h.symm

/-! ### The pieces of the record-breaker decomposition -/

section Parts

variable {M : TwoWay A B Q} {w : List A} {T k : ℕ}

lemma one_le_of_halt (hT : cfgAt M w T = some Cfg.halt) : 1 ≤ T := by
  rcases Nat.eq_zero_or_pos T with rfl | h
  · rw [cfgAt_zero] at hT; simp at hT
  · exact h

/-- Before the end of the run the head is at the column given by the
trajectory. -/
lemma posAt_traj (hT : cfgAt M w T = some Cfg.halt) {t : ℕ} (ht : t ≤ endT M w) :
    posAt M w t = some (traj M w t) := by
  have h1 : 1 ≤ T := one_le_of_halt hT
  rw [endT_eq M w hT] at ht
  obtain ⟨x, hx⟩ := exists_posAt (t := t) M w hT (by omega)
  rw [hx, traj_eq M w hx]

/-- **The two halves of an excursion of a record-breaking column are whole runs
of window transducers on one and the same factor of the input.**  The excursion
is one-sided, so the two halves cross the same window in opposite directions:
the first alternative below is the case of an excursion to the right of the
record-breaking column, the second one that of an excursion to its left.

The window is delimited by the record-breaking column and by the column
furthest away from it that the excursion reaches; which of the two is the left
end depends on the side of the excursion, so the two ends are recorded as the
minimum and the maximum of the two columns.  That identification of the window
is what makes it possible to confine the piece to the two blocks around the
record-breaking column (`Walk.loop_confined`). -/
theorem exists_widthOut_excHalves (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) (hk : 2 ≤ k) (i j : ℕ) :
    ∃ x y : ℕ, x = min (rbCol M w i) (excC M w i j) ∧ y = max (rbCol M w i) (excC M w i j) ∧
      x ≤ y ∧ y ≤ w.length ∧ ∃ q₁ f₁ q₂ f₂ : Q,
      (outRange M w (excT M w i j) (excS M w i j)
          = widthOut (stopRight M (w.take x).getLast? (w.drop y).head? q₁ f₁) (k - 1)
              (seg w x y)
        ∧ outRange M w (excS M w i j) (excT M w i (j + 1))
          = widthOut (stopRight (mirror M) (w.drop y).head? (w.take x).getLast? q₂ f₂) (k - 1)
              (seg w x y).reverse)
      ∨ (outRange M w (excT M w i j) (excS M w i j)
          = widthOut (stopRight (mirror M) (w.drop y).head? (w.take x).getLast? q₁ f₁) (k - 1)
              (seg w x y).reverse
        ∧ outRange M w (excS M w i j) (excT M w i (j + 1))
          = widthOut (stopRight M (w.take x).getLast? (w.drop y).head? q₂ f₂) (k - 1)
              (seg w x y)) := by
  classical
  have hab : excT M w i j ≤ excT M w i (j + 1) := excT_mono_step i j
  have has : excT M w i j ≤ excS M w i j := (excS_bounds i j).1
  have hsb : excS M w i j ≤ excT M w i (j + 1) := (excS_bounds i j).2
  have hbE : excT M w i (j + 1) ≤ endT M w := le_trans (excT_le i (j + 1)) (rbLast_le_endT i)
  have hpa : traj M w (excT M w i j) = rbCol M w i := pos_excT i j
  have hpb : traj M w (excT M w i (j + 1)) = rbCol M w i := pos_excT i (j + 1)
  have hhalves := excHalves_visitsLe hT hwidth hk i j
  rcases eq_or_lt_of_le hab with heq | hlt
  · -- the excursion is empty: both halves produce no output
    have hs1 : excS M w i j = excT M w i j := by omega
    have hs2 : excT M w i (j + 1) = excT M w i j := heq.symm
    have hps : traj M w (excS M w i j) = excC M w i j := Walk.pos_excSplit hab
    have hcol : excC M w i j = rbCol M w i := by rw [← hps, hs1, hpa]
    have hposA : posAt M w (excT M w i j) = some (rbCol M w i) := by
      rw [posAt_traj hT (le_trans hab hbE), hpa]
    have hcw : rbCol M w i ≤ w.length := posAt_le_length M w hposA
    have hseg : seg w (rbCol M w i) (rbCol M w i) = ([] : List A) := by simp [seg]
    refine ⟨rbCol M w i, rbCol M w i, by omega, by omega, le_refl _, hcw,
      M.init, M.init, M.init, M.init, Or.inl ⟨?_, ?_⟩⟩
    · rw [hs1, hseg, widthOut_stopRight_nil]
      simp [outRange]
    · rw [hs1, hs2, hseg, List.reverse_nil, widthOut_stopRight_nil]
      simp [outRange]
  · have hmid : ∀ t, excT M w i j < t → t < excT M w i (j + 1) → traj M w t ≠ rbCol M w i :=
      fun t h1 h2 => Walk.visSeq_no_mid h1 h2
    have hps : traj M w (excS M w i j) = excC M w i j := Walk.pos_excSplit hab
    have hwalk := isWalk_trajE M w hT
    have hab2 : excT M w i j + 1 < excT M w i (j + 1) := by
      rcases eq_or_lt_of_le (show excT M w i j + 1 ≤ excT M w i (j + 1) from hlt) with h | h
      · exfalso
        rcases hwalk (excT M w i j) (by omega) with hst | hst <;> rw [← h] at hpb <;> omega
      · exact h
    have hposb : posAt M w (excT M w i (j + 1)) = some (rbCol M w i) := by
      rw [posAt_traj hT hbE, hpb]
    have hposA : posAt M w (excT M w i j) = some (rbCol M w i) := by
      rw [posAt_traj hT (le_trans hab hbE), hpa]
    have hposS : posAt M w (excS M w i j) = some (excC M w i j) := by
      rw [posAt_traj hT (le_trans hsb hbE), hps]
    rcases Walk.loop_one_sided hwalk hbE hpa hmid with hside | hside
    · -- the excursion goes to the right of the record-breaking column
      have hcol : excC M w i j = Walk.excMax (traj M w) (excT M w i j) (excT M w i (j + 1)) :=
        Walk.excCol_right hwalk hbE hlt hpa hpb hside
      have hrange : ∀ t, excT M w i j ≤ t → t ≤ excT M w i (j + 1) →
          rbCol M w i ≤ traj M w t ∧ traj M w t ≤ excC M w i j := by
        intro t h1 h2
        rw [hcol]
        exact Walk.exc_range_right hab hpa hpb hside h1 h2
      have hltc : rbCol M w i < excC M w i j := by
        have h1 := hside (excT M w i j + 1) (by omega) (by omega)
        have h2 := (hrange (excT M w i j + 1) (by omega) (by omega)).2
        omega
      have hyw : excC M w i j ≤ w.length := posAt_le_length M w hposS
      obtain ⟨q₁, f₁, h1⟩ := exists_widthOut_piece M w has (le_of_lt hltc) hyw hposA hposS
        (fun t ht1 ht2 => ⟨traj M w t, posAt_traj hT (by omega), hrange t ht1 (by omega)⟩)
        (fun t ht1 ht2 hcon => by
          rw [posAt_traj hT (by omega)] at hcon
          exact Walk.excSplit_first hab ht1 ht2 (by simpa using hcon))
        hhalves.1
      obtain ⟨q₂, f₂, h2⟩ := exists_widthOut_pieceRev M w hsb (le_of_lt hltc) hyw hposS hposb
        (fun t ht1 ht2 => ⟨traj M w t, posAt_traj hT (by omega), hrange t (by omega) ht2⟩)
        (fun t ht1 ht2 hcon => by
          rw [posAt_traj hT (by omega)] at hcon
          have hne : excT M w i j < t := by
            rcases eq_or_lt_of_le has with h | h
            · exfalso; rw [← h] at hps; omega
            · omega
          exact hmid t hne ht2 (by simpa using hcon))
        hhalves.2
      exact ⟨rbCol M w i, excC M w i j, by omega, by omega, le_of_lt hltc, hyw,
        q₁, f₁, q₂, f₂, Or.inl ⟨h1, h2⟩⟩
    · -- the excursion goes to the left of the record-breaking column
      have hcol : excC M w i j = Walk.excMin (traj M w) (excT M w i j) (excT M w i (j + 1)) :=
        Walk.excCol_left hwalk hbE hlt hpa hpb hside
      have hrange : ∀ t, excT M w i j ≤ t → t ≤ excT M w i (j + 1) →
          excC M w i j ≤ traj M w t ∧ traj M w t ≤ rbCol M w i := by
        intro t h1 h2
        rw [hcol]
        exact Walk.exc_range_left hab hpa hpb hside h1 h2
      have hltc : excC M w i j < rbCol M w i := by
        have h1 := hside (excT M w i j + 1) (by omega) (by omega)
        have h2 := (hrange (excT M w i j + 1) (by omega) (by omega)).1
        omega
      have hyw : rbCol M w i ≤ w.length := posAt_le_length M w hposA
      obtain ⟨q₁, f₁, h1⟩ := exists_widthOut_pieceRev M w has (le_of_lt hltc) hyw hposA hposS
        (fun t ht1 ht2 => ⟨traj M w t, posAt_traj hT (by omega), hrange t ht1 (by omega)⟩)
        (fun t ht1 ht2 hcon => by
          rw [posAt_traj hT (by omega)] at hcon
          exact Walk.excSplit_first hab ht1 ht2 (by simpa using hcon))
        hhalves.1
      obtain ⟨q₂, f₂, h2⟩ := exists_widthOut_piece M w hsb (le_of_lt hltc) hyw hposS hposb
        (fun t ht1 ht2 => ⟨traj M w t, posAt_traj hT (by omega), hrange t (by omega) ht2⟩)
        (fun t ht1 ht2 hcon => by
          rw [posAt_traj hT (by omega)] at hcon
          have hne : excT M w i j < t := by
            rcases eq_or_lt_of_le has with h | h
            · exfalso; rw [← h] at hps; omega
            · omega
          exact hmid t hne ht2 (by simpa using hcon))
        hhalves.2
      exact ⟨excC M w i j, rbCol M w i, by omega, by omega, le_of_lt hltc, hyw,
        q₁, f₁, q₂, f₂, Or.inr ⟨h1, h2⟩⟩

lemma rbFirst_le_endT (i : ℕ) : rbFirst M w i ≤ endT M w :=
  (Walk.le_firstV_bounds (Walk.visited_recSeq (Nat.zero_le _) i)).2

/-- **The progress part of a record-breaking column that is not the last one is
the whole run of a window transducer**, on the factor of the input between that
record-breaking column and the next one. -/
theorem exists_widthOut_prog (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) (hk : 2 ≤ k) {i : ℕ} (hi : i < rbN M w) :
    ∃ q₀ fin : Q, outRange M w (rbLast M w i) (rbFirst M w (i + 1))
      = widthOut (stopRight M (w.take (rbCol M w i)).getLast?
          (w.drop (rbCol M w (i + 1))).head? q₀ fin) (k - 1)
          (seg w (rbCol M w i) (rbCol M w (i + 1))) := by
  classical
  have hwalk := isWalk_trajE M w hT
  have hns : ¬ Walk.RecStable (traj M w) 0 (endT M w) i := Walk.not_recStable_of_lt_recN hi
  have hab : rbLast M w i ≤ rbFirst M w (i + 1) := Walk.recLast_le_recFirst_succ hns
  have haE : rbLast M w i ≤ endT M w := rbLast_le_endT i
  have hbE : rbFirst M w (i + 1) ≤ endT M w := rbFirst_le_endT (i + 1)
  have hpa : traj M w (rbLast M w i) = rbCol M w i := pos_rbLast i
  have hpb : traj M w (rbFirst M w (i + 1)) = rbCol M w (i + 1) := pos_rbFirst (i + 1)
  have hltc : rbCol M w i < rbCol M w (i + 1) := Walk.lt_recSeq_succ hns
  have hposA : posAt M w (rbLast M w i) = some (rbCol M w i) := by
    rw [posAt_traj hT haE, hpa]
  have hposB : posAt M w (rbFirst M w (i + 1)) = some (rbCol M w (i + 1)) := by
    rw [posAt_traj hT hbE, hpb]
  have hyw : rbCol M w (i + 1) ≤ w.length := posAt_le_length M w hposB
  have hrange : ∀ t, rbLast M w i ≤ t → t ≤ rbFirst M w (i + 1) →
      rbCol M w i ≤ traj M w t ∧ traj M w t ≤ rbCol M w (i + 1) := by
    intro t h1 h2
    refine ⟨?_, Walk.le_recSeq_of_le_recFirst hwalk (Nat.zero_le _) (le_refl _)
      (Nat.zero_le _) h2⟩
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h, hpa]
    · exact le_of_lt (Walk.recSeq_lt_of_recLast_lt hwalk (Nat.zero_le _) (le_refl _) hns h
        (by omega))
  refine exists_widthOut_piece M w hab (le_of_lt hltc) hyw hposA hposB
    (fun t ht1 ht2 => ⟨traj M w t, posAt_traj hT (by omega), hrange t ht1 ht2⟩)
    (fun t ht1 ht2 hcon => ?_) (prog_visitsLe hT hwidth hk hi)
  rw [posAt_traj hT (by omega)] at hcon
  have hvis : t ∈ Walk.visitSet (traj M w) 0 (endT M w) (rbCol M w (i + 1)) :=
    ⟨Nat.zero_le _, by omega, by simpa using hcon⟩
  have h2 : rbFirst M w (i + 1) ≤ t := Walk.firstV_le hvis
  omega

lemma rbLast_eq_lastV (i : ℕ) :
    rbLast M w i = Walk.lastV (traj M w) 0 (endT M w) (rbCol M w i) := rfl

/-- **The last piece of the record-breaker decomposition -- from the last visit
to the last record-breaking column to the halting of the run -- is the whole run
of a window transducer.**  Once the last record-breaking column has been left
for the last time the run stays on one side of it, but that side may be either
one; the two alternatives below are the two cases. -/
theorem exists_widthOut_finalProg (hT : cfgAt M w T = some Cfg.halt)
    (hwidth : WidthLe M w k) (hk : 2 ≤ k) :
    ∃ q₀ : Q,
      outRange M w (rbLast M w (rbN M w)) (haltT M w)
          = widthOut (M.withContext (w.take (rbCol M w (rbN M w))).getLast? none q₀) (k - 1)
              (w.drop (rbCol M w (rbN M w)))
        ∨ outRange M w (rbLast M w (rbN M w)) (haltT M w)
          = widthOut ((mirror M).withContext (w.drop (rbCol M w (rbN M w))).head? none q₀) (k - 1)
              (w.take (rbCol M w (rbN M w))).reverse := by
  classical
  have hT1 : 1 ≤ T := one_le_of_halt hT
  have hTe : endT M w = T - 1 := endT_eq M w hT
  have hTh : haltT M w = T := haltT_eq M w hT
  have hwalk := isWalk_trajE M w hT
  have haE : rbLast M w (rbN M w) ≤ endT M w := rbLast_le_endT (rbN M w)
  have hpa : traj M w (rbLast M w (rbN M w)) = rbCol M w (rbN M w) := pos_rbLast (rbN M w)
  have hposA : posAt M w (rbLast M w (rbN M w)) = some (rbCol M w (rbN M w)) := by
    rw [posAt_traj hT haE, hpa]
  have hcw : rbCol M w (rbN M w) ≤ w.length := posAt_le_length M w hposA
  have hhalt : cfgAt M w (endT M w + 1) = some Cfg.halt := by
    rw [hTe, show T - 1 + 1 = T from by omega]; exact hT
  have hout : haltT M w = endT M w + 1 := by rw [hTh, hTe]; omega
  have hvis : ∀ t, rbLast M w (rbN M w) < t → t ≤ endT M w →
      traj M w t ≠ rbCol M w (rbN M w) := by
    intro t h1 h2 h3
    have h5 : t ≤ Walk.lastV (traj M w) 0 (endT M w) (rbCol M w (rbN M w)) :=
      Walk.le_lastV ⟨Nat.zero_le _, h2, h3⟩
    rw [← rbLast_eq_lastV] at h5
    omega
  have hkw := finalProg_visitsLe hT hwidth hk
  have hside : (∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
        rbCol M w (rbN M w) ≤ traj M w t) ∨
      (∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
        traj M w t ≤ rbCol M w (rbN M w)) := by
    rcases eq_or_lt_of_le haE with heq | hlt
    · left
      intro t h1 h2
      have ht : t = rbLast M w (rbN M w) := by omega
      rw [ht, hpa]
    · rcases Nat.lt_or_ge (rbCol M w (rbN M w)) (traj M w (rbLast M w (rbN M w) + 1)) with
        hgt | hle
      · left
        intro t h1 h2
        rcases eq_or_lt_of_le h1 with h | h
        · rw [← h, hpa]
        · by_contra hcon
          push_neg at hcon
          obtain ⟨τ, hτ1, hτ2, hτ3⟩ := Walk.exists_eq_between hwalk
            (show rbLast M w (rbN M w) + 1 ≤ t from by omega) h2
            (Or.inr ⟨le_of_lt hcon, le_of_lt hgt⟩)
          exact hvis τ (by omega) (by omega) hτ3
      · have hne := hvis (rbLast M w (rbN M w) + 1) (by omega) (by omega)
        have hlt' : traj M w (rbLast M w (rbN M w) + 1) < rbCol M w (rbN M w) := by omega
        right
        intro t h1 h2
        rcases eq_or_lt_of_le h1 with h | h
        · rw [← h, hpa]
        · by_contra hcon
          push_neg at hcon
          obtain ⟨τ, hτ1, hτ2, hτ3⟩ := Walk.exists_eq_between hwalk
            (show rbLast M w (rbN M w) + 1 ≤ t from by omega) h2
            (Or.inl ⟨le_of_lt hlt', le_of_lt hcon⟩)
          exact hvis τ (by omega) (by omega) hτ3
  rcases hside with hside | hside
  · obtain ⟨q₀, h⟩ := exists_widthOut_lastPiece M w haE hcw hposA
      (fun t h1 h2 => ⟨traj M w t, posAt_traj hT h2, hside t h1 h2⟩) hhalt hkw
    exact ⟨q₀, Or.inl (by rw [hout]; exact h)⟩
  · obtain ⟨q₀, h⟩ := exists_widthOut_lastPieceRev M w haE hcw hposA
      (fun t h1 h2 => ⟨traj M w t, posAt_traj hT h2, hside t h1 h2⟩) hhalt hkw
    exact ⟨q₀, Or.inr (by rw [hout]; exact h)⟩

end Parts

end TwoWay

end Lax916827Proofs.Transducers
