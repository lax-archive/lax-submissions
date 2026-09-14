/-
A piece of a run, seen as a complete run of a two-way transducer on a block of
the input.

`RequestProject/PartC/SnakeLocal.lean` shows that a piece of a run of `M` that
stays inside a window `m` of the input `u ++ m ++ z` is a piece of the run of
`M.withContext u.getLast? z.head? q₀` on `m`.  For the induction of the book's
snake lemma this is not quite enough: the induction hypothesis speaks about the
*whole* run of a transducer, from its initial configuration until it halts, so
the transducer used for a piece has to halt exactly where the piece ends.

The pieces produced by the record-breaker decomposition all start at the
leftmost column they visit and -- apart from the very last one, which ends when
the whole run halts -- end at the *first* visit to the rightmost column they
visit.  This file therefore introduces `TwoWay.stopRight M l r q₀ fin`, the
window transducer that halts as soon as its head reaches the right end of the
window in the state `fin`, and proves that such a piece of a run of `M` *is* the
whole run of `stopRight`:

* `TwoWay.cfgAt_stopRight`: the run of `stopRight` follows the piece;
* `TwoWay.stopRight_halt`: it halts one step after the end of the piece;
* `TwoWay.runOut_stopRight`: its output is the output of the piece;
* `TwoWay.widthLe_stopRight`: it has the width of the piece;
* `TwoWay.widthOut_stopRight`: consequently the piece output is the value, on
  the window, of the width-`k` output function of `stopRight`, which is the
  function that the induction hypothesis of the snake lemma applies to.
-/
import Lax916827Proofs.Source.PartC.SnakeLocal
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

open scoped Classical in
/-- The window transducer of `RequestProject/PartC/SnakeLocal.lean`, modified so
that it halts as soon as its head reaches the right end of the window in the
state `fin`. -/
noncomputable def stopRight (M : TwoWay A B Q) (l r : Option A) (q₀ fin : Q) : TwoWay A B Q where
  init := q₀
  step := fun l' q r' => if r' = none ∧ q = fin then Sum.inl [] else M.step (l'.or l) q (r'.or r)

@[simp] lemma stopRight_init (M : TwoWay A B Q) (l r : Option A) (q₀ fin : Q) :
    (stopRight M l r q₀ fin).init = q₀ := rfl

variable (M : TwoWay A B Q)

/-- Away from the stopping configuration, the modified transducer behaves like
the window transducer. -/
lemma stopRight_step_eq {l r : Option A} {q₀ fin q : Q} {p s : List A}
    (hne : ¬ (s = [] ∧ q = fin)) :
    (stopRight M l r q₀ fin).step p.getLast? q s.head?
      = (M.withContext l r q₀).step p.getLast? q s.head? := by
  classical
  simp only [stopRight, withContext]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hne ⟨List.head?_eq_none_iff.mp h1, h2⟩

/-- Away from the stopping configuration, the two transducers take the same
step. -/
lemma stopRight_stepCfg_eq {l r : Option A} {q₀ fin q : Q} {p s : List A}
    (hne : ¬ (s = [] ∧ q = fin)) :
    (stopRight M l r q₀ fin).stepCfg (Cfg.conf p q s)
      = (M.withContext l r q₀).stepCfg (Cfg.conf p q s) := by
  simp only [stepCfg, stopRight_step_eq M hne]

/-- At the stopping configuration, the modified transducer halts with no
output. -/
lemma stopRight_stepCfg_stop {l r : Option A} {q₀ fin : Q} {p : List A} :
    (stopRight M l r q₀ fin).stepCfg (Cfg.conf p fin []) = some ([], Cfg.halt) := by
  classical
  have h : (stopRight M l r q₀ fin).step p.getLast? fin ([] : List A).head? = Sum.inl [] := by
    simp [stopRight]
  simp only [stepCfg, h]

variable (u m z : List A) (q₀ fin : Q)

/-- The hypotheses under which a piece of the run of `M` on `u ++ m ++ z` is the
whole run of `stopRight`: the piece starts at time `a` at the left end of the
window in the state `q₀`, stays inside the window, and reaches the right end of
the window in the state `fin` for the first time at time `a + n`. -/
structure IsPiece (a n : ℕ) : Prop where
  /-- The piece starts at the left end of the window, in the state `q₀`. -/
  start : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z))
  /-- The piece stays inside the window. -/
  confined : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
    u.length ≤ x ∧ x ≤ u.length + m.length
  /-- The piece does not reach its target before its end. -/
  early : ∀ i < n, cfgAt M (u ++ m ++ z) (a + i) ≠ some (Cfg.conf (u ++ m) fin z)
  /-- The piece ends at the right end of the window, in the state `fin`. -/
  stop : cfgAt M (u ++ m ++ z) (a + n) = some (Cfg.conf (u ++ m) fin z)

variable {M u m z q₀ fin}

/-- The window run, at the times of the piece. -/
lemma IsPiece.cfgAt_window {a n : ℕ} (hp : IsPiece M u m z q₀ fin a n) :
    ∀ i ≤ n, ∀ p s q, p ++ s = m →
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) →
      cfgAt (M.withContext u.getLast? z.head? q₀) m i = some (Cfg.conf p q s) :=
  TwoWay.cfgAt_window M u m z q₀ hp.start (window_conf_of_posAt M u m z hp.confined)

/-- At the end of the piece, the window run is at the right end of the window in
the state `fin`. -/
lemma IsPiece.cfgAt_window_last {a n : ℕ} (hp : IsPiece M u m z q₀ fin a n) :
    cfgAt (M.withContext u.getLast? z.head? q₀) m n = some (Cfg.conf m fin []) :=
  hp.cfgAt_window n (le_refl n) m [] fin (by simp) (by simpa using hp.stop)

/-- Before the end of the piece, the window run is not at the right end of the
window in the state `fin`. -/
lemma IsPiece.not_stop {a n : ℕ} (hp : IsPiece M u m z q₀ fin a n) {i : ℕ} (hi : i < n)
    {p s : List A} {q : Q} (hps : p ++ s = m)
    (hc : cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z))) :
    ¬ (s = [] ∧ q = fin) := by
  rintro ⟨rfl, rfl⟩
  simp only [List.append_nil] at hps
  subst hps
  exact hp.early i hi (by simpa using hc)

/-- **A piece of a run is the run of `stopRight`**: up to the end of the piece,
the two runs agree. -/
theorem cfgAt_stopRight {a n : ℕ} (hp : IsPiece M u m z q₀ fin a n) :
    ∀ i ≤ n, cfgAt (stopRight M u.getLast? z.head? q₀ fin) m i
      = cfgAt (M.withContext u.getLast? z.head? q₀) m i := by
  intro i
  induction i with
  | zero => intro _; simp [cfgAt]
  | succ i ih =>
      intro hi
      obtain ⟨p, s, q, hps, hc⟩ := window_conf_of_posAt M u m z hp.confined i (by omega)
      have hW := hp.cfgAt_window i (by omega) p s q hps hc
      have hne := hp.not_stop (by omega) hps hc
      simp only [cfgAt_succ, ih (by omega), hW, Option.bind_some, stopRight_stepCfg_eq M hne]

/-- The outputs of the two runs agree up to the end of the piece. -/
theorem outAt_stopRight {a n : ℕ} (hp : IsPiece M u m z q₀ fin a n) :
    ∀ i < n, outAt (stopRight M u.getLast? z.head? q₀ fin) m i
      = outAt (M.withContext u.getLast? z.head? q₀) m i := by
  intro i hi
  obtain ⟨p, s, q, hps, hc⟩ := window_conf_of_posAt M u m z hp.confined i (by omega)
  have hW := hp.cfgAt_window i (by omega) p s q hps hc
  have hne := hp.not_stop hi hps hc
  simp only [outAt, cfgAt_stopRight hp i (by omega), hW, Option.bind_some,
    stopRight_stepCfg_eq M hne]

/-- `stopRight` halts one step after the end of the piece. -/
theorem stopRight_halt {a n : ℕ} (hp : IsPiece M u m z q₀ fin a n) :
    cfgAt (stopRight M u.getLast? z.head? q₀ fin) m (n + 1) = some Cfg.halt := by
  rw [cfgAt_succ, cfgAt_stopRight hp n (le_refl n), hp.cfgAt_window_last]
  simp [stopRight_stepCfg_stop M]

/-- **The output of a piece of a run is the output of the run of `stopRight` on
the window.** -/
theorem runOut_stopRight {a n : ℕ} (hp : IsPiece M u m z q₀ fin a n) :
    runOut (stopRight M u.getLast? z.head? q₀ fin) m = outRange M (u ++ m ++ z) a (a + n) := by
  classical
  have hhalt := stopRight_halt hp
  have hex : ∃ T, cfgAt (stopRight M u.getLast? z.head? q₀ fin) m T = some Cfg.halt := ⟨n + 1, hhalt⟩
  rw [runOut, dif_pos hex,
    halt_time_unique (stopRight M u.getLast? z.head? q₀ fin) m hex.choose_spec hhalt]
  -- the last step produces no output
  have hlast : outAt (stopRight M u.getLast? z.head? q₀ fin) m n = [] := by
    simp only [outAt, cfgAt_stopRight hp n (le_refl n), hp.cfgAt_window_last]
    simp [stopRight_stepCfg_stop M]
  have hsplit : outRange (stopRight M u.getLast? z.head? q₀ fin) m 0 (n + 1)
      = outRange (stopRight M u.getLast? z.head? q₀ fin) m 0 n
        ++ outAt (stopRight M u.getLast? z.head? q₀ fin) m n := by
    rw [outRange, outRange, Nat.sub_zero, Nat.sub_zero, List.range'_concat]
    simp
  rw [hsplit, hlast, List.append_nil]
  have hout : outRange (stopRight M u.getLast? z.head? q₀ fin) m 0 n
      = outRange (M.withContext u.getLast? z.head? q₀) m 0 n := by
    rw [outRange, outRange]
    congr 1
    refine List.map_congr_left ?_
    intro i hi
    have : i < n := by
      have := List.mem_range'.1 hi
      omega
    exact outAt_stopRight hp i this
  rw [hout, outRange_window_of_pos M u m z q₀ hp.start hp.confined]

/-- The run of `stopRight` has the width of the piece. -/
theorem widthLe_stopRight {a n k : ℕ} (hp : IsPiece M u m z q₀ fin a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    WidthLe (stopRight M u.getLast? z.head? q₀ fin) m k := by
  classical
  have hvis := visitsLe_window M u m z q₀ hp.start hp.confined hk
  intro x s hs
  refine hvis x s ?_
  intro t ht
  have hpos := hs t ht
  -- after the halting time the run of `stopRight` is over, so `t ≤ n`
  have htn : t ≤ n := by
    by_contra hcon
    have h1 : cfgAt (stopRight M u.getLast? z.head? q₀ fin) m t = none ∨
        cfgAt (stopRight M u.getLast? z.head? q₀ fin) m t = some Cfg.halt := by
      rcases Nat.lt_or_ge (n + 1) t with h | h
      · exact Or.inl (cfgAt_none_mono _ _ (show n + 1 + 1 ≤ t by omega)
          (cfgAt_halt_succ _ _ (stopRight_halt hp)))
      · have ht1 : t = n + 1 := by omega
        rw [ht1]
        exact Or.inr (stopRight_halt hp)
    rcases h1 with h1 | h1 <;> rw [posAt, h1] at hpos <;> simp at hpos
  have hposeq : posAt (stopRight M u.getLast? z.head? q₀ fin) m t
      = posAt (M.withContext u.getLast? z.head? q₀) m t := by
    simp only [posAt, cfgAt_stopRight hp t htn]
  rw [hposeq] at hpos
  exact ⟨Nat.zero_le _, htn, traj_eq _ _ hpos⟩

/-- **The output of a piece of a run is a value of the width-`k` output function
of `stopRight`**, which is the function to which the induction hypothesis of the
snake lemma applies. -/
theorem widthOut_stopRight {a n k : ℕ} (hp : IsPiece M u m z q₀ fin a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    widthOut (stopRight M u.getLast? z.head? q₀ fin) k m = outRange M (u ++ m ++ z) a (a + n) := by
  classical
  rw [widthOut, if_pos (widthLe_stopRight hp hk), runOut_stopRight hp]

/-! ### The last piece of a run

The final piece of the record-breaker decomposition does not end at a marked
column: it ends when `M` halts.  For such a piece the window transducer
`withContext` needs no modification -- it halts exactly when `M` does. -/

variable (M u m z q₀)

/-- The hypotheses under which the *last* piece of a run of `M` -- the piece
that ends when `M` halts -- is the whole run of the window transducer: it starts
at time `a` at the left end of the window in the state `q₀`, stays inside the
window, and `M` halts at time `a + n + 1`. -/
structure IsLastPiece (a n : ℕ) : Prop where
  /-- The piece starts at the left end of the window, in the state `q₀`. -/
  start : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z))
  /-- The piece stays inside the window. -/
  confined : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
    u.length ≤ x ∧ x ≤ u.length + m.length
  /-- The run of `M` halts at the end of the piece. -/
  halts : cfgAt M (u ++ m ++ z) (a + n + 1) = some Cfg.halt

variable {M u m z q₀}

/-- The last step of the last piece, in the window run. -/
lemma IsLastPiece.stepCfg_last {a n : ℕ} (hp : IsLastPiece M u m z q₀ a n) :
    ∃ p s q, cfgAt (M.withContext u.getLast? z.head? q₀) m n = some (Cfg.conf p q s) ∧
      (M.withContext u.getLast? z.head? q₀).stepCfg (Cfg.conf p q s)
        = some (outAt M (u ++ m ++ z) (a + n), Cfg.halt) := by
  obtain ⟨p, s, q, hps, hc⟩ := window_conf_of_posAt M u m z hp.confined n (le_refl n)
  have hW := TwoWay.cfgAt_window M u m z q₀ hp.start
    (window_conf_of_posAt M u m z hp.confined) n (le_refl n) p s q hps hc
  obtain ⟨c', hc', hstepc⟩ := exists_pred M (u ++ m ++ z) hp.halts
  rw [hc] at hc'
  have hc'' : c' = Cfg.conf (u ++ p) q (s ++ z) := (Option.some_injective _ hc').symm
  subst hc''
  exact ⟨p, s, q, hW, stepCfg_window_halt M u z q₀ hstepc⟩

/-- The window run of the last piece halts where `M` halts. -/
theorem lastPiece_halt {a n : ℕ} (hp : IsLastPiece M u m z q₀ a n) :
    cfgAt (M.withContext u.getLast? z.head? q₀) m (n + 1) = some Cfg.halt := by
  obtain ⟨p, s, q, hW, hstep⟩ := hp.stepCfg_last
  exact cfgAt_succ_of_step _ _ hW hstep

/-- The last step of the last piece produces the same output in both runs. -/
theorem outAt_lastPiece {a n : ℕ} (hp : IsLastPiece M u m z q₀ a n) :
    outAt (M.withContext u.getLast? z.head? q₀) m n = outAt M (u ++ m ++ z) (a + n) := by
  obtain ⟨p, s, q, hW, hstep⟩ := hp.stepCfg_last
  exact outAt_of_step _ _ hW hstep

/-- **The output of the last piece of a run is the output of the window
transducer.** -/
theorem runOut_lastPiece {a n : ℕ} (hp : IsLastPiece M u m z q₀ a n) :
    runOut (M.withContext u.getLast? z.head? q₀) m = outRange M (u ++ m ++ z) a (a + n + 1) := by
  classical
  have hhalt := lastPiece_halt hp
  have hex : ∃ T, cfgAt (M.withContext u.getLast? z.head? q₀) m T = some Cfg.halt := ⟨n + 1, hhalt⟩
  rw [runOut, dif_pos hex,
    halt_time_unique (M.withContext u.getLast? z.head? q₀) m hex.choose_spec hhalt]
  have hsplit : outRange (M.withContext u.getLast? z.head? q₀) m 0 (n + 1)
      = outRange (M.withContext u.getLast? z.head? q₀) m 0 n
        ++ outAt (M.withContext u.getLast? z.head? q₀) m n := by
    rw [outRange, outRange, Nat.sub_zero, Nat.sub_zero, List.range'_concat]
    simp
  have hsplit' : outRange M (u ++ m ++ z) a (a + n + 1)
      = outRange M (u ++ m ++ z) a (a + n) ++ outAt M (u ++ m ++ z) (a + n) := by
    rw [outRange, outRange, show a + n + 1 - a = (a + n - a) + 1 by omega, List.range'_concat]
    simp
  rw [hsplit, hsplit', outAt_lastPiece hp,
    outRange_window_of_pos M u m z q₀ hp.start hp.confined]

/-- The window run of the last piece has the width of the piece. -/
theorem widthLe_lastPiece {a n k : ℕ} (hp : IsLastPiece M u m z q₀ a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    WidthLe (M.withContext u.getLast? z.head? q₀) m k := by
  classical
  have hvis := visitsLe_window M u m z q₀ hp.start hp.confined hk
  intro x s hs
  refine hvis x s ?_
  intro t ht
  have hpos := hs t ht
  have htn : t ≤ n := by
    by_contra hcon
    have h1 : cfgAt (M.withContext u.getLast? z.head? q₀) m t = none ∨
        cfgAt (M.withContext u.getLast? z.head? q₀) m t = some Cfg.halt := by
      rcases Nat.lt_or_ge (n + 1) t with h | h
      · exact Or.inl (cfgAt_none_mono _ _ (show n + 1 + 1 ≤ t by omega)
          (cfgAt_halt_succ _ _ (lastPiece_halt hp)))
      · have ht1 : t = n + 1 := by omega
        rw [ht1]
        exact Or.inr (lastPiece_halt hp)
    rcases h1 with h1 | h1 <;> rw [posAt, h1] at hpos <;> simp at hpos
  exact ⟨Nat.zero_le _, htn, traj_eq _ _ hpos⟩

/-- **The output of the last piece of a run is a value of the width-`k` output
function of the window transducer.** -/
theorem widthOut_lastPiece {a n k : ℕ} (hp : IsLastPiece M u m z q₀ a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    widthOut (M.withContext u.getLast? z.head? q₀) k m
      = outRange M (u ++ m ++ z) a (a + n + 1) := by
  classical
  rw [widthOut, if_pos (widthLe_lastPiece hp hk), runOut_lastPiece hp]

end TwoWay

end Lax916827Proofs.Transducers
