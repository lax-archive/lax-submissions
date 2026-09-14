/-
Pieces of a run that go from right to left.

`RequestProject/PartC/SnakePiece.lean` presents a piece of a run that enters its
window at the left end and ends at the first visit to the right end as the whole
run of a two-way transducer on the window.  The record-breaker decomposition of
the book's snake lemma also produces pieces that go the other way -- the second
half of a one-sided loop, for instance, returns from the furthest column to the
base column.  The book deals with them by *reversing the snake*; here this is
the mirroring of `RequestProject/PartC/SnakeMirror.lean`.

The result of this file is that a piece which enters its window at the right end
and ends at the first visit to the left end in the state `fin` is the whole run
of `stopRight (mirror M) z.head? u.getLast? q₀ fin` on the *reversed* window,
with the same output and the same width (`TwoWay.runOut_pieceRev`,
`TwoWay.widthOut_pieceRev`).  Together with `SnakePiece.lean` this covers all
the pieces of the decomposition.
-/
import Lax916827Proofs.Source.PartC.SnakePiece
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type} (M : TwoWay A B Q) (u m z : List A) (q₀ fin : Q)

/-- The hypotheses under which a piece of the run of `M` on `u ++ m ++ z` is,
after mirroring, the whole run of a window transducer: the piece starts at time
`a` at the *right* end of the window in the state `q₀`, stays inside the window,
and reaches the *left* end of the window in the state `fin` for the first time
at time `a + n`. -/
structure IsPieceRev (a n : ℕ) : Prop where
  /-- The piece starts at the right end of the window, in the state `q₀`. -/
  start : cfgAt M (u ++ m ++ z) a = some (Cfg.conf (u ++ m) q₀ z)
  /-- The piece stays inside the window. -/
  confined : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
    u.length ≤ x ∧ x ≤ u.length + m.length
  /-- The piece does not reach its target before its end. -/
  early : ∀ i < n, cfgAt M (u ++ m ++ z) (a + i) ≠ some (Cfg.conf u fin (m ++ z))
  /-- The piece ends at the left end of the window, in the state `fin`. -/
  stop : cfgAt M (u ++ m ++ z) (a + n) = some (Cfg.conf u fin (m ++ z))

variable {M u m z q₀ fin}

/-- One step of a right-to-left piece, in the mirrored window transducer. -/
lemma stepCfg_pieceRev {p s p' s' : List A} {q q' : Q} {o : List B}
    (hps : p ++ s = m) (hps' : p' ++ s' = m) (hne : ¬ (p = [] ∧ q = fin))
    (h : M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.conf (u ++ p') q' (s' ++ z))) :
    (stopRight (mirror M) z.head? u.getLast? q₀ fin).stepCfg (Cfg.conf s.reverse q p.reverse)
      = some (o, Cfg.conf s'.reverse q' p'.reverse) := by
  have hN := stepCfg_window M u m z q₀ hps hps' h
  have hmir := stepCfg_mirror (M.withContext u.getLast? z.head? q₀) (Cfg.conf p q s)
  rw [hN, mirrorCfg_conf, mirror_withContext] at hmir
  simp only [Option.map_some, mirrorCfg_conf] at hmir
  rw [stopRight_stepCfg_eq (mirror M) (l := z.head?) (r := u.getLast?) (q₀ := q₀) (fin := fin)
    (p := s.reverse) (s := p.reverse) (by
      rintro ⟨h1, h2⟩
      exact hne ⟨by simpa using h1, h2⟩)]
  exact hmir

/-- **A right-to-left piece of a run is the run of the mirrored window
transducer on the reversed window.** -/
theorem cfgAt_pieceRev {a n : ℕ} (hp : IsPieceRev M u m z q₀ fin a n) :
    ∀ i ≤ n, ∀ p s q, p ++ s = m →
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) →
      cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse i
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
      have hne : ¬ (p₀ = [] ∧ q'' = fin) := by
        rintro ⟨rfl, rfl⟩
        simp only [List.nil_append] at hps₀
        subst hps₀
        exact hp.early i (by omega) (by simpa using hc₀)
      exact cfgAt_succ_of_step _ _ hIH (stepCfg_pieceRev hps₀ hps hne hstepc)

/-- The outputs of a right-to-left piece and of the mirrored window run agree,
step by step. -/
theorem outAt_pieceRev {a n : ℕ} (hp : IsPieceRev M u m z q₀ fin a n) :
    ∀ i < n, outAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse i
      = outAt M (u ++ m ++ z) (a + i) := by
  intro i hi
  obtain ⟨p, s, q, hps, hc⟩ := window_conf_of_posAt M u m z hp.confined i (by omega)
  obtain ⟨p', s', q', hps', hc'⟩ := window_conf_of_posAt M u m z hp.confined (i + 1) (by omega)
  have hS := cfgAt_pieceRev hp i (by omega) p s q hps hc
  obtain ⟨c', hcc, hstepc⟩ :=
    exists_pred M (u ++ m ++ z) (show cfgAt M (u ++ m ++ z) ((a + i) + 1) = _ by
      rw [Nat.add_assoc]; exact hc')
  rw [hc] at hcc
  have hcc' : c' = Cfg.conf (u ++ p) q (s ++ z) := (Option.some_injective _ hcc).symm
  subst hcc'
  have hne : ¬ (p = [] ∧ q = fin) := by
    rintro ⟨rfl, rfl⟩
    simp only [List.nil_append] at hps
    subst hps
    exact hp.early i hi (by simpa using hc)
  rw [outAt_of_step _ _ hS (stepCfg_pieceRev hps hps' hne hstepc)]

/-- The mirrored window run of a right-to-left piece is at the right end of the
reversed window, in the state `fin`, at the end of the piece. -/
lemma IsPieceRev.cfgAt_last {a n : ℕ} (hp : IsPieceRev M u m z q₀ fin a n) :
    cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse n
      = some (Cfg.conf m.reverse fin []) :=
  cfgAt_pieceRev hp n (le_refl n) [] m fin (by simp) (by simpa using hp.stop)

/-- The mirrored window run halts one step after the end of the piece. -/
theorem pieceRev_halt {a n : ℕ} (hp : IsPieceRev M u m z q₀ fin a n) :
    cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse (n + 1) = some Cfg.halt := by
  rw [cfgAt_succ, hp.cfgAt_last]
  simp [stopRight_stepCfg_stop (mirror M)]

/-- **The output of a right-to-left piece of a run is the output of the mirrored
window transducer on the reversed window.** -/
theorem runOut_pieceRev {a n : ℕ} (hp : IsPieceRev M u m z q₀ fin a n) :
    runOut (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse
      = outRange M (u ++ m ++ z) a (a + n) := by
  classical
  have hhalt := pieceRev_halt hp
  have hex : ∃ T, cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse T
      = some Cfg.halt := ⟨n + 1, hhalt⟩
  rw [runOut, dif_pos hex,
    halt_time_unique (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse
      hex.choose_spec hhalt]
  have hlast : outAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse n = [] := by
    simp only [outAt, hp.cfgAt_last]
    simp [stopRight_stepCfg_stop (mirror M)]
  have hsplit : outRange (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse 0 (n + 1)
      = outRange (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse 0 n
        ++ outAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse n := by
    rw [outRange, outRange, Nat.sub_zero, Nat.sub_zero, List.range'_concat]
    simp
  rw [hsplit, hlast, List.append_nil]
  -- the two runs produce the same output at every step of the piece
  have key : ∀ N j : ℕ, j + N = n →
      outRange (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse j n
        = outRange M (u ++ m ++ z) (a + j) (a + n) := by
    intro N
    induction N with
    | zero =>
        intro j hj
        rw [show j = n from by omega]
        simp [outRange]
    | succ N ih =>
        intro j hj
        have hjn : j < n := by omega
        rw [outRange_cons _ _ hjn, outRange_cons M _ (show a + j < a + n from by omega),
          outAt_pieceRev hp j hjn, ih (j + 1) (by omega),
          show a + j + 1 = a + (j + 1) from by omega]
  simpa using key n 0 (by omega)

/-- The mirrored window run of a right-to-left piece has the width of the
piece. -/
theorem widthLe_pieceRev {a n k : ℕ} (hp : IsPieceRev M u m z q₀ fin a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    WidthLe (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse k := by
  classical
  intro y s hs
  -- the reversed run is over after the halting time
  have hmem : ∀ t ∈ s, t ≤ n ∧ ∃ x, posAt M (u ++ m ++ z) (a + t) = some x ∧
      u.length ≤ x ∧ x ≤ u.length + m.length ∧ x + y = u.length + m.length := by
    intro t ht
    have hpos := hs t ht
    have htn : t ≤ n := by
      by_contra hcon
      have h1 : cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse t = none ∨
          cfgAt (stopRight (mirror M) z.head? u.getLast? q₀ fin) m.reverse t = some Cfg.halt := by
        rcases Nat.lt_or_ge (n + 1) t with h | h
        · exact Or.inl (cfgAt_none_mono _ _ (show n + 1 + 1 ≤ t by omega)
            (cfgAt_halt_succ _ _ (pieceRev_halt hp)))
        · have ht1 : t = n + 1 := by omega
          rw [ht1]
          exact Or.inr (pieceRev_halt hp)
      rcases h1 with h1 | h1 <;> rw [posAt, h1] at hpos <;> simp at hpos
    obtain ⟨x, hx, h1, h2⟩ := hp.confined t htn
    obtain ⟨p, ss, q, hps, hlen, hc⟩ := window_of_posAt M u m z hx h1 h2
    have hS := cfgAt_pieceRev hp t htn p ss q hps hc
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

/-- **The output of a right-to-left piece of a run is a value of the width-`k`
output function of the mirrored window transducer.** -/
theorem widthOut_pieceRev {a n k : ℕ} (hp : IsPieceRev M u m z q₀ fin a n)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    widthOut (stopRight (mirror M) z.head? u.getLast? q₀ fin) k m.reverse
      = outRange M (u ++ m ++ z) a (a + n) := by
  classical
  rw [widthOut, if_pos (widthLe_pieceRev hp hk), runOut_pieceRev hp]

end TwoWay

end Lax916827Proofs.Transducers
