/-
Locality of the run of a two-way transducer: a piece of a run that stays inside
a window of the input is the run of a two-way transducer on that window.

This is the bridge that the book's proof of the snake lemma (see
`RequestProject/PartC/SnakeWidth.lean` and `RequestProject/PartC/SnakeReg.lean`)
needs in order to apply the induction hypothesis to the pieces of a run: the
pieces of the record-breaker decomposition are confined to a block of the input
(`RequestProject/PartC/SnakeConfine.lean`), and their outputs have to be
recognised as the values of the width-`(k-1)` output function *on that block*.

A two-way transducer reads the two letters adjacent to its head, so a run
confined to the columns `|u| … |u| + |m|` of the input `u ++ m ++ z` depends
only on the window `m` together with the last letter of `u` and the first letter
of `z`.  Those two letters are built into the transducer:
`M.withContext l r q₀` behaves like `M`, except that when its head stands at the
left (resp. right) end of the input it uses `l` (resp. `r`) as the missing
neighbouring letter.  The main results are

* `TwoWay.cfgAt_window`: the run of `M.withContext u.getLast? z.head? q₀` on `m`
  is the piece of the run of `M` on `u ++ m ++ z`, read in the window;
* `TwoWay.outRange_window`: the two runs produce the same output;
* `TwoWay.widthLe_window`: the window run inherits the width bound of the piece.
-/
import Lax916827Proofs.Source.PartC.SnakeWidth
import Lax916827Proofs.Source.PartC.SnakeMirror
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- The transducer `M` run inside a window of the input: `l` and `r` are the
letters that `M` sees immediately to the left and to the right of the window,
and `q₀` is the state in which the piece of the run starts. -/
def withContext (M : TwoWay A B Q) (l r : Option A) (q₀ : Q) : TwoWay A B Q where
  init := q₀
  step := fun l' q r' => M.step (l'.or l) q (r'.or r)

@[simp] lemma withContext_init (M : TwoWay A B Q) (l r : Option A) (q₀ : Q) :
    (M.withContext l r q₀).init = q₀ := rfl

@[simp] lemma withContext_step (M : TwoWay A B Q) (l r : Option A) (q₀ : Q)
    (l' : Option A) (q : Q) (r' : Option A) :
    (M.withContext l r q₀).step l' q r' = M.step (l'.or l) q (r'.or r) := rfl

variable (M : TwoWay A B Q) (u m z : List A) (q₀ : Q)

/-- Inside the window, the transition of `M.withContext` is the transition of
`M`. -/
lemma step_window (p s : List A) (q : Q) :
    (M.withContext u.getLast? z.head? q₀).step p.getLast? q s.head?
      = M.step (u ++ p).getLast? q (s ++ z).head? := by
  simp [withContext, List.getLast?_append, List.head?_append]

/-- One step of a run confined to the window is one step of the window run. -/
lemma stepCfg_window {p s p' s' : List A} {q q' : Q} {o : List B}
    (hps : p ++ s = m) (hps' : p' ++ s' = m)
    (h : M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.conf (u ++ p') q' (s' ++ z))) :
    (M.withContext u.getLast? z.head? q₀).stepCfg (Cfg.conf p q s) = some (o, Cfg.conf p' q' s') := by
  have hstep := step_window M u z q₀ p s q
  rcases hM : M.step (u ++ p).getLast? q (s ++ z).head? with o'' | ⟨q'', o'', dir⟩
  · rw [stepCfg_halt_eq M hM] at h
    exact absurd (congrArg Prod.snd (Option.some_injective _ h)) (by simp)
  · cases dir with
    | true =>
        rcases hs : s with _ | ⟨b, s₀⟩
        · -- the head would leave the window on the right
          exfalso
          subst hs
          simp only [List.nil_append] at h hps hM
          rcases z with _ | ⟨a, z'⟩
          · rw [stepCfg_right_nil M hM] at h
            simp at h
          · rw [stepCfg_right_cons M hM] at h
            have h2 : Cfg.conf ((u ++ p) ++ [a]) q'' z' = Cfg.conf (u ++ p') q' (s' ++ (a :: z')) :=
              congrArg Prod.snd (Option.some_injective _ h)
            simp only [Cfg.conf.injEq] at h2
            have hlen := congrArg List.length h2.1
            have hlen2 := congrArg List.length hps'
            have hlen3 := congrArg List.length hps
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen hlen2 hlen3
            omega
        · subst hs
          rw [List.cons_append] at h hM
          rw [stepCfg_right_cons M (by simpa using hM)] at h
          have h2 : Cfg.conf ((u ++ p) ++ [b]) q'' (s₀ ++ z) = Cfg.conf (u ++ p') q' (s' ++ z) :=
            congrArg Prod.snd (Option.some_injective _ h)
          have ho : o'' = o := congrArg Prod.fst (Option.some_injective _ h)
          simp only [Cfg.conf.injEq] at h2
          obtain ⟨h21, h22, h23⟩ := h2
          have hp' : p' = p ++ [b] := by
            have := h21
            rw [List.append_assoc] at this
            exact (List.append_cancel_left this).symm
          have hs' : s' = s₀ := (List.append_cancel_right h23).symm
          subst hp'; subst hs'; subst h22; subst ho
          rw [stepCfg_right_cons _ (by rw [hstep]; simpa using hM)]
    | false =>
        rcases hu : (u ++ p).getLast? with _ | a
        · rw [stepCfg_left_none M hu hM] at h
          simp at h
        · rw [stepCfg_left_some M hu hM] at h
          have h2 : Cfg.conf (u ++ p).dropLast q'' (a :: (s ++ z)) =
              Cfg.conf (u ++ p') q' (s' ++ z) :=
            congrArg Prod.snd (Option.some_injective _ h)
          have ho : o'' = o := congrArg Prod.fst (Option.some_injective _ h)
          simp only [Cfg.conf.injEq] at h2
          obtain ⟨h21, h22, h23⟩ := h2
          rcases hp : p.getLast? with _ | c
          · -- the head would leave the window on the left
            exfalso
            have hpnil : p = [] := List.getLast?_eq_none_iff.mp hp
            subst hpnil
            simp only [List.append_nil] at h21 hu
            have hune : u ≠ [] := by
              intro hh; rw [hh] at hu; simp at hu
            have hlen := congrArg List.length h21
            simp only [List.length_dropLast, List.length_append] at hlen
            have : 0 < u.length := List.length_pos_iff.mpr hune
            omega
          · have hpne : p ≠ [] := by
              intro hh; rw [hh] at hp; simp at hp
            have hac : a = c := by
              rw [List.getLast?_append, hp] at hu
              simp only [Option.some_or, Option.some.injEq] at hu
              exact hu.symm
            subst hac
            have hdrop : (u ++ p).dropLast = u ++ p.dropLast := by
              rw [List.dropLast_append_of_ne_nil hpne]
            rw [hdrop] at h21
            have hp' : p' = p.dropLast := (List.append_cancel_left h21).symm
            have hs' : s' = a :: s := by
              have : s' ++ z = (a :: s) ++ z := by simpa using h23.symm
              exact List.append_cancel_right this
            subst hp'; subst hs'; subst h22; subst ho
            rw [stepCfg_left_some _ hp (by rw [hstep]; exact hM)]

/-- A halting step of a run confined to the window is a halting step of the
window run. -/
lemma stepCfg_window_halt {p s : List A} {q : Q} {o : List B}
    (h : M.stepCfg (Cfg.conf (u ++ p) q (s ++ z)) = some (o, Cfg.halt)) :
    (M.withContext u.getLast? z.head? q₀).stepCfg (Cfg.conf p q s) = some (o, Cfg.halt) := by
  have hstep := step_window M u z q₀ p s q
  rcases hM : M.step (u ++ p).getLast? q (s ++ z).head? with o'' | ⟨q'', o'', dir⟩
  · rw [stepCfg_halt_eq M hM] at h
    have ho : o'' = o := congrArg Prod.fst (Option.some_injective _ h)
    subst ho
    exact stepCfg_halt_eq _ (by rw [hstep]; exact hM)
  · exfalso
    cases dir with
    | true =>
        rcases hv : s ++ z with _ | ⟨b, v₀⟩
        · rw [hv] at h hM
          rw [stepCfg_right_nil M hM] at h
          simp at h
        · rw [hv] at h hM
          rw [stepCfg_right_cons M hM] at h
          exact absurd (congrArg Prod.snd (Option.some_injective _ h)) (by simp)
    | false =>
        rcases hu : (u ++ p).getLast? with _ | c
        · rw [stepCfg_left_none M hu hM] at h
          simp at h
        · rw [stepCfg_left_some M hu hM] at h
          exact absurd (congrArg Prod.snd (Option.some_injective _ h)) (by simp)

/-- **Locality of the run.**  If the run of `M` on `u ++ m ++ z` is, at all the
times `a, a+1, …, a+n`, inside the window `m` -- and, at time `a`, at the left
end of the window in the state `q₀` -- then the run of `M.withContext` on `m` is
that piece of the run, read in the window. -/
theorem cfgAt_window {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hconf : ∀ i ≤ n, ∃ p s q, p ++ s = m ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z))) :
    ∀ i ≤ n, ∀ p s q, p ++ s = m →
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) →
      cfgAt (M.withContext u.getLast? z.head? q₀) m i = some (Cfg.conf p q s) := by
  intro i
  induction i with
  | zero =>
      intro _ p s q hps hc
      rw [Nat.add_zero, hstart] at hc
      simp only [Option.some.injEq, Cfg.conf.injEq] at hc
      obtain ⟨h1, h2, h3⟩ := hc
      have hp : p = [] := by
        have := h1.symm
        have hlen := congrArg List.length this
        simp only [List.length_append] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hp
      simp only [List.nil_append] at hps
      subst hps
      subst h2
      simp
  | succ i ih =>
      intro hin p s q hps hc
      obtain ⟨p₀, s₀, q'', hps₀, hc₀⟩ := hconf i (by omega)
      have hIH := ih (by omega) p₀ s₀ q'' hps₀ hc₀
      have hc2 : cfgAt M (u ++ m ++ z) ((a + i) + 1) = some (Cfg.conf (u ++ p) q (s ++ z)) := by
        rw [show (a + i) + 1 = a + (i + 1) from by omega]; exact hc
      obtain ⟨c', hc', hstepc⟩ := exists_pred M (u ++ m ++ z) hc2
      rw [hc₀] at hc'
      have : c' = Cfg.conf (u ++ p₀) q'' (s₀ ++ z) := (Option.some_injective _ hc').symm
      subst this
      have hstepN := stepCfg_window M u m z q₀ hps₀ hps hstepc
      exact cfgAt_succ_of_step _ _ hIH hstepN

/-- The outputs of the piece and of the window run agree, step by step. -/
theorem outAt_window {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hconf : ∀ i ≤ n, ∃ p s q, p ++ s = m ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z))) :
    ∀ i < n, outAt (M.withContext u.getLast? z.head? q₀) m i = outAt M (u ++ m ++ z) (a + i) := by
  intro i hi
  obtain ⟨p, s, q, hps, hc⟩ := hconf i (by omega)
  obtain ⟨p', s', q', hps', hc'⟩ := hconf (i + 1) (by omega)
  have hN := cfgAt_window M u m z q₀ hstart hconf i (by omega) p s q hps hc
  obtain ⟨c', hcc, hstepc⟩ :=
    exists_pred M (u ++ m ++ z) (show cfgAt M (u ++ m ++ z) ((a + i) + 1) = _ by
      rw [Nat.add_assoc]; exact hc')
  rw [hc] at hcc
  have : c' = Cfg.conf (u ++ p) q (s ++ z) := (Option.some_injective _ hcc).symm
  subst this
  have hstepN := stepCfg_window M u m z q₀ hps hps' hstepc
  rw [outAt_of_step _ _ hN hstepN]

/-- Splitting off the first step of an output range. -/
lemma outRange_cons (M : TwoWay A B Q) (w : List A) {a b : ℕ} (hab : a < b) :
    outRange M w a b = outAt M w a ++ outRange M w (a + 1) b := by
  rw [outRange, outRange, show b - a = (b - (a + 1)) + 1 by omega, List.range'_succ]
  simp

/-- **The output of a piece of a run confined to a window** is the output of the
window run. -/
theorem outRange_window {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hconf : ∀ i ≤ n, ∃ p s q, p ++ s = m ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z))) :
    outRange (M.withContext u.getLast? z.head? q₀) m 0 n = outRange M (u ++ m ++ z) a (a + n) := by
  have hout := outAt_window M u m z q₀ hstart hconf
  clear hstart hconf
  have key : ∀ N j : ℕ, j + N = n →
      outRange (M.withContext u.getLast? z.head? q₀) m j n
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
          hout j hjn, ih (j + 1) (by omega), show a + j + 1 = a + (j + 1) from by omega]
  exact key n 0 (by omega)

/-! ### From the columns of the run to the window decomposition -/

/-- A configuration of the run whose column lies inside the window decomposes
along the window. -/
lemma window_of_posAt {t x : ℕ} (hx : posAt M (u ++ m ++ z) t = some x)
    (h1 : u.length ≤ x) (h2 : x ≤ u.length + m.length) :
    ∃ p s q, p ++ s = m ∧ p.length = x - u.length ∧
      cfgAt M (u ++ m ++ z) t = some (Cfg.conf (u ++ p) q (s ++ z)) := by
  rcases hc : cfgAt M (u ++ m ++ z) t with _ | (⟨U, q, V⟩ | _)
  · rw [posAt, hc] at hx; simp at hx
  · rw [posAt, hc] at hx
    simp only [Option.bind_some, Option.some.injEq] at hx
    have hUV : U ++ V = u ++ m ++ z := cfgAt_append M _ t hc
    have hU : U = (u ++ m ++ z).take x := by rw [← hUV, ← hx]; simp
    have hV : V = (u ++ m ++ z).drop x := by rw [← hUV, ← hx]; simp
    refine ⟨m.take (x - u.length), m.drop (x - u.length), q, by simp, by simp; omega, ?_⟩
    have hU' : U = u ++ m.take (x - u.length) := by
      rw [hU]
      simp [List.take_append, List.take_of_length_le h1,
        show x - u.length - m.length = 0 by omega]
    have hV' : V = m.drop (x - u.length) ++ z := by
      rw [hV]
      simp [List.drop_append, List.drop_eq_nil_of_le h1,
        show x - u.length - m.length = 0 by omega]
    rw [hU', hV']
  · rw [posAt, hc] at hx; simp at hx

/-- The confinement hypothesis of `cfgAt_window`, in terms of the columns of the
run. -/
lemma window_conf_of_posAt {a n : ℕ}
    (hpos : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
      u.length ≤ x ∧ x ≤ u.length + m.length) :
    ∀ i ≤ n, ∃ p s q, p ++ s = m ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)) := by
  intro i hi
  obtain ⟨x, hx, h1, h2⟩ := hpos i hi
  obtain ⟨p, s, q, hps, -, hc⟩ := window_of_posAt M u m z hx h1 h2
  exact ⟨p, s, q, hps, hc⟩

/-- The columns of the window run are the columns of the piece, shifted by the
length of the prefix that precedes the window. -/
theorem posAt_window {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hpos : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
      u.length ≤ x ∧ x ≤ u.length + m.length) :
    ∀ i ≤ n, ∀ x, posAt M (u ++ m ++ z) (a + i) = some x →
      posAt (M.withContext u.getLast? z.head? q₀) m i = some (x - u.length) := by
  intro i hi x hx
  obtain ⟨y, hy, h1, h2⟩ := hpos i hi
  rw [hy] at hx
  have hxy : x = y := (Option.some_injective _ hx).symm
  subst hxy
  obtain ⟨p, s, q, hps, hlen, hc⟩ := window_of_posAt M u m z hy h1 h2
  have hN := cfgAt_window M u m z q₀ hstart (window_conf_of_posAt M u m z hpos) i hi p s q hps hc
  rw [posAt, hN]
  simp [hlen]

/-- The window run inherits the width bound of the piece. -/
theorem visitsLe_window {a n k : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hpos : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
      u.length ≤ x ∧ x ≤ u.length + m.length)
    (hk : Walk.VisitsLe (traj M (u ++ m ++ z)) a (a + n) k) :
    Walk.VisitsLe (traj (M.withContext u.getLast? z.head? q₀) m) 0 n k := by
  classical
  intro y s hs
  refine le_trans (le_of_eq ?_) (hk (y + u.length) (s.image (fun i => a + i)) ?_)
  · exact (Finset.card_image_of_injective s (fun i j hij => by omega)).symm
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨-, hin, hy⟩ := hs i hi
    obtain ⟨x, hx, h1, h2⟩ := hpos i hin
    have hNi := posAt_window M u m z q₀ hstart hpos i hin x hx
    rw [traj_eq _ _ hNi] at hy
    refine ⟨by omega, by omega, ?_⟩
    rw [traj_eq M _ hx]
    omega

/-- **The output of a piece of a run confined to a window** is the output of the
window run (the version with the confinement expressed by the columns of the
run). -/
theorem outRange_window_of_pos {a n : ℕ}
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf u q₀ (m ++ z)))
    (hpos : ∀ i ≤ n, ∃ x, posAt M (u ++ m ++ z) (a + i) = some x ∧
      u.length ≤ x ∧ x ≤ u.length + m.length) :
    outRange (M.withContext u.getLast? z.head? q₀) m 0 n = outRange M (u ++ m ++ z) a (a + n) :=
  outRange_window M u m z q₀ hstart (window_conf_of_posAt M u m z hpos)

/-! ### Pieces that do not start at the left end of the window

The pieces of the record-breaker decomposition that run from right to left --
the second half of a one-sided loop, say -- enter the window at its *right* end.
For them the statement above, which is about the run of the window transducer
started in its initial configuration, is not directly applicable; what is
available is the reachability statement below, which does not care where in the
window the piece starts, together with the mirroring of
`RequestProject/PartC/SnakeMirror.lean`: mirroring turns such a piece into a
piece that starts at the left end of the mirrored window. -/

/-- **Locality of the run, for a piece that starts anywhere in the window.**
A piece of the run of `M` that stays inside the window is a run of the window
transducer, with the same output. -/
theorem reaches_window (M : TwoWay A B Q) (u m z : List A) (q₀ : Q) :
    ∀ (n a : ℕ), (∀ i ≤ n, ∃ p s q, p ++ s = m ∧
        cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z))) →
      ∀ p s q p' s' q', p ++ s = m → p' ++ s' = m →
        cfgAt M (u ++ m ++ z) a = some (Cfg.conf (u ++ p) q (s ++ z)) →
        cfgAt M (u ++ m ++ z) (a + n) = some (Cfg.conf (u ++ p') q' (s' ++ z)) →
        (M.withContext u.getLast? z.head? q₀).Reaches (Cfg.conf p q s)
          (outRange M (u ++ m ++ z) a (a + n)) (Cfg.conf p' q' s') := by
  intro n
  induction n with
  | zero =>
      intro a _ p s q p' s' q' _ _ hc hc'
      rw [Nat.add_zero] at hc'
      rw [hc] at hc'
      simp only [Option.some.injEq, Cfg.conf.injEq] at hc'
      obtain ⟨h1, h2, h3⟩ := hc'
      have hp : p = p' := List.append_cancel_left h1
      have hs : s = s' := List.append_cancel_right h3
      subst hp; subst hs; subst h2
      rw [Nat.add_zero, outRange, Nat.sub_self]
      simpa using Reaches.refl _
  | succ n ih =>
      intro a hconf p s q p' s' q' hps hps' hc hc'
      obtain ⟨p₁, s₁, q₁, hps₁, hc₁⟩ := hconf 1 (by omega)
      obtain ⟨c', hcc, hstepc⟩ := exists_pred M (u ++ m ++ z) hc₁
      rw [hc] at hcc
      have : c' = Cfg.conf (u ++ p) q (s ++ z) := (Option.some_injective _ hcc).symm
      subst this
      have hstepN := stepCfg_window M u m z q₀ hps hps₁ hstepc
      have hrec := ih (a + 1) (fun i hi => by
          obtain ⟨pp, ss, qq, h1, h2⟩ := hconf (i + 1) (by omega)
          exact ⟨pp, ss, qq, h1, by rw [show a + 1 + i = a + (i + 1) from by omega]; exact h2⟩)
        p₁ s₁ q₁ p' s' q' hps₁ hps' hc₁
        (by rw [show a + 1 + n = a + (n + 1) from by omega]; exact hc')
      rw [outRange_cons M _ (show a < a + (n + 1) from by omega)]
      rw [show a + 1 + n = a + (n + 1) from by omega] at hrec
      exact Reaches.step hstepN hrec

/-- Mirroring commutes with restricting to a window. -/
lemma mirror_withContext (M : TwoWay A B Q) (l r : Option A) (q₀ : Q) :
    mirror (M.withContext l r q₀) = (mirror M).withContext r l q₀ := by
  simp only [mirror, withContext]

/-- **A piece of a run that enters the window at its right end and leaves it at
its left end** is, after mirroring, a run of the window transducer of the
mirrored transducer on the reversed window, started in its initial
configuration. -/
theorem reaches_window_mirror (M : TwoWay A B Q) (u m z : List A) (q₀ fin : Q) {a n : ℕ}
    (hconf : ∀ i ≤ n, ∃ p s q, p ++ s = m ∧
      cfgAt M (u ++ m ++ z) (a + i) = some (Cfg.conf (u ++ p) q (s ++ z)))
    (hstart : cfgAt M (u ++ m ++ z) a = some (Cfg.conf (u ++ m) q₀ z))
    (hstop : cfgAt M (u ++ m ++ z) (a + n) = some (Cfg.conf u fin (m ++ z))) :
    ((mirror M).withContext z.head? u.getLast? q₀).Reaches (Cfg.conf [] q₀ m.reverse)
      (outRange M (u ++ m ++ z) a (a + n)) (Cfg.conf m.reverse fin []) := by
  have h := reaches_window M u m z q₀ n a hconf m [] q₀ [] m fin (by simp) (by simp)
    (by simpa using hstart) (by simpa using hstop)
  have := reaches_mirror h
  rwa [mirror_withContext, mirrorCfg_conf, mirrorCfg_conf, List.reverse_nil] at this

end TwoWay

end Lax916827Proofs.Transducers
