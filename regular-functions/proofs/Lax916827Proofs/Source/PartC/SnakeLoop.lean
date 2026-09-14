/-
Splitting a looping part of a walk into pieces of smaller width.

This file continues `RequestProject/PartC/SnakeWalk.lean` and
`RequestProject/PartC/SnakeRec.lean`.  Following the book's proof of the snake
lemma (see `RequestProject/PartC/SnakeWidth.lean`), the *loop part* of a
record-breaking column -- the piece of the walk between the first and the last
visit to that column -- is cut into finitely many pieces, each of which visits
every column at most `k - 1` times, where `k` bounds the number of visits of the
whole walk:

* first, at every intermediate visit to the base column, which leaves *one-sided*
  loops: pieces that do not return to the base column in between;
* then, each one-sided loop is cut at the first visit to its furthest column;
  both halves have smaller width, because the furthest column is not reached
  again in the other half.

The second point is proved in `RequestProject/PartC/SnakeWalk.lean` for loops
that lie to the right of their base column; the loops that lie to the left are
reduced to those by reflecting the walk (`Transducers.Walk.mir`).
-/
import Lax916827Proofs.Source.PartC.SnakeRec
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace Walk

variable {p : ℕ → ℕ} {T : ℕ}

/-! ### The furthest column of a piece of a walk -/

/-- A piece of a walk has a rightmost column, and that column is visited. -/
lemma exists_max_col (p : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ m, Visited p a b m ∧ ∀ t, a ≤ t → t ≤ b → p t ≤ m := by
  classical
  set s : Finset ℕ := (Finset.Icc a b).image p with hs
  have hne : s.Nonempty := ⟨p a, Finset.mem_image.2 ⟨a, Finset.mem_Icc.2 ⟨le_refl _, hab⟩, rfl⟩⟩
  refine ⟨s.max' hne, ?_, ?_⟩
  · obtain ⟨t, ht, hpt⟩ := Finset.mem_image.1 (s.max'_mem hne)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
    exact ⟨t, h1, h2, hpt⟩
  · intro t h1 h2
    exact Finset.le_max' s (p t) (Finset.mem_image.2 ⟨t, Finset.mem_Icc.2 ⟨h1, h2⟩, rfl⟩)

/-! ### Reflecting a walk -/

/-- The reflection of a walk in the column `D`. -/
def mir (D : ℕ) (p : ℕ → ℕ) : ℕ → ℕ := fun t => D - p t

lemma isWalk_mir {D : ℕ} (hw : IsWalk p T) (hD : ∀ t, t ≤ T → p t ≤ D) :
    IsWalk (mir D p) T := by
  intro t ht
  have h1 := hD t (by omega)
  have h2 := hD (t + 1) (by omega)
  rcases hw t ht with h | h <;> simp only [mir] <;> omega

/-- The reflected walk visits every column at most as often as the original
one. -/
lemma visitsLe_mir {D a b k : ℕ} (hD : ∀ t, a ≤ t → t ≤ b → p t ≤ D)
    (hk : VisitsLe p a b k) : VisitsLe (mir D p) a b k := by
  intro y s hs
  refine hk (D - y) s ?_
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hs t ht
  have := hD t h1 h2
  simp only [mir] at h3
  exact ⟨h1, h2, by omega⟩

/-- A bound on the number of visits of the reflected walk is a bound on the
number of visits of the original one. -/
lemma visitsLe_of_mir {D u v k : ℕ} (hD : ∀ t, u ≤ t → t ≤ v → p t ≤ D)
    (hk : VisitsLe (mir D p) u v k) : VisitsLe p u v k := by
  intro y s hs
  refine hk (D - y) s ?_
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hs t ht
  have := hD t h1 h2
  exact ⟨h1, h2, by simp only [mir]; omega⟩

/-! ### Splitting a one-sided loop -/

/-- A loop that stays to the right of its base column splits, at the first visit
to its furthest column, into two pieces of smaller width. -/
lemma exists_split_of_loop_right (hw : IsWalk p T) {a0 b0 c k : ℕ} (hb0 : b0 ≤ T)
    (hab : a0 < b0) (hk : VisitsLe p a0 b0 k) (ha : p a0 = c) (hb : p b0 = c)
    (hside : ∀ t, a0 < t → t < b0 → c < p t) :
    ∃ τ, a0 ≤ τ ∧ τ ≤ b0 ∧ VisitsLe p a0 τ (k - 1) ∧ VisitsLe p τ b0 (k - 1) := by
  obtain ⟨m, hmvis, hmax⟩ := exists_max_col p (le_of_lt hab)
  have hne1 : a0 + 1 < b0 := by
    rcases eq_or_lt_of_le (show a0 + 1 ≤ b0 by omega) with h | h
    · exfalso
      rcases hw a0 (by omega) with hstep | hstep <;> rw [← h] at hb <;> omega
    · exact h
  have hcm : c < m := by
    have h1 := hside (a0 + 1) (by omega) (by omega)
    have h2 := hmax (a0 + 1) (by omega) (by omega)
    omega
  refine ⟨firstV p a0 b0 m, (le_firstV_bounds hmvis).1, (le_firstV_bounds hmvis).2, ?_, ?_⟩
  · intro y s hs
    have := loop_first_half_visits hw hb0 (le_of_lt hab) hk ha hb hcm hmvis hside hmax hs
    omega
  · intro y s hs
    have := loop_second_half_visits hw hb0 (le_of_lt hab) hk ha hb hcm hmvis hside hmax hs
    omega

/-- A loop that does not return to its base column in between splits into two
pieces of smaller width. -/
lemma exists_split_of_loop (hw : IsWalk p T) {a0 b0 c k : ℕ} (hb0 : b0 ≤ T)
    (hab : a0 < b0) (hk : VisitsLe p a0 b0 k) (ha : p a0 = c) (hb : p b0 = c)
    (hmid : ∀ t, a0 < t → t < b0 → p t ≠ c) :
    ∃ τ, a0 ≤ τ ∧ τ ≤ b0 ∧ VisitsLe p a0 τ (k - 1) ∧ VisitsLe p τ b0 (k - 1) := by
  rcases loop_one_sided hw hb0 ha hmid with hside | hside
  · exact exists_split_of_loop_right hw hb0 hab hk ha hb hside
  · -- the loop lies to the left of its base column: reflect it
    obtain ⟨D, -, hD⟩ := exists_max_col p (show (0 : ℕ) ≤ b0 by omega)
    have hD' : ∀ t, t ≤ b0 → p t ≤ D := fun t ht => hD t (Nat.zero_le _) ht
    have hDab : ∀ t, a0 ≤ t → t ≤ b0 → p t ≤ D := fun t _ ht => hD' t ht
    have hwm : IsWalk (mir D p) b0 := isWalk_mir (hw.of_le hb0) hD'
    have hcD : c ≤ D := by rw [← ha]; exact hD' a0 (by omega)
    have hkm : VisitsLe (mir D p) a0 b0 k := visitsLe_mir hDab hk
    have ham : mir D p a0 = D - c := by simp [mir, ha]
    have hbm : mir D p b0 = D - c := by simp [mir, hb]
    have hsidem : ∀ t, a0 < t → t < b0 → D - c < mir D p t := by
      intro t h1 h2
      have := hside t h1 h2
      have := hD' t (by omega)
      simp only [mir]
      omega
    obtain ⟨τ, h1, h2, h3, h4⟩ :=
      exists_split_of_loop_right hwm (le_refl b0) hab hkm ham hbm hsidem
    exact ⟨τ, h1, h2, visitsLe_of_mir (fun t _ ht => hD' t (by omega)) h3,
      visitsLe_of_mir (fun t ht _ => hD' t (by omega)) h4⟩

/-! ### Cutting a piece of a walk into pieces of bounded width -/

/-- The piece of the walk between the times `u` and `v` can be cut into finitely
many consecutive pieces, each of which visits every column at most `k` times. -/
inductive SplitsInto (p : ℕ → ℕ) (k : ℕ) : ℕ → ℕ → Prop
  | refl (u : ℕ) : SplitsInto p k u u
  | step {u v z : ℕ} (huv : u ≤ v) (h : VisitsLe p u v k) (rest : SplitsInto p k v z) :
      SplitsInto p k u z

lemma SplitsInto.le {k u v : ℕ} (h : SplitsInto p k u v) : u ≤ v := by
  induction h with
  | refl u => exact le_refl u
  | step huv _ _ ih => omega

lemma SplitsInto.trans {k u v z : ℕ} (h1 : SplitsInto p k u v) (h2 : SplitsInto p k v z) :
    SplitsInto p k u z := by
  induction h1 with
  | refl u => exact h2
  | step huv h _ ih => exact SplitsInto.step huv h (ih h2)

lemma SplitsInto.single {k u v : ℕ} (huv : u ≤ v) (h : VisitsLe p u v k) :
    SplitsInto p k u v :=
  SplitsInto.step huv h (SplitsInto.refl v)

/-- A cutting of a piece of the walk, presented as an increasing chain of times
from `u` to `v` whose consecutive pieces have width at most `k`. -/
lemma SplitsInto.exists_chain {k u v : ℕ} (h : SplitsInto p k u v) :
    ∃ ts : List ℕ, List.IsChain (· ≤ ·) (u :: ts) ∧ (u :: ts).getLast? = some v ∧
      ∀ q ∈ (u :: ts).zip ts, VisitsLe p q.1 q.2 k := by
  induction h with
  | refl u => exact ⟨[], by simp, by simp, by simp⟩
  | @step u v z huv hvis _ ih =>
      obtain ⟨ts, hchain, hlast, hpairs⟩ := ih
      refine ⟨v :: ts, ?_, ?_, ?_⟩
      · exact List.isChain_cons_cons.2 ⟨huv, hchain⟩
      · rw [List.getLast?_cons_cons]
        exact hlast
      · intro q hq
        rw [List.zip_cons_cons] at hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hvis
        · exact hpairs q hq

/-- **A looping part of a walk splits into pieces of smaller width.**  If the
walk is at the same column at the times `u` and `v`, then the piece between `u`
and `v` can be cut into finitely many pieces, each of which visits every column
at most `k - 1` times, where `k` bounds the number of visits of the piece
itself.  The cutting points are the intermediate visits to the base column and,
inside each of the resulting one-sided loops, the first visit to the furthest
column. -/
lemma loop_splitsInto (hw : IsWalk p T) {k : ℕ} :
    ∀ (d u v : ℕ), v - u ≤ d → u ≤ v → v ≤ T → p u = p v → VisitsLe p u v k →
      SplitsInto p (k - 1) u v := by
  intro d
  induction d with
  | zero =>
      intro u v hd huv _ _ _
      obtain rfl : u = v := by omega
      exact SplitsInto.refl u
  | succ d ih =>
      intro u v hd huv0 hvT hpuv hk
      rcases Nat.eq_or_lt_of_le huv0 with rfl | huv
      · exact SplitsInto.refl u
      · by_cases hmid : ∃ t, u < t ∧ t < v ∧ p t = p u
        · obtain ⟨t, ht1, ht2, ht3⟩ := hmid
          have hk1 : VisitsLe p u t k := by
            intro y s hs
            exact hk y s (fun r hr => ⟨(hs r hr).1, by have := (hs r hr).2.1; omega,
              (hs r hr).2.2⟩)
          have hk2 : VisitsLe p t v k := by
            intro y s hs
            exact hk y s (fun r hr => ⟨by have := (hs r hr).1; omega, (hs r hr).2.1,
              (hs r hr).2.2⟩)
          exact SplitsInto.trans
            (ih u t (by omega) (by omega) (by omega) ht3.symm hk1)
            (ih t v (by omega) (by omega) hvT (by omega) hk2)
        · push_neg at hmid
          obtain ⟨τ, h1, h2, h3, h4⟩ :=
            exists_split_of_loop hw hvT huv hk rfl hpuv.symm
              (fun t ht1 ht2 => hmid t ht1 ht2)
          exact SplitsInto.trans (SplitsInto.single h1 h3) (SplitsInto.single h2 h4)

/-! ### The last progress part -/

/-- Restricting the time interval preserves a bound on the number of visits. -/
lemma VisitsLe.mono {a b u v k : ℕ} (hk : VisitsLe p a b k) (hu : a ≤ u) (hv : v ≤ b) :
    VisitsLe p u v k := by
  intro y s hs
  exact hk y s (fun t ht => ⟨by have := (hs t ht).1; omega,
    by have := (hs t ht).2.1; omega, (hs t ht).2.2⟩)

/-- **The last progress part has smaller width.**  If there is no record-breaking
column after `x`, then the piece of the walk after the last visit to `x` visits
every column at most `k - 1` times.  (The walk is assumed to start at its
leftmost column, as the run of a two-way transducer does.) -/
lemma final_progress_visitsLe (hw : IsWalk p T) {a b x k : ℕ} (hbT : b ≤ T)
    (hk : VisitsLe p a b k) (hk2 : 2 ≤ k) (hx : Visited p a b x)
    (hmin : ∀ t, a ≤ t → t ≤ b → p a ≤ p t)
    (hstable : ¬ (recSet p a b x).Nonempty) :
    VisitsLe p (lastV p a b x) b (k - 1) := by
  classical
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  intro y s hs
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨t0, ht0⟩
  · simp
  · obtain ⟨h1, h2, h3⟩ := hs t0 ht0
    rcases lt_trichotomy y x with hy | hy | hy
    · -- the column `y` lies to the left of `x`, so it is visited before the walk
      -- reaches `x` for the last time
      have hay : p a ≤ y := by rw [← h3]; exact hmin t0 (by omega) h2
      obtain ⟨τ, hτ1, hτ2, hτ3⟩ :=
        exists_eq_between (x := y) hw hl1 (le_trans hl2 hbT)
          (Or.inl ⟨hay, by rw [hl3]; omega⟩)
      have hτne : τ ≠ lastV p a b x := by
        intro h; rw [h, hl3] at hτ3; omega
      have := visits_le_of_extra hk hτ1 (by omega) hτ3 (Or.inl (by omega)) hs hl1 (le_refl b)
      omega
    · -- the column `x` itself is visited only at the beginning of the piece
      subst hy
      have hsub : s ⊆ {lastV p a b y} := by
        intro t ht
        obtain ⟨g1, g2, g3⟩ := hs t ht
        have := le_lastV (p := p) (a := a) (b := b) (x := y) ⟨by omega, g2, g3⟩
        simp only [Finset.mem_singleton]
        omega
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at this
      omega
    · -- the column `y` lies to the right of `x`, so it is already visited during
      -- the loop part of `x`
      have hyvis : Visited p a b y := ⟨t0, by omega, h2, h3⟩
      have hfy := loop_of_recSet_empty hstable hx hy hyvis
      obtain ⟨g1, g2, g3⟩ := firstV_mem hyvis
      have := visits_le_of_extra hk g1 g2 g3 (Or.inl (by omega)) hs hl1 (le_refl b)
      omega

/-! ### The whole walk splits into pieces of smaller width -/

/-- **The induction step of the book's snake lemma, at the level of walks.**  A
walk that starts at its leftmost column and visits every column at most `k`
times (`k ≥ 2`) can be cut into finitely many consecutive pieces, each of which
visits every column at most `k - 1` times.  The cutting points are the first and
the last visits to the record-breaking columns, together with the cutting points
of the loop parts. -/
theorem walk_splitsInto_pred (hw : IsWalk p T) {a b k : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hk : VisitsLe p a b k) (hk2 : 2 ≤ k)
    (hmin : ∀ t, a ≤ t → t ≤ b → p a ≤ p t) :
    SplitsInto p (k - 1) a b := by
  have hloop : ∀ i, SplitsInto p (k - 1) (recFirst p a b i) (recLast p a b i) := by
    intro i
    have hvis := visited_recSeq (p := p) hab i
    have h1 := le_recFirst (p := p) hab i
    have h2 := recLast_le (p := p) hab i
    have h3 := recFirst_le_recLast (p := p) hab i
    refine loop_splitsInto hw (recLast p a b i - recFirst p a b i) _ _ (le_refl _) h3
      (by omega) ?_ (hk.mono (by omega) (by omega))
    rw [recFirst, recLast, pos_firstV hvis, pos_lastV hvis]
  have hstep : ∀ (n i : ℕ), i + n = recN p a b → SplitsInto p (k - 1) (recFirst p a b i) b := by
    intro n
    induction n with
    | zero =>
        intro i hi
        have hstable : RecStable p a b (recN p a b) := recStable_recN hw hab hbT
        rw [show i = recN p a b by omega] at *
        have hfin := final_progress_visitsLe hw hbT hk hk2
          (visited_recSeq (p := p) hab (recN p a b)) hmin hstable
        refine SplitsInto.trans (hloop (recN p a b)) (SplitsInto.single ?_ hfin)
        exact (lastV_bounds (visited_recSeq (p := p) hab (recN p a b))).2
    | succ n ih =>
        intro i hi
        have hlt : i < recN p a b := by omega
        have hns : ¬ RecStable p a b i := not_recStable_of_lt_recN hlt
        have hprog := recProgress_visitsLe hw hab hbT hk hk2 hns
        refine SplitsInto.trans (hloop i)
          (SplitsInto.trans (SplitsInto.single (recLast_le_recFirst_succ hns) hprog)
            (ih (i + 1) (by omega)))
  have := hstep (recN p a b) 0 (by omega)
  rwa [recFirst_zero hab] at this

end Walk

namespace TwoWay

variable {A B Q : Type}

/-- The run starts at the leftmost column. -/
@[simp] lemma traj_zero (M : TwoWay A B Q) (w : List A) : traj M w 0 = 0 := by
  have h : posAt M w 0 = some 0 := by simp [posAt]
  simp [traj, h]

/-- **The induction step of the book's snake lemma, for the run of a two-way
transducer.**  If the run of `M` on `w` halts and visits every column at most
`k` times (`k ≥ 2`), then it splits into finitely many consecutive pieces, each
of which visits every column at most `k - 1` times. -/
theorem run_splitsInto_pred (M : TwoWay A B Q) (w : List A) {T k : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w k) (hk2 : 2 ≤ k) :
    Walk.SplitsInto (traj M w) (k - 1) 0 (T - 1) := by
  refine Walk.walk_splitsInto_pred (isWalk_traj M w hT) (Nat.zero_le _) (le_refl _)
    (visitsLe_of_widthLe M w hT hwidth) hk2 ?_
  intro t _ _
  rw [traj_zero]
  exact Nat.zero_le _

/-- **The output of a halting run of width at most `k` is the concatenation of
the outputs of finitely many consecutive pieces of width at most `k - 1`** (plus
the output of the very last step of the run).  This is the whole combinatorial
content of the induction step in the book's proof that the output of a snake
graph is a regular function; what remains to be seen, in order to complete
`Transducers.boundedWidth_isRegular`, is that the outputs of the pieces are
computed by regular functions of factors of the input, and that they can be
glued back together by Lemma `lem:regular-closure-properties`. -/
theorem runOutput_splits (M : TwoWay A B Q) (w : List A) {T k : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w k) (hk2 : 2 ≤ k) :
    ∃ ts : List ℕ, List.IsChain (· ≤ ·) (0 :: ts) ∧ (0 :: ts).getLast? = some (T - 1) ∧
      (∀ q ∈ (0 :: ts).zip ts, Walk.VisitsLe (traj M w) q.1 q.2 (k - 1)) ∧
      outRange M w 0 T = outChain M w (0 :: ts) ++ outRange M w (T - 1) T := by
  obtain ⟨ts, hchain, hlast, hpairs⟩ := (run_splitsInto_pred M w hT hwidth hk2).exists_chain
  refine ⟨ts, hchain, hlast, hpairs, ?_⟩
  have hT1 : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with rfl | h
    · rw [cfgAt_zero] at hT; simp at hT
    · exact h
  rw [outChain_eq_outRange M w ts 0 (T - 1) hchain hlast,
    ← outRange_split M w (show (0 : ℕ) ≤ T - 1 by omega) (show T - 1 ≤ T by omega)]

end TwoWay

end Lax916827Proofs.Transducers
