/-
The *record-breaking columns* of a walk and the resulting decomposition of the
output of a run of a two-way transducer.

This file continues `RequestProject/PartC/SnakeWalk.lean`.  It builds the
sequence of record-breaking columns

  `x₀ < x₁ < ⋯ < x_N`

of the trajectory of a run (Definition in the book's proof of the lemma "the
output of a snake graph is regular", cf. `RequestProject/PartC/SnakeWidth.lean`)
and proves that the times

  `a = f₀ ≤ l₀ ≤ f₁ ≤ l₁ ≤ ⋯ ≤ f_N ≤ l_N ≤ b`

(where `f i` and `l i` are the first and the last visit to `x i`) form an
increasing chain that covers the whole run.  Consequently the output of the run
is the concatenation, in this order, of the outputs of the *loop parts*
`[f i, l i]` and of the *progress parts* `[l i, f (i+1)]` (the last progress
part being `[l N, b]`).  This is the combinatorial heart of the induction on the
width in the book's proof.
-/
import Lax916827Proofs.Source.PartC.SnakeWidth
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace Walk

variable {p : ℕ → ℕ} {T : ℕ}

/-! ### A walk moves by at most one column per step -/

/-- A walk started at time `a` is at most `t - a` columns to the right of its
starting column at time `t`. -/
lemma le_add_of_isWalk (hw : IsWalk p T) {a t : ℕ} (ha : a ≤ t) (ht : t ≤ T) :
    p t ≤ p a + (t - a) := by
  induction t with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge a (n + 1) with hlt | hge
      · have han : a ≤ n := by omega
        have hn : n ≤ T := by omega
        have := ih han hn
        rcases hw n (by omega) with h | h <;> omega
      · have : a = n + 1 := by omega
        subst this
        simp

/-! ### The sequence of record-breaking columns -/

open Classical in
/-- The `i`-th record-breaking column of the walk `p` on the time interval
`[a, b]`.  The first one is the starting column; the sequence becomes constant
once there is no further record-breaker. -/
noncomputable def recSeq (p : ℕ → ℕ) (a b : ℕ) : ℕ → ℕ
  | 0 => p a
  | (i + 1) =>
      if (recSet p a b (recSeq p a b i)).Nonempty then
        recNext p a b (recSeq p a b i)
      else recSeq p a b i

@[simp] lemma recSeq_zero (p : ℕ → ℕ) (a b : ℕ) : recSeq p a b 0 = p a := rfl

open Classical in
lemma recSeq_succ (p : ℕ → ℕ) (a b i : ℕ) :
    recSeq p a b (i + 1) =
      if (recSet p a b (recSeq p a b i)).Nonempty then
        recNext p a b (recSeq p a b i)
      else recSeq p a b i := rfl

/-- The walk is *stable* at stage `i` if there is no record-breaker after the
`i`-th one. -/
def RecStable (p : ℕ → ℕ) (a b i : ℕ) : Prop := ¬ (recSet p a b (recSeq p a b i)).Nonempty

lemma recSeq_succ_of_stable {a b i : ℕ} (h : RecStable p a b i) :
    recSeq p a b (i + 1) = recSeq p a b i := by
  rw [recSeq_succ, if_neg h]

lemma recSeq_succ_of_not_stable {a b i : ℕ} (h : ¬ RecStable p a b i) :
    recSeq p a b (i + 1) = recNext p a b (recSeq p a b i) := by
  rw [recSeq_succ, if_pos (not_not.1 h)]

lemma lt_recSeq_succ {a b i : ℕ} (h : ¬ RecStable p a b i) :
    recSeq p a b i < recSeq p a b (i + 1) := by
  rw [recSeq_succ_of_not_stable h]
  exact lt_recNext (not_not.1 h)

/-- Every record-breaking column is visited. -/
lemma visited_recSeq {a b : ℕ} (hab : a ≤ b) (i : ℕ) : Visited p a b (recSeq p a b i) := by
  induction i with
  | zero => exact ⟨a, le_refl _, hab, rfl⟩
  | succ n ih =>
      by_cases h : RecStable p a b n
      · rw [recSeq_succ_of_stable h]; exact ih
      · rw [recSeq_succ_of_not_stable h]; exact visited_recNext (not_not.1 h)

/-- Before stabilisation the record-breaking columns increase by at least one at
each stage. -/
lemma add_le_recSeq {a b i : ℕ} (h : ∀ j, j < i → ¬ RecStable p a b j) :
    p a + i ≤ recSeq p a b i := by
  induction i with
  | zero => simp
  | succ n ih =>
      have hn : ∀ j, j < n → ¬ RecStable p a b j := fun j hj => h j (by omega)
      have h1 := ih hn
      have h2 := lt_recSeq_succ (h n (by omega))
      omega

/-- The sequence of record-breaking columns stabilises after at most `b - a`
stages. -/
lemma exists_recStable (hw : IsWalk p T) {a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T) :
    ∃ i, i ≤ b - a ∧ RecStable p a b i := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ j, j < b - a + 1 → ¬ RecStable p a b j := by
    intro j hj
    exact hcon j (by omega)
  have h1 := add_le_recSeq (p := p) (a := a) (b := b) (i := b - a + 1) hall
  obtain ⟨t, ht1, ht2, ht3⟩ := visited_recSeq (p := p) hab (b - a + 1)
  have h2 := le_add_of_isWalk hw ht1 (le_trans ht2 hbT)
  omega

open Classical in
/-- The number of record-breaking columns (minus one): the least stage at which
the sequence of record-breakers stabilises. -/
noncomputable def recN (p : ℕ → ℕ) (a b : ℕ) : ℕ :=
  if h : ∃ i, RecStable p a b i then Nat.find h else 0

lemma recStable_recN (hw : IsWalk p T) {a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T) :
    RecStable p a b (recN p a b) := by
  classical
  obtain ⟨i, -, hi⟩ := exists_recStable hw hab hbT
  have hex : ∃ i, RecStable p a b i := ⟨i, hi⟩
  rw [recN, dif_pos hex]
  exact Nat.find_spec hex

lemma not_recStable_of_lt_recN {a b i : ℕ} (h : i < recN p a b) : ¬ RecStable p a b i := by
  classical
  by_cases hex : ∃ i, RecStable p a b i
  · rw [recN, dif_pos hex] at h
    exact Nat.find_min hex h
  · push_neg at hex
    exact hex i

/-! ### The chain of times -/

/-- The first visit to the `i`-th record-breaking column. -/
noncomputable def recFirst (p : ℕ → ℕ) (a b i : ℕ) : ℕ := firstV p a b (recSeq p a b i)

/-- The last visit to the `i`-th record-breaking column. -/
noncomputable def recLast (p : ℕ → ℕ) (a b i : ℕ) : ℕ := lastV p a b (recSeq p a b i)

lemma recFirst_zero {a b : ℕ} (hab : a ≤ b) : recFirst p a b 0 = a := by
  have h1 : a ∈ visitSet p a b (recSeq p a b 0) := ⟨le_refl _, hab, rfl⟩
  have h2 := firstV_le (p := p) h1
  have h3 := (le_firstV_bounds (p := p) (visited_recSeq hab 0)).1
  exact le_antisymm h2 h3

lemma recFirst_le_recLast {a b : ℕ} (hab : a ≤ b) (i : ℕ) :
    recFirst p a b i ≤ recLast p a b i :=
  firstV_le_lastV (visited_recSeq hab i)

lemma recLast_le_recFirst_succ {a b i : ℕ} (h : ¬ RecStable p a b i) :
    recLast p a b i ≤ recFirst p a b (i + 1) := by
  have := lastV_lt_firstV_recNext (p := p) (not_not.1 h)
  rw [recFirst, recSeq_succ_of_not_stable h, recLast]
  omega

lemma recLast_le {a b : ℕ} (hab : a ≤ b) (i : ℕ) : recLast p a b i ≤ b :=
  (lastV_bounds (visited_recSeq hab i)).2

lemma le_recFirst {a b : ℕ} (hab : a ≤ b) (i : ℕ) : a ≤ recFirst p a b i :=
  (le_firstV_bounds (visited_recSeq hab i)).1


/-! ### The chain of times of the record-breaking columns -/

/-- The chain of times `f i ≤ l i ≤ f (i+1) ≤ ⋯ ≤ l (i+n) ≤ b` of the record
breaking columns of the stages `i, …, i + n`. -/
noncomputable def recChainFrom (p : ℕ → ℕ) (a b : ℕ) (i : ℕ) : ℕ → List ℕ
  | 0 => [recFirst p a b i, recLast p a b i, b]
  | (n + 1) => recFirst p a b i :: recLast p a b i :: recChainFrom p a b (i + 1) n

lemma recChainFrom_head {a b i n : ℕ} :
    (recChainFrom p a b i n).head? = some (recFirst p a b i) := by
  cases n <;> rfl

lemma recChainFrom_getLast {a b : ℕ} :
    ∀ (n i : ℕ), (recChainFrom p a b i n).getLast? = some b := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih => intro i; simp [recChainFrom, List.getLast?_cons, ih (i + 1)]

/-- The times of the record-breaking columns increase. -/
lemma recChainFrom_isChain {a b : ℕ} (hab : a ≤ b) :
    ∀ (n i : ℕ), (∀ j, i ≤ j → j < i + n → ¬ RecStable p a b j) →
      List.IsChain (· ≤ ·) (recChainFrom p a b i n) := by
  intro n
  induction n with
  | zero =>
      intro i _
      have h1 := recFirst_le_recLast (p := p) hab i
      have h2 := recLast_le (p := p) hab i
      simp [recChainFrom, List.isChain_cons_cons, h1, h2]
  | succ n ih =>
      intro i h
      have hi : ¬ RecStable p a b i := h i (le_refl _) (by omega)
      have hrec := ih (i + 1) (fun j hj1 hj2 => h j (by omega) (by omega))
      refine List.isChain_cons_cons.2 ⟨recFirst_le_recLast hab i, ?_⟩
      refine List.isChain_cons.2 ⟨?_, hrec⟩
      intro y hy
      rw [recChainFrom_head] at hy
      obtain rfl : y = recFirst p a b (i + 1) := by simpa [eq_comm] using hy
      exact recLast_le_recFirst_succ hi

/-! ### The width of a progress part -/

/-- **The progress part of a record-breaking column has smaller width.**  The
piece of the walk between the last visit to `x` and the first visit to the next
record-breaking column visits every column at most `k - 1` times, if the whole
walk visits every column at most `k` times and `k ≥ 2`. -/
lemma progress_visitsLe (hw : IsWalk p T) {a b x k : ℕ} (hbT : b ≤ T)
    (hk : VisitsLe p a b k) (hk2 : 2 ≤ k) (hx : Visited p a b x)
    (hne : (recSet p a b x).Nonempty) :
    VisitsLe p (lastV p a b x) (firstV p a b (recNext p a b x)) (k - 1) := by
  classical
  set x' := recNext p a b x with hx'def
  have hxx' : x < x' := lt_recNext hne
  have hx'vis : Visited p a b x' := visited_recNext hne
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hx'vis
  intro y s hs
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨t0, ht0⟩
  · simp
  · obtain ⟨h1, h2, h3⟩ := hs t0 ht0
    have hrange := progress_columns hw hbT hx hx'vis hxx' h1 h2
    rw [h3] at hrange
    rcases eq_or_lt_of_le hrange.1 with hyx | hyx
    · have := progress_visits_left hx (x' := x') (s := s) (by
        intro t ht; obtain ⟨g1, g2, g3⟩ := hs t ht; exact ⟨g1, g2, by rw [g3, ← hyx]⟩) hf2
      omega
    · rcases eq_or_lt_of_le hrange.2 with hyx' | hyx'
      · have := progress_visits_right hx'vis (x := x) (s := s) (by
          intro t ht; obtain ⟨g1, g2, g3⟩ := hs t ht; exact ⟨g1, g2, by rw [g3, hyx']⟩) hl1
        omega
      · obtain ⟨hyvis, hyloop⟩ := loop_of_lt_recNext hw hbT hne hx hyx hyx'
        have := progress_visits_mid hk hyvis hyloop hs hf2
        omega

/-- The progress part of the `i`-th record-breaking column has smaller width. -/
lemma recProgress_visitsLe (hw : IsWalk p T) {a b k i : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hk : VisitsLe p a b k) (hk2 : 2 ≤ k) (hi : ¬ RecStable p a b i) :
    VisitsLe p (recLast p a b i) (recFirst p a b (i + 1)) (k - 1) := by
  have := progress_visitsLe hw hbT hk hk2 (visited_recSeq hab i) (not_not.1 hi)
  rwa [recLast, recFirst, recSeq_succ_of_not_stable hi]

end Walk

namespace TwoWay

variable {A B Q : Type} (M : TwoWay A B Q) (w : List A)

/-- The output over a range of times splits at every intermediate time. -/
lemma outRange_split {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    outRange M w a c = outRange M w a b ++ outRange M w b c := by
  unfold outRange
  rw [show c - a = (b - a) + (c - b) by omega, ← List.range'_append_1,
    show a + (b - a) = b by omega]
  simp

/-- The output produced along a chain of times. -/
def outChain (M : TwoWay A B Q) (w : List A) (ts : List ℕ) : List B :=
  (ts.zip ts.tail).flatMap (fun q => outRange M w q.1 q.2)

@[simp] lemma outChain_singleton (a : ℕ) : outChain M w [a] = [] := by simp [outChain]

lemma outChain_cons_cons (a y : ℕ) (t : List ℕ) :
    outChain M w (a :: y :: t) = outRange M w a y ++ outChain M w (y :: t) := by
  simp [outChain]

end TwoWay

namespace Walk

/-- The first element of an increasing chain is at most its last element. -/
lemma head_le_getLast : ∀ (ts : List ℕ) (a b : ℕ), List.IsChain (· ≤ ·) (a :: ts) →
    (a :: ts).getLast? = some b → a ≤ b := by
  intro ts
  induction ts with
  | nil =>
      intro a b _ h2
      simp only [List.getLast?_singleton, Option.some.injEq] at h2
      omega
  | cons y t ih =>
      intro a b hc h2
      rw [List.getLast?_cons_cons] at h2
      have hay : a ≤ y := (List.isChain_cons_cons.1 hc).1
      have := ih y b (List.isChain_cons_cons.1 hc).2 h2
      omega

end Walk

namespace TwoWay

variable {A B Q : Type}

/-- The outputs along an increasing chain of times concatenate to the output
over the whole range. -/
lemma outChain_eq_outRange (M : TwoWay A B Q) (w : List A) :
    ∀ (ts : List ℕ) (a b : ℕ), List.IsChain (· ≤ ·) (a :: ts) →
      (a :: ts).getLast? = some b → outChain M w (a :: ts) = outRange M w a b := by
  intro ts
  induction ts with
  | nil =>
      intro a b _ h2
      simp only [List.getLast?_singleton, Option.some.injEq] at h2
      subst h2
      simp [outRange]
  | cons y t ih =>
      intro a b hc h2
      rw [List.getLast?_cons_cons] at h2
      have hay : a ≤ y := (List.isChain_cons_cons.1 hc).1
      have hyb : y ≤ b := Walk.head_le_getLast t y b (List.isChain_cons_cons.1 hc).2 h2
      rw [outChain_cons_cons, ih y b (List.isChain_cons_cons.1 hc).2 h2,
        ← outRange_split M w hay hyb]

end TwoWay

namespace TwoWay

variable {A B Q : Type}

/-! ### The output of a run along its record-breaking columns -/

/-- The concatenation, over the record-breaking stages `i, …, i + n`, of the
output of the *loop part* of the stage (between the first and the last visit to
the record-breaking column) followed by the output of its *progress part*
(between the last visit to the record-breaking column and the first visit to the
next one; for the last stage, up to the end of the run). -/
noncomputable def loopProgOut (M : TwoWay A B Q) (w : List A) (p : ℕ → ℕ) (a b : ℕ) :
    ℕ → ℕ → List B
  | 0, i =>
      outRange M w (Walk.recFirst p a b i) (Walk.recLast p a b i) ++
        outRange M w (Walk.recLast p a b i) b
  | (n + 1), i =>
      (outRange M w (Walk.recFirst p a b i) (Walk.recLast p a b i) ++
          outRange M w (Walk.recLast p a b i) (Walk.recFirst p a b (i + 1))) ++
        loopProgOut M w p a b n (i + 1)

lemma outChain_recChainFrom (M : TwoWay A B Q) (w : List A) (p : ℕ → ℕ) (a b : ℕ) :
    ∀ (n i : ℕ), outChain M w (Walk.recChainFrom p a b i n) = loopProgOut M w p a b n i := by
  intro n
  induction n with
  | zero =>
      intro i
      simp [Walk.recChainFrom, loopProgOut, outChain]
  | succ n ih =>
      intro i
      obtain ⟨ts, hts⟩ : ∃ ts, Walk.recChainFrom p a b (i + 1) n
          = Walk.recFirst p a b (i + 1) :: ts := by
        cases n <;> exact ⟨_, rfl⟩
      show outChain M w (Walk.recFirst p a b i :: Walk.recLast p a b i ::
          Walk.recChainFrom p a b (i + 1) n) = _
      rw [loopProgOut, hts, outChain_cons_cons, outChain_cons_cons, ← ih (i + 1), hts]
      simp

/-- **The output of a run is the concatenation of the outputs of the loop parts
and of the progress parts of its record-breaking columns.**  This is the
combinatorial content of the induction step in the book's proof of the snake
lemma: it remains to see that each of these parts is computed by a regular
function of a factor of the input. -/
theorem outRange_eq_loopProgOut (M : TwoWay A B Q) (w : List A) (p : ℕ → ℕ)
    {a b N : ℕ} (hab : a ≤ b) (hN : ∀ j, j < N → ¬ Walk.RecStable p a b j) :
    outRange M w a b = loopProgOut M w p a b N 0 := by
  obtain ⟨ts, hts⟩ : ∃ ts, Walk.recChainFrom p a b 0 N = Walk.recFirst p a b 0 :: ts := by
    cases N <;> exact ⟨_, rfl⟩
  have hchain := Walk.recChainFrom_isChain (p := p) hab N 0 (fun j _ hj => hN j (by omega))
  have hlast := Walk.recChainFrom_getLast (p := p) (a := a) (b := b) N 0
  rw [hts, Walk.recFirst_zero hab] at hchain hlast
  rw [← outChain_recChainFrom M w p a b N 0, hts, Walk.recFirst_zero hab]
  exact (outChain_eq_outRange M w ts a b hchain hlast).symm

/-- The same decomposition for the whole run of a two-way transducer that halts
at time `T`: the record-breaking columns of the trajectory decompose the output
of the run, up to the very last step of the run. -/
theorem runOutput_eq_loopProgOut (M : TwoWay A B Q) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) :
    outRange M w 0 T =
      loopProgOut M w (traj M w) 0 (T - 1) (Walk.recN (traj M w) 0 (T - 1)) 0 ++
        outRange M w (T - 1) T := by
  have hT1 : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with rfl | h
    · rw [cfgAt_zero] at hT; simp at hT
    · exact h
  rw [outRange_split M w (show (0 : ℕ) ≤ T - 1 by omega) (show T - 1 ≤ T by omega)]
  congr 1
  exact outRange_eq_loopProgOut M w (traj M w) (Nat.zero_le _)
    (fun j hj => Walk.not_recStable_of_lt_recN hj)

end TwoWay

end Lax916827Proofs.Transducers
