import Lax17Proofs.Source.CutMatchingGameIncrement

namespace Lax17Proofs

universe u v w

/-!
# Sparse-cut histories in the cut-matching game

Theorem 4.2 of the cut-matching-game paper is a stopping argument: while a
`c`-balanced cut of expansion below `1/4` exists, the cut player chooses a
bisection containing the smaller side, and the entropy potential increases by
a fixed multiple of `c * n`.  This file packages the formal version of that
argument for an abstract transcript.
-/

namespace SimpleGraph
namespace CutMatchingGame

open scoped BigOperators


variable {X : Type u} [Fintype X] [DecidableEq X]

/-- A sparse `cNum/cDen`-balanced cut in the current history.  We orient the
cut by its smaller side, so the side also has size at most half the vertices.
The expansion threshold is `1/4`, written as
`4 * |∂T| <= |T|`; this weak inequality is the form needed for the entropy
increment. -/
def SparseCutAvailable (cNum cDen : ℕ) (rounds : List (LazyRound X)) : Prop :=
  ∃ T : Finset X,
    cNum * Fintype.card X ≤ cDen * T.card ∧
      2 * T.card ≤ Fintype.card X ∧
        4 * edgeBoundaryCount rounds T ≤ T.card

noncomputable instance sparseCutAvailableDecidable
    (cNum cDen : ℕ) (rounds : List (LazyRound X)) :
    Decidable (SparseCutAvailable (X := X) cNum cDen rounds) :=
  Classical.propDecidable _

/-- Expansion restricted to `cNum/cDen`-balanced cuts. -/
def IsBalancedEdgeExpanderWith
    (rounds : List (LazyRound X))
    (cNum cDen numerator denominator : ℕ) : Prop :=
  0 < denominator ∧
    ∀ T : Finset X,
      cNum * Fintype.card X ≤ cDen * T.card →
        2 * T.card ≤ Fintype.card X →
          numerator * T.card ≤ denominator * edgeBoundaryCount rounds T

theorem balancedEdgeExpander_one_four_of_not_sparseCutAvailable
    {cNum cDen : ℕ} {rounds : List (LazyRound X)}
    (hstop : ¬ SparseCutAvailable (X := X) cNum cDen rounds) :
    IsBalancedEdgeExpanderWith (X := X) rounds cNum cDen 1 4 := by
  refine ⟨by decide, ?_⟩
  intro T hlarge hhalf
  have hnotSparse : ¬ 4 * edgeBoundaryCount rounds T ≤ T.card := by
    intro hsparse
    exact hstop ⟨T, hlarge, hhalf, hsparse⟩
  have hlt : T.card < 4 * edgeBoundaryCount rounds T :=
    Nat.lt_of_not_ge hnotSparse
  omega

theorem balancedEdgeExpander_one_four_append_of_not_sparseCutAvailable
    {cNum cDen : ℕ} {rounds extra : List (LazyRound X)}
    (hstop : ¬ SparseCutAvailable (X := X) cNum cDen rounds) :
    IsBalancedEdgeExpanderWith (X := X) (rounds ++ extra) cNum cDen 1 4 := by
  refine ⟨by decide, ?_⟩
  intro T hlarge hhalf
  have hprefix :=
    (balancedEdgeExpander_one_four_of_not_sparseCutAvailable
      (X := X) hstop).2 T hlarge hhalf
  have hmono := edgeBoundaryCount_le_append rounds extra T
  omega

theorem edgeBoundaryCount_le_append_left
    (rounds extra : List (LazyRound X)) (T : Finset X) :
    edgeBoundaryCount extra T ≤ edgeBoundaryCount (rounds ++ extra) T := by
  rw [edgeBoundaryCount_append]
  omega

theorem balancedEdgeExpanderWith_append_same_den
    {rounds₁ rounds₂ : List (LazyRound X)}
    {cNum cDen numerator₁ numerator₂ denominator : ℕ}
    (h₁ : IsBalancedEdgeExpanderWith (X := X) rounds₁
      cNum cDen numerator₁ denominator)
    (h₂ : IsBalancedEdgeExpanderWith (X := X) rounds₂
      cNum cDen numerator₂ denominator) :
    IsBalancedEdgeExpanderWith (X := X) (rounds₁ ++ rounds₂)
      cNum cDen (numerator₁ + numerator₂) denominator := by
  refine ⟨h₁.1, ?_⟩
  intro T hlarge hhalf
  have hb₁ := h₁.2 T hlarge hhalf
  have hb₂ := h₂.2 T hlarge hhalf
  rw [edgeBoundaryCount_append]
  nlinarith

/-- Four `1/4` balanced-expander phases combine to expansion at least `1` on
the same class of balanced cuts. -/
theorem balancedEdgeExpander_one_of_four_one_four
    {rounds₁ rounds₂ rounds₃ rounds₄ : List (LazyRound X)}
    {cNum cDen : ℕ}
    (h₁ : IsBalancedEdgeExpanderWith (X := X) rounds₁ cNum cDen 1 4)
    (h₂ : IsBalancedEdgeExpanderWith (X := X) rounds₂ cNum cDen 1 4)
    (h₃ : IsBalancedEdgeExpanderWith (X := X) rounds₃ cNum cDen 1 4)
    (h₄ : IsBalancedEdgeExpanderWith (X := X) rounds₄ cNum cDen 1 4) :
    IsBalancedEdgeExpanderWith (X := X)
      (((rounds₁ ++ rounds₂) ++ rounds₃) ++ rounds₄)
      cNum cDen 1 1 := by
  refine ⟨by decide, ?_⟩
  intro T hlarge hhalf
  have hb₁ := h₁.2 T hlarge hhalf
  have hb₂ := h₂.2 T hlarge hhalf
  have hb₃ := h₃.2 T hlarge hhalf
  have hb₄ := h₄.2 T hlarge hhalf
  repeat rw [edgeBoundaryCount_append]
  omega

namespace SparseCutAvailable

omit [DecidableEq X] in
theorem cut_card_le_half
    {m : ℕ}
    (hm : 2 * m = Fintype.card X)
    {T : Finset X}
    (hhalf : 2 * T.card ≤ Fintype.card X) :
    T.card ≤ m := by
  omega

/-- Extend an available sparse side to a full bisection. -/
noncomputable def toBisection
    {cNum cDen m : ℕ} {rounds : List (LazyRound X)}
    (hm : 2 * m = Fintype.card X)
    (h : SparseCutAvailable (X := X) cNum cDen rounds) :
    Bisection X :=
  let T := Classical.choose h
  let hspec := Classical.choose_spec h
  Classical.choose
    (Bisection.exists_leftHalf_superset
      (T := T)
      (m := m)
      (cut_card_le_half (X := X) hm hspec.2.1)
      hm)

theorem chosen_subset_toBisection_left
    {cNum cDen m : ℕ} {rounds : List (LazyRound X)}
    (hm : 2 * m = Fintype.card X)
    (h : SparseCutAvailable (X := X) cNum cDen rounds) :
    Classical.choose h ⊆ (toBisection (X := X) hm h).left := by
  classical
  unfold toBisection
  exact (Classical.choose_spec
    (Bisection.exists_leftHalf_superset
      (T := Classical.choose h)
      (m := m)
      (cut_card_le_half (X := X) hm
        (Classical.choose_spec h).2.1)
      hm)).1

theorem chosen_large
    {cNum cDen : ℕ} {rounds : List (LazyRound X)}
    (h : SparseCutAvailable (X := X) cNum cDen rounds) :
    cNum * Fintype.card X ≤ cDen * (Classical.choose h).card :=
  (Classical.choose_spec h).1

theorem chosen_sparse
    {cNum cDen : ℕ} {rounds : List (LazyRound X)}
    (h : SparseCutAvailable (X := X) cNum cDen rounds) :
    4 * edgeBoundaryCount rounds (Classical.choose h) ≤
      (Classical.choose h).card :=
  (Classical.choose_spec h).2.2

end SparseCutAvailable

/-- A matching responder indexed by natural time. -/
def SequentialResponder (X : Type u) [Fintype X] [DecidableEq X] : Type u :=
  ∀ _round : ℕ, (B : Bisection X) → MatchingAcross B

namespace SequentialResponder

/-- Shift a sequential responder by a fixed number of already-used rounds. -/
def shift (responder : SequentialResponder X) (offset : ℕ) :
    SequentialResponder X :=
  fun round B => responder (offset + round) B

end SequentialResponder

/-- A lazy round obtained by presenting a bisection to a sequential responder. -/
noncomputable def LazyRound.ofResponder
    (responder : SequentialResponder X) (round : ℕ) (B : Bisection X) :
    LazyRound X where
  cut := B
  matching := responder round B

/-- A list transcript follows a sequential responder from a given time offset
when its `n`-th round uses the responder's matching at time `offset + n` for
the cut stored in that round.  The predicate is stated with `get?` so append
bookkeeping stays elementary. -/
def FollowsResponder
    (responder : SequentialResponder X) (offset : ℕ)
    (rounds : List (LazyRound X)) : Prop :=
  ∀ n R, rounds[n]? = some R →
    R = LazyRound.ofResponder responder (offset + n) R.cut

@[simp]
theorem followsResponder_nil
    (responder : SequentialResponder X) (offset : ℕ) :
    FollowsResponder (X := X) responder offset [] := by
  intro n R hget
  simp at hget

theorem followsResponder_singleton
    (responder : SequentialResponder X) (offset : ℕ) (B : Bisection X) :
    FollowsResponder (X := X) responder offset
      [LazyRound.ofResponder responder offset B] := by
  intro n R hget
  cases n with
  | zero =>
      simp at hget
      subst R
      simp [LazyRound.ofResponder]
  | succ n =>
      simp at hget

/-- Follower transcripts compose under append, with the second transcript
started after the length of the first. -/
theorem followsResponder_append
    {responder : SequentialResponder X} {offset : ℕ}
    {rounds extra : List (LazyRound X)}
    (hrounds : FollowsResponder (X := X) responder offset rounds)
    (hextra : FollowsResponder (X := X) responder (offset + rounds.length) extra) :
    FollowsResponder (X := X) responder offset (rounds ++ extra) := by
  intro n R hget
  by_cases hlt : n < rounds.length
  · have hleft :
        (rounds ++ extra)[n]? = rounds[n]? :=
      List.getElem?_append_left (l₂ := extra) hlt
    have hget_rounds : rounds[n]? = some R := by
      rwa [hleft] at hget
    exact hrounds n R hget_rounds
  · have hle : rounds.length ≤ n := Nat.le_of_not_gt hlt
    have hright :
        (rounds ++ extra)[n]? = extra[n - rounds.length]? :=
      List.getElem?_append_right (l₂ := extra) hle
    have hget_extra : extra[n - rounds.length]? = some R := by
      rwa [hright] at hget
    have hx := hextra (n - rounds.length) R hget_extra
    have hoff :
        offset + rounds.length + (n - rounds.length) = offset + n := by
      omega
    simpa [Nat.add_assoc, hoff] using hx

/-- An arbitrary half-bisection, used after the sparse-cut process has already
stopped so that the remaining fixed number of rounds can still be filled. -/
noncomputable def arbitraryBisection
    {m : ℕ} (hm : 2 * m = Fintype.card X) : Bisection X :=
  Classical.choose
    (Bisection.exists_leftHalf_superset
      (T := (∅ : Finset X)) (m := m) (by simp) hm)

/-- Deterministic filler rounds used after an expanding prefix has already
been produced, so that fixed-round downstream interfaces can be met exactly. -/
noncomputable def fillerRounds
    {m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (start count : ℕ) :
    List (LazyRound X) :=
  List.ofFn fun i : Fin count =>
    LazyRound.ofResponder responder (start + i.1)
      (arbitraryBisection (X := X) hm)

@[simp]
theorem fillerRounds_length
    {m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (start count : ℕ) :
    (fillerRounds (X := X) hm responder start count).length = count := by
  simp [fillerRounds]

theorem fillerRounds_followsResponder
    {m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (start count : ℕ) :
    FollowsResponder (X := X) responder start
      (fillerRounds (X := X) hm responder start count) := by
  intro n R hget
  rw [fillerRounds, List.getElem?_ofFn] at hget
  by_cases hn : n < count
  · simp [hn] at hget
    subst R
    simp [LazyRound.ofResponder]
  · simp [hn] at hget

/-- The cut-player process for a fixed number of rounds.  At step `k`, if a
sparse balanced cut exists in the current history, extend its smaller side to
a bisection; otherwise play an arbitrary bisection. -/
noncomputable def sparseCutPlay
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) : ℕ → List (LazyRound X)
  | 0 => []
  | k + 1 =>
      let rounds := sparseCutPlay cNum cDen m hm responder k
      if h : SparseCutAvailable (X := X) cNum cDen rounds then
        let B := SparseCutAvailable.toBisection (X := X) hm h
        rounds ++ [LazyRound.ofResponder responder k B]
      else
        let B := arbitraryBisection (X := X) hm
        rounds ++ [LazyRound.ofResponder responder k B]

theorem sparseCutPlay_length
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ) :
    (sparseCutPlay (X := X) cNum cDen m hm responder k).length = k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      unfold sparseCutPlay
      by_cases h :
          SparseCutAvailable (X := X) cNum cDen
            (sparseCutPlay (X := X) cNum cDen m hm responder k)
      · simp [h, ih]
      · simp [h, ih]

theorem sparseCutPlay_succ_eq_append
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ) :
    ∃ R : LazyRound X,
      sparseCutPlay (X := X) cNum cDen m hm responder (k + 1) =
        sparseCutPlay (X := X) cNum cDen m hm responder k ++ [R] := by
  by_cases h :
      SparseCutAvailable (X := X) cNum cDen
        (sparseCutPlay (X := X) cNum cDen m hm responder k)
  · refine ⟨LazyRound.ofResponder responder k
        (SparseCutAvailable.toBisection (X := X) hm h), ?_⟩
    simp [sparseCutPlay, h]
  · refine ⟨LazyRound.ofResponder responder k
        (arbitraryBisection (X := X) hm), ?_⟩
    simp [sparseCutPlay, h]

/-- The sparse-cut play transcript uses exactly the sequential responder at
the natural time index of each generated round. -/
theorem sparseCutPlay_followsResponder
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ) :
    FollowsResponder (X := X) responder 0
      (sparseCutPlay (X := X) cNum cDen m hm responder k) := by
  induction k with
  | zero =>
      simp [sparseCutPlay]
  | succ k ih =>
      unfold sparseCutPlay
      by_cases h :
          SparseCutAvailable (X := X) cNum cDen
            (sparseCutPlay (X := X) cNum cDen m hm responder k)
      · simp [h]
        have hsingle :
            FollowsResponder (X := X) responder k
              [LazyRound.ofResponder responder k
                (SparseCutAvailable.toBisection (X := X) hm h)] :=
          followsResponder_singleton (X := X) responder k
            (SparseCutAvailable.toBisection (X := X) hm h)
        have hlen :
            (sparseCutPlay (X := X) cNum cDen m hm responder k).length = k :=
          sparseCutPlay_length (X := X) cNum cDen m hm responder k
        have hsingle' :
            FollowsResponder (X := X) responder
              (0 + (sparseCutPlay (X := X) cNum cDen m hm responder k).length)
              [LazyRound.ofResponder responder k
                (SparseCutAvailable.toBisection (X := X) hm h)] := by
          simpa [hlen] using hsingle
        exact
          followsResponder_append (X := X) (offset := 0)
            (rounds := sparseCutPlay (X := X) cNum cDen m hm responder k)
            (extra :=
              [LazyRound.ofResponder responder k
                (SparseCutAvailable.toBisection (X := X) hm h)])
            ih hsingle'
      · simp [h]
        have hsingle :
            FollowsResponder (X := X) responder k
              [LazyRound.ofResponder responder k
                (arbitraryBisection (X := X) hm)] :=
          followsResponder_singleton (X := X) responder k
            (arbitraryBisection (X := X) hm)
        have hlen :
            (sparseCutPlay (X := X) cNum cDen m hm responder k).length = k :=
          sparseCutPlay_length (X := X) cNum cDen m hm responder k
        have hsingle' :
            FollowsResponder (X := X) responder
              (0 + (sparseCutPlay (X := X) cNum cDen m hm responder k).length)
              [LazyRound.ofResponder responder k
                (arbitraryBisection (X := X) hm)] := by
          simpa [hlen] using hsingle
        exact
          followsResponder_append (X := X) (offset := 0)
            (rounds := sparseCutPlay (X := X) cNum cDen m hm responder k)
            (extra := [LazyRound.ofResponder responder k
              (arbitraryBisection (X := X) hm)])
            ih hsingle'

theorem sparseCutPlay_prefix
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) {j k : ℕ} (hjk : j ≤ k) :
    ∃ extra : List (LazyRound X),
      sparseCutPlay (X := X) cNum cDen m hm responder k =
        sparseCutPlay (X := X) cNum cDen m hm responder j ++ extra := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := by omega
      subst hj
      exact ⟨[], by simp⟩
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hjk with hEq | hlt
      · subst hEq
        exact ⟨[], by simp⟩
      · have hjk' : j ≤ k := by omega
        rcases ih hjk' with ⟨extra, hextra⟩
        rcases sparseCutPlay_succ_eq_append
            (X := X) cNum cDen m hm responder k with ⟨R, hR⟩
        refine ⟨extra ++ [R], ?_⟩
        rw [hR, hextra, List.append_assoc]

theorem sparseCutPlay_balancedExpander_one_four_of_stopped_prefix
    {cNum cDen m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) {j k : ℕ} (hjk : j ≤ k)
    (hstop :
      ¬ SparseCutAvailable (X := X) cNum cDen
        (sparseCutPlay (X := X) cNum cDen m hm responder j)) :
    IsBalancedEdgeExpanderWith (X := X)
      (sparseCutPlay (X := X) cNum cDen m hm responder k)
      cNum cDen 1 4 := by
  rcases sparseCutPlay_prefix (X := X) cNum cDen m hm responder hjk with
    ⟨extra, hextra⟩
  rw [hextra]
  exact balancedEdgeExpander_one_four_append_of_not_sparseCutAvailable
    (X := X) hstop

/-- A history whose every appended round was justified by a sparse cut of the
previous history.  The lower-balance parameter is represented by the rational
number `cNum / cDen`: the witness cut `T` has
`cNum * |X| <= cDen * |T|`, lies on the left side of the next bisection, and
has current boundary at most `|T| / 4`. -/
inductive SparseCutHistory (cNum cDen : ℕ) :
    List (LazyRound X) → Prop where
  | nil : SparseCutHistory cNum cDen []
  | snoc {rounds : List (LazyRound X)} {R : LazyRound X}
      (hist : SparseCutHistory cNum cDen rounds)
      (T : Finset X)
      (large : cNum * Fintype.card X ≤ cDen * T.card)
      (left : ∀ v ∈ T, v ∈ R.cut.left)
      (sparse : 4 * edgeBoundaryCount rounds T ≤ T.card) :
      SparseCutHistory cNum cDen (rounds ++ [R])

/-- If the sparse-cut branch is available at every earlier step, the generated
prefix is a `SparseCutHistory`. -/
theorem sparseCutPlay_history_of_available_prefixes
    {cNum cDen m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ)
    (havailable :
      ∀ j < k,
        SparseCutAvailable (X := X) cNum cDen
          (sparseCutPlay (X := X) cNum cDen m hm responder j)) :
    SparseCutHistory (X := X) cNum cDen
      (sparseCutPlay (X := X) cNum cDen m hm responder k) := by
  induction k with
  | zero =>
      exact SparseCutHistory.nil
  | succ k ih =>
      have hprefix :
          ∀ j < k,
            SparseCutAvailable (X := X) cNum cDen
              (sparseCutPlay (X := X) cNum cDen m hm responder j) := by
        intro j hj
        exact havailable j (Nat.lt_trans hj (Nat.lt_succ_self k))
      have ihist := ih hprefix
      have hk :
          SparseCutAvailable (X := X) cNum cDen
            (sparseCutPlay (X := X) cNum cDen m hm responder k) :=
        havailable k (Nat.lt_succ_self k)
      unfold sparseCutPlay
      simp [hk]
      refine SparseCutHistory.snoc ihist (Classical.choose hk)
        (SparseCutAvailable.chosen_large hk)
        ?left
        (SparseCutAvailable.chosen_sparse hk)
      intro v hv
      exact SparseCutAvailable.chosen_subset_toBisection_left
        (X := X) hm hk hv

/-- The guaranteed potential increment per sparse-cut round for balance
parameter `cNum / cDen`. -/
noncomputable def sparseCutRoundIncrement
    (X : Type u) [Fintype X] (cNum cDen : ℕ) : ℝ :=
  entropyGapConstant * ((cNum * Fintype.card X : ℕ) : ℝ) / (8 * cDen)

namespace SparseCutHistory

theorem roundIncrement_le_gain
    {cNum cDen : ℕ} (hden : 0 < cDen)
    {rounds : List (LazyRound X)} {R : LazyRound X}
    {T : Finset X}
    (large : cNum * Fintype.card X ≤ cDen * T.card)
    (left : ∀ v ∈ T, v ∈ R.cut.left)
    (sparse : 4 * edgeBoundaryCount rounds T ≤ T.card) :
    sparseCutRoundIncrement X cNum cDen ≤
      entropyPotential (walkMatrix (rounds ++ [R])) -
        entropyPotential (walkMatrix rounds) := by
  have hgain :=
    entropyGapConstant_mul_card_div_eight_le_walkMatrix_append_potential_gain
      rounds R left sparse
  have hlarge_real :
      ((cNum * Fintype.card X : ℕ) : ℝ) ≤
        (cDen : ℝ) * (T.card : ℝ) := by
    exact_mod_cast large
  have hden_pos : 0 < (cDen : ℝ) := Nat.cast_pos.mpr hden
  have hconst_nonneg : 0 ≤ entropyGapConstant :=
    le_of_lt entropyGapConstant_pos
  unfold sparseCutRoundIncrement
  have hper_le :
      entropyGapConstant * ((cNum * Fintype.card X : ℕ) : ℝ) / (8 * cDen) ≤
        entropyGapConstant * (T.card : ℝ) / 8 := by
    have hdiv :
        ((cNum * Fintype.card X : ℕ) : ℝ) / (cDen : ℝ) ≤
          (T.card : ℝ) := by
      rw [div_le_iff₀ hden_pos]
      nlinarith
    calc
      entropyGapConstant * ((cNum * Fintype.card X : ℕ) : ℝ) / (8 * cDen)
          = (entropyGapConstant / 8) *
              (((cNum * Fintype.card X : ℕ) : ℝ) / (cDen : ℝ)) := by
            field_simp [ne_of_gt hden_pos]
      _ ≤ (entropyGapConstant / 8) * (T.card : ℝ) := by
            exact mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = entropyGapConstant * (T.card : ℝ) / 8 := by ring
  exact hper_le.trans hgain

/-- Entropy lower bound accumulated over a sparse-cut history. -/
theorem potential_lower
    {cNum cDen : ℕ} (hden : 0 < cDen)
    {rounds : List (LazyRound X)}
    (hist : SparseCutHistory (X := X) cNum cDen rounds) :
    sparseCutRoundIncrement X cNum cDen * (rounds.length : ℝ) ≤
      entropyPotential (walkMatrix rounds) := by
  induction hist with
  | nil =>
      simp [sparseCutRoundIncrement, pointMassMatrix.entropyPotential_eq_zero]
  | @snoc rounds R hist T large left sparse ih =>
      have hgain :=
        roundIncrement_le_gain (X := X) hden large left sparse
      have hlen :
          ((rounds ++ [R]).length : ℝ) = (rounds.length : ℝ) + 1 := by
        simp
      have hnonneg_old : 0 ≤ entropyPotential (walkMatrix rounds) :=
        entropyPotential_walkMatrix_nonneg rounds
      rw [hlen]
      nlinarith

/-- A sparse-cut history cannot have accumulated potential above the universal
`n log n` upper bound. -/
theorem length_increment_le_card_mul_log_card
    {cNum cDen : ℕ} (hden : 0 < cDen)
    {rounds : List (LazyRound X)}
    (hist : SparseCutHistory (X := X) cNum cDen rounds)
    (hn : 0 < Fintype.card X) :
    sparseCutRoundIncrement X cNum cDen * (rounds.length : ℝ) ≤
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) :=
  (potential_lower (X := X) hden hist).trans
    (entropyPotential_walkMatrix_le_card_mul_log_card rounds hn)

end SparseCutHistory

theorem sparseCutPlay_exists_stopped_prefix_of_potential_budget
    {cNum cDen m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ)
    (hden : 0 < cDen) (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X cNum cDen * (k : ℝ)) :
    ∃ j < k,
      ¬ SparseCutAvailable (X := X) cNum cDen
        (sparseCutPlay (X := X) cNum cDen m hm responder j) := by
  by_contra hnone
  push Not at hnone
  have hist :
      SparseCutHistory (X := X) cNum cDen
        (sparseCutPlay (X := X) cNum cDen m hm responder k) :=
    sparseCutPlay_history_of_available_prefixes
      (X := X) hm responder k hnone
  have hbound :=
    SparseCutHistory.length_increment_le_card_mul_log_card
      (X := X) hden hist hn
  rw [sparseCutPlay_length (X := X) cNum cDen m hm responder k] at hbound
  exact (not_lt_of_ge hbound) hbudget

/-- Abstract Theorem 4.2: after any number of rounds whose guaranteed entropy
budget exceeds `n log n`, the sequential sparse-cut strategy has already
stopped at some prefix; therefore the final history is a `cNum/cDen`-balanced
edge expander of expansion at least `1/4`. -/
theorem sparseCutPlay_balancedExpander_one_four_of_potential_budget
    {cNum cDen m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ)
    (hden : 0 < cDen) (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X cNum cDen * (k : ℝ)) :
    IsBalancedEdgeExpanderWith (X := X)
      (sparseCutPlay (X := X) cNum cDen m hm responder k)
      cNum cDen 1 4 := by
  rcases sparseCutPlay_exists_stopped_prefix_of_potential_budget
      (X := X) hm responder k hden hn hbudget with
    ⟨j, hjk, hstop⟩
  exact sparseCutPlay_balancedExpander_one_four_of_stopped_prefix
    (X := X) hm responder (Nat.le_of_lt hjk) hstop

/-- Repeat the independent `c`-balanced cut-matching phase several times.
Each phase is run from an empty phase-local history and uses a shifted view of
the sequential responder so that different phases consume disjoint round
indices. -/
noncomputable def sparseCutPlayMany
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ) : ℕ → List (LazyRound X)
  | 0 => []
  | phase + 1 =>
      sparseCutPlayMany cNum cDen m hm responder k phase ++
        sparseCutPlay cNum cDen m hm
          (SequentialResponder.shift responder (phase * k)) k

@[simp]
theorem sparseCutPlayMany_zero
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ) :
    sparseCutPlayMany (X := X) cNum cDen m hm responder k 0 = [] := rfl

theorem sparseCutPlayMany_succ
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k phase : ℕ) :
    sparseCutPlayMany (X := X) cNum cDen m hm responder k (phase + 1) =
      sparseCutPlayMany (X := X) cNum cDen m hm responder k phase ++
        sparseCutPlay (X := X) cNum cDen m hm
          (SequentialResponder.shift responder (phase * k)) k := rfl

/-- The repeated phase history has the expected length. -/
theorem sparseCutPlayMany_length
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k phase : ℕ) :
    (sparseCutPlayMany (X := X) cNum cDen m hm responder k phase).length =
      phase * k := by
  induction phase with
  | zero =>
      simp
  | succ phase ih =>
      rw [sparseCutPlayMany_succ]
      simp [ih, sparseCutPlay_length, Nat.succ_mul]

/-- The repeated-phase transcript follows the global responder time index:
phase `p` uses the responder shifted by `p*k`, so appending phases preserves
the single global time convention. -/
theorem sparseCutPlayMany_followsResponder
    (cNum cDen m : ℕ) (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k phase : ℕ) :
    FollowsResponder (X := X) responder 0
      (sparseCutPlayMany (X := X) cNum cDen m hm responder k phase) := by
  induction phase with
  | zero =>
      simp [sparseCutPlayMany]
  | succ phase ih =>
      rw [sparseCutPlayMany_succ]
      have hblock :
          FollowsResponder (X := X) responder (phase * k)
            (sparseCutPlay (X := X) cNum cDen m hm
              (SequentialResponder.shift responder (phase * k)) k) := by
        have hlocal :=
          sparseCutPlay_followsResponder (X := X) cNum cDen m hm
            (SequentialResponder.shift responder (phase * k)) k
        intro n R hget
        have hx := hlocal n R hget
        simpa [SequentialResponder.shift, LazyRound.ofResponder,
          Nat.add_assoc] using hx
      have hlen :
          (sparseCutPlayMany (X := X) cNum cDen m hm responder k phase).length =
            phase * k :=
        sparseCutPlayMany_length (X := X) cNum cDen m hm responder k phase
      have hblock' :
          FollowsResponder (X := X) responder
            (0 + (sparseCutPlayMany (X := X) cNum cDen m hm responder k phase).length)
            (sparseCutPlay (X := X) cNum cDen m hm
              (SequentialResponder.shift responder (phase * k)) k) := by
        simpa [hlen] using hblock
      exact
        followsResponder_append (X := X) (offset := 0)
          (rounds :=
            sparseCutPlayMany (X := X) cNum cDen m hm responder k phase)
          (extra :=
            sparseCutPlay (X := X) cNum cDen m hm
              (SequentialResponder.shift responder (phase * k)) k)
          ih hblock'

/-- Repeating `phase` independent `1/4`-expander phases gives expansion
`phase/4` on the same balanced cuts. -/
theorem sparseCutPlayMany_balancedExpander_of_potential_budget
    {cNum cDen m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k phase : ℕ)
    (hden : 0 < cDen) (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X cNum cDen * (k : ℝ)) :
    IsBalancedEdgeExpanderWith (X := X)
      (sparseCutPlayMany (X := X) cNum cDen m hm responder k phase)
      cNum cDen phase 4 := by
  induction phase with
  | zero =>
      refine ⟨by decide, ?_⟩
      intro T _hlarge _hhalf
      simp
  | succ phase ih =>
      rw [sparseCutPlayMany_succ]
      have hprev := ih
      have hblock :=
        sparseCutPlay_balancedExpander_one_four_of_potential_budget
          (X := X) hm (SequentialResponder.shift responder (phase * k))
          k hden hn hbudget
      have hcombined :=
        balancedEdgeExpanderWith_append_same_den
          (X := X) (rounds₁ :=
            sparseCutPlayMany (X := X) cNum cDen m hm responder k phase)
          (rounds₂ :=
            sparseCutPlay (X := X) cNum cDen m hm
              (SequentialResponder.shift responder (phase * k)) k)
          hprev hblock
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hcombined

/-- Sixteen independent phases at the `1/4` threshold give expansion at
least `4` on every `1/4`-balanced cut.  This stronger constant is convenient
for the deterministic peeling step that upgrades balanced expansion to
all-cut half expansion. -/
theorem sparseCutPlayMany_balancedExpander_four_of_potential_budget
    {m : ℕ} (hm : 2 * m = Fintype.card X)
    (responder : SequentialResponder X) (k : ℕ)
    (hn : 0 < Fintype.card X)
    (hbudget :
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) <
        sparseCutRoundIncrement X 1 4 * (k : ℝ)) :
    IsBalancedEdgeExpanderWith (X := X)
      (sparseCutPlayMany (X := X) 1 4 m hm responder k 16)
      1 4 4 1 := by
  have h :=
    sparseCutPlayMany_balancedExpander_of_potential_budget
      (X := X) hm responder k 16 (by decide : 0 < 4) hn hbudget
  refine ⟨by decide, ?_⟩
  intro T hlarge hhalf
  have hb := h.2 T hlarge hhalf
  omega

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
