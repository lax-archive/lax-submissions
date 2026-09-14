/-
**The regular conditions on a string over the alphabet of snake letters, I.**

Three of the four conditions that make a string `w` over `Transducers.SnakeLetter` represent a snake
graph of width at most `k` are checked here:

* every vertex has at most one outgoing edge, and at most one incoming edge;
* no column is visited more than `k` times;
* the graph has at most one source.

The first two are conditions on the pair of letters around a column, so the language they define is
regular by `Transducers.SnakeLoc.isRegular_pairsOK`.  The third one is not local -- two sources may
sit in far apart columns -- but a left-to-right automaton only has to remember whether it has
already seen a source, so the language is again regular, this time by
`Transducers.RegAut.isRegular_foldl`.

The remaining condition, that the graph has no directed cycle, is
`RequestProject/PartC/SnakeAlphCyc.lean`.
-/
import Lax916827Proofs.Source.PartC.SnakeAlphLoc
import Lax916827Proofs.Source.PartC.SnakeAlphChar
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SnakeGraph

variable {Q B : Type}

/-! ## The local conditions -/

/-- At most one outgoing edge, for every vertex of a column with the letters `l` and `r` around
it. -/
def OutDegLe1At (l r : Option (SnakeLetter Q B)) : Prop :=
  ∀ q, ¬ ((outR r q).isSome ∧ (outL l q).isSome)

/-- At most one incoming edge, for every vertex of a column with the letters `l` and `r` around it:
the edges coming from the left have pairwise distinct targets, so do the edges coming from the
right, and no vertex is the target of both. -/
def InDegLe1At (l r : Option (SnakeLetter Q B)) : Prop :=
  (∀ q p₁ p₂ o₁ o₂, outR l p₁ = some (q, o₁) → outR l p₂ = some (q, o₂) → p₁ = p₂) ∧
  (∀ q p₁ p₂ o₁ o₂, outL r p₁ = some (q, o₁) → outL r p₂ = some (q, o₂) → p₁ = p₂) ∧
  (∀ q p₁ p₂ o₁ o₂, outR l p₁ = some (q, o₁) → outL r p₂ = some (q, o₂) → False)

/-- The column with the letters `l` and `r` around it is visited at most `k` times. -/
noncomputable def ColVisitsLeAt (k : ℕ) (l r : Option (SnakeLetter Q B)) : Prop :=
  {q : Q | IncidentAt l r q}.ncard ≤ k

/-- All the local conditions at a column with the letters `l` and `r` around it. -/
noncomputable def ColOK (k : ℕ) (l r : Option (SnakeLetter Q B)) : Prop :=
  OutDegLe1At l r ∧ InDegLe1At l r ∧ ColVisitsLeAt k l r

variable {w : List (SnakeLetter Q B)}

lemma outDegLe1_iff : OutDegLe1 w ↔ ∀ x, OutDegLe1At (prevLet w x) w[x]? := by
  constructor
  · rintro h x q ⟨h1, h2⟩
    obtain ⟨z₁, hz₁⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨z₂, hz₂⟩ := Option.isSome_iff_exists.1 h2
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · rw [prevLet_zero, outL_none] at hz₂; exact absurd hz₂ (by simp)
    · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      have e1 : Edge w (q, y + 1) (z₁.1, y + 1 + 1) z₁.2 := edge_of_outR (by rw [hz₁])
      have e2 : Edge w (q, y + 1) (z₂.1, y) z₂.2 := edge_of_outL (by rw [hz₂])
      have heq := (h _ _ _ _ _ e1 e2).1
      have : y + 1 + 1 = y := congrArg Prod.snd heq
      omega
  · intro h v v₁ v₂ o₁ o₂ h1 h2
    obtain ⟨q, x⟩ := v
    rcases edge_out_cases h1 with ⟨hc1, he1⟩ | ⟨hc1, he1⟩ <;>
        rcases edge_out_cases h2 with ⟨hc2, he2⟩ | ⟨hc2, he2⟩
    · rw [he1, Option.some_inj, Prod.ext_iff] at he2
      exact ⟨Prod.ext he2.1 (by omega), he2.2⟩
    · exact absurd ⟨by rw [he1]; rfl, by rw [he2]; rfl⟩ (h x q)
    · exact absurd ⟨by rw [he2]; rfl, by rw [he1]; rfl⟩ (h x q)
    · rw [he1, Option.some_inj, Prod.ext_iff] at he2
      exact ⟨Prod.ext he2.1 (by omega), he2.2⟩

lemma inDegLe1_iff : InDegLe1 w ↔ ∀ x, InDegLe1At (prevLet w x) w[x]? := by
  constructor
  · intro h x
    refine ⟨?_, ?_, ?_⟩
    · intro q p₁ p₂ o₁ o₂ h1 h2
      rcases Nat.eq_zero_or_pos x with rfl | hpos
      · rw [prevLet_zero, outR_none] at h1; exact absurd h1 (by simp)
      · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
        rw [prevLet_succ] at h1 h2
        have e1 : Edge w (p₁, y) (q, y + 1) o₁ := edge_of_outR h1
        have e2 : Edge w (p₂, y) (q, y + 1) o₂ := edge_of_outR h2
        exact congrArg Prod.fst (h _ _ _ _ _ e1 e2).1
    · intro q p₁ p₂ o₁ o₂ h1 h2
      have e1 : Edge w (p₁, x + 1) (q, x) o₁ := edge_of_outL (by rw [prevLet_succ]; exact h1)
      have e2 : Edge w (p₂, x + 1) (q, x) o₂ := edge_of_outL (by rw [prevLet_succ]; exact h2)
      exact congrArg Prod.fst (h _ _ _ _ _ e1 e2).1
    · intro q p₁ p₂ o₁ o₂ h1 h2
      rcases Nat.eq_zero_or_pos x with rfl | hpos
      · rw [prevLet_zero, outR_none] at h1; exact absurd h1 (by simp)
      · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
        rw [prevLet_succ] at h1
        have e1 : Edge w (p₁, y) (q, y + 1) o₁ := edge_of_outR h1
        have e2 : Edge w (p₂, y + 1 + 1) (q, y + 1) o₂ :=
          edge_of_outL (by rw [prevLet_succ]; exact h2)
        have := congrArg Prod.snd (h _ _ _ _ _ e1 e2).1
        simp only at this
        omega
  · intro h u₁ u₂ v o₁ o₂ h1 h2
    obtain ⟨q, x⟩ := v
    obtain ⟨ha, hb, hc⟩ := h x
    rcases edge_in_cases h1 with ⟨hc1, he1⟩ | ⟨hc1, he1⟩ <;>
        rcases edge_in_cases h2 with ⟨hc2, he2⟩ | ⟨hc2, he2⟩
    · have hp := ha q u₁.1 u₂.1 o₁ o₂ he1 he2
      rw [hp] at he1
      rw [he1, Option.some_inj] at he2
      exact ⟨Prod.ext hp (by omega), (Prod.ext_iff.1 he2).2⟩
    · exact absurd (hc q u₁.1 u₂.1 o₁ o₂ he1 he2) (by simp)
    · exact absurd (hc q u₂.1 u₁.1 o₂ o₁ he2 he1) (by simp)
    · have hp := hb q u₁.1 u₂.1 o₁ o₂ he1 he2
      rw [hp] at he1
      rw [he1, Option.some_inj] at he2
      exact ⟨Prod.ext hp (by omega), (Prod.ext_iff.1 he2).2⟩

lemma widthLe_iff (k : ℕ) : SnakeWidthLe w k ↔ ∀ x, ColVisitsLeAt k (prevLet w x) w[x]? := by
  have hset : ∀ x, {q : Q | Incident w (q, x)} = {q : Q | IncidentAt (prevLet w x) w[x]? q} := by
    intro x; ext q; exact incident_iff
  constructor
  · intro h x
    have := h x
    rwa [colVisits, hset x] at this
  · intro h x
    have := h x
    rwa [colVisits, hset x]

/-- Beyond the end of the string, all the local conditions hold. -/
lemma colOK_none (k : ℕ) : ColOK k (none : Option (SnakeLetter Q B)) none := by
  refine ⟨fun q h => by simpa using h.1, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro q p₁ p₂ o₁ o₂ h1 _; exact absurd h1 (by simp)
  · intro q p₁ p₂ o₁ o₂ h1 _; exact absurd h1 (by simp)
  · intro q p₁ p₂ o₁ o₂ h1 _; exact absurd h1 (by simp)
  · have : {q : Q | IncidentAt (none : Option (SnakeLetter Q B)) none q} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, IncidentAt, HasOutAt,
        HasInAt, outR_none, outL_none]
      rintro ((h | h) | (⟨p, o, h⟩ | ⟨p, o, h⟩)) <;> simp at h
    rw [ColVisitsLeAt, this]
    simp

/-- **The local conditions, column by column.** -/
theorem locConditions_iff (k : ℕ) (w : List (SnakeLetter Q B)) :
    (OutDegLe1 w ∧ InDegLe1 w ∧ SnakeWidthLe w k) ↔
      ∀ x ≤ w.length, ColOK k (prevLet w x) w[x]? := by
  rw [outDegLe1_iff, inDegLe1_iff, widthLe_iff k]
  constructor
  · rintro ⟨h1, h2, h3⟩ x -
    exact ⟨h1 x, h2 x, h3 x⟩
  · intro h
    have hall : ∀ x, ColOK k (prevLet w x) w[x]? := by
      intro x
      rcases Nat.lt_or_ge w.length x with hx | hx
      · obtain ⟨h1, h2⟩ := letters_none_of_lt hx
        rw [h1, h2]
        exact colOK_none k
      · exact h x hx
    exact ⟨fun x => (hall x).1, fun x => (hall x).2.1, fun x => (hall x).2.2⟩

/-- **The local conditions define a regular language.** -/
theorem isRegular_locOK [Finite Q] [Finite B] (k : ℕ) :
    Language.IsRegular {w : List (SnakeLetter Q B) |
      OutDegLe1 w ∧ InDegLe1 w ∧ SnakeWidthLe w k} := by
  classical
  have h := SnakeLoc.isRegular_pairsOK (Γ := SnakeLetter Q B)
    (fun l r => decide (ColOK k l r))
  refine RegAut.isRegular_of_eq h (fun w => ?_)
  simp only [SnakeLoc.PairsOK, decide_eq_true_eq]
  exact locConditions_iff k w

/-! ## At most one source -/

/-- The vertex `(q, x)` is a source of the graph described by `w`, read off the two letters around
the column `x`. -/
def SrcAtIdx (w : List (SnakeLetter Q B)) (x : ℕ) (q : Q) : Prop :=
  IsSrcAt (prevLet w x) w[x]? q

lemma src_iff_srcAtIdx {w : List (SnakeLetter Q B)} {v : Vtx Q} :
    Src w v ↔ SrcAtIdx w v.2 v.1 := src_iff

/-- The column with the letters `l` and `r` around it contains a source. -/
def HasSrcAt (l r : Option (SnakeLetter Q B)) : Prop := ∃ q, IsSrcAt l r q

/-- The column with the letters `l` and `r` around it contains two distinct sources. -/
def HasTwoSrcAt (l r : Option (SnakeLetter Q B)) : Prop :=
  ∃ q q', q ≠ q' ∧ IsSrcAt l r q ∧ IsSrcAt l r q'

/-- There is a source in one of the columns `< n`. -/
def SrcBelow (w : List (SnakeLetter Q B)) (n : ℕ) : Prop := ∃ q x, x < n ∧ SrcAtIdx w x q

/-- There are two distinct sources in the columns `< n`. -/
def TwoSrcBelow (w : List (SnakeLetter Q B)) (n : ℕ) : Prop :=
  ∃ q x q' x', x < n ∧ x' < n ∧ (q, x) ≠ (q', x') ∧ SrcAtIdx w x q ∧ SrcAtIdx w x' q'

/-- Splitting off the last column. -/
lemma twoSrcBelow_succ (w : List (SnakeLetter Q B)) (n : ℕ) :
    TwoSrcBelow w (n + 1) ↔ TwoSrcBelow w n ∨ HasTwoSrcAt (prevLet w n) w[n]? ∨
      (SrcBelow w n ∧ HasSrcAt (prevLet w n) w[n]?) := by
  constructor
  · rintro ⟨q, x, q', x', hx, hx', hne, h1, h2⟩
    rcases Nat.lt_or_ge x n with hxn | hxn
    · rcases Nat.lt_or_ge x' n with hxn' | hxn'
      · exact Or.inl ⟨q, x, q', x', hxn, hxn', hne, h1, h2⟩
      · have hx'n : x' = n := by omega
        subst hx'n
        exact Or.inr (Or.inr ⟨⟨q, x, hxn, h1⟩, ⟨q', h2⟩⟩)
    · have hxn2 : x = n := by omega
      subst hxn2
      rcases Nat.lt_or_ge x' x with hxn' | hxn'
      · exact Or.inr (Or.inr ⟨⟨q', x', hxn', h2⟩, ⟨q, h1⟩⟩)
      · have hx'n : x' = x := by omega
        subst hx'n
        refine Or.inr (Or.inl ⟨q, q', ?_, h1, h2⟩)
        intro hq; exact hne (by rw [hq])
  · rintro (⟨q, x, q', x', hx, hx', hne, h1, h2⟩ | ⟨q, q', hne, h1, h2⟩ |
      ⟨⟨q, x, hx, h1⟩, ⟨q', h2⟩⟩)
    · exact ⟨q, x, q', x', by omega, by omega, hne, h1, h2⟩
    · exact ⟨q, n, q', n, by omega, by omega, by simpa using hne, h1, h2⟩
    · exact ⟨q, x, q', n, by omega, by omega, by
        intro hq; exact absurd (congrArg Prod.snd hq) (by simpa using Nat.ne_of_lt hx), h1, h2⟩

/-! ### Appending a letter -/

variable {c : SnakeLetter Q B}

lemma srcAtIdx_append_of_lt {w : List (SnakeLetter Q B)} {x : ℕ} {q : Q} (hx : x < w.length) :
    SrcAtIdx (w ++ [c]) x q ↔ SrcAtIdx w x q := by
  unfold SrcAtIdx
  rw [show prevLet (w ++ [c]) x = prevLet w x from SnakeLoc.prevAt_append_one (le_of_lt hx),
    List.getElem?_append_left hx]

lemma srcAtIdx_append_eq {w : List (SnakeLetter Q B)} {q : Q} :
    SrcAtIdx (w ++ [c]) w.length q ↔ IsSrcAt w.getLast? (some c) q := by
  unfold SrcAtIdx
  rw [show prevLet (w ++ [c]) w.length = w.getLast? from
      (SnakeLoc.prevAt_append_one (le_refl _)).trans (SnakeLoc.prevAt_length w),
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

lemma srcBelow_append {w : List (SnakeLetter Q B)} {n : ℕ} (hn : n ≤ w.length) :
    SrcBelow (w ++ [c]) n ↔ SrcBelow w n := by
  constructor
  · rintro ⟨q, x, hx, h⟩
    exact ⟨q, x, hx, (srcAtIdx_append_of_lt (by omega)).1 h⟩
  · rintro ⟨q, x, hx, h⟩
    exact ⟨q, x, hx, (srcAtIdx_append_of_lt (by omega)).2 h⟩

lemma twoSrcBelow_append {w : List (SnakeLetter Q B)} {n : ℕ} (hn : n ≤ w.length) :
    TwoSrcBelow (w ++ [c]) n ↔ TwoSrcBelow w n := by
  constructor
  · rintro ⟨q, x, q', x', hx, hx', hne, h1, h2⟩
    exact ⟨q, x, q', x', hx, hx', hne, (srcAtIdx_append_of_lt (by omega)).1 h1,
      (srcAtIdx_append_of_lt (by omega)).1 h2⟩
  · rintro ⟨q, x, q', x', hx, hx', hne, h1, h2⟩
    exact ⟨q, x, q', x', hx, hx', hne, (srcAtIdx_append_of_lt (by omega)).2 h1,
      (srcAtIdx_append_of_lt (by omega)).2 h2⟩

lemma hasSrcAt_append {w : List (SnakeLetter Q B)} :
    HasSrcAt (prevLet (w ++ [c]) w.length) (w ++ [c])[w.length]? ↔ HasSrcAt w.getLast? (some c) := by
  constructor
  · rintro ⟨q, h⟩; exact ⟨q, srcAtIdx_append_eq.1 h⟩
  · rintro ⟨q, h⟩; exact ⟨q, srcAtIdx_append_eq.2 h⟩

lemma hasTwoSrcAt_append {w : List (SnakeLetter Q B)} :
    HasTwoSrcAt (prevLet (w ++ [c]) w.length) (w ++ [c])[w.length]? ↔
      HasTwoSrcAt w.getLast? (some c) := by
  constructor
  · rintro ⟨q, q', hne, h1, h2⟩
    exact ⟨q, q', hne, srcAtIdx_append_eq.1 h1, srcAtIdx_append_eq.1 h2⟩
  · rintro ⟨q, q', hne, h1, h2⟩
    exact ⟨q, q', hne, srcAtIdx_append_eq.2 h1, srcAtIdx_append_eq.2 h2⟩

/-! ### The automaton -/

/-- The state of the automaton checking that there is at most one source: the previous letter,
whether a source has already been seen, and whether two distinct sources have already been seen. -/
abbrev SrcSt (Q B : Type) := Option (SnakeLetter Q B) × Prop × Prop

/-- One step of that automaton. -/
def srcStep : SrcSt Q B → SnakeLetter Q B → SrcSt Q B := fun s c =>
  (some c, s.2.1 ∨ HasSrcAt s.1 (some c),
    s.2.2 ∨ HasTwoSrcAt s.1 (some c) ∨ (s.2.1 ∧ HasSrcAt s.1 (some c)))

/-- The initial state. -/
def srcInit (Q B : Type) : SrcSt Q B := (none, False, False)

private lemma foldl_srcStep_fst (w : List (SnakeLetter Q B)) :
    (w.foldl srcStep (srcInit Q B)).1 = w.getLast? := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton v c ih => rw [List.foldl_append]; simp [srcStep]

private lemma foldl_srcStep_snd (w : List (SnakeLetter Q B)) :
    (w.foldl srcStep (srcInit Q B)).2.1 ↔ SrcBelow w w.length := by
  induction w using List.reverseRecOn with
  | nil =>
      simp only [List.foldl_nil, srcInit, List.length_nil, SrcBelow]
      simp
  | append_singleton v c ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, srcStep]
      rw [ih, foldl_srcStep_fst v]
      rw [show (v ++ [c]).length = v.length + 1 by simp]
      constructor
      · rintro (h | h)
        · obtain ⟨q, x, hx, hq⟩ := h
          exact ⟨q, x, by omega, (srcAtIdx_append_of_lt hx).2 hq⟩
        · obtain ⟨q, hq⟩ := h
          exact ⟨q, v.length, by omega, srcAtIdx_append_eq.2 hq⟩
      · rintro ⟨q, x, hx, hq⟩
        rcases Nat.lt_or_ge x v.length with hlt | hge
        · exact Or.inl ⟨q, x, hlt, (srcAtIdx_append_of_lt hlt).1 hq⟩
        · have : x = v.length := by omega
          subst this
          exact Or.inr ⟨q, srcAtIdx_append_eq.1 hq⟩

private lemma foldl_srcStep_thd (w : List (SnakeLetter Q B)) :
    (w.foldl srcStep (srcInit Q B)).2.2 ↔ TwoSrcBelow w w.length := by
  induction w using List.reverseRecOn with
  | nil =>
      simp only [List.foldl_nil, srcInit, List.length_nil, TwoSrcBelow]
      simp
  | append_singleton v c ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, srcStep]
      rw [ih, foldl_srcStep_snd v, foldl_srcStep_fst v]
      rw [show (v ++ [c]).length = v.length + 1 by simp, twoSrcBelow_succ,
        twoSrcBelow_append (c := c) (le_refl _), srcBelow_append (c := c) (le_refl _),
        hasSrcAt_append, hasTwoSrcAt_append]

/-- The two distinct sources of a graph that has more than one live in the columns
`0, …, w.length`. -/
lemma not_srcUnique_iff (w : List (SnakeLetter Q B)) :
    ¬ SrcUnique w ↔ TwoSrcBelow w (w.length + 1) := by
  constructor
  · intro h
    rw [SrcUnique] at h
    push_neg at h
    obtain ⟨v, v', hv, hv', hne⟩ := h
    refine ⟨v.1, v.2, v'.1, v'.2, ?_, ?_, ?_, src_iff_srcAtIdx.1 hv, src_iff_srcAtIdx.1 hv'⟩
    · have := col_le_of_hasOut hv.1; omega
    · have := col_le_of_hasOut hv'.1; omega
    · intro hq; exact hne (by rw [show v = (v.1, v.2) from rfl, hq])
  · rintro ⟨q, x, q', x', -, -, hne, h1, h2⟩ hu
    exact hne (hu (q, x) (q', x') (src_iff_srcAtIdx.2 h1) (src_iff_srcAtIdx.2 h2))

/-- **Having at most one source is a regular condition.** -/
theorem isRegular_srcUnique [Finite Q] [Finite B] :
    Language.IsRegular {w : List (SnakeLetter Q B) | SrcUnique w} := by
  classical
  have h := RegAut.isRegular_foldl (Γ := SnakeLetter Q B) srcStep (srcInit Q B)
    {s : SrcSt Q B | ¬ (s.2.2 ∨ HasTwoSrcAt s.1 none ∨ (s.2.1 ∧ HasSrcAt s.1 none))}
  refine RegAut.isRegular_of_eq h (fun w => ?_)
  have hf := foldl_srcStep_fst (Q := Q) (B := B) w
  have hs := foldl_srcStep_snd (Q := Q) (B := B) w
  have ht := foldl_srcStep_thd (Q := Q) (B := B) w
  show SrcUnique w ↔ ¬ ((List.foldl srcStep (srcInit Q B) w).2.2 ∨
      HasTwoSrcAt (List.foldl srcStep (srcInit Q B) w).1 none ∨
        ((List.foldl srcStep (srcInit Q B) w).2.1 ∧
          HasSrcAt (List.foldl srcStep (srcInit Q B) w).1 none))
  rw [hf, hs, ht, show w.getLast? = prevLet w w.length from (SnakeLoc.prevAt_length w).symm,
    show (none : Option (SnakeLetter Q B)) = w[w.length]? from
      (List.getElem?_eq_none (le_refl _)).symm]
  rw [← twoSrcBelow_succ, ← not_srcUnique_iff, not_not]

end SnakeGraph

end Lax916827Proofs.Transducers
