import Lax185574Proofs.ResolveRam.CallList
import Lax185574Proofs.StpRam.FinalRead
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
The distances from the color classes of `P` and `Q`, as the glue program
of lem:resolve-lift computes them.

The data of the resolve test `cd X Y r`, whether a vertex of color `X` is
within distance `r` of a vertex of color `Y` in `G`. The program only
asks this for `X ∈ {P, Q}`. It runs a breadth-first search from the
whole color class `X` (`msP`, the ball of the class), and records for
every color `Y` one more than the first layer that reaches `Y`
(`cTab`, `0` if no layer does). The ball of a class is the union of the
balls `ballP` of its vertices, the balls of the core (`msP_iff`), and
these are the balls of `G` (`ballP_withinDist`). A shortest walk has
fewer than `n` steps (`withinDist_card`), so `n` layers suffice.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574Proofs.StpRam Lax185574Proofs.TreeAlgo Lax185574Proofs.ResolveRam
open Lax808846Proofs.Reasoning.Lib.Csr Lax185574Proofs.WalkDistance

/-! ### Balls of sets -/

/-- The ball of radius `s` around the set `S`, along a relation on
`[0, n)`. -/
def msP (n : ℕ) (A : ℕ → ℕ → Prop) (S : ℕ → Prop) : ℕ → ℕ → Prop
  | 0 => S
  | s + 1 => fun v => msP n A S s v ∨ ∃ w < n, msP n A S s w ∧ A w v

/-- **The ball of a set is the union of the balls of its members.** -/
theorem msP_iff (n : ℕ) (A : ℕ → ℕ → Prop) (S : ℕ → Prop) :
    ∀ s v, msP n A S s v ↔ ∃ u, S u ∧ ballP n A u s v
  | 0, v => by simp [msP, ballP]
  | s + 1, v => by
    simp only [msP, ballP, msP_iff n A S s]
    constructor
    · rintro (⟨u, hu, h⟩ | ⟨w, hw, ⟨u, hu, h⟩, hA⟩)
      · exact ⟨u, hu, Or.inl h⟩
      · exact ⟨u, hu, Or.inr ⟨w, hw, h, hA⟩⟩
    · rintro ⟨u, hu, h | ⟨w, hw, h, hA⟩⟩
      · exact Or.inl ⟨u, hu, h⟩
      · exact Or.inr ⟨w, hw, ⟨u, hu, h⟩, hA⟩

variable {n : ℕ}

/-- The adjacency of the resolved pairs of `G` in compressed-row form. -/
noncomputable abbrev adjG (G : PartialGraph (Fin n)) : ℕ → ℕ → Prop :=
  Adj2 (offL G.edge) (tgtL G.edge) (offL G.nonEdge) (tgtL G.nonEdge)

theorem ballP_lt (G : PartialGraph (Fin n)) {u : ℕ} (hu : u < n) :
    ∀ s v, ballP n (adjG G) u s v → v < n
  | 0, v, h => by simp only [ballP] at h; omega
  | s + 1, v, h => by
    rcases h with h | ⟨w, hw, -, hA⟩
    · exact ballP_lt G hu s v h
    · exact adj2_lt G w v hw hA

/-- **The balls of the search are the balls of `G`.** -/
theorem ballP_withinDist (G : PartialGraph (Fin n)) (s : ℕ) (u v : Fin n) :
    ballP n (adjG G) u s v ↔ WithinDist G.resolved s u v := by
  rw [← ballP_iff (adj := adjOf G) (fun w v => mem_adjOf G w v) (fun w v hw h => adj2_lt G w v hw h),
    mem_ballFrom (fun w v => mem_adjOf_resolved G w v)]

/-- The color class `X` as a set of numbers. -/
def clsP (G : PartialGraph (Fin n)) (X : ℕ) (u : ℕ) : Prop := ∃ h : u < n, G.color ⟨u, h⟩ = X

theorem msP_withinDist (G : PartialGraph (Fin n)) (X s : ℕ) (v : Fin n) :
    msP n (adjG G) (clsP G X) s v ↔ ∃ x : Fin n, G.color x = X ∧ WithinDist G.resolved s x v := by
  rw [msP_iff]
  constructor
  · rintro ⟨u, ⟨hu, hX⟩, h⟩
    exact ⟨⟨u, hu⟩, hX, (ballP_withinDist G s ⟨u, hu⟩ v).1 h⟩
  · rintro ⟨x, hX, h⟩
    exact ⟨x, ⟨x.isLt, hX⟩, (ballP_withinDist G s x v).2 h⟩

theorem msP_lt (G : PartialGraph (Fin n)) (X s v : ℕ) (h : msP n (adjG G) (clsP G X) s v) : v < n := by
  obtain ⟨u, ⟨hu, -⟩, hb⟩ := (msP_iff _ _ _ s v).1 h
  exact ballP_lt G hu s v hb

/-! ### Shortest walks -/

/-- A vertex within some distance is within distance `|V| - 1`. -/
theorem withinDist_card {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} {d : ℕ}
    {u v : W} (h : WithinDist H d u v) : WithinDist H (Fintype.card W - 1) u v := by
  obtain ⟨p, -⟩ := h
  refine ⟨p.bypass, ?_⟩
  have := p.bypass_isPath.length_lt
  omega

/-! ### The table of a color class -/

open Classical in
/-- One more than the distance from the class `X` to the class `Y` in
`G`, and `0` if there is no walk between them. -/
noncomputable def cTab (G : PartialGraph (Fin n)) (X Y : ℕ) : ℕ :=
  if h : ∃ s, ∃ x y : Fin n, G.color x = X ∧ G.color y = Y ∧ WithinDist G.resolved s x y then
    Nat.find h + 1 else 0

/-- **The test `cd` from the table.** -/
theorem cdSem_iff (G : PartialGraph (Fin n)) (X Y r : ℕ) :
    cdSem G X Y r = true ↔ cTab G X Y ≠ 0 ∧ cTab G X Y ≤ r + 1 := by
  classical
  simp only [cdSem, decide_eq_true_eq, cTab]
  split_ifs with h
  · constructor
    · rintro ⟨x, y, hx, hy, hd⟩
      exact ⟨by omega, by have := Nat.find_min' h ⟨x, y, hx, hy, hd⟩; omega⟩
    · rintro ⟨-, hr⟩
      obtain ⟨x, y, hx, hy, hd⟩ := Nat.find_spec h
      exact ⟨x, y, hx, hy, withinDist_mono (by omega) hd⟩
  · simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    rintro ⟨x, y, hx, hy, hd⟩
    exact h ⟨r, x, y, hx, hy, hd⟩

/-- The distance of the table is below `n`. -/
theorem cTab_le (G : PartialGraph (Fin n)) (X Y : ℕ) : cTab G X Y ≤ n := by
  classical
  unfold cTab
  split_ifs with h
  · obtain ⟨s, x, y, hx, hy, hd⟩ := h
    have h' := withinDist_card hd
    rw [Fintype.card_fin] at h'
    have := Nat.find_min' (⟨s, x, y, hx, hy, hd⟩ : ∃ s, ∃ x y : Fin n, G.color x = X ∧
      G.color y = Y ∧ WithinDist G.resolved s x y) ⟨x, y, hx, hy, h'⟩
    have : 1 ≤ n := Fin.pos x
    omega
  · omega

/-- The table is `t + 1` exactly if layer `t` is the first that reaches
the class `Y`. -/
theorem cTab_eq_succ (G : PartialGraph (Fin n)) (X Y t : ℕ) :
    cTab G X Y = t + 1 ↔ (∃ y : Fin n, G.color y = Y ∧ msP n (adjG G) (clsP G X) t y) ∧
      ∀ t' < t, ¬ ∃ y : Fin n, G.color y = Y ∧ msP n (adjG G) (clsP G X) t' y := by
  classical
  have key : ∀ s, (∃ y : Fin n, G.color y = Y ∧ msP n (adjG G) (clsP G X) s y) ↔
      ∃ x y : Fin n, G.color x = X ∧ G.color y = Y ∧ WithinDist G.resolved s x y := by
    intro s
    simp only [msP_withinDist]
    constructor
    · rintro ⟨y, hy, x, hx, hd⟩; exact ⟨x, y, hx, hy, hd⟩
    · rintro ⟨x, y, hx, hy, hd⟩; exact ⟨y, hy, x, hx, hd⟩
  simp only [key]
  unfold cTab
  split_ifs with h
  · rw [Nat.add_right_cancel_iff, Nat.find_eq_iff]
  · simp only [false_iff, not_and]
    intro h'
    exact absurd ⟨t, h'⟩ h

/-- The table is `0` exactly if no layer below `n` reaches the class `Y`. -/
theorem cTab_eq_zero (G : PartialGraph (Fin n)) (X Y : ℕ) :
    cTab G X Y = 0 ↔ ∀ t < n, ¬ ∃ y : Fin n, G.color y = Y ∧ msP n (adjG G) (clsP G X) t y := by
  classical
  simp only [msP_withinDist]
  unfold cTab
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨s, x, y, hx, hy, hd⟩ := h
    have h' := withinDist_card hd
    rw [Fintype.card_fin] at h'
    exact ⟨n - 1, by have := Fin.pos x; omega, y, hy, x, hx, h'⟩
  · simp only [true_iff]
    rintro t - ⟨y, hy, x, hx, hd⟩
    exact h ⟨t, x, y, hx, hy, hd⟩

end Lax185574Proofs.ResolveRam.Glue
