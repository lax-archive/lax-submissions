import Lax185574Proofs.Gaifman.GaifmanNormalForm

/-!
Basic facts about the bounded-walk presentation of Gaifman distance.  Keeping
these facts in one module lets the normalization proof reason about radii
without unfolding walks at every use.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/Distance.lean`.
-/

namespace Lax185574Proofs.Gaifman.Distance

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality

variable {σ : Vocabulary} {M : Type*} (A : Structure σ M)

/-- Gaifman adjacency is symmetric. -/
theorem adjacent_symm {a b : M} (h : gaifmanAdjacent A a b) :
    gaifmanAdjacent A b a := by
  rcases h with ⟨hne, R, tuple, hR, i, j, hij, hi, hj⟩
  exact ⟨hne.symm, R, tuple, hR, j, i, hij.symm, hj, hi⟩

/-- Every point is at distance at most every radius from itself. -/
theorem distanceAtMost_refl (r : ℕ) (a : M) : distanceAtMost A r a a := by
  induction r with
  | zero => rfl
  | succ r ih => exact Or.inl ih

/-- A bounded-distance witness remains valid after increasing the radius by
one. -/
theorem distanceAtMost_succ {r : ℕ} {a b : M}
    (h : distanceAtMost A r a b) : distanceAtMost A (r + 1) a b :=
  Or.inl h

/-- Bounded Gaifman distance is monotone in its numerical bound. -/
theorem distanceAtMost_mono {r s : ℕ} (hrs : r ≤ s) {a b : M}
    (h : distanceAtMost A r a b) : distanceAtMost A s a b := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ s _ ih => exact distanceAtMost_succ A ih

/-- An edge followed by a walk of radius `r` is a walk of radius `r + 1`. -/
theorem distanceAtMost_of_adjacent_left {r : ℕ} {a b c : M}
    (hab : gaifmanAdjacent A a b) (hbc : distanceAtMost A r b c) :
    distanceAtMost A (r + 1) a c :=
  Or.inr ⟨b, hab, hbc⟩

/-- Adjacent points have distance at most one. -/
theorem distanceAtMost_one_of_adjacent {a b : M}
    (h : gaifmanAdjacent A a b) : distanceAtMost A 1 a b :=
  Or.inr ⟨b, h, rfl⟩

/-- A walk of radius `r` followed by an edge is a walk of radius `r + 1`. -/
theorem distanceAtMost_of_adjacent_right {r : ℕ} {a b c : M}
    (hab : distanceAtMost A r a b) (hbc : gaifmanAdjacent A b c) :
    distanceAtMost A (r + 1) a c := by
  induction r generalizing a b with
  | zero =>
      subst b
      exact Or.inr ⟨c, hbc, rfl⟩
  | succ r ih =>
      rcases hab with hab | ⟨d, had, hdb⟩
      · exact Or.inl (ih hab hbc)
      · exact Or.inr ⟨d, had, ih hdb hbc⟩

/-- Bounded Gaifman distance is symmetric. -/
theorem distanceAtMost_symm {r : ℕ} {a b : M}
    (h : distanceAtMost A r a b) : distanceAtMost A r b a := by
  induction r generalizing a b with
  | zero => exact h.symm
  | succ r ih =>
      rcases h with h | ⟨c, hac, hcb⟩
      · exact Or.inl (ih h)
      · exact distanceAtMost_of_adjacent_right A (ih hcb) (adjacent_symm A hac)

/-- Concatenating bounded walks adds their radius bounds. -/
theorem distanceAtMost_trans {r s : ℕ} {a b c : M}
    (hab : distanceAtMost A r a b) (hbc : distanceAtMost A s b c) :
    distanceAtMost A (r + s) a c := by
  induction r generalizing a b with
  | zero =>
      subst b
      simpa using hbc
  | succ r ih =>
      rcases hab with hab | ⟨d, had, hdb⟩
      · simpa [Nat.succ_add] using distanceAtMost_succ A (ih hab hbc)
      · simpa [Nat.succ_add] using
          distanceAtMost_of_adjacent_left A had (ih hdb hbc)

/-- Enlarging the radius enlarges the union of balls around anchors and
constants. -/
theorem inBallAround_mono {r s k : ℕ} (hrs : r ≤ s)
    (anchors : Fin k → M) {x : M} (h : inBallAround A r anchors x) :
    inBallAround A s anchors x := by
  rcases h with ⟨i, hi⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨i, distanceAtMost_mono A hrs hi⟩
  · exact Or.inr ⟨c, distanceAtMost_mono A hrs hc⟩

/-- Moving a bounded distance away from a ball enlarges its radius by that
distance. -/
theorem inBallAround_of_distance {r s k : ℕ} (anchors : Fin k → M)
    {x y : M} (hx : inBallAround A r anchors x)
    (hxy : distanceAtMost A s x y) :
    inBallAround A (r + s) anchors y := by
  rcases hx with ⟨i, hi⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨i, distanceAtMost_trans A hi hxy⟩
  · exact Or.inr ⟨c, distanceAtMost_trans A hc hxy⟩

/-- Every anchor is in every ball around the anchor tuple. -/
theorem anchor_inBallAround {r k : ℕ} (anchors : Fin k → M) (i : Fin k) :
    inBallAround A r anchors (anchors i) :=
  Or.inl ⟨i, distanceAtMost_refl A r (anchors i)⟩

/-- Every interpreted constant is in every ball used for locality. -/
theorem constant_inBallAround {r k : ℕ} (anchors : Fin k → M)
    (c : σ.Constant) :
    inBallAround A r anchors (A.constant c) :=
  Or.inr ⟨c, distanceAtMost_refl A r (A.constant c)⟩

/-- Every entry of a relation tuple is at distance at most one from any fixed
entry of that tuple. -/
theorem relation_tuple_distance_one {R : σ.Relation}
    {tuple : Fin (σ.arity R) → M} (hR : A.relation R tuple)
    (i j : Fin (σ.arity R)) :
    distanceAtMost A 1 (tuple i) (tuple j) := by
  by_cases hval : tuple i = tuple j
  · exact Or.inl hval
  · have hij : i ≠ j := by
      intro h
      exact hval (congrArg tuple h)
    exact Or.inr ⟨tuple j,
      ⟨hval, R, tuple, hR, i, j, hij, rfl, rfl⟩, rfl⟩

end Lax185574Proofs.Gaifman.Distance
