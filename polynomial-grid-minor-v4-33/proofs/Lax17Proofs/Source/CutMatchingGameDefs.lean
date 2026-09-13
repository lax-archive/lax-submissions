import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Abstract cut-matching game definitions

This file contains the finite, graph-free objects used in the
cut-matching-game proof: full bisections of a finite vertex set, perfect
matchings across a bisection, the multiset-free family of matching edges
generated over a finite index set of rounds, and the half-expansion property
for that family.

The definitions are intentionally abstract in the vertex type.  The hairy-grid
construction later instantiates the matching player by the transported local
crossbar matchings.
-/

namespace SimpleGraph
namespace CutMatchingGame


/-- A full bisection of a finite set: two disjoint sets of equal cardinality
whose union is all vertices.  This is the cut player's move in one round. -/
structure Bisection (X : Type u) [Fintype X] [DecidableEq X] where
  left : Finset X
  right : Finset X
  disjoint : Disjoint left right
  card_eq : left.card = right.card
  cover : left ∪ right = Finset.univ

namespace Bisection

variable {X : Type u} [Fintype X] [DecidableEq X] (B : Bisection X)

@[simp]
theorem mem_left_or_right (x : X) : x ∈ B.left ∨ x ∈ B.right := by
  have hx : x ∈ B.left ∪ B.right := by
    rw [B.cover]
    exact Finset.mem_univ x
  simpa [Finset.mem_union] using hx

theorem not_mem_right_of_mem_left {x : X} (hx : x ∈ B.left) : x ∉ B.right := by
  exact fun hy => Finset.disjoint_left.mp B.disjoint hx hy

theorem not_mem_left_of_mem_right {x : X} (hx : x ∈ B.right) : x ∉ B.left := by
  exact fun hy => Finset.disjoint_left.mp B.disjoint hy hx

theorem mem_right_iff_not_mem_left (x : X) : x ∈ B.right ↔ x ∉ B.left := by
  constructor
  · exact B.not_mem_left_of_mem_right
  · intro hx
    rcases B.mem_left_or_right x with hleft | hright
    · exact False.elim (hx hleft)
    · exact hright

theorem mem_left_iff_not_mem_right (x : X) : x ∈ B.left ↔ x ∉ B.right := by
  constructor
  · exact B.not_mem_right_of_mem_left
  · intro hx
    rcases B.mem_left_or_right x with hleft | hright
    · exact hleft
    · exact False.elim (hx hright)

theorem card_left_add_card_right : B.left.card + B.right.card = Fintype.card X := by
  have hcard_union :
      (B.left ∪ B.right).card = B.left.card + B.right.card := by
    rw [Finset.card_union_of_disjoint B.disjoint]
  calc
    B.left.card + B.right.card = (B.left ∪ B.right).card := by
      exact hcard_union.symm
    _ = (Finset.univ : Finset X).card := by rw [B.cover]
    _ = Fintype.card X := Finset.card_univ

theorem two_mul_left_card : 2 * B.left.card = Fintype.card X := by
  calc
    2 * B.left.card = B.left.card + B.left.card := by omega
    _ = B.left.card + B.right.card := by rw [B.card_eq]
    _ = Fintype.card X := B.card_left_add_card_right

theorem two_mul_right_card : 2 * B.right.card = Fintype.card X := by
  calc
    2 * B.right.card = B.right.card + B.right.card := by omega
    _ = B.left.card + B.right.card := by
      rw [← B.card_eq]
    _ = Fintype.card X := B.card_left_add_card_right

/-- Build a bisection from a chosen half-size left side. -/
noncomputable def ofLeftHalf (S : Finset X)
    (hhalf : 2 * S.card = Fintype.card X) : Bisection X where
  left := S
  right := Finset.univ \ S
  disjoint := by
    rw [Finset.disjoint_left]
    intro x hx hxcomp
    exact (Finset.mem_sdiff.mp hxcomp).2 hx
  card_eq := by
    have hsub : S ⊆ (Finset.univ : Finset X) := by
      intro x _; exact Finset.mem_univ x
    have hright :
        (Finset.univ \ S).card = Fintype.card X - S.card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ]
    rw [hright]
    omega
  cover := by
    ext x
    simp

/-- Any set of size at most half the ground set can be extended to the left
side of a bisection. -/
theorem exists_leftHalf_superset
    {T : Finset X} {m : ℕ}
    (hT : T.card ≤ m) (hm : 2 * m = Fintype.card X) :
    ∃ B : Bisection X, T ⊆ B.left ∧ B.left.card = m := by
  classical
  have hmuniv : m ≤ (Finset.univ : Finset X).card := by
    rw [Finset.card_univ]
    omega
  rcases Finset.exists_subsuperset_card_eq
      (by intro x _; exact Finset.mem_univ x : T ⊆ (Finset.univ : Finset X))
      hT hmuniv with
    ⟨S, hTS, _hSuniv, hScard⟩
  refine ⟨ofLeftHalf S ?_, ?_, ?_⟩
  · rw [hScard, hm]
  · exact hTS
  · exact hScard

end Bisection

/-- A perfect matching across a chosen bisection, represented as a bijection
from the left side to the right side. -/
structure MatchingAcross {X : Type u} [Fintype X] [DecidableEq X]
    (B : Bisection X) where
  toEquiv : {x : X // x ∈ B.left} ≃ {x : X // x ∈ B.right}

namespace MatchingAcross

variable {X : Type u} [Fintype X] [DecidableEq X] {B : Bisection X}
variable (M : MatchingAcross B)

/-- The right endpoint matched to a left endpoint. -/
def rightEndpoint (x : {x : X // x ∈ B.left}) : X :=
  (M.toEquiv x).1

/-- The left endpoint matched to a right endpoint. -/
def leftEndpoint (y : {x : X // x ∈ B.right}) : X :=
  (M.toEquiv.symm y).1

@[simp]
theorem rightEndpoint_mem (x : {x : X // x ∈ B.left}) :
    M.rightEndpoint x ∈ B.right :=
  (M.toEquiv x).2

@[simp]
theorem leftEndpoint_mem (y : {x : X // x ∈ B.right}) :
    M.leftEndpoint y ∈ B.left :=
  (M.toEquiv.symm y).2

@[simp]
theorem leftEndpoint_rightEndpoint (x : {x : X // x ∈ B.left}) :
    M.leftEndpoint ⟨M.rightEndpoint x, M.rightEndpoint_mem x⟩ = x.1 := by
  simp [leftEndpoint, rightEndpoint]

@[simp]
theorem rightEndpoint_leftEndpoint (y : {x : X // x ∈ B.right}) :
    M.rightEndpoint ⟨M.leftEndpoint y, M.leftEndpoint_mem y⟩ = y.1 := by
  simp [leftEndpoint, rightEndpoint]

end MatchingAcross

/-- A finite collection of cut-matching rounds on a fixed vertex type.  The
index type is kept abstract so that it can be a `Fin r` when the round count is
known. -/
structure RoundFamily (X : Type u) [Fintype X] [DecidableEq X]
    (ι : Type v) where
  cut : ι → Bisection X
  matching : ∀ i : ι, MatchingAcross (cut i)

namespace RoundFamily

variable {X : Type u} [Fintype X] [DecidableEq X]
variable {ι : Type v} [Fintype ι]
variable (F : RoundFamily X ι)

/-- A matching player/responder for a fixed finite set of rounds: after the
cut player presents the bisection for round `i`, the responder supplies a
perfect matching across that bisection. -/
def Responder (X : Type u) [Fintype X] [DecidableEq X] (ι : Type v) : Type (max u v) :=
  ∀ _ : ι, (B : Bisection X) → MatchingAcross B

/-- Build a round family from the cut player's chosen bisections and a
matching responder. -/
def ofCutsAndResponder
    (cuts : ι → Bisection X) (responder : Responder X ι) :
    RoundFamily X ι where
  cut := cuts
  matching := fun i => responder i (cuts i)

/-- One matching edge in one round, oriented from the left side of that
round's bisection to the right side. -/
abbrev Edge : Type (max u v) :=
  Σ i : ι, {x : X // x ∈ (F.cut i).left}

/-- The source vertex of an oriented matching edge. -/
def edgeSource (e : F.Edge) : X :=
  e.2.1

/-- The target vertex of an oriented matching edge. -/
def edgeTarget (e : F.Edge) : X :=
  (F.matching e.1).rightEndpoint e.2

omit [Fintype ι] in
@[simp]
theorem edgeSource_mem_left (e : F.Edge) :
    F.edgeSource e ∈ (F.cut e.1).left :=
  e.2.2

omit [Fintype ι] in
@[simp]
theorem edgeTarget_mem_right (e : F.Edge) :
    F.edgeTarget e ∈ (F.cut e.1).right :=
  (F.matching e.1).rightEndpoint_mem e.2

omit [Fintype ι] in
theorem edgeSource_ne_edgeTarget (e : F.Edge) :
    F.edgeSource e ≠ F.edgeTarget e := by
  intro h
  have hleft : F.edgeTarget e ∈ (F.cut e.1).left := by
    rw [← h]
    exact F.edgeSource_mem_left e
  exact (F.cut e.1).not_mem_left_of_mem_right (F.edgeTarget_mem_right e) hleft

/-- An oriented matching edge crosses a set if exactly one of its endpoints is
in the set.  Since edges are counted by round and left endpoint, parallel
matching edges in different rounds remain distinct. -/
def edgeCrosses (S : Finset X) (e : F.Edge) : Prop :=
  (F.edgeSource e ∈ S ∧ F.edgeTarget e ∉ S) ∨
    (F.edgeTarget e ∈ S ∧ F.edgeSource e ∉ S)

instance edgeCrossesDecidable (S : Finset X) : DecidablePred (F.edgeCrosses S) := by
  intro e
  unfold edgeCrosses
  infer_instance

/-- The finite set of matching edges crossing a vertex set. -/
def edgeBoundary (S : Finset X) : Finset F.Edge :=
  Finset.univ.filter (F.edgeCrosses S)

@[simp]
theorem mem_edgeBoundary {S : Finset X} {e : F.Edge} :
    e ∈ F.edgeBoundary S ↔ F.edgeCrosses S e := by
  rw [edgeBoundary]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Half edge expansion for the union of all matching rounds: every set of
size at most half the vertices has at least half as many boundary edges. -/
def IsHalfEdgeExpander : Prop :=
  ∀ S : Finset X, 0 < S.card → 2 * S.card ≤ Fintype.card X →
    S.card ≤ 2 * (F.edgeBoundary S).card

/-- Reindex the rounds of a round family along an equivalence. -/
def reindex {κ : Type*} [Fintype κ] (e : κ ≃ ι)
    (F : RoundFamily X ι) : RoundFamily X κ where
  cut := fun k => F.cut (e k)
  matching := fun k => F.matching (e k)

/-- The edge instances of a reindexed round family are canonically equivalent
to the original edge instances. -/
def reindexEdgeEquiv {κ : Type*} [Fintype κ] (e : κ ≃ ι)
    (F : RoundFamily X ι) :
    (F.reindex e).Edge ≃ F.Edge where
  toFun a := ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, by
    simpa [reindex] using a.2⟩
  left_inv := by
    intro a
    cases a with
    | mk k x =>
        simp [reindex]
  right_inv := by
    intro a
    cases a with
    | mk i x =>
        simp [reindex]

omit [Fintype ι] in
@[simp]
theorem reindexEdgeEquiv_edgeSource {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (F : RoundFamily X ι)
    (a : (F.reindex e).Edge) :
    F.edgeSource (F.reindexEdgeEquiv e a) =
      (F.reindex e).edgeSource a := by
  rfl

omit [Fintype ι] in
@[simp]
theorem reindexEdgeEquiv_edgeTarget {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (F : RoundFamily X ι)
    (a : (F.reindex e).Edge) :
    F.edgeTarget (F.reindexEdgeEquiv e a) =
      (F.reindex e).edgeTarget a := by
  rfl

/-- Reindexing preserves the cardinality of every edge boundary. -/
theorem edgeBoundary_card_reindex {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (F : RoundFamily X ι) (S : Finset X) :
    ((F.reindex e).edgeBoundary S).card = (F.edgeBoundary S).card := by
  classical
  refine Finset.card_bij
    (fun a _ha => F.reindexEdgeEquiv e a)
    ?maps_to ?injective ?surjective
  · intro a ha
    rw [mem_edgeBoundary]
    rw [mem_edgeBoundary] at ha
    simpa [edgeCrosses] using ha
  · intro a _ha b _hb hab
    exact (F.reindexEdgeEquiv e).injective hab
  · intro a ha
    refine ⟨(F.reindexEdgeEquiv e).symm a, ?_, ?_⟩
    · rw [mem_edgeBoundary]
      rw [mem_edgeBoundary] at ha
      have hsource :
          (F.reindex e).edgeSource ((F.reindexEdgeEquiv e).symm a) =
            F.edgeSource a := by
        have h :=
          congrArg F.edgeSource ((F.reindexEdgeEquiv e).right_inv a)
        simpa only [reindexEdgeEquiv_edgeSource] using h
      have htarget :
          (F.reindex e).edgeTarget ((F.reindexEdgeEquiv e).symm a) =
            F.edgeTarget a := by
        have h :=
          congrArg F.edgeTarget ((F.reindexEdgeEquiv e).right_inv a)
        simpa only [reindexEdgeEquiv_edgeTarget] using h
      unfold edgeCrosses
      rw [hsource, htarget]
      exact ha
    · simp

/-- Reindexing preserves half-expansion. -/
theorem isHalfEdgeExpander_reindex_iff {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (F : RoundFamily X ι) :
    (F.reindex e).IsHalfEdgeExpander ↔ F.IsHalfEdgeExpander := by
  constructor
  · intro h S hS hhalf
    have h' := h S hS hhalf
    rwa [F.edgeBoundary_card_reindex e S] at h'
  · intro h S hS hhalf
    have h' := h S hS hhalf
    rwa [F.edgeBoundary_card_reindex e S]

/-- A more convenient boundary lower bound for singleton sets. -/
theorem edgeBoundary_nonempty_of_halfExpander (hF : F.IsHalfEdgeExpander)
    {S : Finset X} (hS : 0 < S.card) (hhalf : 2 * S.card ≤ Fintype.card X) :
    0 < (F.edgeBoundary S).card := by
  have hle : S.card ≤ 2 * (F.edgeBoundary S).card := hF S hS hhalf
  by_contra hzero
  have hcard : (F.edgeBoundary S).card = 0 := Nat.eq_zero_of_not_pos hzero
  omega

end RoundFamily

end CutMatchingGame
end SimpleGraph

end Lax17Proofs
