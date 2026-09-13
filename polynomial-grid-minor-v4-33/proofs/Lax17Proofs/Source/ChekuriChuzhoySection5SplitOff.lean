import Lax17Proofs.Source.ChekuriChuzhoySection5ElementConnectivity

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 split-off bookkeeping

This module formalizes the operation in Mader's split-off theorem as it is
used in the proof of Chekuri--Chuzhoy, journal Theorem 5.12 (preprint
Theorem 5.10).  A pair may consist of two parallel copies from the center to
the same other endpoint.  Splitting such a pair creates a loop; because the
project's named multigraph representation is loopless, that loop is explicitly
discarded.

`MaderAdmissible` is the exact preservation predicate: every local edge-cut
threshold between vertices other than the split center is unchanged.  This
file proves only finite bookkeeping and provenance facts.  It does not assume
or prove Mader's theorem asserting that an admissible pair exists.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-! ## Split pairs, including the loop case -/

/-- Two distinct named edge copies incident with `s`, with no requirement that
their other endpoints differ.  Equality of the other endpoints is precisely
the case in which splitting creates a loop. -/
structure MaderSplitPair (H : FiniteEdgeIndexedGraph W) (s : W) where
  first : H.Edge
  second : H.Edge
  edge_ne : first ≠ second
  firstOther : W
  secondOther : W
  first_ends :
    (H.left first = s ∧ H.right first = firstOther) ∨
      (H.right first = s ∧ H.left first = firstOther)
  second_ends :
    (H.left second = s ∧ H.right second = secondOther) ∨
      (H.right second = s ∧ H.left second = secondOther)

namespace MaderSplitPair

variable {H : FiniteEdgeIndexedGraph W} {s : W}

theorem firstOther_ne_center (p : H.MaderSplitPair s) : p.firstOther ≠ s := by
  rcases p.first_ends with h | h
  · intro hs
    exact H.end_ne p.first (h.1.trans (h.2.trans hs).symm)
  · intro hs
    exact H.end_ne p.first ((h.2.trans hs).trans h.1.symm)

theorem secondOther_ne_center (p : H.MaderSplitPair s) : p.secondOther ≠ s := by
  rcases p.second_ends with h | h
  · intro hs
    exact H.end_ne p.second (h.1.trans (h.2.trans hs).symm)
  · intro hs
    exact H.end_ne p.second ((h.2.trans hs).trans h.1.symm)

theorem first_mem_incidentEdges (p : H.MaderSplitPair s) :
    p.first ∈ H.incidentEdges s := by
  rw [H.mem_incidentEdges]
  rcases p.first_ends with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem second_mem_incidentEdges (p : H.MaderSplitPair s) :
    p.second ∈ H.incidentEdges s := by
  rw [H.mem_incidentEdges]
  rcases p.second_ends with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Forgetting the possible loop case gives the primitive loopless split pair. -/
def toSplitPair (p : H.MaderSplitPair s) (hother : p.firstOther ≠ p.secondOther) :
    H.SplitPair s where
  first := p.first
  second := p.second
  edge_ne := p.edge_ne
  firstOther := p.firstOther
  secondOther := p.secondOther
  first_ends := p.first_ends
  second_ends := p.second_ends
  other_ne := hother

end MaderSplitPair

/-- Split a general Mader pair.  Surviving old copies form the left summand.
The right summand has one inhabitant exactly when the new edge is not a loop.
Thus two copies with the same other endpoint are both removed and no loop is
stored. -/
def maderSplit (H : FiniteEdgeIndexedGraph W) {s : W} (p : H.MaderSplitPair s) :
    FiniteEdgeIndexedGraph W where
  Edge := {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
    {u : Unit // p.firstOther ≠ p.secondOther}
  left e := Sum.elim (fun f => H.left f.1) (fun _ => p.firstOther) e
  right e := Sum.elim (fun f => H.right f.1) (fun _ => p.secondOther) e
  end_ne e := by
    cases e with
    | inl f => exact H.end_ne f.1
    | inr h => exact h.2

@[simp] theorem maderSplit_old_left (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s)
    (e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    (H.maderSplit p).left (Sum.inl e) = H.left e.1 := rfl

@[simp] theorem maderSplit_old_right (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s)
    (e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    (H.maderSplit p).right (Sum.inl e) = H.right e.1 := rfl

@[simp] theorem maderSplit_new_left (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s)
    (u : {u : Unit // p.firstOther ≠ p.secondOther}) :
    (H.maderSplit p).left (Sum.inr u) = p.firstOther := rfl

@[simp] theorem maderSplit_new_right (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s)
    (u : {u : Unit // p.firstOther ≠ p.secondOther}) :
    (H.maderSplit p).right (Sum.inr u) = p.secondOther := rfl

theorem maderSplit_no_newEdge_of_other_eq (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) (hother : p.firstOther = p.secondOther) :
    IsEmpty {u : Unit // p.firstOther ≠ p.secondOther} := by
  constructor
  intro u
  exact u.2 hother

/-! ## Exact admissibility -/

/-- The named edge cuts between `x` and `y` all have size at least `k`.
Quantifying over thresholds avoids choosing a minimum cut while exactly
capturing finite local edge-connectivity. -/
def PairwiseEdgeConnectedAtLeast
    (H : FiniteEdgeIndexedGraph W) (x y : W) (k : Nat) : Prop :=
  ∀ X : Finset W, x ∈ X -> y ∉ X -> k <= (H.boundary X).card

theorem PairwiseEdgeConnectedAtLeast.mono
    {H : FiniteEdgeIndexedGraph W} {x y : W} {k l : Nat}
    (h : H.PairwiseEdgeConnectedAtLeast x y k) (hlk : l <= k) :
    H.PairwiseEdgeConnectedAtLeast x y l := by
  intro X hx hy
  exact hlk.trans (h X hx hy)

theorem pairwiseEdgeConnectedAtLeast_comm
    (H : FiniteEdgeIndexedGraph W) (x y : W) (k : Nat) :
    H.PairwiseEdgeConnectedAtLeast x y k ↔
      H.PairwiseEdgeConnectedAtLeast y x k := by
  constructor
  · intro h X hy hx
    have hcut := h Xᶜ (by simpa using hx) (by simpa using hy)
    simpa using hcut
  · intro h X hx hy
    have hcut := h Xᶜ (by simpa using hy) (by simpa using hx)
    simpa using hcut

/-- A split pair is Mader-admissible when splitting it preserves every local
edge-connectivity value between vertices other than the center.  Equality is
expressed by agreement at every natural cut threshold. -/
def MaderAdmissible (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) : Prop :=
  ∀ (x y : W), x ≠ s -> y ≠ s -> x ≠ y -> ∀ k : Nat,
    H.PairwiseEdgeConnectedAtLeast x y k ↔
      (H.maderSplit p).PairwiseEdgeConnectedAtLeast x y k

/-! ## Edge and degree bookkeeping -/

private theorem remainingEdges_card (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) :
    Fintype.card {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} =
      Fintype.card H.Edge - 2 := by
  classical
  rw [Fintype.card_subtype]
  have hfirst : p.first ∈ (Finset.univ : Finset H.Edge) := Finset.mem_univ _
  have hsecond : p.second ∈ (Finset.univ.erase p.first : Finset H.Edge) := by
    simp [p.edge_ne.symm]
  rw [show (Finset.univ.filter fun e : H.Edge => e ≠ p.first ∧ e ≠ p.second) =
      (Finset.univ.erase p.first).erase p.second by ext e; simp [and_comm]]
  rw [Finset.card_erase_of_mem hsecond, Finset.card_erase_of_mem hfirst,
    Finset.card_univ]
  omega

theorem maderSplit_edgeCard_of_other_ne (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) (hother : p.firstOther ≠ p.secondOther) :
    Fintype.card (H.maderSplit p).Edge = Fintype.card H.Edge - 1 := by
  classical
  change Fintype.card
      ({e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
        {u : Unit // p.firstOther ≠ p.secondOther}) = _
  rw [Fintype.card_sum, remainingEdges_card H p]
  have hone : Fintype.card {u : Unit // p.firstOther ≠ p.secondOther} = 1 := by
    simp [hother]
  rw [hone]
  have htwo : 2 <= Fintype.card H.Edge := by
    haveI : Nontrivial H.Edge := ⟨⟨p.first, p.second, p.edge_ne⟩⟩
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

theorem maderSplit_edgeCard_of_other_eq (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) (hother : p.firstOther = p.secondOther) :
    Fintype.card (H.maderSplit p).Edge = Fintype.card H.Edge - 2 := by
  classical
  change Fintype.card
      ({e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
        {u : Unit // p.firstOther ≠ p.secondOther}) = _
  rw [Fintype.card_sum, remainingEdges_card H p]
  have hzero : Fintype.card {u : Unit // p.firstOther ≠ p.secondOther} = 0 := by
    simp [hother]
  simp [hzero]

theorem maderSplit_edgeCard_lt (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) :
    Fintype.card (H.maderSplit p).Edge < Fintype.card H.Edge := by
  by_cases hother : p.firstOther = p.secondOther
  · rw [maderSplit_edgeCard_of_other_eq H p hother]
    have htwo : 2 <= Fintype.card H.Edge := by
      haveI : Nontrivial H.Edge := ⟨⟨p.first, p.second, p.edge_ne⟩⟩
      exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  · rw [maderSplit_edgeCard_of_other_ne H p hother]
    have hone : 1 <= Fintype.card H.Edge :=
      Fintype.card_pos_iff.mpr ⟨p.first⟩
    omega

private def centerIncidentEquiv (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) :
    (H.maderSplit p).incidentEdges s ≃
      ↥((H.incidentEdges s).erase p.first |>.erase p.second) where
  toFun e := by
    obtain ⟨value, hvalue⟩ := e
    rcases value with old | new
    · refine ⟨old.1, ?_⟩
      have hold : old.1 ∈ H.incidentEdges s := by
        rw [H.mem_incidentEdges]
        simpa only [maderSplit_old_left, maderSplit_old_right] using
          ((H.maderSplit p).mem_incidentEdges s (Sum.inl old)).mp hvalue
      simpa [old.2.1, old.2.2] using hold
    · have hinc := ((H.maderSplit p).mem_incidentEdges s (Sum.inr new)).mp hvalue
      simp only [maderSplit_new_left, maderSplit_new_right] at hinc
      exact (hinc.elim p.firstOther_ne_center p.secondOther_ne_center).elim
  invFun e := by
    have he : e.1 ≠ p.first ∧ e.1 ≠ p.second := by
      have hneSecond : e.1 ≠ p.second := Finset.ne_of_mem_erase e.2
      have hmemFirstErase : e.1 ∈ (H.incidentEdges s).erase p.first :=
        Finset.mem_of_mem_erase e.2
      have hneFirst : e.1 ≠ p.first := Finset.ne_of_mem_erase hmemFirstErase
      exact ⟨hneFirst, hneSecond⟩
    refine ⟨Sum.inl ⟨e.1, he⟩, ?_⟩
    rw [(H.maderSplit p).mem_incidentEdges]
    simpa only [maderSplit_old_left, maderSplit_old_right] using
      (H.mem_incidentEdges s e.1).mp
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase e.2))
  left_inv := by
    intro e
    obtain ⟨value, hvalue⟩ := e
    rcases value with old | new
    · rfl
    · have hinc := ((H.maderSplit p).mem_incidentEdges s (Sum.inr new)).mp hvalue
      simp only [maderSplit_new_left, maderSplit_new_right] at hinc
      exact (hinc.elim p.firstOther_ne_center p.secondOther_ne_center).elim
  right_inv := by
    intro e
    rfl

theorem maderSplit_degree_center (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) :
    (H.maderSplit p).degree s = H.degree s - 2 := by
  classical
  unfold degree
  rw [← Fintype.card_coe, Fintype.card_congr (centerIncidentEquiv H p),
    Fintype.card_coe]
  have hfirst := p.first_mem_incidentEdges
  have hsecond : p.second ∈ (H.incidentEdges s).erase p.first := by
    simp [p.second_mem_incidentEdges, p.edge_ne.symm]
  rw [Finset.card_erase_of_mem hsecond, Finset.card_erase_of_mem hfirst]
  omega

theorem maderSplit_degree_le (H : FiniteEdgeIndexedGraph W) {s : W}
    (p : H.MaderSplitPair s) (w : W) :
    (H.maderSplit p).degree w <= H.degree w := by
  classical
  let f : (H.maderSplit p).incidentEdges w -> H.incidentEdges w := fun e => by
    obtain ⟨value, hvalue⟩ := e
    rcases value with old | new
    · refine ⟨old.1, ?_⟩
      rw [H.mem_incidentEdges]
      simpa only [maderSplit_old_left, maderSplit_old_right] using
        ((H.maderSplit p).mem_incidentEdges w (Sum.inl old)).mp hvalue
    · by_cases hw : w = p.firstOther
      · refine ⟨p.first, ?_⟩
        rw [H.mem_incidentEdges]
        rcases p.first_ends with h | h
        · exact Or.inr (h.2.trans hw.symm)
        · exact Or.inl (h.2.trans hw.symm)
      · refine ⟨p.second, ?_⟩
        have hinc := ((H.maderSplit p).mem_incidentEdges w (Sum.inr new)).mp hvalue
        simp only [maderSplit_new_left, maderSplit_new_right] at hinc
        have hsecond : p.secondOther = w := hinc.resolve_left (by
          intro hfirst
          exact hw hfirst.symm)
        rw [H.mem_incidentEdges]
        rcases p.second_ends with h | h
        · exact Or.inr (h.2.trans hsecond)
        · exact Or.inl (h.2.trans hsecond)
  have hf : Function.Injective f := by
    intro e e' heq
    obtain ⟨value, hvalue⟩ := e
    obtain ⟨value', hvalue'⟩ := e'
    rcases value with old | new <;> rcases value' with old' | new'
    · dsimp only [f] at heq
      have hold : old.1 = old'.1 :=
        congrArg (fun z : H.incidentEdges w => z.1) heq
      have holdeq : old = old' := Subtype.ext hold
      subst old'
      rfl
    · dsimp only [f] at heq
      split at heq
      · exact (old.2.1 (congrArg Subtype.val heq)).elim
      · exact (old.2.2 (congrArg Subtype.val heq)).elim
    · dsimp only [f] at heq
      split at heq
      · exact (old'.2.1 (congrArg Subtype.val heq.symm)).elim
      · exact (old'.2.2 (congrArg Subtype.val heq.symm)).elim
    · have hnew : new = new' := Subtype.ext (Subsingleton.elim new.1 new'.1)
      subst new'
      rfl
  unfold degree
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective f hf

/-! ## Provenance composition and walk lifting -/

/-- Compose any edge provenance through one split.  A surviving edge keeps its
old provenance.  The new edge, when present, is represented by the first
provenance followed by the second.  In the loop case the new-edge branch is
uninhabited. -/
def MaderSplitPair.composeProvenance {A : Type v} {H : FiniteEdgeIndexedGraph W}
    {s : W} (p : H.MaderSplitPair s) (origin : H.Edge -> List A) :
    (H.maderSplit p).Edge -> List A
  | Sum.inl e => origin e.1
  | Sum.inr _ => origin p.first ++ origin p.second

@[simp] theorem MaderSplitPair.composeProvenance_old {A : Type v}
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    (origin : H.Edge -> List A)
    (e : {e : H.Edge // e ≠ p.first ∧ e ≠ p.second}) :
    p.composeProvenance origin (Sum.inl e) = origin e.1 := rfl

@[simp] theorem MaderSplitPair.composeProvenance_new {A : Type v}
    {H : FiniteEdgeIndexedGraph W} {s : W} (p : H.MaderSplitPair s)
    (origin : H.Edge -> List A)
    (u : {u : Unit // p.firstOther ≠ p.secondOther}) :
    p.composeProvenance origin (Sum.inr u) =
      origin p.first ++ origin p.second := rfl

/-- One result edge lifted to a named-edge walk in the graph before splitting. -/
def MaderSplitPair.liftEdge {H : FiniteEdgeIndexedGraph W} {s x y : W}
    (p : H.MaderSplitPair s) (e : (H.maderSplit p).Edge)
    (he : (H.maderSplit p).Joins e x y) : H.NamedEdgeWalk x y := by
  rcases e with old | new
  · exact .cons old.1 (by simpa [Joins] using he) (.nil y)
  · have he' :
        (p.firstOther = x ∧ p.secondOther = y) ∨
          (p.secondOther = x ∧ p.firstOther = y) := by
      simpa [Joins] using he
    by_cases hx : p.firstOther = x
    · have hxy : p.firstOther = x ∧ p.secondOther = y := by
        rcases he' with h | h
        · exact h
        · exact (new.2 (hx.trans h.1.symm)).elim
      rw [← hxy.1, ← hxy.2]
      have hfirst : H.Joins p.first p.firstOther s := by
        rcases p.first_ends with h | h <;> simp_all [Joins]
      have hsecond : H.Joins p.second s p.secondOther := by
        rcases p.second_ends with h | h <;> simp_all [Joins]
      exact .cons (y := s) p.first hfirst
        (.cons (y := p.secondOther) p.second hsecond (.nil p.secondOther))
    · have hxy : p.secondOther = x ∧ p.firstOther = y := by
        rcases he' with h | h
        · exact (hx h.1).elim
        · exact h
      rw [← hxy.1, ← hxy.2]
      have hsecond : H.Joins p.second p.secondOther s := by
        rcases p.second_ends with h | h <;> simp_all [Joins]
      have hfirst : H.Joins p.first s p.firstOther := by
        rcases p.first_ends with h | h <;> simp_all [Joins]
      exact .cons (y := s) p.second hsecond
        (.cons (y := p.firstOther) p.first hfirst (.nil p.firstOther))

/-- Replace every edge of a post-split walk by its one- or two-edge original
walk. -/
def MaderSplitPair.liftWalk {H : FiniteEdgeIndexedGraph W} {s x y : W}
    (p : H.MaderSplitPair s) :
    (H.maderSplit p).NamedEdgeWalk x y -> H.NamedEdgeWalk x y
  | .nil x => .nil x
  | .cons e he tail => (p.liftEdge e he).append (p.liftWalk tail)

/-- The relation between a post-split edge and each original edge contributing
to it. -/
def MaderSplitPair.EdgeOrigin {H : FiniteEdgeIndexedGraph W} {s : W}
    (p : H.MaderSplitPair s) (e : (H.maderSplit p).Edge) (f : H.Edge) : Prop :=
  match e with
  | Sum.inl old => f = old.1
  | Sum.inr _ => f = p.first ∨ f = p.second

theorem MaderSplitPair.liftEdge_provenance
    {H : FiniteEdgeIndexedGraph W} {s x y : W} (p : H.MaderSplitPair s)
    (e : (H.maderSplit p).Edge) (he : (H.maderSplit p).Joins e x y)
    {f : H.Edge} (hf : f ∈ (p.liftEdge e he).edgeList) :
    p.EdgeOrigin e f := by
  rcases e with old | new
  · simp [MaderSplitPair.liftEdge] at hf
    exact hf
  · have he' :
        (p.firstOther = x ∧ p.secondOther = y) ∨
          (p.secondOther = x ∧ p.firstOther = y) := by
      simpa [Joins] using he
    by_cases hx : p.firstOther = x
    · have hxy : p.firstOther = x ∧ p.secondOther = y := by
        rcases he' with h | h
        · exact h
        · exact (new.2 (hx.trans h.1.symm)).elim
      rcases hxy with ⟨rfl, rfl⟩
      simp [MaderSplitPair.liftEdge] at hf
      exact hf
    · have hxy : p.secondOther = x ∧ p.firstOther = y := by
        rcases he' with h | h
        · exact (hx h.1).elim
        · exact h
      rcases hxy with ⟨rfl, rfl⟩
      simp [MaderSplitPair.liftEdge, new.2] at hf
      exact hf.symm

theorem MaderSplitPair.liftWalk_provenance
    {H : FiniteEdgeIndexedGraph W} {s x y : W} (p : H.MaderSplitPair s)
    (P : (H.maderSplit p).NamedEdgeWalk x y) {f : H.Edge}
    (hf : f ∈ (p.liftWalk P).edgeList) :
    ∃ e ∈ P.edgeList, p.EdgeOrigin e f := by
  induction P with
  | nil => simp [MaderSplitPair.liftWalk] at hf
  | cons e he tail ih =>
      simp only [MaderSplitPair.liftWalk, NamedEdgeWalk.edgeList_append,
        List.mem_append] at hf
      rcases hf with hf | hf
      · exact ⟨e, by simp, p.liftEdge_provenance e he hf⟩
      · rcases ih hf with ⟨g, hg, hgf⟩
        exact ⟨g, by simp [hg], hgf⟩

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
