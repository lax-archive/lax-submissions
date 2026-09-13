import Lax17Proofs.Source.EdgeMenger
import Lax17Proofs.Source.Flow
import Lax17Proofs.Source.Section46Flow

namespace Lax17Proofs

universe u v w

/-!
# Integral realization of denominator-scaled well-linked flows

Chekuri--Chuzhoy Section 5 uses truncated scaled bandwidth only with numerator
one.  In that specialization, denominator `D` is an integral edge-capacity.
This file replaces every original edge by `D` two-edge channels and attaches
one private leaf to each source and target terminal.  Finite edge-Menger then
produces a full routing, and projection of the channel paths gives a rational
unit path flow in the original graph with edge congestion at most `D`.
-/

namespace SimpleGraph
namespace ScaledWellLinkedPathFlow


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

namespace CapacityExpansion

/-- Vertices of the integral edge-capacity expansion. -/
abbrev Node
    (G : _root_.SimpleGraph V) (S T : Finset V) (D : Nat) :=
  V ⊕
    ({v : V // v ∈ S} ⊕
      ({v : V // v ∈ T} ⊕
        ({e : Sym2 V // e ∈ G.edgeSet} × Fin D)))

noncomputable instance nodeDecidableEq
    (S T : Finset V) (D : Nat) :
    DecidableEq (Node G S T D) :=
  Classical.decEq _

def original {S T : Finset V} {D : Nat} (v : V) :
    Node G S T D :=
  Sum.inl v

def source {S T : Finset V} {D : Nat} (v : {v : V // v ∈ S}) :
    Node G S T D :=
  Sum.inr (Sum.inl v)

def target {S T : Finset V} {D : Nat} (v : {v : V // v ∈ T}) :
    Node G S T D :=
  Sum.inr (Sum.inr (Sum.inl v))

def channel {S T : Finset V} {D : Nat}
    (e : {e : Sym2 V // e ∈ G.edgeSet}) (i : Fin D) :
    Node G S T D :=
  Sum.inr (Sum.inr (Sum.inr (e, i)))

/-- Adjacency in the capacity expansion.  Terminal leaves have their unique
incidence, while a channel vertex is incident with the two endpoints of its
underlying original edge. -/
inductive Adj {S T : Finset V} {D : Nat} :
    Node G S T D → Node G S T D → Prop
  | sourceEdge (v : {v : V // v ∈ S}) :
      Adj (source v) (original v.1)
  | sourceEdgeSymm (v : {v : V // v ∈ S}) :
      Adj (original v.1) (source v)
  | targetEdge (v : {v : V // v ∈ T}) :
      Adj (original v.1) (target v)
  | targetEdgeSymm (v : {v : V // v ∈ T}) :
      Adj (target v) (original v.1)
  | channelEdge (e : {e : Sym2 V // e ∈ G.edgeSet}) (i : Fin D)
      (v : V) (hv : v ∈ e.1) :
      Adj (original v) (channel e i)
  | channelEdgeSymm (e : {e : Sym2 V // e ∈ G.edgeSet}) (i : Fin D)
      (v : V) (hv : v ∈ e.1) :
      Adj (channel e i) (original v)

/-- The finite simple graph realizing integral capacity `D` on every edge. -/
def graph (G : _root_.SimpleGraph V) (S T : Finset V) (D : Nat) :
    _root_.SimpleGraph (Node G S T D) where
  Adj := Adj
  symm := by
    intro x y h
    cases h with
    | sourceEdge v => exact Adj.sourceEdgeSymm v
    | sourceEdgeSymm v => exact Adj.sourceEdge v
    | targetEdge v => exact Adj.targetEdgeSymm v
    | targetEdgeSymm v => exact Adj.targetEdge v
    | channelEdge e i v hv => exact Adj.channelEdgeSymm e i v hv
    | channelEdgeSymm e i v hv => exact Adj.channelEdge e i v hv
  loopless := by
    constructor
    intro x h
    cases h <;> simp_all [source, target, original, channel]

/-- Private source leaves of the expansion. -/
noncomputable def sourceLeaves
    [DecidableRel G.Adj] (S T : Finset V) (D : Nat) :
    Finset (Node G S T D) := by
  classical
  exact Finset.univ.image source

/-- Private target leaves of the expansion. -/
noncomputable def targetLeaves
    [DecidableRel G.Adj] (S T : Finset V) (D : Nat) :
    Finset (Node G S T D) := by
  classical
  exact Finset.univ.image target

@[simp] theorem mem_sourceLeaves [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} (v : {v : V // v ∈ S}) :
    source v ∈ sourceLeaves (G := G) S T D := by
  classical
  simp [sourceLeaves]

@[simp] theorem mem_targetLeaves [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} (v : {v : V // v ∈ T}) :
    target v ∈ targetLeaves (G := G) S T D := by
  classical
  simp [targetLeaves]

theorem sourceLeaves_disjoint_targetLeaves [DecidableRel G.Adj]
    (S T : Finset V) (D : Nat) :
    Disjoint (sourceLeaves (G := G) S T D)
      (targetLeaves (G := G) S T D) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxS hxT
  rcases Finset.mem_image.mp hxS with ⟨s, _hs, rfl⟩
  rcases Finset.mem_image.mp hxT with ⟨t, _ht, h⟩
  cases h

@[simp] theorem sourceLeaves_card [DecidableRel G.Adj]
    (S T : Finset V) (D : Nat) :
    (sourceLeaves (G := G) S T D).card = S.card := by
  classical
  rw [sourceLeaves, Finset.card_image_of_injective]
  · simp
  · intro x y h
    simpa only [source, Sum.inr.injEq, Sum.inl.injEq] using h

@[simp] theorem targetLeaves_card [DecidableRel G.Adj]
    (S T : Finset V) (D : Nat) :
    (targetLeaves (G := G) S T D).card = T.card := by
  classical
  rw [targetLeaves, Finset.card_image_of_injective]
  · simp
  · intro x y h
    simpa only [target, Sum.inr.injEq, Sum.inl.injEq] using h

/-! ## Capacity-expansion cuts -/

/-- Original vertices whose copies lie on the left side of an expansion cut. -/
noncomputable def originalSide [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (X : Finset (Node G S T D)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => original (G := G) (S := S) (T := T) (D := D) v ∈ X

@[simp] theorem mem_originalSide_iff [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (X : Finset (Node G S T D)) (v : V) :
    v ∈ originalSide (G := G) X ↔
      original (G := G) (S := S) (T := T) (D := D) v ∈ X := by
  classical
  simp [originalSide]

/-- A source, channel, or target contribution to the natural lower bound on an
expansion cut. -/
abbrev CutChargeIndex [DecidableRel G.Adj]
    (S T A B : Finset V) (D : Nat) :=
  {v : V // v ∈ S \ A} ⊕
    (({e : Sym2 V // e ∈ Section44.edgeBoundary G A B} × Fin D) ⊕
      {v : V // v ∈ T ∩ A})

/-- Checked endpoints of an original boundary edge. -/
noncomputable def boundaryEndpoints [DecidableRel G.Adj]
    {A B : Finset V}
    (e : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B}) :
    {p : V × V // p.1 ∈ A ∧ p.2 ∈ B ∧ e.1 = s(p.1, p.2)} := by
  classical
  have hex :
      ∃ p : V × V, p.1 ∈ A ∧ p.2 ∈ B ∧ e.1 = s(p.1, p.2) := by
    have h := (Section44.mem_edgeBoundary (G := G) A B e.1).1 e.2
    exact Exists.elim h.2 fun x hx =>
      Exists.elim hx.2 fun y hy =>
        ⟨(x, y), hx.1, hy.1, hy.2⟩
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

noncomputable def boundaryLeft [DecidableRel G.Adj]
    {A B : Finset V}
    (e : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B}) : V :=
  (boundaryEndpoints (G := G) e).1.1

noncomputable def boundaryRight [DecidableRel G.Adj]
    {A B : Finset V}
    (e : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B}) : V :=
  (boundaryEndpoints (G := G) e).1.2

theorem boundaryLeft_mem [DecidableRel G.Adj]
    {A B : Finset V}
    (e : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B}) :
    boundaryLeft (G := G) e ∈ A :=
  (boundaryEndpoints (G := G) e).2.1

theorem boundaryRight_mem [DecidableRel G.Adj]
    {A B : Finset V}
    (e : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B}) :
    boundaryRight (G := G) e ∈ B :=
  (boundaryEndpoints (G := G) e).2.2.1

theorem boundary_eq [DecidableRel G.Adj]
    {A B : Finset V}
    (e : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B}) :
    e.1 = s(boundaryLeft (G := G) e, boundaryRight (G := G) e) :=
  (boundaryEndpoints (G := G) e).2.2.2

noncomputable def boundaryOriginalEdge [DecidableRel G.Adj]
    {A B : Finset V}
    (e : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B}) :
    {f : Sym2 V // f ∈ G.edgeSet} := by
  classical
  exact ⟨e.1, (Section44.mem_edgeBoundary (G := G) A B e.1).1 e.2 |>.1⟩

/-- The concrete expansion edge charged by one term of the cut lower bound. -/
noncomputable def cutCharge [DecidableRel G.Adj]
    {S T A B : Finset V} {D : Nat}
    (X : Finset (Node G S T D)) :
    CutChargeIndex (G := G) S T A B D → Sym2 (Node G S T D) := by
  classical
  intro z
  cases z with
  | inl v =>
      exact
        s(source (G := G) (T := T) (D := D)
            ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩,
          original (G := G) (S := S) (T := T) (D := D) v.1)
  | inr w =>
      cases w with
      | inl ei =>
          let e := ei.1
          let i := ei.2
          let f := boundaryOriginalEdge (G := G) e
          let c := channel (S := S) (T := T) f i
          exact if c ∈ X then
            s(c, original (G := G) (S := S) (T := T) (D := D)
              (boundaryRight (G := G) e))
          else
            s(original (G := G) (S := S) (T := T) (D := D)
              (boundaryLeft (G := G) e), c)
      | inr v =>
          exact
            s(original (G := G) (S := S) (T := T) (D := D) v.1,
              target (G := G) (S := S) (D := D)
                ⟨v.1, (Finset.mem_inter.mp v.2).1⟩)

@[simp] theorem cutCharge_source [DecidableRel G.Adj]
    {S T A B : Finset V} {D : Nat}
    (X : Finset (Node G S T D)) (v : {v : V // v ∈ S \ A}) :
    cutCharge (G := G) (T := T) (B := B) X (Sum.inl v) =
      s(source (G := G) (T := T) (D := D)
          ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩,
        original (G := G) (S := S) (T := T) (D := D) v.1) :=
  rfl

@[simp] theorem cutCharge_channel [DecidableRel G.Adj]
    {S T A B : Finset V} {D : Nat}
    (X : Finset (Node G S T D))
    (ei : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B} × Fin D) :
    cutCharge (G := G) (S := S) (T := T) X (Sum.inr (Sum.inl ei)) =
      if channel (S := S) (T := T) (boundaryOriginalEdge (G := G) ei.1) ei.2 ∈ X
      then
        s(channel (S := S) (T := T) (boundaryOriginalEdge (G := G) ei.1) ei.2,
          original (G := G) (S := S) (T := T) (D := D)
            (boundaryRight (G := G) ei.1))
      else
        s(original (G := G) (S := S) (T := T) (D := D)
            (boundaryLeft (G := G) ei.1),
          channel (S := S) (T := T)
            (boundaryOriginalEdge (G := G) ei.1) ei.2) :=
  rfl

@[simp] theorem cutCharge_target [DecidableRel G.Adj]
    {S T A B : Finset V} {D : Nat}
    (X : Finset (Node G S T D)) (v : {v : V // v ∈ T ∩ A}) :
    cutCharge (G := G) (S := S) (B := B) X (Sum.inr (Sum.inr v)) =
      s(original (G := G) (S := S) (T := T) (D := D) v.1,
        target (G := G) (S := S) (D := D)
          ⟨v.1, (Finset.mem_inter.mp v.2).1⟩) :=
  rfl

private theorem channelNode_injective [DecidableRel G.Adj]
    {S T A B : Finset V} {D : Nat} :
    Function.Injective
      (fun ei : {e : Sym2 V // e ∈ Section44.edgeBoundary G A B} × Fin D =>
        channel (S := S) (T := T)
          (boundaryOriginalEdge (G := G) ei.1) ei.2) := by
  intro a b hab
  have hp :
      (boundaryOriginalEdge (G := G) a.1, a.2) =
        (boundaryOriginalEdge (G := G) b.1, b.2) := by
    simpa only [channel, Sum.inr.injEq] using hab
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun p => p.1.1) hp
  · exact congrArg
      (fun p : {f : Sym2 V // f ∈ G.edgeSet} × Fin D => p.2) hp

private theorem mem_right_of_cover_of_not_left
    {W : Type*} [Fintype W] [DecidableEq W] {X Y : Finset W}
    (hcover : X ∪ Y = Finset.univ) {z : W} (hz : z ∉ X) :
    z ∈ Y := by
  have hmem : z ∈ X ∪ Y := by
    rw [hcover]
    exact Finset.mem_univ z
  exact (Finset.mem_union.mp hmem).resolve_left hz

/-- Every charged edge really crosses the supplied expansion cut. -/
theorem cutCharge_mem_boundary [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    {X Y : Finset (Node G S T D)}
    (hcover : X ∪ Y = Finset.univ)
    (hsource : sourceLeaves (G := G) S T D ⊆ X)
    (htarget : targetLeaves (G := G) S T D ⊆ Y)
    (z : CutChargeIndex (G := G) S T
      (originalSide (G := G) X)
      (Finset.univ \ originalSide (G := G) X) D) :
    cutCharge (G := G) X z ∈
      Section44.edgeBoundary (graph G S T D) X Y := by
  classical
  let A := originalSide (G := G) X
  let B := Finset.univ \ A
  cases z with
  | inl v =>
      let sv : {v : V // v ∈ S} :=
        ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩
      have hsvX : source (G := G) (T := T) (D := D) sv ∈ X :=
        hsource (mem_sourceLeaves (G := G) sv)
      have hvNotX :
          original (G := G) (S := S) (T := T) (D := D) v.1 ∉ X := by
        simpa [A] using (Finset.mem_sdiff.mp v.2).2
      have hvY :
          original (G := G) (S := S) (T := T) (D := D) v.1 ∈ Y :=
        mem_right_of_cover_of_not_left hcover hvNotX
      exact (Section44.mem_edgeBoundary
        (G := graph G S T D) X Y _).2
        ⟨by
          change
            (graph G S T D).Adj
              (source (G := G) (T := T) (D := D) sv)
              (original (G := G) (S := S) (T := T) (D := D) v.1)
          exact Adj.sourceEdge sv,
        _, hsvX, _, hvY, rfl⟩
  | inr w =>
      cases w with
      | inl ei =>
          let e := ei.1
          let i := ei.2
          let f := boundaryOriginalEdge (G := G) e
          let c := channel (S := S) (T := T) f i
          have hleftX :
              original (G := G) (S := S) (T := T) (D := D)
                (boundaryLeft (G := G) e) ∈ X := by
            rw [← mem_originalSide_iff (G := G)]
            exact boundaryLeft_mem (G := G) e
          have hrightNotX :
              original (G := G) (S := S) (T := T) (D := D)
                (boundaryRight (G := G) e) ∉ X := by
            rw [← mem_originalSide_iff (G := G)]
            exact (Finset.mem_sdiff.mp (boundaryRight_mem (G := G) e)).2
          have hrightY :
              original (G := G) (S := S) (T := T) (D := D)
                (boundaryRight (G := G) e) ∈ Y :=
            mem_right_of_cover_of_not_left hcover hrightNotX
          by_cases hcX : c ∈ X
          · exact (Section44.mem_edgeBoundary
              (G := graph G S T D) X Y _).2
              ⟨by
                simp [cutCharge, e, i, f, c, hcX]
                apply Adj.channelEdgeSymm
                change boundaryRight (G := G) e ∈ e.1
                rw [boundary_eq (G := G) e]
                simp,
              _, hcX, _, hrightY, by simp [cutCharge, e, i, f, c, hcX]⟩
          · have hcY : c ∈ Y :=
              mem_right_of_cover_of_not_left hcover hcX
            exact (Section44.mem_edgeBoundary
              (G := graph G S T D) X Y _).2
              ⟨by
                simp [cutCharge, e, i, f, c, hcX]
                apply Adj.channelEdge
                change boundaryLeft (G := G) e ∈ e.1
                rw [boundary_eq (G := G) e]
                simp,
              _, hleftX, _, hcY, by simp [cutCharge, e, i, f, c, hcX]⟩
      | inr v =>
          let tv : {v : V // v ∈ T} :=
            ⟨v.1, (Finset.mem_inter.mp v.2).1⟩
          have hvX :
              original (G := G) (S := S) (T := T) (D := D) v.1 ∈ X := by
            rw [← mem_originalSide_iff (G := G)]
            exact (Finset.mem_inter.mp v.2).2
          have htvY : target (G := G) (S := S) (D := D) tv ∈ Y :=
            htarget (mem_targetLeaves (G := G) tv)
          exact (Section44.mem_edgeBoundary
            (G := graph G S T D) X Y _).2
            ⟨by
              change
                (graph G S T D).Adj
                  (original (G := G) (S := S) (T := T) (D := D) v.1)
                  (target (G := G) (S := S) (D := D) tv)
              exact Adj.targetEdge tv,
            _, hvX, _, htvY, rfl⟩

/-- Different terms in the natural cut lower bound charge different expansion
edges. -/
theorem cutCharge_injective [DecidableRel G.Adj]
    {S T A B : Finset V} {D : Nat}
    (X : Finset (Node G S T D)) :
    Function.Injective
      (cutCharge (G := G) (S := S) (T := T) (A := A) (B := B) X) := by
  classical
  intro a b hab
  rcases a with a | a
  · rcases b with b | b
    · rw [cutCharge_source, cutCharge_source, Sym2.eq_iff] at hab
      rcases hab with hab | hab
      · have hv : a.1 = b.1 := by
          simpa only [original, Sum.inl.injEq] using hab.2
        have : a = b := Subtype.ext hv
        subst b
        rfl
      · simp [source, original] at hab
    · rcases b with b | b
      · rw [cutCharge_source, cutCharge_channel] at hab
        by_cases hb :
            channel (S := S) (T := T)
              (boundaryOriginalEdge (G := G) b.1) b.2 ∈ X
        · rw [if_pos hb, Sym2.eq_iff] at hab
          simp [source, channel, original] at hab
        · rw [if_neg hb, Sym2.eq_iff] at hab
          simp [source, channel, original] at hab
      · rw [cutCharge_source, cutCharge_target, Sym2.eq_iff] at hab
        simp [source, target, original] at hab
  · rcases a with a | a
    · rcases b with b | b
      · rw [cutCharge_channel, cutCharge_source] at hab
        by_cases ha :
            channel (S := S) (T := T)
              (boundaryOriginalEdge (G := G) a.1) a.2 ∈ X
        · rw [if_pos ha, Sym2.eq_iff] at hab
          simp [source, channel, original] at hab
        · rw [if_neg ha, Sym2.eq_iff] at hab
          simp [source, channel, original] at hab
      · rcases b with b | b
        · rw [cutCharge_channel, cutCharge_channel] at hab
          by_cases ha :
              channel (S := S) (T := T)
                (boundaryOriginalEdge (G := G) a.1) a.2 ∈ X
          <;> by_cases hb :
              channel (S := S) (T := T)
                (boundaryOriginalEdge (G := G) b.1) b.2 ∈ X
          · rw [if_pos ha, if_pos hb, Sym2.eq_iff] at hab
            rcases hab with hab | hab
            · have : a = b := channelNode_injective hab.1
              subst b
              rfl
            · simp [channel, original] at hab
          · rw [if_pos ha, if_neg hb, Sym2.eq_iff] at hab
            rcases hab with hab | hab
            · simp [channel, original] at hab
            · have : a = b := channelNode_injective hab.1
              subst b
              rfl
          · rw [if_neg ha, if_pos hb, Sym2.eq_iff] at hab
            rcases hab with hab | hab
            · simp [channel, original] at hab
            · have : a = b := channelNode_injective hab.2
              subst b
              rfl
          · rw [if_neg ha, if_neg hb, Sym2.eq_iff] at hab
            rcases hab with hab | hab
            · have : a = b := channelNode_injective hab.2
              subst b
              rfl
            · simp [channel, original] at hab
        · rw [cutCharge_channel, cutCharge_target] at hab
          by_cases ha :
              channel (S := S) (T := T)
                (boundaryOriginalEdge (G := G) a.1) a.2 ∈ X
          · rw [if_pos ha, Sym2.eq_iff] at hab
            simp [channel, target, original] at hab
          · rw [if_neg ha, Sym2.eq_iff] at hab
            simp [channel, target, original] at hab
    · rcases b with b | b
      · rw [cutCharge_target, cutCharge_source, Sym2.eq_iff] at hab
        simp [source, target, original] at hab
      · rcases b with b | b
        · rw [cutCharge_target, cutCharge_channel] at hab
          by_cases hb :
              channel (S := S) (T := T)
                (boundaryOriginalEdge (G := G) b.1) b.2 ∈ X
          · rw [if_pos hb, Sym2.eq_iff] at hab
            simp [channel, target, original] at hab
          · rw [if_neg hb, Sym2.eq_iff] at hab
            simp [channel, target, original] at hab
        · rw [cutCharge_target, cutCharge_target, Sym2.eq_iff] at hab
          rcases hab with hab | hab
          · have hv : a.1 = b.1 := by
              simpa only [original, Sum.inl.injEq] using hab.1
            have : a = b := Subtype.ext hv
            subst b
            rfl
          · simp [target, original] at hab

/-- The source deficits, all `D` copies of each original boundary edge, and
the target deficits inject into the expansion cut boundary. -/
theorem cut_lower_bound [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    {X Y : Finset (Node G S T D)}
    (hcover : X ∪ Y = Finset.univ)
    (hsource : sourceLeaves (G := G) S T D ⊆ X)
    (htarget : targetLeaves (G := G) S T D ⊆ Y) :
    (S \ originalSide (G := G) X).card +
        D * (Section44.edgeBoundary G
          (originalSide (G := G) X)
          (Finset.univ \ originalSide (G := G) X)).card +
        (T ∩ originalSide (G := G) X).card ≤
      (Section44.edgeBoundary (graph G S T D) X Y).card := by
  classical
  let I := CutChargeIndex (G := G) S T
    (originalSide (G := G) X)
    (Finset.univ \ originalSide (G := G) X) D
  let charge : I →
      {e : Sym2 (Node G S T D) //
        e ∈ Section44.edgeBoundary (graph G S T D) X Y} :=
    fun z => ⟨cutCharge (G := G) X z,
      cutCharge_mem_boundary (G := G) hcover hsource htarget z⟩
  have hinjective : Function.Injective charge := by
    intro a b hab
    apply cutCharge_injective (G := G) X
    exact congrArg Subtype.val hab
  have hcard := Fintype.card_le_of_injective charge hinjective
  simpa only [I, CutChargeIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_fin, Nat.mul_comm, Nat.add_assoc] using hcard

/-- Integral edge-Menger realizes a full routing in the capacity expansion
when the original terminal set is scaled edge-well-linked with numerator one.
-/
theorem exists_full_pathPacking [DecidableRel G.Adj]
    {Terminals S T : Finset V} {D : Nat}
    (hwell : ScaledEdgeWellLinked G Terminals 1 D)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) :
    ∃ P : EdgePathPacking (graph G S T D)
        (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D),
      P.card = S.card := by
  classical
  have hpaths :
      EdgeMenger.HasEdgeDisjointPathsIn
        (graph G S T D) Finset.univ
        (sourceLeaves (G := G) S T D)
        (targetLeaves (G := G) S T D) S.card := by
    by_contra hno
    rcases EdgeMenger.edge_menger_cut
        (G := graph G S T D) (C := Finset.univ)
        (A := sourceLeaves (G := G) S T D)
        (B := targetLeaves (G := G) S T D) (k := S.card)
        (by simp) (by simp)
        (sourceLeaves_disjoint_targetLeaves (G := G) S T D) hno with
      ⟨cut⟩
    have hexpansion :
        (S \ originalSide (G := G) cut.X).card +
              D * (Section44.edgeBoundary G
                (originalSide (G := G) cut.X)
                (Finset.univ \ originalSide (G := G) cut.X)).card +
              (T ∩ originalSide (G := G) cut.X).card ≤
            (EdgeMenger.edgeBoundary (graph G S T D) cut.X cut.Y).card := by
      have h := cut_lower_bound (G := G) cut.cover
        cut.left_subset cut.right_subset
      simpa only [Section44.edgeBoundary_eq_edgeMenger] using h
    have horiginal :
        S.card ≤
          (S \ originalSide (G := G) cut.X).card +
              D * (Section44.edgeBoundary G
                (originalSide (G := G) cut.X)
                (Finset.univ \ originalSide (G := G) cut.X)).card +
              (T ∩ originalSide (G := G) cut.X).card := by
      simpa using
        (FlowWellLinked.superSourceSink_cutCapacity_lowerBound
          (G := G) (Terminals := Terminals) (S := S) (T := T)
          (A := originalSide (G := G) cut.X)
          (alphaNum := 1) (alphaDen := D) hwell hS hT hcard)
    exact (Nat.not_lt_of_ge (horiginal.trans hexpansion)) cut.boundary_lt
  rcases EdgeMenger.exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn
      hpaths with ⟨P, hPcard, _hstay⟩
  exact ⟨P, hPcard⟩

/-! ## Projection back to the original graph -/

/-- Collapse original and terminal copies to their original vertex, and each
channel to the first endpoint of its underlying unordered edge. -/
noncomputable def nodeProjection
    {S T : Finset V} {D : Nat} : Node G S T D → V
  | Sum.inl v => v
  | Sum.inr (Sum.inl v) => v.1
  | Sum.inr (Sum.inr (Sum.inl v)) => v.1
  | Sum.inr (Sum.inr (Sum.inr ei)) => ei.1.1.out.1

@[simp] theorem nodeProjection_original [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} (v : V) :
    nodeProjection (G := G)
      (original (G := G) (S := S) (T := T) (D := D) v) = v :=
  rfl

@[simp] theorem nodeProjection_source [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} (v : {v : V // v ∈ S}) :
    nodeProjection (G := G) (source (G := G) (T := T) (D := D) v) = v.1 :=
  rfl

@[simp] theorem nodeProjection_target [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} (v : {v : V // v ∈ T}) :
    nodeProjection (G := G) (target (G := G) (S := S) (D := D) v) = v.1 :=
  rfl

@[simp] theorem nodeProjection_channel [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (e : {e : Sym2 V // e ∈ G.edgeSet}) (i : Fin D) :
    nodeProjection (G := G) (channel (S := S) (T := T) e i) = e.1.out.1 :=
  rfl

/-- An expansion edge either collapses to equality or projects to an original
graph edge. -/
theorem nodeProjection_adj_or_eq [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} {a b : Node G S T D}
    (h : (graph G S T D).Adj a b) :
    nodeProjection (G := G) a = nodeProjection (G := G) b ∨
      G.Adj (nodeProjection (G := G) a) (nodeProjection (G := G) b) := by
  cases h with
  | sourceEdge v => exact Or.inl rfl
  | sourceEdgeSymm v => exact Or.inl rfl
  | targetEdge v => exact Or.inl rfl
  | targetEdgeSymm v => exact Or.inl rfl
  | channelEdge e i v hv =>
      by_cases heq : v = e.1.out.1
      · exact Or.inl heq
      · right
        rw [← _root_.SimpleGraph.mem_edgeSet]
        have hedge : e.1 = s(v, e.1.out.1) :=
          (Sym2.mem_and_mem_iff heq).1 ⟨hv, Sym2.out_fst_mem e.1⟩
        change s(v, e.1.out.1) ∈ G.edgeSet
        rw [← hedge]
        exact e.2
  | channelEdgeSymm e i v hv =>
      by_cases heq : e.1.out.1 = v
      · exact Or.inl heq
      · right
        apply G.symm
        rw [← _root_.SimpleGraph.mem_edgeSet]
        have hedge : e.1 = s(v, e.1.out.1) :=
          (Sym2.mem_and_mem_iff (Ne.symm heq)).1
            ⟨hv, Sym2.out_fst_mem e.1⟩
        change s(v, e.1.out.1) ∈ G.edgeSet
        rw [← hedge]
        exact e.2

/-- Project an expansion walk, deleting those expansion steps whose two
endpoints collapse to the same original vertex. -/
noncomputable def projectWalk [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} :
    ∀ {a b : Node G S T D}, (graph G S T D).Walk a b →
      G.Walk (nodeProjection (G := G) a) (nodeProjection (G := G) b)
  | _, _, .nil => .nil
  | _, _, .cons h w =>
      if heq :
          nodeProjection (G := G) _ = nodeProjection (G := G) _ then
        (projectWalk w).copy heq.symm rfl
      else
        .cons ((nodeProjection_adj_or_eq (G := G) h).resolve_left heq)
          (projectWalk w)

/-- The expansion edge at the non-collapsed endpoint of a channel.  This is
the unique edge charged when that channel projects to its underlying original
edge. -/
noncomputable def canonicalChannelEdge
    {S T : Finset V} {D : Nat}
    (e : {e : Sym2 V // e ∈ G.edgeSet}) (i : Fin D) :
    Sym2 (Node G S T D) :=
  s(original (G := G) (S := S) (T := T) (D := D) e.1.out.2,
    channel (S := S) (T := T) e i)

private theorem mem_edge_out_resolve
    (e : Sym2 V) {v : V} (hv : v ∈ e) (hne : v ≠ e.out.1) :
    v = e.out.2 := by
  have hv' : v ∈ s(e.out.1, e.out.2) := by
    rw [Sym2.mk, e.out_eq]
    exact hv
  rcases Sym2.mem_iff.mp hv' with hv' | hv'
  · exact False.elim (hne hv')
  · exact hv'

/-- Every original edge retained by `projectWalk` is witnessed by the
canonical expansion edge of one channel copy used by the input walk. -/
theorem projectWalk_edge_provenance [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    {a b : Node G S T D} (W : (graph G S T D).Walk a b)
    {edge : Sym2 V}
    (hedge : edge ∈ (projectWalk (G := G) W).edges) :
    ∃ (e : {e : Sym2 V // e ∈ G.edgeSet}) (i : Fin D),
      e.1 = edge ∧ canonicalChannelEdge (G := G) e i ∈ W.edges := by
  induction W with
  | nil =>
      simp [projectWalk] at hedge
  | @cons a b c h W ih =>
      by_cases heq :
          nodeProjection (G := G) a = nodeProjection (G := G) b
      · have hedgeTail :
            edge ∈ (projectWalk (G := G) W).edges := by
          simpa [projectWalk, heq] using hedge
        rcases ih hedgeTail with ⟨e, i, he, hi⟩
        exact ⟨e, i, he, by simpa using Or.inr hi⟩
      · have hedgeCases :
            edge =
                s(nodeProjection (G := G) a,
                  nodeProjection (G := G) b) ∨
              edge ∈ (projectWalk (G := G) W).edges := by
          simpa [projectWalk, heq] using hedge
        rcases hedgeCases with hedgeNow | hedgeTail
        · subst edge
          cases h with
          | sourceEdge v => exact False.elim (heq rfl)
          | sourceEdgeSymm v => exact False.elim (heq rfl)
          | targetEdge v => exact False.elim (heq rfl)
          | targetEdgeSymm v => exact False.elim (heq rfl)
          | channelEdge e i v hv =>
              have hvne : v ≠ e.1.out.1 := by simpa using heq
              have hvother : v = e.1.out.2 :=
                mem_edge_out_resolve e.1 hv hvne
              have heUnderlying :
                  e.1 = s(v, e.1.out.1) :=
                (Sym2.mem_and_mem_iff hvne).1
                  ⟨hv, Sym2.out_fst_mem e.1⟩
              refine ⟨e, i, ?_, ?_⟩
              · simpa using heUnderlying
              · simp [canonicalChannelEdge, hvother]
          | channelEdgeSymm e i v hv =>
              have hvne : v ≠ e.1.out.1 := by
                exact fun h => heq h.symm
              have hvother : v = e.1.out.2 :=
                mem_edge_out_resolve e.1 hv hvne
              have heUnderlying :
                  e.1 = s(e.1.out.1, v) := by
                rw [hvother, Sym2.mk, e.1.out_eq]
              refine ⟨e, i, ?_, ?_⟩
              · simpa using heUnderlying
              · simp [canonicalChannelEdge, hvother, Sym2.eq_swap]
        · rcases ih hedgeTail with ⟨e, i, he, hi⟩
          exact ⟨e, i, he, by simpa using Or.inr hi⟩

/-- Cycle-erase the projected walk to obtain a simple original-graph path. -/
noncomputable def projectPath [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (R : GraphPath (graph G S T D)) : GraphPath G where
  source := nodeProjection (G := G) R.source
  target := nodeProjection (G := G) R.target
  walk := (projectWalk (G := G) R.walk).bypass
  isPath := _root_.SimpleGraph.Walk.bypass_isPath _

@[simp] theorem projectPath_source [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (R : GraphPath (graph G S T D)) :
    (projectPath (G := G) R).source = nodeProjection (G := G) R.source :=
  rfl

@[simp] theorem projectPath_target [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (R : GraphPath (graph G S T D)) :
    (projectPath (G := G) R).target = nodeProjection (G := G) R.target :=
  rfl

/-- Provenance survives the final cycle erasure. -/
theorem projectPath_edge_provenance [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (R : GraphPath (graph G S T D)) {edge : Sym2 V}
    (hedge : edge ∈ (projectPath (G := G) R).edgeSet) :
    ∃ (e : {e : Sym2 V // e ∈ G.edgeSet}) (i : Fin D),
      e.1 = edge ∧ canonicalChannelEdge (G := G) e i ∈ R.edgeSet := by
  have hedgeBypass :
      edge ∈ (projectWalk (G := G) R.walk).bypass.edges := by
    simpa [projectPath, GraphPath.edgeSet] using hedge
  have hedgeWalk :
      edge ∈ (projectWalk (G := G) R.walk).edges :=
    _root_.SimpleGraph.Walk.edges_bypass_subset _ hedgeBypass
  rcases projectWalk_edge_provenance (G := G) R.walk hedgeWalk with
    ⟨e, i, he, hi⟩
  exact ⟨e, i, he, by simpa [GraphPath.edgeSet] using hi⟩

theorem nodeProjection_mem_source_of_mem_sourceLeaves [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} {x : Node G S T D}
    (hx : x ∈ sourceLeaves (G := G) S T D) :
    nodeProjection (G := G) x ∈ S := by
  classical
  rcases Finset.mem_image.mp hx with ⟨v, _hv, rfl⟩
  exact v.2

theorem nodeProjection_mem_target_of_mem_targetLeaves [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} {x : Node G S T D}
    (hx : x ∈ targetLeaves (G := G) S T D) :
    nodeProjection (G := G) x ∈ T := by
  classical
  rcases Finset.mem_image.mp hx with ⟨v, _hv, rfl⟩
  exact v.2

private theorem sourceLeaf_unique_neighbor [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} (v : {v : V // v ∈ S})
    {x : Node G S T D}
    (h : (graph G S T D).Adj (source (G := G) (T := T) (D := D) v) x) :
    x = original (G := G) (S := S) (T := T) (D := D) v.1 := by
  cases h
  rfl

private theorem targetLeaf_unique_neighbor [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} (v : {v : V // v ∈ T})
    {x : Node G S T D}
    (h : (graph G S T D).Adj (target (G := G) (S := S) (D := D) v) x) :
    x = original (G := G) (S := S) (T := T) (D := D) v.1 := by
  cases h
  rfl

private theorem sourcePendantEdge_mem [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (Q : GraphPath (graph G S T D)) (v : {v : V // v ∈ S})
    (hsource :
      Q.source = source (G := G) (T := T) (D := D) v)
    (htarget : Q.target ∈ targetLeaves (G := G) S T D) :
    s(source (G := G) (T := T) (D := D) v,
      original (G := G) (S := S) (T := T) (D := D) v.1) ∈ Q.edgeSet := by
  classical
  have hne : Q.source ≠ Q.target := by
    intro heq
    have hsTarget :
        source (G := G) (T := T) (D := D) v ∈
          targetLeaves (G := G) S T D := by
      rw [← hsource, heq]
      exact htarget
    exact Finset.disjoint_left.mp
      (sourceLeaves_disjoint_targetLeaves (G := G) S T D)
      (mem_sourceLeaves (G := G) v) hsTarget
  rcases Q.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hne Q.source_mem_vertexSet with ⟨edge, hedge, hincident⟩
  rcases Sym2.mem_iff_exists.mp hincident with ⟨x, hx⟩
  have hedgeGraph : edge ∈ (graph G S T D).edgeSet :=
    Q.edgeSet_subset_edgeSet hedge
  have hadj :
      (graph G S T D).Adj
        (source (G := G) (T := T) (D := D) v) x := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    rw [← hsource, ← hx]
    exact hedgeGraph
  have hxOriginal := sourceLeaf_unique_neighbor (G := G) v hadj
  rw [hxOriginal] at hx
  rw [hsource] at hx
  rw [← hx]
  exact hedge

private theorem targetPendantEdge_mem [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (Q : GraphPath (graph G S T D)) (v : {v : V // v ∈ T})
    (hsource : Q.source ∈ sourceLeaves (G := G) S T D)
    (htarget :
      Q.target = target (G := G) (S := S) (D := D) v) :
    s(target (G := G) (S := S) (D := D) v,
      original (G := G) (S := S) (T := T) (D := D) v.1) ∈ Q.edgeSet := by
  classical
  have hne : Q.source ≠ Q.target := by
    intro heq
    have htSource :
        target (G := G) (S := S) (D := D) v ∈
          sourceLeaves (G := G) S T D := by
      rw [← htarget, ← heq]
      exact hsource
    exact Finset.disjoint_left.mp
      (sourceLeaves_disjoint_targetLeaves (G := G) S T D)
      htSource (mem_targetLeaves (G := G) v)
  rcases Q.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hne Q.target_mem_vertexSet with ⟨edge, hedge, hincident⟩
  rcases Sym2.mem_iff_exists.mp hincident with ⟨x, hx⟩
  have hedgeGraph : edge ∈ (graph G S T D).edgeSet :=
    Q.edgeSet_subset_edgeSet hedge
  have hadj :
      (graph G S T D).Adj
        (target (G := G) (S := S) (D := D) v) x := by
    rw [← _root_.SimpleGraph.mem_edgeSet]
    rw [← htarget, ← hx]
    exact hedgeGraph
  have hxOriginal := targetLeaf_unique_neighbor (G := G) v hadj
  rw [hxOriginal] at hx
  rw [htarget] at hx
  rw [← hx]
  exact hedge

private theorem oriented_source_injective [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D)) :
    Function.Injective fun i : P.Index =>
      ((P.path i).orient (P.connects i)).source := by
  classical
  intro i j hij
  by_contra hne
  let Qi := (P.path i).orient (P.connects i)
  let Qj := (P.path j).orient (P.connects j)
  have hiSource : Qi.source ∈ sourceLeaves (G := G) S T D :=
    (P.path i).orient_source_mem (P.connects i)
  rcases Finset.mem_image.mp hiSource with ⟨v, _hv, hvSource⟩
  have hQiSource :
      Qi.source = source (G := G) (T := T) (D := D) v :=
    hvSource.symm
  have hQjSource :
      Qj.source = source (G := G) (T := T) (D := D) v := by
    exact hij.symm.trans hQiSource
  have hiEdge := sourcePendantEdge_mem (G := G) Qi v hQiSource
    ((P.path i).orient_target_mem (P.connects i))
  have hjEdge := sourcePendantEdge_mem (G := G) Qj v hQjSource
    ((P.path j).orient_target_mem (P.connects j))
  have hdisjoint := P.edge_disjoint hne
  exact Finset.disjoint_left.mp hdisjoint
    (by simpa [Qi] using hiEdge) (by simpa [Qj] using hjEdge)

private theorem oriented_target_injective [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D)) :
    Function.Injective fun i : P.Index =>
      ((P.path i).orient (P.connects i)).target := by
  classical
  intro i j hij
  by_contra hne
  let Qi := (P.path i).orient (P.connects i)
  let Qj := (P.path j).orient (P.connects j)
  have hiTarget : Qi.target ∈ targetLeaves (G := G) S T D :=
    (P.path i).orient_target_mem (P.connects i)
  rcases Finset.mem_image.mp hiTarget with ⟨v, _hv, hvTarget⟩
  have hQiTarget :
      Qi.target = target (G := G) (S := S) (D := D) v :=
    hvTarget.symm
  have hQjTarget :
      Qj.target = target (G := G) (S := S) (D := D) v := by
    exact hij.symm.trans hQiTarget
  have hiEdge := targetPendantEdge_mem (G := G) Qi v
    ((P.path i).orient_source_mem (P.connects i)) hQiTarget
  have hjEdge := targetPendantEdge_mem (G := G) Qj v
    ((P.path j).orient_source_mem (P.connects j)) hQjTarget
  have hdisjoint := P.edge_disjoint hne
  exact Finset.disjoint_left.mp hdisjoint
    (by simpa [Qi] using hiEdge) (by simpa [Qj] using hjEdge)

/-- Unit-weight flow obtained by projecting an integral expansion packing. -/
noncomputable def projectedFlow [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D)) :
    OrientedPathFlow G S T where
  Index := P.Index
  path := fun i =>
    projectPath (G := G) ((P.path i).orient (P.connects i))
  source_mem := fun i =>
    nodeProjection_mem_source_of_mem_sourceLeaves (G := G)
      ((P.path i).orient_source_mem (P.connects i))
  target_mem := fun i =>
    nodeProjection_mem_target_of_mem_targetLeaves (G := G)
      ((P.path i).orient_target_mem (P.connects i))
  weight := fun _ => 1
  weight_nonneg := fun _ => by norm_num

private theorem nodeProjection_injective_on_sourceLeaves [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} :
    Set.InjOn (nodeProjection (G := G))
      (sourceLeaves (G := G) S T D : Set (Node G S T D)) := by
  classical
  intro a ha b hb hab
  rcases Finset.mem_image.mp ha with ⟨va, _hva, hva⟩
  rcases Finset.mem_image.mp hb with ⟨vb, _hvb, hvb⟩
  rw [← hva, ← hvb] at hab ⊢
  have hv : va.1 = vb.1 := by simpa using hab
  have : va = vb := Subtype.ext hv
  subst vb
  rfl

private theorem nodeProjection_injective_on_targetLeaves [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat} :
    Set.InjOn (nodeProjection (G := G))
      (targetLeaves (G := G) S T D : Set (Node G S T D)) := by
  classical
  intro a ha b hb hab
  rcases Finset.mem_image.mp ha with ⟨va, _hva, hva⟩
  rcases Finset.mem_image.mp hb with ⟨vb, _hvb, hvb⟩
  rw [← hva, ← hvb] at hab ⊢
  have hv : va.1 = vb.1 := by simpa using hab
  have : va = vb := Subtype.ext hv
  subst vb
  rfl

theorem projectedFlow_source_injective [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D)) :
    Function.Injective fun i : P.Index => (projectedFlow (G := G) P).path i |>.source := by
  intro i j hij
  apply oriented_source_injective (G := G) P
  apply nodeProjection_injective_on_sourceLeaves (G := G)
  · exact (P.path i).orient_source_mem (P.connects i)
  · exact (P.path j).orient_source_mem (P.connects j)
  · exact hij

theorem projectedFlow_target_injective [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D)) :
    Function.Injective fun i : P.Index => (projectedFlow (G := G) P).path i |>.target := by
  intro i j hij
  apply oriented_target_injective (G := G) P
  apply nodeProjection_injective_on_targetLeaves (G := G)
  · exact (P.path i).orient_target_mem (P.connects i)
  · exact (P.path j).orient_target_mem (P.connects j)
  · exact hij

theorem projectedFlow_isUnitFlow [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D))
    (hsource : P.card = S.card) (htarget : P.card = T.card) :
    (projectedFlow (G := G) P).IsUnitFlow := by
  classical
  constructor
  · intro v hvS
    have hRangeEq :
        (Finset.univ.image fun i : P.Index =>
          ((projectedFlow (G := G) P).path i).source) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
        exact (projectedFlow (G := G) P).source_mem i
      · rw [Finset.card_image_of_injective _
          (projectedFlow_source_injective (G := G) P)]
        exact le_of_eq (by simpa [EdgePathPacking.card] using hsource.symm)
    have hvRange :
        v ∈ Finset.univ.image fun i : P.Index =>
          ((projectedFlow (G := G) P).path i).source := by
      rw [hRangeEq]
      exact hvS
    rcases Finset.mem_image.mp hvRange with ⟨i, _hi, hi⟩
    change (∑ j : P.Index,
      if ((projectedFlow (G := G) P).path j).source = v
      then (1 : Rat) else 0) = 1
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _hj hji
      have hne :
          ((projectedFlow (G := G) P).path j).source ≠ v := by
        intro hj
        exact hji (projectedFlow_source_injective (G := G) P
          (hj.trans hi.symm))
      simp [hne]
    · simp
  · intro v hvT
    have hRangeEq :
        (Finset.univ.image fun i : P.Index =>
          ((projectedFlow (G := G) P).path i).target) = T := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
        exact (projectedFlow (G := G) P).target_mem i
      · rw [Finset.card_image_of_injective _
          (projectedFlow_target_injective (G := G) P)]
        exact le_of_eq (by simpa [EdgePathPacking.card] using htarget.symm)
    have hvRange :
        v ∈ Finset.univ.image fun i : P.Index =>
          ((projectedFlow (G := G) P).path i).target := by
      rw [hRangeEq]
      exact hvT
    rcases Finset.mem_image.mp hvRange with ⟨i, _hi, hi⟩
    change (∑ j : P.Index,
      if ((projectedFlow (G := G) P).path j).target = v
      then (1 : Rat) else 0) = 1
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _hj hji
      have hne :
          ((projectedFlow (G := G) P).path j).target ≠ v := by
        intro hj
        exact hji (projectedFlow_target_injective (G := G) P
          (hj.trans hi.symm))
      simp [hne]
    · simp

theorem projected_edge_users_card_le [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D))
    (edge : Sym2 V) (hedgeG : edge ∈ G.edgeSet) :
    (Finset.univ.filter fun i : P.Index =>
      edge ∈ ((projectedFlow (G := G) P).path i).edgeSet).card ≤ D := by
  classical
  let Used := Finset.univ.filter fun i : P.Index =>
    edge ∈ ((projectedFlow (G := G) P).path i).edgeSet
  let originalEdge : {e : Sym2 V // e ∈ G.edgeSet} := ⟨edge, hedgeG⟩
  have hexists (u : {i : P.Index // i ∈ Used}) :
      ∃ c : Fin D,
        canonicalChannelEdge (G := G) originalEdge c ∈ (P.path u.1).edgeSet := by
    have hu :
        edge ∈ ((projectedFlow (G := G) P).path u.1).edgeSet :=
      (Finset.mem_filter.mp u.2).2
    rcases projectPath_edge_provenance (G := G)
        ((P.path u.1).orient (P.connects u.1)) hu with
      ⟨e, c, he, hc⟩
    have heEq : e = originalEdge := by
      apply Subtype.ext
      exact he
    subst e
    exact ⟨c, by simpa using hc⟩
  let channelOf (u : {i : P.Index // i ∈ Used}) : Fin D :=
    Classical.choose (hexists u)
  have hchannel (u : {i : P.Index // i ∈ Used}) :
      canonicalChannelEdge (G := G) originalEdge (channelOf u) ∈
        (P.path u.1).edgeSet :=
    Classical.choose_spec (hexists u)
  have hinjective : Function.Injective channelOf := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have hdisjoint := P.edge_disjoint hne
    exact Finset.disjoint_left.mp hdisjoint
      (hchannel a) (by simpa [hab] using hchannel b)
  have hcard := Fintype.card_le_of_injective channelOf hinjective
  simpa only [Used, Fintype.card_coe, Fintype.card_fin] using hcard

theorem projectedFlow_edgeCongestionAtMost [DecidableRel G.Adj]
    {S T : Finset V} {D : Nat}
    (P : EdgePathPacking (graph G S T D)
      (sourceLeaves (G := G) S T D) (targetLeaves (G := G) S T D)) :
    (projectedFlow (G := G) P).EdgeCongestionAtMost (D : Rat) := by
  intro edge hedgeG
  rw [OrientedPathFlow.edgeLoad]
  change
    (∑ i : P.Index,
      if edge ∈ ((projectedFlow (G := G) P).path i).edgeSet
      then (1 : Rat) else 0) ≤ D
  rw [Finset.sum_boole]
  exact_mod_cast projected_edge_users_card_le (G := G) P edge hedgeG

/-- Full rational unit flow between equal-size subsets of a numerator-one
scaled edge-well-linked terminal set.  This is the semantic flow consequence
used by the Chekuri--Chuzhoy Section 5 support-tree routing. -/
theorem exists_unitFlow_of_scaledEdgeWellLinked_one [DecidableRel G.Adj]
    {Terminals S T : Finset V} {D : Nat}
    (hwell : ScaledEdgeWellLinked G Terminals 1 D)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) :
    ∃ F : OrientedPathFlow G S T,
      F.IsUnitFlow ∧ F.EdgeCongestionAtMost (D : Rat) := by
  rcases exists_full_pathPacking (G := G) hwell hS hT hcard with
    ⟨P, hPcard⟩
  refine ⟨projectedFlow (G := G) P, ?_, projectedFlow_edgeCongestionAtMost P⟩
  apply projectedFlow_isUnitFlow (G := G) P hPcard
  exact hPcard.trans hcard

end CapacityExpansion

end ScaledWellLinkedPathFlow
end SimpleGraph

end Lax17Proofs
