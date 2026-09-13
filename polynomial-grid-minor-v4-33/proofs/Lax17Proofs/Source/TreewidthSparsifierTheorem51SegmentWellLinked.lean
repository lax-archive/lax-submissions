import Lax17Proofs.Source.TreewidthSparsifierTheorem51SegmentOutcome

namespace Lax17Proofs

universe u v w

/-!
# Well-linked terminals in the surviving segment graph

This module is the contracted-graph part of Step 3 in Chekuri--Chuzhoy,
*Degree-3 Treewidth Sparsifiers*, Theorem 5.1.  The initial terminals are
mapped injectively to their physical red-rail segments.  Claim 5.2 transfers
through the segment contraction, and the outcome selected by the finite
Karger union bound preserves the resulting cut inequalities.

The surviving blue objects counted here are complete carrier-clean arcs, not
individual edges of an unsuppressed blue path.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- The segment containing the initial terminal of rail `x`. -/
noncomputable def initialTerminalSegment
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (x : Fin h) :
    ExactRailSegmentIndex E hbudget hrecords B hB :=
  E.segmentOwner hbudget hrecords B hB fallback
    (E.initialTerminal hrecords x)

@[simp] theorem initialTerminalSegment_fst
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (x : Fin h) :
    (E.initialTerminalSegment
      hbudget hrecords B hB fallback x).1 = x := by
  exact E.segmentOwner_rail hbudget hrecords B hB fallback
    (E.initialTerminal_redCarrier hbudget hrecords x)

theorem initialTerminalSegment_injective
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Function.Injective
      (E.initialTerminalSegment hbudget hrecords B hB fallback) := by
  intro x y hxy
  have := congrArg Sigma.fst hxy
  simpa using this

/-- Images of the `h` initial terminals in the segment quotient. -/
noncomputable def initialTerminalSegments
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    Finset (ExactRailSegmentIndex E hbudget hrecords B hB) :=
  Finset.univ.image
    (E.initialTerminalSegment hbudget hrecords B hB fallback)

theorem initialTerminalSegments_card
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB) :
    (E.initialTerminalSegments
      hbudget hrecords B hB fallback).card = h := by
  classical
  rw [initialTerminalSegments,
    Finset.card_image_of_injective _
      (E.initialTerminalSegment_injective
        hbudget hrecords B hB fallback)]
  simp

/-- Rail labels whose initial-terminal segments belong to a quotient side. -/
noncomputable def initialTerminalSegmentSide
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    Finset (Fin h) :=
  Finset.univ.filter fun x =>
    E.initialTerminalSegment hbudget hrecords B hB fallback x ∈ S

theorem initialTerminalSegmentSide_card
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    (E.initialTerminalSegmentSide
        hbudget hrecords B hB fallback S).card =
      (S ∩ E.initialTerminalSegments
        hbudget hrecords B hB fallback).card := by
  classical
  let f :=
    E.initialTerminalSegment hbudget hrecords B hB fallback
  have hinj : Function.Injective f :=
    E.initialTerminalSegment_injective
      hbudget hrecords B hB fallback
  calc
    (E.initialTerminalSegmentSide
        hbudget hrecords B hB fallback S).card =
        ((E.initialTerminalSegmentSide
          hbudget hrecords B hB fallback S).image f).card := by
      symm
      exact Finset.card_image_of_injective _ hinj
    _ = (S ∩ E.initialTerminalSegments
          hbudget hrecords B hB fallback).card := by
      congr 1
      ext i
      constructor
      · intro hi
        rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_filter.mp hx).2,
            Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
      · intro hi
        rcases Finset.mem_inter.mp hi with ⟨hiS, hiT⟩
        rcases Finset.mem_image.mp hiT with ⟨x, _hx, rfl⟩
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hiS⟩, rfl⟩

theorem initialTerminalSegmentSide_compl
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    E.initialTerminalSegmentSide
        hbudget hrecords B hB fallback Sᶜ =
      (E.initialTerminalSegmentSide
        hbudget hrecords B hB fallback S)ᶜ := by
  classical
  ext x
  simp [initialTerminalSegmentSide]

/-- The terminal counts in a quotient cut are exactly the original terminal
counts in its two owner fibres. -/
theorem ownerSide_initialTerminal_card
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB)) :
    ((E.segmentOwnerSide hbudget hrecords B hB fallback S) ∩
        P.left P.firstIndex).card =
      (S ∩ E.initialTerminalSegments
        hbudget hrecords B hB fallback).card := by
  classical
  rw [← E.terminalSide_card hbudget hrecords]
  rw [← E.initialTerminalSegmentSide_card
    hbudget hrecords B hB fallback S]
  congr 1
  ext x
  simp [initialTerminalSegmentSide, initialTerminalSegment,
    E.mem_terminalSide, E.mem_segmentOwnerSide]

/-- Cut-well-linkedness for the terminal images in the surviving contracted
segment graph.  The right side is the number of deterministic nonblue edges
plus complete surviving blue arcs. -/
def SurvivingSegmentWellLinked
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (den : ℕ) : Prop :=
  ∀ S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB),
    min
        (S ∩ E.initialTerminalSegments
          hbudget hrecords B hB fallback).card
        (Sᶜ ∩ E.initialTerminalSegments
          hbudget hrecords B hB fallback).card ≤
      den *
        E.usableSegmentBoundaryCount
          hbudget hrecords B hB fallback S outcome

/-- Claim 5.2 transferred through segment contraction and combined with the
all-cuts outcome.  `512` is the division-safe form of the selected `1/256`
cut fraction. -/
theorem survivingSegmentWellLinked_of_cut_preserving
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (B : ℕ) (hB : 0 < B)
    (fallback : ExactRailSegmentIndex E hbudget hrecords B hB)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    (houtcome :
      ∀ S : Finset (ExactRailSegmentIndex E hbudget hrecords B hB),
        S.Nonempty → S ≠ Finset.univ →
          ((E.segmentQuotient
              hbudget hrecords B hB fallback).boundary S).card / 256 ≤
            E.usableSegmentBoundaryCount
              hbudget hrecords B hB fallback S outcome)
    (hconn :
      (E.segmentQuotient
        hbudget hrecords B hB fallback).IsEdgeConnected
          (segmentRestartCount h)) :
    E.SurvivingSegmentWellLinked
      hbudget hrecords B hB fallback outcome
      (512 * (2 * (2 * E.finalState.records.length + 1))) := by
  classical
  let T :=
    E.initialTerminalSegments hbudget hrecords B hB fallback
  let Q := E.segmentQuotient hbudget hrecords B hB fallback
  let d := 2 * (2 * E.finalState.records.length + 1)
  have hbase :=
    E.assembledSupport_initialTerminals_scaledWellLinked
      hbudget (segmentRestartCount_pos h) hrecords
  intro S
  let X := E.segmentOwnerSide hbudget hrecords B hB fallback S
  let Y := E.segmentOwnerSide hbudget hrecords B hB fallback Sᶜ
  have hcover : X ∪ Y = Finset.univ := by
    ext v
    by_cases hv :
        E.segmentOwner hbudget hrecords B hB fallback v ∈ S
    · simp [X, Y, hv]
    · simp [X, Y, hv]
  have hdisjoint : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro v hvX hvY
    have hvS :
        E.segmentOwner hbudget hrecords B hB fallback v ∈ S :=
      (E.mem_segmentOwnerSide
        hbudget hrecords B hB fallback S v).1
        (by simpa [X] using hvX)
    have hvNot :
        E.segmentOwner hbudget hrecords B hB fallback v ∉ S := by
      have :=
        (E.mem_segmentOwnerSide
          hbudget hrecords B hB fallback Sᶜ v).1
          (by simpa [Y] using hvY)
      simpa using this
    exact hvNot hvS
  have hraw :
      min (S ∩ T).card (Sᶜ ∩ T).card ≤
        d * (Q.boundary S).card := by
    have hcut := hbase.2.2 X Y hcover hdisjoint
    rw [E.ownerSide_initialTerminal_card
      hbudget hrecords B hB fallback S] at hcut
    rw [E.ownerSide_initialTerminal_card
      hbudget hrecords B hB fallback Sᶜ] at hcut
    have hboundaryEq :
        (Section44.edgeBoundary
          (E.assembledSupport hbudget) X Y).card =
          (Q.boundary S).card := by
      rw [← E.segmentBoundaryEdges_eq_edgeBoundary_ownerSides
        hbudget hrecords B hB fallback S]
      rw [← E.segmentQuotient_boundary_card
        hbudget hrecords B hB fallback S]
    rw [hboundaryEq] at hcut
    simpa [T, Q, d] using hcut
  by_cases hzero : min (S ∩ T).card (Sᶜ ∩ T).card = 0
  · change
      min (S ∩ T).card (Sᶜ ∩ T).card ≤
        (512 * (2 * (2 * E.finalState.records.length + 1))) *
          E.usableSegmentBoundaryCount
            hbudget hrecords B hB fallback S outcome
    rw [hzero]
    simp
  have hleft : S.Nonempty := by
    have hpos : 0 < (S ∩ T).card := by
      omega
    rcases Finset.card_pos.mp hpos with ⟨i, hi⟩
    exact ⟨i, (Finset.mem_inter.mp hi).1⟩
  have hproper : S ≠ Finset.univ := by
    intro hS
    have : (Sᶜ ∩ T).card = 0 := by simp [hS]
    omega
  have hboundary :
      segmentRestartCount h ≤ (Q.boundary S).card :=
    hconn S hleft hproper
  have hrestart : 256 ≤ segmentRestartCount h := by
    have hpow : 256 ≤ 2 ^ (realizedRoundConstant + 51) := by
      have : 8 ≤ realizedRoundConstant + 51 := by omega
      exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) this)
    have hlog : 1 ≤ Nat.log 2 h + 1 := by omega
    rw [segmentRestartCount_eq]
    calc
      256 = 256 * 1 := by simp
      _ ≤ 2 ^ (realizedRoundConstant + 51) *
          (Nat.log 2 h + 1) :=
        Nat.mul_le_mul hpow hlog
  have hlarge : 256 ≤ (Q.boundary S).card :=
    hrestart.trans hboundary
  have hdivision :
      (Q.boundary S).card ≤
        512 * ((Q.boundary S).card / 256) := by
    omega
  have hkeep :=
    houtcome S hleft hproper
  calc
    min (S ∩ T).card (Sᶜ ∩ T).card ≤
        d * (Q.boundary S).card := hraw
    _ ≤ d * (512 * ((Q.boundary S).card / 256)) :=
      Nat.mul_le_mul_left d hdivision
    _ ≤ d * (512 *
        E.usableSegmentBoundaryCount
          hbudget hrecords B hB fallback S outcome) :=
      Nat.mul_le_mul_left d (Nat.mul_le_mul_left 512 hkeep)
    _ = (512 * (2 * (2 * E.finalState.records.length + 1))) *
        E.usableSegmentBoundaryCount
          hbudget hrecords B hB fallback S outcome := by
      simp [d]
      ring

/-- The complete contracted-graph conclusion of Step 3: one degree-three
thinning outcome makes the `h` initial-terminal segment images
polylogarithmically cut-well-linked. -/
theorem exists_outcome_survivingSegmentWellLinked
    (E : ExpanderBlocks P (segmentRestartCount h))
    (hheight : 2 ≤ h)
    (hbudget :
      segmentRestartCount h *
          (realizedRoundConstant * Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length) :
    let N := segmentRestartCount h
    let B := 200 * N ^ 4
    let hB : 0 < B :=
      Nat.mul_pos (by norm_num)
        (Nat.pow_pos (segmentRestartCount_pos h))
    let fallback :=
      E.firstExactRailSegment hheight hbudget hrecords B hB
    ∃ outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget),
      E.SurvivingSegmentWellLinked
        hbudget hrecords B hB fallback outcome
        (512 * (2 * (2 * E.finalState.records.length + 1))) := by
  classical
  let N := segmentRestartCount h
  let B := 200 * N ^ 4
  have hN : 0 < N := segmentRestartCount_pos h
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by norm_num) (Nat.pow_pos hN)
  let fallback :=
    E.firstExactRailSegment hheight hbudget hrecords B hB
  obtain ⟨outcome, houtcome⟩ :=
    E.exists_segment_cut_preserving_outcome
      hheight hbudget hrecords
  have hconn :
      (E.segmentQuotient
        hbudget hrecords B hB fallback).IsEdgeConnected N := by
    exact E.segmentQuotient_isEdgeConnected
      hbudget hheight hrecords hN hB fallback
  refine ⟨outcome, ?_⟩
  exact E.survivingSegmentWellLinked_of_cut_preserving
    hbudget hrecords B hB fallback outcome
    (by simpa [N, B, fallback] using houtcome) hconn

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
