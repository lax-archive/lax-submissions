import Lax17Proofs.Source.TreewidthSparsifierTheorem51ChunkConcentration

namespace Lax17Proofs

universe u v w

/-!
# One outcome preserving every abstract cut by complete chunks

The multigraph here has one named edge for every realized matching edge.
Karger's cut count is applied to this abstract transcript graph, while the bad
event records survival of the corresponding complete carrier-clean physical
chunks.  Thus the simultaneous outcome obtained below already consists of
usable rail-to-rail connections.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame
open ChekuriChuzhoySection5TerminalSkeleton
open ThinningUnion


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- One named edge for every matching source in every physical record. -/
abbrev RecordEdge (E : ExpanderBlocks P count) :=
  Σ j : Fin E.finalState.records.length,
    {x : Fin h // x ∈ (E.recordAt j).cut.left}

/-- The abstract multigraph formed by all realized matching rounds. -/
noncomputable def transcriptGraph
    (E : ExpanderBlocks P count) :
    FiniteEdgeIndexedGraph (Fin h) where
  Edge := E.RecordEdge
  left := fun z => z.2.1
  right := fun z =>
    (E.recordAt z.1).round.matching.rightEndpoint z.2
  end_ne := by
    intro z heq
    have hleft : z.2.1 ∈ (E.recordAt z.1).cut.left := z.2.2
    have hright :
        (E.recordAt z.1).round.matching.rightEndpoint z.2 ∈
          (E.recordAt z.1).cut.right :=
      (E.recordAt z.1).round.matching.rightEndpoint_mem z.2
    exact
      (E.recordAt z.1).cut.not_mem_left_of_mem_right hright
        (heq ▸ hleft)

/-- Boundary edges of the transcript graph are exactly the
`RecordBoundary` instances used to select physical chunks. -/
noncomputable def transcriptBoundaryEquiv
    (E : ExpanderBlocks P count) (S : Finset (Fin h)) :
    {z : (E.transcriptGraph).Edge //
      z ∈ (E.transcriptGraph).boundary S} ≃
      E.RecordBoundary S where
  toFun := fun z =>
    ⟨z.1.1,
      ⟨z.1.2,
        LazyRound.mem_edgeBoundary.mpr
          ((FiniteEdgeIndexedGraph.mem_boundary
            E.transcriptGraph S z.1).mp z.2)⟩⟩
  invFun := fun z =>
    ⟨⟨z.1, z.2.1⟩,
      (FiniteEdgeIndexedGraph.mem_boundary
        E.transcriptGraph S ⟨z.1, z.2.1⟩).mpr
          (LazyRound.mem_edgeBoundary.mp z.2.2)⟩
  left_inv := by
    intro z
    apply Subtype.ext
    rfl
  right_inv := by
    intro z
    rfl

theorem transcriptGraph_boundary_card
    (E : ExpanderBlocks P count) (S : Finset (Fin h)) :
    (E.transcriptGraph.boundary S).card =
      Fintype.card (E.RecordBoundary S) := by
  classical
  calc
    (E.transcriptGraph.boundary S).card =
        Fintype.card
          {z : E.transcriptGraph.Edge //
            z ∈ E.transcriptGraph.boundary S} := by
      rw [Fintype.card_coe]
    _ = Fintype.card (E.RecordBoundary S) :=
      Fintype.card_congr (E.transcriptBoundaryEquiv S)

/-- The transcript graph has edge connectivity at least half the number of
independent expander blocks. -/
theorem transcriptGraph_isEdgeConnected
    (E : ExpanderBlocks P count) :
    E.transcriptGraph.IsEdgeConnected (count / 2) := by
  classical
  intro S hS hproper
  have hScard : S.card ≤ h := by
    simpa using Finset.card_le_univ S
  by_cases hhalf : 2 * S.card ≤ h
  · have hexpand :=
      count_mul_card_le_two_mul_edgeBoundaryCount P E S
        (Finset.card_pos.mpr hS) hhalf
    have hcount :
        count ≤
          2 * edgeBoundaryCount (List.ofFn E.rounds).flatten S :=
      (Nat.le_mul_of_pos_right count
        (Finset.card_pos.mpr hS)).trans hexpand
    rw [E.transcriptGraph_boundary_card,
      E.recordBoundary_card_eq_edgeBoundaryCount]
    omega
  · have hcomp : (Sᶜ : Finset (Fin h)).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hc
      apply hproper
      have hc' := congrArg (fun T : Finset (Fin h) => Tᶜ) hc
      simpa using hc'
    have hcompHalf :
        2 * (Sᶜ : Finset (Fin h)).card ≤ h := by
      have hcompCard :
          (Sᶜ : Finset (Fin h)).card = h - S.card := by
        simpa using Finset.card_compl S
      omega
    have hexpand :=
      count_mul_card_le_two_mul_edgeBoundaryCount P E Sᶜ
        (Finset.card_pos.mpr hcomp) hcompHalf
    have hcount :
        count ≤
          2 * edgeBoundaryCount
            (List.ofFn E.rounds).flatten Sᶜ :=
      (Nat.le_mul_of_pos_right count
        (Finset.card_pos.mpr hcomp)).trans hexpand
    have hboundary :
        (E.transcriptGraph.boundary S).card =
          edgeBoundaryCount (List.ofFn E.rounds).flatten Sᶜ := by
      rw [← E.recordBoundary_card_eq_edgeBoundaryCount,
        ← E.transcriptGraph_boundary_card,
        FiniteEdgeIndexedGraph.boundary_compl]
    omega

/-- One genuine thinning outcome preserves at least one sixteenth of every
nontrivial abstract transcript cut as complete physical chunks. -/
theorem exists_chunk_cut_preserving_outcome
    (E : ExpanderBlocks P count)
    (hcount : count = restartCount h)
    (hheight : 2 ≤ h)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    ∃ outcome :
        BlueThinningInput.Outcome
          (H := E.assembledSupport hbudget),
      ∀ S : Finset (Fin h),
        S.Nonempty → S ≠ Finset.univ →
          (E.transcriptGraph.boundary S).card / 16 ≤
            E.survivingChunkCount hbudget S outcome := by
  classical
  let Q := E.transcriptGraph
  let C := count / 2
  let Ω :=
    BlueThinningInput.Outcome
      (H := E.assembledSupport hbudget)
  let bad : Finset (Fin h) → Finset Ω :=
    fun S => Finset.univ.filter fun outcome =>
      E.survivingChunkCount hbudget S outcome <
        (Q.boundary S).card / 16
  have hC : 0 < C := by
    dsimp [C]
    rw [hcount]
    exact restartCount_half_pos h
  have hconn : Q.IsEdgeConnected C := by
    exact E.transcriptGraph_isEdgeConnected
  have htail :
      ∀ S ∈ ThinningUnion.nontrivialCuts,
        (bad S).card *
            4 ^ ((Q.boundary S).card / 16 + 1) ≤
          Fintype.card Ω := by
    intro S _hS
    have hfixed :=
      E.survivingChunkCount_bad_mul_failureFactor_le_total
        hbudget S
    simpa [bad, Q, Ω, E.transcriptGraph_boundary_card S] using hfixed
  have hcapacity :
      ∀ a, 0 < a →
        (ThinningUnion.scaleCuts Q C a).card * 2 ^ (a + 2) ≤
          4 ^ ((a * C) / 16 + 1) := by
    intro a ha
    have hscaleSmall :=
      ThinningUnion.card_scaleCuts_le_smallCuts
        (a := a) Q hC
    have hkarger :=
      Karger.card_smallCuts_le_two_mul_vertexCard_pow_all
        Q hC (by omega : 0 < a + 1) hconn
        (by simpa using hheight)
    have hscale :
        (ThinningUnion.scaleCuts Q C a).card ≤
          2 * h ^ (2 * (a + 1)) :=
      hscaleSmall.trans (by simpa [Q] using hkarger)
    have hnum :=
      restartCount_failure_capacity hheight ha
    rw [← hcount] at hnum
    have hexp :
        (a * C) / 128 + 1 ≤ (a * C) / 16 + 1 := by
      exact Nat.add_le_add_right
        (Nat.div_le_div_left
          (by norm_num : 16 ≤ 128) (by norm_num : 0 < 16)) 1
    exact
      (Nat.mul_le_mul_right _ hscale).trans
        (hnum.trans
          (Nat.pow_le_pow_right (by norm_num) hexp))
  obtain ⟨outcome, houtcome⟩ :=
    ThinningUnion.exists_outcome_avoiding_all_cut_badSets
      Q hC (by norm_num : 0 < 16) hconn bad htail hcapacity
  refine ⟨outcome, ?_⟩
  intro S hS hproper
  have hnot := houtcome S hS hproper
  simp [bad, Q] at hnot
  exact hnot

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
