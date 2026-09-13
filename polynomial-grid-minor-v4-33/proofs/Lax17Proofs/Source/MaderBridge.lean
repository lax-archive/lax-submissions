import Lax17Proofs.Source.ChekuriChuzhoySection5SplitOff

namespace Lax17Proofs

universe u v w

/-!
# Named cut edges for Mader splitting

The auxiliary graphs used in Section 5 are edge-indexed multigraphs.  A bridge
must therefore remember the named edge copy: two parallel copies are never
bridges even though they have the same unordered endpoint pair.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A named edge copy is a cut edge when it is the entire boundary of some
vertex set.  This definition is component-local and works without a global
connectedness hypothesis. -/
def IsNamedCutEdge (H : FiniteEdgeIndexedGraph W) (e : H.Edge) : Prop :=
  ∃ X : Finset W, H.boundary X = {e}

/-- No named edge copy incident with the center is a cut edge. -/
def NoIncidentCutEdge (H : FiniteEdgeIndexedGraph W) (s : W) : Prop :=
  ∀ e ∈ H.incidentEdges s, ¬ H.IsNamedCutEdge e

/-- The exact multigraph form of Mader's admissible-pair theorem needed by the
Section 5 terminal-skeleton construction.  The lower degree bound excludes an
isolated center, while `degree ≠ 3` is Mader's exceptional case. -/
def MaderAdmissiblePairStatement : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : FiniteEdgeIndexedGraph W) (s : W),
    2 ≤ H.degree s → H.degree s ≠ 3 → H.NoIncidentCutEdge s →
      ∃ p : H.MaderSplitPair s, H.MaderAdmissible p

theorem isNamedCutEdge_iff_boundary_card_one_mem
    (H : FiniteEdgeIndexedGraph W) (e : H.Edge) :
    H.IsNamedCutEdge e ↔
      ∃ X : Finset W, (H.boundary X).card = 1 ∧ e ∈ H.boundary X := by
  classical
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, by simp [hX], by simp [hX]⟩
  · rintro ⟨X, hcard, he⟩
    refine ⟨X, ?_⟩
    rcases Finset.card_eq_one.mp hcard with ⟨f, hf⟩
    have hef : e = f := by
      have : e ∈ ({f} : Finset H.Edge) := by simpa [hf] using he
      simpa using this
    simpa [hef] using hf

theorem NoIncidentCutEdge.boundary_card_ne_one
    {H : FiniteEdgeIndexedGraph W} {s : W} (h : H.NoIncidentCutEdge s)
    {X : Finset W} {e : H.Edge} (heS : e ∈ H.incidentEdges s)
    (heX : e ∈ H.boundary X) :
    (H.boundary X).card ≠ 1 := by
  intro hcard
  exact h e heS ((isNamedCutEdge_iff_boundary_card_one_mem H e).2
    ⟨X, hcard, heX⟩)

theorem NoIncidentCutEdge.two_le_boundary
    {H : FiniteEdgeIndexedGraph W} {s : W} (h : H.NoIncidentCutEdge s)
    {X : Finset W} {e : H.Edge} (heS : e ∈ H.incidentEdges s)
    (heX : e ∈ H.boundary X) :
    2 ≤ (H.boundary X).card := by
  have hpos : 0 < (H.boundary X).card := Finset.card_pos.mpr ⟨e, heX⟩
  have hne := h.boundary_card_ne_one heS heX
  omega

theorem noIncidentCutEdge_iff_boundary_ne_singleton
    (H : FiniteEdgeIndexedGraph W) (s : W) :
    H.NoIncidentCutEdge s ↔
      ∀ (e : H.Edge), e ∈ H.incidentEdges s →
        ∀ X : Finset W, H.boundary X ≠ {e} := by
  simp only [NoIncidentCutEdge, IsNamedCutEdge, not_exists]

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
