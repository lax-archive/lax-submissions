import Lax17Proofs.Source.MaderEvenInduction
import Lax17Proofs.Source.MaderNoCutPreservation

namespace Lax17Proofs

universe u v w

/-!
# Iterated even-degree Mader splitting

This module packages repeated applications of an even-degree admissible-pair
theorem.  The graph-indexed decomposition avoids identifying the changing
named-edge types after successive splits.

For the odd-degree reduction, `MaderAvoidingRun` additionally transports a
finite set of distinguished edge copies.  A split retains exactly those
distinguished copies which survive as old edges.  Consequently, after at
most `D.card + 1` choices, one selected admissible pair avoids all currently
surviving representatives of `D`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton


open Finset

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- A hypothesis supplying an admissible pair at every eligible even-degree
center.  Separating this interface from its proof makes the iteration reusable
with either the irreducible core hypothesis or the final even Mader theorem. -/
def EvenMaderPairExistence : Prop :=
  ∀ (H : FiniteEdgeIndexedGraph W) (s : W),
    2 ≤ H.degree s → Even (H.degree s) → H.NoIncidentCutEdge s →
      ∃ p : H.MaderSplitPair s, H.MaderAdmissible p

/-- A complete sequence of admissible splits at `s`, ending when no named
edge copy remains incident with `s`. -/
inductive MaderEvenDecomposition (s : W) :
    FiniteEdgeIndexedGraph W → Type (u + 2)
  | done (H : FiniteEdgeIndexedGraph W) (degree_eq_zero : H.degree s = 0) :
      MaderEvenDecomposition s H
  | step (H : FiniteEdgeIndexedGraph W) (p : H.MaderSplitPair s)
      (admissible : H.MaderAdmissible p)
      (tail : MaderEvenDecomposition s (H.maderSplit p)) :
      MaderEvenDecomposition s H

namespace MaderEvenDecomposition

/-- Number of admissible pairs selected by a complete decomposition. -/
def length {s : W} {H : FiniteEdgeIndexedGraph W} :
    MaderEvenDecomposition s H → Nat
  | .done _ _ => 0
  | .step _ _ _ tail => tail.length + 1

/-- A complete decomposition selects exactly half the initial center degree
many pairs. -/
theorem two_mul_length {s : W} {H : FiniteEdgeIndexedGraph W}
    (D : MaderEvenDecomposition s H) :
    2 * D.length = H.degree s := by
  induction D with
  | done H hzero => simp [length, hzero]
  | step H p hadm tail ih =>
      rw [length, Nat.mul_add, ih, H.maderSplit_degree_center p]
      have htwo : 2 ≤ H.degree s := by
        unfold degree
        have hsubset : ({p.first, p.second} : Finset H.Edge) ⊆
            H.incidentEdges s := by
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · exact p.first_mem_incidentEdges
          · exact p.second_mem_incidentEdges
        have hcard := Finset.card_le_card hsubset
        simpa [p.edge_ne] using hcard
      omega

end MaderEvenDecomposition

/-- Repeated admissible splitting reaches center degree zero.  The no-cut
condition is maintained at each recursive call by admissibility and parity. -/
theorem exists_maderEvenDecomposition
    (hexists : EvenMaderPairExistence (W := W))
    (H : FiniteEdgeIndexedGraph W) (s : W)
    (heven : Even (H.degree s)) (hno : H.NoIncidentCutEdge s) :
    Nonempty (MaderEvenDecomposition s H) := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ H : FiniteEdgeIndexedGraph W,
      H.degree s = n → Even (H.degree s) → H.NoIncidentCutEdge s →
        Nonempty (MaderEvenDecomposition s H)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro K hdegree hevenK hnoK
        rcases even_eq_zero_or_two_le hevenK with hzero | htwo
        · exact ⟨.done K hzero⟩
        · rcases hexists K s htwo hevenK hnoK with ⟨p, hp⟩
          let K' := K.maderSplit p
          have hdegree' : K'.degree s = n - 2 := by
            rw [K.maderSplit_degree_center p, hdegree]
          have hlt : K'.degree s < n := by omega
          have heven' : Even (K'.degree s) := by
            simpa [K', K.maderSplit_degree_center p] using even_sub_two hevenK
          have hno' : K'.NoIncidentCutEdge s := by
            apply K.maderAdmissible_preserves_noIncidentCutEdge p hnoK hp
            exact even_eq_zero_or_two_le heven'
          rcases ih (K'.degree s) hlt K' rfl heven' hno' with ⟨tail⟩
          exact ⟨.step K p hp tail⟩
  exact hP (H.degree s) H rfl heven hno

/-- The current representatives of `D` after splitting `p`: selected copies
are deleted, and every other distinguished copy survives through the old-edge
injection. -/
def survivingDistinguished {H : FiniteEdgeIndexedGraph W} {s : W}
    (p : H.MaderSplitPair s) (D : Finset H.Edge) :
    Finset (H.maderSplit p).Edge := by
  classical
  let remaining := (D.erase p.first).erase p.second
  let embed : remaining → (H.maderSplit p).Edge := fun e =>
    Sum.inl ⟨e.1, by
      have hsecond := Finset.mem_erase.mp e.2
      have hfirst := Finset.mem_erase.mp hsecond.2
      exact ⟨hfirst.1, hsecond.1⟩⟩
  exact remaining.attach.map ⟨embed, by
    intro e f hef
    change Sum.inl (⟨e.1, _⟩ :
      {g : H.Edge // g ≠ p.first ∧ g ≠ p.second}) =
        Sum.inl (⟨f.1, _⟩ :
          {g : H.Edge // g ≠ p.first ∧ g ≠ p.second}) at hef
    have hsub := Sum.inl.inj hef
    apply Subtype.ext
    exact congrArg
      (fun z : {g : H.Edge // g ≠ p.first ∧ g ≠ p.second} => z.1) hsub⟩

@[simp] theorem card_survivingDistinguished
    {H : FiniteEdgeIndexedGraph W} {s : W}
    (p : H.MaderSplitPair s) (D : Finset H.Edge) :
    (survivingDistinguished p D).card =
      ((D.erase p.first).erase p.second).card := by
  classical
  simp [survivingDistinguished]

theorem card_survivingDistinguished_lt
    {H : FiniteEdgeIndexedGraph W} {s : W}
    (p : H.MaderSplitPair s) (D : Finset H.Edge)
    (hhit : p.first ∈ D ∨ p.second ∈ D) :
    (survivingDistinguished p D).card < D.card := by
  rw [card_survivingDistinguished]
  rcases hhit with hfirst | hsecond
  · exact (Finset.card_erase_le.trans_lt (Finset.card_erase_lt_of_mem hfirst))
  · by_cases hfirst : p.first ∈ D
    · exact (Finset.card_erase_le.trans_lt (Finset.card_erase_lt_of_mem hfirst))
    · rw [Finset.erase_eq_of_notMem hfirst]
      exact Finset.card_erase_lt_of_mem hsecond

/-- A bounded run which stops at the first selected admissible pair avoiding
all surviving representatives of the distinguished initial copies. -/
inductive MaderAvoidingRun (s : W) :
    (H : FiniteEdgeIndexedGraph W) → Finset H.Edge → Type (u + 2)
  | here (H : FiniteEdgeIndexedGraph W) (D : Finset H.Edge)
      (p : H.MaderSplitPair s) (admissible : H.MaderAdmissible p)
      (first_not_distinguished : p.first ∉ D)
      (second_not_distinguished : p.second ∉ D) :
      MaderAvoidingRun s H D
  | later (H : FiniteEdgeIndexedGraph W) (D : Finset H.Edge)
      (p : H.MaderSplitPair s) (admissible : H.MaderAdmissible p)
      (hits_distinguished : p.first ∈ D ∨ p.second ∈ D)
      (tail : MaderAvoidingRun s (H.maderSplit p)
        (survivingDistinguished p D)) :
      MaderAvoidingRun s H D

namespace MaderAvoidingRun

/-- Number of pair choices, including the final avoiding choice. -/
def length {s : W} {H : FiniteEdgeIndexedGraph W} {D : Finset H.Edge} :
    MaderAvoidingRun s H D → Nat
  | .here _ _ _ _ _ _ => 1
  | .later _ _ _ _ _ tail => tail.length + 1

/-- The pigeonhole bound carried by the run representation. -/
theorem length_le_card_add_one {s : W} {H : FiniteEdgeIndexedGraph W}
    {D : Finset H.Edge} (R : MaderAvoidingRun s H D) :
    R.length ≤ D.card + 1 := by
  induction R with
  | here => simp [length]
  | later H D p hadm hhit tail ih =>
      rw [length]
      have hcard := card_survivingDistinguished_lt p D hhit
      omega

end MaderAvoidingRun

/-- If there are two more center copies than twice the number of distinguished
copies, repeated admissible splitting finds a pair which avoids all of them.
For `D.card ≤ 3`, center degree at least eight is the intended instance. -/
theorem exists_maderAvoidingRun
    (hexists : EvenMaderPairExistence (W := W))
    (H : FiniteEdgeIndexedGraph W) (s : W) (D : Finset H.Edge)
    (heven : Even (H.degree s)) (hno : H.NoIncidentCutEdge s)
    (hdegree : 2 * (D.card + 1) ≤ H.degree s) :
    Nonempty (MaderAvoidingRun s H D) := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ (K : FiniteEdgeIndexedGraph W) (E : Finset K.Edge),
      E.card = n → Even (K.degree s) → K.NoIncidentCutEdge s →
        2 * (E.card + 1) ≤ K.degree s →
          Nonempty (MaderAvoidingRun s K E)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro K E hcard hevenK hnoK hdegreeK
        have htwo : 2 ≤ K.degree s := by omega
        rcases hexists K s htwo hevenK hnoK with ⟨p, hp⟩
        by_cases havoid : p.first ∉ E ∧ p.second ∉ E
        · exact ⟨.here K E p hp havoid.1 havoid.2⟩
        · have hhit : p.first ∈ E ∨ p.second ∈ E := by
            simpa only [not_and_or, not_not] using havoid
          let E' := survivingDistinguished p E
          let K' := K.maderSplit p
          have hcardlt : E'.card < n := by
            rw [← hcard]
            exact card_survivingDistinguished_lt p E hhit
          have heven' : Even (K'.degree s) := by
            simpa [K', K.maderSplit_degree_center p] using even_sub_two hevenK
          have hbound' : 2 * (E'.card + 1) ≤ K'.degree s := by
            have hsurvive : E'.card < E.card :=
              card_survivingDistinguished_lt p E hhit
            change 2 * (E'.card + 1) ≤ (K.maderSplit p).degree s
            rw [K.maderSplit_degree_center p]
            omega
          have hno' : K'.NoIncidentCutEdge s := by
            apply K.maderAdmissible_preserves_noIncidentCutEdge p hnoK hp
            exact Or.inr (le_trans (by omega : 2 ≤ 2 * (E'.card + 1)) hbound')
          rcases ih E'.card hcardlt K' E' rfl heven' hno' hbound' with ⟨tail⟩
          exact ⟨.later K E p hp hhit tail⟩
  exact hP D.card H D rfl heven hno hdegree

/-- The degree-eight, at-most-three-distinguished-copies specialization used
by the three-edge augmentation reduction. -/
theorem exists_maderAvoidingRun_of_card_le_three
    (hexists : EvenMaderPairExistence (W := W))
    (H : FiniteEdgeIndexedGraph W) (s : W) (D : Finset H.Edge)
    (heven : Even (H.degree s)) (hno : H.NoIncidentCutEdge s)
    (hD : D.card ≤ 3) (hdegree : 8 ≤ H.degree s) :
    Nonempty (MaderAvoidingRun s H D) := by
  apply exists_maderAvoidingRun hexists H s D heven hno
  omega

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph

end Lax17Proofs
