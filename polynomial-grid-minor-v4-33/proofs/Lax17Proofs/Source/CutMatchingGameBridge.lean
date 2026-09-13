import Lax17Proofs.Source.CutMatchingGameExpansion
import Lax17Proofs.Source.HairyCrossbarGrid

namespace Lax17Proofs

universe u v w

/-!
# Bridge from abstract cut-matching games to transported grid rounds

The cut-matching game proof is most naturally formalized for an abstract
finite vertex set and an adversarial matching player.  The large-case
crossbar-grid construction uses a concrete matching player: each cut is
matched by the transported local crossbar matching.  This file identifies the
abstract edge-indexed matching union with the existing transported
edge-indexed auxiliary multigraph.
-/

namespace SimpleGraph
namespace HairyCrossbarGrid
namespace SelectedOddLocalCrossbarGridTransportedRoundFamily


/-- The `Fin`-indexed abstract round family associated with a finite
transported bisection transcript.  This form keeps the cuts bundled as
`Bisection`s, which is convenient when the transcript has already been
generated as a list of lazy cut-matching rounds. -/
noncomputable def abstractFinRoundFamilyOfBisections
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (hrounds : roundBound ≤ m)
    (cuts : Fin roundBound → CutMatchingGame.Bisection (GridVertex g)) :
    CutMatchingGame.RoundFamily (GridVertex g) (Fin roundBound) where
  cut := cuts
  matching := fun r =>
    { toEquiv :=
        (selectedOddLocalCrossbarGridTransportedMatchingRound
          Hsys hcrossbars hlen (finCluster hrounds r)
          (cuts r).disjoint (cuts r).card_eq).middleCoordMatching }

/-- The `Fin`-indexed abstract round family associated with a finite
transported cut transcript.  This is the proof-facing version produced by the
sequential cut-player strategy before the repository wraps the index type in
`ULift` for universe bookkeeping. -/
noncomputable def abstractFinRoundFamilyOfFinCuts
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (hrounds : roundBound ≤ m)
    (U W : Fin roundBound → Finset (GridVertex g))
    (hdisj : ∀ r : Fin roundBound, Disjoint (U r) (W r))
    (hcard : ∀ r : Fin roundBound, (U r).card = (W r).card)
    (hcover : ∀ r : Fin roundBound, U r ∪ W r = Finset.univ) :
    CutMatchingGame.RoundFamily (GridVertex g) (Fin roundBound) where
  cut := fun r =>
    { left := U r
      right := W r
      disjoint := hdisj r
      card_eq := hcard r
      cover := hcover r }
  matching := fun r =>
    { toEquiv :=
        (selectedOddLocalCrossbarGridTransportedMatchingRound
          Hsys hcrossbars hlen (finCluster hrounds r)
          (hdisj r) (hcard r)).middleCoordMatching }

/-- The `r`-th transported coordinate cut as an abstract cut-matching-game
bisection. -/
noncomputable def toAbstractBisection
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll) (r : F.Index) :
    CutMatchingGame.Bisection (GridVertex g) where
  left := F.U r
  right := F.W r
  disjoint := F.disjoint r
  card_eq := F.card_eq r
  cover := hcover r

/-- The transported matching in round `r`, viewed as an abstract perfect
matching across the corresponding bisection. -/
noncomputable def toAbstractMatching
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll) (r : F.Index) :
    CutMatchingGame.MatchingAcross (F.toAbstractBisection hcover r) where
  toEquiv := (F.round r).middleCoordMatching

/-- A transported round family as an abstract cut-matching-game round family. -/
noncomputable def toAbstractRoundFamily
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll) :
    CutMatchingGame.RoundFamily (GridVertex g) F.Index where
  cut := F.toAbstractBisection hcover
  matching := F.toAbstractMatching hcover

/-- The abstract edge type is definitionally the same data as the transported
edge type: a round and a left endpoint in that round. -/
noncomputable def abstractEdgeEquiv
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll) :
    (F.toAbstractRoundFamily hcover).Edge ≃ Edge F where
  toFun := fun e => ⟨e.1, e.2⟩
  invFun := fun e => ⟨e.round, e.source⟩
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro e
    cases e
    rfl

@[simp]
theorem abstractEdgeEquiv_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (e : (F.toAbstractRoundFamily hcover).Edge) :
    (F.abstractEdgeEquiv hcover e).left =
      (F.toAbstractRoundFamily hcover).edgeSource e := by
  rfl

@[simp]
theorem abstractEdgeEquiv_right
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (e : (F.toAbstractRoundFamily hcover).Edge) :
    (F.abstractEdgeEquiv hcover e).right =
      (F.toAbstractRoundFamily hcover).edgeTarget e := by
  rfl

/-- Crossing a cut is preserved by the edge identification above. -/
theorem abstractEdgeEquiv_crosses_iff
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (S : Finset (GridVertex g))
    (e : (F.toAbstractRoundFamily hcover).Edge) :
    (F.toAbstractRoundFamily hcover).edgeCrosses S e ↔
      (F.abstractEdgeEquiv hcover e).Crosses S := by
  rfl

/-- The abstract and transported edge-boundaries have the same cardinality. -/
theorem abstract_edgeBoundary_card_eq
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (S : Finset (GridVertex g)) :
    ((F.toAbstractRoundFamily hcover).edgeBoundary S).card =
      (F.edgeBoundary S).card := by
  classical
  refine Finset.card_bij
    (fun e _he => F.abstractEdgeEquiv hcover e)
    ?maps_to ?injective ?surjective
  · intro e he
    rw [mem_edgeBoundary]
    rw [← F.abstractEdgeEquiv_crosses_iff hcover S e]
    simpa using he
  · intro e₁ _he₁ e₂ _he₂ heq
    exact (F.abstractEdgeEquiv hcover).injective heq
  · intro e he
    refine ⟨(F.abstractEdgeEquiv hcover).symm e, ?_, ?_⟩
    · rw [CutMatchingGame.RoundFamily.mem_edgeBoundary]
      rw [F.abstractEdgeEquiv_crosses_iff hcover S
        ((F.abstractEdgeEquiv hcover).symm e)]
      rw [mem_edgeBoundary] at he
      simpa using he
    · simp

/-- If the abstract cut-matching-game union is a half-expander, then the
existing transported edge-indexed auxiliary multigraph is a half-expander. -/
theorem isHalfEdgeExpander_of_toAbstractRoundFamily
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (hF : (F.toAbstractRoundFamily hcover).IsHalfEdgeExpander) :
    F.IsHalfEdgeExpander := by
  rw [isHalfEdgeExpander_iff]
  intro S hS hhalf
  have h := hF S hS hhalf
  rwa [F.abstract_edgeBoundary_card_eq hcover S] at h

/-- A half-expander proof for the natural `Fin`-indexed abstract transcript
transfers to the transported `ofFinCuts` family used downstream. -/
theorem ofFinCuts_isHalfEdgeExpander_of_abstractFinRoundFamily
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (hrounds : roundBound ≤ m)
    (U W : Fin roundBound → Finset (GridVertex g))
    (hdisj : ∀ r : Fin roundBound, Disjoint (U r) (W r))
    (hcard : ∀ r : Fin roundBound, (U r).card = (W r).card)
    (hcover : ∀ r : Fin roundBound, U r ∪ W r = Finset.univ)
    (hfin :
      (abstractFinRoundFamilyOfFinCuts Hsys hcrossbars hlen hrounds
        U W hdisj hcard hcover).IsHalfEdgeExpander) :
    (ofFinCuts Hsys hcrossbars hlen hrounds U W hdisj hcard).IsHalfEdgeExpander := by
  classical
  let F := ofFinCuts Hsys hcrossbars hlen hrounds U W hdisj hcard
  have hcoverF : F.CoversAll := by
    intro r
    rcases r with ⟨r⟩
    simpa [F, ofFinCuts, ofCuts] using hcover r
  apply (ofFinCuts Hsys hcrossbars hlen hrounds U W hdisj hcard).isHalfEdgeExpander_of_toAbstractRoundFamily
    hcoverF
  have hfin' :
      ((F.toAbstractRoundFamily hcoverF).reindex (Equiv.ulift.symm)).IsHalfEdgeExpander := by
    simpa [F, abstractFinRoundFamilyOfFinCuts, toAbstractRoundFamily,
      toAbstractBisection, toAbstractMatching, ofFinCuts, ofCuts,
      CutMatchingGame.RoundFamily.reindex] using hfin
  exact
    (CutMatchingGame.RoundFamily.isHalfEdgeExpander_reindex_iff
      (Equiv.ulift.symm) (F.toAbstractRoundFamily hcoverF)).mp hfin'

/-- Bisection-bundled version of
`ofFinCuts_isHalfEdgeExpander_of_abstractFinRoundFamily`. -/
theorem ofFinBisections_isHalfEdgeExpander_of_abstractFinRoundFamily
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (hrounds : roundBound ≤ m)
    (cuts : Fin roundBound → CutMatchingGame.Bisection (GridVertex g))
    (hfin :
      (abstractFinRoundFamilyOfBisections Hsys hcrossbars hlen hrounds
        cuts).IsHalfEdgeExpander) :
    (ofFinCuts Hsys hcrossbars hlen hrounds
      (fun r => (cuts r).left)
      (fun r => (cuts r).right)
      (fun r => (cuts r).disjoint)
      (fun r => (cuts r).card_eq)).IsHalfEdgeExpander := by
  apply ofFinCuts_isHalfEdgeExpander_of_abstractFinRoundFamily
    Hsys hcrossbars hlen hrounds
    (fun r => (cuts r).left)
    (fun r => (cuts r).right)
    (fun r => (cuts r).disjoint)
    (fun r => (cuts r).card_eq)
    (fun r => (cuts r).cover)
  simpa [abstractFinRoundFamilyOfBisections, abstractFinRoundFamilyOfFinCuts]
    using hfin

end SelectedOddLocalCrossbarGridTransportedRoundFamily
end HairyCrossbarGrid
end SimpleGraph

end Lax17Proofs
