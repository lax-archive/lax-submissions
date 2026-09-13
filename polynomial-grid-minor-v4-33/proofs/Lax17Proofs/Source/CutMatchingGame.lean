import Lax17Proofs.Source.CutMatchingGameBridge
import Lax17Proofs.Source.CutMatchingGameBudget

namespace Lax17Proofs

universe u v w

/-!
# Cut-matching game bridge

This file packages the Section 4 cut-matching-game theorem in the provider
form consumed by the large crossbar-grid assembly.

The proof combines the abstract entropy-potential cut-matching game, the
deterministic peeling upgrade, and the transported local-crossbar matching
responder.  The final theorem has the same shape as the contract statement but
does not import the contract module.
-/

namespace SimpleGraph
namespace HairyCrossbarGrid


/-- Sequential matching responder supplied by the selected odd local
crossbars.  For round indices below the fixed round bound it uses the
corresponding selected odd cluster; the fallback branch is unreachable in the
fixed-round transcript but keeps the responder total on natural time. -/
noncomputable def transportedSequentialResponder
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g roundBound : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * roundBound ≤ ell) (hpos : 0 < roundBound) :
    CutMatchingGame.SequentialResponder (GridVertex g) :=
  fun round B =>
    if hround : round < roundBound then
      { toEquiv :=
          (selectedOddLocalCrossbarGridTransportedMatchingRound
            Hsys hcrossbars hlen ⟨round, hround⟩
            B.disjoint B.card_eq).middleCoordMatching }
    else
      { toEquiv :=
          (selectedOddLocalCrossbarGridTransportedMatchingRound
            Hsys hcrossbars hlen ⟨0, hpos⟩
            B.disjoint B.card_eq).middleCoordMatching }

/-- The cut-matching-game upper bound supplies the unbundled fixed-round
provider used by the crossbar-grid construction: after `O(log g)` rounds,
the transported matching union is a half-edge-expander. -/
theorem exists_fixedRoundCutMatchingUnbundledProvider :
    ∃ cRound : ℕ, 0 < cRound ∧
      FixedRoundCutMatchingUnbundledProvider.{u} cRound := by
  rcases
    CutMatchingGame.exists_gridVertex_fixedRound_exact_list_halfExpander
    with ⟨cRound, hcRound, hstrategy⟩
  refine ⟨cRound, hcRound, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow _hdeg hrounds _hw hcrossbars
  let roundBound := largeCaseRoundBound cRound g
  let hlen : 2 * roundBound ≤ ell :=
    two_mul_largeCaseRoundBound_le_of_two_mul_roundConstant hrounds
  have hlogPos : 0 < Nat.log 2 g :=
    Nat.log_pos (by decide : 1 < 2) hg
  have hroundBoundPos : 0 < roundBound := by
    dsimp [roundBound, largeCaseRoundBound]
    exact Nat.mul_pos hcRound hlogPos
  let responder :=
    transportedSequentialResponder Hsys hcrossbars hlen hroundBoundPos
  rcases hstrategy hg hpow responder with
    ⟨rounds, hroundsLen, hhalf, hfollow⟩
  have hroundsLen' : rounds.length = roundBound := by
    simpa [roundBound, largeCaseRoundBound] using hroundsLen
  let cuts : Fin roundBound → CutMatchingGame.Bisection (GridVertex g) :=
    fun r => (rounds.get (Fin.cast hroundsLen'.symm r)).cut
  refine ⟨fun r => (cuts r).left, fun r => (cuts r).right,
    fun r => (cuts r).disjoint, fun r => (cuts r).card_eq, ?_, ?_⟩
  · intro r
    exact (cuts r).cover
  · let F :=
      SelectedOddLocalCrossbarGridTransportedRoundFamily.abstractFinRoundFamilyOfBisections
          Hsys hcrossbars hlen
          (le_rfl : roundBound ≤ roundBound) cuts
    have hget :
        ∀ r : Fin roundBound,
          F.lazyRound r = rounds.get (Fin.cast hroundsLen'.symm r) := by
      intro r
      let iRound : Fin rounds.length := Fin.cast hroundsLen'.symm r
      have hgetSome :
          rounds[iRound.1]? = some (rounds.get iRound) := by
        rw [List.get_eq_getElem]
        exact List.getElem?_eq_getElem iRound.2
      have hresp := hfollow iRound.1 (rounds.get iRound) hgetSome
      have hidx : iRound.1 = r.1 := by
        simp [iRound]
      have hresp' :
          rounds.get iRound =
            CutMatchingGame.LazyRound.ofResponder responder r.1 (cuts r) := by
        simpa [cuts, hidx] using hresp
      have hlt : r.1 < roundBound := r.2
      have hFresp :
          F.lazyRound r =
            CutMatchingGame.LazyRound.ofResponder responder r.1 (cuts r) := by
        have hcluster :
            SelectedOddLocalCrossbarGridTransportedRoundFamily.finCluster
              (le_rfl : roundBound ≤ roundBound) r =
              (⟨r.1, hlt⟩ : Fin roundBound) := by
          apply Fin.ext
          rfl
        apply CutMatchingGame.LazyRound.ext
        · simp [F,
            SelectedOddLocalCrossbarGridTransportedRoundFamily.abstractFinRoundFamilyOfBisections,
            CutMatchingGame.RoundFamily.lazyRound,
            CutMatchingGame.LazyRound.ofResponder]
        · dsimp [F,
            SelectedOddLocalCrossbarGridTransportedRoundFamily.abstractFinRoundFamilyOfBisections,
            CutMatchingGame.RoundFamily.lazyRound,
            CutMatchingGame.LazyRound.ofResponder,
            responder, transportedSequentialResponder]
          simp [hlt]
          rw [hcluster]
      exact hFresp.trans hresp'.symm
    have htoList : F.toFinList = rounds := by
      apply List.ext_get
      · rw [CutMatchingGame.RoundFamily.length_toFinList, hroundsLen']
      · intro n hF hR
        have hrb : n < roundBound := by
          rw [← hroundsLen']
          exact hR
        let r : Fin roundBound := ⟨n, hrb⟩
        have hcast :
            Fin.cast hroundsLen'.symm r = (⟨n, hR⟩ : Fin rounds.length) := by
          apply Fin.ext
          simp [r]
        have hround := hget r
        have hleft :
            F.toFinList.get ⟨n, hF⟩ = F.lazyRound r := by
          dsimp [CutMatchingGame.RoundFamily.toFinList]
          simp [r]
        rw [hleft, hround, hcast]
    have hfin : F.IsHalfEdgeExpander :=
      F.isHalfEdgeExpander_of_toFinList (by
        simpa [htoList] using hhalf)
    exact
      SelectedOddLocalCrossbarGridTransportedRoundFamily.ofFinBisections_isHalfEdgeExpander_of_abstractFinRoundFamily
          Hsys hcrossbars hlen
          (le_rfl : roundBound ≤ roundBound) cuts hfin

/-- Direct proved version of the cut-matching-game contract statement:
there is a universal `O(log g)` round constant such that the cut player can
choose full bisections of `GridVertex g` whose transported local-crossbar
matching union is a half-edge-expander. -/
theorem exists_bisection_strategy_transported_matchings_half_expander :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                (hrounds : (2 * cRound) * Nat.log 2 g ≤ ell) →
                  g ^ 2 ≤ w →
                    (hcrossbars :
                      ∀ i : Fin ell, OneBasedOdd i →
                        Nonempty (Crossbar (Hsys.hairLocalGraph i)
                          (Hsys.base.left i) (Hsys.base.right i)
                          (Hsys.y i) (g ^ 2))) →
                      ∃ U W :
                          Fin (largeCaseRoundBound cRound g) →
                            Finset (GridVertex g),
                        ∃ hdisj : ∀ r : Fin (largeCaseRoundBound cRound g),
                            Disjoint (U r) (W r),
                          ∃ hcard :
                              ∀ r : Fin (largeCaseRoundBound cRound g),
                                (U r).card = (W r).card,
                            (∀ r : Fin (largeCaseRoundBound cRound g),
                                U r ∪ W r = Finset.univ) ∧
                              (SelectedOddLocalCrossbarGridTransportedRoundFamily.ofFinCuts
                                Hsys hcrossbars
                                  (two_mul_largeCaseRoundBound_le_of_two_mul_roundConstant
                                    hrounds)
                                  (le_rfl :
                                    largeCaseRoundBound cRound g ≤
                                      largeCaseRoundBound cRound g)
                                  U W hdisj hcard).IsHalfEdgeExpander := by
  rcases exists_fixedRoundCutMatchingUnbundledProvider.{u} with
    ⟨cRound, hcRound, hprovider⟩
  exact ⟨cRound, hcRound, hprovider⟩

/-- Combining the cut-matching-game upper bound with the already formalized
explicit Theorem 8.1 target-size arithmetic gives the fixed-round expander
data provider used by the crossbar-grid assembly. -/
theorem exists_fixedRoundLargeCaseExpanderDataProvider_of_cutMatchingGame :
    ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
      FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale := by
  rcases exists_fixedRoundCutMatchingUnbundledProvider.{u} with
    ⟨cRound, hcRound, hcutMatching⟩
  exact exists_fixedRoundLargeCaseExpanderDataProvider_of_unbundled_and_target
    ⟨cRound, fixedRoundExpanderTargetScale cRound,
      hcRound, fixedRoundExpanderTargetScale_pos cRound,
      hcutMatching, fixedRoundExpanderTargetProvider_explicit cRound⟩

/-- Crossbar-grid assembly with the large case supplied by the
cut-matching-game theorem rather than by the old large-case contract. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_cutMatchingGame :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                c * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    (∀ i : Fin ell, OneBasedOdd i →
                      Nonempty (Crossbar (Hsys.hairLocalGraph i)
                        (Hsys.base.left i) (Hsys.base.right i)
                        (Hsys.y i) (g ^ 2))) →
                      ∃ g' : ℕ,
                        g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g' :=
  exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_fixedRoundExpanderDataProvider
    exists_fixedRoundLargeCaseExpanderDataProvider_of_cutMatchingGame

end HairyCrossbarGrid
end SimpleGraph

end Lax17Proofs
