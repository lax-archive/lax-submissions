import Lax17Proofs.Source.Exponent8.LastHitCrossbar

namespace Lax17Proofs

/-!
# A strengthened Chuzhoy--Tan Claim 5.3

Chuzhoy--Tan Claim 5.3 discards every auxiliary path meeting a bad row
segment.  The printed greedy charging argument loses `O(g^6)` paths.  The
last-hit crossbar construction charges each discarded path to the row
containing its *last* bad-segment intersection.  Consequently, if every bad
row meets at most `d` localized auxiliary paths and there is no width-`r`
crossbar, fewer than `d * r` paths are discarded.

For the parameters used in Section 5, `d = 4 * g^2` and `r = g^2`, so the
loss is strictly less than `4 * g^4`.  The retained-family statement below is
division-free and records the slightly weaker but compositional inequality

`|Qset| <= |Qgood| + 4 * g^4`.

This module is experimental exponent-eight work.  It does not alter the
degree-ten endpoint.
-/

namespace SimpleGraph
namespace Exponent8
namespace SliceLocalizationInvariant

universe u v

variable
    {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {M : ℕ} {sigma : PathSlicing Rbar M} {i : Fin M}

/-- The localized auxiliary paths retained after deleting every path that
meets one of the selected bad row segments. -/
noncomputable def goodQ
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index) :
    Finset Qbar.Index :=
  Qset \ L.badHitQ bad Qset

theorem goodQ_subset
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index) :
    L.goodQ bad Qset ⊆ Qset :=
  Finset.sdiff_subset

theorem badHitQ_subset
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index) :
    L.badHitQ bad Qset ⊆ Qset := by
  classical
  intro q hq
  exact ((L.mem_badHitQ bad Qset q).1 hq).1

/-- Contrapositive last-hit count: without a width-`r` crossbar, the family
of localized paths meeting bad row segments has cardinality strictly below
`d * r`. -/
theorem badHitQ_card_lt_of_no_crossbar
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (d r : ℕ)
    (hd : 0 < d)
    (hQset : Qset ⊆ L.localizedQ)
    (hcap : ∀ b ∈ bad, (L.hitQAt Qset b).card ≤ d)
    (hnoCrossbar : ¬ Nonempty (Crossbar G A B X r)) :
    (L.badHitQ bad Qset).card < d * r := by
  by_contra hnot
  exact hnoCrossbar
    (L.lastHitCrossbar_direct bad Qset d r hd hQset hcap
      (Nat.le_of_not_gt hnot))

/-- Division-free retention form of strengthened Claim 5.3.  The strict loss
bound above implies this closed inequality, which is the useful form for
recursive arithmetic. -/
theorem claim53Strong
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (d r : ℕ)
    (hd : 0 < d)
    (hQset : Qset ⊆ L.localizedQ)
    (hcap : ∀ b ∈ bad, (L.hitQAt Qset b).card ≤ d)
    (hnoCrossbar : ¬ Nonempty (Crossbar G A B X r)) :
    Qset.card ≤ (L.goodQ bad Qset).card + d * r := by
  classical
  have hbad_lt :
      (L.badHitQ bad Qset).card < d * r :=
    L.badHitQ_card_lt_of_no_crossbar
      bad Qset d r hd hQset hcap hnoCrossbar
  have hsplit :
      Qset.card =
        (L.goodQ bad Qset).card + (L.badHitQ bad Qset).card := by
    have h :=
      Finset.card_sdiff_add_card_eq_card (L.badHitQ_subset bad Qset)
    simpa [goodQ] using h.symm
  omega

/-- The Section 5 specialization: each bad row segment meets at most
`4 * g^2` localized auxiliary paths, while the forbidden crossbar has width
`g^2`.  Hence strictly fewer than `4 * g^4` paths are bad. -/
theorem badHitQ_card_lt_four_mul_g_pow_four
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (g : ℕ)
    (hg : 0 < g)
    (hQset : Qset ⊆ L.localizedQ)
    (hcap :
      ∀ b ∈ bad, (L.hitQAt Qset b).card ≤ 4 * g ^ 2)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    (L.badHitQ bad Qset).card < 4 * g ^ 4 := by
  have hd : 0 < 4 * g ^ 2 := by positivity
  have h :=
    L.badHitQ_card_lt_of_no_crossbar
      bad Qset (4 * g ^ 2) (g ^ 2)
      hd hQset hcap hnoCrossbar
  nlinarith [h]

/-- Exact `O(g^4)` retained-family form of strengthened Claim 5.3. -/
theorem claim53Strong_four_mul_g_pow_four
    (L : SliceLocalizationInvariant G H A B X P Q Rbar Qbar sigma i)
    (bad : Finset Rbar.Index) (Qset : Finset Qbar.Index)
    (g : ℕ)
    (hg : 0 < g)
    (hQset : Qset ⊆ L.localizedQ)
    (hcap :
      ∀ b ∈ bad, (L.hitQAt Qset b).card ≤ 4 * g ^ 2)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    Qset.card ≤ (L.goodQ bad Qset).card + 4 * g ^ 4 := by
  have hd : 0 < 4 * g ^ 2 := by positivity
  have h :=
    L.claim53Strong
      bad Qset (4 * g ^ 2) (g ^ 2)
      hd hQset hcap hnoCrossbar
  nlinarith [h]

end SliceLocalizationInvariant
end Exponent8
end SimpleGraph

end Lax17Proofs
