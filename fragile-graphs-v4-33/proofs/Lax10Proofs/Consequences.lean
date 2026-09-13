import Lax10Proofs.Theorem3

/-!
# Consequences of Theorem 3

This file proves the public consequences that do not require opening the
separator induction.  The only paper-level input used here is
$theorem3_mfragile$.
-/

namespace Lax10Proofs

universe u

/-- The colorability corollary extracted from Theorem 3. -/
theorem mfragile_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hfrag : MFragile m G) :
    KColorable m G := by
  classical
  rcases subsingleton_or_nontrivial V with hsub | hnontriv
  · have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
    refine ⟨{ color := fun _ => ⟨0, hm_pos⟩, valid := ?_ }⟩
    intro x y hxy hcolor
    have hxy_eq : x = y := hsub.elim x y
    subst y
    exact G.irrefl hxy
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    obtain ⟨c, _hc⟩ := (theorem3_mfragile m G hm hfrag).c2 hxy
    exact ⟨c⟩

/--
Theorem 2, contrapositive form: a graph that is not $m$-colorable has a
3-connected subgraph that is not $(m - 1)$-colorable.
-/
theorem theorem2_contra {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hnot : ¬ KColorable m G) :
    ∃ H : G.Subgraph, ThreeConnected H.coe ∧ ¬ KColorable (m - 1) H.coe := by
  classical
  by_contra hnone
  apply hnot
  exact mfragile_colorable m G hm fun H hHconn => by
    by_contra hHnot
    exact hnone ⟨H, hHconn, hHnot⟩

/--
Theorem 2 in chromatic-number wording, using mathlib's $chromaticNumber$ API:
if $χ(G) ≥ m + 1$, then some 3-connected subgraph has chromatic number at least $m$.
-/
theorem theorem2 {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hchi : ((m + 1 : Nat) : ℕ∞) ≤ G.chromaticNumber) :
    ∃ H : G.Subgraph, ThreeConnected H.coe ∧ (m : ℕ∞) ≤ H.coe.chromaticNumber := by
  have hnot : ¬ KColorable m G := by
    intro hcolor
    have hmath : G.Colorable m := kColorable_iff_mathlib_colorable.mp hcolor
    have hm_lt_succ : (m : ℕ∞) < ((m + 1 : Nat) : ℕ∞) := by
      rw [ENat.coe_lt_coe]
      exact Nat.lt_succ_self m
    exact (not_lt_of_ge hchi) (lt_of_le_of_lt hmath.chromaticNumber_le hm_lt_succ)
  obtain ⟨H, hHconn, hHnot⟩ := theorem2_contra m G hm hnot
  refine ⟨H, hHconn, ?_⟩
  have hlt : ((m - 1 : Nat) : ℕ∞) < H.coe.chromaticNumber := by
    exact lt_of_not_ge fun hle =>
      hHnot (kColorable_iff_mathlib_colorable.mpr
        (SimpleGraph.chromaticNumber_le_iff_colorable.mp hle))
  have hle_succ : ((m - 1 : Nat) : ℕ∞) + 1 ≤ H.coe.chromaticNumber :=
    (ENat.add_one_le_iff (by simp)).mpr hlt
  have hcast : ((m - 1 : Nat) : ℕ∞) + 1 = (m : ℕ∞) := by
    have h1m : 1 ≤ m := le_trans (by decide : 1 ≤ 4) hm
    rw [← ENat.coe_one, ← ENat.coe_add, Nat.sub_add_cancel h1m]
  exact hcast ▸ hle_succ

/-- Main corollary: graphs with no 3-connected subgraph are 4-colorable. -/
theorem fragile_four_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfragile : HasNoThreeConnectedSubgraph G) :
    KColorable 4 G :=
  mfragile_colorable 4 G (by decide) fun H hH =>
    False.elim (hfragile H hH)

end Lax10Proofs
