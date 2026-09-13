import Lax17Proofs.Source.CrossbarContract
import Lax17Proofs.Source.PathOfSetsGrid
import Lax17Proofs.Source.Section45
import Lax17Proofs.Source.Section46
import Lax17Proofs.Source.Theorem41

namespace Lax17Proofs

universe u v w

/-!
# Crossbar dichotomy theorem

This module exposes the Chuzhoy--Tan crossbar dichotomy outside the contract
namespace.  It keeps the contract-backed Theorem 3.1 statement available, and
also provides the Section 4 `g^10 log g` route from the formal Theorem 4.1
proof plus explicit proof-facing inputs for the remaining pseudo-grid branch.
-/

namespace SimpleGraph

namespace CrossbarContract

/-- The strong-path-of-sets-minor outcome is monotone under adding edges to the
host graph. -/
theorem HasStrongPathOfSetsMinor.mono {V : Type u} [DecidableEq V]
    {G G' : _root_.SimpleGraph V} {ell w : ℕ}
    (h : HasStrongPathOfSetsMinor G ell w) (hGG' : G ≤ G') :
    HasStrongPathOfSetsMinor G' ell w := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, hsystem⟩
  exact ⟨W, hWfin, hWdec, H, hminor.mono hGG', hsystem⟩

/-- The strong-path-of-sets-minor outcome transfers forward through an
arbitrary graph-minor relation. -/
theorem HasStrongPathOfSetsMinor.of_minor {W V : Type u}
    [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V} {ell w : ℕ}
    (h : HasStrongPathOfSetsMinor H ell w) (hminor : IsMinor H G) :
    HasStrongPathOfSetsMinor G ell w := by
  rcases h with ⟨U, hUfin, hUdec, F, hFH, hsystem⟩
  exact ⟨U, hUfin, hUdec, F, hFH.trans hminor, hsystem⟩

/-- The strong-path-of-sets-minor outcome is invariant under relabeling the
host graph. -/
theorem HasStrongPathOfSetsMinor.of_iso {V V' : Type u}
    [DecidableEq V] [DecidableEq V']
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'} {ell w : ℕ}
    (e : G ≃g G') (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G' ell w := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, hsystem⟩
  exact ⟨W, hWfin, hWdec, H, hminor.of_iso_right e, hsystem⟩

/-- Thin only the length of the strong path-of-sets system carried by a minor. -/
theorem HasStrongPathOfSetsMinor.restrictLength {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w ell' : ℕ}
    (hell_pos : 0 < ell') (hell : ell' ≤ ell)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G ell' w := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, hWfin, hWdec, H, hminor,
    ⟨Hsys.restrictLength hell_pos hell⟩⟩

/-- Thin only the width of the strong path-of-sets system carried by a minor. -/
theorem HasStrongPathOfSetsMinor.restrictWidth {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w w' : ℕ}
    (hw_pos : 0 < w') (hw : w' ≤ w)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G ell w' := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, hWfin, hWdec, H, hminor,
    ⟨Hsys.restrictWidth hw_pos hw⟩⟩

/-- Simultaneously thin the length and width of the strong path-of-sets system
carried by a minor. -/
theorem HasStrongPathOfSetsMinor.restrict {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w ell' w' : ℕ}
    (hell_pos : 0 < ell') (hw_pos : 0 < w')
    (hell : ell' ≤ ell) (hw : w' ≤ w)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G ell' w' := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, hWfin, hWdec, H, hminor,
    ⟨Hsys.restrict hell_pos hw_pos hell hw⟩⟩

/-- Thin the strong path-of-sets system carried by a minor to an exact square
length and width. -/
theorem HasStrongPathOfSetsMinor.restrictSquare {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (hg : 2 ≤ g) (hell : g ^ 2 ≤ ell) (hw : g ^ 2 ≤ w)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G (g ^ 2) (g ^ 2) := by
  exact h.restrict
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    hell hw



/-- The exact strong-path-of-sets-minor outcome gives a grid minor, using
Chekuri--Chuzhoy Corollary 3.2 as an explicit input. -/
theorem HasStrongPathOfSetsMinor.exists_gridMinor_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {g : ℕ},
          2 ≤ g →
            HasStrongPathOfSetsMinor G (g ^ 2) (g ^ 2) →
              ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases
    PathOfSetsGrid.exists_gridMinor_of_strong_pathOfSets_minor_of_corollary32Input
      hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G g hg hminor
  rcases hminor with ⟨W, hWfin, hWdec, H, hHG, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact hgrid H G hg hHG Hsys

/-- The strong Path-of-Sets minor outcome contains a grid minor whenever its
length and width dominate the square of the requested path-of-sets parameter,
using Chekuri--Chuzhoy Corollary 3.2 as an explicit input. -/
theorem HasStrongPathOfSetsMinor.exists_gridMinor_of_large_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                HasStrongPathOfSetsMinor G ell w →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases HasStrongPathOfSetsMinor.exists_gridMinor_of_corollary32Input hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g hg hell hw hminor
  exact hgrid hg (hminor.restrictSquare hg hell hw)

end CrossbarContract

namespace CrossbarTheorem


/-- The weaker Section 4 crossbar threshold is above the Theorem 3.1
threshold for every relevant grid order. -/
theorem crossbar_threshold_degree9_le_degree10 {g : ℕ} (hg : 2 ≤ g) :
    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤
      2 ^ 22 * g ^ 10 * Nat.log 2 g := by
  have hgpos : 0 < g := lt_of_lt_of_le (by decide : 0 < 2) hg
  have hpow : g ^ 9 ≤ g ^ 10 :=
    Nat.pow_le_pow_right hgpos (by decide : 9 ≤ 10)
  calc
    2 ^ 22 * g ^ 9 * Nat.log 2 g
        ≤ 2 ^ 22 * g ^ 10 * Nat.log 2 g :=
          Nat.mul_le_mul_right (Nat.log 2 g)
            (Nat.mul_le_mul_left (2 ^ 22) hpow)

/-- The Section 4 terminal threshold is large enough to run Theorem 4.1 at
the depth `D = 64 * g^4` used by Sections 4.2--4.6. -/
theorem depth64_le_kappa_div_two_mul_g_sq_of_crossbar_threshold_degree10
    {g kappa : ℕ} (hg : 2 ≤ g)
    (hlarge : 2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa) :
    64 * g ^ 4 ≤ kappa / (2 * g ^ 2) := by
  have hgpos : 0 < g := lt_of_lt_of_le (by decide : 0 < 2) hg
  have hden_pos : 0 < 2 * g ^ 2 := by positivity
  rw [Nat.le_div_iff_mul_le hden_pos]
  have hlog_pos : 0 < Nat.log 2 g := by
    rw [Nat.log_pos_iff]
    exact ⟨hg, (by decide : 1 < 2)⟩
  have hlog : 1 ≤ Nat.log 2 g := Nat.succ_le_of_lt hlog_pos
  have hpow : g ^ 6 ≤ g ^ 10 :=
    Nat.pow_le_pow_right hgpos (by decide : 6 ≤ 10)
  have hcoeff : 128 ≤ 2 ^ 22 := by decide
  have hbase : 128 * g ^ 6 ≤ 2 ^ 22 * g ^ 10 := by
    calc
      128 * g ^ 6 ≤ 2 ^ 22 * g ^ 6 :=
        Nat.mul_le_mul_right (g ^ 6) hcoeff
      _ ≤ 2 ^ 22 * g ^ 10 :=
        Nat.mul_le_mul_left (2 ^ 22) hpow
  calc
    (64 * g ^ 4) * (2 * g ^ 2) = 128 * g ^ 6 := by ring
    _ ≤ 2 ^ 22 * g ^ 10 := hbase
    _ ≤ 2 ^ 22 * g ^ 10 * Nat.log 2 g := by
      calc
        2 ^ 22 * g ^ 10 = 2 ^ 22 * g ^ 10 * 1 := by simp
        _ ≤ 2 ^ 22 * g ^ 10 * Nat.log 2 g :=
          Nat.mul_le_mul_left (2 ^ 22 * g ^ 10) hlog
    _ ≤ kappa := hlarge

/-- The remaining Section 4 branch after Theorem 4.1 finds a pseudo-grid.

Sections 4.2--4.6 of Chuzhoy--Tan prove this input from the pseudo-grid:
slicing, weak-cluster extraction, weak path-of-sets assembly, and
strongification.  The formal statement keeps that branch separate from
Theorem 4.1 so the `g^10 log g` crossbar dichotomy can be derived without
appealing to the stronger Theorem 3.1 contract. -/
def Section4PseudoGridBranchInput10 (c : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {H : _root_.SimpleGraph V} {A B X : Finset V}
    {g kappa : ℕ}
    {P : PerfectPathPacking H A B} {Q : PerfectPathPacking H A X},
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          Disjoint A B →
            Disjoint A X →
              Disjoint B X →
                (∀ x ∈ X, DegreeEquals H x 1) →
          2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa →
            P.card = kappa →
              Q.card = kappa →
                P.IsMinimumTheorem41Pair Q →
                  Nonempty (PseudoGrid H A B X g (64 * g ^ 4) P Q) →
                    ∃ ell w : ℕ,
                      g ^ 2 ≤ c * ell ∧
                        g ^ 2 ≤ c * w ∧
                          CrossbarContract.HasStrongPathOfSetsMinor H ell w

/-- Proof-facing Section 4 branch input after reducing the pseudo-grid branch
to the formalized Section 4.5 and Section 4.6 assembly steps.

For the depth-`64 * g^4` pseudo-grid used in the paper, this input asks for a
minor in which Section 4.5 can assemble a weak path-of-sets system of length
and width `ell`, together with Section 4.6 strongification data of retained
width `w`.  The theorem below checks that these concrete data imply the older
branch input which directly asked for the resulting strong path-of-sets minor. -/
def Section4WeakToStrongAssemblyInput10 (c : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {H : _root_.SimpleGraph V} {A B X : Finset V}
    {g kappa : ℕ}
    {P : PerfectPathPacking H A B} {Q : PerfectPathPacking H A X},
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          Disjoint A B →
            Disjoint A X →
              Disjoint B X →
                (∀ x ∈ X, DegreeEquals H x 1) →
          2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa →
            P.card = kappa →
              Q.card = kappa →
                P.IsMinimumTheorem41Pair Q →
                  (Gamma : PseudoGrid H A B X g (64 * g ^ 4) P Q) →
                    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
                      (J : _root_.SimpleGraph W) (N M Dhat ell w : ℕ),
                        IsMinor J H ∧
                          g ^ 2 ≤ c * ell ∧
                            g ^ 2 ≤ c * w ∧
                              (∃ _weakInput :
                                Section45.Section45Input J N M Dhat ell,
                                (∀ Pweak : WeakPathOfSetsSystem J ell ell,
                                  Nonempty
                                    (Section46.StrongificationData
                                      (G := J)
                                      (P := Pweak.toPathOfSetsSystem)
                                      (w' := w))))

/-- Section 4.5 weak assembly plus Section 4.6 strongification data imply the
pseudo-grid branch input used by the self-contained `g^10 log g` crossbar
dichotomy. -/
theorem section4PseudoGridBranchInput10_of_weakToStrongAssemblyInput10
    {c : ℕ} (hinput : Section4WeakToStrongAssemblyInput10.{u} c) :
    Section4PseudoGridBranchInput10.{u} c := by
  intro V _ _ H A B X g kappa P Q hg hpow hAB hAX hBX hdegree hlarge
    hPcard hQcard hminimum hpseudo
  rcases hpseudo with ⟨Gamma⟩
  rcases hinput hg hpow hAB hAX hBX hdegree hlarge hPcard hQcard hminimum
      Gamma with
    ⟨W, hWfin, hWdec, J, N, M, Dhat, ell, w,
      hminor, hell, hw, hweakInput, hstrongify⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  rcases Section45.section45_weak_pathOfSetsSystem hweakInput with ⟨Pweak⟩
  rcases hstrongify Pweak with ⟨Dstrong⟩
  refine ⟨ell, w, hell, hw, ?_⟩
  refine ⟨W, hWfin, hWdec, J, hminor, ?_⟩
  exact ⟨Section46.strong_pathOfSetsSystem_of_strongificationData
    Pweak Dstrong⟩



/-- Section 4 crossbar dichotomy from the self-contained Theorem 4.1 proof
and an explicit pseudo-grid branch input for Sections 4.2--4.6.

Unlike `crossbar_or_strong_pathOfSets_minor_degree10`, this theorem does not
derive the weaker `g^10 log g` statement from the stronger Theorem 3.1
contract. -/
theorem crossbar_or_strong_pathOfSets_minor_degree10_of_section4PseudoGridBranchInput
    {c : ℕ} (hc : 0 < c)
    (hbranch : Section4PseudoGridBranchInput10.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (H : _root_.SimpleGraph V) {g kappa : ℕ}
        {A B X : Finset V},
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              A.card = kappa →
                B.card = kappa →
                  X.card = kappa →
                    Disjoint A B →
                      Disjoint A X →
                        Disjoint B X →
                          2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa →
                            (∀ x ∈ X, DegreeEquals H x 1) →
                              (Pab : PathPacking H A B) →
                                Pab.card = kappa →
                                  (Pax : PathPacking H A X) →
                                    Pax.card = kappa →
                                      Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                        ∃ ell w : ℕ,
                                          g ^ 2 ≤ c * ell ∧
                                            g ^ 2 ≤ c * w ∧
                                              CrossbarContract.HasStrongPathOfSetsMinor H ell w := by
  refine ⟨c, hc, ?_⟩
  intro V _ _ H g kappa A B X hg hpow hA hB hX hAB hAX hBX hlarge10
    hdeg Pab hPab Pax hPax
  have hDpos : 1 ≤ 64 * g ^ 4 := by
    have : 0 < 64 * g ^ 4 := by positivity
    exact this
  have hDle : 64 * g ^ 4 ≤ kappa / (2 * g ^ 2) :=
    depth64_le_kappa_div_two_mul_g_sq_of_crossbar_threshold_degree10
      hg hlarge10
  rcases theorem_four_one_of_pathPackings H hg hpow hA hB hX
      hAB hAX hBX hdeg Pab hPab Pax hPax
      hDpos hDle with
    ⟨P, Q, hPcard, hQcard, hminimum, hconclusion⟩
  rcases hconclusion with hcross | hpseudo
  · exact Or.inl hcross
  · exact Or.inr
      (hbranch hg hpow hAB hAX hBX hdeg hlarge10 hPcard hQcard hminimum
        hpseudo)

/-- Section 4 crossbar dichotomy from Theorem 4.1 and the concrete Section
4.5/4.6 weak-to-strong assembly input. -/
theorem crossbar_or_strong_pathOfSets_minor_degree10_of_weakToStrongAssemblyInput
    {c : ℕ} (hc : 0 < c)
    (hbranch : Section4WeakToStrongAssemblyInput10.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (H : _root_.SimpleGraph V) {g kappa : ℕ}
        {A B X : Finset V},
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              A.card = kappa →
                B.card = kappa →
                  X.card = kappa →
                    Disjoint A B →
                      Disjoint A X →
                        Disjoint B X →
                          2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa →
                            (∀ x ∈ X, DegreeEquals H x 1) →
                              (Pab : PathPacking H A B) →
                                Pab.card = kappa →
                                  (Pax : PathPacking H A X) →
                                    Pax.card = kappa →
                                      Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                        ∃ ell w : ℕ,
                                          g ^ 2 ≤ c * ell ∧
                                            g ^ 2 ≤ c * w ∧
                                              CrossbarContract.HasStrongPathOfSetsMinor H ell w :=
  crossbar_or_strong_pathOfSets_minor_degree10_of_section4PseudoGridBranchInput
    hc
    (section4PseudoGridBranchInput10_of_weakToStrongAssemblyInput10
      hbranch)

end CrossbarTheorem
end SimpleGraph

end Lax17Proofs
