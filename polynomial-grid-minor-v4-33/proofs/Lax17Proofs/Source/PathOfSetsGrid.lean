import Mathlib.Tactic.Ring
import Lax17Proofs.Source.ChekuriChuzhoy
import Lax17Proofs.Source.MinorTransitivity
import Lax17Proofs.Source.GridMinor

namespace Lax17Proofs

universe u v w


/-!
# Grid minors from strong path-of-sets systems

This file exposes the path-of-sets-to-grid theorem in the form used by
Chuzhoy--Tan.  The proof reduces the `g^2` by `g^2` strong-system statement to
Chekuri--Chuzhoy Corollary 3.3, stated in `ChekuriChuzhoy`.
-/

namespace SimpleGraph
namespace PathOfSetsGrid

/-- A strong path-of-sets system has a nonempty first cluster. -/
theorem first_cluster_nonempty
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w : ℕ}
    (Hsys : StrongPathOfSetsSystem G ell w) :
    (Hsys.cluster ⟨0, Hsys.length_pos⟩).Nonempty := by
  have hleft_nonempty : (Hsys.left ⟨0, Hsys.length_pos⟩).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcard_zero : (Hsys.left ⟨0, Hsys.length_pos⟩).card = 0 := by
      simp [hempty]
    have : w = 0 := by
      exact (Hsys.left_card ⟨0, Hsys.length_pos⟩).symm.trans hcard_zero
    exact Nat.ne_of_gt Hsys.width_pos this
  rcases hleft_nonempty with ⟨v, hv⟩
  exact ⟨v, Hsys.left_subset_cluster ⟨0, Hsys.length_pos⟩ hv⟩

/-- Every strong path-of-sets system contains the `1 x 1` grid as a minor by
using its first connected cluster as the single branch set. -/
theorem containsGridMinor_one_of_strong_pathOfSets
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w : ℕ}
    (Hsys : StrongPathOfSetsSystem G ell w) :
    ContainsGridMinor G 1 := by
  classical
  refine ContainsGridMinor.of_grid_branchSets
    (G := G) (g := 1)
    (fun _ : GridVertex 1 => Hsys.cluster ⟨0, Hsys.length_pos⟩)
    ?nonempty ?connected ?disjoint ?adjacent
  · intro _
    exact first_cluster_nonempty Hsys
  · intro _
    exact Hsys.cluster_connected ⟨0, Hsys.length_pos⟩
  · intro x y hxy
    exact False.elim (hxy (Subsingleton.elim x y))
  · intro x y hxy
    have hloop : (gridGraph 1).Adj x x := by
      have hyx : y = x := Subsingleton.elim y x
      rw [hyx] at hxy
      exact hxy
    haveI := (gridGraph 1).loopless
    exact False.elim (Std.Irrefl.irrefl x hloop)

/-- Small requested grid orders are handled by the `1 x 1` grid minor.  This
is the base branch used before the genuine linear-size grid construction takes
over. -/
theorem exists_gridMinor_of_strong_pathOfSets_of_le_constant
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w c g : ℕ}
    (hg : g ≤ c) (Hsys : StrongPathOfSetsSystem G ell w) :
    ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  refine ⟨1, ?_, containsGridMinor_one_of_strong_pathOfSets Hsys⟩
  simpa using hg


/-- A strong Path-of-Sets System of length and width `g^2` contains a grid
minor of order at least a constant fraction of `g`, using Chekuri--Chuzhoy
Corollary 3.2 as an explicit input.

This is the contract-free version of
`exists_gridMinor_of_strong_pathOfSets`: the proof is the same numerical
reduction to Corollary 3.3, but the Corollary 3.2 dichotomy is supplied as a
hypothesis. -/
theorem exists_gridMinor_of_strong_pathOfSets_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            StrongPathOfSetsSystem G (g ^ 2) (g ^ 2) →
              ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  refine ⟨64, by decide, ?_⟩
  intro V _ _ G g hg Hsys
  by_cases hsmall : g ≤ 64
  · exact ⟨1, by simpa using hsmall,
      containsGridMinor_one_of_strong_pathOfSets Hsys⟩
  · let r := g / 32
    have hg_large : 65 ≤ g := by omega
    have hmul_le_g : 32 * r ≤ g := by
      have hdecomp := Nat.mod_add_div g 32
      omega
    have hr : 2 ≤ r := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 32)]
      omega
    have hbound : g ≤ 64 * r := by
      have hdecomp := Nat.mod_add_div g 32
      have hmod_lt : g % 32 < 32 := Nat.mod_lt _ (by decide : 0 < 32)
      omega
    have hr_sq_le : r ≤ r ^ 2 := by
      simpa using
        (Nat.le_self_pow (a := r) (by decide : (2 : ℕ) ≠ 0))
    have hwidth_scaled : 16 * r ^ 2 + 10 * r ≤ (32 * r) ^ 2 := by
      calc
        16 * r ^ 2 + 10 * r ≤ 16 * r ^ 2 + 10 * r ^ 2 :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 10 hr_sq_le) _
        _ = 26 * r ^ 2 := by ring
        _ ≤ 1024 * r ^ 2 :=
          Nat.mul_le_mul_right (r ^ 2) (by decide : 26 ≤ 1024)
        _ = (32 * r) ^ 2 := by ring
    have hlength_scaled : 2 * r * (r - 1) ≤ (32 * r) ^ 2 := by
      calc
        2 * r * (r - 1) ≤ 2 * r * r :=
          Nat.mul_le_mul_left (2 * r) (Nat.sub_le r 1)
        _ = 2 * r ^ 2 := by ring
        _ ≤ 1024 * r ^ 2 :=
          Nat.mul_le_mul_right (r ^ 2) (by decide : 2 ≤ 1024)
        _ = (32 * r) ^ 2 := by ring
    have hscale_sq : (32 * r) ^ 2 ≤ g ^ 2 :=
      Nat.pow_le_pow_left hmul_le_g 2
    have hwidth : 16 * r ^ 2 + 10 * r ≤ g ^ 2 :=
      le_trans hwidth_scaled hscale_sq
    have hlength : 2 * r * (r - 1) ≤ g ^ 2 :=
      le_trans hlength_scaled hscale_sq
    refine ⟨r, hbound, ?_⟩
    exact ChekuriChuzhoy.containsGridMinor_of_strongPathOfSets_ge_of_corollary32Input
      hinput G hr hlength hwidth Hsys






/-- Minor-closed input-form version of the path-of-sets-to-grid theorem. -/
theorem exists_gridMinor_of_strong_pathOfSets_minor_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            IsMinor H G →
              StrongPathOfSetsSystem H (g ^ 2) (g ^ 2) →
                ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases exists_gridMinor_of_strong_pathOfSets_of_corollary32Input hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro W V _ _ H G g hg hminor Hsys
  rcases hgrid H hg Hsys with ⟨g', hbound, hgridH⟩
  exact ⟨g', hbound, hgridH.of_minor hminor⟩

/-- Path-of-sets-to-grid theorem using the split Chekuri--Chuzhoy inputs:
local routing plus row stitching. -/
theorem exists_gridMinor_of_strong_pathOfSets_of_localRoutingInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            StrongPathOfSetsSystem G (g ^ 2) (g ^ 2) →
              ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_strong_pathOfSets_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)

/-- Minor-closed path-of-sets-to-grid theorem using the split
Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_strong_pathOfSets_minor_of_localRoutingInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            IsMinor H G →
              StrongPathOfSetsSystem H (g ^ 2) (g ^ 2) →
                ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_strong_pathOfSets_minor_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)

/-- Length-monotone input-form version of the path-of-sets-to-grid theorem. -/
theorem exists_gridMinor_of_long_strong_pathOfSets_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              StrongPathOfSetsSystem G ell (g ^ 2) →
                ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases exists_gridMinor_of_strong_pathOfSets_of_corollary32Input hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell g hg hlength Hsys
  have hpos : 0 < g ^ 2 :=
    Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg)
  exact hgrid G hg (Hsys.restrictLength hpos hlength)

/-- Length-monotone path-of-sets-to-grid theorem using the split
Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_long_strong_pathOfSets_of_localRoutingInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              StrongPathOfSetsSystem G ell (g ^ 2) →
                ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_long_strong_pathOfSets_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)

/-- Minor-closed length-monotone input-form version of the
path-of-sets-to-grid theorem. -/
theorem exists_gridMinor_of_long_strong_pathOfSets_minor_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {ell g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              IsMinor H G →
                StrongPathOfSetsSystem H ell (g ^ 2) →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases exists_gridMinor_of_long_strong_pathOfSets_of_corollary32Input hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro W V _ _ H G ell g hg hlength hminor Hsys
  rcases hgrid H hg hlength Hsys with ⟨g', hbound, hgridH⟩
  exact ⟨g', hbound, hgridH.of_minor hminor⟩

/-- Minor-closed length-monotone path-of-sets-to-grid theorem using the split
Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_long_strong_pathOfSets_minor_of_localRoutingInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {ell g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              IsMinor H G →
                StrongPathOfSetsSystem H ell (g ^ 2) →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_long_strong_pathOfSets_minor_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)

/-- Size-monotone input-form version of the path-of-sets-to-grid theorem. -/
theorem exists_gridMinor_of_large_strong_pathOfSets_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                StrongPathOfSetsSystem G ell w →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases exists_gridMinor_of_strong_pathOfSets_of_corollary32Input hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g hg hlength hwidth Hsys
  exact hgrid G hg (Hsys.restrictSquare hg hlength hwidth)

/-- Size-monotone path-of-sets-to-grid theorem using the split
Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_large_strong_pathOfSets_of_localRoutingInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                StrongPathOfSetsSystem G ell w →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_large_strong_pathOfSets_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)

/-- Minor-closed size-monotone input-form version of the
path-of-sets-to-grid theorem. -/
theorem exists_gridMinor_of_large_strong_pathOfSets_minor_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                IsMinor H G →
                  StrongPathOfSetsSystem H ell w →
                    ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases exists_gridMinor_of_large_strong_pathOfSets_of_corollary32Input hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro W V _ _ H G ell w g hg hlength hwidth hminor Hsys
  rcases hgrid H hg hlength hwidth Hsys with ⟨g', hbound, hgridH⟩
  exact ⟨g', hbound, hgridH.of_minor hminor⟩

/-- Minor-closed size-monotone path-of-sets-to-grid theorem using the split
Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_large_strong_pathOfSets_minor_of_localRoutingInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                IsMinor H G →
                  StrongPathOfSetsSystem H ell w →
                    ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_large_strong_pathOfSets_minor_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)

/-- Path-of-sets-to-grid theorem using the cluster-faithful split
Chekuri--Chuzhoy inputs: local routing in connected clusters plus row
stitching. -/
theorem exists_gridMinor_of_strong_pathOfSets_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            StrongPathOfSetsSystem G (g ^ 2) (g ^ 2) →
              ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_strong_pathOfSets_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingClusterInput_and_stitchingInput
      hlocal hstitch)

/-- Minor-closed path-of-sets-to-grid theorem using the cluster-faithful split
Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_strong_pathOfSets_minor_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            IsMinor H G →
              StrongPathOfSetsSystem H (g ^ 2) (g ^ 2) →
                ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_strong_pathOfSets_minor_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingClusterInput_and_stitchingInput
      hlocal hstitch)

/-- Length-monotone path-of-sets-to-grid theorem using the cluster-faithful
split Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_long_strong_pathOfSets_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              StrongPathOfSetsSystem G ell (g ^ 2) →
                ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_long_strong_pathOfSets_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingClusterInput_and_stitchingInput
      hlocal hstitch)

/-- Minor-closed length-monotone path-of-sets-to-grid theorem using the
cluster-faithful split Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_long_strong_pathOfSets_minor_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {ell g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              IsMinor H G →
                StrongPathOfSetsSystem H ell (g ^ 2) →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_long_strong_pathOfSets_minor_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingClusterInput_and_stitchingInput
      hlocal hstitch)

/-- Size-monotone path-of-sets-to-grid theorem using the cluster-faithful split
Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_large_strong_pathOfSets_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                StrongPathOfSetsSystem G ell w →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_large_strong_pathOfSets_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingClusterInput_and_stitchingInput
      hlocal hstitch)

/-- Minor-closed size-monotone path-of-sets-to-grid theorem using the
cluster-faithful split Chekuri--Chuzhoy inputs. -/
theorem exists_gridMinor_of_large_strong_pathOfSets_minor_of_localRoutingClusterInput_and_stitchingInput
    (hlocal : ChekuriChuzhoy.LocalRoutingClusterInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {W V : Type u} [Fintype W] [DecidableEq W]
        (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                IsMinor H G →
                  StrongPathOfSetsSystem H ell w →
                    ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' :=
  exists_gridMinor_of_large_strong_pathOfSets_minor_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingClusterInput_and_stitchingInput
      hlocal hstitch)

end PathOfSetsGrid
end SimpleGraph

end Lax17Proofs
