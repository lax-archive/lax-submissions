import Lax17Proofs.Source.TreeOfSetsSourceSharpStrongification

namespace Lax17Proofs

universe u v w

/-!
# A cleared-width form of source-sharp strongification

The source-sharp strongification theorem exposes the two grouping passes and
all seven intermediate widths.  This file fixes conservative integral values
for those widths.  The resulting single premise has order
`alphaDen^2 * Delta^4 * W`, which is the `m^4` loss used in the Section 4
exponent count when `alphaDen` has order `m^2 polylog`.
-/

namespace SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

namespace BandwidthTreeOfSetsSystem

/-- Conservative ordinary width sufficient for the two source-sharp
strongification passes. -/
def coarseStrongificationWidth (alphaDen Delta W : Nat) : Nat :=
  let carrierWidth1 := 4 * Delta * W
  let groupedWidth1 := 20 * Delta * carrierWidth1
  let passWidth := 3 * alphaDen * groupedWidth1
  let carrierWidth0 := 4 * Delta * passWidth
  let groupedWidth0 := 20 * Delta * carrierWidth0
  3 * alphaDen * groupedWidth0

theorem coarseStrongificationWidth_eq
    (alphaDen Delta W : Nat) :
    coarseStrongificationWidth alphaDen Delta W =
      57600 * alphaDen ^ 2 * Delta ^ 4 * W := by
  simp only [coarseStrongificationWidth]
  ring

theorem coarseStrongificationWidth_pos
    {alphaDen Delta W : Nat}
    (hden : 0 < alphaDen) (hDelta : 0 < Delta) (hW : 0 < W) :
    0 < coarseStrongificationWidth alphaDen Delta W := by
  simp only [coarseStrongificationWidth]
  positivity

/-- A bandwidth tree whose width dominates
`coarseStrongificationWidth alphaDen Delta W` has a strong width-`W`
restriction. -/
theorem exists_strongTreeOfSetsSystem_of_coarse_width_with_same_clusters
    {m w alphaDen Delta W : Nat}
    (T : BandwidthTreeOfSetsSystem G m w 1 alphaDen)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hden : 0 < alphaDen)
    (hW : 0 < W)
    (hwidth : coarseStrongificationWidth alphaDen Delta W ≤ w) :
    ∃ S : StrongTreeOfSetsSystem G m W,
      ∀ i : Fin m, S.cluster i = T.cluster i := by
  let carrierWidth1 := 4 * Delta * W
  let groupedWidth1 := 20 * Delta * carrierWidth1
  let passWidth := 3 * alphaDen * groupedWidth1
  let carrierWidth0 := 4 * Delta * passWidth
  let groupedWidth0 := 20 * Delta * carrierWidth0
  have hDeltaPos : 0 < Delta := by omega
  have hcoarse :
      3 * alphaDen * groupedWidth0 =
        coarseStrongificationWidth alphaDen Delta W := by
    rfl
  have hden_le_w : alphaDen ≤ w := by
    calc
      alphaDen = alphaDen * 1 := by simp
      _ ≤ alphaDen * (3 * groupedWidth0) := by
        apply Nat.mul_le_mul_left
        have hgroupedPos : 0 < groupedWidth0 := by
          dsimp [groupedWidth0, carrierWidth0, passWidth,
            groupedWidth1, carrierWidth1]
          positivity
        omega
      _ = 3 * alphaDen * groupedWidth0 := by ring
      _ = coarseStrongificationWidth alphaDen Delta W := hcoarse
      _ ≤ w := hwidth
  have hgroup0 :
      groupedWidth0 ≤ w / (3 * alphaDen) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 3 * alphaDen)).2
    calc
      groupedWidth0 * (3 * alphaDen) =
          3 * alphaDen * groupedWidth0 := by ring
      _ = coarseStrongificationWidth alphaDen Delta W := hcoarse
      _ ≤ w := hwidth
  have hextract0 :
      carrierWidth0 ≤ (3 * groupedWidth0) / (20 * Delta) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 20 * Delta)).2
    dsimp [groupedWidth0]
    nlinarith
  have hpass :
      passWidth ≤ carrierWidth0 := by
    dsimp [carrierWidth0]
    have : 1 ≤ 4 * Delta := by omega
    nlinarith
  have hlink0 :
      4 * Delta * passWidth ≤ carrierWidth0 := by
    rfl
  have hden_le_pass : alphaDen ≤ passWidth := by
    dsimp [passWidth]
    have hgroupedPos : 0 < groupedWidth1 := by
      dsimp [groupedWidth1, carrierWidth1]
      positivity
    nlinarith
  have hgroup1 :
      groupedWidth1 ≤ passWidth / (3 * alphaDen) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 3 * alphaDen)).2
    dsimp [passWidth]
    ring_nf
    omega
  have hextract1 :
      carrierWidth1 ≤ (3 * groupedWidth1) / (20 * Delta) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 20 * Delta)).2
    dsimp [groupedWidth1]
    nlinarith
  have hWcarrier : W ≤ carrierWidth1 := by
    dsimp [carrierWidth1]
    have : 1 ≤ 4 * Delta := by omega
    nlinarith
  have hlink1 : 4 * Delta * W ≤ carrierWidth1 := by
    rfl
  exact T.exists_strongTreeOfSetsSystem_of_bandwidth_sourceSharp_with_same_clusters
    hdegree hDelta
    hden hden_le_w (by simp) hgroup0 hextract0 hpass hlink0
    hden hden_le_pass (by simp) hgroup1 hextract1
    hWcarrier hlink1 hW

/-- Compatibility wrapper that forgets the preserved cluster identity. -/
theorem exists_strongTreeOfSetsSystem_of_coarse_width
    {m w alphaDen Delta W : Nat}
    (T : BandwidthTreeOfSetsSystem G m w 1 alphaDen)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 3 ≤ Delta)
    (hden : 0 < alphaDen)
    (hW : 0 < W)
    (hwidth : coarseStrongificationWidth alphaDen Delta W ≤ w) :
    Nonempty (StrongTreeOfSetsSystem G m W) := by
  rcases T.exists_strongTreeOfSetsSystem_of_coarse_width_with_same_clusters
      hdegree hDelta hden hW hwidth with ⟨S, _⟩
  exact ⟨S⟩

end BandwidthTreeOfSetsSystem
end SimpleGraph

end Lax17Proofs
