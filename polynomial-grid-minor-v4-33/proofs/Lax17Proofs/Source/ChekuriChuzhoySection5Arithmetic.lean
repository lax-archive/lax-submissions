import Lax17Proofs.Source.ChekuriChuzhoySection5CoreAssembly

namespace Lax17Proofs

universe u v w

/-!
# Explicit Section 5 parameters

This module fixes all intermediate integer and rational parameters in the
source-sharp Section 5 assembly.  The only remaining numerical obligations are
the source degree cap, the skeleton-flow budget, and the terminal-capacity
budget; these are the three inequalities discharged by the final `m^23`
wrapper.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Arithmetic


open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph

namespace Parameters

def D (Delta : Nat) : Nat := Delta + 3
def n (m : Nat) : Nat := m ^ 2
def alpha (m x : Nat) : Nat :=
  16 * (20 * n m) * (Nat.log 2 x + 1)
def ordinaryWidth (m W x Delta : Nat) : Nat :=
  BandwidthTreeOfSetsSystem.coarseStrongificationWidth
    (alpha m x) (D Delta) W
def longWidth (m W x Delta : Nat) : Nat :=
  (m + 1) * ordinaryWidth m W x Delta
def outWidth (m W x Delta : Nat) : Nat :=
  m ^ 4 * ordinaryWidth m W x Delta
def carrierWidth (m W x Delta : Nat) : Nat :=
  4 * D Delta * outWidth m W x Delta
def groupedWidth (m W x Delta : Nat) : Nat :=
  20 * D Delta * carrierWidth m W x Delta
def groupSize (m x : Nat) : Nat := alpha m x
def q (m W x Delta : Nat) : Nat :=
  3 * groupSize m x * groupedWidth m W x Delta
def replicas (m W x Delta : Nat) : Nat :=
  D Delta * q m W x Delta
def eta (m x : Nat) : Nat :=
  n m + (m - 1) * (alpha m x + n m)
def scaleDen (m x Delta : Nat) : Nat :=
  m * (2 + D Delta * eta m x)
def scale (m x Delta : Nat) : Rat :=
  1 / scaleDen m x Delta
def leafWidth (m W x Delta : Nat) : Nat :=
  replicas m W x Delta * scaleDen m x Delta +
    2 * n m * D Delta * longWidth m W x Delta
def mu (m W x Delta : Nat) : Nat :=
  2 * (n m) ^ 2 * D Delta * leafWidth m W x Delta

end Parameters

open Parameters

/-- All internal Section 5 inequalities follow from the two budgets that
still mention the size `x` of the node-well-linked terminal set. -/
theorem exists_strongTreeOfSetsSystem_of_source_budgets
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (X : Finset V)
    {m W x Delta : Nat}
    (hm : 2 ≤ m) (hW : 0 < W) (hx : 2 ≤ x)
    (hdegree : MaxDegreeAtMost G Delta)
    (hXcard : X.card = x)
    (hXwell : NodeWellLinkedIn G Finset.univ X)
    (hdegreeCap :
      Delta + 1 < claim59SourceDegreeCap x (n m))
    (hmuRoute :
      mu m W x Delta ≤
        (claim59SourceDegreeCap x (n m) / 2) / (8 * D Delta)) :
    Nonempty (StrongTreeOfSetsSystem G m W) := by
  classical
  have hn : 0 < n m := by simp [n]; positivity
  have hD : 0 < D Delta := by simp [D]
  have hlog : 0 < Nat.log 2 x + 1 := by omega
  have halpha : 0 < alpha m x := by
    simp only [alpha]
    positivity
  have hord : 0 < ordinaryWidth m W x Delta :=
    BandwidthTreeOfSetsSystem.coarseStrongificationWidth_pos
      halpha hD hW
  have hlong : 0 < longWidth m W x Delta := by
    simp only [longWidth]
    positivity
  have hscaleDen : 0 < scaleDen m x Delta := by
    simp only [scaleDen]
    positivity
  have hreplicas : 0 < replicas m W x Delta := by
    simp only [replicas, q, groupSize, groupedWidth, carrierWidth, outWidth]
    positivity
  have hleaf : 0 < leafWidth m W x Delta := by
    simp only [leafWidth]
    positivity
  have hmu : 0 < mu m W x Delta := by
    simp only [mu]
    positivity
  have hrouterCap :
      2 * leafWidth m W x Delta ≤
        claim59SourceDegreeCap x (n m) / 2 := by
    have hmuCap :
        mu m W x Delta ≤ claim59SourceDegreeCap x (n m) / 2 :=
      hmuRoute.trans (Nat.div_le_self _ _)
    have hleafMu :
        2 * leafWidth m W x Delta ≤ mu m W x Delta := by
      simp only [mu]
      have hnOne : 1 ≤ n m := hn
      have hDOne : 1 ≤ D Delta := hD
      have hfactor : 1 ≤ n m ^ 2 * D Delta := by
        exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc
        2 * leafWidth m W x Delta =
            2 * 1 * leafWidth m W x Delta := by ring
        _ ≤ 2 * (n m ^ 2 * D Delta) * leafWidth m W x Delta := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hfactor)
        _ = 2 * n m ^ 2 * D Delta * leafWidth m W x Delta := by ring
    exact hleafMu.trans hmuCap
  apply ChekuriChuzhoySection5CoreAssembly.exists_strongTreeOfSetsSystem_of_parameters
      G X (m := m) (W := W) (n := n m) (cap := x)
      (longWidth := longWidth m W x Delta)
      (leafWidth := leafWidth m W x Delta)
      (mu := mu m W x Delta) (eta := eta m x)
      (replicas := replicas m W x Delta) (q := q m W x Delta)
      (groupSize := groupSize m x)
      (groupedWidth := groupedWidth m W x Delta)
      (carrierWidth := carrierWidth m W x Delta)
      (outWidth := outWidth m W x Delta)
      (ordinaryWidth := ordinaryWidth m W x Delta)
      (Delta := Delta) (c := scale m x Delta)
  · exact hm
  · exact hW
  · exact hn
  · simp [n]
  · exact hdegree
  · simpa [hXcard] using hx
  · exact hXwell
  · simpa [hXcard, n] using hdegreeCap
  · omega
  · simpa [hXcard, n] using
      (Nat.div_le_self x (192 * n m ^ 3 * Nat.log 2 x))
  · exact hmu
  · simpa [hXcard, D, n] using hmuRoute
  · simp [mu, D]
    ring_nf
    omega
  · simp only [longWidth, leafWidth]
    have hbase :
        n m * (8 * D Delta ^ 2 * ((m + 1) * ordinaryWidth m W x Delta)) ≤
          4 * D Delta *
            (2 * n m * D Delta * ((m + 1) * ordinaryWidth m W x Delta)) := by
      nlinarith
    exact hbase.trans (Nat.mul_le_mul_left (4 * D Delta)
      (Nat.le_add_left _ _))
  · exact hlong
  · exact hleaf
  · simpa [hXcard, n] using hrouterCap
  · simp [eta, alpha]
  · simp [scale]
  · exact hreplicas
  · simp only [scale, leafWidth, scaleDen]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hscaleDen.ne']
    norm_cast
    omega
  · simp only [scale, scaleDen]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hscaleDen.ne']
    simp [D]
    nlinarith
  · simp [replicas, D]
  · have hq_leaf : m * q m W x Delta ≤ leafWidth m W x Delta := by
      simp only [leafWidth, replicas, scaleDen]
      have hfactor : m ≤ D Delta * (m * (2 + D Delta * eta m x)) := by
        have hmfac : m ≤ m * (2 + D Delta * eta m x) := by
          calc
            m = m * 1 := by simp
            _ ≤ m * (2 + D Delta * eta m x) := by
              exact Nat.mul_le_mul_left m (by omega)
        calc
          m ≤ m * (2 + D Delta * eta m x) := hmfac
          _ ≤ D Delta * (m * (2 + D Delta * eta m x)) := by
            exact Nat.le_mul_of_pos_left _ hD
      calc
        m * q m W x Delta ≤
            (D Delta * (m * (2 + D Delta * eta m x))) * q m W x Delta :=
          Nat.mul_le_mul_right _ hfactor
        _ = replicas m W x Delta * scaleDen m x Delta := by
          simp [replicas, scaleDen]
          ring
        _ ≤ leafWidth m W x Delta := by
          exact Nat.le_add_right _ _
    rw [hXcard]
    exact hq_leaf.trans (by
      have := hrouterCap
      omega)
  · exact halpha
  · have hgrouped : 0 < groupedWidth m W x Delta := by
      simp [groupedWidth, carrierWidth, outWidth]
      exact ⟨hD, Nat.pow_pos (by omega), hord⟩
    simp only [groupSize, q]
    calc
      alpha m x = alpha m x * 1 := by simp
      _ ≤ alpha m x * (3 * groupedWidth m W x Delta) := by
        exact Nat.mul_le_mul_left _ (by omega)
      _ = 3 * alpha m x * groupedWidth m W x Delta := by ring
  · simp [alpha, groupSize]
  · apply (Nat.le_div_iff_mul_le (by positivity)).2
    simp [q]
    ring_nf
    exact le_rfl
  · apply (Nat.le_div_iff_mul_le (by positivity)).2
    simp [groupedWidth, D]
    ring_nf
    omega
  · simp only [carrierWidth]
    have : 1 ≤ 4 * D Delta := by omega
    calc
      outWidth m W x Delta = 1 * outWidth m W x Delta := by simp
      _ ≤ (4 * D Delta) * outWidth m W x Delta :=
        Nat.mul_le_mul_right _ this
  · simp [carrierWidth, D]
  · simp only [longWidth]
    have hDm : 2 * (m - 1) ≤ D Delta * m := by
      have htwo : 2 * m ≤ D Delta * m :=
        Nat.mul_le_mul_right m (by simp [D])
      omega
    calc
      16 * D Delta * (m - 1) * ordinaryWidth m W x Delta +
          8 * D Delta ^ 2 * ordinaryWidth m W x Delta =
        (8 * D Delta * ordinaryWidth m W x Delta) * (2 * (m - 1)) +
          8 * D Delta ^ 2 * ordinaryWidth m W x Delta := by ring
      _ ≤ (8 * D Delta * ordinaryWidth m W x Delta) * (D Delta * m) +
          8 * D Delta ^ 2 * ordinaryWidth m W x Delta :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left _ hDm) _
      _ = 8 * D Delta ^ 2 *
          ((m + 1) * ordinaryWidth m W x Delta) := by ring
  · exact hord
  · simp only [outWidth]
    omega
  · have hord_cap :
        3 * ordinaryWidth m W x Delta ≤
          claim59SourceDegreeCap x (n m) / 2 := by
      have hord_leaf : 3 * ordinaryWidth m W x Delta ≤
          leafWidth m W x Delta := by
        simp only [leafWidth, longWidth]
        have : 3 ≤ 2 * n m * D Delta * (m + 1) := by
          calc
            3 ≤ 2 * 1 * 1 * 3 := by norm_num
            _ ≤ 2 * n m * D Delta * (m + 1) := by
              gcongr <;> omega
        calc
          3 * ordinaryWidth m W x Delta ≤
              (2 * n m * D Delta * (m + 1)) *
                ordinaryWidth m W x Delta :=
            Nat.mul_le_mul_right _ this
          _ ≤ replicas m W x Delta * scaleDen m x Delta +
              2 * n m * D Delta *
                ((m + 1) * ordinaryWidth m W x Delta) := by
            ring_nf
            exact Nat.le_add_right _ _
      exact hord_leaf.trans (by
        have := hrouterCap
        omega)
    simpa [hXcard, n] using hord_cap
  · exact le_rfl

/-! ## One-monomial degree-24 wrapper -/

def buildConstant24 : Nat :=
  6144 * (110592000 * 320 ^ 4) * 16 * 4 ^ 10

private theorem maxDegree_pos_of_nodeWellLinked
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {X : Finset V} {Delta : Nat}
    (hXcard : 1 < X.card)
    (hXwell : NodeWellLinkedIn G Finset.univ X)
    (hdegree : MaxDegreeAtMost G Delta) :
    0 < Delta := by
  classical
  rcases Finset.one_lt_card.mp hXcard with ⟨a, ha, b, hb, hab⟩
  have hdisjoint : Disjoint ({a} : Finset V) {b} := by simp [hab]
  rcases hXwell.2 (by simpa using ha) (by simpa using hb) hdisjoint with
    ⟨P, hPcard, _hstay⟩
  have hindexCard : Fintype.card P.Index = 1 := by
    simpa [PathPacking.card] using hPcard
  let i : P.Index :=
    (Fintype.equivFinOfCardEq hindexCard).symm ⟨0, by decide⟩
  have hconnects := P.connects i
  have hendpoints :
      ((P.path i).source = a ∧ (P.path i).target = b) ∨
        ((P.path i).source = b ∧ (P.path i).target = a) := by
    simpa [GraphPath.Connects] using hconnects
  have hne : (P.path i).source ≠ (P.path i).target := by
    rcases hendpoints with h | h
    · simpa [h.1, h.2] using hab
    · simpa [h.1, h.2] using hab.symm
  have hadj : G.Adj (P.path i).target (P.path i).penultimate :=
    ((P.path i).penultimate_adj_target hne).symm
  rcases hdegree (P.path i).target with ⟨N, hN, hNcard⟩
  have hmem : (P.path i).penultimate ∈ N := (hN _).2 hadj
  have hNpos : 0 < N.card := Finset.card_pos.mpr ⟨_, hmem⟩
  omega

private theorem eta_le_two_mul
    {m x : Nat} (hm : 2 ≤ m) :
    eta m x ≤ 2 * m * alpha m x := by
  have hn_alpha : 2 * n m ≤ alpha m x := by
    simp [alpha]
    nlinarith
  have hsub : m - 1 ≤ m := Nat.sub_le _ _
  calc
    eta m x = n m + (m - 1) * (alpha m x + n m) := rfl
    _ ≤ m * n m + m * (alpha m x + n m) := by
      exact Nat.add_le_add
        (by
          calc
            n m = 1 * n m := by simp
            _ ≤ m * n m := Nat.mul_le_mul_right _ (by omega))
        (Nat.mul_le_mul_right _ hsub)
    _ = m * alpha m x + 2 * m * n m := by ring
    _ ≤ m * alpha m x + m * alpha m x := by
      exact Nat.add_le_add_left (by
        calc
          2 * m * n m = m * (2 * n m) := by ring
          _ ≤ m * alpha m x := Nat.mul_le_mul_left _ hn_alpha) _
    _ = 2 * m * alpha m x := by ring

private theorem scaleDen_le
    {m x Delta : Nat} (hm : 2 ≤ m) :
    scaleDen m x Delta ≤ 4 * m ^ 2 * D Delta * alpha m x := by
  have hnPos : 0 < n m := by simp [n]; positivity
  have hetaPos : 0 < eta m x := by
    exact hnPos.trans_le (by
      simp only [eta]
      exact Nat.le_add_right _ _)
  have hDeta : 2 ≤ D Delta * eta m x := by
    have hD : 3 ≤ D Delta := by simp [D]
    nlinarith
  have heta := eta_le_two_mul (x := x) hm
  calc
    scaleDen m x Delta = m * (2 + D Delta * eta m x) := rfl
    _ ≤ m * (2 * (D Delta * eta m x)) := by
      exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ m * (2 * (D Delta * (2 * m * alpha m x))) := by
      gcongr
    _ = 4 * m ^ 2 * D Delta * alpha m x := by ring

private theorem longWidth_le
    {m W x Delta : Nat} (hm : 2 ≤ m) :
    longWidth m W x Delta ≤
      2 * m * ordinaryWidth m W x Delta := by
  simp only [longWidth]
  exact Nat.mul_le_mul_right _ (by omega)

private theorem replicas_eq
    (m W x Delta : Nat) :
    replicas m W x Delta =
      240 * alpha m x * D Delta ^ 3 * m ^ 4 *
        ordinaryWidth m W x Delta := by
  simp [replicas, q, groupSize, groupedWidth, carrierWidth, outWidth]
  ring

theorem leafWidth_le_monomial
    {m W x Delta : Nat} (hm : 2 ≤ m) (hW : 0 < W) :
    leafWidth m W x Delta ≤
      (110592000 * 320 ^ 4) * W * m ^ 14 * D Delta ^ 8 *
        (Nat.log 2 x + 1) ^ 4 := by
  have hscale := scaleDen_le (x := x) (Delta := Delta) hm
  have hlong := longWidth_le (W := W) (x := x) (Delta := Delta) hm
  have hn : 0 < n m := by simp [n]; positivity
  have hD : 0 < D Delta := by simp [D]
  have halpha : 0 < alpha m x := by simp [alpha]; positivity
  have hord : 0 < ordinaryWidth m W x Delta :=
    BandwidthTreeOfSetsSystem.coarseStrongificationWidth_pos
      halpha hD hW
  have hfirst :
      replicas m W x Delta * scaleDen m x Delta ≤
        960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 *
          ordinaryWidth m W x Delta := by
    rw [replicas_eq]
    calc
      (240 * alpha m x * D Delta ^ 3 * m ^ 4 *
          ordinaryWidth m W x Delta) * scaleDen m x Delta
          ≤ (240 * alpha m x * D Delta ^ 3 * m ^ 4 *
              ordinaryWidth m W x Delta) *
              (4 * m ^ 2 * D Delta * alpha m x) :=
        Nat.mul_le_mul_left _ hscale
      _ = 960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 *
          ordinaryWidth m W x Delta := by ring
  have hsecond :
      2 * n m * D Delta * longWidth m W x Delta ≤
        960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 *
          ordinaryWidth m W x Delta := by
    calc
      2 * n m * D Delta * longWidth m W x Delta
          ≤ 2 * n m * D Delta *
              (2 * m * ordinaryWidth m W x Delta) :=
        Nat.mul_le_mul_left _ hlong
      _ ≤ 960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 *
          ordinaryWidth m W x Delta := by
        have hnalpha : n m ≤ alpha m x := by
          calc
            n m = 1 * n m := by simp
            _ ≤ (320 * (Nat.log 2 x + 1)) * n m :=
              Nat.mul_le_mul_right _
                (show 1 ≤ 320 * (Nat.log 2 x + 1) by omega)
            _ = alpha m x := by simp [alpha]; ring
        have hcoef :
            4 * n m * D Delta * m ≤
              960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 := by
          calc
            4 * n m * D Delta * m
                ≤ 4 * alpha m x * D Delta * m := by gcongr
            _ ≤ 960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 := by
              have hprodPos :
                  0 < 240 * alpha m x * D Delta ^ 3 * m ^ 5 := by
                positivity
              have : 1 ≤ 240 * alpha m x * D Delta ^ 3 * m ^ 5 :=
                Nat.succ_le_of_lt hprodPos
              calc
                4 * alpha m x * D Delta * m =
                    (4 * alpha m x * D Delta * m) * 1 := by ring
                _ ≤ (4 * alpha m x * D Delta * m) *
                    (240 * alpha m x * D Delta ^ 3 * m ^ 5) :=
                  Nat.mul_le_mul_left _ this
                _ = 960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 := by ring
        calc
          2 * n m * D Delta * (2 * m * ordinaryWidth m W x Delta) =
              (4 * n m * D Delta * m) * ordinaryWidth m W x Delta := by ring
          _ ≤ (960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6) *
              ordinaryWidth m W x Delta :=
            Nat.mul_le_mul_right _ hcoef
          _ = 960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 *
              ordinaryWidth m W x Delta := by ring
  calc
    leafWidth m W x Delta =
        replicas m W x Delta * scaleDen m x Delta +
          2 * n m * D Delta * longWidth m W x Delta := rfl
    _ ≤ 2 * (960 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 *
          ordinaryWidth m W x Delta) := by omega
    _ = 1920 * alpha m x ^ 2 * D Delta ^ 4 * m ^ 6 *
          ordinaryWidth m W x Delta := by ring
    _ = 110592000 * alpha m x ^ 4 * D Delta ^ 8 * m ^ 6 * W := by
      unfold ordinaryWidth
      rw [BandwidthTreeOfSetsSystem.coarseStrongificationWidth_eq]
      ring
    _ = (110592000 * 320 ^ 4) * W * m ^ 14 * D Delta ^ 8 *
          (Nat.log 2 x + 1) ^ 4 := by
      simp [alpha, n]
      ring

/-- The exponent-24 closure requested for WP1C.  The deliberately generous
constant absorbs every integral floor and the shifts `Delta + 3` and
`log_2 x + 1`; the polynomial powers are `m^24`, `Delta^10`, and `log^5`. -/
theorem exists_strongTreeOfSetsSystem_of_m24_threshold
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (X : Finset V)
    {m W x Delta : Nat}
    (hm : 2 ≤ m) (hW : 0 < W) (hx : 2 ≤ x)
    (hdegree : MaxDegreeAtMost G Delta)
    (hXcard : X.card = x)
    (hXwell : NodeWellLinkedIn G Finset.univ X)
    (hlarge :
      buildConstant24 * W * m ^ 24 * Delta ^ 10 *
          (Nat.log 2 x) ^ 5 < x) :
    Nonempty (StrongTreeOfSetsSystem G m W) := by
  have hDelta : 0 < Delta :=
    maxDegree_pos_of_nodeWellLinked (by simpa [hXcard] using hx)
      hXwell hdegree
  let logx := Nat.log 2 x
  let denominator := 192 * (n m) ^ 3 * logx
  let demand := 16 * D Delta * mu m W x Delta
  have hlog : 0 < logx := by
    dsimp [logx]
    exact Nat.log_pos (by omega) hx
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    have hn : 0 < n m := by simp [n]; positivity
    positivity
  have hDpos : 0 < D Delta := by simp [D]
  have hnPos : 0 < n m := by simp [n]; positivity
  have hD_le : D Delta ≤ 4 * Delta := by simp [D]; omega
  have hL_le : Nat.log 2 x + 1 ≤ 2 * logx := by
    dsimp [logx]
    omega
  have hleaf := leafWidth_le_monomial (x := x) (Delta := Delta) hm hW
  have hdemand :
      demand ≤
        32 * (110592000 * 320 ^ 4) * W * m ^ 18 * D Delta ^ 10 *
          (Nat.log 2 x + 1) ^ 4 := by
    dsimp [demand]
    simp only [mu, n]
    calc
      16 * D Delta *
          (2 * (m ^ 2) ^ 2 * D Delta * leafWidth m W x Delta)
          ≤ 16 * D Delta *
              (2 * (m ^ 2) ^ 2 * D Delta *
                ((110592000 * 320 ^ 4) * W * m ^ 14 * D Delta ^ 8 *
                  (Nat.log 2 x + 1) ^ 4)) := by
            gcongr
      _ = 32 * (110592000 * 320 ^ 4) * W * m ^ 18 * D Delta ^ 10 *
          (Nat.log 2 x + 1) ^ 4 := by ring
  have hshifted :
      D Delta ^ 10 * (Nat.log 2 x + 1) ^ 4 * logx ≤
        4 ^ 10 * 16 * Delta ^ 10 * logx ^ 5 := by
    calc
      D Delta ^ 10 * (Nat.log 2 x + 1) ^ 4 * logx
          ≤ (4 * Delta) ^ 10 * (2 * logx) ^ 4 * logx := by
            gcongr
      _ = 4 ^ 10 * 16 * Delta ^ 10 * logx ^ 5 := by ring
  have hproduct : demand * denominator < x := by
    calc
      demand * denominator ≤
          (32 * (110592000 * 320 ^ 4) * W * m ^ 18 * D Delta ^ 10 *
            (Nat.log 2 x + 1) ^ 4) * denominator :=
        Nat.mul_le_mul_right _ hdemand
      _ = 6144 * (110592000 * 320 ^ 4) * W * m ^ 24 *
          (D Delta ^ 10 * (Nat.log 2 x + 1) ^ 4 * logx) := by
        dsimp [denominator, logx]
        simp [n]
        ring
      _ ≤ 6144 * (110592000 * 320 ^ 4) * W * m ^ 24 *
          (4 ^ 10 * 16 * Delta ^ 10 * logx ^ 5) :=
        Nat.mul_le_mul_left _ hshifted
      _ = buildConstant24 * W * m ^ 24 * Delta ^ 10 * logx ^ 5 := by
        simp [buildConstant24]
        ring
      _ < x := by simpa [logx] using hlarge
  have hdemandCap :
      demand ≤ claim59SourceDegreeCap x (n m) := by
    apply (Nat.le_div_iff_mul_le hdenominator).2
    simpa [claim59SourceDegreeCap, denominator, logx,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.le_of_lt hproduct)
  have hmuRoute :
      mu m W x Delta ≤
        (claim59SourceDegreeCap x (n m) / 2) / (8 * D Delta) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) hDpos)).2
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    calc
      mu m W x Delta * (8 * D Delta) * 2 = demand := by
        dsimp [demand]
        ring
      _ ≤ claim59SourceDegreeCap x (n m) := hdemandCap
  have halphaPos : 0 < alpha m x := by simp [alpha]; positivity
  have hordPos : 0 < ordinaryWidth m W x Delta :=
    BandwidthTreeOfSetsSystem.coarseStrongificationWidth_pos
      halphaPos hDpos hW
  have hreplicasPos : 0 < replicas m W x Delta := by
    simp only [replicas, q, groupSize, groupedWidth, carrierWidth, outWidth]
    positivity
  have hscaleDenPos : 0 < scaleDen m x Delta := by
    simp only [scaleDen]
    positivity
  have hlongPos : 0 < longWidth m W x Delta := by
    simp only [longWidth]
    positivity
  have hleafPos : 0 < leafWidth m W x Delta := by
    simp only [leafWidth]
    positivity
  have hmuPos : 0 < mu m W x Delta := by
    simp only [mu]
    positivity
  have hdegreeDemand : Delta + 2 ≤ demand := by
    dsimp [demand]
    have hbase : Delta + 2 ≤ 16 * D Delta := by simp [D]; omega
    calc
      Delta + 2 ≤ 16 * D Delta := hbase
      _ = (16 * D Delta) * 1 := by simp
      _ ≤ (16 * D Delta) * mu m W x Delta :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hmuPos)
  have hdegreeCap :
      Delta + 1 < claim59SourceDegreeCap x (n m) := by
    have : Delta + 2 ≤ claim59SourceDegreeCap x (n m) :=
      hdegreeDemand.trans hdemandCap
    omega
  exact exists_strongTreeOfSetsSystem_of_source_budgets
    G X hm hW hx hdegree hXcard hXwell hdegreeCap hmuRoute

end ChekuriChuzhoySection5Arithmetic
end SimpleGraph

end Lax17Proofs
