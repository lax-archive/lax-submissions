import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Amortization for recursive truncated-bandwidth cuts

Chekuri--Chuzhoy, journal Section 5.1 (the bandwidth decomposition preceding
Claims 5.3--5.19), recursively splits a cluster along a cut that violates
truncated bandwidth.  If the old boundary is divided into parts of sizes
`a` and `b`, and the cut has size `c`, the two new boundaries have sizes
`a + c` and `b + c`.  The violating-cut inequality has the denominator-cleared
form

`D * c < min (min a b) K`,

where `K` is the truncation cap.  This file proves the finite numerical
amortization behind that construction.  The proof uses a sum of dyadically
weighted capped quadratic potentials.  It therefore has no dependence on the
depth of the split tree or on a vertex count.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5BandwidthAmortization

open scoped BigOperators

/-- A finite binary history of boundary splits.  At a node, `a` and `b` are
the two portions of the parent boundary and `c` is the new cut. -/
inductive SplitTree where
  | leaf (boundary : Nat)
  | node (a b c : Nat) (left right : SplitTree)

namespace SplitTree

/-- Boundary size at the root of a split history. -/
def rootBoundary : SplitTree → Nat
  | leaf boundary => boundary
  | node a b _ _ _ => a + b

/-- Sum of all newly cut edges, with one contribution per internal node. -/
def totalCut : SplitTree → Nat
  | leaf _ => 0
  | node _ _ c left right => c + left.totalCut + right.totalCut

/-- Sum of the truncated smaller-side charges over all internal nodes. -/
def totalCharge (K : Nat) : SplitTree → Nat
  | leaf _ => 0
  | node a b _ left right =>
      min (min a b) K + left.totalCharge K + right.totalCharge K

/-- Numerical validity of a recursive truncated-bandwidth decomposition.
The equalities explicitly retain the boundary inflation by `c`. -/
def Valid (K D : Nat) : SplitTree → Prop
  | leaf _ => True
  | node a b c left right =>
      left.rootBoundary = a + c ∧
      right.rootBoundary = b + c ∧
      D * c < min (min a b) K ∧
      left.Valid K D ∧ right.Valid K D

end SplitTree

/-! ## The dyadic potential -/

/-- The quadratic `n^2`, continued linearly after the cap `q`. -/
private def cappedQuadratic (q n : Nat) : Int :=
  if n ≤ q then (n : Int) ^ 2
  else 2 * (q : Int) * (n : Int) - (q : Int) ^ 2

private theorem cappedQuadratic_nonneg (q n : Nat) :
    0 ≤ cappedQuadratic q n := by
  by_cases h : n ≤ q
  · simp [cappedQuadratic, h]
  · have hqn : (q : Int) ≤ (n : Int) := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
    simp only [cappedQuadratic, h, ↓reduceIte]
    have hq0 : 0 ≤ (q : Int) := by positivity
    nlinarith

private theorem cappedQuadratic_upper (q n : Nat) :
    cappedQuadratic q n ≤ 2 * (q : Int) * (n : Int) := by
  by_cases h : n ≤ q
  · simp only [cappedQuadratic, h, ↓reduceIte]
    have hnq : (n : Int) ≤ (q : Int) := by exact_mod_cast h
    have hn : 0 ≤ (n : Int) := by positivity
    nlinarith
  · simp only [cappedQuadratic, h, ↓reduceIte]
    nlinarith [sq_nonneg (q : Int)]

private theorem cappedQuadratic_superadditive (q a b : Nat) :
    cappedQuadratic q a + cappedQuadratic q b ≤
      cappedQuadratic q (a + b) := by
  by_cases ha : a ≤ q <;>
    by_cases hb : b ≤ q <;>
      by_cases hab : a + b ≤ q
  all_goals
    simp only [cappedQuadratic, ha, hb, hab, ↓reduceIte, Nat.cast_add]
  all_goals
    have ha0 : 0 ≤ (a : Int) := by positivity
    have hb0 : 0 ≤ (b : Int) := by positivity
    have hq0 : 0 ≤ (q : Int) := by positivity
  · nlinarith [show (a : Int) ≤ q by exact_mod_cast ha,
      show (b : Int) ≤ q by exact_mod_cast hb]
  · have habq : (q : Int) < a + b := by
      exact_mod_cast (Nat.lt_of_not_ge hab)
    have haq : (a : Int) ≤ q := by exact_mod_cast ha
    have hbq : (b : Int) ≤ q := by exact_mod_cast hb
    nlinarith [mul_nonneg (sub_nonneg.mpr haq) (sub_nonneg.mpr hbq)]
  · omega
  · have haq : (a : Int) ≤ q := by exact_mod_cast ha
    nlinarith
  · omega
  · have hqa : (q : Int) ≤ a := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge ha))
    have hbq : (b : Int) ≤ q := by exact_mod_cast hb
    nlinarith
  · omega
  · have hqa : (q : Int) ≤ a := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge ha))
    have hqb : (q : Int) ≤ b := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hb))
    nlinarith

private theorem cappedQuadratic_add_le
    (q n c : Nat) :
    cappedQuadratic q (n + c) ≤
      cappedQuadratic q n + 2 * (q : Int) * (c : Int) := by
  by_cases hn : n ≤ q <;>
    by_cases hnc : n + c ≤ q
  · simp only [cappedQuadratic, hn, hnc, ↓reduceIte, Nat.cast_add]
    have hncq : ((n + c : Nat) : Int) ≤ q := by exact_mod_cast hnc
    have hn0 : 0 ≤ (n : Int) := by positivity
    have hc0 : 0 ≤ (c : Int) := by positivity
    nlinarith
  · simp only [cappedQuadratic, hn, hnc, ↓reduceIte, Nat.cast_add]
    have hnq : (n : Int) ≤ q := by exact_mod_cast hn
    have hqnc : (q : Int) < n + c := by
      exact_mod_cast (Nat.lt_of_not_ge hnc)
    nlinarith [sq_nonneg ((q : Int) - (n : Int))]
  · omega
  · simp only [cappedQuadratic, hn, hnc, ↓reduceIte, Nat.cast_add]
    ring_nf
    exact le_rfl

private theorem cappedQuadratic_linear_region
    {q a b : Nat} (hq : 0 < q) (hqa : q ≤ a) (hqb : q ≤ b) :
    cappedQuadratic q (a + b) -
        cappedQuadratic q a - cappedQuadratic q b =
      (q : Int) ^ 2 := by
  have hqab : ¬a + b ≤ q := by omega
  by_cases ha : a ≤ q
  · have haeq : a = q := Nat.le_antisymm ha hqa
    subst a
    by_cases hb : b ≤ q
    · have hbeq : b = q := Nat.le_antisymm hb hqb
      subst b
      have hqq : ¬q + q ≤ q := by omega
      simp [cappedQuadratic, hqq]
      ring
    · simp [cappedQuadratic, hb, hqab]
      ring
  · by_cases hb : b ≤ q
    · have hbeq : b = q := Nat.le_antisymm hb hqb
      subst b
      simp [cappedQuadratic, ha, hqab]
      ring
    · simp [cappedQuadratic, ha, hb, hqab]
      ring

private def logCap (K : Nat) : Nat := Nat.log 2 K

private def dyadicUnit (K : Nat) : Nat := 2 ^ logCap K

private def scaleWeight (K i : Nat) : Nat :=
  2 ^ (logCap K - i)

private def scaledTerm (K i n : Nat) : Int :=
  (scaleWeight K i : Int) * cappedQuadratic (2 ^ i) n

/-- The common-denominator version of
`sum_i cappedQuadratic(2^i,n) / 2^i`. -/
private def dyadicPotential (K n : Nat) : Int :=
  ∑ i ∈ Finset.range (logCap K + 1), scaledTerm K i n

private theorem scaleWeight_mul_scale
    {K i : Nat} (hi : i ≤ logCap K) :
    scaleWeight K i * 2 ^ i = dyadicUnit K := by
  rw [scaleWeight, dyadicUnit, ← pow_add,
    Nat.sub_add_cancel hi]

private theorem scaledTerm_nonneg (K i n : Nat) :
    0 ≤ scaledTerm K i n :=
  mul_nonneg (by positivity) (cappedQuadratic_nonneg _ _)

private theorem scaledTerm_upper
    {K i n : Nat} (hi : i ≤ logCap K) :
    scaledTerm K i n ≤
      2 * (dyadicUnit K : Int) * (n : Int) := by
  have hscale :
      (scaleWeight K i : Int) * ((2 ^ i : Nat) : Int) =
        (dyadicUnit K : Int) := by
    exact_mod_cast scaleWeight_mul_scale hi
  calc
    scaledTerm K i n ≤
        (scaleWeight K i : Int) *
          (2 * ((2 ^ i : Nat) : Int) * (n : Int)) :=
      mul_le_mul_of_nonneg_left
        (cappedQuadratic_upper (2 ^ i) n) (by positivity)
    _ = 2 * (dyadicUnit K : Int) * (n : Int) := by
      rw [show (scaleWeight K i : Int) *
          (2 * ((2 ^ i : Nat) : Int) * (n : Int)) =
        2 * ((scaleWeight K i : Int) * ((2 ^ i : Nat) : Int)) *
          (n : Int) by ring, hscale]

private theorem scaledTerm_superadditive (K i a b : Nat) :
    scaledTerm K i a + scaledTerm K i b ≤
      scaledTerm K i (a + b) := by
  unfold scaledTerm
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (cappedQuadratic_superadditive (2 ^ i) a b) (by positivity)

private theorem scaledTerm_add_le
    {K i n c : Nat} (hi : i ≤ logCap K) :
    scaledTerm K i (n + c) ≤
      scaledTerm K i n +
        2 * (dyadicUnit K : Int) * (c : Int) := by
  have hscale :
      (scaleWeight K i : Int) * ((2 ^ i : Nat) : Int) =
        (dyadicUnit K : Int) := by
    exact_mod_cast scaleWeight_mul_scale hi
  calc
    scaledTerm K i (n + c) ≤
        (scaleWeight K i : Int) *
          (cappedQuadratic (2 ^ i) n +
            2 * ((2 ^ i : Nat) : Int) * (c : Int)) :=
      mul_le_mul_of_nonneg_left
        (cappedQuadratic_add_le (2 ^ i) n c) (by positivity)
    _ = scaledTerm K i n +
        2 * (dyadicUnit K : Int) * (c : Int) := by
      rw [mul_add]
      unfold scaledTerm
      rw [show (scaleWeight K i : Int) *
          (2 * ((2 ^ i : Nat) : Int) * (c : Int)) =
        2 * ((scaleWeight K i : Int) * ((2 ^ i : Nat) : Int)) *
          (c : Int) by ring, hscale]

private theorem dyadicPotential_nonneg (K n : Nat) :
    0 ≤ dyadicPotential K n := by
  unfold dyadicPotential
  exact Finset.sum_nonneg fun i _ => scaledTerm_nonneg K i n

private theorem dyadicPotential_upper (K n : Nat) :
    dyadicPotential K n ≤
      2 * (dyadicUnit K : Int) *
        (logCap K + 1 : Nat) * (n : Int) := by
  unfold dyadicPotential
  calc
    ∑ i ∈ Finset.range (logCap K + 1), scaledTerm K i n ≤
        ∑ _i ∈ Finset.range (logCap K + 1),
          2 * (dyadicUnit K : Int) * (n : Int) := by
      apply Finset.sum_le_sum
      intro i hi
      exact scaledTerm_upper (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = 2 * (dyadicUnit K : Int) *
        (logCap K + 1 : Nat) * (n : Int) := by
      simp
      ring

private theorem dyadicPotential_superadditive (K a b : Nat) :
    dyadicPotential K a + dyadicPotential K b ≤
      dyadicPotential K (a + b) := by
  unfold dyadicPotential
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    scaledTerm_superadditive K i a b

private theorem dyadicPotential_add_le (K n c : Nat) :
    dyadicPotential K (n + c) ≤
      dyadicPotential K n +
        2 * (dyadicUnit K : Int) *
          (logCap K + 1 : Nat) * (c : Int) := by
  unfold dyadicPotential
  calc
    ∑ i ∈ Finset.range (logCap K + 1), scaledTerm K i (n + c) ≤
        ∑ i ∈ Finset.range (logCap K + 1),
          (scaledTerm K i n +
            2 * (dyadicUnit K : Int) * (c : Int)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact scaledTerm_add_le
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = dyadicPotential K n +
        2 * (dyadicUnit K : Int) *
          (logCap K + 1 : Nat) * (c : Int) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      unfold dyadicPotential
      ring

private theorem scaledTerm_linear_gap
    {K i a b : Nat} (hi : i ≤ logCap K)
    (hia : 2 ^ i ≤ a) (hib : 2 ^ i ≤ b) :
    scaledTerm K i (a + b) -
        scaledTerm K i a - scaledTerm K i b =
      (dyadicUnit K : Int) * (2 ^ i : Nat) := by
  unfold scaledTerm
  have hgap :
      cappedQuadratic (2 ^ i) (a + b) -
          cappedQuadratic (2 ^ i) a - cappedQuadratic (2 ^ i) b =
        ((2 ^ i : Nat) : Int) ^ 2 :=
    cappedQuadratic_linear_region (by positivity) hia hib
  have hscale :
      (scaleWeight K i : Int) * ((2 ^ i : Nat) : Int) =
        (dyadicUnit K : Int) := by
    exact_mod_cast scaleWeight_mul_scale hi
  calc
    (scaleWeight K i : Int) * cappedQuadratic (2 ^ i) (a + b) -
          (scaleWeight K i : Int) * cappedQuadratic (2 ^ i) a -
          (scaleWeight K i : Int) * cappedQuadratic (2 ^ i) b =
        (scaleWeight K i : Int) *
          (cappedQuadratic (2 ^ i) (a + b) -
            cappedQuadratic (2 ^ i) a - cappedQuadratic (2 ^ i) b) := by
      ring
    _ = (scaleWeight K i : Int) * ((2 ^ i : Nat) : Int) ^ 2 := by
      rw [hgap]
    _ = (dyadicUnit K : Int) * (2 ^ i : Nat) := by
      rw [show (scaleWeight K i : Int) * ((2 ^ i : Nat) : Int) ^ 2 =
        ((scaleWeight K i : Int) * ((2 ^ i : Nat) : Int)) *
          ((2 ^ i : Nat) : Int) by ring, hscale]

private theorem dyadicPotential_split_gap
    {K a b m : Nat} (hm : 0 < m)
    (hma : m ≤ a) (hmb : m ≤ b) (hmK : m ≤ K) :
    (dyadicUnit K : Int) * (m : Int) +
        2 * dyadicPotential K a + 2 * dyadicPotential K b ≤
      2 * dyadicPotential K (a + b) := by
  let j := Nat.log 2 m
  let q := 2 ^ j
  have hj : j ≤ logCap K := by
    exact Nat.log_mono_right hmK
  have hjmem : j ∈ Finset.range (logCap K + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hqpos : 0 < q := by positivity
  have hqm : q ≤ m := by
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
  have hm2q : m < 2 * q := by
    simpa [q, j, pow_succ, Nat.mul_comm] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  let gap : Nat → Int := fun i =>
    scaledTerm K i (a + b) -
      scaledTerm K i a - scaledTerm K i b
  have hgap_nonneg : ∀ i, 0 ≤ gap i := by
    intro i
    dsimp [gap]
    linarith [scaledTerm_superadditive K i a b]
  have hgapj :
      gap j = (dyadicUnit K : Int) * (q : Int) := by
    dsimp [gap, q]
    exact scaledTerm_linear_gap hj (hqm.trans hma) (hqm.trans hmb)
  have hj_le_sum :
      gap j ≤ ∑ i ∈ Finset.range (logCap K + 1), gap i := by
    exact Finset.single_le_sum
      (fun i _hi => hgap_nonneg i) hjmem
  have hQnonneg : 0 ≤ (dyadicUnit K : Int) := by positivity
  have hmq :
      (dyadicUnit K : Int) * (m : Int) ≤
        2 * ((dyadicUnit K : Int) * (q : Int)) := by
    have hm2qInt : (m : Int) ≤ 2 * (q : Int) := by
      exact_mod_cast (Nat.le_of_lt hm2q)
    nlinarith
  have hgap_sum :
      ∑ i ∈ Finset.range (logCap K + 1), gap i =
        dyadicPotential K (a + b) -
          dyadicPotential K a - dyadicPotential K b := by
    simp only [gap, dyadicPotential, Finset.sum_sub_distrib]
  rw [hgapj] at hj_le_sum
  rw [hgap_sum] at hj_le_sum
  linarith

/-! ## Amortization over the finite split tree -/

/-- Summing the strict violating-cut inequality over the tree bounds the
denominator-scaled cut total by the sum of truncated smaller-side charges. -/
theorem SplitTree.denominator_mul_totalCut_le_totalCharge
    {K D : Nat} {tree : SplitTree} (hvalid : tree.Valid K D) :
    D * tree.totalCut ≤ tree.totalCharge K := by
  induction tree with
  | leaf boundary =>
      simp [SplitTree.totalCut, SplitTree.totalCharge]
  | node a b c left right ihleft ihright =>
      rcases hvalid with
        ⟨_hleftRoot, _hrightRoot, hcut, hleftValid, hrightValid⟩
      have hc :
          D * c ≤ min (min a b) K :=
        Nat.le_of_lt hcut
      have hleft := ihleft hleftValid
      have hright := ihright hrightValid
      simp only [SplitTree.totalCut, SplitTree.totalCharge]
      calc
        D * (c + left.totalCut + right.totalCut) =
            D * c + D * left.totalCut + D * right.totalCut := by
          ring
        _ ≤ min (min a b) K +
            left.totalCharge K + right.totalCharge K :=
          Nat.add_le_add (Nat.add_le_add hc hleft) hright

private theorem totalCharge_potential_bound
    {K D : Nat} {tree : SplitTree} (hvalid : tree.Valid K D) :
    (dyadicUnit K : Int) * (tree.totalCharge K : Int) ≤
      2 * dyadicPotential K tree.rootBoundary +
        8 * (dyadicUnit K : Int) *
          (logCap K + 1 : Nat) * (tree.totalCut : Int) := by
  induction tree with
  | leaf boundary =>
      simp only [SplitTree.totalCharge, Nat.cast_zero, mul_zero,
        SplitTree.rootBoundary, SplitTree.totalCut]
      have hpot := dyadicPotential_nonneg K boundary
      linarith
  | node a b c left right ihleft ihright =>
      rcases hvalid with
        ⟨hleftRoot, hrightRoot, hcut, hleftValid, hrightValid⟩
      have hleft := ihleft hleftValid
      have hright := ihright hrightValid
      rw [hleftRoot] at hleft
      rw [hrightRoot] at hright
      let m := min (min a b) K
      have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le (D * c)) hcut
      have hma : m ≤ a :=
        (Nat.min_le_left (min a b) K).trans (Nat.min_le_left a b)
      have hmb : m ≤ b :=
        (Nat.min_le_left (min a b) K).trans (Nat.min_le_right a b)
      have hmK : m ≤ K := Nat.min_le_right (min a b) K
      have hsplit :=
        dyadicPotential_split_gap hm hma hmb hmK
      have hleftInflation := dyadicPotential_add_le K a c
      have hrightInflation := dyadicPotential_add_le K b c
      simp only [SplitTree.totalCharge, SplitTree.rootBoundary,
        SplitTree.totalCut, Nat.cast_add]
      change
        (dyadicUnit K : Int) *
            ((m : Int) + (left.totalCharge K : Int) +
              (right.totalCharge K : Int)) ≤
          2 * dyadicPotential K (a + b) +
            8 * (dyadicUnit K : Int) *
              (logCap K + 1 : Nat) *
                ((c : Int) + (left.totalCut : Int) +
                  (right.totalCut : Int))
      nlinarith

/-- Depth-independent cleared amortization bound.

The constant `16` absorbs the two child-boundary inflations at every split.
The conclusion is deliberately in natural-number form for direct use by the
finite bandwidth decomposition. -/
theorem SplitTree.denominator_mul_totalCut_le
    {K D : Nat} {tree : SplitTree}
    (hvalid : tree.Valid K D)
    (hD : 16 * (Nat.log 2 K + 1) ≤ D) :
    D * tree.totalCut ≤
      8 * (Nat.log 2 K + 1) * tree.rootBoundary := by
  let Q := dyadicUnit K
  let L := logCap K + 1
  have hcharge :=
    tree.denominator_mul_totalCut_le_totalCharge hvalid
  have hpotential := totalCharge_potential_bound hvalid
  have hrootPotential := dyadicPotential_upper K tree.rootBoundary
  have hQpos : 0 < Q := by
    dsimp [Q, dyadicUnit]
    positivity
  have hQL :
      (Q : Int) * (tree.totalCharge K : Int) ≤
        4 * (Q : Int) * (L : Int) * (tree.rootBoundary : Int) +
          8 * (Q : Int) * (L : Int) * (tree.totalCut : Int) := by
    change
      (dyadicUnit K : Int) * (tree.totalCharge K : Int) ≤
        4 * (dyadicUnit K : Int) * (logCap K + 1 : Nat) *
            (tree.rootBoundary : Int) +
          8 * (dyadicUnit K : Int) * (logCap K + 1 : Nat) *
            (tree.totalCut : Int)
    nlinarith
  have hscaledCharge :
      (Q : Int) * (D : Int) * (tree.totalCut : Int) ≤
        (Q : Int) * (tree.totalCharge K : Int) := by
    have hchargeInt :
        (D : Int) * (tree.totalCut : Int) ≤
          (tree.totalCharge K : Int) := by
      exact_mod_cast hcharge
    have hQnonneg : 0 ≤ (Q : Int) := by exact_mod_cast hQpos.le
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hchargeInt hQnonneg)
  have hD' : 16 * L ≤ D := by
    simpa [L, logCap] using hD
  have habsorbNat :
      16 * Q * L * tree.totalCut ≤ Q * D * tree.totalCut := by
    calc
      16 * Q * L * tree.totalCut =
          (16 * L) * (Q * tree.totalCut) := by ring
      _ ≤ D * (Q * tree.totalCut) :=
        Nat.mul_le_mul_right (Q * tree.totalCut) hD'
      _ = Q * D * tree.totalCut := by ring
  have habsorb :
      16 * (Q : Int) * (L : Int) * (tree.totalCut : Int) ≤
        (Q : Int) * (D : Int) * (tree.totalCut : Int) := by
    exact_mod_cast habsorbNat
  have hscaledFinal :
      (Q : Int) * (D : Int) * (tree.totalCut : Int) ≤
        8 * (Q : Int) * (L : Int) * (tree.rootBoundary : Int) := by
    nlinarith
  have hscaledFinalNat :
      Q * (D * tree.totalCut) ≤
        Q * (8 * L * tree.rootBoundary) := by
    have hnat :
        Q * D * tree.totalCut ≤
          8 * Q * L * tree.rootBoundary := by
      exact_mod_cast hscaledFinal
    calc
      Q * (D * tree.totalCut) = Q * D * tree.totalCut := by ring
      _ ≤ 8 * Q * L * tree.rootBoundary := hnat
      _ = Q * (8 * L * tree.rootBoundary) := by ring
  have hfinal :
      D * tree.totalCut ≤ 8 * L * tree.rootBoundary :=
    Nat.le_of_mul_le_mul_left hscaledFinalNat hQpos
  simpa [L, logCap] using hfinal

/-- The parameter choice used downstream: with
`D = 16 * ell * (log_2 K + 1)`, the total cut consumes strictly less than the
root boundary after multiplication by `ell`. -/
theorem SplitTree.ell_mul_totalCut_lt_rootBoundary
    {K ell : Nat} {tree : SplitTree}
    (hell : 0 < ell) (hroot : 0 < tree.rootBoundary)
    (hvalid :
      tree.Valid K (16 * ell * (Nat.log 2 K + 1))) :
    ell * tree.totalCut < tree.rootBoundary := by
  let L := Nat.log 2 K + 1
  have hLpos : 0 < L := by simp [L]
  have hLell : L ≤ ell * L := by
    have hone : 1 ≤ ell := hell
    simpa using Nat.mul_le_mul_right L hone
  have hD : 16 * L ≤ 16 * ell * L := by
    simpa [Nat.mul_assoc] using (Nat.mul_le_mul_left 16 hLell)
  have hbudget :=
    tree.denominator_mul_totalCut_le hvalid (by simpa [L] using hD)
  have hscaled :
      (8 * L) * (2 * ell * tree.totalCut) ≤
        (8 * L) * tree.rootBoundary := by
    calc
      (8 * L) * (2 * ell * tree.totalCut) =
          (16 * ell * L) * tree.totalCut := by ring
      _ ≤ 8 * L * tree.rootBoundary := by
        simpa [L] using hbudget
      _ = (8 * L) * tree.rootBoundary := by ring
  have htwo :
      2 * ell * tree.totalCut ≤ tree.rootBoundary :=
    Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos (by decide) hLpos)
  have htwo' :
      2 * (ell * tree.totalCut) ≤ tree.rootBoundary := by
    simpa [Nat.mul_assoc] using htwo
  omega

end ChekuriChuzhoySection5BandwidthAmortization
end SimpleGraph

end Lax17Proofs
