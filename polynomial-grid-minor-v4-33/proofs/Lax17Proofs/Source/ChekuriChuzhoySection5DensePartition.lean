import Lax17Proofs.Source.ChekuriChuzhoySection5Selection
import Lax17Proofs.Source.ChekuriChuzhoySection5TerminalSkeleton

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 dense partition

This module isolates the deterministic finite-existence content of journal
Claim 5.9.  A coloring of the nonterminal vertices gives the required indexed
blocks.  Boundary size counts named edge copies in the full edge-indexed
graph, while internal size counts named original edges with both endpoints in
the block.

The final theorem below is an exact finite second-moment statement.  Its sole
analytic premise is a displayed sum over every finite coloring; it is not a
probabilistic provider.  Proving that sum bound from the paper's maximum-degree
and numerical hypotheses is the remaining concentration calculation.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5DensePartition

open Finset
open ChekuriChuzhoySection5TerminalSkeleton


/-! ## Exact finite second-moment selection -/

/-- A finite union-bound/second-moment principle with all denominators
cleared.  Every bad pair `(i, omega)` consumes at least `threshold` units of
its nonnegative cost.  If the total cost is strictly smaller than one such
unit per sample, some sample is good for every constraint. -/
theorem exists_forall_not_bad_of_sum_cost_lt
    {Omega : Type u} {I : Type v}
    [DecidableEq Omega] [DecidableEq I]
    (samples : Finset Omega) (constraints : Finset I)
    (bad : I -> Omega -> Prop) [DecidablePred fun p : I × Omega => bad p.1 p.2]
    (cost : I -> Omega -> Nat) (threshold : Nat)
    (hcharge : ∀ i ∈ constraints, ∀ omega ∈ samples,
      bad i omega -> threshold <= cost i omega)
    (hbudget : (∑ i ∈ constraints, ∑ omega ∈ samples, cost i omega) <
      samples.card * threshold) :
    ∃ omega ∈ samples, ∀ i ∈ constraints, ¬ bad i omega := by
  classical
  by_contra hnone
  push_neg at hnone
  let badSamples : I -> Finset Omega := fun i =>
    samples.filter fun omega => bad i omega
  have hcover : samples ⊆ constraints.biUnion badSamples := by
    intro omega homega
    rcases hnone omega homega with ⟨i, hi, hbad⟩
    exact Finset.mem_biUnion.mpr
      ⟨i, hi, Finset.mem_filter.mpr ⟨homega, hbad⟩⟩
  have hcardCover : samples.card <= ∑ i ∈ constraints, (badSamples i).card := by
    exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcharged :
      (∑ i ∈ constraints, (badSamples i).card) * threshold <=
        ∑ i ∈ constraints, ∑ omega ∈ samples, cost i omega := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    calc
      (badSamples i).card * threshold =
          ∑ _omega ∈ badSamples i, threshold := by simp
      _ <= ∑ omega ∈ badSamples i, cost i omega := by
        apply Finset.sum_le_sum
        intro omega homega
        exact hcharge i hi omega (Finset.mem_filter.mp homega).1
          (Finset.mem_filter.mp homega).2
      _ <= ∑ omega ∈ samples, cost i omega := by
        apply Finset.sum_le_sum_of_subset
        intro omega homega
        exact (Finset.mem_filter.mp homega).1
  have : samples.card * threshold <=
      ∑ i ∈ constraints, ∑ omega ∈ samples, cost i omega :=
    (Nat.mul_le_mul_right threshold hcardCover).trans hcharged
  omega

/-- Squared excess above a proposed center. -/
def upperDeviationSq (value center : Nat) : Nat := (value - center) ^ 2

/-- Squared deficit below a proposed center. -/
def lowerDeviationSq (value center : Nat) : Nat := (center - value) ^ 2

theorem sq_le_upperDeviationSq_of_add_le
    {value center gap : Nat} (h : center + gap <= value) :
    gap ^ 2 <= upperDeviationSq value center := by
  have hgap : gap <= value - center := by omega
  exact Nat.pow_le_pow_left hgap 2

theorem sq_le_lowerDeviationSq_of_add_le
    {value center gap : Nat} (h : value + gap <= center) :
    gap ^ 2 <= lowerDeviationSq value center := by
  have hgap : gap <= center - value := by omega
  exact Nat.pow_le_pow_left hgap 2

theorem upperDeviationSq_add_two_mul_le (value center : Nat) :
    upperDeviationSq value center + 2 * value * center <=
      value ^ 2 + center ^ 2 := by
  unfold upperDeviationSq
  by_cases h : center <= value
  · have hsplit : value - center + center = value := Nat.sub_add_cancel h
    nlinarith [sq_nonneg (value - center)]
  · have hle : value <= center := by omega
    rw [Nat.sub_eq_zero_of_le hle]
    nlinarith [sq_nonneg (center - value)]

theorem lowerDeviationSq_add_two_mul_le (value center : Nat) :
    lowerDeviationSq value center + 2 * value * center <=
      value ^ 2 + center ^ 2 := by
  have h := upperDeviationSq_add_two_mul_le center value
  unfold lowerDeviationSq
  unfold upperDeviationSq at h
  calc
    (center - value) ^ 2 + 2 * value * center =
        (center - value) ^ 2 + 2 * center * value := by ac_rfl
    _ <= center ^ 2 + value ^ 2 := h
    _ = value ^ 2 + center ^ 2 := by ac_rfl

/-! ## Edge-indexed blocks and observables -/

namespace FiniteEdgeIndexedGraph

variable {W : Type u} [Fintype W] [DecidableEq W]

/-! ## Uniform finite-coloring counts -/

/-- Splitting a coloring into its values on `A` and off `A`, with the latter
represented by a coloring which is constantly `j` on `A`. -/
noncomputable def fixedColorEquiv (A : Finset W) {ell : Nat} (j : Fin ell) :
    ({color : W -> Fin ell // ∀ w ∈ A, color w = j} ×
      ({w : W // w ∈ A} -> Fin ell)) ≃ (W -> Fin ell) := by
  classical
  let forward :
      ({color : W -> Fin ell // ∀ w ∈ A, color w = j} ×
        ({w : W // w ∈ A} -> Fin ell)) -> (W -> Fin ell) := fun p w =>
    if hw : w ∈ A then p.2 ⟨w, hw⟩ else p.1.1 w
  let inverse : (W -> Fin ell) ->
      ({color : W -> Fin ell // ∀ w ∈ A, color w = j} ×
        ({w : W // w ∈ A} -> Fin ell)) := fun color =>
    (⟨fun w => if w ∈ A then j else color w, by
        intro w hw
        simp [hw]⟩,
      fun w => color w.1)
  exact
    { toFun := forward
      invFun := inverse
      left_inv := by
        rintro ⟨color, onA⟩
        apply Prod.ext
        · apply Subtype.ext
          funext w
          by_cases hw : w ∈ A
          · simp [forward, inverse, hw, color.2 w hw]
          · simp [forward, inverse, hw]
        · funext w
          simp [forward, inverse, w.2]
      right_inv := by
        intro color
        funext w
        by_cases hw : w ∈ A <;> simp [forward, inverse, hw] }

/-- Clearing the denominator, the number of colorings constantly equal to
`j` on `A` is exactly an `ell ^ A.card` fraction of all colorings. -/
theorem card_fixedColor_mul_pow (A : Finset W) {ell : Nat} (j : Fin ell) :
    Fintype.card {color : W -> Fin ell // ∀ w ∈ A, color w = j} * ell ^ A.card =
      Fintype.card (W -> Fin ell) := by
  classical
  rw [← Fintype.card_congr (fixedColorEquiv A j), Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-- Finset form of `card_fixedColor_mul_pow`. -/
theorem card_filter_fixedColor_mul_pow (A : Finset W) {ell : Nat} (j : Fin ell) :
    ((Finset.univ : Finset (W -> Fin ell)).filter
      fun color => ∀ w ∈ A, color w = j).card * ell ^ A.card =
        Fintype.card (W -> Fin ell) := by
  classical
  let e :
      {color // color ∈ ((Finset.univ : Finset (W -> Fin ell)).filter
        fun color => ∀ w ∈ A, color w = j)} ≃
        {color : W -> Fin ell // ∀ w ∈ A, color w = j} :=
    { toFun := fun color => ⟨color.1, (Finset.mem_filter.mp color.2).2⟩
      invFun := fun color => ⟨color.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, color.2⟩⟩
      left_inv := fun color => Subtype.ext rfl
      right_inv := fun color => Subtype.ext rfl }
  rw [← Fintype.card_coe, Fintype.card_congr e]
  exact card_fixedColor_mul_pow A j

/-- Weighted finite-sum form of the uniform coloring count. -/
theorem sum_ite_fixedColor_mul_pow (A : Finset W) {ell : Nat} (j : Fin ell)
    (weight : Nat) :
    (∑ color : W -> Fin ell,
      if (∀ w ∈ A, color w = j) then weight else 0) * ell ^ A.card =
        Fintype.card (W -> Fin ell) * weight := by
  classical
  have hsum : ∀ colors : Finset (W -> Fin ell),
      (∑ color ∈ colors,
        if (∀ w ∈ A, color w = j) then weight else 0) =
          (colors.filter fun color => ∀ w ∈ A, color w = j).card * weight := by
    intro colors
    induction colors using Finset.induction_on with
    | empty => simp
    | @insert color colors hcolor ih =>
        rw [Finset.sum_insert hcolor, ih, Finset.filter_insert]
        by_cases hfixed : ∀ w ∈ A, color w = j
        · rw [if_pos hfixed, if_pos hfixed,
            Finset.card_insert_of_notMem (by simp [hcolor])]
          rw [Nat.add_mul, one_mul, Nat.add_comm]
        · rw [if_neg hfixed, if_neg hfixed]
          simp
  rw [show (∑ color : W -> Fin ell,
      if (∀ w ∈ A, color w = j) then weight else 0) =
        ((Finset.univ : Finset (W -> Fin ell)).filter
          fun color => ∀ w ∈ A, color w = j).card * weight by
      simpa using hsum Finset.univ]
  calc
    ((Finset.univ.filter fun color : W -> Fin ell =>
        ∀ w ∈ A, color w = j).card * weight) * ell ^ A.card =
        ((Finset.univ.filter fun color : W -> Fin ell =>
          ∀ w ∈ A, color w = j).card * ell ^ A.card) * weight := by
          ac_rfl
    _ = Fintype.card (W -> Fin ell) * weight := by
      rw [card_filter_fixedColor_mul_pow A j]

theorem sum_ite_const_eq_filter_card_mul
    {A : Type*} [DecidableEq A] (s : Finset A) (p : A -> Prop)
    [DecidablePred p] (weight : Nat) :
    (∑ x ∈ s, if p x then weight else 0) = (s.filter p).card * weight := by
  rw [Finset.sum_ite]
  simp

/-- A fixed vertex receives a prescribed color in exactly a cleared
`1 / ell` fraction of all colorings. -/
theorem sum_ite_vertexColor_mul (w : W) {ell : Nat} (j : Fin ell)
    (weight : Nat) :
    (∑ color : W -> Fin ell, if color w = j then weight else 0) * ell =
      Fintype.card (W -> Fin ell) * weight := by
  simpa using sum_ite_fixedColor_mul_pow ({w} : Finset W) j weight

/-- Weighted size of one color class inside a prescribed vertex set. -/
def weightedColorClassSum {ell : Nat} (vertices : Finset W)
    (weight : W -> Nat) (color : W -> Fin ell) (j : Fin ell) : Nat :=
  ∑ w ∈ vertices, if color w = j then weight w else 0

/-- Exact cleared first moment of a weighted color class. -/
theorem sum_weightedColorClassSum_mul
    (vertices : Finset W) (weight : W -> Nat)
    {ell : Nat} (j : Fin ell) :
    (∑ color : W -> Fin ell,
      weightedColorClassSum vertices weight color j) * ell =
        Fintype.card (W -> Fin ell) * ∑ w ∈ vertices, weight w := by
  classical
  unfold weightedColorClassSum
  rw [Finset.sum_comm, Finset.sum_mul]
  calc
    (∑ w ∈ vertices,
      (∑ color : W -> Fin ell, if color w = j then weight w else 0) * ell) =
        ∑ w ∈ vertices, Fintype.card (W -> Fin ell) * weight w := by
          apply Finset.sum_congr rfl
          intro w _
          exact sum_ite_vertexColor_mul w j (weight w)
    _ = Fintype.card (W -> Fin ell) * ∑ w ∈ vertices, weight w := by
      rw [Finset.mul_sum]

/-- Joint weighted count for two vertices, with a uniform square denominator.
The diagonal has one free color and therefore contributes one extra factor of
`ell`. -/
theorem sum_ite_vertexPairColor_mul_sq
    (x y : W) {ell : Nat} (j : Fin ell) (weight : Nat) :
    (∑ color : W -> Fin ell,
      if color x = j ∧ color y = j then weight else 0) * ell ^ 2 =
        if x = y then Fintype.card (W -> Fin ell) * weight * ell
        else Fintype.card (W -> Fin ell) * weight := by
  classical
  by_cases hxy : x = y
  · subst y
    simp only [and_self, if_true]
    rw [pow_two, ← Nat.mul_assoc,
      sum_ite_vertexColor_mul x j weight]
  · rw [if_neg hxy]
    simpa [hxy] using
      sum_ite_fixedColor_mul_pow ({x, y} : Finset W) j weight

/-- Exact cleared second moment of a weighted color class. -/
theorem sum_weightedColorClassSum_sq_mul_sq
    (vertices : Finset W) (weight : W -> Nat)
    {ell : Nat} (j : Fin ell) (hell : 0 < ell) :
    (∑ color : W -> Fin ell,
      (weightedColorClassSum vertices weight color j) ^ 2) * ell ^ 2 =
        Fintype.card (W -> Fin ell) *
          ((∑ w ∈ vertices, weight w) ^ 2 +
            (ell - 1) * ∑ w ∈ vertices, (weight w) ^ 2) := by
  classical
  have hsquare : ∀ color : W -> Fin ell,
      (weightedColorClassSum vertices weight color j) ^ 2 =
        ∑ x ∈ vertices, ∑ y ∈ vertices,
          if color x = j ∧ color y = j then weight x * weight y else 0 := by
    intro color
    unfold weightedColorClassSum
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : color x = j <;> by_cases hy : color y = j <;>
      simp [hx, hy]
  simp_rw [hsquare]
  rw [show (∑ color : W -> Fin ell, ∑ x ∈ vertices, ∑ y ∈ vertices,
      if color x = j ∧ color y = j then weight x * weight y else 0) =
      ∑ x ∈ vertices, ∑ y ∈ vertices, ∑ color : W -> Fin ell,
        if color x = j ∧ color y = j then weight x * weight y else 0 by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]]
  rw [Finset.sum_mul]
  calc
    (∑ x ∈ vertices, (∑ y ∈ vertices, ∑ color : W -> Fin ell,
      if color x = j ∧ color y = j then weight x * weight y else 0) * ell ^ 2) =
      ∑ x ∈ vertices, ∑ y ∈ vertices,
        Fintype.card (W -> Fin ell) *
          (weight x * weight y +
            if x = y then (ell - 1) * (weight x) ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [sum_ite_vertexPairColor_mul_sq x y j (weight x * weight y)]
      by_cases hxy : x = y
      · subst y
        rw [if_pos rfl, if_pos rfl]
        calc
          Fintype.card (W -> Fin ell) * (weight x * weight x) * ell =
              Fintype.card (W -> Fin ell) * (weight x * weight x) *
                ((ell - 1) + 1) := by
            apply congrArg (fun z =>
              Fintype.card (W -> Fin ell) * (weight x * weight x) * z)
            omega
          _ = Fintype.card (W -> Fin ell) *
              (weight x * weight x + (ell - 1) * weight x ^ 2) := by ring
      · simp [hxy]
    _ = Fintype.card (W -> Fin ell) *
        ((∑ w ∈ vertices, weight w) ^ 2 +
          (ell - 1) * ∑ w ∈ vertices, (weight w) ^ 2) := by
      let N := Fintype.card (W -> Fin ell)
      have hfactor (f : W -> W -> Nat) :
          (∑ x ∈ vertices, ∑ y ∈ vertices, N * f x y) =
            N * ∑ x ∈ vertices, ∑ y ∈ vertices, f x y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      have hbase :
          (∑ x ∈ vertices, ∑ y ∈ vertices, weight x * weight y) =
            (∑ w ∈ vertices, weight w) ^ 2 := by
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      have hdiag :
          (∑ x ∈ vertices, ∑ y ∈ vertices,
            if x = y then (ell - 1) * weight x ^ 2 else 0) =
              (ell - 1) * ∑ x ∈ vertices, weight x ^ 2 := by
        calc
          (∑ x ∈ vertices, ∑ y ∈ vertices,
            if x = y then (ell - 1) * weight x ^ 2 else 0) =
              ∑ x ∈ vertices, (ell - 1) * weight x ^ 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            simpa [eq_comm, hx] using
              Finset.sum_ite_eq' vertices x
                (fun _y => (ell - 1) * weight x ^ 2)
          _ = (ell - 1) * ∑ x ∈ vertices, weight x ^ 2 := by
            rw [Finset.mul_sum]
      calc
        (∑ x ∈ vertices, ∑ y ∈ vertices,
          N * (weight x * weight y +
            if x = y then (ell - 1) * weight x ^ 2 else 0)) =
            (∑ x ∈ vertices, ∑ y ∈ vertices, N * (weight x * weight y)) +
            (∑ x ∈ vertices, ∑ y ∈ vertices,
              N * (if x = y then (ell - 1) * weight x ^ 2 else 0)) := by
          simp_rw [Nat.mul_add, Finset.sum_add_distrib]
        _ = N * (∑ x ∈ vertices, ∑ y ∈ vertices, weight x * weight y) +
            N * (∑ x ∈ vertices, ∑ y ∈ vertices,
              if x = y then (ell - 1) * weight x ^ 2 else 0) := by
          rw [hfactor, hfactor]
        _ = N * ((∑ w ∈ vertices, weight w) ^ 2 +
            (ell - 1) * ∑ w ∈ vertices, weight w ^ 2) := by
          rw [hbase, hdiag, Nat.mul_add]

/-- One-sided weighted color-class variance, stated entirely as a finite sum. -/
theorem sum_upperDeviationSq_weightedColorClass_le
    (vertices : Finset W) (weight : W -> Nat)
    {ell : Nat} (j : Fin ell) (hell : 0 < ell) :
    (∑ color : W -> Fin ell,
      upperDeviationSq
        (ell * weightedColorClassSum vertices weight color j)
        (∑ w ∈ vertices, weight w)) <=
      Fintype.card (W -> Fin ell) * (ell - 1) *
        (∑ w ∈ vertices, (weight w) ^ 2) := by
  classical
  let N := Fintype.card (W -> Fin ell)
  let S := ∑ w ∈ vertices, weight w
  let Q := ∑ w ∈ vertices, (weight w) ^ 2
  let D : (W -> Fin ell) -> Nat := fun color =>
    weightedColorClassSum vertices weight color j
  have hfirst : (∑ color : W -> Fin ell, D color) * ell = N * S := by
    simpa [D, N, S] using sum_weightedColorClassSum_mul vertices weight j
  have hsecond : (∑ color : W -> Fin ell, (D color) ^ 2) * ell ^ 2 =
      N * (S ^ 2 + (ell - 1) * Q) := by
    simpa [D, N, S, Q] using
      sum_weightedColorClassSum_sq_mul_sq vertices weight j hell
  have hcross :
      (∑ color : W -> Fin ell, 2 * (ell * D color) * S) = 2 * N * S ^ 2 := by
    have hinner :
        (∑ color : W -> Fin ell, 2 * (ell * D color)) =
          2 * ell * ∑ color : W -> Fin ell, D color := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    calc
      (∑ color : W -> Fin ell, 2 * (ell * D color) * S) =
          (∑ color : W -> Fin ell, 2 * (ell * D color)) * S := by
        rw [Finset.sum_mul]
      _ =
          2 * S * ((∑ color : W -> Fin ell, D color) * ell) := by
        rw [hinner]
        ring
      _ = 2 * S * (N * S) := by rw [hfirst]
      _ = 2 * N * S ^ 2 := by ring
  have hsquares :
      (∑ color : W -> Fin ell, (ell * D color) ^ 2) =
        N * (S ^ 2 + (ell - 1) * Q) := by
    calc
      (∑ color : W -> Fin ell, (ell * D color) ^ 2) =
          (∑ color : W -> Fin ell, (D color) ^ 2) * ell ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = N * (S ^ 2 + (ell - 1) * Q) := hsecond
  have hcombined :
      (∑ color : W -> Fin ell,
          upperDeviationSq (ell * D color) S) + 2 * N * S ^ 2 <=
        N * (S ^ 2 + (ell - 1) * Q) + N * S ^ 2 := by
    calc
      (∑ color : W -> Fin ell,
          upperDeviationSq (ell * D color) S) + 2 * N * S ^ 2 =
          ∑ color : W -> Fin ell,
            (upperDeviationSq (ell * D color) S + 2 * (ell * D color) * S) := by
        rw [Finset.sum_add_distrib, hcross]
      _ <= ∑ color : W -> Fin ell,
          ((ell * D color) ^ 2 + S ^ 2) := by
        apply Finset.sum_le_sum
        intro color _
        exact upperDeviationSq_add_two_mul_le (ell * D color) S
      _ = N * (S ^ 2 + (ell - 1) * Q) + N * S ^ 2 := by
        rw [Finset.sum_add_distrib, hsquares]
        simp [N]
  have hnormalize :
      N * (S ^ 2 + (ell - 1) * Q) + N * S ^ 2 =
        2 * N * S ^ 2 + N * ((ell - 1) * Q) := by ring
  rw [hnormalize] at hcombined
  change (∑ color : W -> Fin ell,
      upperDeviationSq (ell * D color) S) <= N * (ell - 1) * Q
  have hmul : N * ((ell - 1) * Q) = N * (ell - 1) * Q := by ring
  rw [← hmul]
  omega

/-- The two endpoints of a loopless named edge receive one prescribed color
in exactly a cleared `1 / ell^2` fraction of all colorings. -/
theorem sum_ite_edgeColor_mul_sq (H : FiniteEdgeIndexedGraph W) (e : H.Edge)
    {ell : Nat} (j : Fin ell) (weight : Nat) :
    (∑ color : W -> Fin ell,
      if color (H.left e) = j ∧ color (H.right e) = j then weight else 0) * ell ^ 2 =
        Fintype.card (W -> Fin ell) * weight := by
  simpa [H.end_ne e] using
    sum_ite_fixedColor_mul_pow ({H.left e, H.right e} : Finset W) j weight

/-- The two-element endpoint set of a named edge. -/
def edgeEnds (H : FiniteEdgeIndexedGraph W) (e : H.Edge) : Finset W :=
  {H.left e, H.right e}

/-- Edges in `edges` sharing at least one endpoint with `e`. -/
noncomputable def overlappingEdges (H : FiniteEdgeIndexedGraph W)
    (edges : Finset H.Edge) (e : H.Edge) : Finset H.Edge := by
  classical
  exact edges.filter fun f => ¬ Disjoint (edgeEnds H e) (edgeEnds H f)

@[simp] theorem card_edgeEnds (H : FiniteEdgeIndexedGraph W) (e : H.Edge) :
    (edgeEnds H e).card = 2 := by
  simp [edgeEnds, H.end_ne e]

theorem card_edgeEnds_union_le_four (H : FiniteEdgeIndexedGraph W) (e f : H.Edge) :
    ((edgeEnds H e) ∪ (edgeEnds H f)).card <= 4 := by
  calc
    ((edgeEnds H e) ∪ (edgeEnds H f)).card <=
        (edgeEnds H e).card + (edgeEnds H f).card :=
      Finset.card_union_le (edgeEnds H e) (edgeEnds H f)
    _ = 4 := by simp

theorem overlappingEdges_subset_incidentUnion
    (H : FiniteEdgeIndexedGraph W) (edges : Finset H.Edge) (e : H.Edge) :
    overlappingEdges H edges e ⊆
      H.incidentEdges (H.left e) ∪ H.incidentEdges (H.right e) := by
  classical
  intro f hf
  have hoverlap := (Finset.mem_filter.mp hf).2
  rcases Finset.not_disjoint_iff.mp hoverlap with ⟨w, hwe, hwf⟩
  simp only [edgeEnds, Finset.mem_insert, Finset.mem_singleton] at hwe hwf
  rcases hwe with hwe | hwe
  · subst w
    exact Finset.mem_union_left _ ((H.mem_incidentEdges (H.left e) f).mpr
      (by simpa [eq_comm] using hwf))
  · subst w
    exact Finset.mem_union_right _ ((H.mem_incidentEdges (H.right e) f).mpr
      (by simpa [eq_comm] using hwf))

theorem edgePairKernel_le_one_add_overlap
    (H : FiniteEdgeIndexedGraph W) (e f : H.Edge)
    {ell : Nat} (hell : 0 < ell) :
    ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card) <=
      1 + if ¬ Disjoint (edgeEnds H e) (edgeEnds H f) then ell ^ 2 else 0 := by
  classical
  by_cases hoverlap : ¬ Disjoint (edgeEnds H e) (edgeEnds H f)
  · rw [if_pos hoverlap]
    have htwo : 2 <= ((edgeEnds H e) ∪ (edgeEnds H f)).card := by
      simpa using Finset.card_le_card (Finset.subset_union_left :
        edgeEnds H e ⊆ edgeEnds H e ∪ edgeEnds H f)
    have hexponent : 4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card <= 2 := by omega
    have hpow := Nat.pow_le_pow_right hell hexponent
    omega
  · have hdisjoint : Disjoint (edgeEnds H e) (edgeEnds H f) := by
      exact not_not.mp hoverlap
    have hcard : ((edgeEnds H e) ∪ (edgeEnds H f)).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisjoint]
      simp
    simp [hoverlap, hcard]

/-- Exact joint coloring count for two named edges, whether equal, adjacent,
or vertex-disjoint. -/
theorem sum_ite_edgePairColor_mul_unionPow
    (H : FiniteEdgeIndexedGraph W) (e f : H.Edge)
    {ell : Nat} (j : Fin ell) (weight : Nat) :
    (∑ color : W -> Fin ell,
      if (color (H.left e) = j ∧ color (H.right e) = j) ∧
          (color (H.left f) = j ∧ color (H.right f) = j)
        then weight else 0) *
        ell ^ ((edgeEnds H e) ∪ (edgeEnds H f)).card =
      Fintype.card (W -> Fin ell) * weight := by
  simpa [edgeEnds, and_assoc, and_left_comm, and_comm] using
    sum_ite_fixedColor_mul_pow ((edgeEnds H e) ∪ (edgeEnds H f)) j weight

/-- The same joint count with the uniform fourth-power denominator used when
summing over all ordered edge pairs. -/
theorem sum_ite_edgePairColor_mul_pow_four
    (H : FiniteEdgeIndexedGraph W) (e f : H.Edge)
    {ell : Nat} (j : Fin ell) (weight : Nat) :
    (∑ color : W -> Fin ell,
      if (color (H.left e) = j ∧ color (H.right e) = j) ∧
          (color (H.left f) = j ∧ color (H.right f) = j)
        then weight else 0) * ell ^ 4 =
      Fintype.card (W -> Fin ell) * weight *
        ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card) := by
  let r := ((edgeEnds H e) ∪ (edgeEnds H f)).card
  have hr : r <= 4 := card_edgeEnds_union_le_four H e f
  have hpow : ell ^ 4 = ell ^ r * ell ^ (4 - r) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, ← Nat.mul_assoc,
    sum_ite_edgePairColor_mul_unionPow H e f j weight]

/-- Exact denominator-cleared first moment for the number of edges in an
arbitrary named-edge family whose endpoints both receive `j`. -/
theorem sum_monochromaticEdgeCount_mul_sq
    (H : FiniteEdgeIndexedGraph W) (edges : Finset H.Edge)
    {ell : Nat} (j : Fin ell) :
    (∑ color : W -> Fin ell,
      ∑ e ∈ edges,
        if color (H.left e) = j ∧ color (H.right e) = j then 1 else 0) * ell ^ 2 =
      Fintype.card (W -> Fin ell) * edges.card := by
  classical
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  calc
    (∑ e ∈ edges,
        (∑ color : W -> Fin ell,
          if color (H.left e) = j ∧ color (H.right e) = j then 1 else 0) * ell ^ 2) =
        ∑ _e ∈ edges, Fintype.card (W -> Fin ell) := by
          apply Finset.sum_congr rfl
          intro e _
          simpa using sum_ite_edgeColor_mul_sq H e j 1
    _ = Fintype.card (W -> Fin ell) * edges.card := by
      simp [Nat.mul_comm]

/-- Exact fourth-power-cleared second raw moment of a monochromatic named-edge
count.  Equal edge pairs contribute `ell^2`, adjacent distinct pairs
contribute `ell`, and vertex-disjoint pairs contribute `1`; the endpoint-union
form records all three cases without a separate adjacency definition. -/
theorem sum_monochromaticEdgeCount_sq_mul_pow_four
    (H : FiniteEdgeIndexedGraph W) (edges : Finset H.Edge)
    {ell : Nat} (j : Fin ell) :
    (∑ color : W -> Fin ell,
      (∑ e ∈ edges,
        if color (H.left e) = j ∧ color (H.right e) = j then 1 else 0) ^ 2) * ell ^ 4 =
      Fintype.card (W -> Fin ell) *
        (∑ e ∈ edges, ∑ f ∈ edges,
          ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)) := by
  classical
  have hsquare : ∀ color : W -> Fin ell,
      (∑ e ∈ edges,
        if color (H.left e) = j ∧ color (H.right e) = j then 1 else 0) ^ 2 =
      ∑ e ∈ edges, ∑ f ∈ edges,
        if (color (H.left e) = j ∧ color (H.right e) = j) ∧
            (color (H.left f) = j ∧ color (H.right f) = j)
          then 1 else 0 := by
    intro color
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hec : color (H.left e) = j ∧ color (H.right e) = j <;>
      by_cases hfc : color (H.left f) = j ∧ color (H.right f) = j <;>
        simp [hec, hfc]
  simp_rw [hsquare]
  rw [show (∑ color : W -> Fin ell, ∑ e ∈ edges, ∑ f ∈ edges,
      if (color (H.left e) = j ∧ color (H.right e) = j) ∧
          (color (H.left f) = j ∧ color (H.right f) = j) then 1 else 0) =
      ∑ e ∈ edges, ∑ f ∈ edges, ∑ color : W -> Fin ell,
        if (color (H.left e) = j ∧ color (H.right e) = j) ∧
            (color (H.left f) = j ∧ color (H.right f) = j) then 1 else 0 by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm]]
  rw [Finset.sum_mul]
  calc
    (∑ e ∈ edges, (∑ f ∈ edges, ∑ color : W -> Fin ell,
      if (color (H.left e) = j ∧ color (H.right e) = j) ∧
          (color (H.left f) = j ∧ color (H.right f) = j) then 1 else 0) * ell ^ 4) =
      ∑ e ∈ edges, ∑ f ∈ edges,
        Fintype.card (W -> Fin ell) *
          ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      simpa using sum_ite_edgePairColor_mul_pow_four H e f j 1
    _ = Fintype.card (W -> Fin ell) *
        (∑ e ∈ edges, ∑ f ∈ edges,
          ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]

/-- Named edges whose two endpoints both lie in `X`. -/
noncomputable def internalEdges (H : FiniteEdgeIndexedGraph W)
    (X : Finset W) : Finset H.Edge := by
  classical
  exact Finset.univ.filter fun e => H.left e ∈ X ∧ H.right e ∈ X

@[simp] theorem mem_internalEdges (H : FiniteEdgeIndexedGraph W)
    (X : Finset W) (e : H.Edge) :
    e ∈ internalEdges H X ↔ H.left e ∈ X ∧ H.right e ∈ X := by
  simp [internalEdges]

/-- The nonterminal color class indexed by `j`.  Terminal colors are ignored. -/
noncomputable def colorBlock (terminals : Finset W) {ell : Nat}
    (color : W -> Fin ell) (j : Fin ell) : Finset W := by
  classical
  exact (Finset.univ \ terminals).filter fun w => color w = j

@[simp] theorem mem_colorBlock (terminals : Finset W) {ell : Nat}
    (color : W -> Fin ell) (j : Fin ell) (w : W) :
    w ∈ colorBlock terminals color j ↔ w ∉ terminals ∧ color w = j := by
  simp [colorBlock]

theorem colorBlock_subset_nonterminals (terminals : Finset W) {ell : Nat}
    (color : W -> Fin ell) (j : Fin ell) :
    colorBlock terminals color j ⊆ Finset.univ \ terminals := by
  intro w hw
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (mem_colorBlock _ _ _ _).mp hw |>.1⟩

theorem existsUnique_mem_colorBlock (terminals : Finset W) {ell : Nat}
    (color : W -> Fin ell) {w : W} (hw : w ∉ terminals) :
    ∃! j, w ∈ colorBlock terminals color j := by
  refine ⟨color w, (mem_colorBlock _ _ _ _).2 ⟨hw, rfl⟩, ?_⟩
  intro j hj
  exact (mem_colorBlock _ _ _ _).1 hj |>.2.symm

theorem colorBlock_disjoint (terminals : Finset W) {ell : Nat}
    (color : W -> Fin ell) {i j : Fin ell} (hij : i ≠ j) :
    Disjoint (colorBlock terminals color i) (colorBlock terminals color j) := by
  rw [Finset.disjoint_left]
  intro w hwi hwj
  exact hij (((mem_colorBlock _ _ _ _).1 hwi).2.symm.trans
    ((mem_colorBlock _ _ _ _).1 hwj).2)

/-- The original edges available to Claim 5.9, namely edges with two
nonterminal endpoints. -/
noncomputable def nonterminalEdges (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) : Finset H.Edge :=
  internalEdges H (Finset.univ \ terminals)

/-- The vertices which are colored in Claim 5.9. -/
def nonterminalVertices (terminals : Finset W) : Finset W :=
  Finset.univ \ terminals

/-- Source-faithful degree and terminal-incidence hypotheses for Claim 5.9.
The second field is the denominator-cleared form of
`2 * |E(H)| + terminalIncidences <= 5 * |E(H)|`. -/
structure Claim59MomentHypotheses (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (Delta : Nat) : Prop where
  maxDegree : ∀ w ∈ nonterminalVertices terminals, H.degree w <= Delta
  nonterminalDegreeSum_le :
    (∑ w ∈ nonterminalVertices terminals, H.degree w) <=
      5 * (nonterminalEdges H terminals).card

/-- Named-multigraph handshake identity restricted to a vertex set.  Internal
edge copies contribute twice and boundary copies contribute once. -/
theorem sum_degree_eq_two_mul_internalEdges_card_add_boundary_card
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) :
    (∑ w ∈ X, H.degree w) =
      2 * (internalEdges H X).card + (H.boundary X).card := by
  classical
  have hdegree (w : W) : H.degree w =
      ∑ e : H.Edge, if H.left e = w ∨ H.right e = w then 1 else 0 := by
    simp [FiniteEdgeIndexedGraph.degree, FiniteEdgeIndexedGraph.incidentEdges]
  have hincident (e : H.Edge) :
      (∑ w ∈ X, if H.left e = w ∨ H.right e = w then 1 else 0) =
        (if H.left e ∈ X then 1 else 0) +
          (if H.right e ∈ X then 1 else 0) := by
    have hpoint (w : W) :
        (if H.left e = w ∨ H.right e = w then 1 else 0) =
          (if H.left e = w then 1 else 0) +
            (if H.right e = w then 1 else 0) := by
      by_cases hl : H.left e = w <;> by_cases hr : H.right e = w <;>
        simp [hl, hr]
      exact (H.end_ne e) (hl.trans hr.symm)
    simp_rw [hpoint, Finset.sum_add_distrib]
    simp
  have hedge (e : H.Edge) :
      (if H.left e ∈ X then 1 else 0) +
          (if H.right e ∈ X then 1 else 0) =
        2 * (if e ∈ internalEdges H X then 1 else 0) +
          (if e ∈ H.boundary X then 1 else 0) := by
    by_cases hl : H.left e ∈ X <;> by_cases hr : H.right e ∈ X <;>
      simp [mem_internalEdges, FiniteEdgeIndexedGraph.Crosses, hl, hr]
  simp_rw [hdegree]
  rw [Finset.sum_comm]
  simp_rw [hincident, hedge, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [internalEdges, FiniteEdgeIndexedGraph.boundary]

/-- The nonterminal boundary is charged to pendant terminals. -/
theorem boundary_nonterminalVertices_card_le_terminal_card_of_degree_one
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1) :
    (H.boundary (nonterminalVertices terminals)).card <= terminals.card := by
  have hnonterminalCompl : nonterminalVertices terminals = terminalsᶜ := by
    ext w
    simp [nonterminalVertices]
  calc
    (H.boundary (nonterminalVertices terminals)).card =
        (H.boundary terminals).card := by
      rw [hnonterminalCompl, H.boundary_compl]
    _ <= ∑ t ∈ terminals, H.degree t := by
      have hhandshake :=
        sum_degree_eq_two_mul_internalEdges_card_add_boundary_card H terminals
      omega
    _ = terminals.card := by
      calc
        (∑ t ∈ terminals, H.degree t) = ∑ _t ∈ terminals, 1 := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hpendant t ht
        _ = terminals.card := by simp

/-- The source's identity
`sum_{v notin T} d(v) = 2|E(H-T)| + |out(T)|`, together with pendant
terminals and `|T| <= 3m`, supplies the degree-sum premise used by the finite
second-moment proof. -/
theorem claim59MomentHypotheses_of_pendantTerminals
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (Delta : Nat)
    (hmaxDegree : ∀ w ∈ nonterminalVertices terminals, H.degree w <= Delta)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (hterminalCard : terminals.card <=
      3 * (nonterminalEdges H terminals).card) :
    Claim59MomentHypotheses H terminals Delta := by
  refine ⟨hmaxDegree, ?_⟩
  have hhandshake :=
    sum_degree_eq_two_mul_internalEdges_card_add_boundary_card H
      (nonterminalVertices terminals)
  have hinternal : internalEdges H (nonterminalVertices terminals) =
      nonterminalEdges H terminals := rfl
  have hboundary :=
    boundary_nonterminalVertices_card_le_terminal_card_of_degree_one
      H terminals hpendant
  rw [hinternal] at hhandshake
  omega

theorem overlappingEdges_card_le_two_mul_maxDegree
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (Delta : Nat)
    (hhyp : Claim59MomentHypotheses H terminals Delta)
    {e : H.Edge} (he : e ∈ nonterminalEdges H terminals) :
    (overlappingEdges H (nonterminalEdges H terminals) e).card <= 2 * Delta := by
  have hends := (mem_internalEdges H (nonterminalVertices terminals) e).mp he
  have hleft := hhyp.maxDegree (H.left e) hends.1
  have hright := hhyp.maxDegree (H.right e) hends.2
  calc
    (overlappingEdges H (nonterminalEdges H terminals) e).card <=
        (H.incidentEdges (H.left e) ∪ H.incidentEdges (H.right e)).card :=
      Finset.card_le_card (overlappingEdges_subset_incidentUnion H _ e)
    _ <= H.degree (H.left e) + H.degree (H.right e) := by
      simpa [FiniteEdgeIndexedGraph.degree] using
        Finset.card_union_le (H.incidentEdges (H.left e)) (H.incidentEdges (H.right e))
    _ <= 2 * Delta := by omega

theorem edgePairKernel_sum_le
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (Delta ell : Nat) (hell : 0 < ell)
    (hhyp : Claim59MomentHypotheses H terminals Delta) :
    (∑ e ∈ nonterminalEdges H terminals,
      ∑ f ∈ nonterminalEdges H terminals,
        ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)) <=
      (nonterminalEdges H terminals).card ^ 2 +
        2 * (nonterminalEdges H terminals).card * Delta * ell ^ 2 := by
  classical
  let edges := nonterminalEdges H terminals
  let m := edges.card
  have hrow : ∀ e ∈ edges,
      (∑ f ∈ edges,
        ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)) <=
        m + 2 * Delta * ell ^ 2 := by
    intro e he
    calc
      (∑ f ∈ edges,
        ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)) <=
          ∑ f ∈ edges,
            (1 + if ¬ Disjoint (edgeEnds H e) (edgeEnds H f)
              then ell ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro f _
        exact edgePairKernel_le_one_add_overlap H e f hell
      _ = m + (overlappingEdges H edges e).card * ell ^ 2 := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, one_mul]
        rw [sum_ite_const_eq_filter_card_mul]
        simp [m, overlappingEdges]
      _ <= m + 2 * Delta * ell ^ 2 := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right (ell ^ 2)
            (overlappingEdges_card_le_two_mul_maxDegree H terminals Delta hhyp he)) m
  calc
    (∑ e ∈ edges,
      ∑ f ∈ edges,
        ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)) <=
        ∑ _e ∈ edges, (m + 2 * Delta * ell ^ 2) := by
      apply Finset.sum_le_sum
      intro e he
      exact hrow e he
    _ = edges.card * (m + 2 * Delta * ell ^ 2) := by simp
    _ = edges.card ^ 2 + 2 * edges.card * Delta * ell ^ 2 := by
      simp [m]
      ring

theorem boundary_subset_biUnion_incidentEdges
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) :
    H.boundary X ⊆ X.biUnion H.incidentEdges := by
  intro e he
  rcases (H.mem_boundary X e).mp he with h | h
  · exact Finset.mem_biUnion.mpr
      ⟨H.left e, h.1, (H.mem_incidentEdges (H.left e) e).mpr (Or.inl rfl)⟩
  · exact Finset.mem_biUnion.mpr
      ⟨H.right e, h.1, (H.mem_incidentEdges (H.right e) e).mpr (Or.inr rfl)⟩

theorem boundary_card_le_sum_degree
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) :
    (H.boundary X).card <= ∑ w ∈ X, H.degree w := by
  calc
    (H.boundary X).card <= (X.biUnion H.incidentEdges).card :=
      Finset.card_le_card (boundary_subset_biUnion_incidentEdges H X)
    _ <= ∑ w ∈ X, (H.incidentEdges w).card := Finset.card_biUnion_le
    _ = ∑ w ∈ X, H.degree w := rfl

theorem boundary_colorBlock_card_le_weightedColorClassSum
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    {ell : Nat} (color : W -> Fin ell) (j : Fin ell) :
    (H.boundary (colorBlock terminals color j)).card <=
      weightedColorClassSum (nonterminalVertices terminals) H.degree color j := by
  calc
    (H.boundary (colorBlock terminals color j)).card <=
        ∑ w ∈ colorBlock terminals color j, H.degree w :=
      boundary_card_le_sum_degree H (colorBlock terminals color j)
    _ = weightedColorClassSum (nonterminalVertices terminals) H.degree color j := by
      simp [colorBlock, nonterminalVertices, weightedColorClassSum,
        Finset.sum_filter]

theorem internalEdges_colorBlock_card_eq_sum (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) {ell : Nat} (color : W -> Fin ell) (j : Fin ell) :
    (internalEdges H (colorBlock terminals color j)).card =
      ∑ e ∈ nonterminalEdges H terminals,
        if color (H.left e) = j ∧ color (H.right e) = j then 1 else 0 := by
  classical
  have hfilter : internalEdges H (colorBlock terminals color j) =
      (nonterminalEdges H terminals).filter fun e =>
        color (H.left e) = j ∧ color (H.right e) = j := by
    ext e
    simp only [mem_internalEdges, mem_colorBlock, Finset.mem_filter,
      nonterminalEdges, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  rw [hfilter, Finset.card_filter]

/-- Exact cleared expectation of the internal-edge count in one color block. -/
theorem sum_internalEdges_colorBlock_card_mul_sq
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    {ell : Nat} (j : Fin ell) :
    (∑ color : W -> Fin ell,
      (internalEdges H (colorBlock terminals color j)).card) * ell ^ 2 =
        Fintype.card (W -> Fin ell) * (nonterminalEdges H terminals).card := by
  classical
  simp_rw [internalEdges_colorBlock_card_eq_sum]
  exact sum_monochromaticEdgeCount_mul_sq H (nonterminalEdges H terminals) j

/-- Exact cleared second raw moment of the actual internal-edge count in one
color block. -/
theorem sum_internalEdges_colorBlock_card_sq_mul_pow_four
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    {ell : Nat} (j : Fin ell) :
    (∑ color : W -> Fin ell,
      (internalEdges H (colorBlock terminals color j)).card ^ 2) * ell ^ 4 =
      Fintype.card (W -> Fin ell) *
        (∑ e ∈ nonterminalEdges H terminals,
          ∑ f ∈ nonterminalEdges H terminals,
            ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)) := by
  classical
  simp_rw [internalEdges_colorBlock_card_eq_sum]
  exact sum_monochromaticEdgeCount_sq_mul_pow_four H
    (nonterminalEdges H terminals) j

/-- The cleared outgoing-incidence observable `ell * |out(X_j)|`. -/
noncomputable def boundaryObservable (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) {ell : Nat} (color : W -> Fin ell)
    (j : Fin ell) : Nat :=
  ell * (H.boundary (colorBlock terminals color j)).card

theorem sum_boundary_upperDeviationSq_le
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (Delta ell : Nat) (hell : 0 < ell)
    (hhyp : Claim59MomentHypotheses H terminals Delta) :
    (∑ j : Fin ell, ∑ color : W -> Fin ell,
      upperDeviationSq (boundaryObservable H terminals color j)
        (5 * (nonterminalEdges H terminals).card)) <=
      Fintype.card (W -> Fin ell) * ell * (ell - 1) * Delta *
        (5 * (nonterminalEdges H terminals).card) := by
  classical
  let vertices := nonterminalVertices terminals
  let S := ∑ w ∈ vertices, H.degree w
  let Q := ∑ w ∈ vertices, (H.degree w) ^ 2
  let m := (nonterminalEdges H terminals).card
  let N := Fintype.card (W -> Fin ell)
  have hS : S <= 5 * m := by
    simpa [S, vertices, m] using hhyp.nonterminalDegreeSum_le
  have hQ : Q <= Delta * S := by
    unfold Q
    calc
      (∑ w ∈ vertices, H.degree w ^ 2) <=
          ∑ w ∈ vertices, Delta * H.degree w := by
        apply Finset.sum_le_sum
        intro w hw
        have hd := hhyp.maxDegree w (by simpa [vertices] using hw)
        nlinarith
      _ = Delta * S := by rw [Finset.mul_sum]
  have hfixed : ∀ j : Fin ell,
      (∑ color : W -> Fin ell,
        upperDeviationSq (boundaryObservable H terminals color j) (5 * m)) <=
        N * (ell - 1) * Delta * (5 * m) := by
    intro j
    have hpoint : ∀ color : W -> Fin ell,
        upperDeviationSq (boundaryObservable H terminals color j) (5 * m) <=
          upperDeviationSq
            (ell * weightedColorClassSum vertices H.degree color j) S := by
      intro color
      have hb := boundary_colorBlock_card_le_weightedColorClassSum
        H terminals color j
      have hmul : boundaryObservable H terminals color j <=
          ell * weightedColorClassSum vertices H.degree color j := by
        exact Nat.mul_le_mul_left ell hb
      unfold upperDeviationSq
      exact Nat.pow_le_pow_left (tsub_le_tsub hmul hS) 2
    calc
      (∑ color : W -> Fin ell,
        upperDeviationSq (boundaryObservable H terminals color j) (5 * m)) <=
          ∑ color : W -> Fin ell,
            upperDeviationSq
              (ell * weightedColorClassSum vertices H.degree color j) S := by
        apply Finset.sum_le_sum
        intro color _
        exact hpoint color
      _ <= N * (ell - 1) * Q := by
        simpa [N, S, Q, vertices] using
          sum_upperDeviationSq_weightedColorClass_le
            vertices H.degree j hell
      _ <= N * (ell - 1) * (Delta * S) :=
        Nat.mul_le_mul_left (N * (ell - 1)) hQ
      _ <= N * (ell - 1) * (Delta * (5 * m)) :=
        Nat.mul_le_mul_left (N * (ell - 1)) (Nat.mul_le_mul_left Delta hS)
      _ = N * (ell - 1) * Delta * (5 * m) := by ring
  calc
    (∑ j : Fin ell, ∑ color : W -> Fin ell,
      upperDeviationSq (boundaryObservable H terminals color j) (5 * m)) <=
        ∑ _j : Fin ell, N * (ell - 1) * Delta * (5 * m) := by
      apply Finset.sum_le_sum
      intro j _
      exact hfixed j
    _ = N * ell * (ell - 1) * Delta * (5 * m) := by
      simp
      ring

/-- Twice the cleared internal-edge observable
`ell^2 * |E(X_j)|`. -/
noncomputable def internalObservable (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) {ell : Nat} (color : W -> Fin ell)
    (j : Fin ell) : Nat :=
  2 * ell ^ 2 * (internalEdges H (colorBlock terminals color j)).card

theorem sum_internal_lowerDeviationSq_le
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (Delta ell : Nat) (hell : 0 < ell)
    (hhyp : Claim59MomentHypotheses H terminals Delta) :
    (∑ j : Fin ell, ∑ color : W -> Fin ell,
      lowerDeviationSq (internalObservable H terminals color j)
        (2 * (nonterminalEdges H terminals).card)) <=
      8 * Fintype.card (W -> Fin ell) *
        (nonterminalEdges H terminals).card * Delta * ell ^ 3 := by
  classical
  let N := Fintype.card (W -> Fin ell)
  let m := (nonterminalEdges H terminals).card
  let pairKernel :=
    ∑ e ∈ nonterminalEdges H terminals,
      ∑ f ∈ nonterminalEdges H terminals,
        ell ^ (4 - ((edgeEnds H e) ∪ (edgeEnds H f)).card)
  have hpair : pairKernel <= m ^ 2 + 2 * m * Delta * ell ^ 2 := by
    simpa [pairKernel, m] using edgePairKernel_sum_le H terminals Delta ell hell hhyp
  have hfixed : ∀ j : Fin ell,
      (∑ color : W -> Fin ell,
        lowerDeviationSq (internalObservable H terminals color j) (2 * m)) <=
        8 * N * m * Delta * ell ^ 2 := by
    intro j
    let I : (W -> Fin ell) -> Nat := fun color =>
      (internalEdges H (colorBlock terminals color j)).card
    have hfirst : (∑ color : W -> Fin ell, I color) * ell ^ 2 = N * m := by
      simpa [I, N, m] using sum_internalEdges_colorBlock_card_mul_sq H terminals j
    have hsecond : (∑ color : W -> Fin ell, (I color) ^ 2) * ell ^ 4 =
        N * pairKernel := by
      simpa [I, N, pairKernel] using
        sum_internalEdges_colorBlock_card_sq_mul_pow_four H terminals j
    have hcross :
        (∑ color : W -> Fin ell, 2 * (ell ^ 2 * I color) * m) =
          2 * N * m ^ 2 := by
      have hinner :
          (∑ color : W -> Fin ell, 2 * (ell ^ 2 * I color)) =
            2 * ell ^ 2 * ∑ color : W -> Fin ell, I color := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
      calc
        (∑ color : W -> Fin ell, 2 * (ell ^ 2 * I color) * m) =
            (∑ color : W -> Fin ell, 2 * (ell ^ 2 * I color)) * m := by
          rw [Finset.sum_mul]
        _ = 2 * m * ((∑ color : W -> Fin ell, I color) * ell ^ 2) := by
          rw [hinner]
          ring
        _ = 2 * m * (N * m) := by rw [hfirst]
        _ = 2 * N * m ^ 2 := by ring
    have hsquares :
        (∑ color : W -> Fin ell, (ell ^ 2 * I color) ^ 2) = N * pairKernel := by
      calc
        (∑ color : W -> Fin ell, (ell ^ 2 * I color) ^ 2) =
            (∑ color : W -> Fin ell, (I color) ^ 2) * ell ^ 4 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = N * pairKernel := hsecond
    have hcentered :
        (∑ color : W -> Fin ell,
          lowerDeviationSq (ell ^ 2 * I color) m) <=
            N * (2 * m * Delta * ell ^ 2) := by
      have hcombined :
          (∑ color : W -> Fin ell,
            lowerDeviationSq (ell ^ 2 * I color) m) + 2 * N * m ^ 2 <=
              N * pairKernel + N * m ^ 2 := by
        calc
          (∑ color : W -> Fin ell,
            lowerDeviationSq (ell ^ 2 * I color) m) + 2 * N * m ^ 2 =
              ∑ color : W -> Fin ell,
                (lowerDeviationSq (ell ^ 2 * I color) m +
                  2 * (ell ^ 2 * I color) * m) := by
            rw [Finset.sum_add_distrib, hcross]
          _ <= ∑ color : W -> Fin ell,
              ((ell ^ 2 * I color) ^ 2 + m ^ 2) := by
            apply Finset.sum_le_sum
            intro color _
            exact lowerDeviationSq_add_two_mul_le (ell ^ 2 * I color) m
          _ = N * pairKernel + N * m ^ 2 := by
            rw [Finset.sum_add_distrib, hsquares]
            simp [N]
      have hright : N * pairKernel + N * m ^ 2 <=
          2 * N * m ^ 2 + N * (2 * m * Delta * ell ^ 2) := by
        calc
          N * pairKernel + N * m ^ 2 <=
              N * (m ^ 2 + 2 * m * Delta * ell ^ 2) + N * m ^ 2 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left N hpair) _
          _ = 2 * N * m ^ 2 + N * (2 * m * Delta * ell ^ 2) := by ring
      have := hcombined.trans hright
      omega
    have hscale : ∀ color : W -> Fin ell,
        lowerDeviationSq (internalObservable H terminals color j) (2 * m) =
          4 * lowerDeviationSq (ell ^ 2 * I color) m := by
      intro color
      unfold lowerDeviationSq internalObservable
      change (2 * m - 2 * ell ^ 2 * I color) ^ 2 =
        4 * (m - ell ^ 2 * I color) ^ 2
      rw [show 2 * ell ^ 2 * I color = 2 * (ell ^ 2 * I color) by ring]
      rw [← Nat.mul_sub_left_distrib]
      ring
    simp_rw [hscale]
    rw [← Finset.mul_sum]
    calc
      4 * (∑ color : W -> Fin ell,
        lowerDeviationSq (ell ^ 2 * I color) m) <=
          4 * (N * (2 * m * Delta * ell ^ 2)) := Nat.mul_le_mul_left 4 hcentered
      _ = 8 * N * m * Delta * ell ^ 2 := by ring
  calc
    (∑ j : Fin ell, ∑ color : W -> Fin ell,
      lowerDeviationSq (internalObservable H terminals color j) (2 * m)) <=
        ∑ _j : Fin ell, 8 * N * m * Delta * ell ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact hfixed j
    _ = 8 * N * m * Delta * ell ^ 3 := by
      simp
      ring

/-- The exact sum of one-sided squared deviations over every coloring and
every block.  The centers are the paper proof's bounds `5m` for outgoing
incidence and `2m` for internal edges, after denominators are cleared. -/
noncomputable def densePartitionTotalMoment (H : FiniteEdgeIndexedGraph W)
    (terminals : Finset W) (ell : Nat) : Nat := by
  classical
  let m := (nonterminalEdges H terminals).card
  exact ∑ j : Fin ell, ∑ color : W -> Fin ell,
    (upperDeviationSq (boundaryObservable H terminals color j) (5 * m) +
      lowerDeviationSq (internalObservable H terminals color j) (2 * m))

/-- Deterministic aggregate form of the Claim 5.9 second-moment calculation.
The constant is intentionally loose; the source-faithful dependence is
`ell^3 * Delta * m`. -/
theorem densePartitionTotalMoment_le_thirteen
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (Delta ell : Nat) (hell : 0 < ell)
    (hhyp : Claim59MomentHypotheses H terminals Delta) :
    densePartitionTotalMoment H terminals ell <=
      13 * Fintype.card (W -> Fin ell) *
        (nonterminalEdges H terminals).card * Delta * ell ^ 3 := by
  classical
  let N := Fintype.card (W -> Fin ell)
  let m := (nonterminalEdges H terminals).card
  let boundaryMoment :=
    ∑ j : Fin ell, ∑ color : W -> Fin ell,
      upperDeviationSq (boundaryObservable H terminals color j) (5 * m)
  let internalMoment :=
    ∑ j : Fin ell, ∑ color : W -> Fin ell,
      lowerDeviationSq (internalObservable H terminals color j) (2 * m)
  have hboundary : boundaryMoment <= 5 * N * m * Delta * ell ^ 3 := by
    have h := sum_boundary_upperDeviationSq_le H terminals Delta ell hell hhyp
    change boundaryMoment <= N * ell * (ell - 1) * Delta * (5 * m) at h
    calc
      boundaryMoment <= N * ell * (ell - 1) * Delta * (5 * m) := h
      _ <= N * ell * ell * Delta * (5 * m) := by
        gcongr
        omega
      _ = 5 * N * m * Delta * ell ^ 2 := by ring
      _ <= 5 * N * m * Delta * ell ^ 3 := by
        exact Nat.mul_le_mul_left (5 * N * m * Delta)
          (Nat.pow_le_pow_right hell (by omega))
  have hinternal : internalMoment <= 8 * N * m * Delta * ell ^ 3 := by
    simpa [internalMoment, N, m] using
      sum_internal_lowerDeviationSq_le H terminals Delta ell hell hhyp
  calc
    densePartitionTotalMoment H terminals ell = boundaryMoment + internalMoment := by
      simp [densePartitionTotalMoment, boundaryMoment, internalMoment, m,
        Finset.sum_add_distrib]
    _ <= 5 * N * m * Delta * ell ^ 3 + 8 * N * m * Delta * ell ^ 3 :=
      Nat.add_le_add hboundary hinternal
    _ = 13 * N * m * Delta * ell ^ 3 := by ring

/-- Strict total-moment budget under the explicit numerical domination needed
by this second-moment proof. -/
theorem densePartitionTotalMoment_lt_of_claim59
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (Delta ell : Nat) (hell : 0 < ell)
    (hhyp : Claim59MomentHypotheses H terminals Delta)
    (hnumeric : 13 * ell ^ 3 * Delta < (nonterminalEdges H terminals).card) :
    densePartitionTotalMoment H terminals ell <
      Fintype.card (W -> Fin ell) * (nonterminalEdges H terminals).card ^ 2 := by
  let N := Fintype.card (W -> Fin ell)
  let m := (nonterminalEdges H terminals).card
  have hbound := densePartitionTotalMoment_le_thirteen
    H terminals Delta ell hell hhyp
  change densePartitionTotalMoment H terminals ell <= 13 * N * m * Delta * ell ^ 3
    at hbound
  have hm : 0 < m := by
    change 13 * ell ^ 3 * Delta < m at hnumeric
    omega
  have hN : 0 < N := by
    simp [N, Fintype.card_fun, hell]
  have hscale := Nat.mul_lt_mul_of_pos_left hnumeric (Nat.mul_pos hN hm)
  have hstrict : 13 * N * m * Delta * ell ^ 3 < N * m ^ 2 := by
    calc
      13 * N * m * Delta * ell ^ 3 = N * m * (13 * ell ^ 3 * Delta) := by ring
      _ < N * m * m := hscale
      _ = N * m ^ 2 := by ring
  exact hbound.trans_lt hstrict

/-- Deterministic finite-existence form of journal Claim 5.9 from its exact
second-moment inequality.  The result is an indexed partition of all
nonterminals.  For every block, outgoing named-edge incidence is strictly less
than `10m / ell`, and at least `m / (2 ell^2)` named original edges are
internal; both statements are kept in source-faithful cleared form. -/
theorem exists_densePartition_of_totalMoment_lt
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (ell : Nat)
    (hell : 0 < ell)
    (hmoment : densePartitionTotalMoment H terminals ell <
      Fintype.card (W -> Fin ell) * (nonterminalEdges H terminals).card ^ 2) :
    ∃ blocks : Fin ell -> Finset W,
      (forall j, blocks j ⊆ Finset.univ \ terminals) ∧
      (forall w, w ∉ terminals -> ∃! j, w ∈ blocks j) ∧
      (forall i j, i ≠ j -> Disjoint (blocks i) (blocks j)) ∧
      (forall j, ell * (H.boundary (blocks j)).card <
        10 * (nonterminalEdges H terminals).card) ∧
      (forall j, (nonterminalEdges H terminals).card <=
        2 * ell ^ 2 * (internalEdges H (blocks j)).card) := by
  classical
  let m := (nonterminalEdges H terminals).card
  let samples : Finset (W -> Fin ell) := Finset.univ
  let constraints : Finset (Fin ell × Bool) := Finset.univ
  let bad : (Fin ell × Bool) -> (W -> Fin ell) -> Prop := fun p color =>
    if p.2 then
      10 * m <= boundaryObservable H terminals color p.1
    else
      internalObservable H terminals color p.1 < m
  let cost : (Fin ell × Bool) -> (W -> Fin ell) -> Nat := fun p color =>
    if p.2 then
      upperDeviationSq (boundaryObservable H terminals color p.1) (5 * m)
    else
      lowerDeviationSq (internalObservable H terminals color p.1) (2 * m)
  have hcost : (∑ p ∈ constraints, ∑ color ∈ samples, cost p color) =
      densePartitionTotalMoment H terminals ell := by
    simp [constraints, samples, cost, densePartitionTotalMoment, m,
      Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib,
      add_comm]
  have hcharge : ∀ p ∈ constraints, ∀ color ∈ samples,
      bad p color -> m ^ 2 <= cost p color := by
    intro p _ color _ hbad
    cases p with
    | mk j side =>
      cases side
      · change internalObservable H terminals color j < m at hbad
        change m ^ 2 <=
          lowerDeviationSq (internalObservable H terminals color j) (2 * m)
        apply sq_le_lowerDeviationSq_of_add_le
        omega
      · change 10 * m <= boundaryObservable H terminals color j at hbad
        change m ^ 2 <=
          upperDeviationSq (boundaryObservable H terminals color j) (5 * m)
        apply sq_le_upperDeviationSq_of_add_le
        omega
  have hbudget : (∑ p ∈ constraints, ∑ color ∈ samples, cost p color) <
      samples.card * m ^ 2 := by
    rw [hcost]
    simpa [samples, m] using hmoment
  rcases exists_forall_not_bad_of_sum_cost_lt samples constraints bad cost (m ^ 2)
      hcharge hbudget with ⟨color, _hcolor, hgood⟩
  refine ⟨colorBlock terminals color, ?_, ?_, ?_, ?_, ?_⟩
  · exact colorBlock_subset_nonterminals terminals color
  · exact fun _ hw => existsUnique_mem_colorBlock terminals color hw
  · exact fun _ _ hij => colorBlock_disjoint terminals color hij
  · intro j
    have h := hgood (j, true) (by simp [constraints])
    change ¬ 10 * m <= boundaryObservable H terminals color j at h
    simpa [boundaryObservable, m] using Nat.lt_of_not_ge h
  · intro j
    have h := hgood (j, false) (by simp [constraints])
    change ¬ internalObservable H terminals color j < m at h
    simpa [internalObservable, m] using Nat.le_of_not_gt h

/-- Claim 5.9 from the explicit degree/incidence and numerical hypotheses used
by the finite second-moment argument. -/
theorem exists_densePartition_of_claim59
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W)
    (Delta ell : Nat) (hell : 0 < ell)
    (hhyp : Claim59MomentHypotheses H terminals Delta)
    (hnumeric : 13 * ell ^ 3 * Delta < (nonterminalEdges H terminals).card) :
    ∃ blocks : Fin ell -> Finset W,
      (forall j, blocks j ⊆ Finset.univ \ terminals) ∧
      (forall w, w ∉ terminals -> ∃! j, w ∈ blocks j) ∧
      (forall i j, i ≠ j -> Disjoint (blocks i) (blocks j)) ∧
      (forall j, ell * (H.boundary (blocks j)).card <
        10 * (nonterminalEdges H terminals).card) ∧
      (forall j, (nonterminalEdges H terminals).card <=
        2 * ell ^ 2 * (internalEdges H (blocks j)).card) := by
  apply exists_densePartition_of_totalMoment_lt H terminals ell hell
  exact densePartitionTotalMoment_lt_of_claim59
    H terminals Delta ell hell hhyp hnumeric

/-! ## Source-facing Claim 5.9 producer -/

/-- The journal Section 5 degree cap
`w0 = floor (k / (192 * ell0^3 * log k))`.  We use base-two natural
logarithm; this only makes the integral cap more explicit than the paper's
asymptotic logarithm convention. -/
def claim59SourceDegreeCap (k ell0 : Nat) : Nat :=
  k / (192 * ell0 ^ 3 * Nat.log 2 k)

/-- The actual Section 5 parameters imply the strict numerical budget used by
the finite second-moment proof.  The source facts are `k <= 3m` (Claim 5.3)
and maximum degree at most `w0`. -/
theorem thirteen_mul_cube_mul_claim59SourceDegreeCap_lt
    {k m ell0 : Nat} (hk : 2 <= k) (hell0 : 0 < ell0)
    (hkm : k <= 3 * m) :
    13 * ell0 ^ 3 * claim59SourceDegreeCap k ell0 < m := by
  have hlog : 0 < Nat.log 2 k := Nat.log_pos (by omega) hk
  let D := 192 * ell0 ^ 3 * Nat.log 2 k
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hcapMul : claim59SourceDegreeCap k ell0 * D <= k := by
    exact (Nat.le_div_iff_mul_le hD).mp (by simp [claim59SourceDegreeCap, D])
  have hlogOne : 1 <= Nat.log 2 k := hlog
  have hdenomGrow : 192 * ell0 ^ 3 <=
      192 * ell0 ^ 3 * Nat.log 2 k := by
    simpa using Nat.mul_le_mul_left (192 * ell0 ^ 3) hlogOne
  have hlarge : 192 * ell0 ^ 3 * claim59SourceDegreeCap k ell0 <= k := by
    calc
      192 * ell0 ^ 3 * claim59SourceDegreeCap k ell0 =
          claim59SourceDegreeCap k ell0 * (192 * ell0 ^ 3) := by ring
      _ <= claim59SourceDegreeCap k ell0 *
          (192 * ell0 ^ 3 * Nat.log 2 k) := by
        exact Nat.mul_le_mul_left _ hdenomGrow
      _ = claim59SourceDegreeCap k ell0 * D := by rfl
      _ <= k := hcapMul
  let x := ell0 ^ 3 * claim59SourceDegreeCap k ell0
  have hscaled : 192 * x <= 3 * m := by
    calc
      192 * x = 192 * ell0 ^ 3 * claim59SourceDegreeCap k ell0 := by
        simp [x]
        ring
      _ <= k := hlarge
      _ <= 3 * m := hkm
  have hm : 0 < m := by omega
  by_cases hx : x = 0
  · have hgoalZero : 13 * ell0 ^ 3 * claim59SourceDegreeCap k ell0 = 0 := by
      calc
        13 * ell0 ^ 3 * claim59SourceDegreeCap k ell0 = 13 * x := by
          simp [x]
          ring
        _ = 0 := by simp [hx]
    omega
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hx
    have htarget : 13 * x < m := by nlinarith
    calc
      13 * ell0 ^ 3 * claim59SourceDegreeCap k ell0 = 13 * x := by
        simp [x]
        ring
      _ < m := htarget

/-- Concrete journal Claim 5.9 producer for a legal contracted graph with
pendant terminals.  It derives the degree-sum moment premise from terminal
degree one and `|T| <= 3m`, and derives the strict moment budget from the
paper's `w0` parameter rather than asking either fact from the caller. -/
theorem exists_densePartition_of_pendant_source_parameters
    (H : FiniteEdgeIndexedGraph W) (terminals : Finset W) (ell0 : Nat)
    (hell0 : 0 < ell0) (hterminalTwo : 2 <= terminals.card)
    (hmaxDegree : ∀ w ∈ nonterminalVertices terminals,
      H.degree w <= claim59SourceDegreeCap terminals.card ell0)
    (hpendant : ∀ t ∈ terminals, H.degree t = 1)
    (hterminalCard : terminals.card <=
      3 * (nonterminalEdges H terminals).card) :
    ∃ blocks : Fin ell0 -> Finset W,
      (forall j, blocks j ⊆ Finset.univ \ terminals) ∧
      (forall w, w ∉ terminals -> ∃! j, w ∈ blocks j) ∧
      (forall i j, i ≠ j -> Disjoint (blocks i) (blocks j)) ∧
      (forall j, ell0 * (H.boundary (blocks j)).card <
        10 * (nonterminalEdges H terminals).card) ∧
      (forall j, (nonterminalEdges H terminals).card <=
        2 * ell0 ^ 2 * (internalEdges H (blocks j)).card) := by
  let Delta := claim59SourceDegreeCap terminals.card ell0
  have hhyp : Claim59MomentHypotheses H terminals Delta :=
    claim59MomentHypotheses_of_pendantTerminals H terminals Delta
      hmaxDegree hpendant hterminalCard
  have hnumeric :
      13 * ell0 ^ 3 * Delta < (nonterminalEdges H terminals).card := by
    exact thirteen_mul_cube_mul_claim59SourceDegreeCap_lt
      hterminalTwo hell0 hterminalCard
  exact exists_densePartition_of_claim59 H terminals Delta ell0 hell0
    hhyp hnumeric

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5DensePartition
end SimpleGraph

end Lax17Proofs
