import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic
import Lax17Proofs.Source.SinghLau

namespace Lax17Proofs

universe u v w

/-!
# Proof of Singh--Lau bounded-degree spanning-tree rounding

This file formalizes the cost-free specialization of Singh and Lau's
iterative-relaxation proof.  The residual edge set is kept as a
`Finset (Sym2 V)`, while weights are functions on the fixed finite coordinate
type `Sym2 V`.  Coordinates outside the residual edge set are required to be
zero.  This avoids changing the ambient vector space when zero-weight edges
are removed.

The proof follows Algorithm II and Lemma 4.2 of:

* Mohit Singh and Lap Chi Lau, *Approximating Minimum Bounded Degree Spanning
  Trees to within One of Optimal*, JACM 62(1), 2015.

The public theorem at the end has exactly the proposition
`BoundedDegreeSpanningTreeStatement` from `SinghLau.lean`.
-/

namespace SimpleGraph
namespace SinghLau


open Finset Set
open scoped BigOperators
noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Residual spanning-tree relaxation -/

/-- Edges of the residual set `A` with both endpoints in `S`. -/
noncomputable def residualInternalEdges
    (A : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact A.filter (PairInside S)

/-- Edges of the residual set `A` incident with `v`. -/
def residualIncidentEdges
    (A : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  A.filter fun e => v ∈ e

@[simp] theorem mem_residualInternalEdges
    {A : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} :
    e ∈ residualInternalEdges A S ↔ e ∈ A ∧ PairInside S e := by
  simp [residualInternalEdges]

@[simp] theorem mem_residualIncidentEdges
    {A : Finset (Sym2 V)} {v : V} {e : Sym2 V} :
    e ∈ residualIncidentEdges A v ↔ e ∈ A ∧ v ∈ e := by
  simp [residualIncidentEdges]

/-- A real-valued point of the residual polytope `P(A,W)`.

`W` is the set of vertices whose degree constraints remain active.  Keeping
the zero-outside-`A` field makes every residual polytope a subset of the same
finite-dimensional real vector space. -/
structure ResidualFeasible
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ)
    (y : Sym2 V → ℝ) : Prop where
  zero_outside : ∀ e, e ∉ A → y e = 0
  nonnegative : ∀ e ∈ A, 0 ≤ y e
  total :
    ∑ e ∈ A, y e = (Fintype.card V - 1 : ℕ)
  forest :
    ∀ S : Finset V, S ≠ Finset.univ →
      ∑ e ∈ residualInternalEdges A S, y e ≤ (S.card - 1 : ℕ)
  degree :
    ∀ v ∈ W, ∑ e ∈ residualIncidentEdges A v, y e ≤ B

/-- The edge set on which a residual point has positive weight. -/
def supportEdges
    (A : Finset (Sym2 V)) (y : Sym2 V → ℝ) : Finset (Sym2 V) :=
  A.filter fun e => 0 < y e

@[simp] theorem mem_supportEdges
    {A : Finset (Sym2 V)} {y : Sym2 V → ℝ} {e : Sym2 V} :
    e ∈ supportEdges A y ↔ e ∈ A ∧ 0 < y e := by
  simp [supportEdges]

/-- Degree cap retained for vertices whose LP degree constraint has already
been removed. -/
def InactiveCap
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ) : Prop :=
  ∀ v, v ∉ W → (residualIncidentEdges A v).card ≤ B + 1

theorem residualInternalEdges_mono
    {A A' : Finset (Sym2 V)} (hAA' : A' ⊆ A) (S : Finset V) :
    residualInternalEdges A' S ⊆ residualInternalEdges A S := by
  intro e he
  exact mem_residualInternalEdges.2
    ⟨hAA' (mem_residualInternalEdges.1 he).1,
      (mem_residualInternalEdges.1 he).2⟩

theorem residualIncidentEdges_mono
    {A A' : Finset (Sym2 V)} (hAA' : A' ⊆ A) (v : V) :
    residualIncidentEdges A' v ⊆ residualIncidentEdges A v := by
  intro e he
  exact mem_residualIncidentEdges.2
    ⟨hAA' (mem_residualIncidentEdges.1 he).1,
      (mem_residualIncidentEdges.1 he).2⟩

theorem supportEdges_subset
    (A : Finset (Sym2 V)) (y : Sym2 V → ℝ) :
    supportEdges A y ⊆ A := by
  intro e he
  exact (mem_supportEdges.1 he).1

/-- Restricting a feasible point to its support preserves residual
feasibility.  The function itself does not change: feasibility already forces
all discarded coordinates to be zero. -/
theorem ResidualFeasible.restrict_support
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y) :
    ResidualFeasible (supportEdges A y) W B y := by
  have hzero_of_not_pos : ∀ e ∈ A, ¬ 0 < y e → y e = 0 := by
    intro e heA hnot
    exact le_antisymm (le_of_not_gt hnot) (hy.nonnegative e heA)
  have hsum_restrict (F : Finset (Sym2 V)) (hFA : F ⊆ A) :
      ∑ e ∈ F.filter (fun e => 0 < y e), y e = ∑ e ∈ F, y e := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e heF
    split_ifs with hpos
    · rfl
    · simp [hzero_of_not_pos e (hFA heF) hpos]
  refine {
    zero_outside := ?_
    nonnegative := ?_
    total := ?_
    forest := ?_
    degree := ?_ }
  · intro e he
    by_cases heA : e ∈ A
    · exact hzero_of_not_pos e heA (fun hpos =>
        he (mem_supportEdges.2 ⟨heA, hpos⟩))
    · exact hy.zero_outside e heA
  · intro e he
    exact hy.nonnegative e (supportEdges_subset A y he)
  · simpa [supportEdges, residualInternalEdges] using hsum_restrict A (by simp)
      |>.trans hy.total
  · intro S hS
    have hfilter :
        residualInternalEdges (supportEdges A y) S =
          (residualInternalEdges A S).filter (fun e => 0 < y e) := by
      ext e
      simp [residualInternalEdges, supportEdges, and_assoc, and_left_comm,
        and_comm]
    rw [hfilter, hsum_restrict (residualInternalEdges A S)
      (by intro e he; exact (mem_residualInternalEdges.1 he).1)]
    exact hy.forest S hS
  · intro v hv
    have hfilter :
        residualIncidentEdges (supportEdges A y) v =
          (residualIncidentEdges A v).filter (fun e => 0 < y e) := by
      ext e
      simp [residualIncidentEdges, supportEdges, and_assoc, and_left_comm,
        and_comm]
    rw [hfilter, hsum_restrict (residualIncidentEdges A v)
      (by intro e he; exact (mem_residualIncidentEdges.1 he).1)]
    exact hy.degree v hv

/-- Removing an active degree constraint preserves feasibility. -/
theorem ResidualFeasible.mono_active
    {A : Finset (Sym2 V)} {W W' : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    (hW : W' ⊆ W) :
    ResidualFeasible A W' B y where
  zero_outside := hy.zero_outside
  nonnegative := hy.nonnegative
  total := hy.total
  forest := hy.forest
  degree := fun v hv => hy.degree v (hW hv)

/-- A point supported on `A'` can be viewed as a point on a larger allowed
edge set `A`; the newly allowed coordinates remain zero. -/
theorem ResidualFeasible.extend_allowed
    {A A' : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A' W B y)
    (hsub : A' ⊆ A) :
    ResidualFeasible A W B y := by
  have hsum_eq
      (F' F : Finset (Sym2 V))
      (hF' : F' ⊆ F) (hF'A' : F' ⊆ A')
      (houtside : ∀ e ∈ F, e ∉ F' → e ∉ A') :
      ∑ e ∈ F, y e = ∑ e ∈ F', y e := by
    rw [← Finset.sum_subset hF']
    intro e heF heNot
    exact hy.zero_outside e (houtside e heF heNot)
  refine {
    zero_outside := fun e heA =>
      hy.zero_outside e (fun heA' => heA (hsub heA'))
    nonnegative := ?_
    total := ?_
    forest := ?_
    degree := ?_ }
  · intro e heA
    by_cases heA' : e ∈ A'
    · exact hy.nonnegative e heA'
    · simp [hy.zero_outside e heA']
  · have hEq :
        ∑ e ∈ A, y e = ∑ e ∈ A', y e := by
      apply hsum_eq A' A hsub (by simp)
      intro e _ he
      exact he
    rw [hEq, hy.total]
  · intro S hS
    have hIntSub :
        residualInternalEdges A' S ⊆
          residualInternalEdges A S :=
      residualInternalEdges_mono hsub S
    have hEq :
        ∑ e ∈ residualInternalEdges A S, y e =
          ∑ e ∈ residualInternalEdges A' S, y e := by
      apply hsum_eq _ _ hIntSub
        (fun e he => (mem_residualInternalEdges.1 he).1)
      intro e heA heNot heA'
      exact heNot (mem_residualInternalEdges.2
        ⟨heA', (mem_residualInternalEdges.1 heA).2⟩)
    rw [hEq]
    exact hy.forest S hS
  · intro v hv
    have hIncSub :
        residualIncidentEdges A' v ⊆
          residualIncidentEdges A v :=
      residualIncidentEdges_mono hsub v
    have hEq :
        ∑ e ∈ residualIncidentEdges A v, y e =
          ∑ e ∈ residualIncidentEdges A' v, y e := by
      apply hsum_eq _ _ hIncSub
        (fun e he => (mem_residualIncidentEdges.1 he).1)
      intro e heA heNot heA'
      exact heNot (mem_residualIncidentEdges.2
        ⟨heA', (mem_residualIncidentEdges.1 heA).2⟩)
    rw [hEq]
    exact hy.degree v hv

/-- Zero-extend the rational point from host edges and cast it to `ℝ`. -/
noncomputable def initialRealWeight
    (G : _root_.SimpleGraph V) (B : ℕ)
    (point : FeasibleBoundedDegreePoint G B) :
    Sym2 V → ℝ :=
  fun e => if e ∈ G.edgeFinset then (point.weight e : ℝ) else 0

/-- Cast the rational point in the public interface to the real residual
polytope on all host edges. -/
theorem feasibleBoundedDegreePoint_residual
    (G : _root_.SimpleGraph V) (B : ℕ)
    (point : FeasibleBoundedDegreePoint G B) :
    ResidualFeasible G.edgeFinset Finset.univ B
      (initialRealWeight G B point) := by
  refine {
    zero_outside := ?_
    nonnegative := ?_
    total := ?_
    forest := ?_
    degree := ?_ }
  · intro e he
    simp [initialRealWeight, he]
  · intro e he
    simp only [initialRealWeight, if_pos he]
    exact_mod_cast point.nonnegative e he
  · calc
      ∑ e ∈ G.edgeFinset, initialRealWeight G B point e =
          ∑ e ∈ G.edgeFinset, (point.weight e : ℝ) := by
            apply Finset.sum_congr rfl
            intro e he
            simp [initialRealWeight, he]
      _ = (Fintype.card V - 1 : ℕ) := by
        exact_mod_cast point.total
  · intro S hS
    calc
      ∑ e ∈ residualInternalEdges G.edgeFinset S,
          initialRealWeight G B point e =
          ∑ e ∈ residualInternalEdges G.edgeFinset S,
            (point.weight e : ℝ) := by
            apply Finset.sum_congr rfl
            intro e he
            simp [initialRealWeight, (mem_residualInternalEdges.1 he).1]
      _ = ∑ e ∈ internalEdges G S, (point.weight e : ℝ) := by
        congr 1
        ext e
        simp [residualInternalEdges, internalEdges]
      _ ≤ (S.card - 1 : ℕ) := by
        exact_mod_cast point.forest S hS
  · intro v _hv
    calc
      ∑ e ∈ residualIncidentEdges G.edgeFinset v,
          initialRealWeight G B point e =
          ∑ e ∈ residualIncidentEdges G.edgeFinset v,
            (point.weight e : ℝ) := by
            apply Finset.sum_congr rfl
            intro e he
            simp [initialRealWeight, (mem_residualIncidentEdges.1 he).1]
      _ = ∑ e ∈ incidentEdges G v, (point.weight e : ℝ) := by
        congr 1
        ext e
        simp [residualIncidentEdges, incidentEdges]
      _ ≤ B := by
        exact_mod_cast point.degree v

/-! ## Elementary residual-polytope facts -/

theorem pairInside_toFinset_self (e : Sym2 V) :
    PairInside e.toFinset e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp [PairInside, Sym2.toFinset_mk_eq]

theorem pairInside_iff_toFinset_subset
    (S : Finset V) (e : Sym2 V) :
    PairInside S e ↔ e.toFinset ⊆ S := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [PairInside, Sym2.toFinset_mk_eq]
      constructor
      · rintro ⟨hu, hv⟩ x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hu
        · exact hv
      · intro h
        exact ⟨h (by simp), h (by simp)⟩

theorem sym2_toFinset_card_le_two (e : Sym2 V) :
    e.toFinset.card ≤ 2 := by
  rw [Sym2.card_toFinset]
  split_ifs <;> omega

/-- Lemma 2.1: every residual coordinate is at most one. -/
theorem ResidualFeasible.weight_le_one
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    {e : Sym2 V} (heA : e ∈ A) :
    y e ≤ 1 := by
  let S : Finset V := e.toFinset
  have heS : e ∈ residualInternalEdges A S :=
    mem_residualInternalEdges.2 ⟨heA, pairInside_toFinset_self e⟩
  have hsingle_internal :
      y e ≤ ∑ f ∈ residualInternalEdges A S, y f := by
    apply Finset.single_le_sum
    · intro f hf
      exact hy.nonnegative f (mem_residualInternalEdges.1 hf).1
    · exact heS
  by_cases hS : S = Finset.univ
  · have hsingle_total : y e ≤ ∑ f ∈ A, y f := by
      apply Finset.single_le_sum
      · exact hy.nonnegative
      · exact heA
    rw [hy.total] at hsingle_total
    have hcard : Fintype.card V ≤ 2 := by
      rw [← Finset.card_univ, ← hS]
      exact sym2_toFinset_card_le_two e
    norm_num at hsingle_total ⊢
    exact hsingle_total.trans (by
      exact_mod_cast (show Fintype.card V - 1 ≤ 1 by omega))
  · have hforest := hy.forest S hS
    have hcard : S.card - 1 ≤ 1 :=
      Nat.sub_le_iff_le_add |>.2 (by
        exact (sym2_toFinset_card_le_two e).trans (by omega))
    exact hsingle_internal.trans (hforest.trans (by exact_mod_cast hcard))

/-- Every coordinate of a residual point lies in `[0,1]`; outside `A` it is
zero. -/
theorem ResidualFeasible.weight_mem_unitInterval
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    (e : Sym2 V) :
    y e ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ A
  · exact ⟨hy.nonnegative e he, hy.weight_le_one he⟩
  · simp [hy.zero_outside e he]

/-! ## Extreme residual points -/

/-- The residual feasible set as a subset of the fixed real coordinate
space. -/
def residualPolytope
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ) :
    Set (Sym2 V → ℝ) :=
  {y | ResidualFeasible A W B y}

theorem extreme_restrict_support
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hext : y ∈ (residualPolytope A W B).extremePoints ℝ) :
    y ∈
      (residualPolytope (supportEdges A y) W B).extremePoints ℝ := by
  refine ⟨hy.restrict_support, ?_⟩
  intro z₁ hz₁ z₂ hz₂ hopen
  apply hext.2
  · exact hz₁.extend_allowed (supportEdges_subset A y)
  · exact hz₂.extend_allowed (supportEdges_subset A y)
  · exact hopen

theorem isClosed_residualPolytope
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ) :
    IsClosed (residualPolytope A W B) := by
  have hz :
      IsClosed {y : Sym2 V → ℝ | ∀ e, e ∉ A → y e = 0} := by
    convert (isClosed_iInter fun e : Sym2 V =>
      isClosed_iInter fun (_he : e ∉ A) =>
        isClosed_eq
          (continuous_apply e : Continuous fun y : Sym2 V → ℝ => y e)
          (continuous_const :
            Continuous fun _ : Sym2 V → ℝ => (0 : ℝ))) using 1 <;>
      ext y <;> simp
  have hn :
      IsClosed {y : Sym2 V → ℝ | ∀ e, e ∈ A → 0 ≤ y e} := by
    convert (isClosed_iInter fun e : Sym2 V =>
      isClosed_iInter fun (_he : e ∈ A) =>
        isClosed_le
          (continuous_const :
            Continuous fun _ : Sym2 V → ℝ => (0 : ℝ))
          (continuous_apply e : Continuous fun y : Sym2 V → ℝ => y e)) using 1 <;>
      ext y <;> simp
  have ht :
      IsClosed {y : Sym2 V → ℝ |
        ∑ e ∈ A, y e = (Fintype.card V - 1 : ℕ)} := by
    exact isClosed_eq (by fun_prop)
      (continuous_const : Continuous fun _ : Sym2 V → ℝ =>
        ((Fintype.card V - 1 : ℕ) : ℝ))
  have hf :
      IsClosed {y : Sym2 V → ℝ |
        ∀ S : Finset V, S ≠ Finset.univ →
          ∑ e ∈ residualInternalEdges A S, y e ≤ (S.card - 1 : ℕ)} := by
    convert (isClosed_iInter fun S : Finset V =>
      isClosed_iInter fun (_hS : S ≠ Finset.univ) => by
        have hc : Continuous (fun y : Sym2 V → ℝ =>
            ∑ e ∈ residualInternalEdges A S, y e) := by
          fun_prop
        exact isClosed_le hc
          (continuous_const : Continuous fun _ : Sym2 V → ℝ =>
            ((S.card - 1 : ℕ) : ℝ))) using 1 <;>
      ext y <;> simp
  have hd :
      IsClosed {y : Sym2 V → ℝ |
        ∀ v, v ∈ W →
          ∑ e ∈ residualIncidentEdges A v, y e ≤ B} := by
    convert (isClosed_iInter fun v : V =>
      isClosed_iInter fun (_hv : v ∈ W) => by
        have hc : Continuous (fun y : Sym2 V → ℝ =>
            ∑ e ∈ residualIncidentEdges A v, y e) := by
          fun_prop
        exact isClosed_le hc
          (continuous_const : Continuous fun _ : Sym2 V → ℝ => (B : ℝ))) using 1 <;>
      ext y <;> simp
  have hall := hz.inter (hn.inter (ht.inter (hf.inter hd)))
  rw [show residualPolytope A W B =
      {y : Sym2 V → ℝ | ∀ e, e ∉ A → y e = 0} ∩
        ({y : Sym2 V → ℝ | ∀ e, e ∈ A → 0 ≤ y e} ∩
          ({y : Sym2 V → ℝ |
              ∑ e ∈ A, y e = (((Fintype.card V - 1 : ℕ)) : ℝ)} ∩
            ({y : Sym2 V → ℝ |
              ∀ S : Finset V, S ≠ Finset.univ →
                ∑ e ∈ residualInternalEdges A S, y e ≤
                  (((S.card - 1 : ℕ)) : ℝ)} ∩
              {y : Sym2 V → ℝ | ∀ v, v ∈ W →
                ∑ e ∈ residualIncidentEdges A v, y e ≤ (B : ℝ)}))) by
    ext y
    constructor
    · intro hy
      exact ⟨hy.zero_outside,
        hy.nonnegative, hy.total, hy.forest, hy.degree⟩
    · rintro ⟨hz', hn', ht', hf', hd'⟩
      exact ⟨hz', hn', ht', hf', hd'⟩]
  exact hall

theorem residualPolytope_subset_unitCube
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ) :
    residualPolytope A W B ⊆
      Set.pi Set.univ (fun _ : Sym2 V => Set.Icc (0 : ℝ) 1) := by
  intro y hy
  rw [Set.mem_pi]
  intro e _he
  exact hy.weight_mem_unitInterval e

theorem isCompact_residualPolytope
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ) :
    IsCompact (residualPolytope A W B) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ : Sym2 V => isCompact_Icc)
    (isClosed_residualPolytope A W B)
    (residualPolytope_subset_unitCube A W B)

/-- A chosen extreme point exists in every nonempty residual polytope. -/
theorem exists_extreme_residual
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    (hne : (residualPolytope A W B).Nonempty) :
    ∃ y : Sym2 V → ℝ,
      y ∈ (residualPolytope A W B).extremePoints ℝ := by
  exact (isCompact_residualPolytope A W B).extremePoints_nonempty hne

/-! ## Tight rows and uncrossing -/

/-- The `0`-`1` indicator that an edge has both endpoints in `S`. -/
noncomputable def rankIndicator (S : Finset V) (e : Sym2 V) : ℝ := by
  classical
  exact if PairInside S e then 1 else 0

/-- The induced-edge row of a vertex set, restricted to residual
coordinates. -/
def rankRow (A : Finset (Sym2 V)) (S : Finset V) : A → ℝ :=
  fun e => rankIndicator S e.1

/-- The degree row of a vertex, restricted to residual coordinates. -/
def degreeRow (A : Finset (Sym2 V)) (v : V) : A → ℝ :=
  fun e => if v ∈ e.1 then 1 else 0

@[simp] theorem rankRow_apply_of_mem
    {A : Finset (Sym2 V)} {S : Finset V} {e : A}
  (he : PairInside S e.1) :
    rankRow A S e = 1 := by
  simp [rankRow, rankIndicator, he]

@[simp] theorem rankRow_apply_of_not_mem
    {A : Finset (Sym2 V)} {S : Finset V} {e : A}
  (he : ¬ PairInside S e.1) :
    rankRow A S e = 0 := by
  simp [rankRow, rankIndicator, he]

@[simp] theorem degreeRow_apply_of_incident
    {A : Finset (Sym2 V)} {v : V} {e : A}
    (he : v ∈ e.1) :
    degreeRow A v e = 1 := by
  simp [degreeRow, he]

/-- The sum selected by a rank row is the residual induced-edge sum. -/
theorem sum_mul_rankRow
    (A : Finset (Sym2 V)) (S : Finset V) (y : Sym2 V → ℝ) :
    ∑ e : A, y e.1 * rankRow A S e =
      ∑ e ∈ residualInternalEdges A S, y e := by
  classical
  rw [residualInternalEdges, Finset.sum_filter]
  calc
    ∑ e : A, y e.1 * rankRow A S e =
        ∑ e : A, if PairInside S e.1 then y e.1 else 0 := by
          apply Fintype.sum_congr
          intro e
          simp [rankRow, rankIndicator]
    _ = ∑ e ∈ A, if PairInside S e then y e else 0 :=
      (Finset.sum_subtype A (fun _ => Iff.rfl)
        (fun e => if PairInside S e then y e else 0)).symm

/-- The sum selected by a degree row is the residual incident-edge sum. -/
theorem sum_mul_degreeRow
    (A : Finset (Sym2 V)) (v : V) (y : Sym2 V → ℝ) :
    ∑ e : A, y e.1 * degreeRow A v e =
      ∑ e ∈ residualIncidentEdges A v, y e := by
  classical
  rw [residualIncidentEdges, Finset.sum_filter]
  calc
    ∑ e : A, y e.1 * degreeRow A v e =
        ∑ e : A, if v ∈ e.1 then y e.1 else 0 := by
          apply Fintype.sum_congr
          intro e
          simp [degreeRow]
    _ = ∑ e ∈ A, if v ∈ e then y e else 0 :=
      (Finset.sum_subtype A (fun _ => Iff.rfl)
        (fun e => if v ∈ e then y e else 0)).symm

/-- A rank constraint is tight.  The full set is included: its equality is
the total-weight equation. -/
def TightRank
    (A : Finset (Sym2 V)) (y : Sym2 V → ℝ) (S : Finset V) : Prop :=
  ∑ e ∈ residualInternalEdges A S, y e = (S.card - 1 : ℕ)

/-- An active degree constraint is tight. -/
def TightDegree
    (A : Finset (Sym2 V)) (B : ℕ) (y : Sym2 V → ℝ) (v : V) : Prop :=
  ∑ e ∈ residualIncidentEdges A v, y e = B

theorem ResidualFeasible.tightRank_univ
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y) :
    TightRank A y Finset.univ := by
  have hInternal : residualInternalEdges A (Finset.univ : Finset V) = A := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v => simp [residualInternalEdges, PairInside]
  simp only [TightRank, hInternal, Finset.card_univ]
  exact hy.total

/-- Pointwise supermodularity of induced-edge indicators. -/
theorem rankIndicator_supermodular
    (S T : Finset V) (e : Sym2 V) :
    rankIndicator S e + rankIndicator T e ≤
      rankIndicator (S ∩ T) e + rankIndicator (S ∪ T) e := by
  classical
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S <;>
        by_cases huT : u ∈ T <;> by_cases hvT : v ∈ T <;>
        simp [rankIndicator, huS, hvS, huT, hvT]

/-- Pointwise supermodularity of induced-edge row vectors. -/
theorem rankRow_supermodular_apply
    (A : Finset (Sym2 V)) (S T : Finset V) (e : A) :
    rankRow A S e + rankRow A T e ≤
      rankRow A (S ∩ T) e + rankRow A (S ∪ T) e :=
  rankIndicator_supermodular S T e.1

/-- Two sets cross when they overlap but neither contains the other. -/
def Crossing (S T : Finset V) : Prop :=
  ¬ Disjoint S T ∧ ¬ S ⊆ T ∧ ¬ T ⊆ S

theorem Crossing.inter_nonempty
    {S T : Finset V} (h : Crossing S T) :
    (S ∩ T).Nonempty := by
  simpa [Finset.not_disjoint_iff_nonempty_inter] using h.1

theorem Crossing.left_nonempty
    {S T : Finset V} (h : Crossing S T) :
    S.Nonempty := by
  exact (h.inter_nonempty.mono Finset.inter_subset_left)

theorem Crossing.right_nonempty
    {S T : Finset V} (h : Crossing S T) :
    T.Nonempty := by
  exact (h.inter_nonempty.mono Finset.inter_subset_right)

theorem Crossing.union_nonempty
    {S T : Finset V} (h : Crossing S T) :
    (S ∪ T).Nonempty :=
  h.left_nonempty.mono Finset.subset_union_left

/-- The natural-number rank values obey the modular identity on crossing
sets. -/
theorem rankValue_modular_of_crossing
    {S T : Finset V} (h : Crossing S T) :
    (S.card - 1) + (T.card - 1) =
      ((S ∩ T).card - 1) + ((S ∪ T).card - 1) := by
  have hS := h.left_nonempty.card_pos
  have hT := h.right_nonempty.card_pos
  have hI := h.inter_nonempty.card_pos
  have hU := h.union_nonempty.card_pos
  have hcard := Finset.card_union_add_card_inter S T
  omega

/-- The induced-edge sums are supermodular for nonnegative weights. -/
theorem residualInternalSum_supermodular
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    (S T : Finset V) :
    (∑ e ∈ residualInternalEdges A S, y e) +
        (∑ e ∈ residualInternalEdges A T, y e) ≤
      (∑ e ∈ residualInternalEdges A (S ∩ T), y e) +
        (∑ e ∈ residualInternalEdges A (S ∪ T), y e) := by
  rw [← sum_mul_rankRow A S y, ← sum_mul_rankRow A T y,
    ← sum_mul_rankRow A (S ∩ T) y, ← sum_mul_rankRow A (S ∪ T) y,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _he
  calc
    y e.1 * rankRow A S e + y e.1 * rankRow A T e =
        y e.1 * (rankRow A S e + rankRow A T e) := by ring
    _ ≤ y e.1 *
        (rankRow A (S ∩ T) e + rankRow A (S ∪ T) e) :=
      mul_le_mul_of_nonneg_left (rankRow_supermodular_apply A S T e)
        (hy.nonnegative e.1 e.2)
    _ = y e.1 * rankRow A (S ∩ T) e +
        y e.1 * rankRow A (S ∪ T) e := by ring

/-- Every vertex set, including `univ`, satisfies its rank upper bound. -/
theorem ResidualFeasible.rank_bound
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    (S : Finset V) :
    ∑ e ∈ residualInternalEdges A S, y e ≤ (S.card - 1 : ℕ) := by
  by_cases hS : S = Finset.univ
  · subst S
    exact (hy.tightRank_univ).le
  · exact hy.forest S hS

/-- Uncrossing preserves tightness of intersection and union. -/
theorem tightRank_inter_union_of_crossing
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    {S T : Finset V} (hcross : Crossing S T)
    (hS : TightRank A y S) (hT : TightRank A y T) :
    TightRank A y (S ∩ T) ∧ TightRank A y (S ∪ T) := by
  have hsuper := residualInternalSum_supermodular hy S T
  have hI := hy.rank_bound (S ∩ T)
  have hU := hy.rank_bound (S ∪ T)
  have hmod := rankValue_modular_of_crossing hcross
  simp only [TightRank] at hS hT ⊢
  have hcast :
      ((S.card - 1 : ℕ) : ℝ) + ((T.card - 1 : ℕ) : ℝ) =
        (((S ∩ T).card - 1 : ℕ) : ℝ) +
          (((S ∪ T).card - 1 : ℕ) : ℝ) := by
    exact_mod_cast hmod
  rw [hS, hT] at hsuper
  constructor <;> linarith

/-- On a positive support, tight uncrossing gives the exact row identity. -/
theorem rankRow_add_eq_inter_union_of_tight_crossing
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    {S T : Finset V} (hcross : Crossing S T)
    (hS : TightRank A y S) (hT : TightRank A y T) :
    rankRow A S + rankRow A T =
      rankRow A (S ∩ T) + rankRow A (S ∪ T) := by
  have hIU := tightRank_inter_union_of_crossing hy hcross hS hT
  have hsumEq :
      (∑ e ∈ residualInternalEdges A S, y e) +
          (∑ e ∈ residualInternalEdges A T, y e) =
        (∑ e ∈ residualInternalEdges A (S ∩ T), y e) +
          (∑ e ∈ residualInternalEdges A (S ∪ T), y e) := by
    simp only [TightRank] at hS hT hIU
    rw [hS, hT, hIU.1, hIU.2]
    exact_mod_cast rankValue_modular_of_crossing hcross
  have hweighted :
      ∑ e : A, y e.1 *
          ((rankRow A (S ∩ T) e + rankRow A (S ∪ T) e) -
            (rankRow A S e + rankRow A T e)) = 0 := by
    simp_rw [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    rw [sum_mul_rankRow A (S ∩ T) y,
      sum_mul_rankRow A (S ∪ T) y,
      sum_mul_rankRow A S y, sum_mul_rankRow A T y]
    linarith
  have hterm_nonneg :
      ∀ e : A, 0 ≤ y e.1 *
          ((rankRow A (S ∩ T) e + rankRow A (S ∪ T) e) -
            (rankRow A S e + rankRow A T e)) := by
    intro e
    apply mul_nonneg (hy.nonnegative e.1 e.2)
    linarith [rankRow_supermodular_apply A S T e]
  funext e
  have hzero_fun :
      (fun e : A => y e.1 *
          ((rankRow A (S ∩ T) e + rankRow A (S ∪ T) e) -
            (rankRow A S e + rankRow A T e))) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hweighted
  have hzero :
      y e.1 *
          ((rankRow A (S ∩ T) e + rankRow A (S ∪ T) e) -
            (rankRow A S e + rankRow A T e)) = 0 := by
    simpa using congrFun hzero_fun e
  have hyne : y e.1 ≠ 0 := ne_of_gt (hpos e.1 e.2)
  have hgap :
      (rankRow A (S ∩ T) e + rankRow A (S ∪ T) e) -
        (rankRow A S e + rankRow A T e) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hyne
  simp only [Pi.add_apply]
  linarith

/-! ## Maximal laminar tight families -/

/-- Pairwise laminarity of a finite family of vertex sets. -/
def IsLaminar (L : Finset (Finset V)) : Prop :=
  ∀ ⦃S⦄, S ∈ L → ∀ ⦃T⦄, T ∈ L →
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

theorem isLaminar_empty : IsLaminar (∅ : Finset (Finset V)) := by
  simp [IsLaminar]

theorem IsLaminar.subset
    {L K : Finset (Finset V)} (hL : IsLaminar L) (hKL : K ⊆ L) :
    IsLaminar K := by
  intro S hS T hT
  exact hL (hKL hS) (hKL hT)

theorem IsLaminar.insert
    {L : Finset (Finset V)} (hL : IsLaminar L) {S : Finset V}
    (hcompat : ∀ T ∈ L, S ⊆ T ∨ T ⊆ S ∨ Disjoint S T) :
    IsLaminar (insert S L) := by
  intro A hA C hC
  rcases Finset.mem_insert.mp hA with hAS | hAL
  · subst A
    rcases Finset.mem_insert.mp hC with hCS | hCL
    · subst C
      exact Or.inl Finset.Subset.rfl
    · exact hcompat C hCL
  · rcases Finset.mem_insert.mp hC with hCS | hCL
    · subst C
      rcases hcompat A hAL with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm)
    · exact hL hAL hCL

/-- A maximal laminar family of tight rank sets. -/
structure MaximalTightLaminar
    (A : Finset (Sym2 V)) (y : Sym2 V → ℝ) where
  family : Finset (Finset V)
  laminar : IsLaminar family
  tight : ∀ S ∈ family, TightRank A y S
  maximal :
    ∀ K : Finset (Finset V),
      IsLaminar K →
      (∀ S ∈ K, TightRank A y S) →
      family ⊆ K →
      K = family

/-- Finiteness supplies an inclusion-maximal laminar family of tight sets. -/
theorem exists_maximalTightLaminar
    (A : Finset (Sym2 V)) (y : Sym2 V → ℝ) :
    Nonempty (MaximalTightLaminar A y) := by
  classical
  let Good : Finset (Finset V) → Prop := fun L =>
    IsLaminar L ∧ ∀ S ∈ L, TightRank A y S
  have hfinite : Set.Finite {L : Finset (Finset V) | Good L} :=
    Set.toFinite _
  have hn : Set.Nonempty {L : Finset (Finset V) | Good L} := by
    refine ⟨∅, isLaminar_empty, ?_⟩
    simp
  rcases hfinite.exists_maximal hn with ⟨L, hgood, hmax⟩
  refine ⟨{
    family := L
    laminar := hgood.1
    tight := hgood.2
    maximal := ?_ }⟩
  intro K hKlam hKtight hLK
  exact (hmax ⟨hKlam, hKtight⟩ hLK).antisymm hLK

/-- Number of members of `L` crossing `S`. -/
noncomputable def crossingCount
    (L : Finset (Finset V)) (S : Finset V) : ℕ := by
  classical
  exact (L.filter fun T => Crossing S T).card

theorem crossingCount_eq_zero_iff
    (L : Finset (Finset V)) (S : Finset V) :
    crossingCount L S = 0 ↔
      ∀ T ∈ L, S ⊆ T ∨ T ⊆ S ∨ Disjoint S T := by
  classical
  constructor
  · intro hzero T hT
    have hempty :
        L.filter (fun R => Crossing S R) = ∅ :=
      Finset.card_eq_zero.mp (by simpa [crossingCount] using hzero)
    by_contra hcompat
    push_neg at hcompat
    have hcross : Crossing S T := ⟨hcompat.2.2, hcompat.1, hcompat.2.1⟩
    have : T ∈ L.filter (fun R => Crossing S R) :=
      Finset.mem_filter.2 ⟨hT, hcross⟩
    simpa [hempty] using this
  · intro h
    have hempty :
        L.filter (fun R => Crossing S R) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨R, hR⟩
      rcases Finset.mem_filter.1 hR with ⟨hRL, hSR⟩
      rcases h R hRL with hsub | hsup | hdisj
      · exact hSR.2.1 hsub
      · exact hSR.2.2 hsup
      · exact hSR.1 hdisj
    simp [crossingCount, hempty]

theorem crossing_inter_imp_crossing
    {L : Finset (Finset V)} (hL : IsLaminar L)
    {S T R : Finset V} (hT : T ∈ L) (hR : R ∈ L)
    (hST : Crossing S T) (hIR : Crossing (S ∩ T) R) :
    Crossing S R := by
  have hrel := hL hT hR
  rcases hrel with hTR | hRT | hdisj
  · grind [Crossing, Finset.disjoint_left]
  · grind [Crossing, Finset.disjoint_left]
  · grind [Crossing, Finset.disjoint_left]

theorem crossing_union_imp_crossing
    {L : Finset (Finset V)} (hL : IsLaminar L)
    {S T R : Finset V} (hT : T ∈ L) (hR : R ∈ L)
    (hST : Crossing S T) (hUR : Crossing (S ∪ T) R) :
    Crossing S R := by
  have hrel := hL hT hR
  rcases hrel with hTR | hRT | hdisj
  · grind [Crossing, Finset.disjoint_left]
  · grind [Crossing, Finset.disjoint_left]
  · grind [Crossing, Finset.disjoint_left]

theorem crossingCount_inter_lt
    {L : Finset (Finset V)} (hL : IsLaminar L)
    {S T : Finset V} (hT : T ∈ L) (hST : Crossing S T) :
    crossingCount L (S ∩ T) < crossingCount L S := by
  classical
  let FI := L.filter fun R => Crossing (S ∩ T) R
  let FS := L.filter fun R => Crossing S R
  have hsub : FI ⊆ FS := by
    intro R hR
    rcases Finset.mem_filter.1 hR with ⟨hRL, hIR⟩
    exact Finset.mem_filter.2
      ⟨hRL, crossing_inter_imp_crossing hL hT hRL hST hIR⟩
  have hTFS : T ∈ FS := Finset.mem_filter.2 ⟨hT, hST⟩
  have hTFI : T ∉ FI := by
    intro h
    have hcross := (Finset.mem_filter.1 h).2
    exact hcross.2.1 Finset.inter_subset_right
  have hne : FI ≠ FS := by
    intro heq
    exact hTFI (heq ▸ hTFS)
  have hssub : FI ⊂ FS := (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hne⟩
  simpa [crossingCount, FI, FS] using Finset.card_lt_card hssub

theorem crossingCount_union_lt
    {L : Finset (Finset V)} (hL : IsLaminar L)
    {S T : Finset V} (hT : T ∈ L) (hST : Crossing S T) :
    crossingCount L (S ∪ T) < crossingCount L S := by
  classical
  let FU := L.filter fun R => Crossing (S ∪ T) R
  let FS := L.filter fun R => Crossing S R
  have hsub : FU ⊆ FS := by
    intro R hR
    rcases Finset.mem_filter.1 hR with ⟨hRL, hUR⟩
    exact Finset.mem_filter.2
      ⟨hRL, crossing_union_imp_crossing hL hT hRL hST hUR⟩
  have hTFS : T ∈ FS := Finset.mem_filter.2 ⟨hT, hST⟩
  have hTFU : T ∉ FU := by
    intro h
    have hcross := (Finset.mem_filter.1 h).2
    exact hcross.2.2 Finset.subset_union_right
  have hne : FU ≠ FS := by
    intro heq
    exact hTFU (heq ▸ hTFS)
  have hssub : FU ⊂ FS := (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hne⟩
  simpa [crossingCount, FU, FS] using Finset.card_lt_card hssub

/-- Span of the rank rows indexed by a finite family. -/
def rankSpan (A : Finset (Sym2 V)) (L : Finset (Finset V)) :
    Submodule ℝ (A → ℝ) :=
  Submodule.span ℝ (rankRow A '' (L : Set (Finset V)))

theorem rankRow_mem_rankSpan
    (A : Finset (Sym2 V)) {L : Finset (Finset V)}
    {S : Finset V} (hS : S ∈ L) :
    rankRow A S ∈ rankSpan A L := by
  apply Submodule.subset_span
  exact ⟨S, hS, rfl⟩

/-- Every tight rank row is spanned by a maximal laminar tight family. -/
theorem MaximalTightLaminar.rankRow_mem_span
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ} (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    (M : MaximalTightLaminar A y)
    {S : Finset V} (hS : TightRank A y S) :
    rankRow A S ∈ rankSpan A M.family := by
  classical
  let n := crossingCount M.family S
  have aux :
      ∀ m : ℕ, ∀ R : Finset V,
        crossingCount M.family R = m →
        TightRank A y R →
        rankRow A R ∈ rankSpan A M.family := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro R hcount hRtight
      by_cases hm : m = 0
      · have hcompat :
            ∀ T ∈ M.family,
              R ⊆ T ∨ T ⊆ R ∨ Disjoint R T :=
          (crossingCount_eq_zero_iff M.family R).1 (hcount.trans hm)
        let K := insert R M.family
        have hKlam : IsLaminar K := M.laminar.insert hcompat
        have hKtight : ∀ T ∈ K, TightRank A y T := by
          intro T hT
          rcases Finset.mem_insert.mp hT with rfl | hT
          · exact hRtight
          · exact M.tight T hT
        have hMK : M.family ⊆ K := Finset.subset_insert R M.family
        have hEq : K = M.family := M.maximal K hKlam hKtight hMK
        have hRmem : R ∈ M.family := by
          rw [← hEq]
          exact Finset.mem_insert_self R M.family
        exact rankRow_mem_rankSpan A hRmem
      · have hfilter :
            (M.family.filter fun T => Crossing R T).Nonempty := by
          exact Finset.card_pos.mp (by
            have hp : 0 < crossingCount M.family R := by
              rw [hcount]
              exact Nat.pos_of_ne_zero hm
            simpa [crossingCount] using hp)
        rcases hfilter with ⟨T, hTfilter⟩
        have hTmem := (Finset.mem_filter.1 hTfilter).1
        have hcross := (Finset.mem_filter.1 hTfilter).2
        have hIU := tightRank_inter_union_of_crossing hy hcross
          hRtight (M.tight T hTmem)
        have hIlt :
            crossingCount M.family (R ∩ T) < m := by
          rw [← hcount]
          exact crossingCount_inter_lt M.laminar hTmem hcross
        have hUlt :
            crossingCount M.family (R ∪ T) < m := by
          rw [← hcount]
          exact crossingCount_union_lt M.laminar hTmem hcross
        have hI := ih _ hIlt _ rfl hIU.1
        have hU := ih _ hUlt _ rfl hIU.2
        have hTrow := rankRow_mem_rankSpan A hTmem
        have hrow := rankRow_add_eq_inter_union_of_tight_crossing
          hy hpos hcross hRtight (M.tight T hTmem)
        have hsolve :
            rankRow A R =
              rankRow A (R ∩ T) + rankRow A (R ∪ T) - rankRow A T := by
          rw [← hrow]
          abel
        rw [hsolve]
        exact (rankSpan A M.family).sub_mem
          ((rankSpan A M.family).add_mem hI hU) hTrow
  exact aux n S rfl hS

/-! ## Tight normals at an extreme point -/

/-- Rank rows and tight active degree rows at a residual point. -/
def activeNormals
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ)
    (y : Sym2 V → ℝ) : Set (A → ℝ) :=
  {r | ∃ S : Finset V, TightRank A y S ∧ r = rankRow A S} ∪
  {r | ∃ v ∈ W, TightDegree A B y v ∧ r = degreeRow A v}

/-- The ordinary real dot product on the finite active coordinate type. -/
def activeDot (A : Finset (Sym2 V)) (r d : A → ℝ) : ℝ :=
  ∑ e, r e * d e

/-- Extend a direction on the active edge coordinates by zero. -/
def extendActive
    (A : Finset (Sym2 V)) (d : A → ℝ) : Sym2 V → ℝ :=
  fun e => if h : e ∈ A then d ⟨e, h⟩ else 0

@[simp] theorem extendActive_apply_mem
    (A : Finset (Sym2 V)) (d : A → ℝ) {e : Sym2 V} (he : e ∈ A) :
    extendActive A d e = d ⟨e, he⟩ := by
  simp [extendActive, he]

theorem extendActive_apply_subtype
    (A : Finset (Sym2 V)) (d : A → ℝ) (e : A) :
    extendActive A d e.1 = d e := by
  simp [extendActive, e.2]

@[simp] theorem extendActive_apply_not_mem
    (A : Finset (Sym2 V)) (d : A → ℝ) {e : Sym2 V} (he : e ∉ A) :
    extendActive A d e = 0 := by
  simp [extendActive, he]

/-- Orthogonality to a rank row says that the corresponding selected
direction sum vanishes. -/
theorem sum_extendActive_eq_zero_of_rankRow_orthogonal
    (A : Finset (Sym2 V)) (d : A → ℝ) (S : Finset V)
    (horth : activeDot A (rankRow A S) d = 0) :
    ∑ e ∈ residualInternalEdges A S, extendActive A d e = 0 := by
  rw [← sum_mul_rankRow A S (extendActive A d)]
  simpa only [activeDot, extendActive_apply_subtype, mul_comm] using horth

/-- Orthogonality to a degree row says that the corresponding incident
direction sum vanishes. -/
theorem sum_extendActive_eq_zero_of_degreeRow_orthogonal
    (A : Finset (Sym2 V)) (d : A → ℝ) (v : V)
    (horth : activeDot A (degreeRow A v) d = 0) :
    ∑ e ∈ residualIncidentEdges A v, extendActive A d e = 0 := by
  rw [← sum_mul_degreeRow A v (extendActive A d)]
  simpa only [activeDot, extendActive_apply_subtype, mul_comm] using horth

theorem dual_apply_eq_activeDot
    (A : Finset (Sym2 V))
    (φ : Module.Dual ℝ (A → ℝ)) (r : A → ℝ) :
    φ r = activeDot A r (fun e => φ (Pi.single e 1)) := by
  classical
  calc
    φ r = φ (∑ e, Pi.single e (r e)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ e, φ (Pi.single e (r e)) :=
      map_sum φ (fun e => Pi.single e (r e)) Finset.univ
    _ = ∑ e, r e * φ (Pi.single e 1) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [show Pi.single e (r e) =
          r e • (Pi.single e (1 : ℝ) : A → ℝ) by
        ext i
        by_cases h : i = e
        · subst i
          simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul,
            mul_one]
        · simp [Pi.single_eq_of_ne h]]
      exact LinearMap.map_smul φ (r e) (Pi.single e (1 : ℝ))
    _ = activeDot A r (fun e => φ (Pi.single e 1)) := by
      simp [activeDot]

/-- If the active normals fail to span all active coordinates, there is a
nonzero direction annihilating every active normal. -/
theorem exists_direction_of_active_span_ne_top
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hspan :
      Submodule.span ℝ (activeNormals A W B y) ≠ ⊤) :
    ∃ d : A → ℝ, d ≠ 0 ∧
      ∀ r ∈ activeNormals A W B y, activeDot A r d = 0 := by
  classical
  let K := Submodule.span ℝ (activeNormals A W B y)
  have hAnn : K.dualAnnihilator ≠ ⊥ := by
    intro hbot
    have htop : K = ⊤ :=
      (Submodule.dualAnnihilator_eq_bot_iff).1 hbot
    exact hspan htop
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hAnn with ⟨φ, hφmem, hφne⟩
  let d : A → ℝ := fun e => (φ : Module.Dual ℝ (A → ℝ)) (Pi.single e 1)
  have hdne : d ≠ 0 := by
    intro hd
    have hφzero : φ = 0 := by
      apply LinearMap.ext
      intro r
      have heval := dual_apply_eq_activeDot A φ r
      change φ r = activeDot A r d at heval
      rw [heval, hd]
      simp [activeDot]
    exact hφne hφzero
  refine ⟨d, hdne, ?_⟩
  intro r hr
  have hrK : r ∈ K :=
    Submodule.subset_span hr
  have hzero :
      (φ : Module.Dual ℝ (A → ℝ)) r = 0 :=
    (Submodule.mem_dualAnnihilator φ).1 hφmem r hrK
  rw [dual_apply_eq_activeDot A] at hzero
  exact hzero

/-- Affine perturbation of a residual point in an active direction. -/
def perturb
    (y D : Sym2 V → ℝ) (t : ℝ) : Sym2 V → ℝ :=
  fun e => y e + t * D e

theorem eventually_residualFeasible_perturb
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y D : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    (hzeroD : ∀ e, e ∉ A → D e = 0)
    (hrank :
      ∀ S : Finset V, TightRank A y S →
        ∑ e ∈ residualInternalEdges A S, D e = 0)
    (hdegree :
      ∀ v ∈ W, TightDegree A B y v →
        ∑ e ∈ residualIncidentEdges A v, D e = 0) :
    ∀ᶠ t in nhds (0 : ℝ), ResidualFeasible A W B (perturb y D t) := by
  classical
  have hnonnegative :
      ∀ᶠ t in nhds (0 : ℝ),
        ∀ e ∈ A, 0 ≤ perturb y D t e := by
    rw [Finset.eventually_all]
    intro e he
    have hcont :
        ContinuousAt (fun t : ℝ => perturb y D t e) 0 := by
      simpa [perturb] using
        continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    exact
      (continuousAt_const.eventually_lt hcont (by
        simpa [perturb] using hpos e he)).mono
        (fun _ h => h.le)
  have hforest :
      ∀ᶠ t in nhds (0 : ℝ),
        ∀ S : Finset V, S ≠ Finset.univ →
          ∑ e ∈ residualInternalEdges A S, perturb y D t e ≤
            (S.card - 1 : ℕ) := by
    rw [Filter.eventually_all]
    intro S
    by_cases hS : S = Finset.univ
    · exact Filter.Eventually.of_forall fun _ hne => (hne hS).elim
    · by_cases htight : TightRank A y S
      · exact Filter.Eventually.of_forall fun t _ => by
          have hD := hrank S htight
          simp only [perturb, Finset.sum_add_distrib,
            ← Finset.mul_sum]
          rw [hD, mul_zero, add_zero, htight]
      · have hstrict :
            ∑ e ∈ residualInternalEdges A S, y e <
              (S.card - 1 : ℕ) :=
          lt_of_le_of_ne (hy.forest S hS) htight
        have hcont :
            ContinuousAt
              (fun t : ℝ =>
                ∑ e ∈ residualInternalEdges A S, perturb y D t e) 0 := by
          have hc :
              ContinuousAt
                (fun t : ℝ =>
                  (∑ e ∈ residualInternalEdges A S, y e) +
                    t * (∑ e ∈ residualInternalEdges A S, D e)) 0 :=
            continuousAt_const.add (continuousAt_id.mul continuousAt_const)
          convert hc using 1
          ext t
          simp [perturb, Finset.sum_add_distrib, Finset.mul_sum]
        have hatzero :
            (fun t : ℝ =>
                ∑ e ∈ residualInternalEdges A S, perturb y D t e) 0 =
              ∑ e ∈ residualInternalEdges A S, y e := by
          simp [perturb]
        have hev :=
          hcont.eventually_lt continuousAt_const (by
            simpa only [hatzero] using hstrict)
        exact hev.mono fun _ h _ => h.le
  have hdegreeEv :
      ∀ᶠ t in nhds (0 : ℝ),
        ∀ v ∈ W,
          ∑ e ∈ residualIncidentEdges A v, perturb y D t e ≤ B := by
    rw [Finset.eventually_all]
    intro v hv
    by_cases htight : TightDegree A B y v
    · exact Filter.Eventually.of_forall fun t => by
        have hD := hdegree v hv htight
        simp only [perturb, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        rw [hD, mul_zero, add_zero, htight]
    · have hstrict :
          ∑ e ∈ residualIncidentEdges A v, y e < (B : ℝ) :=
        lt_of_le_of_ne (hy.degree v hv) htight
      have hcont :
          ContinuousAt
            (fun t : ℝ =>
              ∑ e ∈ residualIncidentEdges A v, perturb y D t e) 0 := by
        have hc :
            ContinuousAt
              (fun t : ℝ =>
                (∑ e ∈ residualIncidentEdges A v, y e) +
                  t * (∑ e ∈ residualIncidentEdges A v, D e)) 0 :=
          continuousAt_const.add (continuousAt_id.mul continuousAt_const)
        convert hc using 1
        ext t
        simp [perturb, Finset.sum_add_distrib, Finset.mul_sum]
      have hatzero :
          (fun t : ℝ =>
              ∑ e ∈ residualIncidentEdges A v, perturb y D t e) 0 =
            ∑ e ∈ residualIncidentEdges A v, y e := by
        simp [perturb]
      have hev :=
        hcont.eventually_lt continuousAt_const (by
          simpa only [hatzero] using hstrict)
      exact hev.mono fun _ h => h.le
  filter_upwards [hnonnegative, hforest, hdegreeEv] with
    t hnonneg hfor hdeg
  refine {
    zero_outside := ?_
    nonnegative := hnonneg
    total := ?_
    forest := hfor
    degree := hdeg }
  · intro e he
    simp [perturb, hy.zero_outside e he, hzeroD e he]
  · have hD :
        ∑ e ∈ A, D e = 0 := by
      have h := hrank Finset.univ hy.tightRank_univ
      have hInternal :
          residualInternalEdges A (Finset.univ : Finset V) = A := by
        ext e
        induction e using Sym2.inductionOn with
        | _ u v => simp [residualInternalEdges, PairInside]
      simpa [hInternal] using h
    simp only [perturb, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hD, mul_zero, add_zero, hy.total]

/-- At a positive extreme residual point, the tight rank rows together with
the tight active degree rows span every active edge coordinate. -/
theorem activeNormals_span_eq_top
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    (hext : y ∈ (residualPolytope A W B).extremePoints ℝ) :
    Submodule.span ℝ (activeNormals A W B y) = ⊤ := by
  classical
  by_contra hspan
  rcases exists_direction_of_active_span_ne_top hspan with
    ⟨d, hdne, hdorth⟩
  let D := extendActive A d
  have hrank :
      ∀ S : Finset V, TightRank A y S →
        ∑ e ∈ residualInternalEdges A S, D e = 0 := by
    intro S hS
    apply sum_extendActive_eq_zero_of_rankRow_orthogonal A d S
    apply hdorth (rankRow A S)
    exact Or.inl ⟨S, hS, rfl⟩
  have hdegree :
      ∀ v ∈ W, TightDegree A B y v →
        ∑ e ∈ residualIncidentEdges A v, D e = 0 := by
    intro v hv htight
    apply sum_extendActive_eq_zero_of_degreeRow_orthogonal A d v
    apply hdorth (degreeRow A v)
    exact Or.inr ⟨v, hv, htight, rfl⟩
  have hev :
      ∀ᶠ t in nhds (0 : ℝ),
        ResidualFeasible A W B (perturb y D t) :=
    eventually_residualFeasible_perturb hy hpos
      (fun e he => extendActive_apply_not_mem A d he) hrank hdegree
  have hneg_tendsto :
      Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
    simpa only [ContinuousAt, id_eq, neg_zero] using
      (continuousAt_id.neg : ContinuousAt (fun t : ℝ => -t) 0)
  have hevneg :
      ∀ᶠ t in nhds (0 : ℝ),
        ResidualFeasible A W B (perturb y D (-t)) :=
    hneg_tendsto.eventually hev
  have hboth :
      {t : ℝ |
        ResidualFeasible A W B (perturb y D t) ∧
        ResidualFeasible A W B (perturb y D (-t))} ∈ nhds 0 :=
    hev.and hevneg
  rcases (Metric.mem_nhds_iff.1 hboth) with ⟨ε, hε, hεsub⟩
  let t : ℝ := ε / 2
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [t]
    rw [sub_zero, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  have htfeas := hεsub htball
  have hplus :
      perturb y D t ∈ residualPolytope A W B :=
    htfeas.1
  have hminus :
      perturb y D (-t) ∈ residualPolytope A W B :=
    htfeas.2
  have hopen :
      y ∈ openSegment ℝ (perturb y D t) (perturb y D (-t)) := by
    have hp : perturb y D t = y + t • D := by
      ext e
      simp [perturb]
    have hm : perturb y D (-t) = y - t • D := by
      ext e
      simp [perturb]
      ring
    rw [hp, hm]
    exact mem_openSegment_add_sub (𝕜 := ℝ) y (t • D)
  have hplus_eq : perturb y D t = y :=
    hext.2 hplus hminus hopen
  apply hdne
  funext e
  have heq := congrFun hplus_eq e.1
  simp only [perturb, D, extendActive_apply_subtype] at heq
  have hmul : t * d e = 0 := by linarith
  exact (mul_eq_zero.mp hmul).resolve_left htpos.ne'

/-! ## A laminar basis of tight constraints -/

theorem exists_finset_linearIndependent_span_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (t : Finset E) :
    ∃ b : Finset E,
      b ⊆ t ∧
      LinearIndependent ℝ ((↑) : b → E) ∧
      Submodule.span ℝ (b : Set E) =
        Submodule.span ℝ (t : Set E) := by
  classical
  rcases exists_linearIndependent ℝ (t : Set E) with
    ⟨b, hbt, hspan, hli⟩
  have hbfinite : b.Finite :=
    t.finite_toSet.subset hbt
  let bf : Finset E := hbfinite.toFinset
  have hbfset : (bf : Set E) = b := by
    ext x
    simp [bf]
  refine ⟨bf, ?_, ?_, ?_⟩
  · intro x hx
    have hxb : x ∈ b := by
      rw [← hbfset]
      exact hx
    exact hbt hxb
  · let e : bf ≃ b := Equiv.setCongr hbfset
    have he := hli.comp e e.injective
    simpa [e, Equiv.setCongr] using he
  · simpa [hbfset] using hspan

theorem exists_finset_linearIndependent_extension
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s t : Finset E}
    (hli : LinearIndependent ℝ ((↑) : s → E))
    (hst : s ⊆ t) :
    ∃ b : Finset E,
      s ⊆ b ∧ b ⊆ t ∧
      (t : Set E) ⊆ Submodule.span ℝ (b : Set E) ∧
      LinearIndependent ℝ ((↑) : b → E) := by
  classical
  have hstSet : (s : Set E) ⊆ (t : Set E) := hst
  rcases exists_linearIndepOn_id_extension hli hstSet with
    ⟨b, hbt, hsb, htspan, hbLI⟩
  have hbfinite : b.Finite :=
    t.finite_toSet.subset hbt
  let bf : Finset E := hbfinite.toFinset
  have hbfset : (bf : Set E) = b := by
    ext x
    simp [bf]
  refine ⟨bf, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have : x ∈ b := hsb hx
    rwa [← hbfset] at this
  · intro x hx
    apply hbt
    rwa [← hbfset]
  · simpa [hbfset] using htspan
  · let e : bf ≃ b := Equiv.setCongr hbfset
    have he := hbLI.comp e e.injective
    simpa [e, Equiv.setCongr] using he

/-- Tight rank rows supplied by a maximal laminar family. -/
def laminarRankCandidates
    (A : Finset (Sym2 V)) {y : Sym2 V → ℝ}
    (M : MaximalTightLaminar A y) :
    Finset (A → ℝ) :=
  M.family.image (rankRow A)

/-- Tight degree rows among the active vertices. -/
def tightDegreeCandidates
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ)
    (y : Sym2 V → ℝ) : Finset (A → ℝ) := by
  classical
  exact (W.filter fun v => TightDegree A B y v).image (degreeRow A)

theorem activeNormals_subset_span_candidates
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    (M : MaximalTightLaminar A y) :
    activeNormals A W B y ⊆
      Submodule.span ℝ
        ((laminarRankCandidates A M ∪
          tightDegreeCandidates A W B y : Finset (A → ℝ)) :
          Set (A → ℝ)) := by
  classical
  intro r hr
  rcases hr with hrank | hdegree
  · rcases hrank with ⟨S, hS, rfl⟩
    have hmem := M.rankRow_mem_span hy hpos hS
    apply Submodule.span_mono ?_ hmem
    intro r hr
    rcases hr with ⟨T, hT, rfl⟩
    apply Finset.mem_coe.2
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨T, hT, rfl⟩
  · rcases hdegree with ⟨v, hvW, hvTight, rfl⟩
    apply Submodule.subset_span
    change degreeRow A v ∈
      (laminarRankCandidates A M ∪ tightDegreeCandidates A W B y)
    apply Finset.mem_union_right
    simp only [tightDegreeCandidates, Finset.mem_image]
    exact ⟨v, Finset.mem_filter.2 ⟨hvW, hvTight⟩, rfl⟩

theorem candidates_span_eq_top
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    (hext : y ∈ (residualPolytope A W B).extremePoints ℝ)
    (M : MaximalTightLaminar A y) :
    Submodule.span ℝ
        ((laminarRankCandidates A M ∪
          tightDegreeCandidates A W B y : Finset (A → ℝ)) :
          Set (A → ℝ)) =
      ⊤ := by
  have hactive := activeNormals_span_eq_top hy hpos hext
  apply top_unique
  rw [← hactive]
  apply Submodule.span_le.2
  exact activeNormals_subset_span_candidates hy hpos M

/-- A vector-level version of the Singh--Lau laminar basis.  `rankRows`
are independent rows chosen from a maximal laminar tight family;
`allRows` extends them to a basis using tight degree rows. -/
structure TightLaminarBasisData
    (A : Finset (Sym2 V)) (W : Finset V) (B : ℕ)
    (y : Sym2 V → ℝ) where
  maximalLaminar : MaximalTightLaminar A y
  rankRows : Finset (A → ℝ)
  allRows : Finset (A → ℝ)
  rankRows_subset_candidates :
    rankRows ⊆ laminarRankCandidates A maximalLaminar
  rankRows_span :
    Submodule.span ℝ (rankRows : Set (A → ℝ)) =
      Submodule.span ℝ
        (laminarRankCandidates A maximalLaminar : Set (A → ℝ))
  rankRows_subset_allRows : rankRows ⊆ allRows
  allRows_subset_candidates :
    allRows ⊆
      (laminarRankCandidates A maximalLaminar ∪
        tightDegreeCandidates A W B y)
  independent :
    LinearIndependent ℝ ((↑) : allRows → (A → ℝ))
  span_eq_top :
    Submodule.span ℝ (allRows : Set (A → ℝ)) = ⊤
  added_is_degree :
    ∀ r ∈ allRows \ rankRows,
      r ∈ tightDegreeCandidates A W B y
  card_eq : allRows.card = A.card

theorem exists_tightLaminarBasisData
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    (hext : y ∈ (residualPolytope A W B).extremePoints ℝ) :
    Nonempty (TightLaminarBasisData A W B y) := by
  classical
  let M : MaximalTightLaminar A y :=
    Classical.choice (exists_maximalTightLaminar A y)
  rcases exists_finset_linearIndependent_span_eq
      (laminarRankCandidates A M) with
    ⟨R, hRsub, hRLI, hRspan⟩
  have hRcandidate :
      R ⊆
        (laminarRankCandidates A M ∪
          tightDegreeCandidates A W B y) :=
    fun r hr => Finset.mem_union_left _ (hRsub hr)
  rcases exists_finset_linearIndependent_extension hRLI hRcandidate with
    ⟨C, hRC, hCsub, hcandSpan, hCLI⟩
  have hCspan : Submodule.span ℝ (C : Set (A → ℝ)) = ⊤ := by
    apply top_unique
    rw [← candidates_span_eq_top hy hpos hext M]
    apply Submodule.span_le.2
    exact hcandSpan
  have hAdded :
      ∀ r ∈ C \ R, r ∈ tightDegreeCandidates A W B y := by
    intro r hr
    have hrC : r ∈ C := (Finset.mem_sdiff.1 hr).1
    have hrR : r ∉ R := (Finset.mem_sdiff.1 hr).2
    have hrcand := hCsub hrC
    rcases Finset.mem_union.1 hrcand with hrank | hdegree
    · exfalso
      have hrspanRank :
          r ∈ Submodule.span ℝ
            (laminarRankCandidates A M : Set (A → ℝ)) :=
        Submodule.subset_span hrank
      have hrspanR :
          r ∈ Submodule.span ℝ (R : Set (A → ℝ)) := by
        rw [hRspan]
        exact hrspanRank
      let x : C := ⟨r, hrC⟩
      let s : Set C := {z | z.1 ∈ R}
      have hxnot : x ∉ s := by
        simpa [x, s] using hrR
      have himage :
          ((fun z : C => (z.1 : A → ℝ)) '' s) =
            (R : Set (A → ℝ)) := by
        ext q
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro hq
          have hqC : q ∈ C := hRC hq
          exact ⟨⟨q, hqC⟩, hq, rfl⟩
      have hnot :=
        hCLI.notMem_span_image (s := s) (x := x) hxnot
      rw [himage] at hnot
      exact hnot hrspanR
    · exact hdegree
  have hcard : C.card = A.card := by
    have hfin := finrank_span_eq_card hCLI
    have hRange :
        Set.range ((↑) : C → (A → ℝ)) = (C : Set (A → ℝ)) := by
      ext r
      simp
    rw [hRange] at hfin
    rw [hCspan] at hfin
    simpa [Module.finrank_pi] using hfin.symm
  exact ⟨{
    maximalLaminar := M
    rankRows := R
    allRows := C
    rankRows_subset_candidates := hRsub
    rankRows_span := hRspan
    rankRows_subset_allRows := hRC
    allRows_subset_candidates := hCsub
    independent := hCLI
    span_eq_top := hCspan
    added_is_degree := hAdded
    card_eq := hcard }⟩

noncomputable def TightLaminarBasisData.rankSource
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (r : D.rankRows) : Finset V :=
  Classical.choose (Finset.mem_image.1
    (D.rankRows_subset_candidates r.2))

theorem TightLaminarBasisData.rankSource_mem
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (r : D.rankRows) :
    D.rankSource r ∈ D.maximalLaminar.family :=
  (Classical.choose_spec (Finset.mem_image.1
    (D.rankRows_subset_candidates r.2))).1

theorem TightLaminarBasisData.rankRow_rankSource
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (r : D.rankRows) :
    rankRow A (D.rankSource r) = r.1 :=
  (Classical.choose_spec (Finset.mem_image.1
    (D.rankRows_subset_candidates r.2))).2

theorem TightLaminarBasisData.rankSource_injective
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    Function.Injective D.rankSource := by
  intro r s hrs
  apply Subtype.ext
  rw [← D.rankRow_rankSource r, ← D.rankRow_rankSource s, hrs]

/-- The chosen laminar sets indexing the independent tight rank rows. -/
noncomputable def TightLaminarBasisData.laminarSets
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) : Finset (Finset V) :=
  D.rankRows.attach.image D.rankSource

theorem TightLaminarBasisData.laminarSets_card
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    D.laminarSets.card = D.rankRows.card := by
  classical
  rw [laminarSets, Finset.card_image_of_injective _
    D.rankSource_injective, Finset.card_attach]

theorem TightLaminarBasisData.laminarSets_subset
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    D.laminarSets ⊆ D.maximalLaminar.family := by
  classical
  intro S hS
  rcases Finset.mem_image.1 hS with ⟨r, _, rfl⟩
  exact D.rankSource_mem r

theorem TightLaminarBasisData.laminar
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    IsLaminar D.laminarSets :=
  D.maximalLaminar.laminar.subset D.laminarSets_subset

theorem TightLaminarBasisData.laminarSets_tight
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    {S : Finset V} (hS : S ∈ D.laminarSets) :
    TightRank A y S :=
  D.maximalLaminar.tight S (D.laminarSets_subset hS)

noncomputable def TightLaminarBasisData.degreeSource
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (r : ↥(D.allRows \ D.rankRows)) : V :=
  Classical.choose (Finset.mem_image.1
    (D.added_is_degree r.1 r.2))

theorem TightLaminarBasisData.degreeSource_spec
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (r : ↥(D.allRows \ D.rankRows)) :
    D.degreeSource r ∈ W ∧
      TightDegree A B y (D.degreeSource r) ∧
      degreeRow A (D.degreeSource r) = r.1 := by
  classical
  have h := Classical.choose_spec (Finset.mem_image.1
    (D.added_is_degree r.1 r.2))
  exact ⟨(Finset.mem_filter.1 h.1).1,
    (Finset.mem_filter.1 h.1).2, h.2⟩

theorem TightLaminarBasisData.degreeSource_injective
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    Function.Injective D.degreeSource := by
  intro r s hrs
  apply Subtype.ext
  rw [← (D.degreeSource_spec r).2.2,
    ← (D.degreeSource_spec s).2.2, hrs]

/-- Active vertices whose degree rows complete the laminar rank rows to a
basis. -/
noncomputable def TightLaminarBasisData.degreeVertices
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) : Finset V :=
  (D.allRows \ D.rankRows).attach.image D.degreeSource

theorem TightLaminarBasisData.degreeVertices_card
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    D.degreeVertices.card =
      (D.allRows \ D.rankRows).card := by
  classical
  rw [degreeVertices, Finset.card_image_of_injective _
    D.degreeSource_injective, Finset.card_attach]

theorem TightLaminarBasisData.degreeVertices_subset
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    D.degreeVertices ⊆ W := by
  classical
  intro v hv
  rcases Finset.mem_image.1 hv with ⟨r, _, rfl⟩
  exact (D.degreeSource_spec r).1

theorem TightLaminarBasisData.degreeVertices_tight
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    {v : V} (hv : v ∈ D.degreeVertices) :
    TightDegree A B y v := by
  classical
  rcases Finset.mem_image.1 hv with ⟨r, _, rfl⟩
  exact (D.degreeSource_spec r).2.1

theorem TightLaminarBasisData.card_decomposition
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    A.card = D.laminarSets.card + D.degreeVertices.card := by
  rw [D.laminarSets_card, D.degreeVertices_card]
  have hcardDiff :=
    Finset.card_sdiff_add_card_eq_card D.rankRows_subset_allRows
  have htotal := D.card_eq
  omega

/-! ## Counting laminar families -/

theorem minimal_mem_laminar_subset_or_disjoint
    {L : Finset (Finset V)} (hLam : IsLaminar L)
    {S T : Finset V} (hS : S ∈ L) (hT : T ∈ L)
    (hmin : ∀ R ∈ L, R ⊆ S → S ⊆ R) :
    S ⊆ T ∨ Disjoint S T := by
  rcases hLam hS hT with hST | hTS | hdisj
  · exact Or.inl hST
  · exact Or.inl (hmin T hT hTS)
  · exact Or.inr hdisj

theorem erase_injOn_laminar_erase_minimal
    {L : Finset (Finset V)} (hLam : IsLaminar L)
    {S : Finset V} (hS : S ∈ L)
    (hmin : ∀ R ∈ L, R ⊆ S → S ⊆ R)
    {a : V} (ha : a ∈ S) (hScard : 2 ≤ S.card) :
    Set.InjOn (fun T : Finset V => T.erase a) (L.erase S) := by
  classical
  have hSerase : (S.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    omega
  rcases hSerase with ⟨b, hb⟩
  have hbS : b ∈ S := Finset.mem_of_mem_erase hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  intro T hT U hU hEq
  change T.erase a = U.erase a at hEq
  have hTL : T ∈ L := Finset.mem_of_mem_erase hT
  have hUL : U ∈ L := Finset.mem_of_mem_erase hU
  have hTrel :=
    minimal_mem_laminar_subset_or_disjoint hLam hS hTL hmin
  have hUrel :=
    minimal_mem_laminar_subset_or_disjoint hLam hS hUL hmin
  rcases hTrel with hST | hSdT <;>
      rcases hUrel with hSU | hSdU
  · exact Finset.erase_injOn' a
      (hST ha) (hSU ha) hEq
  · have hbLeft : b ∈ T.erase a :=
      Finset.mem_erase.2 ⟨hba, hST hbS⟩
    have hbNotRight : b ∉ U.erase a := by
      intro hbU
      exact Finset.disjoint_left.1 hSdU hbS
        (Finset.mem_of_mem_erase hbU)
    exact (hbNotRight (hEq ▸ hbLeft)).elim
  · have hbRight : b ∈ U.erase a :=
      Finset.mem_erase.2 ⟨hba, hSU hbS⟩
    have hbNotLeft : b ∉ T.erase a := by
      intro hbT
      exact Finset.disjoint_left.1 hSdT hbS
        (Finset.mem_of_mem_erase hbT)
    exact (hbNotLeft (hEq.symm ▸ hbRight)).elim
  · have haT : a ∉ T := by
      intro haT
      exact Finset.disjoint_left.1 hSdT ha haT
    have haU : a ∉ U := by
      intro haU
      exact Finset.disjoint_left.1 hSdU ha haU
    simpa [Finset.erase_eq_of_notMem haT,
      Finset.erase_eq_of_notMem haU] using hEq

/-- A nonempty laminar family of subsets of `U`, all of cardinality at least
two, has at most `|U|-1` members.  Equality forces `U` itself to be a member.
This is the inclusion-forest count used in the Singh--Lau proof. -/
theorem laminar_card_bound_and_eq_top
    (U : Finset V) :
    ∀ (L : Finset (Finset V)),
      L.Nonempty →
      IsLaminar L →
      (∀ S ∈ L, S ⊆ U) →
      (∀ S ∈ L, 2 ≤ S.card) →
      L.card ≤ U.card - 1 ∧
        (L.card = U.card - 1 → U ∈ L) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro L hLne hLam hsub hlarge
    rcases L.exists_minimal hLne with ⟨S, hSL, hSmin⟩
    have hScard : 2 ≤ S.card := hlarge S hSL
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    rcases hSne with ⟨a, haS⟩
    have haU : a ∈ U := hsub S hSL haS
    let U' := U.erase a
    let L' := (L.erase S).image (fun T : Finset V => T.erase a)
    have hU'ssub : U' ⊂ U := by
      simpa [U'] using Finset.erase_ssubset haU
    have hinj :
        Set.InjOn (fun T : Finset V => T.erase a) (L.erase S) :=
      erase_injOn_laminar_erase_minimal hLam hSL hSmin haS hScard
    have hL'card : L'.card = (L.erase S).card := by
      exact Finset.card_image_iff.2 hinj
    have hLerasecard : (L.erase S).card = L.card - 1 :=
      Finset.card_erase_of_mem hSL
    have hL'lam : IsLaminar L' := by
      intro T hT R hR
      rcases Finset.mem_image.1 hT with ⟨T₀, hT₀, rfl⟩
      rcases Finset.mem_image.1 hR with ⟨R₀, hR₀, rfl⟩
      have hrel := hLam
        (Finset.mem_of_mem_erase hT₀)
        (Finset.mem_of_mem_erase hR₀)
      rcases hrel with hTR | hRT | hdisj
      · exact Or.inl (fun x hx =>
          Finset.mem_erase.2
            ⟨(Finset.mem_erase.1 hx).1,
              hTR (Finset.mem_of_mem_erase hx)⟩)
      · exact Or.inr (Or.inl (fun x hx =>
          Finset.mem_erase.2
            ⟨(Finset.mem_erase.1 hx).1,
              hRT (Finset.mem_of_mem_erase hx)⟩))
      · exact Or.inr (Or.inr (Finset.disjoint_left.2 fun x hxT hxR =>
          Finset.disjoint_left.1 hdisj
            (Finset.mem_of_mem_erase hxT)
            (Finset.mem_of_mem_erase hxR)))
    have hL'sub : ∀ T ∈ L', T ⊆ U' := by
      intro T hT
      rcases Finset.mem_image.1 hT with ⟨T₀, hT₀, rfl⟩
      intro x hx
      have hxT₀ := Finset.mem_of_mem_erase hx
      exact Finset.mem_erase.2
        ⟨(Finset.mem_erase.1 hx).1,
          hsub T₀ (Finset.mem_of_mem_erase hT₀) hxT₀⟩
    have hL'large : ∀ T ∈ L', 2 ≤ T.card := by
      intro T hT
      rcases Finset.mem_image.1 hT with ⟨T₀, hT₀, rfl⟩
      have hT₀L : T₀ ∈ L := Finset.mem_of_mem_erase hT₀
      have hT₀ne : T₀ ≠ S := Finset.ne_of_mem_erase hT₀
      rcases minimal_mem_laminar_subset_or_disjoint
          hLam hSL hT₀L hSmin with hST | hdisj
      · have hstrict : S ⊂ T₀ :=
          (Finset.ssubset_iff_subset_ne).2 ⟨hST, Ne.symm hT₀ne⟩
        have hacont : a ∈ T₀ := hST haS
        rw [Finset.card_erase_of_mem hacont]
        have hcardlt := Finset.card_lt_card hstrict
        omega
      · have haNot : a ∉ T₀ := by
          intro haT
          exact Finset.disjoint_left.1 hdisj haS haT
        rw [Finset.erase_eq_of_notMem haNot]
        exact hlarge T₀ hT₀L
    by_cases hL'ne : L'.Nonempty
    · have hIH :=
        ih U' hU'ssub L' hL'ne hL'lam hL'sub hL'large
      have hUcard : U'.card = U.card - 1 := by
        simp [U', Finset.card_erase_of_mem haU]
      have hLpos : 0 < L.card := Finset.card_pos.2 hLne
      have hLcard : L.card = L'.card + 1 := by
        rw [hL'card, hLerasecard]
        omega
      have hIHbound := hIH.1
      have hSleU := Finset.card_le_card (hsub S hSL)
      constructor
      · omega
      · intro heq
        have hEq' : L'.card = U'.card - 1 := by omega
        have hU'mem : U' ∈ L' := hIH.2 hEq'
        rcases Finset.mem_image.1 hU'mem with
          ⟨T, hTLerase, hTerase⟩
        have hTL : T ∈ L := Finset.mem_of_mem_erase hTLerase
        have hTrel :=
          minimal_mem_laminar_subset_or_disjoint
            hLam hSL hTL hSmin
        rcases hTrel with hST | hdisj
        · have haT : a ∈ T := hST haS
          have hTU : T ⊆ U := hsub T hTL
          have hEqErase : T.erase a = U.erase a := by
            simpa [U'] using hTerase
          have hTUeq : T = U :=
            Finset.erase_injOn' a haT haU hEqErase
          simpa [hTUeq] using hTL
        · have hSerase : (S.erase a).Nonempty := by
            apply Finset.card_pos.mp
            rw [Finset.card_erase_of_mem haS]
            omega
          rcases hSerase with ⟨b, hb⟩
          have hbS := Finset.mem_of_mem_erase hb
          have hbne := (Finset.mem_erase.1 hb).1
          have hbU' : b ∈ U' :=
            Finset.mem_erase.2 ⟨hbne, hsub S hSL hbS⟩
          have hbTerase : b ∈ T.erase a := by
            rw [hTerase]
            exact hbU'
          exact (Finset.disjoint_left.1 hdisj hbS
            (Finset.mem_of_mem_erase hbTerase)).elim
    · have hL'empty : L' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hL'ne
      have hLcard : L.card = 1 := by
        have : (L.erase S).card = 0 := by
          rw [← hL'card, hL'empty]
          simp
        rw [hLerasecard] at this
        have hpos : 0 < L.card := Finset.card_pos.2 hLne
        omega
      constructor
      · have hScardU := Finset.card_le_card (hsub S hSL)
        omega
      · intro heq
        have hUcard : U.card = 2 := by omega
        have hScardU := Finset.card_le_card (hsub S hSL)
        have hSU : S = U :=
          Finset.eq_of_subset_of_card_le (hsub S hSL) (by omega)
        simpa [hSU] using hSL

theorem laminar_card_le_card_vertices_sub_one
    {L : Finset (Finset V)}
    (hLam : IsLaminar L)
    (hlarge : ∀ S ∈ L, 2 ≤ S.card) :
    L.card ≤ Fintype.card V - 1 := by
  by_cases hL : L.Nonempty
  · exact (laminar_card_bound_and_eq_top
      (Finset.univ : Finset V) L hL hLam
      (fun _ _ => Finset.subset_univ _) hlarge).1
  · simp [Finset.not_nonempty_iff_eq_empty.1 hL]

theorem univ_mem_of_laminar_card_eq
    {L : Finset (Finset V)}
    (hL : L.Nonempty)
    (hLam : IsLaminar L)
    (hlarge : ∀ S ∈ L, 2 ≤ S.card)
    (hcard : L.card = Fintype.card V - 1) :
    (Finset.univ : Finset V) ∈ L :=
  (laminar_card_bound_and_eq_top
    (Finset.univ : Finset V) L hL hLam
    (fun _ _ => Finset.subset_univ _) hlarge).2
    (by simpa using hcard)

theorem ResidualFeasible.not_isDiag_of_mem
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    {e : Sym2 V} (heA : e ∈ A) :
    ¬ e.IsDiag := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [Sym2.mk_isDiag_iff]
    intro huv
    subst v
    let S : Finset V := {u}
    have hSproper : S ≠ Finset.univ := by
      intro h
      have := congrArg Finset.card h
      simp [S] at this
      omega
    have heInternal :
        s(u, u) ∈ residualInternalEdges A S := by
      simp [S, residualInternalEdges, PairInside, heA]
    have hsingle :
        y s(u, u) ≤
          ∑ e ∈ residualInternalEdges A S, y e := by
      exact Finset.single_le_sum
        (fun e he => hy.nonnegative e
          (mem_residualInternalEdges.1 he).1)
        heInternal
    have hbound := hy.forest S hSproper
    have hposEdge := hpos s(u, u) heA
    simp [S] at hbound
    linarith

theorem rankRow_eq_zero_of_card_le_one
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    {S : Finset V} (hS : S.card ≤ 1) :
    rankRow A S = 0 := by
  funext e
  by_cases hinside : PairInside S e.1
  · have htwo : e.1.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag e.1
        (hy.not_isDiag_of_mem hcard hpos e.2)
    have hsub : e.1.toFinset ⊆ S := by
      exact (pairInside_iff_toFinset_subset S e.1).1 hinside
    have := Finset.card_le_card hsub
    omega
  · simp [rankRow, rankIndicator, hinside]

theorem TightLaminarBasisData.laminarSets_card_ge_two
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e) :
    ∀ S ∈ D.laminarSets, 2 ≤ S.card := by
  classical
  intro S hS
  rcases Finset.mem_image.1 hS with ⟨r, _, hSr⟩
  subst S
  by_contra hsmall
  have hrowzero :
      rankRow A (D.rankSource r) = 0 :=
    rankRow_eq_zero_of_card_le_one hy hcard hpos (by omega)
  have hrzero : (r.1 : A → ℝ) = 0 := by
    rw [← D.rankRow_rankSource r, hrowzero]
  let rC : D.allRows :=
    ⟨r.1, D.rankRows_subset_allRows r.2⟩
  exact D.independent.ne_zero rC (by
    change (r.1 : A → ℝ) = 0
    exact hrzero)

/-! ## Degree deficits -/

theorem sum_incident_sums
    (A : Finset (Sym2 V)) (f : Sym2 V → ℝ) :
    ∑ v : V, ∑ e ∈ residualIncidentEdges A v, f e =
      ∑ e ∈ A, (e.toFinset.card : ℝ) * f e := by
  classical
  simp only [residualIncidentEdges, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases huv : u = v
      · subst v
        simp [Sym2.toFinset_mk_eq]
      · rw [Sym2.card_toFinset_of_not_isDiag s(u, v)
          (Sym2.mk_isDiag_iff.not.2 huv)]
        norm_num
        have hsplit : ∀ x : V,
            (if x = u ∨ x = v then f s(u, v) else 0) =
              (if x = u then f s(u, v) else 0) +
              (if x = v then f s(u, v) else 0) := by
          intro x
          by_cases hxu : x = u <;> by_cases hxv : x = v <;>
            grind
        simp_rw [hsplit, Finset.sum_add_distrib]
        simp
        ring

theorem sum_incident_sums_eq_two_mul
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    (f : Sym2 V → ℝ) :
    ∑ v : V, ∑ e ∈ residualIncidentEdges A v, f e =
      2 * ∑ e ∈ A, f e := by
  rw [sum_incident_sums]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Sym2.card_toFinset_of_not_isDiag e
    (hy.not_isDiag_of_mem hcard hpos he)]
  norm_num

/-- Half of the unused incidence capacity at a vertex. -/
def vertexDeficit
    (A : Finset (Sym2 V)) (y : Sym2 V → ℝ) (v : V) : ℝ :=
  ((residualIncidentEdges A v).card -
    ∑ e ∈ residualIncidentEdges A v, y e) / 2

theorem vertexDeficit_nonnegative
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (v : V) :
    0 ≤ vertexDeficit A y v := by
  have hsum :
      ∑ e ∈ residualIncidentEdges A v, y e ≤
        ∑ _e ∈ residualIncidentEdges A v, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro e he
    exact hy.weight_le_one
      (mem_residualIncidentEdges.1 he).1
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  unfold vertexDeficit
  linarith

theorem sum_vertexDeficit
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e) :
    ∑ v : V, vertexDeficit A y v =
      (A.card : ℝ) - (Fintype.card V - 1 : ℕ) := by
  have hcount :=
    sum_incident_sums_eq_two_mul hy hcard hpos
      (fun _ => (1 : ℝ))
  have hweight :=
    sum_incident_sums_eq_two_mul hy hcard hpos y
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcount
  unfold vertexDeficit
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hcount, hweight, hy.total]
  ring

theorem ResidualFeasible.total_card_le
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y) :
    Fintype.card V - 1 ≤ A.card := by
  have hsum :
      ∑ e ∈ A, y e ≤ ∑ _e ∈ A, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro e he
    exact hy.weight_le_one he
  rw [hy.total] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact_mod_cast hsum

theorem progress_count_consequences
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    (D : TightLaminarBasisData A W B y)
    (hlargeActive :
      ∀ v ∈ W, B + 2 ≤ (residualIncidentEdges A v).card) :
    D.laminarSets.card = Fintype.card V - 1 ∧
      D.degreeVertices = W ∧
      ∀ v ∉ D.degreeVertices,
        ∀ e ∈ residualIncidentEdges A v, y e = 1 := by
  classical
  let X := D.degreeVertices
  let L := D.laminarSets
  have hqnonneg : ∀ v : V, 0 ≤ vertexDeficit A y v :=
    fun v => vertexDeficit_nonnegative hy hcard v
  have hqone : ∀ v ∈ X, 1 ≤ vertexDeficit A y v := by
    intro v hv
    have hvW : v ∈ W := D.degreeVertices_subset hv
    have htight := D.degreeVertices_tight hv
    have hdeg := hlargeActive v hvW
    have hdegR :
        ((B + 2 : ℕ) : ℝ) ≤
          ((residualIncidentEdges A v).card : ℝ) := by
      exact_mod_cast hdeg
    unfold vertexDeficit
    rw [htight]
    norm_num [Nat.cast_add] at hdegR ⊢
    linarith
  have hXleSum :
      (X.card : ℝ) ≤ ∑ v ∈ X, vertexDeficit A y v := by
    calc
      (X.card : ℝ) = ∑ _v ∈ X, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv => hqone v hv)
  have hsumXle :
      ∑ v ∈ X, vertexDeficit A y v ≤
        ∑ v : V, vertexDeficit A y v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ X)
      (fun v _ _ => hqnonneg v)
  have hsumAll := sum_vertexDeficit hy hcard hpos
  have hXreal :
      (X.card : ℝ) ≤
        (A.card : ℝ) - (Fintype.card V - 1 : ℕ) := by
    linarith
  have hXplus :
      X.card + (Fintype.card V - 1) ≤ A.card := by
    exact_mod_cast (show
      (X.card : ℝ) + (Fintype.card V - 1 : ℕ) ≤ A.card by
        linarith)
  have hLbound :
      L.card ≤ Fintype.card V - 1 :=
    laminar_card_le_card_vertices_sub_one D.laminar
      (D.laminarSets_card_ge_two hy hcard hpos)
  have hdecomp := D.card_decomposition
  have hLeq : L.card = Fintype.card V - 1 := by
    dsimp [L, X] at hXplus hLbound hdecomp ⊢
    omega
  have hXcard :
      X.card + (Fintype.card V - 1) = A.card := by
    dsimp [L, X] at hLeq hdecomp ⊢
    omega
  have hsumXeq :
      ∑ v ∈ X, vertexDeficit A y v =
        ∑ v : V, vertexDeficit A y v := by
    have hXcast :
        (X.card : ℝ) =
          (A.card : ℝ) - (Fintype.card V - 1 : ℕ) := by
      have hcast :
          (X.card : ℝ) +
              ((Fintype.card V - 1 : ℕ) : ℝ) =
            (A.card : ℝ) := by
        exact_mod_cast hXcard
      linarith
    linarith
  have hqzeroOutside :
      ∀ v ∉ X, vertexDeficit A y v = 0 := by
    intro v hv
    have hvcomp : v ∈ (Finset.univ \ X : Finset V) := by
      simp [hv]
    have hsplit :=
      Finset.sum_sdiff (s₁ := X) (s₂ := Finset.univ)
        (Finset.subset_univ X) (f := vertexDeficit A y)
    have hcompzero :
        ∑ z ∈ (Finset.univ \ X : Finset V),
          vertexDeficit A y z = 0 := by
      have hAll :
          ∑ z ∈ (Finset.univ : Finset V),
              vertexDeficit A y z =
            ∑ z : V, vertexDeficit A y z := by simp
      linarith
    have hsingle :
        vertexDeficit A y v ≤
          ∑ z ∈ (Finset.univ \ X : Finset V),
            vertexDeficit A y z := by
      exact Finset.single_le_sum
        (fun z _ => hqnonneg z) hvcomp
    have hqvnonneg := hqnonneg v
    linarith
  have hWsubX : W ⊆ X := by
    intro v hvW
    by_contra hvX
    have hqzero := hqzeroOutside v hvX
    have hdeg := hlargeActive v hvW
    have hdegreeBound := hy.degree v hvW
    unfold vertexDeficit at hqzero
    have hcast :
        ((B + 2 : ℕ) : ℝ) ≤
          ((residualIncidentEdges A v).card : ℝ) := by
      exact_mod_cast hdeg
    norm_num at hqzero
    norm_num [Nat.cast_add] at hcast
    linarith
  have hXeqW : X = W :=
    Finset.Subset.antisymm D.degreeVertices_subset hWsubX
  refine ⟨hLeq, hXeqW, ?_⟩
  intro v hvX e he
  have hqzero := hqzeroOutside v hvX
  have hsumle :
      y e ≤ ∑ z ∈ residualIncidentEdges A v, y z := by
    exact Finset.single_le_sum
      (fun z hz => hy.nonnegative z
        (mem_residualIncidentEdges.1 hz).1) he
  have hothers :
      ∑ z ∈ residualIncidentEdges A v, y z ≤
        (residualIncidentEdges A v).card := by
    have :=
      Finset.sum_le_sum
        (s := residualIncidentEdges A v)
        (f := y) (g := fun _ => (1 : ℝ))
        (fun z hz => hy.weight_le_one
          (mem_residualIncidentEdges.1 hz).1)
    simpa using this
  unfold vertexDeficit at hqzero
  have htotalEq :
      ∑ z ∈ residualIncidentEdges A v, y z =
        (residualIncidentEdges A v).card := by
    linarith
  have hrest :
      ∑ z ∈ (residualIncidentEdges A v).erase e, y z ≤
        ((residualIncidentEdges A v).erase e).card := by
    have :=
      Finset.sum_le_sum
        (s := (residualIncidentEdges A v).erase e)
        (f := y) (g := fun _ => (1 : ℝ))
        (fun z hz => hy.weight_le_one
          (mem_residualIncidentEdges.1
            (Finset.mem_of_mem_erase hz)).1)
    simpa using this
  have hsplit :=
    Finset.sum_erase_add (residualIncidentEdges A v) y he
  have hcardErase :=
    Finset.card_erase_of_mem he
  have hcardEraseR :
      (((residualIncidentEdges A v).erase e).card : ℝ) + 1 =
        ((residualIncidentEdges A v).card : ℝ) := by
    have hposCard : 0 < (residualIncidentEdges A v).card :=
      Finset.card_pos.2 ⟨e, he⟩
    exact_mod_cast (show
      ((residualIncidentEdges A v).erase e).card + 1 =
        (residualIncidentEdges A v).card by omega)
  have hyle := hy.weight_le_one
    (mem_residualIncidentEdges.1 he).1
  linarith

theorem sym2_eq_of_toFinset_eq_of_not_isDiag
    {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (h : e.toFinset = f.toFinset) :
    e = f := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    induction f using Sym2.inductionOn with
    | _ a b =>
      rw [Sym2.mk_isDiag_iff] at he hf
      simp only [Sym2.toFinset_mk_eq] at h
      have hu : u ∈ ({a, b} : Finset V) := by
        rw [← h]
        simp
      have hv : v ∈ ({a, b} : Finset V) := by
        rw [← h]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rw [Sym2.eq_iff]
      rcases hu with hua | hub <;> rcases hv with hva | hvb
      · exact (he (hua.trans hva.symm)).elim
      · exact Or.inl ⟨hua, hvb⟩
      · exact Or.inr ⟨hub, hva⟩
      · exact (he (hub.trans hvb.symm)).elim

theorem residualInternalEdges_toFinset_eq_singleton
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    {e : Sym2 V} (heA : e ∈ A) :
    residualInternalEdges A e.toFinset = {e} := by
  ext f
  constructor
  · intro hf
    have hfA := (mem_residualInternalEdges.1 hf).1
    have hfsub :=
      (pairInside_iff_toFinset_subset e.toFinset f).1
        (mem_residualInternalEdges.1 hf).2
    have hecard := Sym2.card_toFinset_of_not_isDiag e
      (hy.not_isDiag_of_mem hcard hpos heA)
    have hfcard := Sym2.card_toFinset_of_not_isDiag f
      (hy.not_isDiag_of_mem hcard hpos hfA)
    have heqFinset : f.toFinset = e.toFinset :=
      Finset.eq_of_subset_of_card_le hfsub (by omega)
    have hfe : f = e :=
      sym2_eq_of_toFinset_eq_of_not_isDiag
        (hy.not_isDiag_of_mem hcard hpos hfA)
        (hy.not_isDiag_of_mem hcard hpos heA)
        heqFinset
    simpa [hfe]
  · intro hf
    have hfe : f = e := by simpa using hf
    subst f
    exact mem_residualInternalEdges.2
      ⟨heA, pairInside_toFinset_self e⟩

theorem tightRank_toFinset_of_weight_eq_one
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    {e : Sym2 V} (heA : e ∈ A) (hye : y e = 1) :
    TightRank A y e.toFinset := by
  rw [TightRank,
    residualInternalEdges_toFinset_eq_singleton hy hcard hpos heA]
  rw [Sym2.card_toFinset_of_not_isDiag e
    (hy.not_isDiag_of_mem hcard hpos heA)]
  simp [hye]

theorem rankRow_toFinset_eq_single
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    (e : A) :
    rankRow A e.1.toFinset = Pi.single e 1 := by
  funext f
  have hInternal :=
    residualInternalEdges_toFinset_eq_singleton hy hcard hpos e.2
  have hiff :
      PairInside e.1.toFinset f.1 ↔ f.1 = e.1 := by
    constructor
    · intro hf
      have hmem :
          f.1 ∈ residualInternalEdges A e.1.toFinset :=
        mem_residualInternalEdges.2 ⟨f.2, hf⟩
      rw [hInternal] at hmem
      simpa using hmem
    · intro hfe
      have hsubeq : f = e := Subtype.ext hfe
      subst f
      exact pairInside_toFinset_self e.1
  by_cases hfe : f = e
  · subst f
    simp [rankRow, rankIndicator,
      pairInside_toFinset_self]
  · have hvalne : f.1 ≠ e.1 := by
      intro h
      exact hfe (Subtype.ext h)
    simp [rankRow, rankIndicator, hiff, hvalne,
      Pi.single_eq_of_ne hfe]

theorem TightLaminarBasisData.tightRank_mem_rankRowsSpan
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (hy : ResidualFeasible A W B y)
    (hpos : ∀ e ∈ A, 0 < y e)
    {S : Finset V} (hS : TightRank A y S) :
    rankRow A S ∈
      Submodule.span ℝ (D.rankRows : Set (A → ℝ)) := by
  have hmem :=
    D.maximalLaminar.rankRow_mem_span hy hpos hS
  rw [D.rankRows_span]
  apply Submodule.span_mono ?_ hmem
  intro r hr
  rcases hr with ⟨T, hT, rfl⟩
  exact Finset.mem_coe.2
    (Finset.mem_image.2 ⟨T, hT, rfl⟩)

theorem TightLaminarBasisData.single_mem_rankRowsSpan_of_weight_eq_one
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    (e : A) (hye : y e.1 = 1) :
    Pi.single e 1 ∈
      Submodule.span ℝ (D.rankRows : Set (A → ℝ)) := by
  rw [← rankRow_toFinset_eq_single hy hcard hpos e]
  exact D.tightRank_mem_rankRowsSpan hy hpos
    (tightRank_toFinset_of_weight_eq_one
      hy hcard hpos e.2 hye)

theorem degreeRow_eq_sum_single
    (A : Finset (Sym2 V)) (v : V) :
    degreeRow A v =
      ∑ e : A, if v ∈ e.1 then Pi.single e 1 else 0 := by
  classical
  calc
    degreeRow A v =
        ∑ e : A, Pi.single e (degreeRow A v e) := by
      rw [Finset.univ_sum_single]
    _ = ∑ e : A, if v ∈ e.1 then Pi.single e 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hve : v ∈ e.1 <;> simp [degreeRow, hve]

theorem TightLaminarBasisData.degreeRow_mem_rankRowsSpan_of_outside
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y)
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    {X : Finset V}
    (hweight :
      ∀ v ∉ X, ∀ e ∈ residualIncidentEdges A v, y e = 1)
    {v : V} (hv : v ∉ X) :
    degreeRow A v ∈
      Submodule.span ℝ (D.rankRows : Set (A → ℝ)) := by
  rw [degreeRow_eq_sum_single]
  apply Submodule.sum_mem
  intro e _
  by_cases hve : v ∈ e.1
  · simp only [if_pos hve]
    exact D.single_mem_rankRowsSpan_of_weight_eq_one
      hy hcard hpos e
      (hweight v hv e.1
        (mem_residualIncidentEdges.2 ⟨e.2, hve⟩))
  · simp only [if_neg hve]
    exact Submodule.zero_mem _

theorem sum_sym2_membership_indicator (e : Sym2 V) :
    ∑ v : V, (if v ∈ e then (1 : ℝ) else 0) =
      (e.toFinset.card : ℝ) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    by_cases huv : u = v
    · subst v
      simp [Sym2.toFinset_mk_eq]
    · have hsplit : ∀ x : V,
          (if x ∈ s(u, v) then (1 : ℝ) else 0) =
            (if x = u then 1 else 0) +
            (if x = v then 1 else 0) := by
        intro x
        by_cases hxu : x = u <;> by_cases hxv : x = v <;>
          grind
      simp_rw [hsplit, Finset.sum_add_distrib]
      simp [Sym2.toFinset_mk_eq, huv]
      norm_num

theorem sum_degreeRow_eq_two_rankRow_univ
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e) :
    ∑ v : V, degreeRow A v =
      (2 : ℝ) • rankRow A (Finset.univ : Finset V) := by
  classical
  funext e
  have hnotdiag :=
    hy.not_isDiag_of_mem hcard hpos e.2
  simp only [Finset.sum_apply, degreeRow, Pi.smul_apply]
  rw [sum_sym2_membership_indicator e.1,
    Sym2.card_toFinset_of_not_isDiag e.1 hnotdiag]
  have hins : PairInside (Finset.univ : Finset V) e.1 := by
    induction e.1 using Sym2.inductionOn with
    | _ u v => simp [PairInside]
  simp [rankRow, rankIndicator, hins]

theorem TightLaminarBasisData.sum_degreeVertices_degreeRow
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (D : TightLaminarBasisData A W B y) :
    ∑ v ∈ D.degreeVertices, degreeRow A v =
      ∑ r ∈ D.allRows \ D.rankRows, r := by
  classical
  unfold degreeVertices
  rw [Finset.sum_image]
  · rw [← Finset.sum_attach (D.allRows \ D.rankRows)]
    apply Finset.sum_congr rfl
    intro r hr
    exact D.degreeSource_spec r |>.2.2
  · exact D.degreeSource_injective.injOn

theorem linearIndependent_complement_sum_not_mem_span
    {E : Type*} [DecidableEq E] [AddCommGroup E] [Module ℝ E]
    {R C : Finset E}
    (hRC : R ⊆ C)
    (hli : LinearIndependent ℝ ((↑) : C → E))
    (hne : (C \ R).Nonempty) :
    (∑ r ∈ (C \ R), r) ∉
      Submodule.span ℝ (R : Set E) := by
  classical
  intro hsum
  rcases hne with ⟨r₀, hr₀Z⟩
  have hr₀C : r₀ ∈ C := (Finset.mem_sdiff.1 hr₀Z).1
  have hr₀R : r₀ ∉ R := (Finset.mem_sdiff.1 hr₀Z).2
  let P := Submodule.span ℝ
    ((C.erase r₀ : Finset E) : Set E)
  have hRsub : R ⊆ C.erase r₀ := by
    intro r hr
    exact Finset.mem_erase.2
      ⟨fun h => hr₀R (h ▸ hr), hRC hr⟩
  have hsumP : (∑ r ∈ (C \ R), r) ∈ P := by
    apply Submodule.span_mono ?_ hsum
    exact hRsub
  have hrestP :
      (∑ r ∈ (C \ R).erase r₀, r) ∈ P := by
    apply Submodule.sum_mem
    intro r hr
    apply Submodule.subset_span
    exact Finset.mem_erase.2
      ⟨(Finset.mem_erase.1 hr).1,
        (Finset.mem_sdiff.1
          (Finset.mem_of_mem_erase hr)).1⟩
  have hsplit :=
    Finset.sum_erase_add (C \ R) (fun r => r) hr₀Z
  have hr₀P : r₀ ∈ P := by
    have heq :
        r₀ =
          (∑ r ∈ (C \ R), r) -
            (∑ r ∈ (C \ R).erase r₀, r) := by
      rw [← hsplit]
      abel
    rw [heq]
    exact P.sub_mem hsumP hrestP
  let x : C := ⟨r₀, hr₀C⟩
  let s : Set C := {z | z.1 ∈ C.erase r₀}
  have hxnot : x ∉ s := by
    simp [x, s]
  have himage :
      ((fun z : C => (z.1 : E)) '' s) =
        ((C.erase r₀ : Finset E) : Set E) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hq
      exact ⟨⟨q, Finset.mem_of_mem_erase hq⟩, hq, rfl⟩
  have hnot :=
    hli.notMem_span_image (s := s) (x := x) hxnot
  rw [himage] at hnot
  exact hnot hr₀P

/-- Lemma 6.1: a positive extreme residual point with an active degree
constraint has an active vertex incident with at most `B+1` support edges. -/
theorem exists_small_active_vertex
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    (hext : y ∈ (residualPolytope A W B).extremePoints ℝ)
    (hW : W.Nonempty) :
    ∃ v ∈ W, (residualIncidentEdges A v).card ≤ B + 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hlarge :
      ∀ v ∈ W, B + 2 ≤ (residualIncidentEdges A v).card := by
    intro v hv
    have := hnone v hv
    omega
  let D : TightLaminarBasisData A W B y :=
    Classical.choice (exists_tightLaminarBasisData hy hpos hext)
  have hcount :=
    progress_count_consequences hy hcard hpos D hlarge
  let X := D.degreeVertices
  have hXeqW : X = W := hcount.2.1
  have hweight :
      ∀ v ∉ X,
        ∀ e ∈ residualIncidentEdges A v, y e = 1 :=
    hcount.2.2
  let P := Submodule.span ℝ
    (D.rankRows : Set (A → ℝ))
  have hrho : rankRow A (Finset.univ : Finset V) ∈ P :=
    D.tightRank_mem_rankRowsSpan hy hpos hy.tightRank_univ
  have houtside :
      ∑ v ∈ (Finset.univ \ X : Finset V), degreeRow A v ∈ P := by
    apply Submodule.sum_mem
    intro v hv
    exact D.degreeRow_mem_rankRowsSpan_of_outside
      hy hcard hpos hweight (Finset.mem_sdiff.1 hv).2
  have htotal := sum_degreeRow_eq_two_rankRow_univ hy hcard hpos
  have hsplit :=
    Finset.sum_sdiff (s₁ := X) (s₂ := Finset.univ)
      (Finset.subset_univ X) (f := degreeRow A)
  have hXsum :
      ∑ v ∈ X, degreeRow A v ∈ P := by
    have heq :
        ∑ v ∈ X, degreeRow A v =
          (2 : ℝ) • rankRow A (Finset.univ : Finset V) -
            ∑ v ∈ (Finset.univ \ X : Finset V), degreeRow A v := by
      rw [← htotal, ← hsplit]
      abel
    rw [heq]
    exact P.sub_mem (P.smul_mem 2 hrho) houtside
  have hAdded :
      ∑ r ∈ D.allRows \ D.rankRows, r ∈ P := by
    rw [← D.sum_degreeVertices_degreeRow]
    exact hXsum
  have hZne : (D.allRows \ D.rankRows).Nonempty := by
    have hXne : X.Nonempty := by
      rw [hXeqW]
      exact hW
    have hcardPositive : 0 < (D.allRows \ D.rankRows).card := by
      rw [← D.degreeVertices_card]
      exact Finset.card_pos.2 hXne
    exact Finset.card_pos.1 hcardPositive
  exact linearIndependent_complement_sum_not_mem_span
    D.rankRows_subset_allRows D.independent hZne hAdded

/-! ## Pure spanning-tree extreme points -/

theorem residualSupportGraph_connected
    {A : Finset (Sym2 V)} {W : Finset V} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A W B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e) :
    (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Connected := by
  classical
  let T : SimpleGraph V :=
    SimpleGraph.fromEdgeSet (A : Set (Sym2 V))
  have hVne : Nonempty V := by
    exact Fintype.card_pos_iff.mp (by omega)
  let root : V := Classical.choice hVne
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨root, ?_⟩
  intro w
  by_contra hw
  let S : Finset V :=
    Finset.univ.filter fun v => T.Reachable root v
  have hrootS : root ∈ S := by
    simp [S]
  have hwS : w ∉ S := by
    simpa [S] using hw
  have hSproper : S ≠ Finset.univ := by
    intro h
    exact hwS (h ▸ Finset.mem_univ w)
  let C : Finset V := Finset.univ \ S
  have hCproper : C ≠ Finset.univ := by
    intro h
    have hrootC : root ∈ C := h ▸ Finset.mem_univ root
    exact (Finset.mem_sdiff.1 hrootC).2 hrootS
  have hpartition :
      A = residualInternalEdges A S ∪
        residualInternalEdges A C := by
    ext e
    constructor
    · intro heA
      induction e using Sym2.inductionOn with
      | _ u v =>
        have huv : u ≠ v := by
          exact Sym2.mk_isDiag_iff.not.1
            (hy.not_isDiag_of_mem hcard hpos heA)
        have hadj : T.Adj u v := by
          change (SimpleGraph.fromEdgeSet
            (A : Set (Sym2 V))).Adj u v
          exact (SimpleGraph.fromEdgeSet_adj
            (A : Set (Sym2 V))).2
            ⟨heA, huv⟩
        have hreach :
            T.Reachable root u ↔ T.Reachable root v := by
          constructor
          · intro hu
            exact hu.trans hadj.reachable
          · intro hv
            exact hv.trans hadj.symm.reachable
        by_cases hu : T.Reachable root u
        · have hv : T.Reachable root v := hreach.1 hu
          apply Finset.mem_union_left
          exact mem_residualInternalEdges.2
            ⟨heA, by simp [PairInside, S, hu, hv]⟩
        · have hv : ¬T.Reachable root v := by
            exact fun hv => hu (hreach.2 hv)
          apply Finset.mem_union_right
          exact mem_residualInternalEdges.2
            ⟨heA, by simp [PairInside, C, S, hu, hv]⟩
    · intro he
      rcases Finset.mem_union.1 he with heS | heC
      · exact (mem_residualInternalEdges.1 heS).1
      · exact (mem_residualInternalEdges.1 heC).1
  have hdisjoint :
      Disjoint (residualInternalEdges A S)
        (residualInternalEdges A C) := by
    apply Finset.disjoint_left.2
    intro e heS heC
    have hSin := (mem_residualInternalEdges.1 heS).2
    have hCin := (mem_residualInternalEdges.1 heC).2
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huS := (pairInside_mk S u v).1 hSin |>.1
      have huC := (pairInside_mk C u v).1 hCin |>.1
      exact (Finset.mem_sdiff.1 huC).2 huS
  have htotalSplit :
      ∑ e ∈ residualInternalEdges A S, y e +
        ∑ e ∈ residualInternalEdges A C, y e =
          (Fintype.card V - 1 : ℕ) := by
    rw [← Finset.sum_union hdisjoint, ← hpartition]
    exact hy.total
  have hSbound := hy.forest S hSproper
  have hCbound := hy.forest C hCproper
  have hcardSC : S.card + C.card = Fintype.card V := by
    have h :=
      Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ S)
    dsimp [C]
    simp at h ⊢
    omega
  have hSpos : 0 < S.card := Finset.card_pos.2 ⟨root, hrootS⟩
  have hCpos : 0 < C.card := by
    apply Finset.card_pos.2
    exact ⟨w, Finset.mem_sdiff.2
      ⟨Finset.mem_univ w, hwS⟩⟩
  have hVpos : 0 < Fintype.card V := by omega
  norm_num [Nat.cast_sub hVpos, Nat.cast_sub hSpos,
    Nat.cast_sub hCpos] at htotalSplit hSbound hCbound
  have hcardSCR :
      (S.card : ℝ) + (C.card : ℝ) =
        (Fintype.card V : ℝ) := by
    exact_mod_cast hcardSC
  linarith

theorem extreme_without_degree_constraints_is_tree
    {A : Finset (Sym2 V)} {B : ℕ}
    {y : Sym2 V → ℝ}
    (hy : ResidualFeasible A ∅ B y)
    (hcard : 1 < Fintype.card V)
    (hpos : ∀ e ∈ A, 0 < y e)
    (hext : y ∈ (residualPolytope A ∅ B).extremePoints ℝ) :
    (SimpleGraph.fromEdgeSet
      (A : Set (Sym2 V))).IsTree := by
  classical
  let D : TightLaminarBasisData A ∅ B y :=
    Classical.choice (exists_tightLaminarBasisData hy hpos hext)
  have hXempty : D.degreeVertices = ∅ :=
    Finset.eq_empty_iff_forall_notMem.2 fun v hv => by
      have hnot : v ∉ (∅ : Finset V) := by simp
      exact hnot (D.degreeVertices_subset hv)
  have hdecomp := D.card_decomposition
  rw [hXempty] at hdecomp
  simp only [Finset.card_empty, add_zero] at hdecomp
  have hLbound :
      D.laminarSets.card ≤ Fintype.card V - 1 :=
    laminar_card_le_card_vertices_sub_one D.laminar
      (D.laminarSets_card_ge_two hy hcard hpos)
  have hAle : A.card ≤ Fintype.card V - 1 := by
    omega
  have hAge : Fintype.card V - 1 ≤ A.card :=
    hy.total_card_le
  have hAcard : A.card = Fintype.card V - 1 := by
    omega
  let T : SimpleGraph V :=
    SimpleGraph.fromEdgeSet (A : Set (Sym2 V))
  have hconn : T.Connected :=
    residualSupportGraph_connected hy hcard hpos
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hedgeSet :
      T.edgeSet = (A : Set (Sym2 V)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · intro he
      exact he.1
    · intro heA
      exact ⟨heA,
        hy.not_isDiag_of_mem hcard hpos heA⟩
  rw [hedgeSet]
  simp only [Nat.card_eq_fintype_card]
  let edgeEquiv : (A : Set (Sym2 V)) ≃ A :=
    Equiv.setCongr rfl
  have hsetCard :
      Fintype.card (A : Set (Sym2 V)) = A.card := by
    rw [Fintype.card_congr edgeEquiv, Fintype.card_coe]
  rw [hsetCard, hAcard]
  omega

/-! ## Iterative relaxation -/

/-- The strong-induction form of Singh--Lau's Algorithm II.  The induction
parameter is the active set `W`; at each step the progress lemma chooses which
vertex constraint to erase. -/
theorem round_aux
    (hcard : 1 < Fintype.card V)
    (B : ℕ)
    (A : Finset (Sym2 V)) (W : Finset V)
    (hne : (residualPolytope A W B).Nonempty)
    (hcap : InactiveCap A W B) :
    ∃ F : Finset (Sym2 V),
      F ⊆ A ∧
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsTree ∧
      ∀ v, (residualIncidentEdges F v).card ≤ B + 1 := by
  classical
  induction W using Finset.strongInductionOn generalizing A with
  | _ W ih =>
    rcases exists_extreme_residual hne with ⟨y, hext⟩
    have hy : ResidualFeasible A W B y := hext.1
    let A' := supportEdges A y
    have hA'sub : A' ⊆ A := supportEdges_subset A y
    have hy' : ResidualFeasible A' W B y := by
      simpa [A'] using hy.restrict_support
    have hext' :
        y ∈ (residualPolytope A' W B).extremePoints ℝ := by
      simpa [A'] using extreme_restrict_support hy hext
    have hpos : ∀ e ∈ A', 0 < y e := by
      intro e he
      exact (mem_supportEdges.1 he).2
    by_cases hWempty : W = ∅
    · subst W
      refine ⟨A', hA'sub,
        extreme_without_degree_constraints_is_tree
          hy' hcard hpos hext', ?_⟩
      intro v
      exact le_trans
        (Finset.card_le_card
          (residualIncidentEdges_mono hA'sub v))
        (hcap v (by simp))
    · have hWne : W.Nonempty :=
        Finset.nonempty_iff_ne_empty.2 hWempty
      rcases exists_small_active_vertex hy' hcard hpos hext' hWne with
        ⟨v, hvW, hvsmall⟩
      let W' := W.erase v
      have hW'ssub : W' ⊂ W := by
        simpa [W'] using Finset.erase_ssubset hvW
      have hne' : (residualPolytope A' W' B).Nonempty := by
        refine ⟨y, ?_⟩
        exact hy'.mono_active (by
          intro u hu
          exact Finset.mem_of_mem_erase hu)
      have hcap' : InactiveCap A' W' B := by
        intro u hu
        by_cases huv : u = v
        · subst u
          exact hvsmall
        · have huW : u ∉ W := by
            intro huW
            exact hu (Finset.mem_erase.2 ⟨huv, huW⟩)
          exact le_trans
            (Finset.card_le_card
              (residualIncidentEdges_mono hA'sub u))
            (hcap u huW)
      rcases ih W' hW'ssub A' hne' hcap' with
        ⟨F, hFA', htree, hdegree⟩
      exact ⟨F, fun e he => hA'sub (hFA' he), htree, hdegree⟩

/-- The Singh--Lau additive-one bounded-degree spanning-tree theorem, proved
from the residual-polytope argument above. -/
theorem boundedDegreeSpanningTree_proved :
    BoundedDegreeSpanningTreeStatement := by
  intro V _instFintype _instDecidableEq G B hcard point
  classical
  have hinitial :
      ∃ A : Finset (Sym2 V),
        (residualPolytope A Finset.univ B).Nonempty ∧
        InactiveCap A Finset.univ B ∧
        (∀ e, e ∈ A ↔ e ∈ G.edgeSet) := by
    refine ⟨_, ⟨initialRealWeight G B point,
      feasibleBoundedDegreePoint_residual G B point⟩, ?_, ?_⟩
    · intro v hv
      simp at hv
    · intro e
      simp
  rcases hinitial with ⟨A, hne, hcap, hAedge⟩
  rcases round_aux hcard B A Finset.univ hne hcap with
    ⟨F, hFG, htree, hdegree⟩
  let T : SimpleGraph V :=
    SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  have hFnondiag : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e heF
    exact G.not_isDiag_of_mem_edgeSet
      ((hAedge e).1 (hFG heF))
  have hedgeFinset : T.edgeFinset = F := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, T,
      SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff,
      Finset.mem_coe, Sym2.mem_diagSet]
    constructor
    · exact fun he => he.1
    · exact fun he => ⟨he, hFnondiag e he⟩
  refine ⟨T, ?_, htree, ?_⟩
  · change SimpleGraph.fromEdgeSet (F : Set (Sym2 V)) ≤ G
    rw [SimpleGraph.fromEdgeSet_le]
    intro e he
    exact (hAedge e).1 (hFG he.1)
  · intro v
    refine ⟨T.neighborFinset v, ?_, ?_⟩
    · intro u
      exact T.mem_neighborFinset v u
    · rw [T.card_neighborFinset_eq_degree,
        ← T.card_incidenceFinset_eq_degree]
      have hinc :
          T.incidenceFinset v = residualIncidentEdges F v := by
        rw [T.incidenceFinset_eq_filter, hedgeFinset]
        ext e
        simp [residualIncidentEdges]
      rw [hinc]
      exact hdegree v

end
end SinghLau
end SimpleGraph

end Lax17Proofs
