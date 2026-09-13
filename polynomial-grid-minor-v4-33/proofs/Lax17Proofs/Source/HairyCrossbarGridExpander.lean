import Mathlib.Tactic
import Lax17Proofs.Source.HairyCrossbarGrid
import Lax17Proofs.Source.ExpanderTheorem81

namespace Lax17Proofs

universe u v w

/-!
# The expander theorem handoff in the hairy crossbar grid construction

This file connects the self-contained proof of Theorem 8.1 from `expander.pdf`
to the Chuzhoy--Tan cut-matching auxiliary graph built in
`HairyCrossbarGrid.lean`.

The existing crossbar-grid module reduced the final post-cut-matching step to
an abstract `SeparatorGridMinorTheoremAt`.  The lemmas here replace that
abstract separator-to-grid input by the explicit Theorem 8.1 statement, plus
the concrete target-size inequality for the canonical grid target.
-/

namespace SimpleGraph


/-- The finite set of indices consecutive to a fixed `Fin` index. -/
noncomputable def finConsecutiveFinset {n : ℕ} (a : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun b => FinConsecutive a b

@[simp] theorem mem_finConsecutiveFinset {n : ℕ} (a b : Fin n) :
    b ∈ finConsecutiveFinset a ↔ FinConsecutive a b := by
  classical
  simp [finConsecutiveFinset]

/-- A two-valued orientation for a consecutive neighbor of `a`: successor or
predecessor.  It is used only as a counting device. -/
def finConsecutiveSide {n : ℕ} (a b : Fin n) : Bool :=
  decide (a.1 + 1 = b.1)

/-- For a fixed finite index, the predecessor/successor side determines a
consecutive neighbor. -/
theorem finConsecutive_eq_of_side_eq {n : ℕ} {a b c : Fin n}
    (hb : FinConsecutive a b) (hc : FinConsecutive a c)
    (hside : finConsecutiveSide a b = finConsecutiveSide a c) :
    b = c := by
  unfold finConsecutiveSide at hside
  rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact Fin.ext (hb.symm.trans hc)
  · have hcnot : ¬ a.1 + 1 = c.1 := by
      intro h
      omega
    have hbc : b.1 = c.1 := by
      simpa [hb, hcnot] using hside
    omega
  · have hbnot : ¬ a.1 + 1 = b.1 := by
      intro h
      omega
    have hcb : c.1 = b.1 := by
      simpa [hbnot, hc] using hside
    omega
  · exact Fin.ext (Nat.succ.inj (hb.trans hc.symm))

/-- A point of a line grid has at most two consecutive neighbors. -/
theorem finConsecutiveFinset_card_le_two {n : ℕ} (a : Fin n) :
    (finConsecutiveFinset a).card ≤ 2 := by
  classical
  have hcard :
      (finConsecutiveFinset a).card ≤
        (Finset.univ : Finset Bool).card := by
    refine Finset.card_le_card_of_injOn
      (fun b : Fin n => finConsecutiveSide a b)
      ?_ ?_
    · intro b _hb
      simp
    · intro b hb c hc hside
      exact finConsecutive_eq_of_side_eq
        ((mem_finConsecutiveFinset a b).1 hb)
        ((mem_finConsecutiveFinset a c).1 hc) hside
  simpa using hcard

/-- Candidate horizontal neighbors of a grid vertex. -/
noncomputable def gridHorizontalNeighborFinset {g : ℕ} (x : GridVertex g) :
    Finset (GridVertex g) :=
  ({x.1} : Finset (Fin g)) ×ˢ finConsecutiveFinset x.2

/-- Candidate vertical neighbors of a grid vertex. -/
noncomputable def gridVerticalNeighborFinset {g : ℕ} (x : GridVertex g) :
    Finset (GridVertex g) :=
  finConsecutiveFinset x.1 ×ˢ ({x.2} : Finset (Fin g))

/-- There are at most two horizontal grid-neighbor candidates. -/
theorem gridHorizontalNeighborFinset_card_le_two {g : ℕ}
    (x : GridVertex g) :
    (gridHorizontalNeighborFinset x).card ≤ 2 := by
  classical
  simpa [gridHorizontalNeighborFinset] using
    finConsecutiveFinset_card_le_two x.2

/-- There are at most two vertical grid-neighbor candidates. -/
theorem gridVerticalNeighborFinset_card_le_two {g : ℕ}
    (x : GridVertex g) :
    (gridVerticalNeighborFinset x).card ≤ 2 := by
  classical
  simpa [gridVerticalNeighborFinset] using
    finConsecutiveFinset_card_le_two x.1

/-- The canonical grid-neighbor set is contained in the union of the two
horizontal and two vertical candidates. -/
theorem gridGraph_neighborFinset_subset_candidates {g : ℕ}
    (x : GridVertex g) :
    (gridGraph g).neighborFinset x ⊆
      gridHorizontalNeighborFinset x ∪ gridVerticalNeighborFinset x := by
  classical
  intro y hy
  have hxy : (gridGraph g).Adj x y := by
    simpa using hy
  rcases hxy with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · exact Finset.mem_union.mpr (Or.inl (by
      simp [gridHorizontalNeighborFinset, hrow, hcol]))
  · exact Finset.mem_union.mpr (Or.inr (by
      simp [gridVerticalNeighborFinset, hcol, hrow]))

/-- Every vertex of the canonical square grid has degree at most four. -/
theorem gridGraph_degreeAtMost_four {g : ℕ} (x : GridVertex g) :
    DegreeAtMost (gridGraph g) x 4 := by
  classical
  refine
    ⟨gridHorizontalNeighborFinset x ∪ gridVerticalNeighborFinset x,
      ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      rw [Finset.mem_union] at hy
      rcases hy with hy | hy
      · rcases Finset.mem_product.mp hy with ⟨hrow, hcol⟩
        have hrow' : y.1 = x.1 := by simpa using hrow
        have hcol' : FinConsecutive x.2 y.2 :=
          (mem_finConsecutiveFinset x.2 y.2).1 hcol
        exact Or.inl ⟨hrow'.symm, hcol'⟩
      · rcases Finset.mem_product.mp hy with ⟨hrow, hcol⟩
        have hrow' : FinConsecutive x.1 y.1 :=
          (mem_finConsecutiveFinset x.1 y.1).1 hrow
        have hcol' : y.2 = x.2 := by simpa using hcol
        exact Or.inr ⟨hcol'.symm, hrow'⟩
    · intro hxy
      rw [Finset.mem_union]
      rcases hxy with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
      · exact Or.inl (by
          simp [gridHorizontalNeighborFinset, hrow, hcol])
      · exact Or.inr (by
          simp [gridVerticalNeighborFinset, hcol, hrow])
  · have hsubset := gridGraph_neighborFinset_subset_candidates x
    have hcard_sum :
        (gridHorizontalNeighborFinset x ∪ gridVerticalNeighborFinset x).card ≤
          (gridHorizontalNeighborFinset x).card +
            (gridVerticalNeighborFinset x).card :=
      Finset.card_union_le _ _
    have hh := gridHorizontalNeighborFinset_card_le_two x
    have hv := gridVerticalNeighborFinset_card_le_two x
    omega

/-- The canonical square grid has maximum degree at most four. -/
theorem gridGraph_maxDegreeAtMost_four (g : ℕ) :
    MaxDegreeAtMost (gridGraph g) 4 := by
  intro x
  exact gridGraph_degreeAtMost_four x

/-- The lifted canonical square grid has maximum degree at most four. -/
theorem gridGraphULift_maxDegreeAtMost_four (g : ℕ) :
    MaxDegreeAtMost (gridGraphULift.{u} g) 4 := by
  classical
  intro x
  rcases gridGraph_degreeAtMost_four (Equiv.ulift x) with
    ⟨N, hN, hcard⟩
  refine ⟨N.map Equiv.ulift.symm.toEmbedding, ?_, by simpa using hcard⟩
  intro y
  constructor
  · intro hy
    rcases Finset.mem_map.mp hy with ⟨z, hz, hzy⟩
    subst y
    change (gridGraph g).Adj (Equiv.ulift x) z
    exact (hN z).1 hz
  · intro hxy
    change (gridGraph g).Adj (Equiv.ulift x) (Equiv.ulift y) at hxy
    exact Finset.mem_map.mpr
      ⟨Equiv.ulift y, (hN (Equiv.ulift y)).2 hxy, by simp⟩

/-- A finite graph with maximum degree at most `d` has at most `d|V|` edges.
The proof deliberately keeps the weaker no-division bound because it is enough
for target-size estimates. -/
theorem edgeFinset_card_le_mul_card_of_maxDegreeAtMost
    {X : Type u} [Fintype X] [DecidableEq X]
    {G : _root_.SimpleGraph X} [DecidableRel G.Adj] {d : ℕ}
    (hmax : MaxDegreeAtMost G d) :
    G.edgeFinset.card ≤ d * Fintype.card X := by
  classical
  have hsum_le : (∑ x : X, G.degree x) ≤ ∑ _x : X, d := by
    exact Finset.sum_le_sum fun x _ =>
      SubcubicExpansion.degree_le_of_degreeAtMost (hmax x)
  have htwice : 2 * G.edgeFinset.card ≤ d * Fintype.card X := by
    calc
      2 * G.edgeFinset.card = ∑ x : X, G.degree x := by
        exact (G.sum_degrees_eq_twice_card_edges).symm
      _ ≤ ∑ _x : X, d := hsum_le
      _ = d * Fintype.card X := by
        simp [Finset.sum_const, mul_comm]
  omega

/-- The canonical lifted `g x g` grid has vertices-plus-edges complexity at
most `5 g^2`. -/
theorem targetComplexity_gridGraphULift_le_five_mul_sq (g : ℕ)
    [Fintype (gridGraphULift.{u} g).edgeSet] :
    targetComplexity (gridGraphULift.{u} g) ≤ 5 * g ^ 2 := by
  classical
  letI : DecidableRel (gridGraphULift.{u} g).Adj :=
    Classical.decRel (gridGraphULift.{u} g).Adj
  have hEdges0 :
      (@_root_.SimpleGraph.edgeFinset (GridVertexULift.{u} g)
        (gridGraphULift.{u} g)
        ((gridGraphULift.{u} g).fintypeEdgeSet)).card ≤
        4 * Fintype.card (GridVertexULift.{u} g) :=
    edgeFinset_card_le_mul_card_of_maxDegreeAtMost
      (G := gridGraphULift.{u} g)
      (d := 4) (gridGraphULift_maxDegreeAtMost_four g)
  have hEdgeFinset_eq :
      (gridGraphULift.{u} g).edgeFinset =
        @_root_.SimpleGraph.edgeFinset (GridVertexULift.{u} g)
          (gridGraphULift.{u} g)
          ((gridGraphULift.{u} g).fintypeEdgeSet) := by
    ext e
    simp
  have hEdges :
      (gridGraphULift.{u} g).edgeFinset.card ≤
        4 * Fintype.card (GridVertexULift.{u} g) := by
    rw [hEdgeFinset_eq]
    exact hEdges0
  have hcard : Fintype.card (GridVertexULift.{u} g) = g ^ 2 := by
    simp [GridVertexULift, pow_two]
  calc
    targetComplexity (gridGraphULift.{u} g)
        = Fintype.card (GridVertexULift.{u} g) +
          (gridGraphULift.{u} g).edgeFinset.card := by
          simp [targetComplexity]
    _ ≤ Fintype.card (GridVertexULift.{u} g) +
          4 * Fintype.card (GridVertexULift.{u} g) := by
          exact Nat.add_le_add_left hEdges _
    _ = 5 * g ^ 2 := by
          omega

/-- It is enough to check the Theorem 8.1 target-size budget with the coarse
bound `targetComplexity(gridGraph g') <= 5(g')^2`. -/
theorem targetSmallForHost_gridGraphULift_of_five_mul_sq
    {g g' targetScale : ℕ}
    [Fintype (gridGraphULift.{0} g').edgeSet]
    (hbudget :
      targetScale * (5 * g' ^ 2) *
          Nat.log 2 (Fintype.card (GridVertex g)) ≤
        Fintype.card (GridVertex g)) :
    TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} g')
      targetScale := by
  classical
  have hcomplex :
      targetComplexity (gridGraphULift.{0} g') ≤ 5 * g' ^ 2 :=
    targetComplexity_gridGraphULift_le_five_mul_sq g'
  calc
    targetScale * targetComplexity (gridGraphULift.{0} g') *
        Nat.log 2 (Fintype.card (GridVertex g))
        ≤ targetScale * (5 * g' ^ 2) *
            Nat.log 2 (Fintype.card (GridVertex g)) := by
          exact Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left targetScale hcomplex)
    _ ≤ Fintype.card (GridVertex g) := hbudget

/-- Division by a positive denominator gives the standard ceiling-style upper
multiple: `n <= a * (n/a + 1)`. -/
theorem le_mul_div_succ_of_pos (n a : ℕ) (ha : 0 < a) :
    n ≤ a * (n / a + 1) := by
  have h := (Nat.lt_div_mul_add (a := n) (b := a) ha).le
  calc
    n ≤ n / a * a + a := h
    _ = a * (n / a + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (n / a) a]

/-- If the denominator is below `n`, then the same ceiling-style multiple is
at most `2n`. -/
theorem mul_div_succ_le_two_mul_of_lt {n a : ℕ} (ha : a < n) :
    a * (n / a + 1) ≤ 2 * n := by
  calc
    a * (n / a + 1) = n / a * a + a := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm a (n / a)]
    _ ≤ n + a := by
      exact Nat.add_le_add_right (Nat.div_mul_le_self n a) a
    _ ≤ 2 * n := by
      omega

/-- The division-rounding target budget: if the rounded denominator times the
chosen order is at most `2g`, and the square of the denominator dominates the
fixed target denominator, then the grid target is small enough for a `g x g`
host. -/
theorem target_budget_of_denominator_square
    {g denom g' targetScale logCard : ℕ}
    (hprod : denom * g' ≤ 2 * g)
    (hdenom : 4 * (targetScale * 5 * logCard) ≤ denom ^ 2) :
    targetScale * (5 * g' ^ 2) * logCard ≤ g ^ 2 := by
  have hprod_sq : (denom * g') ^ 2 ≤ (2 * g) ^ 2 :=
    Nat.pow_le_pow_left hprod 2
  have hleft_le :
      4 * (targetScale * (5 * g' ^ 2) * logCard) ≤
        (denom * g') ^ 2 := by
    calc
      4 * (targetScale * (5 * g' ^ 2) * logCard)
          = (4 * (targetScale * 5 * logCard)) * g' ^ 2 := by
            ring_nf
      _ ≤ denom ^ 2 * g' ^ 2 := by
            exact Nat.mul_le_mul_right (g' ^ 2) hdenom
      _ = (denom * g') ^ 2 := by
            ring_nf
  have hscaled :
      4 * (targetScale * (5 * g' ^ 2) * logCard) ≤ 4 * g ^ 2 := by
    calc
      4 * (targetScale * (5 * g' ^ 2) * logCard)
          ≤ (denom * g') ^ 2 := hleft_le
      _ ≤ (2 * g) ^ 2 := hprod_sq
      _ = 4 * g ^ 2 := by
            ring_nf
  exact Nat.le_of_mul_le_mul_left hscaled (by decide : 0 < 4)

/-- For a power-of-two grid order, the binary logarithm of the canonical
`g x g` vertex set is exactly twice `log_2 g`. -/
theorem log_card_gridVertex_of_isPowerOfTwo {g : ℕ}
    (hpow : CrossbarContract.IsPowerOfTwo g) :
    Nat.log 2 (Fintype.card (GridVertex g)) = 2 * Nat.log 2 g := by
  rcases hpow with ⟨r, rfl⟩
  rw [card_gridVertex]
  rw [← Nat.pow_add, Nat.log_pow (by decide : 1 < 2),
    Nat.log_pow (by decide : 1 < 2)]
  omega

/-- A graph with no balanced separator at scale `d` cannot have a balanced
separator at the strictly stronger scale `d + 1`, provided the host is
nonempty.

This strict-scale version is the form needed to combine the repository's
non-strict predicates:
`NoSmallBalancedSeparator H d` says `|V| <= d * |S|`, while
`HasSmallBalancedSeparator H (d+1)` says `(d+1) * |S| <= |V|`. -/
theorem not_hasSmallBalancedSeparator_succ_of_noSmallBalancedSeparator
    {X : Type u} [Fintype X] [DecidableEq X]
    {H : _root_.SimpleGraph X} {d : ℕ}
    (hnosep : NoSmallBalancedSeparator H d)
    (hnpos : 0 < Fintype.card X) :
    ¬ HasSmallBalancedSeparator H (d + 1) := by
  intro hsmall
  rcases hsmall with ⟨A, B, S, hsep, hsmallS⟩
  have hlargeS : Fintype.card X ≤ d * S.card := hnosep hsep
  by_cases hSzero : S.card = 0
  · have hlargeZero : Fintype.card X ≤ 0 := by
      simpa [hSzero] using hlargeS
    omega
  · have hSpos : 0 < S.card := Nat.pos_of_ne_zero hSzero
    have hchain : (d + 1) * S.card ≤ d * S.card :=
      hsmallS.trans hlargeS
    rw [Nat.succ_mul] at hchain
    omega

/-- Theorem 8.1 turns a no-small-balanced-separator graph into a grid-minor
host when the target is the canonical lifted `g x g` grid and is small enough.

The separator theorem is invoked at scale `d + 1`, which is strictly stronger
than the available no-small-separator scale `d`; this removes the equality
case in the non-strict separator-size inequalities. -/
theorem containsGridMinor_of_expanderMinorTheoremAt_of_noSmallBalancedSeparator
    {X : Type u} [Fintype X] [DecidableEq X]
    (H : _root_.SimpleGraph X) {d g targetScale n₀ : ℕ}
    [hTargetEdges : Fintype (gridGraphULift.{u} g).edgeSet]
    (hminorTheorem :
      ExpanderMinorTheoremAt.{u, u} (d + 1) targetScale n₀)
    (hn : n₀ ≤ Fintype.card X)
    (hnosep : NoSmallBalancedSeparator H d)
    (hnpos : 0 < Fintype.card X)
    (hsmall :
      TargetSmallForHost (V := X) (gridGraphULift.{u} g) targetScale) :
    ContainsGridMinor H g := by
  classical
  have hnot :
      ¬ HasSmallBalancedSeparator H (d + 1) :=
    not_hasSmallBalancedSeparator_succ_of_noSmallBalancedSeparator
      hnosep hnpos
  have hor :
      HasSmallBalancedSeparator H (d + 1) ∨
        IsMinor (gridGraphULift.{u} g) H :=
    @hminorTheorem X inferInstance inferInstance
      (GridVertexULift.{u} g) inferInstance inferInstance
      H (gridGraphULift.{u} g) hTargetEdges hn hsmall
  rcases hor with
    hsep | hminor
  · exact False.elim (hnot hsep)
  · exact ⟨GridVertexULift.{u} g, inferInstance, inferInstance,
      gridGraphULift.{u} g, gridGraphULift_isGridGraph.{u} g,
      hminor⟩

/-- Explicit Theorem 8.1 handoff for grid targets, with the target-size
denominator specialized to separator scale `d + 1`. -/
theorem containsGridMinor_of_expanderTheorem81_of_noSmallBalancedSeparator
    {X : Type u} [Fintype X] [DecidableEq X]
    (H : _root_.SimpleGraph X) {d g : ℕ}
    [Fintype (gridGraphULift.{u} g).edgeSet]
    (hn : 2 ≤ Fintype.card X)
    (hnosep : NoSmallBalancedSeparator H d)
    (hsmall :
      TargetSmallForHost (V := X) (gridGraphULift.{u} g)
        ((3 * (d + 1) * (15 * (d + 1))) * 8)) :
    ContainsGridMinor H g := by
  exact
    containsGridMinor_of_expanderMinorTheoremAt_of_noSmallBalancedSeparator
      (H := H) (d := d) (g := g)
      (targetScale := (3 * (d + 1) * (15 * (d + 1))) * 8)
      (n₀ := 2)
      (expanderMinorTheoremAt_explicit (Nat.succ_pos d)) hn
      hnosep (lt_of_lt_of_le (by decide : 0 < 2) hn) hsmall

namespace HairyCrossbarGrid
namespace SelectedOddLocalCrossbarGridTransportedRoundFamily
namespace CutMatchingGameCertificate

/-- The self-contained Theorem 8.1 supplies the auxiliary grid minor for the
cut-matching graph, once the canonical grid target satisfies the explicit
target-size hypothesis. -/
theorem auxGraph_containsGridMinor_of_expanderTheorem81
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (htarget :
      TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} g')
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ContainsGridMinor F.auxGraph g' := by
  exact
    containsGridMinor_of_expanderTheorem81_of_noSmallBalancedSeparator
      (H := F.auxGraph) (d := 24 * roundBound) (g := g')
      hcard
      (C.noSmallBalancedSeparator_auxGraph_of_two_le_card hcard)
      htarget

/-- Host-level version of
`auxGraph_containsGridMinor_of_expanderTheorem81`: after the explicit
Theorem 8.1 handoff gives an auxiliary grid minor, the already-formalized
allocated branch-set model transports it back to the original graph. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete_of_expanderTheorem81
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (htarget :
      TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} g')
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact
    C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete
      hm
      (C.auxGraph_containsGridMinor_of_expanderTheorem81 hcard htarget)

end CutMatchingGameCertificate

namespace FinCutMatchingGameTranscript

/-- A finite cut-matching transcript plus the explicit Theorem 8.1 target-size
condition gives the host grid minor, with no abstract separator-grid theorem
remaining. -/
theorem containsGridMinor_of_expanderTheorem81
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (htarget :
      TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} g')
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ContainsGridMinor G g' := by
  let C := T.toCertificate
  exact
    (C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete_of_expanderTheorem81
      (T.selectedClusterCount_pos hcard) hcard htarget).1

/-- Contract-shaped transcript handoff using explicit Theorem 8.1 rather than
an abstract separator-grid theorem. -/
theorem exists_gridMinor_of_expanderTheorem81
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound c g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (hscale : g ≤ c * g' * (Nat.log 2 g) ^ 2)
    (htarget :
      TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} g')
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ∃ g'' : ℕ,
      g ≤ c * g'' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g'' := by
  exact ⟨g', hscale,
    T.containsGridMinor_of_expanderTheorem81 hcard htarget⟩

end FinCutMatchingGameTranscript
end SelectedOddLocalCrossbarGridTransportedRoundFamily

/-- Large-case crossbar-grid handoff after the cut-matching transcript and
explicit Theorem 8.1 target-size condition have been supplied. -/
theorem gridMinor_of_hairy_pathOfSets_and_crossbars_large_of_finCutMatchingTranscript_expanderTheorem81
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w g m roundBound c g' : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell)
    (T :
      SelectedOddLocalCrossbarGridTransportedRoundFamily.FinCutMatchingGameTranscript
        Hsys hcrossbars hlen roundBound)
    (hg : 2 ≤ g)
    (hscale : g ≤ c * g' * (Nat.log 2 g) ^ 2)
    (htarget :
      TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} g')
        ((3 * (24 * roundBound + 1) *
          (15 * (24 * roundBound + 1))) * 8)) :
    ∃ g'' : ℕ,
      g ≤ c * g'' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g'' :=
  T.exists_gridMinor_of_expanderTheorem81
    (two_le_card_gridVertex_of_two_le hg) hscale htarget

/-- Fixed-round large-case package whose post-expander obligation is the
explicit target-size inequality from Theorem 8.1, not an abstract
separator-grid theorem. -/
structure FixedRoundLargeCaseExpanderData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (cRound cScale : ℕ) where
  /-- Grid order produced in the auxiliary graph. -/
  gridOrder : ℕ
  /-- The length hypothesis specialized to the fixed round count. -/
  length_bound : 2 * largeCaseRoundBound cRound g ≤ ell
  /-- The transported transcript using exactly the fixed round count. -/
  transcript :
    SelectedOddLocalCrossbarGridTransportedRoundFamily.FinCutMatchingGameTranscript
      Hsys hcrossbars length_bound (largeCaseRoundBound cRound g)
  /-- The auxiliary grid order is large enough for the stated polylogarithmic
  loss at scale `cScale`. -/
  scale : g ≤ cScale * gridOrder * (Nat.log 2 g) ^ 2
  /-- The canonical grid target is small enough for Theorem 8.1 applied to the
  cut-matching auxiliary graph. -/
  targetSmall :
    TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} gridOrder)
      ((3 * (24 * largeCaseRoundBound cRound g + 1) *
        (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8)

namespace FixedRoundLargeCaseExpanderData

/-- A fixed-round expander package gives the exact grid-minor conclusion
needed by the large crossbar-grid assembly. -/
theorem exists_gridMinor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g cRound cScale c : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    (D : FixedRoundLargeCaseExpanderData Hsys hcrossbars cRound cScale)
    (hscale_le : cScale ≤ c) (hg : 2 ≤ g) :
    ∃ g' : ℕ,
      g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g' := by
  refine
    gridMinor_of_hairy_pathOfSets_and_crossbars_large_of_finCutMatchingTranscript_expanderTheorem81
      Hsys hcrossbars D.length_bound D.transcript hg ?_ D.targetSmall
  exact D.scale.trans (by
    gcongr)

end FixedRoundLargeCaseExpanderData

/-- Provider interface for the fixed-round cut-matching construction together
with the explicit Theorem 8.1 target-size arithmetic. -/
def FixedRoundLargeCaseExpanderDataProvider
    (cRound cScale : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w),
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
            (2 * cRound) * Nat.log 2 g ≤ ell →
              g ^ 2 ≤ w →
                cScale * (Nat.log 2 g) ^ 2 < g →
                  (hcrossbars :
                    ∀ i : Fin ell, OneBasedOdd i →
                      Nonempty (Crossbar (Hsys.hairLocalGraph i)
                        (Hsys.base.left i) (Hsys.base.right i)
                        (Hsys.y i) (g ^ 2))) →
                    Nonempty
                      (FixedRoundLargeCaseExpanderData
                        Hsys hcrossbars cRound cScale)

/-- Provider for the remaining arithmetic after the self-contained Theorem 8.1
handoff: choose an auxiliary grid order that has the required final scale and
is small enough relative to the `g x g` auxiliary coordinate graph. -/
def FixedRoundExpanderTargetProvider (cRound cScale : ℕ) : Prop :=
  ∀ {g : ℕ},
    2 ≤ g →
      CrossbarContract.IsPowerOfTwo g →
        cScale * (Nat.log 2 g) ^ 2 < g →
          ∃ g' : ℕ,
            g ≤ cScale * g' * (Nat.log 2 g) ^ 2 ∧
              TargetSmallForHost (V := GridVertex g) (gridGraphULift.{0} g')
                ((3 * (24 * largeCaseRoundBound cRound g + 1) *
                  (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8)

/-- The remaining arithmetic needed for `FixedRoundExpanderTargetProvider`,
with the auxiliary grid order chosen as
`g / (cScale * (log g)^2) + 1`.  This isolates the pure numerical estimate
from the graph-theoretic Theorem 8.1 handoff. -/
def FixedRoundExpanderTargetBudgetProvider (cRound cScale : ℕ) : Prop :=
  ∀ {g : ℕ},
    2 ≤ g →
      CrossbarContract.IsPowerOfTwo g →
        cScale * (Nat.log 2 g) ^ 2 < g →
          let L := Nat.log 2 g
          let denom := cScale * L ^ 2
          let g' := g / denom + 1
          ((3 * (24 * largeCaseRoundBound cRound g + 1) *
              (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8) *
              (5 * g' ^ 2) *
            Nat.log 2 (Fintype.card (GridVertex g)) ≤
              Fintype.card (GridVertex g)

/-- Stronger fixed-round arithmetic budget.  It removes the auxiliary order
from the inequality: after choosing
`g' = g / (cScale * (log g)^2) + 1`, it is enough for the squared denominator
to dominate the fixed target scale and one logarithmic host factor. -/
def FixedRoundExpanderDenominatorSquareBudgetProvider
    (cRound cScale : ℕ) : Prop :=
  ∀ {g : ℕ},
    2 ≤ g →
      CrossbarContract.IsPowerOfTwo g →
        cScale * (Nat.log 2 g) ^ 2 < g →
          let L := Nat.log 2 g
          let denom := cScale * L ^ 2
          4 *
              (((3 * (24 * largeCaseRoundBound cRound g + 1) *
                (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8) *
                  5 * Nat.log 2 (Fintype.card (GridVertex g))) ≤
            denom ^ 2

/-- Explicit target-size scale for the fixed-round expander handoff.  The
constant is intentionally coarse: it absorbs the target grid edge bound, the
Theorem 8.1 constants, the `24`-loss in the cut-matching separator scale, and
the factor four from division rounding. -/
def fixedRoundExpanderTargetScale (cRound : ℕ) : ℕ :=
  3000 * (cRound + 1)

/-- The explicit scale `3000 * (cRound + 1)` satisfies the denominator-square
target budget for every power-of-two large-case grid order. -/
theorem fixedRoundExpanderDenominatorSquareBudgetProvider_explicit
    (cRound : ℕ) :
    FixedRoundExpanderDenominatorSquareBudgetProvider cRound
      (fixedRoundExpanderTargetScale cRound) := by
  intro g hg hpow _hlarge
  let L := Nat.log 2 g
  have hL : 1 ≤ L := by
    exact Nat.succ_le_of_lt (by
      simpa [L] using Nat.log_pos (by decide : 1 < 2) hg)
  have hlogCard :
      Nat.log 2 (Fintype.card (GridVertex g)) = 2 * L := by
    simpa [L] using log_card_gridVertex_of_isPowerOfTwo hpow
  let A := 24 * (cRound * L) + 1
  let B := 25 * (cRound + 1) * L
  have hA : A ≤ B := by
    calc
      A = 24 * (cRound * L) + 1 := rfl
      _ ≤ 24 * (cRound * L) + L := Nat.add_le_add_left hL _
      _ = (24 * cRound + 1) * L := by ring_nf
      _ ≤ 25 * (cRound + 1) * L := by
            exact Nat.mul_le_mul_right L (by omega)
      _ = B := rfl
  have hLpow : L ^ 3 ≤ L ^ 4 :=
    pow_le_pow_right' hL (by decide : 3 ≤ 4)
  have harith :
      4 *
          (((3 * (24 * (cRound * L) + 1) *
            (15 * (24 * (cRound * L) + 1))) * 8) *
              5 * (2 * L)) ≤
        (3000 * (cRound + 1) * L ^ 2) ^ 2 := by
    change
      4 * (((3 * A * (15 * A)) * 8) * 5 * (2 * L)) ≤
        (3000 * (cRound + 1) * L ^ 2) ^ 2
    calc
      4 * (((3 * A * (15 * A)) * 8) * 5 * (2 * L))
          = 14400 * A ^ 2 * L := by ring_nf
      _ ≤ 14400 * B ^ 2 * L := by
            exact Nat.mul_le_mul_right L
              (Nat.mul_le_mul_left 14400 (Nat.pow_le_pow_left hA 2))
      _ = 9000000 * (cRound + 1) ^ 2 * L ^ 3 := by
            simp [B]
            ring_nf
      _ ≤ 9000000 * (cRound + 1) ^ 2 * L ^ 4 := by
            exact Nat.mul_le_mul_left (9000000 * (cRound + 1) ^ 2) hLpow
      _ = (3000 * (cRound + 1) * L ^ 2) ^ 2 := by
            ring_nf
  change
    4 *
        (((3 * (24 * largeCaseRoundBound cRound g + 1) *
          (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8) *
            5 * Nat.log 2 (Fintype.card (GridVertex g))) ≤
      (fixedRoundExpanderTargetScale cRound * L ^ 2) ^ 2
  rw [hlogCard]
  simpa [fixedRoundExpanderTargetScale, largeCaseRoundBound, L,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using harith

/-- The denominator-square budget implies the target budget for the rounded
auxiliary order. -/
theorem fixedRoundExpanderTargetBudgetProvider_of_denominator_square
    {cRound cScale : ℕ}
    (hsquare :
      FixedRoundExpanderDenominatorSquareBudgetProvider cRound cScale) :
    FixedRoundExpanderTargetBudgetProvider cRound cScale := by
  intro g hg hpow hlarge
  let L := Nat.log 2 g
  let denom := cScale * L ^ 2
  let g' := g / denom + 1
  have hprod : denom * g' ≤ 2 * g := by
    simpa [g'] using
      mul_div_succ_le_two_mul_of_lt (n := g) (a := denom)
        (by simpa [denom, L] using hlarge)
  have hdenom :
      4 *
          (((3 * (24 * largeCaseRoundBound cRound g + 1) *
            (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8) *
              5 * Nat.log 2 (Fintype.card (GridVertex g))) ≤
        denom ^ 2 := by
    simpa [FixedRoundExpanderDenominatorSquareBudgetProvider, L, denom] using
      hsquare hg hpow hlarge
  have hbudget :=
    target_budget_of_denominator_square
      (g := g) (denom := denom) (g' := g')
      (targetScale :=
        ((3 * (24 * largeCaseRoundBound cRound g + 1) *
          (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8))
      (logCard := Nat.log 2 (Fintype.card (GridVertex g)))
      hprod hdenom
  simpa [L, denom, g', pow_two] using hbudget

/-- A fixed-round target budget gives the target provider needed by the
expander handoff.  The scale part is the standard division rounding
`g <= (cScale(log g)^2) * (g/(cScale(log g)^2)+1)`. -/
theorem fixedRoundExpanderTargetProvider_of_budget
    {cRound cScale : ℕ} (hcScale : 0 < cScale)
    (hbudget : FixedRoundExpanderTargetBudgetProvider cRound cScale) :
    FixedRoundExpanderTargetProvider cRound cScale := by
  intro g hg hpow hlarge
  let L := Nat.log 2 g
  let denom := cScale * L ^ 2
  let g' := g / denom + 1
  refine ⟨g', ?_, ?_⟩
  · have hLpos : 0 < L := by
      simpa [L] using Nat.log_pos (by decide : 1 < 2) hg
    have hLsq : 0 < L ^ 2 := (Nat.pow_pos hLpos : 0 < L ^ 2)
    have hdenom : 0 < denom := by
      simpa [denom] using Nat.mul_pos hcScale hLsq
    have hscale := le_mul_div_succ_of_pos g denom hdenom
    simpa [denom, g', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscale
  · exact
      targetSmallForHost_gridGraphULift_of_five_mul_sq
        (g := g) (g' := g')
        (targetScale :=
          ((3 * (24 * largeCaseRoundBound cRound g + 1) *
            (15 * (24 * largeCaseRoundBound cRound g + 1))) * 8))
        (by
          simpa [FixedRoundExpanderTargetBudgetProvider, L, denom, g'] using
            hbudget hg hpow hlarge)

/-- A denominator-square budget supplies the fixed-round target provider. -/
theorem fixedRoundExpanderTargetProvider_of_denominator_square
    {cRound cScale : ℕ} (hcScale : 0 < cScale)
    (hsquare :
      FixedRoundExpanderDenominatorSquareBudgetProvider cRound cScale) :
    FixedRoundExpanderTargetProvider cRound cScale :=
  fixedRoundExpanderTargetProvider_of_budget hcScale
    (fixedRoundExpanderTargetBudgetProvider_of_denominator_square hsquare)

/-- The explicit fixed-round target scale is positive. -/
theorem fixedRoundExpanderTargetScale_pos (cRound : ℕ) :
    0 < fixedRoundExpanderTargetScale cRound := by
  simp [fixedRoundExpanderTargetScale]

/-- Concrete fixed-round Theorem 8.1 target provider. -/
theorem fixedRoundExpanderTargetProvider_explicit (cRound : ℕ) :
    FixedRoundExpanderTargetProvider cRound
      (fixedRoundExpanderTargetScale cRound) :=
  fixedRoundExpanderTargetProvider_of_denominator_square
    (fixedRoundExpanderTargetScale_pos cRound)
    (fixedRoundExpanderDenominatorSquareBudgetProvider_explicit cRound)

/-- Combining the fixed-round cut-matching transcript with the explicit
Theorem 8.1 target-size provider gives the fixed-round expander data package. -/
theorem fixedRoundLargeCaseExpanderDataProvider_of_transcript_and_target
    {cRound cScale : ℕ}
    (htranscript :
      FixedRoundCutMatchingTranscriptProvider.{u} cRound)
    (htarget : FixedRoundExpanderTargetProvider cRound cScale) :
    FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale := by
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hrounds hw hlarge hcrossbars
  rcases htranscript G Hsys hg hpow hmaxDegree hrounds hw hcrossbars with
    ⟨T⟩
  rcases htarget hg hpow hlarge with ⟨g', hscale, hsmall⟩
  exact ⟨{
    gridOrder := g'
    length_bound := T.length_bound
    transcript := T.transcript
    scale := hscale
    targetSmall := hsmall }⟩

/-- Existential combination of the transcript provider and the explicit
Theorem 8.1 target-size provider. -/
theorem exists_fixedRoundLargeCaseExpanderDataProvider_of_transcript_and_target
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingTranscriptProvider.{u} cRound ∧
          FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
      FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale := by
  rcases hproviders with
    ⟨cRound, cScale, hcRound, hcScale, htranscript, htarget⟩
  exact ⟨cRound, cScale, hcRound, hcScale,
    fixedRoundLargeCaseExpanderDataProvider_of_transcript_and_target
      htranscript htarget⟩

/-- Existential combination using the unbundled KRV-style cut sequence
provider instead of an already packaged transcript provider. -/
theorem exists_fixedRoundLargeCaseExpanderDataProvider_of_unbundled_and_target
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingUnbundledProvider.{u} cRound ∧
          FixedRoundExpanderTargetProvider cRound cScale) :
    ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
      FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale := by
  rcases hproviders with
    ⟨cRound, cScale, hcRound, hcScale, hunbundled, htarget⟩
  exact
    exists_fixedRoundLargeCaseExpanderDataProvider_of_transcript_and_target
      ⟨cRound, cScale, hcRound, hcScale,
        fixedRoundCutMatchingTranscriptProvider_of_unbundled hunbundled,
        htarget⟩

/-- The self-contained target-size arithmetic removes the target-provider
assumption from the fixed-round large-case package: only the KRV-style
cut-matching transcript provider remains. -/
theorem exists_fixedRoundLargeCaseExpanderDataProvider_of_unbundled
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        FixedRoundCutMatchingUnbundledProvider.{u} cRound) :
    ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
      FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale := by
  rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
  exact
    exists_fixedRoundLargeCaseExpanderDataProvider_of_unbundled_and_target
      ⟨cRound, fixedRoundExpanderTargetScale cRound, hcRound,
        fixedRoundExpanderTargetScale_pos cRound, hunbundled,
        fixedRoundExpanderTargetProvider_explicit cRound⟩

/-- Crossbar-grid assembly from a fixed-round expander data provider.  This
has the same conclusion as the older large-case-provider wrapper, but its
post-cut-matching input is the explicit Theorem 8.1 target-size arithmetic
rather than a separator-grid theorem. -/
theorem gridMinor_of_hairy_pathOfSets_and_crossbars_of_fixedRoundExpanderDataProvider
    {cRound cScale c : ℕ}
    (hround_le : 2 * cRound ≤ c) (hscale_le : cScale ≤ c)
    (hfixed :
      FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale) :
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
                        ContainsGridMinor G g' := by
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hcrossbars
  by_cases hsmall : g ≤ c * (Nat.log 2 g) ^ 2
  · exact gridMinor_of_hairy_pathOfSets_and_crossbars_of_le_constant
      Hsys hsmall
  · have hrounds : (2 * cRound) * Nat.log 2 g ≤ ell := by
      exact (Nat.mul_le_mul_right (Nat.log 2 g) hround_le).trans hell
    have hlarge_fixed : cScale * (Nat.log 2 g) ^ 2 < g := by
      exact lt_of_le_of_lt
        (Nat.mul_le_mul_right ((Nat.log 2 g) ^ 2) hscale_le)
        (Nat.lt_of_not_ge hsmall)
    rcases hfixed G Hsys hg hpow hmaxDegree hrounds hw hlarge_fixed
        hcrossbars with
      ⟨D⟩
    exact D.exists_gridMinor hscale_le hg

/-- Existential wrapper for the fixed-round expander provider.  The single
constant used by the rest of the crossbar-grid proof can be taken to be
`max (2*cRound) cScale`. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_fixedRoundExpanderDataProvider
    (hfixed :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale) :
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
                          ContainsGridMinor G g' := by
  rcases hfixed with ⟨cRound, cScale, hcRound, hcScale, hprovider⟩
  let c := max (2 * cRound) cScale
  refine ⟨c, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.mul_pos (by decide : 0 < 2) hcRound)
      (le_max_left (2 * cRound) cScale)
  · exact gridMinor_of_hairy_pathOfSets_and_crossbars_of_fixedRoundExpanderDataProvider
      (le_max_left (2 * cRound) cScale)
      (le_max_right (2 * cRound) cScale)
      hprovider

/-- Direct existential conversion from the separated transcript and
Theorem 8.1 target-size providers to the crossbar-grid conclusion. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_transcript_and_target
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingTranscriptProvider.{u} cRound ∧
          FixedRoundExpanderTargetProvider cRound cScale) :
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
    (exists_fixedRoundLargeCaseExpanderDataProvider_of_transcript_and_target
      hproviders)

/-- Direct existential conversion from the unbundled cut-sequence provider and
the explicit Theorem 8.1 target-size provider to the crossbar-grid conclusion. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_unbundled_and_target
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingUnbundledProvider.{u} cRound ∧
          FixedRoundExpanderTargetProvider cRound cScale) :
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
    (exists_fixedRoundLargeCaseExpanderDataProvider_of_unbundled_and_target
      hproviders)

/-- Crossbar-grid conclusion with the target-size arithmetic fully internal:
the only remaining large-case input is the fixed-round cut-matching provider. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_unbundled
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        FixedRoundCutMatchingUnbundledProvider.{u} cRound) :
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
    (exists_fixedRoundLargeCaseExpanderDataProvider_of_unbundled hprovider)

end HairyCrossbarGrid
end SimpleGraph

end Lax17Proofs
