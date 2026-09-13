import Lax17Proofs.Source.ChekuriChuzhoySection5Clustering

namespace Lax17Proofs

universe u v w

/-!
# The source potential for Chekuri--Chuzhoy Section 5.2

Chekuri and Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*,
journal Section 5.2, define the potential of a crossing edge `uv` to be

`1 + rho (|out(C_u)|) + rho (|out(C_v)|)`.

This file supplies the graph-theoretic part of that definition over `Rat`.
The numerical construction of `rho` and the decrease estimates used by
Theorem 5.5 and Claims 5.6--5.7 are kept in the action module.  Keeping the
two parts separate makes all uses of the analytic estimates explicit.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5SourcePotential


open scoped BigOperators
open ChekuriChuzhoySection5Clustering

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The properties of `rho` used by Observation 5.4.  The paper proves the
upper bound `rho(z) ≤ 1/28`; the slightly weaker `1/20` bound is exactly what
is needed for the displayed edge bound `phi(e) ≤ 1.1`. -/
structure BoundedContribution where
  rho : Nat → Rat
  nonnegative : ∀ z, 0 ≤ rho z
  monotone : Monotone rho
  upper : ∀ z, rho z ≤ (1 : Rat) / 20

/-- Source potential of one original edge. -/
noncomputable def edgePotential
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (schedule : BoundedContribution) : Sym2 V → Rat := by
  classical
  exact Sym2.lift ⟨fun u v =>
    if P.block u = P.block v then 0
    else
      1 + schedule.rho (endpointBoundarySize G P u) +
        schedule.rho (endpointBoundarySize G P v), by
          intro u v
          by_cases h : P.block u = P.block v
          · simp only [if_pos h, if_pos h.symm]
          · have h' : P.block v ≠ P.block u := ne_comm.mp h
            simp only [if_neg h, if_neg h']
            ring⟩

@[simp] theorem edgePotential_mk
    (P : VertexClustering V) (schedule : BoundedContribution)
    (u v : V) :
    edgePotential G P schedule s(u, v) =
      if P.block u = P.block v then 0
      else
        1 + schedule.rho (endpointBoundarySize G P u) +
          schedule.rho (endpointBoundarySize G P v) := by
  classical
  simp only [edgePotential, Sym2.lift_mk]

theorem edgePotential_eq_zero_of_same_block
    (P : VertexClustering V) (schedule : BoundedContribution)
    {u v : V} (h : P.block u = P.block v) :
    edgePotential G P schedule s(u, v) = 0 := by
  simp [edgePotential_mk, h]

theorem edgePotential_eq_of_crosses
    (P : VertexClustering V) (schedule : BoundedContribution)
    {u v : V} (h : P.block u ≠ P.block v) :
    edgePotential G P schedule s(u, v) =
      1 + schedule.rho (endpointBoundarySize G P u) +
        schedule.rho (endpointBoundarySize G P v) := by
  simp [edgePotential_mk, h]

/-- Observation 5.4, lower half. -/
theorem one_le_edgePotential_of_crosses
    (P : VertexClustering V) (schedule : BoundedContribution)
    {e : Sym2 V} (h : crossesBlocks P e) :
    (1 : Rat) ≤ edgePotential G P schedule e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [edgePotential_eq_of_crosses]
      · linarith [schedule.nonnegative
          (endpointBoundarySize G P u),
          schedule.nonnegative (endpointBoundarySize G P v)]
      · simpa using h

/-- Observation 5.4, upper half, in the exact rational form `11 / 10`. -/
theorem edgePotential_le_eleven_tenths_of_crosses
    (P : VertexClustering V) (schedule : BoundedContribution)
    {e : Sym2 V} (h : crossesBlocks P e) :
    edgePotential G P schedule e ≤ (11 : Rat) / 10 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [edgePotential_eq_of_crosses]
      · linarith [schedule.upper (endpointBoundarySize G P u),
          schedule.upper (endpointBoundarySize G P v)]
      · simpa using h

theorem edgePotential_nonnegative
    (P : VertexClustering V) (schedule : BoundedContribution)
    (e : Sym2 V) :
    0 ≤ edgePotential G P schedule e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases h : P.block u = P.block v
      · rw [edgePotential_eq_zero_of_same_block (G := G) P schedule h]
      · exact (show (0 : Rat) ≤ 1 by norm_num).trans
          (one_le_edgePotential_of_crosses
            (G := G) P schedule (by simpa using h))

theorem edgePotential_le_eleven_tenths
    (P : VertexClustering V) (schedule : BoundedContribution)
    (e : Sym2 V) :
    edgePotential G P schedule e ≤ (11 : Rat) / 10 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      by_cases h : P.block u = P.block v
      · rw [edgePotential_eq_zero_of_same_block (G := G) P schedule h]
        norm_num
      · exact edgePotential_le_eleven_tenths_of_crosses
          (G := G) P schedule (by simpa using h)

/-- A canonical finite presentation of the original edge set.  Defining this
directly from the finite vertex type avoids depending on a choice of
`Fintype G.edgeSet`. -/
noncomputable def sourceEdgeFinset
    (G : _root_.SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ G.edgeSet

@[simp] theorem mem_sourceEdgeFinset {e : Sym2 V} :
    e ∈ sourceEdgeFinset G ↔ e ∈ G.edgeSet := by
  classical
  simp [sourceEdgeFinset]

/-- Sum of source edge potentials over the original finite edge set. -/
noncomputable def clusteringPotential
    (G : _root_.SimpleGraph V) (P : VertexClustering V)
    (schedule : BoundedContribution) : Rat :=
  ∑ e ∈ sourceEdgeFinset G, edgePotential G P schedule e

theorem clusteringPotential_eq_sum_crossBlockOriginalEdges
    (P : VertexClustering V) (schedule : BoundedContribution) :
    clusteringPotential G P schedule =
      ∑ e ∈ crossBlockOriginalEdges G P,
        edgePotential G P schedule e := by
  classical
  symm
  have hsubset :
      crossBlockOriginalEdges G P ⊆ sourceEdgeFinset G := by
    intro e he
    exact mem_sourceEdgeFinset.mpr
      ((mem_crossBlockOriginalEdges (G := G) P e).1 he).1
  apply Finset.sum_subset hsubset
  intro e heG heNot
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hsame : P.block u = P.block v := by
        by_contra hne
        exact heNot ((mk_mem_crossBlockOriginalEdges (G := G) P u v).2
          ⟨by simpa using (mem_sourceEdgeFinset.mp heG), hne⟩)
      exact edgePotential_eq_zero_of_same_block
        (G := G) P schedule hsame

/-- The source potential is nonnegative. -/
theorem clusteringPotential_nonnegative
    (P : VertexClustering V) (schedule : BoundedContribution) :
    0 ≤ clusteringPotential G P schedule := by
  classical
  rw [clusteringPotential_eq_sum_crossBlockOriginalEdges]
  apply Finset.sum_nonneg
  intro e he
  exact (show (0 : Rat) ≤ 1 by norm_num).trans
    (one_le_edgePotential_of_crosses (G := G) P schedule
      ((mem_crossBlockOriginalEdges (G := G) P e).1 he).2)

/-- The number of crossing original edges is a lower bound for the source
potential. -/
theorem crossBlockOriginalEdges_card_le_potential
    (P : VertexClustering V) (schedule : BoundedContribution) :
    ((crossBlockOriginalEdges G P).card : Rat) ≤
      clusteringPotential G P schedule := by
  classical
  rw [clusteringPotential_eq_sum_crossBlockOriginalEdges]
  calc
    ((crossBlockOriginalEdges G P).card : Rat) =
        ∑ _e ∈ crossBlockOriginalEdges G P, (1 : Rat) := by simp
    _ ≤ ∑ e ∈ crossBlockOriginalEdges G P,
        edgePotential G P schedule e := by
      apply Finset.sum_le_sum
      intro e he
      exact one_le_edgePotential_of_crosses (G := G) P schedule
        ((mem_crossBlockOriginalEdges (G := G) P e).1 he).2

/-- The upper estimate following Claim 5.7. -/
theorem clusteringPotential_le_eleven_tenths_mul_crossing_card
    (P : VertexClustering V) (schedule : BoundedContribution) :
    clusteringPotential G P schedule ≤
      (11 : Rat) / 10 * (crossBlockOriginalEdges G P).card := by
  classical
  rw [clusteringPotential_eq_sum_crossBlockOriginalEdges]
  calc
    ∑ e ∈ crossBlockOriginalEdges G P,
        edgePotential G P schedule e ≤
        ∑ _e ∈ crossBlockOriginalEdges G P, (11 : Rat) / 10 := by
      apply Finset.sum_le_sum
      intro e he
      exact edgePotential_le_eleven_tenths_of_crosses
        (G := G) P schedule
        ((mem_crossBlockOriginalEdges (G := G) P e).1 he).2
    _ = (11 : Rat) / 10 *
        (crossBlockOriginalEdges G P).card := by
      simp
      ring

/-- A potential drop by one unit, the conclusion of each phase in Theorem
5.8 after the paper's within-phase actions have been accumulated. -/
def DropsByOne
    (G : _root_.SimpleGraph V) (schedule : BoundedContribution)
    (P Q : VertexClustering V) : Prop :=
  clusteringPotential G Q schedule + 1 ≤
    clusteringPotential G P schedule

/-! ## The finite descent used in Theorem 5.8 -/

/-- A nonnegative rational measure that drops by one cannot support more
steps than an integral upper bound.  This is the source-faithful termination
argument behind Theorem 5.8, without adding a real-valued well-foundedness
assumption. -/
private theorem output_of_bounded_rat_descent
    {State : Type*} (potential : State → Rat) (Valid : State → Prop)
    (Output : Prop)
    (hnonnegative : ∀ state, Valid state → 0 ≤ potential state)
    (step : ∀ state, Valid state →
      Output ∨
        ∃ next, Valid next ∧ potential next + 1 ≤ potential state) :
    ∀ fuel : Nat, ∀ state, Valid state →
      potential state ≤ fuel → Output := by
  intro fuel
  induction fuel with
  | zero =>
      intro state hvalid hbound
      rcases step state hvalid with houtput | ⟨next, hnext, hdrop⟩
      · exact houtput
      · have hnextNonnegative := hnonnegative next hnext
        norm_num at hbound
        linarith
  | succ fuel ih =>
      intro state hvalid hbound
      rcases step state hvalid with houtput | ⟨next, hnext, hdrop⟩
      · exact houtput
      · apply ih next hnext
        norm_num at hbound ⊢
        linarith

theorem clusteringPotential_le_two_mul_edge_card
    (P : VertexClustering V) (schedule : BoundedContribution) :
    clusteringPotential G P schedule ≤
      (2 * (sourceEdgeFinset G).card : Nat) := by
  have hcross :
      (crossBlockOriginalEdges G P).card ≤
        (sourceEdgeFinset G).card := by
    apply Finset.card_le_card
    intro e he
    exact mem_sourceEdgeFinset.mpr
      ((mem_crossBlockOriginalEdges (G := G) P e).1 he).1
  have hpotential :=
    clusteringPotential_le_eleven_tenths_mul_crossing_card
      (G := G) P schedule
  have hcrossRat :
      ((crossBlockOriginalEdges G P).card : Rat) ≤
        ((sourceEdgeFinset G).card : Rat) := by
    exact_mod_cast hcross
  norm_num at hpotential ⊢
  nlinarith

/-- Theorem 5.8's outer finite-descent argument.  The action theorem supplied
to `step` is the numbered phase proof: it must either produce the requested
output or an acceptable successor whose source potential drops by one. -/
theorem output_of_sourcePotential_descent
    (G : _root_.SimpleGraph V) (schedule : BoundedContribution)
    (Valid : VertexClustering V → Prop) (Output : Prop)
    (initial : VertexClustering V) (hinitial : Valid initial)
    (step : ∀ P, Valid P →
      Output ∨ ∃ Q, Valid Q ∧ DropsByOne G schedule P Q) :
    Output := by
  apply output_of_bounded_rat_descent
    (clusteringPotential G · schedule) Valid Output
    (fun P _ => clusteringPotential_nonnegative
      (G := G) P schedule)
    (fun P hP => by
      rcases step P hP with houtput | ⟨Q, hQ, hdrop⟩
      · exact Or.inl houtput
      · exact Or.inr ⟨Q, hQ, hdrop⟩)
    (2 * (sourceEdgeFinset G).card) initial hinitial
  exact clusteringPotential_le_two_mul_edge_card
    (G := G) initial schedule

/-! ## The finite-sum core of Claim 5.7 -/

/-- Finite-sum accounting for one bandwidth or large-cluster split.

The inherited boundary edges on the chosen side each release `gap` units of
endpoint contribution.  The new cut edges cost at most `11/10`.  All other
endpoint changes are included in the pointwise premise. -/
theorem clusteringPotential_le_of_split_edge_accounting
    (P Q : VertexClustering V) (schedule : BoundedContribution)
    (released added : Finset (Sym2 V)) (gap : Rat)
    (hreleased : released ⊆ sourceEdgeFinset G)
    (hadded : added ⊆ sourceEdgeFinset G)
    (hcharge :
      (11 : Rat) / 10 * added.card ≤ gap * released.card)
    (hpointwise : ∀ e, e ∈ G.edgeSet →
      edgePotential G Q schedule e +
          (if e ∈ released then gap else 0) ≤
        edgePotential G P schedule e +
          (if e ∈ added then (11 : Rat) / 10 else 0)) :
    clusteringPotential G Q schedule ≤
      clusteringPotential G P schedule := by
  classical
  have hsum :=
    Finset.sum_le_sum fun e (he : e ∈ sourceEdgeFinset G) =>
      hpointwise e (mem_sourceEdgeFinset.mp he)
  simp only [Finset.sum_add_distrib] at hsum
  have hreleasedSum :
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ released then gap else 0) =
        gap * released.card := by
    calc
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ released then gap else 0) =
          ∑ e ∈ released, if e ∈ released then gap else 0 := by
            symm
            apply Finset.sum_subset hreleased
            intro e _heG heNot
            simp [heNot]
      _ = gap * released.card := by
        simp [mul_comm]
  have haddedSum :
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ added then (11 : Rat) / 10 else 0) =
        (11 : Rat) / 10 * added.card := by
    calc
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ added then (11 : Rat) / 10 else 0) =
          ∑ e ∈ added,
            if e ∈ added then (11 : Rat) / 10 else 0 := by
              symm
              apply Finset.sum_subset hadded
              intro e _heG heNot
              simp [heNot]
      _ = (11 : Rat) / 10 * added.card := by
        simp
        ring
  change
    clusteringPotential G Q schedule +
        (∑ e ∈ sourceEdgeFinset G,
          if e ∈ released then gap else 0) ≤
      clusteringPotential G P schedule +
        (∑ e ∈ sourceEdgeFinset G,
          if e ∈ added then (11 : Rat) / 10 else 0) at hsum
  rw [hreleasedSum, haddedSum] at hsum
  linarith

/-- Summed form of the edge accounting in Claim 5.7.

`removed` is the old large-cluster boundary, charged by at least one per
edge. `added` is the new separating cut, charged by at most `11/10` per
edge.  The pointwise hypothesis also covers edges lying in both sets: their
new potential may exceed their old potential by at most `1/10`. -/
theorem dropsByOne_of_separate_edge_accounting
    (P Q : VertexClustering V) (schedule : BoundedContribution)
    (removed added : Finset (Sym2 V))
    (hremoved : removed ⊆ sourceEdgeFinset G)
    (hadded : added ⊆ sourceEdgeFinset G)
    (hcard :
      11 * added.card + 10 ≤ 10 * removed.card)
    (hpointwise : ∀ e, e ∈ G.edgeSet →
      edgePotential G Q schedule e +
          (if e ∈ removed then (1 : Rat) else 0) ≤
        edgePotential G P schedule e +
          (if e ∈ added then (11 : Rat) / 10 else 0)) :
    DropsByOne G schedule P Q := by
  classical
  have hsum :
      clusteringPotential G Q schedule + removed.card ≤
        clusteringPotential G P schedule +
          (11 : Rat) / 10 * added.card := by
    have h :=
      Finset.sum_le_sum fun e (he : e ∈ sourceEdgeFinset G) =>
        hpointwise e (mem_sourceEdgeFinset.mp he)
    simp only [Finset.sum_add_distrib] at h
    have hremovedSum :
        (∑ e ∈ sourceEdgeFinset G,
            if e ∈ removed then (1 : Rat) else 0) =
          removed.card := by
      calc
        (∑ e ∈ sourceEdgeFinset G,
            if e ∈ removed then (1 : Rat) else 0) =
            ∑ e ∈ removed,
              if e ∈ removed then (1 : Rat) else 0 := by
                symm
                apply Finset.sum_subset hremoved
                intro e _heG heNot
                simp [heNot]
        _ = removed.card := by simp
    have haddedSum :
        (∑ e ∈ sourceEdgeFinset G,
            if e ∈ added then (11 : Rat) / 10 else 0) =
          (11 : Rat) / 10 * added.card := by
      calc
        (∑ e ∈ sourceEdgeFinset G,
            if e ∈ added then (11 : Rat) / 10 else 0) =
            ∑ e ∈ added,
              if e ∈ added then (11 : Rat) / 10 else 0 := by
                symm
                apply Finset.sum_subset hadded
                intro e _heG heNot
                simp [heNot]
        _ = (11 : Rat) / 10 * added.card := by
          simp
          ring
    simpa [clusteringPotential, hremovedSum, haddedSum] using h
  have hcardRat :
      (11 : Rat) / 10 * added.card + 1 ≤
        (removed.card : Rat) := by
    have hcard' :
        ((11 * added.card + 10 : Nat) : Rat) ≤
          (10 * removed.card : Nat) := by
      exact_mod_cast hcard
    norm_num at hcard' ⊢
    linarith
  unfold DropsByOne
  linarith

/-- Finite-sum accounting for Claim 5.10.  Every edge in `removed` releases
one full unit, while an edge in `added` may gain at most `addedCost`.
Keeping the cost symbolic lets the source estimate
`rho(z) ≤ 1 / (28 * ell0)` be used without weakening it to Observation
5.4's global `1/20` bound. -/
theorem dropsByOne_of_removed_added_accounting
    (P Q : VertexClustering V) (schedule : BoundedContribution)
    (removed added : Finset (Sym2 V)) (addedCost : Rat)
    (hremoved : removed ⊆ sourceEdgeFinset G)
    (hadded : added ⊆ sourceEdgeFinset G)
    (hcard :
      addedCost * added.card + 1 ≤ (removed.card : Rat))
    (hpointwise : ∀ e, e ∈ G.edgeSet →
      edgePotential G Q schedule e +
          (if e ∈ removed then (1 : Rat) else 0) ≤
        edgePotential G P schedule e +
          (if e ∈ added then addedCost else 0)) :
    DropsByOne G schedule P Q := by
  classical
  have hsum :=
    Finset.sum_le_sum fun e (he : e ∈ sourceEdgeFinset G) =>
      hpointwise e (mem_sourceEdgeFinset.mp he)
  simp only [Finset.sum_add_distrib] at hsum
  have hremovedSum :
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ removed then (1 : Rat) else 0) =
        removed.card := by
    calc
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ removed then (1 : Rat) else 0) =
          ∑ e ∈ removed,
            if e ∈ removed then (1 : Rat) else 0 := by
              symm
              apply Finset.sum_subset hremoved
              intro e _heG heNot
              simp [heNot]
      _ = removed.card := by simp
  have haddedSum :
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ added then addedCost else 0) =
        addedCost * added.card := by
    calc
      (∑ e ∈ sourceEdgeFinset G,
          if e ∈ added then addedCost else 0) =
          ∑ e ∈ added,
            if e ∈ added then addedCost else 0 := by
              symm
              apply Finset.sum_subset hadded
              intro e _heG heNot
              simp [heNot]
      _ = addedCost * added.card := by
        simp
        ring
  change
    clusteringPotential G Q schedule +
        (∑ e ∈ sourceEdgeFinset G,
          if e ∈ removed then (1 : Rat) else 0) ≤
      clusteringPotential G P schedule +
        (∑ e ∈ sourceEdgeFinset G,
          if e ∈ added then addedCost else 0) at hsum
  rw [hremovedSum, haddedSum] at hsum
  unfold DropsByOne
  linarith

/-- The natural-number estimate in Claim 5.7:

`|out(C)| - 1.1 |out(A)| ≥ 1`

when `C` is large and the separating cut has fewer than `w0 / 2` edges.
Writing it with cleared denominators avoids all rounding ambiguity. -/
theorem separate_card_accounting
    {w0 removedCard addedCard : Nat}
    (hlarge : w0 ≤ removedCard)
    (hcut : addedCard < w0 / 2) :
    11 * addedCard + 10 ≤ 10 * removedCard := by
  omega

/-- Claim 5.7 after the construction of the preliminary component
partition.  The three structural premises are exactly the edge
classifications proved in the paper:

* an old large-boundary edge not on the new cut becomes internal;
* away from the new cut and old large boundary, potential does not increase;
* the remaining two membership cases use Observation 5.4.

The subsequent bandwidth decompositions are handled separately by Theorem
5.5 and transitivity. -/
theorem dropsByOne_of_separate_classification
    (P Q : VertexClustering V) (schedule : BoundedContribution)
    (removed added : Finset (Sym2 V))
    (hremoved : removed ⊆ sourceEdgeFinset G)
    (hadded : added ⊆ sourceEdgeFinset G)
    (hcard : 11 * added.card + 10 ≤ 10 * removed.card)
    (hremovedCrosses :
      ∀ e ∈ removed, crossesBlocks P e)
    (hremovedInternal :
      ∀ e ∈ removed, e ∉ added → ¬ crossesBlocks Q e)
    (hstable :
      ∀ e, e ∈ G.edgeSet → e ∉ removed → e ∉ added →
        edgePotential G Q schedule e ≤
          edgePotential G P schedule e) :
    DropsByOne G schedule P Q := by
  apply dropsByOne_of_separate_edge_accounting
    (G := G) P Q schedule removed added hremoved hadded hcard
  intro e heG
  by_cases heRemoved : e ∈ removed
  · by_cases heAdded : e ∈ added
    · have hQupper :=
        edgePotential_le_eleven_tenths (G := G) Q schedule e
      have hPlower :=
        one_le_edgePotential_of_crosses
          (G := G) P schedule (hremovedCrosses e heRemoved)
      simp only [if_pos heRemoved, if_pos heAdded]
      linarith
    · have hQzero : edgePotential G Q schedule e = 0 := by
        induction e using Sym2.inductionOn with
        | _ u v =>
            apply edgePotential_eq_zero_of_same_block
            simpa only [crossesBlocks_mk, not_ne_iff] using
              hremovedInternal s(u, v) heRemoved heAdded
      have hPlower :=
        one_le_edgePotential_of_crosses
          (G := G) P schedule (hremovedCrosses e heRemoved)
      simp only [if_pos heRemoved, if_neg heAdded, add_zero]
      rw [hQzero]
      linarith
  · by_cases heAdded : e ∈ added
    · have hQupper :=
        edgePotential_le_eleven_tenths (G := G) Q schedule e
      have hPnonnegative :=
        edgePotential_nonnegative (G := G) P schedule e
      simp only [if_neg heRemoved, add_zero, if_pos heAdded]
      linarith
    · simpa [heRemoved, heAdded] using
        hstable e heG heRemoved heAdded

end ChekuriChuzhoySection5SourcePotential
end SimpleGraph

end Lax17Proofs
