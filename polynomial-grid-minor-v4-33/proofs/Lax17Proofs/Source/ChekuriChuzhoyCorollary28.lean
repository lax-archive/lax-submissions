import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Corollary 2.8: finite grouping

This file formalizes the nonalgorithmic content of Corollary 2.8 in the
preprint (Corollary 2.11 in the JACM version), pp. 8--9 of
`chekuri-chuzhoy-2.pdf`.

The source proof first partitions the terminals among edge-disjoint connected
subtrees, with between `ceil (1 / alpha)` and three times that many terminals
in every tree.  It then chooses at most one terminal from every tree, while
retaining a linear number from each prescribed block.  Claim 2.7 in the
preprint (Claim 2.10 in the journal version) shows that the chosen union is
`1/2` edge-well-linked.

`GroupedTransversal` records exactly the finite semantic data consumed by the
last cut-counting argument.  In particular, `crossing_card_le` is the direct
consequence of connected, pairwise edge-disjoint tree supports: every support
meeting both sides of a cut contains a distinct cut edge.
-/

namespace SimpleGraph


namespace ChekuriChuzhoyCorollary28

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The groups crossed by a partition of the ambient cluster. -/
noncomputable def crossingGroups {I : Type v} [Fintype I] [DecidableEq I]
    (support : I → Finset V) (X Y : Finset V) : Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    (support i ∩ X).Nonempty ∧ (support i ∩ Y).Nonempty

@[simp] theorem mem_crossingGroups {I : Type v} [Fintype I] [DecidableEq I]
    (support : I → Finset V) (X Y : Finset V) (i : I) :
    i ∈ crossingGroups support X Y ↔
      (support i ∩ X).Nonempty ∧ (support i ∩ Y).Nonempty := by
  classical
  simp [crossingGroups]

/-- The finite data used by the grouping boost.

The type `I` indexes only groups from which a representative was selected;
unused groups may be discarded, as in the application of Observation 2.9 to
Claim 2.7.  `group i` is the terminal subset assigned to the support, and
`representative i` is its selected terminal. -/
structure GroupedTransversal (I : Type v) [Fintype I] [DecidableEq I]
    (G : _root_.SimpleGraph V) (C T : Finset V) (q : ℕ) where
  support : I → Finset V
  group : I → Finset V
  representative : I → V
  support_subset : ∀ i, support i ⊆ C
  group_subset : ∀ i, group i ⊆ support i ∩ T
  q_le_group_card : ∀ i, q ≤ (group i).card
  groups_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ group
  representative_mem : ∀ i, representative i ∈ group i
  representative_injective : Function.Injective representative
  crossing_card_le :
    ∀ X Y : Finset V, X ⊆ C → Y ⊆ C → X ∪ Y = C → Disjoint X Y →
      (crossingGroups support X Y).card ≤
        (Section44.edgeBoundary G X Y).card

/-- Source-faithful grouping data with connected, edge-disjoint supports.

The internal edge set of support `i` is represented by
`edgeBoundary G (support i) (support i)`.  The source constructs these supports
as edge-disjoint subtrees of a spanning tree. -/
structure TreeGroupedTransversal (I : Type v) [Fintype I] [DecidableEq I]
    (G : _root_.SimpleGraph V) (C T : Finset V) (q : ℕ) where
  support : I → Finset V
  group : I → Finset V
  representative : I → V
  support_subset : ∀ i, support i ⊆ C
  support_connected :
    ∀ i, (G.induce {v : V | v ∈ support i}).Connected
  group_subset : ∀ i, group i ⊆ support i ∩ T
  q_le_group_card : ∀ i, q ≤ (group i).card
  groups_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ group
  representative_mem : ∀ i, representative i ∈ group i
  representative_injective : Function.Injective representative
  internalEdges_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ
      (fun i => Section44.edgeBoundary G (support i) (support i))

namespace TreeGroupedTransversal

variable {I : Type v} [Fintype I] [DecidableEq I]
variable {C T : Finset V} {q : ℕ}

/-- Connected, pairwise edge-disjoint supports crossing a cut inject into its
edge boundary. -/
theorem crossing_card_le
    (D : TreeGroupedTransversal I G C T q)
    (X Y : Finset V) (hXC : X ⊆ C) (hYC : Y ⊆ C)
    (hcover : X ∪ Y = C) (hdisj : Disjoint X Y) :
    (crossingGroups D.support X Y).card ≤
      (Section44.edgeBoundary G X Y).card := by
  classical
  let K := crossingGroups D.support X Y
  let B := Section44.edgeBoundary G X Y
  have hedge : ∀ i : {i // i ∈ K},
      ∃ e ∈ B,
        e ∈ Section44.edgeBoundary G (D.support i) (D.support i) := by
    intro i
    have hi := i.property
    rcases (mem_crossingGroups D.support X Y i).mp hi with
      ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxSupport := (Finset.mem_inter.mp hx).1
    have hxX := (Finset.mem_inter.mp hx).2
    have hySupport := (Finset.mem_inter.mp hy).1
    have hyY := (Finset.mem_inter.mp hy).2
    let P : GraphPath G :=
      GraphPath.ofConnectedInduce (D.support i) (D.support_connected i)
        x y hxSupport hySupport
    have hPsubSupport : P.vertexSet ⊆ D.support i := by
      simpa [P] using GraphPath.ofConnectedInduce_vertexSet_subset
        (G := G) (D.support i) (D.support_connected i)
          x y hxSupport hySupport
    have hPsub : P.vertexSet ⊆ X ∪ Y := by
      intro z hz
      rw [hcover]
      exact D.support_subset i (hPsubSupport hz)
    have hsource : P.source ∈ X := by simpa [P] using hxX
    have hnot : ¬ P.vertexSet ⊆ X := by
      intro hPX
      have htarget : P.target = y := rfl
      have hyP : y ∈ P.vertexSet := by
        rw [← htarget]
        exact GraphPath.target_mem_vertexSet P
      exact Finset.disjoint_left.mp hdisj (hPX hyP) hyY
    rcases
        Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
          (P := P) hPsub hsource hnot with
      ⟨e, heP, heB⟩
    refine ⟨e, heB, ?_⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      have heWalk : s(a, b) ∈ P.walk.edges := by
        exact List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using heP)
      have haSupport : a ∈ D.support i := hPsubSupport <| by
        simpa [GraphPath.vertexSet] using
          P.walk.fst_mem_support_of_mem_edges heWalk
      have hbSupport : b ∈ D.support i := hPsubSupport <| by
        simpa [GraphPath.vertexSet] using
          P.walk.snd_mem_support_of_mem_edges heWalk
      exact (Section44.mem_edgeBoundary
        (G := G) (D.support i) (D.support i) s(a, b)).mpr
          ⟨GraphPath.edgeSet_subset_edgeSet P heP,
            a, haSupport, b, hbSupport, rfl⟩
  choose edge hedgeB hedgeInternal using hedge
  let f : {i // i ∈ K} → {e // e ∈ B} :=
    fun i => ⟨edge i, hedgeB i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hdisjEdges := D.internalEdges_pairwiseDisjoint
      (by simp) (by simp) hne
    have hedgeEq : edge i = edge j := congrArg Subtype.val hij
    have hiInternal :
        edge i ∈ (fun k : I =>
          Section44.edgeBoundary G (D.support k) (D.support k)) i :=
      hedgeInternal i
    have hjInternal :
        edge j ∈ (fun k : I =>
          Section44.edgeBoundary G (D.support k) (D.support k)) j :=
      hedgeInternal j
    exact Finset.disjoint_left.mp hdisjEdges
      hiInternal
      (by simpa [← hedgeEq] using hjInternal)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hcard
  simpa [K, B] using hcard

/-- Forget the explicit support connectivity after deriving the cut-congestion
bound used by Claim 2.7. -/
noncomputable def toGroupedTransversal
    (D : TreeGroupedTransversal I G C T q) :
    GroupedTransversal I G C T q where
  support := D.support
  group := D.group
  representative := D.representative
  support_subset := D.support_subset
  group_subset := D.group_subset
  q_le_group_card := D.q_le_group_card
  groups_pairwiseDisjoint := D.groups_pairwiseDisjoint
  representative_mem := D.representative_mem
  representative_injective := D.representative_injective
  crossing_card_le := D.crossing_card_le

end TreeGroupedTransversal

namespace GroupedTransversal

variable {I : Type v} [Fintype I] [DecidableEq I]
variable {C T : Finset V} {q alphaNum alphaDen : ℕ}

/-- The terminal set selected by the transversal. -/
noncomputable def selected
    (D : GroupedTransversal I G C T q) : Finset V := by
  classical
  exact Finset.univ.image D.representative

theorem representative_mem_selected
    (D : GroupedTransversal I G C T q) (i : I) :
    D.representative i ∈ D.selected := by
  classical
  simp [selected]

theorem selected_subset_terminals
    (D : GroupedTransversal I G C T q) : D.selected ⊆ T := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  exact (Finset.mem_inter.mp (D.group_subset i (D.representative_mem i))).2

theorem selected_subset_cluster
    (D : GroupedTransversal I G C T q) : D.selected ⊆ C := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  exact D.support_subset i <|
    (Finset.mem_inter.mp (D.group_subset i (D.representative_mem i))).1

theorem selected_card (D : GroupedTransversal I G C T q) :
    D.selected.card = Fintype.card I := by
  classical
  rw [selected, Finset.card_image_of_injective _ D.representative_injective,
    Finset.card_univ]

/-- Representatives on one side of a cut, expressed as group indices. -/
noncomputable def sideIndices
    (D : GroupedTransversal I G C T q) (X : Finset V) : Finset I := by
  classical
  exact Finset.univ.filter fun i => D.representative i ∈ X

@[simp] theorem mem_sideIndices
    (D : GroupedTransversal I G C T q) (X : Finset V) (i : I) :
    i ∈ D.sideIndices X ↔ D.representative i ∈ X := by
  classical
  simp [sideIndices]

theorem card_sideIndices_eq_inter_selected
    (D : GroupedTransversal I G C T q) (X : Finset V) :
    (D.sideIndices X).card = (X ∩ D.selected).card := by
  classical
  have heq : (D.sideIndices X).image D.representative = X ∩ D.selected := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact Finset.mem_inter.mpr
        ⟨(D.mem_sideIndices X i).mp hi, D.representative_mem_selected i⟩
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxX, hxSelected⟩
      rcases Finset.mem_image.mp hxSelected with ⟨i, _hi, hirep⟩
      exact Finset.mem_image.mpr
        ⟨i, (D.mem_sideIndices X i).mpr (by simpa [hirep] using hxX), hirep⟩
  rw [← heq, Finset.card_image_of_injective _ D.representative_injective]

/-- Disjoint groups of size at least `q` contribute at least `q` terminals per
index to their union. -/
theorem mul_card_le_card_biUnion_group
    (D : GroupedTransversal I G C T q) (J : Finset I) :
    q * J.card ≤ (J.biUnion D.group).card := by
  classical
  have hp : (J : Set I).PairwiseDisjoint D.group := by
    intro i hi j hj hij
    exact D.groups_pairwiseDisjoint (by simp) (by simp) hij
  rw [Finset.card_biUnion hp]
  calc
    q * J.card = ∑ _i ∈ J, q := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ J, (D.group i).card := by
      exact Finset.sum_le_sum fun i _hi => D.q_le_group_card i

/-- A noncrossing group whose representative is on one side is wholly on that
side. -/
theorem group_subset_side_of_not_crossing
    (D : GroupedTransversal I G C T q)
    {X Y : Finset V} (hcover : X ∪ Y = C) (hdisj : Disjoint X Y)
    {i : I} (hiX : i ∈ D.sideIndices X)
    (hinoncross : i ∉ crossingGroups D.support X Y) :
    D.group i ⊆ X ∩ T := by
  classical
  intro x hx
  have hxSupport : x ∈ D.support i :=
    (Finset.mem_inter.mp (D.group_subset i hx)).1
  have hxT : x ∈ T := (Finset.mem_inter.mp (D.group_subset i hx)).2
  have hxC : x ∈ C := D.support_subset i hxSupport
  have hxXY : x ∈ X ∪ Y := by simpa [hcover] using hxC
  have hrepSupport : D.representative i ∈ D.support i :=
    (Finset.mem_inter.mp (D.group_subset i (D.representative_mem i))).1
  have hrepX : D.representative i ∈ X := (D.mem_sideIndices X i).mp hiX
  rcases Finset.mem_union.mp hxXY with hxX | hxY
  · exact Finset.mem_inter.mpr ⟨hxX, hxT⟩
  · exfalso
    apply hinoncross
    exact (mem_crossingGroups D.support X Y i).mpr
      ⟨⟨D.representative i, Finset.mem_inter.mpr ⟨hrepSupport, hrepX⟩⟩,
        ⟨x, Finset.mem_inter.mpr ⟨hxSupport, hxY⟩⟩⟩

/-- After removing crossing groups, every surviving group contributes its full
`q` terminals to the corresponding side of the original terminal set. -/
theorem q_mul_nonCrossing_side_card_le
    (D : GroupedTransversal I G C T q)
    {X Y : Finset V} (hcover : X ∪ Y = C) (hdisj : Disjoint X Y) :
    q * (D.sideIndices X \ crossingGroups D.support X Y).card ≤
      (X ∩ T).card := by
  classical
  let J := D.sideIndices X \ crossingGroups D.support X Y
  have hUnion : J.biUnion D.group ⊆ X ∩ T := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hiJ, hxi⟩
    exact D.group_subset_side_of_not_crossing hcover hdisj
      (Finset.mem_sdiff.mp hiJ).1 (Finset.mem_sdiff.mp hiJ).2 hxi
  exact (D.mul_card_le_card_biUnion_group J).trans
    (Finset.card_le_card hUnion)

/-- Claim 2.7 (journal Claim 2.10), in ratio-cleared finite form: selecting one
terminal from every group boosts the selected set to `1/2` cut
well-linkedness. -/
theorem selected_scaledEdgeWellLinkedIn_one_two
    (D : GroupedTransversal I G C T q)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hq : alphaDen ≤ alphaNum * q) :
    Section46.ScaledEdgeWellLinkedIn G C D.selected 1 2 := by
  classical
  refine ⟨by simp, by simp, D.selected_subset_cluster, ?_⟩
  intro X Y hXC hYC hcover hdisj
  let K := crossingGroups D.support X Y
  let d := (Section44.edgeBoundary G X Y).card
  have hKle : K.card ≤ d := D.crossing_card_le X Y hXC hYC hcover hdisj
  have hleft := D.q_mul_nonCrossing_side_card_le hcover hdisj
  have hright := D.q_mul_nonCrossing_side_card_le (X := Y) (Y := X)
    (by simpa [Finset.union_comm] using hcover)
    hdisj.symm
  have hKcomm : crossingGroups D.support Y X = K := by
    ext i
    simp [K, and_comm]
  rw [hKcomm] at hright
  change q * (D.sideIndices X \ K).card ≤ (X ∩ T).card at hleft
  change q * (D.sideIndices Y \ K).card ≤ (Y ∩ T).card at hright
  have hleftCard : (D.sideIndices X).card = (X ∩ D.selected).card :=
    D.card_sideIndices_eq_inter_selected X
  have hrightCard : (D.sideIndices Y).card = (Y ∩ D.selected).card :=
    D.card_sideIndices_eq_inter_selected Y
  have hleftDiff :
      (D.sideIndices X).card ≤
        (D.sideIndices X \ K).card + K.card := by
    calc
      (D.sideIndices X).card =
          (D.sideIndices X \ K).card + (D.sideIndices X ∩ K).card := by
            rw [Finset.card_sdiff_add_card_inter]
      _ ≤ (D.sideIndices X \ K).card + K.card := by
        exact Nat.add_le_add_left
          (Finset.card_le_card Finset.inter_subset_right) _
  have hrightDiff :
      (D.sideIndices Y).card ≤
        (D.sideIndices Y \ K).card + K.card := by
    calc
      (D.sideIndices Y).card =
          (D.sideIndices Y \ K).card + (D.sideIndices Y ∩ K).card := by
            rw [Finset.card_sdiff_add_card_inter]
      _ ≤ (D.sideIndices Y \ K).card + K.card := by
        exact Nat.add_le_add_left
          (Finset.card_le_card Finset.inter_subset_right) _
  have hcut := hwell.2.2.2 X Y hXC hYC hcover hdisj
  change alphaNum * min (X ∩ T).card (Y ∩ T).card ≤ alphaDen * d at hcut
  simp only [one_mul]
  change min (X ∩ D.selected).card (Y ∩ D.selected).card ≤ 2 * d
  by_contra hnot
  have hstrict : 2 * d < min (X ∩ D.selected).card (Y ∩ D.selected).card := by
    omega
  have hleftStrict : d < (D.sideIndices X).card := by
    rw [hleftCard]
    have := hstrict.trans_le (Nat.min_le_left _ _)
    omega
  have hrightStrict : d < (D.sideIndices Y).card := by
    rw [hrightCard]
    have := hstrict.trans_le (Nat.min_le_right _ _)
    omega
  have hleftMass : q * (d + 1) ≤ (X ∩ T).card := by
    have : d < (D.sideIndices X \ K).card := by omega
    exact (Nat.mul_le_mul_left q (by omega)).trans hleft
  have hrightMass : q * (d + 1) ≤ (Y ∩ T).card := by
    have : d < (D.sideIndices Y \ K).card := by omega
    exact (Nat.mul_le_mul_left q (by omega)).trans hright
  have hminMass : q * (d + 1) ≤ min (X ∩ T).card (Y ∩ T).card := by
    omega
  have hscaledLower : alphaDen * (d + 1) ≤
      alphaNum * min (X ∩ T).card (Y ∩ T).card := by
    calc
      alphaDen * (d + 1) ≤ (alphaNum * q) * (d + 1) :=
        Nat.mul_le_mul_right (d + 1) hq
      _ = alphaNum * (q * (d + 1)) := by ring
      _ ≤ alphaNum * min (X ∩ T).card (Y ∩ T).card :=
        Nat.mul_le_mul_left alphaNum hminMass
  have : alphaDen * (d + 1) ≤ alphaDen * d := hscaledLower.trans hcut
  have halphaDenPos : 0 < alphaDen := hwell.1.trans_le hwell.2.1
  have hstrictMul : alphaDen * d < alphaDen * (d + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self d) halphaDenPos
  exact (Nat.not_lt_of_ge this) hstrictMul

end GroupedTransversal

/-! ## Colored transversal via Hall's theorem -/

/-- One demand vertex for each terminal that must be retained from a block. -/
abbrev BlockDemand {J : Type v} (block : J → Finset V) (m : ℕ) :=
  (j : J) × Fin ((block j).card / m)

/-- Groups eligible to serve one demand of a prescribed block. -/
noncomputable def eligibleGroups
    {K J : Type v} [Fintype K] [DecidableEq K]
    (group : K → Finset V) (block : J → Finset V) (m : ℕ)
    (d : BlockDemand block m) : Finset K := by
  classical
  exact Finset.univ.filter fun k => (group k ∩ block d.1).Nonempty

@[simp] theorem mem_eligibleGroups
    {K J : Type v} [Fintype K] [DecidableEq K]
    (group : K → Finset V) (block : J → Finset V) (m : ℕ)
    (d : BlockDemand block m) (k : K) :
    k ∈ eligibleGroups group block m d ↔
      (group k ∩ block d.1).Nonempty := by
  classical
  simp [eligibleGroups]

/-- Observation 2.9's integral colored selection, stated through the exact
Hall inequalities for the demand-to-group incidence relation.

The conclusion includes both the injective assignment of demands to groups
and injective terminal representatives.  The final inequality is the source's
per-block floor bound. -/
theorem exists_injective_colored_representatives_of_hall
    {K J : Type v} [Fintype K] [DecidableEq K]
    [Fintype J] [DecidableEq J]
    (group : K → Finset V) (block : J → Finset V) (m : ℕ)
    (hgroups : Set.PairwiseDisjoint Set.univ group)
    (hhall : ∀ s : Finset (BlockDemand block m),
      s.card ≤ (s.biUnion (eligibleGroups group block m)).card) :
    ∃ assign : BlockDemand block m → K,
      ∃ representative : BlockDemand block m → V,
        Function.Injective assign ∧
        Function.Injective representative ∧
        (∀ d, representative d ∈ group (assign d) ∩ block d.1) ∧
        ∀ j, (block j).card / m ≤
          (block j ∩ Finset.univ.image representative).card := by
  classical
  rcases
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (eligibleGroups group block m)).mp hhall with
    ⟨assign, hassignInj, hassignMem⟩
  have helig : ∀ d, (group (assign d) ∩ block d.1).Nonempty := by
    intro d
    exact (mem_eligibleGroups group block m d (assign d)).mp (hassignMem d)
  let representative : BlockDemand block m → V :=
    fun d => (helig d).choose
  have hrepresentativeMem :
      ∀ d, representative d ∈ group (assign d) ∩ block d.1 := by
    intro d
    exact (helig d).choose_spec
  have hrepresentativeInj : Function.Injective representative := by
    intro a b hab
    by_contra habne
    have hassignNe : assign a ≠ assign b := by
      intro heq
      exact habne (hassignInj heq)
    have hdisj := hgroups (by simp) (by simp) hassignNe
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_inter.mp (hrepresentativeMem a)).1
      (by simpa [hab] using
        (Finset.mem_inter.mp (hrepresentativeMem b)).1)
  refine ⟨assign, representative, hassignInj, hrepresentativeInj,
    hrepresentativeMem, ?_⟩
  intro j
  let f : Fin ((block j).card / m) →
      {x // x ∈ block j ∩ Finset.univ.image representative} :=
    fun r => ⟨representative ⟨j, r⟩, by
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp (hrepresentativeMem ⟨j, r⟩)).2,
          Finset.mem_image.mpr ⟨⟨j, r⟩, by simp, rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hdemand : (⟨j, a⟩ : BlockDemand block m) = ⟨j, b⟩ :=
      hrepresentativeInj (congrArg Subtype.val hab)
    cases hdemand
    rfl
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

/-! ## Paper-facing block conclusion -/

/-- The nonalgorithmic conclusion of preprint Corollary 2.8 for a finite
family of terminal blocks.  The source allows an arbitrary finite partition;
the strongification application uses at most three blocks.

The natural division is the source's floor.  When
`q = alphaDen ⌈/⌉ alphaNum`, this is
`floor (|block j| / (3 * ceil (1 / alpha)))`. -/
structure BlockGroupingConclusion {J : Type v} [Fintype J]
    (G : _root_.SimpleGraph V) (C : Finset V)
    (block : J → Finset V) (q : ℕ) where
  selectedBlock : J → Finset V
  selectedBlock_subset : ∀ j, selectedBlock j ⊆ block j
  selectedBlock_card :
    ∀ j, (block j).card / (3 * q) ≤ (selectedBlock j).card
  union_scaledEdgeWellLinked :
    Section46.ScaledEdgeWellLinkedIn G C
      (Finset.univ.biUnion selectedBlock) 1 2

/-- A tree grouping whose representatives meet the required quota in every
block produces the exact finite conclusion of Corollary 2.8.

The remaining colored-transversal construction in Observation 2.9 is exactly
the `hquota` premise.  Keeping it as a cardinal premise makes the mathematical
gap explicit rather than hiding it in a provider structure. -/
theorem blockGroupingConclusion_of_treeGroupedTransversal
    {I : Type v} [Fintype I] [DecidableEq I]
    {J : Type v} [Fintype J] [DecidableEq J]
    {C T : Finset V} {alphaNum alphaDen q : ℕ}
    (block : J → Finset V)
    (D : TreeGroupedTransversal I G C T q)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hq : alphaDen ≤ alphaNum * q)
    (hblockCover : Finset.univ.biUnion block = T)
    (hquota : ∀ j,
      (block j).card / (3 * q) ≤ (block j ∩ D.toGroupedTransversal.selected).card) :
    Nonempty (BlockGroupingConclusion G C block q) := by
  classical
  let selectedBlock : J → Finset V :=
    fun j => block j ∩ D.toGroupedTransversal.selected
  have hUnion : Finset.univ.biUnion selectedBlock =
      D.toGroupedTransversal.selected := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, _hj, hxj⟩
      exact (Finset.mem_inter.mp hxj).2
    · intro hx
      have hxT : x ∈ T := D.toGroupedTransversal.selected_subset_terminals hx
      have hxBlocks : x ∈ Finset.univ.biUnion block := by
        simpa [hblockCover] using hxT
      rcases Finset.mem_biUnion.mp hxBlocks with ⟨j, hj, hxj⟩
      exact Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_inter.mpr ⟨hxj, hx⟩⟩
  refine ⟨{
    selectedBlock := selectedBlock
    selectedBlock_subset := fun j => Finset.inter_subset_left
    selectedBlock_card := ?_
    union_scaledEdgeWellLinked := ?_ }⟩
  · intro j
    exact hquota j
  · rw [hUnion]
    exact D.toGroupedTransversal.selected_scaledEdgeWellLinkedIn_one_two
      hwell hq

/-- Corollary 2.8 with the source's ceiling denominator written using
mathlib's natural `ceilDiv`. -/
theorem blockGroupingConclusion_of_treeGroupedTransversal_ceilDiv
    {I : Type v} [Fintype I] [DecidableEq I]
    {J : Type v} [Fintype J] [DecidableEq J]
    {C T : Finset V} {alphaNum alphaDen : ℕ}
    (block : J → Finset V)
    (D : TreeGroupedTransversal I G C T (alphaDen ⌈/⌉ alphaNum))
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hblockCover : Finset.univ.biUnion block = T)
    (hquota : ∀ j,
      (block j).card / (3 * (alphaDen ⌈/⌉ alphaNum)) ≤
        (block j ∩ D.toGroupedTransversal.selected).card) :
    Nonempty
      (BlockGroupingConclusion G C block (alphaDen ⌈/⌉ alphaNum)) := by
  refine blockGroupingConclusion_of_treeGroupedTransversal
    block D hwell ?_ hblockCover hquota
  exact (ceilDiv_le_iff_le_mul hwell.1).mp le_rfl

end ChekuriChuzhoyCorollary28

end SimpleGraph

end Lax17Proofs
