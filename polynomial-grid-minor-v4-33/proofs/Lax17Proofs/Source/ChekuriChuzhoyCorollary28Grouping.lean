import Lax17Proofs.Source.ChekuriChuzhoyCorollary28
import Lax17Proofs.Source.ChekuriChuzhoyRootedTreePruning
import Mathlib.Data.Fin.Basic

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Observations 2.12--2.13: grouping producers

This file formalizes the producer side of Observations 2.12--2.13 in the
journal version of Chekuri--Chuzhoy, pp. 9--10 of
`chekuri-chuzhoy-2.pdf`.

`TreeGrouping` is the exact finite output of Observation 2.12: the terminal
groups partition the terminals, every group has between `q` and `3 * q`
members, and the connected supports have pairwise disjoint internal edge
sets.  The theorems below prove Observation 2.13 unconditionally from this
output, using Hall's theorem, and assemble the `TreeGroupedTransversal`
consumed by `ChekuriChuzhoyCorollary28.lean`.
-/

namespace SimpleGraph


namespace ChekuriChuzhoyCorollary28

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The finite output of journal Observation 2.12.

Supports may share articulation vertices, as they do in the source pruning
algorithm, but no graph edge is internal to two distinct supports. -/
structure TreeGrouping (K : Type v) [Fintype K] [DecidableEq K]
    (G : _root_.SimpleGraph V) (C T : Finset V) (q : ℕ) where
  support : K → Finset V
  group : K → Finset V
  support_subset : ∀ k, support k ⊆ C
  support_connected :
    ∀ k, (G.induce {v : V | v ∈ support k}).Connected
  group_subset : ∀ k, group k ⊆ support k ∩ T
  q_le_group_card : ∀ k, q ≤ (group k).card
  group_card_le : ∀ k, (group k).card ≤ 3 * q
  groups_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ group
  groups_cover : Finset.univ.biUnion group = T
  internalEdges_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ
      (fun k => Section44.edgeBoundary G (support k) (support k))

namespace TreeGrouping

variable {K : Type v} [Fintype K] [DecidableEq K]
variable {C T : Finset V} {q : ℕ}

/-- Every terminal belongs to its unique group in an Observation 2.12
grouping. -/
theorem exists_unique_group (D : TreeGrouping K G C T q) {x : V}
    (hx : x ∈ T) : ∃! k, x ∈ D.group k := by
  classical
  have hxUnion : x ∈ Finset.univ.biUnion D.group := by
    simpa [D.groups_cover] using hx
  rcases Finset.mem_biUnion.mp hxUnion with ⟨k, _hk, hxk⟩
  refine ⟨k, hxk, ?_⟩
  intro l hxl
  by_contra hkl
  exact Finset.disjoint_left.mp
    (D.groups_pairwiseDisjoint (by simp) (by simp) hkl) hxl hxk

/-- The groups meeting a set of blocks are exactly the neighborhood used in
the Hall argument. -/
noncomputable def groupsMeetingBlocks
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (A : Finset J) : Finset K := by
  classical
  exact Finset.univ.filter fun k =>
    (D.group k ∩ A.biUnion block).Nonempty

@[simp] theorem mem_groupsMeetingBlocks
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (A : Finset J) (k : K) :
    k ∈ D.groupsMeetingBlocks block A ↔
      (D.group k ∩ A.biUnion block).Nonempty := by
  classical
  simp [groupsMeetingBlocks]

/-- A union of terminal blocks is contained in the union of all groups which
meet those blocks. -/
theorem biUnion_block_subset_biUnion_groupsMeetingBlocks
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (hblock : ∀ j, block j ⊆ T) (A : Finset J) :
    A.biUnion block ⊆ (D.groupsMeetingBlocks block A).biUnion D.group := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨j, hjA, hxj⟩
  rcases D.exists_unique_group (hblock j hxj) with ⟨k, hxk, _hunique⟩
  refine Finset.mem_biUnion.mpr ⟨k, ?_, hxk⟩
  exact (D.mem_groupsMeetingBlocks block A k).mpr
    ⟨x, Finset.mem_inter.mpr
      ⟨hxk, Finset.mem_biUnion.mpr ⟨j, hjA, hxj⟩⟩⟩

/-- Cardinal upper bound for a union of Observation 2.12 groups. -/
theorem card_biUnion_group_le
    (D : TreeGrouping K G C T q) (S : Finset K) :
    (S.biUnion D.group).card ≤ (3 * q) * S.card := by
  classical
  calc
    (S.biUnion D.group).card = ∑ k ∈ S, (D.group k).card := by
      apply Finset.card_biUnion
      intro i _hi j _hj hij
      exact D.groups_pairwiseDisjoint (by simp) (by simp) hij
    _ ≤ ∑ _k ∈ S, 3 * q := by
      exact Finset.sum_le_sum fun k _hk => D.group_card_le k
    _ = (3 * q) * S.card := by simp [Nat.mul_comm]

/-- The block indices represented in a set of dependent demand vertices. -/
noncomputable def activeBlocks
    {J : Type v} [Fintype J] [DecidableEq J]
    (block : J → Finset V) (m : ℕ)
    (s : Finset (BlockDemand block m)) : Finset J := by
  classical
  exact s.image Sigma.fst

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_activeBlocks
    {J : Type v} [Fintype J] [DecidableEq J]
    (block : J → Finset V) (m : ℕ)
    (s : Finset (BlockDemand block m)) (j : J) :
    j ∈ activeBlocks block m s ↔ ∃ d ∈ s, d.1 = j := by
  classical
  simp [activeBlocks]

/-- A demand's eligible groups are contained in the groups meeting all active
blocks. -/
theorem eligibleGroups_subset_groupsMeetingBlocks
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (m : ℕ) (s : Finset (BlockDemand block m)) (d : BlockDemand block m)
    (hd : d ∈ s) :
    eligibleGroups D.group block m d ⊆
      D.groupsMeetingBlocks block (activeBlocks block m s) := by
  classical
  intro k hk
  rcases (mem_eligibleGroups D.group block m d k).mp hk with ⟨x, hx⟩
  refine (D.mem_groupsMeetingBlocks block (activeBlocks block m s) k).mpr ?_
  refine ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, ?_⟩⟩
  exact Finset.mem_biUnion.mpr
    ⟨d.1, (mem_activeBlocks block m s d.1).mpr ⟨d, hd, rfl⟩,
      (Finset.mem_inter.mp hx).2⟩

/-- Conversely, every group meeting an active block is eligible for every
demand in the chosen set belonging to that block. -/
theorem groupsMeetingBlocks_subset_biUnion_eligibleGroups
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (m : ℕ) (s : Finset (BlockDemand block m)) :
    D.groupsMeetingBlocks block (activeBlocks block m s) ⊆
      s.biUnion (eligibleGroups D.group block m) := by
  classical
  intro k hk
  rcases (D.mem_groupsMeetingBlocks block (activeBlocks block m s) k).mp hk with
    ⟨x, hx⟩
  have hxGroup := (Finset.mem_inter.mp hx).1
  have hxBlocks := (Finset.mem_inter.mp hx).2
  rcases Finset.mem_biUnion.mp hxBlocks with ⟨j, hjActive, hxj⟩
  rcases (mem_activeBlocks block m s j).mp hjActive with ⟨d, hd, hdj⟩
  refine Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩
  apply (mem_eligibleGroups D.group block m d k).mpr
  exact ⟨x, Finset.mem_inter.mpr
    ⟨hxGroup, by simpa [hdj] using hxj⟩⟩

/-- Observation 2.13's Hall inequalities follow from disjoint terminal blocks
and the upper bound `3 * q` on every group. -/
theorem hall_eligibleGroups
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (hblockDisjoint : Set.PairwiseDisjoint Set.univ block)
    (hblockCover : Finset.univ.biUnion block = T) (hq : 0 < q) :
    ∀ s : Finset (BlockDemand block (3 * q)),
      s.card ≤
        (s.biUnion (eligibleGroups D.group block (3 * q))).card := by
  classical
  intro s
  let A := activeBlocks block (3 * q) s
  let N := D.groupsMeetingBlocks block A
  have hm : 0 < 3 * q := Nat.mul_pos (by omega) hq
  have hblockSubset : ∀ j, block j ⊆ T := by
    intro j x hx
    rw [← hblockCover]
    exact Finset.mem_biUnion.mpr ⟨j, by simp, hx⟩
  have hsFiber :
      s.card = ∑ j ∈ A, (s.filter fun d => d.1 = j).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro d hd
    exact (mem_activeBlocks block (3 * q) s d.1).mpr ⟨d, hd, rfl⟩
  have hfiber : ∀ j,
      (s.filter fun d => d.1 = j).card ≤ (block j).card / (3 * q) := by
    intro j
    let f : {d // d ∈ s.filter fun d => d.1 = j} →
        Fin ((block j).card / (3 * q)) := fun d => by
      have hdj : d.1.1 = j := (Finset.mem_filter.mp d.2).2
      exact ⟨d.1.2.val, by simpa [hdj] using d.1.2.isLt⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have hfirst : a.1.1 = b.1.1 :=
        (Finset.mem_filter.mp a.2).2.trans
          (Finset.mem_filter.mp b.2).2.symm
      have hval := congrArg (fun z : Fin ((block j).card / (3 * q)) => z.val) hab
      simp only [f] at hval
      have hbound :
          (block a.1.1).card / (3 * q) =
            (block b.1.1).card / (3 * q) := by rw [hfirst]
      exact Sigma.ext hfirst <| (Fin.heq_ext_iff hbound).mpr hval
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  have hdemands : (3 * q) * s.card ≤ (A.biUnion block).card := by
    rw [hsFiber, Finset.mul_sum]
    calc
      ∑ j ∈ A, (3 * q) * (s.filter fun d => d.1 = j).card ≤
          ∑ j ∈ A, (block j).card := by
        apply Finset.sum_le_sum
        intro j _hj
        calc
          (3 * q) * (s.filter fun d => d.1 = j).card ≤
              (3 * q) * ((block j).card / (3 * q)) :=
            Nat.mul_le_mul_left _ (hfiber j)
          _ ≤ (block j).card := Nat.mul_div_le _ _
      _ = (A.biUnion block).card := by
        symm
        apply Finset.card_biUnion
        intro i _hi j _hj hij
        exact hblockDisjoint (by simp) (by simp) hij
  have hblocksToGroups : A.biUnion block ⊆ N.biUnion D.group := by
    exact D.biUnion_block_subset_biUnion_groupsMeetingBlocks
      block hblockSubset A
  have hmul : (3 * q) * s.card ≤ (3 * q) * N.card :=
    hdemands.trans <| (Finset.card_le_card hblocksToGroups).trans
      (D.card_biUnion_group_le N)
  have hsN : s.card ≤ N.card := by
    exact Nat.le_of_mul_le_mul_left hmul hm
  have hNsubset : N ⊆
      s.biUnion (eligibleGroups D.group block (3 * q)) := by
    exact D.groupsMeetingBlocks_subset_biUnion_eligibleGroups block (3 * q) s
  exact hsN.trans (Finset.card_le_card hNsubset)

/-- Journal Observation 2.13: choose one terminal from distinct groups while
retaining `floor (|block j| / (3*q))` terminals from every block. -/
theorem exists_colored_representatives
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (hblockDisjoint : Set.PairwiseDisjoint Set.univ block)
    (hblockCover : Finset.univ.biUnion block = T) (hq : 0 < q) :
    ∃ assign : BlockDemand block (3 * q) → K,
      ∃ representative : BlockDemand block (3 * q) → V,
        Function.Injective assign ∧
        Function.Injective representative ∧
        (∀ d, representative d ∈ D.group (assign d) ∩ block d.1) ∧
        ∀ j, (block j).card / (3 * q) ≤
          (block j ∩ Finset.univ.image representative).card := by
  exact exists_injective_colored_representatives_of_hall
    D.group block (3 * q) D.groups_pairwiseDisjoint
      (D.hall_eligibleGroups block hblockDisjoint hblockCover hq)

/-- Assemble the exact tree-grouped transversal consumed by the corollary
proof.  Only groups selected by Observation 2.13 remain in the index type. -/
theorem exists_treeGroupedTransversal
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (hblockDisjoint : Set.PairwiseDisjoint Set.univ block)
    (hblockCover : Finset.univ.biUnion block = T) (hq : 0 < q) :
    ∃ E : TreeGroupedTransversal (BlockDemand block (3 * q)) G C T q,
      ∀ j, (block j).card / (3 * q) ≤
        (block j ∩ E.toGroupedTransversal.selected).card := by
  classical
  rcases D.exists_colored_representatives block hblockDisjoint hblockCover hq with
    ⟨assign, representative, hassignInj, hrepresentativeInj,
      hrepresentativeMem, hquota⟩
  let E : TreeGroupedTransversal (BlockDemand block (3 * q)) G C T q := {
    support := fun d => D.support (assign d)
    group := fun d => D.group (assign d)
    representative := representative
    support_subset := fun d => D.support_subset (assign d)
    support_connected := fun d => D.support_connected (assign d)
    group_subset := fun d => D.group_subset (assign d)
    q_le_group_card := fun d => D.q_le_group_card (assign d)
    groups_pairwiseDisjoint := by
      intro a _ha b _hb hab
      exact D.groups_pairwiseDisjoint (by simp) (by simp)
        (fun h => hab (hassignInj h))
    representative_mem := fun d =>
      (Finset.mem_inter.mp (hrepresentativeMem d)).1
    representative_injective := hrepresentativeInj
    internalEdges_pairwiseDisjoint := by
      intro a _ha b _hb hab
      exact D.internalEdges_pairwiseDisjoint (by simp) (by simp)
        (fun h => hab (hassignInj h)) }
  refine ⟨E, ?_⟩
  intro j
  simpa [E, GroupedTransversal.selected] using hquota j

/-- Full finite producer from an Observation 2.12 tree grouping through the
paper-facing conclusion of Corollary 2.11 (preprint Corollary 2.8). -/
theorem blockGroupingConclusion
    {J : Type v} [Fintype J] [DecidableEq J]
    (D : TreeGrouping K G C T q) (block : J → Finset V)
    (hblockDisjoint : Set.PairwiseDisjoint Set.univ block)
    (hblockCover : Finset.univ.biUnion block = T) (hq : 0 < q)
    {alphaNum alphaDen : ℕ}
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hscale : alphaDen ≤ alphaNum * q) :
    Nonempty (BlockGroupingConclusion G C block q) := by
  rcases D.exists_treeGroupedTransversal block hblockDisjoint hblockCover hq with
    ⟨E, hquota⟩
  exact blockGroupingConclusion_of_treeGroupedTransversal
    block E hwell hscale hblockCover hquota

/-! ## Observation 2.12 base case -/

/-- The final iteration of Observation 2.12: if the remaining connected
support contains between `q` and `3*q` terminals, it is itself one valid
group. -/
noncomputable def ofSingleSupport
    (hconnected : (G.induce {v : V | v ∈ C}).Connected)
    (hTC : T ⊆ C) (hlower : q ≤ T.card) (hupper : T.card ≤ 3 * q) :
    TreeGrouping (ULift.{v} Unit) G C T q where
  support := fun _ => C
  group := fun _ => T
  support_subset := fun _ => Finset.Subset.rfl
  support_connected := fun _ => hconnected
  group_subset := by
    intro _ x hx
    exact Finset.mem_inter.mpr ⟨hTC hx, hx⟩
  q_le_group_card := fun _ => hlower
  group_card_le := fun _ => hupper
  groups_pairwiseDisjoint := by
    intro i _hi j _hj hij
    exact (hij (Subsingleton.elim i j)).elim
  groups_cover := by simp
  internalEdges_pairwiseDisjoint := by
    intro i _hi j _hj hij
    exact (hij (Subsingleton.elim i j)).elim

/-- Existential form of the final Observation 2.12 iteration. -/
theorem exists_treeGrouping_of_card_between
    (hconnected : (G.induce {v : V | v ∈ C}).Connected)
    (hTC : T ⊆ C) (hlower : q ≤ T.card) (hupper : T.card ≤ 3 * q) :
    Nonempty (TreeGrouping (ULift.{v} Unit) G C T q) :=
  ⟨ofSingleSupport hconnected hTC hlower hupper⟩

/-- The complete producer in the base range, including Observation 2.13 and
the paper-facing well-linked conclusion. -/
theorem blockGroupingConclusion_of_card_between
    {J : Type v} [Fintype J] [DecidableEq J]
    (block : J → Finset V)
    (hblockDisjoint : Set.PairwiseDisjoint Set.univ block)
    (hblockCover : Finset.univ.biUnion block = T)
    (hconnected : (G.induce {v : V | v ∈ C}).Connected)
    (hTC : T ⊆ C) (hq : 0 < q)
    (hlower : q ≤ T.card) (hupper : T.card ≤ 3 * q)
    {alphaNum alphaDen : ℕ}
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hscale : alphaDen ≤ alphaNum * q) :
    Nonempty (BlockGroupingConclusion G C block q) := by
  exact (ofSingleSupport hconnected hTC hlower hupper).blockGroupingConclusion
    block hblockDisjoint hblockCover hq hwell hscale

/-! ## Residual pruning and finite descent -/

/-- A family form of `TreeGrouping`, convenient for induction because a new
support/group pair can be inserted without changing an index type. -/
structure Family (G : _root_.SimpleGraph V) (C T : Finset V) (q : ℕ) where
  pieces : Finset (Finset V × Finset V)
  support_subset : ∀ p ∈ pieces, p.1 ⊆ C
  support_connected :
    ∀ p ∈ pieces, (G.induce {v : V | v ∈ p.1}).Connected
  group_subset : ∀ p ∈ pieces, p.2 ⊆ p.1 ∩ T
  q_le_group_card : ∀ p ∈ pieces, q ≤ p.2.card
  group_card_le : ∀ p ∈ pieces, p.2.card ≤ 3 * q
  groups_pairwiseDisjoint :
    (↑pieces : Set (Finset V × Finset V)).PairwiseDisjoint Prod.snd
  groups_cover : pieces.biUnion Prod.snd = T
  internalEdges_pairwiseDisjoint :
    (↑pieces : Set (Finset V × Finset V)).PairwiseDisjoint
      (fun p => Section44.edgeBoundary G p.1 p.1)

namespace Family

/-- The arithmetic core of the source's "smallest prefix of children"
argument.  No ordering is needed: induction either uses a suitable subfamily
of the tail or adds the current branch to a tail whose total is still below
`q`. -/
theorem exists_subfamily_sum_between
    {I : Type u} [DecidableEq I] (s : Finset I) (weight : I → ℕ) {q : ℕ}
    (htotal : q ≤ ∑ i ∈ s, weight i)
    (heach : ∀ i ∈ s, weight i ≤ q) :
    ∃ t ⊆ s, q ≤ ∑ i ∈ t, weight i ∧ ∑ i ∈ t, weight i ≤ 2 * q := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨∅, Finset.Subset.rfl, ?_, by simp⟩
      simpa using htotal
  | @insert a s ha ih =>
      by_cases htail : q ≤ ∑ i ∈ s, weight i
      · rcases ih htail (fun i hi => heach i (Finset.mem_insert_of_mem hi)) with
          ⟨t, hts, hlower, hupper⟩
        exact ⟨t, hts.trans (Finset.subset_insert a s), hlower, hupper⟩
      · refine ⟨insert a s, Finset.Subset.rfl, htotal, ?_⟩
        rw [Finset.sum_insert ha]
        have haBound := heach a (by simp)
        omega

/-- Convert the family representation to the public indexed representation. -/
noncomputable def toTreeGrouping (F : Family G C T q) :
    TreeGrouping {p // p ∈ F.pieces} G C T q where
  support := fun p => p.1.1
  group := fun p => p.1.2
  support_subset := fun p => F.support_subset p p.2
  support_connected := fun p => F.support_connected p p.2
  group_subset := fun p => F.group_subset p p.2
  q_le_group_card := fun p => F.q_le_group_card p p.2
  group_card_le := fun p => F.group_card_le p p.2
  groups_pairwiseDisjoint := by
    intro p _hp r _hr hpr
    exact F.groups_pairwiseDisjoint p.2 r.2 (fun h => hpr (Subtype.ext h))
  groups_cover := by
    calc
      Finset.univ.biUnion (fun p : {p // p ∈ F.pieces} => p.1.2) =
          F.pieces.biUnion Prod.snd := by
        ext x
        simp
      _ = T := F.groups_cover
  internalEdges_pairwiseDisjoint := by
    intro p _hp r _hr hpr
    exact F.internalEdges_pairwiseDisjoint p.2 r.2
      (fun h => hpr (Subtype.ext h))

/-- Internal edge sets are monotone in their vertex support. -/
theorem internalEdges_mono {A B : Finset V} (hAB : A ⊆ B) :
    Section44.edgeBoundary G A A ⊆ Section44.edgeBoundary G B B := by
  intro e he
  rcases (Section44.mem_edgeBoundary (G := G) A A e).mp he with
    ⟨heG, a, ha, b, hb, hab⟩
  exact (Section44.mem_edgeBoundary (G := G) B B e).mpr
    ⟨heG, a, hAB ha, b, hAB hb, hab⟩

/-- Supports intersecting in at most one prescribed vertex cannot share an
internal edge.  This turns the source's articulation-vertex overlap into the
edge-disjointness invariant used by `TreeGrouping`. -/
theorem internalEdges_disjoint_of_inter_subset_singleton
    {A B : Finset V} {pivot : V} (hinter : A ∩ B ⊆ {pivot}) :
    Disjoint (Section44.edgeBoundary G A A)
      (Section44.edgeBoundary G B B) := by
  apply Finset.disjoint_left.mpr
  intro e heA heB
  rcases (Section44.mem_edgeBoundary (G := G) A A e).mp heA with
    ⟨heG, a, haA, b, hbA, hab⟩
  rcases (Section44.mem_edgeBoundary (G := G) B B e).mp heB with
    ⟨_heG', c, hcB, d, hdB, hcd⟩
  have hedgeEq : s(a, b) = s(c, d) := hab.symm.trans hcd
  have habNe : a ≠ b := G.ne_of_adj (by
    rw [hab] at heG
    simpa using heG)
  rcases Sym2.eq_iff.mp hedgeEq with hsame | hswap
  · have haB : a ∈ B := by simpa [hsame.1] using hcB
    have hbB : b ∈ B := by simpa [hsame.2] using hdB
    have haPivot : a = pivot := by
      simpa using hinter (Finset.mem_inter.mpr ⟨haA, haB⟩)
    have hbPivot : b = pivot := by
      simpa using hinter (Finset.mem_inter.mpr ⟨hbA, hbB⟩)
    exact habNe (haPivot.trans hbPivot.symm)
  · have haB : a ∈ B := by simpa [hswap.1] using hdB
    have hbB : b ∈ B := by simpa [hswap.2] using hcB
    have haPivot : a = pivot := by
      simpa using hinter (Finset.mem_inter.mpr ⟨haA, haB⟩)
    have hbPivot : b = pivot := by
      simpa using hinter (Finset.mem_inter.mpr ⟨hbA, hbB⟩)
    exact habNe (haPivot.trans hbPivot.symm)

/-- One source iteration, stated only with the invariants needed by finite
descent.  The source's lowest-heavy-subtree construction supplies this
certificate with `group.card ≤ 2*q`; the weaker `3*q` bound is what the final
grouping consumes. -/
structure ResidualPruningStep
    (G : _root_.SimpleGraph V) (R U : Finset V) (q : ℕ) where
  support : Finset V
  group : Finset V
  residualSupport : Finset V
  residualTerminals : Finset V
  support_subset : support ⊆ R
  support_connected :
    (G.induce {v : V | v ∈ support}).Connected
  group_subset : group ⊆ support ∩ U
  q_le_group_card : q ≤ group.card
  group_card_le : group.card ≤ 3 * q
  residualSupport_subset : residualSupport ⊆ R
  residual_connected :
    (G.induce {v : V | v ∈ residualSupport}).Connected
  residualTerminals_subset :
    residualTerminals ⊆ residualSupport ∩ U
  q_le_residual_card : q ≤ residualTerminals.card
  terminals_disjoint : Disjoint group residualTerminals
  terminals_cover : group ∪ residualTerminals = U
  internalEdges_disjoint :
    Disjoint (Section44.edgeBoundary G support support)
      (Section44.edgeBoundary G residualSupport residualSupport)

namespace ResidualPruningStep

variable {R U : Finset V}

theorem group_nonempty (S : ResidualPruningStep G R U q) (hq : 0 < q) :
    S.group.Nonempty := by
  exact Finset.card_pos.mp (lt_of_lt_of_le hq S.q_le_group_card)

theorem residual_card_lt (S : ResidualPruningStep G R U q) (hq : 0 < q) :
    S.residualTerminals.card < U.card := by
  have hcard := Finset.card_union_of_disjoint S.terminals_disjoint
  rw [S.terminals_cover] at hcard
  have hgroupPos : 0 < S.group.card := lt_of_lt_of_le hq S.q_le_group_card
  omega

/-- Insert one pruning step in front of a grouping of the residual. -/
noncomputable def cons (S : ResidualPruningStep G R U q)
    (F : Family G S.residualSupport S.residualTerminals q) (hq : 0 < q) :
    Family G R U q := by
  classical
  let head : Finset V × Finset V := (S.support, S.group)
  have hheadNotMem : head ∉ F.pieces := by
    intro hmem
    have hsub := F.group_subset head hmem
    have hnonempty := S.group_nonempty hq
    rcases hnonempty with ⟨x, hx⟩
    have hxResidual : x ∈ S.residualTerminals :=
      (Finset.mem_inter.mp (hsub hx)).2
    exact Finset.disjoint_left.mp S.terminals_disjoint hx hxResidual
  refine {
    pieces := insert head F.pieces
    support_subset := ?_
    support_connected := ?_
    group_subset := ?_
    q_le_group_card := ?_
    group_card_le := ?_
    groups_pairwiseDisjoint := ?_
    groups_cover := ?_
    internalEdges_pairwiseDisjoint := ?_ }
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact S.support_subset
    · exact (F.support_subset p hp).trans S.residualSupport_subset
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact S.support_connected
    · exact F.support_connected p hp
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · intro x hx
      have hx' := S.group_subset hx
      exact hx'
    · intro x hx
      have hx' := F.group_subset p hp hx
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hx').1,
          by rw [← S.terminals_cover]; exact Finset.mem_union_right _ (Finset.mem_inter.mp hx').2⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact S.q_le_group_card
    · exact F.q_le_group_card p hp
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact S.group_card_le
    · exact F.group_card_le p hp
  · intro p hp r hr hpr
    rcases Finset.mem_insert.mp hp with hpEq | hpOld
    · subst p
      rcases Finset.mem_insert.mp hr with hrEq | hrOld
      · subst r
        exact (hpr rfl).elim
      · apply Finset.disjoint_left.mpr
        intro x hxHead hxOld
        have hxResidual := (Finset.mem_inter.mp (F.group_subset r hrOld hxOld)).2
        exact Finset.disjoint_left.mp S.terminals_disjoint hxHead hxResidual
    · rcases Finset.mem_insert.mp hr with hrEq | hrOld
      · subst r
        apply Finset.disjoint_left.mpr
        intro x hxOld hxHead
        have hxResidual := (Finset.mem_inter.mp (F.group_subset p hpOld hxOld)).2
        exact Finset.disjoint_left.mp S.terminals_disjoint hxHead hxResidual
      · exact F.groups_pairwiseDisjoint hpOld hrOld hpr
  · rw [Finset.biUnion_insert]
    simp only [head]
    rw [F.groups_cover, S.terminals_cover]
  · intro p hp r hr hpr
    rcases Finset.mem_insert.mp hp with hpEq | hpOld
    · subst p
      rcases Finset.mem_insert.mp hr with hrEq | hrOld
      · subst r
        exact (hpr rfl).elim
      · exact S.internalEdges_disjoint.mono_right
          (internalEdges_mono (F.support_subset r hrOld))
    · rcases Finset.mem_insert.mp hr with hrEq | hrOld
      · subst r
        exact S.internalEdges_disjoint.symm.mono_left
          (internalEdges_mono (F.support_subset p hpOld))
      · exact F.internalEdges_pairwiseDisjoint hpOld hrOld hpr

end ResidualPruningStep

/-- The one-step statement required from the rooted-tree argument. -/
def HasResidualPruningStep (G : _root_.SimpleGraph V) (q : ℕ) : Prop :=
  ∀ (R U : Finset V),
    (G.induce {v : V | v ∈ R}).Connected → U ⊆ R →
    q ≤ U.card → 3 * q < U.card →
    Nonempty (ResidualPruningStep G R U q)

/-- Finite descent: once every oversized connected residual admits one
pruning step, repeated pruning terminates and yields all of Observation 2.12. -/
theorem exists_family_of_hasResidualPruningStep
    (hq : 0 < q) (hstep : HasResidualPruningStep G q)
    (hconnected : (G.induce {v : V | v ∈ C}).Connected)
    (hTC : T ⊆ C) (hlower : q ≤ T.card) :
    Nonempty (Family G C T q) := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (R U : Finset V), U.card = n →
      (G.induce {v : V | v ∈ R}).Connected → U ⊆ R → q ≤ U.card →
      Nonempty (Family G R U q)
  have go : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro R U hcard hconn hUR hqU
        by_cases hsmall : U.card ≤ 3 * q
        · exact ⟨{
            pieces := {(R, U)}
            support_subset := by simp
            support_connected := by simpa using hconn
            group_subset := by
              intro p hp
              simp only [Finset.mem_singleton] at hp
              subst p
              intro x hx
              exact Finset.mem_inter.mpr ⟨hUR hx, hx⟩
            q_le_group_card := by simpa
            group_card_le := by simpa
            groups_pairwiseDisjoint := by
              intro p hp r hr hpr
              simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hp hr
              exact (hpr (hp.trans hr.symm)).elim
            groups_cover := by simp
            internalEdges_pairwiseDisjoint := by
              intro p hp r hr hpr
              simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hp hr
              exact (hpr (hp.trans hr.symm)).elim }⟩
        · have hlarge : 3 * q < U.card := by omega
          rcases hstep R U hconn hUR hqU hlarge with ⟨S⟩
          have hresLt : S.residualTerminals.card < n := by
            rw [← hcard]
            exact S.residual_card_lt hq
          rcases ih S.residualTerminals.card hresLt
              S.residualSupport S.residualTerminals rfl S.residual_connected
              (fun x hx => (Finset.mem_inter.mp (S.residualTerminals_subset hx)).1)
              S.q_le_residual_card with ⟨F⟩
          exact ⟨S.cons F hq⟩
  exact go T.card C T rfl hconnected hTC hlower

/-- Public indexed grouping produced by finite residual descent. -/
theorem exists_treeGrouping_of_hasResidualPruningStep
    (hq : 0 < q) (hstep : HasResidualPruningStep G q)
    (hconnected : (G.induce {v : V | v ∈ C}).Connected)
    (hTC : T ⊆ C) (hlower : q ≤ T.card) :
    ∃ K : Type u, ∃ _ : Fintype K, ∃ _ : DecidableEq K,
      Nonempty (TreeGrouping K G C T q) := by
  classical
  rcases exists_family_of_hasResidualPruningStep hq hstep hconnected hTC hlower with ⟨F⟩
  exact ⟨{p // p ∈ F.pieces}, inferInstance, inferInstance, ⟨F.toTreeGrouping⟩⟩

end Family

end TreeGrouping

end ChekuriChuzhoyCorollary28

end SimpleGraph

end Lax17Proofs
