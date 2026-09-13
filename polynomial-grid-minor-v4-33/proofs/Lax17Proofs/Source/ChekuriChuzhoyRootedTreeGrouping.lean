import Lax17Proofs.Source.ChekuriChuzhoyCorollary28Grouping
import Lax17Proofs.Source.ChekuriChuzhoyRootedTreeComponents

namespace Lax17Proofs

universe u v w

/-!
# Rooted-tree producer for Chekuri--Chuzhoy Observation 2.12

This file implements the lowest-heavy-subtree step and transports it from a
spanning tree of a connected residual to the ambient graph.  Together with
the finite descent in `ChekuriChuzhoyCorollary28Grouping`, it removes the last
semantic premise from the source-sharp grouping theorem.
-/

namespace SimpleGraph


namespace ChekuriChuzhoyRootedTreeGrouping

open Finset
open ChekuriChuzhoyRootedTreePruning
open ChekuriChuzhoyRootedTreeComponents

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H : _root_.SimpleGraph V}

/-- Terminals below a rooted-tree vertex. -/
noncomputable def subtreeTerminals (hH : H.IsTree) (root : V)
    (U : Finset V) (v : V) : Finset V :=
  U ∩ descendants hH root v

/-- Terminals below one immediate child. -/
noncomputable def childTerminals (hH : H.IsTree) (root : V)
    (U : Finset V) (c : V) : Finset V :=
  U ∩ childSubtree hH root c

@[simp] theorem mem_subtreeTerminals (hH : H.IsTree) (root : V)
    (U : Finset V) (v x : V) :
    x ∈ subtreeTerminals hH root U v ↔
      x ∈ U ∧ x ∈ descendants hH root v := by
  simp [subtreeTerminals]

@[simp] theorem mem_childTerminals (hH : H.IsTree) (root : V)
    (U : Finset V) (c x : V) :
    x ∈ childTerminals hH root U c ↔
      x ∈ U ∧ x ∈ childSubtree hH root c := by
  simp [childTerminals]

/-- The terminal count below a vertex is its own terminal indicator plus the
sum of the counts in its pairwise disjoint child subtrees. -/
theorem subtreeTerminals_card_eq
    (hH : H.IsTree) (root : V)
    (hdec : ParentDistanceDecreases hH root) (U : Finset V) (v : V) :
    (subtreeTerminals hH root U v).card =
      (if v ∈ U then 1 else 0) +
        ∑ c ∈ children hH root v, (childTerminals hH root U c).card := by
  classical
  let own : Finset V := if v ∈ U then {v} else ∅
  let branches : Finset V :=
    (children hH root v).biUnion (childTerminals hH root U)
  have hdecomp : subtreeTerminals hH root U v = own ∪ branches := by
    ext x
    rw [mem_subtreeTerminals]
    rw [mem_descendants_iff_eq_or_childSubtree hH root hdec]
    simp only [branches, Finset.mem_union, Finset.mem_biUnion,
      mem_childTerminals]
    by_cases hvU : v ∈ U
    · simp only [own, hvU, if_pos, Finset.mem_singleton]
      aesop
    · simp [own, hvU]
      aesop
  have hownBranches : Disjoint own branches := by
    apply Finset.disjoint_left.mpr
    intro x hxown hxbranches
    have hxv : x = v := by
      dsimp [own] at hxown
      split at hxown
      · simpa using hxown
      · simp at hxown
    subst x
    rcases Finset.mem_biUnion.mp hxbranches with ⟨c, hc, hvc⟩
    have hcchild := (mem_children hH root v c).1 hc
    exact parent_not_mem_childSubtree hH root hdec hcchild
      ((mem_childTerminals hH root U c v).1 hvc).2
  have hbranchesCard : branches.card =
      ∑ c ∈ children hH root v, (childTerminals hH root U c).card := by
    dsimp [branches]
    apply Finset.card_biUnion
    intro c hc d hd hcd
    exact (childSubtree_disjoint hH root hdec
      ((mem_children hH root v c).1 hc)
      ((mem_children hH root v d).1 hd) hcd).mono
        (Finset.inter_subset_right)
        (Finset.inter_subset_right)
  rw [hdecomp, Finset.card_union_of_disjoint hownBranches, hbranchesCard]
  by_cases hvU : v ∈ U <;> simp [own, hvU]

/-- Terminal count in a pruning support formed from an arbitrary selection of
child branches. -/
theorem pruningTerminals_card_eq
    (hH : H.IsTree) (root : V)
    (hdec : ParentDistanceDecreases hH root) (U : Finset V) (v : V)
    {selected : Finset V}
    (hselected : ∀ c ∈ selected, IsChild hH root v c) :
    (U ∩ pruningSupport hH root v selected).card =
      (if v ∈ U then 1 else 0) +
        ∑ c ∈ selected, (childTerminals hH root U c).card := by
  classical
  let own : Finset V := if v ∈ U then {v} else ∅
  let branches : Finset V := selected.biUnion (childTerminals hH root U)
  have hdecomp : U ∩ pruningSupport hH root v selected = own ∪ branches := by
    ext x
    rw [Finset.mem_inter, mem_pruningSupport]
    simp only [branches, Finset.mem_union, Finset.mem_biUnion,
      mem_childTerminals]
    by_cases hvU : v ∈ U
    · simp only [own, hvU, if_pos, Finset.mem_singleton]
      aesop
    · simp [own, hvU]
      aesop
  have hownBranches : Disjoint own branches := by
    apply Finset.disjoint_left.mpr
    intro x hxown hxbranches
    have hxv : x = v := by
      dsimp [own] at hxown
      split at hxown
      · simpa using hxown
      · simp at hxown
    subst x
    rcases Finset.mem_biUnion.mp hxbranches with ⟨c, hc, hvc⟩
    exact parent_not_mem_childSubtree hH root hdec (hselected c hc)
      ((mem_childTerminals hH root U c v).1 hvc).2
  have hbranchesCard : branches.card =
      ∑ c ∈ selected, (childTerminals hH root U c).card := by
    dsimp [branches]
    apply Finset.card_biUnion
    intro c hc d hd hcd
    exact (childSubtree_disjoint hH root hdec
      (hselected c hc) (hselected d hd) hcd).mono
        Finset.inter_subset_right Finset.inter_subset_right
  rw [hdecomp, Finset.card_union_of_disjoint hownBranches, hbranchesCard]
  by_cases hvU : v ∈ U <;> simp [own, hvU]

/-- Vertices whose descendant subtree contains at least `q` terminals. -/
noncomputable def heavyVertices (hH : H.IsTree) (root : V)
    (U : Finset V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun v => q ≤ (subtreeTerminals hH root U v).card

@[simp] theorem mem_heavyVertices (hH : H.IsTree) (root : V)
    (U : Finset V) (q : ℕ) (v : V) :
    v ∈ heavyVertices hH root U q ↔
      q ≤ (subtreeTerminals hH root U v).card := by
  classical
  simp [heavyVertices]

theorem subtreeTerminals_root (hH : H.IsTree) (root : V) (U : Finset V) :
    subtreeTerminals hH root U root = U := by
  ext x
  simp [subtreeTerminals, mem_descendants_root hH root x]

/-- A deepest heavy vertex has only light immediate child subtrees. -/
theorem exists_lowestHeavy
    (hH : H.IsTree) (root : V)
    (hdec : ParentDistanceDecreases hH root) (U : Finset V) {q : ℕ}
    (hqU : q ≤ U.card) :
    ∃ v ∈ heavyVertices hH root U q,
      ∀ c ∈ children hH root v,
        (childTerminals hH root U c).card < q := by
  classical
  have hrootHeavy : root ∈ heavyVertices hH root U q := by
    rw [mem_heavyVertices, subtreeTerminals_root]
    exact hqU
  rcases Finset.exists_max_image (heavyVertices hH root U q)
      (H.dist root) ⟨root, hrootHeavy⟩ with ⟨v, hvHeavy, hvMax⟩
  refine ⟨v, hvHeavy, ?_⟩
  intro c hc
  by_contra hnot
  have hcHeavy : c ∈ heavyVertices hH root U q := by
    rw [mem_heavyVertices]
    have hchildSubset : childTerminals hH root U c ⊆
        subtreeTerminals hH root U c := by
      intro x hx
      exact (mem_subtreeTerminals hH root U c x).2
        ⟨(mem_childTerminals hH root U c x).1 hx |>.1,
          (mem_childTerminals hH root U c x).1 hx |>.2⟩
    exact (Nat.le_of_not_gt hnot).trans
      (Finset.card_le_card hchildSubset)
  have hdistLe := hvMax c hcHeavy
  have hdistStep := ((mem_children hH root v c).1 hc).dist_eq_add_one
    hH root hdec
  omega

/-- At a lowest heavy vertex, select whole child branches whose combined
terminal weight, together with the pivot when terminal, lies between `q` and
`2*q+1`. -/
theorem exists_selectedChildren
    (hH : H.IsTree) (root : V)
    (hdec : ParentDistanceDecreases hH root) (U : Finset V)
    {v : V} {q : ℕ} (hq : 0 < q)
    (hvHeavy : q ≤ (subtreeTerminals hH root U v).card)
    (hchildren : ∀ c ∈ children hH root v,
      (childTerminals hH root U c).card < q) :
    ∃ selected ⊆ children hH root v,
      q ≤ (U ∩ pruningSupport hH root v selected).card ∧
      (U ∩ pruningSupport hH root v selected).card ≤ 2 * q + 1 := by
  classical
  let own := if v ∈ U then 1 else 0
  let weight := fun c : V => (childTerminals hH root U c).card
  let all := children hH root v
  have hcount := subtreeTerminals_card_eq hH root hdec U v
  change (subtreeTerminals hH root U v).card =
      own + ∑ c ∈ all, weight c at hcount
  by_cases hsum : q ≤ ∑ c ∈ all, weight c
  · rcases
      ChekuriChuzhoyCorollary28.TreeGrouping.Family.exists_subfamily_sum_between
        all weight hsum (fun c hc => (hchildren c hc).le) with
      ⟨selected, hselected, hlower, hupper⟩
    refine ⟨selected, hselected, ?_, ?_⟩
    · rw [pruningTerminals_card_eq hH root hdec U v
          (fun c hc => (mem_children hH root v c).1 (hselected hc))]
      exact hlower.trans (Nat.le_add_left _ _)
    · rw [pruningTerminals_card_eq hH root hdec U v
          (fun c hc => (mem_children hH root v c).1 (hselected hc))]
      have hown : own ≤ 1 := by
        dsimp [own]
        split <;> omega
      change own + ∑ c ∈ selected, weight c ≤ 2 * q + 1
      omega
  · refine ⟨all, Finset.Subset.rfl, ?_, ?_⟩
    · rw [pruningTerminals_card_eq hH root hdec U v
          (fun c hc => (mem_children hH root v c).1 hc)]
      change q ≤ own + ∑ c ∈ all, weight c
      omega
    · rw [pruningTerminals_card_eq hH root hdec U v
          (fun c hc => (mem_children hH root v c).1 hc)]
      have hown : own ≤ 1 := by
        dsimp [own]
        split <;> omega
      change own + ∑ c ∈ all, weight c ≤ 2 * q + 1
      omega

/-- The complete Observation 2.12 pruning step for a finite tree, retaining
the singleton-intersection certificate needed when the tree is mapped back
into an ambient graph with additional edges. -/
theorem exists_residualPruningStepWithIntersection_of_isTree
    (hH : H.IsTree) (U : Finset V) {q : ℕ}
    (hq : 0 < q) (hqU : q ≤ U.card) (hlarge : 3 * q < U.card) :
    ∃ S : ChekuriChuzhoyCorollary28.TreeGrouping.Family.ResidualPruningStep
        H Finset.univ U q,
      ∃ pivot : V, S.support ∩ S.residualSupport ⊆ {pivot} := by
  classical
  let root : V := Classical.choice hH.nonempty
  have hdec : ParentDistanceDecreases hH root :=
    fun {_} hx => dist_parent_add_one hH root hx
  rcases exists_lowestHeavy hH root hdec U hqU with
    ⟨v, hvHeavy, hvChildren⟩
  have hvCount := (mem_heavyVertices hH root U q v).1 hvHeavy
  rcases exists_selectedChildren hH root hdec U hq hvCount hvChildren with
    ⟨selected, hselectedSubset, hgroupLower, hgroupUpper⟩
  have hselected : ∀ c ∈ selected, IsChild hH root v c :=
    fun c hc => (mem_children hH root v c).1 (hselectedSubset hc)
  let support := pruningSupport hH root v selected
  let group := U ∩ support
  let residualSupport := residual hH root selected
  let residualTerminals := U \ group
  have hgroupSubsetU : group ⊆ U := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hresidualCard : q ≤ residualTerminals.card := by
    have hcard : residualTerminals.card = U.card - group.card := by
      exact Finset.card_sdiff_of_subset hgroupSubsetU
    have hgroupBound : group.card ≤ 2 * q + 1 := by
      simpa [group, support] using hgroupUpper
    rw [hcard]
    omega
  refine ⟨{
    support := support
    group := group
    residualSupport := residualSupport
    residualTerminals := residualTerminals
    support_subset := Finset.subset_univ support
    support_connected := by
      simpa [support] using pruningSupport_connected hH root v hselected
    group_subset := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
    q_le_group_card := by simpa [group, support] using hgroupLower
    group_card_le := by
      have htwo : 2 * q + 1 ≤ 3 * q := by omega
      have hg : group.card ≤ 2 * q + 1 := by
        simpa [group, support] using hgroupUpper
      exact hg.trans htwo
    residualSupport_subset := Finset.subset_univ residualSupport
    residual_connected := by
      simpa [residualSupport] using
        residual_connected hH root v hdec hselected
    residualTerminals_subset := by
      intro x hx
      have hxU : x ∈ U := (Finset.mem_sdiff.mp hx).1
      have hxNotGroup : x ∉ group := (Finset.mem_sdiff.mp hx).2
      refine Finset.mem_inter.mpr ⟨?_, hxU⟩
      rw [show residualSupport = residual hH root selected from rfl,
        ChekuriChuzhoyRootedTreeComponents.mem_residual]
      intro hxRemoved
      apply hxNotGroup
      exact Finset.mem_inter.mpr ⟨hxU, by
        rw [show support = pruningSupport hH root v selected from rfl,
          mem_pruningSupport]
        rw [mem_selectedDescendants] at hxRemoved
        exact Or.inr hxRemoved⟩
    q_le_residual_card := hresidualCard
    terminals_disjoint := Finset.disjoint_sdiff
    terminals_cover := by
      exact Finset.union_sdiff_of_subset hgroupSubsetU
    internalEdges_disjoint := by
      exact
        ChekuriChuzhoyCorollary28.TreeGrouping.Family.internalEdges_disjoint_of_inter_subset_singleton
            (pruningSupport_inter_residual_subset hH root v selected) }, v, ?_⟩
  simpa [support, residualSupport] using
    pruningSupport_inter_residual_subset hH root v selected

/-- Existential projection of the tree pruning certificate. -/
theorem exists_residualPruningStep_of_isTree
    (hH : H.IsTree) (U : Finset V) {q : ℕ}
    (hq : 0 < q) (hqU : q ≤ U.card) (hlarge : 3 * q < U.card) :
    Nonempty
      (ChekuriChuzhoyCorollary28.TreeGrouping.Family.ResidualPruningStep
        H Finset.univ U q) := by
  rcases exists_residualPruningStepWithIntersection_of_isTree
    hH U hq hqU hlarge with ⟨S, _pivot, _hinter⟩
  exact ⟨S⟩

/-! ## Transport from a spanning tree of an induced residual -/

/-- Map a finset on the residual subtype back to ambient vertices. -/
noncomputable def liftFinset {R : Finset V}
    (A : Finset {v : V // v ∈ R}) : Finset V :=
  A.image Subtype.val

@[simp] theorem mem_liftFinset {R : Finset V}
    (A : Finset {v : V // v ∈ R}) (x : V) :
    x ∈ liftFinset A ↔ ∃ y ∈ A, y.1 = x := by
  classical
  simp [liftFinset]

theorem card_liftFinset {R : Finset V}
    (A : Finset {v : V // v ∈ R}) :
    (liftFinset A).card = A.card := by
  classical
  exact Finset.card_image_iff.mpr fun x _ y _ hxy => Subtype.ext hxy

theorem liftFinset_subset {R : Finset V}
    (A : Finset {v : V // v ∈ R}) : liftFinset A ⊆ R := by
  intro x hx
  rcases (mem_liftFinset A x).1 hx with ⟨y, _hy, rfl⟩
  exact y.2

theorem liftFinset_union {R : Finset V}
    (A B : Finset {v : V // v ∈ R}) :
    liftFinset (A ∪ B) = liftFinset A ∪ liftFinset B := by
  classical
  ext x
  constructor
  · intro hx
    rcases (mem_liftFinset (A ∪ B) x).1 hx with ⟨y, hy, hxy⟩
    rcases Finset.mem_union.mp hy with hyA | hyB
    · exact Finset.mem_union_left _ ((mem_liftFinset A x).2 ⟨y, hyA, hxy⟩)
    · exact Finset.mem_union_right _ ((mem_liftFinset B x).2 ⟨y, hyB, hxy⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · rcases (mem_liftFinset A x).1 hxA with ⟨y, hy, hxy⟩
      exact (mem_liftFinset (A ∪ B) x).2
        ⟨y, Finset.mem_union_left _ hy, hxy⟩
    · rcases (mem_liftFinset B x).1 hxB with ⟨y, hy, hxy⟩
      exact (mem_liftFinset (A ∪ B) x).2
        ⟨y, Finset.mem_union_right _ hy, hxy⟩

theorem liftFinset_inter {R : Finset V}
    (A B : Finset {v : V // v ∈ R}) :
    liftFinset (A ∩ B) = liftFinset A ∩ liftFinset B := by
  classical
  ext x
  constructor
  · intro hx
    rcases (mem_liftFinset (A ∩ B) x).1 hx with ⟨y, hy, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_liftFinset A y.1).2 ⟨y, (Finset.mem_inter.mp hy).1, rfl⟩,
        (mem_liftFinset B y.1).2 ⟨y, (Finset.mem_inter.mp hy).2, rfl⟩⟩
  · intro hx
    rcases (mem_liftFinset A x).1 (Finset.mem_inter.mp hx).1 with
      ⟨a, ha, hax⟩
    rcases (mem_liftFinset B x).1 (Finset.mem_inter.mp hx).2 with
      ⟨b, hb, hbx⟩
    have hab : a = b := Subtype.ext (hax.trans hbx.symm)
    subst b
    exact (mem_liftFinset (A ∩ B) x).2
      ⟨a, Finset.mem_inter.mpr ⟨ha, hb⟩, hax⟩

/-- Restrict ambient terminals to a residual subtype. -/
noncomputable def restrictFinset (R U : Finset V) :
    Finset {v : V // v ∈ R} :=
  Finset.univ.filter fun x => x.1 ∈ U

@[simp] theorem mem_restrictFinset (R U : Finset V) (x : {v : V // v ∈ R}) :
    x ∈ restrictFinset R U ↔ x.1 ∈ U := by
  classical
  simp [restrictFinset]

theorem liftFinset_restrictFinset {R U : Finset V} (hUR : U ⊆ R) :
    liftFinset (restrictFinset R U) = U := by
  classical
  ext x
  constructor
  · rintro hx
    rcases (mem_liftFinset (restrictFinset R U) x).1 hx with ⟨y, hy, rfl⟩
    exact (mem_restrictFinset R U y).1 hy
  · intro hx
    exact (mem_liftFinset (restrictFinset R U) x).2
      ⟨⟨x, hUR hx⟩, (mem_restrictFinset R U _).2 hx, rfl⟩

theorem card_restrictFinset {R U : Finset V} (hUR : U ⊆ R) :
    (restrictFinset R U).card = U.card := by
  rw [← card_liftFinset (restrictFinset R U), liftFinset_restrictFinset hUR]

/-- Connected induced subgraphs of a residual-subtype graph remain connected
after mapping their vertices into an ambient supergraph. -/
theorem connected_liftFinset
    {G : _root_.SimpleGraph V} {R : Finset V}
    {K : _root_.SimpleGraph {v : V // v ∈ R}}
    (hK : K ≤ G.induce {v : V | v ∈ R})
    (A : Finset {v : V // v ∈ R})
    (hconn : (K.induce {x | x ∈ A}).Connected) :
    (G.induce {v : V | v ∈ liftFinset A}).Connected := by
  classical
  let f : (K.induce {x | x ∈ A}) →g
      (G.induce {v : V | v ∈ liftFinset A}) := {
    toFun := fun x => ⟨x.1.1, (mem_liftFinset A x.1.1).2 ⟨x.1, x.2, rfl⟩⟩
    map_rel' := by
      intro x y hxy
      change G.Adj x.1.1 y.1.1
      exact hK hxy }
  apply hconn.map f
  intro y
  rcases (mem_liftFinset A y.1).1 y.2 with ⟨x, hxA, hxy⟩
  refine ⟨⟨x, hxA⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- Journal Observation 2.12's one-step producer for every connected finite
residual.  A spanning tree is chosen on the residual subtype, pruned there,
and mapped back to the ambient graph. -/
theorem hasResidualPruningStep_of_connected
    {G : _root_.SimpleGraph V} {q : ℕ} (hq : 0 < q) :
    ChekuriChuzhoyCorollary28.TreeGrouping.Family.HasResidualPruningStep G q := by
  classical
  intro R U hconnected hUR hqU hlarge
  let GR : _root_.SimpleGraph {v : V // v ∈ R} :=
    G.induce {v : V | v ∈ R}
  let UR : Finset {v : V // v ∈ R} := restrictFinset R U
  have hURcard : UR.card = U.card := by
    simpa [UR] using card_restrictFinset hUR
  have hGRconnected : GR.Connected := by
    simpa [GR] using hconnected
  rcases hGRconnected.exists_isTree_le with ⟨T, hTle, hTtree⟩
  have hqUR : q ≤ UR.card := by simpa [hURcard] using hqU
  have hlargeUR : 3 * q < UR.card := by simpa [hURcard] using hlarge
  rcases exists_residualPruningStepWithIntersection_of_isTree
      hTtree UR hq hqUR hlargeUR with ⟨S, pivot, hinter⟩
  have hTleAmbient : T ≤ G.induce {v : V | v ∈ R} := by
    simpa [GR] using hTle
  have hsupportInter :
      liftFinset S.support ∩ liftFinset S.residualSupport ⊆ {pivot.1} := by
    intro x hx
    have hx' : x ∈ liftFinset (S.support ∩ S.residualSupport) := by
      rw [liftFinset_inter]
      exact hx
    rcases (mem_liftFinset (S.support ∩ S.residualSupport) x).1 hx' with
      ⟨y, hy, hyx⟩
    have hyp : y = pivot := by simpa using hinter hy
    subst y
    simpa [hyx]
  refine ⟨{
    support := liftFinset S.support
    group := liftFinset S.group
    residualSupport := liftFinset S.residualSupport
    residualTerminals := liftFinset S.residualTerminals
    support_subset := liftFinset_subset S.support
    support_connected := connected_liftFinset hTleAmbient S.support
      S.support_connected
    group_subset := by
      intro x hx
      rcases (mem_liftFinset S.group x).1 hx with ⟨y, hy, rfl⟩
      have hy' := S.group_subset hy
      have hySupport := (Finset.mem_inter.mp hy').1
      have hyUR := (Finset.mem_inter.mp hy').2
      exact Finset.mem_inter.mpr
        ⟨(mem_liftFinset S.support y.1).2 ⟨y, hySupport, rfl⟩,
          by simpa [UR] using (mem_restrictFinset R U y).1 hyUR⟩
    q_le_group_card := by
      rw [card_liftFinset]
      exact S.q_le_group_card
    group_card_le := by
      rw [card_liftFinset]
      exact S.group_card_le
    residualSupport_subset := liftFinset_subset S.residualSupport
    residual_connected := connected_liftFinset hTleAmbient S.residualSupport
      S.residual_connected
    residualTerminals_subset := by
      intro x hx
      rcases (mem_liftFinset S.residualTerminals x).1 hx with ⟨y, hy, rfl⟩
      have hy' := S.residualTerminals_subset hy
      have hySupport := (Finset.mem_inter.mp hy').1
      have hyUR := (Finset.mem_inter.mp hy').2
      exact Finset.mem_inter.mpr
        ⟨(mem_liftFinset S.residualSupport y.1).2 ⟨y, hySupport, rfl⟩,
          by simpa [UR] using (mem_restrictFinset R U y).1 hyUR⟩
    q_le_residual_card := by
      rw [card_liftFinset]
      exact S.q_le_residual_card
    terminals_disjoint := by
      apply Finset.disjoint_left.mpr
      intro x hxg hxr
      rcases (mem_liftFinset S.group x).1 hxg with ⟨a, ha, hax⟩
      rcases (mem_liftFinset S.residualTerminals x).1 hxr with ⟨b, hb, hbx⟩
      have hab : a = b := Subtype.ext (hax.trans hbx.symm)
      subst b
      exact Finset.disjoint_left.mp S.terminals_disjoint ha hb
    terminals_cover := by
      rw [← liftFinset_union, S.terminals_cover]
      exact liftFinset_restrictFinset hUR
    internalEdges_disjoint :=
      ChekuriChuzhoyCorollary28.TreeGrouping.Family.internalEdges_disjoint_of_inter_subset_singleton
        hsupportInter }⟩

/-- Full source-sharp Observation 2.12 grouping in every connected cluster. -/
theorem exists_treeGrouping_of_connected
    {G : _root_.SimpleGraph V} {C U : Finset V} {q : ℕ}
    (hq : 0 < q)
    (hconnected : (G.induce {v : V | v ∈ C}).Connected)
    (hUC : U ⊆ C) (hqU : q ≤ U.card) :
    ∃ K : Type u, ∃ _ : Fintype K, ∃ _ : DecidableEq K,
      Nonempty
        (ChekuriChuzhoyCorollary28.TreeGrouping K G C U q) := by
  exact
    ChekuriChuzhoyCorollary28.TreeGrouping.Family.exists_treeGrouping_of_hasResidualPruningStep hq
        (hasResidualPruningStep_of_connected hq) hconnected hUC hqU

end ChekuriChuzhoyRootedTreeGrouping
end SimpleGraph

end Lax17Proofs
