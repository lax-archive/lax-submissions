import Lax17Proofs.Source.ChekuriChuzhoySection5Clustering

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 finite selection foundations

This module isolates the deterministic finite content of the edge-group
selections used in journal Section 5.4.  A group map models the partition into
groups supplied by journal Theorem 5.12.  The main theorem greedily reserves
distinct groups for every requested bundle and then chooses one item from each
reserved group.  Its spread hypothesis is necessary: arbitrary bundles may be
different singletons in the same group, in which case no transversal can meet
all of them.

No randomized algorithm or probability API is used.  The resulting existence
theorems are suitable for the Phase 1 and Phase 2 selections once the paper's
concentration estimates have supplied enough distinct groups per bundle.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Selection


open Finset

variable {Item : Type u} {Group : Type v}

/-! ## Partial and exact group transversals -/

/-- A subset of `items` containing at most one item with each group label. -/
def IsPartialGroupTransversal [DecidableEq Item]
    (items : Finset Item) (group : Item → Group) (selected : Finset Item) : Prop :=
  selected ⊆ items ∧ Set.InjOn group selected

/-- A partial transversal containing one item from every group represented in
`items`. -/
def IsExactGroupTransversal [DecidableEq Item] [DecidableEq Group]
    (items : Finset Item) (group : Item → Group) (selected : Finset Item) : Prop :=
  IsPartialGroupTransversal items group selected ∧
    selected.image group = items.image group

theorem IsPartialGroupTransversal.card_inter_fiber_le_one
    [DecidableEq Item] [DecidableEq Group]
    {items selected : Finset Item} {group : Item → Group}
    (h : IsPartialGroupTransversal items group selected) (g : Group) :
    (selected.filter fun x => group x = g).card ≤ 1 := by
  classical
  by_contra hbad
  have htwo : 2 ≤ (selected.filter fun x => group x = g).card := by omega
  rcases Finset.one_lt_card.mp (lt_of_lt_of_le Nat.one_lt_two htwo) with
    ⟨x, hx, y, hy, hxy⟩
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  exact hxy (h.2 hx'.1 hy'.1 (hx'.2.trans hy'.2.symm))

theorem IsExactGroupTransversal.existsUnique_mem_group
    [DecidableEq Item] [DecidableEq Group]
    {items selected : Finset Item} {group : Item → Group}
    (h : IsExactGroupTransversal items group selected)
    {g : Group} (hg : g ∈ items.image group) :
    ∃! x, x ∈ selected ∧ group x = g := by
  have hg' : g ∈ selected.image group := h.2.symm ▸ hg
  rcases Finset.mem_image.mp hg' with ⟨x, hx, hxg⟩
  refine ⟨x, ⟨hx, hxg⟩, ?_⟩
  rintro y ⟨hy, hyg⟩
  exact h.1.2 hy hx (hyg.trans hxg.symm)

/-- Choose one item above each prescribed represented group. -/
theorem exists_partialGroupTransversal_image_eq
    [DecidableEq Item] [DecidableEq Group]
    (items : Finset Item) (group : Item → Group) (groups : Finset Group)
    (hgroups : groups ⊆ items.image group) :
    ∃ selected : Finset Item,
      IsPartialGroupTransversal items group selected ∧
        selected.image group = groups := by
  classical
  have hsurj : (↑items : Set Item).SurjOn group (↑groups : Set Group) := by
    intro g hg
    rcases Finset.mem_image.mp (hgroups hg) with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  rcases Finset.exists_subset_injOn_image_eq_of_surjOn
      (s := (↑items : Set Item)) groups hsurj with
    ⟨selected, hselected, hinj, himage⟩
  exact ⟨selected, ⟨by simpa using hselected, hinj⟩, himage⟩

private theorem disjoint_of_disjoint_image
    [DecidableEq Item] [DecidableEq Group]
    {group : Item → Group} {left right : Finset Item}
    (h : Disjoint (left.image group) (right.image group)) :
    Disjoint left right := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hxleft hxright
  exact h (Finset.mem_image_of_mem group hxleft)
    (Finset.mem_image_of_mem group hxright)

private theorem injOn_union_of_disjoint_image
    [DecidableEq Item] [DecidableEq Group]
    {group : Item → Group} {left right : Finset Item}
    (hleft : Set.InjOn group left) (hright : Set.InjOn group right)
    (himage : Disjoint (left.image group) (right.image group)) :
    Set.InjOn group (left ∪ right) := by
  have hdisjoint : Disjoint left right := disjoint_of_disjoint_image himage
  rw [Set.injOn_union (by simpa using hdisjoint)]
  refine ⟨hleft, hright, ?_⟩
  intro x hx y hy hxy
  rw [Finset.disjoint_left] at himage
  exact himage (Finset.mem_image_of_mem group hx)
    (hxy ▸ Finset.mem_image_of_mem group hy)

/-- Any partial transversal extends to an exact transversal without removing a
previously selected item. -/
theorem IsPartialGroupTransversal.exists_exact_superset
    [DecidableEq Item] [DecidableEq Group]
    {items selected : Finset Item} {group : Item → Group}
    (h : IsPartialGroupTransversal items group selected) :
    ∃ full : Finset Item,
      IsExactGroupTransversal items group full ∧ selected ⊆ full := by
  classical
  let remaining := items.image group \ selected.image group
  have hremaining : remaining ⊆ items.image group := Finset.sdiff_subset
  rcases exists_partialGroupTransversal_image_eq items group remaining hremaining with
    ⟨fresh, hfresh, hfreshImage⟩
  have himage : Disjoint (selected.image group) (fresh.image group) := by
    rw [hfreshImage, Finset.disjoint_left]
    intro g hgselected hgremaining
    exact (Finset.mem_sdiff.mp hgremaining).2 hgselected
  refine ⟨selected ∪ fresh, ?_, Finset.subset_union_left⟩
  constructor
  · constructor
    · exact Finset.union_subset h.1 hfresh.1
    · simpa only [Finset.coe_union] using
        injOn_union_of_disjoint_image h.2 hfresh.2 himage
  · rw [Finset.image_union, hfreshImage]
    ext g
    simp only [remaining, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hg | ⟨hg, _⟩)
      · rcases Finset.mem_image.mp hg with ⟨x, hx, rfl⟩
        exact Finset.mem_image_of_mem group (h.1 hx)
      · exact hg
    · intro hg
      by_cases hs : g ∈ selected.image group
      · exact Or.inl hs
      · exact Or.inr ⟨hg, hs⟩

/-! ## A sharp single-bundle counting bound -/

/-- For one requested bundle, an exact transversal can favor that bundle in
every group it meets.  If all groups have size at most `maxGroupSize`, the
selected intersection retains the sharp cleared fraction
`bundle.card / maxGroupSize`. -/
theorem exists_exactGroupTransversal_card_bundle_le_mul
    [DecidableEq Item] [DecidableEq Group]
    (items : Finset Item) (group : Item → Group)
    (bundle : Finset Item) (maxGroupSize : ℕ)
    (hbundle : bundle ⊆ items)
    (hgroupSize : ∀ g ∈ items.image group,
      (items.filter fun x => group x = g).card ≤ maxGroupSize) :
    ∃ selected : Finset Item,
      IsExactGroupTransversal items group selected ∧
        bundle.card ≤ maxGroupSize * (selected ∩ bundle).card := by
  classical
  rcases exists_partialGroupTransversal_image_eq
      bundle group (bundle.image group) (fun _ h => h) with
    ⟨favored, hfavored, hfavoredImage⟩
  have hfavoredItems : IsPartialGroupTransversal items group favored :=
    ⟨hfavored.1.trans hbundle, hfavored.2⟩
  rcases hfavoredItems.exists_exact_superset with
    ⟨selected, hselected, hfavoredSubset⟩
  have hfiber : ∀ g ∈ bundle.image group,
      (bundle.filter fun x => group x = g).card ≤ maxGroupSize := by
    intro g hg
    have hgItems : g ∈ items.image group := by
      rcases Finset.mem_image.mp hg with ⟨x, hx, rfl⟩
      exact Finset.mem_image_of_mem group (hbundle hx)
    exact (Finset.card_le_card (by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxBundle, hxg⟩
      exact Finset.mem_filter.mpr ⟨hbundle hxBundle, hxg⟩)).trans
        (hgroupSize g hgItems)
  refine ⟨selected, hselected, ?_⟩
  calc
    bundle.card ≤ maxGroupSize * (bundle.image group).card :=
      Finset.card_le_mul_card_image bundle maxGroupSize hfiber
    _ = maxGroupSize * favored.card := by
      rw [← hfavoredImage, Finset.card_image_of_injOn hfavored.2]
    _ ≤ maxGroupSize * (selected ∩ bundle).card := Nat.mul_le_mul_left _
      (Finset.card_le_card (by
        intro x hx
        exact Finset.mem_inter.mpr ⟨hfavoredSubset hx, hfavored.1 hx⟩))

/-! ## Simultaneous retention in requested bundles -/

/-- Greedy simultaneous group selection.  If there are at most `r` requested
bundles and every bundle meets at least `r * q` distinct groups, one can select
at most one item per group while retaining at least `q` items from every
bundle. -/
theorem exists_partialGroupTransversal_card_inter_bundle
    [DecidableEq Item] [DecidableEq Group]
    (items : Finset Item) (group : Item → Group)
    (bundles : Finset (Finset Item)) (r q : ℕ)
    (hbundles : ∀ B ∈ bundles, B ⊆ items)
    (hcount : bundles.card ≤ r)
    (hspread : ∀ B ∈ bundles, r * q ≤ (B.image group).card) :
    ∃ selected : Finset Item,
      IsPartialGroupTransversal items group selected ∧
        selected.card = bundles.card * q ∧
        ∀ B ∈ bundles, q ≤ (selected ∩ B).card := by
  classical
  induction bundles using Finset.induction_on with
  | empty =>
      refine ⟨∅, ⟨Finset.empty_subset _, by simp⟩, by simp, ?_⟩
      simp
  | @insert B rest hB ih =>
      have hrestCount : rest.card ≤ r := by
        calc
          rest.card ≤ (insert B rest).card := Finset.card_le_card (Finset.subset_insert B rest)
          _ ≤ r := hcount
      have hrestBundles : ∀ C ∈ rest, C ⊆ items := by
        intro C hC
        exact hbundles C (Finset.mem_insert_of_mem hC)
      have hrestSpread : ∀ C ∈ rest, r * q ≤ (C.image group).card := by
        intro C hC
        exact hspread C (Finset.mem_insert_of_mem hC)
      rcases ih hrestBundles hrestCount hrestSpread with
        ⟨old, hold, holdCard, holdBundles⟩
      let available := B.image group \ old.image group
      have hqAvailable : q ≤ available.card := by
        have hBSpread : r * q ≤ (B.image group).card := hspread B (by simp)
        have hinsertCard : rest.card + 1 ≤ r := by
          simpa [Finset.card_insert_of_notMem hB] using hcount
        have holdImageCard : (old.image group).card = old.card :=
          Finset.card_image_of_injOn hold.2
        have hinterCard : (old.image group ∩ B.image group).card ≤
            (old.image group).card :=
          Finset.card_le_card Finset.inter_subset_left
        rw [Finset.card_sdiff]
        apply Nat.le_sub_of_add_le
        calc
          q + (old.image group ∩ B.image group).card ≤
              q + (old.image group).card := Nat.add_le_add_left hinterCard q
          _ = (rest.card + 1) * q := by
            rw [holdImageCard, holdCard, Nat.add_mul]
            omega
          _ ≤ r * q := Nat.mul_le_mul_right q hinsertCard
          _ ≤ (B.image group).card := hBSpread
      rcases Finset.exists_subset_card_eq hqAvailable with
        ⟨newGroups, hnewGroups, hnewGroupsCard⟩
      have hnewGroupsB : newGroups ⊆ B.image group :=
        hnewGroups.trans Finset.sdiff_subset
      rcases exists_partialGroupTransversal_image_eq B group newGroups hnewGroupsB with
        ⟨fresh, hfresh, hfreshImage⟩
      have hfreshItems : fresh ⊆ items := hfresh.1.trans (hbundles B (by simp))
      have himage : Disjoint (old.image group) (fresh.image group) := by
        rw [hfreshImage, Finset.disjoint_left]
        intro g hgold hgnew
        exact (Finset.mem_sdiff.mp (hnewGroups hgnew)).2 hgold
      have hdisjoint : Disjoint old fresh := disjoint_of_disjoint_image himage
      have hfreshCard : fresh.card = q := by
        calc
          fresh.card = (fresh.image group).card :=
            (Finset.card_image_of_injOn hfresh.2).symm
          _ = newGroups.card := congrArg Finset.card hfreshImage
          _ = q := hnewGroupsCard
      refine ⟨old ∪ fresh, ?_, ?_, ?_⟩
      · refine ⟨Finset.union_subset hold.1 hfreshItems, ?_⟩
        simpa only [Finset.coe_union] using
          injOn_union_of_disjoint_image hold.2 hfresh.2 himage
      · rw [Finset.card_union_of_disjoint hdisjoint, holdCard, hfreshCard,
          Finset.card_insert_of_notMem hB, Nat.add_mul]
        simp
      · intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hCrest
        · calc
            q = fresh.card := hfreshCard.symm
            _ ≤ ((old ∪ fresh) ∩ C).card := by
              apply Finset.card_le_card
              intro x hx
              exact Finset.mem_inter.mpr
                ⟨Finset.mem_union_right old hx, hfresh.1 hx⟩
        · exact (holdBundles C hCrest).trans (Finset.card_le_card (by
            intro x hx
            rcases Finset.mem_inter.mp hx with ⟨hxold, hxC⟩
            exact Finset.mem_inter.mpr ⟨Finset.mem_union_left fresh hxold, hxC⟩))

/-- Bounded group size converts a bundle-cardinality lower bound into the
spread hypothesis of the greedy theorem.  The conclusion retains `q` items in
each bundle, i.e. the cleared fraction encoded by
`maxGroupSize * r * q ≤ B.card`. -/
theorem exists_partialGroupTransversal_of_bounded_groups
    [DecidableEq Item] [DecidableEq Group]
    (items : Finset Item) (group : Item → Group)
    (bundles : Finset (Finset Item)) (maxGroupSize r q : ℕ)
    (hmax : 0 < maxGroupSize)
    (hbundles : ∀ B ∈ bundles, B ⊆ items)
    (hcount : bundles.card ≤ r)
    (hgroupSize : ∀ g ∈ items.image group,
      (items.filter fun x => group x = g).card ≤ maxGroupSize)
    (hbundleSize : ∀ B ∈ bundles,
      maxGroupSize * (r * q) ≤ B.card) :
    ∃ selected : Finset Item,
      IsPartialGroupTransversal items group selected ∧
        selected.card = bundles.card * q ∧
        ∀ B ∈ bundles, q ≤ (selected ∩ B).card := by
  apply exists_partialGroupTransversal_card_inter_bundle
    items group bundles r q hbundles hcount
  intro B hB
  have hfiber : ∀ g ∈ B.image group,
      (B.filter fun x => group x = g).card ≤ maxGroupSize := by
    intro g hg
    have hgItems : g ∈ items.image group := by
      rcases Finset.mem_image.mp hg with ⟨x, hxB, rfl⟩
      exact Finset.mem_image_of_mem group (hbundles B hB hxB)
    exact (Finset.card_le_card (by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxB, hxg⟩
      exact Finset.mem_filter.mpr ⟨hbundles B hB hxB, hxg⟩)).trans
        (hgroupSize g hgItems)
  have hcard := Finset.card_le_mul_card_image B maxGroupSize hfiber
  have hmul : maxGroupSize * (r * q) ≤
      maxGroupSize * (B.image group).card :=
    (hbundleSize B hB).trans hcard
  exact le_of_mul_le_mul_left hmul hmax

/-- The bounded-size simultaneous selection can be completed to exactly one
item from every represented group while preserving all bundle lower bounds. -/
theorem exists_exactGroupTransversal_of_bounded_groups
    [DecidableEq Item] [DecidableEq Group]
    (items : Finset Item) (group : Item → Group)
    (bundles : Finset (Finset Item)) (maxGroupSize r q : ℕ)
    (hmax : 0 < maxGroupSize)
    (hbundles : ∀ B ∈ bundles, B ⊆ items)
    (hcount : bundles.card ≤ r)
    (hgroupSize : ∀ g ∈ items.image group,
      (items.filter fun x => group x = g).card ≤ maxGroupSize)
    (hbundleSize : ∀ B ∈ bundles,
      maxGroupSize * (r * q) ≤ B.card) :
    ∃ selected : Finset Item,
      IsExactGroupTransversal items group selected ∧
        ∀ B ∈ bundles, q ≤ (selected ∩ B).card := by
  rcases exists_partialGroupTransversal_of_bounded_groups
      items group bundles maxGroupSize r q hmax hbundles hcount
      hgroupSize hbundleSize with
    ⟨initial, hinitial, _hcard, hretained⟩
  rcases hinitial.exists_exact_superset with ⟨selected, hexact, hsubset⟩
  refine ⟨selected, hexact, ?_⟩
  intro B hB
  exact (hretained B hB).trans (Finset.card_le_card (by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxpartial, hxB⟩
    exact Finset.mem_inter.mpr ⟨hsubset hxpartial, hxB⟩))

end ChekuriChuzhoySection5Selection
end SimpleGraph

end Lax17Proofs
