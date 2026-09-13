import Lax17Proofs.Source.Exponent8.DyadicClusterClass
import Mathlib.Data.Finset.Sort

namespace Lax17Proofs

/-!
# Parent-ordered happy-cluster tables

The happy clusters retained in Chuzhoy--Tan Section 5.1 are occurrences:
the same original row may contribute one segment in several parent slices.
This module first tags every cluster by its parent slice, then orders the
tagged family lexicographically by parent and an injective tie-breaker.
After restricting to the dyadic class, numerical order in the resulting
`Fin C` table is therefore compatible with parent-slice order.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

open Finset
open Section44

/-- A finite family enumerated so that its parent indices are monotone. -/
structure ParentOrderedEnumeration
    {m : ℕ} (Flat : Type v) [Fintype Flat]
    (parent : Flat → Fin m) where
  count : ℕ
  count_eq : count = Fintype.card Flat
  entry : Fin count ≃ Flat
  parent_monotone : Monotone fun i => parent (entry i)

/-- Sort a finite family first by parent and then by an arbitrary injective
tie rank.  The tie rank is used only to make the lifted order linear. -/
noncomputable def parentOrderedEnumeration
    {m : ℕ} (Flat : Type v) [Fintype Flat]
    (parent : Flat → Fin m) :
    ParentOrderedEnumeration Flat parent := by
  classical
  let tie : Flat ≃ Fin (Fintype.card Flat) := Fintype.equivFin Flat
  let key : Flat → Lex (ℕ × ℕ) :=
    fun c => toLex ((parent c).1, (tie c).1)
  have hkey : Function.Injective key := by
    intro a b hab
    have hab' :
        ((parent a).1, (tie a).1) =
          ((parent b).1, (tie b).1) :=
      congrArg ofLex hab
    apply tie.injective
    apply Fin.ext
    exact congrArg Prod.snd hab'
  letI : LinearOrder Flat := LinearOrder.lift' key hkey
  let e : Fin (Fintype.card Flat) ≃o Flat :=
    Fintype.orderIsoFinOfCardEq Flat rfl
  refine
    { count := Fintype.card Flat
      count_eq := rfl
      entry := e.toEquiv
      parent_monotone := ?_ }
  intro a b hab
  have habKey : key (e a) ≤ key (e b) :=
    e.monotone hab
  change parent (e a) ≤ parent (e b)
  by_contra hparent
  have hparent' : (parent (e b)).1 < (parent (e a)).1 := by
    omega
  have hkeyRev : key (e b) < key (e a) := by
    exact Prod.Lex.left _ _ hparent'
  exact (not_lt_of_ge habKey) hkeyRev

namespace RecursiveSliceLayer

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width g : ℕ}

/-- The same additive cleanup, with `32*g^4` written in the exact
`2*(16*g^4)` form consumed by Theorem 4.11. -/
noncomputable def happyCleanup
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (i : Fin m) :
    AdditiveSliceCleanup (Qbar := Qbar) L.sigma i
      (4 * (g ^ 2)) (2 * (16 * g ^ 4)) := by
  let O := L.cleanup i
  refine
    { rows := O.rows
      paths := O.paths
      rows_subset := O.rows_subset
      paths_subset := O.paths_subset
      intersecting := ?_
      half_paths := O.half_paths
      discarded_rows_sparse := O.discarded_rows_sparse
      additive_loss := ?_ }
  · simpa only [show 2 * (16 * g ^ 4) = 32 * g ^ 4 by ring] using
      O.intersecting
  · simpa only [show 2 * (16 * g ^ 4) = 32 * g ^ 4 by ring] using
      O.additive_loss

@[simp] theorem happyCleanup_rows
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (i : Fin m) :
    (L.happyCleanup i).rows = (L.cleanup i).rows := by
  simp [happyCleanup]

@[simp] theorem happyCleanup_paths
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (i : Fin m) :
    (L.happyCleanup i).paths = (L.cleanup i).paths := by
  simp [happyCleanup]

end RecursiveSliceLayer

/-- The clusters in one corrected dyadic class, ordered by their actual
parent slices.  Rows retain their original `Rbar.Index` names. -/
structure ParentedHappyClusterTable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    {m width g : ℕ}
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (C Dclass : ℕ) where
  parent : Fin C → Fin m
  parent_monotone : Monotone parent
  cluster : Fin C → Finset W
  rows : Fin C → Finset Rbar.Index
  cluster_connected : ∀ c, IsCluster H (cluster c)
  cluster_disjoint :
    Pairwise fun c d => Disjoint (cluster c) (cluster d)
  rows_same_parent_disjoint :
    ∀ {c d}, c ≠ d → parent c = parent d →
      Disjoint (rows c) (rows d)
  cluster_subset_support :
    ∀ c,
      cluster c ⊆
        L.sigma.cleanedSupportVertexSet Qbar (parent c)
          (L.happyCleanup (parent c)).toOrdinary
  rows_subset_cleanup :
    ∀ c, rows c ⊆ (L.happyCleanup (parent c)).rows
  row_card : ∀ c, Dclass ≤ (rows c).card
  row_path_contained :
    ∀ c r, r ∈ rows c →
      ((L.sigma.sliceRowPacking (parent c)).path r).vertexSet ⊆
        cluster c
  weak :
    ∀ c,
      WeakEdgeWellLinkedIn H (cluster c)
        ((rows c).image
            (fun r =>
              ((L.sigma.sliceRowPacking (parent c)).path r).source) ∪
          (rows c).image
            (fun r =>
              ((L.sigma.sliceRowPacking (parent c)).path r).target))
        (g ^ 2)
  depth_base : 16 * g ^ 4 ≤ Dclass
  class_mass :
    4 * Rbar.card * g ^ 2 ≤ ∑ c : Fin C, (rows c).card
  count_mass :
    2 * Rbar.card * g ^ 2 ≤ Dclass * C

namespace ParentedHappyClusterTable

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width g C Dclass : ℕ}
    {L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4)}

/-- Cluster row sets in the common `Fin Rbar.card` indexing used by
Theorem 4.15. -/
noncomputable def sliceRows
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) : Finset (Fin Rbar.card) :=
  (T.rows c).image Rbar.finIndexEquiv.symm

noncomputable def leftEndpoint
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) (r : Fin Rbar.card) : W :=
  ((L.sigma.sliceRowPacking (T.parent c)).path
    (Rbar.finIndexEquiv r)).source

noncomputable def rightEndpoint
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) (r : Fin Rbar.card) : W :=
  ((L.sigma.sliceRowPacking (T.parent c)).path
    (Rbar.finIndexEquiv r)).target

theorem mem_sliceRows_iff
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) (r : Fin Rbar.card) :
    r ∈ T.sliceRows c ↔ Rbar.finIndexEquiv r ∈ T.rows c := by
  classical
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨s, hs, rfl⟩
    simpa using hs
  · intro hr
    exact Finset.mem_image.2
      ⟨Rbar.finIndexEquiv r, hr,
        Rbar.finIndexEquiv.symm_apply_apply r⟩

@[simp] theorem sliceRows_card
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) :
    (T.sliceRows c).card = (T.rows c).card :=
  Finset.card_image_of_injective _ Rbar.finIndexEquiv.symm.injective

theorem leftEndpoint_injective
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) :
    Function.Injective (T.leftEndpoint c) :=
  (L.sigma.sliceRowPath_source_injective (T.parent c)).comp
    Rbar.finIndexEquiv.injective

theorem rightEndpoint_injective
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) :
    Function.Injective (T.rightEndpoint c) :=
  (L.sigma.sliceRowPath_target_injective (T.parent c)).comp
    Rbar.finIndexEquiv.injective

theorem leftEndpoint_mem
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) {r : Fin Rbar.card} (hr : r ∈ T.sliceRows c) :
    T.leftEndpoint c r ∈ T.cluster c :=
  T.row_path_contained c _ ((T.mem_sliceRows_iff c r).1 hr)
    (GraphPath.source_mem_vertexSet _)

theorem rightEndpoint_mem
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) {r : Fin Rbar.card} (hr : r ∈ T.sliceRows c) :
    T.rightEndpoint c r ∈ T.cluster c :=
  T.row_path_contained c _ ((T.mem_sliceRows_iff c r).1 hr)
    (GraphPath.target_mem_vertexSet _)

theorem endpoint_union_weak
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (c : Fin C) (leftRows rightRows : Finset (Fin Rbar.card))
    (hleft : leftRows ⊆ T.sliceRows c)
    (hright : rightRows ⊆ T.sliceRows c) :
    WeakEdgeWellLinkedIn H (T.cluster c)
      (leftRows.image (T.leftEndpoint c) ∪
        rightRows.image (T.rightEndpoint c)) (g ^ 2) := by
  apply WeakEdgeWellLinkedIn.mono_terminals (T.weak c)
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · apply Finset.mem_union_left
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    exact Finset.mem_image.2
      ⟨Rbar.finIndexEquiv r,
        (T.mem_sliceRows_iff c r).1 (hleft hr), rfl⟩
  · apply Finset.mem_union_right
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    exact Finset.mem_image.2
      ⟨Rbar.finIndexEquiv r,
        (T.mem_sliceRows_iff c r).1 (hright hr), rfl⟩

/-- Positive overlap of two table entries forces strict order of their
actual parent slices.  Equality is impossible because distinct happy
clusters in one parent have disjoint row-index sets. -/
theorem parent_lt_of_largeOverlap
    (T : ParentedHappyClusterTable Rbar Qbar L C Dclass)
    (hg : 0 < g)
    {c d : Fin C}
    (hrel : Section45.LargeOverlapRel T.sliceRows (g ^ 2) c d) :
    T.parent c < T.parent d := by
  have hle : T.parent c ≤ T.parent d :=
    T.parent_monotone hrel.1.le
  have hne : T.parent c ≠ T.parent d := by
    intro hparent
    have hdisj :=
      T.rows_same_parent_disjoint (ne_of_lt hrel.1) hparent
    have hpos : 0 < (T.sliceRows c ∩ T.sliceRows d).card :=
      lt_of_lt_of_le (by positivity : 0 < g ^ 2) hrel.2
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
    have hrc : Rbar.finIndexEquiv r ∈ T.rows c :=
      (T.mem_sliceRows_iff c r).1 (Finset.mem_inter.mp hr).1
    have hrd : Rbar.finIndexEquiv r ∈ T.rows d :=
      (T.mem_sliceRows_iff d r).1 (Finset.mem_inter.mp hr).2
    exact Finset.disjoint_left.mp hdisj hrc hrd
  exact lt_of_le_of_ne hle hne

end ParentedHappyClusterTable

namespace RecursiveSliceLayer

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width g rowCap : ℕ}

/-- Chuzhoy--Tan Section 5.1, Steps 4--5, through geometric grouping:
all happy-cluster occurrences from the majority-large slices are tagged,
ordered by their parent slice, and restricted to one corrected dyadic class.
-/
theorem exists_parentedHappyClusterTable_of_largeSliceMass
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) (32 * g ^ 4))
    (Large : LargeSliceLayer L rowCap)
    (hintersects : PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hNupper : Rbar.card ≤ 64 * g ^ 6)
    (hinputMass :
      32 * Rbar.card * g ^ 2 * (Nat.log 2 g + 1) ≤
        ∑ i ∈ Large.large, (L.cleanup i).rows.card) :
    ∃ C Dclass : ℕ,
      Nonempty (ParentedHappyClusterTable Rbar Qbar L C Dclass) := by
  classical
  have hw : 0 < g ^ 2 := by positivity
  have hD : 0 < 16 * g ^ 4 := by positivity
  have hscale : 8 * g ^ 2 ≤ 16 * g ^ 4 := by
    calc
      8 * g ^ 2 ≤ 16 * g ^ 2 :=
        Nat.mul_le_mul_right (g ^ 2) (by omega)
      _ ≤ 16 * g ^ 4 :=
        Nat.mul_le_mul_left 16
          (Nat.pow_le_pow_right (by omega) (by omega))
  let LargeIndex := {i : Fin m // i ∈ Large.large}
  let Happy :
      ∀ i : LargeIndex,
        AllHappyClustersData Rbar Qbar L.sigma i.1
          (L.happyCleanup i.1) :=
    fun i =>
      SimpleGraph.Exponent8.PathSlicing.allHappyClusters_of_additiveCleanup
        (L.happyCleanup i.1) hw hD hscale
  let Flat := Σ i : LargeIndex, (Happy i).ClusterIndex
  let flatParent : Flat → Fin m := fun c => c.1.1
  let flatRows : Flat → Finset Rbar.Index :=
    fun c => (Happy c.1).rows c.2
  let flatCluster : Flat → Finset W :=
    fun c => (Happy c.1).cluster c.2
  have hsliceMass :
      32 * Rbar.card * g ^ 2 * (Nat.log 2 g + 1) ≤
        ∑ i : LargeIndex, (L.cleanup i.1).rows.card := by
    rw [Finset.sum_subtype Large.large (fun i => Iff.rfl)] at hinputMass
    exact hinputMass
  have hquarter :
      (∑ i : LargeIndex, (L.cleanup i.1).rows.card) ≤
        4 * ∑ c : Flat, (flatRows c).card := by
    calc
      (∑ i : LargeIndex, (L.cleanup i.1).rows.card)
          ≤ ∑ i : LargeIndex,
              4 * ∑ c : (Happy i).ClusterIndex,
                ((Happy i).rows c).card := by
            apply Finset.sum_le_sum
            intro i _hi
            simpa using (Happy i).quarter_mass
      _ = 4 * ∑ i : LargeIndex,
              ∑ c : (Happy i).ClusterIndex,
                ((Happy i).rows c).card := by
            rw [Finset.mul_sum]
      _ = 4 * ∑ c : Flat, (flatRows c).card := by
            rw [Fintype.sum_sigma]
  have hhappyMass :
      8 * Rbar.card * g ^ 2 * (Nat.log 2 g + 1) ≤
        ∑ c : Flat, (flatRows c).card := by
    apply Nat.le_of_mul_le_mul_left
      (by
        calc
          4 * (8 * Rbar.card * g ^ 2 *
                (Nat.log 2 g + 1)) =
              32 * Rbar.card * g ^ 2 *
                (Nat.log 2 g + 1) := by ring
          _ ≤ ∑ i : LargeIndex, (L.cleanup i.1).rows.card :=
            hsliceMass
          _ ≤ 4 * ∑ c : Flat, (flatRows c).card := hquarter)
      (by omega)
  let E := parentOrderedEnumeration Flat flatParent
  let size : Fin E.count → ℕ :=
    fun c => (flatRows (E.entry c)).card
  have hsizeLower :
      ∀ c : Fin E.count, 16 * g ^ 4 ≤ size c := by
    intro c
    exact (Happy (E.entry c).1).row_card (E.entry c).2
  have hsizeUpper :
      ∀ c : Fin E.count, size c ≤ Rbar.card := by
    intro c
    calc
      size c ≤ (Finset.univ : Finset Rbar.Index).card :=
        Finset.card_le_card (fun _ _ => Finset.mem_univ _)
      _ = Rbar.card := by simp [PerfectPathPacking.card, PathPacking.card]
  have horderedMass :
      8 * Rbar.card * g ^ 2 * (Nat.log 2 g + 1) ≤
        ∑ c : Fin E.count, size c := by
    change
      8 * Rbar.card * g ^ 2 * (Nat.log 2 g + 1) ≤
        ∑ c : Fin E.count, (flatRows (E.entry c)).card
    rw [E.entry.sum_comp (fun c => (flatRows c).card)]
    exact hhappyMass
  let D :=
    exists_dyadicClusterClass size g Rbar.card
      hg hpow hsizeLower hsizeUpper hNupper horderedMass
  let classOrder :
      Fin D.members.card ≃o {c : Fin E.count // c ∈ D.members} :=
    D.members.orderIsoOfFin rfl
  let selected : Fin D.members.card → Flat :=
    fun c => E.entry (classOrder c).1
  have hselectedParentMonotone :
      Monotone fun c : Fin D.members.card =>
        flatParent (selected c) := by
    intro c d hcd
    apply E.parent_monotone
    exact (classOrder.monotone hcd)
  have hselectedInjective : Function.Injective selected := by
    intro c d hcd
    apply classOrder.injective
    apply Subtype.ext
    exact E.entry.injective hcd
  have hflatClusterDisjoint :
      Pairwise fun c d : Flat =>
        Disjoint (flatCluster c) (flatCluster d) := by
    rintro ⟨i, c⟩ ⟨j, d⟩ hne
    by_cases hij : i = j
    · subst j
      apply (Happy i).cluster_disjoint
      intro hcd
      apply hne
      exact Sigma.ext rfl (heq_of_eq hcd)
    · have hijVal : i.1 ≠ j.1 := by
        intro h
        exact hij (Subtype.ext h)
      exact
        (L.sigma.cleanedSupportVertexSet_disjoint
          Qbar hintersects hijVal
          (L.happyCleanup i.1).toOrdinary
          (L.happyCleanup j.1).toOrdinary hw).mono
          ((Happy i).cluster_subset_support c)
          ((Happy j).cluster_subset_support d)
  have hflatRowsSameParent :
      ∀ {c d : Flat}, c ≠ d →
        flatParent c = flatParent d →
          Disjoint (flatRows c) (flatRows d) := by
    rintro ⟨i, c⟩ ⟨j, d⟩ hne hparent
    have hij : i = j := Subtype.ext hparent
    subst j
    apply (Happy i).rows_pairwise_disjoint
    intro hcd
    apply hne
    exact Sigma.ext rfl (heq_of_eq hcd)
  refine ⟨D.members.card, dyadicClassDepth g D.j, ?_⟩
  exact ⟨{
    parent := fun c => flatParent (selected c)
    parent_monotone := hselectedParentMonotone
    cluster := fun c => flatCluster (selected c)
    rows := fun c => flatRows (selected c)
    cluster_connected := fun c =>
      (Happy (selected c).1).cluster_connected (selected c).2
    cluster_disjoint := by
      intro c d hcd
      apply hflatClusterDisjoint
      exact fun h => hcd (hselectedInjective h)
    rows_same_parent_disjoint := by
      intro c d hcd hp
      apply hflatRowsSameParent
      · exact fun h => hcd (hselectedInjective h)
      · exact hp
    cluster_subset_support := fun c =>
      (Happy (selected c).1).cluster_subset_support (selected c).2
    rows_subset_cleanup := fun c =>
      (Happy (selected c).1).rows_subset_cleanup (selected c).2
    row_card := by
      intro c
      exact D.lower (classOrder c).1 (classOrder c).2
    row_path_contained := fun c =>
      (Happy (selected c).1).row_path_contained (selected c).2
    weak := fun c => (Happy (selected c).1).weak (selected c).2
    depth_base := by
      dsimp [dyadicClassDepth]
      exact Nat.le_mul_of_pos_right _
        (pow_pos (by omega : 0 < 2) D.j.1)
    class_mass := by
      calc
        4 * Rbar.card * g ^ 2
            ≤ ∑ c ∈ D.members, size c := D.mass
        _ = ∑ c : {c : Fin E.count // c ∈ D.members}, size c.1 := by
          exact
            Finset.sum_subtype D.members (fun _ => Iff.rfl) size
        _ = ∑ c : Fin D.members.card, size (classOrder c).1 := by
          exact (classOrder.toEquiv.sum_comp fun c => size c.1).symm
    count_mass := D.count_mass
  }⟩

end RecursiveSliceLayer

end Exponent8
end SimpleGraph

end Lax17Proofs
