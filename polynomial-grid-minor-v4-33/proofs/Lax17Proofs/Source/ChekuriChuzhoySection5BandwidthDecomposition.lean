import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic
import Lax17Proofs.Source.ChekuriChuzhoySection5BandwidthAmortization
import Lax17Proofs.Source.ChekuriChuzhoySection5Clustering

namespace Lax17Proofs

universe u v w

/-!
# Finite truncated-bandwidth decompositions

This file supplies the terminating base of the bandwidth-decomposition
arguments in Chekuri--Chuzhoy journal Section 5.2.  A decomposition is a
finite partition of a prescribed cluster in which every part satisfies the
paper's truncated bandwidth predicate.  Such decompositions are never an
input assumption: the discrete partition into singletons is a concrete
candidate.

The quantitative cut budget used to select a source-faithful minimum
decomposition is developed on top of this existence theorem.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5BandwidthDecomposition


open Finset
open ChekuriChuzhoySection5Clustering

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A partition of `C` all of whose parts have the requested truncated
bandwidth. -/
def IsBandwidthDecomposition
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : Nat) (P : Finpartition C) : Prop :=
  ∀ U ∈ P.parts,
    TruncatedScaledBandwidth G U cap alphaNum alphaDen

/-- A singleton has every valid truncated bandwidth ratio.  Every partition
of a singleton has an empty side, so its truncated interface demand is zero. -/
theorem truncatedScaledBandwidth_singleton
    (G : _root_.SimpleGraph V) (v : V)
    (cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    TruncatedScaledBandwidth G {v} cap alphaNum alphaDen := by
  refine ⟨hnum, hratio, ?_⟩
  intro X Y hX hY hcover hdisjoint
  have hXcases : X = ∅ ∨ X = {v} := by
    simpa [Finset.subset_singleton_iff] using hX
  have hYcases : Y = ∅ ∨ Y = {v} := by
    simpa [Finset.subset_singleton_iff] using hY
  rcases hXcases with rfl | rfl <;>
    rcases hYcases with rfl | rfl
  · simp at hcover
  · simp [truncatedInterfaceDemand]
  · simp [truncatedInterfaceDemand]
  · simp at hdisjoint

/-- The discrete partition is a concrete bandwidth decomposition of every
finite cluster. -/
theorem discrete_isBandwidthDecomposition
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    IsBandwidthDecomposition G C cap alphaNum alphaDen
      (⊥ : Finpartition C) := by
  intro U hU
  rw [Finpartition.mem_bot_iff] at hU
  rcases hU with ⟨v, _hv, rfl⟩
  exact truncatedScaledBandwidth_singleton
    G v cap alphaNum alphaDen hnum hratio

/-- Every finite cluster admits a truncated-bandwidth decomposition. -/
theorem exists_bandwidthDecomposition
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    ∃ P : Finpartition C,
      IsBandwidthDecomposition G C cap alphaNum alphaDen P :=
  ⟨⊥, discrete_isBandwidthDecomposition
    G C cap alphaNum alphaDen hnum hratio⟩

/-! ## Boundary bookkeeping for one recursive split -/

@[simp] theorem mk_mem_clusterBoundary_iff
    (G : _root_.SimpleGraph V) (C : Finset V) (u v : V) :
    s(u, v) ∈ Section44.clusterBoundary G C ↔
      G.Adj u v ∧
        ((u ∈ C ∧ v ∉ C) ∨ (v ∈ C ∧ u ∉ C)) := by
  classical
  rw [Section44.clusterBoundary,
    Section44.mem_edgeBoundary (G := G) C (Finset.univ \ C)]
  simp only [_root_.SimpleGraph.mem_edgeSet, Sym2.eq_iff,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨huv, x, hx, y, hy, hxy⟩
    rcases hxy with hxy | hxy
    · exact ⟨huv, Or.inl ⟨hxy.1 ▸ hx, hxy.2 ▸ hy⟩⟩
    · exact ⟨huv, Or.inr ⟨hxy.2 ▸ hx, hxy.1 ▸ hy⟩⟩
  · rintro ⟨huv, h | h⟩
    · exact ⟨huv, u, h.1, v, h.2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨huv, v, h.1, u, h.2,
        Or.inr ⟨rfl, rfl⟩⟩

@[simp] theorem mk_mem_edgeBoundary_iff
    (G : _root_.SimpleGraph V) (X Y : Finset V) (u v : V) :
    s(u, v) ∈ Section44.edgeBoundary G X Y ↔
      G.Adj u v ∧
        ((u ∈ X ∧ v ∈ Y) ∨ (v ∈ X ∧ u ∈ Y)) := by
  classical
  rw [Section44.mem_edgeBoundary (G := G) X Y]
  simp only [_root_.SimpleGraph.mem_edgeSet, Sym2.eq_iff]
  constructor
  · rintro ⟨huv, x, hx, y, hy, hxy⟩
    rcases hxy with hxy | hxy
    · exact ⟨huv, Or.inl ⟨hxy.1 ▸ hx, hxy.2 ▸ hy⟩⟩
    · exact ⟨huv, Or.inr ⟨hxy.2 ▸ hx, hxy.1 ▸ hy⟩⟩
  · rintro ⟨huv, h | h⟩
    · exact ⟨huv, u, h.1, v, h.2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨huv, v, h.1, u, h.2,
        Or.inr ⟨rfl, rfl⟩⟩

/-- Splitting a cluster into two disjoint sides replaces its outer boundary by
the union of the two child boundaries, with the cut edges added. -/
theorem clusterBoundary_union_split
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) :
    Section44.clusterBoundary G X ∪ Section44.clusterBoundary G Y =
      Section44.clusterBoundary G C ∪ Section44.edgeBoundary G X Y := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [Finset.mem_union, mk_mem_clusterBoundary_iff,
        mk_mem_edgeBoundary_iff]
      have hmemC (z : V) : z ∈ C ↔ z ∈ X ∨ z ∈ Y := by
        rw [← hcover]
        simp
      have hXY : ∀ {z : V}, z ∈ X → z ∈ Y → False := by
        intro z hzX hzY
        exact Finset.disjoint_left.mp hdisjoint hzX hzY
      rw [hmemC u, hmemC v]
      by_cases huX : u ∈ X <;>
        by_cases hvX : v ∈ X <;>
          by_cases huY : u ∈ Y <;>
            by_cases hvY : v ∈ Y <;> simp_all

/-- The overlap of the two child boundaries is exactly their mutual cut. -/
theorem clusterBoundary_inter_split
    {C X Y : Finset V} (_hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) :
    Section44.clusterBoundary G X ∩ Section44.clusterBoundary G Y =
      Section44.edgeBoundary G X Y := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [Finset.mem_inter, mk_mem_clusterBoundary_iff,
        mk_mem_edgeBoundary_iff]
      have hXY : ∀ {z : V}, z ∈ X → z ∈ Y → False := by
        intro z hzX hzY
        exact Finset.disjoint_left.mp hdisjoint hzX hzY
      by_cases huX : u ∈ X <;>
        by_cases hvX : v ∈ X <;>
          by_cases huY : u ∈ Y <;>
            by_cases hvY : v ∈ Y <;> simp_all

/-- A cut internal to `C` cannot also be an edge leaving `C`. -/
theorem clusterBoundary_disjoint_edgeBoundary_split
    {C X Y : Finset V} (hcover : X ∪ Y = C) :
    Disjoint (Section44.clusterBoundary G C)
      (Section44.edgeBoundary G X Y) := by
  classical
  rw [Finset.disjoint_left]
  intro e heOuter heCut
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mk_mem_clusterBoundary_iff] at heOuter
      simp only [mk_mem_edgeBoundary_iff] at heCut
      have hXC : X ⊆ C := by
        rw [← hcover]
        exact Finset.subset_union_left
      have hYC : Y ⊆ C := by
        rw [← hcover]
        exact Finset.subset_union_right
      have huC : u ∈ C := by
        rcases heCut.2 with h | h
        · exact hXC h.1
        · exact hYC h.2
      have hvC : v ∈ C := by
        rcases heCut.2 with h | h
        · exact hYC h.2
        · exact hXC h.1
      exact heOuter.2.elim (fun h => h.2 hvC) (fun h => h.2 huC)

/-- Exact boundary accounting for one recursive split.  Every outer boundary
edge occurs in one child boundary, while every cut edge occurs in both. -/
theorem clusterBoundary_card_add_split
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) :
    (Section44.clusterBoundary G X).card +
        (Section44.clusterBoundary G Y).card =
      (Section44.clusterBoundary G C).card +
        2 * (Section44.edgeBoundary G X Y).card := by
  classical
  have hunion := congrArg Finset.card
    (clusterBoundary_union_split (G := G) hcover hdisjoint)
  have hinter := congrArg Finset.card
    (clusterBoundary_inter_split (G := G) hcover hdisjoint)
  have hleft := Finset.card_union_add_card_inter
    (Section44.clusterBoundary G X) (Section44.clusterBoundary G Y)
  have hright := Finset.card_union_of_disjoint
    (clusterBoundary_disjoint_edgeBoundary_split (G := G) hcover)
  omega

/-! ## Boundary mass inherited by the two children -/

/-- One chosen edge witnessing that an interface vertex sees outside `C`. -/
noncomputable def interfaceBoundaryEdge
    (G : _root_.SimpleGraph V) (C : Finset V)
    (v : {v : V // v ∈ interfaceVertices G C}) : Sym2 V :=
  s(v.1, Classical.choose (mem_interfaceVertices.mp v.2).2)

theorem interfaceBoundaryEdge_neighbor_not_mem
    (G : _root_.SimpleGraph V) (C : Finset V)
    (v : {v : V // v ∈ interfaceVertices G C}) :
    Classical.choose (mem_interfaceVertices.mp v.2).2 ∉ C :=
  (Classical.choose_spec (mem_interfaceVertices.mp v.2).2).1

theorem interfaceBoundaryEdge_adj
    (G : _root_.SimpleGraph V) (C : Finset V)
    (v : {v : V // v ∈ interfaceVertices G C}) :
    G.Adj v.1 (Classical.choose (mem_interfaceVertices.mp v.2).2) :=
  (Classical.choose_spec (mem_interfaceVertices.mp v.2).2).2

theorem interfaceBoundaryEdge_injective
    (G : _root_.SimpleGraph V) (C : Finset V) :
    Function.Injective (interfaceBoundaryEdge G C) := by
  intro a b hab
  have haC := (mem_interfaceVertices.mp a.2).1
  have hbC := (mem_interfaceVertices.mp b.2).1
  have haOut := interfaceBoundaryEdge_neighbor_not_mem G C a
  have hbOut := interfaceBoundaryEdge_neighbor_not_mem G C b
  change s(a.1, Classical.choose (mem_interfaceVertices.mp a.2).2) =
    s(b.1, Classical.choose (mem_interfaceVertices.mp b.2).2) at hab
  rcases Sym2.eq_iff.mp hab with h | h
  · exact Subtype.ext h.1
  · exact False.elim <| hbOut (h.1 ▸ haC)

/-- The old outer-boundary edges inherited by `X` after cutting it from `Y`.
The mutual cut itself is removed. -/
noncomputable def inheritedBoundary
    (G : _root_.SimpleGraph V) (X Y : Finset V) : Finset (Sym2 V) :=
  Section44.clusterBoundary G X \ Section44.edgeBoundary G X Y

@[simp] theorem mk_mem_inheritedBoundary_iff
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) (u v : V) :
    s(u, v) ∈ inheritedBoundary G X Y ↔
      G.Adj u v ∧
        ((u ∈ X ∧ v ∉ C) ∨ (v ∈ X ∧ u ∉ C)) := by
  classical
  simp only [inheritedBoundary, Finset.mem_sdiff,
    mk_mem_clusterBoundary_iff, mk_mem_edgeBoundary_iff]
  have hmemC (z : V) : z ∈ C ↔ z ∈ X ∨ z ∈ Y := by
    rw [← hcover]
    simp
  have hXY : ∀ {z : V}, z ∈ X → z ∈ Y → False := by
    intro z hzX hzY
    exact Finset.disjoint_left.mp hdisjoint hzX hzY
  rw [hmemC u, hmemC v]
  by_cases huX : u ∈ X <;>
    by_cases hvX : v ∈ X <;>
      by_cases huY : u ∈ Y <;>
        by_cases hvY : v ∈ Y <;> simp_all

theorem edgeBoundary_subset_clusterBoundary_left
    {X Y : Finset V} (hdisjoint : Disjoint X Y) :
    Section44.edgeBoundary G X Y ⊆ Section44.clusterBoundary G X := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      rcases (mk_mem_edgeBoundary_iff G X Y u v).1 he with
        ⟨huv, h | h⟩
      · exact (mk_mem_clusterBoundary_iff G X u v).2
          ⟨huv, Or.inl ⟨h.1,
            fun hvX => Finset.disjoint_left.mp hdisjoint hvX h.2⟩⟩
      · exact (mk_mem_clusterBoundary_iff G X u v).2
          ⟨huv, Or.inr ⟨h.1,
            fun huX => Finset.disjoint_left.mp hdisjoint huX h.2⟩⟩

theorem inheritedBoundary_union_cut
    {X Y : Finset V} (hdisjoint : Disjoint X Y) :
    inheritedBoundary G X Y ∪ Section44.edgeBoundary G X Y =
      Section44.clusterBoundary G X :=
  Finset.sdiff_union_of_subset
    (edgeBoundary_subset_clusterBoundary_left (G := G) hdisjoint)

theorem inheritedBoundary_card_add_cut
    {X Y : Finset V} (hdisjoint : Disjoint X Y) :
    (inheritedBoundary G X Y).card +
        (Section44.edgeBoundary G X Y).card =
      (Section44.clusterBoundary G X).card := by
  calc
    (inheritedBoundary G X Y).card +
          (Section44.edgeBoundary G X Y).card =
        (inheritedBoundary G X Y ∪
          Section44.edgeBoundary G X Y).card :=
      (Finset.card_union_of_disjoint Finset.sdiff_disjoint).symm
    _ = (Section44.clusterBoundary G X).card := by
      rw [inheritedBoundary_union_cut (G := G) hdisjoint]

theorem inheritedBoundary_union
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) :
    inheritedBoundary G X Y ∪ inheritedBoundary G Y X =
      Section44.clusterBoundary G C := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [Finset.mem_union,
        mk_mem_inheritedBoundary_iff (G := G) hcover hdisjoint,
        mk_mem_inheritedBoundary_iff (G := G)
          (by simpa [Finset.union_comm] using hcover) hdisjoint.symm,
        mk_mem_clusterBoundary_iff]
      have hmemC (z : V) : z ∈ C ↔ z ∈ X ∨ z ∈ Y := by
        rw [← hcover]
        simp
      have hXY : ∀ {z : V}, z ∈ X → z ∈ Y → False := by
        intro z hzX hzY
        exact Finset.disjoint_left.mp hdisjoint hzX hzY
      rw [hmemC u, hmemC v]
      by_cases huX : u ∈ X <;>
        by_cases hvX : v ∈ X <;>
          by_cases huY : u ∈ Y <;>
            by_cases hvY : v ∈ Y <;> simp_all

theorem inheritedBoundary_disjoint
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) :
    Disjoint (inheritedBoundary G X Y) (inheritedBoundary G Y X) := by
  classical
  rw [Finset.disjoint_left]
  intro e heX heY
  induction e using Sym2.inductionOn with
  | _ u v =>
      rcases (mk_mem_inheritedBoundary_iff (G := G)
        hcover hdisjoint u v).1 heX with ⟨_, hX⟩
      rcases (mk_mem_inheritedBoundary_iff (G := G)
        (by simpa [Finset.union_comm] using hcover)
        hdisjoint.symm u v).1 heY with ⟨_, hY⟩
      rcases hX with hX | hX <;> rcases hY with hY | hY
      · exact Finset.disjoint_left.mp hdisjoint hX.1 hY.1
      · exact hY.2 (hcover ▸ Finset.mem_union_left _ hX.1)
      · exact hX.2 (hcover ▸ Finset.mem_union_right _ hY.1)
      · exact Finset.disjoint_left.mp hdisjoint hX.1 hY.1

theorem inheritedBoundary_card_add
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) :
    (inheritedBoundary G X Y).card +
        (inheritedBoundary G Y X).card =
      (Section44.clusterBoundary G C).card := by
  rw [← Finset.card_union_of_disjoint
    (inheritedBoundary_disjoint (G := G) hcover hdisjoint),
    inheritedBoundary_union (G := G) hcover hdisjoint]

/-- Interface vertices on one side inject into the inherited outer-boundary
edges on that side. -/
theorem inter_interfaceVertices_card_le_inheritedBoundary_card
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) :
    (X ∩ interfaceVertices G C).card ≤
      (inheritedBoundary G X Y).card := by
  classical
  let f :
      {v : V // v ∈ X ∩ interfaceVertices G C} →
        {e : Sym2 V // e ∈ inheritedBoundary G X Y} := fun v => by
    let v' : {v : V // v ∈ interfaceVertices G C} :=
      ⟨v.1, (Finset.mem_inter.mp v.2).2⟩
    refine ⟨interfaceBoundaryEdge G C v', ?_⟩
    apply (mk_mem_inheritedBoundary_iff (G := G)
      hcover hdisjoint v'.1
      (Classical.choose (mem_interfaceVertices.mp v'.2).2)).2
    exact ⟨interfaceBoundaryEdge_adj G C v',
      Or.inl ⟨(Finset.mem_inter.mp v.2).1,
        interfaceBoundaryEdge_neighbor_not_mem G C v'⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hv :
        (⟨a.1, (Finset.mem_inter.mp a.2).2⟩ :
            {v : V // v ∈ interfaceVertices G C}) =
          ⟨b.1, (Finset.mem_inter.mp b.2).2⟩ :=
      interfaceBoundaryEdge_injective G C
        (congrArg Subtype.val hab)
    exact congrArg
      (fun z : {v : V // v ∈ interfaceVertices G C} => z.1) hv
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

theorem truncatedInterfaceDemand_le_inheritedBoundary_left
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) (cap : Nat) :
    truncatedInterfaceDemand G C X Y cap ≤
      (inheritedBoundary G X Y).card := by
  exact (Nat.min_le_left _ _).trans <|
    (Nat.min_le_left _ _).trans <|
      inter_interfaceVertices_card_le_inheritedBoundary_card
        (G := G) hcover hdisjoint

theorem truncatedInterfaceDemand_le_inheritedBoundary_right
    {C X Y : Finset V} (hcover : X ∪ Y = C)
    (hdisjoint : Disjoint X Y) (cap : Nat) :
    truncatedInterfaceDemand G C X Y cap ≤
      (inheritedBoundary G Y X).card := by
  rw [truncatedInterfaceDemand_comm]
  exact truncatedInterfaceDemand_le_inheritedBoundary_left
    (G := G) (by simpa [Finset.union_comm] using hcover)
      hdisjoint.symm cap

/-! ## The terminating recursive split tree -/

namespace ScaledViolatingPartition

variable {C : Finset V} {cap alphaNum alphaDen : Nat}

theorem left_nonempty
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    cut.X.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hX
  have hsparse := cut.sparse
  simp [hX, truncatedInterfaceDemand] at hsparse

theorem right_nonempty
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    cut.Y.Nonempty :=
  left_nonempty cut.swap

theorem left_card_lt
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    cut.X.card < C.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨cut.left_subset, ?_⟩
  intro hXC
  rcases right_nonempty cut with ⟨y, hyY⟩
  have hyC := cut.right_subset hyY
  have hyNotX : y ∉ cut.X := by
    intro hyX
    exact Finset.disjoint_left.mp cut.disjoint hyX hyY
  exact hyNotX (hXC.symm ▸ hyC)

theorem right_card_lt
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    cut.Y.card < C.card :=
  left_card_lt cut.swap

/-- The two sides of a violating cut, viewed as a two-part partition. -/
noncomputable def pairFinpartition
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen) :
    Finpartition C where
  parts := {cut.X, cut.Y}
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hne
    have hA' : A = cut.X ∨ A = cut.Y := by simpa using hA
    have hB' : B = cut.X ∨ B = cut.Y := by simpa using hB
    rcases hA' with rfl | rfl <;> rcases hB' with rfl | rfl
    · exact False.elim (hne rfl)
    · exact cut.disjoint
    · exact cut.disjoint.symm
    · exact False.elim (hne rfl)
  sup_parts := by
    simpa only [Finset.sup_insert, Finset.sup_singleton, id_eq] using cut.cover
  bot_notMem := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => (left_nonempty cut).ne_empty h.symm,
      fun h => (right_nonempty cut).ne_empty h.symm⟩

end ScaledViolatingPartition

/-- The finite binary history obtained by recursively splitting every part
that violates truncated bandwidth. -/
inductive BandwidthSplitTree
    (G : _root_.SimpleGraph V) (cap alphaNum alphaDen : Nat) :
    Finset V → Type u
  | leaf {C : Finset V} :
      TruncatedScaledBandwidth G C cap alphaNum alphaDen →
      BandwidthSplitTree G cap alphaNum alphaDen C
  | split {C : Finset V}
      (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
      (left : BandwidthSplitTree G cap alphaNum alphaDen cut.X)
      (right : BandwidthSplitTree G cap alphaNum alphaDen cut.Y) :
      BandwidthSplitTree G cap alphaNum alphaDen C

namespace BandwidthSplitTree

variable {cap alphaNum alphaDen : Nat} {C : Finset V}

/-- Recursively split a violating part.  Both recursive calls are on strict
subsets because a violating cut has positive demand on both sides. -/
noncomputable def build
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    BandwidthSplitTree G cap alphaNum alphaDen C := by
  classical
  exact
  if hband : TruncatedScaledBandwidth G C cap alphaNum alphaDen then
    .leaf hband
  else
    let cut := Classical.choice <|
      (not_truncatedScaledBandwidth_iff_exists_violating
        (G := G) (C := C) (cap := cap) hnum hratio).mp hband
    .split cut
      (build G cut.X cap alphaNum alphaDen hnum hratio)
      (build G cut.Y cap alphaNum alphaDen hnum hratio)
termination_by C.card
decreasing_by
  · exact ScaledViolatingPartition.left_card_lt cut
  · exact ScaledViolatingPartition.right_card_lt cut

/-- Refine the root two-part partition by the recursively constructed
partitions on its two sides. -/
noncomputable def combinePartitions
    {C : Finset V}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    (left : Finpartition cut.X) (right : Finpartition cut.Y) :
    Finpartition C :=
  ((ScaledViolatingPartition.pairFinpartition cut).bind fun A hA =>
    dite (A = cut.X)
      (fun h => h ▸ left)
      (fun h =>
        have hAY : A = cut.Y := by
          simp only [ScaledViolatingPartition.pairFinpartition] at hA
          exact Finset.mem_singleton.mp
            ((Finset.mem_insert.mp hA).resolve_left h)
        hAY ▸ right))

/-- The leaf partition represented by a split tree. -/
noncomputable def partition :
    {C : Finset V} →
      BandwidthSplitTree G cap alphaNum alphaDen C → Finpartition C
  | _, .leaf _ => ⊤
  | _, .split cut left right =>
      combinePartitions cut (partition left) (partition right)

theorem mem_combinePartitions_iff
    {C U : Finset V}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    (left : Finpartition cut.X) (right : Finpartition cut.Y) :
    U ∈ (combinePartitions cut left right).parts ↔
      U ∈ left.parts ∨ U ∈ right.parts := by
  classical
  rw [combinePartitions, Finpartition.mem_bind]
  constructor
  · rintro ⟨A, hA, hU⟩
    by_cases hAX : A = cut.X
    · subst A
      have hU' : U ∈ left.parts := by
        simpa only [dif_pos] using hU
      exact Or.inl hU'
    · have hAY : A = cut.Y := by
        simp only [ScaledViolatingPartition.pairFinpartition] at hA
        exact Finset.mem_singleton.mp
          ((Finset.mem_insert.mp hA).resolve_left hAX)
      subst A
      have hYX : cut.Y ≠ cut.X := by
        intro h
        rcases ScaledViolatingPartition.right_nonempty cut with ⟨y, hy⟩
        have hyX : y ∈ cut.X := h ▸ hy
        exact Finset.disjoint_left.mp cut.disjoint hyX hy
      simp only [dif_neg hYX] at hU
      exact Or.inr hU
  · intro hU
    rcases hU with hU | hU
    · refine ⟨cut.X, ?_, ?_⟩
      · simp [ScaledViolatingPartition.pairFinpartition]
      · simpa only [dif_pos rfl] using hU
    · refine ⟨cut.Y, ?_, ?_⟩
      · simp [ScaledViolatingPartition.pairFinpartition]
      · have hXY : cut.Y ≠ cut.X := by
          intro h
          rcases ScaledViolatingPartition.right_nonempty cut with ⟨y, hy⟩
          have hyX : y ∈ cut.X := h ▸ hy
          exact Finset.disjoint_left.mp cut.disjoint hyX hy
        simpa only [dif_neg hXY] using hU

/-- Every leaf of the recursive construction has the requested bandwidth. -/
theorem partition_bandwidth
    (tree : BandwidthSplitTree G cap alphaNum alphaDen C) :
    IsBandwidthDecomposition G C cap alphaNum alphaDen tree.partition := by
  induction tree with
  | leaf hband =>
      intro U hU
      change U ∈ (⊤ : Finpartition _).parts at hU
      have hUC : U = _ :=
        Finset.mem_singleton.mp
          (Finpartition.parts_top_subset _ hU)
      subst U
      exact hband
  | split cut left right ihLeft ihRight =>
      intro U hU
      rw [partition, mem_combinePartitions_iff] at hU
      exact hU.elim (ihLeft U) (ihRight U)

/-- Every leaf of a valid recursive bandwidth decomposition has boundary no
larger than the root boundary.  This is the "all resulting clusters are
small" assertion in journal Theorem 5.5.

At a split, the sparse-cut inequality and `alphaNum ≤ alphaDen` imply that
the new cut has size at most either inherited part of the old boundary.
Consequently each child boundary is at most the parent boundary. -/
theorem partition_part_boundary_card_le_root
    (tree : BandwidthSplitTree G cap alphaNum alphaDen C)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen)
    {U : Finset V} (hU : U ∈ tree.partition.parts) :
    (Section44.clusterBoundary G U).card ≤
      (Section44.clusterBoundary G C).card := by
  revert U
  let Bound :
      ∀ D : Finset V,
        BandwidthSplitTree G cap alphaNum alphaDen D → Prop :=
    fun D t => ∀ {U : Finset V}, U ∈ t.partition.parts →
      (Section44.clusterBoundary G U).card ≤
        (Section44.clusterBoundary G D).card
  change Bound C tree
  induction tree with
  | @leaf D hband =>
      intro U hU
      rw [partition] at hU
      have hUC : U = D :=
        Finset.mem_singleton.mp
          (Finpartition.parts_top_subset D hU)
      subst U
      exact le_rfl
  | @split C cut left right ihLeft ihRight =>
      intro U hU
      rw [partition, mem_combinePartitions_iff] at hU
      have hdenPos : 0 < alphaDen := lt_of_lt_of_le hnum hratio
      have hscaled :
          alphaDen *
              (Section44.edgeBoundary G cut.X cut.Y).card <
            alphaDen *
              (truncatedInterfaceDemand
                G C cut.X cut.Y cap) :=
        cut.sparse.trans_le
          (Nat.mul_le_mul_right
            (truncatedInterfaceDemand G C cut.X cut.Y cap) hratio)
      have hcutDemand :
          (Section44.edgeBoundary G cut.X cut.Y).card <
            truncatedInterfaceDemand G C cut.X cut.Y cap := by
        exact (Nat.mul_lt_mul_left hdenPos).mp hscaled
      have hleftInherited :
          truncatedInterfaceDemand G C cut.X cut.Y cap ≤
            (inheritedBoundary G cut.X cut.Y).card :=
        truncatedInterfaceDemand_le_inheritedBoundary_left
          (G := G) cut.cover cut.disjoint cap
      have hrightInherited :
          truncatedInterfaceDemand G C cut.X cut.Y cap ≤
            (inheritedBoundary G cut.Y cut.X).card :=
        truncatedInterfaceDemand_le_inheritedBoundary_right
          (G := G) cut.cover cut.disjoint cap
      have hroot :
          (inheritedBoundary G cut.X cut.Y).card +
              (inheritedBoundary G cut.Y cut.X).card =
            (Section44.clusterBoundary G C).card :=
        inheritedBoundary_card_add (G := G) cut.cover cut.disjoint
      have hleft :
          (Section44.clusterBoundary G cut.X).card ≤
            (Section44.clusterBoundary G C).card := by
        have hchild :=
          inheritedBoundary_card_add_cut (G := G) cut.disjoint
        omega
      have hright :
          (Section44.clusterBoundary G cut.Y).card ≤
            (Section44.clusterBoundary G C).card := by
        have hchild :=
          inheritedBoundary_card_add_cut
            (G := G) cut.disjoint.symm
        rw [Section44.edgeBoundary_comm] at hchild
        omega
      rcases hU with hU | hU
      · exact (ihLeft hU).trans hleft
      · exact (ihRight hU).trans hright

end BandwidthSplitTree

/-- Edges of `G` internal to `C` whose endpoints lie in different parts of
`P`. -/
noncomputable def crossingEdges
    (G : _root_.SimpleGraph V) (C : Finset V) (P : Finpartition C) :
    Finset (Sym2 V) := by
  classical
  exact (Section44.edgeBoundary G C C).filter <|
    Sym2.lift
      ⟨fun u v => P.part u ≠ P.part v, by
        intro u v
        exact propext ne_comm⟩

@[simp] theorem mk_mem_crossingEdges
    (G : _root_.SimpleGraph V) (C : Finset V)
    (P : Finpartition C) (u v : V) :
    s(u, v) ∈ crossingEdges G C P ↔
      G.Adj u v ∧ u ∈ C ∧ v ∈ C ∧ P.part u ≠ P.part v := by
  classical
  simp [crossingEdges, mk_mem_edgeBoundary_iff, and_left_comm,
    and_comm, and_assoc]

namespace BandwidthSplitTree

variable {cap alphaNum alphaDen : Nat} {C : Finset V}

/-- The union of all sparse cuts made in a recursive split history. -/
noncomputable def cutEdges :
    {C : Finset V} →
      BandwidthSplitTree G cap alphaNum alphaDen C → Finset (Sym2 V)
  | _, .leaf _ => ∅
  | _, .split cut left right =>
      (Section44.edgeBoundary G cut.X cut.Y ∪ cutEdges left) ∪
        cutEdges right

/-- The sum of the cardinalities of all cuts in the history. -/
noncomputable def totalCut :
    {C : Finset V} →
      BandwidthSplitTree G cap alphaNum alphaDen C → Nat
  | _, .leaf _ => 0
  | _, .split cut left right =>
      (Section44.edgeBoundary G cut.X cut.Y).card +
        totalCut left + totalCut right

theorem combinePartitions_part_eq_left
    {C : Finset V}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    (left : Finpartition cut.X) (right : Finpartition cut.Y)
    {u : V} (hu : u ∈ cut.X) :
    (combinePartitions cut left right).part u = left.part u := by
  apply (combinePartitions cut left right).part_eq_of_mem
  · exact (mem_combinePartitions_iff cut left right).2 <|
      Or.inl (left.part_mem.2 hu)
  · exact left.mem_part hu

theorem combinePartitions_part_eq_right
    {C : Finset V}
    (cut : ScaledViolatingPartition G C cap alphaNum alphaDen)
    (left : Finpartition cut.X) (right : Finpartition cut.Y)
    {u : V} (hu : u ∈ cut.Y) :
    (combinePartitions cut left right).part u = right.part u := by
  apply (combinePartitions cut left right).part_eq_of_mem
  · exact (mem_combinePartitions_iff cut left right).2 <|
      Or.inr (right.part_mem.2 hu)
  · exact right.mem_part hu

/-- Every edge separated by the leaf partition occurs in an ancestor cut. -/
theorem crossingEdges_subset_cutEdges
    (tree : BandwidthSplitTree G cap alphaNum alphaDen C) :
    crossingEdges G C tree.partition ⊆ tree.cutEdges := by
  intro e he
  induction tree with
  | leaf hband =>
      induction e using Sym2.inductionOn with
      | _ u v =>
          rcases (mk_mem_crossingEdges G _ _ u v).1 he with
            ⟨_huv, hu, hv, hne⟩
          change s(u, v) ∈ (∅ : Finset (Sym2 V))
          change (⊤ : Finpartition _).part u ≠
            (⊤ : Finpartition _).part v at hne
          exact False.elim <| hne <|
            Finpartition.parts_top_subsingleton _
              ((⊤ : Finpartition _).part_mem.2 hu)
              ((⊤ : Finpartition _).part_mem.2 hv)
  | split cut left right ihLeft ihRight =>
      induction e using Sym2.inductionOn with
      | _ u v =>
          rcases (mk_mem_crossingEdges G _ _ u v).1 he with
            ⟨huv, huC, hvC, hne⟩
          have huSides : u ∈ cut.X ∨ u ∈ cut.Y := by
            simpa only [← cut.cover, Finset.mem_union] using huC
          have hvSides : v ∈ cut.X ∨ v ∈ cut.Y := by
            simpa only [← cut.cover, Finset.mem_union] using hvC
          rcases huSides with huX | huY <;>
            rcases hvSides with hvX | hvY
          · have hneLeft :
                left.partition.part u ≠ left.partition.part v := by
              simpa only [partition,
                combinePartitions_part_eq_left cut left.partition
                  right.partition huX,
                combinePartitions_part_eq_left cut left.partition
                  right.partition hvX] using hne
            have heLeft : s(u, v) ∈
                crossingEdges G cut.X left.partition :=
              (mk_mem_crossingEdges G _ _ u v).2
                ⟨huv, huX, hvX, hneLeft⟩
            exact Finset.mem_union_left _ <|
              Finset.mem_union_right _ (ihLeft heLeft)
          · exact Finset.mem_union_left _ <|
              Finset.mem_union_left _ <|
                (mk_mem_edgeBoundary_iff G cut.X cut.Y u v).2
                  ⟨huv, Or.inl ⟨huX, hvY⟩⟩
          · exact Finset.mem_union_left _ <|
              Finset.mem_union_left _ <|
                (mk_mem_edgeBoundary_iff G cut.X cut.Y u v).2
                  ⟨huv, Or.inr ⟨hvX, huY⟩⟩
          · have hneRight :
                right.partition.part u ≠ right.partition.part v := by
              simpa only [partition,
                combinePartitions_part_eq_right cut left.partition
                  right.partition huY,
                combinePartitions_part_eq_right cut left.partition
                  right.partition hvY] using hne
            have heRight : s(u, v) ∈
                crossingEdges G cut.Y right.partition :=
              (mk_mem_crossingEdges G _ _ u v).2
                ⟨huv, huY, hvY, hneRight⟩
            exact Finset.mem_union_right _ (ihRight heRight)

theorem cutEdges_card_le_totalCut
    (tree : BandwidthSplitTree G cap alphaNum alphaDen C) :
    tree.cutEdges.card ≤ tree.totalCut := by
  induction tree with
  | leaf _ => simp [cutEdges, totalCut]
  | split cut left right ihLeft ihRight =>
      simp only [cutEdges, totalCut]
      calc
        #((Section44.edgeBoundary G cut.X cut.Y ∪ left.cutEdges) ∪
            right.cutEdges)
            ≤ #(Section44.edgeBoundary G cut.X cut.Y ∪ left.cutEdges) +
                #right.cutEdges :=
          Finset.card_union_le _ _
        _ ≤ (#(Section44.edgeBoundary G cut.X cut.Y) +
              #left.cutEdges) + #right.cutEdges := by
            exact Nat.add_le_add_right
              (Finset.card_union_le
                (Section44.edgeBoundary G cut.X cut.Y) left.cutEdges) _
        _ ≤ #(Section44.edgeBoundary G cut.X cut.Y) +
              left.totalCut + right.totalCut := by omega

/-- The graph edges crossing the final bandwidth decomposition are bounded
by the accumulated sparse-cut charge. -/
theorem crossingEdges_card_le_totalCut
    (tree : BandwidthSplitTree G cap alphaNum alphaDen C) :
    (crossingEdges G C tree.partition).card ≤ tree.totalCut :=
  (Finset.card_le_card tree.crossingEdges_subset_cutEdges).trans
    tree.cutEdges_card_le_totalCut

open ChekuriChuzhoySection5BandwidthAmortization

/-- Forget the graph labels of a split history while retaining exactly the
three boundary masses used by the numerical amortization theorem. -/
noncomputable def toAmortizationTree :
    {C : Finset V} →
      BandwidthSplitTree G cap alphaNum alphaDen C →
        ChekuriChuzhoySection5BandwidthAmortization.SplitTree
  | C, .leaf _ =>
      .leaf (Section44.clusterBoundary G C).card
  | _, .split cut left right =>
      .node
        (inheritedBoundary G cut.X cut.Y).card
        (inheritedBoundary G cut.Y cut.X).card
        (Section44.edgeBoundary G cut.X cut.Y).card
        (toAmortizationTree left) (toAmortizationTree right)

@[simp] theorem toAmortizationTree_rootBoundary
    (tree : BandwidthSplitTree G cap alphaNum alphaDen C) :
    tree.toAmortizationTree.rootBoundary =
      (Section44.clusterBoundary G C).card := by
  cases tree with
  | leaf _ => rfl
  | split cut left right =>
      exact inheritedBoundary_card_add (G := G)
        cut.cover cut.disjoint

@[simp] theorem toAmortizationTree_totalCut
    (tree : BandwidthSplitTree G cap alphaNum alphaDen C) :
    tree.toAmortizationTree.totalCut = tree.totalCut := by
  induction tree with
  | leaf _ => rfl
  | split cut left right ihLeft ihRight =>
      simp only [toAmortizationTree,
        ChekuriChuzhoySection5BandwidthAmortization.SplitTree.totalCut,
        totalCut, ihLeft, ihRight]

/-- Every graph split with ratio `1 / D` supplies the exact numerical node
invariant consumed by the depth-independent amortization theorem. -/
theorem toAmortizationTree_valid
    {D : Nat} (tree : BandwidthSplitTree G cap 1 D C) :
    tree.toAmortizationTree.Valid cap D := by
  induction tree with
  | leaf _ => trivial
  | split cut left right ihLeft ihRight =>
      have hleftBoundary :
          (Section44.clusterBoundary G cut.X).card =
            (inheritedBoundary G cut.X cut.Y).card +
              (Section44.edgeBoundary G cut.X cut.Y).card :=
        (inheritedBoundary_card_add_cut (G := G) cut.disjoint).symm
      have hrightBoundary :
          (Section44.clusterBoundary G cut.Y).card =
            (inheritedBoundary G cut.Y cut.X).card +
              (Section44.edgeBoundary G cut.X cut.Y).card := by
        have h := inheritedBoundary_card_add_cut
          (G := G) cut.disjoint.symm
        rw [Section44.edgeBoundary_comm] at h
        exact h.symm
      have hdemandLeft :
          truncatedInterfaceDemand G _ cut.X cut.Y cap ≤
            (inheritedBoundary G cut.X cut.Y).card :=
        truncatedInterfaceDemand_le_inheritedBoundary_left
          (G := G) cut.cover cut.disjoint cap
      have hdemandRight :
          truncatedInterfaceDemand G _ cut.X cut.Y cap ≤
            (inheritedBoundary G cut.Y cut.X).card :=
        truncatedInterfaceDemand_le_inheritedBoundary_right
          (G := G) cut.cover cut.disjoint cap
      have hdemandCap := truncatedInterfaceDemand_le_cap G
        (cut.X ∪ cut.Y) cut.X cut.Y cap
      rw [cut.cover] at hdemandCap
      have hcut :
          D * (Section44.edgeBoundary G cut.X cut.Y).card <
            min
              (min (inheritedBoundary G cut.X cut.Y).card
                (inheritedBoundary G cut.Y cut.X).card) cap := by
        have hsparse := cut.sparse
        simp only [one_mul] at hsparse
        exact lt_min
          (lt_min (hsparse.trans_le hdemandLeft)
            (hsparse.trans_le hdemandRight))
          (hsparse.trans_le hdemandCap)
      exact ⟨by
          rw [toAmortizationTree_rootBoundary]
          exact hleftBoundary,
        by
          rw [toAmortizationTree_rootBoundary]
          exact hrightBoundary,
        hcut, ihLeft, ihRight⟩

/-- Source-strength truncated-bandwidth decomposition.  With denominator
`16 * ell * (log_2 cap + 1)`, the final crossing edges consume strictly less
than one `ell`-th of the root boundary. -/
theorem exists_bandwidthDecomposition_crossing_lt
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap ell : Nat) (hell : 0 < ell)
    (hboundary : 0 < (Section44.clusterBoundary G C).card) :
    ∃ P : Finpartition C,
      IsBandwidthDecomposition G C cap 1
          (16 * ell * (Nat.log 2 cap + 1)) P ∧
        ell * (crossingEdges G C P).card <
          (Section44.clusterBoundary G C).card := by
  let D := 16 * ell * (Nat.log 2 cap + 1)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  let tree := build G C cap 1 D (by decide) (Nat.one_le_iff_ne_zero.mpr hDpos.ne')
  refine ⟨tree.partition, tree.partition_bandwidth, ?_⟩
  have htotal :
      ell * tree.totalCut <
        (Section44.clusterBoundary G C).card := by
    have := tree.toAmortizationTree.ell_mul_totalCut_lt_rootBoundary
      hell (by simpa using hboundary) tree.toAmortizationTree_valid
    simpa [D] using this
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_left ell tree.crossingEdges_card_le_totalCut) htotal

/-- The non-strict companion to
`exists_bandwidthDecomposition_crossing_lt`, valid even when the root has
empty outer boundary.  In that case the amortization inequality forces every
recursive cut, and hence every final crossing edge, to vanish. -/
theorem exists_bandwidthDecomposition_crossing_le
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap ell : Nat) (hell : 0 < ell) :
    ∃ P : Finpartition C,
      IsBandwidthDecomposition G C cap 1
          (16 * ell * (Nat.log 2 cap + 1)) P ∧
        ell * (crossingEdges G C P).card ≤
          (Section44.clusterBoundary G C).card := by
  let L := Nat.log 2 cap + 1
  let D := 16 * ell * L
  have hL : 0 < L := by
    dsimp [L]
    omega
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  let tree := build G C cap 1 D (by decide)
    (Nat.one_le_iff_ne_zero.mpr hDpos.ne')
  refine ⟨tree.partition, tree.partition_bandwidth, ?_⟩
  have htotalD :
      D * tree.totalCut ≤
        8 * L * (Section44.clusterBoundary G C).card := by
    have h :=
      tree.toAmortizationTree.denominator_mul_totalCut_le
        tree.toAmortizationTree_valid
        (by
          change 16 * L ≤ D
          calc
            16 * L = (16 * L) * 1 := by simp
            _ ≤ (16 * L) * ell :=
              Nat.mul_le_mul_left (16 * L) (by omega)
            _ = D := by
              simp [D]
              ring)
    simpa [D, L] using h
  have htotal :
      2 * ell * tree.totalCut ≤
        (Section44.clusterBoundary G C).card := by
    have hfactor : 0 < 8 * L := Nat.mul_pos (by decide) hL
    have hscaled :
        8 * L * (2 * ell * tree.totalCut) ≤
          8 * L * (Section44.clusterBoundary G C).card := by
      calc
        8 * L * (2 * ell * tree.totalCut) =
            D * tree.totalCut := by
              simp [D]
              ring
        _ ≤ 8 * L * (Section44.clusterBoundary G C).card := htotalD
    exact Nat.le_of_mul_le_mul_left hscaled hfactor
  have hellTwo : ell ≤ 2 * ell := by omega
  have hcrossTotal :
      ell * (crossingEdges G C tree.partition).card ≤
        ell * tree.totalCut :=
    Nat.mul_le_mul_left ell tree.crossingEdges_card_le_totalCut
  exact hcrossTotal.trans <|
    (Nat.mul_le_mul_right tree.totalCut hellTwo).trans
      (by simpa [Nat.mul_assoc] using htotal)

end BandwidthSplitTree

/-- A source-independent minimum crossing-edge decomposition.  This finite
choice is the object to which the Section 5.2 cut-budget argument applies. -/
structure IsMinimumCrossingBandwidthDecomposition
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : Nat) (P : Finpartition C) : Prop where
  bandwidth :
    IsBandwidthDecomposition G C cap alphaNum alphaDen P
  crossing_minimal :
    ∀ Q : Finpartition C,
      IsBandwidthDecomposition G C cap alphaNum alphaDen Q →
        (crossingEdges G C P).card ≤ (crossingEdges G C Q).card

/-- A minimum crossing-edge bandwidth decomposition exists by finite
minimization over the already inhabited candidate family. -/
theorem exists_minimumCrossingBandwidthDecomposition
    (G : _root_.SimpleGraph V) (C : Finset V)
    (cap alphaNum alphaDen : Nat)
    (hnum : 0 < alphaNum) (hratio : alphaNum ≤ alphaDen) :
    ∃ P : Finpartition C,
      IsMinimumCrossingBandwidthDecomposition
        G C cap alphaNum alphaDen P := by
  classical
  let candidates : Finset (Finpartition C) :=
    Finset.univ.filter fun P =>
      IsBandwidthDecomposition G C cap alphaNum alphaDen P
  have hcandidates : candidates.Nonempty := by
    refine ⟨(⊥ : Finpartition C), ?_⟩
    simp [candidates, discrete_isBandwidthDecomposition,
      hnum, hratio]
  rcases candidates.exists_min_image
      (fun P => (crossingEdges G C P).card) hcandidates with
    ⟨P, hPmem, hPmin⟩
  have hPband :
      IsBandwidthDecomposition G C cap alphaNum alphaDen P := by
    simpa [candidates] using hPmem
  refine ⟨P, ⟨hPband, ?_⟩⟩
  intro Q hQ
  apply hPmin
  simp [candidates, hQ]

end ChekuriChuzhoySection5BandwidthDecomposition
end SimpleGraph

end Lax17Proofs
