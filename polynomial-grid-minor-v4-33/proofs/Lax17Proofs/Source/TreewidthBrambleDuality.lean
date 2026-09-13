import Lax17Proofs.Source.BrambleWellLinked
import Lax17Proofs.Source.Treewidth

namespace Lax17Proofs

universe u v w

/-!
# The finite direction of treewidth--bramble duality

This file follows Frederic Mazoit's proof using partial `(< k)` tree
decompositions and their flaps.  The formulation is deliberately finite: both
the vertex type and every family of flaps are represented by finsets.
-/

namespace SimpleGraph

namespace TreewidthBrambleDuality


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {α : Type v}

/-- A vertex outside `X` belongs to its external vertex boundary when it has a
neighbor in `X`. -/
noncomputable def externalBoundary (G : _root_.SimpleGraph V) (X : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ X ∧ ∃ x ∈ X, G.Adj v x

@[simp] theorem mem_externalBoundary {X : Finset V} {v : V} :
    v ∈ externalBoundary G X ↔ v ∉ X ∧ ∃ x ∈ X, G.Adj v x := by
  classical
  simp [externalBoundary]

/-- `x` is a leaf of `T` with unique neighbor `u`.  Keeping the neighbor in
the predicate avoids making an arbitrary choice later. -/
def IsLeafWith (T : _root_.SimpleGraph α) (x u : α) : Prop :=
  T.Adj x u ∧ ∀ z, T.Adj x z → z = u

namespace IsLeafWith

variable {T : _root_.SimpleGraph α} {x u : α}

theorem ne (h : IsLeafWith T x u) : x ≠ u := h.1.ne

theorem unique (h : IsLeafWith T x u) {z : α} (hz : T.Adj x z) : z = u :=
  h.2 z hz

end IsLeafWith

/-- A partial `(< k)`-decomposition in the sense used by Mazoit.

Internal bags are small, at least one bag is small, and the neighbor of every
big leaf is small.  `flap_boundary` records the standard consequence of the
running-intersection axiom: the boundary of `bag x \ bag u` is contained in
the neighboring bag.  Recording this derived invariant makes decomposition
surgery independent of a particular path API for the decomposition tree. -/
structure PartialLTDecomposition (G : _root_.SimpleGraph V) (k : ℕ) where
  decomp : TreeDecomposition G
  has_small_bag : ∃ t : decomp.Node, (decomp.bag t).card ≤ k
  internal_bag_small :
    ∀ t : decomp.Node,
      (∀ u : decomp.Node, ¬IsLeafWith decomp.tree t u) →
        (decomp.bag t).card ≤ k
  big_leaf_neighbor_small :
    ∀ {x u : decomp.Node}, IsLeafWith decomp.tree x u →
      k < (decomp.bag x).card → (decomp.bag u).card ≤ k
  flap_boundary :
    ∀ {x u : decomp.Node}, IsLeafWith decomp.tree x u →
      externalBoundary G (decomp.bag x \ decomp.bag u) ⊆ decomp.bag u

namespace PartialLTDecomposition

variable {k : ℕ} (P : PartialLTDecomposition G k)

/-- A `k`-flap is the nonempty part of a big leaf bag outside its neighboring
small bag. -/
def IsKFlap (X : Finset V) : Prop :=
  ∃ x u : P.decomp.Node,
    IsLeafWith P.decomp.tree x u ∧
      k < (P.decomp.bag x).card ∧
      X = P.decomp.bag x \ P.decomp.bag u

/-- The finite family of all flaps of a partial decomposition. -/
noncomputable def kFlaps (P : PartialLTDecomposition G k) : Finset (Finset V) := by
  classical
  exact (Finset.univ.powerset : Finset (Finset V)).filter P.IsKFlap

@[simp] theorem mem_kFlaps {X : Finset V} :
    X ∈ P.kFlaps ↔ P.IsKFlap X := by
  classical
  simp [kFlaps]

theorem flap_nonempty {X : Finset V} (hX : P.IsKFlap X) : X.Nonempty := by
  rcases hX with ⟨x, u, hleaf, hbig, rfl⟩
  rw [Finset.sdiff_nonempty]
  intro hsub
  have hcard := Finset.card_le_card hsub
  exact (not_lt_of_ge (hcard.trans (P.big_leaf_neighbor_small hleaf hbig))) hbig

theorem exists_small_separator_of_flap {X : Finset V} (hX : P.IsKFlap X) :
    ∃ S : Finset V, externalBoundary G X ⊆ S ∧ S.card ≤ k := by
  rcases hX with ⟨x, u, hleaf, hbig, rfl⟩
  exact ⟨P.decomp.bag u, P.flap_boundary hleaf,
    P.big_leaf_neighbor_small hleaf hbig⟩

/-- Every flap has a boundary of cardinality at most `k`. -/
theorem flap_boundary_card_le {X : Finset V} (hX : P.IsKFlap X) :
    (externalBoundary G X).card ≤ k := by
  rcases hX with ⟨x, u, hleaf, hbig, rfl⟩
  exact (Finset.card_le_card (P.flap_boundary hleaf)).trans
    (P.big_leaf_neighbor_small hleaf hbig)

/-- If no flap exists, every bag is small. -/
theorem all_bags_small_of_kFlaps_empty (hflaps : P.kFlaps = ∅) :
    ∀ t : P.decomp.Node, (P.decomp.bag t).card ≤ k := by
  intro t
  by_cases hleaf : ∃ u : P.decomp.Node, IsLeafWith P.decomp.tree t u
  · rcases hleaf with ⟨u, htu⟩
    by_contra hbig
    have hbig' : k < (P.decomp.bag t).card := Nat.lt_of_not_ge hbig
    let X := P.decomp.bag t \ P.decomp.bag u
    have hX : P.IsKFlap X := ⟨t, u, htu, hbig', rfl⟩
    have : X ∈ P.kFlaps := P.mem_kFlaps.mpr hX
    simpa [hflaps] using this
  · exact P.internal_bag_small t (by simpa using hleaf)

/-- If every bag has at most `k` vertices and `k > 0`, the decomposition has
width strictly less than `k`. -/
theorem width_lt_of_all_bags_small (hk : 0 < k)
    (hsmall : ∀ t : P.decomp.Node, (P.decomp.bag t).card ≤ k) :
    P.decomp.width < k := by
  classical
  letI : Fintype P.decomp.Node := P.decomp.nodeFintype
  letI : DecidableEq P.decomp.Node := P.decomp.nodeDecidableEq
  have hsup :
      Finset.univ.sup (fun t : P.decomp.Node => (P.decomp.bag t).card) ≤ k := by
    apply Finset.sup_le
    intro t _ht
    exact hsmall t
  dsimp [TreeDecomposition.width]
  omega

/-- A partial decomposition without flaps contradicts treewidth at least `k`
when `k` is positive. -/
theorem treewidth_lt_of_kFlaps_empty (hk : 0 < k)
    (hflaps : P.kFlaps = ∅) : treewidth G < k := by
  have hwidth := P.width_lt_of_all_bags_small hk
    (P.all_bags_small_of_kFlaps_empty hflaps)
  exact (treewidth_le_of_hasTreewidthAtMost ⟨P.decomp, le_rfl⟩).trans_lt hwidth

theorem kFlaps_nonempty_of_le_treewidth (hk : 0 < k)
    (htw : k ≤ treewidth G) : P.kFlaps.Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  exact (not_lt_of_ge htw) (P.treewidth_lt_of_kFlaps_empty hk hempty)

end PartialLTDecomposition

/-! ## Finite flap families -/

/-- A finite set is a connected flap candidate. -/
def IsConnectedVertexSet (G : _root_.SimpleGraph V) (X : Finset V) : Prop :=
  X.Nonempty ∧ (G.induce {v : V | v ∈ X}).Connected

/-- A set which occurs as a flap of some partial `(< k)`-decomposition. -/
def IsGlobalKFlap (G : _root_.SimpleGraph V) (k : ℕ) (X : Finset V) : Prop :=
  ∃ P : PartialLTDecomposition G k, P.IsKFlap X

/-- The finite family of all global `k`-flaps. -/
noncomputable def globalKFlaps (G : _root_.SimpleGraph V) (k : ℕ) :
    Finset (Finset V) := by
  classical
  exact (Finset.univ.powerset : Finset (Finset V)).filter (IsGlobalKFlap G k)

@[simp] theorem mem_globalKFlaps {k : ℕ} {X : Finset V} :
    X ∈ globalKFlaps G k ↔ IsGlobalKFlap G k X := by
  classical
  simp [globalKFlaps]

/-- `F` contains a flap from every partial decomposition. -/
def MeetsEveryPartial (G : _root_.SimpleGraph V) (k : ℕ)
    (F : Finset (Finset V)) : Prop :=
  ∀ P : PartialLTDecomposition G k,
    ∃ X ∈ P.kFlaps, X ∈ F

/-- Upward closure is only required among sets which actually occur as
`k`-flaps, exactly as in Mazoit's proof. -/
def UpwardClosedOnFlaps (G : _root_.SimpleGraph V) (k : ℕ)
    (F : Finset (Finset V)) : Prop :=
  ∀ ⦃X⦄, X ∈ F → ∀ ⦃Y⦄, X ⊆ Y → IsGlobalKFlap G k Y → Y ∈ F

def IsAdmissibleFlapFamily (G : _root_.SimpleGraph V) (k : ℕ)
    (F : Finset (Finset V)) : Prop :=
  MeetsEveryPartial G k F ∧ UpwardClosedOnFlaps G k F

/-- The global family is admissible whenever every partial decomposition has
a flap. -/
theorem globalKFlaps_admissible {k : ℕ}
    (hne : ∀ P : PartialLTDecomposition G k, P.kFlaps.Nonempty) :
    IsAdmissibleFlapFamily G k (globalKFlaps G k) := by
  classical
  constructor
  · intro P
    rcases hne P with ⟨X, hX⟩
    exact ⟨X, hX, mem_globalKFlaps.mpr ⟨P, P.mem_kFlaps.mp hX⟩⟩
  · intro X hX Y _hXY hY
    exact mem_globalKFlaps.mpr hY

/-- There is a cardinality-minimal admissible flap family.  Cardinal
minimality is stronger than the inclusion minimality used on paper and is
more convenient for finite Lean bookkeeping. -/
theorem exists_minimal_admissibleFlapFamily {k : ℕ}
    (hne : ∀ P : PartialLTDecomposition G k, P.kFlaps.Nonempty) :
    ∃ F : Finset (Finset V),
      IsAdmissibleFlapFamily G k F ∧
        ∀ F' : Finset (Finset V),
          IsAdmissibleFlapFamily G k F' → F.card ≤ F'.card := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ F : Finset (Finset V), IsAdmissibleFlapFamily G k F ∧ F.card = n
  have hQ : ∃ n, Q n := by
    exact ⟨(globalKFlaps G k).card, globalKFlaps G k,
      globalKFlaps_admissible hne, rfl⟩
  rcases Nat.find_spec hQ with ⟨F, hF, hcard⟩
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  have hmin : Nat.find hQ ≤ F'.card :=
    Nat.find_min' hQ ⟨F', hF', rfl⟩
  simpa [hcard] using hmin

/-- Inclusion-minimal membership within a flap family. -/
def IsMinimalMember (F : Finset (Finset V)) (X : Finset V) : Prop :=
  X ∈ F ∧ ∀ ⦃Y⦄, Y ∈ F → Y ⊆ X → X ⊆ Y

theorem exists_minimalMember_subset {F : Finset (Finset V)}
    {A : Finset V} (hA : A ∈ F) :
    ∃ X : Finset V, IsMinimalMember F X ∧ X ⊆ A := by
  classical
  let C := F.filter fun X => X ⊆ A
  have hC : C.Nonempty := ⟨A, by simp [C, hA]⟩
  rcases C.exists_min_image Finset.card hC with ⟨X, hXC, hmin⟩
  have hXF : X ∈ F := (Finset.mem_filter.mp hXC).1
  have hXA : X ⊆ A := (Finset.mem_filter.mp hXC).2
  refine ⟨X, ⟨hXF, ?_⟩, hXA⟩
  intro Y hYF hYX
  have hYA : Y ⊆ A := hYX.trans hXA
  have hYC : Y ∈ C := Finset.mem_filter.mpr ⟨hYF, hYA⟩
  have hcard : X.card ≤ Y.card := hmin Y hYC
  have hEq : Y = X := Finset.eq_of_subset_of_card_le hYX hcard
  exact hEq.symm.subset

/-- Removing a minimal member preserves upward closure. -/
theorem upwardClosed_erase_minimal {k : ℕ} {F : Finset (Finset V)}
    {X : Finset V} (hup : UpwardClosedOnFlaps G k F)
    (hX : IsMinimalMember F X) :
    UpwardClosedOnFlaps G k (F.erase X) := by
  classical
  intro Y hY Z hYZ hZglobal
  have hYF : Y ∈ F := Finset.mem_of_mem_erase hY
  have hZF : Z ∈ F := hup hYF hYZ hZglobal
  apply Finset.mem_erase.mpr
  refine ⟨?_, hZF⟩
  intro hZX
  subst Z
  have hXY : X ⊆ Y := hX.2 hYF hYZ
  have : Y = X := Finset.Subset.antisymm hYZ hXY
  exact (Finset.ne_of_mem_erase hY) this

/-- In a cardinal-minimal admissible family, each inclusion-minimal member is
the unique selected flap of some partial decomposition. -/
theorem exists_partial_unique_family_flap {k : ℕ}
    {F : Finset (Finset V)}
    (hF : IsAdmissibleFlapFamily G k F)
    (hmin : ∀ F' : Finset (Finset V),
      IsAdmissibleFlapFamily G k F' → F.card ≤ F'.card)
    {X : Finset V} (hX : IsMinimalMember F X) :
    ∃ P : PartialLTDecomposition G k,
      P.IsKFlap X ∧
        ∀ ⦃Y : Finset V⦄, P.IsKFlap Y → Y ∈ F → Y = X := by
  classical
  have hupErase : UpwardClosedOnFlaps G k (F.erase X) :=
    upwardClosed_erase_minimal hF.2 hX
  have hnotMeet : ¬MeetsEveryPartial G k (F.erase X) := by
    intro hmeet
    have hadm : IsAdmissibleFlapFamily G k (F.erase X) := ⟨hmeet, hupErase⟩
    have hle := hmin (F.erase X) hadm
    have hlt : (F.erase X).card < F.card := Finset.card_erase_lt_of_mem hX.1
    exact (not_lt_of_ge hle) hlt
  simp only [MeetsEveryPartial] at hnotMeet
  push_neg at hnotMeet
  rcases hnotMeet with ⟨P, hP⟩
  rcases hF.1 P with ⟨Y, hYflap, hYF⟩
  have hYX : Y = X := by
    by_contra hne
    exact hP Y hYflap (Finset.mem_erase.mpr ⟨hne, hYF⟩)
  subst Y
  refine ⟨P, P.mem_kFlaps.mp hYflap, ?_⟩
  intro Y hYflap hYF
  by_contra hne
  exact hP Y (P.mem_kFlaps.mpr hYflap)
    (Finset.mem_erase.mpr ⟨hne, hYF⟩)

/-! ## Star and gluing interfaces -/

/-- The property of the star decomposition from `S` used by the duality
argument: all its flaps are connected components outside `S`. -/
def IsStarDecompositionFrom {k : ℕ}
    (P : PartialLTDecomposition G k) (S : Finset V) : Prop :=
  ∀ ⦃X : Finset V⦄, P.IsKFlap X →
    IsConnectedVertexSet G X ∧ Disjoint X S

/-- Every small separator admits its star decomposition. -/
def HasStarDecompositions (G : _root_.SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ k →
    ∃ P : PartialLTDecomposition G k, IsStarDecompositionFrom P S

/-- Mazoit's gluing conclusion for two non-touching flaps.  Every new flap is
contained in an old flap other than the two flaps used for gluing. -/
def HasNonTouchingFlapGluing (G : _root_.SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (PX PY : PartialLTDecomposition G k) (X Y : Finset V),
    PX.IsKFlap X → PY.IsKFlap Y → ¬FinsetTouching G X Y →
      ∃ P : PartialLTDecomposition G k,
        ∀ ⦃Z : Finset V⦄, P.IsKFlap Z →
          (∃ W : Finset V, PX.IsKFlap W ∧ W ≠ X ∧ Z ⊆ W) ∨
          (∃ W : Finset V, PY.IsKFlap W ∧ W ≠ Y ∧ Z ⊆ W)

theorem finsetTouching_mono {A B C D : Finset V}
    (h : FinsetTouching G A B) (hAC : A ⊆ C) (hBD : B ⊆ D) :
    FinsetTouching G C D := by
  rcases h with hinter | ⟨a, ha, b, hb, hab⟩
  · rcases hinter with ⟨v, hv⟩
    exact Or.inl ⟨v, Finset.mem_inter.mpr
      ⟨hAC (Finset.mem_inter.mp hv).1, hBD (Finset.mem_inter.mp hv).2⟩⟩
  · exact Or.inr ⟨a, hAC ha, b, hBD hb, hab⟩

/-- The minimal admissible family is pairwise touching, assuming the gluing
lemma. -/
theorem minimal_family_pairwise_touching {k : ℕ}
    {F : Finset (Finset V)}
    (hF : IsAdmissibleFlapFamily G k F)
    (hmin : ∀ F' : Finset (Finset V),
      IsAdmissibleFlapFamily G k F' → F.card ≤ F'.card)
    (hglue : HasNonTouchingFlapGluing G k) :
    ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → FinsetTouching G A B := by
  classical
  intro A hAF B hBF
  by_contra hnAB
  rcases exists_minimalMember_subset hAF with ⟨X, hXmin, hXA⟩
  rcases exists_minimalMember_subset hBF with ⟨Y, hYmin, hYB⟩
  have hnXY : ¬FinsetTouching G X Y := by
    intro hXY
    exact hnAB (finsetTouching_mono hXY hXA hYB)
  rcases exists_partial_unique_family_flap hF hmin hXmin with
    ⟨PX, hPX, hPXunique⟩
  rcases exists_partial_unique_family_flap hF hmin hYmin with
    ⟨PY, hPY, hPYunique⟩
  rcases hglue PX PY X Y hPX hPY hnXY with ⟨P, hP⟩
  rcases hF.1 P with ⟨Z, hZflap, hZF⟩
  rcases hP (P.mem_kFlaps.mp hZflap) with
    ⟨W, hWflap, hWne, hZW⟩ | ⟨W, hWflap, hWne, hZW⟩
  · have hWglobal : IsGlobalKFlap G k W := ⟨PX, hWflap⟩
    have hWF : W ∈ F := hF.2 hZF hZW hWglobal
    exact hWne (hPXunique hWflap hWF)
  · have hWglobal : IsGlobalKFlap G k W := ⟨PY, hWflap⟩
    have hWF : W ∈ F := hF.2 hZF hZW hWglobal
    exact hWne (hPYunique hWflap hWF)

/-! ## Extraction of the finite bramble -/

/-- Keep the connected members of a flap family. -/
noncomputable def connectedMembers (G : _root_.SimpleGraph V)
    (F : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact F.filter (IsConnectedVertexSet G)

@[simp] theorem mem_connectedMembers {F : Finset (Finset V)} {X : Finset V} :
    X ∈ connectedMembers G F ↔ X ∈ F ∧ IsConnectedVertexSet G X := by
  classical
  simp [connectedMembers]

/-- Connected members of a pairwise-touching family form a `FiniteBramble`. -/
noncomputable def finiteBrambleOfFamily (F : Finset (Finset V))
    (htouch : ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → FinsetTouching G A B) :
    FiniteBramble G where
  sets := connectedMembers G F
  nonempty := by
    intro A hA
    exact (mem_connectedMembers.mp hA).2.1
  connected := by
    intro A hA
    exact (mem_connectedMembers.mp hA).2.2
  touching := by
    intro A hA B hB _hne
    exact htouch (mem_connectedMembers.mp hA).1
      (mem_connectedMembers.mp hB).1

/-- Star decompositions show that no set of fewer than `k` vertices hits all
connected members of an admissible flap family. -/
theorem hitting_card_ge_of_stars {k : ℕ} {F : Finset (Finset V)}
    (hF : IsAdmissibleFlapFamily G k F)
    (hstar : HasStarDecompositions G k)
    {htouch : ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → FinsetTouching G A B}
    {H : Finset V}
    (hH : (finiteBrambleOfFamily F htouch).IsHittingSet H) :
    k ≤ H.card := by
  by_contra hnot
  have hHlt : H.card < k := Nat.lt_of_not_ge hnot
  rcases hstar H (Nat.le_of_lt hHlt) with ⟨P, hPstar⟩
  rcases hF.1 P with ⟨X, hXflap, hXF⟩
  have hXflap' : P.IsKFlap X := P.mem_kFlaps.mp hXflap
  have hXstar := hPstar hXflap'
  have hXB : X ∈ (finiteBrambleOfFamily F htouch).sets := by
    exact mem_connectedMembers.mpr ⟨hXF, hXstar.1⟩
  rcases hH X hXB with ⟨v, hvX, hvH⟩
  exact Finset.disjoint_left.mp hXstar.2 hvX hvH

/-- The finite Mazoit argument, factored over its two decomposition
constructions.  This theorem contains all minimal-family and empty-width
bookkeeping; the only remaining graph-specific obligations are star
decompositions and the non-touching-flap gluing lemma. -/
theorem exists_finiteBramble_hitting_card_ge_treewidth_of_stars_and_gluing
    (hstar : HasStarDecompositions G (treewidth G))
    (hglue : HasNonTouchingFlapGluing G (treewidth G)) :
    ∃ B : FiniteBramble G,
      ∀ H : Finset V, B.IsHittingSet H → treewidth G ≤ H.card := by
  classical
  by_cases hzero : treewidth G = 0
  · let B : FiniteBramble G :=
      { sets := ∅
        nonempty := by simp
        connected := by simp
        touching := by simp }
    refine ⟨B, ?_⟩
    intro H _hH
    simp [hzero]
  · have htwpos : 0 < treewidth G := Nat.pos_of_ne_zero hzero
    have hne : ∀ P : PartialLTDecomposition G (treewidth G),
        P.kFlaps.Nonempty := by
      intro P
      exact P.kFlaps_nonempty_of_le_treewidth htwpos le_rfl
    rcases exists_minimal_admissibleFlapFamily hne with ⟨F, hF, hmin⟩
    have htouch :
        ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → FinsetTouching G A B :=
      minimal_family_pairwise_touching hF hmin hglue
    let B : FiniteBramble G := finiteBrambleOfFamily F htouch
    refine ⟨B, ?_⟩
    intro H hH
    exact hitting_card_ge_of_stars hF hstar hH

/-! ## Concrete star decompositions -/

/-- The star with center `Sum.inl ()` and leaves indexed by `I`. -/
def starTree (I : Type*) : _root_.SimpleGraph (Unit ⊕ I) :=
  completeBipartiteGraph Unit I

theorem starTree_connected (I : Type*) : (starTree I).Connected := by
  apply _root_.SimpleGraph.Connected.mk
  intro a b
  cases a with
  | inl a =>
      cases a
      cases b with
      | inl b =>
          cases b
          exact _root_.SimpleGraph.Reachable.refl (Sum.inl ())
      | inr b => exact (_root_.SimpleGraph.Adj.reachable (by simp [starTree]))
  | inr a =>
      cases b with
      | inl b =>
          cases b
          exact _root_.SimpleGraph.Adj.reachable (by simp [starTree])
      | inr b =>
          have ha : (starTree I).Adj (Sum.inr a) (Sum.inl ()) := by
            simp [starTree]
          have hb : (starTree I).Adj (Sum.inl ()) (Sum.inr b) := by
            simp [starTree]
          exact ha.reachable.trans hb.reachable

theorem starTree_isTree (I : Type*) [Finite I] : (starTree I).IsTree := by
  rw [_root_.SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨starTree_connected I, ?_⟩
  have hedge : (starTree I).edgeSet =
      Set.range (fun x : Unit × I => s(Sum.inl x.1, Sum.inr x.2)) := by
    refine Set.ext (Sym2.ind fun u v => ?_)
    constructor
    · intro h
      cases u with
      | inl a =>
          cases v with
          | inl b =>
              have : False := by simpa [starTree] using h
              exact this.elim
          | inr b => exact ⟨(a, b), rfl⟩
      | inr a =>
          cases v with
          | inl b => exact ⟨(b, a), Sym2.eq_swap⟩
          | inr b =>
              have : False := by simpa [starTree] using h
              exact this.elim
    · rintro ⟨⟨a, b⟩, h⟩
      rw [← h]
      simp [starTree]
  rw [hedge, Nat.card_range_of_injective]
  · rw [Nat.card_prod, Nat.card_sum]
    simp only [Nat.card_unique, one_mul]
    omega
  · grind [Function.Injective]

private abbrev deletedGraph (G : _root_.SimpleGraph V) (S : Finset V) :=
  G.induce {v : V | v ∉ S}

/-- Vertices of one connected component of `G - S`, coerced back to the
original vertex type. -/
noncomputable def componentVertices (G : _root_.SimpleGraph V) (S : Finset V)
    (c : (deletedGraph G S).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ hv : v ∉ S, (deletedGraph G S).connectedComponentMk ⟨v, hv⟩ = c

@[simp] theorem mem_componentVertices {S : Finset V}
    {c : (deletedGraph G S).ConnectedComponent} {v : V} :
    v ∈ componentVertices G S c ↔
      ∃ hv : v ∉ S, (deletedGraph G S).connectedComponentMk ⟨v, hv⟩ = c := by
  classical
  simp [componentVertices]

theorem componentVertices_nonempty {S : Finset V}
    (c : (deletedGraph G S).ConnectedComponent) :
    (componentVertices G S c).Nonempty := by
  rcases c.exists_rep with ⟨v, hv⟩
  exact ⟨v.1, mem_componentVertices.mpr ⟨v.2, hv⟩⟩

theorem componentVertices_disjoint {S : Finset V}
    (c : (deletedGraph G S).ConnectedComponent) :
    Disjoint (componentVertices G S c) S := by
  rw [Finset.disjoint_left]
  intro v hvC hvS
  rcases mem_componentVertices.mp hvC with ⟨hv, _⟩
  exact hv hvS

private noncomputable def componentVertexEquiv {S : Finset V}
    (c : (deletedGraph G S).ConnectedComponent) :
    c ≃ {v : V // v ∈ componentVertices G S c} where
  toFun q := ⟨q.1.1, mem_componentVertices.mpr ⟨q.1.2, q.2⟩⟩
  invFun v := by
    let hv := Classical.choose (mem_componentVertices.mp v.2)
    let heq := Classical.choose_spec (mem_componentVertices.mp v.2)
    exact ⟨⟨v.1, hv⟩, heq⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro v
    apply Subtype.ext
    rfl

private noncomputable def componentVertexIso {S : Finset V}
    (c : (deletedGraph G S).ConnectedComponent) :
    c.toSimpleGraph ≃g G.induce {v : V | v ∈ componentVertices G S c} where
  toEquiv := componentVertexEquiv c
  map_rel_iff' := by
    intro a b
    rfl

theorem componentVertices_connected {S : Finset V}
    (c : (deletedGraph G S).ConnectedComponent) :
    (G.induce {v : V | v ∈ componentVertices G S c}).Connected := by
  exact (componentVertexIso c).connected_iff.mp c.connected_toSimpleGraph

/-- Adjacent vertices outside `S` belong to the same component of `G - S`. -/
theorem component_eq_of_adj_outside {S : Finset V} {a b : V}
    (ha : a ∉ S) (hb : b ∉ S) (hab : G.Adj a b) :
    (deletedGraph G S).connectedComponentMk ⟨a, ha⟩ =
      (deletedGraph G S).connectedComponentMk ⟨b, hb⟩ := by
  exact
    _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := deletedGraph G S) hab

private abbrev ComponentIndex (G : _root_.SimpleGraph V) (S : Finset V) :=
  Fin (Nat.card (deletedGraph G S).ConnectedComponent)

private noncomputable def componentAt (G : _root_.SimpleGraph V) (S : Finset V)
    (i : ComponentIndex G S) : (deletedGraph G S).ConnectedComponent :=
  (Finite.equivFin (deletedGraph G S).ConnectedComponent).symm i

private noncomputable def componentIndex (G : _root_.SimpleGraph V) (S : Finset V)
    (c : (deletedGraph G S).ConnectedComponent) : ComponentIndex G S :=
  Finite.equivFin (deletedGraph G S).ConnectedComponent c

@[simp] private theorem componentAt_componentIndex (G : _root_.SimpleGraph V)
    (S : Finset V) (c : (deletedGraph G S).ConnectedComponent) :
    componentAt G S (componentIndex G S c) = c := by
  exact (Finite.equivFin (deletedGraph G S).ConnectedComponent).symm_apply_apply c

@[simp] private theorem componentIndex_componentAt (G : _root_.SimpleGraph V)
    (S : Finset V) (i : ComponentIndex G S) :
    componentIndex G S (componentAt G S i) = i := by
  exact (Finite.equivFin (deletedGraph G S).ConnectedComponent).apply_symm_apply i

noncomputable def starBag (G : _root_.SimpleGraph V) (S : Finset V) :
    Unit ⊕ ComponentIndex G S → Finset V
  | Sum.inl _ => S
  | Sum.inr i => S ∪ componentVertices G S (componentAt G S i)

/-- The concrete star tree decomposition from `S`: its center bag is `S` and
the leaf for component `c` is `S ∪ c`. -/
noncomputable def starTreeDecomposition (G : _root_.SimpleGraph V)
    (S : Finset V) : TreeDecomposition G where
  Node := Unit ⊕ ComponentIndex G S
  nodeFintype := Fintype.ofFinite _
  nodeDecidableEq := Classical.decEq _
  tree := starTree _
  isTree := starTree_isTree _
  bag := starBag G S
  vertex_mem_bag := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨Sum.inl (), hv⟩
    · let c := (deletedGraph G S).connectedComponentMk ⟨v, hv⟩
      refine ⟨Sum.inr (componentIndex G S c), ?_⟩
      simp [starBag, c, mem_componentVertices, hv]
  edge_mem_bag := by
    intro a b hab
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · exact ⟨Sum.inl (), ha, hb⟩
      · let c := (deletedGraph G S).connectedComponentMk ⟨b, hb⟩
        refine ⟨Sum.inr (componentIndex G S c), ?_, ?_⟩
        · simp [starBag, ha]
        · simp [starBag, c, mem_componentVertices, hb]
    · by_cases hb : b ∈ S
      · let c := (deletedGraph G S).connectedComponentMk ⟨a, ha⟩
        refine ⟨Sum.inr (componentIndex G S c), ?_, ?_⟩
        · simp [starBag, c, mem_componentVertices, ha]
        · simp [starBag, hb]
      · let c := (deletedGraph G S).connectedComponentMk ⟨a, ha⟩
        have heq : (deletedGraph G S).connectedComponentMk ⟨b, hb⟩ = c :=
          (component_eq_of_adj_outside ha hb hab).symm
        refine ⟨Sum.inr (componentIndex G S c), ?_, ?_⟩
        · simp [starBag, c, mem_componentVertices, ha]
        · exact Finset.mem_union_right S
            (mem_componentVertices.mpr ⟨hb,
              heq.trans (componentAt_componentIndex G S c).symm⟩)
  bag_indices_connected := by
    intro v
    by_cases hv : v ∈ S
    · have hset :
          {i : Unit ⊕ ComponentIndex G S |
              v ∈ starBag G S i} = Set.univ := by
          ext i
          cases i <;> simp [starBag, hv]
      rw [hset]
      exact (_root_.SimpleGraph.induceUnivIso (starTree _)).connected_iff.mpr
        (starTree_connected _)
    · let c := (deletedGraph G S).connectedComponentMk ⟨v, hv⟩
      have hset :
          {i : Unit ⊕ ComponentIndex G S |
              v ∈ starBag G S i} = {Sum.inr (componentIndex G S c)} := by
        ext i
        cases i with
        | inl i => simp [starBag, hv]
        | inr d =>
            change (v ∈ S ∪ componentVertices G S (componentAt G S d)) ↔
              Sum.inr d = Sum.inr (componentIndex G S c)
            constructor
            · intro hmem
              have hvC : v ∈ componentVertices G S (componentAt G S d) := by
                rcases Finset.mem_union.mp hmem with hvS | hvC
                · exact (hv hvS).elim
                · exact hvC
              rcases mem_componentVertices.mp hvC with ⟨hv', heq⟩
              apply congrArg Sum.inr
              have hc : (deletedGraph G S).connectedComponentMk ⟨v, hv'⟩ = c := by
                simp [c]
              have hdc : componentAt G S d = c := heq.symm.trans hc
              calc
                d = componentIndex G S (componentAt G S d) :=
                  (componentIndex_componentAt G S d).symm
                _ = componentIndex G S c := congrArg (componentIndex G S) hdc
            · intro heq
              have hdc : d = componentIndex G S c := Sum.inr_injective heq
              apply Finset.mem_union_right S
              apply mem_componentVertices.mpr
              exact ⟨hv, by simp [hdc, c]⟩
      rw [hset]
      letI : Nonempty {i : Unit ⊕ ComponentIndex G S |
          i ∈ ({Sum.inr (componentIndex G S c)} : Set (Unit ⊕ ComponentIndex G S))} :=
        ⟨⟨Sum.inr (componentIndex G S c), by simp⟩⟩
      letI : Subsingleton {i : Unit ⊕ ComponentIndex G S |
          i ∈ ({Sum.inr (componentIndex G S c)} : Set (Unit ⊕ ComponentIndex G S))} := by
        constructor
        intro a b
        apply Subtype.ext
        simpa using a.2.trans b.2.symm
      exact _root_.SimpleGraph.Connected.of_subsingleton

theorem starTree_leafWith (I : Type*) (i : I) :
    IsLeafWith (starTree I) (Sum.inr i) (Sum.inl ()) := by
  constructor
  · simp [starTree]
  · intro z hz
    cases z with
    | inl z => cases z; rfl
    | inr z => simp [starTree] at hz

private theorem component_union_sdiff {S : Finset V}
    (c : (deletedGraph G S).ConnectedComponent) :
    (S ∪ componentVertices G S c) \ S = componentVertices G S c := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hvUnion, hvS⟩
    rcases Finset.mem_union.mp hvUnion with hvS' | hvC
    · exact (hvS hvS').elim
    · exact hvC
  · intro hvC
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right S hvC,
      Finset.disjoint_left.mp (componentVertices_disjoint c) hvC⟩

private theorem component_boundary_subset {S : Finset V}
    (c : (deletedGraph G S).ConnectedComponent) :
    externalBoundary G (componentVertices G S c) ⊆ S := by
  intro v hvBoundary
  rcases mem_externalBoundary.mp hvBoundary with ⟨hvC, x, hxC, hvx⟩
  by_cases hvS : v ∈ S
  · exact hvS
  · exfalso
    rcases mem_componentVertices.mp hxC with ⟨hxS, hxEq⟩
    apply hvC
    apply mem_componentVertices.mpr
    refine ⟨hvS, ?_⟩
    exact (component_eq_of_adj_outside hvS hxS hvx).trans hxEq

/-- The star tree decomposition is a partial `(< k)`-decomposition whenever
the center has at most `k` vertices. -/
noncomputable def starPartialDecomposition (G : _root_.SimpleGraph V)
    (k : ℕ) (S : Finset V) (hS : S.card ≤ k) :
    PartialLTDecomposition G k where
  decomp := starTreeDecomposition G S
  has_small_bag := ⟨Sum.inl (), hS⟩
  internal_bag_small := by
    intro t hnotLeaf
    cases t with
    | inl t => exact hS
    | inr i =>
        exact False.elim (hnotLeaf (Sum.inl ()) (starTree_leafWith _ i))
  big_leaf_neighbor_small := by
    intro x u hleaf hbig
    cases x with
    | inl x =>
        have : (starTreeDecomposition G S).bag (Sum.inl x) = S := rfl
        rw [this] at hbig
        exact False.elim ((not_lt_of_ge hS) hbig)
    | inr i =>
        have hu : u = Sum.inl () := (starTree_leafWith _ i).unique hleaf.1
        subst u
        exact hS
  flap_boundary := by
    intro x u hleaf
    cases x with
    | inl x =>
        cases x
        cases u with
        | inl u =>
            cases u
            have hfalse : False := by
              have hadj := hleaf.1
              simpa [starTree] using hadj
            exact hfalse.elim
        | inr i =>
            have hdiff :
                (starTreeDecomposition G S).bag (Sum.inl ()) \
                    (starTreeDecomposition G S).bag (Sum.inr i) = ∅ := by
              simp [starTreeDecomposition, starBag]
            rw [hdiff]
            simp [externalBoundary, starTreeDecomposition, starBag]
    | inr i =>
        have hu : u = Sum.inl () := (starTree_leafWith _ i).unique hleaf.1
        subst u
        change externalBoundary G
            ((S ∪ componentVertices G S (componentAt G S i)) \ S) ⊆ S
        rw [component_union_sdiff]
        exact component_boundary_subset (componentAt G S i)

/-- Every flap of the star partial decomposition is one of the connected
components of `G - S`, hence connected and disjoint from `S`. -/
theorem starPartialDecomposition_isStar (k : ℕ) (S : Finset V)
    (hS : S.card ≤ k) :
    IsStarDecompositionFrom (starPartialDecomposition G k S hS) S := by
  intro X hX
  rcases hX with ⟨x, u, hleaf, hbig, rfl⟩
  cases x with
  | inl x =>
      have hsmall :
          ((starPartialDecomposition G k S hS).decomp.bag (Sum.inl x)).card ≤ k := by
        simpa [starPartialDecomposition, starTreeDecomposition, starBag] using hS
      exact False.elim ((not_lt_of_ge hsmall) hbig)
  | inr i =>
      have hu : u = Sum.inl () := (starTree_leafWith _ i).unique hleaf.1
      subst u
      have hdiff :
          (starPartialDecomposition G k S hS).decomp.bag (Sum.inr i) \
              (starPartialDecomposition G k S hS).decomp.bag (Sum.inl ()) =
            componentVertices G S (componentAt G S i) := by
        exact component_union_sdiff (componentAt G S i)
      rw [hdiff]
      exact ⟨⟨componentVertices_nonempty _, componentVertices_connected _⟩,
        componentVertices_disjoint _⟩

theorem hasStarDecompositions (G : _root_.SimpleGraph V) (k : ℕ) :
    HasStarDecompositions G k := by
  intro S hS
  exact ⟨starPartialDecomposition G k S hS,
    starPartialDecomposition_isStar k S hS⟩

end TreewidthBrambleDuality

end SimpleGraph

end Lax17Proofs
