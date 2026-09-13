import Mathlib.Tactic
import Lax17Proofs.Source.Degree
import Lax17Proofs.Source.FlowDefs
import Lax17Proofs.Source.LocalSubgraph
import Lax17Proofs.Source.Menger
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Section 4.6: from weak to strong path-of-sets systems

Section 4.6 upgrades a weak path-of-sets system to a strong one by shrinking
the nail sets.  In the paper the shrink is constant-factor and uses two
external results of Chekuri--Chuzhoy: a boost from edge/cut well-linkedness to
node-well-linked subsets, and a linkedness theorem for two node-well-linked
terminal sets.

This file contains the proof-facing part that is independent of those external
boosting theorems.

* `strong_pathOfSetsSystem_of_restrictWidth_certificates` is the exact assembly
  step: once the trimmed left and right nail sets are certified to be
  node-well-linked and mutually linked in every cluster, the restricted
  path-of-sets system is strong.
* `weak_pathOfSetsSystem_to_strong_width_one` is a fully self-contained
  certified weakening of Section 4.6.  It shows that every positive-width weak
  system has a strong width-one restriction.  This uses only the definitions:
  singleton terminal sets are node-well-linked, and a one-path edge linkage is
  automatically node-disjoint.

The constant-factor form of the paper reduces to the first theorem once the
external Chekuri--Chuzhoy boosting/linking statements are formalized with the
chosen constants.
-/

namespace SimpleGraph


namespace Section46

open Finset

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-! ## Scaled cut well-linkedness -/

/-- Paper-style `α`-well-linkedness, with `α` represented by a natural ratio
`alphaNum / alphaDen`.

`ScaledEdgeWellLinkedIn G C T alphaNum alphaDen` means that `T` lies in `C` and
every partition `X,Y` of `C` has at least an `alphaNum / alphaDen` fraction of
the smaller terminal side crossing it:

`alphaNum * min |X ∩ T| |Y ∩ T| ≤ alphaDen * |E_G(X,Y)|`.

This is the cut-based well-linkedness called just "well-linked" in the
Chekuri--Chuzhoy papers. -/
def ScaledEdgeWellLinkedIn [Fintype V]
    (G : _root_.SimpleGraph V) (C T : Finset V)
    (alphaNum alphaDen : ℕ) : Prop :=
  0 < alphaNum ∧ alphaNum ≤ alphaDen ∧ T ⊆ C ∧
    ∀ X Y : Finset V, X ⊆ C → Y ⊆ C → X ∪ Y = C → Disjoint X Y →
      alphaNum * min (X ∩ T).card (Y ∩ T).card ≤
        alphaDen * (Section44.edgeBoundary G X Y).card

namespace ScaledEdgeWellLinkedIn

variable [Fintype V]

private theorem edgeBoundary_induced_eq_inter
    (G : _root_.SimpleGraph V) (C X Y : Finset V) :
    Section44.edgeBoundary (inducedOnFinset G C) X Y =
      Section44.edgeBoundary G (X ∩ C) (Y ∩ C) := by
  classical
  ext e
  constructor
  · intro he
    rcases ((Section44.mem_edgeBoundary (G := inducedOnFinset G C) X Y e).1 he) with
      ⟨heG, x, hx, y, hy, rfl⟩
    have hAdj : G.Adj x y ∧ x ∈ C ∧ y ∈ C := by
      simpa [inducedOnFinset_adj] using heG
    exact (Section44.mem_edgeBoundary (G := G) (X ∩ C) (Y ∩ C) s(x, y)).2
      ⟨by simpa using hAdj.1, x, by exact mem_inter.mpr ⟨hx, hAdj.2.1⟩,
        y, by exact mem_inter.mpr ⟨hy, hAdj.2.2⟩, rfl⟩
  · intro he
    rcases ((Section44.mem_edgeBoundary (G := G) (X ∩ C) (Y ∩ C) e).1 he) with
      ⟨heG, x, hx, y, hy, rfl⟩
    have hx' := (mem_inter.mp hx).1
    have hxC := (mem_inter.mp hx).2
    have hy' := (mem_inter.mp hy).1
    have hyC := (mem_inter.mp hy).2
    have hAdj : (inducedOnFinset G C).Adj x y := by
      exact ⟨by simpa using heG, hxC, hyC⟩
    exact (Section44.mem_edgeBoundary (G := inducedOnFinset G C) X Y s(x, y)).2
      ⟨by simpa using hAdj, x, hx', y, hy', rfl⟩

/-- Scaled edge-well-linkedness is inherited by smaller terminal sets. -/
theorem mono_terminals {C T U : Finset V} {alphaNum alphaDen : ℕ}
    (h : ScaledEdgeWellLinkedIn G C T alphaNum alphaDen) (hU : U ⊆ T) :
    ScaledEdgeWellLinkedIn G C U alphaNum alphaDen := by
  classical
  refine ⟨h.1, h.2.1, subset_trans hU h.2.2.1, ?_⟩
  intro X Y hXC hYC hcover hdisj
  have hXT : X ∩ U ⊆ X ∩ T := by
    intro v hv
    exact mem_inter.mpr ⟨(mem_inter.mp hv).1, hU (mem_inter.mp hv).2⟩
  have hYT : Y ∩ U ⊆ Y ∩ T := by
    intro v hv
    exact mem_inter.mpr ⟨(mem_inter.mp hv).1, hU (mem_inter.mp hv).2⟩
  have hmin :
      min (X ∩ U).card (Y ∩ U).card ≤
        min (X ∩ T).card (Y ∩ T).card :=
    by
      have hx := card_le_card hXT
      have hy := card_le_card hYT
      omega
  exact (Nat.mul_le_mul_left alphaNum hmin).trans
    (h.2.2.2 X Y hXC hYC hcover hdisj)

/-- The cluster-local scaled well-linkedness definition induces the global
scaled well-linkedness definition on the same-vertex induced graph. -/
theorem toScaledEdgeWellLinked_induced {C T : Finset V} {alphaNum alphaDen : ℕ}
    (h : ScaledEdgeWellLinkedIn G C T alphaNum alphaDen) :
    ScaledEdgeWellLinked (inducedOnFinset G C) T alphaNum alphaDen := by
  classical
  refine ⟨h.1, h.2.1, ?_⟩
  intro X Y hcover hdisj
  have hXC : X ∩ C ⊆ C := inter_subset_right
  have hYC : Y ∩ C ⊆ C := inter_subset_right
  have hcoverC : (X ∩ C) ∪ (Y ∩ C) = C := by
    ext v
    constructor
    · intro hv
      rcases mem_union.mp hv with hv | hv
      · exact (mem_inter.mp hv).2
      · exact (mem_inter.mp hv).2
    · intro hvC
      have hvXY : v ∈ X ∪ Y := by
        rw [hcover]
        exact mem_univ v
      rcases mem_union.mp hvXY with hvX | hvY
      · exact mem_union_left _ (mem_inter.mpr ⟨hvX, hvC⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hvY, hvC⟩)
  have hdisjC : Disjoint (X ∩ C) (Y ∩ C) :=
    hdisj.mono inter_subset_left inter_subset_left
  have hXT : (X ∩ C) ∩ T = X ∩ T := by
    ext v
    constructor
    · intro hv
      exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hv).1).1, (mem_inter.mp hv).2⟩
    · intro hv
      exact mem_inter.mpr
        ⟨mem_inter.mpr ⟨(mem_inter.mp hv).1, h.2.2.1 (mem_inter.mp hv).2⟩,
          (mem_inter.mp hv).2⟩
  have hYT : (Y ∩ C) ∩ T = Y ∩ T := by
    ext v
    constructor
    · intro hv
      exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hv).1).1, (mem_inter.mp hv).2⟩
    · intro hv
      exact mem_inter.mpr
        ⟨mem_inter.mpr ⟨(mem_inter.mp hv).1, h.2.2.1 (mem_inter.mp hv).2⟩,
          (mem_inter.mp hv).2⟩
  have hmain := h.2.2.2 (X ∩ C) (Y ∩ C) hXC hYC hcoverC hdisjC
  rw [hXT, hYT] at hmain
  simpa [edgeBoundary_induced_eq_inter] using hmain

end ScaledEdgeWellLinkedIn

/-! ## Observation 4.19: edge-linked implies `1`-well-linked -/

namespace EdgePathPacking

variable [Fintype V]
variable {C S T X Y : Finset V}

omit [Fintype V] in
/-- Edge sets of distinct paths in an edge-disjoint packing are disjoint, even
after intersecting with a common finite edge set. -/
theorem pairwiseDisjoint_edgeSet_inter
    (P : EdgePathPacking G S T) (J : Finset P.Index) (F : Finset (Sym2 V)) :
    (↑J : Set P.Index).PairwiseDisjoint
      (fun i => (P.path i).edgeSet ∩ F) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hnonempty
  rcases hnonempty with ⟨e, he⟩
  rcases Finset.mem_inter.1 he with ⟨hei, hej⟩
  have heiPath : e ∈ (P.path i).edgeSet := (Finset.mem_inter.1 hei).1
  have hejPath : e ∈ (P.path j).edgeSet := (Finset.mem_inter.1 hej).1
  by_contra hne
  exact Finset.disjoint_left.mp (P.edge_disjoint hne) heiPath hejPath

/-- Every path in an edge-disjoint packing connecting the two sides of a
partition must use a distinct edge of the cut. -/
theorem card_le_edgeBoundary_of_staysIn_partition
    (P : EdgePathPacking G (X ∩ T) (Y ∩ T))
    (hstay : P.StaysIn C) (hcover : X ∪ Y = C) (hdisj : Disjoint X Y) :
    P.card ≤ (Section44.edgeBoundary G X Y).card := by
  classical
  let Bdry := Section44.edgeBoundary G X Y
  have hpath_boundary :
      ∀ i : P.Index, ∃ e ∈ (P.path i).edgeSet, e ∈ Bdry := by
    intro i
    have hsub : (P.path i).vertexSet ⊆ X ∪ Y := by
      intro v hv
      rw [hcover]
      exact hstay i hv
    rcases P.connects i with hconn | hconn
    · have hsourceX : (P.path i).source ∈ X := (Finset.mem_inter.mp hconn.1).1
      have htargetY : (P.path i).target ∈ Y := (Finset.mem_inter.mp hconn.2).1
      have hnot : ¬ (P.path i).vertexSet ⊆ X := by
        intro hsubX
        exact Finset.disjoint_left.mp hdisj
          (hsubX (GraphPath.target_mem_vertexSet (P.path i))) htargetY
      simpa [Bdry] using
        Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
          (G := G) (P := P.path i) hsub hsourceX hnot
    · have hsourceY : (P.path i).source ∈ Y := (Finset.mem_inter.mp hconn.1).1
      have htargetX : (P.path i).target ∈ X := (Finset.mem_inter.mp hconn.2).1
      have hnot : ¬ (P.path i).vertexSet ⊆ X := by
        intro hsubX
        exact Finset.disjoint_left.mp hdisj
          (hsubX (GraphPath.source_mem_vertexSet (P.path i))) hsourceY
      simpa [Bdry] using
        Section44.GraphPath.exists_edgeBoundary_of_target_mem_left_of_not_subset_left
          (G := G) (P := P.path i) hsub htargetX hnot
  have hone :
      ∀ i : P.Index, 1 ≤ ((P.path i).edgeSet ∩ Bdry).card := by
    intro i
    rcases hpath_boundary i with ⟨e, hePath, heBdry⟩
    exact Finset.one_le_card.mpr
      ⟨e, Finset.mem_inter.mpr ⟨hePath, heBdry⟩⟩
  have hcard_le_sum :
      P.card ≤ ∑ i : P.Index, ((P.path i).edgeSet ∩ Bdry).card := by
    calc
      P.card = ∑ _i : P.Index, 1 := by
        simp [EdgePathPacking.card]
      _ ≤ ∑ i : P.Index, ((P.path i).edgeSet ∩ Bdry).card := by
        exact Finset.sum_le_sum fun i _hi => hone i
  have hunion_subset :
      (Finset.univ.biUnion fun i : P.Index => (P.path i).edgeSet ∩ Bdry) ⊆
        Bdry := by
    intro e he
    rcases Finset.mem_biUnion.1 he with ⟨i, _hi, hei⟩
    exact (Finset.mem_inter.1 hei).2
  have hsum_le :
      (∑ i : P.Index, ((P.path i).edgeSet ∩ Bdry).card) ≤ Bdry.card := by
    have hpair :
        (↑(Finset.univ : Finset P.Index) : Set P.Index).PairwiseDisjoint
          (fun i => (P.path i).edgeSet ∩ Bdry) :=
      pairwiseDisjoint_edgeSet_inter P Finset.univ Bdry
    have hcard_union :
        (Finset.univ.biUnion fun i : P.Index =>
            (P.path i).edgeSet ∩ Bdry).card =
          ∑ i : P.Index, ((P.path i).edgeSet ∩ Bdry).card := by
      simpa using Finset.card_biUnion hpair
    rw [← hcard_union]
    exact Finset.card_le_card hunion_subset
  exact hcard_le_sum.trans hsum_le

end EdgePathPacking

/-- Observation 4.19.  Path-based edge-well-linkedness implies the cut
inequality for `α = 1`. -/
theorem scaledEdgeWellLinkedIn_one_of_edgeWellLinkedIn [Fintype V]
    {C T : Finset V} (h : EdgeWellLinkedIn G C T) :
    ScaledEdgeWellLinkedIn G C T 1 1 := by
  classical
  refine ⟨by norm_num, by norm_num, h.1, ?_⟩
  intro X Y hXC hYC hcover hdisj
  let A := X ∩ T
  let B := Y ∩ T
  have hA : A ⊆ T := inter_subset_right
  have hB : B ⊆ T := inter_subset_right
  have hAB : Disjoint A B := by
    exact hdisj.mono inter_subset_left inter_subset_left
  rcases h.2 hA hB hAB with ⟨P, hPcard, hPstay⟩
  have hPle :
      P.card ≤ (Section44.edgeBoundary G X Y).card :=
    EdgePathPacking.card_le_edgeBoundary_of_staysIn_partition
      (G := G) (C := C) (T := T) (X := X) (Y := Y) P hPstay hcover hdisj
  simpa [A, B, hPcard] using hPle

/-! ## Menger inside an induced cluster -/

namespace InducedOnFinset

variable {C A B : Finset V}

omit [DecidableEq V] in
/-- A walk in the same-vertex graph induced on `C` has all of its vertices in
`C`, provided its first vertex lies in `C`. -/
theorem walk_support_subset {u v : V}
    (p : (inducedOnFinset G C).Walk u v) (hu : u ∈ C) :
    ∀ x : V, x ∈ p.support → x ∈ C := by
  induction p with
  | nil =>
      intro x hx
      simp at hx
      subst x
      simpa using hu
  | cons hxy p ih =>
      intro x hx
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hxy.2.1
      · exact ih hxy.2.2 x hx

/-- A graph path in `inducedOnFinset G C` connecting subsets of `C` uses only
vertices of `C`. -/
theorem graphPath_vertexSet_subset_of_connects
    (P : GraphPath (inducedOnFinset G C))
    (hP : P.Connects A B) (hA : A ⊆ C) (hB : B ⊆ C) :
    P.vertexSet ⊆ C := by
  classical
  have hsource : P.source ∈ C := by
    rcases hP with h | h
    · exact hA h.1
    · exact hB h.1
  intro x hx
  exact walk_support_subset (G := G) (C := C) P.walk hsource x
    (by simpa [GraphPath.vertexSet] using hx)

/-- A path packing in `inducedOnFinset G C` between terminal subsets of `C`
becomes an ambient packing in `G` whose paths stay in `C`. -/
theorem pathPacking_mapLe_staysIn
    (P : PathPacking (inducedOnFinset G C) A B)
    (hA : A ⊆ C) (hB : B ⊆ C) :
    (P.mapLe (inducedOnFinset_le (G := G) (C := C))).StaysIn C := by
  classical
  intro i x hx
  have hsubset :=
    graphPath_vertexSet_subset_of_connects (G := G) (C := C)
      (A := A) (B := B) (P.path i) (P.connects i) hA hB
  have hx' : x ∈ (P.path i).vertexSet := by
    simpa [PathPacking.mapLe] using hx
  exact hsubset hx'

end InducedOnFinset

/-! ## Menger-to-linked conversion inside a cluster -/

/-- If every separator between subfamilies of `A` and `B` inside the induced
cluster has size at least the smaller terminal side, then `A` and `B` are
node-linked inside that cluster.

This is the formal Menger wrapper used in Theorem 4.21: the hard separator
estimate is isolated as the hypothesis `hsep`, while this lemma converts that
estimate into the linkedness conclusion with paths staying inside `C`. -/
theorem nodeLinkedIn_of_induced_separator_lower_bound
    [Fintype V]
    {C A B : Finset V}
    (hA : A ⊆ C) (hB : B ⊆ C) (hdisj : Disjoint A B)
    (hsep :
      ∀ ⦃A' B' X : Finset V⦄,
        A' ⊆ A → B' ⊆ B →
          STSeparator (inducedOnFinset G C) A' B' X →
            min A'.card B'.card ≤ X.card) :
    NodeLinkedIn G C A B := by
  classical
  refine ⟨hA, hB, hdisj, ?_⟩
  intro A' B' hA' hB'
  let H := inducedOnFinset G C
  let k := min A'.card B'.card
  have hA'C : A' ⊆ C := subset_trans hA' hA
  have hB'C : B' ⊆ C := subset_trans hB' hB
  rcases Menger.finite_vertex_menger_sharp (G := H) A' B' k with hpaths | hsmall
  · rcases HasAtLeastDisjointPaths.exists_exact hpaths with ⟨P, hPcard⟩
    refine ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), ?_, ?_⟩
    · simpa [k] using hPcard
    · exact InducedOnFinset.pathPacking_mapLe_staysIn
        (G := G) (C := C) (A := A') (B := B') P hA'C hB'C
  · rcases hsmall with ⟨X, hXcard, hXsep⟩
    have hk_le : k ≤ X.card := hsep hA' hB' hXsep
    omega

/-- If every separator between disjoint subfamilies of `T` inside the induced
cluster has size at least the smaller terminal side, then `T` is
node-well-linked inside that cluster.

This is the Menger wrapper needed for Claim A.1 in the proof of
Chekuri--Chuzhoy Theorem 2.14. -/
theorem nodeWellLinkedIn_of_induced_separator_lower_bound
    [Fintype V]
    {C T : Finset V}
    (hT : T ⊆ C)
    (hsep :
      ∀ ⦃A B X : Finset V⦄,
        A ⊆ T → B ⊆ T → Disjoint A B →
          STSeparator (inducedOnFinset G C) A B X →
            min A.card B.card ≤ X.card) :
    NodeWellLinkedIn G C T := by
  classical
  refine ⟨hT, ?_⟩
  intro A B hA hB hdisj
  let H := inducedOnFinset G C
  let k := min A.card B.card
  have hAC : A ⊆ C := subset_trans hA hT
  have hBC : B ⊆ C := subset_trans hB hT
  rcases Menger.finite_vertex_menger_sharp (G := H) A B k with hpaths | hsmall
  · rcases HasAtLeastDisjointPaths.exists_exact hpaths with ⟨P, hPcard⟩
    refine ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), ?_, ?_⟩
    · simpa [k] using hPcard
    · exact InducedOnFinset.pathPacking_mapLe_staysIn
        (G := G) (C := C) (A := A) (B := B) P hAC hBC
  · rcases hsmall with ⟨X, hXcard, hXsep⟩
    have hk_le : k ≤ X.card := hsep hA hB hdisj hXsep
    omega

/-- A reachability witness inside `C \ X` contradicts an `(A,B)`-separator
`X` in the induced graph on `C`. -/
theorem not_separator_of_reachable_avoiding
    {C X A B : Finset V} {a b : V}
    (hsep : STSeparator (inducedOnFinset G C) A B X)
    (ha : a ∈ A) (hb : b ∈ B) (haCX : a ∈ C \ X)
    (hreach : (inducedOnFinset G (C \ X)).Reachable a b) :
    False := by
  classical
  let Hdel := inducedOnFinset G (C \ X)
  let H := inducedOnFinset G C
  have hle : Hdel ≤ H := by
    intro u v huv
    exact ⟨huv.1, (Finset.mem_sdiff.mp huv.2.1).1,
      (Finset.mem_sdiff.mp huv.2.2).1⟩
  rcases hreach with ⟨W⟩
  let Wc : H.Walk a b := W.mapLe hle
  let Wp := Wc.toPath
  let P : GraphPath H :=
    { source := a
      target := b
      walk := (Wp : H.Walk a b)
      isPath := Wp.property }
  rcases hsep P (Or.inl ⟨ha, hb⟩) with ⟨v, hvP, hvX⟩
  have hvWp : v ∈ (Wp : H.Walk a b).support := by
    simpa [P, GraphPath.vertexSet] using hvP
  have hvWc : v ∈ Wc.support :=
    _root_.SimpleGraph.Walk.support_toPath_subset Wc hvWp
  have hvW : v ∈ W.support := by
    simpa [Wc, _root_.SimpleGraph.Walk.support_mapLe_eq_support] using hvWc
  have hvCX : v ∈ C \ X :=
    InducedOnFinset.walk_support_subset (G := G) (C := C \ X) W haCX v hvW
  exact (Finset.mem_sdiff.mp hvCX).2 hvX

/-- A graph path staying in `C` and avoiding `X` gives reachability in the
same-vertex graph induced on `C \ X`. -/
theorem reachable_in_deleted_of_path_avoids
    {C X : Finset V} (P : GraphPath G)
    (hstay : P.vertexSet ⊆ C)
    (havoid : Disjoint P.vertexSet X) :
    (inducedOnFinset G (C \ X)).Reachable P.source P.target := by
  classical
  have hPX : P.vertexSet ⊆ C \ X := by
    intro v hv
    exact Finset.mem_sdiff.mpr
      ⟨hstay hv, fun hvX => Finset.disjoint_left.mp havoid hv hvX⟩
  exact ⟨(P.inInducedOnFinset hPX).walk⟩

namespace PathPacking

variable {S T X : Finset V}

/-- A node-disjoint packing with more paths than vertices in `X` contains a
path avoiding `X`.

The proof charges each path meeting `X` to its first vertex in `X`; node
disjointness makes this charge injective. -/
theorem exists_path_vertexSet_disjoint_of_card_gt
    (P : PathPacking G S T) (hcard : X.card < P.card) :
    ∃ i : P.Index, Disjoint (P.path i).vertexSet X := by
  classical
  by_contra hnone
  have hhit :
      ∀ i : P.Index, ((P.path i).vertexSet ∩ X).Nonempty := by
    intro i
    by_contra hne
    have hempty : (P.path i).vertexSet ∩ X = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hdisj : Disjoint (P.path i).vertexSet X := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hempty
    exact hnone ⟨i, hdisj⟩
  let hit : P.Index → {x : V // x ∈ X} := fun i =>
    ⟨(P.path i).firstHitVertex X (hhit i),
      GraphPath.firstHitVertex_mem_set (P.path i) X (hhit i)⟩
  have hinj : Function.Injective hit := by
    intro i j hij
    by_contra hne
    have hval : (hit i).1 = (hit j).1 := congrArg Subtype.val hij
    have hvi : (hit i).1 ∈ (P.path i).vertexSet := by
      exact GraphPath.firstHitVertex_mem_vertexSet (P.path i) X (hhit i)
    have hvj : (hit i).1 ∈ (P.path j).vertexSet := by
      have hvj' :
          (hit j).1 ∈ (P.path j).vertexSet :=
        GraphPath.firstHitVertex_mem_vertexSet (P.path j) X (hhit j)
      simpa [hval] using hvj'
    exact Finset.disjoint_left.mp (P.node_disjoint hne) hvi hvj
  have hle : P.card ≤ X.card := by
    have hle' := Fintype.card_le_of_injective hit hinj
    simpa [PathPacking.card] using hle'
  omega

end PathPacking

/-! ## Reachable terminal sets after deleting a separator -/

/-- Terminals of `T` that are either already in `A`, or are reachable from
`A` by a walk staying inside `C \ X`.

This is the formal counterpart of the set of terminals lying in a component of
`G \ X` that contains a vertex of `A`.  The explicit `t ∈ A` disjunct keeps the
source set contained in the reachable side even when the separator meets `A`;
the reachability disjunct itself requires both endpoints to lie outside `X`,
avoiding the reflexive reachability of isolated same-vertex induced subgraphs. -/
noncomputable def reachableTerminalsAfterDeleting
    (G : _root_.SimpleGraph V) (C X A T : Finset V) : Finset V := by
  classical
  exact T.filter fun t =>
    t ∈ A ∨
      (t ∈ C \ X ∧
        ∃ a ∈ A, a ∈ C \ X ∧
          (inducedOnFinset G (C \ X)).Reachable a t)

namespace reachableTerminalsAfterDeleting

variable {C X A T : Finset V}

theorem subset_terminals :
    reachableTerminalsAfterDeleting G C X A T ⊆ T := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).1

theorem left_subset (hA : A ⊆ T) :
    A ⊆ reachableTerminalsAfterDeleting G C X A T := by
  classical
  intro v hv
  rw [reachableTerminalsAfterDeleting, Finset.mem_filter]
  exact ⟨hA hv, Or.inl hv⟩

theorem mem_of_path_connects_avoiding
    {A' : Finset V} {P : GraphPath G}
    (hconn : P.Connects A A')
    (hstay : P.vertexSet ⊆ C)
    (havoid : Disjoint P.vertexSet X)
    {t : V} (ht : t ∈ A')
    (htP : t = P.target ∨ t = P.source)
    (hA' : A' ⊆ T) :
    t ∈ reachableTerminalsAfterDeleting G C X A T := by
  classical
  have hPX : P.vertexSet ⊆ C \ X := by
    intro v hv
    exact Finset.mem_sdiff.mpr
      ⟨hstay hv, fun hvX => Finset.disjoint_left.mp havoid hv hvX⟩
  let H := inducedOnFinset G (C \ X)
  have hreach_source_target : H.Reachable P.source P.target := by
    exact ⟨(P.inInducedOnFinset hPX).walk⟩
  have hsourceCX : P.source ∈ C \ X :=
    hPX (GraphPath.source_mem_vertexSet P)
  have htargetCX : P.target ∈ C \ X :=
    hPX (GraphPath.target_mem_vertexSet P)
  rw [reachableTerminalsAfterDeleting, Finset.mem_filter]
  refine ⟨hA' ht, ?_⟩
  rcases hconn with h | h
  · rcases htP with rfl | rfl
    · exact Or.inr
        ⟨htargetCX, P.source, h.1, hsourceCX, hreach_source_target⟩
    · exact Or.inl h.1
  · rcases htP with rfl | rfl
    · exact Or.inl h.2
    · exact Or.inr
        ⟨hsourceCX, P.target, h.2, htargetCX, hreach_source_target.symm⟩

/-- Membership in the reachable-terminal side, together with not being
deleted, gives an actual reachability witness in `C \ X` from the seed set. -/
theorem exists_reachable_of_mem_of_not_mem_deleted
    (hA_C : A ⊆ C)
    {t : V}
    (ht : t ∈ reachableTerminalsAfterDeleting G C X A T)
    (htX : t ∉ X) :
    ∃ a ∈ A, a ∈ C \ X ∧
      (inducedOnFinset G (C \ X)).Reachable a t := by
  classical
  rw [reachableTerminalsAfterDeleting, Finset.mem_filter] at ht
  rcases ht.2 with htA | hreach
  · refine ⟨t, htA, ?_, ?_⟩
    · exact Finset.mem_sdiff.mpr ⟨hA_C htA, htX⟩
    · exact ⟨_root_.SimpleGraph.Walk.nil⟩
  · rcases hreach with ⟨_htCX, a, haA, haCX, hreach⟩
    exact ⟨a, haA, haCX, hreach⟩

/-- If `A` has size `k` and fewer than `k` vertices are deleted, the reachable
side in a node-well-linked terminal set misses at most `k` terminals. -/
theorem card_ge_terminals_sub
    {k : ℕ}
    (hnode : NodeWellLinkedIn G C T)
    (hA : A ⊆ T) (hAcard : A.card = k) (hXcard : X.card < k) :
    T.card - k ≤ (reachableTerminalsAfterDeleting G C X A T).card := by
  classical
  let R := reachableTerminalsAfterDeleting G C X A T
  have hRT : R ⊆ T := subset_terminals (G := G) (C := C) (X := X) (A := A) (T := T)
  have hAR : A ⊆ R := left_subset (G := G) (C := C) (X := X) (A := A) (T := T) hA
  by_contra hnot
  have hlt : R.card < T.card - k := Nat.lt_of_not_ge hnot
  have hcomp_card : k ≤ (T \ R).card := by
    have hcard_sdiff : (T \ R).card = T.card - R.card := by
      rw [Finset.card_sdiff]
      have hcard_inter : (R ∩ T).card = R.card := by
        congr
        ext v
        constructor
        · intro hv
          exact (Finset.mem_inter.mp hv).1
        · intro hv
          exact Finset.mem_inter.mpr ⟨hv, hRT hv⟩
      rw [hcard_inter]
    omega
  rcases Finset.exists_subset_card_eq hcomp_card with ⟨A'', hA''sub, hA''card⟩
  have hA''T : A'' ⊆ T := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hA''sub hv)).1
  have hA''Rdisj : Disjoint A'' R := by
    rw [Finset.disjoint_left]
    intro v hvA'' hvR
    exact (Finset.mem_sdiff.mp (hA''sub hvA'')).2 hvR
  have hdisj : Disjoint A A'' := by
    rw [Finset.disjoint_left]
    intro v hvA hvA''
    exact Finset.disjoint_left.mp hA''Rdisj hvA'' (hAR hvA)
  rcases hnode.2 hA hA''T hdisj with ⟨Ppack, hPcard, hPstay⟩
  have hPcard_eq : Ppack.card = k := by
    simpa [hAcard, hA''card] using hPcard
  rcases Section46.PathPacking.exists_path_vertexSet_disjoint_of_card_gt (P := Ppack)
      (X := X) (by simpa [hPcard_eq] using hXcard) with ⟨i, havoid⟩
  have hconn := Ppack.connects i
  have hstay := hPstay i
  rcases hconn with h | h
  · have htR :
        (Ppack.path i).target ∈ R :=
      mem_of_path_connects_avoiding (G := G) (C := C) (X := X) (A := A)
        (T := T) (A' := A'') (P := Ppack.path i) (Or.inl h)
        hstay havoid h.2 (Or.inl rfl) hA''T
    exact Finset.disjoint_left.mp hA''Rdisj h.2 htR
  · have htR :
        (Ppack.path i).source ∈ R :=
      mem_of_path_connects_avoiding (G := G) (C := C) (X := X) (A := A)
        (T := T) (A' := A'') (P := Ppack.path i) (Or.inr h)
        hstay havoid h.1 (Or.inr rfl) hA''T
    exact Finset.disjoint_left.mp hA''Rdisj h.1 htR

end reachableTerminalsAfterDeleting

namespace EdgePathPacking

variable {S T X : Finset V} {Δ : ℕ}

/-- In a graph of maximum degree `Δ`, an edge-disjoint packing with more than
`Δ * |X|` paths contains a path avoiding `X`, provided the two terminal sides
are disjoint.

Each path meeting `X` is charged to an edge of the path incident with its first
hit in `X`; edge-disjointness makes the charged edges distinct, and the degree
bound gives at most `Δ` charges per vertex of `X`. -/
theorem exists_path_vertexSet_disjoint_of_card_gt_degree_mul
    (P : EdgePathPacking G S T) (hdegree : MaxDegreeAtMost G Δ)
    (hST : Disjoint S T) (hcard : Δ * X.card < P.card) :
    ∃ i : P.Index, Disjoint (P.path i).vertexSet X := by
  classical
  by_contra hnone
  have hhit :
      ∀ i : P.Index, ((P.path i).vertexSet ∩ X).Nonempty := by
    intro i
    by_contra hne
    have hempty : (P.path i).vertexSet ∩ X = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hdisj : Disjoint (P.path i).vertexSet X := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hempty
    exact hnone ⟨i, hdisj⟩
  let hitVertex : P.Index → V := fun i =>
    (P.path i).firstHitVertex X (hhit i)
  have hit_mem_path :
      ∀ i : P.Index, hitVertex i ∈ (P.path i).vertexSet := by
    intro i
    exact GraphPath.firstHitVertex_mem_vertexSet (P.path i) X (hhit i)
  have hit_mem_X : ∀ i : P.Index, hitVertex i ∈ X := by
    intro i
    exact GraphPath.firstHitVertex_mem_set (P.path i) X (hhit i)
  have endpoints_ne : ∀ i : P.Index, (P.path i).source ≠ (P.path i).target := by
    intro i hst
    rcases P.connects i with h | h
    · exact Finset.disjoint_left.mp hST h.1 (by simpa [hst] using h.2)
    · exact Finset.disjoint_left.mp hST h.2 (by simpa [hst] using h.1)
  let edgeWitness :
      (i : P.Index) →
        {e : Sym2 V // e ∈ (P.path i).edgeSet ∧ hitVertex i ∈ e} :=
    fun i =>
      ⟨Classical.choose
          (GraphPath.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
            (P.path i) (endpoints_ne i) (hit_mem_path i)),
        Classical.choose_spec
          (GraphPath.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
            (P.path i) (endpoints_ne i) (hit_mem_path i))⟩
  have edge_mem_path : ∀ i : P.Index, (edgeWitness i).1 ∈ (P.path i).edgeSet := by
    intro i
    exact (edgeWitness i).2.1
  have hit_mem_edge : ∀ i : P.Index, hitVertex i ∈ (edgeWitness i).1 := by
    intro i
    exact (edgeWitness i).2.2
  have edge_mem_graph : ∀ i : P.Index, (edgeWitness i).1 ∈ G.edgeSet := by
    intro i
    exact GraphPath.edgeSet_subset_edgeSet (P.path i) (edge_mem_path i)
  let incidenceProof :
      (i : P.Index) → (edgeWitness i).1 ∈ G.incidenceSet (hitVertex i) :=
    fun i => ⟨edge_mem_graph i, hit_mem_edge i⟩
  let otherVertex : P.Index → V := fun i =>
    G.otherVertexOfIncident (incidenceProof i)
  have other_mem_neighbor :
      ∀ i : P.Index,
        otherVertex i ∈ MaxDegreeAtMost.neighborFinset (G := G) hdegree (hitVertex i) := by
    intro i
    rw [MaxDegreeAtMost.mem_neighborFinset]
    exact (G.incidence_other_prop (incidenceProof i) :
      otherVertex i ∈ G.neighborSet (hitVertex i))
  have edge_eq_pair :
      ∀ i : P.Index, (edgeWitness i).1 = s(hitVertex i, otherVertex i) := by
    intro i
    exact (Sym2.other_spec' (hit_mem_edge i)).symm
  let chargeSet : Finset (V × V) :=
    X.biUnion fun x =>
      (MaxDegreeAtMost.neighborFinset (G := G) hdegree x).image fun y => (x, y)
  have charge_mem :
      ∀ i : P.Index, (hitVertex i, otherVertex i) ∈ chargeSet := by
    intro i
    change (hitVertex i, otherVertex i) ∈
      X.biUnion fun x =>
        (MaxDegreeAtMost.neighborFinset (G := G) hdegree x).image fun y => (x, y)
    rw [Finset.mem_biUnion]
    refine ⟨hitVertex i, hit_mem_X i, ?_⟩
    exact Finset.mem_image.mpr ⟨otherVertex i, other_mem_neighbor i, rfl⟩
  let charge : P.Index → {p : V × V // p ∈ chargeSet} := fun i =>
    ⟨(hitVertex i, otherVertex i), charge_mem i⟩
  have charge_inj : Function.Injective charge := by
    intro i j hij
    by_contra hne
    have hp : (hitVertex i, otherVertex i) = (hitVertex j, otherVertex j) :=
      congrArg Subtype.val hij
    have hx : hitVertex i = hitVertex j := congrArg Prod.fst hp
    have hu : otherVertex i = otherVertex j := congrArg Prod.snd hp
    have hedge : (edgeWitness i).1 = (edgeWitness j).1 := by
      rw [edge_eq_pair i, edge_eq_pair j, hx, hu]
    exact Finset.disjoint_left.mp (P.edge_disjoint hne)
      (edge_mem_path i) (by simpa [hedge] using edge_mem_path j)
  have hcharge_card : chargeSet.card ≤ X.card * Δ := by
    calc
      chargeSet.card
          ≤ ∑ x ∈ X,
              ((MaxDegreeAtMost.neighborFinset (G := G) hdegree x).image
                fun y => (x, y)).card := by
            exact Finset.card_biUnion_le
      _ ≤ ∑ x ∈ X, Δ := by
            exact Finset.sum_le_sum fun x _hx =>
              (Finset.card_image_le.trans
                (MaxDegreeAtMost.card_neighborFinset_le (G := G) hdegree x))
      _ = X.card * Δ := by
            simp [Finset.sum_const, Nat.mul_comm]
  have hP_le_charge : P.card ≤ chargeSet.card := by
    have hle := Fintype.card_le_of_injective charge charge_inj
    simpa [EdgePathPacking.card] using hle
  have hcharge_card' : chargeSet.card ≤ Δ * X.card := by
    simpa [Nat.mul_comm] using hcharge_card
  omega

end EdgePathPacking

/-! ## Theorem 4.21 in the `α = 1` edge-linked form -/

/-- Theorem 4.21 in the form used by Section 4.6 after Observation 4.19:
if `T₁ ∪ T₂` is edge-well-linked, `T₁` and `T₂` are node-well-linked, and
small equal subsets are chosen from both sides, then those chosen subsets are
linked.

This is the paper proof with `α = 1`: a small vertex separator would leave
large reachable terminal subsets on both sides; edge-well-linkedness routes
many edge-disjoint paths between them, and the degree bound forces one of
those paths to avoid the separator. -/
theorem theorem421_linkedSubsets_edgeWellLinked
    [Fintype V]
    {C T1 T2 T1' T2' : Finset V} {Δ κ : ℕ}
    (hdegree : MaxDegreeAtMost G Δ) (hDelta : 0 < Δ)
    (hdisj : Disjoint T1 T2)
    (hT1card : κ ≤ T1.card) (hT2card : κ ≤ T2.card)
    (hwell : EdgeWellLinkedIn G C (T1 ∪ T2))
    (hT1node : NodeWellLinkedIn G C T1)
    (hT2node : NodeWellLinkedIn G C T2)
    (hT1' : T1' ⊆ T1) (hT2' : T2' ⊆ T2)
    (_hcard_eq : T1'.card = T2'.card)
    (hsmall : 2 * Δ * T1'.card ≤ κ) :
    NodeLinkedIn G C T1' T2' := by
  classical
  have hT1'C : T1' ⊆ C := subset_trans hT1' hT1node.1
  have hT2'C : T2' ⊆ C := subset_trans hT2' hT2node.1
  have hT1'T2' : Disjoint T1' T2' := hdisj.mono hT1' hT2'
  refine nodeLinkedIn_of_induced_separator_lower_bound
      (G := G) (C := C) (A := T1') (B := T2')
      hT1'C hT2'C hT1'T2' ?_
  intro A B X hA hB hsep
  let k := min A.card B.card
  by_contra hnot
  have hXlt : X.card < k := Nat.lt_of_not_ge hnot
  have hkA : k ≤ A.card := Nat.min_le_left A.card B.card
  have hkB : k ≤ B.card := Nat.min_le_right A.card B.card
  rcases Finset.exists_subset_card_eq hkA with ⟨A0, hA0sub, hA0card⟩
  rcases Finset.exists_subset_card_eq hkB with ⟨B0, hB0sub, hB0card⟩
  have hA0T1' : A0 ⊆ T1' := subset_trans hA0sub hA
  have hB0T2' : B0 ⊆ T2' := subset_trans hB0sub hB
  have hA0T1 : A0 ⊆ T1 := subset_trans hA0T1' hT1'
  have hB0T2 : B0 ⊆ T2 := subset_trans hB0T2' hT2'
  have hA0C : A0 ⊆ C := subset_trans hA0T1 hT1node.1
  have hB0C : B0 ⊆ C := subset_trans hB0T2 hT2node.1
  have hsep0 : STSeparator (inducedOnFinset G C) A0 B0 X := by
    intro P hP
    apply hsep P
    rcases hP with h | h
    · exact Or.inl ⟨hA0sub h.1, hB0sub h.2⟩
    · exact Or.inr ⟨hB0sub h.1, hA0sub h.2⟩
  let R1 := reachableTerminalsAfterDeleting G C X A0 T1
  let R2 := reachableTerminalsAfterDeleting G C X B0 T2
  have hR1T1 : R1 ⊆ T1 :=
    reachableTerminalsAfterDeleting.subset_terminals
      (G := G) (C := C) (X := X) (A := A0) (T := T1)
  have hR2T2 : R2 ⊆ T2 :=
    reachableTerminalsAfterDeleting.subset_terminals
      (G := G) (C := C) (X := X) (A := B0) (T := T2)
  have hR1_lower : T1.card - k ≤ R1.card := by
    exact reachableTerminalsAfterDeleting.card_ge_terminals_sub
      (G := G) (C := C) (X := X) (A := A0) (T := T1)
      hT1node hA0T1 hA0card hXlt
  have hR2_lower : T2.card - k ≤ R2.card := by
    exact reachableTerminalsAfterDeleting.card_ge_terminals_sub
      (G := G) (C := C) (X := X) (A := B0) (T := T2)
      hT2node hB0T2 hB0card hXlt
  have hR1_union : R1 ⊆ T1 ∪ T2 := subset_trans hR1T1 (subset_union_left (s₁ := T1) (s₂ := T2))
  have hR2_union : R2 ⊆ T1 ∪ T2 := subset_trans hR2T2 (subset_union_right (s₁ := T1) (s₂ := T2))
  have hRdisj : Disjoint R1 R2 := hdisj.mono hR1T1 hR2T2
  rcases hwell.2 hR1_union hR2_union hRdisj with ⟨Q, hQcard, hQstay⟩
  have hk_le_T1' : k ≤ T1'.card :=
    hkA.trans ((Finset.card_le_card hA).trans (le_rfl))
  have htwodelta_k : 2 * Δ * k ≤ κ := by
    have hmul : (2 * Δ) * k ≤ (2 * Δ) * T1'.card :=
      Nat.mul_le_mul_left (2 * Δ) hk_le_T1'
    calc
      2 * Δ * k = (2 * Δ) * k := by ring
      _ ≤ (2 * Δ) * T1'.card := hmul
      _ = 2 * Δ * T1'.card := by ring
      _ ≤ κ := hsmall
  have hDX_add_lt : Δ * X.card + k < κ := by
    have hDXlt : Δ * X.card < Δ * k :=
      Nat.mul_lt_mul_of_pos_left hXlt hDelta
    have hk_le_Dk : k ≤ Δ * k := by
      have h1 : 1 ≤ Δ := hDelta
      calc
        k = 1 * k := by simp
        _ ≤ Δ * k := Nat.mul_le_mul_right k h1
    have hsum : Δ * X.card + k < Δ * k + Δ * k :=
      Nat.add_lt_add_of_lt_of_le hDXlt hk_le_Dk
    have hsum' : Δ * X.card + k < (Δ + Δ) * k := by
      rw [Nat.right_distrib]
      exact hsum
    have hsum'' : Δ * X.card + k < 2 * Δ * k := by
      simpa [two_mul, Nat.mul_assoc] using hsum'
    exact hsum''.trans_le htwodelta_k
  have hDX_lt_sub : Δ * X.card < κ - k := by
    omega
  have hk_sub_le_R1 : κ - k ≤ R1.card := by
    exact (Nat.sub_le_sub_right hT1card k).trans hR1_lower
  have hk_sub_le_R2 : κ - k ≤ R2.card := by
    exact (Nat.sub_le_sub_right hT2card k).trans hR2_lower
  have hk_sub_le_Q : κ - k ≤ Q.card := by
    rw [hQcard]
    exact le_min hk_sub_le_R1 hk_sub_le_R2
  have hQlarge : Δ * X.card < Q.card := hDX_lt_sub.trans_le hk_sub_le_Q
  rcases EdgePathPacking.exists_path_vertexSet_disjoint_of_card_gt_degree_mul
      (G := G) (S := R1) (T := R2) (X := X) (Δ := Δ)
      Q hdegree hRdisj hQlarge with ⟨i, havoid⟩
  have hconn := Q.connects i
  have hstay := hQstay i
  have hreachQ := reachable_in_deleted_of_path_avoids
      (G := G) (C := C) (X := X) (Q.path i) hstay havoid
  rcases hconn with h | h
  · have hsource_notX : (Q.path i).source ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.source_mem_vertexSet (Q.path i)) hx
    have htarget_notX : (Q.path i).target ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.target_mem_vertexSet (Q.path i)) hx
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := A0) (T := T1)
        hA0C h.1 hsource_notX with ⟨a, haA, haCX, hreachA⟩
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := B0) (T := T2)
        hB0C h.2 htarget_notX with ⟨b, hbB, _hbCX, hreachB⟩
    have hreachAB :
        (inducedOnFinset G (C \ X)).Reachable a b :=
      (hreachA.trans hreachQ).trans hreachB.symm
    exact not_separator_of_reachable_avoiding
      (G := G) (C := C) (X := X) (A := A0) (B := B0)
      hsep0 haA hbB haCX hreachAB
  · have hsource_notX : (Q.path i).source ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.source_mem_vertexSet (Q.path i)) hx
    have htarget_notX : (Q.path i).target ∉ X := by
      intro hx
      exact Finset.disjoint_left.mp havoid
        (GraphPath.target_mem_vertexSet (Q.path i)) hx
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := A0) (T := T1)
        hA0C h.2 htarget_notX with ⟨a, haA, haCX, hreachA⟩
    rcases reachableTerminalsAfterDeleting.exists_reachable_of_mem_of_not_mem_deleted
        (G := G) (C := C) (X := X) (A := B0) (T := T2)
        hB0C h.1 hsource_notX with ⟨b, hbB, _hbCX, hreachB⟩
    have hreachAB :
        (inducedOnFinset G (C \ X)).Reachable a b :=
      (hreachA.trans hreachQ.symm).trans hreachB.symm
    exact not_separator_of_reachable_avoiding
      (G := G) (C := C) (X := X) (A := A0) (B := B0)
      hsep0 haA hbB haCX hreachAB

/-! ## Direct edge-well-linked routing at weaker constants -/

/-- A self-contained edge-well-linked routing lemma.

If two disjoint equal-size terminal subsets lie in an edge-well-linked terminal
set, then a bounded-degree graph contains `k` node-disjoint paths between them
as soon as `Δ * k ≤ |S|`.  This is weaker than the fractional-flow constant
used in Chekuri--Chuzhoy Theorem 2.14, but it uses only the path definition of
edge-well-linkedness, finite vertex-Menger, and the degree counting lemma above. -/
theorem hasDisjointSTPaths_of_edgeWellLinkedIn_disjoint
    [Fintype V]
    {C Terminals S T : Finset V} {Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ) (hDelta : 0 < Δ)
    (hwell : EdgeWellLinkedIn G C Terminals)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) (hdisj : Disjoint S T)
    (hk : Δ * k ≤ S.card) :
    HasDisjointSTPaths G S T k := by
  classical
  let H := inducedOnFinset G C
  rcases Menger.finite_vertex_menger_sharp (G := H) S T k with hpaths | hsmall
  · rcases hpaths with ⟨P, hPcard⟩
    exact ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), by simpa using hPcard⟩
  · rcases hsmall with ⟨X, hXcard, hsep⟩
    rcases hwell.2 hS hT hdisj with ⟨Q, hQcard, hQstay⟩
    have hQcardS : Q.card = S.card := by
      simpa [hcard] using hQcard
    have hlarge : Δ * X.card < Q.card := by
      have hlt : Δ * X.card < Δ * k :=
        Nat.mul_lt_mul_of_pos_left hXcard hDelta
      exact hlt.trans_le (by simpa [hQcardS] using hk)
    rcases EdgePathPacking.exists_path_vertexSet_disjoint_of_card_gt_degree_mul
        (G := G) (S := S) (T := T) (X := X) (Δ := Δ)
        Q hdegree hdisj hlarge with
      ⟨i, havoid⟩
    let R : GraphPath H := (Q.path i).inInducedOnFinset (hQstay i)
    have hRconn : R.Connects S T := by
      simpa [R, GraphPath.inInducedOnFinset] using Q.connects i
    rcases hsep R hRconn with ⟨v, hvR, hvX⟩
    have hvQ : v ∈ (Q.path i).vertexSet := by
      simpa [R] using hvR
    exact False.elim (Finset.disjoint_left.mp havoid hvQ hvX)

/-- Path-packing form of `hasDisjointSTPaths_of_edgeWellLinkedIn_disjoint`,
with the paths certified to stay inside the cluster. -/
theorem exists_pathPacking_staysIn_of_edgeWellLinkedIn_disjoint
    [Fintype V]
    {C Terminals S T : Finset V} {Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ) (hDelta : 0 < Δ)
    (hwell : EdgeWellLinkedIn G C Terminals)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) (hdisj : Disjoint S T)
    (hk : Δ * k ≤ S.card) :
    ∃ P : PathPacking G S T, k ≤ P.card ∧ P.StaysIn C := by
  classical
  let H := inducedOnFinset G C
  rcases Menger.finite_vertex_menger_sharp (G := H) S T k with hpaths | hsmall
  · rcases hpaths with ⟨P, hPcard⟩
    refine ⟨P.mapLe (inducedOnFinset_le (G := G) (C := C)), by simpa using hPcard, ?_⟩
    exact InducedOnFinset.pathPacking_mapLe_staysIn
      (G := G) (C := C) (A := S) (B := T) P
      (subset_trans hS hwell.1) (subset_trans hT hwell.1)
  · rcases hsmall with ⟨X, hXcard, hsep⟩
    rcases hwell.2 hS hT hdisj with ⟨Q, hQcard, hQstay⟩
    have hQcardS : Q.card = S.card := by
      simpa [hcard] using hQcard
    have hlarge : Δ * X.card < Q.card := by
      have hlt : Δ * X.card < Δ * k :=
        Nat.mul_lt_mul_of_pos_left hXcard hDelta
      exact hlt.trans_le (by simpa [hQcardS] using hk)
    rcases EdgePathPacking.exists_path_vertexSet_disjoint_of_card_gt_degree_mul
        (G := G) (S := S) (T := T) (X := X) (Δ := Δ)
        Q hdegree hdisj hlarge with
      ⟨i, havoid⟩
    let R : GraphPath H := (Q.path i).inInducedOnFinset (hQstay i)
    have hRconn : R.Connects S T := by
      simpa [R, GraphPath.inInducedOnFinset] using Q.connects i
    rcases hsep R hRconn with ⟨v, hvR, hvX⟩
    have hvQ : v ∈ (Q.path i).vertexSet := by
      simpa [R] using hvR
    exact False.elim (Finset.disjoint_left.mp havoid hvQ hvX)

/-! ## Empty and one-path packing helpers -/

/-- The empty node-disjoint path packing between two terminal sets. -/
def emptyPathPacking (G : _root_.SimpleGraph V) (A B : Finset V) :
    PathPacking G A B where
  Index := PEmpty
  path := fun i => nomatch i
  connects := fun i => nomatch i
  node_disjoint := fun i => nomatch i

@[simp] theorem emptyPathPacking_card (A B : Finset V) :
    (emptyPathPacking G A B).card = 0 := by
  simp [emptyPathPacking, PathPacking.card]

theorem emptyPathPacking_staysIn (A B C : Finset V) :
    (emptyPathPacking G A B).StaysIn C := by
  intro i
  cases i

/-- An edge-disjoint packing with at most one path is also a node-disjoint
packing, since the node-disjointness condition only concerns distinct indices. -/
def edgePathPackingToPathPackingOfCardLeOne {A B : Finset V}
    (P : EdgePathPacking G A B) (hcard : P.card ≤ 1) :
    PathPacking G A B where
  Index := P.Index
  path := P.path
  connects := P.connects
  node_disjoint := by
    classical
    have hsub : Subsingleton P.Index := by
      apply Fintype.card_le_one_iff_subsingleton.mp
      simpa [EdgePathPacking.card] using hcard
    intro i j hij
    exfalso
    exact hij (Subsingleton.elim i j)

@[simp] theorem edgePathPackingToPathPackingOfCardLeOne_card
    {A B : Finset V} (P : EdgePathPacking G A B) (hcard : P.card ≤ 1) :
    (edgePathPackingToPathPackingOfCardLeOne P hcard).card = P.card := rfl

theorem edgePathPackingToPathPackingOfCardLeOne_staysIn
    {A B C : Finset V} (P : EdgePathPacking G A B) (hcard : P.card ≤ 1)
    (hstay : P.StaysIn C) :
    (edgePathPackingToPathPackingOfCardLeOne P hcard).StaysIn C := hstay

/-! ## Singleton terminal sets are automatically node-robust -/

/-- A terminal set of cardinality at most one is node-well-linked in any
ambient cluster containing it. -/
theorem nodeWellLinkedIn_of_card_le_one {C T : Finset V}
    (hTC : T ⊆ C) (hcard : T.card ≤ 1) :
    NodeWellLinkedIn G C T := by
  classical
  refine ⟨hTC, ?_⟩
  intro A B hA hB hdisj
  refine ⟨emptyPathPacking G A B, ?_, emptyPathPacking_staysIn A B C⟩
  have hUnion : A ∪ B ⊆ T := by
    intro v hv
    rcases mem_union.mp hv with hvA | hvB
    · exact hA hvA
    · exact hB hvB
  have hsum : A.card + B.card ≤ 1 := by
    have hcard_union : (A ∪ B).card = A.card + B.card := by
      rw [card_union_of_disjoint hdisj]
    have hle : (A ∪ B).card ≤ 1 :=
      (card_le_card hUnion).trans hcard
    omega
  have hmin : min A.card B.card = 0 := by
    omega
  simp [hmin]

/-- A terminal set of cardinality at most three is node-well-linked in a
connected ambient cluster containing it.

For two disjoint subfamilies `A` and `B` of such a terminal set, the smaller
side has size at most one.  If it has size zero the empty packing is enough; if
it has size one, connectedness of the cluster gives the unique required path. -/
theorem nodeWellLinkedIn_of_card_le_three_of_isCluster {C T : Finset V}
    (hC : IsCluster G C) (hTC : T ⊆ C) (hcard : T.card ≤ 3) :
    NodeWellLinkedIn G C T := by
  classical
  refine ⟨hTC, ?_⟩
  intro A B hA hB hdisj
  have hUnion : A ∪ B ⊆ T := by
    intro v hv
    rcases mem_union.mp hv with hvA | hvB
    · exact hA hvA
    · exact hB hvB
  have hsum : A.card + B.card ≤ 3 := by
    have hcard_union : (A ∪ B).card = A.card + B.card := by
      rw [card_union_of_disjoint hdisj]
    have hle : (A ∪ B).card ≤ 3 :=
      (card_le_card hUnion).trans hcard
    omega
  have hmin_le_one : min A.card B.card ≤ 1 := by
    omega
  have hmin_cases : min A.card B.card = 0 ∨ min A.card B.card = 1 := by
    omega
  rcases hmin_cases with hmin | hmin
  · refine ⟨emptyPathPacking G A B, ?_, emptyPathPacking_staysIn A B C⟩
    simp [hmin]
  · have hApos : 0 < A.card := by
      have hle := Nat.min_le_left A.card B.card
      omega
    have hBpos : 0 < B.card := by
      have hle := Nat.min_le_right A.card B.card
      omega
    rcases Finset.card_pos.mp hApos with ⟨a, haA⟩
    rcases Finset.card_pos.mp hBpos with ⟨b, hbB⟩
    have haC : a ∈ C := hTC (hA haA)
    have hbC : b ∈ C := hTC (hB hbB)
    let P : GraphPath G := GraphPath.ofConnectedInduce C hC a b haC hbC
    refine ⟨
      { Index := PUnit
        path := fun _ => P
        connects := fun _ => Or.inl ⟨by simpa [P] using haA, by simpa [P] using hbB⟩
        node_disjoint := ?_ }, ?_, ?_⟩
    · intro i j hij
      cases i
      cases j
      exact False.elim (hij rfl)
    · simp [PathPacking.card, hmin]
    · intro i
      simpa [P] using
        GraphPath.ofConnectedInduce_vertexSet_subset
          (G := G) C hC a b haC hbC

/-! ## The low-cardinality branch of Theorem 4.20 -/

/-- Theorem 4.20 is immediate when the terminal set has at most three
vertices: the whole terminal set is node-well-linked in a connected cluster,
and the stated lower bound is then just arithmetic from
`alphaNum ≤ alphaDen` and `3 ≤ Δ`. -/
theorem theorem420_nodeWellLinkedBoosting_of_card_le_three
    [Fintype V]
    {C T : Finset V} {alphaNum alphaDen Δ κ : ℕ}
    (hcluster : IsCluster G C)
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hcard : T.card = κ)
    (hwell : ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hkappa : κ ≤ 3) :
    ∃ T' : Finset V,
      T' ⊆ T ∧
        3 * alphaNum * κ ≤ 10 * Δ * alphaDen * T'.card ∧
          NodeWellLinkedIn G C T' := by
  classical
  refine ⟨T, subset_rfl, ?_, ?_⟩
  · have hTcard : T.card = κ := hcard
    have hκ : κ = T.card := hcard.symm
    have hpos_le : alphaNum ≤ Δ * alphaDen := by
      calc
        alphaNum ≤ alphaDen := halpha_le
        _ ≤ Δ * alphaDen := by
          have hΔpos : 1 ≤ Δ := by omega
          calc
            alphaDen = 1 * alphaDen := by simp
            _ ≤ Δ * alphaDen := Nat.mul_le_mul_right alphaDen hΔpos
    rw [hκ]
    have hmul : 3 * alphaNum * T.card ≤ 3 * (Δ * alphaDen) * T.card := by
      exact Nat.mul_le_mul_right T.card
        (Nat.mul_le_mul_left 3 hpos_le)
    have hfactor : 3 * (Δ * alphaDen) * T.card ≤
        10 * Δ * alphaDen * T.card := by
      have hcoef : 3 * (Δ * alphaDen) ≤ 10 * Δ * alphaDen := by
        nlinarith [Nat.zero_le (Δ * alphaDen)]
      exact Nat.mul_le_mul_right T.card hcoef
    exact hmul.trans hfactor
  · exact nodeWellLinkedIn_of_card_le_three_of_isCluster
      hcluster hwell.2.2.1 (by simpa [hcard] using hkappa)

/-- If two terminal sets each have cardinality at most one, edge-linkedness of
their union supplies node-linkedness between them. -/
theorem nodeLinkedIn_of_edgeWellLinked_card_le_one
    {C A B : Finset V}
    (hA : A ⊆ C) (hB : B ⊆ C) (hdisj : Disjoint A B)
    (hAcard : A.card ≤ 1) (_hBcard : B.card ≤ 1)
    (hEdge : EdgeWellLinkedIn G C (A ∪ B)) :
    NodeLinkedIn G C A B := by
  classical
  refine ⟨hA, hB, hdisj, ?_⟩
  intro A' B' hA' hB'
  have hAunion : A' ⊆ A ∪ B := by
    exact subset_trans hA' (subset_union_left (s₁ := A) (s₂ := B))
  have hBunion : B' ⊆ A ∪ B := by
    exact subset_trans hB' (subset_union_right (s₁ := A) (s₂ := B))
  have hdisj' : Disjoint A' B' :=
    hdisj.mono hA' hB'
  rcases hEdge.2 hAunion hBunion hdisj' with ⟨P, hPcard, hPstay⟩
  have hmin_le_one : min A'.card B'.card ≤ 1 := by
    exact (Nat.min_le_left A'.card B'.card).trans
      ((card_le_card hA').trans hAcard)
  refine ⟨edgePathPackingToPathPackingOfCardLeOne P ?_, ?_, ?_⟩
  · simpa [hPcard] using hmin_le_one
  · simp [hPcard]
  · exact edgePathPackingToPathPackingOfCardLeOne_staysIn P
      (by simpa [hPcard] using hmin_le_one) hPstay

/-! ## Section 4.6 assembly theorems -/

/-- Certificate data for the paper's Section 4.6 strongification step.

The data chooses smaller left and right nail sets in every cluster and, for
every gap, exactly the connector paths whose endpoints are the chosen right
nails of the left cluster and the chosen left nails of the next cluster.  It
also records the three strongness certificates for each cluster.

This structure is deliberately independent of how the data is obtained.  The
paper obtains it by applying Theorems 4.20 and 4.21; the construction theorem
below only checks that such data really assembles into a strong path-of-sets
system. -/
structure StrongificationData {ell w w' : ℕ}
    (P : PathOfSetsSystem G ell w) where
  /-- The retained width is positive. -/
  width_pos : 0 < w'
  /-- Retained left nail sets. -/
  left : Fin ell → Finset V
  /-- Retained right nail sets. -/
  right : Fin ell → Finset V
  /-- Retained left nails come from the original left nails. -/
  left_subset_left : ∀ i : Fin ell, left i ⊆ P.left i
  /-- Retained right nails come from the original right nails. -/
  right_subset_right : ∀ i : Fin ell, right i ⊆ P.right i
  /-- Each retained left nail set has the target width. -/
  left_card : ∀ i : Fin ell, (left i).card = w'
  /-- Each retained right nail set has the target width. -/
  right_card : ∀ i : Fin ell, (right i).card = w'
  /-- Retained connector-path indices across each gap. -/
  connectorIndexSet :
    (i : Fin ell) → (hi : i.1 + 1 < ell) →
      Finset (P.connector i hi).Index
  /-- Exactly `w'` connector paths are retained across each gap. -/
  connectorIndexSet_card :
    ∀ (i : Fin ell) (hi : i.1 + 1 < ell),
      (connectorIndexSet i hi).card = w'
  /-- The source endpoints of retained connector paths are precisely the
  retained right nails of the left cluster. -/
  sourceSet_eq_right :
    ∀ (i : Fin ell) (hi : i.1 + 1 < ell),
      (P.connector i hi).sourceSet (connectorIndexSet i hi) = right i
  /-- The target endpoints of retained connector paths are precisely the
  retained left nails of the next cluster. -/
  targetSet_eq_left_next :
    ∀ (i : Fin ell) (hi : i.1 + 1 < ell),
      (P.connector i hi).targetSet (connectorIndexSet i hi) =
        left ⟨i.1 + 1, hi⟩
  /-- The retained left nails are node-well-linked in their cluster. -/
  left_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (P.cluster i) (left i)
  /-- The retained right nails are node-well-linked in their cluster. -/
  right_nodeWellLinked :
    ∀ i : Fin ell, NodeWellLinkedIn G (P.cluster i) (right i)
  /-- The retained left and right nails are linked in their cluster. -/
  left_right_nodeLinked :
    ∀ i : Fin ell, NodeLinkedIn G (P.cluster i) (left i) (right i)

namespace StrongificationData

variable {ell w w' : ℕ} {P : PathOfSetsSystem G ell w}

/-- The path-of-sets system obtained from `StrongificationData` by keeping the
same clusters and restricting each connector family to the recorded path
indices. -/
noncomputable def toPathOfSetsSystem
    (D : StrongificationData (G := G) (w' := w') P) :
    PathOfSetsSystem G ell w' where
  length_pos := P.length_pos
  width_pos := D.width_pos
  cluster := P.cluster
  cluster_connected := P.cluster_connected
  cluster_disjoint := P.cluster_disjoint
  left := D.left
  right := D.right
  left_subset_cluster := by
    intro i v hv
    exact P.left_subset_cluster i (D.left_subset_left i hv)
  right_subset_cluster := by
    intro i v hv
    exact P.right_subset_cluster i (D.right_subset_right i hv)
  left_right_disjoint := by
    intro i
    exact Finset.disjoint_left.mpr fun v hvleft hvright =>
      Finset.disjoint_left.mp (P.left_right_disjoint i)
        (D.left_subset_left i hvleft) (D.right_subset_right i hvright)
  left_card := D.left_card
  right_card := D.right_card
  connector := by
    intro i hi
    exact ((P.connector i hi).restrictIndexSet (D.connectorIndexSet i hi)).copyTerminals
      (by simp [D.sourceSet_eq_right i hi])
      (by simp [D.targetSet_eq_left_next i hi])
  connector_card := by
    intro i hi
    rw [PerfectPathPacking.copyTerminals_card]
    rw [(P.connector i hi).restrictIndexSet_card (D.connectorIndexSet i hi)]
    exact D.connectorIndexSet_card i hi
  connector_internally_disjoint_clusters := by
    intro i hi j a
    simpa [PerfectPathPacking.copyTerminals] using
      P.connector_internally_disjoint_clusters i hi j a.1
  connector_mutually_nodeDisjoint := by
    intro i j hi hj hij a b
    simpa [PerfectPathPacking.copyTerminals, GraphPath.NodeDisjoint] using
      P.connector_mutually_nodeDisjoint hi hj hij a.1 b.1

/-- The strong path-of-sets system certified by `StrongificationData`. -/
noncomputable def toStrongPathOfSetsSystem
    (D : StrongificationData (G := G) (w' := w') P) :
    StrongPathOfSetsSystem G ell w' where
  toPathOfSetsSystem := D.toPathOfSetsSystem
  left_nodeWellLinked := D.left_nodeWellLinked
  right_nodeWellLinked := D.right_nodeWellLinked
  left_right_nodeLinked := D.left_right_nodeLinked

end StrongificationData

/-- Paper-shaped Section 4.6 assembly theorem.  A weak path-of-sets system,
together with selected strongification data of width `w'`, contains a strong
path-of-sets system with the same cluster sequence and retained connector
paths. -/
noncomputable def strong_pathOfSetsSystem_of_strongificationData
    {ell w w' : ℕ} (P : WeakPathOfSetsSystem G ell w)
    (D : StrongificationData (G := G) (P := P.toPathOfSetsSystem) (w' := w')) :
    StrongPathOfSetsSystem G ell w' :=
  D.toStrongPathOfSetsSystem

/-- Section 4.6 assembly step.  If a width restriction of a weak
path-of-sets system has, in every cluster, node-well-linked left nails,
node-well-linked right nails, and linked left/right nails, then that restricted
system is a strong path-of-sets system.

This theorem is intentionally stated with the three certificate families as
hypotheses.  The paper's Theorems 4.20 and 4.21 are precisely the external
inputs used to produce such certificates at constant-factor width. -/
noncomputable def strong_pathOfSetsSystem_of_restrictWidth_certificates
    {ell w w' : ℕ} (P : WeakPathOfSetsSystem G ell w)
    (hpos : 0 < w') (hle : w' ≤ w)
    (hleft :
      ∀ i : Fin ell,
        NodeWellLinkedIn G
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).cluster i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).left i))
    (hright :
      ∀ i : Fin ell,
        NodeWellLinkedIn G
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).cluster i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).right i))
    (hlinked :
      ∀ i : Fin ell,
        NodeLinkedIn G
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).cluster i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).left i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).right i)) :
    StrongPathOfSetsSystem G ell w' where
  toPathOfSetsSystem := P.toPathOfSetsSystem.restrictWidth hpos hle
  left_nodeWellLinked := hleft
  right_nodeWellLinked := hright
  left_right_nodeLinked := hlinked

/-- Fully self-contained width-one form of Section 4.6.  Any weak
path-of-sets system of positive width has a strong path-of-sets subsystem of
the same length and width one. -/
theorem weak_pathOfSetsSystem_to_strong_width_one
    {ell w : ℕ} (P : WeakPathOfSetsSystem G ell w) (hw : 0 < w) :
    Nonempty (StrongPathOfSetsSystem G ell 1) := by
  classical
  let hle : 1 ≤ w := Nat.succ_le_of_lt hw
  let Q : PathOfSetsSystem G ell 1 :=
    P.toPathOfSetsSystem.restrictWidth (by decide : 0 < 1) hle
  refine ⟨strong_pathOfSetsSystem_of_restrictWidth_certificates
    (P := P) (hpos := by decide) (hle := hle) ?_ ?_ ?_⟩
  · intro i
    apply nodeWellLinkedIn_of_card_le_one
    · exact (Q.left_subset_cluster i)
    · rw [Q.left_card i]
  · intro i
    apply nodeWellLinkedIn_of_card_le_one
    · exact (Q.right_subset_cluster i)
    · rw [Q.right_card i]
  · intro i
    have hsubset : Q.left i ∪ Q.right i ⊆ P.left i ∪ P.right i := by
      intro v hv
      rcases mem_union.mp hv with hvleft | hvright
      · exact mem_union_left _ <|
          P.toPathOfSetsSystem.leftTrim_subset_left hle i
            (by simpa [Q] using hvleft)
      · exact mem_union_right _ <|
          P.toPathOfSetsSystem.rightTrim_subset_right hle i
            (by simpa [Q] using hvright)
    have hEdge : EdgeWellLinkedIn G (Q.cluster i) (Q.left i ∪ Q.right i) := by
      simpa [Q] using (P.nails_edgeWellLinked i).mono_terminals hsubset
    apply nodeLinkedIn_of_edgeWellLinked_card_le_one
    · exact Q.left_subset_cluster i
    · exact Q.right_subset_cluster i
    · exact Q.left_right_disjoint i
    · rw [Q.left_card i]
    · rw [Q.right_card i]
    · exact hEdge

end Section46
end SimpleGraph

end Lax17Proofs
