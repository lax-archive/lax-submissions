import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Crossbars

This file formalizes the crossbar object introduced in Section 3 of
Chuzhoy--Tan.  An `(A, B, X)`-crossbar of width `rho` consists of `rho`
disjoint main paths from `A` to `B`, together with one disjoint spoke path from
each main path to `X`.
-/

namespace SimpleGraph

namespace GraphPath

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- A path connects another path `P` to a vertex set `X` when one endpoint lies
on `P` and the other endpoint lies in `X`. -/
def ConnectsPathToSet (Q P : GraphPath G) (X : Finset V) : Prop :=
  (Q.source ∈ P.vertexSet ∧ Q.target ∈ X) ∨
    (Q.target ∈ P.vertexSet ∧ Q.source ∈ X)

/-- A path intersects another path in exactly the singleton vertex `v`. -/
def MeetsExactlyAt (P Q : GraphPath G) (v : V) : Prop :=
  P.vertexSet ∩ Q.vertexSet = {v}

/-- The other endpoint of a path relative to one endpoint candidate.  If the
candidate is the source, this returns the target; otherwise it returns the
source. -/
def otherEndpoint (P : GraphPath G) (v : V) : V :=
  if P.source = v then P.target else P.source

/-- A vertex lying on both paths in an exact singleton intersection is the
specified intersection vertex. -/
theorem eq_of_mem_of_meetsExactlyAt {P Q : GraphPath G} {v u : V}
    (hmeet : P.MeetsExactlyAt Q v)
    (huP : u ∈ P.vertexSet) (huQ : u ∈ Q.vertexSet) :
    u = v := by
  have hu : u ∈ P.vertexSet ∩ Q.vertexSet := Finset.mem_inter.mpr ⟨huP, huQ⟩
  rw [MeetsExactlyAt] at hmeet
  rw [hmeet] at hu
  simpa using hu

/-- The other endpoint selector always returns an endpoint of the same path. -/
theorem otherEndpoint_mem_vertexSet {P : GraphPath G} {v : V} :
    P.otherEndpoint v ∈ P.vertexSet := by
  by_cases hsource : P.source = v
  · simp [otherEndpoint, hsource]
  · simp [otherEndpoint, hsource]

/-- The other endpoint selector returns one of the two endpoints of the path. -/
theorem otherEndpoint_isEndpoint (P : GraphPath G) (v : V) :
    P.IsEndpoint (P.otherEndpoint v) := by
  by_cases hsource : P.source = v
  · simp [otherEndpoint, IsEndpoint, hsource]
  · simp [otherEndpoint, IsEndpoint, hsource]

/-- If `Q` connects a path `P` to a set `X` and meets `P` exactly at endpoint
`v`, then the other endpoint of `Q` lies in `X`. -/
theorem otherEndpoint_mem_of_connectsPathToSet_meetsExactlyAt
    {Q P : GraphPath G} {X : Finset V} {v : V}
    (hconn : Q.ConnectsPathToSet P X)
    (hmeet : P.MeetsExactlyAt Q v) :
    Q.otherEndpoint v ∈ X := by
  rcases hconn with hconn | hconn
  · rcases hconn with ⟨hsourceP, htargetX⟩
    have hsource_eq :
        Q.source = v :=
      eq_of_mem_of_meetsExactlyAt hmeet hsourceP Q.source_mem_vertexSet
    simp [otherEndpoint, hsource_eq, htargetX]
  · rcases hconn with ⟨htargetP, hsourceX⟩
    have htarget_eq :
        Q.target = v :=
      eq_of_mem_of_meetsExactlyAt hmeet htargetP Q.target_mem_vertexSet
    by_cases hsource : Q.source = v
    · have htarget_source : Q.target = Q.source := htarget_eq.trans hsource.symm
      simpa [otherEndpoint, hsource, htarget_source] using hsourceX
    · simp [otherEndpoint, hsource, hsourceX]

end GraphPath

/-- An `(A, B, X)`-crossbar of width `rho`.

The fields follow the Section 3 definition: main paths are pairwise disjoint,
spoke paths are pairwise disjoint, each spoke meets its own main path in a
single endpoint of the spoke, and each spoke is disjoint from all other main
paths.
-/
structure Crossbar {V : Type*} [DecidableEq V]
    (G : _root_.SimpleGraph V) (A B X : Finset V) (rho : ℕ) where
  /-- The finite index type for the `rho` main paths. -/
  Index : Type
  /-- The index type is finite. -/
  [indexFintype : Fintype Index]
  /-- The index type has decidable equality. -/
  [indexDecidableEq : DecidableEq Index]
  /-- The crossbar has exactly `rho` main paths. -/
  card_index : Fintype.card Index = rho
  /-- Main paths connecting `A` to `B`. -/
  mainPath : Index → GraphPath G
  /-- Each main path connects `A` to `B`. -/
  main_connects : ∀ i : Index, (mainPath i).Connects A B
  /-- Main paths are pairwise node-disjoint. -/
  main_nodeDisjoint :
    Pairwise fun i j => GraphPath.NodeDisjoint (mainPath i) (mainPath j)
  /-- Spoke paths, one for each main path. -/
  spokePath : Index → GraphPath G
  /-- Each spoke connects its corresponding main path to `X`. -/
  spoke_connects :
    ∀ i : Index, (spokePath i).ConnectsPathToSet (mainPath i) X
  /-- Spoke paths are pairwise node-disjoint. -/
  spoke_nodeDisjoint :
    Pairwise fun i j => GraphPath.NodeDisjoint (spokePath i) (spokePath j)
  /-- Each spoke meets its own main path in exactly one vertex, and that vertex
  is an endpoint of the spoke. -/
  spoke_meets_own_main :
    ∀ i : Index, ∃ v : V,
      (spokePath i).IsEndpoint v ∧
        (mainPath i).MeetsExactlyAt (spokePath i) v
  /-- The endpoint of each spoke opposite its attachment point lies in `X` and
  is not on the corresponding main path.  This rules out the degenerate case
  where the spoke is a trivial path at a vertex already lying in `X`. -/
  spoke_exits_own_main :
    ∀ i : Index, ∃ v : V,
      (spokePath i).IsEndpoint v ∧
        (mainPath i).MeetsExactlyAt (spokePath i) v ∧
          (spokePath i).otherEndpoint v ∈ X ∧
            (spokePath i).otherEndpoint v ∉ (mainPath i).vertexSet
  /-- Each spoke is disjoint from every other main path. -/
  spoke_disjoint_other_main :
    ∀ ⦃i j : Index⦄, i ≠ j →
      GraphPath.NodeDisjoint (mainPath i) (spokePath j)

namespace Crossbar

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {rho : ℕ}

instance (C : Crossbar G A B X rho) : Fintype C.Index := C.indexFintype
instance (C : Crossbar G A B X rho) : DecidableEq C.Index := C.indexDecidableEq

/-- The main-path index type has cardinality equal to the crossbar width. -/
theorem card_eq_width (C : Crossbar G A B X rho) :
    Fintype.card C.Index = rho :=
  C.card_index

/-- The main paths of a crossbar form a path packing from `A` to `B`. -/
def mainPathPacking (C : Crossbar G A B X rho) : PathPacking G A B where
  Index := C.Index
  path := C.mainPath
  connects := C.main_connects
  node_disjoint := C.main_nodeDisjoint

/-- The main-path packing has the crossbar width. -/
@[simp] theorem mainPathPacking_card (C : Crossbar G A B X rho) :
    C.mainPathPacking.card = rho := by
  simpa [mainPathPacking, PathPacking.card] using C.card_index

@[simp] theorem mainPathPacking_path_vertexSet
    (C : Crossbar G A B X rho) (i : C.Index) :
    (C.mainPathPacking.path i).vertexSet = (C.mainPath i).vertexSet := rfl

@[simp] theorem mainPathPacking_path_edgeSet
    (C : Crossbar G A B X rho) (i : C.Index) :
    (C.mainPathPacking.path i).edgeSet = (C.mainPath i).edgeSet := rfl

/-- Reindex a crossbar by an equivalent finite index type. -/
noncomputable def reindex {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) :
    Crossbar G A B X rho where
  Index := ι
  card_index := by
    calc
      Fintype.card ι = Fintype.card C.Index := Fintype.card_congr e
      _ = rho := C.card_index
  mainPath := fun i => C.mainPath (e i)
  main_connects := fun i => C.main_connects (e i)
  main_nodeDisjoint := by
    intro i j hij
    exact C.main_nodeDisjoint (fun h => hij (e.injective h))
  spokePath := fun i => C.spokePath (e i)
  spoke_connects := fun i => C.spoke_connects (e i)
  spoke_nodeDisjoint := by
    intro i j hij
    exact C.spoke_nodeDisjoint (fun h => hij (e.injective h))
  spoke_meets_own_main := fun i => C.spoke_meets_own_main (e i)
  spoke_exits_own_main := fun i => C.spoke_exits_own_main (e i)
  spoke_disjoint_other_main := by
    intro i j hij
    exact C.spoke_disjoint_other_main (fun h => hij (e.injective h))

@[simp] theorem reindex_mainPathPacking_card
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) :
    (C.reindex e).mainPathPacking.card = rho := by
  simpa [mainPathPacking, PathPacking.card] using (C.reindex e).card_index

@[simp] theorem reindex_mainPath_vertexSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) (i : ι) :
    ((C.reindex e).mainPath i).vertexSet = (C.mainPath (e i)).vertexSet := rfl

@[simp] theorem reindex_mainPath_edgeSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) (i : ι) :
    ((C.reindex e).mainPath i).edgeSet = (C.mainPath (e i)).edgeSet := rfl

@[simp] theorem reindex_mainPathPacking_path_vertexSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) (i : ι) :
    (((C.reindex e).mainPathPacking).path i).vertexSet =
      (C.mainPath (e i)).vertexSet := rfl

@[simp] theorem reindex_mainPathPacking_path_edgeSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) (i : ι) :
    (((C.reindex e).mainPathPacking).path i).edgeSet =
      (C.mainPath (e i)).edgeSet := rfl

@[simp] theorem reindex_spokePath_vertexSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) (i : ι) :
    ((C.reindex e).spokePath i).vertexSet = (C.spokePath (e i)).vertexSet := rfl

@[simp] theorem reindex_spokePath_edgeSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Crossbar G A B X rho) (e : ι ≃ C.Index) (i : ι) :
    ((C.reindex e).spokePath i).edgeSet = (C.spokePath (e i)).edgeSet := rfl

/-- The canonical equivalence from `Fin rho` to the crossbar index type. -/
noncomputable def finIndexEquiv (C : Crossbar G A B X rho) :
    Fin rho ≃ C.Index :=
  (finCongr C.card_index.symm).trans (Fintype.equivFin C.Index).symm

/-- Reindex a crossbar by `Fin rho`. -/
noncomputable def finReindex (C : Crossbar G A B X rho) :
    Crossbar G A B X rho :=
  C.reindex C.finIndexEquiv

@[simp] theorem finReindex_mainPathPacking_card
    (C : Crossbar G A B X rho) :
    C.finReindex.mainPathPacking.card = rho := by
  simp [finReindex]

/-- When the terminal sides have the same size as the crossbar width, the main
paths can be oriented as a perfect packing from `A` to `B`. -/
noncomputable def mainPerfectPathPacking
    (C : Crossbar G A B X rho) (hA : A.card = rho) (hB : B.card = rho) :
    PerfectPathPacking G A B :=
  C.mainPathPacking.toPerfectOfCardEq
    (C.mainPathPacking_card.trans hA.symm)
    (C.mainPathPacking_card.trans hB.symm)

/-- The perfect main-path packing still has the crossbar width. -/
@[simp] theorem mainPerfectPathPacking_card
    (C : Crossbar G A B X rho) (hA : A.card = rho) (hB : B.card = rho) :
    (C.mainPerfectPathPacking hA hB).card = rho := by
  simpa [mainPerfectPathPacking, PathPacking.toPerfectOfCardEq,
    PerfectPathPacking.card, PathPacking.card] using C.card_index

/-- A crossbar in a graph is also a crossbar in any same-vertex supergraph. -/
def mapLe (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') : Crossbar G' A B X rho where
  Index := C.Index
  card_index := C.card_index
  mainPath := fun i => (C.mainPath i).mapLe hGG'
  main_connects := by
    intro i
    simpa [GraphPath.Connects] using C.main_connects i
  main_nodeDisjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using C.main_nodeDisjoint hij
  spokePath := fun i => (C.spokePath i).mapLe hGG'
  spoke_connects := by
    intro i
    simpa [GraphPath.ConnectsPathToSet] using C.spoke_connects i
  spoke_nodeDisjoint := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using C.spoke_nodeDisjoint hij
  spoke_meets_own_main := by
    intro i
    rcases C.spoke_meets_own_main i with ⟨v, hvendpoint, hmeet⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [GraphPath.mapLe, GraphPath.IsEndpoint] using hvendpoint
    · simpa [GraphPath.MeetsExactlyAt] using hmeet
  spoke_exits_own_main := by
    intro i
    rcases C.spoke_exits_own_main i with
      ⟨v, hvendpoint, hmeet, hotherX, hotherMain⟩
    refine ⟨v, ?_, ?_, ?_, ?_⟩
    · simpa [GraphPath.mapLe, GraphPath.IsEndpoint] using hvendpoint
    · simpa [GraphPath.MeetsExactlyAt] using hmeet
    · simpa [GraphPath.mapLe, GraphPath.otherEndpoint] using hotherX
    · change
        ((C.spokePath i).mapLe hGG').otherEndpoint v ∉
          ((C.mainPath i).mapLe hGG').vertexSet
      rw [GraphPath.mapLe_vertexSet]
      simpa [GraphPath.mapLe, GraphPath.otherEndpoint] using hotherMain
  spoke_disjoint_other_main := by
    intro i j hij
    simpa [GraphPath.NodeDisjoint] using C.spoke_disjoint_other_main hij

@[simp] theorem mapLe_mainPath_vertexSet
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') (i : (C.mapLe hGG').Index) :
    ((C.mapLe hGG').mainPath i).vertexSet = (C.mainPath i).vertexSet := by
  simp [mapLe]

@[simp] theorem mapLe_mainPath_edgeSet
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') (i : (C.mapLe hGG').Index) :
    ((C.mapLe hGG').mainPath i).edgeSet = (C.mainPath i).edgeSet := by
  simp [mapLe]

@[simp] theorem mapLe_finIndexEquiv
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') :
    (C.mapLe hGG').finIndexEquiv = C.finIndexEquiv := rfl

@[simp] theorem mapLe_finReindex_mainPath_edgeSet
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') (i : Fin rho) :
    ((C.mapLe hGG').finReindex.mainPath i).edgeSet =
      (C.finReindex.mainPath i).edgeSet := by
  simp [finReindex]
  rfl

@[simp] theorem mapLe_finReindex_mainPathPacking_path_edgeSet
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') (i : Fin rho) :
    (((C.mapLe hGG').finReindex.mainPathPacking).path i).edgeSet =
      (C.finReindex.mainPath i).edgeSet := by
  simp [finReindex]
  rfl

@[simp] theorem mapLe_spokePath_vertexSet
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') (i : (C.mapLe hGG').Index) :
    ((C.mapLe hGG').spokePath i).vertexSet = (C.spokePath i).vertexSet := by
  simp [mapLe]

@[simp] theorem mapLe_spokePath_edgeSet
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') (i : (C.mapLe hGG').Index) :
    ((C.mapLe hGG').spokePath i).edgeSet = (C.spokePath i).edgeSet := by
  simp [mapLe]

@[simp] theorem mapLe_finReindex_spokePath_edgeSet
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') (i : Fin rho) :
    ((C.mapLe hGG').finReindex.spokePath i).edgeSet =
      (C.finReindex.spokePath i).edgeSet := by
  simp [finReindex]
  rfl

@[simp] theorem mapLe_mainPathPacking_card
    (C : Crossbar G A B X rho) {G' : _root_.SimpleGraph V}
    (hGG' : G ≤ G') :
    ((C.mapLe hGG').mainPathPacking).card = rho := by
  simp

end Crossbar

end SimpleGraph

end Lax17Proofs
