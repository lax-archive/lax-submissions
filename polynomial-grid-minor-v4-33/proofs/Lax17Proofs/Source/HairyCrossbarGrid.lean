import Lax17Proofs.Source.HairyCrossbarGridContract
import Lax17Proofs.Source.HairyCrossbarGridIndex
import Lax17Proofs.Source.MinorTransitivity
import Lax17Proofs.Source.PathOfSetsGrid
import Lax17Proofs.Source.Paths
import Lax17Proofs.Source.SeparatorGridMinor

namespace Lax17Proofs

universe u v w

/-!
# Assembling crossbars into a grid minor

This module exposes the Section 3 assembly theorem outside the contract
namespace.  The small-parameter branch is proved here from the `1 x 1` grid
minor in the base strong path-of-sets system; the contract supplies only the
large crossbar-grid assembly.
-/

namespace SimpleGraph
namespace HairyCrossbarGrid


/-- View a crossbar supplied in the local graph `C_i ∪ Q_i` as an ambient
crossbar.  The path vertex sets are unchanged by `mapLe`; only the graph in
which their edges are interpreted changes. -/
noncomputable def localCrossbarAsAmbient
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) :
    Crossbar G (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2) :=
  (Classical.choice (hcrossbars i hi)).mapLe (Hsys.hairLocalGraph_le i)

@[simp] theorem localCrossbarAsAmbient_mainPath_vertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ((localCrossbarAsAmbient Hsys hcrossbars i hi).mainPath a).vertexSet =
      ((Classical.choice (hcrossbars i hi)).mainPath a).vertexSet := by
  simp [localCrossbarAsAmbient]

@[simp] theorem localCrossbarAsAmbient_mainPath_edgeSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ((localCrossbarAsAmbient Hsys hcrossbars i hi).mainPath a).edgeSet =
      ((Classical.choice (hcrossbars i hi)).mainPath a).edgeSet := by
  simp [localCrossbarAsAmbient]

/-- An ambiently viewed local crossbar main path still uses only edges of the
local graph it came from. -/
theorem localCrossbarAsAmbient_mainPath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ↑((localCrossbarAsAmbient Hsys hcrossbars i hi).mainPath a).edgeSet ⊆
      (Hsys.hairLocalGraph i).edgeSet := by
  intro e he
  rw [localCrossbarAsAmbient_mainPath_edgeSet] at he
  exact ((Classical.choice (hcrossbars i hi)).mainPath a).edgeSet_subset_edgeSet he

/-- The source of a local crossbar main path lies in the corresponding base
cluster. -/
theorem localCrossbar_mainPath_source_mem_cluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (Classical.choice (hcrossbars i hi)).Index) :
    ((Classical.choice (hcrossbars i hi)).mainPath a).source ∈
      Hsys.base.cluster i := by
  let C := Classical.choice (hcrossbars i hi)
  rcases C.main_connects a with ⟨hsource, _htarget⟩ | ⟨hsource, _htarget⟩
  · exact Hsys.base.left_subset_cluster i hsource
  · exact Hsys.base.right_subset_cluster i hsource

/-- A local crossbar main path stays in the base cluster plus the local
hair-connector footprint. -/
theorem localCrossbar_mainPath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (Classical.choice (hcrossbars i hi)).Index) :
    ((Classical.choice (hcrossbars i hi)).mainPath a).vertexSet ⊆
      Hsys.base.cluster i ∪ (Hsys.hairConnector i).toPathPacking.vertexSet := by
  exact Hsys.hairLocalGraph_path_vertexSet_subset_localVertexSet_of_source_mem_cluster
    i ((Classical.choice (hcrossbars i hi)).mainPath a)
    (localCrossbar_mainPath_source_mem_cluster Hsys hcrossbars i hi a)

/-- An ambiently viewed local crossbar main path stays in the same local
footprint. -/
theorem localCrossbarAsAmbient_mainPath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ((localCrossbarAsAmbient Hsys hcrossbars i hi).mainPath a).vertexSet ⊆
      Hsys.base.cluster i ∪ (Hsys.hairConnector i).toPathPacking.vertexSet := by
  simpa [localCrossbarAsAmbient] using
    localCrossbar_mainPath_vertexSet_subset_localVertexSet Hsys hcrossbars i hi a

/-- The source of a local crossbar spoke path lies in the local footprint. -/
theorem localCrossbar_spokePath_source_mem_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (Classical.choice (hcrossbars i hi)).Index) :
    ((Classical.choice (hcrossbars i hi)).spokePath a).source ∈
      Hsys.base.cluster i ∪ (Hsys.hairConnector i).toPathPacking.vertexSet := by
  let C := Classical.choice (hcrossbars i hi)
  rcases C.spoke_connects a with ⟨hsourceMain, _htargetY⟩ |
      ⟨_htargetMain, hsourceY⟩
  · exact localCrossbar_mainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars i hi a hsourceMain
  · exact Finset.mem_union_right _
      (Hsys.y_subset_hairConnector_vertexSet i hsourceY)

/-- A local crossbar spoke path stays in the base cluster plus the local
hair-connector footprint. -/
theorem localCrossbar_spokePath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (Classical.choice (hcrossbars i hi)).Index) :
    ((Classical.choice (hcrossbars i hi)).spokePath a).vertexSet ⊆
      Hsys.base.cluster i ∪ (Hsys.hairConnector i).toPathPacking.vertexSet := by
  exact Hsys.hairLocalGraph_path_vertexSet_subset_localVertexSet i
    ((Classical.choice (hcrossbars i hi)).spokePath a)
    (localCrossbar_spokePath_source_mem_localVertexSet Hsys hcrossbars i hi a)

/-- An ambiently viewed local crossbar spoke path stays in the same local
footprint. -/
theorem localCrossbarAsAmbient_spokePath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ((localCrossbarAsAmbient Hsys hcrossbars i hi).spokePath a).vertexSet ⊆
      Hsys.base.cluster i ∪ (Hsys.hairConnector i).toPathPacking.vertexSet := by
  simpa [localCrossbarAsAmbient] using
    localCrossbar_spokePath_vertexSet_subset_localVertexSet Hsys hcrossbars i hi a

@[simp] theorem localCrossbarAsAmbient_spokePath_vertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ((localCrossbarAsAmbient Hsys hcrossbars i hi).spokePath a).vertexSet =
      ((Classical.choice (hcrossbars i hi)).spokePath a).vertexSet := by
  simp [localCrossbarAsAmbient]

@[simp] theorem localCrossbarAsAmbient_spokePath_edgeSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ((localCrossbarAsAmbient Hsys hcrossbars i hi).spokePath a).edgeSet =
      ((Classical.choice (hcrossbars i hi)).spokePath a).edgeSet := by
  simp [localCrossbarAsAmbient]

/-- An ambiently viewed local crossbar spoke still uses only edges of the
local graph it came from. -/
theorem localCrossbarAsAmbient_spokePath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i)
    (a : (localCrossbarAsAmbient Hsys hcrossbars i hi).Index) :
    ↑((localCrossbarAsAmbient Hsys hcrossbars i hi).spokePath a).edgeSet ⊆
      (Hsys.hairLocalGraph i).edgeSet := by
  intro e he
  rw [localCrossbarAsAmbient_spokePath_edgeSet] at he
  exact ((Classical.choice (hcrossbars i hi)).spokePath a).edgeSet_subset_edgeSet he

/-- A normalized main path of an ambiently viewed local crossbar still uses
only edges of the local hair graph it came from. -/
theorem localCrossbarAsAmbient_finReindex_mainPath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) (a : Fin (g ^ 2)) :
    ↑((localCrossbarAsAmbient Hsys hcrossbars i hi).finReindex.mainPath a).edgeSet ⊆
      (Hsys.hairLocalGraph i).edgeSet := by
  let C := Classical.choice (hcrossbars i hi)
  intro e he
  have heLocal : e ∈ ↑(C.finReindex.mainPath a).edgeSet := by
    simpa only [localCrossbarAsAmbient, Crossbar.mapLe_finReindex_mainPath_edgeSet,
      Finset.mem_coe, C] using he
  exact (C.finReindex.mainPath a).edgeSet_subset_edgeSet heLocal

/-- A normalized main path of the main-path packing of an ambiently viewed
local crossbar still uses only edges of the local hair graph it came from. -/
theorem localCrossbarAsAmbient_finReindex_mainPathPacking_path_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) (a : Fin (g ^ 2)) :
    ↑(((localCrossbarAsAmbient Hsys hcrossbars i hi).finReindex.mainPathPacking).path a).edgeSet ⊆
      (Hsys.hairLocalGraph i).edgeSet := by
  let C := Classical.choice (hcrossbars i hi)
  intro e he
  have heLocal : e ∈ ↑(C.finReindex.mainPath a).edgeSet := by
    simpa only [localCrossbarAsAmbient,
      Crossbar.mapLe_finReindex_mainPathPacking_path_edgeSet,
      Finset.mem_coe, C] using he
  exact (C.finReindex.mainPath a).edgeSet_subset_edgeSet heLocal

/-- A normalized main path of the main-path packing of an ambiently viewed
local crossbar stays in the corresponding local footprint. -/
theorem localCrossbarAsAmbient_finReindex_mainPathPacking_path_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) (a : Fin (g ^ 2)) :
    (((localCrossbarAsAmbient Hsys hcrossbars i hi).finReindex.mainPathPacking).path a).vertexSet ⊆
      Hsys.base.cluster i ∪ (Hsys.hairConnector i).toPathPacking.vertexSet := by
  simpa [Crossbar.finReindex, Crossbar.mainPathPacking] using
    localCrossbarAsAmbient_mainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars i hi
      ((localCrossbarAsAmbient Hsys hcrossbars i hi).finIndexEquiv a)

/-- A normalized spoke of an ambiently viewed local crossbar still uses only
edges of the local hair graph it came from. -/
theorem localCrossbarAsAmbient_finReindex_spokePath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) (a : Fin (g ^ 2)) :
    ↑((localCrossbarAsAmbient Hsys hcrossbars i hi).finReindex.spokePath a).edgeSet ⊆
      (Hsys.hairLocalGraph i).edgeSet := by
  let C := Classical.choice (hcrossbars i hi)
  intro e he
  have heLocal : e ∈ ↑(C.finReindex.spokePath a).edgeSet := by
    simpa only [localCrossbarAsAmbient, Crossbar.mapLe_finReindex_spokePath_edgeSet,
      Finset.mem_coe, C] using he
  exact (C.finReindex.spokePath a).edgeSet_subset_edgeSet heLocal

/-- A normalized spoke of an ambiently viewed local crossbar stays in the
corresponding local footprint. -/
theorem localCrossbarAsAmbient_finReindex_spokePath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) (a : Fin (g ^ 2)) :
    ((localCrossbarAsAmbient Hsys hcrossbars i hi).finReindex.spokePath a).vertexSet ⊆
      Hsys.base.cluster i ∪ (Hsys.hairConnector i).toPathPacking.vertexSet := by
  simpa [Crossbar.finReindex] using
    localCrossbarAsAmbient_spokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars i hi
      ((localCrossbarAsAmbient Hsys hcrossbars i hi).finIndexEquiv a)

/-- Local crossbars can be supplied wherever an ambient crossbar family is
needed.  This is a transparent definition, not an opaque theorem, so selecting
from the returned `Nonempty` family gives the ambient view of the local
crossbar. -/
@[reducible] noncomputable def ambientCrossbars_of_local
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))) :
    ∀ i : Fin ell, OneBasedOdd i →
      Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
        (Hsys.y i) (g ^ 2)) :=
  fun i hi => ⟨localCrossbarAsAmbient Hsys hcrossbars i hi⟩

/-- Choose the crossbar supplied at an odd one-based cluster. -/
noncomputable def oddCrossbar
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) :
    Crossbar G (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2) :=
  Classical.choice (hcrossbars i hi)

/-- The main paths of the chosen odd-cluster crossbar as a path packing from
the left nails to the right nails. -/
noncomputable def oddCrossbarMainPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) :
    PathPacking G (Hsys.base.left i) (Hsys.base.right i) :=
  (oddCrossbar Hsys hcrossbars i hi).mainPathPacking

/-- The chosen odd-cluster main-path packing has exactly `g^2` paths. -/
@[simp] theorem oddCrossbarMainPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) :
    (oddCrossbarMainPacking Hsys hcrossbars i hi).card = g ^ 2 := by
  simp [oddCrossbarMainPacking, oddCrossbar]

/-- The chosen odd-cluster main paths are pairwise node-disjoint. -/
theorem oddCrossbarMainPacking_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (i : Fin ell) (hi : OneBasedOdd i) :
    Pairwise fun a b =>
      GraphPath.NodeDisjoint
        ((oddCrossbarMainPacking Hsys hcrossbars i hi).path a)
        ((oddCrossbarMainPacking Hsys hcrossbars i hi).path b) :=
  (oddCrossbarMainPacking Hsys hcrossbars i hi).node_disjoint

/-- Choose the crossbars at the first `m` odd one-based clusters. -/
noncomputable def selectedOddCrossbar
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Crossbar G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i))
      (Hsys.y (oddClusterIndex hlen i)) (g ^ 2) :=
  oddCrossbar Hsys hcrossbars (oddClusterIndex hlen i)
    (oddClusterIndex_oneBasedOdd hlen i)

/-- The selected odd-cluster crossbar with its path index normalized to
`Fin (g^2)`. -/
noncomputable def selectedOddCrossbarFin
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Crossbar G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i))
      (Hsys.y (oddClusterIndex hlen i)) (g ^ 2) :=
  (selectedOddCrossbar Hsys hcrossbars hlen i).finReindex

/-- The main paths of a selected odd-cluster crossbar. -/
noncomputable def selectedOddCrossbarMainPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PathPacking G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i)) :=
  (selectedOddCrossbar Hsys hcrossbars hlen i).mainPathPacking

@[simp] theorem selectedOddCrossbarMainPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarMainPacking Hsys hcrossbars hlen i).card = g ^ 2 := by
  simp [selectedOddCrossbarMainPacking, selectedOddCrossbar, oddCrossbar]

/-- The selected odd-cluster main paths are pairwise node-disjoint. -/
theorem selectedOddCrossbarMainPacking_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Pairwise fun a b =>
      GraphPath.NodeDisjoint
        ((selectedOddCrossbarMainPacking Hsys hcrossbars hlen i).path a)
        ((selectedOddCrossbarMainPacking Hsys hcrossbars hlen i).path b) :=
  (selectedOddCrossbarMainPacking Hsys hcrossbars hlen i).node_disjoint

/-- The main paths of a selected odd-cluster crossbar, indexed by
`Fin (g^2)`. -/
noncomputable def selectedOddCrossbarFinMainPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PathPacking G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i)) :=
  (selectedOddCrossbarFin Hsys hcrossbars hlen i).mainPathPacking

@[simp] theorem selectedOddCrossbarFinMainPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarFinMainPacking Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simp [selectedOddCrossbarFinMainPacking, selectedOddCrossbarFin]

/-- The normalized selected odd-cluster main paths are pairwise
node-disjoint. -/
theorem selectedOddCrossbarFinMainPacking_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Pairwise fun a b =>
      GraphPath.NodeDisjoint
        ((selectedOddCrossbarFinMainPacking Hsys hcrossbars hlen i).path a)
        ((selectedOddCrossbarFinMainPacking Hsys hcrossbars hlen i).path b) :=
  (selectedOddCrossbarFinMainPacking Hsys hcrossbars hlen i).node_disjoint

/-- The main paths of a selected odd-cluster crossbar, indexed by grid
coordinates.  The path indexed by `(r,c)` is the normalized path with flat
index `r * g + c`. -/
noncomputable def selectedOddCrossbarGridMainPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PathPacking G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i)) :=
  (selectedOddCrossbarFinMainPacking Hsys hcrossbars hlen i).reindex
    (gridVertexEquivFin g)

@[simp] theorem selectedOddCrossbarGridMainPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simp [selectedOddCrossbarGridMainPacking]

/-- The grid-indexed selected odd-cluster main paths are pairwise
node-disjoint. -/
theorem selectedOddCrossbarGridMainPacking_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Pairwise fun a b =>
      GraphPath.NodeDisjoint
        ((selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).path a)
        ((selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).path b) :=
  (selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).node_disjoint

/-- The left nail vertices actually used by the selected grid-indexed
crossbar main paths. -/
noncomputable def selectedOddCrossbarGridMainSourceSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  (selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).sourceSet

/-- The right nail vertices actually used by the selected grid-indexed
crossbar main paths. -/
noncomputable def selectedOddCrossbarGridMainTargetSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  (selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).targetSet

@[simp] theorem selectedOddCrossbarGridMainSourceSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simp [selectedOddCrossbarGridMainSourceSet]

@[simp] theorem selectedOddCrossbarGridMainTargetSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simp [selectedOddCrossbarGridMainTargetSet]

/-- The selected source terminals are contained in the selected cluster's left
nail set. -/
theorem selectedOddCrossbarGridMainSourceSet_subset_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i ⊆
      Hsys.base.left (oddClusterIndex hlen i) :=
  (selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).sourceSet_subset_left

/-- The selected target terminals are contained in the selected cluster's
right nail set. -/
theorem selectedOddCrossbarGridMainTargetSet_subset_right
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
      Hsys.base.right (oddClusterIndex hlen i) :=
  (selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).targetSet_subset_right

/-- The main path of a selected odd-cluster crossbar at grid coordinate
`x`. -/
noncomputable def selectedOddCrossbarGridMainPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    GraphPath G :=
  (selectedOddCrossbarGridMainPacking Hsys hcrossbars hlen i).path x

@[simp] theorem selectedOddCrossbarGridMainPath_vertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet =
      ((selectedOddCrossbarFinMainPacking Hsys hcrossbars hlen i).path
        (gridVertexEquivFin g x)).vertexSet := rfl

/-- The spoke path of a selected odd-cluster crossbar at grid coordinate
`x`. -/
noncomputable def selectedOddCrossbarGridSpokePath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    GraphPath G :=
  (selectedOddCrossbarFin Hsys hcrossbars hlen i).spokePath
    (gridVertexEquivFin g x)

/-- A selected grid-indexed spoke connects its corresponding main path to the
hair endpoint set. -/
theorem selectedOddCrossbarGridSpoke_connects
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).ConnectsPathToSet
      (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x)
      (Hsys.y (oddClusterIndex hlen i)) := by
  simpa [selectedOddCrossbarGridSpokePath, selectedOddCrossbarGridMainPath,
    selectedOddCrossbarGridMainPacking, selectedOddCrossbarFinMainPacking]
    using
      (selectedOddCrossbarFin Hsys hcrossbars hlen i).spoke_connects
        (gridVertexEquivFin g x)

/-- The grid-indexed selected spokes are pairwise node-disjoint. -/
theorem selectedOddCrossbarGridSpoke_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Pairwise fun x y =>
      GraphPath.NodeDisjoint
        (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x)
        (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i y) := by
  intro x y hxy
  exact (selectedOddCrossbarFin Hsys hcrossbars hlen i).spoke_nodeDisjoint
    (fun h => hxy ((gridVertexEquivFin g).injective h))

/-- Each selected grid-indexed spoke meets its own main path exactly once, at
an endpoint of the spoke. -/
theorem selectedOddCrossbarGridSpoke_meets_own_main
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    ∃ v : V,
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).IsEndpoint v ∧
        (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x).MeetsExactlyAt
          (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x) v := by
  simpa [selectedOddCrossbarGridSpokePath, selectedOddCrossbarGridMainPath,
    selectedOddCrossbarGridMainPacking, selectedOddCrossbarFinMainPacking]
    using
      (selectedOddCrossbarFin Hsys hcrossbars hlen i).spoke_meets_own_main
        (gridVertexEquivFin g x)

/-- A selected grid-indexed spoke is disjoint from every other selected main
path in the same crossbar. -/
theorem selectedOddCrossbarGridSpoke_disjoint_other_main
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) {x y : GridVertex g}
    (hxy : x ≠ y) :
    GraphPath.NodeDisjoint
      (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x)
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i y) := by
  exact
    (selectedOddCrossbarFin Hsys hcrossbars hlen i).spoke_disjoint_other_main
      (fun h => hxy ((gridVertexEquivFin g).injective h))

/-- The concrete ambient view of the local crossbar selected at the `i`-th odd
one-based cluster.  Unlike `selectedOddCrossbar` applied to a `Nonempty`
ambient family, this definition remembers the actual local witness. -/
noncomputable def selectedOddLocalCrossbarAsAmbient
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Crossbar G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i))
      (Hsys.y (oddClusterIndex hlen i)) (g ^ 2) :=
  localCrossbarAsAmbient Hsys hcrossbars (oddClusterIndex hlen i)
    (oddClusterIndex_oneBasedOdd hlen i)

/-- The concrete selected local crossbar with normalized `Fin (g^2)` index. -/
noncomputable def selectedOddLocalCrossbarFinAsAmbient
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Crossbar G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i))
      (Hsys.y (oddClusterIndex hlen i)) (g ^ 2) :=
  (selectedOddLocalCrossbarAsAmbient Hsys hcrossbars hlen i).finReindex

/-- The concrete selected local main paths, indexed by grid coordinates. -/
noncomputable def selectedOddLocalCrossbarGridMainPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PathPacking G
      (Hsys.base.left (oddClusterIndex hlen i))
      (Hsys.base.right (oddClusterIndex hlen i)) :=
  ((selectedOddLocalCrossbarFinAsAmbient Hsys hcrossbars hlen i).mainPathPacking).reindex
    (gridVertexEquivFin g)

@[simp] theorem selectedOddLocalCrossbarGridMainPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simp [selectedOddLocalCrossbarGridMainPacking]

/-- The source endpoints of the concrete selected local grid-indexed main
paths. -/
noncomputable def selectedOddLocalCrossbarGridMainSourceSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).sourceSet

/-- The target endpoints of the concrete selected local grid-indexed main
paths. -/
noncomputable def selectedOddLocalCrossbarGridMainTargetSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).targetSet

@[simp] theorem selectedOddLocalCrossbarGridMainSourceSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simp [selectedOddLocalCrossbarGridMainSourceSet]

@[simp] theorem selectedOddLocalCrossbarGridMainTargetSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simp [selectedOddLocalCrossbarGridMainTargetSet]

/-- The selected local grid-indexed main paths, oriented as a perfect packing
between the endpoints they actually use. -/
noncomputable def selectedOddLocalCrossbarGridMainPerfectPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) :=
  (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).toPerfectUsedTerminals

@[simp] theorem selectedOddLocalCrossbarGridMainPerfectPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  change
    (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).toPerfectUsedTerminals.card =
      g ^ 2
  rw [PathPacking.toPerfectUsedTerminals_card]
  exact selectedOddLocalCrossbarGridMainPacking_card Hsys hcrossbars hlen i

/-- Concrete selected local source endpoints lie in the selected cluster's left
nail set. -/
theorem selectedOddLocalCrossbarGridMainSourceSet_subset_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i ⊆
      Hsys.base.left (oddClusterIndex hlen i) :=
  (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).sourceSet_subset_left

/-- Concrete selected local target endpoints lie in the selected cluster's
right nail set. -/
theorem selectedOddLocalCrossbarGridMainTargetSet_subset_right
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
      Hsys.base.right (oddClusterIndex hlen i) :=
  (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).targetSet_subset_right

/-- Concrete selected local source endpoints lie in the selected base cluster. -/
theorem selectedOddLocalCrossbarGridMainSourceSet_subset_cluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) := by
  intro v hv
  exact Hsys.base.left_subset_cluster (oddClusterIndex hlen i)
    (selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i hv)

/-- Concrete selected local target endpoints lie in the selected base cluster. -/
theorem selectedOddLocalCrossbarGridMainTargetSet_subset_cluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) := by
  intro v hv
  exact Hsys.base.right_subset_cluster (oddClusterIndex hlen i)
    (selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i hv)

/-- The concrete selected local source and target endpoint sets are disjoint. -/
theorem selectedOddLocalCrossbarGridMainSourceSet_disjoint_targetSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Disjoint
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) := by
  rw [Finset.disjoint_left]
  intro v hvsource hvtarget
  exact Finset.disjoint_left.mp
    (Hsys.base.left_right_disjoint (oddClusterIndex hlen i))
    (selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i
      hvsource)
    (selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
      hvtarget)

/-- Concrete selected local source endpoints inherit node-well-linkedness from
the selected cluster's left nails. -/
theorem selectedOddLocalCrossbarGridMainSourceSet_nodeWellLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeWellLinkedIn G (Hsys.base.cluster (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i) :=
  (Hsys.base.left_nodeWellLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i)

/-- Concrete selected local target endpoints inherit node-well-linkedness from
the selected cluster's right nails. -/
theorem selectedOddLocalCrossbarGridMainTargetSet_nodeWellLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeWellLinkedIn G (Hsys.base.cluster (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) :=
  (Hsys.base.right_nodeWellLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i)

/-- Concrete selected local source and target endpoints remain linked inside
the selected base cluster. -/
theorem selectedOddLocalCrossbarGridMainSourceTarget_nodeLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeLinkedIn G (Hsys.base.cluster (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) :=
  (Hsys.base.left_right_nodeLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i)
    (selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i)

/-- Concrete selected local source endpoint sets in distinct selected odd
clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridMainSourceSet_disjoint_sourceSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.base.cluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddLocalCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen i hvi)
    (selectedOddLocalCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen j hvj)

/-- Concrete selected local source and target endpoint sets in distinct
selected odd clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridMainSourceSet_disjoint_targetSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.base.cluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddLocalCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen i hvi)
    (selectedOddLocalCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen j hvj)

/-- Concrete selected local target endpoint sets in distinct selected odd
clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridMainTargetSet_disjoint_targetSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.base.cluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddLocalCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen i hvi)
    (selectedOddLocalCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen j hvj)

/-- The concrete selected local main path at a grid coordinate. -/
noncomputable def selectedOddLocalCrossbarGridMainPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    GraphPath G :=
  (selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i).path x

/-- The concrete selected local spoke at a grid coordinate. -/
noncomputable def selectedOddLocalCrossbarGridSpokePath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    GraphPath G :=
  (selectedOddLocalCrossbarFinAsAmbient Hsys hcrossbars hlen i).spokePath
    (gridVertexEquivFin g x)

/-- A concrete selected local main path uses only edges of its local hair
graph. -/
theorem selectedOddLocalCrossbarGridMainPath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    ↑(selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet := by
  simpa [selectedOddLocalCrossbarGridMainPath,
    selectedOddLocalCrossbarFinAsAmbient, selectedOddLocalCrossbarAsAmbient]
    using
      localCrossbarAsAmbient_finReindex_mainPathPacking_path_edgeSet_subset_hairLocalGraph
        Hsys hcrossbars (oddClusterIndex hlen i)
        (oddClusterIndex_oneBasedOdd hlen i) (gridVertexEquivFin g x)

/-- A concrete selected local main path stays in the local base-cluster plus
hair-connector footprint. -/
theorem selectedOddLocalCrossbarGridMainPath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) ∪
        (Hsys.hairConnector (oddClusterIndex hlen i)).toPathPacking.vertexSet := by
  simpa [selectedOddLocalCrossbarGridMainPath, selectedOddLocalCrossbarGridMainPacking,
    selectedOddLocalCrossbarFinAsAmbient, selectedOddLocalCrossbarAsAmbient] using
      localCrossbarAsAmbient_finReindex_mainPathPacking_path_vertexSet_subset_localVertexSet
        Hsys hcrossbars (oddClusterIndex hlen i)
        (oddClusterIndex_oneBasedOdd hlen i) (gridVertexEquivFin g x)

/-- Every endpoint of a concrete selected local main path lies in the selected
base cluster. -/
theorem selectedOddLocalCrossbarGridMainPath_endpoint_mem_cluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) {v : V}
    (hend : (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).IsEndpoint v) :
    v ∈ Hsys.base.cluster (oddClusterIndex hlen i) := by
  classical
  let P := selectedOddLocalCrossbarGridMainPacking Hsys hcrossbars hlen i
  have hconn := P.connects x
  rcases hend with hsource | htarget
  · subst v
    rcases hconn with h | h
    · exact Hsys.base.left_subset_cluster (oddClusterIndex hlen i) h.1
    · exact Hsys.base.right_subset_cluster (oddClusterIndex hlen i) h.1
  · subst v
    rcases hconn with h | h
    · exact Hsys.base.right_subset_cluster (oddClusterIndex hlen i) h.2
    · exact Hsys.base.left_subset_cluster (oddClusterIndex hlen i) h.2

/-- A concrete selected local main path is disjoint from the selected local
hair endpoint set.  The key point is that hair endpoints have degree one in the
hair-local graph, while the endpoints of a main path lie in the base cluster. -/
theorem selectedOddLocalCrossbarGridMainPath_vertexSet_disjoint_y
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet
      (Hsys.y (oddClusterIndex hlen i)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvMain hvY
  let idx := oddClusterIndex hlen i
  let P := selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x
  let Hlocal := Hsys.hairLocalGraph idx
  have hEdges : ∀ e, e ∈ P.walk.edges → e ∈ Hlocal.edgeSet := by
    intro e he
    exact
      (selectedOddLocalCrossbarGridMainPath_edgeSet_subset_hairLocalGraph
        Hsys hcrossbars hlen i x) (by
          simpa [P, GraphPath.edgeSet] using he)
  let Plocal := P.transfer Hlocal hEdges
  have hvLocal : v ∈ Plocal.vertexSet := by
    simpa [Plocal, P] using hvMain
  have hendLocal :
      Plocal.IsEndpoint v :=
    GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one Plocal
      (Hsys.hairLocalGraph_degreeEquals_one_of_mem_y idx hvY) hvLocal
  have hend : P.IsEndpoint v := by
    simpa [Plocal, P, GraphPath.transfer, GraphPath.IsEndpoint] using hendLocal
  have hvBase :
      v ∈ Hsys.base.cluster idx :=
    selectedOddLocalCrossbarGridMainPath_endpoint_mem_cluster
      Hsys hcrossbars hlen i x hend
  have hvHair : v ∈ Hsys.hairCluster idx :=
    Hsys.y_subset_hairCluster idx hvY
  exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base idx idx)
    hvHair hvBase

/-- A concrete selected local main path is disjoint from the selected local
hair cluster.  The main path lives in the base cluster together with the local
hair-connector footprint; connector internal disjointness reduces any possible
hair-cluster overlap to a connector endpoint, and the hair endpoint case is
excluded by `selectedOddLocalCrossbarGridMainPath_vertexSet_disjoint_y`. -/
theorem selectedOddLocalCrossbarGridMainPath_vertexSet_disjoint_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet
      (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvMain hvHair
  let idx := oddClusterIndex hlen i
  have hvFootprint :
      v ∈ Hsys.base.cluster idx ∪ (Hsys.hairConnector idx).toPathPacking.vertexSet :=
    (selectedOddLocalCrossbarGridMainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x) hvMain
  rcases Finset.mem_union.mp hvFootprint with hvBase | hvConnector
  · exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base idx idx)
      hvHair hvBase
  · rcases ((Hsys.hairConnector idx).toPathPacking.mem_vertexSet).1 hvConnector with
      ⟨a, hvConnectorPath⟩
    have hend :
        ((Hsys.hairConnector idx).path a).IsEndpoint v :=
      Hsys.hairConnector_internally_disjoint_hairClusters idx idx a
        hvConnectorPath hvHair
    rcases hend with hsource | htarget
    · have hsourceBase :
          ((Hsys.hairConnector idx).path a).source ∈ Hsys.base.cluster idx :=
        Hsys.x_subset_cluster idx ((Hsys.hairConnector idx).source_mem a)
      exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base idx idx)
        hvHair (by simpa [hsource] using hsourceBase)
    · have htargetY :
          ((Hsys.hairConnector idx).path a).target ∈ Hsys.y idx :=
        (Hsys.hairConnector idx).target_mem a
      have hvY : v ∈ Hsys.y idx := by
        simpa [htarget] using htargetY
      exact Finset.disjoint_left.mp
        (selectedOddLocalCrossbarGridMainPath_vertexSet_disjoint_y
          Hsys hcrossbars hlen i x) hvMain hvY

/-- The oriented selected local main path is also disjoint from the selected
local hair cluster; orientation preserves vertex sets. -/
theorem selectedOddLocalCrossbarGridMainPerfectPacking_path_vertexSet_disjoint_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    Disjoint
      ((selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i).path x).vertexSet
      (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  simpa [selectedOddLocalCrossbarGridMainPerfectPacking,
    PathPacking.toPerfectUsedTerminals, selectedOddLocalCrossbarGridMainPath] using
    selectedOddLocalCrossbarGridMainPath_vertexSet_disjoint_hairCluster
      Hsys hcrossbars hlen i x

/-- The oriented perfect main-path packing keeps the same local footprint
containment as the underlying selected main paths. -/
theorem selectedOddLocalCrossbarGridMainPerfectPacking_path_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    ((selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i).path x).vertexSet ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) ∪
        (Hsys.hairConnector (oddClusterIndex hlen i)).toPathPacking.vertexSet := by
  simpa [selectedOddLocalCrossbarGridMainPerfectPacking,
    PathPacking.toPerfectUsedTerminals, selectedOddLocalCrossbarGridMainPath] using
      selectedOddLocalCrossbarGridMainPath_vertexSet_subset_localVertexSet
        Hsys hcrossbars hlen i x

/-- A concrete selected local spoke uses only edges of its local hair graph. -/
theorem selectedOddLocalCrossbarGridSpokePath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    ↑(selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet := by
  simpa [selectedOddLocalCrossbarGridSpokePath,
    selectedOddLocalCrossbarFinAsAmbient, selectedOddLocalCrossbarAsAmbient]
    using
      localCrossbarAsAmbient_finReindex_spokePath_edgeSet_subset_hairLocalGraph
        Hsys hcrossbars (oddClusterIndex hlen i)
        (oddClusterIndex_oneBasedOdd hlen i) (gridVertexEquivFin g x)

/-- A concrete selected local spoke stays in the local base-cluster plus
hair-connector footprint. -/
theorem selectedOddLocalCrossbarGridSpokePath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) ∪
        (Hsys.hairConnector (oddClusterIndex hlen i)).toPathPacking.vertexSet := by
  simpa [selectedOddLocalCrossbarGridSpokePath,
    selectedOddLocalCrossbarFinAsAmbient, selectedOddLocalCrossbarAsAmbient] using
      localCrossbarAsAmbient_finReindex_spokePath_vertexSet_subset_localVertexSet
        Hsys hcrossbars (oddClusterIndex hlen i)
        (oddClusterIndex_oneBasedOdd hlen i) (gridVertexEquivFin g x)

/-- A concrete selected local spoke connects its corresponding concrete local
main path to the local hair endpoint set. -/
theorem selectedOddLocalCrossbarGridSpoke_connects
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).ConnectsPathToSet
      (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x)
      (Hsys.y (oddClusterIndex hlen i)) := by
  simpa [selectedOddLocalCrossbarGridSpokePath,
    selectedOddLocalCrossbarGridMainPath]
    using
      (selectedOddLocalCrossbarFinAsAmbient Hsys hcrossbars hlen i).spoke_connects
        (gridVertexEquivFin g x)

/-- Concrete selected local spokes in one odd cluster are pairwise
node-disjoint. -/
theorem selectedOddLocalCrossbarGridSpoke_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Pairwise fun x y =>
      GraphPath.NodeDisjoint
        (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x)
        (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i y) := by
  intro x y hxy
  exact (selectedOddLocalCrossbarFinAsAmbient Hsys hcrossbars hlen i).spoke_nodeDisjoint
    (fun h => hxy ((gridVertexEquivFin g).injective h))

/-- Each concrete selected local spoke meets its own concrete local main path
exactly once, at an endpoint of the spoke. -/
theorem selectedOddLocalCrossbarGridSpoke_meets_own_main
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    ∃ v : V,
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).IsEndpoint v ∧
        (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).MeetsExactlyAt
          (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x) v := by
  simpa [selectedOddLocalCrossbarGridSpokePath,
    selectedOddLocalCrossbarGridMainPath]
    using
      (selectedOddLocalCrossbarFinAsAmbient Hsys hcrossbars hlen i).spoke_meets_own_main
        (gridVertexEquivFin g x)

/-- A concrete selected local spoke is disjoint from every other concrete
selected local main path in the same crossbar. -/
theorem selectedOddLocalCrossbarGridSpoke_disjoint_other_main
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) {x y : GridVertex g}
    (hxy : x ≠ y) :
    GraphPath.NodeDisjoint
      (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i y) := by
  exact
    (selectedOddLocalCrossbarFinAsAmbient Hsys hcrossbars hlen i).spoke_disjoint_other_main
      (fun h => hxy ((gridVertexEquivFin g).injective h))

/-- The concrete local attachment vertex where a concrete selected local spoke
meets its own main path. -/
noncomputable def selectedOddLocalCrossbarGridAttachment
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : V :=
  Classical.choose
    (selectedOddLocalCrossbarGridSpoke_meets_own_main Hsys hcrossbars hlen i x)

/-- The concrete local attachment is an endpoint of its selected spoke. -/
theorem selectedOddLocalCrossbarGridAttachment_spoke_endpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).IsEndpoint
      (selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x) :=
  (Classical.choose_spec
    (selectedOddLocalCrossbarGridSpoke_meets_own_main Hsys hcrossbars hlen i x)).1

/-- The concrete local attachment is exactly the intersection of its selected
main path and selected spoke. -/
theorem selectedOddLocalCrossbarGridAttachment_meetsExactly
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).MeetsExactlyAt
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x) :=
  (Classical.choose_spec
    (selectedOddLocalCrossbarGridSpoke_meets_own_main Hsys hcrossbars hlen i x)).2

/-- The concrete local attachment lies on its selected main path. -/
theorem selectedOddLocalCrossbarGridAttachment_mem_main
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
      (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet := by
  let v := selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x
  have hmeet :=
    selectedOddLocalCrossbarGridAttachment_meetsExactly Hsys hcrossbars hlen i x
  have hv : v ∈
      (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet ∩
        (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
    rw [GraphPath.MeetsExactlyAt] at hmeet
    rw [hmeet]
    simp [v]
  exact (Finset.mem_inter.mp hv).1

/-- The concrete local attachment lies on its selected spoke. -/
theorem selectedOddLocalCrossbarGridAttachment_mem_spoke
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
  let v := selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x
  have hmeet :=
    selectedOddLocalCrossbarGridAttachment_meetsExactly Hsys hcrossbars hlen i x
  have hv : v ∈
      (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet ∩
        (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
    rw [GraphPath.MeetsExactlyAt] at hmeet
    rw [hmeet]
    simp [v]
  exact (Finset.mem_inter.mp hv).2

/-- Distinct grid coordinates in one concrete local crossbar have distinct
attachment vertices. -/
theorem selectedOddLocalCrossbarGridAttachment_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Function.Injective
      (selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i) := by
  intro x y hxy
  by_contra hne
  have hdisj :=
    (selectedOddLocalCrossbarFinAsAmbient Hsys hcrossbars hlen i).main_nodeDisjoint
      (fun h => hne ((gridVertexEquivFin g).injective h))
  have hx :
      selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
        (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet :=
    selectedOddLocalCrossbarGridAttachment_mem_main Hsys hcrossbars hlen i x
  have hy :
      selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
        (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i y).vertexSet := by
    simpa [hxy] using
      selectedOddLocalCrossbarGridAttachment_mem_main Hsys hcrossbars hlen i y
  exact Finset.disjoint_left.mp hdisj hx hy

/-- The concrete local attachment set selected in one odd cluster. -/
noncomputable def selectedOddLocalCrossbarGridAttachmentSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  Finset.univ.image
    (selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i)

@[simp] theorem selectedOddLocalCrossbarGridAttachmentSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddLocalCrossbarGridAttachmentSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  rw [selectedOddLocalCrossbarGridAttachmentSet,
    Finset.card_image_of_injective]
  · simp [GridVertex, pow_two]
  · exact selectedOddLocalCrossbarGridAttachment_injective Hsys hcrossbars hlen i

/-- Concrete local attachment vertices selected by a set of grid coordinates. -/
noncomputable def selectedOddLocalCrossbarGridAttachmentImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  U.image (selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i)

@[simp] theorem selectedOddLocalCrossbarGridAttachmentImage_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddLocalCrossbarGridAttachmentImage,
    Finset.card_image_of_injective]
  exact selectedOddLocalCrossbarGridAttachment_injective Hsys hcrossbars hlen i

/-- Disjoint coordinate sets have disjoint concrete local attachment images. -/
theorem selectedOddLocalCrossbarGridAttachmentImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i W) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  rw [selectedOddLocalCrossbarGridAttachmentImage] at hvU hvW
  rcases Finset.mem_image.mp hvU with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hvW with ⟨y, hy, hyx⟩
  have hxy : y = x :=
    selectedOddLocalCrossbarGridAttachment_injective Hsys hcrossbars hlen i hyx
  exact Finset.disjoint_left.mp hUW hx (by simpa [hxy] using hy)

/-- The concrete local hair endpoint reached by a selected local spoke. -/
noncomputable def selectedOddLocalCrossbarGridHairEndpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : V :=
  (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).otherEndpoint
    (selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x)

/-- The concrete local hair endpoint lies on its selected spoke. -/
theorem selectedOddLocalCrossbarGridHairEndpoint_mem_spoke
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
  simpa [selectedOddLocalCrossbarGridHairEndpoint] using
    (GraphPath.otherEndpoint_mem_vertexSet
      (P := selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (v := selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x))

/-- The concrete local hair endpoint is an endpoint of its selected spoke. -/
theorem selectedOddLocalCrossbarGridHairEndpoint_spoke_endpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).IsEndpoint
      (selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x) := by
  simpa [selectedOddLocalCrossbarGridHairEndpoint] using
    GraphPath.otherEndpoint_isEndpoint
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x)

/-- A concrete selected local spoke connects its attachment to its concrete
hair endpoint. -/
theorem selectedOddLocalCrossbarGridSpoke_connects_attachment_hairEndpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).Connects
      {selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x}
      {selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x} := by
  let Q := selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x
  let a := selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x
  have ha : Q.IsEndpoint a :=
    selectedOddLocalCrossbarGridAttachment_spoke_endpoint Hsys hcrossbars hlen i x
  by_cases hsource : Q.source = a
  · refine Or.inl ⟨?_, ?_⟩
    · simpa [Q, a] using hsource
    · have hhair :
          selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x =
            Q.target := by
        simp [selectedOddLocalCrossbarGridHairEndpoint, GraphPath.otherEndpoint,
          Q, a, hsource]
      simpa [Q, a] using hhair.symm
  · have htarget : Q.target = a := by
      rcases ha with ha | ha
      · exact False.elim (hsource ha.symm)
      · exact ha.symm
    refine Or.inr ⟨?_, ?_⟩
    · have hhair :
          selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x =
            Q.source := by
        simp [selectedOddLocalCrossbarGridHairEndpoint, GraphPath.otherEndpoint,
          Q, a, hsource]
      simpa [Q, a] using hhair.symm
    · simpa [Q, a] using htarget

/-- A concrete selected local spoke oriented from its attachment point to its
hair endpoint. -/
noncomputable def selectedOddLocalCrossbarGridOrientedSpokePath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : GraphPath G :=
  (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).orient
    (selectedOddLocalCrossbarGridSpoke_connects_attachment_hairEndpoint
      Hsys hcrossbars hlen i x)

@[simp] theorem selectedOddLocalCrossbarGridOrientedSpokePath_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).source =
      selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i x := by
  simpa [selectedOddLocalCrossbarGridOrientedSpokePath] using
    GraphPath.orient_source_mem
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridSpoke_connects_attachment_hairEndpoint
        Hsys hcrossbars hlen i x)

@[simp] theorem selectedOddLocalCrossbarGridOrientedSpokePath_target
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).target =
      selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x := by
  simpa [selectedOddLocalCrossbarGridOrientedSpokePath] using
    GraphPath.orient_target_mem
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridSpoke_connects_attachment_hairEndpoint
        Hsys hcrossbars hlen i x)

@[simp] theorem selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet =
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
  simp [selectedOddLocalCrossbarGridOrientedSpokePath]

/-- Oriented selected local spokes keep the local footprint containment of the
underlying spoke paths. -/
theorem selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) ∪
        (Hsys.hairConnector (oddClusterIndex hlen i)).toPathPacking.vertexSet := by
  simpa [selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet] using
    selectedOddLocalCrossbarGridSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x

@[simp] theorem selectedOddLocalCrossbarGridOrientedSpokePath_edgeSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).edgeSet =
      (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).edgeSet := by
  simp [selectedOddLocalCrossbarGridOrientedSpokePath]

/-- A concrete selected local oriented spoke still uses only local hair-graph
edges. -/
theorem selectedOddLocalCrossbarGridOrientedSpokePath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    ↑(selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet := by
  intro e he
  rw [selectedOddLocalCrossbarGridOrientedSpokePath_edgeSet] at he
  exact selectedOddLocalCrossbarGridSpokePath_edgeSet_subset_hairLocalGraph
    Hsys hcrossbars hlen i x he

/-- The concrete local hair endpoint lies in the selected hair-terminal set. -/
theorem selectedOddLocalCrossbarGridHairEndpoint_mem_y
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
      Hsys.y (oddClusterIndex hlen i) := by
  simpa [selectedOddLocalCrossbarGridHairEndpoint] using
    GraphPath.otherEndpoint_mem_of_connectsPathToSet_meetsExactlyAt
      (selectedOddLocalCrossbarGridSpoke_connects Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridAttachment_meetsExactly Hsys hcrossbars hlen i x)

/-- Distinct grid coordinates in one concrete local crossbar have distinct
hair endpoints. -/
theorem selectedOddLocalCrossbarGridHairEndpoint_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Function.Injective
      (selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i) := by
  intro x y hxy
  by_contra hne
  have hdisj :=
    selectedOddLocalCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen i hne
  have hx :
      selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
        (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet :=
    selectedOddLocalCrossbarGridHairEndpoint_mem_spoke Hsys hcrossbars hlen i x
  have hy :
      selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
        (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i y).vertexSet := by
    simpa [hxy] using
      selectedOddLocalCrossbarGridHairEndpoint_mem_spoke Hsys hcrossbars hlen i y
  exact Finset.disjoint_left.mp hdisj hx hy

/-- The concrete local hair endpoint set selected in one odd cluster. -/
noncomputable def selectedOddLocalCrossbarGridHairEndpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  Finset.univ.image
    (selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i)

@[simp] theorem selectedOddLocalCrossbarGridHairEndpointSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  rw [selectedOddLocalCrossbarGridHairEndpointSet,
    Finset.card_image_of_injective]
  · simp [GridVertex, pow_two]
  · exact selectedOddLocalCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i

/-- Concrete local hair endpoints selected by a set of grid coordinates. -/
noncomputable def selectedOddLocalCrossbarGridHairEndpointImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  U.image (selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i)

@[simp] theorem selectedOddLocalCrossbarGridHairEndpointImage_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddLocalCrossbarGridHairEndpointImage,
    Finset.card_image_of_injective]
  exact selectedOddLocalCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i

/-- The concrete selected hair endpoint set is contained in the corresponding
`Y_i` terminal set. -/
theorem selectedOddLocalCrossbarGridHairEndpointSet_subset_y
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i ⊆
      Hsys.y (oddClusterIndex hlen i) := by
  intro v hv
  rw [selectedOddLocalCrossbarGridHairEndpointSet] at hv
  rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
  exact selectedOddLocalCrossbarGridHairEndpoint_mem_y Hsys hcrossbars hlen i x

/-- The concrete selected local hair endpoint set is contained in the
corresponding hair cluster. -/
theorem selectedOddLocalCrossbarGridHairEndpointSet_subset_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i ⊆
      Hsys.hairCluster (oddClusterIndex hlen i) := by
  intro v hv
  exact Hsys.y_subset_hairCluster (oddClusterIndex hlen i)
    (selectedOddLocalCrossbarGridHairEndpointSet_subset_y Hsys hcrossbars hlen i hv)

/-- Concrete selected local hair endpoint sets in distinct selected odd
clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridHairEndpointSet_disjoint_hairEndpointSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddLocalCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen i hvi)
    (selectedOddLocalCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen j hvj)

/-- A concrete selected local source endpoint set is disjoint from every
concrete selected local hair endpoint set. -/
theorem selectedOddLocalCrossbarGridMainSourceSet_disjoint_hairEndpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) :
    Disjoint
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvsource hvhair
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint_base (oddClusterIndex hlen j)
      (oddClusterIndex hlen i))
    (selectedOddLocalCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen j hvhair)
    (selectedOddLocalCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen i
      hvsource)

/-- A concrete selected local target endpoint set is disjoint from every
concrete selected local hair endpoint set. -/
theorem selectedOddLocalCrossbarGridMainTargetSet_disjoint_hairEndpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) :
    Disjoint
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvtarget hvhair
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint_base (oddClusterIndex hlen j)
      (oddClusterIndex hlen i))
    (selectedOddLocalCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen j hvhair)
    (selectedOddLocalCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen i
      hvtarget)

/-- Concrete coordinate-indexed local hair representatives are contained in
the full concrete local endpoint set. -/
theorem selectedOddLocalCrossbarGridHairEndpointImage_subset_endpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U ⊆
      selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i := by
  intro v hv
  rw [selectedOddLocalCrossbarGridHairEndpointImage] at hv
  rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
  rw [selectedOddLocalCrossbarGridHairEndpointSet]
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

/-- Disjoint coordinate sets have disjoint concrete local hair representative
images. -/
theorem selectedOddLocalCrossbarGridHairEndpointImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  rw [selectedOddLocalCrossbarGridHairEndpointImage] at hvU hvW
  rcases Finset.mem_image.mp hvU with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hvW with ⟨y, hy, hyx⟩
  have hxy : y = x :=
    selectedOddLocalCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i hyx
  exact Finset.disjoint_left.mp hUW hx (by simpa [hxy] using hy)

/-- The concrete local hair endpoint set inherits node-well-linkedness from
the hair cluster. -/
theorem selectedOddLocalCrossbarGridHairEndpointSet_nodeWellLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeWellLinkedIn G (Hsys.hairCluster (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) :=
  (Hsys.y_nodeWellLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddLocalCrossbarGridHairEndpointSet_subset_y Hsys hcrossbars hlen i)

/-- The concrete selected spokes, oriented from local attachments to local
hair endpoints. -/
noncomputable def selectedOddLocalCrossbarGridSpokePacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PathPacking G
      (selectedOddLocalCrossbarGridAttachmentSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) where
  Index := GridVertex g
  path := fun x =>
    selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x
  connects := by
    intro x
    refine Or.inl ⟨?_, ?_⟩
    · rw [selectedOddLocalCrossbarGridAttachmentSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, by simp⟩
    · rw [selectedOddLocalCrossbarGridHairEndpointSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, by simp⟩
  node_disjoint := by
    intro x y hxy
    change Disjoint
      ((selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet)
      ((selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i y).vertexSet)
    simpa using selectedOddLocalCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen
      i hxy

@[simp] theorem selectedOddLocalCrossbarGridSpokePacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddLocalCrossbarGridSpokePacking Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  change Fintype.card (GridVertex g) = g ^ 2
  rw [card_gridVertex, pow_two]

/-- The concrete selected spokes as a perfect packing from local attachment
points to local hair endpoints. -/
noncomputable def selectedOddLocalCrossbarGridSpokePerfectPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridAttachmentSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) :=
  (selectedOddLocalCrossbarGridSpokePacking Hsys hcrossbars hlen i).toPerfectOfCardEq
    (by
      rw [selectedOddLocalCrossbarGridSpokePacking_card,
        selectedOddLocalCrossbarGridAttachmentSet_card])
    (by
      rw [selectedOddLocalCrossbarGridSpokePacking_card,
        selectedOddLocalCrossbarGridHairEndpointSet_card])

/-- The concrete selected spokes indexed by an arbitrary coordinate set,
oriented as a perfect packing from the corresponding attachment image to the
corresponding hair endpoint image. -/
noncomputable def selectedOddLocalCrossbarGridSpokeSubpacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U) where
  toPathPacking := {
    Index := {x : GridVertex g // x ∈ U}
    path := fun x =>
      selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x.1
    connects := by
      intro x
      refine Or.inl ⟨?_, ?_⟩
      · rw [selectedOddLocalCrossbarGridAttachmentImage]
        exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
      · rw [selectedOddLocalCrossbarGridHairEndpointImage]
        exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
    node_disjoint := by
      intro x y hxy
      change Disjoint
        (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x.1).vertexSet
        (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i y.1).vertexSet
      rw [selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet,
        selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet]
      exact selectedOddLocalCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen
        i (fun h => hxy (Subtype.ext h))
  }
  source_mem := by
    intro x
    rw [selectedOddLocalCrossbarGridAttachmentImage]
    exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
  target_mem := by
    intro x
    rw [selectedOddLocalCrossbarGridHairEndpointImage]
    exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
  source_bijective := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply selectedOddLocalCrossbarGridAttachment_injective Hsys hcrossbars hlen i
      have hval := congrArg Subtype.val hxy
      simpa using hval
    · intro v
      rcases v with ⟨v, hv⟩
      rw [selectedOddLocalCrossbarGridAttachmentImage] at hv
      rcases Finset.mem_image.mp hv with ⟨x, hx, hxv⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simp [hxv]
  target_bijective := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply selectedOddLocalCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i
      have hval := congrArg Subtype.val hxy
      simpa using hval
    · intro v
      rcases v with ⟨v, hv⟩
      rw [selectedOddLocalCrossbarGridHairEndpointImage] at hv
      rcases Finset.mem_image.mp hv with ⟨x, hx, hxv⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simp [hxv]

@[simp] theorem selectedOddLocalCrossbarGridSpokeSubpacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddLocalCrossbarGridSpokeSubpacking, PerfectPathPacking.card,
    Fintype.card_coe]

/-- Every path of a concrete local spoke subpacking uses only local hair-graph
edges. -/
theorem selectedOddLocalCrossbarGridSpokeSubpacking_path_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g))
    (x : (selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U).Index) :
    ↑((selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U).path x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet := by
  exact selectedOddLocalCrossbarGridOrientedSpokePath_edgeSet_subset_hairLocalGraph
    Hsys hcrossbars hlen i x.1

/-- The union of vertices used by concrete local selected spokes whose
coordinates lie in `U`. -/
noncomputable def selectedOddLocalCrossbarGridSpokeTraceImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  U.biUnion fun x =>
    (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet

/-- A concrete local oriented spoke with coordinate in `U` is contained in the
local spoke trace of `U`. -/
theorem selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet_subset_trace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U : Finset (GridVertex g)} {x : GridVertex g} (hx : x ∈ U) :
    (selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet ⊆
      selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U := by
  intro v hv
  rw [selectedOddLocalCrossbarGridSpokeTraceImage]
  exact Finset.mem_biUnion.mpr ⟨x, hx, hv⟩

/-- The restricted concrete local selected-spoke packing stays inside its
local spoke trace. -/
theorem selectedOddLocalCrossbarGridSpokeSubpacking_staysIn_trace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U).toPathPacking.StaysIn
      (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U) := by
  intro x
  exact selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet_subset_trace
    Hsys hcrossbars hlen i x.2

/-- Disjoint coordinate sets select disjoint concrete local spoke traces in a
fixed crossbar. -/
theorem selectedOddLocalCrossbarGridSpokeTraceImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  rw [selectedOddLocalCrossbarGridSpokeTraceImage] at hvU hvW
  rcases Finset.mem_biUnion.mp hvU with ⟨x, hx, hvx⟩
  rcases Finset.mem_biUnion.mp hvW with ⟨y, hy, hvy⟩
  by_cases hxy : x = y
  · subst y
    exact Finset.disjoint_left.mp hUW hx hy
  · have hdisj :=
      selectedOddLocalCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen i hxy
    have hvx' :
        v ∈ (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
      simpa using hvx
    have hvy' :
        v ∈ (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i y).vertexSet := by
      simpa using hvy
    exact Finset.disjoint_left.mp hdisj hvx' hvy'

/-- The hair cluster links the concrete local selected representatives of any
two disjoint coordinate sets, with the expected full cardinality. -/
theorem selectedOddLocalCrossbarGridHairEndpointImage_linkage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    ∃ P : PathPacking G
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W),
      P.card = min U.card W.card ∧
        P.StaysIn (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  have hwell :=
    selectedOddLocalCrossbarGridHairEndpointSet_nodeWellLinked
      Hsys hcrossbars hlen i
  rcases hwell.2
      (selectedOddLocalCrossbarGridHairEndpointImage_subset_endpointSet
        Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridHairEndpointImage_subset_endpointSet
        Hsys hcrossbars hlen i W)
      (selectedOddLocalCrossbarGridHairEndpointImage_disjoint
        Hsys hcrossbars hlen i hUW) with
    ⟨P, hPcard, hstay⟩
  refine ⟨P, ?_, hstay⟩
  simpa [selectedOddLocalCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i U,
    selectedOddLocalCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i W]
    using hPcard

/-- Equal-size disjoint coordinate sets have a perfect linkage between their
concrete local selected hair representatives. -/
theorem selectedOddLocalCrossbarGridHairEndpointImage_perfectLinkage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ P : PerfectPathPacking G
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W),
      P.card = U.card ∧
        P.toPathPacking.StaysIn (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  rcases selectedOddLocalCrossbarGridHairEndpointImage_linkage Hsys hcrossbars hlen
      i hUW with
    ⟨P, hPcard, hstay⟩
  have hPcardU : P.card = U.card := by
    simpa [hcard] using hPcard
  have hPcardImageU :
      P.card =
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U).card :=
    hPcardU.trans
      (selectedOddLocalCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i U).symm
  have hPcardImageW :
      P.card =
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W).card :=
    (hPcardU.trans hcard).trans
      (selectedOddLocalCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i W).symm
  refine ⟨P.toPerfectOfCardEq hPcardImageU hPcardImageW, ?_, ?_⟩
  · simpa [PathPacking.toPerfectOfCardEq, PerfectPathPacking.card,
      PathPacking.card] using hPcardU
  · exact PathPacking.orient_staysIn hstay

/-- Concrete-local version of one cut-matching round: selected local spokes
from the left coordinate subset into the hair cluster, a hair-cluster linkage,
and selected local spokes back out to the right coordinate subset.  Unlike the
ambient `Nonempty` wrapper, the two spoke packings are built from the actual
local crossbar witnesses. -/
theorem exists_selectedOddLocalCrossbarGridConcreteMatchingPieces
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ L : PerfectPathPacking G
        (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i U)
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U),
      ∃ M : PerfectPathPacking G
          (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
          (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W),
        ∃ R : PerfectPathPacking G
            (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W)
            (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i W),
          L.card = U.card ∧
            M.card = U.card ∧
              R.card = W.card ∧
                L.toPathPacking.StaysIn
                  (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U) ∧
                  R.toPathPacking.StaysIn
                    (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W) ∧
                    M.toPathPacking.StaysIn
                      (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  let L := selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U
  rcases selectedOddLocalCrossbarGridHairEndpointImage_perfectLinkage
      Hsys hcrossbars hlen i hUW hcard with
    ⟨M, hMcard, hMstay⟩
  let R :=
    (selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W).reverse
  refine ⟨L, M, R, ?_, hMcard, ?_, ?_, ?_, hMstay⟩
  · exact selectedOddLocalCrossbarGridSpokeSubpacking_card Hsys hcrossbars hlen i U
  · change
      ((selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W).reverse).card =
        W.card
    simp [
      selectedOddLocalCrossbarGridSpokeSubpacking_card Hsys hcrossbars hlen i W
    ]
  · exact selectedOddLocalCrossbarGridSpokeSubpacking_staysIn_trace
      Hsys hcrossbars hlen i U
  · change
      ((selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W).reverse).toPathPacking.StaysIn
        (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W)
    exact PerfectPathPacking.reverse_staysIn
      (selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W)
      (selectedOddLocalCrossbarGridSpokeSubpacking_staysIn_trace
        Hsys hcrossbars hlen i W)

/-- Edge-local strengthened version of
`exists_selectedOddLocalCrossbarGridConcreteMatchingPieces`: in addition to
the three compatible pieces, both selected-spoke sides use only edges of the
local hair graph for the selected odd cluster. -/
theorem exists_selectedOddLocalCrossbarGridConcreteMatchingPieces_edgeLocal
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ L : PerfectPathPacking G
        (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i U)
        (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U),
      ∃ M : PerfectPathPacking G
          (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
          (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W),
        ∃ R : PerfectPathPacking G
            (selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W)
            (selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i W),
          L.card = U.card ∧
            M.card = U.card ∧
              R.card = W.card ∧
                L.toPathPacking.StaysIn
                  (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U) ∧
                  R.toPathPacking.StaysIn
                    (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W) ∧
                    M.toPathPacking.StaysIn
                      (Hsys.hairCluster (oddClusterIndex hlen i)) ∧
                      (∀ x : L.Index, ↑(L.path x).edgeSet ⊆
                        (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet) ∧
                        (∀ x : R.Index, ↑(R.path x).edgeSet ⊆
                          (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet) := by
  let L := selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U
  rcases selectedOddLocalCrossbarGridHairEndpointImage_perfectLinkage
      Hsys hcrossbars hlen i hUW hcard with
    ⟨M, hMcard, hMstay⟩
  let R0 := selectedOddLocalCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W
  let R := R0.reverse
  refine ⟨L, M, R, ?_, hMcard, ?_, ?_, ?_, hMstay, ?_, ?_⟩
  · exact selectedOddLocalCrossbarGridSpokeSubpacking_card Hsys hcrossbars hlen i U
  · change R0.reverse.card = W.card
    simp [R0, selectedOddLocalCrossbarGridSpokeSubpacking_card Hsys hcrossbars hlen i W]
  · exact selectedOddLocalCrossbarGridSpokeSubpacking_staysIn_trace
      Hsys hcrossbars hlen i U
  · change R0.reverse.toPathPacking.StaysIn
      (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W)
    exact PerfectPathPacking.reverse_staysIn R0
      (selectedOddLocalCrossbarGridSpokeSubpacking_staysIn_trace
        Hsys hcrossbars hlen i W)
  · intro x
    exact selectedOddLocalCrossbarGridSpokeSubpacking_path_edgeSet_subset_hairLocalGraph
      Hsys hcrossbars hlen i U x
  · intro x
    change ↑(R0.reverse.path x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet
    rw [PerfectPathPacking.reverse_path_edgeSet]
    exact selectedOddLocalCrossbarGridSpokeSubpacking_path_edgeSet_subset_hairLocalGraph
      Hsys hcrossbars hlen i W x

/-- Consecutive selected odd clusters can be stitched through the intervening
even cluster, using the concrete local crossbar main-path endpoint sets as the
new nails.  This is the formal Claim 2.2 interface needed before the
cut-matching construction builds long backbone paths through all selected odd
clusters. -/
theorem exists_selectedOddLocalCrossbarGridStitchingPieces
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    ∃ Lmid Rmid : Finset V,
      ∃ Q₁ : PerfectPathPacking G
          (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) Lmid,
        ∃ Q₂ : PerfectPathPacking G Lmid Rmid,
          ∃ Q₃ : PerfectPathPacking G Rmid
              (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen
                ⟨i.1 + 1, hnext⟩),
            Q₁.card = g ^ 2 ∧
              Q₂.card = g ^ 2 ∧
                Q₃.card = g ^ 2 ∧
                  Lmid ⊆ Hsys.base.left (middleClusterIndex hlen i) ∧
                    Rmid ⊆ Hsys.base.right (middleClusterIndex hlen i) ∧
                      Q₁.toPathPacking.StaysIn
                        (Hsys.base.connector (oddClusterIndex hlen i)
                          (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∧
                        Q₂.toPathPacking.StaysIn
                          (Hsys.base.cluster (middleClusterIndex hlen i)) ∧
                          Q₃.toPathPacking.StaysIn
                            (Hsys.base.connector
                              (middleClusterIndex hlen i)
                              (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet := by
  classical
  let iOdd := oddClusterIndex hlen i
  have hgap₁ : iOdd.1 + 1 < ell := by
    simpa [iOdd] using oddClusterIndex_gap hlen i
  let iMid := middleClusterIndex hlen i
  have hgap₂ : iMid.1 + 1 < ell := by
    simpa [iMid] using middleClusterIndex_gap hlen hnext
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  have hnextOdd : oddClusterIndex hlen j =
      ⟨iMid.1 + 1, hgap₂⟩ := by
    simp [j, iMid]
  have hR :
      selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
        Hsys.base.right iOdd := by
    simpa [iOdd] using
      selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
  have hL :
      selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j ⊆
        Hsys.base.left ⟨iMid.1 + 1, hgap₂⟩ := by
    simpa [hnextOdd] using
      selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen j
  have hcard :
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i).card =
        (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j).card := by
    rw [selectedOddLocalCrossbarGridMainTargetSet_card,
      selectedOddLocalCrossbarGridMainSourceSet_card]
  rcases Hsys.base.exists_twoGap_stitchingPieces_between_subsets
      iOdd hgap₁ hgap₂ hR hL hcard with
    ⟨Lmid, Rmid, Q₁, Q₂, Q₃, hQ₁, hQ₂, hQ₃, hLmid, hRmid,
      hQ₁stay, hQ₂stay, hQ₃stay⟩
  refine ⟨Lmid, Rmid, Q₁, Q₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hnextOdd] using Q₃
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₁
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₂
  · simpa [selectedOddLocalCrossbarGridMainSourceSet_card Hsys hcrossbars hlen j]
      using hQ₃
  · simpa [iMid] using hLmid
  · simpa [iMid] using hRmid
  · simpa [iOdd] using hQ₁stay
  · simpa [iMid] using hQ₂stay
  · simpa [iMid] using hQ₃stay

/-- Consecutive selected odd clusters can be stitched with the separation data
needed for the later concatenation into full backbone paths. -/
theorem exists_selectedOddLocalCrossbarGridStitchingPieces_with_separation
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    ∃ Lmid Rmid : Finset V,
      ∃ Q₁ : PerfectPathPacking G
          (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) Lmid,
        ∃ Q₂ : PerfectPathPacking G Lmid Rmid,
          ∃ Q₃ : PerfectPathPacking G Rmid
              (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen
                ⟨i.1 + 1, hnext⟩),
            Q₁.card = g ^ 2 ∧
              Q₂.card = g ^ 2 ∧
                Q₃.card = g ^ 2 ∧
                  Lmid ⊆ Hsys.base.left (middleClusterIndex hlen i) ∧
                    Rmid ⊆ Hsys.base.right (middleClusterIndex hlen i) ∧
                      Q₁.toPathPacking.StaysIn
                        (Hsys.base.connector (oddClusterIndex hlen i)
                          (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∧
                        Q₂.toPathPacking.StaysIn
                          (Hsys.base.cluster (middleClusterIndex hlen i)) ∧
                          Q₃.toPathPacking.StaysIn
                            (Hsys.base.connector
                              (middleClusterIndex hlen i)
                              (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet ∧
                            Q₁.toPathPacking.InternallyDisjointFromSet
                              (Hsys.base.cluster (middleClusterIndex hlen i)) ∧
                              Q₃.toPathPacking.InternallyDisjointFromSet
                                (Hsys.base.cluster (middleClusterIndex hlen i)) ∧
                                Q₁.toPathPacking.MutuallyNodeDisjoint
                                  Q₃.toPathPacking := by
  classical
  let iOdd := oddClusterIndex hlen i
  have hgap₁ : iOdd.1 + 1 < ell := by
    simpa [iOdd] using oddClusterIndex_gap hlen i
  let iMid := middleClusterIndex hlen i
  have hgap₂ : iMid.1 + 1 < ell := by
    simpa [iMid] using middleClusterIndex_gap hlen hnext
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  have hnextOdd : oddClusterIndex hlen j =
      ⟨iMid.1 + 1, hgap₂⟩ := by
    simp [j, iMid]
  have hR :
      selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
        Hsys.base.right iOdd := by
    simpa [iOdd] using
      selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
  have hL :
      selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j ⊆
        Hsys.base.left ⟨iMid.1 + 1, hgap₂⟩ := by
    simpa [hnextOdd] using
      selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen j
  have hcard :
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i).card =
        (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j).card := by
    rw [selectedOddLocalCrossbarGridMainTargetSet_card,
      selectedOddLocalCrossbarGridMainSourceSet_card]
  rcases Hsys.base.exists_twoGap_stitchingPieces_between_subsets_with_separation
      iOdd hgap₁ hgap₂ hR hL hcard with
    ⟨Lmid, Rmid, Q₁, Q₂, Q₃, hQ₁, hQ₂, hQ₃, hLmid, hRmid,
      hQ₁stay, hQ₂stay, hQ₃stay, hQ₁middle, hQ₃middle, hQ₁Q₃,
      _hQ₁first, _hQ₃last⟩
  refine ⟨Lmid, Rmid, Q₁, Q₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hnextOdd] using Q₃
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₁
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₂
  · simpa [selectedOddLocalCrossbarGridMainSourceSet_card Hsys hcrossbars hlen j]
      using hQ₃
  · simpa [iMid] using hLmid
  · simpa [iMid] using hRmid
  · simpa [iOdd] using hQ₁stay
  · simpa [iMid] using hQ₂stay
  · simpa [iMid] using hQ₃stay
  · simpa [iMid] using hQ₁middle
  · simpa [iMid] using hQ₃middle
  · simpa using hQ₁Q₃

/-- Concrete selected odd clusters provide the two partial concatenations around
the intervening middle cluster.  These are the proof-facing backbone pieces:
one runs from the current selected local target set into the middle right nails,
and the other runs from the middle left nails to the next selected local source
set. -/
theorem exists_selectedOddLocalCrossbarGridPartialConcatPackings
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    ∃ Lmid Rmid : Finset V,
      ∃ Q₁ : PerfectPathPacking G
          (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) Lmid,
        ∃ Q₂ : PerfectPathPacking G Lmid Rmid,
          ∃ Q₃ : PerfectPathPacking G Rmid
              (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen
                ⟨i.1 + 1, hnext⟩),
            ∃ Q₁₂ : PerfectPathPacking G
                (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i) Rmid,
              ∃ Q₂₃ : PerfectPathPacking G Lmid
                  (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen
                    ⟨i.1 + 1, hnext⟩),
                Q₁.card = g ^ 2 ∧
                  Q₂.card = g ^ 2 ∧
                    Q₃.card = g ^ 2 ∧
                      Q₁₂.card = g ^ 2 ∧
                        Q₂₃.card = g ^ 2 ∧
                          Lmid ⊆ Hsys.base.left (middleClusterIndex hlen i) ∧
                            Rmid ⊆ Hsys.base.right (middleClusterIndex hlen i) ∧
                              Q₁₂.toPathPacking.StaysIn
                                ((Hsys.base.connector (oddClusterIndex hlen i)
                                  (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∪
                                  Hsys.base.cluster (middleClusterIndex hlen i)) ∧
                                Q₂₃.toPathPacking.StaysIn
                                  (Hsys.base.cluster (middleClusterIndex hlen i) ∪
                                    (Hsys.base.connector
                                      (middleClusterIndex hlen i)
                                      (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet) ∧
                                  Q₁.toPathPacking.MutuallyNodeDisjoint
                                    Q₃.toPathPacking := by
  classical
  let iOdd := oddClusterIndex hlen i
  have hgap₁ : iOdd.1 + 1 < ell := by
    simpa [iOdd] using oddClusterIndex_gap hlen i
  let iMid := middleClusterIndex hlen i
  have hgap₂ : iMid.1 + 1 < ell := by
    simpa [iMid] using middleClusterIndex_gap hlen hnext
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  have hnextOdd : oddClusterIndex hlen j =
      ⟨iMid.1 + 1, hgap₂⟩ := by
    simp [j, iMid]
  have hR :
      selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
        Hsys.base.right iOdd := by
    simpa [iOdd] using
      selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
  have hL :
      selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j ⊆
        Hsys.base.left ⟨iMid.1 + 1, hgap₂⟩ := by
    simpa [hnextOdd] using
      selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen j
  have hcard :
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i).card =
        (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j).card := by
    rw [selectedOddLocalCrossbarGridMainTargetSet_card,
      selectedOddLocalCrossbarGridMainSourceSet_card]
  rcases Hsys.base.exists_twoGap_partialConcatPackings_between_subsets
      iOdd hgap₁ hgap₂ hR hL hcard with
    ⟨Lmid, Rmid, Q₁, Q₂, Q₃, Q₁₂, Q₂₃, hQ₁, hQ₂, hQ₃,
      hQ₁₂, hQ₂₃, hLmid, hRmid, hQ₁₂stay, hQ₂₃stay, hQ₁Q₃⟩
  refine ⟨Lmid, Rmid, Q₁, Q₂, ?_, Q₁₂, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hnextOdd] using Q₃
  · simpa [hnextOdd] using Q₂₃
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₁
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₂
  · simpa [selectedOddLocalCrossbarGridMainSourceSet_card Hsys hcrossbars hlen j]
      using hQ₃
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₁₂
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQ₂₃
  · simpa [iMid] using hLmid
  · simpa [iMid] using hRmid
  · simpa [iOdd, iMid] using hQ₁₂stay
  · simpa [iMid] using hQ₂₃stay
  · simpa [hnextOdd] using hQ₁Q₃

/-- Concrete full two-gap stitching between consecutive selected odd clusters.
This packages the path-of-sets splicing step as an actual perfect packing from
the current selected local main-path targets to the next selected local
main-path sources. -/
theorem exists_selectedOddLocalCrossbarGridConcatPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    ∃ Q : PerfectPathPacking G
        (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i)
        (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen
          ⟨i.1 + 1, hnext⟩),
      Q.card = g ^ 2 ∧
        Q.toPathPacking.StaysIn
          ((Hsys.base.connector (oddClusterIndex hlen i)
            (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∪
            (Hsys.base.cluster (middleClusterIndex hlen i) ∪
              (Hsys.base.connector
                (middleClusterIndex hlen i)
                (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet)) ∧
          Q.toPathPacking.InternallyDisjointFromSet
            (Hsys.base.cluster (oddClusterIndex hlen i)) ∧
            Q.toPathPacking.InternallyDisjointFromSet
              (Hsys.base.cluster (oddClusterIndex hlen ⟨i.1 + 1, hnext⟩)) := by
  classical
  let iOdd := oddClusterIndex hlen i
  have hgap₁ : iOdd.1 + 1 < ell := by
    simpa [iOdd] using oddClusterIndex_gap hlen i
  let iMid := middleClusterIndex hlen i
  have hgap₂ : iMid.1 + 1 < ell := by
    simpa [iMid] using middleClusterIndex_gap hlen hnext
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  have hnextOdd : oddClusterIndex hlen j =
      ⟨iMid.1 + 1, hgap₂⟩ := by
    simp [j, iMid]
  have hR :
      selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
        Hsys.base.right iOdd := by
    simpa [iOdd] using
      selectedOddLocalCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
  have hL :
      selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j ⊆
        Hsys.base.left ⟨iMid.1 + 1, hgap₂⟩ := by
    simpa [hnextOdd] using
      selectedOddLocalCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen j
  have hcard :
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i).card =
        (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen j).card := by
    rw [selectedOddLocalCrossbarGridMainTargetSet_card,
      selectedOddLocalCrossbarGridMainSourceSet_card]
  rcases Hsys.base.exists_twoGap_concatPacking_between_subsets
      iOdd hgap₁ hgap₂ hR hL hcard with
    ⟨Q, hQcard, hQstay, hQfirst, hQlast⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hnextOdd] using Q
  · simpa [selectedOddLocalCrossbarGridMainTargetSet_card Hsys hcrossbars hlen i]
      using hQcard
  · simpa [iOdd, iMid] using hQstay
  · simpa [iOdd] using hQfirst
  · simpa [hnextOdd] using hQlast

/-- The selected full two-gap stitching packing between consecutive odd local
crossbars. -/
noncomputable def selectedOddLocalCrossbarGridConcatPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridMainTargetSet Hsys hcrossbars hlen i)
      (selectedOddLocalCrossbarGridMainSourceSet Hsys hcrossbars hlen
        ⟨i.1 + 1, hnext⟩) :=
  Classical.choose
    (exists_selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext)

@[simp] theorem selectedOddLocalCrossbarGridConcatPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    (selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext).card =
      g ^ 2 :=
  (Classical.choose_spec
    (exists_selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext)).1

/-- The selected full two-gap stitching packing stays in the union of the two
connectors and the intervening middle cluster. -/
theorem selectedOddLocalCrossbarGridConcatPacking_staysIn
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    (selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext).toPathPacking.StaysIn
      ((Hsys.base.connector (oddClusterIndex hlen i)
        (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∪
        (Hsys.base.cluster (middleClusterIndex hlen i) ∪
          (Hsys.base.connector
            (middleClusterIndex hlen i)
            (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet)) :=
  (Classical.choose_spec
    (exists_selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext)).2.1

/-- The selected two-gap stitching packing is internally disjoint from the
current selected odd base cluster. -/
theorem selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_current
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    PathPacking.InternallyDisjointFromSet
      ((selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext).toPathPacking)
      (Hsys.base.cluster (oddClusterIndex hlen i)) :=
  (Classical.choose_spec
    (exists_selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext)).2.2.1

/-- The selected two-gap stitching packing is internally disjoint from the next
selected odd base cluster. -/
theorem selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_next
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    PathPacking.InternallyDisjointFromSet
      ((selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext).toPathPacking)
      (Hsys.base.cluster (oddClusterIndex hlen ⟨i.1 + 1, hnext⟩)) :=
  (Classical.choose_spec
    (exists_selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext)).2.2.2

/-- The two-gap stitch path starting at the target endpoint of the selected
local main path indexed by a grid coordinate. -/
noncomputable def selectedOddLocalCrossbarGridCoordStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) : GraphPath G :=
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
  Q.path (Q.indexOfSource ⟨(M.path x).target, M.target_mem x⟩)

@[simp] theorem selectedOddLocalCrossbarGridCoordStitchPath_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    (selectedOddLocalCrossbarGridCoordStitchPath Hsys hcrossbars hlen i hnext x).source =
      ((selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i).path x).target := by
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
  have h :=
    congrArg Subtype.val
      (PerfectPathPacking.source_indexOfSource Q
        ⟨(M.path x).target, M.target_mem x⟩)
  simpa [selectedOddLocalCrossbarGridCoordStitchPath, M, Q] using h

/-- A coordinate stitch path stays inside the two connectors and the
intervening middle cluster used by the selected two-gap packing. -/
theorem selectedOddLocalCrossbarGridCoordStitchPath_staysIn
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    (selectedOddLocalCrossbarGridCoordStitchPath Hsys hcrossbars hlen i hnext x).vertexSet ⊆
      ((Hsys.base.connector (oddClusterIndex hlen i)
        (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∪
        (Hsys.base.cluster (middleClusterIndex hlen i) ∪
          (Hsys.base.connector
            (middleClusterIndex hlen i)
            (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet)) := by
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
  change (Q.path (Q.indexOfSource ⟨(M.path x).target, M.target_mem x⟩)).vertexSet ⊆ _
  exact selectedOddLocalCrossbarGridConcatPacking_staysIn
    Hsys hcrossbars hlen i hnext
    (Q.indexOfSource ⟨(M.path x).target, M.target_mem x⟩)

/-- Distinct grid coordinates use node-disjoint selected two-gap stitch paths. -/
theorem selectedOddLocalCrossbarGridCoordStitchPath_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    GraphPath.NodeDisjoint
      (selectedOddLocalCrossbarGridCoordStitchPath Hsys hcrossbars hlen i hnext x)
      (selectedOddLocalCrossbarGridCoordStitchPath Hsys hcrossbars hlen i hnext y) := by
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
  let qx := Q.indexOfSource ⟨(M.path x).target, M.target_mem x⟩
  let qy := Q.indexOfSource ⟨(M.path y).target, M.target_mem y⟩
  have hqx_source : (Q.path qx).source = (M.path x).target := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.source_indexOfSource Q
          ⟨(M.path x).target, M.target_mem x⟩)
    simpa [M, Q, qx] using h
  have hqy_source : (Q.path qy).source = (M.path y).target := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.source_indexOfSource Q
          ⟨(M.path y).target, M.target_mem y⟩)
    simpa [M, Q, qy] using h
  have hq_ne : qx ≠ qy := by
    intro hq
    apply hxy
    apply M.target_bijective.1
    have htarget : (M.path x).target = (M.path y).target := by
      calc
        (M.path x).target = (Q.path qx).source := hqx_source.symm
        _ = (Q.path qy).source := by rw [hq]
        _ = (M.path y).target := hqy_source
    exact Subtype.ext htarget
  simpa [selectedOddLocalCrossbarGridCoordStitchPath, M, Q, qx, qy] using
    Q.toPathPacking.node_disjoint hq_ne

/-- The coordinate in the next selected local crossbar reached by following the
two-gap stitch from coordinate `x`. -/
noncomputable def selectedOddLocalCrossbarGridNextCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) : GridVertex g :=
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let Mnext := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen j
  let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
  let q := Q.indexOfSource ⟨(M.path x).target, M.target_mem x⟩
  Mnext.indexOfSource ⟨(Q.path q).target, Q.target_mem q⟩

@[simp] theorem selectedOddLocalCrossbarGridNextCoord_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    ((selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen
        ⟨i.1 + 1, hnext⟩).path
      (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext x)).source =
      (selectedOddLocalCrossbarGridCoordStitchPath Hsys hcrossbars hlen i hnext x).target := by
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let Mnext := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen j
  let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
  let q := Q.indexOfSource ⟨(M.path x).target, M.target_mem x⟩
  have h :=
    congrArg Subtype.val
      (PerfectPathPacking.source_indexOfSource Mnext
        ⟨(Q.path q).target, Q.target_mem q⟩)
  simpa [selectedOddLocalCrossbarGridNextCoord,
    selectedOddLocalCrossbarGridCoordStitchPath, j, M, Mnext, Q, q] using h

/-- The two-gap stitching induces an injective map on grid coordinates. -/
theorem selectedOddLocalCrossbarGridNextCoord_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    Function.Injective
      (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext) := by
  intro x y hxy
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let Mnext := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen j
  let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
  let qx := Q.indexOfSource ⟨(M.path x).target, M.target_mem x⟩
  let qy := Q.indexOfSource ⟨(M.path y).target, M.target_mem y⟩
  have hnext_x :
      (Mnext.path
        (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext x)).source =
        (Q.path qx).target := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.source_indexOfSource Mnext
          ⟨(Q.path qx).target, Q.target_mem qx⟩)
    simpa [selectedOddLocalCrossbarGridNextCoord, j, M, Mnext, Q, qx] using h
  have hnext_y :
      (Mnext.path
        (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext y)).source =
        (Q.path qy).target := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.source_indexOfSource Mnext
          ⟨(Q.path qy).target, Q.target_mem qy⟩)
    simpa [selectedOddLocalCrossbarGridNextCoord, j, M, Mnext, Q, qy] using h
  have hQtarget : (Q.path qx).target = (Q.path qy).target := by
    calc
      (Q.path qx).target =
          (Mnext.path
            (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext x)).source :=
        hnext_x.symm
      _ =
          (Mnext.path
            (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext y)).source := by
        rw [hxy]
      _ = (Q.path qy).target := hnext_y
  have hq : qx = qy :=
    Q.target_bijective.1 (Subtype.ext hQtarget)
  have hQsource_x : (Q.path qx).source = (M.path x).target := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.source_indexOfSource Q
          ⟨(M.path x).target, M.target_mem x⟩)
    simpa [M, Q, qx] using h
  have hQsource_y : (Q.path qy).source = (M.path y).target := by
    have h :=
      congrArg Subtype.val
        (PerfectPathPacking.source_indexOfSource Q
          ⟨(M.path y).target, M.target_mem y⟩)
    simpa [M, Q, qy] using h
  have hMtarget : (M.path x).target = (M.path y).target := by
    calc
      (M.path x).target = (Q.path qx).source := hQsource_x.symm
      _ = (Q.path qy).source := by rw [hq]
      _ = (M.path y).target := hQsource_y
  exact M.target_bijective.1 (Subtype.ext hMtarget)

/-- The two-gap stitching induces a bijection on grid coordinates. -/
theorem selectedOddLocalCrossbarGridNextCoord_bijective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    Function.Bijective
      (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card
    (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext)).2
  constructor
  · exact selectedOddLocalCrossbarGridNextCoord_injective Hsys hcrossbars hlen i hnext
  · rfl

/-- The coordinate permutation induced by the selected two-gap stitching. -/
noncomputable def selectedOddLocalCrossbarGridNextCoordEquiv
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) :
    GridVertex g ≃ GridVertex g :=
  Equiv.ofBijective
    (selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext)
    (selectedOddLocalCrossbarGridNextCoord_bijective Hsys hcrossbars hlen i hnext)

@[simp] theorem selectedOddLocalCrossbarGridNextCoordEquiv_apply
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    selectedOddLocalCrossbarGridNextCoordEquiv Hsys hcrossbars hlen i hnext x =
      selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext x :=
  rfl

/-- Cumulative coordinate transport from the first selected odd crossbar to the
selected odd crossbar with natural index `t`. -/
noncomputable def selectedOddLocalCrossbarGridCoordTransportNat
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) :
    (t : ℕ) → t < m → GridVertex g ≃ GridVertex g
  | 0, _ => Equiv.refl (GridVertex g)
  | n + 1, ht =>
      (selectedOddLocalCrossbarGridCoordTransportNat Hsys hcrossbars hlen n
        (Nat.lt_of_succ_lt ht)).trans
        (selectedOddLocalCrossbarGridNextCoordEquiv Hsys hcrossbars hlen
          ⟨n, Nat.lt_of_succ_lt ht⟩ ht)
termination_by t _ => t

/-- Cumulative coordinate transport from the first selected odd crossbar to
the selected odd crossbar `i`. -/
noncomputable def selectedOddLocalCrossbarGridCoordTransport
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : GridVertex g ≃ GridVertex g :=
  selectedOddLocalCrossbarGridCoordTransportNat Hsys hcrossbars hlen i.1 i.2

@[simp] theorem selectedOddLocalCrossbarGridCoordTransport_zero
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (h0 : 0 < m) :
    selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen ⟨0, h0⟩ =
      Equiv.refl (GridVertex g) :=
  by
    simp [selectedOddLocalCrossbarGridCoordTransport,
      selectedOddLocalCrossbarGridCoordTransportNat]

@[simp] theorem selectedOddLocalCrossbarGridCoordTransport_succ
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {n : ℕ} (hsucc : n + 1 < m) :
    selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen ⟨n + 1, hsucc⟩ =
      (selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen
        ⟨n, Nat.lt_of_succ_lt hsucc⟩).trans
        (selectedOddLocalCrossbarGridNextCoordEquiv Hsys hcrossbars hlen
          ⟨n, Nat.lt_of_succ_lt hsucc⟩ hsucc) :=
  by
    simp [selectedOddLocalCrossbarGridCoordTransport,
      selectedOddLocalCrossbarGridCoordTransportNat]

/-- The transported coordinate at the next selected odd cluster is obtained by
applying the adjacent two-gap coordinate permutation to the transported
coordinate at the current selected odd cluster. -/
theorem selectedOddLocalCrossbarGridCoordTransport_next
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen
        ⟨i.1 + 1, hnext⟩ x =
      selectedOddLocalCrossbarGridNextCoord Hsys hcrossbars hlen i hnext
        (selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i x) := by
  cases i with
  | mk n hn =>
      simp [selectedOddLocalCrossbarGridCoordTransport_succ]

/-- The coordinate of an initial grid vertex after transport to a selected odd
cluster. -/
noncomputable def selectedOddLocalCrossbarGridTransportedCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : GridVertex g :=
  selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i x

/-- The selected local main path followed by an initial grid vertex after its
coordinate has been transported to the selected odd cluster `i`. -/
noncomputable def selectedOddLocalCrossbarGridTransportedMainPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : GraphPath G :=
  (selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i).path
    (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- Transported selected local main paths stay in the local footprint of the
selected odd cluster where they live. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).vertexSet ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) ∪
        (Hsys.hairConnector (oddClusterIndex hlen i)).toPathPacking.vertexSet := by
  simpa [selectedOddLocalCrossbarGridTransportedMainPath] using
    selectedOddLocalCrossbarGridMainPerfectPacking_path_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i
      (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- Transported selected local main paths are disjoint from the hair cluster of
the selected odd cluster where they live. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).vertexSet
      (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  simpa [selectedOddLocalCrossbarGridTransportedMainPath] using
    selectedOddLocalCrossbarGridMainPerfectPacking_path_vertexSet_disjoint_hairCluster
      Hsys hcrossbars hlen i
      (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- The selected two-gap stitch followed by an initial grid vertex between
selected odd clusters `i` and `i+1`. -/
noncomputable def selectedOddLocalCrossbarGridTransportedStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) : GraphPath G :=
  selectedOddLocalCrossbarGridCoordStitchPath Hsys hcrossbars hlen i hnext
    (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- The base path-of-sets region used by the two-gap stitch from selected odd
cluster `i` to the next selected odd cluster. -/
noncomputable def selectedOddLocalCrossbarGridStitchRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m) : Finset V :=
  (Hsys.base.connector (oddClusterIndex hlen i)
    (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∪
    (Hsys.base.cluster (middleClusterIndex hlen i) ∪
      (Hsys.base.connector
        (middleClusterIndex hlen i)
        (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet)

/-- Transported two-gap stitch paths stay inside the two base connectors and
middle cluster used by that stitch. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen i hnext x).vertexSet ⊆
      ((Hsys.base.connector (oddClusterIndex hlen i)
        (oddClusterIndex_gap hlen i)).toPathPacking.vertexSet ∪
        (Hsys.base.cluster (middleClusterIndex hlen i) ∪
          (Hsys.base.connector
            (middleClusterIndex hlen i)
            (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet)) := by
  simpa [selectedOddLocalCrossbarGridTransportedStitchPath] using
    selectedOddLocalCrossbarGridCoordStitchPath_staysIn
      Hsys hcrossbars hlen i hnext
      (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- Transported two-gap stitch paths stay inside their named stitch region. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_staysIn_region
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedStitchPath
      Hsys hcrossbars hlen i hnext x).vertexSet ⊆
      selectedOddLocalCrossbarGridStitchRegion Hsys hlen i hnext := by
  simpa [selectedOddLocalCrossbarGridStitchRegion] using
    selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
      Hsys hcrossbars hlen i hnext x

/-- Stitch regions belonging to distinct selected gaps are disjoint.  The proof
is a nine-case split over the three region pieces on each side; connector
families are disjoint for different base gaps, connector paths avoid
nonincident clusters, and distinct middle clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridStitchRegion_disjoint_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hlen : 2 * m ≤ ell) {i j : Fin m}
    (hinext : i.1 + 1 < m) (hjnext : j.1 + 1 < m)
    (hij : i ≠ j) :
    Disjoint
      (selectedOddLocalCrossbarGridStitchRegion Hsys hlen i hinext)
      (selectedOddLocalCrossbarGridStitchRegion Hsys hlen j hjnext) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [selectedOddLocalCrossbarGridStitchRegion] at hvi hvj
  rcases Finset.mem_union.mp hvi with hiFirst | hiRest
  · rcases Finset.mem_union.mp hvj with hjFirst | hjRest
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (Hsys.base.connector_mutually_nodeDisjoint
            (i := oddClusterIndex hlen i) (j := oddClusterIndex hlen j)
            (oddClusterIndex_gap hlen i) (oddClusterIndex_gap hlen j)
            (oddClusterIndex_ne_of_ne hlen hij)))
        hiFirst hjFirst
    · rcases Finset.mem_union.mp hjRest with hjMiddle | hjSecond
      · exact Finset.disjoint_left.mp
          (Hsys.base.connector_vertexSet_disjoint_cluster_of_ne
            (oddClusterIndex hlen i) (oddClusterIndex_gap hlen i)
            (middleClusterIndex hlen j)
            (middleClusterIndex_ne_oddClusterIndex hlen j i)
            (by
              simpa [middleClusterIndex_eq_odd_succ hlen i] using
                (middleClusterIndex_ne_of_ne hlen
                  (i := j) (j := i) (fun h => hij h.symm))))
          hiFirst hjMiddle
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.base.connector_mutually_nodeDisjoint
              (i := oddClusterIndex hlen i) (j := middleClusterIndex hlen j)
              (oddClusterIndex_gap hlen i) (middleClusterIndex_gap hlen hjnext)
              (oddClusterIndex_ne_middleClusterIndex hlen i j)))
          hiFirst hjSecond
  · rcases Finset.mem_union.mp hiRest with hiMiddle | hiSecond
    · rcases Finset.mem_union.mp hvj with hjFirst | hjRest
      · exact Finset.disjoint_left.mp
          ((Hsys.base.connector_vertexSet_disjoint_cluster_of_ne
            (oddClusterIndex hlen j) (oddClusterIndex_gap hlen j)
            (middleClusterIndex hlen i)
            (middleClusterIndex_ne_oddClusterIndex hlen i j)
            (by
              simpa [middleClusterIndex_eq_odd_succ hlen j] using
                (middleClusterIndex_ne_of_ne hlen
                  (i := i) (j := j) hij))).symm)
          hiMiddle hjFirst
      · rcases Finset.mem_union.mp hjRest with hjMiddle | hjSecond
        · exact Finset.disjoint_left.mp
            (Hsys.base.cluster_disjoint
              (middleClusterIndex_ne_of_ne hlen hij))
            hiMiddle hjMiddle
        · exact Finset.disjoint_left.mp
            ((Hsys.base.connector_vertexSet_disjoint_cluster_of_ne
              (middleClusterIndex hlen j) (middleClusterIndex_gap hlen hjnext)
              (middleClusterIndex hlen i)
              (middleClusterIndex_ne_of_ne hlen hij)
              (by
                simpa [oddClusterIndex_next_eq_middle_succ hlen hjnext] using
                  (middleClusterIndex_ne_oddClusterIndex hlen i
                    ⟨j.1 + 1, hjnext⟩))).symm)
            hiMiddle hjSecond
    · rcases Finset.mem_union.mp hvj with hjFirst | hjRest
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.base.connector_mutually_nodeDisjoint
              (i := middleClusterIndex hlen i) (j := oddClusterIndex hlen j)
              (middleClusterIndex_gap hlen hinext) (oddClusterIndex_gap hlen j)
              (middleClusterIndex_ne_oddClusterIndex hlen i j)))
          hiSecond hjFirst
      · rcases Finset.mem_union.mp hjRest with hjMiddle | hjSecond
        · exact Finset.disjoint_left.mp
            (Hsys.base.connector_vertexSet_disjoint_cluster_of_ne
              (middleClusterIndex hlen i) (middleClusterIndex_gap hlen hinext)
              (middleClusterIndex hlen j)
              (middleClusterIndex_ne_of_ne hlen (i := j) (j := i)
                (fun h => hij h.symm))
              (by
                simpa [oddClusterIndex_next_eq_middle_succ hlen hinext] using
                  (middleClusterIndex_ne_oddClusterIndex hlen j
                    ⟨i.1 + 1, hinext⟩)))
            hiSecond hjMiddle
        · exact Finset.disjoint_left.mp
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (Hsys.base.connector_mutually_nodeDisjoint
                (i := middleClusterIndex hlen i) (j := middleClusterIndex hlen j)
                (middleClusterIndex_gap hlen hinext)
                (middleClusterIndex_gap hlen hjnext)
                (middleClusterIndex_ne_of_ne hlen hij)))
            hiSecond hjSecond

/-- A selected odd hair-local footprint is disjoint from the two-gap stitch
region of a nonincident stitch.  The excluded incidents are exactly the two
odd clusters at the ends of the stitch. -/
theorem hairLocalVertexSet_disjoint_selectedOddLocalCrossbarGridStitchRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hnext : j.1 + 1 < m)
    (hij : i ≠ j) (hinext : i ≠ ⟨j.1 + 1, hnext⟩) :
    Disjoint (Hsys.hairLocalVertexSet (oddClusterIndex hlen i))
      ((Hsys.base.connector (oddClusterIndex hlen j)
        (oddClusterIndex_gap hlen j)).toPathPacking.vertexSet ∪
        (Hsys.base.cluster (middleClusterIndex hlen j) ∪
          (Hsys.base.connector
            (middleClusterIndex hlen j)
            (middleClusterIndex_gap hlen hnext)).toPathPacking.vertexSet)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvLocal hvRegion
  rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
  · have hodd_ne : oddClusterIndex hlen i ≠ oddClusterIndex hlen j :=
      oddClusterIndex_ne_of_ne hlen hij
    have hodd_ne_middleSucc :
        oddClusterIndex hlen i ≠
          ⟨(oddClusterIndex hlen j).1 + 1, oddClusterIndex_gap hlen j⟩ := by
      simpa [middleClusterIndex_eq_odd_succ hlen j] using
        oddClusterIndex_ne_middleClusterIndex hlen i j
    exact Finset.disjoint_left.mp
      (Hsys.hairLocalVertexSet_disjoint_baseConnector_of_ne
        (i := oddClusterIndex hlen i) (j := oddClusterIndex hlen j)
        (oddClusterIndex_gap hlen j) hodd_ne hodd_ne_middleSucc)
      hvLocal hvFirst
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
    · exact Finset.disjoint_left.mp
        (Hsys.hairLocalVertexSet_disjoint_baseCluster_of_ne
          (oddClusterIndex_ne_middleClusterIndex hlen i j))
        hvLocal hvMiddle
    · have hodd_ne_middle : oddClusterIndex hlen i ≠ middleClusterIndex hlen j :=
        oddClusterIndex_ne_middleClusterIndex hlen i j
      have hodd_ne_next :
          oddClusterIndex hlen i ≠
            ⟨(middleClusterIndex hlen j).1 + 1,
              middleClusterIndex_gap hlen hnext⟩ := by
        simpa [oddClusterIndex_next_eq_middle_succ hlen hnext] using
          oddClusterIndex_ne_of_ne hlen hinext
      exact Finset.disjoint_left.mp
        (Hsys.hairLocalVertexSet_disjoint_baseConnector_of_ne
          (i := oddClusterIndex hlen i) (j := middleClusterIndex hlen j)
          (middleClusterIndex_gap hlen hnext) hodd_ne_middle hodd_ne_next)
        hvLocal hvSecond

/-- Transported stitch paths are disjoint from the hair-local footprint of
every nonincident selected odd cluster. -/
theorem hairLocalVertexSet_disjoint_selectedOddLocalCrossbarGridTransportedStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hnext : j.1 + 1 < m)
    (hij : i ≠ j) (hinext : i ≠ ⟨j.1 + 1, hnext⟩)
    (x : GridVertex g) :
    Disjoint (Hsys.hairLocalVertexSet (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen j hnext x).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvLocal hvStitch
  have hvRegion :=
    selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
      Hsys hcrossbars hlen j hnext x hvStitch
  exact Finset.disjoint_left.mp
    (hairLocalVertexSet_disjoint_selectedOddLocalCrossbarGridStitchRegion
      Hsys hlen hnext hij hinext)
    hvLocal hvRegion

@[simp] theorem selectedOddLocalCrossbarGridTransportedStitchPath_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen i hnext x).source =
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).target := by
  simp [selectedOddLocalCrossbarGridTransportedStitchPath,
    selectedOddLocalCrossbarGridTransportedMainPath,
    selectedOddLocalCrossbarGridTransportedCoord]

@[simp] theorem selectedOddLocalCrossbarGridTransportedNextMainPath_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
        ⟨i.1 + 1, hnext⟩ x).source =
      (selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen
        i hnext x).target := by
  have h :=
    selectedOddLocalCrossbarGridNextCoord_source Hsys hcrossbars hlen i hnext
      (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)
  simp [selectedOddLocalCrossbarGridTransportedMainPath,
    selectedOddLocalCrossbarGridTransportedStitchPath,
    selectedOddLocalCrossbarGridTransportedCoord] at h ⊢

/-- Transported main paths for distinct initial coordinates remain
node-disjoint inside a fixed selected odd crossbar. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    GraphPath.NodeDisjoint
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i y) := by
  let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
  let e := selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i
  have hcoord : e x ≠ e y := by
    intro h
    exact hxy (e.injective h)
  simpa [selectedOddLocalCrossbarGridTransportedMainPath,
    selectedOddLocalCrossbarGridTransportedCoord, M, e] using
    M.toPathPacking.node_disjoint hcoord

/-- Transported stitch paths for distinct initial coordinates remain
node-disjoint across a fixed two-gap stitch. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    GraphPath.NodeDisjoint
      (selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen i hnext x)
      (selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen i hnext y) := by
  let e := selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i
  have hcoord : e x ≠ e y := by
    intro h
    exact hxy (e.injective h)
  simpa [selectedOddLocalCrossbarGridTransportedStitchPath,
    selectedOddLocalCrossbarGridTransportedCoord, e] using
    selectedOddLocalCrossbarGridCoordStitchPath_nodeDisjoint Hsys hcrossbars hlen
      i hnext hcoord

/-- The full row trace followed by an initial grid coordinate through all
selected odd local crossbars.  It contains all transported selected main paths
and all selected two-gap stitch paths between consecutive odd clusters. -/
noncomputable def selectedOddLocalCrossbarGridRowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (x : GridVertex g) : Finset V :=
  (Finset.univ.biUnion fun i : Fin m =>
    (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).vertexSet) ∪
    (Finset.univ.biUnion fun ih : {i : Fin m // i.1 + 1 < m} =>
      (selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen
        ih.1 ih.2 x).vertexSet)

/-- A transported selected main path is contained in the corresponding row
trace. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (x : GridVertex g) (i : Fin m) :
    (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).vertexSet ⊆
      selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x := by
  intro v hv
  rw [selectedOddLocalCrossbarGridRowTrace]
  exact Finset.mem_union_left _ <|
    Finset.mem_biUnion.mpr ⟨i, by simp, hv⟩

/-- A transported selected stitch path is contained in the corresponding row
trace. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_subset_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (x : GridVertex g)
    (i : Fin m) (hnext : i.1 + 1 < m) :
    (selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen i hnext x).vertexSet ⊆
      selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x := by
  intro v hv
  rw [selectedOddLocalCrossbarGridRowTrace]
  exact Finset.mem_union_right _ <|
    Finset.mem_biUnion.mpr ⟨⟨i, hnext⟩, by simp, hv⟩

/-- Membership in a selected row trace is membership in one transported main
path or one transported stitch path. -/
theorem mem_selectedOddLocalCrossbarGridRowTrace_iff
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (x : GridVertex g) (v : V) :
    v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x ↔
      (∃ i : Fin m,
        v ∈ (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen i x).vertexSet) ∨
      (∃ ih : {i : Fin m // i.1 + 1 < m},
        v ∈ (selectedOddLocalCrossbarGridTransportedStitchPath
          Hsys hcrossbars hlen ih.1 ih.2 x).vertexSet) := by
  classical
  rw [selectedOddLocalCrossbarGridRowTrace, Finset.mem_union]
  constructor
  · intro hv
    rcases hv with hvMain | hvStitch
    · rw [Finset.mem_biUnion] at hvMain
      rcases hvMain with ⟨i, _hi, hvPath⟩
      exact Or.inl ⟨i, hvPath⟩
    · rw [Finset.mem_biUnion] at hvStitch
      rcases hvStitch with ⟨ih, _hih, hvPath⟩
      exact Or.inr ⟨ih, hvPath⟩
  · intro hv
    rcases hv with ⟨i, hvPath⟩ | ⟨ih, hvPath⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, by simp, hvPath⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨ih, by simp, hvPath⟩)

/-- Any selected odd hair cluster is disjoint from any transported selected
main path. -/
theorem hairCluster_disjoint_selectedOddLocalCrossbarGridTransportedMainPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) (x : GridVertex g) :
    Disjoint (Hsys.hairCluster (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen j x).vertexSet := by
  classical
  by_cases hij : i = j
  · subst j
    exact (selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_hairCluster
      Hsys hcrossbars hlen i x).symm
  · rw [Finset.disjoint_left]
    intro v hvHair hvMain
    let idxI := oddClusterIndex hlen i
    let idxJ := oddClusterIndex hlen j
    have hvFootprint :
        v ∈ Hsys.base.cluster idxJ ∪
            (Hsys.hairConnector idxJ).toPathPacking.vertexSet :=
      (selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
        Hsys hcrossbars hlen j x) hvMain
    rcases Finset.mem_union.mp hvFootprint with hvBase | hvConn
    · exact Finset.disjoint_left.mp
        (Hsys.hairCluster_disjoint_base idxI idxJ) hvHair hvBase
    · have hidx : idxJ ≠ idxI :=
        oddClusterIndex_ne_of_ne hlen (fun h => hij h.symm)
      exact Finset.disjoint_left.mp
        ((Hsys.hairConnector_vertexSet_disjoint_hairCluster_of_ne
          (i := idxJ) (j := idxI) hidx).symm) hvHair hvConn

/-- Any selected odd hair cluster is disjoint from any transported two-gap
stitch path. -/
theorem hairCluster_disjoint_selectedOddLocalCrossbarGridTransportedStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) (hnext : j.1 + 1 < m)
    (x : GridVertex g) :
    Disjoint (Hsys.hairCluster (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen j hnext x).vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvHair hvStitch
  let idxI := oddClusterIndex hlen i
  have hvRegion :=
    selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
      Hsys hcrossbars hlen j hnext x hvStitch
  rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
  · exact Finset.disjoint_left.mp
      (Hsys.hairCluster_disjoint_baseConnectors idxI
        (oddClusterIndex hlen j) (oddClusterIndex_gap hlen j))
      hvHair hvFirst
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
    · exact Finset.disjoint_left.mp
        (Hsys.hairCluster_disjoint_base idxI (middleClusterIndex hlen j))
        hvHair hvMiddle
    · exact Finset.disjoint_left.mp
        (Hsys.hairCluster_disjoint_baseConnectors idxI
          (middleClusterIndex hlen j) (middleClusterIndex_gap hlen hnext))
        hvHair hvSecond

/-- Any selected odd hair cluster is disjoint from any full transported row
trace. -/
theorem hairCluster_disjoint_selectedOddLocalCrossbarGridRowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    Disjoint (Hsys.hairCluster (oddClusterIndex hlen i))
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvHair hvRow
  have hvSplit :=
    (mem_selectedOddLocalCrossbarGridRowTrace_iff
      Hsys hcrossbars hlen x v).1 hvRow
  rcases hvSplit with ⟨j, hvMain⟩ | ⟨jh, hvStitch⟩
  · exact Finset.disjoint_left.mp
      (hairCluster_disjoint_selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i j x) hvHair hvMain
  · exact Finset.disjoint_left.mp
      (hairCluster_disjoint_selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i jh.1 jh.2 x) hvHair hvStitch

/-- Symmetric form of
`hairCluster_disjoint_selectedOddLocalCrossbarGridRowTrace`. -/
theorem selectedOddLocalCrossbarGridRowTrace_disjoint_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    Disjoint (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
      (Hsys.hairCluster (oddClusterIndex hlen i)) :=
  (hairCluster_disjoint_selectedOddLocalCrossbarGridRowTrace
    Hsys hcrossbars hlen i x).symm

/-- Same-cluster transported main paths for distinct initial coordinates have
disjoint vertex sets. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i y).vertexSet := by
  simpa [GraphPath.NodeDisjoint] using
    selectedOddLocalCrossbarGridTransportedMainPath_nodeDisjoint
      Hsys hcrossbars hlen i hxy

/-- Same-gap transported stitch paths for distinct initial coordinates have
disjoint vertex sets. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext y).vertexSet := by
  simpa [GraphPath.NodeDisjoint] using
    selectedOddLocalCrossbarGridTransportedStitchPath_nodeDisjoint
      Hsys hcrossbars hlen i hnext hxy

/-- Transported stitch paths from distinct selected two-gap regions are
disjoint. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint_of_gap_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m}
    (hinext : i.1 + 1 < m) (hjnext : j.1 + 1 < m)
    (hij : i ≠ j) (x y : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hinext x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen j hjnext y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (selectedOddLocalCrossbarGridStitchRegion_disjoint_of_ne
      Hsys hlen hinext hjnext hij)
    (selectedOddLocalCrossbarGridTransportedStitchPath_staysIn_region
      Hsys hcrossbars hlen i hinext x hvi)
    (selectedOddLocalCrossbarGridTransportedStitchPath_staysIn_region
      Hsys hcrossbars hlen j hjnext y hvj)

/-- Transported stitch paths for distinct grid coordinates are disjoint, whether
they belong to the same selected gap or to different selected gaps. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell)
    (ih jh : {i : Fin m // i.1 + 1 < m})
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen ih.1 ih.2 x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen jh.1 jh.2 y).vertexSet := by
  by_cases hij : ih.1 = jh.1
  · have hsub : ih = jh := Subtype.ext hij
    subst jh
    exact selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint
      Hsys hcrossbars hlen ih.1 ih.2 hxy
  · exact selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint_of_gap_ne
      Hsys hcrossbars hlen ih.2 jh.2 hij x y

/-- Whole-row disjointness follows once every main/stitch piece from the first
row is disjoint from every main/stitch piece from the second row.  This is the
main reduction used to connect the local path-packing disjointness hypotheses
with the branch-set minor disjointness obligation. -/
theorem selectedOddLocalCrossbarGridRowTrace_disjoint_of_piecewise_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {x y : GridVertex g}
    (main_main :
      ∀ i j : Fin m,
        Disjoint
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i x).vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j y).vertexSet)
    (main_stitch :
      ∀ (i : Fin m) (jh : {j : Fin m // j.1 + 1 < m}),
        Disjoint
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i x).vertexSet
          (selectedOddLocalCrossbarGridTransportedStitchPath
            Hsys hcrossbars hlen jh.1 jh.2 y).vertexSet)
    (stitch_main :
      ∀ (ih : {i : Fin m // i.1 + 1 < m}) (j : Fin m),
        Disjoint
          (selectedOddLocalCrossbarGridTransportedStitchPath
            Hsys hcrossbars hlen ih.1 ih.2 x).vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j y).vertexSet)
    (stitch_stitch :
      ∀ ih jh : {i : Fin m // i.1 + 1 < m},
        Disjoint
          (selectedOddLocalCrossbarGridTransportedStitchPath
            Hsys hcrossbars hlen ih.1 ih.2 x).vertexSet
          (selectedOddLocalCrossbarGridTransportedStitchPath
            Hsys hcrossbars hlen jh.1 jh.2 y).vertexSet) :
    Disjoint
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  rw [mem_selectedOddLocalCrossbarGridRowTrace_iff Hsys hcrossbars hlen x v] at hvx
  rw [mem_selectedOddLocalCrossbarGridRowTrace_iff Hsys hcrossbars hlen y v] at hvy
  rcases hvx with ⟨i, hvxi⟩ | ⟨ih, hvxih⟩
  · rcases hvy with ⟨j, hvyj⟩ | ⟨jh, hvyjh⟩
    · exact (Finset.disjoint_left.mp (main_main i j)) hvxi hvyj
    · exact (Finset.disjoint_left.mp (main_stitch i jh)) hvxi hvyjh
  · rcases hvy with ⟨j, hvyj⟩ | ⟨jh, hvyjh⟩
    · exact (Finset.disjoint_left.mp (stitch_main ih j)) hvxih hvyj
    · exact (Finset.disjoint_left.mp (stitch_stitch ih jh)) hvxih hvyjh

/-- If there is at least one selected odd cluster, the row trace is nonempty. -/
theorem selectedOddLocalCrossbarGridRowTrace_nonempty
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (hm : 0 < m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x).Nonempty := by
  let i0 : Fin m := ⟨0, hm⟩
  refine ⟨(selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
    i0 x).source, ?_⟩
  exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_rowTrace
    Hsys hcrossbars hlen x i0
    (GraphPath.source_mem_vertexSet
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i0 x))

/-- The prefix of a selected row trace ending at selected odd cluster `n`.

It contains all transported main paths up to `n` and the transported stitch
paths between consecutive selected odd clusters before `n`.  This set is used
only as a proof device for row-trace connectivity. -/
noncomputable def selectedOddLocalCrossbarGridRowTracePrefixSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) :
    (n : ℕ) → n < m → GridVertex g → Set V
  | 0, h0, x =>
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen ⟨0, h0⟩ x).vertexSet
  | n + 1, hsucc, x =>
      selectedOddLocalCrossbarGridRowTracePrefixSet
          Hsys hcrossbars hlen n (Nat.lt_of_succ_lt hsucc) x ∪
        (selectedOddLocalCrossbarGridTransportedStitchPath
          Hsys hcrossbars hlen ⟨n, Nat.lt_of_succ_lt hsucc⟩ hsucc x).vertexSet ∪
        (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen ⟨n + 1, hsucc⟩ x).vertexSet
termination_by n _ _ => n

/-- Prefix row traces are contained in the full row trace. -/
theorem selectedOddLocalCrossbarGridRowTracePrefixSet_subset_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) :
    ∀ (n : ℕ) (hn : n < m) (x : GridVertex g),
      selectedOddLocalCrossbarGridRowTracePrefixSet Hsys hcrossbars hlen n hn x ⊆
        {v : V | v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x}
  | 0, hn, x => by
      intro v hv
      exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_rowTrace
        Hsys hcrossbars hlen x ⟨0, hn⟩
          (by simpa [selectedOddLocalCrossbarGridRowTracePrefixSet] using hv)
  | n + 1, hn, x => by
      intro v hv
      rw [selectedOddLocalCrossbarGridRowTracePrefixSet] at hv
      rcases hv with hvLeft | hvMain
      · rcases hvLeft with hvPrev | hvStitch
        · exact selectedOddLocalCrossbarGridRowTracePrefixSet_subset_rowTrace
            Hsys hcrossbars hlen n (Nat.lt_of_succ_lt hn) x hvPrev
        · exact selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_subset_rowTrace
            Hsys hcrossbars hlen x ⟨n, Nat.lt_of_succ_lt hn⟩ hn hvStitch
      · exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_rowTrace
          Hsys hcrossbars hlen x ⟨n + 1, hn⟩ hvMain

/-- The first main-path source lies in every nonempty row-trace prefix. -/
theorem selectedOddLocalCrossbarGridRowTracePrefixSet_anchor_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) :
    ∀ (n : ℕ) (hn : n < m) (x : GridVertex g),
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
        ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le n) hn⟩ x).source ∈
          selectedOddLocalCrossbarGridRowTracePrefixSet Hsys hcrossbars hlen n hn x
  | 0, hn, x => by
      simp [selectedOddLocalCrossbarGridRowTracePrefixSet]
  | n + 1, hn, x => by
      rw [selectedOddLocalCrossbarGridRowTracePrefixSet]
      exact Or.inl (Or.inl (by
        simpa using
          selectedOddLocalCrossbarGridRowTracePrefixSet_anchor_mem
            Hsys hcrossbars hlen n (Nat.lt_of_succ_lt hn) x))

/-- The last main-path target lies in the corresponding row-trace prefix. -/
theorem selectedOddLocalCrossbarGridRowTracePrefixSet_lastMain_target_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) :
    ∀ (n : ℕ) (hn : n < m) (x : GridVertex g),
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
        ⟨n, hn⟩ x).target ∈
          selectedOddLocalCrossbarGridRowTracePrefixSet Hsys hcrossbars hlen n hn x
  | 0, hn, x => by
      simp [selectedOddLocalCrossbarGridRowTracePrefixSet]
  | n + 1, hn, x => by
      rw [selectedOddLocalCrossbarGridRowTracePrefixSet]
      exact Or.inr
        (GraphPath.target_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
            ⟨n + 1, hn⟩ x))

/-- Every selected row-trace prefix is connected.  Consecutive pieces intersect:
the stitch path starts at the previous main-path target, and the next main path
starts at the stitch target. -/
theorem selectedOddLocalCrossbarGridRowTracePrefixSet_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) :
    ∀ (n : ℕ) (hn : n < m) (x : GridVertex g),
      (G.induce
        (selectedOddLocalCrossbarGridRowTracePrefixSet
          Hsys hcrossbars hlen n hn x)).Connected
  | 0, hn, x => by
      rw [selectedOddLocalCrossbarGridRowTracePrefixSet]
      exact GraphPath.connected_induce_vertexSet
        (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
          ⟨0, hn⟩ x)
  | n + 1, hn, x => by
      let Sprev : Set V :=
        selectedOddLocalCrossbarGridRowTracePrefixSet Hsys hcrossbars hlen n
          (Nat.lt_of_succ_lt hn) x
      let Pstitch : GraphPath G :=
        selectedOddLocalCrossbarGridTransportedStitchPath Hsys hcrossbars hlen
          ⟨n, Nat.lt_of_succ_lt hn⟩ hn x
      let Sstitch : Set V := Pstitch.vertexSet
      let Pmain : GraphPath G :=
        selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
          ⟨n + 1, hn⟩ x
      let Smain : Set V := Pmain.vertexSet
      have hprev : (G.induce Sprev).Connected := by
        simpa [Sprev] using
          selectedOddLocalCrossbarGridRowTracePrefixSet_connected
            Hsys hcrossbars hlen n (Nat.lt_of_succ_lt hn) x
      have hstitch : (G.induce Sstitch).Connected := by
        change (G.induce (Pstitch.vertexSet : Set V)).Connected
        exact GraphPath.connected_induce_vertexSet Pstitch
      have hmain : (G.induce Smain).Connected := by
        change (G.induce (Pmain.vertexSet : Set V)).Connected
        exact GraphPath.connected_induce_vertexSet Pmain
      have hinterPrevStitch : (Sprev ∩ Sstitch).Nonempty := by
        refine ⟨(selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
          ⟨n, Nat.lt_of_succ_lt hn⟩ x).target, ?_, ?_⟩
        · exact selectedOddLocalCrossbarGridRowTracePrefixSet_lastMain_target_mem
            Hsys hcrossbars hlen n (Nat.lt_of_succ_lt hn) x
        · have hsource :
              Pstitch.source =
                (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
                  ⟨n, Nat.lt_of_succ_lt hn⟩ x).target := by
            simp [Pstitch]
          simpa [Sstitch, hsource] using
            GraphPath.source_mem_vertexSet Pstitch
      have hprevStitch : (G.induce (Sprev ∪ Sstitch)).Connected :=
        G.induce_union_connected hprev.preconnected hstitch.preconnected
          hinterPrevStitch
      have hinterStitchMain : ((Sprev ∪ Sstitch) ∩ Smain).Nonempty := by
        refine ⟨Pstitch.target, ?_, ?_⟩
        · exact Or.inr (by
            simp [Sstitch])
        · have hsource :
              Pmain.source = Pstitch.target := by
            simpa [Pmain, Pstitch] using
              selectedOddLocalCrossbarGridTransportedNextMainPath_source
                Hsys hcrossbars hlen ⟨n, Nat.lt_of_succ_lt hn⟩ hn x
          simpa [Smain, hsource] using
            GraphPath.source_mem_vertexSet Pmain
      have htotal : (G.induce ((Sprev ∪ Sstitch) ∪ Smain)).Connected :=
        G.induce_union_connected hprevStitch.preconnected hmain.preconnected
          hinterStitchMain
      rw [selectedOddLocalCrossbarGridRowTracePrefixSet]
      change (G.induce ((Sprev ∪ Sstitch) ∪ Smain)).Connected
      exact htotal

/-- Every vertex of the full row trace lies in some connected prefix. -/
theorem exists_mem_selectedOddLocalCrossbarGridRowTracePrefixSet_of_mem_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {x : GridVertex g} {v : V}
    (hv : v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x) :
    ∃ n, ∃ hn : n < m,
      v ∈ selectedOddLocalCrossbarGridRowTracePrefixSet Hsys hcrossbars hlen n hn x := by
  classical
  rw [selectedOddLocalCrossbarGridRowTrace, Finset.mem_union] at hv
  rcases hv with hvMain | hvStitch
  · rw [Finset.mem_biUnion] at hvMain
    rcases hvMain with ⟨i, _hi, hvPath⟩
    rcases i with ⟨n, hn⟩
    refine ⟨n, hn, ?_⟩
    cases n with
    | zero =>
        simpa [selectedOddLocalCrossbarGridRowTracePrefixSet] using hvPath
    | succ n =>
        rw [selectedOddLocalCrossbarGridRowTracePrefixSet]
        exact Or.inr hvPath
  · rw [Finset.mem_biUnion] at hvStitch
    rcases hvStitch with ⟨ih, _hih, hvPath⟩
    rcases ih with ⟨i, hnext⟩
    rcases i with ⟨n, hn⟩
    refine ⟨n + 1, hnext, ?_⟩
    rw [selectedOddLocalCrossbarGridRowTracePrefixSet]
    exact Or.inl (Or.inr hvPath)

/-- Full selected row traces are connected. -/
theorem selectedOddLocalCrossbarGridRowTrace_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (hm : 0 < m) (x : GridVertex g) :
    (G.induce
      {v : V | v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x}).Connected := by
  classical
  let a : V :=
    (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
      ⟨0, hm⟩ x).source
  have haRow : a ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x := by
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_rowTrace
      Hsys hcrossbars hlen x ⟨0, hm⟩
      (by
        dsimp [a]
        exact GraphPath.source_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen
            ⟨0, hm⟩ x))
  refine G.induce_connected_of_patches a haRow ?_
  intro v hv
  change v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x at hv
  rcases exists_mem_selectedOddLocalCrossbarGridRowTracePrefixSet_of_mem_rowTrace
      Hsys hcrossbars hlen hv with
    ⟨n, hn, hvPrefix⟩
  let S : Set V :=
    selectedOddLocalCrossbarGridRowTracePrefixSet Hsys hcrossbars hlen n hn x
  have haPrefix : a ∈ S := by
    dsimp [S, a]
    simpa using
      selectedOddLocalCrossbarGridRowTracePrefixSet_anchor_mem
        Hsys hcrossbars hlen n hn x
  refine ⟨S, ?_, haPrefix, hvPrefix, ?_⟩
  · exact selectedOddLocalCrossbarGridRowTracePrefixSet_subset_rowTrace
      Hsys hcrossbars hlen n hn x
  · have hconn : (G.induce S).Connected := by
      simpa [S] using
        selectedOddLocalCrossbarGridRowTracePrefixSet_connected
          Hsys hcrossbars hlen n hn x
    exact hconn.preconnected ⟨a, haPrefix⟩ ⟨v, hvPrefix⟩

/-- Transport a finite set of initial grid coordinates to the coordinate set
seen in selected odd cluster `i`. -/
noncomputable def selectedOddLocalCrossbarGridTransportedCoordImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset (GridVertex g) :=
  U.image (selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i)

@[simp] theorem selectedOddLocalCrossbarGridTransportedCoordImage_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddLocalCrossbarGridTransportedCoordImage,
    Finset.card_image_of_injective]
  exact (selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i).injective

/-- Transport preserves disjointness of finite coordinate sets. -/
theorem selectedOddLocalCrossbarGridTransportedCoordImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i W) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  let e := selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i
  rw [selectedOddLocalCrossbarGridTransportedCoordImage] at hvU hvW
  rcases Finset.mem_image.mp hvU with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hvW with ⟨y, hy, hyx⟩
  have hxy : y = x := e.injective hyx
  exact Finset.disjoint_left.mp hUW hx (by simpa [hxy] using hy)

/-- The attachment vertex selected in cluster `i` by an initial coordinate
after transporting that coordinate to cluster `i`. -/
noncomputable def selectedOddLocalCrossbarGridTransportedAttachment
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : V :=
  selectedOddLocalCrossbarGridAttachment Hsys hcrossbars hlen i
    (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- The hair endpoint selected in cluster `i` by an initial coordinate after
transporting that coordinate to cluster `i`. -/
noncomputable def selectedOddLocalCrossbarGridTransportedHairEndpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : V :=
  selectedOddLocalCrossbarGridHairEndpoint Hsys hcrossbars hlen i
    (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- The oriented spoke selected in cluster `i` by an initial coordinate after
transporting that coordinate to cluster `i`. -/
noncomputable def selectedOddLocalCrossbarGridTransportedSpokePath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : GraphPath G :=
  selectedOddLocalCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i
    (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

@[simp] theorem selectedOddLocalCrossbarGridTransportedSpokePath_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x).source =
      selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x := by
  simp [selectedOddLocalCrossbarGridTransportedSpokePath,
    selectedOddLocalCrossbarGridTransportedAttachment]

@[simp] theorem selectedOddLocalCrossbarGridTransportedSpokePath_target
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x).target =
      selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x := by
  simp [selectedOddLocalCrossbarGridTransportedSpokePath,
    selectedOddLocalCrossbarGridTransportedHairEndpoint]

/-- Transporting the grid coordinate preserves the exact singleton
intersection between the selected main path and its spoke. -/
theorem selectedOddLocalCrossbarGridTransportedAttachment_meetsExactly
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).MeetsExactlyAt
      (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x) := by
  classical
  let y := selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x
  have hmeet := selectedOddLocalCrossbarGridAttachment_meetsExactly
    Hsys hcrossbars hlen i y
  rw [GraphPath.MeetsExactlyAt] at hmeet ⊢
  have hmain :
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).vertexSet =
        (selectedOddLocalCrossbarGridMainPath Hsys hcrossbars hlen i y).vertexSet := by
    simp [selectedOddLocalCrossbarGridTransportedMainPath,
      selectedOddLocalCrossbarGridMainPerfectPacking,
      PathPacking.toPerfectUsedTerminals,
      selectedOddLocalCrossbarGridMainPath, y]
  have hspoke :
      (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x).vertexSet =
        (selectedOddLocalCrossbarGridSpokePath Hsys hcrossbars hlen i y).vertexSet := by
    simp [selectedOddLocalCrossbarGridTransportedSpokePath,
      selectedOddLocalCrossbarGridOrientedSpokePath, y]
  rw [hmain, hspoke]
  simpa [selectedOddLocalCrossbarGridTransportedAttachment, y] using hmeet

/-- Transported spokes still use only edges of the corresponding local hair
graph. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    ↑(selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet := by
  simpa [selectedOddLocalCrossbarGridTransportedSpokePath] using
    selectedOddLocalCrossbarGridOrientedSpokePath_edgeSet_subset_hairLocalGraph
      Hsys hcrossbars hlen i
      (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- Transported selected local spokes stay in the local footprint of the
selected odd cluster where they live. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x).vertexSet ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) ∪
        (Hsys.hairConnector (oddClusterIndex hlen i)).toPathPacking.vertexSet := by
  simpa [selectedOddLocalCrossbarGridTransportedSpokePath] using
    selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i
      (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- A transported spoke meets the selected hair cluster only at its transported
hair endpoint. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_mem_hairCluster_eq_hairEndpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) {v : V}
    (hvSpoke :
      v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet)
    (hvHair : v ∈ Hsys.hairCluster (oddClusterIndex hlen i)) :
    v = selectedOddLocalCrossbarGridTransportedHairEndpoint
      Hsys hcrossbars hlen i x := by
  classical
  let idx := oddClusterIndex hlen i
  let P := selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x
  let Hlocal := Hsys.hairLocalGraph idx
  have hvLocalFootprint : v ∈ Hsys.hairLocalVertexSet idx := by
    rw [HairyPathOfSetsSystem.hairLocalVertexSet]
    exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvSpoke
  have hvY : v ∈ Hsys.y idx :=
    Hsys.mem_y_of_mem_hairLocalVertexSet_and_hairCluster idx
      hvLocalFootprint hvHair
  have hEdges : ∀ e, e ∈ P.walk.edges → e ∈ Hlocal.edgeSet := by
    intro e he
    exact
      (selectedOddLocalCrossbarGridTransportedSpokePath_edgeSet_subset_hairLocalGraph
        Hsys hcrossbars hlen i x) (by
          simpa [P, GraphPath.edgeSet] using he)
  let Plocal := P.transfer Hlocal hEdges
  have hvLocalPath : v ∈ Plocal.vertexSet := by
    simpa [Plocal, P] using hvSpoke
  have hendLocal :
      Plocal.IsEndpoint v :=
    GraphPath.isEndpoint_of_mem_vertexSet_of_degreeEquals_one Plocal
      (Hsys.hairLocalGraph_degreeEquals_one_of_mem_y idx hvY) hvLocalPath
  have hend : P.IsEndpoint v := by
    simpa [Plocal, P, GraphPath.transfer, GraphPath.IsEndpoint] using hendLocal
  rcases hend with hsource | htarget
  · have hsourceHair : P.source ∈ Hsys.hairCluster idx := by
      simpa [hsource] using hvHair
    have hattachHair :
        selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x ∈
          Hsys.hairCluster idx := by
      simpa [P] using hsourceHair
    have hattachMain :
        selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x ∈
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i x).vertexSet :=
      by
        simpa [selectedOddLocalCrossbarGridTransportedAttachment,
          selectedOddLocalCrossbarGridTransportedMainPath,
          selectedOddLocalCrossbarGridMainPerfectPacking,
          selectedOddLocalCrossbarGridMainPath,
          PathPacking.toPerfectUsedTerminals] using
          selectedOddLocalCrossbarGridAttachment_mem_main Hsys hcrossbars hlen i
            (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)
    exact False.elim
      (Finset.disjoint_left.mp
        (selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_hairCluster
          Hsys hcrossbars hlen i x) hattachMain hattachHair)
  · simpa [P] using htarget

/-- Transported main paths in distinct selected odd clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j)
    (x y : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen j y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hsubi :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvi
  have hsubj :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen j y hvj
  exact Finset.disjoint_left.mp
    (Hsys.hairLocalVertexSet_disjoint_of_ne (oddClusterIndex_ne_of_ne hlen hij))
    hsubi hsubj

/-- Transported main paths for distinct grid coordinates are disjoint, whether
they lie in the same selected odd cluster or in different selected odd
clusters. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen j y).vertexSet := by
  by_cases hij : i = j
  · subst j
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint
      Hsys hcrossbars hlen i hxy
  · exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_of_ne
      Hsys hcrossbars hlen hij x y

/-- In the current endpoint cluster of a stitch, a different coordinate's
transported main path is disjoint from that stitch.  The stitch can meet the
current base cluster only at its source, which is the target of the main path
with the same coordinate. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_currentStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext y).vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvMain hvStitch
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) :=
    selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvMain
  rw [HairyPathOfSetsSystem.hairLocalVertexSet] at hvLocal
  rcases Finset.mem_union.mp hvLocal with hvBase | hvHair
  · let coord :=
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i y
    let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
    let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
    let q : Q.Index := Q.indexOfSource ⟨(M.path coord).target, M.target_mem coord⟩
    have hend : (Q.path q).IsEndpoint v := by
      change v ∈ (Q.path q).vertexSet at hvStitch
      exact selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_current
        Hsys hcrossbars hlen i hnext q hvStitch hvBase
    rcases hend with hsource | htarget
    · have hvMainY :
          v ∈ (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i y).vertexSet := by
        have hsrc :=
          selectedOddLocalCrossbarGridTransportedStitchPath_source
            Hsys hcrossbars hlen i hnext y
        change (Q.path q).source =
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i y).target at hsrc
        rw [hsource, hsrc]
        exact GraphPath.target_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i y)
      exact Finset.disjoint_left.mp
        (selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint
          Hsys hcrossbars hlen i hxy)
        hvMain hvMainY
    · have hnextMainSource :
          v =
            (selectedOddLocalCrossbarGridTransportedMainPath
              Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y).source := by
        have htgt :=
          selectedOddLocalCrossbarGridTransportedNextMainPath_source
            Hsys hcrossbars hlen i hnext y
        change
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y).source =
              (Q.path q).target at htgt
        exact htarget.trans htgt.symm
      have hcurLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
        rw [HairyPathOfSetsSystem.hairLocalVertexSet]
        exact Finset.mem_union_left _ hvBase
      have hnextLocal :
          v ∈ Hsys.hairLocalVertexSet
              (oddClusterIndex hlen ⟨i.1 + 1, hnext⟩) := by
        exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
          Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y
          (by
            rw [hnextMainSource]
            exact GraphPath.source_mem_vertexSet
              (selectedOddLocalCrossbarGridTransportedMainPath
                Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y))
      have hindex_ne : i ≠ ⟨i.1 + 1, hnext⟩ := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
      exact Finset.disjoint_left.mp
        (Hsys.hairLocalVertexSet_disjoint_of_ne
          (oddClusterIndex_ne_of_ne hlen hindex_ne))
        hcurLocal hnextLocal
  · have hvRegion :=
      selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
        Hsys hcrossbars hlen i hnext y hvStitch
    rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (Hsys.hairConnector_disjoint_baseConnectors
            (oddClusterIndex hlen i) (oddClusterIndex hlen i)
            (oddClusterIndex_gap hlen i)))
        hvHair hvFirst
    · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
      · exact Finset.disjoint_left.mp
          (Hsys.hairConnector_vertexSet_disjoint_baseCluster_of_ne
            (oddClusterIndex_ne_middleClusterIndex hlen i i))
          hvHair hvMiddle
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.hairConnector_disjoint_baseConnectors
              (oddClusterIndex hlen i) (middleClusterIndex hlen i)
              (middleClusterIndex_gap hlen hnext)))
          hvHair hvSecond

/-- In the next endpoint cluster of a stitch, a different coordinate's
transported main path is disjoint from that stitch. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_nextStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext y).vertexSet := by
  classical
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  rw [Finset.disjoint_left]
  intro v hvMain hvStitch
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen j x (by simpa [j] using hvMain)
  rw [HairyPathOfSetsSystem.hairLocalVertexSet] at hvLocal
  rcases Finset.mem_union.mp hvLocal with hvBase | hvHair
  · let coord :=
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i y
    let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
    let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
    let q : Q.Index := Q.indexOfSource ⟨(M.path coord).target, M.target_mem coord⟩
    have hend : (Q.path q).IsEndpoint v := by
      change v ∈ (Q.path q).vertexSet at hvStitch
      exact selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_next
        Hsys hcrossbars hlen i hnext q hvStitch (by simpa [j] using hvBase)
    rcases hend with hsource | htarget
    · have hsrc :=
        selectedOddLocalCrossbarGridTransportedStitchPath_source
          Hsys hcrossbars hlen i hnext y
      change (Q.path q).source =
        (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen i y).target at hsrc
      have hcurLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
        exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
          Hsys hcrossbars hlen i y
          (by
            rw [hsource, hsrc]
            exact GraphPath.target_mem_vertexSet
              (selectedOddLocalCrossbarGridTransportedMainPath
                Hsys hcrossbars hlen i y))
      have hnextLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
        rw [HairyPathOfSetsSystem.hairLocalVertexSet]
        exact Finset.mem_union_left _ hvBase
      have hindex_ne : i ≠ j := by
        intro h
        have hval := congrArg Fin.val h
        simp [j] at hval
      exact Finset.disjoint_left.mp
        (Hsys.hairLocalVertexSet_disjoint_of_ne
          (oddClusterIndex_ne_of_ne hlen hindex_ne))
        hcurLocal hnextLocal
    · have htgt :=
        selectedOddLocalCrossbarGridTransportedNextMainPath_source
          Hsys hcrossbars hlen i hnext y
      change
        (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen j y).source = (Q.path q).target at htgt
      have hvMainY :
          v ∈ (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j y).vertexSet := by
        rw [htarget, ← htgt]
        exact GraphPath.source_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j y)
      exact Finset.disjoint_left.mp
        (selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint
          Hsys hcrossbars hlen j hxy)
        (by simpa [j] using hvMain) hvMainY
  · have hvRegion :=
      selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
        Hsys hcrossbars hlen i hnext y hvStitch
    rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (Hsys.hairConnector_disjoint_baseConnectors
            (oddClusterIndex hlen j) (oddClusterIndex hlen i)
            (oddClusterIndex_gap hlen i)))
        hvHair hvFirst
    · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
      · exact Finset.disjoint_left.mp
          (Hsys.hairConnector_vertexSet_disjoint_baseCluster_of_ne
            (by
              have hne := oddClusterIndex_ne_middleClusterIndex hlen j i
              simpa using hne))
          hvHair hvMiddle
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.hairConnector_disjoint_baseConnectors
              (oddClusterIndex hlen j) (middleClusterIndex hlen i)
              (middleClusterIndex_gap hlen hnext)))
          hvHair hvSecond

/-- A transported main path and an arbitrary transported stitch path are
disjoint for distinct grid coordinates.  The proof splits into the two
incident endpoint cases and the nonincident footprint case. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_stitchPath_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) (hnext : j.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen j hnext y).vertexSet := by
  by_cases hij : i = j
  · subst i
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_currentStitchPath
      Hsys hcrossbars hlen j hnext hxy
  · by_cases hinext : i = ⟨j.1 + 1, hnext⟩
    · subst i
      exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_nextStitchPath
        Hsys hcrossbars hlen j hnext hxy
    · rw [Finset.disjoint_left]
      intro v hvMain hvStitch
      have hvLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) :=
        selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
          Hsys hcrossbars hlen i x hvMain
      exact Finset.disjoint_left.mp
        (hairLocalVertexSet_disjoint_selectedOddLocalCrossbarGridTransportedStitchPath
          Hsys hcrossbars hlen hnext hij hinext y)
        hvLocal hvStitch

/-- A transported main path and a transported spoke path in distinct selected
odd clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j)
    (x y : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen j y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hsubi :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvi
  have hsubj :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
    exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen j y hvj
  exact Finset.disjoint_left.mp
    (Hsys.hairLocalVertexSet_disjoint_of_ne (oddClusterIndex_ne_of_ne hlen hij))
    hsubi hsubj

/-- A transported main path and a transported spoke path with distinct grid
coordinates in the same selected odd cluster are disjoint. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i y).vertexSet := by
  let e := selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i
  have hcoord : e x ≠ e y := by
    intro h
    exact hxy (e.injective h)
  simpa [selectedOddLocalCrossbarGridTransportedMainPath,
    selectedOddLocalCrossbarGridMainPerfectPacking,
    PathPacking.toPerfectUsedTerminals,
    selectedOddLocalCrossbarGridMainPath,
    selectedOddLocalCrossbarGridTransportedSpokePath,
    selectedOddLocalCrossbarGridTransportedCoord, GraphPath.NodeDisjoint, e] using
    selectedOddLocalCrossbarGridSpoke_disjoint_other_main Hsys hcrossbars hlen i hcoord

/-- A transported main path and a transported spoke path with distinct grid
coordinates are disjoint, whether they lie in the same selected odd cluster or
in different selected odd clusters. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen j y).vertexSet := by
  by_cases hij : i = j
  · subst j
    exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath
      Hsys hcrossbars hlen i hxy
  · exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath_of_ne
      Hsys hcrossbars hlen hij x y

/-- Symmetric form of
`selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath_of_grid_ne`. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_mainPath_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen j y).vertexSet := by
  exact (selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath_of_grid_ne
    Hsys hcrossbars hlen j i hxy.symm).symm

/-- Transported spoke paths in distinct selected odd clusters are disjoint. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j)
    (x y : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen j y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hsubi :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
    exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvi
  have hsubj :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
    exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen j y hvj
  exact Finset.disjoint_left.mp
    (Hsys.hairLocalVertexSet_disjoint_of_ne (oddClusterIndex_ne_of_ne hlen hij))
    hsubi hsubj

/-- A transported main path is disjoint from a nonincident transported stitch
path.  A stitch between rows `j` and `j+1` may only meet the odd-cluster
footprints of those two rows. -/
theorem selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_stitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hnext : j.1 + 1 < m)
    (hij : i ≠ j) (hinext : i ≠ ⟨j.1 + 1, hnext⟩)
    (x y : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen j hnext y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvMain hvStitch
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) :=
    selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvMain
  exact Finset.disjoint_left.mp
    (hairLocalVertexSet_disjoint_selectedOddLocalCrossbarGridTransportedStitchPath
      Hsys hcrossbars hlen hnext hij hinext y)
    hvLocal hvStitch

/-- A transported spoke path is disjoint from a nonincident transported stitch
path. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_stitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hnext : j.1 + 1 < m)
    (hij : i ≠ j) (hinext : i ≠ ⟨j.1 + 1, hnext⟩)
    (x y : GridVertex g) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen j hnext y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvSpoke hvStitch
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) :=
    selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvSpoke
  exact Finset.disjoint_left.mp
    (hairLocalVertexSet_disjoint_selectedOddLocalCrossbarGridTransportedStitchPath
      Hsys hcrossbars hlen hnext hij hinext y)
    hvLocal hvStitch

/-- In the current endpoint cluster of a stitch, a different coordinate's
transported spoke is disjoint from that stitch. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_currentStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext y).vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvSpoke hvStitch
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) :=
    selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvSpoke
  rw [HairyPathOfSetsSystem.hairLocalVertexSet] at hvLocal
  rcases Finset.mem_union.mp hvLocal with hvBase | hvHair
  · let coord :=
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i y
    let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
    let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
    let q : Q.Index := Q.indexOfSource ⟨(M.path coord).target, M.target_mem coord⟩
    have hend : (Q.path q).IsEndpoint v := by
      change v ∈ (Q.path q).vertexSet at hvStitch
      exact selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_current
        Hsys hcrossbars hlen i hnext q hvStitch hvBase
    rcases hend with hsource | htarget
    · have hvMainY :
          v ∈ (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i y).vertexSet := by
        have hsrc :=
          selectedOddLocalCrossbarGridTransportedStitchPath_source
            Hsys hcrossbars hlen i hnext y
        change (Q.path q).source =
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i y).target at hsrc
        rw [hsource, hsrc]
        exact GraphPath.target_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i y)
      exact Finset.disjoint_left.mp
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_mainPath_of_grid_ne
          Hsys hcrossbars hlen i i hxy)
        hvSpoke hvMainY
    · have hnextMainSource :
          v =
            (selectedOddLocalCrossbarGridTransportedMainPath
              Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y).source := by
        have htgt :=
          selectedOddLocalCrossbarGridTransportedNextMainPath_source
            Hsys hcrossbars hlen i hnext y
        change
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y).source =
              (Q.path q).target at htgt
        exact htarget.trans htgt.symm
      have hcurLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
        rw [HairyPathOfSetsSystem.hairLocalVertexSet]
        exact Finset.mem_union_left _ hvBase
      have hnextLocal :
          v ∈ Hsys.hairLocalVertexSet
              (oddClusterIndex hlen ⟨i.1 + 1, hnext⟩) := by
        exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
          Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y
          (by
            rw [hnextMainSource]
            exact GraphPath.source_mem_vertexSet
              (selectedOddLocalCrossbarGridTransportedMainPath
                Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ y))
      have hindex_ne : i ≠ ⟨i.1 + 1, hnext⟩ := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
      exact Finset.disjoint_left.mp
        (Hsys.hairLocalVertexSet_disjoint_of_ne
          (oddClusterIndex_ne_of_ne hlen hindex_ne))
        hcurLocal hnextLocal
  · have hvRegion :=
      selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
        Hsys hcrossbars hlen i hnext y hvStitch
    rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (Hsys.hairConnector_disjoint_baseConnectors
            (oddClusterIndex hlen i) (oddClusterIndex hlen i)
            (oddClusterIndex_gap hlen i)))
        hvHair hvFirst
    · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
      · exact Finset.disjoint_left.mp
          (Hsys.hairConnector_vertexSet_disjoint_baseCluster_of_ne
            (oddClusterIndex_ne_middleClusterIndex hlen i i))
          hvHair hvMiddle
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.hairConnector_disjoint_baseConnectors
              (oddClusterIndex hlen i) (middleClusterIndex hlen i)
              (middleClusterIndex_gap hlen hnext)))
          hvHair hvSecond

/-- In the next endpoint cluster of a stitch, a different coordinate's
transported spoke is disjoint from that stitch. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_nextStitchPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext y).vertexSet := by
  classical
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  rw [Finset.disjoint_left]
  intro v hvSpoke hvStitch
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
    exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen j x (by simpa [j] using hvSpoke)
  rw [HairyPathOfSetsSystem.hairLocalVertexSet] at hvLocal
  rcases Finset.mem_union.mp hvLocal with hvBase | hvHair
  · let coord :=
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i y
    let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
    let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
    let q : Q.Index := Q.indexOfSource ⟨(M.path coord).target, M.target_mem coord⟩
    have hend : (Q.path q).IsEndpoint v := by
      change v ∈ (Q.path q).vertexSet at hvStitch
      exact selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_next
        Hsys hcrossbars hlen i hnext q hvStitch (by simpa [j] using hvBase)
    rcases hend with hsource | htarget
    · have hsrc :=
        selectedOddLocalCrossbarGridTransportedStitchPath_source
          Hsys hcrossbars hlen i hnext y
      change (Q.path q).source =
        (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen i y).target at hsrc
      have hcurLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
        exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
          Hsys hcrossbars hlen i y
          (by
            rw [hsource, hsrc]
            exact GraphPath.target_mem_vertexSet
              (selectedOddLocalCrossbarGridTransportedMainPath
                Hsys hcrossbars hlen i y))
      have hnextLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
        rw [HairyPathOfSetsSystem.hairLocalVertexSet]
        exact Finset.mem_union_left _ hvBase
      have hindex_ne : i ≠ j := by
        intro h
        have hval := congrArg Fin.val h
        simp [j] at hval
      exact Finset.disjoint_left.mp
        (Hsys.hairLocalVertexSet_disjoint_of_ne
          (oddClusterIndex_ne_of_ne hlen hindex_ne))
        hcurLocal hnextLocal
    · have htgt :=
        selectedOddLocalCrossbarGridTransportedNextMainPath_source
          Hsys hcrossbars hlen i hnext y
      change
        (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen j y).source = (Q.path q).target at htgt
      have hvMainY :
          v ∈ (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j y).vertexSet := by
        rw [htarget, ← htgt]
        exact GraphPath.source_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j y)
      exact Finset.disjoint_left.mp
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_mainPath_of_grid_ne
          Hsys hcrossbars hlen j j hxy)
        (by simpa [j] using hvSpoke) hvMainY
  · have hvRegion :=
      selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
        Hsys hcrossbars hlen i hnext y hvStitch
    rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (Hsys.hairConnector_disjoint_baseConnectors
            (oddClusterIndex hlen j) (oddClusterIndex hlen i)
            (oddClusterIndex_gap hlen i)))
        hvHair hvFirst
    · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
      · exact Finset.disjoint_left.mp
          (Hsys.hairConnector_vertexSet_disjoint_baseCluster_of_ne
            (by
              have hne := oddClusterIndex_ne_middleClusterIndex hlen j i
              simpa using hne))
          hvHair hvMiddle
      · exact Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.hairConnector_disjoint_baseConnectors
              (oddClusterIndex hlen j) (middleClusterIndex hlen i)
              (middleClusterIndex_gap hlen hnext)))
          hvHair hvSecond

/-- A transported spoke in the current endpoint cluster of its own coordinate
stitch can meet that stitch only at the transported attachment. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_mem_currentStitchPath_eq_attachment
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) {v : V}
    (hvSpoke :
      v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet)
    (hvStitch :
      v ∈ (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext x).vertexSet) :
    v = selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x := by
  classical
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) :=
    selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen i x hvSpoke
  rw [HairyPathOfSetsSystem.hairLocalVertexSet] at hvLocal
  rcases Finset.mem_union.mp hvLocal with hvBase | hvHair
  · let coord :=
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x
    let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
    let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
    let q : Q.Index := Q.indexOfSource ⟨(M.path coord).target, M.target_mem coord⟩
    have hend : (Q.path q).IsEndpoint v := by
      change v ∈ (Q.path q).vertexSet at hvStitch
      exact selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_current
        Hsys hcrossbars hlen i hnext q hvStitch hvBase
    rcases hend with hsource | htarget
    · have hvMain :
          v ∈ (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i x).vertexSet := by
        have hsrc :=
          selectedOddLocalCrossbarGridTransportedStitchPath_source
            Hsys hcrossbars hlen i hnext x
        change (Q.path q).source =
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i x).target at hsrc
        rw [hsource, hsrc]
        exact GraphPath.target_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen i x)
      exact GraphPath.eq_of_mem_of_meetsExactlyAt
        (selectedOddLocalCrossbarGridTransportedAttachment_meetsExactly
          Hsys hcrossbars hlen i x) hvMain hvSpoke
    · have hnextMainSource :
          v =
            (selectedOddLocalCrossbarGridTransportedMainPath
              Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x).source := by
        have htgt :=
          selectedOddLocalCrossbarGridTransportedNextMainPath_source
            Hsys hcrossbars hlen i hnext x
        change
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x).source =
              (Q.path q).target at htgt
        exact htarget.trans htgt.symm
      have hcurLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
        rw [HairyPathOfSetsSystem.hairLocalVertexSet]
        exact Finset.mem_union_left _ hvBase
      have hnextLocal :
          v ∈ Hsys.hairLocalVertexSet
              (oddClusterIndex hlen ⟨i.1 + 1, hnext⟩) := by
        exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
          Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x
          (by
            rw [hnextMainSource]
            exact GraphPath.source_mem_vertexSet
              (selectedOddLocalCrossbarGridTransportedMainPath
                Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x))
      have hindex_ne : i ≠ ⟨i.1 + 1, hnext⟩ := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
      exact False.elim
        (Finset.disjoint_left.mp
          (Hsys.hairLocalVertexSet_disjoint_of_ne
            (oddClusterIndex_ne_of_ne hlen hindex_ne))
          hcurLocal hnextLocal)
  · have hvRegion :=
      selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
        Hsys hcrossbars hlen i hnext x hvStitch
    rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
    · exact False.elim
        (Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.hairConnector_disjoint_baseConnectors
              (oddClusterIndex hlen i) (oddClusterIndex hlen i)
              (oddClusterIndex_gap hlen i)))
          hvHair hvFirst)
    · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
      · exact False.elim
          (Finset.disjoint_left.mp
            (Hsys.hairConnector_vertexSet_disjoint_baseCluster_of_ne
              (oddClusterIndex_ne_middleClusterIndex hlen i i))
            hvHair hvMiddle)
      · exact False.elim
          (Finset.disjoint_left.mp
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (Hsys.hairConnector_disjoint_baseConnectors
                (oddClusterIndex hlen i) (middleClusterIndex hlen i)
                (middleClusterIndex_gap hlen hnext)))
            hvHair hvSecond)

/-- A transported spoke in the next endpoint cluster of its own coordinate
stitch can meet that stitch only at the transported attachment. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_mem_nextStitchPath_eq_attachment
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (x : GridVertex g) {v : V}
    (hvSpoke :
      v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x).vertexSet)
    (hvStitch :
      v ∈ (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext x).vertexSet) :
    v =
      selectedOddLocalCrossbarGridTransportedAttachment
        Hsys hcrossbars hlen ⟨i.1 + 1, hnext⟩ x := by
  classical
  let j : Fin m := ⟨i.1 + 1, hnext⟩
  have hvLocal :
      v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
    exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen j x (by simpa [j] using hvSpoke)
  rw [HairyPathOfSetsSystem.hairLocalVertexSet] at hvLocal
  rcases Finset.mem_union.mp hvLocal with hvBase | hvHair
  · let coord :=
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x
    let M := selectedOddLocalCrossbarGridMainPerfectPacking Hsys hcrossbars hlen i
    let Q := selectedOddLocalCrossbarGridConcatPacking Hsys hcrossbars hlen i hnext
    let q : Q.Index := Q.indexOfSource ⟨(M.path coord).target, M.target_mem coord⟩
    have hend : (Q.path q).IsEndpoint v := by
      change v ∈ (Q.path q).vertexSet at hvStitch
      exact selectedOddLocalCrossbarGridConcatPacking_internallyDisjoint_next
        Hsys hcrossbars hlen i hnext q hvStitch (by simpa [j] using hvBase)
    rcases hend with hsource | htarget
    · have hsrc :=
        selectedOddLocalCrossbarGridTransportedStitchPath_source
          Hsys hcrossbars hlen i hnext x
      change (Q.path q).source =
        (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen i x).target at hsrc
      have hcurLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen i) := by
        exact selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_localVertexSet
          Hsys hcrossbars hlen i x
          (by
            rw [hsource, hsrc]
            exact GraphPath.target_mem_vertexSet
              (selectedOddLocalCrossbarGridTransportedMainPath
                Hsys hcrossbars hlen i x))
      have hnextLocal :
          v ∈ Hsys.hairLocalVertexSet (oddClusterIndex hlen j) := by
        rw [HairyPathOfSetsSystem.hairLocalVertexSet]
        exact Finset.mem_union_left _ hvBase
      have hindex_ne : i ≠ j := by
        intro h
        have hval := congrArg Fin.val h
        simp [j] at hval
      exact False.elim
        (Finset.disjoint_left.mp
          (Hsys.hairLocalVertexSet_disjoint_of_ne
            (oddClusterIndex_ne_of_ne hlen hindex_ne))
          hcurLocal hnextLocal)
    · have htgt :=
        selectedOddLocalCrossbarGridTransportedNextMainPath_source
          Hsys hcrossbars hlen i hnext x
      change
        (selectedOddLocalCrossbarGridTransportedMainPath
          Hsys hcrossbars hlen j x).source = (Q.path q).target at htgt
      have hvMain :
          v ∈ (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j x).vertexSet := by
        rw [htarget, ← htgt]
        exact GraphPath.source_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedMainPath
            Hsys hcrossbars hlen j x)
      have hvSpoke' :
          v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
            Hsys hcrossbars hlen j x).vertexSet := by
        simpa [j] using hvSpoke
      have h :=
        GraphPath.eq_of_mem_of_meetsExactlyAt
          (selectedOddLocalCrossbarGridTransportedAttachment_meetsExactly
            Hsys hcrossbars hlen j x) hvMain hvSpoke'
      simpa [j] using h
  · have hvRegion :=
      selectedOddLocalCrossbarGridTransportedStitchPath_staysIn
        Hsys hcrossbars hlen i hnext x hvStitch
    rcases Finset.mem_union.mp hvRegion with hvFirst | hvRest
    · exact False.elim
        (Finset.disjoint_left.mp
          (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
            (Hsys.hairConnector_disjoint_baseConnectors
              (oddClusterIndex hlen j) (oddClusterIndex hlen i)
              (oddClusterIndex_gap hlen i)))
          hvHair hvFirst)
    · rcases Finset.mem_union.mp hvRest with hvMiddle | hvSecond
      · exact False.elim
          (Finset.disjoint_left.mp
            (Hsys.hairConnector_vertexSet_disjoint_baseCluster_of_ne
              (by
                have hne := oddClusterIndex_ne_middleClusterIndex hlen j i
                simpa using hne))
            hvHair hvMiddle)
      · exact False.elim
          (Finset.disjoint_left.mp
            (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
              (Hsys.hairConnector_disjoint_baseConnectors
                (oddClusterIndex hlen j) (middleClusterIndex hlen i)
                (middleClusterIndex_gap hlen hnext)))
            hvHair hvSecond)

/-- A transported spoke path and an arbitrary transported stitch path are
disjoint for distinct grid coordinates. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_stitchPath_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) (hnext : j.1 + 1 < m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen j hnext y).vertexSet := by
  by_cases hij : i = j
  · subst i
    exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_currentStitchPath
      Hsys hcrossbars hlen j hnext hxy
  · by_cases hinext : i = ⟨j.1 + 1, hnext⟩
    · subst i
      exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_nextStitchPath
        Hsys hcrossbars hlen j hnext hxy
    · exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_stitchPath
        Hsys hcrossbars hlen hnext hij hinext x y

/-- Symmetric form of
`selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_stitchPath_of_grid_ne`. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint_spokePath_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (j : Fin m) {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext x).vertexSet
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen j y).vertexSet := by
  exact (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_stitchPath_of_grid_ne
    Hsys hcrossbars hlen j i hnext hxy.symm).symm

/-- A transported stitch path and an arbitrary transported main path are disjoint
for distinct grid coordinates. -/
theorem selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint_mainPath_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (hnext : i.1 + 1 < m)
    (j : Fin m) {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedStitchPath
        Hsys hcrossbars hlen i hnext x).vertexSet
      (selectedOddLocalCrossbarGridTransportedMainPath
        Hsys hcrossbars hlen j y).vertexSet := by
  exact (selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_stitchPath_of_grid_ne
    Hsys hcrossbars hlen j i hnext hxy.symm).symm

/-- To prove two full transported row traces with distinct grid coordinates are
disjoint, it remains only to control the stitch-stitch interactions.  Main-main
and main-stitch interactions are supplied by the local crossbar and endpoint
separation lemmas above. -/
theorem selectedOddLocalCrossbarGridRowTrace_disjoint_of_stitch_stitch_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {x y : GridVertex g} (hxy : x ≠ y)
    (stitch_stitch :
      ∀ ih jh : {i : Fin m // i.1 + 1 < m},
        Disjoint
          (selectedOddLocalCrossbarGridTransportedStitchPath
            Hsys hcrossbars hlen ih.1 ih.2 x).vertexSet
          (selectedOddLocalCrossbarGridTransportedStitchPath
            Hsys hcrossbars hlen jh.1 jh.2 y).vertexSet) :
    Disjoint
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  exact selectedOddLocalCrossbarGridRowTrace_disjoint_of_piecewise_disjoint
    Hsys hcrossbars hlen
    (fun i j =>
      selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_of_grid_ne
        Hsys hcrossbars hlen i j hxy)
    (fun i jh =>
      selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_stitchPath_of_grid_ne
        Hsys hcrossbars hlen i jh.1 jh.2 hxy)
    (fun ih j =>
      selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint_mainPath_of_grid_ne
        Hsys hcrossbars hlen ih.1 ih.2 j hxy)
    stitch_stitch

/-- Full transported row traces for distinct grid coordinates are disjoint.  This
is the row-support separation needed for the branch-set minor model. -/
theorem selectedOddLocalCrossbarGridRowTrace_disjoint_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  exact selectedOddLocalCrossbarGridRowTrace_disjoint_of_stitch_stitch_disjoint
    Hsys hcrossbars hlen hxy
    (fun ih jh =>
      selectedOddLocalCrossbarGridTransportedStitchPath_vertexSet_disjoint_of_grid_ne
        Hsys hcrossbars hlen ih jh hxy)

/-- A transported spoke path for coordinate `x` is disjoint from the full row
trace of every distinct coordinate `y`. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_rowTrace_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  rw [Finset.disjoint_left]
  intro v hvSpoke hvRow
  rw [mem_selectedOddLocalCrossbarGridRowTrace_iff Hsys hcrossbars hlen y v] at hvRow
  rcases hvRow with ⟨j, hvMain⟩ | ⟨jh, hvStitch⟩
  · exact Finset.disjoint_left.mp
      (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_mainPath_of_grid_ne
        Hsys hcrossbars hlen i j hxy)
      hvSpoke hvMain
  · exact Finset.disjoint_left.mp
      (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_stitchPath_of_grid_ne
        Hsys hcrossbars hlen i jh.1 jh.2 hxy)
      hvSpoke hvStitch

/-- A transported spoke can meet its own full transported row trace only at its
row attachment.  Nonincident pieces are separated by selected-cluster
disjointness; the two incident stitch pieces meet the local footprint only at
their endpoints, and the endpoint on the spoke's main path is forced to be the
attachment by exactness of the spoke-main intersection. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_mem_rowTrace_eq_attachment
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) {v : V}
    (hvSpoke :
      v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet)
    (hvRow :
      v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x) :
    v = selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x := by
  classical
  rw [mem_selectedOddLocalCrossbarGridRowTrace_iff Hsys hcrossbars hlen x v] at hvRow
  rcases hvRow with ⟨j, hvMain⟩ | ⟨jh, hvStitch⟩
  · by_cases hji : j = i
    · subst j
      exact GraphPath.eq_of_mem_of_meetsExactlyAt
        (selectedOddLocalCrossbarGridTransportedAttachment_meetsExactly
          Hsys hcrossbars hlen i x) hvMain hvSpoke
    · exact False.elim
        (Finset.disjoint_left.mp
          ((selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_disjoint_spokePath_of_ne
            Hsys hcrossbars hlen hji x x).symm)
          hvSpoke hvMain)
  · by_cases hcur : i = jh.1
    · subst i
      exact selectedOddLocalCrossbarGridTransportedSpokePath_mem_currentStitchPath_eq_attachment
        Hsys hcrossbars hlen jh.1 jh.2 x hvSpoke hvStitch
    · by_cases hnext : i = ⟨jh.1.1 + 1, jh.2⟩
      · subst i
        exact selectedOddLocalCrossbarGridTransportedSpokePath_mem_nextStitchPath_eq_attachment
          Hsys hcrossbars hlen jh.1 jh.2 x hvSpoke hvStitch
      · exact False.elim
          (Finset.disjoint_left.mp
            (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_stitchPath
              Hsys hcrossbars hlen jh.2 hcur hnext x x)
            hvSpoke hvStitch)

/-- Symmetric form of
`selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_rowTrace_of_grid_ne`. -/
theorem selectedOddLocalCrossbarGridRowTrace_disjoint_spokePath_vertexSet_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i y).vertexSet := by
  exact (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_rowTrace_of_grid_ne
    Hsys hcrossbars hlen i hxy.symm).symm

/-- Transported attachments are injective as a function of the initial
coordinate. -/
theorem selectedOddLocalCrossbarGridTransportedAttachment_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Function.Injective
      (selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i) := by
  intro x y hxy
  have hcoord :
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x =
        selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i y :=
    selectedOddLocalCrossbarGridAttachment_injective Hsys hcrossbars hlen i hxy
  exact (selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i).injective hcoord

/-- Transported hair endpoints are injective as a function of the initial
coordinate. -/
theorem selectedOddLocalCrossbarGridTransportedHairEndpoint_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Function.Injective
      (selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i) := by
  intro x y hxy
  have hcoord :
      selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x =
        selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i y :=
    selectedOddLocalCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i hxy
  exact (selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i).injective hcoord

/-- Transported spokes for distinct initial coordinates remain node-disjoint
inside a fixed selected odd local crossbar. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_nodeDisjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    GraphPath.NodeDisjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x)
      (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i y) := by
  let e := selectedOddLocalCrossbarGridCoordTransport Hsys hcrossbars hlen i
  have hcoord : e x ≠ e y := by
    intro h
    exact hxy (e.injective h)
  simpa [selectedOddLocalCrossbarGridTransportedSpokePath,
    selectedOddLocalCrossbarGridTransportedCoord, GraphPath.NodeDisjoint,
    e] using
    selectedOddLocalCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen i hcoord

/-- Transported spoke paths for distinct grid coordinates are disjoint, whether
they lie in the same selected odd cluster or in different selected odd
clusters. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_grid_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x).vertexSet
      (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen j y).vertexSet := by
  by_cases hij : i = j
  · subst j
    simpa [GraphPath.NodeDisjoint] using
      selectedOddLocalCrossbarGridTransportedSpokePath_nodeDisjoint
        Hsys hcrossbars hlen i hxy
  · exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_ne
      Hsys hcrossbars hlen hij x y

/-- Attachment vertices selected by a transported coordinate set. -/
noncomputable def selectedOddLocalCrossbarGridTransportedAttachmentImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  selectedOddLocalCrossbarGridAttachmentImage Hsys hcrossbars hlen i
    (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U)

/-- Hair endpoints selected by a transported coordinate set. -/
noncomputable def selectedOddLocalCrossbarGridTransportedHairEndpointImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  selectedOddLocalCrossbarGridHairEndpointImage Hsys hcrossbars hlen i
    (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U)

@[simp] theorem selectedOddLocalCrossbarGridTransportedAttachmentImage_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i U).card =
      U.card := by
  simp [selectedOddLocalCrossbarGridTransportedAttachmentImage]

@[simp] theorem selectedOddLocalCrossbarGridTransportedHairEndpointImage_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U).card =
      U.card := by
  simp [selectedOddLocalCrossbarGridTransportedHairEndpointImage]

/-- The transported attachment image is the pointwise image of the transported
attachment map. -/
theorem selectedOddLocalCrossbarGridTransportedAttachmentImage_eq_image
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i U =
      U.image (selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i) := by
  ext v
  constructor
  · intro hv
    rw [selectedOddLocalCrossbarGridTransportedAttachmentImage,
      selectedOddLocalCrossbarGridAttachmentImage,
      selectedOddLocalCrossbarGridTransportedCoordImage] at hv
    rcases Finset.mem_image.mp hv with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
    rw [selectedOddLocalCrossbarGridTransportedAttachmentImage,
      selectedOddLocalCrossbarGridAttachmentImage,
      selectedOddLocalCrossbarGridTransportedCoordImage]
    exact Finset.mem_image.mpr
      ⟨selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- The transported hair-endpoint image is the pointwise image of the
transported hair-endpoint map. -/
theorem selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U =
      U.image (selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i) := by
  ext v
  constructor
  · intro hv
    rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage,
      selectedOddLocalCrossbarGridHairEndpointImage,
      selectedOddLocalCrossbarGridTransportedCoordImage] at hv
    rcases Finset.mem_image.mp hv with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
    rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage,
      selectedOddLocalCrossbarGridHairEndpointImage,
      selectedOddLocalCrossbarGridTransportedCoordImage]
    exact Finset.mem_image.mpr
      ⟨selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- Membership in a transported hair-endpoint image is witnessed by a unique
initial coordinate from the source coordinate set. -/
theorem exists_selectedOddLocalCrossbarGridCoord_of_mem_transportedHairEndpointImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) {v : V}
    (hv : v ∈ selectedOddLocalCrossbarGridTransportedHairEndpointImage
      Hsys hcrossbars hlen i U) :
    ∃ x : GridVertex g,
      x ∈ U ∧
        selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x = v := by
  rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image] at hv
  exact Finset.mem_image.mp hv

/-- Recover the initial coordinate whose transported hair endpoint is `v`. -/
noncomputable def selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) (v : V)
    (hv : v ∈ selectedOddLocalCrossbarGridTransportedHairEndpointImage
      Hsys hcrossbars hlen i U) : GridVertex g :=
  Classical.choose
    (exists_selectedOddLocalCrossbarGridCoord_of_mem_transportedHairEndpointImage
      Hsys hcrossbars hlen i U hv)

/-- The recovered coordinate belongs to the coordinate set whose transported
hair-endpoint image contained `v`. -/
theorem selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) (v : V)
    (hv : v ∈ selectedOddLocalCrossbarGridTransportedHairEndpointImage
      Hsys hcrossbars hlen i U) :
    selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint
      Hsys hcrossbars hlen i U v hv ∈ U :=
  (Classical.choose_spec
    (exists_selectedOddLocalCrossbarGridCoord_of_mem_transportedHairEndpointImage
      Hsys hcrossbars hlen i U hv)).1

/-- The transported hair endpoint of the recovered coordinate is the original
vertex. -/
theorem selectedOddLocalCrossbarGridTransportedHairEndpoint_coordOf
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) (v : V)
    (hv : v ∈ selectedOddLocalCrossbarGridTransportedHairEndpointImage
      Hsys hcrossbars hlen i U) :
    selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
        (selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint
          Hsys hcrossbars hlen i U v hv) =
      v :=
  (Classical.choose_spec
    (exists_selectedOddLocalCrossbarGridCoord_of_mem_transportedHairEndpointImage
      Hsys hcrossbars hlen i U hv)).2

/-- The union of transported spoke vertices selected by an initial coordinate
set `U` in cluster `i`. -/
noncomputable def selectedOddLocalCrossbarGridTransportedSpokeTraceImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i
    (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U)

/-- A transported spoke whose initial coordinate lies in `U` is contained in
the transported spoke trace of `U`. -/
theorem selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_trace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U : Finset (GridVertex g)} {x : GridVertex g} (hx : x ∈ U) :
    (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x).vertexSet ⊆
      selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U := by
  rw [selectedOddLocalCrossbarGridTransportedSpokeTraceImage,
    selectedOddLocalCrossbarGridTransportedSpokePath]
  exact selectedOddLocalCrossbarGridOrientedSpokePath_vertexSet_subset_trace
    Hsys hcrossbars hlen i (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- Disjoint initial coordinate sets select disjoint transported spoke traces
inside a fixed selected odd local crossbar. -/
theorem selectedOddLocalCrossbarGridTransportedSpokeTraceImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i W) := by
  rw [selectedOddLocalCrossbarGridTransportedSpokeTraceImage,
    selectedOddLocalCrossbarGridTransportedSpokeTraceImage]
  exact selectedOddLocalCrossbarGridSpokeTraceImage_disjoint Hsys hcrossbars hlen i
    (selectedOddLocalCrossbarGridTransportedCoordImage_disjoint Hsys hcrossbars hlen i hUW)

/-- A transported spoke trace selected by a coordinate set `U` is disjoint from
the row trace of any coordinate outside `U`. -/
theorem selectedOddLocalCrossbarGridTransportedSpokeTraceImage_disjoint_rowTrace_of_not_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) {y : GridVertex g} (hy : y ∉ U) :
    Disjoint
      (selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  rw [Finset.disjoint_left]
  intro v hvTrace hvRow
  rw [selectedOddLocalCrossbarGridTransportedSpokeTraceImage,
    selectedOddLocalCrossbarGridSpokeTraceImage,
    selectedOddLocalCrossbarGridTransportedCoordImage] at hvTrace
  rcases Finset.mem_biUnion.mp hvTrace with ⟨z, hz, hvPath⟩
  rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
  have hxy : x ≠ y := by
    intro h
    exact hy (by simpa [h] using hx)
  change v ∈
    (selectedOddLocalCrossbarGridTransportedSpokePath
      Hsys hcrossbars hlen i x).vertexSet at hvPath
  exact Finset.disjoint_left.mp
    (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_rowTrace_of_grid_ne
      Hsys hcrossbars hlen i hxy)
    hvPath hvRow

/-- Symmetric form of
`selectedOddLocalCrossbarGridTransportedSpokeTraceImage_disjoint_rowTrace_of_not_mem`. -/
theorem selectedOddLocalCrossbarGridRowTrace_disjoint_transportedSpokeTraceImage_of_not_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) {y : GridVertex g} (hy : y ∉ U) :
    Disjoint
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y)
      (selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U) := by
  exact (selectedOddLocalCrossbarGridTransportedSpokeTraceImage_disjoint_rowTrace_of_not_mem
    Hsys hcrossbars hlen i U hy).symm

/-- A transported attachment lies on the transported main path with the same
initial coordinate. -/
theorem selectedOddLocalCrossbarGridTransportedAttachment_mem_mainPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x ∈
      (selectedOddLocalCrossbarGridTransportedMainPath Hsys hcrossbars hlen i x).vertexSet := by
  simpa [selectedOddLocalCrossbarGridTransportedAttachment,
    selectedOddLocalCrossbarGridTransportedMainPath,
    selectedOddLocalCrossbarGridMainPerfectPacking,
    selectedOddLocalCrossbarGridMainPath,
    PathPacking.toPerfectUsedTerminals] using
    selectedOddLocalCrossbarGridAttachment_mem_main Hsys hcrossbars hlen i
      (selectedOddLocalCrossbarGridTransportedCoord Hsys hcrossbars hlen i x)

/-- A transported attachment lies in the row trace of the same initial
coordinate. -/
theorem selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x ∈
      selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x :=
  selectedOddLocalCrossbarGridTransportedMainPath_vertexSet_subset_rowTrace
    Hsys hcrossbars hlen x i
    (selectedOddLocalCrossbarGridTransportedAttachment_mem_mainPath
      Hsys hcrossbars hlen i x)

/-- Transported attachment images are contained in the union of the
corresponding row traces. -/
theorem selectedOddLocalCrossbarGridTransportedAttachmentImage_subset_rowTraceImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i U ⊆
      U.biUnion fun x => selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x := by
  intro v hv
  rw [selectedOddLocalCrossbarGridTransportedAttachmentImage_eq_image] at hv
  rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
  exact Finset.mem_biUnion.mpr
    ⟨x, hx, selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
      Hsys hcrossbars hlen i x⟩

/-- Transported hair-endpoint images are contained in the transported spoke
trace of the same initial coordinate set. -/
theorem selectedOddLocalCrossbarGridTransportedHairEndpointImage_subset_spokeTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U ⊆
      selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U := by
  intro v hv
  rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image] at hv
  rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
  exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_trace
    Hsys hcrossbars hlen i hx
    (by
      simpa using
        GraphPath.target_mem_vertexSet
          (selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x))

/-- Transported selected spokes indexed by an initial coordinate set.  Unlike
the concrete subpacking on the transported coordinate image, this keeps the
index type `{x // x in U}`, which is the form needed by the cut-matching
minor model. -/
noncomputable def selectedOddLocalCrossbarGridTransportedSpokeSubpacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U) where
  toPathPacking := {
    Index := {x : GridVertex g // x ∈ U}
    path := fun x =>
      selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x.1
    connects := by
      intro x
      refine Or.inl ⟨?_, ?_⟩
      · rw [selectedOddLocalCrossbarGridTransportedAttachmentImage_eq_image]
        exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
      · rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image]
        exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
    node_disjoint := by
      intro x y hxy
      exact selectedOddLocalCrossbarGridTransportedSpokePath_nodeDisjoint
        Hsys hcrossbars hlen i (fun h => hxy (Subtype.ext h))
  }
  source_mem := by
    intro x
    rw [selectedOddLocalCrossbarGridTransportedAttachmentImage_eq_image]
    exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
  target_mem := by
    intro x
    rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image]
    exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
  source_bijective := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply selectedOddLocalCrossbarGridTransportedAttachment_injective Hsys hcrossbars hlen i
      have hval := congrArg Subtype.val hxy
      simpa using hval
    · intro v
      rcases v with ⟨v, hv⟩
      rw [selectedOddLocalCrossbarGridTransportedAttachmentImage_eq_image] at hv
      rcases Finset.mem_image.mp hv with ⟨x, hx, hxv⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simp [hxv]
  target_bijective := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply selectedOddLocalCrossbarGridTransportedHairEndpoint_injective Hsys hcrossbars hlen i
      have hval := congrArg Subtype.val hxy
      simpa using hval
    · intro v
      rcases v with ⟨v, hv⟩
      rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image] at hv
      rcases Finset.mem_image.mp hv with ⟨x, hx, hxv⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simp [hxv]

@[simp] theorem selectedOddLocalCrossbarGridTransportedSpokeSubpacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridTransportedSpokeSubpacking Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddLocalCrossbarGridTransportedSpokeSubpacking,
    PerfectPathPacking.card, Fintype.card_coe]

/-- Every transported spoke subpacking stays inside its transported spoke
trace. -/
theorem selectedOddLocalCrossbarGridTransportedSpokeSubpacking_staysIn_trace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddLocalCrossbarGridTransportedSpokeSubpacking
      Hsys hcrossbars hlen i U).toPathPacking.StaysIn
      (selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U) := by
  intro x
  exact selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_trace
    Hsys hcrossbars hlen i x.2

/-- Every path in a transported spoke subpacking uses only local hair-graph
edges. -/
theorem selectedOddLocalCrossbarGridTransportedSpokeSubpacking_path_edgeSet_subset_hairLocalGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g))
    (x : (selectedOddLocalCrossbarGridTransportedSpokeSubpacking
      Hsys hcrossbars hlen i U).Index) :
    ↑((selectedOddLocalCrossbarGridTransportedSpokeSubpacking
      Hsys hcrossbars hlen i U).path x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet :=
  selectedOddLocalCrossbarGridTransportedSpokePath_edgeSet_subset_hairLocalGraph
    Hsys hcrossbars hlen i x.1

/-- A transported cut-matching round through one selected odd local crossbar.
The left and right packings run along the selected spokes, while the middle
packing runs through the hair cluster.  The endpoint sets are expressed in the
initial grid-coordinate system and transported internally. -/
structure SelectedOddLocalCrossbarGridTransportedMatchingRound
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U W : Finset (GridVertex g)) where
  /-- The spoke-side packing from row attachments into the hair endpoints for
  the left side of the cut. -/
  left :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U)
  /-- The well-linked packing inside the hair cluster across the cut. -/
  middle :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U)
      (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i W)
  /-- The spoke-side packing from the right-side hair endpoints back to their
  row attachments. -/
  right :
    PerfectPathPacking G
      (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i W)
      (selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i W)
  left_card : left.card = U.card
  middle_card : middle.card = U.card
  right_card : right.card = W.card
  left_staysIn :
    left.toPathPacking.StaysIn
      (selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U)
  right_staysIn :
    right.toPathPacking.StaysIn
      (selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i W)
  middle_staysIn :
    middle.toPathPacking.StaysIn
      (Hsys.hairCluster (oddClusterIndex hlen i))
  left_edgeLocal :
    ∀ x : left.Index, ↑(left.path x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet
  right_edgeLocal :
    ∀ x : right.Index, ↑(right.path x).edgeSet ⊆
      (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet

/-- Initial-coordinate-indexed construction of a transported matching round.
The two spoke sides are the canonical transported spoke subpackings, so their
indices are the original coordinates on the two sides of the cut. -/
theorem exists_selectedOddLocalCrossbarGridTransportedMatchingRound_initialIndexed
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    Nonempty
      (SelectedOddLocalCrossbarGridTransportedMatchingRound
        Hsys hcrossbars hlen i U W) := by
  let U' := selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U
  let W' := selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i W
  have hUW' : Disjoint U' W' := by
    simpa [U', W'] using
      selectedOddLocalCrossbarGridTransportedCoordImage_disjoint
        Hsys hcrossbars hlen i hUW
  have hcard' : U'.card = W'.card := by
    simp [U', W', hcard]
  rcases selectedOddLocalCrossbarGridHairEndpointImage_perfectLinkage
      Hsys hcrossbars hlen i hUW' hcard' with
    ⟨M, hMcard, hMstay⟩
  let L := selectedOddLocalCrossbarGridTransportedSpokeSubpacking
    Hsys hcrossbars hlen i U
  let R0 := selectedOddLocalCrossbarGridTransportedSpokeSubpacking
    Hsys hcrossbars hlen i W
  exact ⟨{
    left := L
    middle := M
    right := R0.reverse
    left_card := by
      simp [L]
    middle_card := by
      simpa [U'] using hMcard
    right_card := by
      simp [R0]
    left_staysIn := by
      exact selectedOddLocalCrossbarGridTransportedSpokeSubpacking_staysIn_trace
        Hsys hcrossbars hlen i U
    right_staysIn := by
      exact PerfectPathPacking.reverse_staysIn R0
        (selectedOddLocalCrossbarGridTransportedSpokeSubpacking_staysIn_trace
          Hsys hcrossbars hlen i W)
    middle_staysIn := hMstay
    left_edgeLocal := by
      intro x
      exact selectedOddLocalCrossbarGridTransportedSpokeSubpacking_path_edgeSet_subset_hairLocalGraph
        Hsys hcrossbars hlen i U x
    right_edgeLocal := by
      intro x
      rw [PerfectPathPacking.reverse_path_edgeSet]
      exact selectedOddLocalCrossbarGridTransportedSpokeSubpacking_path_edgeSet_subset_hairLocalGraph
        Hsys hcrossbars hlen i W x }⟩

/-- A cut-matching round at a selected odd cluster can be addressed in the
initial coordinate system: coordinate subsets are transported before invoking
the local crossbar matching machinery. -/
theorem exists_selectedOddLocalCrossbarGridTransportedMatchingPieces_edgeLocal
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ L : PerfectPathPacking G
        (selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i U)
        (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U),
      ∃ M : PerfectPathPacking G
          (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i U)
          (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i W),
        ∃ R : PerfectPathPacking G
            (selectedOddLocalCrossbarGridTransportedHairEndpointImage Hsys hcrossbars hlen i W)
            (selectedOddLocalCrossbarGridTransportedAttachmentImage Hsys hcrossbars hlen i W),
          L.card = U.card ∧
            M.card = U.card ∧
              R.card = W.card ∧
                L.toPathPacking.StaysIn
                  (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i
                    (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U)) ∧
                  R.toPathPacking.StaysIn
                    (selectedOddLocalCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i
                      (selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i W)) ∧
                    M.toPathPacking.StaysIn
                      (Hsys.hairCluster (oddClusterIndex hlen i)) ∧
                      (∀ x : L.Index, ↑(L.path x).edgeSet ⊆
                        (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet) ∧
                        (∀ x : R.Index, ↑(R.path x).edgeSet ⊆
                          (Hsys.hairLocalGraph (oddClusterIndex hlen i)).edgeSet) := by
  let U' := selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i U
  let W' := selectedOddLocalCrossbarGridTransportedCoordImage Hsys hcrossbars hlen i W
  have hUW' : Disjoint U' W' := by
    simpa [U', W'] using
      selectedOddLocalCrossbarGridTransportedCoordImage_disjoint
        Hsys hcrossbars hlen i hUW
  have hcard' : U'.card = W'.card := by
    simp [U', W', hcard]
  rcases exists_selectedOddLocalCrossbarGridConcreteMatchingPieces_edgeLocal
      Hsys hcrossbars hlen i hUW' hcard' with
    ⟨L, M, R, hLcard, hMcard, hRcard, hLstay, hRstay, hMstay,
      hLedge, hRedge⟩
  refine ⟨L, M, R, ?_, ?_, ?_, ?_, ?_, hMstay, hLedge, hRedge⟩
  · simpa [U'] using hLcard
  · simpa [U'] using hMcard
  · simpa [W'] using hRcard
  · simpa [selectedOddLocalCrossbarGridTransportedAttachmentImage,
      selectedOddLocalCrossbarGridTransportedHairEndpointImage, U'] using hLstay
  · simpa [selectedOddLocalCrossbarGridTransportedAttachmentImage,
      selectedOddLocalCrossbarGridTransportedHairEndpointImage, W'] using hRstay

/-- The transported cut-matching round exists whenever the two sides of the
cut are disjoint coordinate sets of equal cardinality. -/
theorem exists_selectedOddLocalCrossbarGridTransportedMatchingRound
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    Nonempty
      (SelectedOddLocalCrossbarGridTransportedMatchingRound
        Hsys hcrossbars hlen i U W) := by
  rcases exists_selectedOddLocalCrossbarGridTransportedMatchingPieces_edgeLocal
      Hsys hcrossbars hlen i hUW hcard with
    ⟨L, M, R, hLcard, hMcard, hRcard, hLstay, hRstay, hMstay,
      hLedge, hRedge⟩
  exact ⟨{
    left := L
    middle := M
    right := R
    left_card := hLcard
    middle_card := hMcard
    right_card := hRcard
    left_staysIn := by
      simpa [selectedOddLocalCrossbarGridTransportedSpokeTraceImage] using hLstay
    right_staysIn := by
      simpa [selectedOddLocalCrossbarGridTransportedSpokeTraceImage] using hRstay
    middle_staysIn := hMstay
    left_edgeLocal := hLedge
    right_edgeLocal := hRedge }⟩

/-- Choose a transported cut-matching round through one selected odd local
crossbar. -/
noncomputable def selectedOddLocalCrossbarGridTransportedMatchingRound
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
  SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W :=
  Classical.choice
    (exists_selectedOddLocalCrossbarGridTransportedMatchingRound_initialIndexed
      Hsys hcrossbars hlen i hUW hcard)

namespace SelectedOddLocalCrossbarGridTransportedMatchingRound

/-- The vertex support of the three packings in a transported matching round. -/
noncomputable def support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) : Finset V :=
  R.left.toPathPacking.vertexSet ∪
    (R.middle.toPathPacking.vertexSet ∪ R.right.toPathPacking.vertexSet)

/-- The support of a transported matching round lies in the two transported
spoke traces and the one hair cluster used by the middle linkage. -/
theorem support_subset_footprint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) :
    R.support ⊆
      selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U ∪
        (Hsys.hairCluster (oddClusterIndex hlen i) ∪
          selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i W) := by
  intro v hv
  rw [support] at hv
  rcases Finset.mem_union.mp hv with hvLeft | hvRest
  · exact Finset.mem_union_left _ <|
      PathPacking.vertexSet_subset_of_staysIn R.left_staysIn hvLeft
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvRight
    · exact Finset.mem_union_right _ <|
        Finset.mem_union_left _ <|
          PathPacking.vertexSet_subset_of_staysIn R.middle_staysIn hvMiddle
    · exact Finset.mem_union_right _ <|
        Finset.mem_union_right _ <|
          PathPacking.vertexSet_subset_of_staysIn R.right_staysIn hvRight

/-- Every left spoke path in a transported matching round is contained in the
round support. -/
theorem left_path_vertexSet_subset_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.left.Index) :
    (R.left.path a).vertexSet ⊆ R.support := by
  intro v hv
  rw [support]
  exact Finset.mem_union_left _ <|
    R.left.toPathPacking.path_vertexSet_subset_vertexSet a hv

/-- Every middle linkage path in a transported matching round is contained in
the round support. -/
theorem middle_path_vertexSet_subset_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.middle.Index) :
    (R.middle.path a).vertexSet ⊆ R.support := by
  intro v hv
  rw [support]
  exact Finset.mem_union_right _ <|
    Finset.mem_union_left _ <|
      R.middle.toPathPacking.path_vertexSet_subset_vertexSet a hv

/-- Every right spoke path in a transported matching round is contained in the
round support. -/
theorem right_path_vertexSet_subset_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.right.Index) :
    (R.right.path a).vertexSet ⊆ R.support := by
  intro v hv
  rw [support]
  exact Finset.mem_union_right _ <|
    Finset.mem_union_right _ <|
      R.right.toPathPacking.path_vertexSet_subset_vertexSet a hv

/-- The initial coordinate on the left side of the cut that corresponds to the
source endpoint of a middle-linkage path. -/
noncomputable def middleSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.middle.Index) : GridVertex g :=
  selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint Hsys hcrossbars hlen i
    U (R.middle.path a).source (R.middle.source_mem a)

/-- The initial coordinate on the right side of the cut that corresponds to the
target endpoint of a middle-linkage path. -/
noncomputable def middleTargetCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.middle.Index) : GridVertex g :=
  selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint Hsys hcrossbars hlen i
    W (R.middle.path a).target (R.middle.target_mem a)

/-- A middle source coordinate belongs to the left side of the cut. -/
theorem middleSourceCoord_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.middle.Index) :
    R.middleSourceCoord a ∈ U :=
  selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint_mem
    Hsys hcrossbars hlen i U (R.middle.path a).source (R.middle.source_mem a)

/-- A middle target coordinate belongs to the right side of the cut. -/
theorem middleTargetCoord_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.middle.Index) :
    R.middleTargetCoord a ∈ W :=
  selectedOddLocalCrossbarGridCoordOfTransportedHairEndpoint_mem
    Hsys hcrossbars hlen i W (R.middle.path a).target (R.middle.target_mem a)

/-- The middle path source is the transported hair endpoint of the recovered
left-side coordinate. -/
theorem transportedHairEndpoint_middleSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.middle.Index) :
    selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
        (R.middleSourceCoord a) =
      (R.middle.path a).source :=
  selectedOddLocalCrossbarGridTransportedHairEndpoint_coordOf
    Hsys hcrossbars hlen i U (R.middle.path a).source (R.middle.source_mem a)

/-- The middle path target is the transported hair endpoint of the recovered
right-side coordinate. -/
theorem transportedHairEndpoint_middleTargetCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) (a : R.middle.Index) :
    selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
        (R.middleTargetCoord a) =
      (R.middle.path a).target :=
  selectedOddLocalCrossbarGridTransportedHairEndpoint_coordOf
    Hsys hcrossbars hlen i W (R.middle.path a).target (R.middle.target_mem a)

/-- Distinct middle-linkage indices have distinct recovered left-side
coordinates. -/
theorem middleSourceCoord_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) :
    Function.Injective R.middleSourceCoord := by
  intro a b hab
  apply R.middle.source_bijective.1
  apply Subtype.ext
  calc
    (R.middle.path a).source =
        selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
          (R.middleSourceCoord a) := by
        exact (R.transportedHairEndpoint_middleSourceCoord a).symm
    _ = selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
          (R.middleSourceCoord b) := by rw [hab]
    _ = (R.middle.path b).source :=
        R.transportedHairEndpoint_middleSourceCoord b

/-- Distinct middle-linkage indices have distinct recovered right-side
coordinates. -/
theorem middleTargetCoord_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) :
    Function.Injective R.middleTargetCoord := by
  intro a b hab
  apply R.middle.target_bijective.1
  apply Subtype.ext
  calc
    (R.middle.path a).target =
        selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
          (R.middleTargetCoord a) := by
        exact (R.transportedHairEndpoint_middleTargetCoord a).symm
    _ = selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
          (R.middleTargetCoord b) := by rw [hab]
    _ = (R.middle.path b).target :=
        R.transportedHairEndpoint_middleTargetCoord b

/-- Every left-side coordinate of the cut occurs as the recovered source
coordinate of a middle-linkage path. -/
theorem exists_middleSourceCoord_eq
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) {x : GridVertex g} (hx : x ∈ U) :
    ∃ a : R.middle.Index, R.middleSourceCoord a = x := by
  have hv :
      selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x ∈
        selectedOddLocalCrossbarGridTransportedHairEndpointImage
          Hsys hcrossbars hlen i U := by
    rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rcases R.middle.source_bijective.2
      ⟨selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x,
        hv⟩ with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply selectedOddLocalCrossbarGridTransportedHairEndpoint_injective Hsys hcrossbars hlen i
  have hsource :
      (R.middle.path a).source =
        selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x :=
    congrArg Subtype.val ha
  rw [R.transportedHairEndpoint_middleSourceCoord a, hsource]

/-- Every right-side coordinate of the cut occurs as the recovered target
coordinate of a middle-linkage path. -/
theorem exists_middleTargetCoord_eq
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) {x : GridVertex g} (hx : x ∈ W) :
    ∃ a : R.middle.Index, R.middleTargetCoord a = x := by
  have hv :
      selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x ∈
        selectedOddLocalCrossbarGridTransportedHairEndpointImage
          Hsys hcrossbars hlen i W := by
    rw [selectedOddLocalCrossbarGridTransportedHairEndpointImage_eq_image]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rcases R.middle.target_bijective.2
      ⟨selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x,
        hv⟩ with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply selectedOddLocalCrossbarGridTransportedHairEndpoint_injective Hsys hcrossbars hlen i
  have htarget :
      (R.middle.path a).target =
        selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x :=
    congrArg Subtype.val ha
  rw [R.transportedHairEndpoint_middleTargetCoord a, htarget]

/-- The middle paths are in bijection with the left-side coordinates of the
cut through their recovered source coordinates. -/
noncomputable def middleSourceCoordEquiv
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) :
    R.middle.Index ≃ {x : GridVertex g // x ∈ U} :=
  Equiv.ofBijective
    (fun a => ⟨R.middleSourceCoord a, R.middleSourceCoord_mem a⟩)
    ⟨by
      intro a b hab
      exact R.middleSourceCoord_injective (congrArg Subtype.val hab),
    by
      intro x
      rcases R.exists_middleSourceCoord_eq x.2 with ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩⟩

/-- The middle paths are in bijection with the right-side coordinates of the
cut through their recovered target coordinates. -/
noncomputable def middleTargetCoordEquiv
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) :
    R.middle.Index ≃ {x : GridVertex g // x ∈ W} :=
  Equiv.ofBijective
    (fun a => ⟨R.middleTargetCoord a, R.middleTargetCoord_mem a⟩)
    ⟨by
      intro a b hab
      exact R.middleTargetCoord_injective (congrArg Subtype.val hab),
    by
      intro x
      rcases R.exists_middleTargetCoord_eq x.2 with ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩⟩

/-- The perfect matching on initial coordinates induced by the middle linkage
of a transported matching round. -/
noncomputable def middleCoordMatching
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) :
    {x : GridVertex g // x ∈ U} ≃ {x : GridVertex g // x ∈ W} :=
  R.middleSourceCoordEquiv.symm.trans R.middleTargetCoordEquiv

/-- Applying the inverse source-coordinate equivalence recovers the requested
left coordinate. -/
theorem middleSourceCoord_symm_apply
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    R.middleSourceCoord (R.middleSourceCoordEquiv.symm x) = x.1 := by
  exact congrArg Subtype.val (R.middleSourceCoordEquiv.apply_symm_apply x)

/-- Applying the target-coordinate equivalence to the inverse source index gives
the coordinate selected by `middleCoordMatching`. -/
theorem middleTargetCoord_symm_source_eq_matching
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    R.middleTargetCoord (R.middleSourceCoordEquiv.symm x) =
      (R.middleCoordMatching x).1 := by
  rfl

/-- The middle-linkage path index selected by a left-side initial coordinate. -/
noncomputable def middleIndexOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) : R.middle.Index :=
  R.middleSourceCoordEquiv.symm x

/-- The middle index selected by a source coordinate has that source
coordinate. -/
@[simp] theorem middleSourceCoord_middleIndexOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    R.middleSourceCoord (R.middleIndexOfSourceCoord x) = x.1 := by
  simpa [middleIndexOfSourceCoord] using R.middleSourceCoord_symm_apply x

/-- The target coordinate of the middle index selected by `x` is the coordinate
matched to `x`. -/
@[simp] theorem middleTargetCoord_middleIndexOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    R.middleTargetCoord (R.middleIndexOfSourceCoord x) =
      (R.middleCoordMatching x).1 := by
  simpa [middleIndexOfSourceCoord] using
    R.middleTargetCoord_symm_source_eq_matching x

/-- The middle-linkage graph path addressed by an initial left-side
coordinate. -/
noncomputable def middlePathOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) : GraphPath G :=
  R.middle.path (R.middleIndexOfSourceCoord x)

/-- The middle path selected by a source coordinate stays in the selected hair
cluster of the round. -/
theorem middlePathOfSourceCoord_vertexSet_subset_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.middlePathOfSourceCoord x).vertexSet ⊆
      Hsys.hairCluster (oddClusterIndex hlen i) :=
  R.middle_staysIn (R.middleIndexOfSourceCoord x)

/-- The middle path selected by a source coordinate is disjoint from every full
transported row trace. -/
theorem middlePathOfSourceCoord_vertexSet_disjoint_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) (y : GridVertex g) :
    Disjoint (R.middlePathOfSourceCoord x).vertexSet
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  rw [Finset.disjoint_left]
  intro v hvMiddle hvRow
  have hvHair :
      v ∈ Hsys.hairCluster (oddClusterIndex hlen i) :=
    R.middlePathOfSourceCoord_vertexSet_subset_hairCluster x hvMiddle
  exact Finset.disjoint_left.mp
    (hairCluster_disjoint_selectedOddLocalCrossbarGridRowTrace
      Hsys hcrossbars hlen i y) hvHair hvRow

/-- The middle path selected by a source coordinate starts at that coordinate's
transported hair endpoint. -/
@[simp] theorem middlePathOfSourceCoord_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.middlePathOfSourceCoord x).source =
      selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x.1 := by
  calc
    (R.middlePathOfSourceCoord x).source =
        selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
          (R.middleSourceCoord (R.middleIndexOfSourceCoord x)) := by
        exact (R.transportedHairEndpoint_middleSourceCoord
          (R.middleIndexOfSourceCoord x)).symm
    _ = selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x.1 := by
        rw [R.middleSourceCoord_middleIndexOfSourceCoord x]

/-- The middle path selected by a source coordinate ends at the transported
hair endpoint of the matched right-side coordinate. -/
@[simp] theorem middlePathOfSourceCoord_target
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.middlePathOfSourceCoord x).target =
      selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
        (R.middleCoordMatching x).1 := by
  calc
    (R.middlePathOfSourceCoord x).target =
        selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
          (R.middleTargetCoord (R.middleIndexOfSourceCoord x)) := by
        exact (R.transportedHairEndpoint_middleTargetCoord
          (R.middleIndexOfSourceCoord x)).symm
    _ = selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
          (R.middleCoordMatching x).1 := by
        rw [R.middleTargetCoord_middleIndexOfSourceCoord x]

/-- The canonical transported left spoke used by source coordinate `x`. -/
noncomputable def leftCanonicalSpokeOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (_R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) : GraphPath G :=
  selectedOddLocalCrossbarGridTransportedSpokePath Hsys hcrossbars hlen i x.1

/-- The canonical right spoke, reversed so it starts where the middle path
ends and finishes at the matched row attachment. -/
noncomputable def rightCanonicalSpokeOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) : GraphPath G :=
  (selectedOddLocalCrossbarGridTransportedSpokePath
    Hsys hcrossbars hlen i (R.middleCoordMatching x).1).reverse

@[simp] theorem leftCanonicalSpokeOfSourceCoord_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.leftCanonicalSpokeOfSourceCoord x).source =
      selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x.1 := by
  simp [leftCanonicalSpokeOfSourceCoord]

@[simp] theorem leftCanonicalSpokeOfSourceCoord_target
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.leftCanonicalSpokeOfSourceCoord x).target =
      selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i x.1 := by
  simp [leftCanonicalSpokeOfSourceCoord]

@[simp] theorem rightCanonicalSpokeOfSourceCoord_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.rightCanonicalSpokeOfSourceCoord x).source =
      selectedOddLocalCrossbarGridTransportedHairEndpoint Hsys hcrossbars hlen i
        (R.middleCoordMatching x).1 := by
  simp [rightCanonicalSpokeOfSourceCoord]

@[simp] theorem rightCanonicalSpokeOfSourceCoord_target
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.rightCanonicalSpokeOfSourceCoord x).target =
      selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i
        (R.middleCoordMatching x).1 := by
  simp [rightCanonicalSpokeOfSourceCoord]

/-- The canonical right spoke of a matched edge meets the row trace of the
right coordinate only at its right attachment. -/
theorem rightCanonicalSpokeOfSourceCoord_mem_right_rowTrace_eq_target
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) {v : V}
    (hvSpoke : v ∈ (R.rightCanonicalSpokeOfSourceCoord x).vertexSet)
    (hvRow :
      v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen
        (R.middleCoordMatching x).1) :
    v =
      selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i
        (R.middleCoordMatching x).1 := by
  have hvSpoke' :
      v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i (R.middleCoordMatching x).1).vertexSet := by
    simpa [rightCanonicalSpokeOfSourceCoord] using hvSpoke
  exact selectedOddLocalCrossbarGridTransportedSpokePath_mem_rowTrace_eq_attachment
    Hsys hcrossbars hlen i (R.middleCoordMatching x).1 hvSpoke' hvRow

/-- The source-coordinate index map for middle paths is injective. -/
theorem middleIndexOfSourceCoord_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W) :
    Function.Injective R.middleIndexOfSourceCoord := by
  intro x y hxy
  apply R.middleSourceCoordEquiv.symm.injective
  simpa [middleIndexOfSourceCoord] using hxy

/-- Distinct source coordinates select node-disjoint middle paths. -/
theorem middlePathOfSourceCoord_vertexSet_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    {x y : {x : GridVertex g // x ∈ U}} (hxy : x ≠ y) :
    Disjoint (R.middlePathOfSourceCoord x).vertexSet
      (R.middlePathOfSourceCoord y).vertexSet := by
  have hidx :
      R.middleIndexOfSourceCoord x ≠ R.middleIndexOfSourceCoord y := by
    intro h
    exact hxy (R.middleIndexOfSourceCoord_injective h)
  simpa [middlePathOfSourceCoord, GraphPath.NodeDisjoint] using
    R.middle.toPathPacking.node_disjoint hidx

/-- A left canonical spoke for one source coordinate is disjoint from the
middle path of any different source coordinate. -/
theorem leftCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    {x y : {x : GridVertex g // x ∈ U}} (hxy : x ≠ y) :
    Disjoint (R.leftCanonicalSpokeOfSourceCoord x).vertexSet
      (R.middlePathOfSourceCoord y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvSpoke hvMiddle
  have hvHair :
      v ∈ Hsys.hairCluster (oddClusterIndex hlen i) :=
    R.middlePathOfSourceCoord_vertexSet_subset_hairCluster y hvMiddle
  have hvSpoke' :
      v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i x.1).vertexSet := by
    simpa [leftCanonicalSpokeOfSourceCoord] using hvSpoke
  have hveq :
      v = selectedOddLocalCrossbarGridTransportedHairEndpoint
        Hsys hcrossbars hlen i x.1 :=
    selectedOddLocalCrossbarGridTransportedSpokePath_mem_hairCluster_eq_hairEndpoint
      Hsys hcrossbars hlen i x.1 hvSpoke' hvHair
  have hvMiddleX : v ∈ (R.middlePathOfSourceCoord x).vertexSet := by
    rw [hveq, ← R.middlePathOfSourceCoord_source x]
    exact GraphPath.source_mem_vertexSet (R.middlePathOfSourceCoord x)
  exact Finset.disjoint_left.mp
    (R.middlePathOfSourceCoord_vertexSet_disjoint hxy) hvMiddleX hvMiddle

/-- Symmetric form of
`leftCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord`. -/
theorem middlePathOfSourceCoord_vertexSet_disjoint_leftCanonicalSpokeOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    {x y : {x : GridVertex g // x ∈ U}} (hxy : x ≠ y) :
    Disjoint (R.middlePathOfSourceCoord x).vertexSet
      (R.leftCanonicalSpokeOfSourceCoord y).vertexSet :=
  (R.leftCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord
    (x := y) (y := x) (fun h => hxy h.symm)).symm

/-- A right canonical spoke for one source coordinate is disjoint from the
middle path of any different source coordinate. -/
theorem rightCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    {x y : {x : GridVertex g // x ∈ U}} (hxy : x ≠ y) :
    Disjoint (R.rightCanonicalSpokeOfSourceCoord x).vertexSet
      (R.middlePathOfSourceCoord y).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvSpoke hvMiddle
  have hvHair :
      v ∈ Hsys.hairCluster (oddClusterIndex hlen i) :=
    R.middlePathOfSourceCoord_vertexSet_subset_hairCluster y hvMiddle
  have hvSpoke' :
      v ∈ (selectedOddLocalCrossbarGridTransportedSpokePath
        Hsys hcrossbars hlen i (R.middleCoordMatching x).1).vertexSet := by
    simpa [rightCanonicalSpokeOfSourceCoord] using hvSpoke
  have hveq :
      v = selectedOddLocalCrossbarGridTransportedHairEndpoint
        Hsys hcrossbars hlen i (R.middleCoordMatching x).1 :=
    selectedOddLocalCrossbarGridTransportedSpokePath_mem_hairCluster_eq_hairEndpoint
      Hsys hcrossbars hlen i (R.middleCoordMatching x).1 hvSpoke' hvHair
  have hvMiddleX : v ∈ (R.middlePathOfSourceCoord x).vertexSet := by
    rw [hveq, ← R.middlePathOfSourceCoord_target x]
    exact GraphPath.target_mem_vertexSet (R.middlePathOfSourceCoord x)
  exact Finset.disjoint_left.mp
    (R.middlePathOfSourceCoord_vertexSet_disjoint hxy) hvMiddleX hvMiddle

/-- Symmetric form of
`rightCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord`. -/
theorem middlePathOfSourceCoord_vertexSet_disjoint_rightCanonicalSpokeOfSourceCoord
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    {x y : {x : GridVertex g // x ∈ U}} (hxy : x ≠ y) :
    Disjoint (R.middlePathOfSourceCoord x).vertexSet
      (R.rightCanonicalSpokeOfSourceCoord y).vertexSet :=
  (R.rightCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord
    (x := y) (y := x) (fun h => hxy h.symm)).symm

/-- The left canonical spoke and selected middle path concatenate at the
transported hair endpoint of the source coordinate. -/
theorem leftCanonicalSpoke_target_eq_middlePath_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.leftCanonicalSpokeOfSourceCoord x).target =
      (R.middlePathOfSourceCoord x).source := by
  simp

/-- The selected middle path and reversed right canonical spoke concatenate at
the transported hair endpoint of the matched coordinate. -/
theorem middlePath_target_eq_rightCanonicalSpoke_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.middlePathOfSourceCoord x).target =
      (R.rightCanonicalSpokeOfSourceCoord x).source := by
  simp

/-- The concrete walk obtained by concatenating the left canonical spoke, the
middle hair-cluster linkage path, and the reversed right canonical spoke for
one matched coordinate edge.  It runs from the row attachment of the source
coordinate to the row attachment of the matched target coordinate. -/
noncomputable def matchedCoordinateEdgeWalk
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    G.Walk (R.leftCanonicalSpokeOfSourceCoord x).source
      (R.rightCanonicalSpokeOfSourceCoord x).target :=
  ((R.leftCanonicalSpokeOfSourceCoord x).walk.append
    ((R.middlePathOfSourceCoord x).walk.copy
      (R.leftCanonicalSpoke_target_eq_middlePath_source x).symm rfl)).append
    ((R.rightCanonicalSpokeOfSourceCoord x).walk.copy
      (R.middlePath_target_eq_rightCanonicalSpoke_source x).symm rfl)

/-- The three graph-path pieces associated to a matched coordinate edge.  This
is the concrete path-level object consumed by the later minor model: a left
spoke, a middle linkage path through the hair cluster, and the matched right
spoke in reverse orientation. -/
noncomputable def matchedCoordinateEdgeSupport
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) : Finset V :=
  (R.leftCanonicalSpokeOfSourceCoord x).vertexSet ∪
    ((R.middlePathOfSourceCoord x).vertexSet ∪
      (R.rightCanonicalSpokeOfSourceCoord x).vertexSet)

/-- The concatenated matched-edge walk uses exactly the support vertices
recorded for the matched coordinate edge. -/
theorem matchedCoordinateEdgeWalk_support_toFinset
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.matchedCoordinateEdgeWalk x).support.toFinset =
      R.matchedCoordinateEdgeSupport x := by
  classical
  ext v
  simp [matchedCoordinateEdgeWalk, matchedCoordinateEdgeSupport,
    GraphPath.vertexSet, _root_.SimpleGraph.Walk.mem_support_append_iff,
    or_assoc]

/-- A matched coordinate-edge walk is simple once the three path pieces have
only the intended endpoint intersections: the left spoke and middle path meet
only at their glued endpoint, and the right spoke meets the already-built
prefix only at its glued endpoint. -/
theorem matchedCoordinateEdgeWalk_isPath_of_piecewise_intersections
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U})
    (hleft_middle :
      ∀ ⦃v : V⦄,
        v ∈ (R.leftCanonicalSpokeOfSourceCoord x).vertexSet →
          v ∈ (R.middlePathOfSourceCoord x).vertexSet →
            v = (R.leftCanonicalSpokeOfSourceCoord x).target)
    (hleft_right :
      ∀ ⦃v : V⦄,
        v ∈ (R.leftCanonicalSpokeOfSourceCoord x).vertexSet →
          v ∈ (R.rightCanonicalSpokeOfSourceCoord x).vertexSet →
            v = (R.middlePathOfSourceCoord x).target)
    (hmiddle_right :
      ∀ ⦃v : V⦄,
        v ∈ (R.middlePathOfSourceCoord x).vertexSet →
          v ∈ (R.rightCanonicalSpokeOfSourceCoord x).vertexSet →
            v = (R.middlePathOfSourceCoord x).target) :
    (R.matchedCoordinateEdgeWalk x).IsPath := by
  classical
  let L := R.leftCanonicalSpokeOfSourceCoord x
  let M := R.middlePathOfSourceCoord x
  let S := R.rightCanonicalSpokeOfSourceCoord x
  have hLMglue : L.target = M.source := by
    simp [L, M]
  have hMSglue : M.target = S.source := by
    simp [M, S]
  have hLMpath :
      (L.walk.append (M.walk.copy hLMglue.symm rfl)).IsPath :=
    GraphPath.appendWithEq_isPath_of_inter_subset_target L M hLMglue (by
      intro v hvL hvM
      simpa [L] using hleft_middle (v := v) (by simpa [L] using hvL)
        (by simpa [M] using hvM))
  let LM := L.appendWithEq M hLMglue hLMpath
  have hLM_S_glue : LM.target = S.source := by
    simpa [LM, S] using hMSglue
  have hLM_S_path :
      (LM.walk.append (S.walk.copy hLM_S_glue.symm rfl)).IsPath :=
    GraphPath.appendWithEq_isPath_of_inter_subset_target LM S hLM_S_glue (by
      intro v hvLM hvS
      have hvUnion :=
        GraphPath.appendWithEq_vertexSet_subset L M hLMglue hLMpath hvLM
      rcases Finset.mem_union.mp hvUnion with hvL | hvM
      · have htarget :=
          hleft_right (v := v) (by simpa [L] using hvL) (by simpa [S] using hvS)
        simpa [LM, M] using htarget
      · have htarget :=
          hmiddle_right (v := v) (by simpa [M] using hvM) (by simpa [S] using hvS)
        simpa [LM, M] using htarget)
  simpa [matchedCoordinateEdgeWalk, GraphPath.appendWithEq, L, M, S, LM]
    using hLM_S_path

/-- The canonical matched-coordinate walk is simple.  The two spoke-middle
intersections are forced to the glued hair endpoints by the fact that spokes
meet the hair cluster only at their selected hair endpoint; the two spokes are
disjoint because the matching goes across a disjoint cut. -/
theorem matchedCoordinateEdgeWalk_isPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W) (x : {x : GridVertex g // x ∈ U}) :
    (R.matchedCoordinateEdgeWalk x).IsPath := by
  refine R.matchedCoordinateEdgeWalk_isPath_of_piecewise_intersections x ?_ ?_ ?_
  · intro v hvLeft hvMiddle
    have hvHair :
        v ∈ Hsys.hairCluster (oddClusterIndex hlen i) :=
      R.middlePathOfSourceCoord_vertexSet_subset_hairCluster x hvMiddle
    have h :=
      selectedOddLocalCrossbarGridTransportedSpokePath_mem_hairCluster_eq_hairEndpoint
        Hsys hcrossbars hlen i x.1
        (by
          simpa [leftCanonicalSpokeOfSourceCoord] using hvLeft)
        hvHair
    simpa [leftCanonicalSpokeOfSourceCoord] using h
  · intro v hvLeft hvRight
    have hne : x.1 ≠ (R.middleCoordMatching x).1 := by
      intro h
      exact Finset.disjoint_left.mp hUW x.2
        (by
          rw [h]
          exact (R.middleCoordMatching x).2)
    have hdisj :
        Disjoint
          (selectedOddLocalCrossbarGridTransportedSpokePath
            Hsys hcrossbars hlen i x.1).vertexSet
          (selectedOddLocalCrossbarGridTransportedSpokePath
            Hsys hcrossbars hlen i (R.middleCoordMatching x).1).vertexSet :=
      selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_grid_ne
        Hsys hcrossbars hlen i i hne
    exact False.elim
      (Finset.disjoint_left.mp hdisj
        (by simpa [leftCanonicalSpokeOfSourceCoord] using hvLeft)
        (by
          simpa [rightCanonicalSpokeOfSourceCoord] using hvRight))
  · intro v hvMiddle hvRight
    have hvHair :
        v ∈ Hsys.hairCluster (oddClusterIndex hlen i) :=
      R.middlePathOfSourceCoord_vertexSet_subset_hairCluster x hvMiddle
    have h :=
      selectedOddLocalCrossbarGridTransportedSpokePath_mem_hairCluster_eq_hairEndpoint
        Hsys hcrossbars hlen i (R.middleCoordMatching x).1
        (by
          simpa [rightCanonicalSpokeOfSourceCoord] using hvRight)
        hvHair
    simpa [rightCanonicalSpokeOfSourceCoord] using h

/-- The support of one matched coordinate edge is connected in the host graph. -/
theorem matchedCoordinateEdgeSupport_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (G.induce {v : V | v ∈ R.matchedCoordinateEdgeSupport x}).Connected := by
  have hset :
      {v : V | v ∈ R.matchedCoordinateEdgeSupport x} =
        {v : V | v ∈ (R.matchedCoordinateEdgeWalk x).support} := by
    ext v
    rw [← R.matchedCoordinateEdgeWalk_support_toFinset x]
    simp
  rw [hset]
  exact (R.matchedCoordinateEdgeWalk x).connected_induce_support

/-- The matched coordinate-edge support contains the source row attachment. -/
theorem transportedAttachment_mem_matchedCoordinateEdgeSupport_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i x.1 ∈
      R.matchedCoordinateEdgeSupport x := by
  rw [matchedCoordinateEdgeSupport]
  exact Finset.mem_union_left _ (by
    simpa using
      GraphPath.source_mem_vertexSet (R.leftCanonicalSpokeOfSourceCoord x))

/-- The matched coordinate-edge support contains the matched target row
attachment. -/
theorem transportedAttachment_mem_matchedCoordinateEdgeSupport_right
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    selectedOddLocalCrossbarGridTransportedAttachment Hsys hcrossbars hlen i
        (R.middleCoordMatching x).1 ∈
      R.matchedCoordinateEdgeSupport x := by
  rw [matchedCoordinateEdgeSupport]
  exact Finset.mem_union_right _ <|
    Finset.mem_union_right _ (by
      simpa using
        GraphPath.target_mem_vertexSet (R.rightCanonicalSpokeOfSourceCoord x))

/-- The matched coordinate-edge support stays inside the two transported spoke
traces and the hair cluster used by the middle linkage. -/
theorem matchedCoordinateEdgeSupport_subset_footprint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (x : {x : GridVertex g // x ∈ U}) :
    R.matchedCoordinateEdgeSupport x ⊆
      selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U ∪
        (Hsys.hairCluster (oddClusterIndex hlen i) ∪
          selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i W) := by
  intro v hv
  rw [matchedCoordinateEdgeSupport] at hv
  rcases Finset.mem_union.mp hv with hvLeft | hvRest
  · exact Finset.mem_union_left _ <|
      selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_trace
        Hsys hcrossbars hlen i x.2 hvLeft
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvRight
    · exact Finset.mem_union_right _ <|
        Finset.mem_union_left _ <|
          R.middle_staysIn (R.middleIndexOfSourceCoord x) hvMiddle
    · exact Finset.mem_union_right _ <|
        Finset.mem_union_right _ <|
          selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_trace
            Hsys hcrossbars hlen i (R.middleCoordMatching x).2
            (by
              simpa [rightCanonicalSpokeOfSourceCoord] using hvRight)

/-- A transported matching round across disjoint coordinate sets never matches
a source coordinate to itself. -/
theorem middleCoordMatching_ne_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.middleCoordMatching x).1 ≠ x.1 := by
  intro h
  exact (Finset.disjoint_left.mp hUW x.2)
    (by simpa [h] using (R.middleCoordMatching x).2)

/-- The simple graph on initial grid coordinates whose edges are exactly the
perfect matching realized by one transported matching round.  Vertices outside
`U ∪ W` are isolated; the loopless proof uses disjointness of the two sides of
the cut. -/
noncomputable def coordinateMatchingGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W) : _root_.SimpleGraph (GridVertex g) where
  Adj x y :=
    (∃ hx : x ∈ U, (R.middleCoordMatching ⟨x, hx⟩).1 = y) ∨
      (∃ hy : y ∈ U, (R.middleCoordMatching ⟨y, hy⟩).1 = x)
  symm := by
    intro x y hxy
    rcases hxy with ⟨hx, hmatch⟩ | ⟨hy, hmatch⟩
    · exact Or.inr ⟨hx, hmatch⟩
    · exact Or.inl ⟨hy, hmatch⟩
  loopless := ⟨by
    intro x hxx
    rcases hxx with ⟨hx, hmatch⟩ | ⟨hx, hmatch⟩
    · exact R.middleCoordMatching_ne_left hUW ⟨x, hx⟩ hmatch
    · exact R.middleCoordMatching_ne_left hUW ⟨x, hx⟩ hmatch⟩

/-- The left-to-right endpoint of the coordinate matching is an edge in the
coordinate matching graph. -/
theorem coordinateMatchingGraph_adj_matching
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W)
    (x : {x : GridVertex g // x ∈ U}) :
    (R.coordinateMatchingGraph hUW).Adj x.1 (R.middleCoordMatching x).1 := by
  exact Or.inl ⟨x.2, rfl⟩

/-- A coordinate matching graph edge is witnessed by one of the two orientations
of the round's perfect matching. -/
theorem coordinateMatchingGraph_adj_iff
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W) (x y : GridVertex g) :
    (R.coordinateMatchingGraph hUW).Adj x y ↔
      (∃ hx : x ∈ U, (R.middleCoordMatching ⟨x, hx⟩).1 = y) ∨
        (∃ hy : y ∈ U, (R.middleCoordMatching ⟨y, hy⟩).1 = x) := by
  rfl

/-- Every abstract edge of the coordinate matching graph has an oriented source
coordinate whose concrete matched-edge support realizes that edge. -/
theorem coordinateMatchingGraph_adj_exists_oriented_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W) {x y : GridVertex g}
    (hxy : (R.coordinateMatchingGraph hUW).Adj x y) :
    ∃ a : {x : GridVertex g // x ∈ U},
      (((a.1 = x) ∧ (R.middleCoordMatching a).1 = y) ∨
        ((a.1 = y) ∧ (R.middleCoordMatching a).1 = x)) ∧
        selectedOddLocalCrossbarGridTransportedAttachment
            Hsys hcrossbars hlen i a.1 ∈
          R.matchedCoordinateEdgeSupport a ∧
        selectedOddLocalCrossbarGridTransportedAttachment
            Hsys hcrossbars hlen i (R.middleCoordMatching a).1 ∈
          R.matchedCoordinateEdgeSupport a ∧
        R.matchedCoordinateEdgeSupport a ⊆
          selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i U ∪
            (Hsys.hairCluster (oddClusterIndex hlen i) ∪
              selectedOddLocalCrossbarGridTransportedSpokeTraceImage Hsys hcrossbars hlen i W) := by
  rw [R.coordinateMatchingGraph_adj_iff hUW] at hxy
  rcases hxy with ⟨hx, hmatch⟩ | ⟨hy, hmatch⟩
  · refine ⟨⟨x, hx⟩, ?_, ?_, ?_, ?_⟩
    · exact Or.inl ⟨rfl, hmatch⟩
    · exact R.transportedAttachment_mem_matchedCoordinateEdgeSupport_left ⟨x, hx⟩
    · exact R.transportedAttachment_mem_matchedCoordinateEdgeSupport_right ⟨x, hx⟩
    · exact R.matchedCoordinateEdgeSupport_subset_footprint ⟨x, hx⟩
  · refine ⟨⟨y, hy⟩, ?_, ?_, ?_, ?_⟩
    · exact Or.inr ⟨rfl, hmatch⟩
    · exact R.transportedAttachment_mem_matchedCoordinateEdgeSupport_left ⟨y, hy⟩
    · exact R.transportedAttachment_mem_matchedCoordinateEdgeSupport_right ⟨y, hy⟩
    · exact R.matchedCoordinateEdgeSupport_subset_footprint ⟨y, hy⟩

/-- The unique neighbor of a coordinate in one matching round, if that
coordinate lies on either side of the cut. -/
noncomputable def coordinateMatchingGraphNeighborFinset
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (_hUW : Disjoint U W) (x : GridVertex g) : Finset (GridVertex g) :=
  if hx : x ∈ U then
    {(R.middleCoordMatching ⟨x, hx⟩).1}
  else if hw : x ∈ W then
    {(R.middleCoordMatching.symm ⟨x, hw⟩).1}
  else
    ∅

/-- The explicit neighbor finset for the coordinate matching graph is exact. -/
theorem coordinateMatchingGraph_neighborFinset_isNeighbor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W) (x : GridVertex g) :
    IsNeighborFinset (R.coordinateMatchingGraph hUW) x
      (R.coordinateMatchingGraphNeighborFinset hUW x) := by
  classical
  intro y
  rw [coordinateMatchingGraphNeighborFinset]
  by_cases hx : x ∈ U
  · simp [hx]
    constructor
    · intro hy
      rw [hy]
      exact R.coordinateMatchingGraph_adj_matching hUW ⟨x, hx⟩
    · intro hxy
      rw [R.coordinateMatchingGraph_adj_iff hUW] at hxy
      rcases hxy with ⟨hx', hmatch⟩ | ⟨hy, hmatch⟩
      · have hsub : (⟨x, hx'⟩ : {z : GridVertex g // z ∈ U}) = ⟨x, hx⟩ :=
          Subtype.ext rfl
        have hmatch' : (R.middleCoordMatching ⟨x, hx⟩).1 = y := by
          simpa [hsub] using hmatch
        simp [hmatch']
      · exact False.elim <|
          (Finset.disjoint_left.mp hUW hx)
            (by simpa [hmatch] using (R.middleCoordMatching ⟨y, hy⟩).2)
  · by_cases hw : x ∈ W
    · simp [hx, hw]
      constructor
      · intro hy
        rw [hy]
        exact Or.inr ⟨(R.middleCoordMatching.symm ⟨x, hw⟩).2,
          congrArg Subtype.val
            (R.middleCoordMatching.apply_symm_apply ⟨x, hw⟩)⟩
      · intro hxy
        rw [R.coordinateMatchingGraph_adj_iff hUW] at hxy
        rcases hxy with ⟨hx', _hmatch⟩ | ⟨hy, hmatch⟩
        · exact False.elim (hx hx')
        · have hsub :
              R.middleCoordMatching ⟨y, hy⟩ = ⟨x, hw⟩ :=
            Subtype.ext hmatch
          have hy_eq :
              ⟨y, hy⟩ =
                R.middleCoordMatching.symm ⟨x, hw⟩ := by
            simpa [hsub] using
              (R.middleCoordMatching.symm_apply_apply ⟨y, hy⟩).symm
          exact congrArg Subtype.val hy_eq
    · simp [hx, hw]
      intro hxy
      rw [R.coordinateMatchingGraph_adj_iff hUW] at hxy
      rcases hxy with ⟨hx', _hmatch⟩ | ⟨hy, hmatch⟩
      · exact hx hx'
      · exact hw (by simpa [hmatch] using (R.middleCoordMatching ⟨y, hy⟩).2)

/-- One transported round contributes a matching: every coordinate has degree
at most one in its coordinate matching graph. -/
theorem coordinateMatchingGraph_degreeAtMost_one
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W) (x : GridVertex g) :
    DegreeAtMost (R.coordinateMatchingGraph hUW) x 1 := by
  classical
  refine ⟨R.coordinateMatchingGraphNeighborFinset hUW x,
    R.coordinateMatchingGraph_neighborFinset_isNeighbor hUW x, ?_⟩
  rw [coordinateMatchingGraphNeighborFinset]
  by_cases hx : x ∈ U
  · simp [hx]
  · by_cases hw : x ∈ W
    · simp [hx, hw]
    · simp [hx, hw]

/-- The explicit neighbor finset for one coordinate matching round has size at
most one. -/
theorem coordinateMatchingGraphNeighborFinset_card_le_one
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell} {i : Fin m}
    {U W : Finset (GridVertex g)}
    (R : SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen i U W)
    (hUW : Disjoint U W) (x : GridVertex g) :
    (R.coordinateMatchingGraphNeighborFinset hUW x).card ≤ 1 := by
  classical
  rw [coordinateMatchingGraphNeighborFinset]
  by_cases hx : x ∈ U
  · simp [hx]
  · by_cases hw : x ∈ W
    · simp [hx, hw]
    · simp [hx, hw]

end SelectedOddLocalCrossbarGridTransportedMatchingRound

/-- A finite family of transported cut-matching rounds in selected odd local
crossbars.  This is the proof-facing object that records the output of the
cut-matching game before the expander-to-grid-minor step: each round supplies a
perfect matching on the fixed coordinate set `GridVertex g`, and the family
graph is their union. -/
structure SelectedOddLocalCrossbarGridTransportedRoundFamily
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) where
  /-- The finite index type of cut-matching rounds. -/
  Index : Type u
  /-- Finiteness of the round index type. -/
  indexFintype : Fintype Index
  /-- The selected odd local crossbar used by each round. -/
  cluster : Index → Fin m
  /-- Distinct cut-matching rounds use distinct selected odd local crossbars. -/
  cluster_injective : Function.Injective cluster
  /-- The left side of the coordinate cut in each round. -/
  U : Index → Finset (GridVertex g)
  /-- The right side of the coordinate cut in each round. -/
  W : Index → Finset (GridVertex g)
  /-- The two sides of each cut are disjoint. -/
  disjoint : ∀ r : Index, Disjoint (U r) (W r)
  /-- The two sides of each cut have equal size. -/
  card_eq : ∀ r : Index, (U r).card = (W r).card
  /-- The transported matching round realized in the host graph. -/
  round : ∀ r : Index,
    SelectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen (cluster r) (U r) (W r)

namespace SelectedOddLocalCrossbarGridTransportedRoundFamily

instance
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) : Fintype F.Index :=
  F.indexFintype

/-- Build a finite transported-round family by choosing the canonical
transported matching round for every cut in a finite cut transcript. -/
noncomputable def ofCuts
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell)
    (ι : Type u) [Fintype ι]
    (cluster : ι → Fin m)
    (hcluster : Function.Injective cluster)
    (U W : ι → Finset (GridVertex g))
    (hdisj : ∀ r : ι, Disjoint (U r) (W r))
    (hcard : ∀ r : ι, (U r).card = (W r).card) :
    SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen where
  Index := ι
  indexFintype := inferInstance
  cluster := cluster
  cluster_injective := hcluster
  U := U
  W := W
  disjoint := hdisj
  card_eq := hcard
  round := fun r =>
    selectedOddLocalCrossbarGridTransportedMatchingRound
      Hsys hcrossbars hlen (cluster r) (hdisj r) (hcard r)

/-- The canonical injection of finitely many cut-matching rounds into the
selected odd local clusters.  Round `r` uses selected cluster `r`, viewed in
`Fin m` through the proof that enough clusters were reserved. -/
def finCluster
    {roundBound m : ℕ} (hrounds : roundBound ≤ m) :
    Fin roundBound → Fin m :=
  fun r => ⟨r.1, lt_of_lt_of_le r.2 hrounds⟩

/-- The canonical round-to-cluster assignment is injective. -/
theorem finCluster_injective
    {roundBound m : ℕ} (hrounds : roundBound ≤ m) :
    Function.Injective (finCluster hrounds) := by
  intro r s hrs
  apply Fin.ext
  simpa [finCluster] using congrArg Fin.val hrs

/-- Build the transported-round family from a finite cut transcript whose
rounds are indexed by `Fin roundBound`.  This removes the bookkeeping choice
of an arbitrary injection into the selected odd clusters from later theorem
statements. -/
noncomputable def ofFinCuts
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell)
    (hrounds : roundBound ≤ m)
    (U W : Fin roundBound → Finset (GridVertex g))
    (hdisj : ∀ r : Fin roundBound, Disjoint (U r) (W r))
    (hcard : ∀ r : Fin roundBound, (U r).card = (W r).card) :
    SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen :=
  ofCuts Hsys hcrossbars hlen (ULift (Fin roundBound))
    (fun r => finCluster hrounds r.down)
    (by
      intro r s hrs
      apply ULift.ext
      exact finCluster_injective hrounds hrs)
    (fun r => U r.down) (fun r => W r.down)
    (fun r => hdisj r.down) (fun r => hcard r.down)

/-- The coordinate matching graph contributed by one indexed round. -/
noncomputable def roundGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (r : F.Index) :
    _root_.SimpleGraph (GridVertex g) :=
  (F.round r).coordinateMatchingGraph (F.disjoint r)

/-- The auxiliary coordinate graph obtained as the union of all matching rounds
in the family. -/
noncomputable def auxGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) :
    _root_.SimpleGraph (GridVertex g) where
  Adj x y := ∃ r : F.Index, (F.roundGraph r).Adj x y
  symm := by
    intro x y hxy
    rcases hxy with ⟨r, hxy⟩
    exact ⟨r, (F.roundGraph r).symm hxy⟩
  loopless := ⟨by
    intro x hxx
    rcases hxx with ⟨r, hxx⟩
    exact (F.roundGraph r).loopless.irrefl x hxx⟩

/-- Adjacency in the auxiliary graph is adjacency in one round graph. -/
theorem auxGraph_adj_iff
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x y : GridVertex g) :
    F.auxGraph.Adj x y ↔ ∃ r : F.Index, (F.roundGraph r).Adj x y := by
  rfl

/-- A round edge is an edge of the auxiliary union graph. -/
theorem auxGraph_adj_of_round
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (r : F.Index) {x y : GridVertex g}
    (hxy : (F.roundGraph r).Adj x y) :
    F.auxGraph.Adj x y :=
  ⟨r, hxy⟩

/-- The matched coordinate pair of any indexed round is present in the
auxiliary graph. -/
theorem auxGraph_adj_matching
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (r : F.Index)
    (x : {x : GridVertex g // x ∈ F.U r}) :
    F.auxGraph.Adj x.1 ((F.round r).middleCoordMatching x).1 :=
  F.auxGraph_adj_of_round r <|
    (F.round r).coordinateMatchingGraph_adj_matching (F.disjoint r) x

/-- The union of the explicit one-round neighbor finsets. -/
noncomputable def neighborFinset
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x : GridVertex g) : Finset (GridVertex g) :=
  Finset.univ.biUnion fun r : F.Index =>
    (F.round r).coordinateMatchingGraphNeighborFinset (F.disjoint r) x

/-- The explicit neighbor finset for the auxiliary union graph is exact. -/
theorem neighborFinset_isNeighbor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x : GridVertex g) :
    IsNeighborFinset F.auxGraph x (F.neighborFinset x) := by
  classical
  intro y
  constructor
  · intro hy
    rw [neighborFinset] at hy
    rcases Finset.mem_biUnion.mp hy with ⟨r, _hr, hry⟩
    exact ⟨r,
      ((F.round r).coordinateMatchingGraph_neighborFinset_isNeighbor
        (F.disjoint r) x y).1 hry⟩
  · intro hxy
    rw [auxGraph_adj_iff] at hxy
    rcases hxy with ⟨r, hry⟩
    rw [neighborFinset]
    exact Finset.mem_biUnion.mpr
      ⟨r, by simp,
        ((F.round r).coordinateMatchingGraph_neighborFinset_isNeighbor
          (F.disjoint r) x y).2 hry⟩

/-- The degree of the auxiliary coordinate graph is bounded by the number of
cut-matching rounds. -/
theorem auxGraph_degreeAtMost_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x : GridVertex g) :
    DegreeAtMost F.auxGraph x (Fintype.card F.Index) := by
  classical
  refine ⟨F.neighborFinset x, F.neighborFinset_isNeighbor x, ?_⟩
  rw [neighborFinset]
  have hcard :
      (Finset.univ.biUnion fun r : F.Index =>
        (F.round r).coordinateMatchingGraphNeighborFinset (F.disjoint r) x).card ≤
        (Finset.univ : Finset F.Index).card * 1 :=
    Finset.card_biUnion_le_card_mul _ _ 1 (by
      intro r _hr
      exact (F.round r).coordinateMatchingGraphNeighborFinset_card_le_one
        (F.disjoint r) x)
  simpa using hcard

/-- The auxiliary coordinate graph has maximum degree bounded by the number of
cut-matching rounds. -/
theorem auxGraph_maxDegreeAtMost_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) :
    MaxDegreeAtMost F.auxGraph (Fintype.card F.Index) := by
  intro x
  exact F.auxGraph_degreeAtMost_card x

/-- Every round cut covers all coordinate vertices.  This is the condition
supplied by a genuine cut-matching game transcript. -/
def CoversAll
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) : Prop :=
  ∀ r : F.Index, F.U r ∪ F.W r = Finset.univ

/-- Every auxiliary coordinate edge comes from one round and carries the
concrete support witness supplied by that round. -/
theorem auxGraph_adj_exists_round_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) {x y : GridVertex g}
    (hxy : F.auxGraph.Adj x y) :
    ∃ r : F.Index,
      ∃ a : {x : GridVertex g // x ∈ F.U r},
        (((a.1 = x) ∧ ((F.round r).middleCoordMatching a).1 = y) ∨
          ((a.1 = y) ∧ ((F.round r).middleCoordMatching a).1 = x)) ∧
          selectedOddLocalCrossbarGridTransportedAttachment
              Hsys hcrossbars hlen (F.cluster r) a.1 ∈
            (F.round r).matchedCoordinateEdgeSupport a ∧
          selectedOddLocalCrossbarGridTransportedAttachment
              Hsys hcrossbars hlen (F.cluster r)
                ((F.round r).middleCoordMatching a).1 ∈
            (F.round r).matchedCoordinateEdgeSupport a ∧
          (F.round r).matchedCoordinateEdgeSupport a ⊆
            selectedOddLocalCrossbarGridTransportedSpokeTraceImage
                Hsys hcrossbars hlen (F.cluster r) (F.U r) ∪
              (Hsys.hairCluster (oddClusterIndex hlen (F.cluster r)) ∪
                selectedOddLocalCrossbarGridTransportedSpokeTraceImage
                  Hsys hcrossbars hlen (F.cluster r) (F.W r)) := by
  rw [F.auxGraph_adj_iff] at hxy
  rcases hxy with ⟨r, hrxy⟩
  rcases (F.round r).coordinateMatchingGraph_adj_exists_oriented_support
      (F.disjoint r) hrxy with
    ⟨a, horient, hleft, hright, hsupport⟩
  exact ⟨r, a, horient, hleft, hright, hsupport⟩

/-- Every auxiliary coordinate edge has concrete contact vertices on the row
traces of its two endpoints.  The contacts both lie in the support of the
corresponding transported matched edge. -/
theorem auxGraph_adj_exists_rowTrace_contacts
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) {x y : GridVertex g}
    (hxy : F.auxGraph.Adj x y) :
    ∃ r : F.Index,
      ∃ a : {x : GridVertex g // x ∈ F.U r},
        ∃ vx ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x,
          ∃ vy ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y,
            vx ∈ (F.round r).matchedCoordinateEdgeSupport a ∧
              vy ∈ (F.round r).matchedCoordinateEdgeSupport a := by
  rcases F.auxGraph_adj_exists_round_support hxy with
    ⟨r, a, horient, hleft, hright, _hsupport⟩
  rcases horient with ⟨hax, hmatch⟩ | ⟨hay, hmatch⟩
  · refine ⟨r, a,
      selectedOddLocalCrossbarGridTransportedAttachment
        Hsys hcrossbars hlen (F.cluster r) a.1, ?_,
      selectedOddLocalCrossbarGridTransportedAttachment
        Hsys hcrossbars hlen (F.cluster r)
          ((F.round r).middleCoordMatching a).1, ?_, ?_, ?_⟩
    · simpa [hax] using
        selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
          Hsys hcrossbars hlen (F.cluster r) a.1
    · simpa [hmatch] using
        selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
          Hsys hcrossbars hlen (F.cluster r)
            ((F.round r).middleCoordMatching a).1
    · exact hleft
    · exact hright
  · refine ⟨r, a,
      selectedOddLocalCrossbarGridTransportedAttachment
        Hsys hcrossbars hlen (F.cluster r)
          ((F.round r).middleCoordMatching a).1, ?_,
      selectedOddLocalCrossbarGridTransportedAttachment
        Hsys hcrossbars hlen (F.cluster r) a.1, ?_, ?_, ?_⟩
    · simpa [hmatch] using
        selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
          Hsys hcrossbars hlen (F.cluster r)
            ((F.round r).middleCoordMatching a).1
    · simpa [hay] using
        selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
          Hsys hcrossbars hlen (F.cluster r) a.1
    · exact hright
    · exact hleft

/-- Edge instances of the cut-matching transcript.  This keeps the multiplicity
that the paper's auxiliary multigraph uses: an edge is a round together with
one source coordinate on the left side of that round's cut. -/
structure Edge
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) where
  /-- The cut-matching round containing this edge. -/
  round : F.Index
  /-- The left-side source coordinate of this oriented matching edge. -/
  source : {x : GridVertex g // x ∈ F.U round}

namespace Edge

instance
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) : Fintype (Edge F) := by
  classical
  refine Fintype.ofEquiv
    (Σ r : F.Index, {x : GridVertex g // x ∈ F.U r}) ?_
  exact {
    toFun := fun p => ⟨p.1, p.2⟩
    invFun := fun e => ⟨e.round, e.source⟩
    left_inv := by
      intro p
      rfl
    right_inv := by
      intro e
      cases e
      rfl }

/-- Edge instances are equivalent to a sigma type over rounds and left-side
coordinates. -/
noncomputable def sigmaEquiv
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) :
    Edge F ≃ (Σ r : F.Index, {x : GridVertex g // x ∈ F.U r}) where
  toFun := fun e => ⟨e.round, e.source⟩
  invFun := fun p => ⟨p.1, p.2⟩
  left_inv := by
    intro e
    cases e
    rfl
  right_inv := by
    intro p
    rfl

/-- The number of transcript edge instances is the sum of the left-side cut
sizes over all rounds. -/
theorem card_eq_sum_leftCuts
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) :
    Fintype.card (Edge F) = ∑ r : F.Index, (F.U r).card := by
  classical
  calc
    Fintype.card (Edge F) =
        Fintype.card (Σ r : F.Index, {x : GridVertex g // x ∈ F.U r}) :=
      Fintype.card_congr (sigmaEquiv F)
    _ = ∑ r : F.Index, Fintype.card {x : GridVertex g // x ∈ F.U r} := by
      rw [Fintype.card_sigma]
    _ = ∑ r : F.Index, (F.U r).card := by
      simp

/-- Left endpoint of a transcript edge. -/
noncomputable def left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) : GridVertex g :=
  e.source.1

/-- Right endpoint of a transcript edge, obtained from the round's perfect
matching. -/
noncomputable def right
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) : GridVertex g :=
  ((F.round e.round).middleCoordMatching e.source).1

/-- The right endpoint lies on the right side of the corresponding cut. -/
theorem right_mem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.right ∈ F.W e.round :=
  ((F.round e.round).middleCoordMatching e.source).2

/-- A transcript edge is never a loop, because every round matches across a
disjoint cut. -/
theorem right_ne_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.right ≠ e.left :=
  (F.round e.round).middleCoordMatching_ne_left
    (F.disjoint e.round) e.source

/-- Incidence of a coordinate with an edge of the edge-indexed cut-matching
multigraph. -/
def Incident
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) (x : GridVertex g) : Prop :=
  e.left = x ∨ e.right = x

@[simp] theorem incident_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.Incident e.left :=
  Or.inl rfl

@[simp] theorem incident_right
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.Incident e.right :=
  Or.inr rfl

/-- The simple auxiliary graph contains the unordered adjacency underlying a
transcript edge. -/
theorem auxGraph_adj
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    F.auxGraph.Adj e.left e.right :=
  F.auxGraph_adj_matching e.round e.source

/-- The concrete support of a transcript edge in the host graph. -/
noncomputable def support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) : Finset V :=
  (F.round e.round).matchedCoordinateEdgeSupport e.source

/-- The left row-attachment contact of a transcript edge. -/
noncomputable def leftContact
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) : V :=
  selectedOddLocalCrossbarGridTransportedAttachment
    Hsys hcrossbars hlen (F.cluster e.round) e.left

/-- The right row-attachment contact of a transcript edge. -/
noncomputable def rightContact
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) : V :=
  selectedOddLocalCrossbarGridTransportedAttachment
    Hsys hcrossbars hlen (F.cluster e.round) e.right

/-- The left contact lies on the row trace of the left endpoint. -/
theorem leftContact_mem_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.leftContact ∈
      selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.left := by
  simpa [leftContact, left] using
    selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
      Hsys hcrossbars hlen (F.cluster e.round) e.left

/-- The right contact lies on the row trace of the right endpoint. -/
theorem rightContact_mem_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.rightContact ∈
      selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right := by
  simpa [rightContact, right] using
    selectedOddLocalCrossbarGridTransportedAttachment_mem_rowTrace
      Hsys hcrossbars hlen (F.cluster e.round) e.right

/-- The canonical right spoke of a transcript edge meets the right endpoint's
row trace only at the right contact. -/
theorem rightCanonicalSpoke_mem_right_rowTrace_eq_rightContact
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) {v : V}
    (hvSpoke :
      v ∈ ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet)
    (hvRow :
      v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right) :
    v = e.rightContact := by
  simpa [rightContact, right] using
    (F.round e.round).rightCanonicalSpokeOfSourceCoord_mem_right_rowTrace_eq_target
      e.source hvSpoke (by simpa [right] using hvRow)

/-- The left canonical spoke of a transcript edge stays in the local footprint
of the selected odd cluster used by that edge's round. -/
theorem leftCanonicalSpoke_vertexSet_subset_hairLocalVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).vertexSet ⊆
      Hsys.hairLocalVertexSet (oddClusterIndex hlen (F.cluster e.round)) := by
  simpa [SelectedOddLocalCrossbarGridTransportedMatchingRound.leftCanonicalSpokeOfSourceCoord,
    left] using
    selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen (F.cluster e.round) e.left

/-- The right canonical spoke of a transcript edge stays in the local footprint
of the selected odd cluster used by that edge's round. -/
theorem rightCanonicalSpoke_vertexSet_subset_hairLocalVertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet ⊆
      Hsys.hairLocalVertexSet (oddClusterIndex hlen (F.cluster e.round)) := by
  simpa [SelectedOddLocalCrossbarGridTransportedMatchingRound.rightCanonicalSpokeOfSourceCoord,
    right] using
    selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_subset_localVertexSet
      Hsys hcrossbars hlen (F.cluster e.round) e.right

/-- The middle path of a transcript edge stays in the hair cluster of the
selected odd cluster used by that edge's round. -/
theorem middlePath_vertexSet_subset_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet ⊆
      Hsys.hairCluster (oddClusterIndex hlen (F.cluster e.round)) :=
  (F.round e.round).middlePathOfSourceCoord_vertexSet_subset_hairCluster e.source

/-- The left contact is contained in the concrete support of the transcript
edge. -/
theorem leftContact_mem_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.leftContact ∈ e.support := by
  simpa [leftContact, support, left] using
    (F.round e.round).transportedAttachment_mem_matchedCoordinateEdgeSupport_left
      e.source

/-- The right contact is contained in the concrete support of the transcript
edge. -/
theorem rightContact_mem_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.rightContact ∈ e.support := by
  simpa [rightContact, support, right] using
    (F.round e.round).transportedAttachment_mem_matchedCoordinateEdgeSupport_right
      e.source

/-- The concrete host walk supporting a transcript edge.  It is the
concatenation of the selected left spoke, the hair-cluster linkage, and the
reversed selected right spoke. -/
noncomputable def walk
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    G.Walk
      ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).source
      ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).target :=
  (F.round e.round).matchedCoordinateEdgeWalk e.source

/-- The vertices used by the supporting walk of a transcript edge are exactly
the recorded edge support. -/
theorem walk_support_toFinset
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.support.toFinset = e.support := by
  simpa [walk, support] using
    (F.round e.round).matchedCoordinateEdgeWalk_support_toFinset e.source

/-- The concrete supporting walk of every transcript edge is simple. -/
theorem walk_isPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.IsPath := by
  simpa [walk] using
    (F.round e.round).matchedCoordinateEdgeWalk_isPath
      (F.disjoint e.round) e.source

/-- The support of every transcript edge is connected in the host graph. -/
theorem support_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    (G.induce {v : V | v ∈ e.support}).Connected := by
  simpa [support] using
    (F.round e.round).matchedCoordinateEdgeSupport_connected e.source

/-- The two row contacts of a transcript edge are distinct.  They are
transported attachments of distinct coordinate endpoints in the same selected
crossbar. -/
theorem leftContact_ne_rightContact
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.leftContact ≠ e.rightContact := by
  intro h
  have hcoord :
      e.left = e.right :=
    selectedOddLocalCrossbarGridTransportedAttachment_injective
      Hsys hcrossbars hlen (F.cluster e.round) h
  exact e.right_ne_left hcoord.symm

/-- The supporting walk of a transcript edge is nontrivial. -/
theorem walk_not_nil
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    ¬ e.walk.Nil := by
  intro hnil
  have hne := e.leftContact_ne_rightContact
  apply hne
  simpa [walk, leftContact, rightContact, left, right] using hnil.eq

/-- If the supporting walk of a transcript edge is simple, its final right
contact is not part of the half-open support allocated to the left endpoint. -/
theorem rightContact_not_mem_walk_dropLast_support_of_isPath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) (hpath : e.walk.IsPath) :
    e.rightContact ∉ e.walk.support.dropLast.toFinset := by
  simpa [walk, rightContact, right] using
    (Lax17Proofs.SimpleGraph.Walk.end_not_mem_support_dropLast_toFinset_of_isPath
      (p := e.walk) hpath)

/-- The final right contact is not part of the half-open support allocated to
the left endpoint. -/
theorem rightContact_not_mem_walk_dropLast_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.rightContact ∉ e.walk.support.dropLast.toFinset :=
  e.rightContact_not_mem_walk_dropLast_support_of_isPath e.walk_isPath

/-- The final edge of the supporting walk joins its penultimate vertex to the
right row contact. -/
theorem walk_penultimate_adj_rightContact
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    G.Adj e.walk.penultimate e.rightContact := by
  simpa [walk, rightContact, right] using
    e.walk.adj_penultimate e.walk_not_nil

/-- The supporting walk starts at the left row contact. -/
theorem walk_source_eq_leftContact
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).source =
      e.leftContact := by
  simp [leftContact, left]

/-- The left contact belongs to the half-open support of the supporting walk. -/
theorem leftContact_mem_walk_dropLast_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.leftContact ∈ e.walk.support.dropLast.toFinset := by
  have hmem :
      ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).source ∈
        e.walk.dropLast.support.toFinset := by
    simpa [walk] using
      (List.mem_toFinset.mpr e.walk.dropLast.start_mem_support)
  rw [← e.walk.support_dropLast e.walk_not_nil]
  simpa [e.walk_source_eq_leftContact] using hmem

/-- The half-open support of the supporting walk is connected. -/
theorem walk_dropLast_support_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    (G.induce {v : V | v ∈ e.walk.support.dropLast.toFinset}).Connected := by
  have hset :
      {v : V | v ∈ e.walk.support.dropLast.toFinset} =
        {v : V | v ∈ e.walk.dropLast.support} := by
    ext v
    simp [e.walk.support_dropLast e.walk_not_nil]
  rw [hset]
  exact e.walk.dropLast.connected_induce_support

/-- The penultimate vertex of the supporting walk belongs to the recorded
support of the transcript edge. -/
theorem walk_penultimate_mem_dropLast_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.penultimate ∈ e.walk.support.dropLast.toFinset := by
  exact List.mem_toFinset.mpr
    (e.walk.penultimate_mem_dropLast_support e.walk_not_nil)

/-- The penultimate vertex of the supporting walk belongs to the recorded
support of the transcript edge. -/
theorem walk_penultimate_mem_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.penultimate ∈ e.support := by
  have hsubset : e.walk.support.dropLast.toFinset ⊆ e.walk.support.toFinset := by
    intro v hv
    exact List.mem_toFinset.mpr
      (List.mem_of_mem_dropLast (List.mem_toFinset.mp hv))
  rw [← e.walk_support_toFinset]
  exact hsubset e.walk_penultimate_mem_dropLast_support

/-- The half-open walk support used for source allocation is contained in the
full transcript-edge support. -/
theorem walk_dropLast_support_subset_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.support.dropLast.toFinset ⊆ e.support := by
  intro v hv
  rw [← e.walk_support_toFinset]
  exact List.mem_toFinset.mpr
    (List.mem_of_mem_dropLast (List.mem_toFinset.mp hv))

/-- To prove that the half-open support of a transcript edge avoids a row trace,
it is enough to prove this separately for the left spoke, the middle linkage
path, and the reversed right spoke of the matched coordinate edge. -/
theorem walk_dropLast_support_disjoint_rowTrace_of_piecewise_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) (y : GridVertex g)
    (hleft :
      Disjoint
        ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).vertexSet
        (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (hmiddle :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (hright :
      Disjoint
        ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet
        (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y)) :
    Disjoint e.walk.support.dropLast.toFinset
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  rw [Finset.disjoint_left]
  intro v hvDrop hvRow
  have hvSupport := e.walk_dropLast_support_subset_support hvDrop
  rw [support,
    SelectedOddLocalCrossbarGridTransportedMatchingRound.matchedCoordinateEdgeSupport]
    at hvSupport
  rcases Finset.mem_union.mp hvSupport with hvLeft | hvRest
  · exact Finset.disjoint_left.mp hleft hvLeft hvRow
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvRight
    · exact Finset.disjoint_left.mp hmiddle hvMiddle hvRow
    · exact Finset.disjoint_left.mp hright hvRight hvRow

/-- If a row is distinct from both endpoints of a transcript edge, the spoke
parts of the edge support are automatically disjoint from that row; only the
middle hair-cluster linkage path remains as an explicit obligation. -/
theorem walk_dropLast_support_disjoint_rowTrace_of_middle_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) {y : GridVertex g}
    (hleft : e.left ≠ y) (hright : e.right ≠ y)
    (hmiddle :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y)) :
    Disjoint e.walk.support.dropLast.toFinset
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  refine e.walk_dropLast_support_disjoint_rowTrace_of_piecewise_disjoint y ?_ hmiddle ?_
  · simpa [left, SelectedOddLocalCrossbarGridTransportedMatchingRound.leftCanonicalSpokeOfSourceCoord]
      using
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_rowTrace_of_grid_ne
          Hsys hcrossbars hlen (F.cluster e.round) (x := e.left) (y := y) hleft)
  · simpa [right,
      SelectedOddLocalCrossbarGridTransportedMatchingRound.rightCanonicalSpokeOfSourceCoord]
      using
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_rowTrace_of_grid_ne
          Hsys hcrossbars hlen (F.cluster e.round) (x := e.right) (y := y) hright)

/-- If a row is distinct from both endpoints of a transcript edge, then the
half-open support allocated to that edge is disjoint from the row trace.  The
middle linkage lies in the selected hair cluster, which is disjoint from every
row trace. -/
theorem walk_dropLast_support_disjoint_rowTrace_of_endpoints_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) {y : GridVertex g}
    (hleft : e.left ≠ y) (hright : e.right ≠ y) :
    Disjoint e.walk.support.dropLast.toFinset
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  exact e.walk_dropLast_support_disjoint_rowTrace_of_middle_disjoint
    hleft hright
    ((F.round e.round).middlePathOfSourceCoord_vertexSet_disjoint_rowTrace
      e.source y)

/-- Nonincident form of
`walk_dropLast_support_disjoint_rowTrace_of_endpoints_ne`. -/
theorem walk_dropLast_support_disjoint_rowTrace_of_not_incident
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) {y : GridVertex g}
    (hnot : ¬ e.Incident y) :
    Disjoint e.walk.support.dropLast.toFinset
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  exact e.walk_dropLast_support_disjoint_rowTrace_of_endpoints_ne
    (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))

/-- Incident-right endpoint reduction for row separation.  The only extra
input needed is the sharp fact that the right spoke intersects its own row
trace only at the right row contact; the half-open support then removes exactly
that contact. -/
theorem walk_dropLast_support_disjoint_right_rowTrace_of_right_spoke_inter
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F)
    (hright_spoke :
      ∀ ⦃v : V⦄,
        v ∈ ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet →
          v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right →
            v = e.rightContact) :
    Disjoint e.walk.support.dropLast.toFinset
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right) := by
  rw [Finset.disjoint_left]
  intro v hvDrop hvRow
  have hvSupport := e.walk_dropLast_support_subset_support hvDrop
  rw [support,
    SelectedOddLocalCrossbarGridTransportedMatchingRound.matchedCoordinateEdgeSupport]
    at hvSupport
  rcases Finset.mem_union.mp hvSupport with hvLeft | hvRest
  · exact Finset.disjoint_left.mp
      (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_rowTrace_of_grid_ne
        Hsys hcrossbars hlen (F.cluster e.round)
        (x := e.left) (y := e.right)
        (fun h => e.right_ne_left h.symm))
      (by
        simpa [left,
          SelectedOddLocalCrossbarGridTransportedMatchingRound.leftCanonicalSpokeOfSourceCoord]
          using hvLeft)
      hvRow
  · rcases Finset.mem_union.mp hvRest with hvMiddle | hvRight
    · exact Finset.disjoint_left.mp
        ((F.round e.round).middlePathOfSourceCoord_vertexSet_disjoint_rowTrace
          e.source e.right) hvMiddle hvRow
    · have hcontact : v = e.rightContact :=
        hright_spoke hvRight hvRow
      exact e.rightContact_not_mem_walk_dropLast_support (by
        simpa [hcontact] using hvDrop)

/-- Branch-set row-separation form for one outgoing transcript edge.  If the
row is the right endpoint of the edge, the proof uses the sharp right-spoke
intersection hypothesis; otherwise it is the nonincident case. -/
theorem walk_dropLast_support_disjoint_rowTrace_of_left_ne_of_right_spoke_inter
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) {x y : GridVertex g}
    (hleft : e.left = x) (hxy : x ≠ y)
    (hright_spoke :
      ∀ ⦃v : V⦄,
        v ∈ ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet →
          v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right →
            v = e.rightContact) :
    Disjoint e.walk.support.dropLast.toFinset
      (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y) := by
  by_cases hright : e.right = y
  · subst y
    exact e.walk_dropLast_support_disjoint_right_rowTrace_of_right_spoke_inter
      hright_spoke
  · exact e.walk_dropLast_support_disjoint_rowTrace_of_endpoints_ne
      (by
        intro h
        exact hxy (hleft ▸ h))
      hright

/-- To prove that the half-open supports of two transcript edges are disjoint,
it is enough to prove all nine pairwise disjointness facts between their
left-spoke, middle-linkage, and right-spoke pieces. -/
theorem walk_dropLast_support_disjoint_of_piecewise_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e f : Edge F)
    (h_left_left :
      Disjoint
        ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).leftCanonicalSpokeOfSourceCoord f.source).vertexSet)
    (h_left_middle :
      Disjoint
        ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).middlePathOfSourceCoord f.source).vertexSet)
    (h_left_right :
      Disjoint
        ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).rightCanonicalSpokeOfSourceCoord f.source).vertexSet)
    (h_middle_left :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        ((F.round f.round).leftCanonicalSpokeOfSourceCoord f.source).vertexSet)
    (h_middle_middle :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        ((F.round f.round).middlePathOfSourceCoord f.source).vertexSet)
    (h_middle_right :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        ((F.round f.round).rightCanonicalSpokeOfSourceCoord f.source).vertexSet)
    (h_right_left :
      Disjoint
        ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).leftCanonicalSpokeOfSourceCoord f.source).vertexSet)
    (h_right_middle :
      Disjoint
        ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).middlePathOfSourceCoord f.source).vertexSet)
    (h_right_right :
      Disjoint
        ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).rightCanonicalSpokeOfSourceCoord f.source).vertexSet) :
    Disjoint e.walk.support.dropLast.toFinset
      f.walk.support.dropLast.toFinset := by
  rw [Finset.disjoint_left]
  intro v hvE hvF
  have hvESupport := e.walk_dropLast_support_subset_support hvE
  have hvFSupport := f.walk_dropLast_support_subset_support hvF
  rw [support,
    SelectedOddLocalCrossbarGridTransportedMatchingRound.matchedCoordinateEdgeSupport]
    at hvESupport
  rw [support,
    SelectedOddLocalCrossbarGridTransportedMatchingRound.matchedCoordinateEdgeSupport]
    at hvFSupport
  rcases Finset.mem_union.mp hvESupport with hvELeft | hvERest
  · rcases Finset.mem_union.mp hvFSupport with hvFLeft | hvFRest
    · exact Finset.disjoint_left.mp h_left_left hvELeft hvFLeft
    · rcases Finset.mem_union.mp hvFRest with hvFMiddle | hvFRight
      · exact Finset.disjoint_left.mp h_left_middle hvELeft hvFMiddle
      · exact Finset.disjoint_left.mp h_left_right hvELeft hvFRight
  · rcases Finset.mem_union.mp hvERest with hvEMiddle | hvERight
    · rcases Finset.mem_union.mp hvFSupport with hvFLeft | hvFRest
      · exact Finset.disjoint_left.mp h_middle_left hvEMiddle hvFLeft
      · rcases Finset.mem_union.mp hvFRest with hvFMiddle | hvFRight
        · exact Finset.disjoint_left.mp h_middle_middle hvEMiddle hvFMiddle
        · exact Finset.disjoint_left.mp h_middle_right hvEMiddle hvFRight
    · rcases Finset.mem_union.mp hvFSupport with hvFLeft | hvFRest
      · exact Finset.disjoint_left.mp h_right_left hvERight hvFLeft
      · rcases Finset.mem_union.mp hvFRest with hvFMiddle | hvFRight
        · exact Finset.disjoint_left.mp h_right_middle hvERight hvFMiddle
        · exact Finset.disjoint_left.mp h_right_right hvERight hvFRight

/-- Once the four endpoint coordinates of two transcript edges are pairwise
distinct in the relevant spoke-spoke combinations, all pure spoke interactions
are automatic.  The remaining explicit obligations are exactly the five
interactions involving at least one middle linkage path. -/
theorem walk_dropLast_support_disjoint_of_middle_piece_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e f : Edge F)
    (hleft_left : e.left ≠ f.left)
    (hleft_right : e.left ≠ f.right)
    (hright_left : e.right ≠ f.left)
    (hright_right : e.right ≠ f.right)
    (h_left_middle :
      Disjoint
        ((F.round e.round).leftCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).middlePathOfSourceCoord f.source).vertexSet)
    (h_middle_left :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        ((F.round f.round).leftCanonicalSpokeOfSourceCoord f.source).vertexSet)
    (h_middle_middle :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        ((F.round f.round).middlePathOfSourceCoord f.source).vertexSet)
    (h_middle_right :
      Disjoint
        ((F.round e.round).middlePathOfSourceCoord e.source).vertexSet
        ((F.round f.round).rightCanonicalSpokeOfSourceCoord f.source).vertexSet)
    (h_right_middle :
      Disjoint
        ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet
        ((F.round f.round).middlePathOfSourceCoord f.source).vertexSet) :
    Disjoint e.walk.support.dropLast.toFinset
      f.walk.support.dropLast.toFinset := by
  refine e.walk_dropLast_support_disjoint_of_piecewise_disjoint f ?_
    h_left_middle ?_ h_middle_left h_middle_middle h_middle_right ?_
    h_right_middle ?_
  · simpa [left,
      SelectedOddLocalCrossbarGridTransportedMatchingRound.leftCanonicalSpokeOfSourceCoord]
      using
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_grid_ne
          Hsys hcrossbars hlen (F.cluster e.round) (F.cluster f.round)
          (x := e.left) (y := f.left) hleft_left)
  · simpa [left, right,
      SelectedOddLocalCrossbarGridTransportedMatchingRound.leftCanonicalSpokeOfSourceCoord,
      SelectedOddLocalCrossbarGridTransportedMatchingRound.rightCanonicalSpokeOfSourceCoord]
      using
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_grid_ne
          Hsys hcrossbars hlen (F.cluster e.round) (F.cluster f.round)
          (x := e.left) (y := f.right) hleft_right)
  · simpa [left, right,
      SelectedOddLocalCrossbarGridTransportedMatchingRound.leftCanonicalSpokeOfSourceCoord,
      SelectedOddLocalCrossbarGridTransportedMatchingRound.rightCanonicalSpokeOfSourceCoord]
      using
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_grid_ne
          Hsys hcrossbars hlen (F.cluster e.round) (F.cluster f.round)
          (x := e.right) (y := f.left) hright_left)
  · simpa [right,
      SelectedOddLocalCrossbarGridTransportedMatchingRound.rightCanonicalSpokeOfSourceCoord]
      using
        (selectedOddLocalCrossbarGridTransportedSpokePath_vertexSet_disjoint_of_grid_ne
          Hsys hcrossbars hlen (F.cluster e.round) (F.cluster f.round)
          (x := e.right) (y := f.right) hright_right)

/-- Half-open supports of transcript edges in distinct rounds are disjoint
because the round family assigns distinct selected odd clusters to distinct
rounds. -/
theorem walk_dropLast_support_disjoint_of_round_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e f : Edge F)
    (hround : e.round ≠ f.round) :
    Disjoint e.walk.support.dropLast.toFinset
      f.walk.support.dropLast.toFinset := by
  let ie := oddClusterIndex hlen (F.cluster e.round)
  let jf := oddClusterIndex hlen (F.cluster f.round)
  have hcluster : F.cluster e.round ≠ F.cluster f.round := by
    intro h
    exact hround (F.cluster_injective h)
  have hidx : ie ≠ jf := by
    exact oddClusterIndex_ne_of_ne hlen hcluster
  have hlocal :
      Disjoint (Hsys.hairLocalVertexSet ie) (Hsys.hairLocalVertexSet jf) :=
    Hsys.hairLocalVertexSet_disjoint_of_ne hidx
  have hlocal_hair :
      Disjoint (Hsys.hairLocalVertexSet ie) (Hsys.hairCluster jf) :=
    Hsys.hairLocalVertexSet_disjoint_hairCluster_of_ne hidx
  have hhair_local :
      Disjoint (Hsys.hairCluster ie) (Hsys.hairLocalVertexSet jf) :=
    (Hsys.hairLocalVertexSet_disjoint_hairCluster_of_ne
      (i := jf) (j := ie) hidx.symm).symm
  have hhair :
      Disjoint (Hsys.hairCluster ie) (Hsys.hairCluster jf) :=
    Hsys.hairCluster_disjoint hidx
  refine e.walk_dropLast_support_disjoint_of_piecewise_disjoint f ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hlocal
      (e.leftCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvE)
      (f.leftCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hlocal_hair
      (e.leftCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvE)
      (f.middlePath_vertexSet_subset_hairCluster hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hlocal
      (e.leftCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvE)
      (f.rightCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hhair_local
      (e.middlePath_vertexSet_subset_hairCluster hvE)
      (f.leftCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hhair
      (e.middlePath_vertexSet_subset_hairCluster hvE)
      (f.middlePath_vertexSet_subset_hairCluster hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hhair_local
      (e.middlePath_vertexSet_subset_hairCluster hvE)
      (f.rightCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hlocal
      (e.rightCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvE)
      (f.leftCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hlocal_hair
      (e.rightCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvE)
      (f.middlePath_vertexSet_subset_hairCluster hvF)
  · rw [Finset.disjoint_left]
    intro v hvE hvF
    exact Finset.disjoint_left.mp hlocal
      (e.rightCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvE)
      (f.rightCanonicalSpoke_vertexSet_subset_hairLocalVertexSet hvF)

/-- Half-open supports of two transcript edges in the same round are disjoint
when their left endpoints are distinct.  Inside one round this follows from
cut-side disjointness, injectivity of the matching, and node-disjointness of
the middle linkage. -/
theorem walk_dropLast_support_disjoint_of_same_round_left_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e f : Edge F)
    (hround : e.round = f.round) (hleft : e.left ≠ f.left) :
    Disjoint e.walk.support.dropLast.toFinset
      f.walk.support.dropLast.toFinset := by
  cases e with
  | mk er es =>
  cases f with
  | mk fr fs =>
  dsimp at hround
  subst fr
  have hsource_ne : es ≠ fs := by
    intro h
    exact hleft (by simpa [left] using congrArg Subtype.val h)
  have hleft_right :
      (left (F := F) ⟨er, es⟩) ≠ (right (F := F) ⟨er, fs⟩) := by
    intro h
    have hU : (left (F := F) ⟨er, es⟩) ∈ F.U er := by
      simp [left]
    have hW : (right (F := F) ⟨er, fs⟩) ∈ F.W er :=
      right_mem (F := F) ⟨er, fs⟩
    exact Finset.disjoint_left.mp (F.disjoint er) hU (by simpa [h] using hW)
  have hright_left :
      (right (F := F) ⟨er, es⟩) ≠ (left (F := F) ⟨er, fs⟩) := by
    intro h
    have hW : (right (F := F) ⟨er, es⟩) ∈ F.W er :=
      right_mem (F := F) ⟨er, es⟩
    have hU : (left (F := F) ⟨er, fs⟩) ∈ F.U er := by
      simp [left]
    exact Finset.disjoint_left.mp (F.disjoint er) hU (by simpa [← h] using hW)
  have hright_right :
      (right (F := F) ⟨er, es⟩) ≠ (right (F := F) ⟨er, fs⟩) := by
    intro h
    apply hsource_ne
    apply (F.round er).middleCoordMatching.injective
    exact Subtype.ext (by simpa [right] using h)
  exact walk_dropLast_support_disjoint_of_middle_piece_disjoint
    (F := F) (e := ⟨er, es⟩) (f := ⟨er, fs⟩)
    (by simpa [left] using hleft)
    hleft_right hright_left hright_right
    ((F.round er).leftCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord
      hsource_ne)
    ((F.round er).middlePathOfSourceCoord_vertexSet_disjoint_leftCanonicalSpokeOfSourceCoord
      hsource_ne)
    ((F.round er).middlePathOfSourceCoord_vertexSet_disjoint hsource_ne)
    ((F.round er).middlePathOfSourceCoord_vertexSet_disjoint_rightCanonicalSpokeOfSourceCoord
      hsource_ne)
    ((F.round er).rightCanonicalSpokeOfSourceCoord_vertexSet_disjoint_middlePathOfSourceCoord
      hsource_ne)

/-- Half-open supports assigned to distinct left endpoints are pairwise
disjoint. -/
theorem walk_dropLast_support_disjoint_of_left_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e f : Edge F)
    (hleft : e.left ≠ f.left) :
    Disjoint e.walk.support.dropLast.toFinset
      f.walk.support.dropLast.toFinset := by
  by_cases hround : e.round = f.round
  · exact e.walk_dropLast_support_disjoint_of_same_round_left_ne f hround hleft
  · exact e.walk_dropLast_support_disjoint_of_round_ne f hround

/-- The concrete support of a transcript edge stays in the local footprint for
its round. -/
theorem support_subset_footprint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.support ⊆
      selectedOddLocalCrossbarGridTransportedSpokeTraceImage
          Hsys hcrossbars hlen (F.cluster e.round) (F.U e.round) ∪
        (Hsys.hairCluster (oddClusterIndex hlen (F.cluster e.round)) ∪
          selectedOddLocalCrossbarGridTransportedSpokeTraceImage
            Hsys hcrossbars hlen (F.cluster e.round) (F.W e.round)) := by
  simpa [support] using
    (F.round e.round).matchedCoordinateEdgeSupport_subset_footprint e.source

/-- The half-open walk support also stays in the local footprint for its round. -/
theorem walk_dropLast_support_subset_footprint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.support.dropLast.toFinset ⊆
      selectedOddLocalCrossbarGridTransportedSpokeTraceImage
          Hsys hcrossbars hlen (F.cluster e.round) (F.U e.round) ∪
        (Hsys.hairCluster (oddClusterIndex hlen (F.cluster e.round)) ∪
          selectedOddLocalCrossbarGridTransportedSpokeTraceImage
            Hsys hcrossbars hlen (F.cluster e.round) (F.W e.round)) := by
  intro v hv
  exact e.support_subset_footprint (e.walk_dropLast_support_subset_support hv)

end Edge

/-- The concrete source-allocation branch set for an auxiliary coordinate.

It consists of the full row trace for that coordinate and, for every transcript
edge oriented out of the coordinate, the half-open support of the corresponding
walk with the final target contact removed.  The final edge of such a walk is
then used to witness adjacency to the target coordinate's branch set. -/
noncomputable def sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x : GridVertex g) : Finset V := by
  classical
  exact selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x ∪
    (Finset.univ.biUnion fun e : Edge F =>
      if h : e.left = x then e.walk.support.dropLast.toFinset else ∅)

/-- The row trace is contained in the source-allocation branch set. -/
theorem rowTrace_subset_sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x : GridVertex g) :
    selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x ⊆
      F.sourceAllocatedBranchSet x := by
  classical
  intro v hv
  rw [sourceAllocatedBranchSet]
  exact Finset.mem_union_left _ hv

/-- Membership in a source-allocation branch set is exactly membership in the
row trace or in one of the half-open supports of an outgoing transcript edge. -/
theorem mem_sourceAllocatedBranchSet_iff
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) {x : GridVertex g} {v : V} :
    v ∈ F.sourceAllocatedBranchSet x ↔
      v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x ∨
        ∃ e : Edge F, e.left = x ∧
          v ∈ e.walk.support.dropLast.toFinset := by
  classical
  rw [sourceAllocatedBranchSet, Finset.mem_union]
  constructor
  · intro hv
    rcases hv with hvrow | hvedge
    · exact Or.inl hvrow
    · rw [Finset.mem_biUnion] at hvedge
      rcases hvedge with ⟨e, _he, hvif⟩
      by_cases hleft : e.left = x
      · exact Or.inr ⟨e, hleft, by simpa [hleft] using hvif⟩
      · simp [hleft] at hvif
  · intro hv
    rcases hv with hvrow | hvedge
    · exact Or.inl hvrow
    · rcases hvedge with ⟨e, hleft, hvsupport⟩
      refine Or.inr ?_
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, by
        simpa [hleft] using hvsupport⟩

/-- Disjointness of the concrete source-allocation branch sets follows from the
three geometric separation facts that the construction must provide: distinct
row traces are disjoint, every outgoing half-open support is disjoint from every
other row trace, and half-open supports with distinct left endpoints are
disjoint. -/
theorem sourceAllocatedBranchSet_disjoint_of_trace_and_support_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (row_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    ⦃x y : GridVertex g⦄ (hxy : x ≠ y) :
    Disjoint (F.sourceAllocatedBranchSet x) (F.sourceAllocatedBranchSet y) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  rw [F.mem_sourceAllocatedBranchSet_iff] at hvx hvy
  rcases hvx with hvxRow | hvxSupport
  · rcases hvy with hvyRow | hvySupport
    · exact Finset.disjoint_left.mp (row_disjoint hxy) hvxRow hvyRow
    · rcases hvySupport with ⟨f, hfy, hvf⟩
      exact Finset.disjoint_left.mp (support_row_disjoint f hfy hxy.symm) hvf hvxRow
  · rcases hvxSupport with ⟨e, hex, hve⟩
    rcases hvy with hvyRow | hvySupport
    · exact Finset.disjoint_left.mp (support_row_disjoint e hex hxy) hve hvyRow
    · rcases hvySupport with ⟨f, hfy, hvf⟩
      exact Finset.disjoint_left.mp
        (support_support_disjoint e f hex hfy hxy) hve hvf

/-- The half-open support of an outgoing transcript edge is contained in the
source-allocation branch set of its left endpoint. -/
theorem walk_dropLast_support_subset_sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.support.dropLast.toFinset ⊆ F.sourceAllocatedBranchSet e.left := by
  intro v hv
  rw [F.mem_sourceAllocatedBranchSet_iff]
  exact Or.inr ⟨e, rfl, hv⟩

/-- Source-allocation branch sets are nonempty as soon as at least one selected
odd crossbar is present. -/
theorem sourceAllocatedBranchSet_nonempty
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hm : 0 < m) (x : GridVertex g) :
    (F.sourceAllocatedBranchSet x).Nonempty := by
  rcases selectedOddLocalCrossbarGridRowTrace_nonempty Hsys hcrossbars hlen hm x
    with ⟨v, hv⟩
  exact ⟨v, F.rowTrace_subset_sourceAllocatedBranchSet x hv⟩

/-- Source-allocation branch sets are connected once the row traces are
connected.  The full row trace supplies the anchor; each extra half-open
matched-edge support is connected and meets the row trace at the edge's left
contact. -/
theorem sourceAllocatedBranchSet_connected_of_rowTrace_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hm : 0 < m)
    (rowTrace_connected :
      ∀ x : GridVertex g,
        (G.induce {v : V |
          v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x}).Connected)
    (x : GridVertex g) :
    (G.induce {v : V | v ∈ F.sourceAllocatedBranchSet x}).Connected := by
  classical
  rcases selectedOddLocalCrossbarGridRowTrace_nonempty Hsys hcrossbars hlen hm x with
    ⟨a, haRow⟩
  have haBranch : a ∈ F.sourceAllocatedBranchSet x :=
    F.rowTrace_subset_sourceAllocatedBranchSet x haRow
  refine G.induce_connected_of_patches a haBranch ?_
  intro v hv
  change v ∈ F.sourceAllocatedBranchSet x at hv
  rw [F.mem_sourceAllocatedBranchSet_iff] at hv
  rcases hv with hvRow | hvEdge
  · let S : Set V :=
      {z : V | z ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x}
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact F.rowTrace_subset_sourceAllocatedBranchSet x hz
    · exact haRow
    · exact hvRow
    · simpa [S] using
        (rowTrace_connected x).preconnected ⟨a, haRow⟩ ⟨v, hvRow⟩
  · rcases hvEdge with ⟨e, hleft, hvDrop⟩
    let Srow : Set V :=
      {z : V | z ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x}
    let Sdrop : Set V := {z : V | z ∈ e.walk.support.dropLast.toFinset}
    let S : Set V := Srow ∪ Sdrop
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · intro z hz
      change z ∈ Srow ∪ Sdrop at hz
      change z ∈ F.sourceAllocatedBranchSet x
      rw [F.mem_sourceAllocatedBranchSet_iff]
      rcases hz with hzRow | hzDrop
      · exact Or.inl (by simpa [Srow] using hzRow)
      · exact Or.inr ⟨e, hleft, by simpa [Sdrop] using hzDrop⟩
    · exact Or.inl (by simpa [Srow] using haRow)
    · exact Or.inr (by simpa [Sdrop] using hvDrop)
    · have hleftRow : e.leftContact ∈ Srow := by
        simpa [Srow, hleft] using e.leftContact_mem_rowTrace
      have hleftDrop : e.leftContact ∈ Sdrop := by
        simpa [Sdrop] using e.leftContact_mem_walk_dropLast_support
      have hrowConn : (G.induce Srow).Connected := by
        simpa [Srow] using rowTrace_connected x
      have hdropConn : (G.induce Sdrop).Connected := by
        simpa [Sdrop] using e.walk_dropLast_support_connected
      have hconn : (G.induce S).Connected := by
        simpa [S] using
          G.induce_union_connected hrowConn.preconnected hdropConn.preconnected
            ⟨e.leftContact, hleftRow, hleftDrop⟩
      exact hconn.preconnected
        ⟨a, Or.inl (by simpa [Srow] using haRow)⟩
        ⟨v, Or.inr (by simpa [Sdrop] using hvDrop)⟩

/-- The left contact of every transcript edge lies in the source-allocation
branch set of its left endpoint. -/
theorem leftContact_mem_sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.leftContact ∈ F.sourceAllocatedBranchSet e.left :=
  F.rowTrace_subset_sourceAllocatedBranchSet e.left e.leftContact_mem_rowTrace

/-- The right contact of every transcript edge lies in the source-allocation
branch set of its right endpoint, because the full row trace is included. -/
theorem rightContact_mem_sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.rightContact ∈ F.sourceAllocatedBranchSet e.right :=
  F.rowTrace_subset_sourceAllocatedBranchSet e.right e.rightContact_mem_rowTrace

/-- The penultimate vertex of every transcript edge's supporting walk lies in
the source-allocation branch set of its left endpoint. -/
theorem walk_penultimate_mem_sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) :
    e.walk.penultimate ∈ F.sourceAllocatedBranchSet e.left := by
  exact walk_dropLast_support_subset_sourceAllocatedBranchSet e
    e.walk_penultimate_mem_dropLast_support

/-- The unique oriented edge of a full cut-matching round incident with a
coordinate: if the coordinate lies on the left side, orient from it; otherwise
use the inverse matching from the right side. -/
noncomputable def edgeOfRoundVertex
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (r : F.Index) (x : GridVertex g) : Edge F :=
  if hx : x ∈ F.U r then
    ⟨r, ⟨x, hx⟩⟩
  else
    have hw : x ∈ F.W r := by
      have hxUW : x ∈ F.U r ∪ F.W r := by
        simp [hcover r]
      exact (Finset.mem_union.mp hxUW).resolve_left hx
    ⟨r, (F.round r).middleCoordMatching.symm ⟨x, hw⟩⟩

/-- The edge selected for a round and coordinate is incident with that
coordinate. -/
theorem edgeOfRoundVertex_incident
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (r : F.Index) (x : GridVertex g) :
    (F.edgeOfRoundVertex hcover r x).Incident x := by
  classical
  unfold edgeOfRoundVertex
  by_cases hx : x ∈ F.U r
  · rw [dif_pos hx]
    exact Or.inl rfl
  · rw [dif_neg hx]
    right
    simp [Edge.right]

/-- The edge selected for a round and coordinate belongs to that round. -/
@[simp] theorem edgeOfRoundVertex_round
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (r : F.Index) (x : GridVertex g) :
    (F.edgeOfRoundVertex hcover r x).round = r := by
  classical
  unfold edgeOfRoundVertex
  by_cases hx : x ∈ F.U r
  · simp [hx]
  · simp [hx]

/-- If a coordinate lies on the left side of a round cut, the selected
incident edge is the edge oriented out of that coordinate. -/
theorem edgeOfRoundVertex_of_mem_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    {r : F.Index} {x : GridVertex g} (hx : x ∈ F.U r) :
    F.edgeOfRoundVertex hcover r x = ⟨r, ⟨x, hx⟩⟩ := by
  classical
  unfold edgeOfRoundVertex
  simp [hx]

/-- If a coordinate is not on the left side of a full round cut, the selected
incident edge is the inverse image of that coordinate under the matching. -/
theorem edgeOfRoundVertex_of_not_mem_left
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    {r : F.Index} {x : GridVertex g} (hx : x ∉ F.U r) :
    F.edgeOfRoundVertex hcover r x =
      ⟨r, (F.round r).middleCoordMatching.symm
        ⟨x, by
          have hxUW : x ∈ F.U r ∪ F.W r := by
            simp [hcover r]
          exact (Finset.mem_union.mp hxUW).resolve_left hx⟩⟩ := by
  classical
  unfold edgeOfRoundVertex
  simp [hx]

/-- An edge of the transcript is the unique edge in its round incident with a
given coordinate.  This is the Lean form of the paper's statement that each
cut-matching round contributes a perfect matching to the auxiliary multigraph. -/
theorem edge_eq_edgeOfRoundVertex_of_incident
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (e : Edge F) {x : GridVertex g} (hx : e.Incident x) :
    e = F.edgeOfRoundVertex hcover e.round x := by
  classical
  rcases e with ⟨r, source⟩
  rcases source with ⟨source, hsource⟩
  rcases hx with hleft | hright
  · simp [Edge.left] at hleft
    subst x
    rw [edgeOfRoundVertex_of_mem_left F hcover hsource]
  · simp [Edge.right] at hright
    have hxW : x ∈ F.W r := by
      rw [← hright]
      exact ((F.round r).middleCoordMatching ⟨source, hsource⟩).2
    have hxU : x ∉ F.U r := by
      intro hxU
      exact Finset.disjoint_left.mp (F.disjoint r) hxU hxW
    rw [edgeOfRoundVertex_of_not_mem_left F hcover hxU]
    have hmatch :
        (F.round r).middleCoordMatching ⟨source, hsource⟩ = ⟨x, hxW⟩ := by
      apply Subtype.ext
      exact hright
    have hsource_eq :
        (F.round r).middleCoordMatching.symm ⟨x, hxW⟩ =
          ⟨source, hsource⟩ := by
      rw [← hmatch]
      simp
    rw [hsource_eq]

/-- The finite type of transcript edges incident with a coordinate. -/
abbrev IncidentEdge
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x : GridVertex g) : Type u :=
  {e : Edge F // e.Incident x}

noncomputable instance incidentEdgeFintype
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (x : GridVertex g) :
    Fintype (IncidentEdge F x) := by
  classical
  infer_instance

/-- For a full cut transcript, incident transcript edges at a fixed coordinate
are equivalent to rounds.  Thus the auxiliary multigraph is exactly
`|Index|`-regular as a multigraph, not just bounded-degree after simplifying
parallel edges. -/
noncomputable def incidentEdgeEquivRound
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (x : GridVertex g) :
    IncidentEdge F x ≃ F.Index where
  toFun := fun e => e.1.round
  invFun := fun r =>
    ⟨F.edgeOfRoundVertex hcover r x, F.edgeOfRoundVertex_incident hcover r x⟩
  left_inv := by
    intro e
    apply Subtype.ext
    exact (edge_eq_edgeOfRoundVertex_of_incident F hcover e.1 e.2).symm
  right_inv := by
    intro r
    exact F.edgeOfRoundVertex_round hcover r x

/-- A full cut transcript has exactly one incident multigraph edge per round at
every coordinate. -/
theorem incidentEdge_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (x : GridVertex g) :
    Fintype.card (IncidentEdge F x) = Fintype.card F.Index := by
  classical
  exact Fintype.card_congr (F.incidentEdgeEquivRound hcover x)

/-- In a full equal cut, each side has half of the coordinate vertices.  This
is the cardinal arithmetic behind the cut-matching game requirement
`|Z_j| = |Z'_j|`. -/
theorem leftCut_card_mul_two_eq_gridVertex_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll) (r : F.Index) :
    2 * (F.U r).card = Fintype.card (GridVertex g) := by
  classical
  have hsum :
      (F.U r).card + (F.W r).card = Fintype.card (GridVertex g) := by
    have hcard_union := Finset.card_union_of_disjoint (F.disjoint r)
    rw [← hcard_union, hcover r]
    simp
  have hcard_eq := F.card_eq r
  omega

/-- The right side of every full equal cut also has half of the coordinate
vertices. -/
theorem rightCut_card_mul_two_eq_gridVertex_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll) (r : F.Index) :
    2 * (F.W r).card = Fintype.card (GridVertex g) := by
  have hleft := F.leftCut_card_mul_two_eq_gridVertex_card hcover r
  have hcard_eq := F.card_eq r
  omega

/-- An edge of the auxiliary simple graph is represented by a concrete
edge-instance of the paper's auxiliary multigraph. -/
theorem auxGraph_adj_exists_edge
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) {x y : GridVertex g}
    (hxy : F.auxGraph.Adj x y) :
    ∃ e : Edge F, (e.left = x ∧ e.right = y) ∨
      (e.left = y ∧ e.right = x) := by
  rw [F.auxGraph_adj_iff] at hxy
  rcases hxy with ⟨r, hrxy⟩
  change ((F.round r).coordinateMatchingGraph (F.disjoint r)).Adj x y at hrxy
  rw [(F.round r).coordinateMatchingGraph_adj_iff (F.disjoint r)] at hrxy
  rcases hrxy with ⟨hx, hmatch⟩ | ⟨hy, hmatch⟩
  · exact ⟨⟨r, ⟨x, hx⟩⟩, Or.inl ⟨rfl, hmatch⟩⟩
  · exact ⟨⟨r, ⟨y, hy⟩⟩, Or.inr ⟨rfl, hmatch⟩⟩

/-- Every edge of the simplified auxiliary graph is backed by a transcript edge
with concrete row contacts and a connected support in the host graph. -/
theorem auxGraph_adj_exists_edge_connected_support
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) {x y : GridVertex g}
    (hxy : F.auxGraph.Adj x y) :
    ∃ e : Edge F,
      ((e.left = x ∧ e.right = y) ∨ (e.left = y ∧ e.right = x)) ∧
        e.leftContact ∈
          selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.left ∧
        e.rightContact ∈
          selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right ∧
        e.leftContact ∈ e.support ∧
        e.rightContact ∈ e.support ∧
        (G.induce {v : V | v ∈ e.support}).Connected := by
  rcases F.auxGraph_adj_exists_edge hxy with ⟨e, horient⟩
  exact ⟨e, horient, e.leftContact_mem_rowTrace, e.rightContact_mem_rowTrace,
    e.leftContact_mem_support, e.rightContact_mem_support, e.support_connected⟩

/-- A transcript edge crosses a coordinate set when exactly one endpoint lies
in the set. -/
def Edge.Crosses
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) (S : Finset (GridVertex g)) : Prop :=
  (e.left ∈ S ∧ e.right ∉ S) ∨ (e.right ∈ S ∧ e.left ∉ S)

/-- Boundary edges of a coordinate set in the edge-indexed auxiliary
multigraph.  This is the object counted in the cut-matching expander argument,
before parallel edges are forgotten by `auxGraph`. -/
noncomputable def edgeBoundary
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (S : Finset (GridVertex g)) : Finset (Edge F) :=
  by
    classical
    exact Finset.univ.filter fun e : Edge F => e.Crosses S

/-- Membership in the multigraph edge boundary. -/
theorem mem_edgeBoundary
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (S : Finset (GridVertex g)) (e : Edge F) :
    e ∈ F.edgeBoundary S ↔ e.Crosses S := by
  classical
  simp [edgeBoundary]

@[simp] theorem edgeBoundary_empty
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) :
    F.edgeBoundary (∅ : Finset (GridVertex g)) = ∅ := by
  classical
  ext e
  simp [mem_edgeBoundary, Edge.Crosses]

@[simp] theorem edgeBoundary_univ
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) :
    F.edgeBoundary (Finset.univ : Finset (GridVertex g)) = ∅ := by
  classical
  ext e
  simp [mem_edgeBoundary, Edge.Crosses]

/-- Incidence pairs over a coordinate set: a vertex in the set together with a
transcript edge incident with it.  Boundary edges inject into these pairs by
choosing their endpoint inside the set. -/
abbrev IncidentPairInSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (S : Finset (GridVertex g)) : Type u :=
  Σ x : {x : GridVertex g // x ∈ S}, IncidentEdge F x.1

/-- In a full cut transcript, incidence pairs over `S` are counted by
`|S| * |rounds|`. -/
theorem incidentPairInSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (S : Finset (GridVertex g)) :
    Fintype.card (IncidentPairInSet F S) =
      S.card * Fintype.card F.Index := by
  classical
  rw [Fintype.card_sigma]
  simp [incidentEdge_card F hcover]

/-- Choose the endpoint inside `S` of a boundary edge, recording the edge as
incident with that endpoint. -/
noncomputable def edgeBoundaryInsideIncident
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (S : Finset (GridVertex g))
    (e : {e : Edge F // e ∈ F.edgeBoundary S}) :
    IncidentPairInSet F S := by
  classical
  have hcross : e.1.Crosses S := (F.mem_edgeBoundary S e.1).1 e.2
  by_cases hleft : e.1.left ∈ S
  · exact ⟨⟨e.1.left, hleft⟩, ⟨e.1, Or.inl rfl⟩⟩
  · have hright : e.1.right ∈ S := by
      rcases hcross with ⟨hinside, _houtside⟩ | ⟨hinside, _houtside⟩
      · exact False.elim (hleft hinside)
      · exact hinside
    exact ⟨⟨e.1.right, hright⟩, ⟨e.1, Or.inr rfl⟩⟩

/-- The inside-endpoint map for boundary edges is injective because it records
the original transcript edge in the second component. -/
theorem edgeBoundaryInsideIncident_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (S : Finset (GridVertex g)) :
    Function.Injective (F.edgeBoundaryInsideIncident S) := by
  classical
  intro e e' h
  apply Subtype.ext
  have hedge :
      (F.edgeBoundaryInsideIncident S e).2.1 =
        (F.edgeBoundaryInsideIncident S e').2.1 :=
    congrArg (fun p : IncidentPairInSet F S => (p.2.1 : Edge F)) h
  have hedge_left : (F.edgeBoundaryInsideIncident S e).2.1 = e.1 := by
    unfold edgeBoundaryInsideIncident
    by_cases hleft : e.1.left ∈ S
    · rw [dif_pos hleft]
    · rw [dif_neg hleft]
  have hedge_right : (F.edgeBoundaryInsideIncident S e').2.1 = e'.1 := by
    unfold edgeBoundaryInsideIncident
    by_cases hleft : e'.1.left ∈ S
    · rw [dif_pos hleft]
    · rw [dif_neg hleft]
  exact hedge_left.symm.trans (hedge.trans hedge_right)

/-- The elementary boundary-counting upper bound for the auxiliary multigraph:
each boundary edge is charged to its unique endpoint inside `S`, and each
coordinate has exactly one incident transcript edge per round. -/
theorem edgeBoundary_card_le_card_mul_rounds
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcover : F.CoversAll)
    (S : Finset (GridVertex g)) :
    (F.edgeBoundary S).card ≤ S.card * Fintype.card F.Index := by
  classical
  have hle :
      Fintype.card {e : Edge F // e ∈ F.edgeBoundary S} ≤
        Fintype.card (IncidentPairInSet F S) :=
    Fintype.card_le_of_injective (F.edgeBoundaryInsideIncident S)
      (F.edgeBoundaryInsideIncident_injective S)
  have hdomain :
      Fintype.card {e : Edge F // e ∈ F.edgeBoundary S} =
        (F.edgeBoundary S).card := by
    rw [Fintype.card_subtype]
    simp
  have hcodomain :
      Fintype.card (IncidentPairInSet F S) =
        S.card * Fintype.card F.Index :=
    F.incidentPairInSet_card hcover S
  simpa [hdomain, hcodomain] using hle

/-- Charge a boundary edge of `A` to its endpoint in a separator `S`, assuming
`A` and `B` are separated in the simplified auxiliary graph and
`A ∪ B ∪ S` covers all coordinates. -/
noncomputable def edgeBoundaryOutsideSeparatorIncident
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen)
    (A B S : Finset (GridVertex g))
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hnoAB : ∀ ⦃a b : GridVertex g⦄, a ∈ A → b ∈ B →
      ¬ F.auxGraph.Adj a b)
    (e : {e : Edge F // e ∈ F.edgeBoundary A}) :
    IncidentPairInSet F S := by
  classical
  have hcross : e.1.Crosses A := (F.mem_edgeBoundary A e.1).1 e.2
  by_cases hleftA : e.1.left ∈ A
  · have hrightNotA : e.1.right ∉ A := by
      rcases hcross with ⟨_hleft, hright⟩ | ⟨hright, hleft⟩
      · exact hright
      · exact False.elim (hleft hleftA)
    have hrightNotB : e.1.right ∉ B := by
      intro hrightB
      exact hnoAB hleftA hrightB e.1.auxGraph_adj
    have hrightS : e.1.right ∈ S := by
      have hmem : e.1.right ∈ A ∪ B ∪ S := by
        rw [hcover]
        simp
      rcases Finset.mem_union.mp hmem with hAB | hS
      · rcases Finset.mem_union.mp hAB with hA | hB
        · exact False.elim (hrightNotA hA)
        · exact False.elim (hrightNotB hB)
      · exact hS
    exact ⟨⟨e.1.right, hrightS⟩, ⟨e.1, Or.inr rfl⟩⟩
  · have hrightA : e.1.right ∈ A := by
      rcases hcross with ⟨hleft, _hright⟩ | ⟨hright, _hleft⟩
      · exact False.elim (hleftA hleft)
      · exact hright
    have hleftNotB : e.1.left ∉ B := by
      intro hleftB
      exact hnoAB hrightA hleftB (F.auxGraph.symm e.1.auxGraph_adj)
    have hleftS : e.1.left ∈ S := by
      have hmem : e.1.left ∈ A ∪ B ∪ S := by
        rw [hcover]
        simp
      rcases Finset.mem_union.mp hmem with hAB | hS
      · rcases Finset.mem_union.mp hAB with hA | hB
        · exact False.elim (hleftA hA)
        · exact False.elim (hleftNotB hB)
      · exact hS
    exact ⟨⟨e.1.left, hleftS⟩, ⟨e.1, Or.inl rfl⟩⟩

/-- The separator-endpoint map for boundary edges is injective because it
records the original transcript edge in the second component. -/
theorem edgeBoundaryOutsideSeparatorIncident_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen)
    (A B S : Finset (GridVertex g))
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hnoAB : ∀ ⦃a b : GridVertex g⦄, a ∈ A → b ∈ B →
      ¬ F.auxGraph.Adj a b) :
    Function.Injective
      (F.edgeBoundaryOutsideSeparatorIncident A B S hcover hnoAB) := by
  classical
  intro e e' h
  apply Subtype.ext
  have hedge :
      (F.edgeBoundaryOutsideSeparatorIncident A B S hcover hnoAB e).2.1 =
        (F.edgeBoundaryOutsideSeparatorIncident A B S hcover hnoAB e').2.1 :=
    congrArg (fun p : IncidentPairInSet F S => (p.2.1 : Edge F)) h
  have hedge_left :
      (F.edgeBoundaryOutsideSeparatorIncident A B S hcover hnoAB e).2.1 = e.1 := by
    unfold edgeBoundaryOutsideSeparatorIncident
    by_cases hleft : e.1.left ∈ A
    · rw [dif_pos hleft]
    · rw [dif_neg hleft]
  have hedge_right :
      (F.edgeBoundaryOutsideSeparatorIncident A B S hcover hnoAB e').2.1 = e'.1 := by
    unfold edgeBoundaryOutsideSeparatorIncident
    by_cases hleft : e'.1.left ∈ A
    · rw [dif_pos hleft]
    · rw [dif_neg hleft]
  exact hedge_left.symm.trans (hedge.trans hedge_right)

/-- If all auxiliary edges from `A` to the outside of `A` must enter a separator
`S`, then the edge-indexed boundary of `A` is bounded by
`|S| * |rounds|`. -/
theorem edgeBoundary_card_le_separator_card_mul_rounds
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hcutCover : F.CoversAll)
    (A B S : Finset (GridVertex g))
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hnoAB : ∀ ⦃a b : GridVertex g⦄, a ∈ A → b ∈ B →
      ¬ F.auxGraph.Adj a b) :
    (F.edgeBoundary A).card ≤ S.card * Fintype.card F.Index := by
  classical
  have hle :
      Fintype.card {e : Edge F // e ∈ F.edgeBoundary A} ≤
        Fintype.card (IncidentPairInSet F S) :=
    Fintype.card_le_of_injective
      (F.edgeBoundaryOutsideSeparatorIncident A B S hcover hnoAB)
      (F.edgeBoundaryOutsideSeparatorIncident_injective A B S hcover hnoAB)
  have hdomain :
      Fintype.card {e : Edge F // e ∈ F.edgeBoundary A} =
        (F.edgeBoundary A).card := by
    rw [Fintype.card_subtype]
    simp
  have hcodomain :
      Fintype.card (IncidentPairInSet F S) =
        S.card * Fintype.card F.Index :=
    F.incidentPairInSet_card hcutCover S
  simpa [hdomain, hcodomain] using hle

/-- Rational edge expansion for the edge-indexed auxiliary multigraph.  The
parameters represent `numerator / denominator`; for example `1 / 2` expansion
is stated as `S.card <= 2 * (edgeBoundary S).card` for every nonempty
`S` of size at most half the vertex set. -/
def IsEdgeExpanderWith
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (numerator denominator : ℕ) : Prop :=
  0 < denominator ∧
    ∀ S : Finset (GridVertex g), 0 < S.card →
      2 * S.card ≤ Fintype.card (GridVertex g) →
        numerator * S.card ≤ denominator * (F.edgeBoundary S).card

/-- The `1/2`-expansion conclusion used in Lemma 3.3. -/
def IsHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) : Prop :=
  F.IsEdgeExpanderWith 1 2

/-- Unfold the `1/2`-edge-expander predicate into the natural-number
inequality used by subsequent counting arguments. -/
theorem isHalfEdgeExpander_iff
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) :
    F.IsHalfEdgeExpander ↔
      ∀ S : Finset (GridVertex g), 0 < S.card →
        2 * S.card ≤ Fintype.card (GridVertex g) →
          S.card ≤ 2 * (F.edgeBoundary S).card := by
  constructor
  · intro h S hS hhalf
    have hbound := h.2 S hS hhalf
    simpa [IsHalfEdgeExpander, IsEdgeExpanderWith] using hbound
  · intro h
    refine ⟨by decide, ?_⟩
    intro S hS hhalf
    simpa [IsHalfEdgeExpander, IsEdgeExpanderWith] using h S hS hhalf

/-- A nonempty small cut in a half-expander has at least one transcript edge
crossing it. -/
theorem edgeBoundary_nonempty_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander)
    {S : Finset (GridVertex g)} (hS : 0 < S.card)
    (hhalf : 2 * S.card ≤ Fintype.card (GridVertex g)) :
    (F.edgeBoundary S).Nonempty := by
  rw [F.isHalfEdgeExpander_iff] at hexp
  have hbound := hexp S hS hhalf
  have hpos : 0 < (F.edgeBoundary S).card := by
    by_contra hnot
    have hzero : (F.edgeBoundary S).card = 0 := Nat.eq_zero_of_not_pos hnot
    omega
  exact Finset.card_pos.mp hpos

/-- A half-expander cut has an actual edge of the simplified auxiliary graph
from the inside to the outside. -/
theorem exists_auxGraph_adj_crossing_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander)
    {S : Finset (GridVertex g)} (hS : 0 < S.card)
    (hhalf : 2 * S.card ≤ Fintype.card (GridVertex g)) :
    ∃ x ∈ S, ∃ y ∉ S, F.auxGraph.Adj x y := by
  rcases F.edgeBoundary_nonempty_of_isHalfEdgeExpander hexp hS hhalf with
    ⟨e, he⟩
  have hcross : e.Crosses S := (F.mem_edgeBoundary S e).1 he
  rcases hcross with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · exact ⟨e.left, hleft, e.right, hright, e.auxGraph_adj⟩
  · exact ⟨e.right, hright, e.left, hleft, F.auxGraph.symm e.auxGraph_adj⟩

/-- The simplified auxiliary graph of a half-expander transcript is
preconnected.  The proof is the standard reachable-set cut argument: if `b`
is not reachable from `a`, the set of vertices reachable from `a` is a
nonempty proper cut; applying expansion to this set, or to its complement when
the reachable side is larger than half, gives an auxiliary edge that extends
the reachable set, a contradiction. -/
theorem auxGraph_preconnected_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander) :
    F.auxGraph.Preconnected := by
  classical
  intro a b
  by_cases hab : F.auxGraph.Reachable a b
  · exact hab
  · let S : Finset (GridVertex g) :=
      Finset.univ.filter fun z : GridVertex g => F.auxGraph.Reachable a z
    have haS : a ∈ S := by
      simp [S]
    have hbNotS : b ∉ S := by
      simpa [S] using hab
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨a, haS⟩
    by_cases hsmall : 2 * S.card ≤ Fintype.card (GridVertex g)
    · rcases F.exists_auxGraph_adj_crossing_of_isHalfEdgeExpander
          hexp hSpos hsmall with
        ⟨x, hxS, y, hyNotS, hxy⟩
      have hax : F.auxGraph.Reachable a x := by
        simpa [S] using hxS
      have hay : F.auxGraph.Reachable a y := hax.trans hxy.reachable
      have hyS : y ∈ S := by
        simp [S, hay]
      exact (hyNotS hyS).elim
    · let T : Finset (GridVertex g) := Finset.univ \ S
      have hbT : b ∈ T := by
        simp [T, hbNotS]
      have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨b, hbT⟩
      have hTcard : T.card + S.card = Fintype.card (GridVertex g) := by
        simpa [T] using
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      have hlarge : Fintype.card (GridVertex g) < 2 * S.card :=
        Nat.lt_of_not_ge hsmall
      have hThalf : 2 * T.card ≤ Fintype.card (GridVertex g) := by
        omega
      rcases F.exists_auxGraph_adj_crossing_of_isHalfEdgeExpander
          hexp hTpos hThalf with
        ⟨x, hxT, y, hyNotT, hxy⟩
      have hxNotS : x ∉ S := by
        simpa [T] using hxT
      have hyS : y ∈ S := by
        by_contra hyNotS
        exact hyNotT (by simp [T, hyNotS])
      have hay : F.auxGraph.Reachable a y := by
        simpa [S] using hyS
      have hax : F.auxGraph.Reachable a x := hay.trans hxy.symm.reachable
      have hxS : x ∈ S := by
        simp [S, hax]
      exact (hxNotS hxS).elim

/-- A nonempty half-expander transcript has connected simplified auxiliary
graph. -/
theorem auxGraph_connected_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander)
    [Nonempty (GridVertex g)] :
    F.auxGraph.Connected where
  preconnected := F.auxGraph_preconnected_of_isHalfEdgeExpander hexp

/-- In a nontrivial half-expander transcript, every coordinate has an
auxiliary neighbor. -/
theorem exists_auxGraph_neighbor_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) (x : GridVertex g) :
    ∃ y : GridVertex g, F.auxGraph.Adj x y := by
  let S : Finset (GridVertex g) := {x}
  have hS : 0 < S.card := by
    simp [S]
  have hhalf : 2 * S.card ≤ Fintype.card (GridVertex g) := by
    simpa [S] using hcard
  rcases F.exists_auxGraph_adj_crossing_of_isHalfEdgeExpander
      hexp hS hhalf with
    ⟨z, hzS, y, _hyNotS, hzy⟩
  have hzx : z = x := by
    simpa [S] using hzS
  exact ⟨y, by simpa [hzx] using hzy⟩

/-- The explicit neighbor finset is nonempty at every coordinate of a
nontrivial half-expander transcript. -/
theorem neighborFinset_nonempty_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) (x : GridVertex g) :
    (F.neighborFinset x).Nonempty := by
  rcases F.exists_auxGraph_neighbor_of_isHalfEdgeExpander hexp hcard x with
    ⟨y, hxy⟩
  exact ⟨y, ((F.neighborFinset_isNeighbor x) y).2 hxy⟩

/-- A nontrivial half-expander transcript must contain at least one
cut-matching round. -/
theorem index_nonempty_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) :
    Nonempty F.Index := by
  classical
  have hcardPos : 0 < Fintype.card (GridVertex g) := by
    omega
  haveI : Nonempty (GridVertex g) := Fintype.card_pos_iff.mp hcardPos
  let x : GridVertex g := Classical.choice inferInstance
  rcases F.exists_auxGraph_neighbor_of_isHalfEdgeExpander hexp hcard x with
    ⟨y, hxy⟩
  rcases F.auxGraph_adj_exists_edge hxy with ⟨e, _he⟩
  exact ⟨e.round⟩

/-- A nontrivial half-expander transcript has a positive number of
cut-matching rounds. -/
theorem index_card_pos_of_isHalfEdgeExpander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (hexp : F.IsHalfEdgeExpander)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) :
    0 < Fintype.card F.Index :=
  Fintype.card_pos_iff.mpr (F.index_nonempty_of_isHalfEdgeExpander hexp hcard)

/-- A completed cut-matching game transcript on the coordinate set, keeping the
two properties used after Theorem 3.4: all cuts are full bisections and the
resulting edge-indexed auxiliary multigraph is a `1/2`-expander. -/
structure CutMatchingGameCertificate
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (roundBound : ℕ) where
  /-- Every cut partitions the full coordinate set. -/
  coversAll : F.CoversAll
  /-- The number of cut-matching rounds is within the chosen bound. -/
  round_count_le : Fintype.card F.Index ≤ roundBound
  /-- The resulting edge-indexed auxiliary multigraph is a `1/2`-expander. -/
  half_expander : F.IsHalfEdgeExpander

/-- If the cut-matching transcript uses at most `d` rounds, then the simplified
auxiliary graph has maximum degree at most `d`. -/
theorem auxGraph_maxDegreeAtMost_of_round_count_le
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) {d : ℕ}
    (hrounds : Fintype.card F.Index ≤ d) :
    MaxDegreeAtMost F.auxGraph d := by
  intro x
  rcases F.auxGraph_degreeAtMost_card x with ⟨N, hN, hcard⟩
  exact ⟨N, hN, hcard.trans hrounds⟩

namespace CutMatchingGameCertificate

/-- The degree bound on the simplified auxiliary graph supplied by a completed
cut-matching game certificate. -/
theorem auxGraph_maxDegreeAtMost
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound) :
    MaxDegreeAtMost F.auxGraph roundBound :=
  F.auxGraph_maxDegreeAtMost_of_round_count_le C.round_count_le

/-- The simplified auxiliary graph supplied by a completed cut-matching game
certificate is preconnected. -/
theorem auxGraph_preconnected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound) :
    F.auxGraph.Preconnected :=
  F.auxGraph_preconnected_of_isHalfEdgeExpander C.half_expander

/-- If the coordinate set is nonempty, the simplified auxiliary graph supplied
by a completed cut-matching game certificate is connected. -/
theorem auxGraph_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    [Nonempty (GridVertex g)] :
    F.auxGraph.Connected :=
  F.auxGraph_connected_of_isHalfEdgeExpander C.half_expander

/-- In a nontrivial coordinate set, every vertex of the simplified auxiliary
graph supplied by a completed cut-matching game certificate has a neighbor. -/
theorem exists_auxGraph_neighbor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) (x : GridVertex g) :
    ∃ y : GridVertex g, F.auxGraph.Adj x y :=
  F.exists_auxGraph_neighbor_of_isHalfEdgeExpander C.half_expander hcard x

/-- The explicit neighbor finset is nonempty at every coordinate of a
nontrivial completed cut-matching game certificate. -/
theorem neighborFinset_nonempty
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) (x : GridVertex g) :
    (F.neighborFinset x).Nonempty :=
  F.neighborFinset_nonempty_of_isHalfEdgeExpander C.half_expander hcard x

/-- A completed cut-matching game transcript on a nontrivial coordinate set has
a positive round bound. -/
theorem roundBound_pos
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) :
    0 < roundBound :=
  (F.index_card_pos_of_isHalfEdgeExpander C.half_expander hcard).trans_le
    C.round_count_le

/-- Separator counting in the auxiliary expander.  If `A` and `B` are separated
by `S`, `A` is the smaller of the two sides, and `A` is nonempty, then
half-expansion and the per-round incidence bound force
`|A| <= 2 * |S| * |rounds|`. -/
theorem separator_left_card_le_two_mul_separator_card_mul_rounds
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    {A B S : Finset (GridVertex g)}
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hAB : Disjoint A B)
    (hAleB : A.card ≤ B.card)
    (hApos : 0 < A.card)
    (hnoAB : ∀ ⦃a b : GridVertex g⦄, a ∈ A → b ∈ B →
      ¬ F.auxGraph.Adj a b) :
    A.card ≤ 2 * (S.card * Fintype.card F.Index) := by
  classical
  have hABle : A.card + B.card ≤ Fintype.card (GridVertex g) := by
    have hle : (A ∪ B).card ≤ Fintype.card (GridVertex g) := by
      simpa using Finset.card_le_card (Finset.subset_univ (A ∪ B))
    have hcardUnion : (A ∪ B).card = A.card + B.card :=
      Finset.card_union_of_disjoint hAB
    simpa [hcardUnion] using hle
  have hhalf : 2 * A.card ≤ Fintype.card (GridVertex g) := by
    omega
  have hExp :
      A.card ≤ 2 * (F.edgeBoundary A).card :=
    (F.isHalfEdgeExpander_iff.mp C.half_expander) A hApos hhalf
  have hBoundary :
      (F.edgeBoundary A).card ≤ S.card * Fintype.card F.Index :=
    F.edgeBoundary_card_le_separator_card_mul_rounds C.coversAll
      A B S hcover hnoAB
  exact hExp.trans (Nat.mul_le_mul_left 2 hBoundary)

/-- Version of the separator-counting bound using the external round bound
stored in the cut-matching game certificate. -/
theorem separator_left_card_le_two_mul_separator_card_mul_roundBound
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    {A B S : Finset (GridVertex g)}
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hAB : Disjoint A B)
    (hAleB : A.card ≤ B.card)
    (hApos : 0 < A.card)
    (hnoAB : ∀ ⦃a b : GridVertex g⦄, a ∈ A → b ∈ B →
      ¬ F.auxGraph.Adj a b) :
    A.card ≤ 2 * (S.card * roundBound) := by
  have hrounds :
      S.card * Fintype.card F.Index ≤ S.card * roundBound :=
    Nat.mul_le_mul_left S.card C.round_count_le
  exact
    (C.separator_left_card_le_two_mul_separator_card_mul_rounds
      hcover hAB hAleB hApos hnoAB).trans
        (Nat.mul_le_mul_left 2 hrounds)

/-- The separator contradiction used in the expander-to-grid-minor handoff.
If `A`, `B`, `S` partition the auxiliary vertices, there is no auxiliary edge
from `A` to `B`, `A` is the smaller side, `B` is at most `2N/3`, and `S` is
smaller than `N / (24d)` where `d` is the round bound, then the half-expansion
counting bound is impossible.  Division is avoided by writing the smallness
condition as `24 * (|S| * d) < N`. -/
theorem not_small_balanced_separator
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    {A B S : Finset (GridVertex g)}
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hAB : Disjoint A B)
    (hAS : Disjoint A S)
    (hBS : Disjoint B S)
    (hAleB : A.card ≤ B.card)
    (hBbalanced : 3 * B.card ≤ 2 * Fintype.card (GridVertex g))
    (hApos : 0 < A.card)
    (hnoAB : ∀ ⦃a b : GridVertex g⦄, a ∈ A → b ∈ B →
      ¬ F.auxGraph.Adj a b)
    (hroundPos : 0 < roundBound)
    (hsmall : 24 * (S.card * roundBound) <
      Fintype.card (GridVertex g)) :
    False := by
  classical
  have hAB_S : Disjoint (A ∪ B) S := by
    rw [Finset.disjoint_left]
    intro x hx hSx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact Finset.disjoint_left.mp hAS hxA hSx
    · exact Finset.disjoint_left.mp hBS hxB hSx
  have hcardAB : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hAB
  have hcardABS : ((A ∪ B) ∪ S).card = (A ∪ B).card + S.card :=
    Finset.card_union_of_disjoint hAB_S
  have hcardCover :
      ((A ∪ B) ∪ S).card = Fintype.card (GridVertex g) := by
    rw [hcover]
    simp
  have hcardPartition :
      A.card + B.card + S.card = Fintype.card (GridVertex g) := by
    omega
  have hSleProduct : S.card ≤ S.card * roundBound :=
    Nat.le_mul_of_pos_right S.card hroundPos
  have hSsmall :
      24 * S.card < Fintype.card (GridVertex g) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 24 hSleProduct) hsmall
  have hNle6A : Fintype.card (GridVertex g) ≤ 6 * A.card := by
    omega
  have hUpper :
      A.card ≤ 2 * (S.card * roundBound) :=
    C.separator_left_card_le_two_mul_separator_card_mul_roundBound
      hcover hAB hAleB hApos hnoAB
  have hNle12 :
      Fintype.card (GridVertex g) ≤ 6 * (2 * (S.card * roundBound)) :=
    hNle6A.trans (Nat.mul_le_mul_left 6 hUpper)
  omega

/-- Structured version of `not_small_balanced_separator`, using the named
balanced-separator witness that matches the statement of the separator theorem
used in the paper. -/
theorem not_small_balancedSeparator
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    {A B S : Finset (GridVertex g)}
    (Sep : BalancedSeparator F.auxGraph A B S)
    (hroundPos : 0 < roundBound)
    (hsmall : 24 * (S.card * roundBound) <
      Fintype.card (GridVertex g)) :
    False := by
  classical
  by_cases hApos : 0 < A.card
  · exact
      C.not_small_balanced_separator Sep.cover Sep.disjoint_left_right
        Sep.disjoint_left_separator Sep.disjoint_right_separator
        Sep.left_card_le_right_card Sep.right_balanced hApos
        Sep.no_edge_left_right hroundPos hsmall
  · have hAzero : A.card = 0 := Nat.eq_zero_of_not_pos hApos
    have hAB_S : Disjoint (A ∪ B) S := by
      rw [Finset.disjoint_left]
      intro x hx hSx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact Finset.disjoint_left.mp Sep.disjoint_left_separator hxA hSx
      · exact Finset.disjoint_left.mp Sep.disjoint_right_separator hxB hSx
    have hcardAB : (A ∪ B).card = A.card + B.card :=
      Finset.card_union_of_disjoint Sep.disjoint_left_right
    have hcardABS : ((A ∪ B) ∪ S).card = (A ∪ B).card + S.card :=
      Finset.card_union_of_disjoint hAB_S
    have hcardCover :
        ((A ∪ B) ∪ S).card = Fintype.card (GridVertex g) := by
      rw [Sep.cover]
      simp
    have hcardPartition :
        A.card + B.card + S.card = Fintype.card (GridVertex g) := by
      omega
    have hSleProduct : S.card ≤ S.card * roundBound :=
      Nat.le_mul_of_pos_right S.card hroundPos
    have hNle3S :
        Fintype.card (GridVertex g) ≤ 3 * S.card := by
      nlinarith [hAzero, hcardPartition, Sep.right_balanced]
    have hNle24 :
        Fintype.card (GridVertex g) ≤ 24 * (S.card * roundBound) := by
      nlinarith [hNle3S, hSleProduct]
    omega

/-- The auxiliary graph of a completed cut-matching game has no balanced
separator below the Chuzhoy--Tan threshold `N / (24d)`, encoded as
`N <= (24 * d) * |S|`. -/
theorem noSmallBalancedSeparator_auxGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hroundPos : 0 < roundBound) :
    NoSmallBalancedSeparator F.auxGraph (24 * roundBound) := by
  intro A B S Sep
  by_contra hnot
  have hsmall' :
      (24 * roundBound) * S.card < Fintype.card (GridVertex g) :=
    Nat.lt_of_not_ge hnot
  have hsmall : 24 * (S.card * roundBound) <
      Fintype.card (GridVertex g) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsmall'
  exact C.not_small_balancedSeparator Sep hroundPos hsmall

/-- Version of `noSmallBalancedSeparator_auxGraph` where positivity of the
round bound is derived from nontriviality of the coordinate set. -/
theorem noSmallBalancedSeparator_auxGraph_of_two_le_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) :
    NoSmallBalancedSeparator F.auxGraph (24 * roundBound) :=
  C.noSmallBalancedSeparator_auxGraph (C.roundBound_pos hcard)

/-- A separator/minor theorem, specialized to the auxiliary graph produced by
the cut-matching transcript, gives a grid minor in that auxiliary graph.  This
is the proof-facing form of the Krivelevich--Nenadov handoff used after
Chuzhoy--Tan Lemma 3.3. -/
theorem auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hroundPos : 0 < roundBound)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor F.auxGraph g' :=
  hseparatorGrid F.auxGraph C.auxGraph_maxDegreeAtMost
    (C.noSmallBalancedSeparator_auxGraph hroundPos)

/-- Version of `auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem`
where positivity of the round bound is derived from nontriviality of the
coordinate set. -/
theorem auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem_of_two_le_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor F.auxGraph g' :=
  hseparatorGrid F.auxGraph C.auxGraph_maxDegreeAtMost
    (C.noSmallBalancedSeparator_auxGraph_of_two_le_card hcard)

end CutMatchingGameCertificate

/-- A boundary edge has one endpoint inside the set. -/
theorem Edge.left_mem_or_right_mem_of_crosses
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {e : Edge F} {S : Finset (GridVertex g)}
    (h : e.Crosses S) : e.left ∈ S ∨ e.right ∈ S := by
  rcases h with ⟨hleft, _hright⟩ | ⟨hright, _hleft⟩
  · exact Or.inl hleft
  · exact Or.inr hright

/-- A boundary edge has one endpoint outside the set. -/
theorem Edge.left_notMem_or_right_notMem_of_crosses
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {e : Edge F} {S : Finset (GridVertex g)}
    (h : e.Crosses S) : e.left ∉ S ∨ e.right ∉ S := by
  rcases h with ⟨_hleft, hright⟩ | ⟨_hright, hleft⟩
  · exact Or.inr hright
  · exact Or.inl hleft

/-- Crossing is symmetric under replacing a set by its finite complement. -/
theorem Edge.crosses_sdiff_univ
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} (e : Edge F) (S : Finset (GridVertex g)) :
    e.Crosses (Finset.univ \ S) ↔ e.Crosses S := by
  classical
  simp [Edge.Crosses, and_comm, or_comm]

/-- Taking the finite complement of a coordinate set does not change its
multigraph edge boundary. -/
theorem edgeBoundary_sdiff_univ
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) (S : Finset (GridVertex g)) :
    F.edgeBoundary (Finset.univ \ S) = F.edgeBoundary S := by
  classical
  ext e
  simp [mem_edgeBoundary, Edge.crosses_sdiff_univ]

/-- Boundary membership gives adjacency in the simplified auxiliary graph. -/
theorem auxGraph_adj_of_mem_edgeBoundary
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) {S : Finset (GridVertex g)} {e : Edge F}
    (_he : e ∈ F.edgeBoundary S) :
    F.auxGraph.Adj e.left e.right := by
  exact e.auxGraph_adj

/-- A direct-adjacency certificate for all transcript edge instances.  Together
with connected, disjoint branch sets, this is exactly the remaining local
obligation needed to turn the edge-supported auxiliary graph into a branch-set
minor model. -/
structure AuxGraphMinorCertificate
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) where
  /-- The branch set assigned to each coordinate vertex. -/
  branchSet : GridVertex g → Finset V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ x : GridVertex g, (branchSet x).Nonempty
  /-- Every branch set induces a connected subgraph. -/
  branch_connected :
    ∀ x : GridVertex g, (G.induce {v : V | v ∈ branchSet x}).Connected
  /-- Distinct coordinates have disjoint branch sets. -/
  branch_disjoint :
    ∀ ⦃x y : GridVertex g⦄, x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- Each oriented transcript edge has a host edge between its endpoint branch
  sets. -/
  adjacent :
    ∀ e : Edge F,
      ∃ x ∈ branchSet e.left, ∃ y ∈ branchSet e.right, G.Adj x y

namespace AuxGraphMinorCertificate

/-- A direct-adjacency certificate produces a minor model of the simplified
auxiliary coordinate graph.  The theorem isolates the final branch-set-model
obligation from the cut-matching transcript bookkeeping. -/
noncomputable def toMinorModel
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (C : AuxGraphMinorCertificate F) :
    MinorModel F.auxGraph G where
  branchSet := C.branchSet
  branch_nonempty := C.branch_nonempty
  branch_connected := C.branch_connected
  branch_disjoint := C.branch_disjoint
  adjacent := by
    intro x y hxy
    rcases F.auxGraph_adj_exists_edge hxy with
      ⟨e, ⟨hleft, hright⟩ | ⟨hleft, hright⟩⟩
    · simpa [hleft, hright] using C.adjacent e
    · rcases C.adjacent e with ⟨a, ha, b, hb, hab⟩
      exact ⟨b, by simpa [hright] using hb,
        a, by simpa [hleft] using ha, G.symm hab⟩

/-- A direct-adjacency certificate witnesses that the auxiliary coordinate graph
is a minor of the host graph. -/
theorem isMinor_auxGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (C : AuxGraphMinorCertificate F) :
    IsMinor F.auxGraph G :=
  ⟨C.toMinorModel⟩

end AuxGraphMinorCertificate

/-- An allocated walk-support certificate for the auxiliary graph.  For every
transcript edge, the penultimate vertex of its supporting walk is allocated to
the branch set of the left endpoint, while the right row contact belongs to the
branch set of the right endpoint.  The final edge of the walk then realizes the
minor adjacency. -/
structure AuxGraphAllocatedMinorCertificate
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen) where
  /-- Branch set assigned to each coordinate vertex. -/
  branchSet : GridVertex g → Finset V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ x : GridVertex g, (branchSet x).Nonempty
  /-- Every branch set induces a connected subgraph. -/
  branch_connected :
    ∀ x : GridVertex g, (G.induce {v : V | v ∈ branchSet x}).Connected
  /-- Distinct coordinate vertices have disjoint branch sets. -/
  branch_disjoint :
    ∀ ⦃x y : GridVertex g⦄, x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- The left row contact of every transcript edge belongs to the branch set of
  its left endpoint. -/
  leftContact_mem_branch : ∀ e : Edge F, e.leftContact ∈ branchSet e.left
  /-- The right row contact of every transcript edge belongs to the branch set of
  its right endpoint. -/
  rightContact_mem_branch : ∀ e : Edge F, e.rightContact ∈ branchSet e.right
  /-- The penultimate vertex of each supporting walk is allocated to the branch
  set of the left endpoint. -/
  walk_penultimate_mem_branch : ∀ e : Edge F, e.walk.penultimate ∈ branchSet e.left

namespace AuxGraphAllocatedMinorCertificate

/-- Build an allocated auxiliary-minor certificate from the canonical
source-allocation branch sets, once the two genuinely global topological
obligations are supplied: those branch sets are connected and pairwise
disjoint. -/
noncomputable def ofSourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m)
    (branch_connected :
      ∀ x : GridVertex g,
        (G.induce {v : V | v ∈ F.sourceAllocatedBranchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (F.sourceAllocatedBranchSet x) (F.sourceAllocatedBranchSet y)) :
    AuxGraphAllocatedMinorCertificate F where
  branchSet := F.sourceAllocatedBranchSet
  branch_nonempty := F.sourceAllocatedBranchSet_nonempty hm
  branch_connected := branch_connected
  branch_disjoint := branch_disjoint
  leftContact_mem_branch := by
    intro e
    exact leftContact_mem_sourceAllocatedBranchSet e
  rightContact_mem_branch := by
    intro e
    exact rightContact_mem_sourceAllocatedBranchSet e
  walk_penultimate_mem_branch := by
    intro e
    exact walk_penultimate_mem_sourceAllocatedBranchSet e

/-- Build the concrete source-allocation certificate when row traces are known
connected.  This discharges the branch-connectivity obligation by gluing each
outgoing half-open walk support to the corresponding row at its left contact. -/
noncomputable def ofSourceAllocatedBranchSet_of_rowTrace_connected
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m)
    (rowTrace_connected :
      ∀ x : GridVertex g,
        (G.induce {v : V |
          v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (F.sourceAllocatedBranchSet x) (F.sourceAllocatedBranchSet y)) :
    AuxGraphAllocatedMinorCertificate F :=
  AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet hm
    (F.sourceAllocatedBranchSet_connected_of_rowTrace_connected hm rowTrace_connected)
    branch_disjoint

/-- Build the concrete source-allocation certificate from the proved row-trace
connectivity theorem.  The only remaining topological hypothesis is pairwise
disjointness of the source-allocated branch sets. -/
noncomputable def ofSourceAllocatedBranchSet_of_rowTrace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (F.sourceAllocatedBranchSet x) (F.sourceAllocatedBranchSet y)) :
    AuxGraphAllocatedMinorCertificate F :=
  AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_rowTrace_connected
    hm (fun x => selectedOddLocalCrossbarGridRowTrace_connected
      Hsys hcrossbars hlen hm x) branch_disjoint

/-- Build the concrete source-allocation certificate from local geometric
separation facts for rows and half-open matched-edge supports. -/
noncomputable def ofSourceAllocatedBranchSet_of_separated
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m)
    (row_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset) :
    AuxGraphAllocatedMinorCertificate F :=
  AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_rowTrace hm
    (fun {x y} hxy =>
      sourceAllocatedBranchSet_disjoint_of_trace_and_support_disjoint
        row_disjoint support_row_disjoint support_support_disjoint (x := x) (y := y) hxy)

/-- Build the concrete source-allocation certificate once the half-open
walk-support pieces are separated from other rows and from each other.  Row
trace connectivity and row-row disjointness are supplied by the canonical row
trace construction. -/
noncomputable def ofSourceAllocatedBranchSet_of_support_separated
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m)
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset) :
    AuxGraphAllocatedMinorCertificate F :=
  AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_separated
    hm
    (fun {_x _y} hxy =>
      selectedOddLocalCrossbarGridRowTrace_disjoint_of_grid_ne
        (x := _x) (y := _y) Hsys hcrossbars hlen hxy)
    support_row_disjoint support_support_disjoint

/-- Build the concrete source-allocation certificate after internalizing the
support-vs-row separation down to the sharp right-spoke-own-row intersection
fact. -/
noncomputable def ofSourceAllocatedBranchSet_of_right_spoke_inter
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m)
    (right_spoke_inter :
      ∀ e : Edge F, ∀ ⦃v : V⦄,
        v ∈ ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet →
          v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right →
            v = e.rightContact)
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset) :
    AuxGraphAllocatedMinorCertificate F :=
  AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_support_separated
    hm
    (fun {_x _y} e hleft hxy =>
      e.walk_dropLast_support_disjoint_rowTrace_of_left_ne_of_right_spoke_inter
        hleft hxy (right_spoke_inter e))
    support_support_disjoint

/-- Build the concrete source-allocation certificate after the support-vs-row
separation has been fully internalized; only pairwise disjointness of
half-open walk supports for distinct left endpoints remains. -/
noncomputable def ofSourceAllocatedBranchSet_of_support_support_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m)
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset) :
    AuxGraphAllocatedMinorCertificate F :=
  AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_right_spoke_inter
    hm (fun e {_v} hvSpoke hvRow =>
      e.rightCanonicalSpoke_mem_right_rowTrace_eq_rightContact hvSpoke hvRow)
    support_support_disjoint

/-- Fully internalized source-allocation certificate for the transported
cut-matching family.  Row disjointness, support-vs-row separation, and
support-support separation are all supplied by the canonical geometry. -/
noncomputable def ofSourceAllocatedBranchSet_complete
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (hm : 0 < m) :
    AuxGraphAllocatedMinorCertificate F :=
  AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_support_support_disjoint
    hm
    (fun {_x _y} e f hleft hfleft hxy =>
      e.walk_dropLast_support_disjoint_of_left_ne f
        (by
          intro hsame
          apply hxy
          rw [← hleft, ← hfleft, hsame]))

/-- An allocated walk-support certificate supplies direct branch-set adjacency
witnesses for the simplified auxiliary graph. -/
theorem adjacent
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (C : AuxGraphAllocatedMinorCertificate F)
    ⦃x y : GridVertex g⦄ (hxy : F.auxGraph.Adj x y) :
    ∃ u ∈ C.branchSet x, ∃ v ∈ C.branchSet y, G.Adj u v := by
  rcases F.auxGraph_adj_exists_edge hxy with
    ⟨e, ⟨hleft, hright⟩ | ⟨hleft, hright⟩⟩
  · refine ⟨e.walk.penultimate, ?_, e.rightContact, ?_, ?_⟩
    · simpa [hleft] using C.walk_penultimate_mem_branch e
    · simpa [hright] using C.rightContact_mem_branch e
    · exact e.walk_penultimate_adj_rightContact
  · refine ⟨e.rightContact, ?_, e.walk.penultimate, ?_, ?_⟩
    · simpa [hright] using C.rightContact_mem_branch e
    · simpa [hleft] using C.walk_penultimate_mem_branch e
    · exact G.symm e.walk_penultimate_adj_rightContact

/-- Forget the allocation proof to a direct-adjacency certificate. -/
noncomputable def toAuxGraphMinorCertificate
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (C : AuxGraphAllocatedMinorCertificate F) :
    AuxGraphMinorCertificate F where
  branchSet := C.branchSet
  branch_nonempty := C.branch_nonempty
  branch_connected := C.branch_connected
  branch_disjoint := C.branch_disjoint
  adjacent := by
    intro e
    exact ⟨e.walk.penultimate, C.walk_penultimate_mem_branch e,
      e.rightContact, C.rightContact_mem_branch e,
      e.walk_penultimate_adj_rightContact⟩

/-- Convert an allocated walk-support certificate into the standard minor
model. -/
noncomputable def toMinorModel
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (C : AuxGraphAllocatedMinorCertificate F) :
    MinorModel F.auxGraph G :=
  C.toAuxGraphMinorCertificate.toMinorModel

/-- An allocated walk-support certificate proves that the auxiliary graph is a
minor of the host graph. -/
theorem isMinor_auxGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (C : AuxGraphAllocatedMinorCertificate F) :
    IsMinor F.auxGraph G :=
  ⟨C.toMinorModel⟩

/-- Grid minors of the auxiliary coordinate graph transfer to the host graph
through an allocated walk-support certificate. -/
theorem containsGridMinor_of_auxGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen}
    (C : AuxGraphAllocatedMinorCertificate F)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' :=
  ContainsGridMinor.of_minor_small hgrid C.isMinor_auxGraph

end AuxGraphAllocatedMinorCertificate

namespace CutMatchingGameCertificate

/-- Combining the cut-matching game certificate with a branch-set certificate
for the auxiliary graph gives the exact proof-facing output of Lemma 3.3:
a bounded-degree auxiliary graph, edge-indexed `1/2` expansion, and a minor
model in the host graph. -/
theorem auxGraph_minor_degree_expander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (M : AuxGraphMinorCertificate F) :
    IsMinor F.auxGraph G ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact ⟨M.isMinor_auxGraph, C.auxGraph_maxDegreeAtMost, C.half_expander⟩

/-- The same proof-facing output as `auxGraph_minor_degree_expander`, but with
the local allocation obligations instead of already-packaged direct branch-set
adjacency witnesses. -/
theorem auxGraph_allocated_minor_degree_expander
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (M : AuxGraphAllocatedMinorCertificate F) :
    IsMinor F.auxGraph G ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact C.auxGraph_minor_degree_expander M.toAuxGraphMinorCertificate

/-- Once the bounded-degree expanding auxiliary graph has a grid minor, the
allocated support certificate transports that grid minor back to the host
graph. -/
theorem containsGridMinor_of_auxGraph
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (_C : CutMatchingGameCertificate F roundBound)
    (M : AuxGraphAllocatedMinorCertificate F)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' :=
  M.containsGridMinor_of_auxGraph hgrid

/-- A single assembled statement for the output of the cut-matching transcript
plus an external grid-minor theorem for the auxiliary expander. -/
theorem host_gridMinor_and_auxGraph_bounds
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (M : AuxGraphAllocatedMinorCertificate F)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact ⟨C.containsGridMinor_of_auxGraph M hgrid,
    C.auxGraph_maxDegreeAtMost, C.half_expander⟩

/-- Version of `host_gridMinor_and_auxGraph_bounds` specialized to the concrete
source-allocation branch sets.  This is the proof-facing interface left after
the walk-support bookkeeping: prove those source-allocated sets are connected
and pairwise disjoint, and prove the auxiliary expander has a grid minor. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (branch_connected :
      ∀ x : GridVertex g,
        (G.induce {v : V | v ∈ F.sourceAllocatedBranchSet x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (F.sourceAllocatedBranchSet x) (F.sourceAllocatedBranchSet y))
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet hm
      branch_connected branch_disjoint
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- A row-trace-facing version of `host_gridMinor_and_auxGraph_bounds`: after the
local walk-support bookkeeping, the remaining global topological obligations are
row-trace connectivity and pairwise disjointness of the resulting allocated
branch sets. -/
theorem host_gridMinor_and_auxGraph_bounds_of_rowTrace_connected_sourceAllocatedBranchSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (rowTrace_connected :
      ∀ x : GridVertex g,
        (G.induce {v : V |
          v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x}).Connected)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (F.sourceAllocatedBranchSet x) (F.sourceAllocatedBranchSet y))
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_rowTrace_connected
      hm rowTrace_connected branch_disjoint
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- Final source-allocation form of the cut-matching bridge: row-trace
connectivity and all local adjacency bookkeeping are internalized, so the
remaining assumptions are pairwise branch-set disjointness and a grid minor in
the auxiliary expander. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (branch_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint (F.sourceAllocatedBranchSet x) (F.sourceAllocatedBranchSet y))
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_rowTrace
      hm branch_disjoint
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- Source-allocation bridge stated with the concrete separation obligations that
remain after internalizing row connectivity and branch-set adjacency. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_separated
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (row_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_separated
      hm row_disjoint support_row_disjoint support_support_disjoint
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- Source-allocation bridge after internalizing row-trace connectivity and
row-row disjointness.  The remaining local topological obligations are exactly
the two half-open walk-support separation families. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_support_separated
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_support_separated
      hm support_row_disjoint support_support_disjoint
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- Source-allocation bridge after reducing support-vs-row separation to the
right-spoke-own-row intersection fact. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_right_spoke_inter
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (right_spoke_inter :
      ∀ e : Edge F, ∀ ⦃v : V⦄,
        v ∈ ((F.round e.round).rightCanonicalSpokeOfSourceCoord e.source).vertexSet →
          v ∈ selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen e.right →
            v = e.rightContact)
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_right_spoke_inter
      hm right_spoke_inter support_support_disjoint
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- Source-allocation bridge after internalizing all support-vs-row separation.
The only remaining branch-set separation input is pairwise disjointness of the
half-open supports assigned to distinct left endpoints. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_support_support_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_of_support_support_disjoint
      hm support_support_disjoint
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- Fully internalized source-allocation bridge from the auxiliary grid minor
to the host graph.  The canonical row traces and half-open edge supports
provide the branch-set minor model without any extra geometric hypotheses. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hgrid : ContainsGridMinor F.auxGraph g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  let M : AuxGraphAllocatedMinorCertificate F :=
    AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_complete hm
  exact C.host_gridMinor_and_auxGraph_bounds M hgrid

/-- Fully internalized source-allocation bridge with the separator/minor
handoff for the auxiliary graph. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete_of_noSmallBalancedSeparator_theorem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hroundPos : 0 < roundBound)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete
    hm
    (C.auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem
      hroundPos hseparatorGrid)

/-- Large-coordinate version of the fully internalized separator/minor bridge;
`2 <= |GridVertex g|` supplies positivity for the round bound. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete_of_noSmallBalancedSeparator_theorem_of_two_le_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete
    hm
    (C.auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem_of_two_le_card
      hcard hseparatorGrid)

/-- Source-allocation bridge with the expander-to-grid handoff expressed as a
separator/minor theorem.  This is the current formal boundary for the last
post-cut-matching step in Chuzhoy--Tan Theorem 3.2: the cut-matching transcript
supplies bounded degree and no small balanced separator, the supplied theorem
turns those into an auxiliary grid minor, and the allocated branch-set model
transports it back to the host graph. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_separated_of_noSmallBalancedSeparator_theorem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hroundPos : 0 < roundBound)
    (row_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact
    C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_separated
      hm row_disjoint support_row_disjoint support_support_disjoint
      (C.auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem
        hroundPos hseparatorGrid)

/-- Separator/minor handoff with row-trace separation internalized; only the
half-open support separation facts remain as local geometric hypotheses. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_support_separated_of_noSmallBalancedSeparator_theorem
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hroundPos : 0 < roundBound)
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact
    C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_support_separated
      hm support_row_disjoint support_support_disjoint
      (C.auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem
        hroundPos hseparatorGrid)

/-- Version of
`host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_separated_of_noSmallBalancedSeparator_theorem`
where positivity of the round bound is derived from `2 <= |V(aux)|`.  For the
coordinate auxiliary graph, this is the natural large-grid case. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_separated_of_noSmallBalancedSeparator_theorem_of_two_le_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (row_disjoint :
      ∀ ⦃x y : GridVertex g⦄, x ≠ y →
        Disjoint
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen x)
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact
    C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_separated
      hm row_disjoint support_row_disjoint support_support_disjoint
      (C.auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem_of_two_le_card
        hcard hseparatorGrid)

/-- Large-coordinate version of the support-separated bridge; `2 <= |GridVertex g|`
supplies positivity for the cut-matching round bound. -/
theorem host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_support_separated_of_noSmallBalancedSeparator_theorem_of_two_le_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    {F : SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen} {roundBound : ℕ}
    (C : CutMatchingGameCertificate F roundBound)
    (hm : 0 < m)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (support_row_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e : Edge F), e.left = x → x ≠ y →
        Disjoint e.walk.support.dropLast.toFinset
          (selectedOddLocalCrossbarGridRowTrace Hsys hcrossbars hlen y))
    (support_support_disjoint :
      ∀ ⦃x y : GridVertex g⦄ (e f : Edge F),
        e.left = x → f.left = y → x ≠ y →
          Disjoint e.walk.support.dropLast.toFinset
            f.walk.support.dropLast.toFinset)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' ∧
      MaxDegreeAtMost F.auxGraph roundBound ∧
        F.IsHalfEdgeExpander := by
  exact
    C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_support_separated
      hm support_row_disjoint support_support_disjoint
      (C.auxGraph_containsGridMinor_of_noSmallBalancedSeparator_theorem_of_two_le_card
        hcard hseparatorGrid)

end CutMatchingGameCertificate

/-- A finite cut-matching transcript indexed by `Fin roundBound`, with the
canonical assignment of rounds to selected odd clusters already bundled in.

This is the proof-facing form of the cut-matching output used by
Chuzhoy--Tan: the cuts are full bisections of the coordinate set, the number
of rounds fits in the selected odd clusters, and the union of the transported
matchings is a half-edge-expander. -/
structure FinCutMatchingGameTranscript
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (roundBound : ℕ) where
  /-- The chosen number of cut-matching rounds fits into the selected odd
  clusters. -/
  rounds_fit : roundBound ≤ m
  /-- The left side of each cut. -/
  U : Fin roundBound → Finset (GridVertex g)
  /-- The right side of each cut. -/
  W : Fin roundBound → Finset (GridVertex g)
  /-- The two sides of each cut are disjoint. -/
  disjoint : ∀ r : Fin roundBound, Disjoint (U r) (W r)
  /-- Each cut is balanced. -/
  card_eq : ∀ r : Fin roundBound, (U r).card = (W r).card
  /-- Each cut covers the full coordinate set. -/
  coversAll : ∀ r : Fin roundBound, U r ∪ W r = Finset.univ
  /-- The auxiliary graph obtained from the transported matchings is a
  half-edge-expander. -/
  half_expander :
    (ofFinCuts Hsys hcrossbars hlen rounds_fit U W disjoint card_eq).IsHalfEdgeExpander

namespace FinCutMatchingGameTranscript

/-- The transported round family associated to a finite cut-matching
transcript. -/
noncomputable def toRoundFamily
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound) :
    SelectedOddLocalCrossbarGridTransportedRoundFamily
      Hsys hcrossbars hlen :=
  ofFinCuts Hsys hcrossbars hlen T.rounds_fit T.U T.W T.disjoint T.card_eq

/-- The transported family associated to a `Fin roundBound` transcript has
exactly `roundBound` rounds. -/
theorem toRoundFamily_index_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound) :
    Fintype.card T.toRoundFamily.Index = roundBound := by
  change Fintype.card (ULift.{u, 0} (Fin roundBound)) = roundBound
  calc
    Fintype.card (ULift.{u, 0} (Fin roundBound)) =
        Fintype.card (Fin roundBound) :=
      Fintype.card_congr Equiv.ulift
    _ = roundBound := Fintype.card_fin roundBound

/-- The associated transported family uses the canonical cluster allocation:
the lifted round `r` is sent to selected odd cluster `r.down`. -/
theorem toRoundFamily_cluster_eq
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (r : T.toRoundFamily.Index) :
    T.toRoundFamily.cluster r = finCluster T.rounds_fit r.down := by
  rfl

/-- In particular, the selected-cluster number used by a lifted round is the
round number itself. -/
theorem toRoundFamily_cluster_val
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (r : T.toRoundFamily.Index) :
    (T.toRoundFamily.cluster r).1 = r.down.1 := by
  simp [toRoundFamily_cluster_eq, finCluster]

/-- Regression guard for the use of Chuzhoy--Tan Lemma 3.3.

Every transported cut-matching round is allocated to a selected odd cluster
at which a local crossbar is available. Thus the auxiliary-expander argument
uses the lemma only after the odd-cluster stitching/crossbar hypothesis has
been established for every matching-round cluster, rather than relying on the
under-specified standalone statement printed in the paper. -/
theorem toRoundFamily_crossbar_at_round_cluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (r : T.toRoundFamily.Index) :
    Nonempty
      (Crossbar
        (Hsys.hairLocalGraph
          (oddClusterIndex hlen (T.toRoundFamily.cluster r)))
        (Hsys.base.left
          (oddClusterIndex hlen (T.toRoundFamily.cluster r)))
        (Hsys.base.right
          (oddClusterIndex hlen (T.toRoundFamily.cluster r)))
        (Hsys.y (oddClusterIndex hlen (T.toRoundFamily.cluster r)))
        (g ^ 2)) :=
  hcrossbars _
    (oddClusterIndex_oneBasedOdd hlen (T.toRoundFamily.cluster r))

/-- The cut-matching certificate associated to a finite transcript. -/
noncomputable def toCertificate
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound) :
    CutMatchingGameCertificate T.toRoundFamily roundBound where
  coversAll := by
    intro r
    rcases r with ⟨r⟩
    simpa [toRoundFamily, ofFinCuts, ofCuts] using T.coversAll r
  round_count_le := by
    exact le_of_eq T.toRoundFamily_index_card
  half_expander := by
    simpa [toRoundFamily] using T.half_expander

/-- A finite transcript on a nontrivial coordinate set has a positive round
bound. -/
theorem roundBound_pos
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) :
    0 < roundBound :=
  T.toCertificate.roundBound_pos hcard

/-- A finite transcript on a nontrivial coordinate set uses a positive number
of selected odd clusters. -/
theorem selectedClusterCount_pos
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g)) :
    0 < m :=
  (T.roundBound_pos hcard).trans_le T.rounds_fit

/-- A finite cut-matching transcript plus the separator-to-grid theorem gives
a grid minor in the host graph.  All geometric separation needed to realize
the auxiliary minor in the host graph has already been internalized in
`AuxGraphAllocatedMinorCertificate.ofSourceAllocatedBranchSet_complete`. -/
theorem containsGridMinor_of_separatorGridMinor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hm : 0 < m)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' := by
  let C := T.toCertificate
  exact
    (C.host_gridMinor_and_auxGraph_bounds_of_sourceAllocatedBranchSet_complete_of_noSmallBalancedSeparator_theorem_of_two_le_card
      hm hcard hseparatorGrid).1

/-- Version of `containsGridMinor_of_separatorGridMinor` deriving the positive
selected-cluster count from the transcript itself. -/
theorem containsGridMinor_of_separatorGridMinor_of_two_le_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ContainsGridMinor G g' :=
  T.containsGridMinor_of_separatorGridMinor
    (T.selectedClusterCount_pos hcard) hcard hseparatorGrid

/-- Contract-shaped handoff from a finite cut-matching transcript: once the
separator theorem produces a grid order `g'` large enough for the claimed
polylogarithmic loss, the host graph has the corresponding grid minor. -/
theorem exists_gridMinor_of_separatorGridMinor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound c g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hm : 0 < m)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (hscale : g ≤ c * g' * (Nat.log 2 g) ^ 2)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ∃ g'' : ℕ,
      g ≤ c * g'' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g'' := by
  exact ⟨g', hscale,
    T.containsGridMinor_of_separatorGridMinor hm hcard hseparatorGrid⟩

/-- Contract-shaped handoff deriving all local positivity hypotheses from the
finite transcript and the nontrivial coordinate set. -/
theorem exists_gridMinor_of_separatorGridMinor_of_two_le_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m roundBound c g' : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    {hlen : 2 * m ≤ ell}
    (T : FinCutMatchingGameTranscript Hsys hcrossbars hlen roundBound)
    (hcard : 2 ≤ Fintype.card (GridVertex g))
    (hscale : g ≤ c * g' * (Nat.log 2 g) ^ 2)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ∃ g'' : ℕ,
      g ≤ c * g'' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g'' := by
  exact ⟨g', hscale,
    T.containsGridMinor_of_separatorGridMinor_of_two_le_card hcard
      hseparatorGrid⟩

end FinCutMatchingGameTranscript

end SelectedOddLocalCrossbarGridTransportedRoundFamily

/-- Large-case crossbar-grid handoff after the cut-matching transcript and
separator-grid theorem have been supplied.

This theorem has the same conclusion as the large-case contract, but exposes
the two remaining non-local mathematical inputs explicitly: a finite
cut-matching transcript using the selected odd clusters, and the
separator-to-grid theorem at the resulting auxiliary degree scale. -/
theorem gridMinor_of_hairy_pathOfSets_and_crossbars_large_of_finCutMatchingTranscript
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w g m roundBound c g' : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell)
    (T :
      SelectedOddLocalCrossbarGridTransportedRoundFamily.FinCutMatchingGameTranscript
        Hsys hcrossbars hlen roundBound)
    (hg : 2 ≤ g)
    (hscale : g ≤ c * g' * (Nat.log 2 g) ^ 2)
    (hseparatorGrid : SeparatorGridMinorTheoremAt roundBound g') :
    ∃ g'' : ℕ,
      g ≤ c * g'' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g'' :=
  T.exists_gridMinor_of_separatorGridMinor_of_two_le_card
    (two_le_card_gridVertex_of_two_le hg) hscale hseparatorGrid

/-- The remaining data needed for the large crossbar-grid case after all local
geometry has been formalized.

The Chuzhoy--Tan cut-matching argument and the separator-to-grid theorem are
expected to provide this package: enough selected odd clusters, a finite
cut-matching transcript whose auxiliary graph expands, a target auxiliary grid
order, and the numerical loss bound. -/
structure LargeCaseCutMatchingData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (c : ℕ) where
  /-- Number of selected odd clusters reserved for the transcript. -/
  m : ℕ
  /-- Number of cut-matching rounds. -/
  roundBound : ℕ
  /-- Grid order produced in the auxiliary graph. -/
  gridOrder : ℕ
  /-- There are enough clusters in the hairy path-of-sets system. -/
  length_bound : 2 * m ≤ ell
  /-- The transported cut-matching transcript. -/
  transcript :
    SelectedOddLocalCrossbarGridTransportedRoundFamily.FinCutMatchingGameTranscript
      Hsys hcrossbars length_bound roundBound
  /-- The auxiliary grid order is large enough for the stated polylogarithmic
  loss. -/
  scale : g ≤ c * gridOrder * (Nat.log 2 g) ^ 2
  /-- The separator-to-grid theorem at the auxiliary degree scale. -/
  separatorGrid : SeparatorGridMinorTheoremAt roundBound gridOrder

/-- Provider interface for the remaining large-case theorem: for a fixed
constant `c`, every large hairy crossbar instance supplies the finite
cut-matching/separator data package needed by
`LargeCaseCutMatchingData.exists_gridMinor`. -/
def LargeCaseCutMatchingDataProvider (c : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w),
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
            c * Nat.log 2 g ≤ ell →
              g ^ 2 ≤ w →
                c * (Nat.log 2 g) ^ 2 < g →
                  (hcrossbars :
                    ∀ i : Fin ell, OneBasedOdd i →
                      Nonempty (Crossbar (Hsys.hairLocalGraph i)
                        (Hsys.base.left i) (Hsys.base.right i)
                        (Hsys.y i) (g ^ 2))) →
                    Nonempty (LargeCaseCutMatchingData Hsys hcrossbars c)

namespace LargeCaseCutMatchingData

/-- A large-case cut-matching data package gives the exact grid-minor
conclusion needed by the large crossbar-grid assembly. -/
theorem exists_gridMinor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g c : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    (D : LargeCaseCutMatchingData Hsys hcrossbars c)
    (hg : 2 ≤ g) :
    ∃ g' : ℕ,
      g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g' :=
  gridMinor_of_hairy_pathOfSets_and_crossbars_large_of_finCutMatchingTranscript
    Hsys hcrossbars D.length_bound D.transcript hg D.scale D.separatorGrid

end LargeCaseCutMatchingData

/-- The fixed round count used by the cut-matching part of the large
crossbar-grid case.  The paper uses `O(log g)` rounds; this definition records
the concrete natural-number expression once a round constant has been chosen. -/
def largeCaseRoundBound (cRound g : ℕ) : ℕ :=
  cRound * Nat.log 2 g

/-- If the large-case length hypothesis uses twice the round constant, then
there are enough selected odd clusters to allocate one odd cluster per
cut-matching round and one intervening cluster between consecutive rows. -/
theorem two_mul_largeCaseRoundBound_le_of_two_mul_roundConstant
    {cRound ell g : ℕ}
    (h : (2 * cRound) * Nat.log 2 g ≤ ell) :
    2 * largeCaseRoundBound cRound g ≤ ell := by
  simpa [largeCaseRoundBound, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using h

/-- A large-case data package with the cut-matching round count fixed to
`cRound * log_2 g`.

This is closer to the Chuzhoy--Tan construction than
`LargeCaseCutMatchingData`: the number of selected clusters and the number of
rounds are no longer arbitrary fields.  The remaining mathematical content is
the actual cut-matching transcript and the separator-to-grid theorem at that
degree scale. -/
structure FixedRoundLargeCaseCutMatchingData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (cRound cScale : ℕ) where
  /-- Grid order produced in the auxiliary graph. -/
  gridOrder : ℕ
  /-- The length hypothesis specialized to the fixed round count. -/
  length_bound : 2 * largeCaseRoundBound cRound g ≤ ell
  /-- The transported cut-matching transcript using exactly the fixed round
  count. -/
  transcript :
    SelectedOddLocalCrossbarGridTransportedRoundFamily.FinCutMatchingGameTranscript
      Hsys hcrossbars length_bound (largeCaseRoundBound cRound g)
  /-- The auxiliary grid order is large enough for the stated polylogarithmic
  loss at scale `cScale`. -/
  scale : g ≤ cScale * gridOrder * (Nat.log 2 g) ^ 2
  /-- The separator-to-grid theorem at the fixed auxiliary degree scale. -/
  separatorGrid :
    SeparatorGridMinorTheoremAt (largeCaseRoundBound cRound g) gridOrder

namespace FixedRoundLargeCaseCutMatchingData

/-- Forget the fixed-round bookkeeping and view a fixed-round package as a
general large-case package at any scale constant dominating `cScale`. -/
def toLargeCaseCutMatchingData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g cRound cScale c : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    (D : FixedRoundLargeCaseCutMatchingData Hsys hcrossbars cRound cScale)
    (hscale_le : cScale ≤ c) :
    LargeCaseCutMatchingData Hsys hcrossbars c where
  m := largeCaseRoundBound cRound g
  roundBound := largeCaseRoundBound cRound g
  gridOrder := D.gridOrder
  length_bound := D.length_bound
  transcript := D.transcript
  scale := by
    exact D.scale.trans (by
      gcongr)
  separatorGrid := D.separatorGrid

/-- A fixed-round package gives the exact grid-minor conclusion needed by the
large crossbar-grid assembly. -/
theorem exists_gridMinor
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g cRound cScale c : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    (D : FixedRoundLargeCaseCutMatchingData Hsys hcrossbars cRound cScale)
    (hscale_le : cScale ≤ c) (hg : 2 ≤ g) :
    ∃ g' : ℕ,
      g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g' :=
  (D.toLargeCaseCutMatchingData hscale_le).exists_gridMinor hg

end FixedRoundLargeCaseCutMatchingData

/-- The cut-matching transcript part of the fixed-round large-case package,
separated from the separator-to-grid theorem and final scale arithmetic. -/
structure FixedRoundCutMatchingTranscriptData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (cRound : ℕ) where
  /-- The length hypothesis specialized to the fixed round count. -/
  length_bound : 2 * largeCaseRoundBound cRound g ≤ ell
  /-- The transported transcript whose auxiliary graph is a half-edge-expander. -/
  transcript :
    SelectedOddLocalCrossbarGridTransportedRoundFamily.FinCutMatchingGameTranscript
      Hsys hcrossbars length_bound (largeCaseRoundBound cRound g)

namespace FixedRoundCutMatchingTranscriptData

/-- Add a separator-to-grid theorem and scale inequality to a transcript-only
package, obtaining the fixed-round large-case data package. -/
def toFixedRoundLargeCaseCutMatchingData
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g cRound cScale gridOrder : ℕ}
    {Hsys : HairyPathOfSetsSystem G ell w}
    {hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2))}
    (T : FixedRoundCutMatchingTranscriptData Hsys hcrossbars cRound)
    (hscale : g ≤ cScale * gridOrder * (Nat.log 2 g) ^ 2)
    (hseparatorGrid :
      SeparatorGridMinorTheoremAt (largeCaseRoundBound cRound g) gridOrder) :
    FixedRoundLargeCaseCutMatchingData Hsys hcrossbars cRound cScale where
  gridOrder := gridOrder
  length_bound := T.length_bound
  transcript := T.transcript
  scale := hscale
  separatorGrid := hseparatorGrid

end FixedRoundCutMatchingTranscriptData

/-- Provider interface for the fixed-round cut-matching construction.  This
separates the paper's two constants: `cRound` controls the number of
cut-matching rounds, while `cScale` controls the final polylogarithmic loss. -/
def FixedRoundLargeCaseCutMatchingDataProvider
    (cRound cScale : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w),
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
            (2 * cRound) * Nat.log 2 g ≤ ell →
              g ^ 2 ≤ w →
                cScale * (Nat.log 2 g) ^ 2 < g →
                  (hcrossbars :
                    ∀ i : Fin ell, OneBasedOdd i →
                      Nonempty (Crossbar (Hsys.hairLocalGraph i)
                        (Hsys.base.left i) (Hsys.base.right i)
                        (Hsys.y i) (g ^ 2))) →
                    Nonempty
                      (FixedRoundLargeCaseCutMatchingData
                        Hsys hcrossbars cRound cScale)

/-- Provider interface for only the fixed-round cut-matching game: it produces
the full-bisection transcript whose auxiliary graph is a half-edge-expander. -/
def FixedRoundCutMatchingTranscriptProvider (cRound : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w),
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
            (2 * cRound) * Nat.log 2 g ≤ ell →
              g ^ 2 ≤ w →
                (hcrossbars :
                  ∀ i : Fin ell, OneBasedOdd i →
                    Nonempty (Crossbar (Hsys.hairLocalGraph i)
                      (Hsys.base.left i) (Hsys.base.right i)
                      (Hsys.y i) (g ^ 2))) →
                  Nonempty
                    (FixedRoundCutMatchingTranscriptData
                      Hsys hcrossbars cRound)

/-- Unbundled fixed-round cut-matching provider.

The local graph-theoretic matching for a balanced cut is already formalized by
`selectedOddLocalCrossbarGridTransportedMatchingRound`.  This provider exposes
the remaining KRV-style choice: a finite sequence of full bisections whose
transported matching union is a half-edge-expander. -/
def FixedRoundCutMatchingUnbundledProvider (cRound : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w),
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
            (hrounds : (2 * cRound) * Nat.log 2 g ≤ ell) →
              g ^ 2 ≤ w →
                (hcrossbars :
                  ∀ i : Fin ell, OneBasedOdd i →
                    Nonempty (Crossbar (Hsys.hairLocalGraph i)
                      (Hsys.base.left i) (Hsys.base.right i)
                      (Hsys.y i) (g ^ 2))) →
                  ∃ U W :
                      Fin (largeCaseRoundBound cRound g) →
                        Finset (GridVertex g),
                    ∃ hdisj : ∀ r : Fin (largeCaseRoundBound cRound g),
                        Disjoint (U r) (W r),
                      ∃ hcard : ∀ r : Fin (largeCaseRoundBound cRound g),
                          (U r).card = (W r).card,
                        (∀ r : Fin (largeCaseRoundBound cRound g),
                            U r ∪ W r = Finset.univ) ∧
                          (SelectedOddLocalCrossbarGridTransportedRoundFamily.ofFinCuts
                            Hsys hcrossbars
                              (two_mul_largeCaseRoundBound_le_of_two_mul_roundConstant
                                hrounds)
                              (le_rfl :
                                largeCaseRoundBound cRound g ≤
                                  largeCaseRoundBound cRound g)
                              U W hdisj hcard).IsHalfEdgeExpander

/-- The unbundled KRV-style cut sequence packages into the transcript provider
used by the large-case crossbar-grid bridge. -/
theorem fixedRoundCutMatchingTranscriptProvider_of_unbundled
    {cRound : ℕ}
    (hprovider : FixedRoundCutMatchingUnbundledProvider.{u} cRound) :
    FixedRoundCutMatchingTranscriptProvider.{u} cRound := by
  intro V _ _ G ell w g Hsys hg hpow hdeg hrounds hwidth hcrossbars
  rcases hprovider G Hsys hg hpow hdeg hrounds hwidth hcrossbars with
    ⟨U, W, hdisj, hcard, hcover, hexp⟩
  let hlen : 2 * largeCaseRoundBound cRound g ≤ ell :=
    two_mul_largeCaseRoundBound_le_of_two_mul_roundConstant hrounds
  refine ⟨?_⟩
  exact
    { length_bound := hlen
      transcript :=
        { rounds_fit := le_rfl
          U := U
          W := W
          disjoint := hdisj
          card_eq := hcard
          coversAll := hcover
          half_expander := by
            simpa [hlen] using hexp } }

/-- Provider interface for the separator-to-grid handoff at the fixed
cut-matching degree scale, including the final polylogarithmic scale
inequality for the produced auxiliary grid order. -/
def FixedRoundSeparatorGridProvider (cRound cScale : ℕ) : Prop :=
  ∀ {g : ℕ},
    2 ≤ g →
      CrossbarContract.IsPowerOfTwo g →
        cScale * (Nat.log 2 g) ^ 2 < g →
          ∃ g' : ℕ,
            g ≤ cScale * g' * (Nat.log 2 g) ^ 2 ∧
              SeparatorGridMinorTheoremAt (largeCaseRoundBound cRound g) g'

/-- The separator-grid provider is monotone in the scale constant: a larger
constant weakens both the largeness side condition and the final scale
inequality. -/
theorem FixedRoundSeparatorGridProvider.mono_scale
    {cRound cScale cScale' : ℕ}
    (hprovider : FixedRoundSeparatorGridProvider cRound cScale)
    (hscale_le : cScale ≤ cScale') :
    FixedRoundSeparatorGridProvider cRound cScale' := by
  intro g hg hpow hlarge
  have hlarge_small : cScale * (Nat.log 2 g) ^ 2 < g := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right ((Nat.log 2 g) ^ 2) hscale_le) hlarge
  rcases hprovider hg hpow hlarge_small with ⟨g', hscale, hseparator⟩
  refine ⟨g', ?_, hseparator⟩
  exact hscale.trans (by
    gcongr)

/-- Combining the fixed-round cut-matching transcript provider with the
fixed-degree separator-to-grid provider gives the fixed-round large-case data
provider. -/
theorem fixedRoundLargeCaseCutMatchingDataProvider_of_transcript_and_separator
    {cRound cScale : ℕ}
    (htranscript :
      FixedRoundCutMatchingTranscriptProvider.{u} cRound)
    (hseparator : FixedRoundSeparatorGridProvider cRound cScale) :
    FixedRoundLargeCaseCutMatchingDataProvider.{u} cRound cScale := by
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hrounds hw hlarge hcrossbars
  rcases htranscript G Hsys hg hpow hmaxDegree hrounds hw hcrossbars with
    ⟨T⟩
  rcases hseparator hg hpow hlarge with ⟨g', hscale, hseparatorGrid⟩
  exact ⟨T.toFixedRoundLargeCaseCutMatchingData hscale hseparatorGrid⟩

/-- Existential combination of the two separated fixed-round providers. -/
theorem exists_fixedRoundLargeCaseCutMatchingDataProvider_of_transcript_and_separator
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingTranscriptProvider.{u} cRound ∧
          FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
      FixedRoundLargeCaseCutMatchingDataProvider.{u} cRound cScale := by
  rcases hproviders with
    ⟨cRound, cScale, hcRound, hcScale, htranscript, hseparator⟩
  exact ⟨cRound, cScale, hcRound, hcScale,
    fixedRoundLargeCaseCutMatchingDataProvider_of_transcript_and_separator
      htranscript hseparator⟩

/-- Existential combination using the unbundled KRV-style cut sequence
provider instead of an already packaged transcript provider. -/
theorem exists_fixedRoundLargeCaseCutMatchingDataProvider_of_unbundled_and_separator
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingUnbundledProvider.{u} cRound ∧
          FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
      FixedRoundLargeCaseCutMatchingDataProvider.{u} cRound cScale := by
  rcases hproviders with
    ⟨cRound, cScale, hcRound, hcScale, hunbundled, hseparator⟩
  exact
    exists_fixedRoundLargeCaseCutMatchingDataProvider_of_transcript_and_separator
      ⟨cRound, cScale, hcRound, hcScale,
        fixedRoundCutMatchingTranscriptProvider_of_unbundled hunbundled,
        hseparator⟩

/-- A fixed-round provider whose constants are both dominated by a single
constant gives the earlier large-case data provider. -/
theorem largeCaseCutMatchingDataProvider_of_fixedRound
    {cRound cScale c : ℕ}
    (hround_le : 2 * cRound ≤ c) (hscale_le : cScale ≤ c)
    (hfixed :
      FixedRoundLargeCaseCutMatchingDataProvider.{u} cRound cScale) :
    LargeCaseCutMatchingDataProvider.{u} c := by
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge hcrossbars
  have hrounds : (2 * cRound) * Nat.log 2 g ≤ ell := by
    exact (Nat.mul_le_mul_right (Nat.log 2 g) hround_le).trans hell
  have hlarge_fixed : cScale * (Nat.log 2 g) ^ 2 < g := by
    exact lt_of_le_of_lt (Nat.mul_le_mul_right ((Nat.log 2 g) ^ 2) hscale_le)
      hlarge
  rcases hfixed G Hsys hg hpow hmaxDegree hrounds hw hlarge_fixed hcrossbars with
    ⟨D⟩
  exact ⟨D.toLargeCaseCutMatchingData hscale_le⟩

/-- Existential wrapper for the fixed-round provider.  The single constant used
by the rest of the proof can be taken to be
`max (2*cRound) cScale`. -/
theorem exists_largeCaseCutMatchingDataProvider_of_fixedRound
    (hfixed :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundLargeCaseCutMatchingDataProvider.{u} cRound cScale) :
    ∃ c : ℕ, 0 < c ∧ LargeCaseCutMatchingDataProvider.{u} c := by
  rcases hfixed with ⟨cRound, cScale, hcRound, hcScale, hprovider⟩
  let c := max (2 * cRound) cScale
  refine ⟨c, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.mul_pos (by decide : 0 < 2) hcRound)
      (le_max_left (2 * cRound) cScale)
  · exact largeCaseCutMatchingDataProvider_of_fixedRound
      (le_max_left (2 * cRound) cScale)
      (le_max_right (2 * cRound) cScale)
      hprovider

/-- Direct existential conversion from the two separated fixed-round providers
to the single large-case data provider used by the older proof skeleton. -/
theorem exists_largeCaseCutMatchingDataProvider_of_transcript_and_separator
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingTranscriptProvider.{u} cRound ∧
          FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c : ℕ, 0 < c ∧ LargeCaseCutMatchingDataProvider.{u} c :=
  exists_largeCaseCutMatchingDataProvider_of_fixedRound
    (exists_fixedRoundLargeCaseCutMatchingDataProvider_of_transcript_and_separator
      hproviders)

/-- Direct existential conversion from the unbundled cut-sequence provider and
the fixed-round separator-grid provider to the single large-case data provider
used by the older proof skeleton. -/
theorem exists_largeCaseCutMatchingDataProvider_of_unbundled_and_separator
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        FixedRoundCutMatchingUnbundledProvider.{u} cRound ∧
          FixedRoundSeparatorGridProvider cRound cScale) :
    ∃ c : ℕ, 0 < c ∧ LargeCaseCutMatchingDataProvider.{u} c :=
  exists_largeCaseCutMatchingDataProvider_of_fixedRound
    (exists_fixedRoundLargeCaseCutMatchingDataProvider_of_unbundled_and_separator
      hproviders)

/-- The unique attachment vertex where a selected grid-indexed spoke meets
its own main path. -/
noncomputable def selectedOddCrossbarGridAttachment
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : V :=
  Classical.choose
    (selectedOddCrossbarGridSpoke_meets_own_main Hsys hcrossbars hlen i x)

/-- The selected attachment is an endpoint of the spoke. -/
theorem selectedOddCrossbarGridAttachment_spoke_endpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).IsEndpoint
      (selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x) :=
  (Classical.choose_spec
    (selectedOddCrossbarGridSpoke_meets_own_main Hsys hcrossbars hlen i x)).1

/-- The selected attachment is exactly the intersection of the selected main
path and spoke. -/
theorem selectedOddCrossbarGridAttachment_meetsExactly
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x).MeetsExactlyAt
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x) :=
  (Classical.choose_spec
    (selectedOddCrossbarGridSpoke_meets_own_main Hsys hcrossbars hlen i x)).2

/-- The selected attachment lies on the selected main path. -/
theorem selectedOddCrossbarGridAttachment_mem_main
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
      (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet := by
  let v := selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x
  have hmeet :=
    selectedOddCrossbarGridAttachment_meetsExactly Hsys hcrossbars hlen i x
  have hv : v ∈
      (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet ∩
        (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
    rw [GraphPath.MeetsExactlyAt] at hmeet
    rw [hmeet]
    simp [v]
  exact (Finset.mem_inter.mp hv).1

/-- The selected attachment lies on the selected spoke. -/
theorem selectedOddCrossbarGridAttachment_mem_spoke
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
  let v := selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x
  have hmeet :=
    selectedOddCrossbarGridAttachment_meetsExactly Hsys hcrossbars hlen i x
  have hv : v ∈
      (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet ∩
        (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
    rw [GraphPath.MeetsExactlyAt] at hmeet
    rw [hmeet]
    simp [v]
  exact (Finset.mem_inter.mp hv).2

/-- Distinct grid coordinates in one selected crossbar have distinct
attachment vertices. -/
theorem selectedOddCrossbarGridAttachment_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Function.Injective
      (selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i) := by
  intro x y hxy
  by_contra hne
  have hdisj :=
    selectedOddCrossbarGridMainPacking_nodeDisjoint Hsys hcrossbars hlen i hne
  have hx :
      selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
        (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i x).vertexSet :=
    selectedOddCrossbarGridAttachment_mem_main Hsys hcrossbars hlen i x
  have hy :
      selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x ∈
        (selectedOddCrossbarGridMainPath Hsys hcrossbars hlen i y).vertexSet := by
    simpa [hxy] using
      selectedOddCrossbarGridAttachment_mem_main Hsys hcrossbars hlen i y
  exact Finset.disjoint_left.mp hdisj hx hy

/-- The set of attachment vertices in a selected odd-cluster crossbar. -/
noncomputable def selectedOddCrossbarGridAttachmentSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  Finset.univ.image
    (selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i)

@[simp] theorem selectedOddCrossbarGridAttachmentSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarGridAttachmentSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  rw [selectedOddCrossbarGridAttachmentSet,
    Finset.card_image_of_injective]
  · simp [GridVertex, pow_two]
  · exact selectedOddCrossbarGridAttachment_injective Hsys hcrossbars hlen i

/-- Attachment vertices selected by a set of grid-coordinate indices. -/
noncomputable def selectedOddCrossbarGridAttachmentImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  U.image (selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i)

/-- The selected attachment image preserves cardinality. -/
@[simp] theorem selectedOddCrossbarGridAttachmentImage_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddCrossbarGridAttachmentImage Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddCrossbarGridAttachmentImage,
    Finset.card_image_of_injective]
  exact selectedOddCrossbarGridAttachment_injective Hsys hcrossbars hlen i

/-- Coordinate-indexed selected attachments are contained in the full
attachment set. -/
theorem selectedOddCrossbarGridAttachmentImage_subset_attachmentSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    selectedOddCrossbarGridAttachmentImage Hsys hcrossbars hlen i U ⊆
      selectedOddCrossbarGridAttachmentSet Hsys hcrossbars hlen i := by
  intro v hv
  rw [selectedOddCrossbarGridAttachmentImage] at hv
  rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
  rw [selectedOddCrossbarGridAttachmentSet]
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

/-- Disjoint coordinate sets have disjoint selected attachment images. -/
theorem selectedOddCrossbarGridAttachmentImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddCrossbarGridAttachmentImage Hsys hcrossbars hlen i U)
      (selectedOddCrossbarGridAttachmentImage Hsys hcrossbars hlen i W) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  rw [selectedOddCrossbarGridAttachmentImage] at hvU hvW
  rcases Finset.mem_image.mp hvU with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hvW with ⟨y, hy, hyx⟩
  have hxy : y = x :=
    selectedOddCrossbarGridAttachment_injective Hsys hcrossbars hlen i hyx
  exact Finset.disjoint_left.mp hUW hx (by simpa [hxy] using hy)

/-- The hair endpoint reached by a selected grid-indexed spoke. -/
noncomputable def selectedOddCrossbarGridHairEndpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : V :=
  (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).otherEndpoint
    (selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x)

/-- The selected hair endpoint lies on the selected spoke. -/
theorem selectedOddCrossbarGridHairEndpoint_mem_spoke
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
  simpa [selectedOddCrossbarGridHairEndpoint] using
    (GraphPath.otherEndpoint_mem_vertexSet
      (P := selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (v := selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x))

/-- The selected hair endpoint is an endpoint of the selected spoke. -/
theorem selectedOddCrossbarGridHairEndpoint_spoke_endpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).IsEndpoint
      (selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x) := by
  simpa [selectedOddCrossbarGridHairEndpoint] using
    GraphPath.otherEndpoint_isEndpoint
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x)

/-- A selected spoke connects its attachment point on the main path to its
selected hair endpoint. -/
theorem selectedOddCrossbarGridSpoke_connects_attachment_hairEndpoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).Connects
      {selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x}
      {selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x} := by
  let Q := selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x
  let a := selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x
  have ha : Q.IsEndpoint a :=
    selectedOddCrossbarGridAttachment_spoke_endpoint Hsys hcrossbars hlen i x
  by_cases hsource : Q.source = a
  · refine Or.inl ⟨?_, ?_⟩
    · simpa [Q, a] using hsource
    · have hhair :
          selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x =
            Q.target := by
        simp [selectedOddCrossbarGridHairEndpoint, GraphPath.otherEndpoint,
          Q, a, hsource]
      simpa [Q, a] using hhair.symm
  · have htarget : Q.target = a := by
      rcases ha with ha | ha
      · exact False.elim (hsource ha.symm)
      · exact ha.symm
    refine Or.inr ⟨?_, ?_⟩
    · have hhair :
          selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x =
            Q.source := by
        simp [selectedOddCrossbarGridHairEndpoint, GraphPath.otherEndpoint,
          Q, a, hsource]
      simpa [Q, a] using hhair.symm
    · simpa [Q, a] using htarget

/-- A selected spoke oriented from its attachment point to its hair endpoint. -/
noncomputable def selectedOddCrossbarGridOrientedSpokePath
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) : GraphPath G :=
  (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).orient
    (selectedOddCrossbarGridSpoke_connects_attachment_hairEndpoint
      Hsys hcrossbars hlen i x)

@[simp] theorem selectedOddCrossbarGridOrientedSpokePath_source
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).source =
      selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x := by
  simpa [selectedOddCrossbarGridOrientedSpokePath] using
    GraphPath.orient_source_mem
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddCrossbarGridSpoke_connects_attachment_hairEndpoint
        Hsys hcrossbars hlen i x)

@[simp] theorem selectedOddCrossbarGridOrientedSpokePath_target
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).target =
      selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x := by
  simpa [selectedOddCrossbarGridOrientedSpokePath] using
    GraphPath.orient_target_mem
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x)
      (selectedOddCrossbarGridSpoke_connects_attachment_hairEndpoint
        Hsys hcrossbars hlen i x)

@[simp] theorem selectedOddCrossbarGridOrientedSpokePath_vertexSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet =
      (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
  simp [selectedOddCrossbarGridOrientedSpokePath]

/-- The selected hair endpoint lies in the hair terminal set of the selected
cluster. -/
theorem selectedOddCrossbarGridHairEndpoint_mem_y
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
      Hsys.y (oddClusterIndex hlen i) := by
  simpa [selectedOddCrossbarGridHairEndpoint] using
    GraphPath.otherEndpoint_mem_of_connectsPathToSet_meetsExactlyAt
      (selectedOddCrossbarGridSpoke_connects Hsys hcrossbars hlen i x)
      (selectedOddCrossbarGridAttachment_meetsExactly Hsys hcrossbars hlen i x)

/-- Distinct grid coordinates in one selected crossbar have distinct hair
endpoints. -/
theorem selectedOddCrossbarGridHairEndpoint_injective
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Function.Injective
      (selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i) := by
  intro x y hxy
  by_contra hne
  have hdisj :=
    selectedOddCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen i hne
  have hx :
      selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
        (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet :=
    selectedOddCrossbarGridHairEndpoint_mem_spoke Hsys hcrossbars hlen i x
  have hy :
      selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x ∈
        (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i y).vertexSet := by
    simpa [hxy] using
      selectedOddCrossbarGridHairEndpoint_mem_spoke Hsys hcrossbars hlen i y
  exact Finset.disjoint_left.mp hdisj hx hy

/-- The set of hair endpoints reached by a selected odd-cluster crossbar. -/
noncomputable def selectedOddCrossbarGridHairEndpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) : Finset V :=
  Finset.univ.image
    (selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i)

@[simp] theorem selectedOddCrossbarGridHairEndpointSet_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  rw [selectedOddCrossbarGridHairEndpointSet,
    Finset.card_image_of_injective]
  · simp [GridVertex, pow_two]
  · exact selectedOddCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i

/-- Hair representatives selected by a set of grid-coordinate indices.  These
are the terminal sets used by one cut-matching iteration in the proof of
Theorem 3.2. -/
noncomputable def selectedOddCrossbarGridHairEndpointImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  U.image (selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i)

/-- The image of a coordinate set under the selected hair representative map
has the same cardinality. -/
@[simp] theorem selectedOddCrossbarGridHairEndpointImage_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddCrossbarGridHairEndpointImage,
    Finset.card_image_of_injective]
  exact selectedOddCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i

/-- A selected spoke connects the full selected attachment set to the full
selected hair endpoint set. -/
theorem selectedOddCrossbarGridSpoke_connects_attachmentSet_hairEndpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) (x : GridVertex g) :
    (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).Connects
      (selectedOddCrossbarGridAttachmentSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) := by
  have hconn :=
    selectedOddCrossbarGridSpoke_connects_attachment_hairEndpoint
      Hsys hcrossbars hlen i x
  rcases hconn with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · refine Or.inl ⟨?_, ?_⟩
    · have hsource_eq :
          (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).source =
            selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x := by
        simpa using hsource
      rw [selectedOddCrossbarGridAttachmentSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hsource_eq.symm⟩
    · have htarget_eq :
          (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).target =
            selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x := by
        simpa using htarget
      rw [selectedOddCrossbarGridHairEndpointSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, htarget_eq.symm⟩
  · refine Or.inr ⟨?_, ?_⟩
    · have hsource_eq :
          (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).source =
            selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x := by
        simpa using hsource
      rw [selectedOddCrossbarGridHairEndpointSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hsource_eq.symm⟩
    · have htarget_eq :
          (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).target =
            selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x := by
        simpa using htarget
      rw [selectedOddCrossbarGridAttachmentSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, htarget_eq.symm⟩

/-- The selected spokes, oriented from their main-path attachment points to
their hair endpoints. -/
noncomputable def selectedOddCrossbarGridSpokePacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PathPacking G
      (selectedOddCrossbarGridAttachmentSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) where
  Index := GridVertex g
  path := fun x =>
    selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x
  connects := by
    intro x
    refine Or.inl ⟨?_, ?_⟩
    · have hsource :
          (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).source =
            selectedOddCrossbarGridAttachment Hsys hcrossbars hlen i x := by
        simp
      rw [selectedOddCrossbarGridAttachmentSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hsource.symm⟩
    · have htarget :
          (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).target =
            selectedOddCrossbarGridHairEndpoint Hsys hcrossbars hlen i x := by
        simp
      rw [selectedOddCrossbarGridHairEndpointSet]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, htarget.symm⟩
  node_disjoint := by
    intro x y hxy
    change Disjoint
      ((selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet)
      ((selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i y).vertexSet)
    simpa using selectedOddCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen
      i hxy

@[simp] theorem selectedOddCrossbarGridSpokePacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarGridSpokePacking Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  change Fintype.card (GridVertex g) = g ^ 2
  rw [card_gridVertex, pow_two]

/-- The selected spokes as a perfect packing from attachment points to hair
endpoints. -/
noncomputable def selectedOddCrossbarGridSpokePerfectPacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    PerfectPathPacking G
      (selectedOddCrossbarGridAttachmentSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) :=
  (selectedOddCrossbarGridSpokePacking Hsys hcrossbars hlen i).toPerfectOfCardEq
    (by
      rw [selectedOddCrossbarGridSpokePacking_card,
        selectedOddCrossbarGridAttachmentSet_card])
    (by
      rw [selectedOddCrossbarGridSpokePacking_card,
        selectedOddCrossbarGridHairEndpointSet_card])

@[simp] theorem selectedOddCrossbarGridSpokePerfectPacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    (selectedOddCrossbarGridSpokePerfectPacking Hsys hcrossbars hlen i).card =
      g ^ 2 := by
  simpa [selectedOddCrossbarGridSpokePerfectPacking,
    PathPacking.toPerfectOfCardEq, PerfectPathPacking.card, PathPacking.card]
    using selectedOddCrossbarGridSpokePacking_card Hsys hcrossbars hlen i

/-- The selected spokes indexed by an arbitrary set of grid coordinates,
oriented as a perfect packing from the corresponding attachment image to the
corresponding hair endpoint image. -/
noncomputable def selectedOddCrossbarGridSpokeSubpacking
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    PerfectPathPacking G
      (selectedOddCrossbarGridAttachmentImage Hsys hcrossbars hlen i U)
      (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U) where
  toPathPacking := {
    Index := {x : GridVertex g // x ∈ U}
    path := fun x =>
      selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x.1
    connects := by
      intro x
      refine Or.inl ⟨?_, ?_⟩
      · rw [selectedOddCrossbarGridAttachmentImage]
        exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
      · rw [selectedOddCrossbarGridHairEndpointImage]
        exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
    node_disjoint := by
      intro x y hxy
      change Disjoint
        (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x.1).vertexSet
        (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i y.1).vertexSet
      rw [selectedOddCrossbarGridOrientedSpokePath_vertexSet,
        selectedOddCrossbarGridOrientedSpokePath_vertexSet]
      exact selectedOddCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen
        i (fun h => hxy (Subtype.ext h))
  }
  source_mem := by
    intro x
    rw [selectedOddCrossbarGridAttachmentImage]
    exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
  target_mem := by
    intro x
    rw [selectedOddCrossbarGridHairEndpointImage]
    exact Finset.mem_image.mpr ⟨x.1, x.2, by simp⟩
  source_bijective := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply selectedOddCrossbarGridAttachment_injective Hsys hcrossbars hlen i
      have hval := congrArg Subtype.val hxy
      simpa using hval
    · intro v
      rcases v with ⟨v, hv⟩
      rw [selectedOddCrossbarGridAttachmentImage] at hv
      rcases Finset.mem_image.mp hv with ⟨x, hx, hxv⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simp [hxv]
  target_bijective := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply selectedOddCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i
      have hval := congrArg Subtype.val hxy
      simpa using hval
    · intro v
      rcases v with ⟨v, hv⟩
      rw [selectedOddCrossbarGridHairEndpointImage] at hv
      rcases Finset.mem_image.mp hv with ⟨x, hx, hxv⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simp [hxv]

@[simp] theorem selectedOddCrossbarGridSpokeSubpacking_card
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U).card =
      U.card := by
  rw [selectedOddCrossbarGridSpokeSubpacking, PerfectPathPacking.card,
    Fintype.card_coe]

/-- The union of all vertices used by selected spokes whose coordinates lie in
`U`. -/
noncomputable def selectedOddCrossbarGridSpokeTraceImage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) : Finset V :=
  U.biUnion fun x =>
    (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet

/-- A selected oriented spoke with coordinate in `U` is contained in the trace
of `U`. -/
theorem selectedOddCrossbarGridOrientedSpokePath_vertexSet_subset_trace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U : Finset (GridVertex g)} {x : GridVertex g} (hx : x ∈ U) :
    (selectedOddCrossbarGridOrientedSpokePath Hsys hcrossbars hlen i x).vertexSet ⊆
      selectedOddCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U := by
  intro v hv
  rw [selectedOddCrossbarGridSpokeTraceImage]
  exact Finset.mem_biUnion.mpr ⟨x, hx, hv⟩

/-- The restricted selected-spoke packing stays inside its spoke trace. -/
theorem selectedOddCrossbarGridSpokeSubpacking_staysIn_trace
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    (selectedOddCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U).toPathPacking.StaysIn
      (selectedOddCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U) := by
  intro x
  exact selectedOddCrossbarGridOrientedSpokePath_vertexSet_subset_trace
    Hsys hcrossbars hlen i x.2

/-- Disjoint coordinate sets select disjoint spoke traces in a fixed
crossbar. -/
theorem selectedOddCrossbarGridSpokeTraceImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U)
      (selectedOddCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  rw [selectedOddCrossbarGridSpokeTraceImage] at hvU hvW
  rcases Finset.mem_biUnion.mp hvU with ⟨x, hx, hvx⟩
  rcases Finset.mem_biUnion.mp hvW with ⟨y, hy, hvy⟩
  by_cases hxy : x = y
  · subst y
    exact Finset.disjoint_left.mp hUW hx hy
  · have hdisj :=
      selectedOddCrossbarGridSpoke_nodeDisjoint Hsys hcrossbars hlen i hxy
    have hvx' :
        v ∈ (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i x).vertexSet := by
      simpa using hvx
    have hvy' :
        v ∈ (selectedOddCrossbarGridSpokePath Hsys hcrossbars hlen i y).vertexSet := by
      simpa using hvy
    exact Finset.disjoint_left.mp hdisj hvx' hvy'

/-- The selected hair endpoint set is contained in the corresponding `Y_i`
hair terminal set. -/
theorem selectedOddCrossbarGridHairEndpointSet_subset_y
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i ⊆
      Hsys.y (oddClusterIndex hlen i) := by
  intro v hv
  rw [selectedOddCrossbarGridHairEndpointSet] at hv
  rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
  exact selectedOddCrossbarGridHairEndpoint_mem_y Hsys hcrossbars hlen i x

/-- The selected source terminals lie in the corresponding base cluster. -/
theorem selectedOddCrossbarGridMainSourceSet_subset_cluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) := by
  intro v hv
  exact Hsys.base.left_subset_cluster (oddClusterIndex hlen i)
    (selectedOddCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i
      hv)

/-- The selected target terminals lie in the corresponding base cluster. -/
theorem selectedOddCrossbarGridMainTargetSet_subset_cluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i ⊆
      Hsys.base.cluster (oddClusterIndex hlen i) := by
  intro v hv
  exact Hsys.base.right_subset_cluster (oddClusterIndex hlen i)
    (selectedOddCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
      hv)

/-- The selected hair endpoints lie in the corresponding hair cluster. -/
theorem selectedOddCrossbarGridHairEndpointSet_subset_hairCluster
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i ⊆
      Hsys.hairCluster (oddClusterIndex hlen i) := by
  intro v hv
  exact Hsys.y_subset_hairCluster (oddClusterIndex hlen i)
    (selectedOddCrossbarGridHairEndpointSet_subset_y Hsys hcrossbars hlen i
      hv)

/-- The selected source terminals inherit node-well-linkedness from the left
nails of the selected strong cluster. -/
theorem selectedOddCrossbarGridMainSourceSet_nodeWellLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeWellLinkedIn G (Hsys.base.cluster (oddClusterIndex hlen i))
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i) :=
  (Hsys.base.left_nodeWellLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i)

/-- The selected target terminals inherit node-well-linkedness from the right
nails of the selected strong cluster. -/
theorem selectedOddCrossbarGridMainTargetSet_nodeWellLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeWellLinkedIn G (Hsys.base.cluster (oddClusterIndex hlen i))
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i) :=
  (Hsys.base.right_nodeWellLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i)

/-- The selected source and target terminals remain linked inside the selected
strong cluster. -/
theorem selectedOddCrossbarGridMainSourceTarget_nodeLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeLinkedIn G (Hsys.base.cluster (oddClusterIndex hlen i))
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i) :=
  (Hsys.base.left_right_nodeLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i)
    (selectedOddCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i)

/-- The selected hair endpoints inherit node-well-linkedness from the hair
cluster. -/
theorem selectedOddCrossbarGridHairEndpointSet_nodeWellLinked
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    NodeWellLinkedIn G (Hsys.hairCluster (oddClusterIndex hlen i))
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) :=
  (Hsys.y_nodeWellLinked (oddClusterIndex hlen i)).mono_terminals
    (selectedOddCrossbarGridHairEndpointSet_subset_y Hsys hcrossbars hlen i)

/-- Coordinate-indexed selected hair representatives are contained in the full
selected hair endpoint set. -/
theorem selectedOddCrossbarGridHairEndpointImage_subset_endpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    (U : Finset (GridVertex g)) :
    selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U ⊆
      selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i := by
  intro v hv
  rw [selectedOddCrossbarGridHairEndpointImage] at hv
  rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
  rw [selectedOddCrossbarGridHairEndpointSet]
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

/-- Disjoint coordinate sets have disjoint selected hair representative
images. -/
theorem selectedOddCrossbarGridHairEndpointImage_disjoint
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    Disjoint
      (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
      (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W) := by
  rw [Finset.disjoint_left]
  intro v hvU hvW
  rw [selectedOddCrossbarGridHairEndpointImage] at hvU hvW
  rcases Finset.mem_image.mp hvU with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hvW with ⟨y, hy, hyx⟩
  have hxy : y = x :=
    selectedOddCrossbarGridHairEndpoint_injective Hsys hcrossbars hlen i hyx
  exact Finset.disjoint_left.mp hUW hx (by simpa [hxy] using hy)

/-- The hair cluster links the selected representatives of any two disjoint
coordinate sets, with the expected full cardinality. -/
theorem selectedOddCrossbarGridHairEndpointImage_linkage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W) :
    ∃ P : PathPacking G
        (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
        (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W),
      P.card = min U.card W.card ∧
        P.StaysIn (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  have hwell :=
    selectedOddCrossbarGridHairEndpointSet_nodeWellLinked
      Hsys hcrossbars hlen i
  rcases hwell.2
      (selectedOddCrossbarGridHairEndpointImage_subset_endpointSet
        Hsys hcrossbars hlen i U)
      (selectedOddCrossbarGridHairEndpointImage_subset_endpointSet
        Hsys hcrossbars hlen i W)
      (selectedOddCrossbarGridHairEndpointImage_disjoint
        Hsys hcrossbars hlen i hUW) with
    ⟨P, hPcard, hstay⟩
  refine ⟨P, ?_, hstay⟩
  simpa [selectedOddCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i U,
    selectedOddCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i W]
    using hPcard

/-- Equal-size disjoint coordinate sets have a perfect linkage between their
selected hair representatives. -/
theorem selectedOddCrossbarGridHairEndpointImage_perfectLinkage
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ P : PerfectPathPacking G
        (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
        (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W),
      P.card = U.card ∧
        P.toPathPacking.StaysIn (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  rcases selectedOddCrossbarGridHairEndpointImage_linkage Hsys hcrossbars hlen
      i hUW with
    ⟨P, hPcard, hstay⟩
  have hPcardU : P.card = U.card := by
    simpa [hcard] using hPcard
  have hPcardImageU :
      P.card =
        (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U).card :=
    hPcardU.trans
      (selectedOddCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i U).symm
  have hPcardImageW :
      P.card =
        (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W).card :=
    (hPcardU.trans hcard).trans
      (selectedOddCrossbarGridHairEndpointImage_card Hsys hcrossbars hlen i W).symm
  refine ⟨P.toPerfectOfCardEq hPcardImageU hPcardImageW, ?_, ?_⟩
  · simpa [PathPacking.toPerfectOfCardEq, PerfectPathPacking.card,
      PathPacking.card] using hPcardU
  · exact PathPacking.orient_staysIn hstay

/-- One cut-matching round supplies three compatible pieces: selected spokes
from the left coordinate subset into the hair cluster, a hair-cluster linkage,
and selected spokes back out to the right coordinate subset. -/
theorem exists_selectedOddCrossbarGridMatchingPieces
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ L : PerfectPathPacking G
        (selectedOddCrossbarGridAttachmentImage Hsys hcrossbars hlen i U)
        (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U),
      ∃ M : PerfectPathPacking G
          (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i U)
          (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W),
        ∃ R : PerfectPathPacking G
            (selectedOddCrossbarGridHairEndpointImage Hsys hcrossbars hlen i W)
            (selectedOddCrossbarGridAttachmentImage Hsys hcrossbars hlen i W),
          L.card = U.card ∧
            M.card = U.card ∧
              R.card = W.card ∧
                L.toPathPacking.StaysIn
                  (selectedOddCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i U) ∧
                  R.toPathPacking.StaysIn
                    (selectedOddCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W) ∧
                    M.toPathPacking.StaysIn
                      (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  let L := selectedOddCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i U
  rcases selectedOddCrossbarGridHairEndpointImage_perfectLinkage
      Hsys hcrossbars hlen i hUW hcard with
    ⟨M, hMcard, hMstay⟩
  let R :=
    (selectedOddCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W).reverse
  refine ⟨L, M, R, ?_, hMcard, ?_, ?_, ?_, hMstay⟩
  · exact selectedOddCrossbarGridSpokeSubpacking_card Hsys hcrossbars hlen i U
  · change
      ((selectedOddCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W).reverse).card =
        W.card
    simp [
      selectedOddCrossbarGridSpokeSubpacking_card Hsys hcrossbars hlen i W
    ]
  · exact selectedOddCrossbarGridSpokeSubpacking_staysIn_trace
      Hsys hcrossbars hlen i U
  · change
      ((selectedOddCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W).reverse).toPathPacking.StaysIn
        (selectedOddCrossbarGridSpokeTraceImage Hsys hcrossbars hlen i W)
    exact PerfectPathPacking.reverse_staysIn
      (selectedOddCrossbarGridSpokeSubpacking Hsys hcrossbars hlen i W)
      (selectedOddCrossbarGridSpokeSubpacking_staysIn_trace
        Hsys hcrossbars hlen i W)

/-- Local-crossbar version of `exists_selectedOddCrossbarGridMatchingPieces`.
The local witnesses are offered as an ambient `Nonempty` family.  This theorem
uses only the crossbar axioms of the selected ambient witnesses; edge-locality
of a concrete local witness is provided separately by the
`localCrossbarAsAmbient_*_edgeSet_subset_hairLocalGraph` lemmas above. -/
theorem exists_selectedOddLocalCrossbarGridMatchingPieces
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m)
    {U W : Finset (GridVertex g)} (hUW : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ L : PerfectPathPacking G
        (selectedOddCrossbarGridAttachmentImage Hsys
          (ambientCrossbars_of_local Hsys hcrossbars) hlen i U)
        (selectedOddCrossbarGridHairEndpointImage Hsys
          (ambientCrossbars_of_local Hsys hcrossbars) hlen i U),
      ∃ M : PerfectPathPacking G
          (selectedOddCrossbarGridHairEndpointImage Hsys
            (ambientCrossbars_of_local Hsys hcrossbars) hlen i U)
          (selectedOddCrossbarGridHairEndpointImage Hsys
            (ambientCrossbars_of_local Hsys hcrossbars) hlen i W),
        ∃ R : PerfectPathPacking G
            (selectedOddCrossbarGridHairEndpointImage Hsys
              (ambientCrossbars_of_local Hsys hcrossbars) hlen i W)
            (selectedOddCrossbarGridAttachmentImage Hsys
              (ambientCrossbars_of_local Hsys hcrossbars) hlen i W),
          L.card = U.card ∧
            M.card = U.card ∧
              R.card = W.card ∧
                L.toPathPacking.StaysIn
                  (selectedOddCrossbarGridSpokeTraceImage Hsys
                    (ambientCrossbars_of_local Hsys hcrossbars) hlen i U) ∧
                  R.toPathPacking.StaysIn
                    (selectedOddCrossbarGridSpokeTraceImage Hsys
                      (ambientCrossbars_of_local Hsys hcrossbars) hlen i W) ∧
                    M.toPathPacking.StaysIn
                      (Hsys.hairCluster (oddClusterIndex hlen i)) := by
  exact exists_selectedOddCrossbarGridMatchingPieces Hsys
    (ambientCrossbars_of_local Hsys hcrossbars) hlen i hUW hcard

/-- The selected left and right main-path endpoint sets are disjoint. -/
theorem selectedOddCrossbarGridMainSourceSet_disjoint_targetSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Disjoint
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i) := by
  rw [Finset.disjoint_left]
  intro v hvsource hvtarget
  exact Finset.disjoint_left.mp
    (Hsys.base.left_right_disjoint (oddClusterIndex hlen i))
    (selectedOddCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i
      hvsource)
    (selectedOddCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
      hvtarget)

/-- The selected left main-path endpoint set is disjoint from the selected
hair endpoints. -/
theorem selectedOddCrossbarGridMainSourceSet_disjoint_hairEndpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Disjoint
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) := by
  rw [Finset.disjoint_left]
  intro v hvsource hvhair
  have hvbase :
      v ∈ Hsys.base.cluster (oddClusterIndex hlen i) :=
    Hsys.base.left_subset_cluster (oddClusterIndex hlen i)
      (selectedOddCrossbarGridMainSourceSet_subset_left Hsys hcrossbars hlen i
        hvsource)
  have hvhairCluster :
      v ∈ Hsys.hairCluster (oddClusterIndex hlen i) :=
    Hsys.y_subset_hairCluster (oddClusterIndex hlen i)
      (selectedOddCrossbarGridHairEndpointSet_subset_y Hsys hcrossbars hlen i
        hvhair)
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint_base (oddClusterIndex hlen i)
      (oddClusterIndex hlen i))
    hvhairCluster hvbase

/-- The selected right main-path endpoint set is disjoint from the selected
hair endpoints. -/
theorem selectedOddCrossbarGridMainTargetSet_disjoint_hairEndpointSet
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    Disjoint
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i) := by
  rw [Finset.disjoint_left]
  intro v hvtarget hvhair
  have hvbase :
      v ∈ Hsys.base.cluster (oddClusterIndex hlen i) :=
    Hsys.base.right_subset_cluster (oddClusterIndex hlen i)
      (selectedOddCrossbarGridMainTargetSet_subset_right Hsys hcrossbars hlen i
        hvtarget)
  have hvhairCluster :
      v ∈ Hsys.hairCluster (oddClusterIndex hlen i) :=
    Hsys.y_subset_hairCluster (oddClusterIndex hlen i)
      (selectedOddCrossbarGridHairEndpointSet_subset_y Hsys hcrossbars hlen i
        hvhair)
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint_base (oddClusterIndex hlen i)
      (oddClusterIndex hlen i))
    hvhairCluster hvbase

/-- Selected source endpoint sets in distinct selected odd clusters are
disjoint. -/
theorem selectedOddCrossbarGridMainSourceSet_disjoint_sourceSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.base.cluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen i
      hvi)
    (selectedOddCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen j
      hvj)

/-- Selected source and target endpoint sets in distinct selected odd clusters
are disjoint. -/
theorem selectedOddCrossbarGridMainSourceSet_disjoint_targetSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.base.cluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen i
      hvi)
    (selectedOddCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen j
      hvj)

/-- Selected target endpoint sets in distinct selected odd clusters are
disjoint. -/
theorem selectedOddCrossbarGridMainTargetSet_disjoint_targetSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.base.cluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen i
      hvi)
    (selectedOddCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen j
      hvj)

/-- Selected hair endpoint sets in distinct selected odd clusters are
disjoint. -/
theorem selectedOddCrossbarGridHairEndpointSet_disjoint_hairEndpointSet_of_ne
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) {i j : Fin m} (hij : i ≠ j) :
    Disjoint
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint (oddClusterIndex_ne_of_ne hlen hij))
    (selectedOddCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen i hvi)
    (selectedOddCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen j hvj)

/-- A selected source endpoint set is disjoint from every selected hair
endpoint set. -/
theorem selectedOddCrossbarGridMainSourceSet_disjoint_hairEndpointSet'
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) :
    Disjoint
      (selectedOddCrossbarGridMainSourceSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvsource hvhair
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint_base (oddClusterIndex hlen j)
      (oddClusterIndex hlen i))
    (selectedOddCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen j hvhair)
    (selectedOddCrossbarGridMainSourceSet_subset_cluster Hsys hcrossbars hlen i
      hvsource)

/-- A selected target endpoint set is disjoint from every selected hair
endpoint set. -/
theorem selectedOddCrossbarGridMainTargetSet_disjoint_hairEndpointSet'
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w g m : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hcrossbars :
      ∀ i : Fin ell, OneBasedOdd i →
        Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)))
    (hlen : 2 * m ≤ ell) (i j : Fin m) :
    Disjoint
      (selectedOddCrossbarGridMainTargetSet Hsys hcrossbars hlen i)
      (selectedOddCrossbarGridHairEndpointSet Hsys hcrossbars hlen j) := by
  rw [Finset.disjoint_left]
  intro v hvtarget hvhair
  exact Finset.disjoint_left.mp
    (Hsys.hairCluster_disjoint_base (oddClusterIndex hlen j)
      (oddClusterIndex hlen i))
    (selectedOddCrossbarGridHairEndpointSet_subset_hairCluster Hsys hcrossbars
      hlen j hvhair)
    (selectedOddCrossbarGridMainTargetSet_subset_cluster Hsys hcrossbars hlen i
      hvtarget)

/-- Small crossbar parameters are handled by the `1 x 1` grid minor contained
in the base strong path-of-sets system. -/
theorem gridMinor_of_hairy_pathOfSets_and_crossbars_of_le_constant
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w c g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hgsmall : g ≤ c * (Nat.log 2 g) ^ 2) :
    ∃ g' : ℕ,
      g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧ ContainsGridMinor G g' := by
  refine ⟨1, ?_, PathOfSetsGrid.containsGridMinor_one_of_strong_pathOfSets Hsys.base⟩
  simpa [Nat.mul_assoc] using hgsmall

/-- Crossbar-grid assembly reduced to the remaining cut-matching/separator
data-producing theorem.

This theorem no longer uses the large-case contract.  Its single extra
hypothesis is the precise remaining Chuzhoy--Tan obligation: in the large
case, construct `LargeCaseCutMatchingData` from the hairy path-of-sets system
and the odd-cluster crossbars. -/
theorem gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingData
    (c : ℕ) (_hc : 0 < c)
    (hlargeData :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                c * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    c * (Nat.log 2 g) ^ 2 < g →
                      (hcrossbars :
                        ∀ i : Fin ell, OneBasedOdd i →
                          Nonempty (Crossbar (Hsys.hairLocalGraph i)
                            (Hsys.base.left i) (Hsys.base.right i)
                            (Hsys.y i) (g ^ 2))) →
                        LargeCaseCutMatchingData Hsys hcrossbars c) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {ell w g : ℕ}
      (Hsys : HairyPathOfSetsSystem G ell w),
        2 ≤ g →
          CrossbarContract.IsPowerOfTwo g →
            MaxDegreeAtMost G 3 →
              c * Nat.log 2 g ≤ ell →
                g ^ 2 ≤ w →
                  (∀ i : Fin ell, OneBasedOdd i →
                    Nonempty (Crossbar (Hsys.hairLocalGraph i)
                      (Hsys.base.left i) (Hsys.base.right i)
                      (Hsys.y i) (g ^ 2))) →
                    ∃ g' : ℕ,
                      g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧
                        ContainsGridMinor G g' := by
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hcrossbars
  by_cases hsmall : g ≤ c * (Nat.log 2 g) ^ 2
  · exact gridMinor_of_hairy_pathOfSets_and_crossbars_of_le_constant Hsys hsmall
  · exact
      (hlargeData G Hsys hg hpow hmaxDegree hell hw
        (Nat.lt_of_not_ge hsmall) hcrossbars).exists_gridMinor hg

/-- Existential-constant version of
`gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingData`. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingData
    (hlargeData :
      ∃ c : ℕ, 0 < c ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g : ℕ}
          (Hsys : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              CrossbarContract.IsPowerOfTwo g →
                MaxDegreeAtMost G 3 →
                  c * Nat.log 2 g ≤ ell →
                    g ^ 2 ≤ w →
                      c * (Nat.log 2 g) ^ 2 < g →
                        (hcrossbars :
                          ∀ i : Fin ell, OneBasedOdd i →
                            Nonempty (Crossbar (Hsys.hairLocalGraph i)
                              (Hsys.base.left i) (Hsys.base.right i)
                              (Hsys.y i) (g ^ 2))) →
                          Nonempty
                            (LargeCaseCutMatchingData Hsys hcrossbars c)) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                c * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    (∀ i : Fin ell, OneBasedOdd i →
                      Nonempty (Crossbar (Hsys.hairLocalGraph i)
                        (Hsys.base.left i) (Hsys.base.right i)
                        (Hsys.y i) (g ^ 2))) →
                      ∃ g' : ℕ,
                        g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g' := by
  rcases hlargeData with ⟨c, hc, hdata⟩
  refine ⟨c, hc,
    gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingData
      c hc ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge hcrossbars
  exact Classical.choice
    (hdata G Hsys hg hpow hmaxDegree hell hw hlarge hcrossbars)

/-- Provider-interface version of
`exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingData`. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingDataProvider
    (hlargeData :
      ∃ c : ℕ, 0 < c ∧ LargeCaseCutMatchingDataProvider.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                c * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    (∀ i : Fin ell, OneBasedOdd i →
                      Nonempty (Crossbar (Hsys.hairLocalGraph i)
                        (Hsys.base.left i) (Hsys.base.right i)
                        (Hsys.y i) (g ^ 2))) →
                      ∃ g' : ℕ,
                        g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g' :=
by
  rcases hlargeData with ⟨c, hc, hprovider⟩
  refine ⟨c, hc,
    gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingData
      c hc ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge hcrossbars
  exact Classical.choice
    (hprovider G Hsys hg hpow hmaxDegree hell hw hlarge hcrossbars)


end HairyCrossbarGrid
end SimpleGraph

end Lax17Proofs
