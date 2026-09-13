import Lax17Proofs.Source.Exponent7.AlternatingMatchingRows
import Lax17Proofs.Source.Exponent7.OrderedBridgeGridGeometry

namespace Lax17Proofs

/-!
# Grid minors from alternating prescribed matchings

For column `c`, the short-wide construction uses clusters `2c` and `2c+1`.
On each selected global row, take the segment from the source of its local
trace in cluster `2c` to the target of its local trace in cluster `2c+1`.
These segments are connected, pairwise disjoint, and ordered by column. Their
endpoints include those of the prescribed matching bridges. Simultaneous
alternating matching realizations therefore yield a grid minor.
-/

namespace SimpleGraph
namespace Exponent7

open ChekuriChuzhoy AppendixB1

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {g w : ℕ}
variable {P : StrongPathOfSetsSystem G (2 * g) w}

namespace AlternatingClusterRealizations

/-- The selected global horizontal row. -/
noncomputable def globalRow
    (B : AlternatingClusterRealizations g P) (r : Fin g) : GraphPath G :=
  B.threads.threading.packing.path (B.threads.row r)

/-- The local row trace in the odd matching cluster of column `c`. -/
noncomputable def oddLocalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g) : GraphPath G :=
  (StrongPathOfSetsSystem.clusterLinkage P
    (oddMatchingCluster c)).path
      (B.threads.localRow (oddMatchingCluster c) r)

/-- The local row trace in the even matching cluster of column `c`. -/
noncomputable def evenLocalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g) : GraphPath G :=
  (StrongPathOfSetsSystem.clusterLinkage P
    (evenMatchingCluster c)).path
      (B.threads.localRow (evenMatchingCluster c) r)

theorem oddLocalRow_meets_globalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    ((B.globalRow r).vertexSet ∩ (B.oddLocalRow r c).vertexSet).Nonempty := by
  refine ⟨(B.oddLocalRow r c).source, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · apply B.threads.local_path_subset_global (oddMatchingCluster c) r
    exact GraphPath.source_mem_vertexSet _
  · exact GraphPath.source_mem_vertexSet _

theorem evenLocalRow_meets_globalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    ((B.globalRow r).vertexSet ∩ (B.evenLocalRow r c).vertexSet).Nonempty := by
  refine ⟨(B.evenLocalRow r c).target, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · apply B.threads.local_path_subset_global (evenMatchingCluster c) r
    exact GraphPath.target_mem_vertexSet _
  · exact GraphPath.target_mem_vertexSet _

/-- First global-row hit of the odd-cluster local trace. -/
noncomputable def columnStart
    (B : AlternatingClusterRealizations g P) (r c : Fin g) : V :=
  (B.globalRow r).firstHitVertex
    (B.oddLocalRow r c).vertexSet (B.oddLocalRow_meets_globalRow r c)

/-- Last global-row hit of the even-cluster local trace. -/
noncomputable def columnEnd
    (B : AlternatingClusterRealizations g P) (r c : Fin g) : V :=
  (B.globalRow r).lastHitVertex
    (B.evenLocalRow r c).vertexSet (B.evenLocalRow_meets_globalRow r c)

theorem columnStart_mem_globalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    B.columnStart r c ∈ (B.globalRow r).vertexSet := by
  exact (B.globalRow r).firstHitVertex_mem_vertexSet
    (B.oddLocalRow r c).vertexSet (B.oddLocalRow_meets_globalRow r c)

theorem columnEnd_mem_globalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    B.columnEnd r c ∈ (B.globalRow r).vertexSet := by
  exact (B.globalRow r).lastHitVertex_mem_vertexSet
    (B.evenLocalRow r c).vertexSet (B.evenLocalRow_meets_globalRow r c)

theorem columnStart_mem_cluster
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    B.columnStart r c ∈ P.cluster (oddMatchingCluster c) :=
  StrongPathOfSetsSystem.clusterLinkage_staysIn P
    (oddMatchingCluster c) _
    ((B.globalRow r).firstHitVertex_mem_set
      (B.oddLocalRow r c).vertexSet (B.oddLocalRow_meets_globalRow r c))

theorem columnEnd_mem_cluster
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    B.columnEnd r c ∈ P.cluster (evenMatchingCluster c) :=
  StrongPathOfSetsSystem.clusterLinkage_staysIn P
    (evenMatchingCluster c) _
    ((B.globalRow r).lastHitVertex_mem_set
      (B.evenLocalRow r c).vertexSet (B.evenLocalRow_meets_globalRow r c))

theorem columnStart_before_columnEnd
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    (B.globalRow r).Before (B.columnStart r c) (B.columnEnd r c) :=
  B.threads.global_clusters_ordered r
    (oddMatchingCluster_lt_even c)
    (B.columnStart_mem_globalRow r c)
    (B.columnStart_mem_cluster r c)
    (B.columnEnd_mem_globalRow r c)
    (B.columnEnd_mem_cluster r c)

/-- The row block assigned to `(r,c)`. -/
noncomputable def columnBlockPath
    (B : AlternatingClusterRealizations g P) (r c : Fin g) : GraphPath G :=
  (B.globalRow r).segmentOfBefore (B.columnStart_before_columnEnd r c)

noncomputable def columnBlock
    (B : AlternatingClusterRealizations g P) (r c : Fin g) : Finset V :=
  (B.columnBlockPath r c).vertexSet

theorem columnBlock_subset_globalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    B.columnBlock r c ⊆ (B.globalRow r).vertexSet :=
  (B.globalRow r).segmentOfBefore_vertexSet_subset
    (B.columnStart_before_columnEnd r c)

theorem columnBlock_nonempty
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    (B.columnBlock r c).Nonempty :=
  ⟨(B.columnBlockPath r c).source,
    GraphPath.source_mem_vertexSet _⟩

theorem columnBlock_meets
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    ((B.globalRow r).vertexSet ∩ B.columnBlock r c).Nonempty := by
  rcases B.columnBlock_nonempty r c with ⟨v, hv⟩
  exact ⟨v, Finset.mem_inter.mpr
    ⟨B.columnBlock_subset_globalRow r c hv, hv⟩⟩

theorem columnEnd_before_columnStart
    (B : AlternatingClusterRealizations g P) (r : Fin g)
    {c d : Fin g} (hcd : c.1 < d.1) :
    (B.globalRow r).Before (B.columnEnd r c) (B.columnStart r d) :=
  B.threads.global_clusters_ordered r
    (evenMatchingCluster_lt_oddMatchingCluster hcd)
    (B.columnEnd_mem_globalRow r c)
    (B.columnEnd_mem_cluster r c)
    (B.columnStart_mem_globalRow r d)
    (B.columnStart_mem_cluster r d)

theorem columnEnd_ne_columnStart
    (B : AlternatingClusterRealizations g P) (r : Fin g)
    {c d : Fin g} (hcd : c.1 < d.1) :
    B.columnEnd r c ≠ B.columnStart r d := by
  intro h
  exact Finset.disjoint_left.mp
    (P.cluster_disjoint (by
      intro hcluster
      have hval := congrArg Fin.val hcluster
      simp at hval
      omega))
    (B.columnEnd_mem_cluster r c)
    (h ▸ B.columnStart_mem_cluster r d)

theorem columnBlock_disjoint_of_lt
    (B : AlternatingClusterRealizations g P) (r : Fin g)
    {c d : Fin g} (hcd : c.1 < d.1) :
    Disjoint (B.columnBlock r c) (B.columnBlock r d) :=
  (B.globalRow r).segmentOfBefore_disjoint_of_strict_target_before_source
    (B.columnStart_before_columnEnd r c)
    (B.columnStart_before_columnEnd r d)
    (B.columnEnd_before_columnStart r hcd)
    (B.columnEnd_ne_columnStart r hcd)

theorem columnBlock_pairwise_disjoint
    (B : AlternatingClusterRealizations g P) (r : Fin g)
    {c d : Fin g} (hcd : c ≠ d) :
    Disjoint (B.columnBlock r c) (B.columnBlock r d) := by
  have hval : c.1 ≠ d.1 := fun h => hcd (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact B.columnBlock_disjoint_of_lt r hlt
  · exact Disjoint.symm (B.columnBlock_disjoint_of_lt r hgt)

theorem columnBlock_ordered
    (B : AlternatingClusterRealizations g P) (r : Fin g)
    {c d : Fin g} (hcd : c.1 < d.1) :
    (B.globalRow r).Before
      ((B.globalRow r).lastHitVertex
        (B.columnBlock r c) (B.columnBlock_meets r c))
      ((B.globalRow r).firstHitVertex
        (B.columnBlock r d) (B.columnBlock_meets r d)) := by
  apply (B.globalRow r).before_trans
  · exact (B.globalRow r).before_of_mem_segmentOfBefore_right
      (B.columnStart_before_columnEnd r c)
      ((B.globalRow r).lastHitVertex_mem_set
        (B.columnBlock r c) (B.columnBlock_meets r c))
  apply (B.globalRow r).before_trans (B.columnEnd_before_columnStart r hcd)
  exact (B.globalRow r).before_of_mem_segmentOfBefore_left
    (B.columnStart_before_columnEnd r d)
    ((B.globalRow r).firstHitVertex_mem_set
      (B.columnBlock r d) (B.columnBlock_meets r d))

/-- The ordered block family on selected global row `r`. -/
noncomputable def rowBlocks
    (B : AlternatingClusterRealizations g P) (r : Fin g) :
    OrderedPathBlockFamily (B.globalRow r) g where
  block := B.columnBlock r
  meets := B.columnBlock_meets r
  block_subset := B.columnBlock_subset_globalRow r
  pairwise_disjoint := by
    intro c d hcd
    exact B.columnBlock_pairwise_disjoint r hcd
  ordered := by
    intro c d hcd
    exact B.columnBlock_ordered r hcd

theorem rowBlock_connected
    (B : AlternatingClusterRealizations g P) (r c : Fin g) :
    (G.induce {v : V | v ∈ (B.rowBlocks r).block c}).Connected := by
  simpa [rowBlocks, columnBlock] using
    (B.columnBlockPath r c).connected_induce_vertexSet

/-! ## Canonical bridge for a forward consecutive row pair -/

/-- Successor row, when the successor remains below `g`. -/
def successorRow (r : Fin g) (hr : r.1 + 1 < g) : Fin g :=
  ⟨r.1 + 1, hr⟩

/-- The edge of the odd matching beginning at an even row. -/
def oddEdgeOfEven (r : Fin g) (hr : r.1 + 1 < g)
    (heven : r.1 % 2 = 0) :
    (oddRowMatching g).EdgeIndex :=
  ⟨r.1 / 2, by omega⟩

/-- The edge of the even matching beginning at an odd row. -/
def evenEdgeOfOdd (r : Fin g) (hr : r.1 + 1 < g)
    (hodd : r.1 % 2 = 1) :
    (evenRowMatching g).EdgeIndex :=
  ⟨r.1 / 2, by omega⟩

@[simp] theorem oddRowMatching_left_oddEdgeOfEven
    (r : Fin g) (hr : r.1 + 1 < g) (heven : r.1 % 2 = 0) :
    (oddRowMatching g).left (oddEdgeOfEven r hr heven) = r := by
  apply Fin.ext
  simp [oddEdgeOfEven, oddRowMatching]
  omega

@[simp] theorem oddRowMatching_right_oddEdgeOfEven
    (r : Fin g) (hr : r.1 + 1 < g) (heven : r.1 % 2 = 0) :
    (oddRowMatching g).right (oddEdgeOfEven r hr heven) =
      successorRow r hr := by
  apply Fin.ext
  simp [oddEdgeOfEven, oddRowMatching, successorRow]
  omega

@[simp] theorem evenRowMatching_left_evenEdgeOfOdd
    (r : Fin g) (hr : r.1 + 1 < g) (hodd : r.1 % 2 = 1) :
    (evenRowMatching g).left (evenEdgeOfOdd r hr hodd) = r := by
  apply Fin.ext
  simp [evenEdgeOfOdd, evenRowMatching]
  omega

@[simp] theorem evenRowMatching_right_evenEdgeOfOdd
    (r : Fin g) (hr : r.1 + 1 < g) (hodd : r.1 % 2 = 1) :
    (evenRowMatching g).right (evenEdgeOfOdd r hr hodd) =
      successorRow r hr := by
  apply Fin.ext
  simp [evenEdgeOfOdd, evenRowMatching, successorRow]
  omega

theorem mem_columnBlock_of_mem_oddLocalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g)
    {v : V} (hv : v ∈ (B.oddLocalRow r c).vertexSet) :
    v ∈ B.columnBlock r c := by
  have hvGlobal : v ∈ (B.globalRow r).vertexSet :=
    B.threads.local_path_subset_global (oddMatchingCluster c) r hv
  have hvCluster : v ∈ P.cluster (oddMatchingCluster c) :=
    StrongPathOfSetsSystem.clusterLinkage_staysIn P
      (oddMatchingCluster c) _ hv
  apply (B.globalRow r).mem_segmentOfBefore_of_before_of_before
    (B.columnStart_before_columnEnd r c)
  · exact (B.globalRow r).firstHitVertex_before_of_mem_set
      (B.oddLocalRow r c).vertexSet
      (B.oddLocalRow_meets_globalRow r c) hvGlobal hv
  · exact B.threads.global_clusters_ordered r
      (oddMatchingCluster_lt_even c)
      hvGlobal hvCluster
      (B.columnEnd_mem_globalRow r c)
      (B.columnEnd_mem_cluster r c)

theorem mem_columnBlock_of_mem_evenLocalRow
    (B : AlternatingClusterRealizations g P) (r c : Fin g)
    {v : V} (hv : v ∈ (B.evenLocalRow r c).vertexSet) :
    v ∈ B.columnBlock r c := by
  have hvGlobal : v ∈ (B.globalRow r).vertexSet :=
    B.threads.local_path_subset_global (evenMatchingCluster c) r hv
  have hvCluster : v ∈ P.cluster (evenMatchingCluster c) :=
    StrongPathOfSetsSystem.clusterLinkage_staysIn P
      (evenMatchingCluster c) _ hv
  apply (B.globalRow r).mem_segmentOfBefore_of_before_of_before
    (B.columnStart_before_columnEnd r c)
  · exact B.threads.global_clusters_ordered r
      (oddMatchingCluster_lt_even c)
      (B.columnStart_mem_globalRow r c)
      (B.columnStart_mem_cluster r c)
      hvGlobal hvCluster
  · exact (B.globalRow r).before_lastHitVertex_of_mem_set
      (B.evenLocalRow r c).vertexSet
      (B.evenLocalRow_meets_globalRow r c) hvGlobal hv

/-- The bridge from row `r` to row `r+1` in column `c`, selected from the odd
or even prescribed matching according to the parity of `r`. -/
noncomputable def forwardVerticalPath
    (B : AlternatingClusterRealizations g P)
    (c r : Fin g) (hr : r.1 + 1 < g) : GraphPath G :=
  if heven : r.1 % 2 = 0 then
    (B.odd c).path (oddEdgeOfEven r hr heven)
  else
    (B.even c).path
      (evenEdgeOfOdd r hr (by omega))

theorem forwardVerticalPath_source_mem_block
    (B : AlternatingClusterRealizations g P)
    (c r : Fin g) (hr : r.1 + 1 < g) :
    (B.forwardVerticalPath c r hr).source ∈ B.columnBlock r c := by
  by_cases heven : r.1 % 2 = 0
  · rw [forwardVerticalPath]
    simp only [dif_pos heven]
    apply B.mem_columnBlock_of_mem_oddLocalRow
    simpa using (B.odd c).source_mem (oddEdgeOfEven r hr heven)
  · have hodd : r.1 % 2 = 1 := by omega
    rw [forwardVerticalPath]
    simp only [dif_neg heven]
    apply B.mem_columnBlock_of_mem_evenLocalRow
    simpa [hodd] using (B.even c).source_mem (evenEdgeOfOdd r hr hodd)

theorem forwardVerticalPath_target_mem_block
    (B : AlternatingClusterRealizations g P)
    (c r : Fin g) (hr : r.1 + 1 < g) :
    (B.forwardVerticalPath c r hr).target ∈
      B.columnBlock (successorRow r hr) c := by
  by_cases heven : r.1 % 2 = 0
  · rw [forwardVerticalPath]
    simp only [dif_pos heven]
    apply B.mem_columnBlock_of_mem_oddLocalRow
    simpa using (B.odd c).target_mem (oddEdgeOfEven r hr heven)
  · have hodd : r.1 % 2 = 1 := by omega
    rw [forwardVerticalPath]
    simp only [dif_neg heven]
    apply B.mem_columnBlock_of_mem_evenLocalRow
    simpa [hodd] using (B.even c).target_mem (evenEdgeOfOdd r hr hodd)

theorem forwardVerticalPath_internallyDisjoint_globalRow
    (B : AlternatingClusterRealizations g P)
    (c r : Fin g) (hr : r.1 + 1 < g) (s : Fin g) :
    (B.forwardVerticalPath c r hr).InternallyDisjointFromSet
      (B.globalRow s).vertexSet := by
  by_cases heven : r.1 % 2 = 0
  · simpa [forwardVerticalPath, heven, globalRow] using
      B.odd_internallyDisjoint_globalRow c
        (oddEdgeOfEven r hr heven) s
  · have hodd : r.1 % 2 = 1 := by omega
    simpa [forwardVerticalPath, heven, hodd, globalRow] using
      B.even_internallyDisjoint_globalRow c
        (evenEdgeOfOdd r hr hodd) s

theorem oddMatchingCluster_injective :
    Function.Injective (@oddMatchingCluster g) := by
  intro c d h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp at hval
  omega

theorem evenMatchingCluster_injective :
    Function.Injective (@evenMatchingCluster g) := by
  intro c d h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp at hval
  omega

theorem oddMatchingCluster_ne_evenMatchingCluster
    (c d : Fin g) :
    oddMatchingCluster c ≠ evenMatchingCluster d := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval
  omega

theorem oddEdgeOfEven_injective
    {r s : Fin g} {hr : r.1 + 1 < g} {hs : s.1 + 1 < g}
    {hre : r.1 % 2 = 0} {hse : s.1 % 2 = 0}
    (h : oddEdgeOfEven r hr hre = oddEdgeOfEven s hs hse) :
    r = s := by
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [oddEdgeOfEven] at hval
  omega

theorem evenEdgeOfOdd_injective
    {r s : Fin g} {hr : r.1 + 1 < g} {hs : s.1 + 1 < g}
    {hro : r.1 % 2 = 1} {hso : s.1 % 2 = 1}
    (h : evenEdgeOfOdd r hr hro = evenEdgeOfOdd s hs hso) :
    r = s := by
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [evenEdgeOfOdd] at hval
  omega

/-- Distinct canonical `(column, lower-row)` bridge occurrences are
node-disjoint. -/
theorem forwardVerticalPath_nodeDisjoint
    (B : AlternatingClusterRealizations g P)
    {c d r s : Fin g}
    (hr : r.1 + 1 < g) (hs : s.1 + 1 < g)
    (hpairs : (c, r) ≠ (d, s)) :
    (B.forwardVerticalPath c r hr).NodeDisjoint
      (B.forwardVerticalPath d s hs) := by
  by_cases hre : r.1 % 2 = 0
  · by_cases hse : s.1 % 2 = 0
    · simp only [forwardVerticalPath, dif_pos hre, dif_pos hse]
      by_cases hcd : c = d
      · subst d
        apply (B.odd c).node_disjoint
        intro hedge
        apply hpairs
        simp only [Prod.mk.injEq, true_and]
        exact oddEdgeOfEven_injective hedge
      · apply Disjoint.mono
          ((B.odd c).staysIn (oddEdgeOfEven r hr hre))
          ((B.odd d).staysIn (oddEdgeOfEven s hs hse))
        exact P.cluster_disjoint
          (fun h => hcd (oddMatchingCluster_injective h))
    · have hso : s.1 % 2 = 1 := by omega
      simp only [forwardVerticalPath, dif_pos hre, dif_neg hse]
      apply Disjoint.mono
        ((B.odd c).staysIn (oddEdgeOfEven r hr hre))
        ((B.even d).staysIn (evenEdgeOfOdd s hs hso))
      exact P.cluster_disjoint
        (oddMatchingCluster_ne_evenMatchingCluster c d)
  · have hro : r.1 % 2 = 1 := by omega
    by_cases hse : s.1 % 2 = 0
    · simp only [forwardVerticalPath, dif_neg hre, dif_pos hse]
      apply Disjoint.mono
        ((B.even c).staysIn (evenEdgeOfOdd r hr hro))
        ((B.odd d).staysIn (oddEdgeOfEven s hs hse))
      exact P.cluster_disjoint
        (Ne.symm (oddMatchingCluster_ne_evenMatchingCluster d c))
    · have hso : s.1 % 2 = 1 := by omega
      simp only [forwardVerticalPath, dif_neg hre, dif_neg hse]
      by_cases hcd : c = d
      · subst d
        apply (B.even c).node_disjoint
        intro hedge
        apply hpairs
        simp only [Prod.mk.injEq, true_and]
        exact evenEdgeOfOdd_injective hedge
      · apply Disjoint.mono
          ((B.even c).staysIn (evenEdgeOfOdd r hr hro))
          ((B.even d).staysIn (evenEdgeOfOdd s hs hso))
        exact P.cluster_disjoint
          (fun h => hcd (evenMatchingCluster_injective h))

theorem gridConnectorInterior_subset_vertexSet (Q : GraphPath G) :
    gridConnectorInterior Q ⊆ Q.vertexSet := by
  intro v hv
  exact (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2

theorem gridConnectorInterior_disjoint_of_internallyDisjointFromSet
    (Q : GraphPath G) {U : Finset V}
    (hQ : Q.InternallyDisjointFromSet U) :
    Disjoint (gridConnectorInterior Q) U := by
  rw [Finset.disjoint_left]
  intro v hvInterior hvU
  have hvOuter := Finset.mem_erase.mp hvInterior
  have hvInner := Finset.mem_erase.mp hvOuter.2
  rcases hQ hvInner.2 hvU with hsource | htarget
  · exact hvInner.1 hsource
  · exact hvOuter.1 htarget

theorem forwardVerticalPath_pairwise_interior_disjoint
    (B : AlternatingClusterRealizations g P)
    {c d r s : Fin g}
    (hr : r.1 + 1 < g) (hs : s.1 + 1 < g)
    (hpairs : (c, r) ≠ (d, s)) :
    Disjoint
      (gridConnectorInterior (B.forwardVerticalPath c r hr))
      (gridConnectorInterior (B.forwardVerticalPath d s hs)) :=
  Disjoint.mono
    (gridConnectorInterior_subset_vertexSet _)
    (gridConnectorInterior_subset_vertexSet _)
    (B.forwardVerticalPath_nodeDisjoint hr hs hpairs)

/-! ## Orientation-independent vertical connectors -/

/-- The vertical bridge requested in either orientation by the canonical grid
edge API. -/
noncomputable def verticalPath
    (B : AlternatingClusterRealizations g P)
    {x y : GridVertex g}
    (hcol : x.2 = y.2) (hrows : FinConsecutive x.1 y.1) :
    GraphPath G :=
  if hforward : x.1.1 + 1 = y.1.1 then
    B.forwardVerticalPath x.2 x.1 (by omega)
  else
    (B.forwardVerticalPath x.2 y.1
      (by
        have hback := hrows.resolve_left hforward
        omega)).reverse

theorem verticalPath_source_mem_block
    (B : AlternatingClusterRealizations g P)
    {x y : GridVertex g}
    (hcol : x.2 = y.2) (hrows : FinConsecutive x.1 y.1) :
    (B.verticalPath hcol hrows).source ∈
      (B.rowBlocks x.1).block x.2 := by
  by_cases hforward : x.1.1 + 1 = y.1.1
  · have hy : successorRow x.1 (by omega) = y.1 := Fin.ext hforward
    simpa [verticalPath, hforward, rowBlocks] using
      B.forwardVerticalPath_source_mem_block x.2 x.1 (by omega)
  · have hback : y.1.1 + 1 = x.1.1 :=
      hrows.resolve_left hforward
    have hx : successorRow y.1 (by omega) = x.1 := Fin.ext hback
    simpa [verticalPath, hforward, rowBlocks, hx] using
      B.forwardVerticalPath_target_mem_block x.2 y.1 (by omega)

theorem verticalPath_target_mem_block
    (B : AlternatingClusterRealizations g P)
    {x y : GridVertex g}
    (hcol : x.2 = y.2) (hrows : FinConsecutive x.1 y.1) :
    (B.verticalPath hcol hrows).target ∈
      (B.rowBlocks y.1).block y.2 := by
  by_cases hforward : x.1.1 + 1 = y.1.1
  · have hy : successorRow x.1 (by omega) = y.1 := Fin.ext hforward
    simpa [verticalPath, hforward, rowBlocks, hy, ← hcol] using
      B.forwardVerticalPath_target_mem_block x.2 x.1 (by omega)
  · have hback : y.1.1 + 1 = x.1.1 :=
      hrows.resolve_left hforward
    simpa [verticalPath, hforward, rowBlocks, ← hcol] using
      B.forwardVerticalPath_source_mem_block x.2 y.1 (by omega)

theorem verticalPath_interior_disjoint_globalRow
    (B : AlternatingClusterRealizations g P)
    {x y : GridVertex g}
    (hcol : x.2 = y.2) (hrows : FinConsecutive x.1 y.1)
    (r : Fin g) :
    Disjoint (gridConnectorInterior (B.verticalPath hcol hrows))
      (B.globalRow r).vertexSet := by
  by_cases hforward : x.1.1 + 1 = y.1.1
  · rw [verticalPath]
    simp only [dif_pos hforward]
    exact gridConnectorInterior_disjoint_of_internallyDisjointFromSet _
      (B.forwardVerticalPath_internallyDisjoint_globalRow
        x.2 x.1 (by omega) r)
  · have hback : y.1.1 + 1 = x.1.1 :=
      hrows.resolve_left hforward
    rw [verticalPath]
    simp only [dif_neg hforward]
    rw [OrderedPathBlockFamily.gridConnectorInterior_reverse]
    exact gridConnectorInterior_disjoint_of_internallyDisjointFromSet _
      (B.forwardVerticalPath_internallyDisjoint_globalRow
        x.2 y.1 (by omega) r)

theorem verticalPath_pairwise_interior_disjoint
    (B : AlternatingClusterRealizations g P)
    {x y z t : GridVertex g}
    (hxyCol : x.2 = y.2) (hxyRows : FinConsecutive x.1 y.1)
    (hztCol : z.2 = t.2) (hztRows : FinConsecutive z.1 t.1)
    (hordered : (x, y) ≠ (z, t))
    (hreversed : (x, y) ≠ (t, z)) :
    Disjoint
      (gridConnectorInterior (B.verticalPath hxyCol hxyRows))
      (gridConnectorInterior (B.verticalPath hztCol hztRows)) := by
  by_cases hxyForward : x.1.1 + 1 = y.1.1
  · by_cases hztForward : z.1.1 + 1 = t.1.1
    · simp only [verticalPath, dif_pos hxyForward, dif_pos hztForward]
      apply B.forwardVerticalPath_pairwise_interior_disjoint
      intro hkey
      have hcol : x.2 = z.2 := congrArg Prod.fst hkey
      have hrow : x.1 = z.1 := congrArg Prod.snd hkey
      apply hordered
      apply Prod.ext
      · exact Prod.ext hrow hcol
      · apply Prod.ext
        · apply Fin.ext
          have hrowVal := congrArg Fin.val hrow
          calc
            y.1.1 = x.1.1 + 1 := hxyForward.symm
            _ = z.1.1 + 1 := congrArg (fun n => n + 1) hrowVal
            _ = t.1.1 := hztForward
        · exact hxyCol.symm.trans (hcol.trans hztCol)
    · have hztBack : t.1.1 + 1 = z.1.1 :=
        hztRows.resolve_left hztForward
      simp only [verticalPath, dif_pos hxyForward, dif_neg hztForward,
        OrderedPathBlockFamily.gridConnectorInterior_reverse]
      apply B.forwardVerticalPath_pairwise_interior_disjoint
      intro hkey
      have hcol : x.2 = z.2 := congrArg Prod.fst hkey
      have hrow : x.1 = t.1 := congrArg Prod.snd hkey
      apply hreversed
      apply Prod.ext
      · exact Prod.ext hrow (hcol.trans hztCol)
      · apply Prod.ext
        · apply Fin.ext
          have hrowVal := congrArg Fin.val hrow
          calc
            y.1.1 = x.1.1 + 1 := hxyForward.symm
            _ = t.1.1 + 1 := congrArg (fun n => n + 1) hrowVal
            _ = z.1.1 := hztBack
        · exact hxyCol.symm.trans hcol
  · have hxyBack : y.1.1 + 1 = x.1.1 :=
      hxyRows.resolve_left hxyForward
    by_cases hztForward : z.1.1 + 1 = t.1.1
    · simp only [verticalPath, dif_neg hxyForward, dif_pos hztForward,
        OrderedPathBlockFamily.gridConnectorInterior_reverse]
      apply B.forwardVerticalPath_pairwise_interior_disjoint
      intro hkey
      have hcol : x.2 = z.2 := congrArg Prod.fst hkey
      have hrow : y.1 = z.1 := congrArg Prod.snd hkey
      apply hreversed
      apply Prod.ext
      · apply Prod.ext
        · apply Fin.ext
          have hrowVal := congrArg Fin.val hrow
          calc
            x.1.1 = y.1.1 + 1 := hxyBack.symm
            _ = z.1.1 + 1 := congrArg (fun n => n + 1) hrowVal
            _ = t.1.1 := hztForward
        · exact hcol.trans hztCol
      · exact Prod.ext hrow (hxyCol.symm.trans hcol)
    · have hztBack : t.1.1 + 1 = z.1.1 :=
        hztRows.resolve_left hztForward
      simp only [verticalPath, dif_neg hxyForward, dif_neg hztForward,
        OrderedPathBlockFamily.gridConnectorInterior_reverse]
      apply B.forwardVerticalPath_pairwise_interior_disjoint
      intro hkey
      have hcol : x.2 = z.2 := congrArg Prod.fst hkey
      have hrow : y.1 = t.1 := congrArg Prod.snd hkey
      apply hordered
      apply Prod.ext
      · apply Prod.ext
        · apply Fin.ext
          have hrowVal := congrArg Fin.val hrow
          calc
            x.1.1 = y.1.1 + 1 := hxyBack.symm
            _ = t.1.1 + 1 := congrArg (fun n => n + 1) hrowVal
            _ = z.1.1 := hztBack
        · exact hcol
      · exact Prod.ext hrow
          (hxyCol.symm.trans (hcol.trans hztCol))

/-- Package the alternating realizations as the generic ordered-bridge grid
geometry. -/
noncomputable def toOrderedBridgeGridGeometry
    (B : AlternatingClusterRealizations g P) :
    OrderedBridgeGridGeometry G g where
  row := B.globalRow
  row_nodeDisjoint := by
    intro r s hrs
    exact B.threads.threading.packing.toPathPacking.node_disjoint
      (fun h => hrs (B.threads.row.injective h))
  block := B.rowBlocks
  block_connected := B.rowBlock_connected
  verticalPath := by
    intro x y hcol hrows
    exact B.verticalPath hcol hrows
  vertical_source_mem := by
    intro x y hcol hrows
    exact B.verticalPath_source_mem_block hcol hrows
  vertical_target_mem := by
    intro x y hcol hrows
    exact B.verticalPath_target_mem_block hcol hrows
  vertical_interior_disjoint_row := by
    intro x y hcol hrows r
    exact B.verticalPath_interior_disjoint_globalRow hcol hrows r
  vertical_pairwise_interior_disjoint := by
    intro x y z t hxyCol hxyRows hztCol hztRows hordered hreversed
    exact B.verticalPath_pairwise_interior_disjoint
      hxyCol hxyRows hztCol hztRows hordered hreversed

/-- Alternating prescribed matching realizations in `2g` clusters contain a
`g x g` grid minor. -/
theorem containsGridMinor
    (B : AlternatingClusterRealizations g P) :
    ContainsGridMinor G g :=
  B.toOrderedBridgeGridGeometry.containsGridMinor

end AlternatingClusterRealizations

/-- The clean matching dichotomy implies the short-wide grid theorem for a
strong path-of-sets system of length exactly `2g`. -/
theorem shortWideGrid_of_cleanMatchingDichotomy_exact
    {reserve : ℕ}
    (hD : CleanMatchingDichotomyStatement.{u} reserve)
    (P : StrongPathOfSetsSystem G (2 * g) w)
    (hg : 2 ≤ g)
    (hgw : g ≤ w)
    (hwidth : reserve * g ^ 2 ≤ w) :
    ContainsGridMinor G g := by
  rcases grid_or_alternatingClusterRealizations hD P hg hgw hwidth with
    hgrid | hreal
  · exact hgrid
  · exact Classical.choice hreal |>.containsGridMinor

/-- The length-at-least form of the short-wide grid theorem.  We retain the
first `2g` clusters and apply the exact construction above. -/
theorem shortWideGrid_of_cleanMatchingDichotomy
    {ell reserve : ℕ}
    (hD : CleanMatchingDichotomyStatement.{u} reserve)
    (P : StrongPathOfSetsSystem G ell w)
    (hg : 2 ≤ g)
    (hlen : 2 * g ≤ ell)
    (hgw : g ≤ w)
    (hwidth : reserve * g ^ 2 ≤ w) :
    ContainsGridMinor G g := by
  let P' : StrongPathOfSetsSystem G (2 * g) w :=
    P.restrictLength (by omega) hlen
  exact shortWideGrid_of_cleanMatchingDichotomy_exact
    hD P' hg hgw hwidth

end Exponent7
end SimpleGraph

end Lax17Proofs
