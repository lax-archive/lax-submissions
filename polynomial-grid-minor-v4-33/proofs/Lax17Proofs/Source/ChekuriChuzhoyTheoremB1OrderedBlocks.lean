import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1GridAssembly

namespace Lax17Proofs

universe u v w

/-!
# Ordered blocks on a host path

This is the path-order core of the terminal sparse-grid construction in
Chekuri--Chuzhoy Appendix B.1.  Once the row-column intersections occur as
pairwise-disjoint blocks in a common order, consecutive blocks are joined by
the intervening segment of the row or column.  Its internal vertices avoid
every block.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Pairwise-disjoint nonempty blocks occurring in index order on a path. -/
structure OrderedPathBlockFamily (P : GraphPath G) (n : ℕ) where
  block : Fin n → Finset V
  meets : ∀ i, (P.vertexSet ∩ block i).Nonempty
  block_subset : ∀ i, block i ⊆ P.vertexSet
  pairwise_disjoint :
    ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint (block i) (block j)
  ordered :
    ∀ ⦃i j : Fin n⦄, i.1 < j.1 →
      P.Before
        (P.lastHitVertex (block i) (meets i))
        (P.firstHitVertex (block j) (meets j))

namespace OrderedPathBlockFamily

variable {P : GraphPath G} {n : ℕ}

/-- First vertex of a block in the host-path order. -/
noncomputable def first (F : OrderedPathBlockFamily P n) (i : Fin n) : V :=
  P.firstHitVertex (F.block i) (F.meets i)

/-- Last vertex of a block in the host-path order. -/
noncomputable def last (F : OrderedPathBlockFamily P n) (i : Fin n) : V :=
  P.lastHitVertex (F.block i) (F.meets i)

theorem first_mem (F : OrderedPathBlockFamily P n) (i : Fin n) :
    F.first i ∈ F.block i :=
  P.firstHitVertex_mem_set (F.block i) (F.meets i)

theorem last_mem (F : OrderedPathBlockFamily P n) (i : Fin n) :
    F.last i ∈ F.block i :=
  P.lastHitVertex_mem_set (F.block i) (F.meets i)

theorem first_mem_path (F : OrderedPathBlockFamily P n) (i : Fin n) :
    F.first i ∈ P.vertexSet :=
  P.firstHitVertex_mem_vertexSet (F.block i) (F.meets i)

theorem last_mem_path (F : OrderedPathBlockFamily P n) (i : Fin n) :
    F.last i ∈ P.vertexSet :=
  P.lastHitVertex_mem_vertexSet (F.block i) (F.meets i)

theorem before_last_of_mem
    (F : OrderedPathBlockFamily P n) (i : Fin n)
    {v : V} (hv : v ∈ F.block i) :
    P.Before v (F.last i) :=
  P.before_lastHitVertex_of_mem_set
    (F.block i) (F.meets i) (F.block_subset i hv) hv

theorem first_before_of_mem
    (F : OrderedPathBlockFamily P n) (i : Fin n)
    {v : V} (hv : v ∈ F.block i) :
    P.Before (F.first i) v :=
  P.firstHitVertex_before_of_mem_set
    (F.block i) (F.meets i) (F.block_subset i hv) hv

theorem last_before_first
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hij : i.1 < j.1) :
    P.Before (F.last i) (F.first j) :=
  F.ordered hij

/-- The intervening host-path segment from the last point of block `i` to the
first point of the next block `j`. -/
noncomputable def connectorForward
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) : GraphPath G :=
  P.segmentOfBefore
    (F.last_before_first (i := i) (j := j) (by omega))

@[simp] theorem connectorForward_source
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) :
    (F.connectorForward hsucc).source = F.last i := by
  simp [connectorForward]

@[simp] theorem connectorForward_target
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) :
    (F.connectorForward hsucc).target = F.first j := by
  simp [connectorForward]

theorem connectorForward_source_mem
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) :
    (F.connectorForward hsucc).source ∈ F.block i := by
  simpa using F.last_mem i

theorem connectorForward_target_mem
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) :
    (F.connectorForward hsucc).target ∈ F.block j := by
  simpa using F.first_mem j

theorem connectorForward_vertexSet_subset
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) :
    (F.connectorForward hsucc).vertexSet ⊆ P.vertexSet :=
  P.segmentOfBefore_vertexSet_subset _

theorem connectorForward_source_ne_target
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) :
    (F.connectorForward hsucc).source ≠
      (F.connectorForward hsucc).target := by
  intro heq
  have hij : i ≠ j := by
    intro hij
    have hval := congrArg Fin.val hij
    omega
  have hlast_first : F.last i = F.first j := by
    simpa using heq
  exact (Finset.disjoint_left.mp (F.pairwise_disjoint hij))
    (F.last_mem i) (hlast_first.symm ▸ F.first_mem j)

theorem connectorForward_interior_subset_dropLast
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) :
    gridConnectorInterior (F.connectorForward hsucc) ⊆
      (F.connectorForward hsucc).dropLast.vertexSet := by
  intro v hv
  have hvouter := Finset.mem_erase.mp hv
  have hvinner := Finset.mem_erase.mp hvouter.2
  exact
    ((F.connectorForward hsucc).mem_vertexSet_iff_mem_dropLast_or_eq_target
      (F.connectorForward_source_ne_target hsucc) v).mp hvinner.2
      |>.resolve_right hvouter.1

/-- The interior of a connector between consecutive ordered blocks meets no
block in the family. -/
theorem connectorForward_interior_disjoint_block
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hsucc : i.1 + 1 = j.1) (k : Fin n) :
    Disjoint (gridConnectorInterior (F.connectorForward hsucc)) (F.block k) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvint hvblock
  have hvouter := Finset.mem_erase.mp hvint
  have hvinner := Finset.mem_erase.mp hvouter.2
  have hvsegment : v ∈ (F.connectorForward hsucc).vertexSet := by
    exact hvinner.2
  have hvne_source : v ≠ (F.connectorForward hsucc).source := by
    exact hvinner.1
  have hvne_target : v ≠ (F.connectorForward hsucc).target := by
    exact hvouter.1
  have hsource_before_v :
      P.Before (F.last i) v :=
    P.before_of_mem_segmentOfBefore_left
      (F.last_before_first (i := i) (j := j) (by omega))
      (by simpa [connectorForward] using hvsegment)
  have hv_before_target :
      P.Before v (F.first j) :=
    P.before_of_mem_segmentOfBefore_right
      (F.last_before_first (i := i) (j := j) (by omega))
      (by simpa [connectorForward] using hvsegment)
  by_cases hki : k.1 ≤ i.1
  · have hv_before_source : P.Before v (F.last i) := by
      rcases Nat.lt_or_eq_of_le hki with hlt | heq
      · exact P.before_trans
          (P.before_trans (F.before_last_of_mem k hvblock)
            (F.last_before_first hlt))
          (F.first_before_of_mem i (F.last_mem i))
      · have hkeq : k = i := Fin.ext heq
        subst k
        exact F.before_last_of_mem i hvblock
    have hveq : v = F.last i :=
      P.before_antisymm hv_before_source hsource_before_v
    exact hvne_source (by simpa using hveq)
  · have hjk : j.1 ≤ k.1 := by omega
    have htarget_before_v : P.Before (F.first j) v := by
      rcases Nat.lt_or_eq_of_le hjk with hlt | heq
      · exact P.before_trans
          (F.first_before_of_mem j (F.last_mem j))
          (P.before_trans (F.last_before_first hlt)
            (F.first_before_of_mem k hvblock))
      · have hjeq : j = k := Fin.ext heq
        subst k
        exact F.first_before_of_mem j hvblock
    have hveq : v = F.first j :=
      P.before_antisymm hv_before_target htarget_before_v
    exact hvne_target (by simpa using hveq)

/-- Distinct intervening segments between consecutive blocks have disjoint
interiors. -/
theorem connectorForward_pairwise_interior_disjoint
    (F : OrderedPathBlockFamily P n)
    {i j k l : Fin n}
    (hij : i.1 + 1 = j.1) (hkl : k.1 + 1 = l.1)
    (hpairs : (i, j) ≠ (k, l)) :
    Disjoint
      (gridConnectorInterior (F.connectorForward hij))
      (gridConnectorInterior (F.connectorForward hkl)) := by
  classical
  have forward_case :
      ∀ {i j k l : Fin n}
        (hij : i.1 + 1 = j.1) (hkl : k.1 + 1 = l.1),
        i.1 < k.1 →
        Disjoint
          (gridConnectorInterior (F.connectorForward hij))
          (gridConnectorInterior (F.connectorForward hkl)) := by
    intro i j k l hij hkl hiklt
    have hjk : j.1 ≤ k.1 := by omega
    have htarget_source :
        P.Before (F.first j) (F.last k) := by
      rcases Nat.lt_or_eq_of_le hjk with hjklt | hjkeq
      · exact P.before_trans
          (F.first_before_of_mem j (F.last_mem j))
          (P.before_trans (F.last_before_first hjklt)
            (F.first_before_of_mem k (F.last_mem k)))
      · have hjkeq' : j = k := Fin.ext hjkeq
        subst k
        exact F.first_before_of_mem j (F.last_mem j)
    apply Disjoint.mono
      (F.connectorForward_interior_subset_dropLast hij)
      (F.connectorForward_interior_subset_dropLast hkl)
    exact P.segmentOfBefore_dropLast_disjoint_of_target_before_source
      (F.last_before_first (i := i) (j := j) (by omega))
      (F.last_before_first (i := k) (j := l) (by omega))
      htarget_source
      (by simpa [connectorForward] using
        F.connectorForward_source_ne_target hij)
  have hik : i ≠ k := by
    intro hik
    subst k
    have hjl : j = l := Fin.ext (by omega)
    exact hpairs (by simp [hjl])
  have hikval : i.1 ≠ k.1 := by
    intro hval
    exact hik (Fin.ext hval)
  rcases lt_or_gt_of_ne hikval with hiklt | hkilt
  · exact forward_case hij hkl hiklt
  · exact Disjoint.symm (forward_case hkl hij hkilt)

/-- The connector oriented from `i` to `j`, for either orientation of a
consecutive pair. -/
noncomputable def connector
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hij : FinConsecutive i j) : GraphPath G :=
  if hforward : i.1 + 1 = j.1 then
    F.connectorForward hforward
  else
    (F.connectorForward (i := j) (j := i)
      (hij.resolve_left hforward)).reverse

theorem gridConnectorInterior_reverse (Q : GraphPath G) :
    gridConnectorInterior Q.reverse = gridConnectorInterior Q := by
  classical
  ext v
  simp [gridConnectorInterior, and_comm, and_left_comm, and_assoc]

theorem connector_source_mem
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hij : FinConsecutive i j) :
    (F.connector hij).source ∈ F.block i := by
  classical
  by_cases hforward : i.1 + 1 = j.1
  · simpa [connector, hforward] using
      F.connectorForward_source_mem hforward
  · have hback : j.1 + 1 = i.1 := hij.resolve_left hforward
    simpa [connector, hforward] using
      F.connectorForward_target_mem hback

theorem connector_target_mem
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hij : FinConsecutive i j) :
    (F.connector hij).target ∈ F.block j := by
  classical
  by_cases hforward : i.1 + 1 = j.1
  · simpa [connector, hforward] using
      F.connectorForward_target_mem hforward
  · have hback : j.1 + 1 = i.1 := hij.resolve_left hforward
    simpa [connector, hforward] using
      F.connectorForward_source_mem hback

theorem connector_vertexSet_subset
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hij : FinConsecutive i j) :
    (F.connector hij).vertexSet ⊆ P.vertexSet := by
  classical
  by_cases hforward : i.1 + 1 = j.1
  · simpa [connector, hforward] using
      F.connectorForward_vertexSet_subset hforward
  · have hback : j.1 + 1 = i.1 := hij.resolve_left hforward
    simpa [connector, hforward] using
      F.connectorForward_vertexSet_subset hback

theorem connector_interior_subset_path
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hij : FinConsecutive i j) :
    gridConnectorInterior (F.connector hij) ⊆ P.vertexSet := by
  intro v hv
  apply F.connector_vertexSet_subset hij
  exact (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2

theorem connector_interior_disjoint_block
    (F : OrderedPathBlockFamily P n) {i j : Fin n}
    (hij : FinConsecutive i j) (k : Fin n) :
    Disjoint (gridConnectorInterior (F.connector hij)) (F.block k) := by
  classical
  by_cases hforward : i.1 + 1 = j.1
  · simpa [connector, hforward] using
      F.connectorForward_interior_disjoint_block hforward k
  · have hback : j.1 + 1 = i.1 := hij.resolve_left hforward
    rw [show F.connector hij =
        (F.connectorForward (i := j) (j := i) hback).reverse by
      simp [connector, hforward]]
    rw [gridConnectorInterior_reverse]
    exact F.connectorForward_interior_disjoint_block hback k

/-- Two distinct undirected consecutive block pairs have internally disjoint
connectors, regardless of the requested connector orientations. -/
theorem connector_pairwise_interior_disjoint
    (F : OrderedPathBlockFamily P n)
    {i j k l : Fin n}
    (hij : FinConsecutive i j) (hkl : FinConsecutive k l)
    (hordered_ne : (i, j) ≠ (k, l))
    (hreversed_ne : (i, j) ≠ (l, k)) :
    Disjoint
      (gridConnectorInterior (F.connector hij))
      (gridConnectorInterior (F.connector hkl)) := by
  classical
  by_cases hij_forward : i.1 + 1 = j.1
  · by_cases hkl_forward : k.1 + 1 = l.1
    · simpa [connector, hij_forward, hkl_forward] using
        F.connectorForward_pairwise_interior_disjoint
          hij_forward hkl_forward hordered_ne
    · have hkl_back : l.1 + 1 = k.1 :=
        hkl.resolve_left hkl_forward
      rw [show F.connector hij = F.connectorForward hij_forward by
        simp [connector, hij_forward]]
      rw [show F.connector hkl =
          (F.connectorForward (i := l) (j := k) hkl_back).reverse by
        simp [connector, hkl_forward]]
      rw [gridConnectorInterior_reverse]
      exact F.connectorForward_pairwise_interior_disjoint
        hij_forward hkl_back hreversed_ne
  · have hij_back : j.1 + 1 = i.1 :=
      hij.resolve_left hij_forward
    by_cases hkl_forward : k.1 + 1 = l.1
    · rw [show F.connector hij =
          (F.connectorForward (i := j) (j := i) hij_back).reverse by
        simp [connector, hij_forward]]
      rw [gridConnectorInterior_reverse]
      rw [show F.connector hkl = F.connectorForward hkl_forward by
        simp [connector, hkl_forward]]
      exact F.connectorForward_pairwise_interior_disjoint
        hij_back hkl_forward (by
          intro hp
          apply hreversed_ne
          exact Prod.ext
            (congrArg Prod.snd hp) (congrArg Prod.fst hp))
    · have hkl_back : l.1 + 1 = k.1 :=
        hkl.resolve_left hkl_forward
      rw [show F.connector hij =
          (F.connectorForward (i := j) (j := i) hij_back).reverse by
        simp [connector, hij_forward]]
      rw [show F.connector hkl =
          (F.connectorForward (i := l) (j := k) hkl_back).reverse by
        simp [connector, hkl_forward]]
      rw [gridConnectorInterior_reverse, gridConnectorInterior_reverse]
      exact F.connectorForward_pairwise_interior_disjoint
        hij_back hkl_back (by
          intro hp
          apply hordered_ne
          exact Prod.ext
            (congrArg Prod.snd hp) (congrArg Prod.fst hp))

end OrderedPathBlockFamily

/-- The pairwise-connector theorem transported across equality of the index
selecting the host path.  Keeping this transport generic avoids dependent
rewriting problems for row and column families. -/
theorem indexedConnector_pairwise_interior_disjoint
    {κ : Type*} {host : κ → GraphPath G} {n : ℕ}
    (F : ∀ a : κ, OrderedPathBlockFamily (host a) n)
    {a b : κ} (hab : a = b)
    {i j k l : Fin n}
    (hij : FinConsecutive i j) (hkl : FinConsecutive k l)
    (hordered_ne : (i, j) ≠ (k, l))
    (hreversed_ne : (i, j) ≠ (l, k)) :
    Disjoint
      (gridConnectorInterior ((F a).connector hij))
      (gridConnectorInterior ((F b).connector hkl)) := by
  subst b
  exact (F a).connector_pairwise_interior_disjoint
    hij hkl hordered_ne hreversed_ne

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
