import Lax17Proofs.Source.ChekuriChuzhoyRootedTreeDistance

namespace Lax17Proofs

universe u v w

/-!
# Rooted tree components for Observation 2.12

This module proves the component facts used by the rooted spanning-tree
pruning in Chekuri--Chuzhoy, journal Observation 2.12.  The strict decrease
of root distance along a parent edge is an explicit hypothesis so that its
proof can remain in the preceding parent-map layer.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyRootedTreeComponents


open ChekuriChuzhoyRootedTreePruning

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {H : _root_.SimpleGraph V}

/-- The root-distance equation required from the parent-map layer. -/
def ParentDistanceDecreases (hH : H.IsTree) (root : V) : Prop :=
  ∀ {x : V}, x ≠ root →
    H.dist root (parent hH root x) + 1 = H.dist root x

/-- A non-root vertex is a child of `v` when its parent is `v`. -/
def IsChild (hH : H.IsTree) (root v c : V) : Prop :=
  c ≠ root ∧ parent hH root c = v

/-- The finite set of children of a rooted-tree vertex. -/
noncomputable def children (hH : H.IsTree) (root v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun c => IsChild hH root v c

@[simp] theorem mem_children (hH : H.IsTree) (root v c : V) :
    c ∈ children hH root v ↔ IsChild hH root v c := by
  classical
  simp [children]

/-- A child subtree is the descendant finset rooted at that child. -/
noncomputable def childSubtree (hH : H.IsTree) (root c : V) : Finset V :=
  descendants hH root c

@[simp] theorem mem_childSubtree (hH : H.IsTree) (root c x : V) :
    x ∈ childSubtree hH root c ↔
      ∃ n ≤ Fintype.card V, (parent hH root)^[n] x = c := by
  simp [childSubtree]

private theorem iterate_root (hH : H.IsTree) (root : V) (n : ℕ) :
    (parent hH root)^[n] root = root := by
  exact Function.iterate_fixed (parent_root hH root) n

/-- If a parent iterate ends away from the root, its starting point is also
away from the root. -/
theorem ne_root_of_iterate_eq (hH : H.IsTree) (root : V) {x a : V} {n : ℕ}
    (ha : a ≠ root) (hxa : (parent hH root)^[n] x = a) :
    x ≠ root := by
  intro hx
  subst x
  exact ha (((iterate_root hH root n).symm.trans hxa).symm)

/-- Root distance records the length of every parent chain that ends at a
non-root ancestor. -/
theorem dist_add_iterate_eq
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {x a : V} {n : ℕ} (ha : a ≠ root)
    (hxa : (parent hH root)^[n] x = a) :
    H.dist root a + n = H.dist root x := by
  induction n generalizing x with
  | zero =>
      simpa using congrArg (H.dist root) hxa.symm
  | succ n ih =>
      have hx : x ≠ root := ne_root_of_iterate_eq hH root ha hxa
      have htail : (parent hH root)^[n] (parent hH root x) = a := by
        simpa only [Function.iterate_succ_apply] using hxa
      have hih := ih htail
      have hstep := hdec hx
      omega

/-- Two parent chains from one vertex to non-root vertices at the same depth
have the same endpoint. -/
theorem iterate_eq_of_dist_eq
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {x a b : V} {m n : ℕ} (ha : a ≠ root) (hb : b ≠ root)
    (hxa : (parent hH root)^[m] x = a)
    (hxb : (parent hH root)^[n] x = b)
    (habdist : H.dist root a = H.dist root b) : a = b := by
  have ham := dist_add_iterate_eq hH root hdec ha hxa
  have hbn := dist_add_iterate_eq hH root hdec hb hxb
  have hmn : m = n := by omega
  subst n
  exact hxa.symm.trans hxb

/-- Moving one step toward a non-root descendant root stays in the same
descendant set. -/
theorem parent_mem_descendants
    (hH : H.IsTree) (root : V) {a x : V}
    (hx : x ∈ descendants hH root a) (hxa : x ≠ a) :
    parent hH root x ∈ descendants hH root a := by
  rw [mem_descendants] at hx ⊢
  rcases hx with ⟨n, hn, hiter⟩
  cases n with
  | zero => simp at hiter; exact (hxa hiter).elim
  | succ n =>
      refine ⟨n, Nat.le_trans (Nat.le_succ n) hn, ?_⟩
      simpa only [Function.iterate_succ_apply] using hiter

/-- The parent chain witnessing descendant membership lifts to the induced
descendant graph. -/
theorem reachable_in_descendants_of_iterate
    (hH : H.IsTree) (root a : V) {x : V} {n : ℕ}
    (hn : n ≤ Fintype.card V) (hiter : (parent hH root)^[n] x = a) :
    (H.induce {z : V | z ∈ descendants hH root a}).Reachable
      ⟨x, (mem_descendants hH root a x).2 ⟨n, hn, hiter⟩⟩
      ⟨a, self_mem_descendants hH root a⟩ := by
  induction n generalizing x with
  | zero =>
      have hxa : x = a := by simpa using hiter
      subst x
      exact .rfl
  | succ n ih =>
      by_cases hxa : x = a
      · subst x
        exact .rfl
      · have hxroot : x ≠ root := by
          intro hxr
          subst x
          have hroota : root = a := by
            simpa [iterate_root] using hiter
          exact hxa hroota
        have htail : (parent hH root)^[n] (parent hH root x) = a := by
          simpa only [Function.iterate_succ_apply] using hiter
        have hn' : n ≤ Fintype.card V := Nat.le_trans (Nat.le_succ n) hn
        have hpMem : parent hH root x ∈ descendants hH root a :=
          (mem_descendants hH root a _).2 ⟨n, hn', htail⟩
        have hreach := ih hn' htail
        exact (_root_.SimpleGraph.Adj.reachable (show
          (H.induce {z : V | z ∈ descendants hH root a}).Adj
            ⟨x, (mem_descendants hH root a x).2 ⟨n.succ, hn, hiter⟩⟩
            ⟨parent hH root x, hpMem⟩ from
          (parent_adj hH root hxroot).symm)).trans hreach

/-- Every descendant finset induces a connected subtree. -/
theorem descendants_connected (hH : H.IsTree) (root a : V) :
    (H.induce {x : V | x ∈ descendants hH root a}).Connected := by
  have ha : a ∈ descendants hH root a := self_mem_descendants hH root a
  refine H.induce_connected_of_patches a ha ?_
  intro x hx
  change x ∈ descendants hH root a at hx
  rw [mem_descendants] at hx
  rcases hx with ⟨n, hn, hiter⟩
  exact ⟨{z : V | z ∈ descendants hH root a}, Set.Subset.rfl,
    ha, (mem_descendants hH root a x).2 ⟨n, hn, hiter⟩,
    (reachable_in_descendants_of_iterate hH root a hn hiter).symm⟩

/-- Child subtrees are connected. -/
theorem childSubtree_connected (hH : H.IsTree) (root c : V) :
    (H.induce {x : V | x ∈ childSubtree hH root c}).Connected := by
  simpa [childSubtree] using descendants_connected hH root c

/-- A child and its parent differ by exactly one level. -/
theorem IsChild.dist_eq_add_one
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {v c : V} (hc : IsChild hH root v c) :
    H.dist root v + 1 = H.dist root c := by
  simpa [hc.2] using hdec hc.1

/-- Every proper descendant lies in the subtree of a unique immediate child.
The root case uses the first time the parent chain reaches the root; away from
the root, any descendant witness already has the exact length forced by root
distance. -/
theorem exists_child_of_mem_descendants_of_ne
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {v x : V} (hx : x ∈ descendants hH root v) (hxv : x ≠ v) :
    ∃ c ∈ children hH root v, x ∈ childSubtree hH root c := by
  by_cases hvroot : v = root
  · subst v
    have hxroot : x ≠ root := hxv
    have hnpos : 0 < H.dist root x := hH.connected.pos_dist_of_ne hxroot.symm
    obtain ⟨k, hkdist⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    have hnroot := iterate_parent_eq_root hH root x
    rw [hkdist] at hnroot
    let c := (parent hH root)^[k] x
    have hcparent : parent hH root c = root := by
      simpa only [c, Function.iterate_succ_apply'] using hnroot
    have hklt : k < H.dist root x := by
      omega
    have hcroot : c ≠ root := by
      simpa [c] using (iterate_parent_ne_root_iff hH root x k).2 hklt
    refine ⟨c, (mem_children hH root root c).2 ⟨hcroot, hcparent⟩, ?_⟩
    rw [mem_childSubtree]
    refine ⟨k, ?_, rfl⟩
    have hdistLt := dist_lt_card hH root x
    omega
  · rw [mem_descendants] at hx
    rcases hx with ⟨n, hncard, hn⟩
    have hnzero : n ≠ 0 := by
      intro hn0
      subst n
      simp only [Function.iterate_zero, id_eq] at hn
      exact hxv hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnzero
    let c := (parent hH root)^[k] x
    have hcparent : parent hH root c = v := by
      simpa only [c, Function.iterate_succ_apply'] using hn
    have hcroot : c ≠ root := by
      intro hc
      have : v = root := by simpa [hc, parent_root] using hcparent.symm
      exact hvroot this
    refine ⟨c, (mem_children hH root v c).2 ⟨hcroot, hcparent⟩, ?_⟩
    rw [mem_childSubtree]
    exact ⟨k, Nat.le_trans (Nat.le_succ k) hncard, rfl⟩

/-- Descendants of a vertex decompose into the vertex itself and the disjoint
subtrees rooted at its immediate children. -/
theorem mem_descendants_iff_eq_or_childSubtree
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {v x : V} :
    x ∈ descendants hH root v ↔
      x = v ∨ ∃ c ∈ children hH root v, x ∈ childSubtree hH root c := by
  constructor
  · intro hx
    by_cases hxv : x = v
    · exact Or.inl hxv
    · exact Or.inr (exists_child_of_mem_descendants_of_ne hH root hdec hx hxv)
  · rintro (rfl | ⟨c, hcchild, hxc⟩)
    · exact self_mem_descendants hH root _
    · rw [mem_children] at hcchild
      rw [mem_childSubtree] at hxc
      rcases hxc with ⟨n, hncard, hn⟩
      rw [mem_descendants]
      refine ⟨n + 1, ?_, ?_⟩
      · have hchain := dist_add_iterate_eq hH root hdec hcchild.1 hn
        have hcstep := hcchild.dist_eq_add_one hH root hdec
        have hdistLt := dist_lt_card hH root x
        omega
      · simpa only [Function.iterate_succ_apply', hn, hcchild.2]

/-- Finset form of the immediate-child decomposition. -/
theorem descendants_eq_insert_biUnion_children
    (hH : H.IsTree) (root v : V) (hdec : ParentDistanceDecreases hH root) :
    descendants hH root v =
      insert v ((children hH root v).biUnion (childSubtree hH root)) := by
  ext x
  rw [mem_descendants_iff_eq_or_childSubtree hH root hdec]
  simp

/-- Distinct children have disjoint descendant subtrees. -/
theorem childSubtree_disjoint
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {v c d : V} (hc : IsChild hH root v c) (hd : IsChild hH root v d)
    (hcd : c ≠ d) :
    Disjoint (childSubtree hH root c) (childSubtree hH root d) := by
  apply Finset.disjoint_left.mpr
  intro x hxc hxd
  rw [mem_childSubtree] at hxc hxd
  rcases hxc with ⟨m, _hm, hxm⟩
  rcases hxd with ⟨n, _hn, hxn⟩
  exact hcd (iterate_eq_of_dist_eq hH root hdec hc.1 hd.1 hxm hxn (by
    rw [← hc.dist_eq_add_one hH root hdec, ← hd.dist_eq_add_one hH root hdec]))

/-- An adjacent pair in a rooted tree is oriented by the parent map. -/
theorem parent_eq_of_adj_of_dist_eq_add_one
    (hH : H.IsTree) (root : V) {x y : V} (hxy : H.Adj x y)
    (hdist : H.dist root y + 1 = H.dist root x) :
    parent hH root x = y := by
  have hxroot : x ≠ root := by
    intro hx
    subst x
    simp at hdist
  let p := (rootPath hH root y).concat hxy.symm
  have hpLength : p.length = H.dist root x := by
    simp [p, rootPath_length, hdist]
  have hpPath : p.IsPath := p.isPath_of_length_eq_dist hpLength
  have heq : rootPath hH root x = p := by
    exact Subtype.ext_iff.mp <| hH.isAcyclic.path_unique
      ⟨rootPath hH root x, rootPath_isPath hH root x⟩ ⟨p, hpPath⟩
  rw [parent_eq_penultimate hH root hxroot, heq]
  simp [p]

/-- Every tree edge joins a vertex to its parent in one orientation. -/
theorem adj_parent_or_parent
    (hH : H.IsTree) (root : V) {x y : V} (hxy : H.Adj x y) :
    parent hH root x = y ∨ parent hH root y = x := by
  rcases hH.dist_eq_dist_add_one_of_adj root hxy with h | h
  · exact Or.inl (parent_eq_of_adj_of_dist_eq_add_one hH root hxy h.symm)
  · exact Or.inr (parent_eq_of_adj_of_dist_eq_add_one hH root hxy.symm h.symm)

/-- A parent of a descendant is either the child-subtree root's parent or
remains in the same child subtree. -/
theorem parent_eq_or_mem_childSubtree
    (hH : H.IsTree) (root : V) {v c x : V}
    (hc : IsChild hH root v c) (hx : x ∈ childSubtree hH root c) :
    parent hH root x = v ∨ parent hH root x ∈ childSubtree hH root c := by
  by_cases hxc : x = c
  · left
    simpa [hxc] using hc.2
  · right
    exact parent_mem_descendants hH root hx hxc

/-- Distinct child subtrees have no tree edge between them. -/
theorem childSubtree_not_adj
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {v c d x y : V} (hc : IsChild hH root v c) (hd : IsChild hH root v d)
    (hcd : c ≠ d) (hxc : x ∈ childSubtree hH root c)
    (hyd : y ∈ childSubtree hH root d) :
    ¬ H.Adj x y := by
  intro hxy
  rcases adj_parent_or_parent hH root hxy with hpx | hpy
  · rcases parent_eq_or_mem_childSubtree hH root hc hxc with hpv | hpc
    · have hyv : y = v := hpx.symm.trans hpv
      have hvd : v ∈ childSubtree hH root d := by simpa [hyv] using hyd
      rw [mem_childSubtree] at hvd
      rcases hvd with ⟨n, _hn, hvn⟩
      have hdist := dist_add_iterate_eq hH root hdec hd.1 hvn
      have hdstep := hd.dist_eq_add_one hH root hdec
      omega
    · exact Finset.disjoint_left.mp
        (childSubtree_disjoint hH root hdec hc hd hcd) hpc (by simpa [hpx] using hyd)
  · rcases parent_eq_or_mem_childSubtree hH root hd hyd with hpv | hpd
    · have hxv : x = v := hpy.symm.trans hpv
      have hvc : v ∈ childSubtree hH root c := by simpa [hxv] using hxc
      rw [mem_childSubtree] at hvc
      rcases hvc with ⟨n, _hn, hvn⟩
      have hdist := dist_add_iterate_eq hH root hdec hc.1 hvn
      have hcstep := hc.dist_eq_add_one hH root hdec
      omega
    · exact Finset.disjoint_left.mp
        (childSubtree_disjoint hH root hdec hc hd hcd) (by simpa [hpy] using hxc) hpd

/-- The child subtrees selected at one pivot are pairwise vertex-disjoint. -/
theorem selected_childSubtrees_pairwiseDisjoint
    (hH : H.IsTree) (root v : V) (hdec : ParentDistanceDecreases hH root)
    {selected : Finset V}
    (hselected : ∀ c ∈ selected, IsChild hH root v c) :
    (↑selected : Set V).PairwiseDisjoint (childSubtree hH root) := by
  intro c hc d hd hcd
  exact childSubtree_disjoint hH root hdec
    (hselected c hc) (hselected d hd) hcd

/-- Distinct selected child subtrees have no tree edge between them. -/
theorem selected_childSubtrees_pairwise_not_adj
    (hH : H.IsTree) (root v : V) (hdec : ParentDistanceDecreases hH root)
    {selected : Finset V}
    (hselected : ∀ c ∈ selected, IsChild hH root v c)
    {c d x y : V} (hc : c ∈ selected) (hd : d ∈ selected) (hcd : c ≠ d)
    (hxc : x ∈ childSubtree hH root c)
    (hyd : y ∈ childSubtree hH root d) :
    ¬ H.Adj x y :=
  childSubtree_not_adj hH root hdec
    (hselected c hc) (hselected d hd) hcd hxc hyd

/-! ## Selected child branches and the residual -/

/-- The union of a selected set of child subtrees. -/
noncomputable def selectedDescendants
    (hH : H.IsTree) (root : V) (selected : Finset V) : Finset V :=
  selected.biUnion (childSubtree hH root)

/-- The support emitted by one pruning iteration: the pivot together with
the selected child subtrees. -/
noncomputable def pruningSupport
    (hH : H.IsTree) (root v : V) (selected : Finset V) : Finset V :=
  insert v (selectedDescendants hH root selected)

/-- The remaining rooted tree after deleting the selected child subtrees.
The pivot itself remains. -/
noncomputable def residual
    (hH : H.IsTree) (root : V) (selected : Finset V) : Finset V :=
  Finset.univ \ selectedDescendants hH root selected

@[simp] theorem mem_selectedDescendants
    (hH : H.IsTree) (root : V) (selected : Finset V) (x : V) :
    x ∈ selectedDescendants hH root selected ↔
      ∃ c ∈ selected, x ∈ childSubtree hH root c := by
  classical
  simp [selectedDescendants]

@[simp] theorem mem_pruningSupport
    (hH : H.IsTree) (root v : V) (selected : Finset V) (x : V) :
    x ∈ pruningSupport hH root v selected ↔
      x = v ∨ ∃ c ∈ selected, x ∈ childSubtree hH root c := by
  classical
  simp [pruningSupport]

@[simp] theorem mem_residual
    (hH : H.IsTree) (root : V) (selected : Finset V) (x : V) :
    x ∈ residual hH root selected ↔
      x ∉ selectedDescendants hH root selected := by
  classical
  simp [residual]

/-- A parent-closed finite vertex set contains the parent of each of its
non-root vertices. -/
def ParentClosed (hH : H.IsTree) (root : V) (R : Finset V) : Prop :=
  root ∈ R ∧ ∀ {x : V}, x ∈ R → x ≠ root → parent hH root x ∈ R

/-- A parent-closed set containing the root induces a connected subtree. -/
theorem ParentClosed.connected
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {R : Finset V} (hR : ParentClosed hH root R) :
    (H.induce {x : V | x ∈ R}).Connected := by
  let rec go (x : V) (hxR : x ∈ R) :
      (H.induce {z : V | z ∈ R}).Reachable
        ⟨x, hxR⟩ ⟨root, hR.1⟩ := by
    by_cases hxroot : x = root
    · subst x
      exact .rfl
    · have hpR : parent hH root x ∈ R := hR.2 hxR hxroot
      have hstep := hdec hxroot
      have hlt : H.dist root (parent hH root x) < H.dist root x := by omega
      have hreach := go (parent hH root x) hpR
      exact (_root_.SimpleGraph.Adj.reachable (show
        (H.induce {z : V | z ∈ R}).Adj ⟨x, hxR⟩
          ⟨parent hH root x, hpR⟩ from
        (parent_adj hH root hxroot).symm)).trans hreach
  termination_by H.dist root x
  decreasing_by exact hlt
  refine H.induce_connected_of_patches root hR.1 ?_
  intro x hxR
  exact ⟨{z : V | z ∈ R}, Set.Subset.rfl, hR.1, hxR, (go x hxR).symm⟩

/-- If the parent of `x` is a descendant of a non-root vertex, then so is
`x`.  The root-distance hypothesis supplies the bound required by the finite
definition of `descendants`. -/
theorem mem_descendants_of_parent_mem
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {a x : V} (ha : a ≠ root) (hxroot : x ≠ root)
    (hp : parent hH root x ∈ descendants hH root a) :
    x ∈ descendants hH root a := by
  rw [mem_descendants] at hp ⊢
  rcases hp with ⟨n, _hn, hiter⟩
  refine ⟨n + 1, ?_, ?_⟩
  · have hchain := dist_add_iterate_eq hH root hdec ha hiter
    have hstep := hdec hxroot
    have hdistLt : H.dist root x < Fintype.card V := by
      rw [← rootPath_length hH root x]
      exact (rootPath_isPath hH root x).length_lt
    omega
  · simpa only [Nat.add_comm, Function.iterate_succ_apply] using hiter

/-- The root cannot lie below a non-root child. -/
theorem root_not_mem_childSubtree
    (hH : H.IsTree) (root : V) {c : V} (hcroot : c ≠ root) :
    root ∉ childSubtree hH root c := by
  rw [mem_childSubtree]
  rintro ⟨n, _hn, hiter⟩
  exact hcroot ((iterate_root hH root n).symm.trans hiter).symm

/-- A parent is not a descendant of one of its children. -/
theorem parent_not_mem_childSubtree
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {v c : V} (hc : IsChild hH root v c) :
    v ∉ childSubtree hH root c := by
  rw [mem_childSubtree]
  rintro ⟨n, _hn, hiter⟩
  have hchain := dist_add_iterate_eq hH root hdec hc.1 hiter
  have hstep := hc.dist_eq_add_one hH root hdec
  omega

/-- Deleting any collection of complete child subtrees leaves a parent-closed
set. -/
theorem residual_parentClosed
    (hH : H.IsTree) (root v : V) (hdec : ParentDistanceDecreases hH root)
    {selected : Finset V}
    (hselected : ∀ c ∈ selected, IsChild hH root v c) :
    ParentClosed hH root (residual hH root selected) := by
  constructor
  · rw [mem_residual]
    rw [mem_selectedDescendants]
    rintro ⟨c, hcselected, hrootc⟩
    exact root_not_mem_childSubtree hH root (hselected c hcselected).1 hrootc
  · intro x hxR hxroot
    rw [mem_residual] at hxR ⊢
    intro hpRemoved
    rw [mem_selectedDescendants] at hpRemoved
    rcases hpRemoved with ⟨c, hcselected, hpc⟩
    apply hxR
    rw [mem_selectedDescendants]
    exact ⟨c, hcselected,
      mem_descendants_of_parent_mem hH root hdec
        (hselected c hcselected).1 hxroot hpc⟩

/-- The residual complement of selected child subtrees is connected. -/
theorem residual_connected
    (hH : H.IsTree) (root v : V) (hdec : ParentDistanceDecreases hH root)
    {selected : Finset V}
    (hselected : ∀ c ∈ selected, IsChild hH root v c) :
    (H.induce {x : V | x ∈ residual hH root selected}).Connected :=
  (residual_parentClosed hH root v hdec hselected).connected hH root hdec

/-- The support formed from selected child subtrees is connected through its
retained pivot. -/
theorem pruningSupport_connected
    (hH : H.IsTree) (root v : V) {selected : Finset V}
    (hselected : ∀ c ∈ selected, IsChild hH root v c) :
    (H.induce {x : V | x ∈ pruningSupport hH root v selected}).Connected := by
  let S : Set V := {x : V | x ∈ pruningSupport hH root v selected}
  have hvS : v ∈ S := by simp [S]
  refine H.induce_connected_of_patches v hvS ?_
  intro x hxS
  have hxSupport : x ∈ pruningSupport hH root v selected := hxS
  rw [mem_pruningSupport] at hxSupport
  rcases hxSupport with rfl | ⟨c, hcselected, hxc⟩
  · exact ⟨S, Set.Subset.rfl, hvS, hvS, .rfl⟩
  · have hc := hselected c hcselected
    have hcSubtree : c ∈ childSubtree hH root c :=
      self_mem_descendants hH root c
    have hcS : c ∈ S := by
      rw [show c ∈ S ↔ c ∈ pruningSupport hH root v selected from Iff.rfl]
      rw [mem_pruningSupport]
      exact Or.inr ⟨c, hcselected, hcSubtree⟩
    have hsub : {z : V | z ∈ childSubtree hH root c} ⊆ S := by
      intro z hz
      rw [show z ∈ S ↔ z ∈ pruningSupport hH root v selected from Iff.rfl]
      rw [mem_pruningSupport]
      exact Or.inr ⟨c, hcselected, hz⟩
    rcases (mem_childSubtree hH root c x).1 hxc with ⟨n, hn, hiter⟩
    have hcx := reachable_in_descendants_of_iterate hH root c hn hiter
    have hcxS : (H.induce S).Reachable ⟨c, hcS⟩ ⟨x, hxS⟩ := by
      exact hcx.symm.map (H.induceHomOfLE hsub).toHom
    have hvcS : (H.induce S).Adj ⟨v, hvS⟩ ⟨c, hcS⟩ := hc.2 ▸ parent_adj hH root hc.1
    exact ⟨S, Set.Subset.rfl, hvS, hxS, hvcS.reachable.trans hcxS⟩

/-- The emitted support and residual share at most the retained pivot. -/
theorem pruningSupport_inter_residual_subset
    (hH : H.IsTree) (root v : V) (selected : Finset V) :
    pruningSupport hH root v selected ∩ residual hH root selected ⊆ {v} := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hxSupport, hxResidual⟩
  rw [mem_pruningSupport] at hxSupport
  rw [mem_residual] at hxResidual
  rcases hxSupport with hxv | ⟨c, hcselected, hxc⟩
  · simpa [hxv]
  · exact (hxResidual ((mem_selectedDescendants hH root selected x).2
      ⟨c, hcselected, hxc⟩)).elim

/-- Internal tree edges of the emitted support and residual are disjoint.
This edge-level form follows directly from their singleton intersection. -/
theorem pruningSupport_residual_no_common_edge
    (hH : H.IsTree) (root v : V) (selected : Finset V) {x y : V}
    (hxy : H.Adj x y)
    (hxs : x ∈ pruningSupport hH root v selected)
    (hys : y ∈ pruningSupport hH root v selected)
    (hxr : x ∈ residual hH root selected)
    (hyr : y ∈ residual hH root selected) : False := by
  have hxv : x = v := by
    simpa using pruningSupport_inter_residual_subset hH root v selected
      (Finset.mem_inter.mpr ⟨hxs, hxr⟩)
  have hyv : y = v := by
    simpa using pruningSupport_inter_residual_subset hH root v selected
      (Finset.mem_inter.mpr ⟨hys, hyr⟩)
  exact hxy.ne (hxv.trans hyv.symm)

/-- Exact graph assembly needed by one Observation 2.12 pruning iteration.
The selected support and parent-closed residual are connected, and no tree
edge is internal to both. -/
theorem pruning_components
    (hH : H.IsTree) (root v : V) (hdec : ParentDistanceDecreases hH root)
    {selected : Finset V}
    (hselected : ∀ c ∈ selected, IsChild hH root v c) :
    (H.induce {x : V | x ∈ pruningSupport hH root v selected}).Connected ∧
    (H.induce {x : V | x ∈ residual hH root selected}).Connected ∧
    pruningSupport hH root v selected ∩ residual hH root selected ⊆ {v} := by
  exact ⟨pruningSupport_connected hH root v hselected,
    residual_connected hH root v hdec hselected,
    pruningSupport_inter_residual_subset hH root v selected⟩

/-- Exact graph assembly for the other Observation 2.12 branch, which emits
one complete child subtree and deletes all of its vertices. -/
theorem childSubtree_components
    (hH : H.IsTree) (root : V) (hdec : ParentDistanceDecreases hH root)
    {v c : V} (hc : IsChild hH root v c) :
    (H.induce {x : V | x ∈ childSubtree hH root c}).Connected ∧
    (H.induce {x : V | x ∈ residual hH root {c}}).Connected ∧
    Disjoint (childSubtree hH root c) (residual hH root {c}) := by
  refine ⟨childSubtree_connected hH root c,
    residual_connected hH root v hdec (by simpa using hc), ?_⟩
  apply Finset.disjoint_left.mpr
  intro x hxc hxr
  rw [mem_residual] at hxr
  apply hxr
  rw [mem_selectedDescendants]
  exact ⟨c, by simp, hxc⟩

end ChekuriChuzhoyRootedTreeComponents
end SimpleGraph

end Lax17Proofs
