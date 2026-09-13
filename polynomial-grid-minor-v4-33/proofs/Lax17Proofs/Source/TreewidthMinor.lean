import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.Treewidth

namespace Lax17Proofs

universe u v w

/-!
# Treewidth monotonicity for graph minors

This file proves the standard branch-set-model fact that graph minors do not
increase treewidth.  The construction turns a tree decomposition of the host
graph into a tree decomposition of the pattern graph by putting a pattern
vertex into a decomposition bag exactly when its branch set intersects the
host bag.
-/

namespace SimpleGraph

open scoped Classical

namespace TreeDecomposition

variable {W V : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}

/-- Host-decomposition nodes whose bags hit a finite vertex set. -/
def hitSet (D : TreeDecomposition G) (S : Finset V) : Set D.Node :=
  {i : D.Node | ∃ v ∈ S, v ∈ D.bag i}

/-- A reachable path inside `hitSet` obtained by staying on bags that contain a
fixed graph vertex. -/
theorem reachable_hitSet_of_same_vertex
    (D : TreeDecomposition G) (S : Finset V) {x : V} (hxS : x ∈ S)
    {i j : D.Node} (hi : x ∈ D.bag i) (hj : x ∈ D.bag j) :
    (D.tree.induce (D.hitSet S)).Reachable
      ⟨i, ⟨x, hxS, hi⟩⟩ ⟨j, ⟨x, hxS, hj⟩⟩ := by
  have hreach :
      (D.tree.induce {i : D.Node | x ∈ D.bag i}).Reachable
        ⟨i, hi⟩ ⟨j, hj⟩ :=
    (D.bag_indices_connected x).preconnected ⟨i, hi⟩ ⟨j, hj⟩
  let φ :
      D.tree.induce {i : D.Node | x ∈ D.bag i} →g
        D.tree.induce (D.hitSet S) :=
    { toFun := fun a =>
        ⟨a.1, show a.1 ∈ D.hitSet S from ⟨x, hxS, a.2⟩⟩
      map_rel' := by
        intro a b hab
        exact hab }
  exact hreach.map φ

/-- A walk inside a connected finite vertex set lifts to a path in the
decomposition tree between any two bags that hit the endpoint vertices. -/
theorem reachable_hitSet_of_induce_walk
    (D : TreeDecomposition G) (S : Finset V)
    {a b : {v : V | v ∈ S}}
    (P : (G.induce {v : V | v ∈ S}).Walk a b)
    {i j : D.Node} (hi : a.1 ∈ D.bag i) (hj : b.1 ∈ D.bag j) :
    (D.tree.induce (D.hitSet S)).Reachable
      ⟨i, ⟨a.1, a.2, hi⟩⟩ ⟨j, ⟨b.1, b.2, hj⟩⟩ := by
  induction P generalizing i with
  | @nil u =>
      exact D.reachable_hitSet_of_same_vertex S u.2 hi hj
  | @cons u v w hxy P ih =>
      rcases D.edge_mem_bag (show G.Adj u.1 v.1 from hxy) with
        ⟨m, hum, hvm⟩
      exact
        (D.reachable_hitSet_of_same_vertex S u.2 hi hum).trans
          (ih hvm hj)

/-- Bags that hit a connected finite vertex set form a connected subtree of
the decomposition tree. -/
theorem connected_induce_hitSet
    (D : TreeDecomposition G) (S : Finset V)
    (hSnonempty : S.Nonempty)
    (hSconn : (G.induce {v : V | v ∈ S}).Connected) :
    (D.tree.induce (D.hitSet S)).Connected := by
  rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
  rcases hSnonempty with ⟨r, hrS⟩
  rcases D.vertex_mem_bag r with ⟨root, hroot⟩
  refine ⟨⟨root, ⟨r, hrS, hroot⟩⟩, ?_⟩
  rintro ⟨i, hi⟩
  rcases hi with ⟨v, hvS, hvi⟩
  have hreach :
      (G.induce {v : V | v ∈ S}).Reachable
        ⟨r, hrS⟩ ⟨v, hvS⟩ :=
    hSconn.preconnected ⟨r, hrS⟩ ⟨v, hvS⟩
  exact hreach.elim fun P =>
    D.reachable_hitSet_of_induce_walk S P hroot hvi

/-- The bag assigned to a pattern vertex in the minor-induced tree
decomposition. -/
noncomputable def minorBag
    (D : TreeDecomposition G) (M : MinorModel H G) (i : D.Node) :
    Finset W :=
  (Finset.univ : Finset W).filter fun w =>
    ∃ v ∈ M.branchSet w, v ∈ D.bag i

theorem mem_minorBag_iff
    (D : TreeDecomposition G) (M : MinorModel H G) (i : D.Node)
    {w : W} :
    w ∈ D.minorBag M i ↔ ∃ v ∈ M.branchSet w, v ∈ D.bag i := by
  classical
  simp [minorBag]

/-- Each minor-induced bag injects into the corresponding host bag by choosing
one witness vertex from the relevant branch set. -/
theorem minorBag_card_le_bag
    (D : TreeDecomposition G) (M : MinorModel H G) (i : D.Node) :
    (D.minorBag M i).card ≤ (D.bag i).card := by
  classical
  let f : (D.minorBag M i) → (D.bag i) := fun w =>
    let hw := (D.mem_minorBag_iff M i).1 w.2
    ⟨Classical.choose hw, (Classical.choose_spec hw).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    let vx : V := Classical.choose ((D.mem_minorBag_iff M i).1 x.2)
    let vy : V := Classical.choose ((D.mem_minorBag_iff M i).1 y.2)
    have hvx :
        vx ∈ M.branchSet x.1 :=
      (Classical.choose_spec ((D.mem_minorBag_iff M i).1 x.2)).1
    have hvy :
        vy ∈ M.branchSet y.1 :=
      (Classical.choose_spec ((D.mem_minorBag_iff M i).1 y.2)).1
    have hvxy : vx = vy := by
      exact congrArg Subtype.val hxy
    exact
      (Finset.disjoint_left.mp (M.branch_disjoint hne) hvx
        (by simpa [vx, vy, hvxy] using hvy))
  exact Finset.card_le_card_of_injective hf

/-- A tree decomposition of a host graph induces one of every graph minor in
that host. -/
noncomputable def of_minor
    (D : TreeDecomposition G) (M : MinorModel H G) :
    TreeDecomposition H where
  Node := D.Node
  nodeFintype := D.nodeFintype
  nodeDecidableEq := D.nodeDecidableEq
  tree := D.tree
  isTree := D.isTree
  bag := D.minorBag M
  vertex_mem_bag := by
    intro w
    rcases M.branch_nonempty w with ⟨v, hv⟩
    rcases D.vertex_mem_bag v with ⟨i, hi⟩
    exact ⟨i, (D.mem_minorBag_iff M i).2 ⟨v, hv, hi⟩⟩
  edge_mem_bag := by
    intro x y hxy
    rcases M.adjacent hxy with ⟨a, ha, b, hb, hab⟩
    rcases D.edge_mem_bag hab with ⟨i, hai, hbi⟩
    exact ⟨i,
      (D.mem_minorBag_iff M i).2 ⟨a, ha, hai⟩,
      (D.mem_minorBag_iff M i).2 ⟨b, hb, hbi⟩⟩
  bag_indices_connected := by
    intro w
    have hset :
        {i : D.Node | w ∈ D.minorBag M i} =
          D.hitSet (M.branchSet w) := by
      ext i
      exact D.mem_minorBag_iff M i
    rw [hset]
    exact D.connected_induce_hitSet (M.branchSet w)
      (M.branch_nonempty w) (M.branch_connected w)

theorem of_minor_width_le
    (D : TreeDecomposition G) (M : MinorModel H G) :
    (D.of_minor M).width ≤ D.width := by
  classical
  letI : Fintype D.Node := D.nodeFintype
  have hsup :
      (Finset.univ.sup fun i : D.Node =>
          ((D.of_minor M).bag i).card) ≤
        (Finset.univ.sup fun i : D.Node => (D.bag i).card) := by
    refine Finset.sup_mono_fun ?_
    intro i _hi
    exact D.minorBag_card_le_bag M i
  dsimp [TreeDecomposition.width]
  exact Nat.sub_le_sub_right hsup 1

end TreeDecomposition

namespace HasTreewidthAtMost

/-- Treewidth-at-most is inherited by graph minors. -/
theorem of_minor
    {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V} {k : ℕ}
    (h : HasTreewidthAtMost G k) (hminor : IsMinor H G) :
    HasTreewidthAtMost H k := by
  rcases h with ⟨D, hD⟩
  rcases hminor with ⟨M⟩
  exact ⟨D.of_minor M, (D.of_minor_width_le M).trans hD⟩

end HasTreewidthAtMost

/-- Graph minors do not increase treewidth. -/
theorem treewidth_le_of_minor
    {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (hminor : IsMinor H G) :
    treewidth H ≤ treewidth G :=
  treewidth_le_of_hasTreewidthAtMost
    ((hasTreewidthAtMost_treewidth G).of_minor hminor)

end SimpleGraph

end Lax17Proofs
