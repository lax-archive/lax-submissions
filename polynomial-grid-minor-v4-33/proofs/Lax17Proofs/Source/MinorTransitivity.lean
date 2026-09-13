import Lax17Proofs.Source.Minor

namespace Lax17Proofs

universe u v w


/-!
# Graph-minor transitivity

This module exposes transitivity of graph minors outside the contract namespace.
The proof composes branch sets: the branch set of a vertex `u` of the first
minor model is the disjoint union of the branch sets, in the second model, of
all vertices lying in the first branch set of `u`.
-/

namespace SimpleGraph

namespace MinorModel

/-- Branch set used in the composition of two minor models. -/
def composeBranchSet {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) (u : U) : Finset V :=
  (M.branchSet u).disjiUnion N.branchSet (by
    intro a _ b _ hab
    exact N.branch_disjoint hab)

theorem mem_composeBranchSet {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) (u : U) (x : V) :
    x ∈ composeBranchSet M N u ↔
      ∃ w ∈ M.branchSet u, x ∈ N.branchSet w := by
  simp [composeBranchSet]

private theorem branchSet_subset_composeBranchSet {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) {u : U}
    {w : W} (hw : w ∈ M.branchSet u) :
    {x : V | x ∈ N.branchSet w} ⊆
      {x : V | x ∈ composeBranchSet M N u} := by
  intro x hx
  change x ∈ composeBranchSet M N u
  rw [mem_composeBranchSet]
  exact ⟨w, hw, hx⟩

private theorem reachable_in_composeBranchSet_of_walk {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) {u : U} :
    ∀ {a b : {w : W | w ∈ M.branchSet u}},
      (p : (H.induce {w : W | w ∈ M.branchSet u}).Walk a b) →
        ∀ {x y : V}, (hx : x ∈ N.branchSet a.1) → (hy : y ∈ N.branchSet b.1) →
          (G.induce {z : V | z ∈ composeBranchSet M N u}).Reachable
            ⟨x, by
              change x ∈ composeBranchSet M N u
              rw [mem_composeBranchSet]
              exact ⟨a.1, a.2, hx⟩⟩
            ⟨y, by
              change y ∈ composeBranchSet M N u
              rw [mem_composeBranchSet]
              exact ⟨b.1, b.2, hy⟩⟩
    := by
  intro a b p
  induction p with
  | @nil a =>
      intro x y hx hy
      have hsubset := branchSet_subset_composeBranchSet M N (u := u) a.2
      have hreach :
          (G.induce {z : V | z ∈ N.branchSet a.1}).Reachable
            ⟨x, hx⟩ ⟨y, by simpa using hy⟩ :=
        N.branch_connected a.1 ⟨x, hx⟩ ⟨y, by simpa using hy⟩
      have hreach' := hreach.map (G.induceHomOfLE hsubset).toHom
      simpa using hreach'
  | @cons a a' b haa' p ih =>
      intro x y hx hy
      rcases N.adjacent (_root_.SimpleGraph.induce_adj.mp haa') with
        ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩
      have hsubseta := branchSet_subset_composeBranchSet M N (u := u) a.2
      have hreach_head :
          (G.induce {z : V | z ∈ N.branchSet a.1}).Reachable
            ⟨x, hx⟩ ⟨x₀, hx₀⟩ :=
        N.branch_connected a.1 ⟨x, hx⟩ ⟨x₀, hx₀⟩
      have hhead := hreach_head.map (G.induceHomOfLE hsubseta).toHom
      have hx₀c : x₀ ∈ composeBranchSet M N u := by
        rw [mem_composeBranchSet]
        exact ⟨a.1, a.2, hx₀⟩
      have hy₀c : y₀ ∈ composeBranchSet M N u := by
        rw [mem_composeBranchSet]
        exact ⟨a'.1, a'.2, hy₀⟩
      have hedge :
          (G.induce {z : V | z ∈ composeBranchSet M N u}).Reachable
            ⟨x₀, hx₀c⟩ ⟨y₀, hy₀c⟩ :=
        (_root_.SimpleGraph.induce_adj.mpr hxy₀).reachable
      have htail := ih hy₀ hy
      have hxc : x ∈ composeBranchSet M N u := by
        rw [mem_composeBranchSet]
        exact ⟨a.1, a.2, hx⟩
      have hhead' :
          (G.induce {z : V | z ∈ composeBranchSet M N u}).Reachable
            ⟨x, hxc⟩ ⟨x₀, hx₀c⟩ := by
        simpa using hhead
      exact hhead'.trans (hedge.trans htail)

/-- Compose two branch-set models of graph minors. -/
def trans {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) :
    MinorModel F G where
  branchSet := composeBranchSet M N
  branch_nonempty := by
    intro u
    rcases M.branch_nonempty u with ⟨w, hw⟩
    rcases N.branch_nonempty w with ⟨x, hx⟩
    exact ⟨x, by
      rw [mem_composeBranchSet]
      exact ⟨w, hw, hx⟩⟩
  branch_connected := by
    intro u
    rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
    rcases M.branch_nonempty u with ⟨w₀, hw₀⟩
    rcases N.branch_nonempty w₀ with ⟨x₀, hx₀⟩
    refine ⟨⟨x₀, by
      change x₀ ∈ composeBranchSet M N u
      rw [mem_composeBranchSet]
      exact ⟨w₀, hw₀, hx₀⟩⟩, ?_⟩
    rintro ⟨y, hy⟩
    change y ∈ composeBranchSet M N u at hy
    rw [mem_composeBranchSet] at hy
    rcases hy with ⟨w, hw, hyw⟩
    have hwalk :
        (H.induce {z : W | z ∈ M.branchSet u}).Reachable
          ⟨w₀, hw₀⟩ ⟨w, hw⟩ :=
      M.branch_connected u ⟨w₀, hw₀⟩ ⟨w, hw⟩
    exact hwalk.elim fun p =>
      reachable_in_composeBranchSet_of_walk M N p hx₀ hyw
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    rw [mem_composeBranchSet] at hxu hxv
    rcases hxu with ⟨a, hau, hxa⟩
    rcases hxv with ⟨b, hbv, hxb⟩
    by_cases hab : a = b
    · subst b
      exact Finset.disjoint_left.mp (M.branch_disjoint huv) hau hbv
    · exact Finset.disjoint_left.mp (N.branch_disjoint hab) hxa hxb
  adjacent := by
    intro u v huv
    rcases M.adjacent huv with ⟨a, hau, b, hbv, hab⟩
    rcases N.adjacent hab with ⟨x, hxa, y, hyb, hxy⟩
    refine ⟨x, ?_, y, ?_, hxy⟩
    · rw [mem_composeBranchSet]
      exact ⟨a, hau, hxa⟩
    · rw [mem_composeBranchSet]
      exact ⟨b, hbv, hyb⟩

end MinorModel

/-- Graph minors are transitive. -/
theorem IsMinor.trans {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (hFH : IsMinor F H) (hHG : IsMinor H G) :
    IsMinor F G := by
  rcases hFH with ⟨M⟩
  rcases hHG with ⟨N⟩
  exact ⟨M.trans N⟩

namespace ContainsGridMinor

/-- Grid-minor containment transfers forward through a graph-minor relation. -/
theorem of_minor {W V : Type u}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V} {g : ℕ}
    (hgrid : ContainsGridMinor H g) (hminor : IsMinor H G) :
    ContainsGridMinor G g := by
  rcases hgrid with ⟨U, hUfin, hUdec, F, hFgrid, hFH⟩
  letI : Fintype U := hUfin
  letI : DecidableEq U := hUdec
  exact ⟨U, inferInstance, inferInstance, F, hFgrid, hFH.trans hminor⟩

/-- Grid-minor containment transfers forward through a graph-minor relation
from a small-universe intermediate graph into an arbitrary host universe.  The
grid witness is lifted to the host universe before composing minor models. -/
theorem of_minor_small {W : Type} {V : Type u}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V} {g : ℕ}
    (hgrid : ContainsGridMinor H g) (hminor : IsMinor H G) :
    ContainsGridMinor G g := by
  rcases hgrid with ⟨U, hUfin, hUdec, F, hFgrid, hFH⟩
  letI : Fintype U := hUfin
  letI : DecidableEq U := hUdec
  let F_lift : _root_.SimpleGraph (ULift.{u, 0} U) :=
    _root_.SimpleGraph.comap Equiv.ulift F
  let e : F_lift ≃g F :=
    { Equiv.ulift with
      map_rel_iff' := by
        intro x y
        rfl }
  exact ⟨ULift.{u, 0} U, inferInstance, inferInstance, F_lift,
    IsGridGraph.of_iso e hFgrid,
    IsMinor.of_iso_left e (hFH.trans hminor)⟩

end ContainsGridMinor

end SimpleGraph

end Lax17Proofs
