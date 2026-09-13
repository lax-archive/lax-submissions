import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Lax17Proofs.Source.MinorContract

namespace Lax17Proofs

universe u v w


/-!
# Basic graph-minor API

This file proves reusable lemmas about the branch-set minor model from
`MinorContract.lean`.  The first API needed by the grid-minor proof is
monotonicity: if `H` is a minor of `G`, then it is also a minor of any
supergraph of `G` on the same vertex type.
-/

namespace SimpleGraph

/-- An isomorphism maps an induced subgraph on a finite vertex set to the
induced subgraph on the image of that set. -/
noncomputable def inducedIsoMapFinset {V V' : Type*}
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') (S : Finset V) :
    G.induce {v : V | v ∈ S} ≃g
      G'.induce {v : V' | v ∈ S.map e.toEquiv.toEmbedding} where
  toFun := fun v =>
    ⟨e v.1, by
      change e v.1 ∈ S.map e.toEquiv.toEmbedding
      exact Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
  invFun := fun v =>
    ⟨e.symm v.1, by
      change e.symm v.1 ∈ S
      rcases Finset.mem_map.mp v.2 with ⟨w, hw, hwv⟩
      have hw_eq : w = e.symm v.1 := by
        rw [← hwv]
        simp
      simpa [← hw_eq] using hw⟩
  left_inv := by
    intro v
    apply Subtype.ext
    simp
  right_inv := by
    intro v
    apply Subtype.ext
    simp
  map_rel_iff' := by
    intro u v
    change G'.Adj (e u.1) (e v.1) ↔ G.Adj u.1 v.1
    exact _root_.SimpleGraph.Iso.map_adj_iff e

namespace MinorModel

/-- The singleton branch-set model witnessing that every graph is a minor of
itself. -/
def refl {V : Type*} (G : _root_.SimpleGraph V) : MinorModel G G where
  branchSet := fun v => {v}
  branch_nonempty := by
    intro v
    exact ⟨v, by simp⟩
  branch_connected := by
    intro v
    haveI : Nonempty {x : V | x ∈ ({v} : Finset V)} := ⟨⟨v, by simp⟩⟩
    haveI : Subsingleton {x : V | x ∈ ({v} : Finset V)} := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : x.1 = v := by simpa using x.2
      have hy : y.1 = v := by simpa using y.2
      exact hx.trans hy.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    have hxu' : x = u := by simpa using hxu
    have hxv' : x = v := by simpa using hxv
    exact huv (hxu'.symm.trans hxv')
  adjacent := by
    intro u v huv
    exact ⟨u, by simp, v, by simp, huv⟩

/-- A graph embedding gives a singleton-branch minor model. -/
def of_embedding {W V : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (e : H ↪g G) : MinorModel H G where
  branchSet := fun w => {e w}
  branch_nonempty := by
    intro w
    exact ⟨e w, by simp⟩
  branch_connected := by
    intro w
    haveI : Nonempty {x : V | x ∈ ({e w} : Finset V)} := ⟨⟨e w, by simp⟩⟩
    haveI : Subsingleton {x : V | x ∈ ({e w} : Finset V)} := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : x.1 = e w := by simpa using x.2
      have hy : y.1 = e w := by simpa using y.2
      exact hx.trans hy.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    have hxu' : x = e u := by simpa using hxu
    have hxv' : x = e v := by simpa using hxv
    exact huv (e.injective (hxu'.symm.trans hxv'))
  adjacent := by
    intro u v huv
    exact ⟨e u, by simp, e v, by simp, e.map_rel_iff.mpr huv⟩

/-- The union of host branch sets visited by a walk in the pattern graph. -/
noncomputable def walkBranchUnion {W V : Type*} [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : MinorModel H G) {x y : W} (P : H.Walk x y) : Finset V :=
  P.support.toFinset.biUnion M.branchSet

/-- A vertex of a branch set visited by the walk belongs to the walk branch
union. -/
theorem mem_walkBranchUnion_of_mem_branch {W V : Type*}
    [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : MinorModel H G) {x y z : W} {P : H.Walk x y}
    (hz : z ∈ P.support.toFinset) {v : V}
    (hv : v ∈ M.branchSet z) :
    v ∈ M.walkBranchUnion P := by
  classical
  simpa [walkBranchUnion] using (Finset.mem_biUnion.2 ⟨z, hz, hv⟩)

/-- The union of host branch sets along a pattern walk induces a connected
subgraph of the host. -/
theorem walkBranchUnion_connected {W V : Type*} [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : MinorModel H G) :
    {x y : W} →
      (P : H.Walk x y) →
        (G.induce {v : V | v ∈ M.walkBranchUnion P}).Connected
  | x, _, _root_.SimpleGraph.Walk.nil' _ => by
      rw [show
        {v : V | v ∈ M.walkBranchUnion
          ((_root_.SimpleGraph.Walk.nil : H.Walk x x))}
          = {v : V | v ∈ M.branchSet x} by
          ext v
          simp [walkBranchUnion]]
      exact M.branch_connected x
  | x, z, _root_.SimpleGraph.Walk.cons' _ y _ hxy P => by
      classical
      have hbranch :
          (G.induce {v : V | v ∈ M.branchSet x}).Connected :=
        M.branch_connected x
      have htail :
          (G.induce {v : V | v ∈ M.walkBranchUnion P}).Connected :=
        M.walkBranchUnion_connected P
      rcases M.adjacent hxy with ⟨u, hu, v, hv, huv⟩
      have hvTail : v ∈ M.walkBranchUnion P :=
        M.mem_walkBranchUnion_of_mem_branch (by simp) hv
      have hconn :
          (G.induce
            ({v : V | v ∈ M.branchSet x} ∪
              {v : V | v ∈ M.walkBranchUnion P})).Connected :=
        _root_.SimpleGraph.connected_induce_union
          hbranch.preconnected htail.preconnected hu hvTail huv
      rw [show
        {w : V | w ∈ M.walkBranchUnion
          (_root_.SimpleGraph.Walk.cons hxy P)}
          =
        ({w : V | w ∈ M.branchSet x} ∪
          {w : V | w ∈ M.walkBranchUnion P}) by
          ext w
          simp [walkBranchUnion, _root_.SimpleGraph.Walk.support_cons,
            Finset.mem_biUnion]]
      exact hconn

/-- Transport the host graph of a minor model across a graph isomorphism. -/
noncomputable def of_iso_right {W V V' : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') (M : MinorModel H G) : MinorModel H G' where
  branchSet := fun w => (M.branchSet w).map e.toEquiv.toEmbedding
  branch_nonempty := by
    intro w
    rcases M.branch_nonempty w with ⟨x, hx⟩
    exact ⟨e x, by
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
  branch_connected := by
    intro w
    exact ((inducedIsoMapFinset e (M.branchSet w)).connected_iff).mp
      (M.branch_connected w)
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    rcases Finset.mem_map.mp hxu with ⟨a, hau, hax⟩
    rcases Finset.mem_map.mp hxv with ⟨b, hbv, hbx⟩
    have hab : a = b := by
      apply e.toEquiv.injective
      exact hax.trans hbx.symm
    exact Finset.disjoint_left.mp (M.branch_disjoint huv) hau (by
      simpa [hab] using hbv)
  adjacent := by
    intro u v huv
    rcases M.adjacent huv with ⟨x, hx, y, hy, hxy⟩
    refine ⟨e x, ?_, e y, ?_, ?_⟩
    · change e x ∈ (M.branchSet u).map e.toEquiv.toEmbedding
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · change e y ∈ (M.branchSet v).map e.toEquiv.toEmbedding
      exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    · exact (_root_.SimpleGraph.Iso.map_adj_iff e).mpr hxy

end MinorModel

namespace IsMinor

/-- Build a graph minor directly from branch-set data.  This is a named
constructor for the standard branch-set model, useful when a proof has already
assembled the nonempty connected branch sets, disjointness, and edge
realization obligations. -/
theorem of_branchSets {W V : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (branchSet : W → Finset V)
    (branch_nonempty : ∀ w : W, (branchSet w).Nonempty)
    (branch_connected :
      ∀ w : W, (G.induce {v : V | v ∈ branchSet w}).Connected)
    (branch_disjoint :
      ∀ ⦃u v : W⦄, u ≠ v → Disjoint (branchSet u) (branchSet v))
    (adjacent :
      ∀ ⦃u v : W⦄, H.Adj u v →
        ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y) :
    IsMinor H G :=
  ⟨{
    branchSet := branchSet
    branch_nonempty := branch_nonempty
    branch_connected := branch_connected
    branch_disjoint := branch_disjoint
    adjacent := adjacent
  }⟩

/-- Every graph is a minor of itself. -/
theorem refl {V : Type*} (G : _root_.SimpleGraph V) : IsMinor G G :=
  ⟨MinorModel.refl G⟩

/-- Every embedded graph is a minor of its host. -/
theorem of_embedding {W V : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (e : H ↪g G) : IsMinor H G :=
  ⟨MinorModel.of_embedding e⟩

/-- A minor model can be transported across an isomorphism of the pattern graph. -/
theorem of_iso_left {W W' V : Type*}
    {H : _root_.SimpleGraph W} {H' : _root_.SimpleGraph W'}
    {G : _root_.SimpleGraph V}
    (e : H' ≃g H) (hminor : IsMinor H G) :
    IsMinor H' G := by
  rcases hminor with ⟨M⟩
  refine ⟨{
    branchSet := fun w => M.branchSet (e w)
    branch_nonempty := ?_
    branch_connected := ?_
    branch_disjoint := ?_
    adjacent := ?_
  }⟩
  · intro w
    exact M.branch_nonempty (e w)
  · intro w
    exact M.branch_connected (e w)
  · intro u v huv
    exact M.branch_disjoint (fun h => huv (e.injective h))
  · intro u v huv
    exact M.adjacent ((_root_.SimpleGraph.Iso.map_adj_iff e).mpr huv)

/-- Minor containment is invariant under isomorphism of the pattern graph. -/
theorem iso_left_iff {W W' V : Type*}
    {H : _root_.SimpleGraph W} {H' : _root_.SimpleGraph W'}
    {G : _root_.SimpleGraph V}
    (e : H' ≃g H) :
    IsMinor H' G ↔ IsMinor H G :=
  ⟨of_iso_left e.symm, of_iso_left e⟩

/-- A minor model can be transported across an isomorphism of the host graph. -/
theorem of_iso_right {W V V' : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') (hminor : IsMinor H G) :
    IsMinor H G' := by
  rcases hminor with ⟨M⟩
  exact ⟨M.of_iso_right e⟩

/-- Minor containment is invariant under isomorphism of the host graph. -/
theorem iso_right_iff {W V V' : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') :
    IsMinor H G ↔ IsMinor H G' :=
  ⟨of_iso_right e, of_iso_right e.symm⟩

/-- Minor containment is invariant under simultaneous relabeling of the pattern
and host graphs. -/
theorem iso_iff {W W' V V' : Type*}
    {H : _root_.SimpleGraph W} {H' : _root_.SimpleGraph W'}
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'}
    (eH : H ≃g H') (eG : G ≃g G') :
    IsMinor H G ↔ IsMinor H' G' :=
  ⟨fun h => of_iso_left eH.symm (of_iso_right eG h),
    fun h => of_iso_left eH (of_iso_right eG.symm h)⟩

/-- Graph minors are monotone under adding edges to the host graph. -/
theorem mono {W V : Type*}
    {H : _root_.SimpleGraph W} {G G' : _root_.SimpleGraph V}
    (hminor : IsMinor H G) (hGG' : G ≤ G') :
    IsMinor H G' := by
  rcases hminor with ⟨M⟩
  refine ⟨{
    branchSet := M.branchSet
    branch_nonempty := M.branch_nonempty
    branch_connected := ?_
    branch_disjoint := M.branch_disjoint
    adjacent := ?_
  }⟩
  · intro w
    refine _root_.SimpleGraph.Connected.mono ?_ (M.branch_connected w)
    intro x y hxy
    exact hGG' hxy
  · intro u v huv
    rcases M.adjacent huv with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hGG' hxy⟩

end IsMinor

namespace ContainsGridMinor

/-- Grid-minor containment is invariant under isomorphism of the host graph. -/
theorem of_iso {V V' : Type u}
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'} {g : ℕ}
    (e : G ≃g G') (hgrid : ContainsGridMinor G g) :
    ContainsGridMinor G' g := by
  rcases hgrid with ⟨W, hWfin, hWdec, H, hHgrid, hminor⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, inferInstance, inferInstance, H, hHgrid, hminor.of_iso_right e⟩

/-- Grid-minor containment is unchanged by relabeling the host graph. -/
theorem iso_iff {V V' : Type u}
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'} {g : ℕ}
    (e : G ≃g G') :
    ContainsGridMinor G g ↔ ContainsGridMinor G' g :=
  ⟨of_iso e, of_iso e.symm⟩

/-- Grid-minor containment is monotone under adding edges to the host graph. -/
theorem mono {V : Type u}
    {G G' : _root_.SimpleGraph V} {g : ℕ}
    (hgrid : ContainsGridMinor G g) (hGG' : G ≤ G') :
    ContainsGridMinor G' g := by
  rcases hgrid with ⟨W, hWfin, hWdec, H, hHgrid, hminor⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, inferInstance, inferInstance, H, hHgrid, hminor.mono hGG'⟩

end ContainsGridMinor

end SimpleGraph

end Lax17Proofs
