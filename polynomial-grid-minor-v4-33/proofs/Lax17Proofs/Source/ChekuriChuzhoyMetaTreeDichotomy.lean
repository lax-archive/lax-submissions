import Lax17Proofs.Source.TreeOfSets
import Lax17Proofs.Source.ChekuriChuzhoyTheorem215
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

namespace Lax17Proofs

universe u v w

/-!
# Finite meta-tree dichotomy

The self-contained tree-counting component used in Chekuri--Chuzhoy
Theorem 4.6 and in the Section 5 Phase-1 support-tree dichotomy.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical

section MetaTreeDichotomy

variable {α : Type u}

/-- A simple path starting at `root` and passing through `v`, with arbitrary
endpoint.  This is the rooted object used in the finite tree counting proof of
the meta-tree dichotomy. -/
abbrev RootPathThrough (G : _root_.SimpleGraph α) (root v : α) :=
  Σ t : α, {p : G.Path root t // v ∈ (p : G.Walk root t).support}

namespace RootPathThrough

variable {G : _root_.SimpleGraph α} {root v : α}

/-- The endpoint of a rooted path-through witness. -/
def target (P : RootPathThrough G root v) : α := P.1

/-- The underlying walk of a rooted path-through witness. -/
def walk (P : RootPathThrough G root v) : G.Walk root P.target := P.2.1.1

/-- The underlying walk is a simple path. -/
theorem isPath (P : RootPathThrough G root v) : P.walk.IsPath := P.2.1.2

/-- The distinguished vertex lies on the path. -/
theorem mem_support (P : RootPathThrough G root v) : v ∈ P.walk.support := P.2.2

/-- The length of a rooted path-through witness. -/
def length (P : RootPathThrough G root v) : ℕ := P.walk.length

@[simp] theorem length_eq (P : RootPathThrough G root v) :
    P.length = P.walk.length := rfl

end RootPathThrough

variable {G : _root_.SimpleGraph α} {root v : α}

/-- In a connected graph, every vertex is contained in some simple path from
the root. -/
theorem exists_rootPathThrough_of_connected
    (hconn : G.Connected) (root v : α) :
    Nonempty (RootPathThrough G root v) := by
  classical
  rcases (hconn root v).exists_path_of_dist with ⟨p, hp, _hlen⟩
  exact ⟨⟨v, ⟨⟨p, hp⟩, by simp⟩⟩⟩

variable [Fintype α] [DecidableEq α]

/-- The rooted path-through witnesses are finite in a finite graph. -/
noncomputable instance rootPathThroughFintype [DecidableRel G.Adj] :
    Fintype (RootPathThrough G root v) := by
  classical
  infer_instance

/-- Choose a longest simple path starting at `root` and passing through `v`. -/
noncomputable def longestRootPathThrough [DecidableRel G.Adj]
    (hconn : G.Connected) (root v : α) :
    RootPathThrough G root v :=
  Classical.choose <|
    Finset.exists_max_image (Finset.univ : Finset (RootPathThrough G root v))
      RootPathThrough.length
      (by
        rcases exists_rootPathThrough_of_connected (G := G) hconn root v with ⟨P⟩
        exact ⟨P, Finset.mem_univ P⟩)

/-- The chosen rooted path-through witness has maximum length among all such
witnesses. -/
theorem longestRootPathThrough_spec [DecidableRel G.Adj]
    (hconn : G.Connected) (root v : α)
    (P : RootPathThrough G root v) :
    P.length ≤ (longestRootPathThrough (G := G) hconn root v).length := by
  classical
  have hspec := Classical.choose_spec <|
    Finset.exists_max_image (Finset.univ : Finset (RootPathThrough G root v))
      RootPathThrough.length
      (by
        rcases exists_rootPathThrough_of_connected (G := G) hconn root v with ⟨Q⟩
        exact ⟨Q, Finset.mem_univ Q⟩)
  exact hspec.2 P (Finset.mem_univ P)

/-- A longest rooted path-through witness in an acyclic graph ends at a leaf,
provided the distinguished vertex is not the root. -/
theorem degreeEquals_target_longestRootPathThrough
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hconn : G.Connected)
    {root v : α} (hv : v ≠ root) :
    DegreeEquals G (longestRootPathThrough (G := G) hconn root v).target 1 := by
  classical
  let P : RootPathThrough G root v :=
    longestRootPathThrough (G := G) hconn root v
  let p : G.Walk root P.target := P.walk
  have hp : p.IsPath := P.isPath
  have hvp : v ∈ p.support := P.mem_support
  have hp_not_nil : ¬ p.Nil := by
    intro hnil
    have hsupport : p.support = [root] := _root_.SimpleGraph.Walk.nil_iff_support_eq.mp hnil
    have hvroot : v = root := by
      simpa [hsupport] using hvp
    exact hv hvroot
  let pred : α := p.penultimate
  have hpred_adj_target : G.Adj P.target pred :=
    (p.adj_penultimate hp_not_nil).symm
  refine degreeEquals_one_of_unique_neighbor hpred_adj_target ?_
  intro y hy
  by_cases hypred : y = pred
  · exact hypred
  have hy_not_mem : y ∉ p.support := by
    intro hy_mem
    have hprefix_path : (p.takeUntil y hy_mem).IsPath :=
      hp.takeUntil hy_mem
    have hp_eq :
        p = (p.takeUntil y hy_mem).concat hy.symm := by
      exact hacyc.path_concat hprefix_path hp hy.symm hy_mem
    have hpen : p.penultimate = y := by
      rw [hp_eq]
      exact _root_.SimpleGraph.Walk.penultimate_concat _ hy.symm
    exact hypred hpen.symm
  let P' : RootPathThrough G root v :=
    ⟨y, ⟨⟨p.concat hy, hp.concat hy_not_mem hy⟩, by
      simpa [_root_.SimpleGraph.Walk.support_concat, p, P] using
        (List.mem_append_left [y] hvp)⟩⟩
  have hmax := longestRootPathThrough_spec (G := G) hconn root v P'
  change (p.concat hy).length ≤ p.length at hmax
  have hmax' : (p.concat hy).length ≤ p.length := hmax
  have hlen : (p.concat hy).length = p.length + 1 :=
    _root_.SimpleGraph.Walk.length_concat p hy
  omega

/-- The position of `v` on its chosen longest rooted path. -/
noncomputable def longestRootPathIndex [DecidableRel G.Adj]
    (hconn : G.Connected) (root v : α) : ℕ :=
  ((longestRootPathThrough (G := G) hconn root v).walk.support).idxOf v

/-- The chosen index really points to `v`. -/
theorem getVert_longestRootPathIndex [DecidableRel G.Adj]
    (hconn : G.Connected) (root v : α) :
    (longestRootPathThrough (G := G) hconn root v).walk.getVert
        (longestRootPathIndex (G := G) hconn root v) = v := by
  classical
  exact _root_.SimpleGraph.Walk.getVert_support_idxOf
    (longestRootPathThrough (G := G) hconn root v).walk
    (longestRootPathThrough (G := G) hconn root v).mem_support

/-- A non-root vertex occurs at a positive index on its chosen rooted path. -/
theorem longestRootPathIndex_pos [DecidableRel G.Adj]
    (hconn : G.Connected) {root v : α} (hv : v ≠ root) :
    0 < longestRootPathIndex (G := G) hconn root v := by
  classical
  by_contra hpos
  have hidx : longestRootPathIndex (G := G) hconn root v = 0 :=
    Nat.eq_zero_of_not_pos hpos
  have hget := getVert_longestRootPathIndex (G := G) hconn root v
  have hvroot : v = root := by
    rw [hidx] at hget
    simpa using hget.symm
  exact hv hvroot

/-- The chosen index is at most the length of the chosen rooted path. -/
theorem longestRootPathIndex_le_length [DecidableRel G.Adj]
    (hconn : G.Connected) (root v : α) :
    longestRootPathIndex (G := G) hconn root v ≤
      (longestRootPathThrough (G := G) hconn root v).walk.length := by
  classical
  let P : RootPathThrough G root v :=
    longestRootPathThrough (G := G) hconn root v
  have hlt :
      P.walk.support.idxOf v < P.walk.support.length :=
    List.idxOf_lt_length_of_mem P.mem_support
  simpa [longestRootPathIndex, P, _root_.SimpleGraph.Walk.length_support] using hlt

/-- A finite tree with at least `ell^2` vertices either has a simple path long
enough to provide the buffered order, or it has at least `ell + 1` leaves.

This is the self-contained tree-counting part of Chekuri--Chuzhoy Theorem 4.6
(Claim 2.2 as used there), with the constants matched to the repository's
buffered-path convention. -/
theorem exists_bufferedPath_or_manyLeaves_of_tree
    [DecidableRel G.Adj] (hT : G.IsTree) {ell : ℕ}
    (hell : 1 < ell) (hcard : ell ^ 2 ≤ Fintype.card α) :
    (∃ order : Fin (ell + 2) → α,
        Function.Injective order ∧
          ∀ r : Fin (ell + 1),
            G.Adj (order ⟨r.1, by omega⟩)
              (order ⟨r.1 + 1, by omega⟩)) ∨
      ∃ leaves : Finset α,
        (∀ x : α, x ∈ leaves ↔ DegreeEquals G x 1) ∧
          ell + 1 ≤ leaves.card ∧
          ∀ {a b : α} (p : G.Walk a b), p.IsPath → p.length ≤ ell := by
  classical
  by_cases hlong :
      ∃ a b : α, ∃ p : G.Walk a b, p.IsPath ∧ ell + 1 ≤ p.length
  · rcases hlong with ⟨a, b, p, hp, hlen⟩
    let order : Fin (ell + 2) → α := fun r => p.getVert r.1
    refine Or.inl ⟨order, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      have hidx := hp.getVert_injOn
        (by simp; omega : i.1 ∈ {n : ℕ | n ≤ p.length})
        (by simp; omega : j.1 ∈ {n : ℕ | n ≤ p.length})
        (by simpa [order] using hij)
      exact hidx
    · intro r
      exact p.adj_getVert_succ (i := r.1) (by omega)
  · let leaves : Finset α := Finset.univ.filter fun x : α => DegreeEquals G x 1
    have hcard_gt_one : 1 < Fintype.card α := by
      have hell_sq_ge : 4 ≤ ell ^ 2 := by nlinarith [hell]
      exact lt_of_lt_of_le (by decide : 1 < 4) (hell_sq_ge.trans hcard)
    haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hcard_gt_one
    rcases hT.exists_vert_degree_one_of_nontrivial with ⟨root, hroot_degree⟩
    have hroot_leaf : DegreeEquals G root 1 :=
      (degreeEquals_iff_degree_eq G root 1).2 hroot_degree
    have hroot_mem_leaves : root ∈ leaves := by
      simp [leaves, hroot_leaf]
    by_cases hmany : ell + 1 ≤ leaves.card
    · refine Or.inr ⟨leaves, by intro x; simp [leaves], hmany, ?_⟩
      intro a b p hp
      by_contra hnot
      exact hlong ⟨a, b, p, hp, by omega⟩
    · have hleaves_le : leaves.card ≤ ell := by omega
      let nonRootLeaves : Finset α := leaves.erase root
      let f : {x : α // x ≠ root} → nonRootLeaves × Fin ell := fun x =>
        let P : RootPathThrough G root x.1 :=
          longestRootPathThrough (G := G) hT.connected root x.1
        let idx : ℕ := longestRootPathIndex (G := G) hT.connected root x.1
        have htarget_leaf : DegreeEquals G P.target 1 :=
          degreeEquals_target_longestRootPathThrough
            (G := G) hT.isAcyclic hT.connected x.2
        have htarget_ne_root : P.target ≠ root := by
          intro htarget
          have hcopy_path : (P.walk.copy rfl htarget).IsPath := by
            exact (_root_.SimpleGraph.Walk.isPath_copy P.walk rfl htarget).2 P.isPath
          have hnil : P.walk.copy rfl htarget = _root_.SimpleGraph.Walk.nil :=
            (_root_.SimpleGraph.Walk.isPath_iff_eq_nil
              (P.walk.copy rfl htarget)).mp hcopy_path
          have hxroot : x.1 = root := by
            have hxmem : x.1 ∈ (P.walk.copy rfl htarget).support := by
              simpa using P.mem_support
            simpa [hnil] using hxmem
          exact x.2 hxroot
        have htarget_mem : P.target ∈ nonRootLeaves := by
          simp [nonRootLeaves, leaves, htarget_leaf, htarget_ne_root]
        have hidx_pos : 0 < idx := by
          simpa [idx] using
            longestRootPathIndex_pos (G := G) hT.connected x.2
        have hidx_le_length : idx ≤ P.walk.length := by
          simpa [idx, P] using
            longestRootPathIndex_le_length (G := G) hT.connected root x.1
        have hlength_le : P.walk.length ≤ ell := by
          by_contra hnot
          have hlongP : ell + 1 ≤ P.walk.length := by omega
          exact hlong ⟨root, P.target, P.walk, P.isPath, hlongP⟩
        (⟨P.target, htarget_mem⟩,
          ⟨idx - 1, by omega⟩)
      have hf_inj : Function.Injective f := by
        intro x y hxy
        dsimp [f] at hxy
        let Px : RootPathThrough G root x.1 :=
          longestRootPathThrough (G := G) hT.connected root x.1
        let Py : RootPathThrough G root y.1 :=
          longestRootPathThrough (G := G) hT.connected root y.1
        let ix : ℕ := longestRootPathIndex (G := G) hT.connected root x.1
        let iy : ℕ := longestRootPathIndex (G := G) hT.connected root y.1
        have htarget : Px.target = Py.target := by
          exact congrArg (fun z : nonRootLeaves × Fin ell => (z.1 : α)) hxy
        have hdepth : (⟨ix - 1, by
              have hix_pos : 0 < ix := by
                simpa [ix] using
                  longestRootPathIndex_pos (G := G) hT.connected x.2
              have hix_len : ix ≤ Px.walk.length := by
                simpa [ix, Px] using
                  longestRootPathIndex_le_length (G := G) hT.connected root x.1
              have hPx_len : Px.walk.length ≤ ell := by
                by_contra hnot
                have hlongP : ell + 1 ≤ Px.walk.length := by omega
                exact hlong ⟨root, Px.target, Px.walk, Px.isPath, hlongP⟩
              omega⟩ : Fin ell) =
            ⟨iy - 1, by
              have hiy_pos : 0 < iy := by
                simpa [iy] using
                  longestRootPathIndex_pos (G := G) hT.connected y.2
              have hiy_len : iy ≤ Py.walk.length := by
                simpa [iy, Py] using
                  longestRootPathIndex_le_length (G := G) hT.connected root y.1
              have hPy_len : Py.walk.length ≤ ell := by
                by_contra hnot
                have hlongP : ell + 1 ≤ Py.walk.length := by omega
                exact hlong ⟨root, Py.target, Py.walk, Py.isPath, hlongP⟩
              omega⟩ := by
          exact congrArg Prod.snd hxy
        have hix_pos : 0 < ix := by
          simpa [ix] using
            longestRootPathIndex_pos (G := G) hT.connected x.2
        have hiy_pos : 0 < iy := by
          simpa [iy] using
            longestRootPathIndex_pos (G := G) hT.connected y.2
        have hixy : ix = iy := by
          have hval : ix - 1 = iy - 1 := congrArg Fin.val hdepth
          omega
        have hPy_copy_path : (Py.walk.copy rfl htarget.symm).IsPath := by
          exact (_root_.SimpleGraph.Walk.isPath_copy Py.walk rfl htarget.symm).2 Py.isPath
        have hpath :
            (⟨Px.walk, Px.isPath⟩ : G.Path root Px.target) =
              ⟨Py.walk.copy rfl htarget.symm, hPy_copy_path⟩ :=
          hT.isAcyclic.path_unique _ _
        have hwalk : Px.walk = Py.walk.copy rfl htarget.symm :=
          congrArg Subtype.val hpath
        apply Subtype.ext
        have hxget := getVert_longestRootPathIndex (G := G) hT.connected root x.1
        have hyget := getVert_longestRootPathIndex (G := G) hT.connected root y.1
        change x.1 = y.1
        calc
          x.1 = Px.walk.getVert ix := by simpa [Px, ix] using hxget.symm
          _ = (Py.walk.copy rfl htarget.symm).getVert iy := by
            rw [hwalk, hixy]
          _ = Py.walk.getVert iy := by simp
          _ = y.1 := by simpa [Py, iy] using hyget
      have hdomain_le :
          Fintype.card {x : α // x ≠ root} ≤
            Fintype.card (nonRootLeaves × Fin ell) :=
        Fintype.card_le_of_injective f hf_inj
      have hdomain_card :
          Fintype.card {x : α // x ≠ root} = Fintype.card α - 1 := by
        rw [Fintype.card_subtype]
        simp [Finset.filter_ne', Finset.card_erase_of_mem]
      have hcodomain_card :
          Fintype.card (nonRootLeaves × Fin ell) = nonRootLeaves.card * ell := by
        rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
      have hnonroot_le : Fintype.card α - 1 ≤ nonRootLeaves.card * ell := by
        simpa [hdomain_card, hcodomain_card] using hdomain_le
      have hnonRootLeaves_card :
          nonRootLeaves.card = leaves.card - 1 := by
        exact Finset.card_erase_of_mem hroot_mem_leaves
      have hnonRootLeaves_le : nonRootLeaves.card ≤ ell - 1 := by
        rw [hnonRootLeaves_card]
        omega
      have hcard_upper : Fintype.card α ≤ (ell - 1) * ell + 1 := by
        have hmul_le : nonRootLeaves.card * ell ≤ (ell - 1) * ell :=
          Nat.mul_le_mul_right ell hnonRootLeaves_le
        have hpred_le : Fintype.card α - 1 ≤ (ell - 1) * ell :=
          hnonroot_le.trans hmul_le
        omega
      have hsquare_gt : (ell - 1) * ell + 1 < ell ^ 2 := by
        have hell_eq : ell = (ell - 1) + 1 := by omega
        rw [hell_eq, pow_two]
        nlinarith
      have hlt : Fintype.card α < ell ^ 2 :=
        lt_of_le_of_lt hcard_upper hsquare_gt
      exact False.elim (not_le_of_gt hlt hcard)

end MetaTreeDichotomy

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
