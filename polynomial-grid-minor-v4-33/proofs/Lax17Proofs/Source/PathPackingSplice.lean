import Lax17Proofs.Source.FunctionalLinkage
import Lax17Proofs.Source.TreewidthSparsifierPathRuns
import Lax17Proofs.Source.TreewidthSparsifierDefs

namespace Lax17Proofs

universe u v w

/-!
# Splicing a rerouted family of path runs

This module supplies the formal linkage-splicing step used in
`treewidth-sparsifier.pdf`, Claim 5.4.  The primitive directed relation is
literal adjacency in the support list of an oriented graph path.  Expressing
it as a two-element infix makes restriction to maximal runs exact.
-/

namespace SimpleGraph


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

namespace GraphPath

/-- `v` immediately follows `u` in the oriented support of `Q`. -/
def ForwardStep (Q : GraphPath G) (u v : V) : Prop :=
  [u, v] <:+: Q.walk.support

theorem forwardStep_adj (Q : GraphPath G) {u v : V}
    (h : Q.ForwardStep u v) :
    G.Adj u v :=
  Q.walk.adj_of_infix_support h

theorem forwardStep_mem_edgeSet (Q : GraphPath G) {u v : V}
    (h : Q.ForwardStep u v) :
    s(u, v) ∈ Q.edgeSet := by
  classical
  have he : s(u, v) ∈ Q.walk.edges :=
    _root_.SimpleGraph.Walk.infix_support_iff_mem_edges.mp (Or.inl h)
  exact List.mem_toFinset.mpr (by simpa [GraphPath.edgeSet] using he)

theorem forwardStep_or_reverse_of_mem_edgeSet
    (Q : GraphPath G) {u v : V}
    (h : s(u, v) ∈ Q.edgeSet) :
    Q.ForwardStep u v ∨ Q.ForwardStep v u := by
  classical
  have he : s(u, v) ∈ Q.walk.edges :=
    List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using h)
  exact _root_.SimpleGraph.Walk.infix_support_iff_mem_edges.mpr he

theorem forwardStep_endpoints_mem_vertexSet
    (Q : GraphPath G) {u v : V}
    (h : Q.ForwardStep u v) :
    u ∈ Q.vertexSet ∧ v ∈ Q.vertexSet := by
  constructor <;>
    simpa [GraphPath.vertexSet] using
      h.mem (by simp)

theorem forwardStep_ne (Q : GraphPath G) {u v : V}
    (h : Q.ForwardStep u v) :
    u ≠ v := by
  intro huv
  subst v
  have hnodup : ([u, u] : List V).Nodup :=
    h.nodup Q.isPath.support_nodup
  simp at hnodup

theorem forwardStep_rightUnique (Q : GraphPath G) :
    Relator.RightUnique Q.ForwardStep := by
  classical
  intro u v w huv huw
  rcases List.infix_iff_getElem?.mp huv with ⟨i, hi, hget⟩
  rcases List.infix_iff_getElem?.mp huw with ⟨j, hj, hget'⟩
  change 2 + i ≤ Q.walk.support.length at hi
  change 2 + j ≤ Q.walk.support.length at hj
  have hui : Q.walk.support[i]? = some u := by
    simpa using hget 0 (by simp)
  have huj : Q.walk.support[j]? = some u := by
    simpa using hget' 0 (by simp)
  have hvi : Q.walk.support[1 + i]? = some v := by
    simpa using hget 1 (by simp)
  have hwj : Q.walk.support[1 + j]? = some w := by
    simpa using hget' 1 (by simp)
  have hij : i = j := by
    have hiLen : i < Q.walk.support.length := by omega
    have hjLen : j < Q.walk.support.length := by omega
    rw [List.getElem?_eq_getElem hiLen] at hui
    rw [List.getElem?_eq_getElem hjLen] at huj
    have hvalues :
        Q.walk.support[i] = Q.walk.support[j] := by
      exact Option.some.inj (hui.trans huj.symm)
    exact Q.isPath.support_nodup.getElem_inj_iff.mp hvalues
  subst j
  exact Option.some.inj (hvi.symm.trans hwj)

theorem forwardStep_leftUnique (Q : GraphPath G) :
    Relator.LeftUnique Q.ForwardStep := by
  classical
  intro u v w huw hvw
  rcases List.infix_iff_getElem?.mp huw with ⟨i, hi, hget⟩
  rcases List.infix_iff_getElem?.mp hvw with ⟨j, hj, hget'⟩
  change 2 + i ≤ Q.walk.support.length at hi
  change 2 + j ≤ Q.walk.support.length at hj
  have hui : Q.walk.support[i]? = some u := by
    simpa using hget 0 (by simp)
  have hvj : Q.walk.support[j]? = some v := by
    simpa using hget' 0 (by simp)
  have hwi : Q.walk.support[1 + i]? = some w := by
    simpa using hget 1 (by simp)
  have hwj : Q.walk.support[1 + j]? = some w := by
    simpa using hget' 1 (by simp)
  have hij : i = j := by
    have hiLen : i + 1 < Q.walk.support.length := by omega
    have hjLen : j + 1 < Q.walk.support.length := by omega
    rw [List.getElem?_eq_getElem (by omega : 1 + i < Q.walk.support.length)] at hwi
    rw [List.getElem?_eq_getElem (by omega : 1 + j < Q.walk.support.length)] at hwj
    have hvalues :
        Q.walk.support[i + 1] = Q.walk.support[j + 1] := by
      simpa [Nat.add_comm] using Option.some.inj (hwi.trans hwj.symm)
    have := Q.isPath.support_nodup.getElem_inj_iff.mp hvalues
    omega
  subst j
  exact Option.some.inj (hui.symm.trans hvj)

theorem forwardStep_source_no_predecessor (Q : GraphPath G) (v : V) :
    ¬ Q.ForwardStep v Q.source := by
  intro h
  rcases List.infix_iff_getElem?.mp h with ⟨i, hi, hget⟩
  change 2 + i ≤ Q.walk.support.length at hi
  have hs : Q.walk.support[1 + i]? = some Q.source := by
    simpa using hget 1 (by simp)
  have hzero : Q.walk.support[0]? = some Q.source := by simp
  have hiOne : i + 1 < Q.walk.support.length := by omega
  rw [List.getElem?_eq_getElem (by omega : 1 + i < Q.walk.support.length)] at hs
  rw [List.getElem?_eq_getElem (by omega : 0 < Q.walk.support.length)] at hzero
  have hdup :
      Q.walk.support[i + 1] = Q.walk.support[0] := by
    simpa [Nat.add_comm] using Option.some.inj (hs.trans hzero.symm)
  have := Q.isPath.support_nodup.getElem_inj_iff.mp hdup
  omega

theorem forwardStep_target_no_successor (Q : GraphPath G) (v : V) :
    ¬ Q.ForwardStep Q.target v := by
  intro h
  rcases List.infix_iff_getElem?.mp h with ⟨i, hi, hget⟩
  change 2 + i ≤ Q.walk.support.length at hi
  have ht : Q.walk.support[i]? = some Q.target := by
    simpa using hget 0 (by simp)
  have hlast :
      Q.walk.support[Q.walk.length]? = some Q.target := by
    rw [List.getElem?_eq_getElem]
    · simp
    · rw [_root_.SimpleGraph.Walk.length_support]
      omega
  have hiLen : i < Q.walk.support.length := by omega
  rw [List.getElem?_eq_getElem hiLen] at ht
  rw [List.getElem?_eq_getElem
    (show Q.walk.length < Q.walk.support.length by
      rw [_root_.SimpleGraph.Walk.length_support]
      omega)] at hlast
  have hdup :
      Q.walk.support[i] = Q.walk.support[Q.walk.length] := by
    exact Option.some.inj (ht.trans hlast.symm)
  have := Q.isPath.support_nodup.getElem_inj_iff.mp hdup
  rw [_root_.SimpleGraph.Walk.length_support] at hi
  omega

theorem exists_forwardStep_of_mem_not_target
    (Q : GraphPath G) {u : V}
    (hu : u ∈ Q.vertexSet) (hut : u ≠ Q.target) :
    ∃ v : V, Q.ForwardStep u v := by
  classical
  have huSupport : u ∈ Q.walk.support := by
    simpa [GraphPath.vertexSet] using hu
  let i := Q.walk.support.idxOf u
  have hiLen : i < Q.walk.support.length :=
    List.idxOf_lt_length_iff.mpr huSupport
  have hiNotLast : i + 1 < Q.walk.support.length := by
    by_contra hnot
    have hiEq : i = Q.walk.length := by
      rw [_root_.SimpleGraph.Walk.length_support] at hiLen hnot
      omega
    have hidx :
        Q.walk.support[i] = u := by
      simpa [i] using List.getElem_idxOf hiLen
    have htgt :
        Q.walk.support[Q.walk.length] = Q.target := by simp
    have hidxOpt : Q.walk.support[i]? = some u := by
      rw [List.getElem?_eq_getElem hiLen]
      exact congrArg some hidx
    have htgtOpt :
        Q.walk.support[Q.walk.length]? = some Q.target := by
      rw [List.getElem?_eq_getElem]
      · exact congrArg some htgt
      · rw [_root_.SimpleGraph.Walk.length_support]
        omega
    have hidxOpt' :
        Q.walk.support[Q.walk.length]? = some u := by
      simpa [hiEq] using hidxOpt
    apply hut
    exact Option.some.inj (hidxOpt'.symm.trans htgtOpt)
  let v := Q.walk.support[i + 1]
  refine ⟨v, List.infix_iff_getElem?.mpr ⟨i, ?_, ?_⟩⟩
  · change 2 + i ≤ Q.walk.support.length
    omega
  intro j hj
  simp at hj
  interval_cases j
  · have hidx :
        Q.walk.support[i] = u := by
      simpa [i] using List.getElem_idxOf hiLen
    have hidxOpt : Q.walk.support[i]? = some u := by
      rw [List.getElem?_eq_getElem hiLen]
      exact congrArg some hidx
    simpa using hidxOpt
  · have hnext :
        Q.walk.support[i + 1]? = some v := by
      rw [List.getElem?_eq_getElem hiNotLast]
    simpa [Nat.add_comm] using hnext

theorem exists_backwardStep_of_mem_not_source
    (Q : GraphPath G) {u : V}
    (hu : u ∈ Q.vertexSet) (hus : u ≠ Q.source) :
    ∃ v : V, Q.ForwardStep v u := by
  rcases
      Q.reverse.exists_forwardStep_of_mem_not_target
        (by simpa using hu) (by simpa using hus) with
    ⟨v, hv⟩
  refine ⟨v, ?_⟩
  rcases hv with ⟨before, after, hsupport⟩
  have hrev := congrArg List.reverse hsupport
  refine ⟨after.reverse, before.reverse, ?_⟩
  simpa [List.reverse_append, GraphPath.reverse,
    _root_.SimpleGraph.Walk.support_reverse] using hrev

end GraphPath

namespace TreewidthSparsifier
namespace PathRuns

@[simp] theorem runPath_source
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runPath Q X i).source =
      (runAt Q X i).head (runAt_ne_nil Q X i) := by
  classical
  simp [runPath]

@[simp] theorem runPath_target
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) :
    (runPath Q X i).target =
      (runAt Q X i).getLast (runAt_ne_nil Q X i) := by
  classical
  simp [runPath]

/-- The last vertex of one run is immediately followed by the first vertex
of the next run in the original oriented path. -/
theorem forwardStep_runPath_target_next_source
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length)
    (hi : i.1 + 1 < (groups Q X).length) :
    Q.ForwardStep
      (runPath Q X i).target
      (runPath Q X ⟨i.1 + 1, hi⟩).source := by
  classical
  let L := groups Q X
  let current := L[i.1]
  let next := L[i.1 + 1]
  have hcurNe : current ≠ [] := by
    exact List.ne_nil_of_mem_splitBy
      (by
        change L[i.1] ∈ L
        exact List.getElem_mem i.2)
  have hnextNe : next ≠ [] := by
    exact List.ne_nil_of_mem_splitBy
      (by
        change L[i.1 + 1] ∈ L
        exact List.getElem_mem hi)
  have htake₀ :
      L.take i.1 ++ [L[i.1]] = L.take (i.1 + 1) :=
    List.take_concat_get' L i.1 i.2
  have htake₁ :
      L.take (i.1 + 1) ++ [L[i.1 + 1]] =
        L.take (i.1 + 2) :=
    List.take_concat_get' L (i.1 + 1) (by omega)
  have hdecomp :
      L =
        L.take i.1 ++
          [current, next] ++ L.drop (i.1 + 2) := by
    calc
      L = L.take (i.1 + 2) ++ L.drop (i.1 + 2) := by
        exact (List.take_append_drop (i.1 + 2) L).symm
      _ =
          L.take i.1 ++
            [current, next] ++ L.drop (i.1 + 2) := by
        rw [← htake₁, ← htake₀]
        simp [current, next, List.append_assoc]
  change
    [(runAt Q X i).getLast (runAt_ne_nil Q X i),
      (runAt Q X ⟨i.1 + 1, hi⟩).head
        (runAt_ne_nil Q X ⟨i.1 + 1, hi⟩)] <:+:
      Q.walk.support
  refine
    ⟨(L.take i.1).flatten ++ current.dropLast,
      next.tail ++ (L.drop (i.1 + 2)).flatten, ?_⟩
  have hcur :
      current.dropLast ++ [current.getLast hcurNe] = current :=
    List.dropLast_append_getLast hcurNe
  have hnext :
      next.head hnextNe :: next.tail = next := by
    exact List.cons_head?_tail (List.head_mem_head? hnextNe)
  have hsupport :
      Q.walk.support =
        (L.take i.1).flatten ++ current ++ next ++
          (L.drop (i.1 + 2)).flatten := by
    have hflat := congrArg List.flatten hdecomp
    have hflat' :
        L.flatten =
          (L.take i.1).flatten ++ current ++ next ++
            (L.drop (i.1 + 2)).flatten := by
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc] using hflat
    exact (flatten_groups Q X).symm.trans hflat'
  have htarget :
      (runAt Q X i).getLast (runAt_ne_nil Q X i) =
        current.getLast hcurNe := by
    rfl
  have hsource :
      (runAt Q X ⟨i.1 + 1, hi⟩).head
          (runAt_ne_nil Q X ⟨i.1 + 1, hi⟩) =
        next.head hnextNe := by
    rfl
  rw [htarget, hsource, hsupport]
  conv_rhs =>
    rw [← hcur, ← hnext]
  simp only [List.singleton_append, List.cons_append, List.nil_append,
    List.append_assoc]

/-- An inside run ends either at the original target or immediately before
an edge leaving the selected side. -/
theorem runPath_target_boundary
    (Q : GraphPath G) (X : Finset V)
    (i : InsideIndex Q X) :
    (runPath Q X i.1).target = Q.target ∨
      ∃ w : V,
        Q.ForwardStep (runPath Q X i.1).target w ∧ w ∉ X := by
  classical
  by_cases hnext : i.1.1 + 1 < (groups Q X).length
  · let j : Fin (groups Q X).length := ⟨i.1.1 + 1, hnext⟩
    have hstep :
        Q.ForwardStep
          (runPath Q X i.1).target (runPath Q X j).source :=
      forwardStep_runPath_target_next_source Q X i.1 hnext
    have hchange :=
      (List.isChain_iff_getElem.mp (groups_isChain_changesSide Q X))
        i.1.1 hnext
    have hcurIn :
        (runPath Q X i.1).target ∈ X :=
      inside_runPath_vertexSet_subset Q X i
        (GraphPath.target_mem_vertexSet _)
    have hnextOut : (runPath Q X j).source ∉ X := by
      intro hnextIn
      exact
        hchange (runAt_ne_nil Q X i.1) (runAt_ne_nil Q X j)
          ⟨fun _ => hnextIn, fun _ => hcurIn⟩
    exact Or.inr ⟨(runPath Q X j).source, hstep, hnextOut⟩
  · left
    have hlenPos : 0 < (groups Q X).length := by omega
    have hiLast :
        i.1.1 = (groups Q X).length - 1 := by omega
    have hgroupsNe : groups Q X ≠ [] := List.ne_nil_of_length_pos hlenPos
    have hsupportNe : Q.walk.support ≠ [] := Q.walk.support_ne_nil
    calc
      (runPath Q X i.1).target =
          ((groups Q X).getLast hgroupsNe).getLast
            (List.ne_nil_of_mem_splitBy (List.getLast_mem hgroupsNe)) := by
        simp [runPath, runAt, List.getLast_eq_getElem, hiLast]
      _ = Q.walk.support.getLast hsupportNe :=
        List.getLast_getLast_splitBy (sameSide X) hsupportNe
      _ = Q.target := by simp

/-- An inside run starts either at the original source or immediately after
an edge entering the selected side. -/
theorem runPath_source_boundary
    (Q : GraphPath G) (X : Finset V)
    (i : InsideIndex Q X) :
    (runPath Q X i.1).source = Q.source ∨
      ∃ u : V,
        Q.ForwardStep u (runPath Q X i.1).source ∧ u ∉ X := by
  classical
  by_cases hzero : i.1.1 = 0
  · left
    have hgroupsNe : groups Q X ≠ [] := by
      exact List.ne_nil_of_length_pos (by omega)
    have hsupportNe : Q.walk.support ≠ [] := Q.walk.support_ne_nil
    calc
      (runPath Q X i.1).source =
          ((groups Q X).head hgroupsNe).head
            (List.ne_nil_of_mem_splitBy (List.head_mem hgroupsNe)) := by
        simp [runPath, runAt, List.head_eq_getElem_zero, hzero]
      _ = Q.walk.support.head hsupportNe :=
        List.head_head_splitBy (sameSide X) hsupportNe
      _ = Q.source := by simp
  · right
    have hipos : 0 < i.1.1 := Nat.pos_of_ne_zero hzero
    let j : Fin (groups Q X).length :=
      ⟨i.1.1 - 1, by omega⟩
    have hsucc : i.1.1 - 1 + 1 = i.1.1 := by omega
    let k : Fin (groups Q X).length :=
      ⟨j.1 + 1, by
        dsimp [j]
        omega⟩
    have hki : k = i.1 := by
      apply Fin.ext
      simpa [k, j] using hsucc
    have hstep :
        Q.ForwardStep
          (runPath Q X j).target (runPath Q X i.1).source := by
      simpa [k, hki] using
        forwardStep_runPath_target_next_source Q X j (by
          dsimp [j]
          omega)
    have hchange :=
      (List.isChain_iff_getElem.mp (groups_isChain_changesSide Q X))
        (i.1.1 - 1) (by omega)
    have hchange' :
        ∀ (ha : runAt Q X j ≠ []) (hb : runAt Q X i.1 ≠ []),
          ¬(((runAt Q X j).getLast ha ∈ X) ↔
            (runAt Q X i.1).head hb ∈ X) := by
      simpa [runAt, j, hsucc] using hchange
    have hcurIn :
        (runPath Q X i.1).source ∈ X :=
      inside_runPath_vertexSet_subset Q X i
        (GraphPath.source_mem_vertexSet _)
    have hprevOut : (runPath Q X j).target ∉ X := by
      intro hprevIn
      exact
        hchange' (runAt_ne_nil Q X j) (runAt_ne_nil Q X i.1)
          ⟨fun _ => hcurIn, fun _ => hprevIn⟩
    exact ⟨(runPath Q X j).target, hstep, hprevOut⟩

/-- Immediate successor steps of a run are immediate successor steps of the
original path. -/
theorem runPath_forwardStep
    (Q : GraphPath G) (X : Finset V)
    (i : Fin (groups Q X).length) {u v : V}
    (h : (runPath Q X i).ForwardStep u v) :
    Q.ForwardStep u v := by
  change [u, v] <:+: (runPath Q X i).walk.support at h
  rw [runPath_support] at h
  exact h.trans (runAt_isInfix Q X i)

/-- If the original path leaves `X` immediately after a vertex of a selected
run, that vertex is the target of the run. -/
theorem runPath_target_eq_of_forwardStep_leaves
    (Q : GraphPath G) (X : Finset V)
    (i : InsideIndex Q X) {u v : V}
    (hu : u ∈ (runPath Q X i.1).vertexSet)
    (huv : Q.ForwardStep u v) (hv : v ∉ X) :
    (runPath Q X i.1).target = u := by
  by_contra hne
  rcases
      (runPath Q X i.1).exists_forwardStep_of_mem_not_target
        hu (Ne.symm hne) with
    ⟨w, huw⟩
  have huwQ : Q.ForwardStep u w :=
    runPath_forwardStep Q X i.1 huw
  have hwv : w = v :=
    Q.forwardStep_rightUnique huwQ huv
  have hwX :
      w ∈ X :=
    inside_runPath_vertexSet_subset Q X i
      (by
        simpa [GraphPath.vertexSet] using
          huw.mem (by simp : w ∈ [u, w]))
  exact hv (hwv ▸ hwX)

/-- Dually, an edge entering `X` lands at the source of its selected run. -/
theorem runPath_source_eq_of_forwardStep_enters
    (Q : GraphPath G) (X : Finset V)
    (i : InsideIndex Q X) {u v : V}
    (hv : v ∈ (runPath Q X i.1).vertexSet)
    (huv : Q.ForwardStep u v) (hu : u ∉ X) :
    (runPath Q X i.1).source = v := by
  by_contra hne
  rcases
      (runPath Q X i.1).exists_backwardStep_of_mem_not_source
        hv (Ne.symm hne) with
    ⟨w, hwv⟩
  have hwvQ : Q.ForwardStep w v :=
    runPath_forwardStep Q X i.1 hwv
  have hwu : w = u :=
    Q.forwardStep_leftUnique hwvQ huv
  have hwX :
      w ∈ X :=
    inside_runPath_vertexSet_subset Q X i
      (by
        simpa [GraphPath.vertexSet] using
          hwv.mem (by simp : w ∈ [w, v]))
  exact hu (hwu ▸ hwX)

/-- The canonical orientation of an inside run does not reverse it: both
temporary endpoint sets are `univ`. -/
@[simp] theorem packingInside_orient_path
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V)
    (q : PackingInsideIndex P X) :
    ((packingInside P X).orient.path q) =
      runPath (P.path q.1) X q.2.1 := by
  classical
  simp [packingInside, PathPacking.orient, GraphPath.orient]

theorem runPath_source_mem_packingInside_sourceSet
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V)
    (q : PackingInsideIndex P X) :
    (runPath (P.path q.1) X q.2.1).source ∈
      (packingInside P X).sourceSet := by
  classical
  rw [PathPacking.sourceSet]
  exact Finset.mem_image.mpr
    ⟨q, Finset.mem_univ _, by simp⟩

theorem runPath_target_mem_packingInside_targetSet
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V)
    (q : PackingInsideIndex P X) :
    (runPath (P.path q.1) X q.2.1).target ∈
      (packingInside P X).targetSet := by
  classical
  rw [PathPacking.targetSet]
  exact Finset.mem_image.mpr
    ⟨q, Finset.mem_univ _, by simp⟩

theorem exists_run_source_eq_of_mem_packingInside_sourceSet
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V)
    {v : V} (hv : v ∈ (packingInside P X).sourceSet) :
    ∃ q : PackingInsideIndex P X,
      (runPath (P.path q.1) X q.2.1).source = v := by
  classical
  rw [PathPacking.sourceSet] at hv
  rcases Finset.mem_image.mp hv with ⟨q, _hq, hqv⟩
  exact ⟨q, by simpa using hqv⟩

theorem exists_run_target_eq_of_mem_packingInside_targetSet
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V)
    {v : V} (hv : v ∈ (packingInside P X).targetSet) :
    ∃ q : PackingInsideIndex P X,
      (runPath (P.path q.1) X q.2.1).target = v := by
  classical
  rw [PathPacking.targetSet] at hv
  rcases Finset.mem_image.mp hv with ⟨q, _hq, hqv⟩
  exact ⟨q, by simpa using hqv⟩

theorem packingInside_sourceSet_subset
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    (packingInside P X).sourceSet ⊆ X := by
  intro v hv
  rcases
      exists_run_source_eq_of_mem_packingInside_sourceSet P X hv with
    ⟨q, hq⟩
  rw [← hq]
  exact
    inside_runPath_vertexSet_subset (P.path q.1) X q.2
      (GraphPath.source_mem_vertexSet _)

theorem packingInside_targetSet_subset
    {S T : Finset V} (P : PathPacking G S T) (X : Finset V) :
    (packingInside P X).targetSet ⊆ X := by
  intro v hv
  rcases
      exists_run_target_eq_of_mem_packingInside_targetSet P X hv with
    ⟨q, hq⟩
  rw [← hq]
  exact
    inside_runPath_vertexSet_subset (P.path q.1) X q.2
      (GraphPath.target_mem_vertexSet _)

end PathRuns

namespace PerfectPathPacking

variable {S T : Finset V}

/-- An immediate oriented step on one of the paths of a perfect packing. -/
def ForwardStep (P : PerfectPathPacking G S T) (u v : V) : Prop :=
  ∃ i : P.Index, (P.path i).ForwardStep u v

theorem source_used (P : PerfectPathPacking G S T)
    {s : V} (hs : s ∈ S) :
    ∃ i : P.Index, s ∈ (P.path i).vertexSet := by
  let i := P.indexOfSource ⟨s, hs⟩
  refine ⟨i, ?_⟩
  have hsource :
      (P.path i).source = s := by
    exact congrArg Subtype.val (P.source_indexOfSource ⟨s, hs⟩)
  simpa [hsource] using GraphPath.source_mem_vertexSet (P.path i)

theorem target_used (P : PerfectPathPacking G S T)
    {t : V} (ht : t ∈ T) :
    ∃ i : P.Index, t ∈ (P.path i).vertexSet := by
  let i := P.indexOfTarget ⟨t, ht⟩
  refine ⟨i, ?_⟩
  have htarget :
      (P.path i).target = t := by
    exact congrArg Subtype.val (P.target_indexOfTarget ⟨t, ht⟩)
  simpa [htarget] using GraphPath.target_mem_vertexSet (P.path i)

theorem forwardStep_adj (P : PerfectPathPacking G S T)
    {u v : V} (h : ForwardStep P u v) :
    G.Adj u v := by
  rcases h with ⟨i, hi⟩
  exact (P.path i).forwardStep_adj hi

theorem forwardStep_endpoints_used
    (P : PerfectPathPacking G S T)
    {u v : V} (h : ForwardStep P u v) :
    (∃ i : P.Index, u ∈ (P.path i).vertexSet) ∧
      ∃ i : P.Index, v ∈ (P.path i).vertexSet := by
  rcases h with ⟨i, hi⟩
  exact
    ⟨⟨i, ((P.path i).forwardStep_endpoints_mem_vertexSet hi).1⟩,
      ⟨i, ((P.path i).forwardStep_endpoints_mem_vertexSet hi).2⟩⟩

theorem forwardStep_rightUnique (P : PerfectPathPacking G S T) :
    Relator.RightUnique (ForwardStep P) := by
  intro u v w huv huw
  rcases huv with ⟨i, hi⟩
  rcases huw with ⟨j, hj⟩
  have hui : u ∈ (P.path i).vertexSet :=
    ((P.path i).forwardStep_endpoints_mem_vertexSet hi).1
  have huj : u ∈ (P.path j).vertexSet :=
    ((P.path j).forwardStep_endpoints_mem_vertexSet hj).1
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.node_disjoint hne) hui huj
  subst j
  exact (P.path i).forwardStep_rightUnique hi hj

theorem forwardStep_leftUnique (P : PerfectPathPacking G S T) :
    Relator.LeftUnique (ForwardStep P) := by
  intro u v w huw hvw
  rcases huw with ⟨i, hi⟩
  rcases hvw with ⟨j, hj⟩
  have hwi : w ∈ (P.path i).vertexSet :=
    ((P.path i).forwardStep_endpoints_mem_vertexSet hi).2
  have hwj : w ∈ (P.path j).vertexSet :=
    ((P.path j).forwardStep_endpoints_mem_vertexSet hj).2
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (P.node_disjoint hne) hwi hwj
  subst j
  exact (P.path i).forwardStep_leftUnique hi hj

theorem exists_forwardStep_of_used_of_not_mem_target
    (P : PerfectPathPacking G S T) {v : V}
    (hv : ∃ i : P.Index, v ∈ (P.path i).vertexSet)
    (hvT : v ∉ T) :
    ∃ w : V, ForwardStep P v w := by
  rcases hv with ⟨i, hvi⟩
  have hvne : v ≠ (P.path i).target := by
    intro h
    exact hvT (h ▸ P.target_mem i)
  rcases (P.path i).exists_forwardStep_of_mem_not_target hvi hvne with
    ⟨w, hvw⟩
  exact ⟨w, i, hvw⟩

theorem exists_backwardStep_of_used_of_not_mem_source
    (P : PerfectPathPacking G S T) {v : V}
    (hv : ∃ i : P.Index, v ∈ (P.path i).vertexSet)
    (hvS : v ∉ S) :
    ∃ u : V, ForwardStep P u v := by
  rcases hv with ⟨i, hvi⟩
  have hvne : v ≠ (P.path i).source := by
    intro h
    exact hvS (h ▸ P.source_mem i)
  rcases (P.path i).exists_backwardStep_of_mem_not_source hvi hvne with
    ⟨u, huv⟩
  exact ⟨u, i, huv⟩

theorem source_no_predecessor
    (P : PerfectPathPacking G S T)
    {s : V} (hs : s ∈ S) (v : V) :
    ¬ ForwardStep P v s := by
  intro h
  rcases h with ⟨i, hi⟩
  have hsPath : s ∈ (P.path i).vertexSet :=
    ((P.path i).forwardStep_endpoints_mem_vertexSet hi).2
  have hsource : s = (P.path i).source :=
    P.eq_source_of_mem_left_of_mem_path_vertexSet i hs hsPath
  exact (P.path i).forwardStep_source_no_predecessor v
    (by simpa [hsource] using hi)

theorem target_no_successor
    (P : PerfectPathPacking G S T)
    {t : V} (ht : t ∈ T) (v : V) :
    ¬ ForwardStep P t v := by
  intro h
  rcases h with ⟨i, hi⟩
  have htPath : t ∈ (P.path i).vertexSet :=
    ((P.path i).forwardStep_endpoints_mem_vertexSet hi).1
  have htarget : t = (P.path i).target :=
    P.eq_target_of_mem_right_of_mem_path_vertexSet i ht htPath
  exact (P.path i).forwardStep_target_no_successor v
    (by simpa [htarget] using hi)

/-- A source terminal lying in the selected side is the source of one of the
maximal inside runs. -/
theorem source_mem_insideSourceSet_of_mem
    (P : PerfectPathPacking G S T) (X : Finset V)
    {s : V} (hs : s ∈ S) (hsX : s ∈ X) :
    s ∈ (PathRuns.packingInside P.toPathPacking X).sourceSet := by
  classical
  let r := P.indexOfSource ⟨s, hs⟩
  have hrSource : (P.path r).source = s := by
    exact congrArg Subtype.val (P.source_indexOfSource ⟨s, hs⟩)
  have hsPath : s ∈ (P.path r).vertexSet := by
    simpa [hrSource] using GraphPath.source_mem_vertexSet (P.path r)
  rcases PathRuns.exists_insideIndex_of_mem (P.path r) X hsPath hsX with
    ⟨q, hsq⟩
  let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
    ⟨r, q⟩
  have hrunSource :
      (PathRuns.runPath (P.path r) X q.1).source = s := by
    by_contra hne
    rcases
        (PathRuns.runPath (P.path r) X q.1)
          |>.exists_backwardStep_of_mem_not_source
            hsq (Ne.symm hne) with
      ⟨u, hu⟩
    have huOriginal :
        (P.path r).ForwardStep u s := by
      exact PathRuns.runPath_forwardStep (P.path r) X q.1 hu
    exact
      (P.path r).forwardStep_source_no_predecessor u
        (by simpa [hrSource] using huOriginal)
  exact hrunSource ▸
    PathRuns.runPath_source_mem_packingInside_sourceSet
      P.toPathPacking X packed

/-- A regional source is either an original source terminal or is entered by
an original crossing step. -/
theorem insideSource_boundary
    (P : PerfectPathPacking G S T) (X : Finset V)
    {v : V}
    (hv : v ∈ (PathRuns.packingInside P.toPathPacking X).sourceSet) :
    v ∈ S ∨
      ∃ u : V, ForwardStep P u v ∧ u ∉ X := by
  classical
  rcases
      PathRuns.exists_run_source_eq_of_mem_packingInside_sourceSet
        P.toPathPacking X hv with
    ⟨q, hq⟩
  rcases PathRuns.runPath_source_boundary (P.path q.1) X q.2 with
    hsource | ⟨u, hu, huX⟩
  · left
    rw [← hq, hsource]
    exact P.source_mem q.1
  · right
    refine ⟨u, ⟨q.1, ?_⟩, huX⟩
    rw [hq] at hu
    exact hu

/-- A regional target is either an original target terminal or is followed
by an original crossing step. -/
theorem insideTarget_boundary
    (P : PerfectPathPacking G S T) (X : Finset V)
    {v : V}
    (hv : v ∈ (PathRuns.packingInside P.toPathPacking X).targetSet) :
    v ∈ T ∨
      ∃ w : V, ForwardStep P v w ∧ w ∉ X := by
  classical
  rcases
      PathRuns.exists_run_target_eq_of_mem_packingInside_targetSet
        P.toPathPacking X hv with
    ⟨q, hq⟩
  rcases PathRuns.runPath_target_boundary (P.path q.1) X q.2 with
    htarget | ⟨w, hw, hwX⟩
  · left
    rw [← hq, htarget]
    exact P.target_mem q.1
  · right
    refine ⟨w, ⟨q.1, ?_⟩, hwX⟩
    rw [hq] at hw
    exact hw

end PerfectPathPacking

namespace PackingSplice

variable {H : _root_.SimpleGraph V} {S T : Finset V}

/-- A path packing stays in a vertex set as soon as its sources lie there
and every edge of the ambient graph has both endpoints there.  This small
lemma is useful after rerouting in a graph made only from regional path
pieces. -/
theorem staysIn_of_source_subset_of_adj_endpoints
    {K : _root_.SimpleGraph V} {A B X : Finset V}
    (P : PerfectPathPacking K A B)
    (hA : A ⊆ X)
    (hadj : ∀ ⦃u v : V⦄, K.Adj u v → u ∈ X ∧ v ∈ X) :
    P.toPathPacking.StaysIn X := by
  intro i v hv
  by_cases hsource : v = (P.path i).source
  · subst v
    exact hA (P.source_mem i)
  · rcases
        (P.path i).exists_backwardStep_of_mem_not_source hv hsource with
      ⟨u, huv⟩
    exact (hadj ((P.path i).forwardStep_adj huv)).2

/-- Every edge of the union of two packings which stay in `X` has both
endpoints in `X`. -/
theorem twoPackingUnionGraph_adj_endpoints_mem
    {K : _root_.SimpleGraph V}
    {A₁ B₁ A₂ B₂ X : Finset V}
    (P : PerfectPathPacking K A₁ B₁)
    (Q : PerfectPathPacking K A₂ B₂)
    (hP : P.toPathPacking.StaysIn X)
    (hQ : Q.toPathPacking.StaysIn X)
    {u v : V}
    (huv : (twoPackingUnionGraph P Q).Adj u v) :
    u ∈ X ∧ v ∈ X := by
  rcases huv with huv | huv
  · rcases
        (P.toPathPacking.spanningGraph_adj_iff_exists_path_edge).mp huv with
      ⟨⟨i, he⟩, _⟩
    exact
      ⟨hP i
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (P.path i) he).1,
        hP i
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (P.path i) he).2⟩
  · rcases
        (Q.toPathPacking.spanningGraph_adj_iff_exists_path_edge).mp huv with
      ⟨⟨i, he⟩, _⟩
    exact
      ⟨hQ i
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (Q.path i) he).1,
        hQ i
          (GraphPath.endpoints_mem_vertexSet_of_edgeSet
            (Q.path i) he).2⟩

noncomputable abbrev InsideSources (P : PerfectPathPacking G S T)
    (X : Finset V) : Finset V :=
  (PathRuns.packingInside P.toPathPacking X).sourceSet

noncomputable abbrev InsideTargets (P : PerfectPathPacking G S T)
    (X : Finset V) : Finset V :=
  (PathRuns.packingInside P.toPathPacking X).targetSet

/-- Retain every original step not internal to `X`, and replace the internal
runs by the steps of `R`. -/
def Step (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (u v : V) : Prop :=
  PerfectPathPacking.ForwardStep R u v ∨
    (PerfectPathPacking.ForwardStep P u v ∧
      ¬(u ∈ X ∧ v ∈ X))

def Active (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (v : V) : Prop :=
  (∃ i : P.Index, v ∈ (P.path i).vertexSet ∧ v ∉ X) ∨
    ∃ j : R.Index, v ∈ (R.path j).vertexSet

theorem step_adj
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hkeep :
      ∀ ⦃u v : V⦄,
        PerfectPathPacking.ForwardStep P u v →
          ¬(u ∈ X ∧ v ∈ X) → H.Adj u v)
    {u v : V} (h : Step P X R u v) :
    H.Adj u v := by
  rcases h with hR | hP
  · exact PerfectPathPacking.forwardStep_adj R hR
  · exact hkeep hP.1 hP.2

theorem step_rightUnique
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hRstay : R.toPathPacking.StaysIn X) :
    Relator.RightUnique (Step P X R) := by
  intro u v w huv huw
  rcases huv with hRuv | hPuv
  · rcases huw with hRuw | hPuw
    · exact PerfectPathPacking.forwardStep_rightUnique R hRuv hRuw
    · rcases hRuv with ⟨j, hjuv⟩
      rcases hPuw.1 with ⟨i, hiuw⟩
      have huX : u ∈ X :=
        hRstay j ((R.path j).forwardStep_endpoints_mem_vertexSet hjuv).1
      have hwX : w ∉ X := by
        intro hwX
        exact hPuw.2 ⟨huX, hwX⟩
      have huP : u ∈ (P.path i).vertexSet :=
        ((P.path i).forwardStep_endpoints_mem_vertexSet hiuw).1
      rcases PathRuns.exists_insideIndex_of_mem (P.path i) X huP huX with
        ⟨q, huq⟩
      have htarget :
          (PathRuns.runPath (P.path i) X q.1).target = u :=
        PathRuns.runPath_target_eq_of_forwardStep_leaves
          (P.path i) X q huq hiuw hwX
      let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
        ⟨i, q⟩
      have huTarget : u ∈ InsideTargets P X := by
        rw [← htarget]
        exact
          PathRuns.runPath_target_mem_packingInside_targetSet
            P.toPathPacking X packed
      exact False.elim
        (PerfectPathPacking.target_no_successor R huTarget v
          ⟨j, hjuv⟩)
  · rcases huw with hRuw | hPuw
    · rcases hRuw with ⟨j, hjuw⟩
      rcases hPuv.1 with ⟨i, hiuv⟩
      have huX : u ∈ X :=
        hRstay j ((R.path j).forwardStep_endpoints_mem_vertexSet hjuw).1
      have hvX : v ∉ X := by
        intro hvX
        exact hPuv.2 ⟨huX, hvX⟩
      have huP : u ∈ (P.path i).vertexSet :=
        ((P.path i).forwardStep_endpoints_mem_vertexSet hiuv).1
      rcases PathRuns.exists_insideIndex_of_mem (P.path i) X huP huX with
        ⟨q, huq⟩
      have htarget :
          (PathRuns.runPath (P.path i) X q.1).target = u :=
        PathRuns.runPath_target_eq_of_forwardStep_leaves
          (P.path i) X q huq hiuv hvX
      let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
        ⟨i, q⟩
      have huTarget : u ∈ InsideTargets P X := by
        rw [← htarget]
        exact
          PathRuns.runPath_target_mem_packingInside_targetSet
            P.toPathPacking X packed
      exact False.elim
        (PerfectPathPacking.target_no_successor R huTarget w
          ⟨j, hjuw⟩)
    · exact
        PerfectPathPacking.forwardStep_rightUnique P hPuv.1 hPuw.1

theorem step_leftUnique
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hRstay : R.toPathPacking.StaysIn X) :
    Relator.LeftUnique (Step P X R) := by
  intro u v w huw hvw
  rcases huw with hRuw | hPuw
  · rcases hvw with hRvw | hPvw
    · exact PerfectPathPacking.forwardStep_leftUnique R hRuw hRvw
    · rcases hRuw with ⟨j, hjuw⟩
      rcases hPvw.1 with ⟨i, hivw⟩
      have hwX : w ∈ X :=
        hRstay j ((R.path j).forwardStep_endpoints_mem_vertexSet hjuw).2
      have hvX : v ∉ X := by
        intro hvX
        exact hPvw.2 ⟨hvX, hwX⟩
      have hwP : w ∈ (P.path i).vertexSet :=
        ((P.path i).forwardStep_endpoints_mem_vertexSet hivw).2
      rcases PathRuns.exists_insideIndex_of_mem (P.path i) X hwP hwX with
        ⟨q, hwq⟩
      have hsource :
          (PathRuns.runPath (P.path i) X q.1).source = w :=
        PathRuns.runPath_source_eq_of_forwardStep_enters
          (P.path i) X q hwq hivw hvX
      let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
        ⟨i, q⟩
      have hwSource : w ∈ InsideSources P X := by
        rw [← hsource]
        exact
          PathRuns.runPath_source_mem_packingInside_sourceSet
            P.toPathPacking X packed
      exact False.elim
        (PerfectPathPacking.source_no_predecessor R hwSource u
          ⟨j, hjuw⟩)
  · rcases hvw with hRvw | hPvw
    · rcases hRvw with ⟨j, hjvw⟩
      rcases hPuw.1 with ⟨i, hiuw⟩
      have hwX : w ∈ X :=
        hRstay j ((R.path j).forwardStep_endpoints_mem_vertexSet hjvw).2
      have huX : u ∉ X := by
        intro huX
        exact hPuw.2 ⟨huX, hwX⟩
      have hwP : w ∈ (P.path i).vertexSet :=
        ((P.path i).forwardStep_endpoints_mem_vertexSet hiuw).2
      rcases PathRuns.exists_insideIndex_of_mem (P.path i) X hwP hwX with
        ⟨q, hwq⟩
      have hsource :
          (PathRuns.runPath (P.path i) X q.1).source = w :=
        PathRuns.runPath_source_eq_of_forwardStep_enters
          (P.path i) X q hwq hiuw huX
      let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
        ⟨i, q⟩
      have hwSource : w ∈ InsideSources P X := by
        rw [← hsource]
        exact
          PathRuns.runPath_source_mem_packingInside_sourceSet
            P.toPathPacking X packed
      exact False.elim
        (PerfectPathPacking.source_no_predecessor R hwSource v
          ⟨j, hjvw⟩)
    · exact
        PerfectPathPacking.forwardStep_leftUnique P hPuw.1 hPvw.1

theorem source_active
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    {s : V} (hs : s ∈ S) :
    Active P X R s := by
  by_cases hsX : s ∈ X
  · right
    exact
      PerfectPathPacking.source_used R
        (PerfectPathPacking.source_mem_insideSourceSet_of_mem P X hs hsX)
  · left
    rcases PerfectPathPacking.source_used P hs with ⟨i, hi⟩
    exact ⟨i, hi, hsX⟩

theorem active_of_step
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hRstay : R.toPathPacking.StaysIn X)
    {u v : V} (_hu : Active P X R u) (huv : Step P X R u v) :
    Active P X R v := by
  rcases huv with hR | hP
  · right
    exact (PerfectPathPacking.forwardStep_endpoints_used R hR).2
  · rcases hP.1 with ⟨i, hi⟩
    have hvP : v ∈ (P.path i).vertexSet :=
      ((P.path i).forwardStep_endpoints_mem_vertexSet hi).2
    by_cases hvX : v ∈ X
    · have huX : u ∉ X := by
        intro huX
        exact hP.2 ⟨huX, hvX⟩
      rcases PathRuns.exists_insideIndex_of_mem (P.path i) X hvP hvX with
        ⟨q, hvq⟩
      have hsource :
          (PathRuns.runPath (P.path i) X q.1).source = v :=
        PathRuns.runPath_source_eq_of_forwardStep_enters
          (P.path i) X q hvq hi huX
      let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
        ⟨i, q⟩
      have hvSource : v ∈ InsideSources P X := by
        rw [← hsource]
        exact
          PathRuns.runPath_source_mem_packingInside_sourceSet
            P.toPathPacking X packed
      right
      exact PerfectPathPacking.source_used R hvSource
    · exact Or.inl ⟨i, hvP, hvX⟩

theorem active_successor_or_target
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    {v : V} (hv : Active P X R v) :
    v ∈ T ∨ ∃ w : V, Step P X R v w := by
  rcases hv with hvP | hvR
  · rcases hvP with ⟨i, hvi, hvX⟩
    by_cases hvT : v ∈ T
    · exact Or.inl hvT
    · rcases
          PerfectPathPacking.exists_forwardStep_of_used_of_not_mem_target
            P ⟨i, hvi⟩ hvT with
        ⟨w, hvw⟩
      exact Or.inr ⟨w, Or.inr ⟨hvw, fun h => hvX h.1⟩⟩
  · by_cases hvB : v ∈ InsideTargets P X
    · rcases PerfectPathPacking.insideTarget_boundary P X hvB with
        hvT | ⟨w, hvw, hwX⟩
      · exact Or.inl hvT
      · exact Or.inr
          ⟨w, Or.inr ⟨hvw, fun h => hwX h.2⟩⟩
    · rcases
          PerfectPathPacking.exists_forwardStep_of_used_of_not_mem_target
            R hvR hvB with
        ⟨w, hvw⟩
      exact Or.inr ⟨w, Or.inl hvw⟩

theorem source_no_predecessor
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hRstay : R.toPathPacking.StaysIn X)
    {s : V} (hs : s ∈ S) (v : V) :
    ¬ Step P X R v s := by
  intro h
  rcases h with hR | hP
  · rcases hR with ⟨j, hj⟩
    have hsX : s ∈ X :=
      hRstay j ((R.path j).forwardStep_endpoints_mem_vertexSet hj).2
    have hsA : s ∈ InsideSources P X :=
      PerfectPathPacking.source_mem_insideSourceSet_of_mem P X hs hsX
    exact PerfectPathPacking.source_no_predecessor R hsA v ⟨j, hj⟩
  · exact PerfectPathPacking.source_no_predecessor P hs v hP.1

theorem active_of_reachable
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hRstay : R.toPathPacking.StaysIn X)
    {s v : V} (hs : s ∈ S)
    (h : Relation.ReflTransGen (Step P X R) s v) :
    Active P X R v := by
  induction h with
  | refl => exact source_active P X R hs
  | @tail u v _huv huv ih =>
      exact active_of_step P X R hRstay ih huv

/-- The functional chain system obtained by replacing all inside runs. -/
noncomputable def functionalLinkage
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hST : Disjoint S T)
    (hRstay : R.toPathPacking.StaysIn X)
    (hkeep :
      ∀ ⦃u v : V⦄,
        PerfectPathPacking.ForwardStep P u v →
          ¬(u ∈ X ∧ v ∈ X) → H.Adj u v) :
    FunctionalLinkage H S T where
  step := Step P X R
  step_decidable := Classical.decRel _
  step_adj := by
    intro u v huv
    exact step_adj P X R hkeep huv
  right_unique := step_rightUnique P X R hRstay
  left_unique := step_leftUnique P X R hRstay
  source_active := by
    intro s hs
    rcases active_successor_or_target P X R
        (source_active P X R hs) with hsT | hnext
    · exact False.elim
        (Finset.disjoint_left.mp hST hs hsT)
    · exact hnext
  source_no_predecessor := by
    intro s hs v
    exact source_no_predecessor P X R hRstay hs v
  successor_or_target := by
    intro s v hs hreach
    exact active_successor_or_target P X R
      (active_of_reachable P X R hRstay hs hreach)
  card_eq := P.card_eq_left_card.symm.trans P.card_eq_right_card

/-- Replacing all maximal pieces inside `X` by an arbitrary perfect routing
between the same oriented boundary sets preserves the original perfect
`S`-to-`T` routing. -/
noncomputable def perfectPacking
    (P : PerfectPathPacking G S T) (X : Finset V)
    (R : PerfectPathPacking H (InsideSources P X) (InsideTargets P X))
    (hST : Disjoint S T)
    (hRstay : R.toPathPacking.StaysIn X)
    (hkeep :
      ∀ ⦃u v : V⦄,
        PerfectPathPacking.ForwardStep P u v →
          ¬(u ∈ X ∧ v ∈ X) → H.Adj u v) :
    PerfectPathPacking H S T :=
  (functionalLinkage P X R hST hRstay hkeep).toPerfectPathPacking

/-- Away from the oriented endpoints of the regional runs, every original
packing edge incident with a vertex of `X` is retained by the regional
packing. -/
theorem insidePerfect_spanningGraph_adj_of_original
    (P : PerfectPathPacking G S T) (X : Finset V)
    {v w : V} (hvX : v ∈ X)
    (hvSource : v ∉ InsideSources P X)
    (hvTarget : v ∉ InsideTargets P X)
    (hvw : P.toPathPacking.spanningGraph.Adj v w) :
    (PathRuns.packingInsidePerfect P.toPathPacking X).toPathPacking
        |>.spanningGraph.Adj v w := by
  classical
  rcases
      (P.toPathPacking.spanningGraph_adj_iff_exists_path_edge).mp hvw with
    ⟨⟨i, he⟩, hvwNe⟩
  rcases (P.path i).forwardStep_or_reverse_of_mem_edgeSet he with
    hforward | hbackward
  · have hvP : v ∈ (P.path i).vertexSet :=
      ((P.path i).forwardStep_endpoints_mem_vertexSet hforward).1
    rcases PathRuns.exists_insideIndex_of_mem (P.path i) X hvP hvX with
      ⟨q, hvq⟩
    let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
      ⟨i, q⟩
    have hvNotTarget :
        v ≠ (PathRuns.runPath (P.path i) X q.1).target := by
      intro h
      apply hvTarget
      rw [h]
      exact
        PathRuns.runPath_target_mem_packingInside_targetSet
          P.toPathPacking X packed
    rcases
        (PathRuns.runPath (P.path i) X q.1)
          |>.exists_forwardStep_of_mem_not_target hvq hvNotTarget with
      ⟨z, hvz⟩
    have hvzP :
        (P.path i).ForwardStep v z :=
      PathRuns.runPath_forwardStep (P.path i) X q.1 hvz
    have hzw : z = w :=
      (P.path i).forwardStep_rightUnique hvzP hforward
    subst z
    rw [PathPacking.spanningGraph_adj_iff_exists_path_edge]
    refine ⟨⟨packed, ?_⟩, hvwNe⟩
    simpa [PathRuns.packingInsidePerfect,
      PathPacking.toPerfectUsedTerminals] using
      (PathRuns.runPath (P.path i) X q.1).forwardStep_mem_edgeSet hvz
  · have hvP : v ∈ (P.path i).vertexSet :=
      ((P.path i).forwardStep_endpoints_mem_vertexSet hbackward).2
    rcases PathRuns.exists_insideIndex_of_mem (P.path i) X hvP hvX with
      ⟨q, hvq⟩
    let packed : PathRuns.PackingInsideIndex P.toPathPacking X :=
      ⟨i, q⟩
    have hvNotSource :
        v ≠ (PathRuns.runPath (P.path i) X q.1).source := by
      intro h
      apply hvSource
      rw [h]
      exact
        PathRuns.runPath_source_mem_packingInside_sourceSet
          P.toPathPacking X packed
    rcases
        (PathRuns.runPath (P.path i) X q.1)
          |>.exists_backwardStep_of_mem_not_source hvq hvNotSource with
      ⟨z, hzv⟩
    have hzvP :
        (P.path i).ForwardStep z v :=
      PathRuns.runPath_forwardStep (P.path i) X q.1 hzv
    have hzw : z = w :=
      (P.path i).forwardStep_leftUnique hzvP hbackward
    subst z
    rw [PathPacking.spanningGraph_adj_iff_exists_path_edge]
    refine ⟨⟨packed, ?_⟩, hvwNe⟩
    simpa [PathRuns.packingInsidePerfect,
      PathPacking.toPerfectUsedTerminals, Sym2.eq_swap] using
      (PathRuns.runPath (P.path i) X q.1).forwardStep_mem_edgeSet hzv

end PackingSplice

end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
