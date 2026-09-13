import Lax17Proofs.Source.ChekuriChuzhoySection5HostSkeleton
import Lax17Proofs.Source.ChekuriChuzhoySection5RouterContraction
import Lax17Proofs.Source.ChekuriChuzhoySection5RouterLinking

namespace Lax17Proofs

universe u v w

/-!
# Router-contracted terminal skeletons

Chekuri--Chuzhoy Section 5.4.1 applies Theorem 5.10 after contracting every
router to a terminal.  This file retains the parallel edge names during
cycle erasure and then realizes the resulting simple named paths in the
original host graph.

The edge-name retention is important: choosing an arbitrary parallel edge
after forgetting names would destroy both the endpoint-congestion estimate
and the one-per-group disjointness guarantee.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph


open Finset

/-! ## Simple named subpaths -/

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- The simple graph underlying a finite edge-indexed multigraph. -/
def underlyingGraph (H : FiniteEdgeIndexedGraph W) :
    _root_.SimpleGraph W where
  Adj x y := ∃ e : H.Edge, H.Joins e x y
  symm := by
    intro x y
    rintro ⟨e, he⟩
    exact ⟨e, (H.joins_comm e x y).mp he⟩
  loopless := ⟨by
    intro x
    rintro ⟨e, he⟩
    rcases he with he | he
    · exact H.end_ne e (he.1.trans he.2.symm)
    · exact H.end_ne e (he.2.trans he.1.symm)⟩

/-- The unordered endpoint pair represented by one named edge. -/
def underlyingEdge (H : FiniteEdgeIndexedGraph W) (e : H.Edge) : Sym2 W :=
  s(H.left e, H.right e)

theorem joins_of_underlyingEdge_eq
    (H : FiniteEdgeIndexedGraph W) {e : H.Edge} {x y : W}
    (h : H.underlyingEdge e = s(x, y)) :
    H.Joins e x y := by
  rw [underlyingEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.2, h.1⟩

namespace NamedEdgeWalk

variable {H : FiniteEdgeIndexedGraph W} {x y z : W}

/-- Forget parallel-edge names but retain the vertex sequence. -/
def toUnderlyingWalk {x y : W} :
    H.NamedEdgeWalk x y → (underlyingGraph H).Walk x y
  | .nil _ => .nil
  | .cons e he tail =>
      .cons (show (underlyingGraph H).Adj _ _ from ⟨e, he⟩)
        tail.toUnderlyingWalk

@[simp] theorem toUnderlyingWalk_nil (x : W) :
    (NamedEdgeWalk.nil (H := H) x).toUnderlyingWalk =
      _root_.SimpleGraph.Walk.nil :=
  rfl

@[simp] theorem toUnderlyingWalk_cons
    {a b c : W} (e : H.Edge) (he : H.Joins e a b)
    (tail : H.NamedEdgeWalk b c) :
    (NamedEdgeWalk.cons e he tail).toUnderlyingWalk =
      _root_.SimpleGraph.Walk.cons
        (show (underlyingGraph H).Adj a b from ⟨e, he⟩)
        tail.toUnderlyingWalk :=
  rfl

@[simp] theorem toUnderlyingWalk_support_toFinset
    (P : H.NamedEdgeWalk x y) :
    P.toUnderlyingWalk.support.toFinset = P.vertexSet := by
  induction P with
  | nil => simp
  | cons e he tail ih => simp [ih]

theorem underlyingEdge_eq_of_joins
    {e : H.Edge} {a b : W} (he : H.Joins e a b) :
    H.underlyingEdge e = s(a, b) := by
  rcases he with he | he
  · simp [underlyingEdge, he.1, he.2]
  · simpa [underlyingEdge, he.1, he.2] using
      (Sym2.eq_swap (a := a) (b := b)).symm

theorem toUnderlyingWalk_edges
    (P : H.NamedEdgeWalk x y) :
    P.toUnderlyingWalk.edges = P.edgeList.map H.underlyingEdge := by
  induction P with
  | nil => rfl
  | cons e he tail ih =>
      simp [ih, underlyingEdge_eq_of_joins he]

private theorem exists_namedEdgeWalk_of_supported_walk
    (P : H.NamedEdgeWalk x y)
    {a b : W} (Q : (underlyingGraph H).Walk a b)
    (hsupport :
      ∀ {r s : W}, s(r, s) ∈ Q.edges →
        ∃ e ∈ P.edgeList, H.underlyingEdge e = s(r, s)) :
    ∃ R : H.NamedEdgeWalk a b,
      R.edgeList.toFinset ⊆ P.edgeList.toFinset ∧
        R.toUnderlyingWalk = Q := by
  induction Q with
  | nil =>
      exact ⟨.nil _, by simp, by simp⟩
  | @cons a c b hac tail ih =>
      obtain ⟨e, heP, heEnds⟩ :=
        hsupport (r := a) (s := c) (by simp)
      have heJoins : H.Joins e a c :=
        H.joins_of_underlyingEdge_eq heEnds
      have htailSupport :
          ∀ {r s : W}, s(r, s) ∈ tail.edges →
            ∃ e ∈ P.edgeList, H.underlyingEdge e = s(r, s) := by
        intro r s hrs
        exact hsupport (by simp [hrs])
      obtain ⟨R, hRedges, hRwalk⟩ := ih htailSupport
      refine ⟨.cons e heJoins R, ?_, ?_⟩
      · intro f hf
        simp only [NamedEdgeWalk.edgeList_cons, List.toFinset_cons,
          Finset.mem_insert] at hf
        rcases hf with rfl | hf
        · exact List.mem_toFinset.mpr heP
        · exact hRedges hf
      · simp [hRwalk]

/-- Cycle-erase a named walk while choosing every retained parallel edge from
the original named edge list. -/
theorem exists_simpleNamedSubpath
    (P : H.NamedEdgeWalk x y) :
    ∃ Q : H.NamedEdgeWalk x y,
      Q.edgeList.toFinset ⊆ P.edgeList.toFinset ∧
        Q.vertexSet ⊆ P.vertexSet ∧
          Q.toUnderlyingWalk.IsPath := by
  classical
  let U : (underlyingGraph H).Walk x y := P.toUnderlyingWalk.toPath
  have hUPath : U.IsPath := by
    change
      (↑P.toUnderlyingWalk.toPath :
        (underlyingGraph H).Walk x y).IsPath
    exact _root_.SimpleGraph.Path.isPath P.toUnderlyingWalk.toPath
  have hsupport :
      ∀ {r s : W}, s(r, s) ∈ U.edges →
        ∃ e ∈ P.edgeList, H.underlyingEdge e = s(r, s) := by
    intro r s hrs
    have hrsOriginal : s(r, s) ∈ P.toUnderlyingWalk.edges :=
      _root_.SimpleGraph.Walk.edges_toPath_subset P.toUnderlyingWalk hrs
    rw [P.toUnderlyingWalk_edges] at hrsOriginal
    rcases List.mem_map.mp hrsOriginal with ⟨e, heP, he⟩
    exact ⟨e, heP, he⟩
  obtain ⟨Q, hQedges, hQwalk⟩ :=
    exists_namedEdgeWalk_of_supported_walk P U hsupport
  refine ⟨Q, hQedges, ?_, ?_⟩
  · intro z hz
    have hzU : z ∈ U.support.toFinset := by
      rw [← hQwalk, Q.toUnderlyingWalk_support_toFinset]
      exact hz
    have hzUList : z ∈ U.support := List.mem_toFinset.mp hzU
    have hzOriginal :
        z ∈ P.toUnderlyingWalk.support.toFinset := by
      apply List.mem_toFinset.mpr
      exact
        _root_.SimpleGraph.Walk.support_toPath_subset
          P.toUnderlyingWalk hzUList
    simpa using hzOriginal
  · rw [hQwalk]
    exact hUPath

/-- A fixed simple named subpath, used by the router realization below. -/
noncomputable def simpleNamedSubpath
    (P : H.NamedEdgeWalk x y) : H.NamedEdgeWalk x y :=
  Classical.choose P.exists_simpleNamedSubpath

theorem simpleNamedSubpath_edgeList_subset
    (P : H.NamedEdgeWalk x y) :
    P.simpleNamedSubpath.edgeList.toFinset ⊆ P.edgeList.toFinset :=
  (Classical.choose_spec P.exists_simpleNamedSubpath).1

theorem simpleNamedSubpath_vertexSet_subset
    (P : H.NamedEdgeWalk x y) :
    P.simpleNamedSubpath.vertexSet ⊆ P.vertexSet :=
  (Classical.choose_spec P.exists_simpleNamedSubpath).2.1

theorem simpleNamedSubpath_isPath
    (P : H.NamedEdgeWalk x y) :
    P.simpleNamedSubpath.toUnderlyingWalk.IsPath :=
  (Classical.choose_spec P.exists_simpleNamedSubpath).2.2

end NamedEdgeWalk
end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton

namespace ChekuriChuzhoySection5RouterSkeleton

open ChekuriChuzhoySection5RouterContraction
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {n : Nat} {cluster : Fin n → Finset V}

namespace Vertex

/-- Router-contraction vertices that retain an original host vertex. -/
def IsOld : ChekuriChuzhoySection5RouterContraction.Vertex V n → Prop
  | .router _ => False
  | .old _ => True

theorem exists_old_of_isOld
    {z : ChekuriChuzhoySection5RouterContraction.Vertex V n}
    (hz : IsOld z) :
    ∃ v : V, z = .old v := by
  cases z with
  | router i => exact False.elim hz
  | old v => exact ⟨v, rfl⟩

end Vertex

theorem mem_cluster_of_projection_eq_router
    {v : V} {i : Fin n}
    (h : projection cluster v =
      ChekuriChuzhoySection5RouterContraction.Vertex.router i) :
    v ∈ cluster i := by
  classical
  unfold projection at h
  split_ifs at h with hv
  · have hindex : Classical.choose hv = i := by
      injection h
    simpa [hindex] using Classical.choose_spec hv

section NamedGraph

variable [Fintype G.edgeSet]

noncomputable abbrev ContractedGraph :=
  graph (G := G) (cluster := cluster)

/-- Orient the original host edge represented by a contracted named edge. -/
theorem exists_hostEdge_of_joins
    {a b : ChekuriChuzhoySection5RouterContraction.Vertex V n}
    (e : (ContractedGraph (G := G) (cluster := cluster)).Edge)
    (he : (ContractedGraph (G := G) (cluster := cluster)).Joins e a b) :
    ∃ x y : V,
      G.Adj x y ∧ projection cluster x = a ∧
        projection cluster y = b ∧
          edgeOrigin (G := G) (cluster := cluster) e = s(x, y) := by
  let x :=
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeLeft G e.1
  let y :=
    ChekuriChuzhoySection5TerminalSkeleton.hostEdgeRight G e.1
  have hxy : G.Adj x y := by
    have hmem := edgeOrigin_mem_edgeFinset
      (G := G) (cluster := cluster) e
    have horigin :
        edgeOrigin (G := G) (cluster := cluster) e = s(x, y) := by
      exact
        (ChekuriChuzhoySection5TerminalSkeleton.sym2_mk_hostEdgeEndpoints
          G e.1).symm
    rw [horigin] at hmem
    simpa [_root_.SimpleGraph.mem_edgeFinset] using hmem
  rcases he with he | he
  · exact ⟨x, y, hxy, he.1, he.2,
      (ChekuriChuzhoySection5TerminalSkeleton.sym2_mk_hostEdgeEndpoints
        G e.1).symm⟩
  · exact ⟨y, x, hxy.symm, he.1, he.2, by
      rw [Sym2.eq_swap]
      exact
        (ChekuriChuzhoySection5TerminalSkeleton.sym2_mk_hostEdgeEndpoints
          G e.1).symm⟩

/-- Host edges traversed by a contracted named walk. -/
noncomputable def namedHostEdgeSet
    {a b : ChekuriChuzhoySection5RouterContraction.Vertex V n}
    (P : (ContractedGraph (G := G) (cluster := cluster)).NamedEdgeWalk a b) :
    Finset (Sym2 V) :=
  (P.edgeList.map
    (edgeOrigin (G := G) (cluster := cluster))).toFinset

namespace GraphPath

/-- The one-edge host path associated with a host adjacency. -/
noncomputable def ofAdj {x y : V} (hxy : G.Adj x y) :
    Lax17Proofs.SimpleGraph.GraphPath G :=
  Lax17Proofs.SimpleGraph.GraphPath.ofWalk
    (_root_.SimpleGraph.Walk.cons hxy _root_.SimpleGraph.Walk.nil)

@[simp] theorem ofAdj_source {x y : V} (hxy : G.Adj x y) :
    (ofAdj hxy).source = x :=
  rfl

@[simp] theorem ofAdj_target {x y : V} (hxy : G.Adj x y) :
    (ofAdj hxy).target = y :=
  rfl

theorem ofAdj_vertexSet_subset {x y : V} (hxy : G.Adj x y) :
    (ofAdj hxy).vertexSet ⊆ ({x, y} : Finset V) := by
  intro z hz
  have hz' :=
    Lax17Proofs.SimpleGraph.GraphPath.ofWalk_vertexSet_subset
      (_root_.SimpleGraph.Walk.cons hxy _root_.SimpleGraph.Walk.nil) hz
  simpa [ofAdj] using hz'

theorem ofAdj_edgeSet_subset {x y : V} (hxy : G.Adj x y) :
    (ofAdj hxy).edgeSet ⊆ ({s(x, y)} : Finset (Sym2 V)) := by
  intro e he
  have he' :=
    Lax17Proofs.SimpleGraph.GraphPath.ofWalk_edgeSet_subset
      (_root_.SimpleGraph.Walk.cons hxy _root_.SimpleGraph.Walk.nil) he
  simpa [ofAdj] using he'

end GraphPath

/-- A simple contracted named path with old internal vertices realizes to a
host path.  Its vertices and edges retain exact contraction provenance. -/
theorem exists_hostPath_of_simpleNamedPath
    {a b : ChekuriChuzhoySection5RouterContraction.Vertex V n}
    (P : (ContractedGraph (G := G) (cluster := cluster)).NamedEdgeWalk a b)
    (hne : a ≠ b)
    (hpath : P.toUnderlyingWalk.IsPath)
    (hinterior :
      ∀ z ∈ P.vertexSet, z ≠ a → z ≠ b → Vertex.IsOld z) :
    ∃ Q : Lax17Proofs.SimpleGraph.GraphPath G,
      projection cluster Q.source = a ∧
        projection cluster Q.target = b ∧
          (∀ v ∈ Q.vertexSet, projection cluster v ∈ P.vertexSet) ∧
            Q.edgeSet ⊆ namedHostEdgeSet P ∧
              (∀ v ∈ Q.vertexSet,
                projection cluster v = a → v = Q.source) ∧
                ∀ v ∈ Q.vertexSet,
                  projection cluster v = b → v = Q.target := by
  classical
  induction P with
  | nil =>
      exact False.elim (hne rfl)
  | @cons a c b e he tail ih =>
      obtain ⟨x, y, hxy, hxProjection, hyProjection, hOrigin⟩ :=
        exists_hostEdge_of_joins (cluster := cluster) e he
      let L := GraphPath.ofAdj hxy
      cases tail with
      | nil =>
          refine ⟨L, hxProjection, hyProjection, ?_, ?_, ?_, ?_⟩
          · intro v hv
            have hvPair := GraphPath.ofAdj_vertexSet_subset hxy hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
            rcases hvPair with rfl | rfl
            · simpa [hxProjection]
            · simpa [hyProjection]
          · intro f hf
            have hfOne := GraphPath.ofAdj_edgeSet_subset hxy hf
            have hfe : f = s(x, y) := Finset.mem_singleton.mp hfOne
            subst f
            simp [namedHostEdgeSet, hOrigin]
          · intro v hv hva
            have hvPair := GraphPath.ofAdj_vertexSet_subset hxy hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
            rcases hvPair with rfl | rfl
            · rfl
            · exact False.elim (hne (hva.symm.trans hyProjection))
          · intro v hv hvb
            have hvPair := GraphPath.ofAdj_vertexSet_subset hxy hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
            rcases hvPair with rfl | rfl
            · exact False.elim (hne (hxProjection.symm.trans hvb))
            · rfl
      | @cons c d b e' he' rest =>
          let tail' :
              (ContractedGraph (G := G) (cluster := cluster)).NamedEdgeWalk c b :=
            .cons e' he' rest
          have htailPath : tail'.toUnderlyingWalk.IsPath := by
            exact hpath.tail
          have hc_ne_a : c ≠ a := by
            intro hca
            rcases he with he | he
            · exact
                (ContractedGraph (G := G) (cluster := cluster)).end_ne e
                  (he.1.trans (he.2.trans hca).symm)
            · exact
                (ContractedGraph (G := G) (cluster := cluster)).end_ne e
                  ((he.2.trans hca).trans he.1.symm)
          have hc_ne_b : c ≠ b := by
            intro hcb
            subst b
            have hnil :
                tail'.toUnderlyingWalk = _root_.SimpleGraph.Walk.nil :=
              (_root_.SimpleGraph.Walk.isPath_iff_eq_nil
                tail'.toUnderlyingWalk).mp htailPath
            have hlength := congrArg
              _root_.SimpleGraph.Walk.length hnil
            simp [tail'] at hlength
          have hcOld : Vertex.IsOld c :=
            hinterior c (by simp) hc_ne_a hc_ne_b
          obtain ⟨z, hcz⟩ := Vertex.exists_old_of_isOld hcOld
          have htailInterior :
              ∀ q ∈ tail'.vertexSet, q ≠ c → q ≠ b →
                Vertex.IsOld q := by
            intro q hq hqc hqb
            apply hinterior q
              (Finset.mem_insert.mpr (Or.inr hq)) ?_ hqb
            intro hqa
            have hnot :
                a ∉ tail'.toUnderlyingWalk.support := by
              have hnodup := hpath.support_nodup
              simp only [NamedEdgeWalk.toUnderlyingWalk_cons,
                _root_.SimpleGraph.Walk.support_cons,
                List.nodup_cons] at hnodup
              exact hnodup.1
            apply hnot
            have hqSupport : q ∈ tail'.toUnderlyingWalk.support := by
              apply List.mem_toFinset.mp
              rw [tail'.toUnderlyingWalk_support_toFinset]
              exact hq
            simpa [hqa] using hqSupport
          obtain ⟨R, hRsource, hRtarget, hRvertices, hRedges,
              hRsourceUnique, hRtargetUnique⟩ :=
            ih hc_ne_b htailPath htailInterior
          have hyz : y = z :=
            eq_of_projection_eq_old
              (cluster := cluster) (by simpa [hcz] using hyProjection)
          have hRz : R.source = z :=
            eq_of_projection_eq_old
              (cluster := cluster) (by simpa [hcz] using hRsource)
          have hglue : L.target = R.source := by
            simpa [L, hyz, hRz]
          let Q := L.appendWithEqToPath R hglue
          refine ⟨Q, ?_, hRtarget, ?_, ?_, ?_, ?_⟩
          · simpa [Q, L] using hxProjection
          · intro v hv
            have hvPieces :=
              L.appendWithEqToPath_vertexSet_subset R hglue hv
            rcases Finset.mem_union.mp hvPieces with hvL | hvR
            · have hvPair := GraphPath.ofAdj_vertexSet_subset hxy hvL
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
              rcases hvPair with rfl | rfl
              · simpa [hxProjection]
              · simpa [hyProjection]
            · exact Finset.mem_insert_of_mem (hRvertices v hvR)
          · intro f hf
            have hfPieces :=
              L.appendWithEqToPath_edgeSet_subset R hglue hf
            rcases Finset.mem_union.mp hfPieces with hfL | hfR
            · have hfOne := GraphPath.ofAdj_edgeSet_subset hxy hfL
              have hfe : f = s(x, y) := Finset.mem_singleton.mp hfOne
              subst f
              simp [namedHostEdgeSet, hOrigin]
            · have hfTail := hRedges hfR
              have hfFull :
                  f ∈ insert
                    (edgeOrigin (G := G) (cluster := cluster) e)
                    (namedHostEdgeSet tail') :=
                Finset.mem_insert.mpr (Or.inr hfTail)
              simpa [namedHostEdgeSet, tail'] using hfFull
          · intro v hv hva
            have hvPieces :=
              L.appendWithEqToPath_vertexSet_subset R hglue hv
            rcases Finset.mem_union.mp hvPieces with hvL | hvR
            · have hvPair := GraphPath.ofAdj_vertexSet_subset hxy hvL
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
              rcases hvPair with rfl | rfl
              · rfl
              · exact False.elim (hc_ne_a
                  (hyProjection.symm.trans hva))
            · have hprojTail := hRvertices v hvR
              have haNotTail :
                  a ∉ tail'.vertexSet := by
                intro ha
                have haSupport :
                    a ∈ tail'.toUnderlyingWalk.support := by
                  apply List.mem_toFinset.mp
                  rw [tail'.toUnderlyingWalk_support_toFinset]
                  exact ha
                have hnodup := hpath.support_nodup
                simp only [NamedEdgeWalk.toUnderlyingWalk_cons,
                  _root_.SimpleGraph.Walk.support_cons,
                  List.nodup_cons] at hnodup
                exact hnodup.1 haSupport
              exact False.elim (haNotTail (hva ▸ hprojTail))
          · intro v hv hvb
            have hvPieces :=
              L.appendWithEqToPath_vertexSet_subset R hglue hv
            rcases Finset.mem_union.mp hvPieces with hvL | hvR
            · have hvPair := GraphPath.ofAdj_vertexSet_subset hxy hvL
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
              rcases hvPair with rfl | rfl
              · exact False.elim (hne (hxProjection.symm.trans hvb))
              · exact False.elim (hc_ne_b
                  (hyProjection.symm.trans hvb))
            · exact hRtargetUnique v hvR hvb

/-! ## Router-index relabeling and the weak Phase 1 skeleton -/

namespace Vertex

/-- The terminal subtype represented by router `i`. -/
def terminalVertex (i : Fin n) :
    TerminalVertex
      (ChekuriChuzhoySection5RouterContraction.terminals
        (V := V) (n := n)) :=
  ⟨ChekuriChuzhoySection5RouterContraction.Vertex.router i,
    mem_terminals_router i⟩

/-- Recover the router index represented by a contracted terminal subtype. -/
noncomputable def terminalIndex
    (t : TerminalVertex
      (ChekuriChuzhoySection5RouterContraction.terminals
        (V := V) (n := n))) : Fin n :=
  Classical.choose (exists_router_of_mem_terminals t.2)

theorem terminalIndex_spec
    (t : TerminalVertex
      (ChekuriChuzhoySection5RouterContraction.terminals
        (V := V) (n := n))) :
    t.1 =
      ChekuriChuzhoySection5RouterContraction.Vertex.router
        (terminalIndex t) :=
  Classical.choose_spec (exists_router_of_mem_terminals t.2)

@[simp] theorem terminalIndex_terminalVertex (i : Fin n) :
    terminalIndex (terminalVertex (V := V) i) = i := by
  have h := terminalIndex_spec (terminalVertex (V := V) i)
  injection h with h
  exact h.symm

theorem terminalVertex_terminalIndex
    (t : TerminalVertex
      (ChekuriChuzhoySection5RouterContraction.terminals
        (V := V) (n := n))) :
    terminalVertex (V := V) (terminalIndex t) = t := by
  apply Subtype.ext
  exact (terminalIndex_spec t).symm

theorem terminalIndex_injective :
    Function.Injective
      (terminalIndex :
        TerminalVertex
          (ChekuriChuzhoySection5RouterContraction.terminals
            (V := V) (n := n)) → Fin n) := by
  intro a b hab
  rw [← terminalVertex_terminalIndex a,
    ← terminalVertex_terminalIndex b, hab]

end Vertex

/-- Relabel a terminal multigraph on contracted router terminals by `Fin n`. -/
noncomputable def projectTerminalGraph
    (H : FiniteEdgeIndexedGraph
      (TerminalVertex
        (ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n)))) :
    FiniteEdgeIndexedGraph (Fin n) where
  Edge := H.Edge
  edgeFintype := H.edgeFintype
  edgeDecidableEq := H.edgeDecidableEq
  left := fun e => Vertex.terminalIndex (H.left e)
  right := fun e => Vertex.terminalIndex (H.right e)
  end_ne := by
    intro e heq
    exact H.end_ne e (Vertex.terminalIndex_injective heq)

theorem terminalIndex_eq_iff
    (t : TerminalVertex
      (ChekuriChuzhoySection5RouterContraction.terminals
        (V := V) (n := n)))
    (i : Fin n) :
    Vertex.terminalIndex t = i ↔
      t = Vertex.terminalVertex (V := V) i := by
  constructor
  · intro h
    apply Vertex.terminalIndex_injective
    simpa using h
  · rintro rfl
    simp

@[simp] theorem terminalVertex_mem_image
    (X : Finset (Fin n)) (i : Fin n) :
    Vertex.terminalVertex (V := V) i ∈
        X.image (Vertex.terminalVertex (V := V)) ↔
      i ∈ X := by
  simp [Vertex.terminalVertex]

theorem terminal_mem_image_iff
    (X : Finset (Fin n))
    (t : TerminalVertex
      (ChekuriChuzhoySection5RouterContraction.terminals
        (V := V) (n := n))) :
    t ∈ X.image (Vertex.terminalVertex (V := V)) ↔
      Vertex.terminalIndex t ∈ X := by
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, hit⟩
    have hiIndex : i = Vertex.terminalIndex t := by
      calc
        i = Vertex.terminalIndex
            (Vertex.terminalVertex (V := V) i) := by simp
        _ = Vertex.terminalIndex t :=
          congrArg Vertex.terminalIndex hit
    simpa [← hiIndex] using hi
  · intro ht
    exact Finset.mem_image.mpr
      ⟨Vertex.terminalIndex t, ht,
        Vertex.terminalVertex_terminalIndex t⟩

theorem projectTerminalGraph_boundary
    (H : FiniteEdgeIndexedGraph
      (TerminalVertex
        (ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n))))
    (X : Finset (Fin n)) :
    (projectTerminalGraph H).boundary X =
      H.boundary (X.image (Vertex.terminalVertex (V := V))) := by
  ext e
  rw [FiniteEdgeIndexedGraph.mem_boundary
    (projectTerminalGraph H) X e]
  constructor
  · intro he
    apply (H.mem_boundary
      (X.image (Vertex.terminalVertex (V := V))) e).2
    change
      (Vertex.terminalIndex (H.left e) ∈ X ∧
          Vertex.terminalIndex (H.right e) ∉ X) ∨
        (Vertex.terminalIndex (H.right e) ∈ X ∧
          Vertex.terminalIndex (H.left e) ∉ X) at he
    simpa only [FiniteEdgeIndexedGraph.Crosses,
      terminal_mem_image_iff] using he
  · intro he
    have he' :=
      (H.mem_boundary
        (X.image (Vertex.terminalVertex (V := V))) e).1 he
    change
      (Vertex.terminalIndex (H.left e) ∈ X ∧
          Vertex.terminalIndex (H.right e) ∉ X) ∨
        (Vertex.terminalIndex (H.right e) ∈ X ∧
          Vertex.terminalIndex (H.left e) ∉ X)
    simpa only [FiniteEdgeIndexedGraph.Crosses,
      terminal_mem_image_iff] using he'

theorem projectTerminalGraph_isEdgeConnected
    (H : FiniteEdgeIndexedGraph
      (TerminalVertex
        (ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n))))
    {k : Nat} (hconn : H.IsEdgeConnected k) :
    (projectTerminalGraph H).IsEdgeConnected k := by
  intro X hX hXproper
  have hImageNonempty :
      (X.image (Vertex.terminalVertex (V := V))).Nonempty :=
    hX.image _
  have hImageProper :
      X.image (Vertex.terminalVertex (V := V)) ≠ Finset.univ := by
    intro hImage
    apply hXproper
    ext i
    simp only [Finset.mem_univ, iff_true]
    have hi :
        Vertex.terminalVertex (V := V) i ∈
          X.image (Vertex.terminalVertex (V := V)) := by
      rw [hImage]
      simp
    exact (terminalVertex_mem_image X i).mp hi
  rw [projectTerminalGraph_boundary]
  exact hconn
    (X.image (Vertex.terminalVertex (V := V)))
    hImageNonempty hImageProper

/-- The weak cluster-valued skeleton produced in Phase 1.  A one-per-group
selection is internally node-disjoint; endpoint collisions are retained until
the paper's bounded-degree thinning step. -/
structure RouterPathSkeleton
    (G : _root_.SimpleGraph V) (cluster : Fin n → Finset V) where
  graph : FiniteEdgeIndexedGraph (Fin n)
  hostPath : graph.Edge → Lax17Proofs.SimpleGraph.GraphPath G
  host_source_mem :
    ∀ e, (hostPath e).source ∈ cluster (graph.left e)
  host_target_mem :
    ∀ e, (hostPath e).target ∈ cluster (graph.right e)
  groups : Finpartition (Finset.univ : Finset graph.Edge)
  internally_disjoint_clusters :
    ∀ e r, (hostPath e).InternallyDisjointFromSet (cluster r)
  one_per_group_internally_node_disjoint :
    ∀ selected : Finset graph.Edge,
      (∀ U ∈ groups.parts, (selected ∩ U).card = 1) →
        ∀ ⦃e⦄, e ∈ selected → ∀ ⦃f⦄, f ∈ selected → e ≠ f →
          (hostPath e).InternallyDisjoint (hostPath f)

namespace RouterPathSkeleton

variable {cluster : Fin n → Finset V}

instance (S : RouterPathSkeleton G cluster) : Fintype S.graph.Edge :=
  S.graph.edgeFintype

instance (S : RouterPathSkeleton G cluster) : DecidableEq S.graph.Edge :=
  S.graph.edgeDecidableEq

def GroupSizeAtMost (S : RouterPathSkeleton G cluster) (k : Nat) : Prop :=
  ∀ U ∈ S.groups.parts, U.card ≤ k

def IsGroupTransversal
    (S : RouterPathSkeleton G cluster)
    (selected : Finset S.graph.Edge) : Prop :=
  ∀ U ∈ S.groups.parts, (selected ∩ U).card = 1

/-- Number of routed abstract edge copies using one original host edge. -/
noncomputable def hostEdgeLoad
    (S : RouterPathSkeleton G cluster) (e : Sym2 V) : Nat :=
  (Finset.univ.filter fun a : S.graph.Edge =>
    e ∈ (S.hostPath a).edgeSet).card

/-- A host edge has an endpoint in one of the router clusters. -/
def HostEdgeIncidentToRouters (e : Sym2 V) : Prop :=
  ∃ i : Fin n, ∃ v ∈ cluster i, v ∈ e

/-- Every original edge incident with a router occurs in at most `c` decoded
core paths. -/
def EndpointCongestionAtMost
    (S : RouterPathSkeleton G cluster) (c : Nat) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet →
    HostEdgeIncidentToRouters (cluster := cluster) e →
      S.hostEdgeLoad e ≤ c

noncomputable def edgeBundle
    (S : RouterPathSkeleton G cluster) (i j : Fin n) :
    Finset S.graph.Edge := by
  classical
  exact Finset.univ.filter fun e => S.graph.Joins e i j

@[simp] theorem mem_edgeBundle
    (S : RouterPathSkeleton G cluster) {i j : Fin n} {e : S.graph.Edge} :
    e ∈ S.edgeBundle i j ↔ S.graph.Joins e i j := by
  simp [edgeBundle]

end RouterPathSkeleton

/-! ## Realizing the grouped terminal core in the original host -/

namespace FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore

variable {mu : Nat}
variable
  (C :
    (ContractedGraph (G := G) (cluster := cluster)).RealizedGroupedTerminalCore
      (ChekuriChuzhoySection5RouterContraction.terminals
        (V := V) (n := n)) mu)

/-- Retain named parallel edges while cycle-erasing one lifted core route. -/
noncomputable def simpleLiftedNamedPath
    (e : C.core.graph.Edge) :
    (ContractedGraph (G := G) (cluster := cluster)).NamedEdgeWalk
      (C.terminalGraph.left e).1 (C.terminalGraph.right e).1 :=
  (C.liftedNamedWalk e).simpleNamedSubpath

theorem simpleLiftedNamedPath_edgeList_subset
    (e : C.core.graph.Edge) :
    (simpleLiftedNamedPath C e).edgeList.toFinset ⊆
      (C.liftedNamedWalk e).edgeList.toFinset :=
  NamedEdgeWalk.simpleNamedSubpath_edgeList_subset _

theorem simpleLiftedNamedPath_vertexSet_subset
    (e : C.core.graph.Edge) :
    (simpleLiftedNamedPath C e).vertexSet ⊆
      (C.liftedNamedWalk e).vertexSet :=
  NamedEdgeWalk.simpleNamedSubpath_vertexSet_subset _

theorem simpleLiftedNamedPath_isPath
    (e : C.core.graph.Edge) :
    (simpleLiftedNamedPath C e).toUnderlyingWalk.IsPath :=
  NamedEdgeWalk.simpleNamedSubpath_isPath _

theorem simpleLiftedNamedPath_end_ne
    (e : C.core.graph.Edge) :
    (C.terminalGraph.left e).1 ≠ (C.terminalGraph.right e).1 := by
  intro h
  apply C.terminalGraph.end_ne e
  apply Subtype.ext
  exact h

/-- Every internal vertex of the simple contracted route is an old host
vertex.  Router constructors can occur only as the two terminal endpoints. -/
theorem simpleLiftedNamedPath_internal_old
    (e : C.core.graph.Edge) :
    ∀ z ∈ (simpleLiftedNamedPath C e).vertexSet,
      z ≠ (C.terminalGraph.left e).1 →
        z ≠ (C.terminalGraph.right e).1 →
          Vertex.IsOld z := by
  intro z hz hzLeft hzRight
  have hzLifted :
      z ∈ (C.liftedNamedWalk e).vertexSet :=
    simpleLiftedNamedPath_vertexSet_subset C e hz
  rcases C.liftedNamedWalk_vertex_classification e hzLifted with
    hleft | hright | ⟨s, hlabel, hzFiber⟩
  · exact False.elim (hzLeft hleft)
  · exact False.elim (hzRight hright)
  · have hsNonterminal :=
      C.core.grouped.split_nonterminal e s hlabel
    cases z with
    | router i =>
        exact False.elim
          (Finset.disjoint_left.mp
            (C.reduction.fiber_disjoint_terminals hsNonterminal)
            hzFiber (mem_terminals_router i))
    | old v =>
        trivial

/-- The host path data retained from one simple named core route. -/
structure RouterHostPathData (e : C.core.graph.Edge) where
  path : Lax17Proofs.SimpleGraph.GraphPath G
  source_projection :
    projection cluster path.source = (C.terminalGraph.left e).1
  target_projection :
    projection cluster path.target = (C.terminalGraph.right e).1
  vertex_projection :
    ∀ v ∈ path.vertexSet,
      projection cluster v ∈ (simpleLiftedNamedPath C e).vertexSet
  edge_provenance :
    path.edgeSet ⊆ namedHostEdgeSet (simpleLiftedNamedPath C e)
  source_unique :
    ∀ v ∈ path.vertexSet,
      projection cluster v = (C.terminalGraph.left e).1 →
        v = path.source
  target_unique :
    ∀ v ∈ path.vertexSet,
      projection cluster v = (C.terminalGraph.right e).1 →
        v = path.target

theorem exists_routerHostPathData
    (e : C.core.graph.Edge) :
    Nonempty (RouterHostPathData C e) := by
  obtain ⟨P, hsource, htarget, hvertices, hedges,
      hsourceUnique, htargetUnique⟩ :=
    exists_hostPath_of_simpleNamedPath
      (cluster := cluster) (simpleLiftedNamedPath C e)
      (simpleLiftedNamedPath_end_ne C e)
      (simpleLiftedNamedPath_isPath C e)
      (simpleLiftedNamedPath_internal_old C e)
  exact ⟨{
    path := P
    source_projection := hsource
    target_projection := htarget
    vertex_projection := hvertices
    edge_provenance := hedges
    source_unique := hsourceUnique
    target_unique := htargetUnique
  }⟩

noncomputable def routerHostPathData
    (e : C.core.graph.Edge) : RouterHostPathData C e :=
  Classical.choice (exists_routerHostPathData C e)

/-- A lifted contracted edge incident with a router terminal comes from a
doubled normal-form route atom, rather than from inside a contraction fiber. -/
private theorem exists_routeAtom_of_lifted_edge_incident_router
    (e : C.core.graph.Edge)
    (q : (ContractedGraph (G := G) (cluster := cluster)).Edge)
    (hq : q ∈ (C.liftedNamedWalk e).edgeList)
    (hincident :
      (ContractedGraph (G := G) (cluster := cluster)).left q ∈
          ChekuriChuzhoySection5RouterContraction.terminals
            (V := V) (n := n) ∨
        (ContractedGraph (G := G) (cluster := cluster)).right q ∈
          ChekuriChuzhoySection5RouterContraction.terminals
            (V := V) (n := n)) :
    ∃ a ∈ C.core.grouped.history.routeEdges e,
      q = C.reduction.edgeOrigin a.1 := by
  rcases C.liftedNamedWalk_isLift e q hq with horigin | hfiber
  · rcases horigin with ⟨a, ha, hqa⟩
    exact ⟨a, List.mem_toFinset.mpr ha, hqa⟩
  · rcases hfiber with ⟨z, _hz, hleft, hright⟩
    rcases hincident with hleftTerminal | hrightTerminal
    · have hzTerminal :=
        C.reduction.terminal_of_mem_fiber hleft hleftTerminal
      have hrightEq :
          (ContractedGraph (G := G) (cluster := cluster)).right q =
            (ContractedGraph (G := G) (cluster := cluster)).left q := by
        have h := hright
        rw [hzTerminal,
          C.reduction.terminal_fiber
            ⟨(ContractedGraph (G := G) (cluster := cluster)).left q,
              hleftTerminal⟩] at h
        simpa using h
      exact ((ContractedGraph (G := G) (cluster := cluster)).end_ne q
        hrightEq.symm).elim
    · have hzTerminal :=
        C.reduction.terminal_of_mem_fiber hright hrightTerminal
      have hleftEq :
          (ContractedGraph (G := G) (cluster := cluster)).left q =
            (ContractedGraph (G := G) (cluster := cluster)).right q := by
        have h := hleft
        rw [hzTerminal,
          C.reduction.terminal_fiber
            ⟨(ContractedGraph (G := G) (cluster := cluster)).right q,
              hrightTerminal⟩] at h
        simpa using h
      exact ((ContractedGraph (G := G) (cluster := cluster)).end_ne q
        hleftEq).elim

/-- Doubled route atoms retaining the contracted input edge `q`. -/
noncomputable def originFiber
    (q : (ContractedGraph (G := G) (cluster := cluster)).Edge) :
    Finset C.reduction.graph.doubleEdges.Edge :=
  Finset.univ.filter fun a => C.reduction.edgeOrigin a.1 = q

@[simp] theorem mem_originFiber
    {q : (ContractedGraph (G := G) (cluster := cluster)).Edge}
    {a : C.reduction.graph.doubleEdges.Edge} :
    a ∈ originFiber C q ↔ C.reduction.edgeOrigin a.1 = q := by
  simp [originFiber]

theorem originFiber_card_le_two
    (q : (ContractedGraph (G := G) (cluster := cluster)).Edge) :
    (originFiber C q).card ≤ 2 := by
  classical
  let tag : originFiber C q → Bool := fun a => a.1.2
  have htag : Function.Injective tag := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · apply C.reduction.edgeOrigin_injective
      have ha : C.reduction.edgeOrigin a.1.1 = q :=
        mem_originFiber C |>.mp a.2
      have hb : C.reduction.edgeOrigin b.1.1 = q :=
        mem_originFiber C |>.mp b.2
      exact ha.trans hb.symm
    · exact hab
  have hcard := Fintype.card_le_of_injective tag htag
  simpa only [Fintype.card_coe] using hcard

theorem contractedEdge_incident_router_of_origin_incident
    (hpair : RouterPairwiseDisjoint cluster)
    (q : (ContractedGraph (G := G) (cluster := cluster)).Edge)
    (hincident :
      RouterPathSkeleton.HostEdgeIncidentToRouters
        (cluster := cluster)
        (edgeOrigin (G := G) (cluster := cluster) q)) :
    (ContractedGraph (G := G) (cluster := cluster)).left q ∈
        ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n) ∨
      (ContractedGraph (G := G) (cluster := cluster)).right q ∈
        ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n) := by
  rcases hincident with ⟨i, v, hvi, hvEdge⟩
  obtain ⟨x, y, _hxy, hxProjection, hyProjection, hOrigin⟩ :=
    exists_hostEdge_of_joins (cluster := cluster) q
      (Or.inl ⟨rfl, rfl⟩)
  rw [hOrigin] at hvEdge
  rcases Sym2.mem_iff.mp hvEdge with hvx | hvy
  · have hleft :
        (ContractedGraph (G := G) (cluster := cluster)).left q =
          ChekuriChuzhoySection5RouterContraction.Vertex.router i := by
      exact hxProjection.symm.trans
        (projection_eq_router_of_mem hpair (hvx ▸ hvi))
    left
    rw [hleft]
    exact mem_terminals_router i
  · have hright :
        (ContractedGraph (G := G) (cluster := cluster)).right q =
          ChekuriChuzhoySection5RouterContraction.Vertex.router i := by
      exact hyProjection.symm.trans
        (projection_eq_router_of_mem hpair (hvy ▸ hvi))
    right
    rw [hright]
    exact mem_terminals_router i

/-- The realized grouped core, relabeled by router indices and decoded into
direct paths in the original host graph. -/
noncomputable def routerPathSkeleton
    (hpair : RouterPairwiseDisjoint cluster) :
    RouterPathSkeleton G cluster := by
  let data : ∀ e : C.core.graph.Edge, RouterHostPathData C e :=
    fun e => routerHostPathData C e
  exact {
    graph := projectTerminalGraph C.terminalGraph
    hostPath := fun e => (data e).path
    host_source_mem := by
      intro e
      apply mem_cluster_of_projection_eq_router
      exact (data e).source_projection.trans
        (Vertex.terminalIndex_spec (C.terminalGraph.left e))
    host_target_mem := by
      intro e
      apply mem_cluster_of_projection_eq_router
      exact (data e).target_projection.trans
        (Vertex.terminalIndex_spec (C.terminalGraph.right e))
    groups :=
      SimpleGraph.ChekuriChuzhoySection5LabelPartition.partition
        C.core.grouped.label
    internally_disjoint_clusters := by
      intro e r v hvPath hvCluster
      have hvProjection :
          projection cluster v =
            ChekuriChuzhoySection5RouterContraction.Vertex.router r :=
        projection_eq_router_of_mem hpair hvCluster
      have hvSimple := (data e).vertex_projection v hvPath
      have hvLifted :
          projection cluster v ∈ (C.liftedNamedWalk e).vertexSet :=
        simpleLiftedNamedPath_vertexSet_subset C e hvSimple
      rcases C.liftedNamedWalk_vertex_classification e hvLifted with
        hleft | hright | ⟨s, hlabel, hvFiber⟩
      · exact Or.inl ((data e).source_unique v hvPath hleft)
      · exact Or.inr ((data e).target_unique v hvPath hright)
      · have hsNonterminal :=
          C.core.grouped.split_nonterminal e s hlabel
        exact False.elim
          (Finset.disjoint_left.mp
            (C.reduction.fiber_disjoint_terminals hsNonterminal)
            (hvProjection ▸ hvFiber) (mem_terminals_router r))
    one_per_group_internally_node_disjoint := by
      intro selected hselected e he f hf hef v hve hvf
      have hlabelNe :
          C.core.grouped.label e ≠ C.core.grouped.label f :=
        SimpleGraph.ChekuriChuzhoySection5LabelPartition.label_ne_of_mem_onePerPart
          hselected he hf hef
      have hveLifted :
          projection cluster v ∈ (C.liftedNamedWalk e).vertexSet :=
        simpleLiftedNamedPath_vertexSet_subset C e
          ((data e).vertex_projection v hve)
      have hvfLifted :
          projection cluster v ∈ (C.liftedNamedWalk f).vertexSet :=
        simpleLiftedNamedPath_vertexSet_subset C f
          ((data f).vertex_projection v hvf)
      by_cases hvTerminal :
          projection cluster v ∈
            ChekuriChuzhoySection5RouterContraction.terminals
              (V := V) (n := n)
      · have heEndpoint :
            (data e).path.IsEndpoint v := by
          rcases C.liftedNamedWalk_vertex_classification e hveLifted with
            hleft | hright | ⟨s, hlabel, hvFiber⟩
          · exact Or.inl ((data e).source_unique v hve hleft)
          · exact Or.inr ((data e).target_unique v hve hright)
          · have hsNonterminal :=
              C.core.grouped.split_nonterminal e s hlabel
            exact False.elim
              (Finset.disjoint_left.mp
                (C.reduction.fiber_disjoint_terminals hsNonterminal)
                hvFiber hvTerminal)
        have hfEndpoint :
            (data f).path.IsEndpoint v := by
          rcases C.liftedNamedWalk_vertex_classification f hvfLifted with
            hleft | hright | ⟨s, hlabel, hvFiber⟩
          · exact Or.inl ((data f).source_unique v hvf hleft)
          · exact Or.inr ((data f).target_unique v hvf hright)
          · have hsNonterminal :=
              C.core.grouped.split_nonterminal f s hlabel
            exact False.elim
              (Finset.disjoint_left.mp
                (C.reduction.fiber_disjoint_terminals hsNonterminal)
                hvFiber hvTerminal)
        exact ⟨heEndpoint, hfEndpoint⟩
      · rcases C.liftedNamedWalk_vertex_classification e hveLifted with
          heLeft | heRight | ⟨s, hlabelE, hvS⟩
        · exact False.elim
            (hvTerminal (heLeft ▸ (C.terminalGraph.left e).2))
        · exact False.elim
            (hvTerminal (heRight ▸ (C.terminalGraph.right e).2))
        · rcases C.liftedNamedWalk_vertex_classification f hvfLifted with
            hfLeft | hfRight | ⟨r, hlabelF, hvR⟩
          · exact False.elim
              (hvTerminal (hfLeft ▸ (C.terminalGraph.left f).2))
          · exact False.elim
              (hvTerminal (hfRight ▸ (C.terminalGraph.right f).2))
          · have hsr : s ≠ r := by
              intro hsr
              apply hlabelNe
              rw [hlabelE, hlabelF, hsr]
            exact False.elim
              (Finset.disjoint_left.mp
                (C.reduction.fiber_pairwise_disjoint hsr) hvS hvR)
  }

@[simp] theorem routerPathSkeleton_graph
    (hpair : RouterPairwiseDisjoint cluster) :
    (routerPathSkeleton C hpair).graph =
      projectTerminalGraph C.terminalGraph :=
  rfl

theorem routerPathSkeleton_edgeConnected
    (hpair : RouterPairwiseDisjoint cluster) :
    (routerPathSkeleton C hpair).graph.IsEdgeConnected (2 * mu) := by
  exact projectTerminalGraph_isEdgeConnected C.terminalGraph
    C.quantitative.terminalGraph_edgeConnected

theorem routerPathSkeleton_groupSize
    (hpair : RouterPairwiseDisjoint cluster) :
    (routerPathSkeleton C hpair).GroupSizeAtMost n := by
  intro U hU
  have hle :
      U.card ≤
        (ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n)).card := by
    apply
      SimpleGraph.ChekuriChuzhoySection5LabelPartition.part_card_le_of_fiber_card_le
        (label := C.core.grouped.label)
        (bound :=
          (ChekuriChuzhoySection5RouterContraction.terminals
            (V := V) (n := n)).card)
        (U := U) ?_ hU
    intro key hkey
    exact C.label_fiber_card_le key
  simpa using hle

theorem routerPathSkeleton_endpointCongestion
    (hpair : RouterPairwiseDisjoint cluster) :
    (routerPathSkeleton C hpair).EndpointCongestionAtMost 2 := by
  classical
  intro hostEdge _hhostEdge hincident
  let items : Finset C.core.graph.Edge :=
    Finset.univ.filter fun e =>
      hostEdge ∈ (routerHostPathData C e).path.edgeSet
  change items.card ≤ 2
  by_cases hitems : items.Nonempty
  · rcases hitems with ⟨e0, he0⟩
    have he0Path :
        hostEdge ∈ (routerHostPathData C e0).path.edgeSet := by
      simpa [items] using he0
    have hexistsQ :
        ∀ e ∈ items,
          ∃ q : (ContractedGraph (G := G) (cluster := cluster)).Edge,
            q ∈ (C.liftedNamedWalk e).edgeList ∧
              edgeOrigin (G := G) (cluster := cluster) q = hostEdge := by
      intro e he
      have hePath :
          hostEdge ∈ (routerHostPathData C e).path.edgeSet := by
        simpa [items] using he
      have heProvenance :=
        (routerHostPathData C e).edge_provenance hePath
      have heList :
          hostEdge ∈
            ((simpleLiftedNamedPath C e).edgeList.map
              (edgeOrigin (G := G) (cluster := cluster))).toFinset := by
        simpa [namedHostEdgeSet] using heProvenance
      rcases List.mem_map.mp (List.mem_toFinset.mp heList) with
        ⟨q, hqSimple, hqOrigin⟩
      have hqLifted :
          q ∈ (C.liftedNamedWalk e).edgeList := by
        apply List.mem_toFinset.mp
        exact simpleLiftedNamedPath_edgeList_subset C e
          (List.mem_toFinset.mpr hqSimple)
      exact ⟨q, hqLifted, hqOrigin⟩
    obtain ⟨q0, hq0Lifted, hq0Origin⟩ := hexistsQ e0 he0
    let support : C.core.graph.Edge →
        Finset C.reduction.graph.doubleEdges.Edge :=
      fun e => C.core.grouped.history.routeEdges e ∩ originFiber C q0
    have hnonempty : ∀ e ∈ items, (support e).Nonempty := by
      intro e he
      obtain ⟨q, hqLifted, hqOrigin⟩ := hexistsQ e he
      have hqq0 : q = q0 := by
        apply edgeOrigin_injective (G := G) (cluster := cluster)
        exact hqOrigin.trans hq0Origin.symm
      have hqIncident :
          (ContractedGraph (G := G) (cluster := cluster)).left q ∈
              ChekuriChuzhoySection5RouterContraction.terminals
                (V := V) (n := n) ∨
            (ContractedGraph (G := G) (cluster := cluster)).right q ∈
              ChekuriChuzhoySection5RouterContraction.terminals
                (V := V) (n := n) := by
        apply contractedEdge_incident_router_of_origin_incident
          hpair q
        simpa [hqOrigin] using hincident
      obtain ⟨a, haRoute, hqa⟩ :=
        exists_routeAtom_of_lifted_edge_incident_router
          C e q hqLifted hqIncident
      refine ⟨a, Finset.mem_inter.mpr ⟨haRoute, ?_⟩⟩
      apply (mem_originFiber C).mpr
      exact hqa.symm.trans hqq0
    have hpairwise :
        (↑items : Set C.core.graph.Edge).PairwiseDisjoint support := by
      intro e he f hf hef
      exact Finset.disjoint_of_subset_left
        Finset.inter_subset_left
        (Finset.disjoint_of_subset_right
          Finset.inter_subset_left
          (C.core.grouped.history.routeEdges_pairwise_disjoint hef))
    have hsubset :
        ∀ e ∈ items, support e ⊆ originFiber C q0 := by
      intro e he
      exact Finset.inter_subset_right
    have hcard :=
      card_le_card_of_disjoint_nonempty_support items support
        (originFiber C q0) hnonempty hpairwise hsubset
    exact hcard.trans (originFiber_card_le_two C q0)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hitems
    simp [hitems]

end FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore

/-- Complete Phase 1 router-skeleton producer.  Pairwise router linking gives
terminal element connectivity in the parallel-edge contraction; the realized
grouped core is then decoded back into direct host paths. -/
theorem exists_routerPathSkeleton_of_goodRouterFamily
    {terminals : Finset V}
    {w0 bandwidthCap alphaNum alphaDen routeValue Delta mu : Nat}
    (R :
      ChekuriChuzhoySection5Routers.GoodRouterFamily
        G terminals n w0 bandwidthCap alphaNum alphaDen routeValue)
    (hterminals : NodeWellLinkedIn G Finset.univ terminals)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (hmu : mu ≤ routeValue / (8 * Delta)) :
    ∃ S : RouterPathSkeleton G R.router,
      S.graph.IsEdgeConnected (2 * mu) ∧
        S.GroupSizeAtMost n ∧
          S.EndpointCongestionAtMost 2 := by
  classical
  have hpair : RouterPairwiseDisjoint R.router :=
    R.pairwise_disjoint
  have hpacking :
      ∀ i j : Fin n, i ≠ j →
        ∃ P : PathPacking G (R.router i) (R.router j), mu ≤ P.card := by
    intro i j hij
    obtain ⟨P, hPcard⟩ :=
      ChekuriChuzhoySection5RouterLinking.exists_routerPair_pathPacking
        R hterminals hdegree hDelta i j hij
    exact ⟨P, hmu.trans hPcard⟩
  have hconn :
      (ContractedGraph (G := G) (cluster := R.router)).TerminalElementConnectedAtLeast
        (ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n)) mu :=
    terminalElementConnectedAtLeast_of_pairwise_packings hpair hpacking
  obtain ⟨C⟩ :=
    (ContractedGraph (G := G) (cluster := R.router)).exists_realizedGroupedTerminalCore
        (ChekuriChuzhoySection5RouterContraction.terminals
          (V := V) (n := n)) mu hconn
  let S := FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore.routerPathSkeleton
    C hpair
  exact ⟨S,
    FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore.routerPathSkeleton_edgeConnected
      C hpair,
    FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore.routerPathSkeleton_groupSize
      C hpair,
    FiniteEdgeIndexedGraph.RealizedGroupedTerminalCore.routerPathSkeleton_endpointCongestion
      C hpair⟩

end NamedGraph

end ChekuriChuzhoySection5RouterSkeleton
end SimpleGraph

end Lax17Proofs
