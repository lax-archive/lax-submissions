import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1
import Lax17Proofs.Source.ChekuriChuzhoyTheorem215
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Theorem 3.1, proof-facing reductions

This file starts the proof-facing assembly of Chekuri--Chuzhoy Theorem 3.1
from its Appendix B.1 rerouting lemma.

The first self-contained component is the finite descent used in the paper:
if every bad linkage can either produce a grid minor or be rerouted to a
linkage with strictly fewer degree-two vertices in the auxiliary graph, then
iteration terminates at a good linkage unless a grid minor has already been
found.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V} {h q : ℕ}

/-- Finite descent for Appendix B.1 rerouting.

This is the termination argument used inside Chekuri--Chuzhoy Theorem 3.1:
starting from any linkage, repeatedly apply a rerouting step to bad linkages.
The natural-number measure is the number of degree-two vertices in the
auxiliary graph, so strict descent cannot continue forever. -/
theorem exists_goodLinkage_or_gridMinor_of_measure_drop
    (hstep :
      ∀ L : PerfectPathPacking G A B,
        ¬ GoodLinkage L h →
          ContainsGridMinor G h ∨
            ∃ L' : PerfectPathPacking G A B,
              linkageAuxDegreeTwoCount L' < linkageAuxDegreeTwoCount L)
    (L : PerfectPathPacking G A B) :
    ContainsGridMinor G h ∨
      ∃ Lgood : PerfectPathPacking G A B, GoodLinkage Lgood h := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ L : PerfectPathPacking G A B,
      linkageAuxDegreeTwoCount L = n →
        ContainsGridMinor G h ∨
          ∃ Lgood : PerfectPathPacking G A B, GoodLinkage Lgood h
  have hmain : ∀ n : ℕ, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro L hcount
        by_cases hgood : GoodLinkage L h
        · exact Or.inr ⟨L, hgood⟩
        · rcases hstep L hgood with hgrid | ⟨L', hdrop⟩
          · exact Or.inl hgrid
          · exact ih (linkageAuxDegreeTwoCount L') (by
              simpa [hcount] using hdrop) L' rfl
  exact hmain (linkageAuxDegreeTwoCount L) L rfl

/-- Finite descent specialized to Theorem B.1's statement.

Once Appendix B.1 supplies the rerouting lemma for every bad linkage, every
initial linkage either yields a grid minor or can be rerouted finitely many
times to a good linkage. -/
theorem exists_goodLinkage_or_gridMinor_of_theoremB1Statement
    [Fintype V]
    (hB1 :
      ∀ L : PerfectPathPacking G A B,
        AppendixB1.TheoremB1Statement G h L)
    (hconn : G.Connected)
    (hlink : NodeLinkedIn G Finset.univ A B)
    (hh : 1 < h)
    (L : PerfectPathPacking G A B) :
    ContainsGridMinor G h ∨
      ∃ Lgood : PerfectPathPacking G A B, GoodLinkage Lgood h := by
  exact exists_goodLinkage_or_gridMinor_of_measure_drop
    (G := G) (A := A) (B := B) (h := h)
    (fun L hbad => hB1 L hconn hlink hh hbad) L

/-- The remaining good-linkage extraction step after Appendix B.1 descent.

In the paper, after the auxiliary graph has no long degree-two path, Theorem
2.15 and the auxiliary-tree argument extract a bounded-size linkage whose
paths are pairwise bridged.  This definition isolates exactly that residual
mathematical obligation from the already formalized finite descent. -/
def GoodLinkageExtractionInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {A B : Finset V} {h q : ℕ},
      1 < h →
        1 < q →
          (L : PerfectPathPacking G A B) →
            GoodLinkage L h →
              q ≤ L.card →
                ∃ Q : PathPacking G A B,
                  Q.card = q ∧ Q.HasPairwiseBridgesIn Finset.univ

/-- Residual extraction from the auxiliary spanning tree branch.

After B.1 descent and Theorem 2.15, the paper uses a spanning tree with many
leaves in the auxiliary graph to select the desired terminal paths and their
bridges.  This definition isolates only that final extraction step. -/
def AuxiliaryTreeExtractionInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {A B : Finset V} {h q : ℕ},
      1 < h →
        1 < q →
          (L : PerfectPathPacking G A B) →
            HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph L) q →
              ∃ Q : PathPacking G A B,
                Q.card = q ∧ Q.HasPairwiseBridgesIn Finset.univ

/-- The remaining bridge-chain realization step in the auxiliary-tree branch.

Given a linkage `L`, a retained index set `I`, and a clean path in the
auxiliary graph from one retained linkage path to another, the paper
concatenates the linkage paths and the auxiliary bridge segments along that
auxiliary path to obtain a single bridge for the restricted packing. -/
def AuxiliaryPathBridgeRealizationInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {A B : Finset V}
    (L : PerfectPathPacking G A B) (I : Finset L.Index),
      ∀ ⦃i j : (L.toPathPacking.restrictIndexSet I).Index⦄,
        i ≠ j →
          (R : GraphPath (linkageAuxGraph L)) →
            R.source = i.1 →
              R.target = j.1 →
                R.InternallyDisjointFromSet I →
                  ∃ β :
                    (L.toPathPacking.restrictIndexSet I).BridgeBetween i j,
                    β.path.vertexSet ⊆ Finset.univ

/-- Choose exactly `q` leaves from a spanning tree with at least `q` leaves. -/
theorem exists_leafIndexSet_card_eq_of_hasSpanningTreeWithAtLeastLeaves
    {X : Type u} [Fintype X] [DecidableEq X]
    (H : _root_.SimpleGraph X) {q : ℕ}
    (htree : HasSpanningTreeWithAtLeastLeaves H q) :
    ∃ T : _root_.SimpleGraph X,
      T ≤ H ∧ T.IsTree ∧
        ∃ I : Finset X,
          I.card = q ∧ ∀ i ∈ I, DegreeEquals T i 1 := by
  classical
  rcases htree with ⟨T, hTH, hTtree, leaves, hleaves, hqleaves⟩
  rcases Finset.exists_subset_card_eq hqleaves with ⟨I, hIleaves, hIcard⟩
  exact ⟨T, hTH, hTtree, I, hIcard, fun i hi =>
    (hleaves i).mp (hIleaves hi)⟩

/-- The first extraction step in the spanning-tree branch: select exactly `q`
leaf linkage paths and restrict the original linkage to those paths. -/
theorem exists_leafSubpacking_of_auxiliarySpanningTree
    [Fintype V]
    (L : PerfectPathPacking G A B) {q : ℕ}
    (htree : HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph L) q) :
    ∃ T : _root_.SimpleGraph L.Index,
      T ≤ linkageAuxGraph L ∧ T.IsTree ∧
        ∃ I : Finset L.Index,
          I.card = q ∧
            (∀ i ∈ I, DegreeEquals T i 1) ∧
              ∃ Q : PathPacking G A B,
                Q = L.toPathPacking.restrictIndexSet I ∧ Q.card = q := by
  classical
  rcases exists_leafIndexSet_card_eq_of_hasSpanningTreeWithAtLeastLeaves
      (linkageAuxGraph L) htree with
    ⟨T, hTH, hTtree, I, hIcard, hIleaf⟩
  refine ⟨T, hTH, hTtree, I, hIcard, hIleaf, ?_⟩
  refine ⟨L.toPathPacking.restrictIndexSet I, rfl, ?_⟩
  simpa [hIcard]

/-- Choose a simple path between two vertices of a connected graph. -/
noncomputable def graphPathOfConnected
    {X : Type u} [DecidableEq X]
    (H : _root_.SimpleGraph X) (hconn : H.Connected) (s t : X) :
    GraphPath H := by
  classical
  let W : H.Walk s t := Classical.choice (hconn.preconnected s t)
  exact GraphPath.ofWalk W

@[simp] theorem graphPathOfConnected_source
    {X : Type u} [DecidableEq X]
    (H : _root_.SimpleGraph X) (hconn : H.Connected) (s t : X) :
    (graphPathOfConnected H hconn s t).source = s := rfl

@[simp] theorem graphPathOfConnected_target
    {X : Type u} [DecidableEq X]
    (H : _root_.SimpleGraph X) (hconn : H.Connected) (s t : X) :
    (graphPathOfConnected H hconn s t).target = t := rfl

/-- A graph path in a graph `T` is internally disjoint from any set of
degree-one vertices of `T`. -/
theorem graphPath_internallyDisjointFrom_leafSet
    {X : Type u} [DecidableEq X] {T : _root_.SimpleGraph X}
    (P : GraphPath T) {I : Finset X}
    (hIleaf : ∀ i ∈ I, DegreeEquals T i 1) :
    P.InternallyDisjointFromSet I := by
  intro v hv hvI
  exact P.isEndpoint_of_mem_vertexSet_of_degreeEquals_one
    (hIleaf v hvI) hv

/-- Between any two selected leaf indices in the auxiliary spanning tree, the
tree path is internally disjoint from all selected leaves when viewed in the
full auxiliary graph. -/
theorem exists_auxiliaryPath_internallyDisjoint_leafSet
    (L : PerfectPathPacking G A B)
    {T : _root_.SimpleGraph L.Index} (hTH : T ≤ linkageAuxGraph L)
    (hTtree : T.IsTree) {I : Finset L.Index}
    (hIleaf : ∀ i ∈ I, DegreeEquals T i 1)
    (i j : L.Index) :
    ∃ P : GraphPath (linkageAuxGraph L),
      P.source = i ∧ P.target = j ∧ P.InternallyDisjointFromSet I := by
  classical
  let P0 : GraphPath T := graphPathOfConnected T hTtree.connected i j
  refine ⟨P0.mapLe hTH, rfl, rfl, ?_⟩
  have hclean0 : P0.InternallyDisjointFromSet I :=
    graphPath_internallyDisjointFrom_leafSet P0 hIleaf
  intro v hv hvI
  rcases hclean0 (by simpa [P0] using hv) hvI with hsrc | htgt
  · exact Or.inl (by simpa [GraphPath.mapLe] using hsrc)
  · exact Or.inr (by simpa [GraphPath.mapLe] using htgt)

/-- The auxiliary spanning-tree extraction is reduced to realizing clean
auxiliary paths as original bridge paths. -/
theorem auxiliaryTreeExtractionInput_of_auxiliaryPathBridgeRealization
    (hrealize : AuxiliaryPathBridgeRealizationInput.{u}) :
    AuxiliaryTreeExtractionInput.{u} := by
  intro V _ _ G A B h q _hh _hq L htree
  classical
  rcases exists_leafIndexSet_card_eq_of_hasSpanningTreeWithAtLeastLeaves
      (linkageAuxGraph L) htree with
    ⟨T, hTH, hTtree, I, hIcard, hIleaf⟩
  let Q : PathPacking G A B := L.toPathPacking.restrictIndexSet I
  refine ⟨Q, ?_, ?_⟩
  · simpa [Q, hIcard]
  · intro i j hij
    rcases exists_auxiliaryPath_internallyDisjoint_leafSet
        (G := G) (A := A) (B := B)
        L hTH hTtree hIleaf i.1 j.1 with
      ⟨R, hRsource, hRtarget, hRclean⟩
    exact hrealize G L I hij R hRsource hRtarget hRclean

/-- Restricting a path packing to a subfamily only removes path vertices. -/
theorem restrictIndexSet_vertexSet_subset
    (P : PathPacking G A B) (I : Finset P.Index) :
    (P.restrictIndexSet I).vertexSet ⊆ P.vertexSet := by
  classical
  intro v hv
  rw [PathPacking.mem_vertexSet] at hv ⊢
  rcases hv with ⟨i, hvi⟩
  exact ⟨i.1, by simpa using hvi⟩

/-- A bridge between two retained paths remains a bridge after restricting the
packing to the retained index set. -/
def bridgeBetween_restrictIndexSet
    (P : PathPacking G A B) (I : Finset P.Index)
    {i j : (P.restrictIndexSet I).Index}
    (β : P.BridgeBetween i.1 j.1) :
    (P.restrictIndexSet I).BridgeBetween i j where
  path := β.path
  connects := by
    simpa [PathPacking.restrictIndexSet] using β.connects
  internallyDisjoint := by
    intro v hv hQ
    exact β.internallyDisjoint hv
      (restrictIndexSet_vertexSet_subset P I hQ)

/-- A reversed bridge between two retained paths remains a bridge after
restriction, since bridge orientation is immaterial. -/
def bridgeBetween_restrictIndexSet_comm
    (P : PathPacking G A B) (I : Finset P.Index)
    {i j : (P.restrictIndexSet I).Index}
    (β : P.BridgeBetween j.1 i.1) :
    (P.restrictIndexSet I).BridgeBetween i j where
  path := β.path
  connects := by
    have hconn :
        β.path.Connects (P.path i.1).vertexSet (P.path j.1).vertexSet :=
      (GraphPath.connects_comm β.path (P.path j.1).vertexSet
        (P.path i.1).vertexSet).mp β.connects
    simpa [PathPacking.restrictIndexSet] using hconn
  internallyDisjoint := by
    intro v hv hQ
    exact β.internallyDisjoint hv
      (restrictIndexSet_vertexSet_subset P I hQ)

/-- An auxiliary adjacency contains an actual bridge in either direction, and
therefore in the requested direction after reversing if necessary. -/
theorem nonempty_bridgeBetween_of_linkageAuxAdj
    (L : PerfectPathPacking G A B) {i j : L.Index}
    (hadj : (linkageAuxGraph L).Adj i j) :
    Nonempty (L.toPathPacking.BridgeBetween i j) := by
  classical
  rcases hadj.2 with hβ | hβ
  · exact hβ
  · rcases hβ with ⟨β⟩
    exact ⟨{
      path := β.path
      connects := by
        exact (GraphPath.connects_comm β.path
          (L.path j).vertexSet (L.path i).vertexSet).mp β.connects
      internallyDisjoint := β.internallyDisjoint
    }⟩

/-- Choose a bridge witnessing an auxiliary adjacency, oriented in the
requested direction. -/
noncomputable def bridgeBetween_of_linkageAuxAdj
    (L : PerfectPathPacking G A B) {i j : L.Index}
    (hadj : (linkageAuxGraph L).Adj i j) :
    L.toPathPacking.BridgeBetween i j :=
  Classical.choice (nonempty_bridgeBetween_of_linkageAuxAdj L hadj)

/-- A vertex on an unretained path is not in the restricted packing. -/
theorem not_mem_restrictIndexSet_vertexSet_of_mem_unretained_path
    (P : PathPacking G A B) (I : Finset P.Index)
    {k : P.Index} (hk : k ∉ I) {v : V}
    (hv : v ∈ (P.path k).vertexSet) :
    v ∉ (P.restrictIndexSet I).vertexSet := by
  classical
  intro hvQ
  rcases (P.restrictIndexSet I).mem_vertexSet.1 hvQ with ⟨r, hvr⟩
  have hkr : k ≠ r.1 := by
    intro h
    exact hk (by simpa [h] using r.2)
  exact Finset.disjoint_left.mp (P.node_disjoint hkr) hv hvr

/-- Any path contained in an unretained linkage path is disjoint from the
restricted packing. -/
theorem disjoint_restrictIndexSet_vertexSet_of_subset_unretained_path
    (P : PathPacking G A B) (I : Finset P.Index)
    {k : P.Index} (hk : k ∉ I) {R : GraphPath G}
    (hR : R.vertexSet ⊆ (P.path k).vertexSet) :
    Disjoint R.vertexSet (P.restrictIndexSet I).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvR hvQ
  exact not_mem_restrictIndexSet_vertexSet_of_mem_unretained_path
    P I hk (hR hvR) hvQ

/-- Any path contained in an unretained linkage path is internally disjoint
from the restricted packing. -/
theorem internallyDisjoint_restrictIndexSet_of_subset_unretained_path
    (P : PathPacking G A B) (I : Finset P.Index)
    {k : P.Index} (hk : k ∉ I) {R : GraphPath G}
    (hR : R.vertexSet ⊆ (P.path k).vertexSet) :
    R.InternallyDisjointFromSet (P.restrictIndexSet I).vertexSet := by
  intro v hvR hvQ
  exact False.elim
    (Finset.disjoint_left.mp
      (disjoint_restrictIndexSet_vertexSet_of_subset_unretained_path
        P I hk hR) hvR hvQ)

/-- An oriented full-linkage bridge remains internally clean with respect to
any restricted subpacking. -/
theorem orientedBridge_internallyDisjoint_restrictIndexSet
    (P : PathPacking G A B) (I : Finset P.Index)
    {i j : P.Index} (β : P.BridgeBetween i j) :
    β.orientedPath.InternallyDisjointFromSet
      (P.restrictIndexSet I).vertexSet := by
  intro v hv hvQ
  exact β.orientedPath_internallyDisjoint hv
    (restrictIndexSet_vertexSet_subset P I hvQ)

/-- A realized auxiliary chain from linkage path `a` to linkage path `b`.

The realizing path starts on linkage path `a`, ends on linkage path `b`, and is
internally disjoint from the retained restricted packing. -/
structure BridgeChainRealization
    (P : PathPacking G A B) (I : Finset P.Index) (a b : P.Index) where
  path : GraphPath G
  source_mem : path.source ∈ (P.path a).vertexSet
  target_mem : path.target ∈ (P.path b).vertexSet
  clean : path.InternallyDisjointFromSet (P.restrictIndexSet I).vertexSet

namespace BridgeChainRealization

/-- A full-linkage bridge is a one-edge realized auxiliary chain. -/
noncomputable def ofBridge
    (P : PathPacking G A B) (I : Finset P.Index)
    {a b : P.Index} (β : P.BridgeBetween a b) :
    BridgeChainRealization P I a b where
  path := β.orientedPath
  source_mem := β.orientedPath_source_mem_left
  target_mem := β.orientedPath_target_mem_right
  clean := orientedBridge_internallyDisjoint_restrictIndexSet P I β

/-- An auxiliary-graph adjacency is a one-edge realized auxiliary chain. -/
noncomputable def ofAuxAdj
    (L : PerfectPathPacking G A B) (I : Finset L.Index)
    {a b : L.Index} (hadj : (linkageAuxGraph L).Adj a b) :
    BridgeChainRealization L.toPathPacking I a b :=
  ofBridge L.toPathPacking I (bridgeBetween_of_linkageAuxAdj L hadj)

/-- The recursive adjacency condition for an explicit list of intermediate
auxiliary indices.  `AuxIndexListConnects L a b [x₁, ..., xₙ]` means
`a--x₁--...--xₙ--b` is a walk in the linkage auxiliary graph. -/
def AuxIndexListConnects
    (L : PerfectPathPacking G A B) (a b : L.Index) :
    List L.Index → Prop
  | [] => (linkageAuxGraph L).Adj a b
  | x :: xs => (linkageAuxGraph L).Adj a x ∧
      AuxIndexListConnects L x b xs

/-- Realized chains concatenate through an unretained intermediate linkage
path.  The middle linkage path supplies the connector between the two chain
endpoints, and because its index is not retained this connector is disjoint
from the restricted packing. -/
noncomputable def trans_unretained
    (P : PathPacking G A B) (I : Finset P.Index)
    {a k b : P.Index} (R₁ : BridgeChainRealization P I a k)
    (R₂ : BridgeChainRealization P I k b) (hk : k ∉ I) :
    BridgeChainRealization P I a b := by
  classical
  let U : Finset V := (P.restrictIndexSet I).vertexSet
  let hSeg :
      ∃ S₀ : GraphPath G,
        S₀.Connects ({R₁.path.target} : Finset V) ({R₂.path.source} : Finset V) ∧
          S₀.vertexSet ⊆ (P.path k).vertexSet :=
    (P.path k).exists_segment_connects_of_mem_vertexSet
      R₁.target_mem R₂.source_mem
  let S₀ : GraphPath G := Classical.choose hSeg
  have hS₀conn :
      S₀.Connects ({R₁.path.target} : Finset V) ({R₂.path.source} : Finset V) :=
    (Classical.choose_spec hSeg).1
  have hS₀sub : S₀.vertexSet ⊆ (P.path k).vertexSet :=
    (Classical.choose_spec hSeg).2
  let S : GraphPath G := S₀.orientBetween hS₀conn
  have hS_source : S.source = R₁.path.target := by
    simpa [S] using GraphPath.orientBetween_source S₀ hS₀conn
  have hS_target : S.target = R₂.path.source := by
    simpa [S] using GraphPath.orientBetween_target S₀ hS₀conn
  have hSsub : S.vertexSet ⊆ (P.path k).vertexSet := by
    intro v hv
    exact hS₀sub (by simpa [S] using hv)
  have hSclean : S.InternallyDisjointFromSet U := by
    simpa [U] using
      internallyDisjoint_restrictIndexSet_of_subset_unretained_path P I hk hSsub
  have hglue₁ : R₁.path.target ∉ U := by
    simpa [U] using
      not_mem_restrictIndexSet_vertexSet_of_mem_unretained_path
        P I hk R₁.target_mem
  have hglue₂ : R₂.path.source ∉ U := by
    simpa [U] using
      not_mem_restrictIndexSet_vertexSet_of_mem_unretained_path
        P I hk R₂.source_mem
  let R₁S : GraphPath G :=
    R₁.path.appendWithEqToPath S (by simpa [hS_source])
  have hR₁Sclean : R₁S.InternallyDisjointFromSet U := by
    simpa [R₁S, U] using
      R₁.path.appendWithEqToPath_internallyDisjointFromSet S
        (by simpa [hS_source]) R₁.clean
        (by simpa [U] using hSclean)
        (by simpa [U] using hglue₁)
  have hR₁S_target : R₁S.target = R₂.path.source := by
    simpa [R₁S, hS_target]
  let R : GraphPath G :=
    R₁S.appendWithEqToPath R₂.path (by simpa [hR₁S_target])
  have hRclean : R.InternallyDisjointFromSet U := by
    simpa [R, U] using
      R₁S.appendWithEqToPath_internallyDisjointFromSet R₂.path
        (by simpa [hR₁S_target]) hR₁Sclean
        (by simpa [U] using R₂.clean)
        (by simpa [hR₁S_target, U] using hglue₂)
  exact {
    path := R
    source_mem := by
      simpa [R, R₁S] using R₁.source_mem
    target_mem := by
      simpa [R] using R₂.target_mem
    clean := by
      simpa [U] using hRclean
  }

/-- Realize an explicit auxiliary index chain whose intermediate indices are
not retained. -/
noncomputable def ofAuxIndexList
    (L : PerfectPathPacking G A B) (I : Finset L.Index)
    (a b : L.Index) :
    (mids : List L.Index) →
      AuxIndexListConnects L a b mids →
        (∀ x ∈ mids, x ∉ I) →
          BridgeChainRealization L.toPathPacking I a b
  | [], hadj, _hclean => ofAuxAdj L I hadj
  | x :: xs, hadj, hclean =>
      let R₁ : BridgeChainRealization L.toPathPacking I a x :=
        ofAuxAdj L I hadj.1
      let R₂ : BridgeChainRealization L.toPathPacking I x b :=
        ofAuxIndexList L I x b xs hadj.2
          (fun y hy => hclean y (by simp [hy]))
      trans_unretained L.toPathPacking I R₁ R₂
        (hclean x (by simp))

/-- Intermediate auxiliary indices read from a segment of a graph path by
walk position.  For a segment of `len` edges starting at `start`, the list is
the vertices at positions `start+1, ..., start+len-1`. -/
def auxGetVertMids
    (L : PerfectPathPacking G A B)
    (R : GraphPath (linkageAuxGraph L)) (start : ℕ) : ℕ → List L.Index
  | 0 => []
  | 1 => []
  | Nat.succ (Nat.succ n) =>
      R.walk.getVert (start + 1) ::
        auxGetVertMids L R (start + 1) (Nat.succ n)

/-- Consecutive `getVert` positions along an auxiliary graph path give the
recursive explicit chain condition. -/
theorem auxIndexListConnects_auxGetVertMids
    (L : PerfectPathPacking G A B)
    (R : GraphPath (linkageAuxGraph L)) :
    ∀ {start len : ℕ},
      0 < len →
        start + len ≤ R.walk.length →
          AuxIndexListConnects L (R.walk.getVert start)
            (R.walk.getVert (start + len))
            (auxGetVertMids L R start len) := by
  intro start len hpos hle
  induction len generalizing start with
  | zero =>
      omega
  | succ len ih =>
      cases len with
      | zero =>
          simp [auxGetVertMids]
          have hadj := R.walk.adj_getVert_succ (i := start) (by omega)
          simpa using hadj
      | succ n =>
          simp [auxGetVertMids]
          constructor
          · have hadj := R.walk.adj_getVert_succ (i := start) (by omega)
            simpa using hadj
          · have hle' : start + 1 + Nat.succ n ≤ R.walk.length := by
              omega
            have htarget :
                start + Nat.succ (Nat.succ n) =
                  start + 1 + Nat.succ n := by
              omega
            simpa [htarget] using
              ih (start := start + 1) (by omega) hle'

/-- An internal vertex of a clean auxiliary path is not a retained index. -/
theorem getVert_not_mem_of_internallyDisjoint_auxPath
    (L : PerfectPathPacking G A B) (I : Finset L.Index)
    (R : GraphPath (linkageAuxGraph L))
    (hclean : R.InternallyDisjointFromSet I)
    {p : ℕ} (hp0 : 0 < p) (hplt : p < R.walk.length) :
    R.walk.getVert p ∉ I := by
  classical
  intro hpI
  have hv : R.walk.getVert p ∈ R.vertexSet := by
    simp [GraphPath.vertexSet]
  rcases hclean hv hpI with hsource | htarget
  · have hget :
        R.walk.getVert p = R.walk.getVert 0 := by
      simpa using hsource
    have hp_eq_zero := R.isPath.getVert_injOn
      (by simp; omega : p ∈ {i : ℕ | i ≤ R.walk.length})
      (by simp : 0 ∈ {i : ℕ | i ≤ R.walk.length})
      hget
    omega
  · have hget :
        R.walk.getVert p = R.walk.getVert R.walk.length := by
      simpa using htarget
    have hp_eq_len := R.isPath.getVert_injOn
      (by simp; omega : p ∈ {i : ℕ | i ≤ R.walk.length})
      (by simp : R.walk.length ∈ {i : ℕ | i ≤ R.walk.length})
      hget
    omega

/-- All position-read intermediates of a clean auxiliary path are unretained.
-/
theorem auxGetVertMids_clean
    (L : PerfectPathPacking G A B) (I : Finset L.Index)
    (R : GraphPath (linkageAuxGraph L))
    (hclean : R.InternallyDisjointFromSet I) :
    ∀ {start len : ℕ},
      start + len ≤ R.walk.length →
        ∀ x ∈ auxGetVertMids L R start len, x ∉ I := by
  intro start len hle
  induction len generalizing start with
  | zero =>
      simp [auxGetVertMids]
  | succ len ih =>
      cases len with
      | zero =>
          simp [auxGetVertMids]
      | succ n =>
          intro x hx
          simp [auxGetVertMids] at hx
          rcases hx with hx | hx
          · subst x
            exact getVert_not_mem_of_internallyDisjoint_auxPath
              L I R hclean (by omega) (by omega)
          · exact ih (start := start + 1) (by omega) x hx

end BridgeChainRealization

/-- A realized auxiliary chain between two retained indices is exactly a
bridge for the restricted packing. -/
theorem exists_bridgeBetween_restrictIndexSet_of_chainRealization
    [Fintype V]
    (P : PathPacking G A B) (I : Finset P.Index)
    {i j : (P.restrictIndexSet I).Index}
    (R : BridgeChainRealization P I i.1 j.1) :
    ∃ β : (P.restrictIndexSet I).BridgeBetween i j,
      β.path.vertexSet ⊆ Finset.univ := by
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    (P.restrictIndexSet I) R.path ?_ ?_ R.clean, ?_⟩
  · simpa [PathPacking.restrictIndexSet] using R.source_mem
  · simpa [PathPacking.restrictIndexSet] using R.target_mem
  · intro v _hv
    exact Finset.mem_univ v

/-- An explicit auxiliary index chain with unretained internal indices gives a
bridge for the retained restricted packing. -/
theorem exists_bridgeBetween_restrictIndexSet_of_auxIndexList
    [Fintype V]
    (L : PerfectPathPacking G A B) (I : Finset L.Index)
    {i j : (L.toPathPacking.restrictIndexSet I).Index}
    (mids : List L.Index)
    (hadj : BridgeChainRealization.AuxIndexListConnects L i.1 j.1 mids)
    (hclean : ∀ x ∈ mids, x ∉ I) :
    ∃ β : (L.toPathPacking.restrictIndexSet I).BridgeBetween i j,
      β.path.vertexSet ⊆ Finset.univ :=
  exists_bridgeBetween_restrictIndexSet_of_chainRealization
    L.toPathPacking I
    (BridgeChainRealization.ofAuxIndexList L I i.1 j.1 mids hadj hclean)

/-- A clean auxiliary graph path realizes as a bridge of the retained
restricted packing. -/
theorem exists_bridgeBetween_restrictIndexSet_of_auxiliaryPath
    [Fintype V]
    (L : PerfectPathPacking G A B) (I : Finset L.Index)
    {i j : (L.toPathPacking.restrictIndexSet I).Index}
    (hij : i ≠ j)
    (R : GraphPath (linkageAuxGraph L))
    (hsource : R.source = i.1)
    (htarget : R.target = j.1)
    (hclean : R.InternallyDisjointFromSet I) :
    ∃ β : (L.toPathPacking.restrictIndexSet I).BridgeBetween i j,
      β.path.vertexSet ⊆ Finset.univ := by
  classical
  have hsource_ne_target : R.source ≠ R.target := by
    intro hst
    apply hij
    apply Subtype.ext
    calc
      i.1 = R.source := hsource.symm
      _ = R.target := hst
      _ = j.1 := htarget
  have hlen_pos : 0 < R.walk.length := by
    exact _root_.SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (R.walk_not_nil_of_source_ne_target hsource_ne_target)
  let mids : List L.Index :=
    BridgeChainRealization.auxGetVertMids L R 0 R.walk.length
  have hadj :
      BridgeChainRealization.AuxIndexListConnects L i.1 j.1 mids := by
    have hchain :=
      BridgeChainRealization.auxIndexListConnects_auxGetVertMids
        L R (start := 0) (len := R.walk.length) hlen_pos (by simp)
    simpa [mids, hsource, htarget] using hchain
  have hclean_mids : ∀ x ∈ mids, x ∉ I := by
    intro x hx
    exact BridgeChainRealization.auxGetVertMids_clean
      L I R hclean (start := 0) (len := R.walk.length) (by simp) x
      (by simpa [mids] using hx)
  exact exists_bridgeBetween_restrictIndexSet_of_auxIndexList
    L I mids hadj hclean_mids

/-- The bridge-chain realization input is fully discharged from clean
auxiliary paths. -/
theorem auxiliaryPathBridgeRealizationInput :
    AuxiliaryPathBridgeRealizationInput.{u} := by
  intro V _ _ G A B L I i j hij R hsource htarget hclean
  exact exists_bridgeBetween_restrictIndexSet_of_auxiliaryPath
    L I hij R hsource htarget hclean

/-- The auxiliary-tree extraction step is now fully discharged by realizing
each clean auxiliary-tree path as a bridge chain in the original graph. -/
theorem auxiliaryTreeExtractionInput :
    AuxiliaryTreeExtractionInput.{u} :=
  auxiliaryTreeExtractionInput_of_auxiliaryPathBridgeRealization
    auxiliaryPathBridgeRealizationInput

/-- Realize a clean two-edge auxiliary path through one unretained linkage
path as a bridge for the restricted packing. -/
theorem exists_bridgeBetween_restrictIndexSet_of_two_auxEdges
    [Fintype V]
    (L : PerfectPathPacking G A B) (I : Finset L.Index)
    {i j : (L.toPathPacking.restrictIndexSet I).Index}
    {k : L.Index} (hk : k ∉ I)
    (hik : (linkageAuxGraph L).Adj i.1 k)
    (hkj : (linkageAuxGraph L).Adj k j.1) :
    ∃ β : (L.toPathPacking.restrictIndexSet I).BridgeBetween i j,
      β.path.vertexSet ⊆ Finset.univ := by
  classical
  let P : PathPacking G A B := L.toPathPacking
  let U : Finset V := (P.restrictIndexSet I).vertexSet
  let β₁ : P.BridgeBetween i.1 k :=
    bridgeBetween_of_linkageAuxAdj (G := G) (A := A) (B := B) L hik
  let β₂ : P.BridgeBetween k j.1 :=
    bridgeBetween_of_linkageAuxAdj (G := G) (A := A) (B := B) L hkj
  let B₁ : GraphPath G := β₁.orientedPath
  let B₂ : GraphPath G := β₂.orientedPath
  have hB₁_target : B₁.target ∈ (P.path k).vertexSet := by
    simpa [B₁, β₁, P] using β₁.orientedPath_target_mem_right
  have hB₂_source : B₂.source ∈ (P.path k).vertexSet := by
    simpa [B₂, β₂, P] using β₂.orientedPath_source_mem_left
  rcases (P.path k).exists_segment_connects_of_mem_vertexSet
      hB₁_target hB₂_source with
    ⟨S₀, hS₀conn, hS₀sub⟩
  let S : GraphPath G :=
    S₀.orientBetween hS₀conn
  have hS_source : S.source = B₁.target := by
    simpa [S] using GraphPath.orientBetween_source S₀ hS₀conn
  have hS_target : S.target = B₂.source := by
    simpa [S] using GraphPath.orientBetween_target S₀ hS₀conn
  have hSsub : S.vertexSet ⊆ (P.path k).vertexSet := by
    intro v hv
    exact hS₀sub (by simpa [S] using hv)
  have hB₁clean : B₁.InternallyDisjointFromSet U := by
    simpa [B₁, U] using
      orientedBridge_internallyDisjoint_restrictIndexSet P I β₁
  have hB₂clean : B₂.InternallyDisjointFromSet U := by
    simpa [B₂, U] using
      orientedBridge_internallyDisjoint_restrictIndexSet P I β₂
  have hSclean : S.InternallyDisjointFromSet U := by
    simpa [U] using
      internallyDisjoint_restrictIndexSet_of_subset_unretained_path P I hk hSsub
  have hglue₁ : B₁.target ∉ U := by
    simpa [U] using
      not_mem_restrictIndexSet_vertexSet_of_mem_unretained_path
        P I hk hB₁_target
  have hglue₂ : B₂.source ∉ U := by
    simpa [U] using
      not_mem_restrictIndexSet_vertexSet_of_mem_unretained_path
        P I hk hB₂_source
  let B₁S : GraphPath G :=
    B₁.appendWithEqToPath S (by simpa [hS_source])
  have hB₁Sclean : B₁S.InternallyDisjointFromSet U := by
    simpa [B₁S] using
      B₁.appendWithEqToPath_internallyDisjointFromSet S
        (by simpa [hS_source]) hB₁clean hSclean hglue₁
  have hB₁S_target : B₁S.target = B₂.source := by
    simpa [B₁S, hS_target]
  have hB₁S_source_left : B₁S.source ∈ (P.path i.1).vertexSet := by
    simpa [B₁S, B₁, β₁, P] using β₁.orientedPath_source_mem_left
  let R : GraphPath G :=
    B₁S.appendWithEqToPath B₂ (by simpa [hB₁S_target])
  have hRclean : R.InternallyDisjointFromSet U := by
    simpa [R] using
      B₁S.appendWithEqToPath_internallyDisjointFromSet B₂
        (by simpa [hB₁S_target]) hB₁Sclean hB₂clean
        (by simpa [hB₁S_target] using hglue₂)
  have hRsource : R.source ∈ ((P.restrictIndexSet I).path i).vertexSet := by
    simpa [R, B₁S, P] using hB₁S_source_left
  have hRtarget : R.target ∈ ((P.restrictIndexSet I).path j).vertexSet := by
    simpa [R, B₂, β₂, P] using β₂.orientedPath_target_mem_right
  refine ⟨PathPacking.BridgeBetween.of_orientedPath
    (P.restrictIndexSet I) R hRsource hRtarget ?_, ?_⟩
  · simpa [U] using hRclean
  · intro v _hv
    exact Finset.mem_univ v

/-- Direct extraction from a clique in the linkage auxiliary graph.

If the chosen linkage indices are pairwise adjacent in `H(L)`, then the
corresponding subpacking has pairwise bridges.  This is the base bridge
extraction used in the spanning-tree leaf branch before concatenating bridge
chains along auxiliary-tree paths. -/
theorem exists_pathPacking_pairwiseBridges_of_auxiliaryClique
    [Fintype V]
    (L : PerfectPathPacking G A B) {q : ℕ} (I : Finset L.Index)
    (hIcard : I.card = q)
    (hpair :
      ∀ ⦃i j : L.Index⦄,
        i ∈ I → j ∈ I → i ≠ j → (linkageAuxGraph L).Adj i j) :
    ∃ Q : PathPacking G A B,
      Q.card = q ∧ Q.HasPairwiseBridgesIn Finset.univ := by
  classical
  let Q : PathPacking G A B := L.toPathPacking.restrictIndexSet I
  refine ⟨Q, ?_, ?_⟩
  · simpa [Q, hIcard]
  · intro i j hij
    have hadj : (linkageAuxGraph L).Adj i.1 j.1 :=
      hpair i.2 j.2 (by
        intro h
        exact hij (Subtype.ext h))
    rcases hadj.2 with hβ | hβ
    · rcases hβ with ⟨β⟩
      refine ⟨bridgeBetween_restrictIndexSet L.toPathPacking I β, ?_⟩
      intro v _hv
      exact Finset.mem_univ v
    · rcases hβ with ⟨β⟩
      refine ⟨bridgeBetween_restrictIndexSet_comm L.toPathPacking I β, ?_⟩
      intro v _hv
      exact Finset.mem_univ v

/-- Global Theorem 3.1 assembly from Appendix B.1 descent and the residual
good-linkage extraction step.

This is the proof-facing, source-routed form for the non-localized setting:
linked equal-size terminal sets in a connected graph either yield an `h x h`
grid minor or a `q`-path packing whose paths are pairwise bridged. -/
theorem exists_pathPacking_pairwiseBridges_or_gridMinor_of_theoremB1Statement_and_goodLinkageExtraction
    [Fintype V]
    (hB1 :
      ∀ L : PerfectPathPacking G A B,
        AppendixB1.TheoremB1Statement G h L)
    (hextract : GoodLinkageExtractionInput.{u})
    (hconn : G.Connected)
    (hlink : NodeLinkedIn G Finset.univ A B)
    (hcard : A.card = B.card)
    (hh : 1 < h)
    (hq : 1 < q)
    (hqcard : q ≤ A.card) :
    ContainsGridMinor G h ∨
      ∃ Q : PathPacking G A B,
        Q.card = q ∧ Q.StaysIn Finset.univ ∧
          Q.HasPairwiseBridgesIn Finset.univ := by
  classical
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq hlink hcard with
    ⟨L₀, _hL₀card, _hL₀stay⟩
  rcases exists_goodLinkage_or_gridMinor_of_theoremB1Statement
      (G := G) (A := A) (B := B) (h := h) hB1 hconn hlink hh L₀ with
    hgrid | ⟨Lgood, hgood⟩
  · exact Or.inl hgrid
  · have hqLgood : q ≤ Lgood.card := by
      rw [Lgood.card_eq_left_card]
      exact hqcard
    rcases hextract G hh hq Lgood hgood hqLgood with
      ⟨Q, hQcard, hQbridges⟩
    refine Or.inr ⟨Q, hQcard, ?_, hQbridges⟩
    intro i v _hv
    exact Finset.mem_univ v

/-- A good linkage whose auxiliary graph is connected and large has a spanning
tree with many leaves.

This is the Theorem 2.15 step in Chekuri--Chuzhoy Theorem 3.1 after Appendix
B.1 has removed all long degree-two auxiliary paths.  The cardinality
hypothesis is written with `8 * h + 1` because that is the current formal
definition of `GoodLinkage`. -/
theorem aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage
    [Fintype V]
    (L : PerfectPathPacking G A B)
    (hgood : GoodLinkage L h)
    (haux : (linkageAuxGraph L).Connected)
    {leaves : ℕ}
    (hleaves : 1 ≤ leaves)
    (hlarge :
      2 * leaves * ((8 * h + 1) + 5) ≤ Fintype.card L.Index) :
    HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph L) leaves := by
  classical
  rcases theorem215_tree_with_many_leaves_or_long_twoPath
      (linkageAuxGraph L) (L := leaves) (p := 8 * h + 1)
      haux hleaves (by omega) hlarge with htree | htwoPath
  · exact htree
  · exact False.elim (hgood htwoPath)

/-- Version of `aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage` using the
Appendix B.1 auxiliary-connectedness observation from the ambient graph. -/
theorem aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage_of_connected
    [Fintype V]
    (L : PerfectPathPacking G A B)
    (hgood : GoodLinkage L h)
    (hnonempty : Nonempty L.Index)
    (hconn : G.Connected)
    {leaves : ℕ}
    (hleaves : 1 ≤ leaves)
    (hlarge :
      2 * leaves * ((8 * h + 1) + 5) ≤ Fintype.card L.Index) :
    HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph L) leaves := by
  classical
  have haux : (linkageAuxGraph L).Connected :=
    AppendixB1.IndexedAuxiliaryPrefix.auxiliaryConnectedObservation_of_connected
      (G := G) L hnonempty hconn
  exact aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage
    (G := G) (A := A) (B := B) (h := h)
    L hgood haux hleaves hlarge

/-- Global Theorem 3.1 assembly reduced all the way to the auxiliary-tree
extraction step.

The route is:
1. choose an initial full linkage from node-linkedness;
2. use Appendix B.1 finite descent to get a good linkage or a grid minor;
3. use Theorem 2.15 on the connected auxiliary graph of the good linkage;
4. apply the remaining auxiliary-tree extraction input. -/
theorem exists_pathPacking_pairwiseBridges_or_gridMinor_of_theoremB1Statement_and_auxiliaryTreeExtraction
    [Fintype V]
    (hB1 :
      ∀ L : PerfectPathPacking G A B,
        AppendixB1.TheoremB1Statement G h L)
    (hextract : AuxiliaryTreeExtractionInput.{u})
    (hconn : G.Connected)
    (hlink : NodeLinkedIn G Finset.univ A B)
    (hcard : A.card = B.card)
    (hh : 1 < h)
    (hq : 1 < q)
    (hlarge :
      2 * q * ((8 * h + 1) + 5) ≤ A.card) :
    ContainsGridMinor G h ∨
      ∃ Q : PathPacking G A B,
        Q.card = q ∧ Q.StaysIn Finset.univ ∧
          Q.HasPairwiseBridgesIn Finset.univ := by
  classical
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq hlink hcard with
    ⟨L₀, _hL₀card, _hL₀stay⟩
  rcases exists_goodLinkage_or_gridMinor_of_theoremB1Statement
      (G := G) (A := A) (B := B) (h := h) hB1 hconn hlink hh L₀ with
    hgrid | ⟨Lgood, hgood⟩
  · exact Or.inl hgrid
  · have hnonempty : Nonempty Lgood.Index := by
      apply Fintype.card_pos_iff.mp
      change 0 < Lgood.card
      rw [Lgood.card_eq_left_card]
      have hprod_pos : 0 < 2 * q * ((8 * h + 1) + 5) := by
        have hqpos : 0 < q := by omega
        have hp_pos : 0 < (8 * h + 1) + 5 := by omega
        positivity
      exact lt_of_lt_of_le hprod_pos hlarge
    have hlargeL :
        2 * q * ((8 * h + 1) + 5) ≤ Fintype.card Lgood.Index := by
      change 2 * q * ((8 * h + 1) + 5) ≤ Lgood.card
      rw [Lgood.card_eq_left_card]
      exact hlarge
    have htree :
        HasSpanningTreeWithAtLeastLeaves (linkageAuxGraph Lgood) q :=
      aux_hasSpanningTreeWithAtLeastLeaves_of_goodLinkage_of_connected
        (G := G) (A := A) (B := B) (h := h)
        Lgood hgood hnonempty hconn (by omega) hlargeL
    rcases hextract G hh hq Lgood htree with
      ⟨Q, hQcard, hQbridges⟩
    refine Or.inr ⟨Q, hQcard, ?_, hQbridges⟩
    intro i v _hv
    exact Finset.mem_univ v

/-- Global Theorem 3.1 assembly from Appendix B.1 and Theorem 2.15, with the
auxiliary-tree bridge-chain step fully formalized in this file. -/
theorem exists_pathPacking_pairwiseBridges_or_gridMinor_of_theoremB1Statement
    [Fintype V]
    (hB1 :
      ∀ L : PerfectPathPacking G A B,
        AppendixB1.TheoremB1Statement G h L)
    (hconn : G.Connected)
    (hlink : NodeLinkedIn G Finset.univ A B)
    (hcard : A.card = B.card)
    (hh : 1 < h)
    (hq : 1 < q)
    (hlarge :
      2 * q * ((8 * h + 1) + 5) ≤ A.card) :
    ContainsGridMinor G h ∨
      ∃ Q : PathPacking G A B,
        Q.card = q ∧ Q.StaysIn Finset.univ ∧
          Q.HasPairwiseBridgesIn Finset.univ :=
  exists_pathPacking_pairwiseBridges_or_gridMinor_of_theoremB1Statement_and_auxiliaryTreeExtraction
    hB1 auxiliaryTreeExtractionInput hconn hlink hcard hh hq hlarge

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
