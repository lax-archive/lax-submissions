import Lax17Proofs.Source.ChekuriChuzhoyPendantTerminals
import Lax17Proofs.Source.ChekuriChuzhoySection5ClusterSkeleton

namespace Lax17Proofs

universe u v w

/-!
# The Phase 2 superterminal bridge

Chekuri--Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*, journal
Section 5.4.2, replaces each surviving router by a temporary superterminal.
The graph below retains the supplied old host graph and adds one superterminal
for every router index.  Superterminal `i` is adjacent exactly to `B i`.

Exact pairwise node-disjoint boundary packings become element-disjoint
superterminal packings.  Journal Theorem 5.10 can therefore be applied to the
augmented graph.  Its terminal-clean paths are stripped of their two
superterminal incidences and projected to the old host graph.

The paper obtains directness by pruning the Phase 2 host before adding the
superterminals.  Since that pruning is not encoded by the boundary sets alone,
the final producer below states the corresponding all-boundary-path
directness property explicitly.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Superterminals


open Finset
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {m mu : Nat}
variable {B cluster : Fin m -> Finset V}

/-! ## The finite simple augmentation -/

/-- Old host vertices together with one temporary superterminal per router. -/
inductive Vertex (V : Type u) (m : Nat) where
  | old : V -> Vertex V m
  | superterminal : Fin m -> Vertex V m
deriving DecidableEq

namespace Vertex

instance [Fintype V] : Fintype (Vertex V m) where
  elems :=
    (Finset.univ.image old) ∪
      (Finset.univ.image superterminal)
  complete := by
    intro z
    cases z <;> simp

/-- A directed presentation of old host edges and superterminal incidences.
`SimpleGraph.fromRel` supplies symmetry and removes loops. -/
def rel (G : _root_.SimpleGraph V) (B : Fin m -> Finset V) :
    Vertex V m -> Vertex V m -> Prop
  | old x, old y => G.Adj x y
  | superterminal i, old x => x ∈ B i
  | _, _ => False

/-- Add one superterminal adjacent exactly to each supplied boundary set. -/
def graph (G : _root_.SimpleGraph V) (B : Fin m -> Finset V) :
    _root_.SimpleGraph (Vertex V m) :=
  _root_.SimpleGraph.fromRel (rel G B)

@[simp] theorem graph_adj
    {a b : Vertex V m} :
    (graph G B).Adj a b ↔
      a ≠ b ∧ (rel G B a b ∨ rel G B b a) :=
  Iff.rfl

@[simp] theorem adj_old_old_iff {x y : V} :
    (graph G B).Adj (old x) (old y) ↔ G.Adj x y := by
  rw [graph_adj]
  constructor
  · rintro ⟨_hne, hxy | hyx⟩
    · exact hxy
    · exact hyx.symm
  · intro hxy
    exact ⟨by
      intro h
      cases h
      exact hxy.ne rfl,
      Or.inl hxy⟩

@[simp] theorem adj_superterminal_iff
    (i : Fin m) {z : Vertex V m} :
    (graph G B).Adj (superterminal i) z ↔
      ∃ x ∈ B i, z = old x := by
  cases z with
  | old x =>
      simp only [graph_adj, rel]
      constructor
      · rintro ⟨_hne, hx | hfalse⟩
        · exact ⟨x, hx, rfl⟩
        · exact False.elim hfalse
      · rintro ⟨y, hy, hxy⟩
        cases hxy
        exact ⟨by simp, Or.inl hy⟩
  | superterminal j =>
      simp [graph_adj, rel]

@[simp] theorem adj_old_superterminal_iff
    (i : Fin m) {x : V} :
    (graph G B).Adj (old x) (superterminal i) ↔ x ∈ B i := by
  rw [(graph G B).adj_comm, adj_superterminal_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    injection hxy with h
    simpa [h] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

@[simp] theorem not_adj_superterminal_superterminal
    (i j : Fin m) :
    ¬(graph G B).Adj (superterminal i) (superterminal j) := by
  simp [graph_adj, rel]

/-- The old-copy inclusion is an injective graph homomorphism. -/
def oldHom (G : _root_.SimpleGraph V) (B : Fin m -> Finset V) :
    G →g graph G B where
  toFun := old
  map_rel' := by
    intro x y hxy
    exact adj_old_old_iff.mpr hxy

theorem old_injective :
    Function.Injective (old : V -> Vertex V m) := by
  intro x y hxy
  injection hxy

/-- A temporary superterminal has exactly its prescribed boundary set as
its old-copy neighborhood. -/
theorem neighborSet_superterminal_ncard
    (G : _root_.SimpleGraph V) (B : Fin m -> Finset V) (i : Fin m) :
    ((graph G B).neighborSet (superterminal i)).ncard = (B i).card := by
  classical
  letI := Classical.decRel (graph G B).Adj
  have hneighbors :
      (graph G B).neighborFinset (superterminal i) =
        (B i).image (old (m := m)) := by
    ext z
    cases z with
    | old x =>
        simp [graph_adj, rel]
    | superterminal j =>
        simp [graph_adj, rel]
  calc
    ((graph G B).neighborSet (superterminal i)).ncard =
        ((graph G B).neighborFinset (superterminal i)).card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    _ = ((B i).image (old (m := m))).card :=
      congrArg Finset.card hneighbors
    _ = (B i).card :=
      Finset.card_image_of_injective _ (old_injective (V := V) (m := m))

/-- All temporary superterminals. -/
noncomputable def terminals : Finset (Vertex V m) :=
  Finset.univ.image superterminal

@[simp] theorem mem_terminals_superterminal (i : Fin m) :
    superterminal i ∈ terminals (V := V) (m := m) := by
  simp [terminals]

@[simp] theorem not_mem_terminals_old (x : V) :
    old (m := m) x ∉ terminals (V := V) (m := m) := by
  simp [terminals]

theorem exists_superterminal_of_mem_terminals
    {z : Vertex V m} (hz : z ∈ terminals (V := V) (m := m)) :
    ∃ i : Fin m, z = superterminal i := by
  rcases Finset.mem_image.mp hz with ⟨i, _hi, hiz⟩
  exact ⟨i, hiz.symm⟩

@[simp] theorem terminals_card :
    (terminals (V := V) (m := m)).card = m := by
  rw [terminals, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    injection hij

/-- The canonical terminal vertex associated with an index. -/
def terminalVertex (i : Fin m) :
    TerminalVertex (terminals (V := V) (m := m)) :=
  ⟨superterminal i, mem_terminals_superterminal i⟩

/-- Recover the router index represented by a terminal subtype. -/
noncomputable def terminalIndex
    (t : TerminalVertex (terminals (V := V) (m := m))) : Fin m :=
  Classical.choose (exists_superterminal_of_mem_terminals t.2)

theorem terminalIndex_spec
    (t : TerminalVertex (terminals (V := V) (m := m))) :
    t.1 = superterminal (terminalIndex t) :=
  Classical.choose_spec (exists_superterminal_of_mem_terminals t.2)

@[simp] theorem terminalIndex_terminalVertex (i : Fin m) :
    terminalIndex (terminalVertex (V := V) i) = i := by
  have h := terminalIndex_spec (terminalVertex (V := V) i)
  injection h with h
  exact h.symm

theorem terminalVertex_terminalIndex
    (t : TerminalVertex (terminals (V := V) (m := m))) :
    terminalVertex (V := V) (terminalIndex t) = t := by
  apply Subtype.ext
  exact (terminalIndex_spec t).symm

theorem terminalIndex_injective :
    Function.Injective
      (terminalIndex :
        TerminalVertex (terminals (V := V) (m := m)) -> Fin m) := by
  intro a b hab
  rw [← terminalVertex_terminalIndex a,
    ← terminalVertex_terminalIndex b, hab]

/-! ## Adding endpoint incidences to an old path -/

namespace GraphPath

/-- Map an old host path into the old-copy subgraph of the augmentation. -/
def mapOld (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    Lax17Proofs.SimpleGraph.GraphPath (graph G B) :=
  ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective P
    (oldHom G B) (old_injective (V := V) (m := m))

@[simp] theorem mapOld_source (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (mapOld (B := B) P).source = old P.source :=
  rfl

@[simp] theorem mapOld_target (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (mapOld (B := B) P).target = old P.target :=
  rfl

@[simp] theorem mapOld_vertexSet (P : Lax17Proofs.SimpleGraph.GraphPath G) :
    (mapOld (B := B) P).vertexSet =
      P.vertexSet.image (old (m := m)) := by
  exact
    ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective_vertexSet P
      (oldHom G B) (old_injective (V := V) (m := m))

/-- A one-edge path, reused for the two superterminal incidences. -/
noncomputable def ofAdj
    {H : _root_.SimpleGraph (Vertex V m)} {a b : Vertex V m}
    (hab : H.Adj a b) :
    Lax17Proofs.SimpleGraph.GraphPath H :=
  ChekuriChuzhoyPendantVertex.GraphPath.ofAdj hab

@[simp] theorem ofAdj_source
    {H : _root_.SimpleGraph (Vertex V m)} {a b : Vertex V m}
    (hab : H.Adj a b) :
    (ofAdj hab).source = a :=
  rfl

@[simp] theorem ofAdj_target
    {H : _root_.SimpleGraph (Vertex V m)} {a b : Vertex V m}
    (hab : H.Adj a b) :
    (ofAdj hab).target = b :=
  rfl

theorem ofAdj_vertexSet_subset_pair
    {H : _root_.SimpleGraph (Vertex V m)} {a b : Vertex V m}
    (hab : H.Adj a b) :
    (ofAdj hab).vertexSet ⊆ ({a, b} : Finset (Vertex V m)) :=
  ChekuriChuzhoyPendantVertex.GraphPath.ofAdj_vertexSet_subset_pair hab

/-- Add the two superterminal incidences to an oriented `B i`--`B j` path.
Cycle erasure is harmless here and avoids a separate concatenation
simplicity proof. -/
noncomputable def addSuperterminalEndpoints
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (i j : Fin m)
    (hsource : P.source ∈ B i) (htarget : P.target ∈ B j) :
    Lax17Proofs.SimpleGraph.GraphPath (graph G B) := by
  let L := ofAdj ((adj_superterminal_iff (G := G) (B := B) i).2
    ⟨P.source, hsource, rfl⟩)
  let M := mapOld (B := B) P
  let R := ofAdj ((adj_old_superterminal_iff (G := G) (B := B) j).2 htarget)
  let LM := L.appendWithEqToPath M (by simp [L, M])
  exact LM.appendWithEqToPath R (by simp [LM, L, M, R])

@[simp] theorem addSuperterminalEndpoints_source
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (i j : Fin m)
    (hsource : P.source ∈ B i) (htarget : P.target ∈ B j) :
    (addSuperterminalEndpoints P i j hsource htarget).source =
      superterminal i := by
  simp [addSuperterminalEndpoints]

@[simp] theorem addSuperterminalEndpoints_target
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (i j : Fin m)
    (hsource : P.source ∈ B i) (htarget : P.target ∈ B j) :
    (addSuperterminalEndpoints P i j hsource htarget).target =
      superterminal j := by
  simp [addSuperterminalEndpoints]

/-- Every vertex of an endpoint-augmented path is one of the two
superterminals or an old copy of a vertex of the input path. -/
theorem addSuperterminalEndpoints_vertex_classification
    (P : Lax17Proofs.SimpleGraph.GraphPath G) (i j : Fin m)
    (hsource : P.source ∈ B i) (htarget : P.target ∈ B j)
    {z : Vertex V m}
    (hz : z ∈
      (addSuperterminalEndpoints P i j hsource htarget).vertexSet) :
    z = superterminal i ∨ z = superterminal j ∨
      ∃ x ∈ P.vertexSet, z = old x := by
  classical
  let hL := (adj_superterminal_iff (G := G) (B := B) i).2
    ⟨P.source, hsource, rfl⟩
  let hR := (adj_old_superterminal_iff (G := G) (B := B) j).2 htarget
  let L := ofAdj hL
  let M := mapOld (B := B) P
  let R := ofAdj hR
  let LM := L.appendWithEqToPath M (by simp [L, M])
  have hzLMR :
      z ∈ LM.vertexSet ∪ R.vertexSet := by
    exact LM.appendWithEqToPath_vertexSet_subset R
      (by simp [LM, L, M, R]) (by
        simpa [addSuperterminalEndpoints, hL, hR, L, M, R, LM] using hz)
  rcases Finset.mem_union.mp hzLMR with hzLM | hzR
  · have hzLM' : z ∈ L.vertexSet ∪ M.vertexSet :=
      L.appendWithEqToPath_vertexSet_subset M (by simp [L, M]) hzLM
    rcases Finset.mem_union.mp hzLM' with hzL | hzM
    · have hzPair := ofAdj_vertexSet_subset_pair hL hzL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
      rcases hzPair with hzTerminal | hzOld
      · exact Or.inl hzTerminal
      · exact Or.inr (Or.inr
          ⟨P.source, P.source_mem_vertexSet, hzOld⟩)
    · rw [mapOld_vertexSet] at hzM
      rcases Finset.mem_image.mp hzM with ⟨x, hx, hzx⟩
      exact Or.inr (Or.inr ⟨x, hx, hzx.symm⟩)
  · have hzPair := ofAdj_vertexSet_subset_pair hR hzR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
    rcases hzPair with hzOld | hzTerminal
    · exact Or.inr (Or.inr
        ⟨P.target, P.target_mem_vertexSet, hzOld⟩)
    · exact Or.inr (Or.inl hzTerminal)

end GraphPath

/-! ## Pairwise boundary packings give terminal element-connectivity -/

private theorem edge_fst_mem_vertexSet
    {W : Type*} [DecidableEq W] {H : _root_.SimpleGraph W}
    (P : Lax17Proofs.SimpleGraph.GraphPath H) {x y : W}
    (hxy : s(x, y) ∈ P.edgeSet) :
    x ∈ P.vertexSet := by
  have hwalk : s(x, y) ∈ P.walk.edges :=
    List.mem_toFinset.mp (by simpa [Lax17Proofs.SimpleGraph.GraphPath.edgeSet] using hxy)
  simpa [Lax17Proofs.SimpleGraph.GraphPath.vertexSet] using
    P.walk.fst_mem_support_of_mem_edges hwalk

private theorem edge_snd_mem_vertexSet
    {W : Type*} [DecidableEq W] {H : _root_.SimpleGraph W}
    (P : Lax17Proofs.SimpleGraph.GraphPath H) {x y : W}
    (hxy : s(x, y) ∈ P.edgeSet) :
    y ∈ P.vertexSet := by
  have hwalk : s(x, y) ∈ P.walk.edges :=
    List.mem_toFinset.mp (by simpa [Lax17Proofs.SimpleGraph.GraphPath.edgeSet] using hxy)
  simpa [Lax17Proofs.SimpleGraph.GraphPath.vertexSet] using
    P.walk.snd_mem_support_of_mem_edges hwalk

/-- Orient a boundary packing and add its common superterminal endpoints. -/
noncomputable def augmentedPackingPath
    {i j : Fin m} (P : PathPacking G (B i) (B j)) (p : P.Index) :
    Lax17Proofs.SimpleGraph.GraphPath (Vertex.graph G B) := by
  let Q := (P.path p).orient (P.connects p)
  exact Vertex.GraphPath.addSuperterminalEndpoints Q i j
    ((P.path p).orient_source_mem (P.connects p))
    ((P.path p).orient_target_mem (P.connects p))

@[simp] theorem augmentedPackingPath_source
    {i j : Fin m} (P : PathPacking G (B i) (B j)) (p : P.Index) :
    (augmentedPackingPath P p).source = Vertex.superterminal i := by
  simp [augmentedPackingPath]

@[simp] theorem augmentedPackingPath_target
    {i j : Fin m} (P : PathPacking G (B i) (B j)) (p : P.Index) :
    (augmentedPackingPath P p).target = Vertex.superterminal j := by
  simp [augmentedPackingPath]

theorem common_vertex_of_augmentedPackingPath_mem_terminals
    {i j : Fin m} (P : PathPacking G (B i) (B j))
    {p q : P.Index} (hpq : p ≠ q) {z : Vertex V m}
    (hzp : z ∈ (augmentedPackingPath P p).vertexSet)
    (hzq : z ∈ (augmentedPackingPath P q).vertexSet) :
    z ∈ Vertex.terminals (V := V) (m := m) := by
  classical
  let Pp := (P.path p).orient (P.connects p)
  let Pq := (P.path q).orient (P.connects q)
  have hpClass :=
    Vertex.GraphPath.addSuperterminalEndpoints_vertex_classification
      Pp i j ((P.path p).orient_source_mem (P.connects p))
        ((P.path p).orient_target_mem (P.connects p))
      (by simpa [augmentedPackingPath, Pp] using hzp)
  rcases hpClass with hpTerminal | hpTerminal | ⟨x, hxp, hzx⟩
  · simpa [hpTerminal] using
      Vertex.mem_terminals_superterminal (V := V) i
  · simpa [hpTerminal] using
      Vertex.mem_terminals_superterminal (V := V) j
  · have hqClass :=
      Vertex.GraphPath.addSuperterminalEndpoints_vertex_classification
        Pq i j ((P.path q).orient_source_mem (P.connects q))
          ((P.path q).orient_target_mem (P.connects q))
        (by simpa [augmentedPackingPath, Pq] using hzq)
    rcases hqClass with hqTerminal | hqTerminal | ⟨y, hyq, hzy⟩
    · simpa [hqTerminal] using
        Vertex.mem_terminals_superterminal (V := V) i
    · simpa [hqTerminal] using
        Vertex.mem_terminals_superterminal (V := V) j
    · have hxy : x = y := by
        apply Vertex.old_injective (m := m)
        exact hzx.symm.trans hzy
      have hdisjoint := P.node_disjoint hpq
      exact False.elim (Finset.disjoint_left.mp hdisjoint
        (by simpa [Pp] using hxp)
        (by simpa [Pq, hxy] using hyq))

theorem augmentedPackingPath_edge_disjoint
    {i j : Fin m} (P : PathPacking G (B i) (B j))
    {p q : P.Index} (hpq : p ≠ q) :
    (augmentedPackingPath P p).EdgeDisjoint
      (augmentedPackingPath P q) := by
  classical
  rw [Lax17Proofs.SimpleGraph.GraphPath.EdgeDisjoint, Finset.disjoint_left]
  intro e hep heq
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxp : x ∈ (augmentedPackingPath P p).vertexSet :=
        edge_fst_mem_vertexSet (augmentedPackingPath P p) hep
      have hxq : x ∈ (augmentedPackingPath P q).vertexSet :=
        edge_fst_mem_vertexSet (augmentedPackingPath P q) heq
      have hyp : y ∈ (augmentedPackingPath P p).vertexSet :=
        edge_snd_mem_vertexSet (augmentedPackingPath P p) hep
      have hyq : y ∈ (augmentedPackingPath P q).vertexSet :=
        edge_snd_mem_vertexSet (augmentedPackingPath P q) heq
      have hxTerminal :=
        common_vertex_of_augmentedPackingPath_mem_terminals P hpq hxp hxq
      have hyTerminal :=
        common_vertex_of_augmentedPackingPath_mem_terminals P hpq hyp hyq
      rcases Vertex.exists_superterminal_of_mem_terminals hxTerminal with
        ⟨a, rfl⟩
      rcases Vertex.exists_superterminal_of_mem_terminals hyTerminal with
        ⟨b, rfl⟩
      have hadj :
          (Vertex.graph G B).Adj
            (Vertex.superterminal a) (Vertex.superterminal b) :=
        Lax17Proofs.SimpleGraph.GraphPath.edgeSet_subset_edgeSet
          (augmentedPackingPath P p) hep
      exact Vertex.not_adj_superterminal_superterminal a b hadj

/-- A node-disjoint boundary packing becomes an element-disjoint packing
between the corresponding superterminals. -/
noncomputable def terminalElementPackingOfPathPacking
    {i j : Fin m} (P : PathPacking G (B i) (B j)) :
    TerminalElementPathPacking
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m))
      (Vertex.terminalVertex (V := V) i)
      (Vertex.terminalVertex (V := V) j) where
  Index := P.Index
  path := augmentedPackingPath P
  source_eq := by
    intro p
    exact augmentedPackingPath_source P p
  target_eq := by
    intro p
    exact augmentedPackingPath_target P p
  edge_disjoint := by
    intro p q hpq
    exact augmentedPackingPath_edge_disjoint P hpq
  nonterminal_disjoint := by
    intro p q hpq z hzp hzq
    exact common_vertex_of_augmentedPackingPath_mem_terminals
      P hpq hzp hzq

@[simp] theorem terminalElementPackingOfPathPacking_card
    {i j : Fin m} (P : PathPacking G (B i) (B j)) :
    (terminalElementPackingOfPathPacking P).card = P.card :=
  rfl

/-- Exact pairwise node-disjoint boundary packings prove element-connectivity
of all temporary superterminals. -/
theorem terminalsElementConnectedAtLeast_of_pairwise_packings
    (hpacking :
      ∀ i j : Fin m, i ≠ j ->
        ∃ P : PathPacking G (B i) (B j), P.card = mu) :
    TerminalsElementConnectedAtLeast
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)) mu := by
  intro a b hab
  let i := Vertex.terminalIndex a
  let j := Vertex.terminalIndex b
  have hij : i ≠ j := by
    intro hij
    apply hab
    exact Vertex.terminalIndex_injective hij
  rcases hpacking i j hij with ⟨P, hPcard⟩
  have ha : Vertex.terminalVertex (V := V) i = a :=
    Vertex.terminalVertex_terminalIndex a
  have hb : Vertex.terminalVertex (V := V) j = b :=
    Vertex.terminalVertex_terminalIndex b
  rw [← ha, ← hb]
  exact ⟨terminalElementPackingOfPathPacking P, by simpa [hPcard]⟩

/-! ## Stripping and projecting terminal-clean paths -/

/-- The finite old-copy region of the augmentation. -/
noncomputable def oldRegion : Finset (Vertex V m) :=
  Finset.univ.image old

@[simp] theorem mem_oldRegion_old (x : V) :
    old (m := m) x ∈ oldRegion (V := V) (m := m) := by
  simp [oldRegion]

@[simp] theorem not_mem_oldRegion_superterminal (i : Fin m) :
    superterminal (V := V) i ∉ oldRegion (V := V) (m := m) := by
  simp [oldRegion]

/-- Predicate cutting out old-copy vertices. -/
def IsOld : Vertex V m -> Prop
  | old _ => True
  | superterminal _ => False

theorem mem_oldRegion_iff_isOld (z : Vertex V m) :
    z ∈ oldRegion (V := V) (m := m) ↔ IsOld z := by
  cases z <;> simp [IsOld]

/-- Forget the old-copy constructor. -/
def oldValue : {z : Vertex V m // IsOld z} -> V
  | ⟨old x, _⟩ => x

/-- Forget the old-copy constructor using an `oldRegion` certificate. -/
def oldRegionValue
    (z : {z : Vertex V m // z ∈ oldRegion (V := V) (m := m)}) : V :=
  oldValue ⟨z.1, (mem_oldRegion_iff_isOld z.1).mp z.2⟩

@[simp] theorem oldRegionValue_old (x : V) :
    oldRegionValue
      ⟨old (m := m) x, mem_oldRegion_old (m := m) x⟩ = x :=
  rfl

theorem old_oldRegionValue
    (z : {z : Vertex V m // z ∈ oldRegion (V := V) (m := m)}) :
    old (m := m) (oldRegionValue z) = z.1 := by
  cases z with
  | mk z hz =>
      cases z with
      | old x => rfl
      | superterminal i =>
          exact False.elim (not_mem_oldRegion_superterminal i hz)

/-- The old-copy induced graph projects homomorphically to `G`. -/
def oldRegionProjectionHom (G : _root_.SimpleGraph V) (B : Fin m -> Finset V) :
    (graph G B).induce
      {z : Vertex V m | z ∈ oldRegion (V := V) (m := m)} →g G where
  toFun := oldRegionValue
  map_rel' := by
    intro a b hab
    have hab' : (graph G B).Adj a.1 b.1 := by
      simpa using hab
    rw [← old_oldRegionValue a, ← old_oldRegionValue b] at hab'
    exact adj_old_old_iff.mp hab'

theorem oldRegionProjectionHom_injective
    (G : _root_.SimpleGraph V) (B : Fin m -> Finset V) :
    Function.Injective (oldRegionProjectionHom G B) := by
  intro a b hab
  apply Subtype.ext
  rw [← old_oldRegionValue a, ← old_oldRegionValue b]
  exact congrArg (old (m := m)) hab

namespace GraphPath

/-- Project a path known to stay in the old-copy region back to `G`. -/
noncomputable def projectOld
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (m := m)) :
    Lax17Proofs.SimpleGraph.GraphPath G :=
  ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective
    (P.induce (oldRegion (V := V) (m := m)) hP)
    (oldRegionProjectionHom G B)
    (oldRegionProjectionHom_injective G B)

@[simp] theorem projectOld_source
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (m := m)) :
    (projectOld P hP).source =
      oldRegionValue
        ⟨P.source, hP P.source_mem_vertexSet⟩ :=
  rfl

@[simp] theorem projectOld_target
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (m := m)) :
    (projectOld P hP).target =
      oldRegionValue
        ⟨P.target, hP P.target_mem_vertexSet⟩ :=
  rfl

theorem mem_projectOld_vertexSet_iff
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B))
    (hP : P.vertexSet ⊆ oldRegion (V := V) (m := m)) (x : V) :
    x ∈ (projectOld P hP).vertexSet ↔
      old (m := m) x ∈ P.vertexSet := by
  classical
  rw [projectOld,
    ChekuriChuzhoyPendantVertex.GraphPath.mapHomInjective_vertexSet]
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, hzx⟩
    have hzP : z.1 ∈ P.vertexSet :=
      (P.mem_induce_vertexSet _ hP z).mp hz
    have hval : old (m := m) x = z.1 := by
      rw [← old_oldRegionValue z]
      exact congrArg (old (m := m)) hzx.symm
    simpa [hval] using hzP
  · intro hx
    let z : {z : Vertex V m //
        z ∈ oldRegion (V := V) (m := m)} :=
      ⟨old (m := m) x, mem_oldRegion_old (m := m) x⟩
    exact Finset.mem_image.mpr
      ⟨z, (P.mem_induce_vertexSet _ hP z).mpr hx, by
        change oldRegionValue z = x
        apply old_injective (m := m)
        rw [old_oldRegionValue z]⟩

/-- Remove the first edge of a path by reversing, dropping its last edge, and
reversing back. -/
def dropFirst
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    Lax17Proofs.SimpleGraph.GraphPath (graph G B) :=
  P.reverse.dropLast.reverse

@[simp] theorem dropFirst_source
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    (dropFirst P).source = P.reverse.penultimate :=
  rfl

@[simp] theorem dropFirst_target
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    (dropFirst P).target = P.target :=
  rfl

theorem dropFirst_vertexSet_subset
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    (dropFirst P).vertexSet ⊆ P.vertexSet := by
  intro z hz
  have hz' : z ∈ P.reverse.dropLast.vertexSet := by
    simpa [dropFirst] using hz
  have hzRev : z ∈ P.reverse.vertexSet :=
    P.reverse.dropLast_vertexSet_subset hz'
  simpa using hzRev

/-- Remove both endpoint incidences from a path. -/
def stripSuperterminalEndpoints
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    Lax17Proofs.SimpleGraph.GraphPath (graph G B) :=
  (dropFirst P).dropLast

@[simp] theorem stripSuperterminalEndpoints_source
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    (stripSuperterminalEndpoints P).source = P.reverse.penultimate :=
  rfl

@[simp] theorem stripSuperterminalEndpoints_target
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    (stripSuperterminalEndpoints P).target = (dropFirst P).penultimate :=
  rfl

theorem stripSuperterminalEndpoints_vertexSet_subset_dropFirst
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    (stripSuperterminalEndpoints P).vertexSet ⊆
      (dropFirst P).vertexSet :=
  (dropFirst P).dropLast_vertexSet_subset

theorem stripSuperterminalEndpoints_vertexSet_subset
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) :
    (stripSuperterminalEndpoints P).vertexSet ⊆ P.vertexSet :=
  subset_trans (stripSuperterminalEndpoints_vertexSet_subset_dropFirst P)
    (dropFirst_vertexSet_subset P)

/-- The first old endpoint obtained after stripping belongs to the source
boundary. -/
theorem exists_source_boundary_of_superterminal_source
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) (i : Fin m)
    (hsource : P.source = superterminal i)
    (hne : P.source ≠ P.target) :
    ∃ x ∈ B i, (dropFirst P).source = old x := by
  have hrev : P.reverse.source ≠ P.reverse.target := by
    simpa using hne.symm
  have hadj :
      (graph G B).Adj (superterminal i) P.reverse.penultimate := by
    have h :=
      (P.reverse.penultimate_adj_target hrev).symm
    simpa [hsource] using h
  rcases (adj_superterminal_iff i).mp hadj with ⟨x, hx, hvalue⟩
  exact ⟨x, hx, by simpa using hvalue⟩

/-- The last old endpoint obtained after stripping belongs to the target
boundary. -/
theorem exists_target_boundary_of_superterminal_endpoints
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) (i j : Fin m)
    (hsource : P.source = superterminal i)
    (htarget : P.target = superterminal j)
    (hne : P.source ≠ P.target) :
    ∃ y ∈ B j, (stripSuperterminalEndpoints P).target = old y := by
  rcases exists_source_boundary_of_superterminal_source P i hsource hne with
    ⟨x, hx, hdropSource⟩
  have hdropNe : (dropFirst P).source ≠ (dropFirst P).target := by
    rw [hdropSource, dropFirst_target, htarget]
    intro h
    cases h
  have hadj :
      (graph G B).Adj
        (superterminal j) (dropFirst P).penultimate := by
    have h := ((dropFirst P).penultimate_adj_target hdropNe).symm
    simpa [htarget] using h
  rcases (adj_superterminal_iff j).mp hadj with ⟨y, hy, hvalue⟩
  exact ⟨y, hy, by simpa using hvalue⟩

/-- A terminal-clean path becomes entirely old after its two superterminal
endpoint incidences are removed. -/
theorem stripSuperterminalEndpoints_vertexSet_subset_oldRegion
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) (i j : Fin m)
    (hsource : P.source = superterminal i)
    (htarget : P.target = superterminal j)
    (hne : P.source ≠ P.target)
    (havoid :
      P.InternallyDisjointFromSet
        (terminals (V := V) (m := m))) :
    (stripSuperterminalEndpoints P).vertexSet ⊆
      oldRegion (V := V) (m := m) := by
  have hrev : P.reverse.source ≠ P.reverse.target := by
    simpa using hne.symm
  have hsourceNotDropFirst :
      P.source ∉ (dropFirst P).vertexSet := by
    have hnot := P.reverse.target_not_mem_dropLast_vertexSet hrev
    simpa [dropFirst] using hnot
  rcases exists_source_boundary_of_superterminal_source P i hsource hne with
    ⟨x, hx, hdropSource⟩
  have hdropNe : (dropFirst P).source ≠ (dropFirst P).target := by
    rw [hdropSource, dropFirst_target, htarget]
    intro h
    cases h
  have htargetNotStrip :
      P.target ∉ (stripSuperterminalEndpoints P).vertexSet := by
    have hnot := (dropFirst P).target_not_mem_dropLast_vertexSet hdropNe
    simpa [stripSuperterminalEndpoints] using hnot
  intro z hz
  cases z with
  | old y => exact mem_oldRegion_old y
  | superterminal k =>
      have hzP : superterminal k ∈ P.vertexSet :=
        stripSuperterminalEndpoints_vertexSet_subset P hz
      have hend :=
        havoid hzP (mem_terminals_superterminal k)
      rcases hend with hzSource | hzTarget
      · apply False.elim
        apply hsourceNotDropFirst
        have hzDrop :
            superterminal k ∈ (dropFirst P).vertexSet :=
          stripSuperterminalEndpoints_vertexSet_subset_dropFirst P hz
        simpa [hzSource] using hzDrop
      · exact False.elim (htargetNotStrip (by simpa [hzTarget] using hz))

/-- Strip the endpoint incidences of a terminal-clean superterminal path and
project the remaining old path to `G`.  Every projected vertex lifts to a
vertex of the original augmented path. -/
theorem exists_projected_of_superterminal_endpoints
    (P : Lax17Proofs.SimpleGraph.GraphPath (graph G B)) (i j : Fin m)
    (hsource : P.source = superterminal i)
    (htarget : P.target = superterminal j)
    (hne : P.source ≠ P.target)
    (havoid :
      P.InternallyDisjointFromSet
        (terminals (V := V) (m := m))) :
    ∃ Q : Lax17Proofs.SimpleGraph.GraphPath G,
      Q.source ∈ B i ∧ Q.target ∈ B j ∧
        ∀ x ∈ Q.vertexSet, old (m := m) x ∈ P.vertexSet := by
  rcases exists_source_boundary_of_superterminal_source P i hsource hne with
    ⟨a, ha, hstripSource⟩
  rcases exists_target_boundary_of_superterminal_endpoints P
      i j hsource htarget hne with
    ⟨b, hb, hstripTarget⟩
  let R := stripSuperterminalEndpoints P
  have hRold :
      R.vertexSet ⊆ oldRegion (V := V) (m := m) := by
    simpa [R] using
      stripSuperterminalEndpoints_vertexSet_subset_oldRegion P
        i j hsource htarget hne havoid
  rcases R.exists_segment_connects_of_mem_vertexSet
      R.source_mem_vertexSet R.target_mem_vertexSet with
    ⟨R0, hR0connects, hR0subset⟩
  let R' := R0.orient hR0connects
  have hR'source : R'.source = R.source := by
    have hmem := R0.orient_source_mem hR0connects
    simpa [R'] using hmem
  have hR'target : R'.target = R.target := by
    have hmem := R0.orient_target_mem hR0connects
    simpa [R'] using hmem
  have hR'subset : R'.vertexSet ⊆ R.vertexSet := by
    simpa [R'] using hR0subset
  have hR'old :
      R'.vertexSet ⊆ oldRegion (V := V) (m := m) :=
    subset_trans hR'subset hRold
  let Q := projectOld R' hR'old
  refine ⟨Q, ?_, ?_, ?_⟩
  · have hsourceValue :
        Q.source = a := by
      change oldRegionValue
        ⟨R'.source, hR'old R'.source_mem_vertexSet⟩ = a
      apply old_injective (m := m)
      rw [old_oldRegionValue]
      exact hR'source.trans (by simpa [R] using hstripSource)
    simpa [hsourceValue] using ha
  · have htargetValue :
        Q.target = b := by
      change oldRegionValue
        ⟨R'.target, hR'old R'.target_mem_vertexSet⟩ = b
      apply old_injective (m := m)
      rw [old_oldRegionValue]
      exact hR'target.trans (by simpa [R] using hstripTarget)
    simpa [htargetValue] using hb
  · intro x hx
    have hxR' : old (m := m) x ∈ R'.vertexSet :=
      (mem_projectOld_vertexSet_iff R' hR'old x).mp hx
    have hxR : old (m := m) x ∈ R.vertexSet :=
      hR'subset hxR'
    exact stripSuperterminalEndpoints_vertexSet_subset P
      (by simpa [R] using hxR)

end GraphPath

end Vertex

/-! ## Relabeling the terminal skeleton by cluster indices -/

/-- The directness supplied in the paper by pruning the Phase 2 host:
every oriented path between distinct boundary sets is internally disjoint
from every router cluster. -/
def BoundaryPathsDirect
    (G : _root_.SimpleGraph V)
    (cluster B : Fin m -> Finset V) : Prop :=
  ∀ ⦃i j : Fin m⦄, i ≠ j ->
    ∀ P : Lax17Proofs.SimpleGraph.GraphPath G,
      P.source ∈ B i -> P.target ∈ B j ->
        ∀ r : Fin m, P.InternallyDisjointFromSet (cluster r)

/-- Relabel a terminal multigraph by the unique index of each
superterminal.  Named edge copies and their orientation are unchanged. -/
noncomputable def projectTerminalGraph
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m))) :
    FiniteEdgeIndexedGraph (Fin m) where
  Edge := S.graph.Edge
  left := fun e => Vertex.terminalIndex (S.graph.left e)
  right := fun e => Vertex.terminalIndex (S.graph.right e)
  end_ne := by
    intro e heq
    exact S.graph.end_ne e (Vertex.terminalIndex_injective heq)

theorem terminalIndex_eq_iff
    (t : TerminalVertex (Vertex.terminals (V := V) (m := m)))
    (i : Fin m) :
    Vertex.terminalIndex t = i ↔
      t = Vertex.terminalVertex (V := V) i := by
  constructor
  · intro h
    apply Vertex.terminalIndex_injective
    simpa using h
  · rintro rfl
    simp

/-- Relabeling temporary terminals preserves each named-edge incidence
finset, and hence every multigraph degree. -/
theorem projectTerminalGraph_incidentEdges
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (i : Fin m) :
    (projectTerminalGraph S).incidentEdges i =
      S.graph.incidentEdges (Vertex.terminalVertex (V := V) i) := by
  ext e
  rw [(projectTerminalGraph S).mem_incidentEdges]
  constructor
  · intro he
    apply (S.graph.mem_incidentEdges
      (Vertex.terminalVertex (V := V) i) e).2
    change
      Vertex.terminalIndex (S.graph.left e) = i ∨
        Vertex.terminalIndex (S.graph.right e) = i at he
    rcases he with he | he
    · exact Or.inl ((terminalIndex_eq_iff (S.graph.left e) i).mp he)
    · exact Or.inr ((terminalIndex_eq_iff (S.graph.right e) i).mp he)
  · intro he
    have he' := (S.graph.mem_incidentEdges
      (Vertex.terminalVertex (V := V) i) e).1 he
    change
      Vertex.terminalIndex (S.graph.left e) = i ∨
        Vertex.terminalIndex (S.graph.right e) = i
    rcases he' with he' | he'
    · exact Or.inl ((terminalIndex_eq_iff (S.graph.left e) i).mpr he')
    · exact Or.inr ((terminalIndex_eq_iff (S.graph.right e) i).mpr he')

@[simp] theorem projectTerminalGraph_degree
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (i : Fin m) :
    (projectTerminalGraph S).degree i =
      S.graph.degree (Vertex.terminalVertex (V := V) i) := by
  exact congrArg Finset.card (projectTerminalGraph_incidentEdges S i)

@[simp] theorem terminalVertex_mem_image
    (X : Finset (Fin m)) (i : Fin m) :
    Vertex.terminalVertex (V := V) i ∈
        X.image (Vertex.terminalVertex (V := V)) ↔
      i ∈ X := by
  simp [Vertex.terminalVertex]

theorem terminal_mem_image_iff
    (X : Finset (Fin m))
    (t : TerminalVertex (Vertex.terminals (V := V) (m := m))) :
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
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (X : Finset (Fin m)) :
    (projectTerminalGraph S).boundary X =
      S.graph.boundary
        (X.image (Vertex.terminalVertex (V := V))) := by
  ext e
  rw [
    FiniteEdgeIndexedGraph.mem_boundary
      (projectTerminalGraph S) X e]
  constructor
  · intro he
    apply (S.graph.mem_boundary
      (X.image (Vertex.terminalVertex (V := V))) e).2
    change
      (Vertex.terminalIndex (S.graph.left e) ∈ X ∧
          Vertex.terminalIndex (S.graph.right e) ∉ X) ∨
        (Vertex.terminalIndex (S.graph.right e) ∈ X ∧
          Vertex.terminalIndex (S.graph.left e) ∉ X) at he
    simpa only [FiniteEdgeIndexedGraph.Crosses,
      terminal_mem_image_iff] using he
  · intro he
    have he' :=
      (S.graph.mem_boundary
        (X.image (Vertex.terminalVertex (V := V))) e).1 he
    change
      (Vertex.terminalIndex (S.graph.left e) ∈ X ∧
          Vertex.terminalIndex (S.graph.right e) ∉ X) ∨
        (Vertex.terminalIndex (S.graph.right e) ∈ X ∧
          Vertex.terminalIndex (S.graph.left e) ∉ X)
    simpa only [FiniteEdgeIndexedGraph.Crosses,
      terminal_mem_image_iff] using he'

/-- Terminal edge-connectivity is unchanged by relabeling the terminal
subtype with `Fin m`. -/
theorem projectTerminalGraph_isEdgeConnected
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    {k : Nat} (hconn : S.TerminalEdgeConnected k) :
    (projectTerminalGraph S).IsEdgeConnected k := by
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

/-- The old host path and endpoint data obtained from one terminal-skeleton
edge. -/
structure ProjectedHostPathData
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (e : S.graph.Edge) where
  path : Lax17Proofs.SimpleGraph.GraphPath G
  source_mem :
    path.source ∈ B (Vertex.terminalIndex (S.graph.left e))
  target_mem :
    path.target ∈ B (Vertex.terminalIndex (S.graph.right e))
  vertex_lifts :
    ∀ x ∈ path.vertexSet,
      Vertex.old (m := m) x ∈ (S.hostPath e).vertexSet

/-- The terminal-clean conclusion of Theorem 5.10 constructs the projected
old host path for each named terminal-skeleton edge. -/
theorem exists_projectedHostPathData
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (havoid : S.InternallyAvoidsTerminals)
    (e : S.graph.Edge) :
    Nonempty (ProjectedHostPathData S e) := by
  have hsource :
      (S.hostPath e).source =
        Vertex.superterminal
          (Vertex.terminalIndex (S.graph.left e)) := by
    calc
      (S.hostPath e).source = (S.graph.left e).1 :=
        S.host_source e
      _ = Vertex.superterminal
          (Vertex.terminalIndex (S.graph.left e)) :=
        Vertex.terminalIndex_spec (S.graph.left e)
  have htarget :
      (S.hostPath e).target =
        Vertex.superterminal
          (Vertex.terminalIndex (S.graph.right e)) := by
    calc
      (S.hostPath e).target = (S.graph.right e).1 :=
        S.host_target e
      _ = Vertex.superterminal
          (Vertex.terminalIndex (S.graph.right e)) :=
        Vertex.terminalIndex_spec (S.graph.right e)
  have hne :
      (S.hostPath e).source ≠ (S.hostPath e).target := by
    intro heq
    apply S.graph.end_ne e
    apply Subtype.ext
    exact (S.host_source e).symm.trans
      (heq.trans (S.host_target e))
  rcases
      Vertex.GraphPath.exists_projected_of_superterminal_endpoints
        (S.hostPath e)
        (Vertex.terminalIndex (S.graph.left e))
        (Vertex.terminalIndex (S.graph.right e))
        hsource htarget hne (havoid e) with
    ⟨P, hPsource, hPtarget, hPlifts⟩
  exact ⟨{
    path := P
    source_mem := hPsource
    target_mem := hPtarget
    vertex_lifts := hPlifts
  }⟩

/-- Choose the projected old host path data for one named edge. -/
noncomputable def projectedHostPathData
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (havoid : S.InternallyAvoidsTerminals)
    (e : S.graph.Edge) :
    ProjectedHostPathData S e :=
  Classical.choice (exists_projectedHostPathData S havoid e)

/-- Strip and project every path in a Theorem 5.10 terminal skeleton. -/
noncomputable def clusterPathSkeletonOfTerminalSkeleton
    (hinterface :
      ∀ i : Fin m, B i ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i))
    (hdirect : BoundaryPathsDirect G cluster B)
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (houtput : IsTheorem512Output
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)) mu S) :
    ChekuriChuzhoySection5ClusterSkeleton.ClusterPathSkeleton G cluster := by
  let data : ∀ e : S.graph.Edge, ProjectedHostPathData S e :=
    fun e => projectedHostPathData S
      houtput.internal_terminal_avoidance e
  exact {
    graph := projectTerminalGraph S
    hostPath := fun e => (data e).path
    host_source_mem := by
      intro e
      exact
        (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
          G (cluster (Vertex.terminalIndex (S.graph.left e))))
        (hinterface _ (data e).source_mem)
    host_target_mem := by
      intro e
      exact
        (ChekuriChuzhoySection5Clustering.interfaceVertices_subset
          G (cluster (Vertex.terminalIndex (S.graph.right e))))
        (hinterface _ (data e).target_mem)
    host_source_interface := by
      intro e
      exact hinterface _ (data e).source_mem
    host_target_interface := by
      intro e
      exact hinterface _ (data e).target_mem
    groups := S.groups
    internally_disjoint_clusters := by
      intro e r
      have hendNe :
          Vertex.terminalIndex (S.graph.left e) ≠
            Vertex.terminalIndex (S.graph.right e) :=
        (projectTerminalGraph S).end_ne e
      exact hdirect hendNe (data e).path
        (data e).source_mem (data e).target_mem r
    one_per_group_node_disjoint := by
      intro selected hselected e he f hf hef
      have hinter :
          (S.hostPath e).InternallyDisjoint (S.hostPath f) :=
        houtput.one_per_group_node_disjoint
          selected hselected he hf hef
      rw [Lax17Proofs.SimpleGraph.GraphPath.NodeDisjoint,
        Finset.disjoint_left]
      intro x hxe hxf
      have hxeOld :
          Vertex.old (m := m) x ∈ (S.hostPath e).vertexSet :=
        (data e).vertex_lifts x hxe
      have hxfOld :
          Vertex.old (m := m) x ∈ (S.hostPath f).vertexSet :=
        (data f).vertex_lifts x hxf
      have heEndpoint := (hinter hxeOld hxfOld).1
      rcases heEndpoint with heSource | heTarget
      · apply Vertex.not_mem_terminals_old (m := m) x
        rw [heSource]
        exact S.hostPath_source_mem_terminals e
      · apply Vertex.not_mem_terminals_old (m := m) x
        rw [heTarget]
        exact S.hostPath_target_mem_terminals e
  }

theorem clusterPathSkeletonOfTerminalSkeleton_groupSize
    (hinterface :
      ∀ i : Fin m, B i ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i))
    (hdirect : BoundaryPathsDirect G cluster B)
    (S : TerminalPathSkeleton
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)))
    (houtput : IsTheorem512Output
      (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)) mu S) :
    (clusterPathSkeletonOfTerminalSkeleton
      hinterface hdirect S houtput).GroupSizeAtMost m := by
  simpa [clusterPathSkeletonOfTerminalSkeleton,
    Vertex.terminals_card] using houtput.group_size

/-! ## The Phase 2 producer -/

/-- Phase 2 superterminal bridge.

The first hypothesis says that every boundary vertex is an actual interface
vertex of its represented cluster.  `hdirect` records the direct-path
property forced by the paper's pruned Phase 2 host.  The final hypothesis
supplies exact node-disjoint pairwise boundary packings; their directness is
an immediate instance of `hdirect`.

The output retains the `2 * mu` terminal edge-connectivity and the theorem's
groups, now of size at most the number `m` of represented clusters. -/
theorem exists_clusterPathSkeleton_of_pairwise_direct_packings
    (G : _root_.SimpleGraph V)
    (cluster B : Fin m -> Finset V) (mu : Nat)
    (hmu : 1 ≤ mu)
    (hinterface :
      ∀ i : Fin m, B i ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i))
    (hdirect : BoundaryPathsDirect G cluster B)
    (hpacking :
      ∀ i j : Fin m, i ≠ j ->
        ∃ P : PathPacking G (B i) (B j), P.card = mu) :
    ∃ S :
        ChekuriChuzhoySection5ClusterSkeleton.ClusterPathSkeleton G cluster,
      S.graph.IsEdgeConnected (2 * mu) ∧ S.GroupSizeAtMost m := by
  have hconn :
      TerminalsElementConnectedAtLeast
        (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)) mu :=
    Vertex.terminalsElementConnectedAtLeast_of_pairwise_packings hpacking
  rcases
      ChekuriChuzhoySection5TerminalSkeleton.theorem510
        (Vertex.graph G B) (Vertex.terminals (V := V) (m := m))
        mu hmu hconn with
    ⟨T, hT⟩
  let S :=
    clusterPathSkeletonOfTerminalSkeleton hinterface hdirect T hT
  refine ⟨S, ?_, ?_⟩
  · change (projectTerminalGraph T).IsEdgeConnected (2 * mu)
    exact projectTerminalGraph_isEdgeConnected T
      hT.terminal_edge_connected
  · change S.GroupSizeAtMost m
    exact clusterPathSkeletonOfTerminalSkeleton_groupSize
      hinterface hdirect T hT

/-- Phase 2 with the regularity conclusion used by Claim 5.17.

If every selected boundary has cardinality `mu`, Theorem 5.10 bounds the
degree of its temporary terminal by `2 * mu`.  The simultaneous
`2 * mu` edge-connectivity gives the reverse inequality at every vertex, so
the projected terminal multigraph is exactly regular. -/
theorem exists_regularClusterPathSkeleton_of_pairwise_direct_packings
    (G : _root_.SimpleGraph V)
    (cluster B : Fin m -> Finset V) (mu : Nat)
    (hm : 2 ≤ m) (hmu : 1 ≤ mu)
    (hBcard : ∀ i : Fin m, (B i).card = mu)
    (hinterface :
      ∀ i : Fin m, B i ⊆
        ChekuriChuzhoySection5Clustering.interfaceVertices G (cluster i))
    (hdirect : BoundaryPathsDirect G cluster B)
    (hpacking :
      ∀ i j : Fin m, i ≠ j ->
        ∃ P : PathPacking G (B i) (B j), P.card = mu) :
    ∃ S :
        ChekuriChuzhoySection5ClusterSkeleton.ClusterPathSkeleton G cluster,
      S.graph.IsEdgeConnected (2 * mu) ∧
        S.GroupSizeAtMost m ∧
          ∀ i : Fin m, S.graph.degree i = 2 * mu := by
  have hconn :
      TerminalsElementConnectedAtLeast
        (Vertex.graph G B) (Vertex.terminals (V := V) (m := m)) mu :=
    Vertex.terminalsElementConnectedAtLeast_of_pairwise_packings hpacking
  rcases
      ChekuriChuzhoySection5TerminalSkeleton.theorem510
        (Vertex.graph G B) (Vertex.terminals (V := V) (m := m))
        mu hmu hconn with
    ⟨T, hT⟩
  let S :=
    clusterPathSkeletonOfTerminalSkeleton hinterface hdirect T hT
  have hSconnected : S.graph.IsEdgeConnected (2 * mu) := by
    change (projectTerminalGraph T).IsEdgeConnected (2 * mu)
    exact projectTerminalGraph_isEdgeConnected T
      hT.terminal_edge_connected
  refine ⟨S, hSconnected, ?_, ?_⟩
  · change S.GroupSizeAtMost m
    exact clusterPathSkeletonOfTerminalSkeleton_groupSize
      hinterface hdirect T hT
  · intro i
    have hcardFin : 1 < Fintype.card (Fin m) := by
      simpa using hm
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcardFin i
    apply Nat.le_antisymm
    · change (projectTerminalGraph T).degree i ≤ 2 * mu
      rw [projectTerminalGraph_degree]
      calc
        T.graph.degree (Vertex.terminalVertex (V := V) i) ≤
            2 * ((Vertex.graph G B).neighborSet
              (Vertex.superterminal i)).ncard :=
          hT.terminal_degree (Vertex.terminalVertex (V := V) i)
        _ = 2 * mu := by
          rw [Vertex.neighborSet_superterminal_ncard, hBcard]
    · exact hSconnected.le_degree_of_exists_ne i ⟨j, hji⟩

end ChekuriChuzhoySection5Superterminals
end SimpleGraph

end Lax17Proofs
