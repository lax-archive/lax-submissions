import Lax17Proofs.Source.ChekuriChuzhoySection5Routers
import Lax17Proofs.Source.Menger
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5.4 router linking

At the start of journal Section 5.4 (JACM 63(5), Article 40), the routing from
each good router to the node-well-linked terminal set is combined with a
terminal-to-terminal routing.  The three path families have edge congestion at
most three.  In a host of maximum degree `Delta`, finite vertex-Menger then
gives a node-disjoint router-to-router packing with only a linear loss in
`Delta`.

The proof below uses the equivalent separator argument.  If `X` is a small
router-to-router separator, each outer edge-disjoint routing has more than
`|X|` distinct terminal endpoints reachable while avoiding `X`; otherwise all
of its paths could be charged to edges incident with `X` and those endpoints.
The two endpoint sets are disjoint, since a common endpoint would concatenate
two outer paths around `X`.  Node-well-linkedness routes the endpoint sets, and
one middle path avoids `X`, giving the final contradiction.  The fixed factor
eight leaves the natural-number division arithmetic explicit.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RouterLinking


open scoped Classical

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Terminal endpoints reached by paths of `P` whose full vertex sets avoid
`X`.  Paths are oriented from `S` to `T` before taking the endpoint. -/
private noncomputable def avoidingTerminalSet
    {S T : Finset V} (P : EdgePathPacking G S T) (X : Finset V) : Finset V :=
  (Finset.univ.filter fun i : P.Index => Disjoint (P.path i).vertexSet X).image
    fun i => (P.path i).orient (P.connects i) |>.target

omit [Fintype V] in
private theorem avoidingTerminalSet_subset
    {S T X : Finset V} (P : EdgePathPacking G S T) :
    avoidingTerminalSet P X ⊆ T := by
  classical
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨i, _hi, rfl⟩
  exact GraphPath.orient_target_mem (P.path i) (P.connects i)

omit [Fintype V] in
private theorem exists_avoiding_path_of_mem_avoidingTerminalSet
    {S T X : Finset V} (P : EdgePathPacking G S T) {t : V}
    (ht : t ∈ avoidingTerminalSet P X) :
    ∃ i : P.Index,
      Disjoint (P.path i).vertexSet X ∧
        ((P.path i).orient (P.connects i)).target = t := by
  classical
  rcases Finset.mem_image.mp ht with ⟨i, hi, hit⟩
  exact ⟨i, (Finset.mem_filter.mp hi).2, hit⟩

omit [Fintype V] in
/-- An edge-disjoint routing with more than `2 * Delta * |X|` paths reaches
more than `|X|` distinct terminal endpoints while avoiding `X`.

This is the capacity count used twice in the separator proof. -/
private theorem card_lt_avoidingTerminalSet
    {S T X : Finset V} {Delta : ℕ}
    (P : EdgePathPacking G S T)
    (hdegree : MaxDegreeAtMost G Delta)
    (hST : Disjoint S T)
    (hlarge : Delta * (2 * X.card) < P.card) :
    X.card < (avoidingTerminalSet P X).card := by
  classical
  by_contra hnot
  have hterminalCard : (avoidingTerminalSet P X).card ≤ X.card :=
    Nat.le_of_not_gt hnot
  have hpacking :
      P.card ≤ Delta * (X ∪ avoidingTerminalSet P X).card := by
    by_contra hnotPacking
    have hgt :
        Delta * (X ∪ avoidingTerminalSet P X).card < P.card :=
      Nat.lt_of_not_ge hnotPacking
    rcases
        Section46.EdgePathPacking.exists_path_vertexSet_disjoint_of_card_gt_degree_mul
          P hdegree hST hgt with
      ⟨i, hiAvoid⟩
    have hiAvoidX : Disjoint (P.path i).vertexSet X := by
      rw [Finset.disjoint_left] at hiAvoid ⊢
      intro v hvPath hvX
      exact hiAvoid hvPath (Finset.mem_union_left _ hvX)
    have hiTerminal :
        ((P.path i).orient (P.connects i)).target ∈
          avoidingTerminalSet P X := by
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiAvoidX⟩, rfl⟩
    have hiTargetPath :
        ((P.path i).orient (P.connects i)).target ∈
          (P.path i).vertexSet := by
      simpa using
        GraphPath.target_mem_vertexSet ((P.path i).orient (P.connects i))
    exact Finset.disjoint_left.mp hiAvoid hiTargetPath
      (Finset.mem_union_right X hiTerminal)
  have hunion :
      (X ∪ avoidingTerminalSet P X).card ≤ 2 * X.card := by
    calc
      (X ∪ avoidingTerminalSet P X).card
          ≤ X.card + (avoidingTerminalSet P X).card :=
        Finset.card_union_le _ _
      _ ≤ X.card + X.card := Nat.add_le_add_left hterminalCard _
      _ = 2 * X.card := by omega
  have hsmall : P.card ≤ Delta * (2 * X.card) :=
    hpacking.trans (Nat.mul_le_mul_left Delta hunion)
  exact (Nat.not_lt_of_ge hsmall) hlarge

private theorem degree_twice_separator_lt_routeValue
    {routeValue Delta x : ℕ}
    (hDelta : 0 < Delta)
    (hx : x < routeValue / (8 * Delta)) :
    Delta * (2 * x) < routeValue := by
  have hdenominator : 0 < 8 * Delta := Nat.mul_pos (by omega) hDelta
  have hxDiv : x + 1 ≤ routeValue / (8 * Delta) := by omega
  have hxMul : (x + 1) * (8 * Delta) ≤ routeValue :=
    (Nat.le_div_iff_mul_le hdenominator).mp hxDiv
  have hinside : 2 * x < 8 * (x + 1) := by omega
  have hscaled : Delta * (2 * x) < Delta * (8 * (x + 1)) :=
    Nat.mul_lt_mul_of_pos_left hinside hDelta
  have hreassociate :
      Delta * (8 * (x + 1)) = (x + 1) * (8 * Delta) := by
    ac_rfl
  exact hscaled.trans_le (by simpa [hreassociate] using hxMul)

/-- Chekuri--Chuzhoy Section 5.4, initial router-linking step.

Every distinct pair in a good-router family has at least
`routeValue / (8 * Delta)` pairwise node-disjoint connecting paths, provided
the common terminal set is node-well-linked and the host maximum degree is at
most the positive integer `Delta`. -/
theorem exists_routerPair_pathPacking
    {terminals : Finset V}
    {count w0 bandwidthCap alphaNum alphaDen routeValue Delta : ℕ}
    (R :
      ChekuriChuzhoySection5Routers.GoodRouterFamily
        G terminals count w0 bandwidthCap alphaNum alphaDen routeValue)
    (hterminals : NodeWellLinkedIn G Finset.univ terminals)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (i j : Fin count) (hij : i ≠ j) :
    ∃ P : PathPacking G (R.router i) (R.router j),
      routeValue / (8 * Delta) ≤ P.card := by
  classical
  have _hrouterDisjoint : Disjoint (R.router i) (R.router j) :=
    R.pairwise_disjoint hij
  let target := routeValue / (8 * Delta)
  rcases Menger.finite_vertex_menger_sharp
      G (R.router i) (R.router j) target with hpacking | hseparator
  · simpa [target] using hpacking
  · rcases hseparator with ⟨X, hXcard, hXsep⟩
    rcases
        EdgeMenger.exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn
          (R.good i).routes with
      ⟨Pi, hPiCard, _hPiStay⟩
    rcases
        EdgeMenger.exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn
          (R.good j).routes with
      ⟨Pj, hPjCard, _hPjStay⟩
    have hXcard' : X.card < routeValue / (8 * Delta) := by
      simpa [target] using hXcard
    have hlarge : Delta * (2 * X.card) < routeValue :=
      degree_twice_separator_lt_routeValue hDelta hXcard'
    let Ti := avoidingTerminalSet Pi X
    let Tj := avoidingTerminalSet Pj X
    have hTiSubset : Ti ⊆ terminals := by
      simpa [Ti] using avoidingTerminalSet_subset (X := X) Pi
    have hTjSubset : Tj ⊆ terminals := by
      simpa [Tj] using avoidingTerminalSet_subset (X := X) Pj
    have hTiCard : X.card < Ti.card := by
      apply card_lt_avoidingTerminalSet Pi hdegree (R.good i).terminal_disjoint
      simpa [hPiCard] using hlarge
    have hTjCard : X.card < Tj.card := by
      apply card_lt_avoidingTerminalSet Pj hdegree (R.good j).terminal_disjoint
      simpa [hPjCard] using hlarge
    have hTiTj : Disjoint Ti Tj := by
      rw [Finset.disjoint_left]
      intro t htTi htTj
      rcases exists_avoiding_path_of_mem_avoidingTerminalSet Pi
          (by simpa [Ti] using htTi) with
        ⟨a, haAvoid, haTarget⟩
      rcases exists_avoiding_path_of_mem_avoidingTerminalSet Pj
          (by simpa [Tj] using htTj) with
        ⟨b, hbAvoid, hbTarget⟩
      let Oi := (Pi.path a).orient (Pi.connects a)
      let Oj := (Pj.path b).orient (Pj.connects b)
      have hglue : Oi.target = Oj.reverse.source := by
        simpa [Oi, Oj] using haTarget.trans hbTarget.symm
      let Q := Oi.appendWithEqToPath Oj.reverse hglue
      have hQconnects : Q.Connects (R.router i) (R.router j) := by
        exact Or.inl
          ⟨by
            simpa [Q, Oi] using
              GraphPath.orient_source_mem (Pi.path a) (Pi.connects a),
           by
            simpa [Q, Oj] using
              GraphPath.orient_source_mem (Pj.path b) (Pj.connects b)⟩
      rcases hXsep Q hQconnects with ⟨v, hvQ, hvX⟩
      have hvPieces : v ∈ Oi.vertexSet ∪ Oj.reverse.vertexSet :=
        Oi.appendWithEqToPath_vertexSet_subset Oj.reverse hglue hvQ
      rcases Finset.mem_union.mp hvPieces with hvOi | hvOj
      · exact Finset.disjoint_left.mp haAvoid
          (by simpa [Oi] using hvOi) hvX
      · exact Finset.disjoint_left.mp hbAvoid
          (by simpa [Oj] using hvOj) hvX
    rcases hterminals.2 hTiSubset hTjSubset hTiTj with
      ⟨Pmid, hPmidCard, _hPmidStay⟩
    have hPmidLarge : X.card < Pmid.card := by
      rw [hPmidCard]
      exact lt_min hTiCard hTjCard
    rcases Section46.PathPacking.exists_path_vertexSet_disjoint_of_card_gt
        Pmid hPmidLarge with
      ⟨q, hqAvoid⟩
    let M := (Pmid.path q).orient (Pmid.connects q)
    have hMsourceTi : M.source ∈ Ti := by
      simpa [M] using
        GraphPath.orient_source_mem (Pmid.path q) (Pmid.connects q)
    have hMtargetTj : M.target ∈ Tj := by
      simpa [M] using
        GraphPath.orient_target_mem (Pmid.path q) (Pmid.connects q)
    rcases exists_avoiding_path_of_mem_avoidingTerminalSet Pi
        (by simpa [Ti] using hMsourceTi) with
      ⟨a, haAvoid, haTarget⟩
    rcases exists_avoiding_path_of_mem_avoidingTerminalSet Pj
        (by simpa [Tj] using hMtargetTj) with
      ⟨b, hbAvoid, hbTarget⟩
    let Oi := (Pi.path a).orient (Pi.connects a)
    let Oj := (Pj.path b).orient (Pj.connects b)
    have hleft : Oi.target = M.source := by
      simpa [Oi] using haTarget
    have hright : M.target = Oj.reverse.source := by
      simpa [Oj] using hbTarget.symm
    let Q := Oi.append3WithEqToPath M Oj.reverse hleft hright
    have hQconnects : Q.Connects (R.router i) (R.router j) := by
      exact Or.inl
        ⟨by
          simpa [Q, Oi] using
            GraphPath.orient_source_mem (Pi.path a) (Pi.connects a),
         by
          simpa [Q, Oj] using
            GraphPath.orient_source_mem (Pj.path b) (Pj.connects b)⟩
    exfalso
    rcases hXsep Q hQconnects with ⟨v, hvQ, hvX⟩
    have hvPieces :
        v ∈ Oi.vertexSet ∪ M.vertexSet ∪ Oj.reverse.vertexSet :=
      Oi.append3WithEqToPath_vertexSet_subset M Oj.reverse
        hleft hright hvQ
    rcases Finset.mem_union.mp hvPieces with hvOuter | hvOj
    · rcases Finset.mem_union.mp hvOuter with hvOi | hvM
      · exact Finset.disjoint_left.mp haAvoid
          (by simpa [Oi] using hvOi) hvX
      · exact Finset.disjoint_left.mp hqAvoid
          (by simpa [M] using hvM) hvX
    · exact Finset.disjoint_left.mp hbAvoid
        (by simpa [Oj] using hvOj) hvX

end ChekuriChuzhoySection5RouterLinking
end SimpleGraph

end Lax17Proofs
