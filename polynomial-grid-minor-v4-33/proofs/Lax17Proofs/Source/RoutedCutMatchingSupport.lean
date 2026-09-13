import Lax17Proofs.Source.ChekuriChuzhoyTheorem221
import Lax17Proofs.Source.GenericCutMatchingBudget
import Lax17Proofs.Source.PathPackingSupportDegree
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Routed cut-matching support graphs

This file realizes an abstract cut-matching transcript on a routable terminal
set by node-disjoint paths in the ambient graph.  The selected route in each
round supplies both the abstract perfect matching and one layer of the support
graph.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace RoutedCutMatchingSupport

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {X : Finset V} {eta : ℕ}

/-- A subtype finset of terminals, viewed again as a finset of ambient
vertices. -/
def ambientFinset (S : Finset {v : V // v ∈ X}) : Finset V :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem mem_ambientFinset (S : Finset {v : V // v ∈ X}) (v : V) :
    v ∈ ambientFinset S ↔ ∃ hv : v ∈ X, (⟨v, hv⟩ : {x : V // x ∈ X}) ∈ S := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨x, hxS, hxv⟩
    have hxval : x.1 = v := hxv
    subst v
    exact ⟨x.2, hxS⟩
  · rintro ⟨hvX, hvS⟩
    exact Finset.mem_map.mpr ⟨⟨v, hvX⟩, hvS, rfl⟩

theorem ambientFinset_subset (S : Finset {v : V // v ∈ X}) :
    ambientFinset S ⊆ X := by
  intro v hv
  rcases (mem_ambientFinset S v).1 hv with ⟨hvX, _⟩
  exact hvX

theorem ambientFinset_card (S : Finset {v : V // v ∈ X}) :
    (ambientFinset S).card = S.card := by
  simp [ambientFinset]

theorem ambientFinset_disjoint {S T : Finset {v : V // v ∈ X}}
    (h : Disjoint S T) :
    Disjoint (ambientFinset S) (ambientFinset T) := by
  classical
  rw [Finset.disjoint_left] at h ⊢
  intro v hvS hvT
  rcases (mem_ambientFinset S v).1 hvS with ⟨hvX, hvS'⟩
  rcases (mem_ambientFinset T v).1 hvT with ⟨_, hvT'⟩
  exact h hvS' hvT'

theorem ambientFinset_union (S T : Finset {v : V // v ∈ X}) :
    ambientFinset (S ∪ T) = ambientFinset S ∪ ambientFinset T := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
    rcases Finset.mem_union.mp hx with hxS | hxT
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨x, hxS, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨x, hxT, rfl⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · rcases Finset.mem_map.mp hvS with ⟨x, hxS, rfl⟩
      exact Finset.mem_map.mpr ⟨x, Finset.mem_union_left _ hxS, rfl⟩
    · rcases Finset.mem_map.mp hvT with ⟨x, hxT, rfl⟩
      exact Finset.mem_map.mpr ⟨x, Finset.mem_union_right _ hxT, rfl⟩

theorem ambientFinset_univ :
    ambientFinset (Finset.univ : Finset {v : V // v ∈ X}) = X := by
  classical
  ext v
  simp [ambientFinset]

/-- The ambient left side of a terminal bisection. -/
def leftTerminals (B : Bisection {v : V // v ∈ X}) : Finset V :=
  ambientFinset B.left

/-- The ambient right side of a terminal bisection. -/
def rightTerminals (B : Bisection {v : V // v ∈ X}) : Finset V :=
  ambientFinset B.right

theorem left_right_cover (B : Bisection {v : V // v ∈ X}) :
    leftTerminals B ∪ rightTerminals B = X := by
  unfold leftTerminals rightTerminals
  rw [← ambientFinset_union, B.cover, ambientFinset_univ]

theorem left_right_disjoint (B : Bisection {v : V // v ∈ X}) :
    Disjoint (leftTerminals B) (rightTerminals B) :=
  ambientFinset_disjoint B.disjoint

theorem left_right_card_eq (B : Bisection {v : V // v ∈ X}) :
    (leftTerminals B).card = (rightTerminals B).card := by
  simpa [leftTerminals, rightTerminals, ambientFinset_card] using B.card_eq

/-- The routed perfect packing selected for a terminal bisection. -/
noncomputable def selectedPacking
    (hroute : RoutableSetIn G X eta)
    (B : Bisection {v : V // v ∈ X}) :
    PerfectPathPacking G (leftTerminals B) (rightTerminals B) :=
  Classical.choice
    (hroute.2 (leftTerminals B) (rightTerminals B)
      (ambientFinset_subset B.left) (ambientFinset_subset B.right)
      (left_right_disjoint B) (left_right_cover B) (left_right_card_eq B)).2

/-- The ambient endpoint subtype of an attached terminal side is canonically
equivalent to the original subtype side. -/
noncomputable def ambientSubtypeEquiv (S : Finset {v : V // v ∈ X}) :
    {x : {v : V // v ∈ X} // x ∈ S} ≃ {v : V // v ∈ ambientFinset S} where
  toFun x := ⟨x.1.1, by
    exact (mem_ambientFinset S x.1.1).2 ⟨x.1.2, x.2⟩⟩
  invFun v := ⟨⟨v.1, (ambientFinset_subset S v.2)⟩, by
    exact (mem_ambientFinset S v.1).1 v.2 |>.2⟩
  left_inv x := by ext; rfl
  right_inv v := by ext; rfl

/-- The matching induced by the endpoint bijections of the selected perfect
path packing. -/
noncomputable def routedMatching
    (hroute : RoutableSetIn G X eta)
    (B : Bisection {v : V // v ∈ X}) : MatchingAcross B where
  toEquiv :=
    (ambientSubtypeEquiv B.left).trans
      (((selectedPacking hroute B).sourceEquiv.symm.trans
        (selectedPacking hroute B).targetEquiv).trans
        (ambientSubtypeEquiv B.right).symm)

/-- The routed responder is independent of time; each presented bisection
selects its certified perfect path packing. -/
noncomputable def routedResponder
    (hroute : RoutableSetIn G X eta) :
    SequentialResponder {v : V // v ∈ X} :=
  fun _round B => routedMatching hroute B

/-- The routed packing attached to one position of a transcript. -/
noncomputable def transcriptPacking
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (i : Fin rounds.length) :
    PerfectPathPacking G
      (leftTerminals (rounds.get i).cut)
      (rightTerminals (rounds.get i).cut) :=
  selectedPacking hroute (rounds.get i).cut

/-- The union of the path edges used to realize all transcript rounds. -/
noncomputable def supportGraph
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X})) :
    _root_.SimpleGraph V :=
  Finset.univ.sup fun i : Fin rounds.length =>
    (transcriptPacking hroute rounds i).toPathPacking.spanningGraph

/-- Every routed support edge is an ambient edge. -/
theorem supportGraph_le
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X})) :
    supportGraph hroute rounds ≤ G := by
  apply Finset.sup_le
  intro i _hi
  exact (transcriptPacking hroute rounds i).toPathPacking.spanningGraph_le

/-- Each node-disjoint routing layer contributes maximum degree at most two. -/
theorem supportGraph_maxDegreeAtMost
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X})) :
    MaxDegreeAtMost (supportGraph hroute rounds) (2 * rounds.length) := by
  simpa [supportGraph] using
    (PathPacking.maxDegreeAtMost_univ_sup_spanningGraph
      (fun i : Fin rounds.length =>
        (transcriptPacking hroute rounds i).toPathPacking))

@[simp]
theorem routedMatching_rightEndpoint_val
    (hroute : RoutableSetIn G X eta)
    (B : Bisection {v : V // v ∈ X})
    (x : {x : {v : V // v ∈ X} // x ∈ B.left}) :
    ((routedMatching hroute B).rightEndpoint x).1 =
      ((selectedPacking hroute B).path
        ((selectedPacking hroute B).indexOfSource
          (ambientSubtypeEquiv B.left x))).target := by
  rfl

@[simp]
theorem selectedPacking_source_indexOfSource
    (hroute : RoutableSetIn G X eta)
    (B : Bisection {v : V // v ∈ X})
    (x : {x : {v : V // v ∈ X} // x ∈ B.left}) :
    ((selectedPacking hroute B).path
      ((selectedPacking hroute B).indexOfSource
        (ambientSubtypeEquiv B.left x))).source = x.1.1 := by
  have h := congrArg Subtype.val
    ((selectedPacking hroute B).source_indexOfSource
      (ambientSubtypeEquiv B.left x))
  exact h

/-- One routed round has no more abstract crossing edges than physical
crossing edges in any supergraph of its path support. -/
theorem routedRound_edgeBoundary_card_le
    (hroute : RoutableSetIn G X eta)
    (B : Bisection {v : V // v ∈ X}) (round : ℕ)
    (K : _root_.SimpleGraph V)
    (hPK : (selectedPacking hroute B).toPathPacking.spanningGraph ≤ K)
    (A D : Finset V) (hcover : A ∪ D = Finset.univ)
    (hdisj : Disjoint A D)
    (S : Finset {v : V // v ∈ X})
    (hS : ∀ x : {v : V // v ∈ X}, x ∈ S ↔ x.1 ∈ A) :
    ((LazyRound.ofResponder (routedResponder hroute) round B).edgeBoundary S).card ≤
      (Section44.edgeBoundary K A D).card := by
  classical
  let P := selectedPacking hroute B
  let R := LazyRound.ofResponder (routedResponder hroute) round B
  let routeIndex : {x : {v : V // v ∈ X} // x ∈ B.left} → P.Index :=
    fun x => P.indexOfSource (ambientSubtypeEquiv B.left x)
  have hindex_injective : Function.Injective routeIndex := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hsx := selectedPacking_source_indexOfSource hroute B x
    have hsy := selectedPacking_source_indexOfSource hroute B y
    have hp : (P.path (routeIndex x)).source = (P.path (routeIndex y)).source :=
      congrArg (fun i => (P.path i).source) hxy
    exact hsx.symm.trans (hp.trans hsy)
  have hside : ∀ v : V, v ∉ A → v ∈ D := by
    intro v hvA
    have hv : v ∈ A ∪ D := by rw [hcover]; simp
    exact (Finset.mem_union.mp hv).resolve_left hvA
  let boundaryEquiv :
      Fin (R.edgeBoundary S).card ≃
        {x : {x : {v : V // v ∈ X} // x ∈ B.left} // x ∈ R.edgeBoundary S} :=
    (R.edgeBoundary S).equivFin.symm
  let Q : EdgePathPacking K (A ∩ (A ∪ D)) (D ∩ (A ∪ D)) := {
    Index := Fin (R.edgeBoundary S).card
    path := fun x =>
      (P.toPathPacking.inSpanningGraph.path (routeIndex (boundaryEquiv x).1)).mapLe hPK
    connects := by
      intro x
      let e := boundaryEquiv x
      have hxCross : R.edgeCrosses S e.1 :=
        (LazyRound.mem_edgeBoundary).1 e.2
      have hsource : (P.path (routeIndex e.1)).source = e.1.1.1 := by
        simpa [P, routeIndex] using
          selectedPacking_source_indexOfSource hroute B e.1
      have htarget :
          (P.path (routeIndex e.1)).target =
            ((routedMatching hroute B).rightEndpoint e.1).1 := by
        simpa [P, routeIndex] using
          (routedMatching_rightEndpoint_val hroute B e.1).symm
      change
        (e.1.1 ∈ S ∧
            (routedMatching hroute B).rightEndpoint e.1 ∉ S) ∨
          ((routedMatching hroute B).rightEndpoint e.1 ∈ S ∧
            e.1.1 ∉ S) at hxCross
      have hconn : (P.path (routeIndex e.1)).Connects A D := by
        change
          (P.path (routeIndex e.1)).source ∈ A ∧
              (P.path (routeIndex e.1)).target ∈ D ∨
            (P.path (routeIndex e.1)).source ∈ D ∧
              (P.path (routeIndex e.1)).target ∈ A
        rcases hxCross with hx | hx
        · exact Or.inl ⟨by simpa [hsource] using (hS e.1.1).1 hx.1,
            hside _ (by
              intro htA
              exact hx.2 ((hS ((routedMatching hroute B).rightEndpoint e.1)).2
                (by simpa [htarget] using htA)))⟩
        · exact Or.inr ⟨hside _ (by
              intro hsA
              exact hx.2 ((hS e.1.1).2 (by simpa [hsource] using hsA))),
            by simpa [htarget] using
              (hS ((routedMatching hroute B).rightEndpoint e.1)).1 hx.1⟩
      simpa [hcover, GraphPath.mapLe, GraphPath.Connects] using hconn
    edge_disjoint := by
      intro x y hxy
      have he_ne : (boundaryEquiv x).1 ≠ (boundaryEquiv y).1 := by
        intro heq
        apply hxy
        exact boundaryEquiv.injective (Subtype.ext heq)
      have hne : routeIndex (boundaryEquiv x).1 ≠ routeIndex (boundaryEquiv y).1 := by
        intro heq
        exact he_ne (hindex_injective heq)
      simpa [PathPacking.inSpanningGraph, PathPacking.transfer,
        GraphPath.EdgeDisjoint] using
        GraphPath.edgeDisjoint_of_nodeDisjoint (P.node_disjoint hne)
  }
  have hQstay : Q.StaysIn Finset.univ := by
    intro i v _hv
    simp
  have hQ :=
    Section46.EdgePathPacking.card_le_edgeBoundary_of_staysIn_partition
      (G := K) (C := (Finset.univ : Finset V)) (T := A ∪ D)
      (X := A) (Y := D) Q hQstay hcover hdisj
  simpa [Q, R, EdgePathPacking.card] using hQ

theorem transcriptPacking_spanningGraph_le_supportGraph
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (i : Fin rounds.length) :
    (transcriptPacking hroute rounds i).toPathPacking.spanningGraph ≤
      supportGraph hroute rounds := by
  exact Finset.le_sup (f := fun j : Fin rounds.length =>
    (transcriptPacking hroute rounds j).toPathPacking.spanningGraph) (by simp)

theorem transcriptRound_eq_of_followsResponder
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (hfollow : FollowsResponder (routedResponder hroute) 0 rounds)
    (i : Fin rounds.length) :
    rounds.get i = LazyRound.ofResponder
      (routedResponder hroute) i.1 (rounds.get i).cut := by
  have hget : rounds[i.1]? = some (rounds.get i) := by
    rw [List.get_eq_getElem]
    exact List.getElem?_eq_getElem i.2
  simpa using hfollow i.1 (rounds.get i) hget

/-- Every individual transcript round can be charged to the same physical
support-graph boundary. -/
theorem transcriptRound_edgeBoundary_card_le
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (hfollow : FollowsResponder (routedResponder hroute) 0 rounds)
    (i : Fin rounds.length)
    (A D : Finset V) (hcover : A ∪ D = Finset.univ)
    (hdisj : Disjoint A D)
    (S : Finset {v : V // v ∈ X})
    (hS : ∀ x : {v : V // v ∈ X}, x ∈ S ↔ x.1 ∈ A) :
    ((rounds.get i).edgeBoundary S).card ≤
      (Section44.edgeBoundary (supportGraph hroute rounds) A D).card := by
  let R := rounds.get i
  have hR : R = LazyRound.ofResponder
      (routedResponder hroute) i.1 R.cut := by
    simpa [R] using transcriptRound_eq_of_followsResponder hroute rounds hfollow i
  calc
    (R.edgeBoundary S).card =
        ((LazyRound.ofResponder (routedResponder hroute) i.1 R.cut).edgeBoundary S).card :=
      congrArg (fun Q => (Q.edgeBoundary S).card) hR
    _ ≤ (Section44.edgeBoundary (supportGraph hroute rounds) A D).card :=
      routedRound_edgeBoundary_card_le hroute R.cut i.1
        (supportGraph hroute rounds)
        (by simpa [R, transcriptPacking] using
          transcriptPacking_spanningGraph_le_supportGraph hroute rounds i)
        A D hcover hdisj S hS

theorem edgeBoundaryCount_eq_sum_get
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (S : Finset {v : V // v ∈ X}) :
    edgeBoundaryCount rounds S =
      ∑ i : Fin rounds.length, ((rounds.get i).edgeBoundary S).card := by
  unfold edgeBoundaryCount
  have hlist :
      rounds.map (fun R => (R.edgeBoundary S).card) =
        List.ofFn (fun i : Fin rounds.length =>
          ((rounds.get i).edgeBoundary S).card) := by
    calc
      rounds.map (fun R => (R.edgeBoundary S).card) =
          (List.ofFn rounds.get).map (fun R => (R.edgeBoundary S).card) :=
        congrArg (List.map fun R => (R.edgeBoundary S).card)
          (List.ofFn_get rounds).symm
      _ = List.ofFn ((fun R => (R.edgeBoundary S).card) ∘ rounds.get) :=
        List.map_ofFn
      _ = List.ofFn (fun i : Fin rounds.length =>
          ((rounds.get i).edgeBoundary S).card) := rfl
  calc
    (rounds.map fun R => (R.edgeBoundary S).card).sum =
        (List.ofFn fun i : Fin rounds.length =>
          ((rounds.get i).edgeBoundary S).card).sum := by
      rw [hlist]
    _ = ∑ i : Fin rounds.length, ((rounds.get i).edgeBoundary S).card :=
      List.sum_ofFn

/-- Summing the roundwise charging bound loses exactly the transcript length. -/
theorem transcript_edgeBoundaryCount_le
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (hfollow : FollowsResponder (routedResponder hroute) 0 rounds)
    (A D : Finset V) (hcover : A ∪ D = Finset.univ)
    (hdisj : Disjoint A D)
    (S : Finset {v : V // v ∈ X})
    (hS : ∀ x : {v : V // v ∈ X}, x ∈ S ↔ x.1 ∈ A) :
    edgeBoundaryCount rounds S ≤ rounds.length *
      (Section44.edgeBoundary (supportGraph hroute rounds) A D).card := by
  rw [edgeBoundaryCount_eq_sum_get]
  calc
    (∑ i : Fin rounds.length, ((rounds.get i).edgeBoundary S).card) ≤
        ∑ _i : Fin rounds.length,
          (Section44.edgeBoundary (supportGraph hroute rounds) A D).card := by
      exact Finset.sum_le_sum fun i _hi =>
        transcriptRound_edgeBoundary_card_le hroute rounds hfollow i
          A D hcover hdisj S hS
    _ = rounds.length *
        (Section44.edgeBoundary (supportGraph hroute rounds) A D).card := by
      simp

/-- Terminals lying on one ambient side of a cut. -/
def terminalsIn (X A : Finset V) : Finset {v : V // v ∈ X} :=
  Finset.univ.filter fun x => x.1 ∈ A

@[simp]
theorem mem_terminalsIn (A : Finset V) (x : {v : V // v ∈ X}) :
    x ∈ terminalsIn X A ↔ x.1 ∈ A := by
  simp [terminalsIn]

theorem terminalsIn_card (A : Finset V) :
    (terminalsIn X A).card = (A ∩ X).card := by
  classical
  have himage : ambientFinset (terminalsIn X A) = A ∩ X := by
    ext v
    constructor
    · intro hv
      rcases (mem_ambientFinset _ _).1 hv with ⟨hvX, hvA⟩
      exact Finset.mem_inter.mpr ⟨(mem_terminalsIn A _).1 hvA, hvX⟩
    · intro hv
      exact (mem_ambientFinset _ _).2
        ⟨(Finset.mem_inter.mp hv).2,
          (mem_terminalsIn A _).2 (Finset.mem_inter.mp hv).1⟩
  rw [← ambientFinset_card (terminalsIn X A), himage]

theorem terminal_cut_card_add
    (A D : Finset V) (hcover : A ∪ D = Finset.univ)
    (hdisj : Disjoint A D) :
    (A ∩ X).card + (D ∩ X).card = X.card := by
  have hdisj' : Disjoint (A ∩ X) (D ∩ X) :=
    hdisj.mono Finset.inter_subset_left Finset.inter_subset_left
  have hcover' : (A ∩ X) ∪ (D ∩ X) = X := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
    · intro hvX
      have hvAD : v ∈ A ∪ D := by rw [hcover]; simp
      rcases Finset.mem_union.mp hvAD with hvA | hvD
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvA, hvX⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvD, hvX⟩)
  rw [← Finset.card_union_of_disjoint hdisj', hcover']

/-- A half-expander on a positive even terminal set must use at least one
matching round. -/
theorem rounds_length_pos_of_halfExpander
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (hXpos : 0 < X.card) (hXeven : Even X.card)
    (hhalf : IsHalfEdgeExpander rounds) :
    0 < rounds.length := by
  rcases Finset.card_pos.mp hXpos with ⟨v, hvX⟩
  have hXtwo : 2 ≤ X.card := by
    rcases hXeven with ⟨m, hm⟩
    omega
  let x : {v : V // v ∈ X} := ⟨v, hvX⟩
  have hsmall : 2 * ({x} : Finset {v : V // v ∈ X}).card ≤
      Fintype.card {v : V // v ∈ X} := by
    simpa using hXtwo
  have hbound := (isHalfEdgeExpander_iff rounds).1 hhalf
    ({x} : Finset {v : V // v ∈ X}) (by simp) hsmall
  by_contra hnot
  have hzero : rounds.length = 0 := Nat.eq_zero_of_not_pos hnot
  have hrnil : rounds = [] := List.length_eq_zero_iff.mp hzero
  subst rounds
  simp at hbound

/-- Half-expansion of the routed transcript transfers to global scaled
edge-well-linkedness of the terminal set in its physical support graph. -/
theorem scaledEdgeWellLinkedIn_univ_of_halfExpander
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (hXpos : 0 < X.card) (hXeven : Even X.card)
    (hhalf : IsHalfEdgeExpander rounds)
    (hfollow : FollowsResponder (routedResponder hroute) 0 rounds) :
    Section46.ScaledEdgeWellLinkedIn
      (supportGraph hroute rounds) Finset.univ X 1 (2 * rounds.length) := by
  classical
  have hlenpos : 0 < rounds.length :=
    rounds_length_pos_of_halfExpander rounds hXpos hXeven hhalf
  refine ⟨by decide, by omega, by simp, ?_⟩
  intro A D _hA _hD hcover hdisj
  have hsum := terminal_cut_card_add (X := X) A D hcover hdisj
  let a := (A ∩ X).card
  let d := (D ∩ X).card
  let boundary :=
    (Section44.edgeBoundary (supportGraph hroute rounds) A D).card
  by_cases had : a ≤ d
  · by_cases ha0 : a = 0
    · rw [Nat.min_eq_left had, ha0]
      simp
    let S := terminalsIn X A
    have hScard : S.card = a := by simp [S, a, terminalsIn_card]
    have hsmall : 2 * S.card ≤ Fintype.card {v : V // v ∈ X} := by
      have : 2 * a ≤ X.card := by omega
      rw [hScard]
      simpa only [Fintype.card_coe] using this
    have hexpand : S.card ≤ 2 * edgeBoundaryCount rounds S :=
      (isHalfEdgeExpander_iff rounds).1 hhalf S (by rw [hScard]; omega) hsmall
    have hcount : edgeBoundaryCount rounds S ≤ rounds.length * boundary := by
      exact transcript_edgeBoundaryCount_le hroute rounds hfollow A D hcover hdisj S
        (fun x => mem_terminalsIn A x)
    rw [Nat.min_eq_left had]
    simp only [one_mul]
    calc
      a = S.card := hScard.symm
      _ ≤ 2 * edgeBoundaryCount rounds S := hexpand
      _ ≤ 2 * (rounds.length * boundary) := Nat.mul_le_mul_left 2 hcount
      _ = (2 * rounds.length) * boundary := by simp [Nat.mul_assoc]
  · have hda : d ≤ a := Nat.le_of_not_ge had
    by_cases hd0 : d = 0
    · rw [Nat.min_eq_right hda, hd0]
      simp
    let S := terminalsIn X D
    have hScard : S.card = d := by simp [S, d, terminalsIn_card]
    have hsmall : 2 * S.card ≤ Fintype.card {v : V // v ∈ X} := by
      have : 2 * d ≤ X.card := by omega
      rw [hScard]
      simpa only [Fintype.card_coe] using this
    have hexpand : S.card ≤ 2 * edgeBoundaryCount rounds S :=
      (isHalfEdgeExpander_iff rounds).1 hhalf S (by rw [hScard]; omega) hsmall
    have hcount' :
        edgeBoundaryCount rounds S ≤ rounds.length *
          (Section44.edgeBoundary (supportGraph hroute rounds) D A).card := by
      exact transcript_edgeBoundaryCount_le hroute rounds hfollow D A
        (by simpa [Finset.union_comm] using hcover) hdisj.symm S
        (fun x => mem_terminalsIn D x)
    have hcount : edgeBoundaryCount rounds S ≤ rounds.length * boundary := by
      simpa [boundary, Section44.edgeBoundary_comm] using hcount'
    rw [Nat.min_eq_right hda]
    simp only [one_mul]
    calc
      d = S.card := hScard.symm
      _ ≤ 2 * edgeBoundaryCount rounds S := hexpand
      _ ≤ 2 * (rounds.length * boundary) := Nat.mul_le_mul_left 2 hcount
      _ = (2 * rounds.length) * boundary := by simp [Nat.mul_assoc]

/-- Denominator-weakened form of the routed support-graph transfer. -/
theorem supportGraph_scaledEdgeWellLinkedIn_univ
    (hroute : RoutableSetIn G X eta)
    (rounds : List (LazyRound {v : V // v ∈ X}))
    (hXpos : 0 < X.card) (hXeven : Even X.card)
    (hhalf : IsHalfEdgeExpander rounds)
    (hfollow : FollowsResponder (routedResponder hroute) 0 rounds)
    {alphaDen : ℕ} (hlen : 2 * rounds.length ≤ alphaDen) :
    Section46.ScaledEdgeWellLinkedIn
      (supportGraph hroute rounds) Finset.univ X 1 alphaDen := by
  have hbase := scaledEdgeWellLinkedIn_univ_of_halfExpander
    hroute rounds hXpos hXeven hhalf hfollow
  refine ⟨hbase.1, hbase.2.1.trans hlen, hbase.2.2.1, ?_⟩
  intro A D hA hD hcover hdisj
  exact (hbase.2.2.2 A D hA hD hcover hdisj).trans
    (Nat.mul_le_mul_right
      (Section44.edgeBoundary (supportGraph hroute rounds) A D).card hlen)

end RoutedCutMatchingSupport
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
