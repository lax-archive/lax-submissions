import Lax17Proofs.Source.Degree
import Lax17Proofs.Source.DirectedFlow
import Lax17Proofs.Source.FlowDefs
import Lax17Proofs.Source.LocalSubgraph
import Lax17Proofs.Source.Menger

namespace Lax17Proofs

universe u v w

/-!
# From cut well-linkedness to many disjoint paths

This file isolates the flow part of Chekuri--Chuzhoy Theorem 2.14.  It builds
the standard super-source/super-sink auxiliary network, proves the relevant
cut lower bound from scaled edge-well-linkedness, applies finite
max-flow/min-cut, and then derives the needed disjoint-path consequences by
contradicting finite vertex-Menger separators.
-/

namespace SimpleGraph


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

namespace FlowWellLinked

variable {S T : Finset V} {alphaNum alphaDen : ℕ}

/-- Vertices of the auxiliary directed network used to route between terminal
sets: a super-source, the original graph vertices, and a super-sink. -/
inductive RoutingVertex (V : Type u) where
  | source : RoutingVertex V
  | original : V → RoutingVertex V
  | sink : RoutingVertex V
deriving DecidableEq, Fintype

namespace RoutingVertex

/-- The original graph vertices lying on a side of an auxiliary-network cut. -/
noncomputable def originalSide [Fintype V] (R : Finset (RoutingVertex V)) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v => RoutingVertex.original v ∈ R

set_option linter.unusedSectionVars false in
theorem mem_originalSide_iff [Fintype V]
    (R : Finset (RoutingVertex V)) (v : V) :
    v ∈ originalSide R ↔ RoutingVertex.original v ∈ R := by
  classical
  simp [originalSide]

end RoutingVertex

/-- Arcs of the auxiliary directed network: one unit arc out of the
super-source for each source terminal, one unit arc into the super-sink for
each target terminal, and one directed dart for each orientation of each graph
edge. -/
inductive RoutingArc
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  | source : {v : V // v ∈ S} → RoutingArc G S T
  | sink : {v : V // v ∈ T} → RoutingArc G S T
  | dart : G.Dart → RoutingArc G S T
deriving DecidableEq

def routingArcEquiv :
    RoutingArc G S T ≃ ({v : V // v ∈ S} ⊕ ({v : V // v ∈ T} ⊕ G.Dart)) where
  toFun
    | RoutingArc.source v => Sum.inl v
    | RoutingArc.sink v => Sum.inr (Sum.inl v)
    | RoutingArc.dart d => Sum.inr (Sum.inr d)
  invFun
    | Sum.inl v => RoutingArc.source v
    | Sum.inr (Sum.inl v) => RoutingArc.sink v
    | Sum.inr (Sum.inr d) => RoutingArc.dart d
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro a
    cases a with
    | inl v => rfl
    | inr x =>
        cases x <;> rfl

noncomputable instance routingArcFintype
    [Fintype V] [DecidableRel G.Adj] :
    Fintype (RoutingArc G S T) :=
  Fintype.ofEquiv _ (routingArcEquiv (G := G) (S := S) (T := T)).symm

namespace RoutingArc

variable {Terminals S T : Finset V} {alphaNum alphaDen : ℕ}

/-- The finite directed network underlying the standard super-source/super-sink
reduction for routing equal-size terminal subsets.  Original graph edges are
represented by both darts, each with capacity `alphaDen / alphaNum`; source and
sink arcs have unit capacity. -/
noncomputable def network
    (G : _root_.SimpleGraph V) (S T : Finset V)
    (alphaNum alphaDen : ℕ) :
    DirectedNetwork (RoutingVertex V) (RoutingArc G S T) where
  tail
    | RoutingArc.source _ => RoutingVertex.source
    | RoutingArc.sink v => RoutingVertex.original v.1
    | RoutingArc.dart d => RoutingVertex.original d.fst
  head
    | RoutingArc.source v => RoutingVertex.original v.1
    | RoutingArc.sink _ => RoutingVertex.sink
    | RoutingArc.dart d => RoutingVertex.original d.snd
  cap
    | RoutingArc.source _ => 1
    | RoutingArc.sink _ => 1
    | RoutingArc.dart _ => ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ)
  cap_nonneg := by
    intro e
    cases e with
    | source v => norm_num
    | sink v => norm_num
    | dart d =>
        unfold scaledCongestion
        positivity

end RoutingArc

/-! ## Boundary darts for the routing network -/

/-- Darts oriented from one vertex set to another. -/
noncomputable def crossingDarts [DecidableRel G.Adj] (A B : Finset V) :
    Finset G.Dart := by
  classical
  exact Finset.univ.filter fun d : G.Dart => d.fst ∈ A ∧ d.snd ∈ B

theorem mem_crossingDarts [DecidableRel G.Adj] (A B : Finset V) (d : G.Dart) :
    d ∈ crossingDarts (G := G) A B ↔ d.fst ∈ A ∧ d.snd ∈ B := by
  classical
  simp [crossingDarts]

/-- Every undirected boundary edge has an orientation from the left side to the
right side, so the boundary cardinality is bounded by the number of such
darts. -/
theorem edgeBoundary_card_le_crossingDarts_card
    [DecidableRel G.Adj] (A B : Finset V) :
    (Section44.edgeBoundary G A B).card ≤
      (crossingDarts (G := G) A B).card := by
  classical
  let edgeOfDart : G.Dart → Sym2 V := fun d => d.edge
  have hsubset :
      Section44.edgeBoundary G A B ⊆
        (crossingDarts (G := G) A B).image edgeOfDart := by
    intro e he
    rcases (Section44.mem_edgeBoundary (G := G) A B e).1 he with
      ⟨heG, x, hxA, y, hyB, rfl⟩
    have hxy : G.Adj x y := by
      simpa [_root_.SimpleGraph.mem_edgeSet] using heG
    let d : G.Dart := ⟨(x, y), hxy⟩
    refine Finset.mem_image.2 ⟨d, ?_, ?_⟩
    · exact (mem_crossingDarts (G := G) A B d).2 ⟨hxA, hyB⟩
    · rfl
  exact (Finset.card_le_card hsubset).trans
    (Finset.card_image_le
      (s := crossingDarts (G := G) A B) (f := edgeOfDart))

theorem crossingDarts_card_le_maxDegree_mul_of_snd_subset
    [DecidableRel G.Adj] {A B X : Finset V} {Δ : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hsnd : ∀ d : G.Dart, d ∈ crossingDarts (G := G) A B → d.snd ∈ X) :
    (crossingDarts (G := G) A B).card ≤ Δ * X.card := by
  classical
  let chargeSet : Finset (V × V) :=
    X.biUnion fun x =>
      (MaxDegreeAtMost.neighborFinset (G := G) hdegree x).image fun y => (x, y)
  let charge : {d : G.Dart // d ∈ crossingDarts (G := G) A B} → V × V :=
    fun d => (d.1.snd, d.1.fst)
  have hcharge_mem : ∀ d, charge d ∈ chargeSet := by
    intro d
    have hd := (mem_crossingDarts (G := G) A B d.1).1 d.2
    have hsndX : d.1.snd ∈ X := hsnd d.1 d.2
    have hneigh :
        d.1.fst ∈ MaxDegreeAtMost.neighborFinset (G := G) hdegree d.1.snd := by
      rw [MaxDegreeAtMost.mem_neighborFinset]
      exact G.symm d.1.2
    refine Finset.mem_biUnion.2 ⟨d.1.snd, hsndX, ?_⟩
    exact Finset.mem_image.2 ⟨d.1.fst, hneigh, rfl⟩
  let charge' : {d : G.Dart // d ∈ crossingDarts (G := G) A B} →
      {p : V × V // p ∈ chargeSet} :=
    fun d => ⟨charge d, hcharge_mem d⟩
  have hinj : Function.Injective charge' := by
    intro d e h
    apply Subtype.ext
    have hp : (d.1.snd, d.1.fst) = (e.1.snd, e.1.fst) :=
      congrArg Subtype.val h
    have hfst : d.1.fst = e.1.fst := by
      exact congrArg Prod.snd hp
    have hsnd_eq : d.1.snd = e.1.snd := by
      exact congrArg Prod.fst hp
    exact _root_.SimpleGraph.Dart.ext _ _ (Prod.ext hfst hsnd_eq)
  have hcard_le : (crossingDarts (G := G) A B).card ≤ chargeSet.card := by
    have h := Fintype.card_le_of_injective charge' hinj
    simpa using h
  have hcharge_card : chargeSet.card ≤ X.card * Δ := by
    calc
      chargeSet.card
          ≤ ∑ x ∈ X,
              ((MaxDegreeAtMost.neighborFinset (G := G) hdegree x).image
                fun y => (x, y)).card := by
            exact Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ X, Δ := by
            exact Finset.sum_le_sum fun x _hx =>
              (Finset.card_image_le.trans
                (MaxDegreeAtMost.card_neighborFinset_le (G := G) hdegree x))
      _ = X.card * Δ := by
            simp [Finset.sum_const, Nat.mul_comm]
  exact hcard_le.trans (by simpa [Nat.mul_comm] using hcharge_card)

theorem crossingDarts_card_add_le_maxDegree_mul_middle
    [DecidableRel G.Adj] {A X B : Finset V} {Δ : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hAB : Disjoint A B) :
    (crossingDarts (G := G) A X).card +
        (crossingDarts (G := G) X B).card ≤ Δ * X.card := by
  classical
  let left := crossingDarts (G := G) A X
  let right := crossingDarts (G := G) X B
  let chargeSet : Finset (V × V) :=
    X.biUnion fun x =>
      (MaxDegreeAtMost.neighborFinset (G := G) hdegree x).image fun y => (x, y)
  let charge : ({d : G.Dart // d ∈ left} ⊕ {d : G.Dart // d ∈ right}) → V × V
    | Sum.inl d => (d.1.snd, d.1.fst)
    | Sum.inr d => (d.1.fst, d.1.snd)
  have hcharge_mem :
      ∀ d, charge d ∈ chargeSet := by
    intro d
    cases d with
    | inl d =>
        have hd := (mem_crossingDarts (G := G) A X d.1).1 d.2
        have hneigh :
            d.1.fst ∈ MaxDegreeAtMost.neighborFinset (G := G) hdegree d.1.snd := by
          rw [MaxDegreeAtMost.mem_neighborFinset]
          exact G.symm d.1.2
        refine Finset.mem_biUnion.2 ⟨d.1.snd, hd.2, ?_⟩
        exact Finset.mem_image.2 ⟨d.1.fst, hneigh, rfl⟩
    | inr d =>
        have hd := (mem_crossingDarts (G := G) X B d.1).1 d.2
        have hneigh :
            d.1.snd ∈ MaxDegreeAtMost.neighborFinset (G := G) hdegree d.1.fst := by
          rw [MaxDegreeAtMost.mem_neighborFinset]
          exact d.1.2
        refine Finset.mem_biUnion.2 ⟨d.1.fst, hd.1, ?_⟩
        exact Finset.mem_image.2 ⟨d.1.snd, hneigh, rfl⟩
  let charge' :
      ({d : G.Dart // d ∈ left} ⊕ {d : G.Dart // d ∈ right}) →
        {p : V × V // p ∈ chargeSet} :=
    fun d => ⟨charge d, hcharge_mem d⟩
  have hinj : Function.Injective charge' := by
    intro d e h
    cases d with
    | inl d =>
        cases e with
        | inl e =>
            apply congrArg Sum.inl
            apply Subtype.ext
            have hp : (d.1.snd, d.1.fst) = (e.1.snd, e.1.fst) :=
              congrArg Subtype.val h
            exact _root_.SimpleGraph.Dart.ext _ _
              (Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp))
        | inr e =>
            have hp : (d.1.snd, d.1.fst) = (e.1.fst, e.1.snd) :=
              congrArg Subtype.val h
            have hA : d.1.fst ∈ A :=
              ((mem_crossingDarts (G := G) A X d.1).1 d.2).1
            have hB : e.1.snd ∈ B :=
              ((mem_crossingDarts (G := G) X B e.1).1 e.2).2
            have heq : d.1.fst = e.1.snd := congrArg Prod.snd hp
            exact False.elim (Finset.disjoint_left.mp hAB hA (by simpa [← heq] using hB))
    | inr d =>
        cases e with
        | inl e =>
            have hp : (d.1.fst, d.1.snd) = (e.1.snd, e.1.fst) :=
              congrArg Subtype.val h
            have hB : d.1.snd ∈ B :=
              ((mem_crossingDarts (G := G) X B d.1).1 d.2).2
            have hA : e.1.fst ∈ A :=
              ((mem_crossingDarts (G := G) A X e.1).1 e.2).1
            have heq : d.1.snd = e.1.fst := congrArg Prod.snd hp
            exact False.elim (Finset.disjoint_left.mp hAB hA (by simpa [heq] using hB))
        | inr e =>
            apply congrArg Sum.inr
            apply Subtype.ext
            have hp : (d.1.fst, d.1.snd) = (e.1.fst, e.1.snd) :=
              congrArg Subtype.val h
            exact _root_.SimpleGraph.Dart.ext _ _
              (Prod.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp))
  have hcard_le : left.card + right.card ≤ chargeSet.card := by
    have h := Fintype.card_le_of_injective charge' hinj
    simpa [left, right] using h
  have hcharge_card : chargeSet.card ≤ X.card * Δ := by
    calc
      chargeSet.card
          ≤ ∑ x ∈ X,
              ((MaxDegreeAtMost.neighborFinset (G := G) hdegree x).image
                fun y => (x, y)).card := by
            exact Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ X, Δ := by
            exact Finset.sum_le_sum fun x _hx =>
              (Finset.card_image_le.trans
                (MaxDegreeAtMost.card_neighborFinset_le (G := G) hdegree x))
      _ = X.card * Δ := by
            simp [Finset.sum_const, Nat.mul_comm]
  exact hcard_le.trans (by simpa [Nat.mul_comm] using hcharge_card)

/-- Source arcs of the auxiliary network crossing a cut whose original side is
`A`. -/
noncomputable def sourceCutArcs (S T A : Finset V) :
    Finset (RoutingArc G S T) := by
  classical
  exact (S \ A).attach.image fun v =>
    RoutingArc.source (G := G) (S := S) (T := T)
      ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩

/-- Sink arcs of the auxiliary network crossing a cut whose original side is
`A`. -/
noncomputable def sinkCutArcs (S T A : Finset V) :
    Finset (RoutingArc G S T) := by
  classical
  exact (T ∩ A).attach.image fun v =>
    RoutingArc.sink (G := G) (S := S) (T := T)
      ⟨v.1, (Finset.mem_inter.mp v.2).1⟩

/-- Original graph darts crossing a cut in the auxiliary network. -/
noncomputable def dartCutArcs [DecidableRel G.Adj]
    (S T A B : Finset V) :
    Finset (RoutingArc G S T) := by
  classical
  exact (crossingDarts (G := G) A B).image fun d =>
    RoutingArc.dart (G := G) (S := S) (T := T) d

omit [Fintype V] in
@[simp] theorem source_mem_sourceCutArcs
    {S T A : Finset V} (v : {v : V // v ∈ S}) :
    RoutingArc.source (G := G) (S := S) (T := T) v ∈
        sourceCutArcs (G := G) S T A ↔ v.1 ∉ A := by
  classical
  unfold sourceCutArcs
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
    injection hwEq with hsub
    have hvw : w.1 = v.1 := congrArg Subtype.val hsub
    simpa [← hvw] using (Finset.mem_sdiff.mp w.2).2
  · intro hvA
    refine Finset.mem_image.2 ⟨⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hvA⟩⟩, ?_, ?_⟩
    · simp
    · rfl

omit [Fintype V] in
@[simp] theorem source_not_mem_sinkCutArcs
    {S T A : Finset V} (v : {v : V // v ∈ S}) :
    RoutingArc.source (G := G) (S := S) (T := T) v ∉
        sinkCutArcs (G := G) S T A := by
  classical
  intro h
  unfold sinkCutArcs at h
  rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
  cases hwEq

@[simp] theorem source_not_mem_dartCutArcs
    [DecidableRel G.Adj] {S T A B : Finset V} (v : {v : V // v ∈ S}) :
    RoutingArc.source (G := G) (S := S) (T := T) v ∉
        dartCutArcs (G := G) S T A B := by
  classical
  intro h
  unfold dartCutArcs at h
  rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
  cases hwEq

omit [Fintype V] in
@[simp] theorem sink_mem_sinkCutArcs
    {S T A : Finset V} (v : {v : V // v ∈ T}) :
    RoutingArc.sink (G := G) (S := S) (T := T) v ∈
        sinkCutArcs (G := G) S T A ↔ v.1 ∈ A := by
  classical
  unfold sinkCutArcs
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
    injection hwEq with hsub
    have hvw : w.1 = v.1 := congrArg Subtype.val hsub
    simpa [← hvw] using (Finset.mem_inter.mp w.2).2
  · intro hvA
    refine Finset.mem_image.2 ⟨⟨v.1, Finset.mem_inter.mpr ⟨v.2, hvA⟩⟩, ?_, ?_⟩
    · simp
    · rfl

omit [Fintype V] in
@[simp] theorem sink_not_mem_sourceCutArcs
    {S T A : Finset V} (v : {v : V // v ∈ T}) :
    RoutingArc.sink (G := G) (S := S) (T := T) v ∉
        sourceCutArcs (G := G) S T A := by
  classical
  intro h
  unfold sourceCutArcs at h
  rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
  cases hwEq

@[simp] theorem sink_not_mem_dartCutArcs
    [DecidableRel G.Adj] {S T A B : Finset V} (v : {v : V // v ∈ T}) :
    RoutingArc.sink (G := G) (S := S) (T := T) v ∉
        dartCutArcs (G := G) S T A B := by
  classical
  intro h
  unfold dartCutArcs at h
  rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
  cases hwEq

@[simp] theorem dart_mem_dartCutArcs
    [DecidableRel G.Adj] {S T A B : Finset V} (d : G.Dart) :
    RoutingArc.dart (G := G) (S := S) (T := T) d ∈
        dartCutArcs (G := G) S T A B ↔ d.fst ∈ A ∧ d.snd ∈ B := by
  classical
  unfold dartCutArcs
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
    injection hwEq with hd
    subst hd
    exact (mem_crossingDarts (G := G) A B w).1 hw
  · intro hd
    exact Finset.mem_image.2
      ⟨d, (mem_crossingDarts (G := G) A B d).2 hd, rfl⟩

omit [Fintype V] in
@[simp] theorem dart_not_mem_sourceCutArcs
    {S T A : Finset V} (d : G.Dart) :
    RoutingArc.dart (G := G) (S := S) (T := T) d ∉
        sourceCutArcs (G := G) S T A := by
  classical
  intro h
  unfold sourceCutArcs at h
  rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
  cases hwEq

omit [Fintype V] in
@[simp] theorem dart_not_mem_sinkCutArcs
    {S T A : Finset V} (d : G.Dart) :
    RoutingArc.dart (G := G) (S := S) (T := T) d ∉
        sinkCutArcs (G := G) S T A := by
  classical
  intro h
  unfold sinkCutArcs at h
  rcases Finset.mem_image.mp h with ⟨w, hw, hwEq⟩
  cases hwEq

omit [Fintype V] in
theorem sourceCutArcs_card (S T A : Finset V) :
    (sourceCutArcs (G := G) S T A).card = (S \ A).card := by
  classical
  unfold sourceCutArcs
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    simp at hxy
    exact hxy

omit [Fintype V] in
theorem sinkCutArcs_card (S T A : Finset V) :
    (sinkCutArcs (G := G) S T A).card = (T ∩ A).card := by
  classical
  unfold sinkCutArcs
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    simp at hxy
    exact hxy

theorem dartCutArcs_card [DecidableRel G.Adj]
    (S T A B : Finset V) :
    (dartCutArcs (G := G) S T A B).card =
      (crossingDarts (G := G) A B).card := by
  classical
  unfold dartCutArcs
  rw [Finset.card_image_of_injective
    (s := crossingDarts (G := G) A B)
    (f := fun d => RoutingArc.dart (G := G) (S := S) (T := T) d)
    (by
      intro x y hxy
      injection hxy)]

theorem sourceCutArcs_subset_cut
    [DecidableRel G.Adj]
    {S T A : Finset V} {R : Finset (RoutingVertex V)}
    (hsource : RoutingVertex.source ∈ R)
    (hA : A = RoutingVertex.originalSide R) :
    sourceCutArcs (G := G) S T A ⊆
      Finset.univ.filter (fun a : RoutingArc G S T =>
        (RoutingArc.network G S T alphaNum alphaDen).tail a ∈ R ∧
          (RoutingArc.network G S T alphaNum alphaDen).head a ∉ R) := by
  classical
  intro a ha
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ a, ?_⟩
  unfold sourceCutArcs at ha
  rcases Finset.mem_image.mp ha with ⟨v, hv, rfl⟩
  constructor
  · simpa [RoutingArc.network] using hsource
  · have hvA : v.1 ∉ A := (Finset.mem_sdiff.mp v.2).2
    intro hvR
    have hvOrig : v.1 ∈ RoutingVertex.originalSide R := by
      rw [RoutingVertex.mem_originalSide_iff]
      simpa [RoutingArc.network] using hvR
    exact hvA (by simpa [hA] using hvOrig)

theorem sinkCutArcs_subset_cut
    [DecidableRel G.Adj]
    {S T A : Finset V} {R : Finset (RoutingVertex V)}
    (hsink : RoutingVertex.sink ∉ R)
    (hA : A = RoutingVertex.originalSide R) :
    sinkCutArcs (G := G) S T A ⊆
      Finset.univ.filter (fun a : RoutingArc G S T =>
        (RoutingArc.network G S T alphaNum alphaDen).tail a ∈ R ∧
          (RoutingArc.network G S T alphaNum alphaDen).head a ∉ R) := by
  classical
  intro a ha
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ a, ?_⟩
  unfold sinkCutArcs at ha
  rcases Finset.mem_image.mp ha with ⟨v, hv, rfl⟩
  constructor
  · have hvA : v.1 ∈ A := (Finset.mem_inter.mp v.2).2
    have hvOrig : v.1 ∈ RoutingVertex.originalSide R := by
      simpa [hA] using hvA
    rw [RoutingVertex.mem_originalSide_iff] at hvOrig
    simpa [RoutingArc.network] using hvOrig
  · simpa [RoutingArc.network] using hsink

theorem dartCutArcs_subset_cut [DecidableRel G.Adj]
    {S T A B : Finset V} {R : Finset (RoutingVertex V)}
    (hA : A = RoutingVertex.originalSide R)
    (hB : B = (Finset.univ : Finset V) \ A) :
    dartCutArcs (G := G) S T A B ⊆
      Finset.univ.filter (fun a : RoutingArc G S T =>
        (RoutingArc.network G S T alphaNum alphaDen).tail a ∈ R ∧
          (RoutingArc.network G S T alphaNum alphaDen).head a ∉ R) := by
  classical
  intro a ha
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ a, ?_⟩
  unfold dartCutArcs at ha
  rcases Finset.mem_image.mp ha with ⟨d, hd, rfl⟩
  rcases (mem_crossingDarts (G := G) A B d).1 hd with ⟨hfst, hsnd⟩
  constructor
  · rw [hA, RoutingVertex.mem_originalSide_iff] at hfst
    simpa [RoutingArc.network] using hfst
  · rw [hB] at hsnd
    have hsnd_notA : d.snd ∉ A := (Finset.mem_sdiff.mp hsnd).2
    intro hsndR
    exact hsnd_notA (by
      rw [hA, RoutingVertex.mem_originalSide_iff]
      exact hsndR)

omit [Fintype V] in
theorem sourceCutArcs_cap_sum
    {S T A : Finset V} {alphaNum alphaDen : ℕ} :
    (∑ a ∈ sourceCutArcs (G := G) S T A,
      (RoutingArc.network G S T alphaNum alphaDen).cap a) =
        ((S \ A).card : ℝ) := by
  classical
  unfold sourceCutArcs
  rw [Finset.sum_image]
  · simp [RoutingArc.network]
  · intro x _hx y _hy hxy
    injection hxy with hsub
    exact Subtype.ext (congrArg (fun z : {v : V // v ∈ S} => (z : V)) hsub)

omit [Fintype V] in
theorem sinkCutArcs_cap_sum
    {S T A : Finset V} {alphaNum alphaDen : ℕ} :
    (∑ a ∈ sinkCutArcs (G := G) S T A,
      (RoutingArc.network G S T alphaNum alphaDen).cap a) =
        ((T ∩ A).card : ℝ) := by
  classical
  unfold sinkCutArcs
  rw [Finset.sum_image]
  · simp [RoutingArc.network]
  · intro x _hx y _hy hxy
    injection hxy with hsub
    exact Subtype.ext (congrArg (fun z : {v : V // v ∈ T} => (z : V)) hsub)

theorem dartCutArcs_cap_sum [DecidableRel G.Adj]
    {S T A B : Finset V} {alphaNum alphaDen : ℕ} :
    (∑ a ∈ dartCutArcs (G := G) S T A B,
      (RoutingArc.network G S T alphaNum alphaDen).cap a) =
        ((crossingDarts (G := G) A B).card : ℝ) *
          ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
  classical
  unfold dartCutArcs
  rw [Finset.sum_image]
  · simp [RoutingArc.network, mul_comm]
  · intro x _hx y _hy hxy
    injection hxy

/-- The three families of auxiliary arcs that certainly cross a super-source
cut with original side `A` and complement `B`. -/
noncomputable def selectedCutArcs [DecidableRel G.Adj]
    (S T A B : Finset V) : Finset (RoutingArc G S T) :=
  sourceCutArcs (G := G) S T A ∪
    sinkCutArcs (G := G) S T A ∪
      dartCutArcs (G := G) S T A B

omit [Fintype V] in
private theorem source_sink_disjoint
    {S T A : Finset V} :
    Disjoint (sourceCutArcs (G := G) S T A)
      (sinkCutArcs (G := G) S T A) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  unfold sourceCutArcs at ha
  unfold sinkCutArcs at hb
  rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨y, hy, hyEq⟩
  cases hyEq

private theorem source_dart_disjoint [DecidableRel G.Adj]
    {S T A B : Finset V} :
    Disjoint (sourceCutArcs (G := G) S T A)
      (dartCutArcs (G := G) S T A B) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  unfold sourceCutArcs at ha
  unfold dartCutArcs at hb
  rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨d, hd, hdEq⟩
  cases hdEq

private theorem sink_dart_disjoint [DecidableRel G.Adj]
    {S T A B : Finset V} :
    Disjoint (sinkCutArcs (G := G) S T A)
      (dartCutArcs (G := G) S T A B) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  unfold sinkCutArcs at ha
  unfold dartCutArcs at hb
  rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨d, hd, hdEq⟩
  cases hdEq

theorem selectedCutArcs_subset_cut [DecidableRel G.Adj]
    {S T A B : Finset V} {R : Finset (RoutingVertex V)}
    (hsource : RoutingVertex.source ∈ R)
    (hsink : RoutingVertex.sink ∉ R)
    (hA : A = RoutingVertex.originalSide R)
    (hB : B = (Finset.univ : Finset V) \ A) :
    selectedCutArcs (G := G) S T A B ⊆
      Finset.univ.filter (fun a : RoutingArc G S T =>
        (RoutingArc.network G S T alphaNum alphaDen).tail a ∈ R ∧
          (RoutingArc.network G S T alphaNum alphaDen).head a ∉ R) := by
  classical
  intro a ha
  unfold selectedCutArcs at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · exact sourceCutArcs_subset_cut
        (G := G) (alphaNum := alphaNum) (alphaDen := alphaDen)
        hsource hA ha
    · exact sinkCutArcs_subset_cut
        (G := G) (alphaNum := alphaNum) (alphaDen := alphaDen)
        hsink hA ha
  · exact dartCutArcs_subset_cut
      (G := G) (alphaNum := alphaNum) (alphaDen := alphaDen)
      hA hB ha

theorem selectedCutArcs_cap_sum [DecidableRel G.Adj]
    {S T A B : Finset V} {alphaNum alphaDen : ℕ} :
    (∑ a ∈ selectedCutArcs (G := G) S T A B,
      (RoutingArc.network G S T alphaNum alphaDen).cap a) =
        ((S \ A).card : ℝ) + ((T ∩ A).card : ℝ) +
    ((crossingDarts (G := G) A B).card : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
  classical
  unfold selectedCutArcs
  have hsd : Disjoint
      (sourceCutArcs (G := G) S T A ∪ sinkCutArcs (G := G) S T A)
      (dartCutArcs (G := G) S T A B) := by
    rw [Finset.disjoint_left]
    intro a ha hd
    rcases Finset.mem_union.mp ha with hs | ht
    · exact Finset.disjoint_left.mp source_dart_disjoint hs hd
    · exact Finset.disjoint_left.mp sink_dart_disjoint ht hd
  rw [Finset.sum_union hsd]
  rw [Finset.sum_union source_sink_disjoint]
  rw [sourceCutArcs_cap_sum, sinkCutArcs_cap_sum, dartCutArcs_cap_sum]

theorem selectedCutArcs_eq_cut [DecidableRel G.Adj]
    {S T A B : Finset V} {R : Finset (RoutingVertex V)}
    {alphaNum alphaDen : ℕ}
    (hsource : RoutingVertex.source ∈ R)
    (hsink : RoutingVertex.sink ∉ R)
    (hA : A = RoutingVertex.originalSide R)
    (hB : B = (Finset.univ : Finset V) \ A) :
    selectedCutArcs (G := G) S T A B =
      Finset.univ.filter (fun a : RoutingArc G S T =>
        (RoutingArc.network G S T alphaNum alphaDen).tail a ∈ R ∧
          (RoutingArc.network G S T alphaNum alphaDen).head a ∉ R) := by
  classical
  ext a
  cases a with
  | source v =>
      simp [selectedCutArcs,
        RoutingArc.network, hsource, hA, RoutingVertex.mem_originalSide_iff]
  | sink v =>
      simp [selectedCutArcs,
        RoutingArc.network, hsink, hA, RoutingVertex.mem_originalSide_iff]
  | dart d =>
      simp [selectedCutArcs,
        RoutingArc.network, hA, hB,
        RoutingVertex.mem_originalSide_iff]

theorem cutCapacity_eq_selectedCutArcs_cap_sum [DecidableRel G.Adj]
    {S T A B : Finset V} {R : Finset (RoutingVertex V)}
    {alphaNum alphaDen : ℕ}
    (hsource : RoutingVertex.source ∈ R)
    (hsink : RoutingVertex.sink ∉ R)
    (hA : A = RoutingVertex.originalSide R)
    (hB : B = (Finset.univ : Finset V) \ A) :
    (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R =
      ∑ a ∈ selectedCutArcs (G := G) S T A B,
        (RoutingArc.network G S T alphaNum alphaDen).cap a := by
  classical
  let N := RoutingArc.network G S T alphaNum alphaDen
  have hcut :
      Finset.univ.filter (fun a : RoutingArc G S T =>
        N.tail a ∈ R ∧ N.head a ∉ R) =
          selectedCutArcs (G := G) S T A B := by
    exact (selectedCutArcs_eq_cut
      (G := G) (S := S) (T := T) (A := A) (B := B) (R := R)
      (alphaNum := alphaNum) (alphaDen := alphaDen)
      hsource hsink hA hB).symm
  unfold DirectedNetwork.cutCapacity DirectedNetwork.cutOut
  change (∑ e : RoutingArc G S T,
      if N.tail e ∈ R ∧ N.head e ∉ R then N.cap e else 0) =
    ∑ a ∈ selectedCutArcs (G := G) S T A B, N.cap a
  rw [show (∑ e : RoutingArc G S T,
      if N.tail e ∈ R ∧ N.head e ∉ R then N.cap e else 0) =
        ∑ e ∈ Finset.univ.filter (fun a : RoutingArc G S T =>
          N.tail a ∈ R ∧ N.head a ∉ R), N.cap e by
    simpa using
      (Finset.sum_filter
        (s := (Finset.univ : Finset (RoutingArc G S T)))
        (p := fun a : RoutingArc G S T => N.tail a ∈ R ∧ N.head a ∉ R)
        (f := fun a : RoutingArc G S T => N.cap a)).symm]
  rw [hcut]

theorem selectedCutArcs_cap_sum_le_cutCapacity [DecidableRel G.Adj]
    {S T A B : Finset V} {R : Finset (RoutingVertex V)}
    {alphaNum alphaDen : ℕ}
    (hsource : RoutingVertex.source ∈ R)
    (hsink : RoutingVertex.sink ∉ R)
    (hA : A = RoutingVertex.originalSide R)
    (hB : B = (Finset.univ : Finset V) \ A) :
    (∑ a ∈ selectedCutArcs (G := G) S T A B,
      (RoutingArc.network G S T alphaNum alphaDen).cap a) ≤
        (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R := by
  classical
  let N := RoutingArc.network G S T alphaNum alphaDen
  let cutArcs : Finset (RoutingArc G S T) :=
    Finset.univ.filter fun a : RoutingArc G S T =>
      N.tail a ∈ R ∧ N.head a ∉ R
  have hsub :
      selectedCutArcs (G := G) S T A B ⊆ cutArcs := by
    simpa [cutArcs, N] using
      selectedCutArcs_subset_cut
        (G := G) (S := S) (T := T) (A := A) (B := B) (R := R)
        (alphaNum := alphaNum) (alphaDen := alphaDen)
        hsource hsink hA hB
  have hnonneg :
      ∀ a ∈ cutArcs, a ∉ selectedCutArcs (G := G) S T A B →
        0 ≤ N.cap a := by
    intro a _ha _hnot
    exact N.cap_nonneg a
  have hle :
      (∑ a ∈ selectedCutArcs (G := G) S T A B, N.cap a) ≤
        ∑ a ∈ cutArcs, N.cap a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hcut :
      (∑ a ∈ cutArcs, N.cap a) = N.cutCapacity R := by
    unfold cutArcs DirectedNetwork.cutCapacity DirectedNetwork.cutOut
    rw [Finset.sum_filter]
  simpa [N] using hle.trans_eq hcut

private theorem superSourceSink_cut_arith
    {α n sOut a b D : ℕ}
    (hS : sOut + a = n)
    (hD : α * (a - b) ≤ D) :
    α * n ≤ α * sOut + D + α * b := by
  rw [← hS, Nat.mul_add]
  calc
    α * sOut + α * a ≤ α * sOut + (D + α * b) := by
      apply Nat.add_le_add_left
      by_cases hba : b ≤ a
      · have ha : a = (a - b) + b := (Nat.sub_add_cancel hba).symm
        rw [ha, Nat.mul_add]
        exact Nat.add_le_add_right hD (α * b)
      · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
        exact (Nat.mul_le_mul_left α hab).trans (Nat.le_add_left _ _)
    _ = α * sOut + D + α * b := by rw [Nat.add_assoc]

/-- Cut arithmetic for the super-source/super-sink reduction.

For equal-size terminal subsets `S,T` of a scaled edge-well-linked set, any
original-vertex side `A` of a super cut has enough capacity from three sources:
unit source arcs crossing out of `S \ A`, original graph boundary capacity, and
unit sink arcs crossing from `T ∩ A`.  This is the key numerical reduction from
multi-terminal routing to ordinary single-source/sink max-flow. -/
theorem superSourceSink_cutCapacity_lowerBound
    {Terminals S T A : Finset V} {alphaNum alphaDen : ℕ}
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) :
    alphaNum * S.card ≤
      alphaNum * (S \ A).card +
        alphaDen * (Section44.edgeBoundary G A ((univ : Finset V) \ A)).card +
          alphaNum * (T ∩ A).card := by
  classical
  let B := (univ : Finset V) \ A
  have hcover : A ∪ B = (univ : Finset V) := by
    ext v
    by_cases hv : v ∈ A <;> simp [B, hv]
  have hdisj : Disjoint A B := by
    rw [disjoint_iff_inter_eq_empty]
    ext v
    simp [B]
  have hwell_cut :
      alphaNum * min (A ∩ Terminals).card (B ∩ Terminals).card ≤
        alphaDen * (Section44.edgeBoundary G A B).card :=
    hwell.2.2 A B hcover hdisj
  have hleft :
      (S ∩ A).card ≤ (A ∩ Terminals).card := by
    refine card_le_card ?_
    intro v hv
    exact mem_inter.mpr ⟨(mem_inter.mp hv).2, hS (mem_inter.mp hv).1⟩
  have hright :
      (T \ A).card ≤ (B ∩ Terminals).card := by
    refine card_le_card ?_
    intro v hv
    exact mem_inter.mpr
      ⟨by
        exact mem_sdiff.mpr ⟨mem_univ v, (mem_sdiff.mp hv).2⟩,
       hT (mem_sdiff.mp hv).1⟩
  have hdiff_le_min :
      (S ∩ A).card - (T ∩ A).card ≤
        min (A ∩ Terminals).card (B ∩ Terminals).card := by
    apply le_min
    · exact (Nat.sub_le _ _).trans hleft
    · have hSA_le : (S ∩ A).card ≤ S.card :=
        card_le_card inter_subset_left
      have hTdecomp : (T \ A).card + (T ∩ A).card = T.card :=
        card_sdiff_add_card_inter T A
      have hdiff_le_Tdiff :
          (S ∩ A).card - (T ∩ A).card ≤ (T \ A).card := by
        omega
      exact hdiff_le_Tdiff.trans hright
  have hD :
      alphaNum * ((S ∩ A).card - (T ∩ A).card) ≤
        alphaDen * (Section44.edgeBoundary G A B).card :=
    (Nat.mul_le_mul_left alphaNum hdiff_le_min).trans hwell_cut
  have hSdecomp : (S \ A).card + (S ∩ A).card = S.card :=
    card_sdiff_add_card_inter S A
  simpa [B] using
    superSourceSink_cut_arith
      (α := alphaNum) (n := S.card) (sOut := (S \ A).card)
      (a := (S ∩ A).card) (b := (T ∩ A).card)
      (D := alphaDen * (Section44.edgeBoundary G A B).card)
      hSdecomp hD

/-- Every super-source/super-sink cut in the auxiliary routing network has
capacity at least `|S|`, assuming the terminal set is scaled edge-well-linked. -/
theorem routingNetwork_cutCapacity_lowerBound
    [DecidableRel G.Adj]
    {Terminals S T : Finset V} {alphaNum alphaDen : ℕ}
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card)
    {R : Finset (RoutingVertex V)}
    (hsource : RoutingVertex.source ∈ R)
    (hsink : RoutingVertex.sink ∉ R) :
    (S.card : ℝ) ≤
      (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R := by
  classical
  let A := RoutingVertex.originalSide R
  let B := (Finset.univ : Finset V) \ A
  have hnat :=
    superSourceSink_cutCapacity_lowerBound
      (G := G) (Terminals := Terminals) (S := S) (T := T) (A := A)
      (alphaNum := alphaNum) (alphaDen := alphaDen)
      hwell hS hT hcard
  have hnatR :
      (alphaNum : ℝ) * (S.card : ℝ) ≤
        (alphaNum : ℝ) * ((S \ A).card : ℝ) +
          (alphaDen : ℝ) *
            ((Section44.edgeBoundary G A ((Finset.univ : Finset V) \ A)).card : ℝ) +
            (alphaNum : ℝ) * ((T ∩ A).card : ℝ) := by
    exact_mod_cast hnat
  have hboundary_le_cross :
      ((Section44.edgeBoundary G A B).card : ℝ) ≤
        ((crossingDarts (G := G) A B).card : ℝ) := by
    exact_mod_cast edgeBoundary_card_le_crossingDarts_card (G := G) A B
  have hnatCross :
      (alphaNum : ℝ) * (S.card : ℝ) ≤
        (alphaNum : ℝ) * ((S \ A).card : ℝ) +
          (alphaDen : ℝ) * ((crossingDarts (G := G) A B).card : ℝ) +
            (alphaNum : ℝ) * ((T ∩ A).card : ℝ) := by
    have hmul :
        (alphaDen : ℝ) *
            ((Section44.edgeBoundary G A B).card : ℝ) ≤
          (alphaDen : ℝ) * ((crossingDarts (G := G) A B).card : ℝ) :=
      mul_le_mul_of_nonneg_left hboundary_le_cross (by positivity)
    simpa [B] using (by nlinarith [hnatR, hmul])
  have halpha_pos : (0 : ℝ) < alphaNum := by
    exact_mod_cast hwell.1
  have hη :
      (((scaledCongestion alphaNum alphaDen : ℚ) : ℝ)) =
        (alphaDen : ℝ) / (alphaNum : ℝ) := by
    unfold scaledCongestion
    norm_num
  have hselected_lower :
      (S.card : ℝ) ≤
        ((S \ A).card : ℝ) + ((T ∩ A).card : ℝ) +
          ((crossingDarts (G := G) A B).card : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
    rw [hη]
    field_simp [halpha_pos.ne']
    nlinarith
  have hselected_cap :
      (∑ a ∈ selectedCutArcs (G := G) S T A B,
        (RoutingArc.network G S T alphaNum alphaDen).cap a) ≤
          (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R :=
    selectedCutArcs_cap_sum_le_cutCapacity
      (G := G) (S := S) (T := T) (A := A) (B := B) (R := R)
      (alphaNum := alphaNum) (alphaDen := alphaDen)
      hsource hsink rfl rfl
  calc
    (S.card : ℝ)
        ≤ (∑ a ∈ selectedCutArcs (G := G) S T A B,
            (RoutingArc.network G S T alphaNum alphaDen).cap a) := by
          rw [selectedCutArcs_cap_sum]
          exact hselected_lower
    _ ≤ (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R :=
          hselected_cap

/-- The cut consisting only of the super-source has capacity exactly `|S|`. -/
theorem routingNetwork_sourceSingleton_cutCapacity
    [DecidableRel G.Adj]
    {S T : Finset V} {alphaNum alphaDen : ℕ} :
    (RoutingArc.network G S T alphaNum alphaDen).cutCapacity
      ({RoutingVertex.source} : Finset (RoutingVertex V)) =
        (S.card : ℝ) := by
  classical
  let N := RoutingArc.network G S T alphaNum alphaDen
  have hsource :
      sourceCutArcs (G := G) S T (∅ : Finset V) =
        Finset.univ.filter (fun a : RoutingArc G S T =>
          N.tail a ∈ ({RoutingVertex.source} : Finset (RoutingVertex V)) ∧
            N.head a ∉ ({RoutingVertex.source} : Finset (RoutingVertex V))) := by
    ext a
    cases a with
    | source v =>
        simp [sourceCutArcs, RoutingArc.network, N]
    | sink v =>
        simp [sourceCutArcs, RoutingArc.network, N]
    | dart d =>
        simp [sourceCutArcs, RoutingArc.network, N]
  calc
    N.cutCapacity ({RoutingVertex.source} : Finset (RoutingVertex V))
        = ∑ a ∈ sourceCutArcs (G := G) S T (∅ : Finset V), N.cap a := by
          unfold DirectedNetwork.cutCapacity DirectedNetwork.cutOut
          have hfilter :
              (∑ e : RoutingArc G S T,
                if N.tail e ∈ ({RoutingVertex.source} : Finset (RoutingVertex V)) ∧
                    N.head e ∉ ({RoutingVertex.source} : Finset (RoutingVertex V))
                then N.cap e else 0) =
                ∑ e ∈ (Finset.univ.filter fun a : RoutingArc G S T =>
                  N.tail a ∈ ({RoutingVertex.source} : Finset (RoutingVertex V)) ∧
                    N.head a ∉ ({RoutingVertex.source} : Finset (RoutingVertex V))),
                  N.cap e := by
            simpa using
              (Finset.sum_filter
                (s := (Finset.univ : Finset (RoutingArc G S T)))
                (p := fun a : RoutingArc G S T =>
                  N.tail a ∈ ({RoutingVertex.source} : Finset (RoutingVertex V)) ∧
                    N.head a ∉ ({RoutingVertex.source} : Finset (RoutingVertex V)))
                (f := fun a : RoutingArc G S T => N.cap a)).symm
          rw [hfilter, ← hsource]
    _ = (S.card : ℝ) := by
          simpa [N] using
            sourceCutArcs_cap_sum (G := G) (S := S) (T := T)
              (A := (∅ : Finset V)) (alphaNum := alphaNum)
              (alphaDen := alphaDen)

/-- Max-flow/min-cut supplies a maximum auxiliary flow of value `|S|`. -/
theorem exists_maximumRoutingFlow_value_card
    [DecidableRel G.Adj]
    {Terminals S T : Finset V} {alphaNum alphaDen : ℕ}
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) :
    ∃ x : RoutingArc G S T → ℝ,
      (RoutingArc.network G S T alphaNum alphaDen).IsMaximumFlow
        RoutingVertex.source RoutingVertex.sink x ∧
        (RoutingArc.network G S T alphaNum alphaDen).value
          RoutingVertex.source x = (S.card : ℝ) := by
  classical
  let N := RoutingArc.network G S T alphaNum alphaDen
  have hst : RoutingVertex.source ≠ (RoutingVertex.sink : RoutingVertex V) := by
    intro h
    cases h
  rcases N.exists_maximumFlow_minimumCut hst with ⟨x, R, hmax, hmin, hval⟩
  have hlower : (S.card : ℝ) ≤ N.cutCapacity R :=
    routingNetwork_cutCapacity_lowerBound
      (G := G) (Terminals := Terminals) (S := S) (T := T)
      (alphaNum := alphaNum) (alphaDen := alphaDen)
      hwell hS hT hcard hmin.1.1 hmin.1.2
  have hupper : N.cutCapacity R ≤ (S.card : ℝ) := by
    have hcutSource : DirectedNetwork.IsSTCut RoutingVertex.source RoutingVertex.sink
        ({RoutingVertex.source} : Finset (RoutingVertex V)) := by
      constructor <;> simp
    have hle := hmin.2 _ hcutSource
    simpa [N, routingNetwork_sourceSingleton_cutCapacity
      (G := G) (S := S) (T := T) (alphaNum := alphaNum)
      (alphaDen := alphaDen)] using hle
  refine ⟨x, hmax, ?_⟩
  linarith

/-! ## Separator cuts for extracting disjoint paths -/

namespace SeparatorCut

variable {S T X : Finset V}

/-- Vertices reachable from `S \ X` after deleting a candidate separator `X`.
This is the original-vertex side of the source cut used to contradict
Menger separators. -/
noncomputable def reachableSide (G : _root_.SimpleGraph V)
    (S X : Finset V) : Finset V := by
  classical
  let U : Finset V := (Finset.univ : Finset V) \ X
  exact U.filter fun v =>
    ∃ s ∈ S, s ∈ U ∧ (inducedOnFinset G U).Reachable s v

theorem reachableSide_subset_deleted :
    reachableSide G S X ⊆ (Finset.univ : Finset V) \ X := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).1

theorem reachableSide_disjoint_separator :
    Disjoint (reachableSide G S X) X := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hX
  exact (Finset.mem_sdiff.mp
    (reachableSide_subset_deleted (G := G) (S := S) (X := X) hv)).2 hX

theorem source_sdiff_subset_reachableSide :
    S \ X ⊆ reachableSide G S X := by
  classical
  intro s hs
  let U : Finset V := (Finset.univ : Finset V) \ X
  have hsS : s ∈ S := (Finset.mem_sdiff.mp hs).1
  have hsU : s ∈ U := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ s, (Finset.mem_sdiff.mp hs).2⟩
  rw [reachableSide, Finset.mem_filter]
  exact ⟨hsU, s, hsS, hsU, ⟨_root_.SimpleGraph.Walk.nil⟩⟩

omit [Fintype V] [DecidableEq V] in
private theorem inducedOnFinset_walk_support_subset
    {C : Finset V} {u v : V}
    (p : (inducedOnFinset G C).Walk u v) (hu : u ∈ C) :
    ∀ x : V, x ∈ p.support → x ∈ C := by
  induction p with
  | nil =>
      intro x hx
      simp at hx
      subst x
      simpa using hu
  | cons hxy p ih =>
      intro x hx
      simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hxy.2.1
      · exact ih hxy.2.2 x hx

theorem reachableSide_mem_of_adj
    {u v : V}
    (hu : u ∈ reachableSide G S X)
    (hvX : v ∉ X)
    (huv : G.Adj u v) :
    v ∈ reachableSide G S X := by
  classical
  let U : Finset V := (Finset.univ : Finset V) \ X
  have huU : u ∈ U :=
    reachableSide_subset_deleted (G := G) (S := S) (X := X) hu
  have hvU : v ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvX⟩
  change u ∈ U.filter (fun v =>
    ∃ s ∈ S, s ∈ U ∧ (inducedOnFinset G U).Reachable s v) at hu
  rcases (Finset.mem_filter.mp hu).2 with
    ⟨s, hsS, hsU, hreach⟩
  have huvU : (inducedOnFinset G U).Adj u v := ⟨huv, huU, hvU⟩
  rw [reachableSide, Finset.mem_filter]
  exact ⟨hvU, s, hsS, hsU, hreach.trans huvU.reachable⟩

theorem target_disjoint_reachableSide_of_separator
    (hsep : STSeparator G S T X) :
    Disjoint T (reachableSide G S X) := by
  classical
  rw [Finset.disjoint_left]
  intro t htT htR
  let U : Finset V := (Finset.univ : Finset V) \ X
  change t ∈ U.filter (fun v =>
    ∃ s ∈ S, s ∈ U ∧ (inducedOnFinset G U).Reachable s v) at htR
  rcases (Finset.mem_filter.mp htR).2 with
    ⟨s, hsS, hsU, hreach⟩
  rcases hreach with ⟨W⟩
  let WG : G.Walk s t := W.mapLe (inducedOnFinset_le (G := G) (C := U))
  let Wp := WG.toPath
  let P : GraphPath G :=
    { source := s
      target := t
      walk := (Wp : G.Walk s t)
      isPath := Wp.property }
  rcases hsep P (Or.inl ⟨hsS, htT⟩) with ⟨v, hvP, hvX⟩
  have hvWp : v ∈ (Wp : G.Walk s t).support := by
    simpa [P, GraphPath.vertexSet] using hvP
  have hvWG : v ∈ WG.support :=
    _root_.SimpleGraph.Walk.support_toPath_subset WG hvWp
  have hvW : v ∈ W.support := by
    simpa [WG, _root_.SimpleGraph.Walk.support_mapLe_eq_support] using hvWG
  have hvU : v ∈ U :=
    inducedOnFinset_walk_support_subset (G := G) (C := U) W hsU v hvW
  exact (Finset.mem_sdiff.mp hvU).2 hvX

/-- The auxiliary source cut corresponding to the reachable side. -/
noncomputable def sourceCut (G : _root_.SimpleGraph V)
    (S X : Finset V) : Finset (RoutingVertex V) := by
  classical
  exact insert RoutingVertex.source
    ((reachableSide G S X).image RoutingVertex.original)

theorem source_mem_sourceCut :
    RoutingVertex.source ∈ sourceCut G S X := by
  classical
  simp [sourceCut]

theorem sink_notMem_sourceCut :
    RoutingVertex.sink ∉ sourceCut G S X := by
  classical
  simp [sourceCut]

theorem original_mem_sourceCut_iff (v : V) :
    RoutingVertex.original v ∈ sourceCut G S X ↔
      v ∈ reachableSide G S X := by
  classical
  simp [sourceCut]

theorem originalSide_sourceCut :
    RoutingVertex.originalSide (sourceCut G S X) =
      reachableSide G S X := by
  classical
  ext v
  rw [RoutingVertex.mem_originalSide_iff, original_mem_sourceCut_iff]

theorem sourceCut_capacity_le
    [DecidableRel G.Adj] {alphaNum alphaDen Δ : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hsep : STSeparator G S T X) :
    (RoutingArc.network G S T alphaNum alphaDen).cutCapacity
        (sourceCut G S X) ≤
      (X.card : ℝ) +
        ((Δ * X.card : ℕ) : ℝ) *
          ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
  classical
  let A := reachableSide G S X
  let B := (Finset.univ : Finset V) \ A
  let R := sourceCut G S X
  have hcap :
      (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R =
        ((S \ A).card : ℝ) + ((T ∩ A).card : ℝ) +
          ((crossingDarts (G := G) A B).card : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
    rw [cutCapacity_eq_selectedCutArcs_cap_sum
      (G := G) (S := S) (T := T) (A := A) (B := B) (R := R)
      (alphaNum := alphaNum) (alphaDen := alphaDen)
      source_mem_sourceCut sink_notMem_sourceCut]
    · rw [selectedCutArcs_cap_sum]
    · simpa [A, R] using (originalSide_sourceCut (G := G) (S := S) (X := X)).symm
    · rfl
  have hSdiff_subset : S \ A ⊆ X := by
    intro v hv
    by_contra hvX
    have hvSX : v ∈ S \ X :=
      Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hvX⟩
    exact (Finset.mem_sdiff.mp hv).2
      (source_sdiff_subset_reachableSide (G := G) (S := S) (X := X) hvSX)
  have hTinter_zero : (T ∩ A).card = 0 := by
    have hdisj : Disjoint T A :=
      target_disjoint_reachableSide_of_separator (G := G) (S := S) (T := T) (X := X) hsep
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_iff_forall_notMem.2 (by
      intro v hv
      exact Finset.disjoint_left.mp hdisj (Finset.mem_inter.mp hv).1
        (Finset.mem_inter.mp hv).2)
  have hdart_head :
      ∀ d : G.Dart, d ∈ crossingDarts (G := G) A B → d.snd ∈ X := by
    intro d hd
    rcases (mem_crossingDarts (G := G) A B d).1 hd with ⟨hfstA, hsndB⟩
    by_contra hsndX
    have hsndA : d.snd ∈ A :=
      reachableSide_mem_of_adj (G := G) (S := S) (X := X)
        hfstA hsndX d.2
    exact (Finset.mem_sdiff.mp hsndB).2 hsndA
  have hsource_card : (S \ A).card ≤ X.card := Finset.card_le_card hSdiff_subset
  have hdart_card :
      (crossingDarts (G := G) A B).card ≤ Δ * X.card :=
    crossingDarts_card_le_maxDegree_mul_of_snd_subset
      (G := G) (A := A) (B := B) (X := X) hdegree hdart_head
  have hη_nonneg : 0 ≤ ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
    unfold scaledCongestion
    positivity
  rw [hcap, hTinter_zero]
  have hsource_cardR : ((S \ A).card : ℝ) ≤ (X.card : ℝ) := by
    exact_mod_cast hsource_card
  have hdart_cardR :
      ((crossingDarts (G := G) A B).card : ℝ) ≤ ((Δ * X.card : ℕ) : ℝ) := by
    exact_mod_cast hdart_card
  have hmul :=
    mul_le_mul_of_nonneg_right hdart_cardR hη_nonneg
  calc
    ((S \ A).card : ℝ) + (((0 : ℕ) : ℝ)) +
        ((crossingDarts (G := G) A B).card : ℝ) *
          ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ)
        ≤ (X.card : ℝ) +
            ((crossingDarts (G := G) A B).card : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
          have hsource0 :
              ((S \ A).card : ℝ) + (((0 : ℕ) : ℝ)) ≤ (X.card : ℝ) := by
            simpa using hsource_cardR
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hsource0
            (((crossingDarts (G := G) A B).card : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ))
    _ ≤ (X.card : ℝ) +
          ((Δ * X.card : ℕ) : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
          linarith

theorem sourceCut_union_separator_capacity_pair_le
    [DecidableRel G.Adj] {alphaNum alphaDen Δ : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hsep : STSeparator G S T X)
    (hdisj : Disjoint S T) :
    (RoutingArc.network G S T alphaNum alphaDen).cutCapacity
        (sourceCut G S X) +
      (RoutingArc.network G S T alphaNum alphaDen).cutCapacity
        (insert RoutingVertex.source
          (((reachableSide G S X ∪ X).image RoutingVertex.original))) ≤
      (X.card : ℝ) +
        ((Δ * X.card : ℕ) : ℝ) *
          ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
  classical
  let A := reachableSide G S X
  let A₂ := A ∪ X
  let B := (Finset.univ : Finset V) \ A
  let B₂ := (Finset.univ : Finset V) \ A₂
  let R := sourceCut G S X
  let R₂ : Finset (RoutingVertex V) :=
    insert RoutingVertex.source ((A₂).image RoutingVertex.original)
  have hsourceR₂ : RoutingVertex.source ∈ R₂ := by simp [R₂]
  have hsinkR₂ : RoutingVertex.sink ∉ R₂ := by simp [R₂]
  have horigR₂ : RoutingVertex.originalSide R₂ = A₂ := by
    ext v
    simp [RoutingVertex.mem_originalSide_iff, R₂, A₂]
  have hcap₁ :
      (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R =
        ((S \ A).card : ℝ) + ((T ∩ A).card : ℝ) +
          ((crossingDarts (G := G) A B).card : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
    rw [cutCapacity_eq_selectedCutArcs_cap_sum
      (G := G) (S := S) (T := T) (A := A) (B := B) (R := R)
      (alphaNum := alphaNum) (alphaDen := alphaDen)
      source_mem_sourceCut sink_notMem_sourceCut]
    · rw [selectedCutArcs_cap_sum]
    · simpa [A, R] using (originalSide_sourceCut (G := G) (S := S) (X := X)).symm
    · rfl
  have hcap₂ :
      (RoutingArc.network G S T alphaNum alphaDen).cutCapacity R₂ =
        ((S \ A₂).card : ℝ) + ((T ∩ A₂).card : ℝ) +
          ((crossingDarts (G := G) A₂ B₂).card : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
    rw [cutCapacity_eq_selectedCutArcs_cap_sum
      (G := G) (S := S) (T := T) (A := A₂) (B := B₂) (R := R₂)
      (alphaNum := alphaNum) (alphaDen := alphaDen)
      hsourceR₂ hsinkR₂]
    · rw [selectedCutArcs_cap_sum]
    · exact horigR₂.symm
    · rfl
  have hSdiffA_subset : S \ A ⊆ X := by
    intro v hv
    by_contra hvX
    have hvSX : v ∈ S \ X :=
      Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hvX⟩
    exact (Finset.mem_sdiff.mp hv).2
      (source_sdiff_subset_reachableSide (G := G) (S := S) (X := X) hvSX)
  have hSdiffA₂_zero : (S \ A₂).card = 0 := by
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_iff_forall_notMem.2 (by
      intro v hv
      have hvA : v ∈ A₂ := by
        by_cases hvX : v ∈ X
        · exact Finset.mem_union_right A hvX
        · have hvSX : v ∈ S \ X :=
            Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hvX⟩
          exact Finset.mem_union_left X
            (source_sdiff_subset_reachableSide (G := G) (S := S) (X := X) hvSX)
      exact (Finset.mem_sdiff.mp hv).2 hvA)
  have hTinterA_zero : (T ∩ A).card = 0 := by
    have hdisjTA : Disjoint T A :=
      target_disjoint_reachableSide_of_separator (G := G) (S := S) (T := T) (X := X) hsep
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_iff_forall_notMem.2 (by
      intro v hv
      exact Finset.disjoint_left.mp hdisjTA (Finset.mem_inter.mp hv).1
        (Finset.mem_inter.mp hv).2)
  have hendpoint_sum :
      (S \ A).card + (T ∩ A₂).card ≤ X.card := by
    have hSX : S \ A ⊆ X := hSdiffA_subset
    have hTA₂X : T ∩ A₂ ⊆ X := by
      intro v hv
      rcases Finset.mem_union.mp (Finset.mem_inter.mp hv).2 with hvA | hvX
      · have hdisjTA : Disjoint T A :=
          target_disjoint_reachableSide_of_separator
            (G := G) (S := S) (T := T) (X := X) hsep
        exact False.elim
          (Finset.disjoint_left.mp hdisjTA (Finset.mem_inter.mp hv).1 hvA)
      · exact hvX
    have hdisj_sub : Disjoint (S \ A) (T ∩ A₂) := by
      exact hdisj.mono (by intro v hv; exact (Finset.mem_sdiff.mp hv).1)
        (by intro v hv; exact (Finset.mem_inter.mp hv).1)
    have hunion_subset : (S \ A) ∪ (T ∩ A₂) ⊆ X := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hSX hv
      · exact hTA₂X hv
    have hcard_union :
        ((S \ A) ∪ (T ∩ A₂)).card = (S \ A).card + (T ∩ A₂).card := by
      rw [Finset.card_union_of_disjoint hdisj_sub]
    rw [← hcard_union]
    exact Finset.card_le_card hunion_subset
  have hD₁_subset_AX :
      crossingDarts (G := G) A B ⊆ crossingDarts (G := G) A X := by
    intro d hd
    rcases (mem_crossingDarts (G := G) A B d).1 hd with ⟨hfstA, hsndB⟩
    have hsndX : d.snd ∈ X := by
      by_contra hsndX
      have hsndA : d.snd ∈ A :=
        reachableSide_mem_of_adj (G := G) (S := S) (X := X)
          hfstA hsndX d.2
      exact (Finset.mem_sdiff.mp hsndB).2 hsndA
    exact (mem_crossingDarts (G := G) A X d).2 ⟨hfstA, hsndX⟩
  have hD₂_subset_XB :
      crossingDarts (G := G) A₂ B₂ ⊆ crossingDarts (G := G) X B₂ := by
    intro d hd
    rcases (mem_crossingDarts (G := G) A₂ B₂ d).1 hd with ⟨hfstA₂, hsndB₂⟩
    have hfstX : d.fst ∈ X := by
      rcases Finset.mem_union.mp hfstA₂ with hfstA | hfstX
      · have hsnd_notX : d.snd ∉ X := by
          intro hsndX
          exact (Finset.mem_sdiff.mp hsndB₂).2 (Finset.mem_union_right A hsndX)
        have hsndA : d.snd ∈ A :=
          reachableSide_mem_of_adj (G := G) (S := S) (X := X)
            hfstA hsnd_notX d.2
        exact False.elim
          ((Finset.mem_sdiff.mp hsndB₂).2 (Finset.mem_union_left X hsndA))
      · exact hfstX
    exact (mem_crossingDarts (G := G) X B₂ d).2 ⟨hfstX, hsndB₂⟩
  have hAB₂ : Disjoint A B₂ := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact (Finset.mem_sdiff.mp hvB).2 (Finset.mem_union_left X hvA)
  have hmiddle :
      (crossingDarts (G := G) A X).card +
          (crossingDarts (G := G) X B₂).card ≤ Δ * X.card :=
    crossingDarts_card_add_le_maxDegree_mul_middle
      (G := G) (A := A) (X := X) (B := B₂) hdegree hAB₂
  have hdart_sum :
      (crossingDarts (G := G) A B).card +
          (crossingDarts (G := G) A₂ B₂).card ≤ Δ * X.card := by
    exact Nat.add_le_add (Finset.card_le_card hD₁_subset_AX)
      (Finset.card_le_card hD₂_subset_XB) |>.trans hmiddle
  have hη_nonneg : 0 ≤ ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
    unfold scaledCongestion
    positivity
  rw [hcap₁, hcap₂, hTinterA_zero, hSdiffA₂_zero]
  have hendpointR :
      (((S \ A).card : ℝ) + ((T ∩ A₂).card : ℝ)) ≤ (X.card : ℝ) := by
    exact_mod_cast hendpoint_sum
  have hdartR :
      (((crossingDarts (G := G) A B).card : ℝ) +
        ((crossingDarts (G := G) A₂ B₂).card : ℝ)) ≤
          ((Δ * X.card : ℕ) : ℝ) := by
    exact_mod_cast hdart_sum
  have hmul :=
    mul_le_mul_of_nonneg_right hdartR hη_nonneg
  calc
    ((S \ A).card : ℝ) + (((0 : ℕ) : ℝ)) +
          ((crossingDarts (G := G) A B).card : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) +
        ((((0 : ℕ) : ℝ)) + ((T ∩ A₂).card : ℝ) +
          ((crossingDarts (G := G) A₂ B₂).card : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ))
        = (((S \ A).card : ℝ) + ((T ∩ A₂).card : ℝ)) +
            (((crossingDarts (G := G) A B).card : ℝ) +
              ((crossingDarts (G := G) A₂ B₂).card : ℝ)) *
                ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
          ring_nf
    _ ≤ (X.card : ℝ) +
          ((Δ * X.card : ℕ) : ℝ) *
            ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
          nlinarith

end SeparatorCut

/-- Equal-size terminal subsets of a scaled cut-well-linked set contain many
node-disjoint paths in a bounded-degree graph.

The size bound is written without division:
`10 * Δ * alphaDen * k ≤ 3 * alphaNum * |S|`. -/
theorem hasDisjointSTPaths_of_scaledEdgeWellLinked
    {Terminals S T : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card)
    (hk : 10 * Δ * alphaDen * k ≤ 3 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  rcases Menger.finite_vertex_menger_sharp (G := G) S T k with hpaths | hsepSmall
  · exact hpaths
  · rcases hsepSmall with ⟨X, hXcard, hsep⟩
    let N := RoutingArc.network G S T alphaNum alphaDen
    rcases exists_maximumRoutingFlow_value_card
        (G := G) (Terminals := Terminals) (S := S) (T := T)
        (alphaNum := alphaNum) (alphaDen := alphaDen)
        hwell hS hT hcard with
      ⟨x, hmax, hval⟩
    let R := SeparatorCut.sourceCut G S X
    have hcut : N.value RoutingVertex.source x ≤ N.cutCapacity R :=
      N.value_le_cutCapacity_of_cut hmax.1
        (SeparatorCut.source_mem_sourceCut (G := G) (S := S) (X := X))
        (SeparatorCut.sink_notMem_sourceCut (G := G) (S := S) (X := X))
    have hcap :
        N.cutCapacity R ≤
          (X.card : ℝ) +
            ((Δ * X.card : ℕ) : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) :=
      SeparatorCut.sourceCut_capacity_le
        (G := G) (S := S) (T := T) (X := X)
        (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ)
        hdegree hsep
    have hS_le :
        (S.card : ℝ) ≤
          (X.card : ℝ) +
            ((Δ * X.card : ℕ) : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
      nlinarith [hcut, hcap, hval]
    have hη :
        ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) =
          (alphaDen : ℝ) / (alphaNum : ℝ) := by
      unfold scaledCongestion
      norm_num
    have hαpos : (0 : ℝ) < alphaNum := by exact_mod_cast hwell.1
    have hβpos : (0 : ℝ) < alphaDen := by
      exact_mod_cast (hwell.1.trans_le hwell.2.1)
    have hΔpos : (0 : ℝ) < Δ := by
      exact_mod_cast (by omega : 0 < Δ)
    have hαleβ : (alphaNum : ℝ) ≤ alphaDen := by exact_mod_cast hwell.2.1
    have hΔge : (3 : ℝ) ≤ Δ := by exact_mod_cast hDelta
    have hkR :
        (10 * Δ * alphaDen * k : ℝ) ≤
          (3 * alphaNum * S.card : ℝ) := by
      exact_mod_cast hk
    have hcoef_pos :
        0 < 1 + (Δ : ℝ) *
          ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
      rw [hη]
      positivity
    have hXlt : (X.card : ℝ) < (k : ℝ) := by
      exact_mod_cast hXcard
    have hX_bound :
        (X.card : ℝ) +
            ((Δ * X.card : ℕ) : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) <
          (k : ℝ) *
            (1 + (Δ : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ)) := by
      rw [hη]
      norm_num [Nat.cast_mul]
      have hlt := mul_lt_mul_of_pos_right hXlt
        (by positivity : 0 < 1 + (Δ : ℝ) * ((alphaDen : ℝ) / alphaNum))
      convert hlt using 1
      ring_nf
    have hk_bound :
        (k : ℝ) *
            (1 + (Δ : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ)) ≤
          (S.card : ℝ) := by
      rw [hη]
      field_simp [hαpos.ne']
      have hmain : (alphaNum : ℝ) * k + (Δ : ℝ) * alphaDen * k ≤
          (alphaNum : ℝ) * S.card := by
        have hα_le_Δβ : (alphaNum : ℝ) ≤ (Δ : ℝ) * alphaDen := by
          nlinarith
        have hαk_le : (alphaNum : ℝ) * k ≤
            ((Δ : ℝ) * alphaDen) * k := by
          exact mul_le_mul_of_nonneg_right hα_le_Δβ (by positivity)
        have hroute : ((Δ : ℝ) * alphaDen) * k ≤
            (3 / 10 : ℝ) * alphaNum * S.card := by
          nlinarith
        nlinarith
      nlinarith
    linarith

/-- Sharpened version for disjoint terminal subsets.

The size bound is written without division:
`5 * Δ * alphaDen * k ≤ 6 * alphaNum * |S|`. -/
theorem hasDisjointSTPaths_of_scaledEdgeWellLinked_disjoint
    {Terminals S T : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) (hdisj : Disjoint S T)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  rcases Menger.finite_vertex_menger_sharp (G := G) S T k with hpaths | hsepSmall
  · exact hpaths
  · rcases hsepSmall with ⟨X, hXcard, hsep⟩
    let N := RoutingArc.network G S T alphaNum alphaDen
    rcases exists_maximumRoutingFlow_value_card
        (G := G) (Terminals := Terminals) (S := S) (T := T)
        (alphaNum := alphaNum) (alphaDen := alphaDen)
        hwell hS hT hcard with
      ⟨x, hmax, hval⟩
    let R := SeparatorCut.sourceCut G S X
    let A₂ := SeparatorCut.reachableSide G S X ∪ X
    let R₂ : Finset (RoutingVertex V) :=
      insert RoutingVertex.source (A₂.image RoutingVertex.original)
    have hcut₁ : N.value RoutingVertex.source x ≤ N.cutCapacity R :=
      N.value_le_cutCapacity_of_cut hmax.1
        (SeparatorCut.source_mem_sourceCut (G := G) (S := S) (X := X))
        (SeparatorCut.sink_notMem_sourceCut (G := G) (S := S) (X := X))
    have hcut₂ : N.value RoutingVertex.source x ≤ N.cutCapacity R₂ := by
      apply N.value_le_cutCapacity_of_cut hmax.1
      · simp [R₂]
      · simp [R₂]
    have hcap_pair :
        N.cutCapacity R + N.cutCapacity R₂ ≤
          (X.card : ℝ) +
            ((Δ * X.card : ℕ) : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) :=
      SeparatorCut.sourceCut_union_separator_capacity_pair_le
        (G := G) (S := S) (T := T) (X := X)
        (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ)
        hdegree hsep hdisj
    have hS_pair :
        2 * (S.card : ℝ) ≤
          (X.card : ℝ) +
            ((Δ * X.card : ℕ) : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
      nlinarith [hcut₁, hcut₂, hcap_pair, hval]
    have hη :
        ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) =
          (alphaDen : ℝ) / (alphaNum : ℝ) := by
      unfold scaledCongestion
      norm_num
    have hαpos : (0 : ℝ) < alphaNum := by exact_mod_cast hwell.1
    have hβpos : (0 : ℝ) < alphaDen := by
      exact_mod_cast (hwell.1.trans_le hwell.2.1)
    have hαleβ : (alphaNum : ℝ) ≤ alphaDen := by exact_mod_cast hwell.2.1
    have hΔge : (3 : ℝ) ≤ Δ := by exact_mod_cast hDelta
    have hkR :
        (5 * Δ * alphaDen * k : ℝ) ≤
          (6 * alphaNum * S.card : ℝ) := by
      exact_mod_cast hk
    have hXlt : (X.card : ℝ) < (k : ℝ) := by
      exact_mod_cast hXcard
    have hcoef_pos :
        0 < 1 + (Δ : ℝ) *
          ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) := by
      rw [hη]
      positivity
    have hX_bound :
        (X.card : ℝ) +
            ((Δ * X.card : ℕ) : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ) <
          (k : ℝ) *
            (1 + (Δ : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ)) := by
      rw [hη]
      norm_num [Nat.cast_mul]
      have hlt := mul_lt_mul_of_pos_right hXlt
        (by positivity : 0 < 1 + (Δ : ℝ) * ((alphaDen : ℝ) / alphaNum))
      convert hlt using 1
      ring_nf
    have hk_bound :
        (k : ℝ) *
            (1 + (Δ : ℝ) *
              ((scaledCongestion alphaNum alphaDen : ℚ) : ℝ)) ≤
          2 * (S.card : ℝ) := by
      rw [hη]
      field_simp [hαpos.ne']
      have hmain : (alphaNum : ℝ) * k + (Δ : ℝ) * alphaDen * k ≤
          2 * (alphaNum : ℝ) * S.card := by
        have hthreeα_le_Δβ : 3 * (alphaNum : ℝ) ≤ (Δ : ℝ) * alphaDen := by
          nlinarith
        have h3αk_le : 3 * ((alphaNum : ℝ) * k) ≤
            ((Δ : ℝ) * alphaDen) * k := by
          have hmul := mul_le_mul_of_nonneg_right hthreeα_le_Δβ
            (by positivity : 0 ≤ (k : ℝ))
          nlinarith
        have hroute : ((Δ : ℝ) * alphaDen) * k ≤
            (6 / 5 : ℝ) * alphaNum * S.card := by
          nlinarith
        nlinarith
      nlinarith
    linarith

end FlowWellLinked

end SimpleGraph

end Lax17Proofs
