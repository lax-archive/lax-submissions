import Lax17Proofs.Source.TreewidthSparsifierTheorem51Rails

namespace Lax17Proofs

universe u v w

/-!
# Lifting transcript cuts to physical cuts

This file gives a direct cut proof for the last step of Theorem 5.1.  It uses
the whole red rails rather than the paper's shorter segment contraction.
There is only one matching incidence at a rail in each recorded round, so the
degree of the whole-rail transcript is at most the number of records.  This
loses only a polylogarithmic factor.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

open CutMatchingGame


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

private theorem reachable_map_eq
    {K : _root_.SimpleGraph V} {X : Type*} (f : V → X)
    (hadj : ∀ ⦃u v : V⦄, K.Adj u v → f u = f v)
    {u v : V} (huv : K.Reachable u v) :
    f u = f v := by
  rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv using Relation.ReflTransGen.trans_induction_on with
  | refl => rfl
  | single h => exact hadj h
  | trans _ _ hxy hyz => exact hxy.trans hyz

/-- The explicitly named first terminal is carried by its own rail. -/
theorem initialTerminal_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (x : Fin h) :
    E.RedCarrier hbudget (E.initialTerminal hrecords x) x := by
  left
  refine ⟨E.firstRecord hrecords, ?_⟩
  have hsource :
      (E.localRedPath (E.firstRecord hrecords) x).source =
        E.initialTerminal hrecords x := by
    simp [initialTerminal]
  rw [← hsource]
  exact GraphPath.source_mem_vertexSet _

/-- Rail ownership is constant on every red connected component. -/
theorem railOwner_eq_of_redReachable
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (fallback : Fin h) {u v : V}
    (huv : (E.redSupport hbudget).Reachable u v) :
    E.railOwner hbudget fallback u =
      E.railOwner hbudget fallback v :=
  reachable_map_eq (K := E.redSupport hbudget)
    (E.railOwner hbudget fallback)
    (by
      intro u v huv
      exact E.railOwner_eq_of_redSupport_adj hbudget fallback huv)
    huv

/-- A path whose endpoints lie on opposite sides of a full vertex partition
contains an edge of that cut. -/
theorem path_exists_edgeBoundary_of_endpoints_opposite
    {K : _root_.SimpleGraph V} (Q : GraphPath K)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (hsource : Q.source ∈ X) (htarget : Q.target ∈ Y) :
    ∃ e ∈ Q.edgeSet, e ∈ Section44.edgeBoundary K X Y := by
  apply
    Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
      Q
  · intro v hv
    rw [hcover]
    exact Finset.mem_univ v
  · exact hsource
  · intro hsub
    have : Q.target ∈ X := hsub (GraphPath.target_mem_vertexSet Q)
    exact Finset.disjoint_left.mp hdisjoint this htarget

/-- A rail crosses a physical vertex cut when one of its carried vertices is
on the opposite side from its initial terminal. -/
def RailCrossesCut
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V) (x : Fin h) : Prop :=
  ∃ v : V, E.RedCarrier hbudget v x ∧
    ((E.initialTerminal hrecords x ∈ X ∧ v ∈ Y) ∨
      (E.initialTerminal hrecords x ∈ Y ∧ v ∈ X))

noncomputable def crossingRails
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (E.RailCrossesCut hbudget hrecords X Y)

@[simp] theorem mem_crossingRails
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V) (x : Fin h) :
    x ∈ E.crossingRails hbudget hrecords X Y ↔
      E.RailCrossesCut hbudget hrecords X Y x := by
  classical
  simp [crossingRails]

noncomputable def crossingRailWitness
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) : V :=
  Classical.choose ((E.mem_crossingRails hbudget hrecords X Y x.1).mp x.2)

theorem crossingRailWitness_spec
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    E.RedCarrier hbudget
        (E.crossingRailWitness hbudget hrecords X Y x) x.1 ∧
      ((E.initialTerminal hrecords x.1 ∈ X ∧
          E.crossingRailWitness hbudget hrecords X Y x ∈ Y) ∨
        (E.initialTerminal hrecords x.1 ∈ Y ∧
          E.crossingRailWitness hbudget hrecords X Y x ∈ X)) :=
  Classical.choose_spec
    ((E.mem_crossingRails hbudget hrecords X Y x.1).mp x.2)

noncomputable def crossingRailPath
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    GraphPath (E.redSupport hbudget) := by
  let hr :=
    E.initialTerminal_reachable_of_redCarrier hbudget hrecords
      (E.crossingRailWitness_spec hbudget hrecords X Y x).1
  let w := Classical.choose hr.exists_isPath
  exact ⟨E.initialTerminal hrecords x.1,
    E.crossingRailWitness hbudget hrecords X Y x,
    w, Classical.choose_spec hr.exists_isPath⟩

@[simp] theorem crossingRailPath_source
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    (E.crossingRailPath hbudget hrecords X Y x).source =
      E.initialTerminal hrecords x.1 := rfl

@[simp] theorem crossingRailPath_target
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X Y : Finset V)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    (E.crossingRailPath hbudget hrecords X Y x).target =
      E.crossingRailWitness hbudget hrecords X Y x := rfl

theorem exists_crossingRailEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    ∃ e : Sym2 V,
      e ∈ (E.crossingRailPath hbudget hrecords X Y x).edgeSet ∧
        e ∈ Section44.edgeBoundary (E.redSupport hbudget) X Y := by
  classical
  let Q := E.crossingRailPath hbudget hrecords X Y x
  by_cases hx : E.initialTerminal hrecords x.1 ∈ X
  ·
    have hvY :
        E.crossingRailWitness hbudget hrecords X Y x ∈ Y := by
      rcases (E.crossingRailWitness_spec hbudget hrecords X Y x).2 with
        hside | hside
      · exact hside.2
      · exact False.elim
          (Finset.disjoint_left.mp hdisjoint hx hside.1)
    exact
      path_exists_edgeBoundary_of_endpoints_opposite Q
        hcover hdisjoint (by simpa [Q] using hx)
        (by simpa [Q] using hvY)
  ·
    have hinitY : E.initialTerminal hrecords x.1 ∈ Y := by
      have hu : E.initialTerminal hrecords x.1 ∈ X ∪ Y := by
        rw [hcover]
        simp
      exact (Finset.mem_union.mp hu).resolve_left hx
    have hvX :
        E.crossingRailWitness hbudget hrecords X Y x ∈ X := by
      rcases (E.crossingRailWitness_spec hbudget hrecords X Y x).2 with
        hside | hside
      · exact False.elim (hx hside.1)
      · exact hside.2
    obtain ⟨e, heQ, heCut⟩ :=
      path_exists_edgeBoundary_of_endpoints_opposite Q.reverse
        hcover hdisjoint (by simpa [Q] using hvX)
        (by simpa [Q] using hinitY)
    exact ⟨e, by simpa using heQ, heCut⟩

noncomputable def crossingRailEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    Sym2 V :=
  Classical.choose
    (E.exists_crossingRailEdge hbudget hrecords hcover hdisjoint x)

theorem crossingRailEdge_mem_path
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    E.crossingRailEdge hbudget hrecords hcover hdisjoint x ∈
      (E.crossingRailPath hbudget hrecords X Y x).edgeSet := by
  exact
    (Classical.choose_spec
      (E.exists_crossingRailEdge hbudget hrecords hcover hdisjoint x)).1

theorem crossingRailEdge_mem_boundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    E.crossingRailEdge hbudget hrecords hcover hdisjoint x ∈
      Section44.edgeBoundary (E.redSupport hbudget) X Y := by
  exact
    (Classical.choose_spec
      (E.exists_crossingRailEdge hbudget hrecords hcover hdisjoint x)).2

theorem crossingRailEdge_owner
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) (fallback : Fin h)
    (x : {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y}) :
    E.railOwner hbudget fallback
        (E.crossingRailEdge hbudget hrecords hcover hdisjoint x).out.1 =
      x.1 := by
  let Q := E.crossingRailPath hbudget hrecords X Y x
  have he :=
    E.crossingRailEdge_mem_path hbudget hrecords hcover hdisjoint x
  have he' :
      s((E.crossingRailEdge hbudget hrecords hcover hdisjoint x).out.1,
        (E.crossingRailEdge hbudget hrecords hcover hdisjoint x).out.2) ∈
        Q.edgeSet := by
    rw [Sym2.mk,
      (E.crossingRailEdge hbudget hrecords hcover hdisjoint x).out_eq]
    simpa [Q] using he
  have hv :
      (E.crossingRailEdge hbudget hrecords hcover hdisjoint x).out.1 ∈
        Q.vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet Q he').1
  have hreach : (E.redSupport hbudget).Reachable Q.source
      (E.crossingRailEdge hbudget hrecords hcover hdisjoint x).out.1 :=
    (Q.takeUntil hv).walk.reachable
  have howner :=
    E.railOwner_eq_of_redReachable hbudget fallback hreach
  have hsourceCarrier :=
    E.initialTerminal_redCarrier hbudget hrecords x.1
  have hQsource :
      Q.source = E.initialTerminal hrecords x.1 := by
    rfl
  rw [hQsource] at howner
  rw [E.railOwner_eq_of_redCarrier hbudget fallback hsourceCarrier] at howner
  exact howner.symm

/-- Distinct crossing rails charge distinct physical red cut edges. -/
theorem crossingRailEdge_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) (fallback : Fin h) :
    Function.Injective
      (E.crossingRailEdge hbudget hrecords hcover hdisjoint) := by
  intro x y hxy
  apply Subtype.ext
  have hx :=
    E.crossingRailEdge_owner hbudget hrecords hcover hdisjoint fallback x
  have hy :=
    E.crossingRailEdge_owner hbudget hrecords hcover hdisjoint fallback y
  rw [hxy] at hx
  exact hx.symm.trans hy

theorem edgeBoundary_mono
    {H K : _root_.SimpleGraph V} (hHK : H ≤ K)
    (X Y : Finset V) :
    Section44.edgeBoundary H X Y ⊆
      Section44.edgeBoundary K X Y := by
  intro e he
  rcases (Section44.mem_edgeBoundary (G := H) X Y e).1 he with
    ⟨heH, x, hx, y, hy, rfl⟩
  exact (Section44.mem_edgeBoundary (G := K) X Y s(x, y)).2
    ⟨_root_.SimpleGraph.edgeSet_mono hHK heH, x, hx, y, hy, rfl⟩

/-- The number of rails changing physical side is bounded by the physical
cut size in every thinning outcome. -/
theorem crossingRails_card_le_edgeBoundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (outcome :
      BlueThinningInput.Outcome
        (H := E.assembledSupport hbudget))
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) (fallback : Fin h) :
    (E.crossingRails hbudget hrecords X Y).card ≤
      (Section44.edgeBoundary
        ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y).card := by
  classical
  let f :
      {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y} →
        {e : Sym2 V //
          e ∈ Section44.edgeBoundary
            ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y} :=
    fun x =>
      ⟨E.crossingRailEdge hbudget hrecords hcover hdisjoint x,
        edgeBoundary_mono
          (E.redSupport_le_thinnedGraph hbudget outcome) X Y
          (E.crossingRailEdge_mem_boundary
            hbudget hrecords hcover hdisjoint x)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact E.crossingRailEdge_injective
      hbudget hrecords hcover hdisjoint fallback
      (congrArg Subtype.val hxy)
  calc
    (E.crossingRails hbudget hrecords X Y).card =
        Fintype.card
          {x : Fin h // x ∈ E.crossingRails hbudget hrecords X Y} := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card
          {e : Sym2 V //
            e ∈ Section44.edgeBoundary
              ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y} :=
      Fintype.card_le_of_injective f hf
    _ = (Section44.edgeBoundary
          ((E.blueThinningInput hbudget).thinnedGraph outcome) X Y).card := by
      rw [Fintype.card_coe]

/-- Transcript boundary instances incident with a chosen set of rail labels. -/
noncomputable def incidentBoundaryRecords
    (E : ExpanderBlocks P count) (S B : Finset (Fin h)) :
    Finset (E.RecordBoundary S) := by
  classical
  exact Finset.univ.filter fun z =>
    z.2.1.1 ∈ B ∨
      (E.recordAt z.1).round.matching.rightEndpoint z.2.1 ∈ B

@[simp] theorem mem_incidentBoundaryRecords
    (E : ExpanderBlocks P count) (S B : Finset (Fin h))
    (z : E.RecordBoundary S) :
    z ∈ E.incidentBoundaryRecords S B ↔
      z.2.1.1 ∈ B ∨
        (E.recordAt z.1).round.matching.rightEndpoint z.2.1 ∈ B := by
  classical
  simp [incidentBoundaryRecords]

private theorem sourceIncident_card_le
    (E : ExpanderBlocks P count) (S B : Finset (Fin h)) :
    (Finset.univ.filter fun z : E.RecordBoundary S =>
      z.2.1.1 ∈ B).card ≤ E.finalState.records.length * B.card := by
  classical
  let f :
      {z : E.RecordBoundary S //
        z ∈ (Finset.univ.filter fun z : E.RecordBoundary S =>
          z.2.1.1 ∈ B)} →
        Fin E.finalState.records.length × {x : Fin h // x ∈ B} :=
    fun z => ⟨z.1.1, ⟨z.1.2.1.1,
      (Finset.mem_filter.mp z.2).2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨j, x⟩, hx⟩ ⟨⟨k, y⟩, hy⟩ hxy
    dsimp only [f] at hxy
    have hj : j = k := congrArg Prod.fst hxy
    subst k
    have hlabel : x.1.1 = y.1.1 :=
      congrArg (fun q => q.2.1) hxy
    have hleft : x.1 = y.1 := Subtype.ext hlabel
    have hxy' : x = y := Subtype.ext hleft
    subst y
    rfl
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hc

private theorem targetIncident_card_le
    (E : ExpanderBlocks P count) (S B : Finset (Fin h)) :
    (Finset.univ.filter fun z : E.RecordBoundary S =>
      (E.recordAt z.1).round.matching.rightEndpoint z.2.1 ∈ B).card ≤
        E.finalState.records.length * B.card := by
  classical
  let f :
      {z : E.RecordBoundary S //
        z ∈ (Finset.univ.filter fun z : E.RecordBoundary S =>
          (E.recordAt z.1).round.matching.rightEndpoint z.2.1 ∈ B)} →
        Fin E.finalState.records.length × {x : Fin h // x ∈ B} :=
    fun z => ⟨z.1.1,
      ⟨(E.recordAt z.1.1).round.matching.rightEndpoint z.1.2.1,
        (Finset.mem_filter.mp z.2).2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨j, x⟩, hx⟩ ⟨⟨k, y⟩, hy⟩ hxy
    dsimp only [f] at hxy
    have hj : j = k := congrArg Prod.fst hxy
    subst k
    have htarget :
        (E.recordAt j).round.matching.rightEndpoint x.1 =
          (E.recordAt j).round.matching.rightEndpoint y.1 :=
      congrArg (fun q => q.2.1) hxy
    have hxy' : x = y := by
      apply Subtype.ext
      apply (E.recordAt j).round.matching.toEquiv.injective
      exact Subtype.ext htarget
    subst y
    rfl
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hc

/-- At most two boundary incidences per record are charged to each bad rail. -/
theorem incidentBoundaryRecords_card_le
    (E : ExpanderBlocks P count) (S B : Finset (Fin h)) :
    (E.incidentBoundaryRecords S B).card ≤
      2 * E.finalState.records.length * B.card := by
  classical
  let L : Finset (E.RecordBoundary S) :=
    Finset.univ.filter fun z => z.2.1.1 ∈ B
  let R : Finset (E.RecordBoundary S) :=
    Finset.univ.filter fun z =>
      (E.recordAt z.1).round.matching.rightEndpoint z.2.1 ∈ B
  have hsubset :
      E.incidentBoundaryRecords S B ⊆ L ∪ R := by
    intro z hz
    rw [E.mem_incidentBoundaryRecords] at hz
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, L, R]
    exact hz
  have hL := E.sourceIncident_card_le S B
  have hR := E.targetIncident_card_le S B
  have hunion : (L ∪ R).card ≤ L.card + R.card :=
    Finset.card_union_le L R
  dsimp [L] at hL
  dsimp [R] at hR
  calc
    (E.incidentBoundaryRecords S B).card ≤ (L ∪ R).card :=
      Finset.card_le_card hsubset
    _ ≤ L.card + R.card := hunion
    _ ≤ E.finalState.records.length * B.card +
          E.finalState.records.length * B.card :=
      Nat.add_le_add hL hR
    _ = 2 * E.finalState.records.length * B.card := by
      simp [two_mul, Nat.add_mul]

/-- Labels whose initial terminals lie on one side of a physical cut. -/
noncomputable def terminalSide
    (E : ExpanderBlocks P count)
    (hrecords : 0 < E.finalState.records.length)
    (X : Finset V) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun x => E.initialTerminal hrecords x ∈ X

@[simp] theorem mem_terminalSide
    (E : ExpanderBlocks P count)
    (hrecords : 0 < E.finalState.records.length)
    (X : Finset V) (x : Fin h) :
    x ∈ E.terminalSide hrecords X ↔
      E.initialTerminal hrecords x ∈ X := by
  classical
  simp [terminalSide]

theorem redCarrier_mem_left_of_not_crossing
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    {x : Fin h} (hx :
      x ∉ E.crossingRails hbudget hrecords X Y)
    {v : V} (hv : E.RedCarrier hbudget v x)
    (hinit : E.initialTerminal hrecords x ∈ X) :
    v ∈ X := by
  have hnot :
      ¬ E.RailCrossesCut hbudget hrecords X Y x := by
    simpa [E.mem_crossingRails hbudget hrecords X Y x] using hx
  have hvUnion : v ∈ X ∪ Y := by
    rw [hcover]
    exact Finset.mem_univ v
  rcases Finset.mem_union.mp hvUnion with hvX | hvY
  · exact hvX
  · exact False.elim (hnot ⟨v, hv, Or.inl ⟨hinit, hvY⟩⟩)

theorem redCarrier_mem_right_of_not_crossing
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    {x : Fin h} (hx :
      x ∉ E.crossingRails hbudget hrecords X Y)
    {v : V} (hv : E.RedCarrier hbudget v x)
    (hinit : E.initialTerminal hrecords x ∈ Y) :
    v ∈ Y := by
  have hnot :
      ¬ E.RailCrossesCut hbudget hrecords X Y x := by
    simpa [E.mem_crossingRails hbudget hrecords X Y x] using hx
  have hvUnion : v ∈ X ∪ Y := by
    rw [hcover]
    exact Finset.mem_univ v
  rcases Finset.mem_union.mp hvUnion with hvX | hvY
  · exact False.elim (hnot ⟨v, hv, Or.inr ⟨hinit, hvX⟩⟩)
  · exact hvY

theorem localBluePath_source_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left}) :
    E.RedCarrier hbudget (E.localBluePath j x).source x.1 := by
  left
  refine ⟨j, ?_⟩
  rw [E.localBluePath_source]
  simpa [E.localRedPath_source] using
    GraphPath.source_mem_vertexSet (E.localRedPath j x.1)

theorem localBluePath_target_redCarrier
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (j : Fin E.finalState.records.length)
    (x : {x : Fin h // x ∈ (E.recordAt j).cut.left}) :
    E.RedCarrier hbudget (E.localBluePath j x).target
      ((E.recordAt j).round.matching.rightEndpoint x) := by
  left
  refine ⟨j, ?_⟩
  rw [E.localBluePath_target]
  simpa [E.localRedPath_source] using
    GraphPath.source_mem_vertexSet
      (E.localRedPath j
        ((E.recordAt j).round.matching.rightEndpoint x))

/-- Boundary records whose two prescribed endpoint rails do not cross the
physical cut. -/
noncomputable def cleanBoundaryRecords
    (E : ExpanderBlocks P count)
    (S B : Finset (Fin h)) : Finset (E.RecordBoundary S) :=
  Finset.univ \ E.incidentBoundaryRecords S B

@[simp] theorem mem_cleanBoundaryRecords
    (E : ExpanderBlocks P count)
    (S B : Finset (Fin h)) (z : E.RecordBoundary S) :
    z ∈ E.cleanBoundaryRecords S B ↔
      z ∉ E.incidentBoundaryRecords S B := by
  classical
  simp [cleanBoundaryRecords]

theorem recordBoundary_card_le_incident_add_clean
    (E : ExpanderBlocks P count)
    (S B : Finset (Fin h)) :
    Fintype.card (E.RecordBoundary S) ≤
      (E.incidentBoundaryRecords S B).card +
        (E.cleanBoundaryRecords S B).card := by
  classical
  have hcover :
      (Finset.univ : Finset (E.RecordBoundary S)) ⊆
        E.incidentBoundaryRecords S B ∪ E.cleanBoundaryRecords S B := by
    intro z _hz
    by_cases hi : z ∈ E.incidentBoundaryRecords S B
    · exact Finset.mem_union.mpr (Or.inl hi)
    · exact Finset.mem_union.mpr
        (Or.inr ((E.mem_cleanBoundaryRecords S B z).2 hi))
  calc
    Fintype.card (E.RecordBoundary S) =
        (Finset.univ : Finset (E.RecordBoundary S)).card := by simp
    _ ≤ (E.incidentBoundaryRecords S B ∪
          E.cleanBoundaryRecords S B).card :=
      Finset.card_le_card hcover
    _ ≤ (E.incidentBoundaryRecords S B).card +
          (E.cleanBoundaryRecords S B).card :=
      Finset.card_union_le _ _

theorem exists_cleanRecordBoundaryEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (z : {z : E.RecordBoundary (E.terminalSide hrecords X) //
      z ∈ E.cleanBoundaryRecords
        (E.terminalSide hrecords X)
        (E.crossingRails hbudget hrecords X Y)}) :
    ∃ e : Sym2 V,
      e ∈ (E.localBluePath z.1.1 z.1.2.1).edgeSet ∧
        e ∈ Section44.edgeBoundary
          (E.assembledSupport hbudget) X Y := by
  classical
  let S := E.terminalSide hrecords X
  let B := E.crossingRails hbudget hrecords X Y
  let j := z.1.1
  let x := z.1.2.1
  let y := (E.recordAt j).round.matching.rightEndpoint x
  let Q := E.localBluePath j x
  have hzClean :
      z.1 ∉ E.incidentBoundaryRecords S B := by
    exact (E.mem_cleanBoundaryRecords S B z.1).1 (by
      simpa [S, B] using z.2)
  have hxNot : x.1 ∉ B := by
    intro hx
    exact hzClean ((E.mem_incidentBoundaryRecords S B z.1).2
      (Or.inl hx))
  have hyNot : y ∉ B := by
    intro hy
    exact hzClean ((E.mem_incidentBoundaryRecords S B z.1).2
      (Or.inr (by simpa [j, x, y] using hy)))
  have hxCarrier :
      E.RedCarrier hbudget Q.source x.1 := by
    simpa [Q, j, x] using E.localBluePath_source_redCarrier hbudget j x
  have hyCarrier :
      E.RedCarrier hbudget Q.target y := by
    simpa [Q, j, x, y] using
      E.localBluePath_target_redCarrier hbudget j x
  have hcross :
      (E.recordAt j).round.edgeCrosses S x := by
    exact LazyRound.mem_edgeBoundary.mp z.1.2.2
  have htoAssembled :
      Section44.edgeBoundary (E.recordAt j).layer.localGraph X Y ⊆
        Section44.edgeBoundary (E.assembledSupport hbudget) X Y :=
    edgeBoundary_mono
      (E.recordAt_localGraph_le_assembledSupport hbudget j) X Y
  rcases hcross with hforward | hbackward
  · have hxInit : E.initialTerminal hrecords x.1 ∈ X := by
      exact (E.mem_terminalSide hrecords X x.1).1 hforward.1
    have hyInit : E.initialTerminal hrecords y ∈ Y := by
      have hyNotX :
          E.initialTerminal hrecords y ∉ X := by
        simpa [S, E.mem_terminalSide hrecords X y] using hforward.2
      have hu : E.initialTerminal hrecords y ∈ X ∪ Y := by
        rw [hcover]
        simp
      exact (Finset.mem_union.mp hu).resolve_left hyNotX
    have hsourceX : Q.source ∈ X :=
      E.redCarrier_mem_left_of_not_crossing
        hbudget hrecords hcover hdisjoint hxNot hxCarrier hxInit
    have htargetY : Q.target ∈ Y :=
      E.redCarrier_mem_right_of_not_crossing
        hbudget hrecords hcover hdisjoint hyNot hyCarrier hyInit
    obtain ⟨e, heQ, heCut⟩ :=
      path_exists_edgeBoundary_of_endpoints_opposite
        Q hcover hdisjoint hsourceX htargetY
    exact ⟨e, by simpa [Q, j, x] using heQ, htoAssembled heCut⟩
  · have hyInit : E.initialTerminal hrecords y ∈ X := by
      exact (E.mem_terminalSide hrecords X y).1 hbackward.1
    have hxInit : E.initialTerminal hrecords x.1 ∈ Y := by
      have hxNotX :
          E.initialTerminal hrecords x.1 ∉ X := by
        simpa [S, E.mem_terminalSide hrecords X x.1] using hbackward.2
      have hu : E.initialTerminal hrecords x.1 ∈ X ∪ Y := by
        rw [hcover]
        simp
      exact (Finset.mem_union.mp hu).resolve_left hxNotX
    have htargetX : Q.target ∈ X :=
      E.redCarrier_mem_left_of_not_crossing
        hbudget hrecords hcover hdisjoint hyNot hyCarrier hyInit
    have hsourceY : Q.source ∈ Y :=
      E.redCarrier_mem_right_of_not_crossing
        hbudget hrecords hcover hdisjoint hxNot hxCarrier hxInit
    obtain ⟨e, heQ, heCut⟩ :=
      path_exists_edgeBoundary_of_endpoints_opposite
        Q.reverse hcover hdisjoint
        (by simpa using htargetX) (by simpa using hsourceY)
    exact ⟨e, by simpa [Q, j, x] using heQ, htoAssembled heCut⟩

noncomputable def cleanRecordBoundaryEdge
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (z : {z : E.RecordBoundary (E.terminalSide hrecords X) //
      z ∈ E.cleanBoundaryRecords
        (E.terminalSide hrecords X)
        (E.crossingRails hbudget hrecords X Y)}) :
    Sym2 V :=
  Classical.choose
    (E.exists_cleanRecordBoundaryEdge
      hbudget hrecords hcover hdisjoint z)

theorem cleanRecordBoundaryEdge_mem_path
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (z : {z : E.RecordBoundary (E.terminalSide hrecords X) //
      z ∈ E.cleanBoundaryRecords
        (E.terminalSide hrecords X)
        (E.crossingRails hbudget hrecords X Y)}) :
    E.cleanRecordBoundaryEdge hbudget hrecords hcover hdisjoint z ∈
      (E.localBluePath z.1.1 z.1.2.1).edgeSet :=
  (Classical.choose_spec
    (E.exists_cleanRecordBoundaryEdge
      hbudget hrecords hcover hdisjoint z)).1

theorem cleanRecordBoundaryEdge_mem_boundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y)
    (z : {z : E.RecordBoundary (E.terminalSide hrecords X) //
      z ∈ E.cleanBoundaryRecords
        (E.terminalSide hrecords X)
        (E.crossingRails hbudget hrecords X Y)}) :
    E.cleanRecordBoundaryEdge hbudget hrecords hcover hdisjoint z ∈
      Section44.edgeBoundary (E.assembledSupport hbudget) X Y :=
  (Classical.choose_spec
    (E.exists_cleanRecordBoundaryEdge
      hbudget hrecords hcover hdisjoint z)).2

theorem cleanRecordBoundaryEdge_injective
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    Function.Injective
      (E.cleanRecordBoundaryEdge
        hbudget hrecords hcover hdisjoint) := by
  classical
  intro z w heq
  let e :=
    E.cleanRecordBoundaryEdge hbudget hrecords hcover hdisjoint z
  have hez :
      e ∈ (E.localBluePath z.1.1 z.1.2.1).edgeSet :=
    E.cleanRecordBoundaryEdge_mem_path
      hbudget hrecords hcover hdisjoint z
  have hew :
      e ∈ (E.localBluePath w.1.1 w.1.2.1).edgeSet := by
    have hw :=
      E.cleanRecordBoundaryEdge_mem_path
        hbudget hrecords hcover hdisjoint w
    simpa [e, heq] using hw
  have heout : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  have hez' :
      s(e.out.1, e.out.2) ∈
        (E.localBluePath z.1.1 z.1.2.1).edgeSet := by
    simpa [heout] using hez
  have hew' :
      s(e.out.1, e.out.2) ∈
        (E.localBluePath w.1.1 w.1.2.1).edgeSet := by
    simpa [heout] using hew
  have hvz :
      e.out.1 ∈ (E.localBluePath z.1.1 z.1.2.1).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath z.1.1 z.1.2.1) hez').1
  have hvw :
      e.out.1 ∈ (E.localBluePath w.1.1 w.1.2.1).vertexSet :=
    (GraphPath.endpoints_mem_vertexSet_of_edgeSet
      (E.localBluePath w.1.1 w.1.2.1) hew').1
  have hjk : z.1.1 = w.1.1 :=
    E.localBluePath_record_unique hbudget hvz hvw
  rcases z with ⟨⟨j, x⟩, hz⟩
  rcases w with ⟨⟨k, y⟩, hw⟩
  dsimp only at hjk
  subst k
  have hxy : x.1 = y.1 :=
    E.localBluePath_label_unique j hvz hvw
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Clean transcript boundary records inject into the physical cut. -/
theorem cleanBoundaryRecords_card_le_edgeBoundary
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    (E.cleanBoundaryRecords
        (E.terminalSide hrecords X)
        (E.crossingRails hbudget hrecords X Y)).card ≤
      (Section44.edgeBoundary
        (E.assembledSupport hbudget) X Y).card := by
  classical
  let f :
      {z : E.RecordBoundary (E.terminalSide hrecords X) //
        z ∈ E.cleanBoundaryRecords
          (E.terminalSide hrecords X)
          (E.crossingRails hbudget hrecords X Y)} →
        {e : Sym2 V //
          e ∈ Section44.edgeBoundary
            (E.assembledSupport hbudget) X Y} :=
    fun z =>
      ⟨E.cleanRecordBoundaryEdge
          hbudget hrecords hcover hdisjoint z,
        E.cleanRecordBoundaryEdge_mem_boundary
          hbudget hrecords hcover hdisjoint z⟩
  have hf : Function.Injective f := by
    intro z w h
    exact E.cleanRecordBoundaryEdge_injective
      hbudget hrecords hcover hdisjoint
      (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hc

/-- The restarted transcript expands the smaller side of every label cut. -/
theorem count_mul_min_card_le_two_mul_recordBoundary
    (E : ExpanderBlocks P count) (S : Finset (Fin h)) :
    count * min S.card (Sᶜ : Finset (Fin h)).card ≤
      2 * Fintype.card (E.RecordBoundary S) := by
  classical
  by_cases hS : S = ∅
  · subst S
    simp
  by_cases hU : S = Finset.univ
  · subst S
    simp
  have hScard : S.card ≤ h := by
    simpa using Finset.card_le_univ S
  have hcompCard :
      (Sᶜ : Finset (Fin h)).card = h - S.card := by
    simpa using Finset.card_compl S
  by_cases hhalf : 2 * S.card ≤ h
  · have hexpand :=
      count_mul_card_le_two_mul_edgeBoundaryCount P E S
        (Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hS)) hhalf
    have hmin :
        min S.card (Sᶜ : Finset (Fin h)).card = S.card := by
      rw [Nat.min_eq_left]
      omega
    rw [hmin, E.recordBoundary_card_eq_edgeBoundaryCount]
    exact hexpand
  · have hcompNonempty : (Sᶜ : Finset (Fin h)).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hc
      apply hU
      have hc' := congrArg (fun T : Finset (Fin h) => Tᶜ) hc
      simpa using hc'
    have hcompHalf : 2 * (Sᶜ : Finset (Fin h)).card ≤ h := by
      omega
    have hexpand :=
      count_mul_card_le_two_mul_edgeBoundaryCount P E Sᶜ
        (Finset.card_pos.mpr hcompNonempty) hcompHalf
    have hmin :
        min S.card (Sᶜ : Finset (Fin h)).card =
          (Sᶜ : Finset (Fin h)).card := by
      rw [Nat.min_eq_right]
      omega
    have hboundary :
        Fintype.card (E.RecordBoundary Sᶜ) =
          Fintype.card (E.RecordBoundary S) := by
      rw [← E.transcriptGraph_boundary_card,
        ← E.transcriptGraph_boundary_card,
        ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph.boundary_compl]
    rw [hmin, ← hboundary,
      E.recordBoundary_card_eq_edgeBoundaryCount]
    exact hexpand

theorem image_terminalSide
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X : Finset V) :
    (E.terminalSide hrecords X).image (E.initialTerminal hrecords) =
      X ∩ P.left P.firstIndex := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨x, hxS, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨(E.mem_terminalSide hrecords X x).1 hxS,
        E.initialTerminal_mem hbudget hrecords x⟩
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvX, hvT⟩
    have hvImage :
        v ∈ Finset.univ.image (E.initialTerminal hrecords) := by
      rw [E.image_initialTerminal_univ hbudget hrecords]
      exact hvT
    rcases Finset.mem_image.mp hvImage with ⟨x, _hx, hxv⟩
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, hxv⟩
    exact (E.mem_terminalSide hrecords X x).2 (hxv ▸ hvX)

theorem terminalSide_card
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hrecords : 0 < E.finalState.records.length)
    (X : Finset V) :
    (E.terminalSide hrecords X).card =
      (X ∩ P.left P.firstIndex).card := by
  classical
  calc
    (E.terminalSide hrecords X).card =
        ((E.terminalSide hrecords X).image
          (E.initialTerminal hrecords)).card := by
      symm
      apply Finset.card_image_of_injective
      exact E.initialTerminal_injective hrecords
    _ = (X ∩ P.left P.firstIndex).card := by
      rw [E.image_terminalSide hbudget hrecords X]

theorem terminalSide_right_eq_compl
    (E : ExpanderBlocks P count)
    (hrecords : 0 < E.finalState.records.length)
    {X Y : Finset V} (hcover : X ∪ Y = Finset.univ)
    (hdisjoint : Disjoint X Y) :
    E.terminalSide hrecords Y =
      (E.terminalSide hrecords X)ᶜ := by
  classical
  ext x
  rw [E.mem_terminalSide, Finset.mem_compl, E.mem_terminalSide]
  constructor
  · intro hxY hxX
    exact Finset.disjoint_left.mp hdisjoint hxX hxY
  · intro hxNotX
    have hu :
        E.initialTerminal hrecords x ∈ X ∪ Y := by
      rw [hcover]
      simp
    exact (Finset.mem_union.mp hu).resolve_left hxNotX

/-- Source Claim 5.2 in a slightly weaker but still polylogarithmic form:
before degree-three thinning, the initial terminals are cut-well-linked.
The loss is expressed through the realized transcript length. -/
theorem assembledSupport_initialTerminals_scaledWellLinked
    (E : ExpanderBlocks P count)
    (hbudget :
      count *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell)
    (hcount : 0 < count)
    (hrecords : 0 < E.finalState.records.length) :
    ScaledWellLinked
      (E.assembledSupport hbudget)
      (P.left P.firstIndex) 1
      (2 * (2 * E.finalState.records.length + 1)) := by
  classical
  refine ⟨by omega, by omega, ?_⟩
  intro X Y hcover hdisjoint
  let S := E.terminalSide hrecords X
  let B := E.crossingRails hbudget hrecords X Y
  let C :=
    (Section44.edgeBoundary
      (E.assembledSupport hbudget) X Y).card
  have hbad : B.card ≤ C := by
    let f :
        {x : Fin h // x ∈ B} →
          {e : Sym2 V //
            e ∈ Section44.edgeBoundary
              (E.assembledSupport hbudget) X Y} :=
      fun x =>
        ⟨E.crossingRailEdge hbudget hrecords hcover hdisjoint x,
          edgeBoundary_mono
            (le_sup_left :
              E.redSupport hbudget ≤ E.assembledSupport hbudget) X Y
            (E.crossingRailEdge_mem_boundary
              hbudget hrecords hcover hdisjoint x)⟩
    have hf : Function.Injective f := by
      by_cases hh : h = 0
      · subst h
        intro x
        exact Fin.elim0 x.1
      · let fallback : Fin h := ⟨0, Nat.pos_of_ne_zero hh⟩
        intro x y hxy
        exact E.crossingRailEdge_injective
          hbudget hrecords hcover hdisjoint fallback
          (congrArg Subtype.val hxy)
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, B, C] using hc
  have hincident :
      (E.incidentBoundaryRecords S B).card ≤
        2 * E.finalState.records.length * C :=
    (E.incidentBoundaryRecords_card_le S B).trans
      (Nat.mul_le_mul_left (2 * E.finalState.records.length) hbad)
  have hclean :
      (E.cleanBoundaryRecords S B).card ≤ C := by
    simpa [S, B, C] using
      E.cleanBoundaryRecords_card_le_edgeBoundary
        hbudget hrecords hcover hdisjoint
  have hrecord :
      Fintype.card (E.RecordBoundary S) ≤
        (2 * E.finalState.records.length + 1) * C := by
    have hsplit := E.recordBoundary_card_le_incident_add_clean S B
    calc
      Fintype.card (E.RecordBoundary S) ≤
          (E.incidentBoundaryRecords S B).card +
            (E.cleanBoundaryRecords S B).card := hsplit
      _ ≤ 2 * E.finalState.records.length * C + C :=
        Nat.add_le_add hincident hclean
      _ = (2 * E.finalState.records.length + 1) * C := by ring
  have hexpand :=
    E.count_mul_min_card_le_two_mul_recordBoundary S
  have hpositive :
      min S.card (Sᶜ : Finset (Fin h)).card ≤
        count * min S.card (Sᶜ : Finset (Fin h)).card :=
    Nat.le_mul_of_pos_left _ hcount
  have hterminalX :
      S.card = (X ∩ P.left P.firstIndex).card := by
    exact E.terminalSide_card hbudget hrecords X
  have hterminalY :
      (Sᶜ : Finset (Fin h)).card =
        (Y ∩ P.left P.firstIndex).card := by
    rw [← E.terminalSide_right_eq_compl hrecords hcover hdisjoint]
    exact E.terminalSide_card hbudget hrecords Y
  dsimp [S] at hexpand hpositive hterminalX hterminalY
  dsimp [C] at hrecord
  rw [← hterminalX, ← hterminalY]
  simpa only [one_mul] using hpositive.trans (hexpand.trans (by
    calc
      2 * Fintype.card (E.RecordBoundary S) ≤
          2 * ((2 * E.finalState.records.length + 1) *
            (Section44.edgeBoundary
              (E.assembledSupport hbudget) X Y).card) :=
        Nat.mul_le_mul_left 2 hrecord
      _ = 2 * (2 * E.finalState.records.length + 1) *
            (Section44.edgeBoundary
              (E.assembledSupport hbudget) X Y).card := by ring))

theorem records_length_le_restartCount_log_sq
    (E : ExpanderBlocks P (restartCount h))
    (hheight : 2 ≤ h) :
    E.finalState.records.length ≤
      8192 *
        realizedRoundConstant *
        (Nat.log 2 h) ^ 2 := by
  let L := Nat.log 2 h
  let cRound :=
    realizedRoundConstant
  have hL : 0 < L := by
    exact Nat.log_pos (by decide : 1 < 2) hheight
  have hplus : L + 1 ≤ 2 * L := by omega
  calc
    E.finalState.records.length =
        (List.ofFn E.rounds).flatten.length :=
      E.records_length_eq_flattened_length
    _ ≤ restartCount h * (cRound * L) := by
      simpa [L, cRound] using E.flattened_length_le
    _ = 4096 * (L + 1) * (cRound * L) := by
      simp [restartCount, L]
    _ ≤ 4096 * (2 * L) * (cRound * L) := by
      exact Nat.mul_le_mul_right (cRound * L)
        (Nat.mul_le_mul_left 4096 hplus)
    _ = 8192 * cRound * L ^ 2 := by ring
    _ = 8192 *
          realizedRoundConstant *
          (Nat.log 2 h) ^ 2 := by rfl

/-- Claim 5.2 with a fixed paper-style polylogarithmic denominator. -/
theorem assembledSupport_initialTerminals_polylogWellLinked
    (E : ExpanderBlocks P (restartCount h))
    (hheight : 2 ≤ h)
    (hbudget :
      restartCount h *
          (realizedRoundConstant *
            Nat.log 2 h) ≤ ell) :
    ScaledWellLinked
      (E.assembledSupport hbudget)
      (P.left P.firstIndex) 1
      (32770 *
        (realizedRoundConstant + 1) *
        (Nat.log 2 h) ^ 2) := by
  classical
  have hrestart : 0 < restartCount h := by
    simp [restartCount]
  have hrecords : 0 < E.finalState.records.length :=
    E.records_nonempty hheight hrestart
  have hbase :=
    E.assembledSupport_initialTerminals_scaledWellLinked
      hbudget hrestart hrecords
  let L := Nat.log 2 h
  let cRound :=
    realizedRoundConstant
  have hL : 0 < L := by
    exact Nat.log_pos (by decide : 1 < 2) hheight
  have hrecordBound :=
    E.records_length_le_restartCount_log_sq hheight
  have hden :
      2 * (2 * E.finalState.records.length + 1) ≤
        32770 * (cRound + 1) * L ^ 2 := by
    have hLone : 1 ≤ L := Nat.succ_le_of_lt hL
    have hLsq : 1 ≤ L ^ 2 := by
      nlinarith
    calc
      2 * (2 * E.finalState.records.length + 1) =
          4 * E.finalState.records.length + 2 := by ring
      _ ≤ 4 * (8192 * cRound * L ^ 2) + 2 * L ^ 2 :=
        Nat.add_le_add
          (Nat.mul_le_mul_left 4 (by simpa [L, cRound] using hrecordBound))
          (Nat.mul_le_mul_left 2 hLsq)
      _ ≤ 32770 * (cRound + 1) * L ^ 2 := by
        nlinarith
  refine ⟨hbase.1, hbase.2.1.trans ?_, ?_⟩
  · simpa [L, cRound] using hden
  · intro X Y hcover hdisjoint
    exact (hbase.2.2 X Y hcover hdisjoint).trans
      (Nat.mul_le_mul_right
        (Section44.edgeBoundary
          (E.assembledSupport hbudget) X Y).card
        (by simpa [L, cRound] using hden))

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
