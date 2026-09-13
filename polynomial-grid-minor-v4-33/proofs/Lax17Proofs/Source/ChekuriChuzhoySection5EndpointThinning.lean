import Lax17Proofs.Source.ChekuriChuzhoySection5RouterSkeleton
import Lax17Proofs.Source.Degree

namespace Lax17Proofs

universe u v w

/-!
# Endpoint thinning for Chekuri--Chuzhoy Section 5.4.1

In the long-support-path branch of Phase 1, one edge is first selected from
each Theorem 5.10 group.  The corresponding host paths are internally
node-disjoint, but paths on consecutive router pairs can still share a router
endpoint.  The paper invokes Claim 2.3 on the bipartite multigraph whose named
edges are these paths.

This module isolates the finite endpoint argument.  The first theorem is a
greedy, constant-factor version of Claim 2.3 that preserves parallel named
edges.  The source-facing theorem uses `RouterPathSkeleton`: its endpoint
congestion bound and maximum host degree `Delta` give endpoint multiplicity at
most `2 * Delta`.  It removes paths meeting already reserved neighboring
interfaces and retains the explicit Phase 1 lower bound
`card / (8 * Delta^2)`.  The terminal-skeleton layer records the same charging
argument in a generic compatibility form.

Source: Chekuri--Chuzhoy, journal Section 5.4.1 (Phase 1), using Claim 2.3.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5EndpointThinning


open Finset
open ChekuriChuzhoySection5TerminalSkeleton

/-! ## Claim 2.3-style finite bipartite matching -/

/-- A finite family of named bipartite edges with both endpoint multiplicities
at most `d` contains a matching accounting for the whole family within factor
`2 * d`.

The paper's flow proof of Claim 2.3 gives factor `d`.  The factor-two greedy
form is sufficient for the endpoint-reservation step below and avoids
replacing named parallel edges by a simple graph. -/
theorem exists_boundedDegreeBipartiteMatching
    {Edge : Type u} {Left : Type v} {Right : Type w}
    [DecidableEq Edge] [DecidableEq Left] [DecidableEq Right]
    (edges : Finset Edge) (left : Edge → Left) (right : Edge → Right)
    (d : Nat)
    (hleft : ∀ x : Left,
      (edges.filter fun e => left e = x).card ≤ d)
    (hright : ∀ y : Right,
      (edges.filter fun e => right e = y).card ≤ d) :
    ∃ matching : Finset Edge,
      matching ⊆ edges ∧
        Set.InjOn left matching ∧
        Set.InjOn right matching ∧
        edges.card ≤ 2 * d * matching.card := by
  classical
  induction edges using Finset.strongInductionOn with
  | _ edges ih =>
      by_cases hempty : edges = ∅
      · subst edges
        exact ⟨∅, by simp, by simp, by simp, by simp⟩
      · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        let rest :=
          edges.filter fun f => left f ≠ left e ∧ right f ≠ right e
        have hrestSubset : rest ⊆ edges := Finset.filter_subset _ _
        have heRest : e ∉ rest := by simp [rest]
        have hrestStrict : rest ⊂ edges :=
          (Finset.ssubset_iff_of_subset hrestSubset).2 ⟨e, he, heRest⟩
        have hleftRest : ∀ x : Left,
            (rest.filter fun f => left f = x).card ≤ d := by
          intro x
          exact
            (Finset.card_le_card (by
              intro f hf
              exact Finset.mem_filter.mpr
                ⟨hrestSubset (Finset.mem_filter.mp hf).1,
                  (Finset.mem_filter.mp hf).2⟩)).trans
              (hleft x)
        have hrightRest : ∀ y : Right,
            (rest.filter fun f => right f = y).card ≤ d := by
          intro y
          exact
            (Finset.card_le_card (by
              intro f hf
              exact Finset.mem_filter.mpr
                ⟨hrestSubset (Finset.mem_filter.mp hf).1,
                  (Finset.mem_filter.mp hf).2⟩)).trans
              (hright y)
        rcases ih rest hrestStrict hleftRest hrightRest with
          ⟨matching, hmatchingRest, hleftInj, hrightInj, hcardRest⟩
        let leftFiber := edges.filter fun f => left f = left e
        let rightFiber := edges.filter fun f => right f = right e
        have hcover : edges ⊆ rest ∪ (leftFiber ∪ rightFiber) := by
          intro f hf
          by_cases hl : left f = left e
          · exact Finset.mem_union_right _
              (Finset.mem_union_left _
                (Finset.mem_filter.mpr ⟨hf, hl⟩))
          · by_cases hr : right f = right e
            · exact Finset.mem_union_right _
                (Finset.mem_union_right _
                  (Finset.mem_filter.mpr ⟨hf, hr⟩))
            · exact Finset.mem_union_left _
                (Finset.mem_filter.mpr ⟨hf, hl, hr⟩)
        have hcoveredCard :
            edges.card ≤ rest.card + 2 * d := by
          calc
            edges.card ≤ (rest ∪ (leftFiber ∪ rightFiber)).card :=
              Finset.card_le_card hcover
            _ ≤ rest.card + (leftFiber ∪ rightFiber).card :=
              Finset.card_union_le _ _
            _ ≤ rest.card + (leftFiber.card + rightFiber.card) :=
              Nat.add_le_add_left (Finset.card_union_le _ _) _
            _ ≤ rest.card + (d + d) :=
              Nat.add_le_add_left
                (Nat.add_le_add
                  (by simpa [leftFiber] using hleft (left e))
                  (by simpa [rightFiber] using hright (right e))) _
            _ = rest.card + 2 * d := by omega
        have heMatching : e ∉ matching := fun heM =>
          heRest (hmatchingRest heM)
        refine ⟨insert e matching, ?_, ?_, ?_, ?_⟩
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact he
          · exact hrestSubset (hmatchingRest hf)
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | haM
          · rcases Finset.mem_insert.mp hb with rfl | hbM
            · rfl
            · exact False.elim
                ((Finset.mem_filter.mp (hmatchingRest hbM)).2.1 hab.symm)
          · rcases Finset.mem_insert.mp hb with rfl | hbM
            · exact False.elim
                ((Finset.mem_filter.mp (hmatchingRest haM)).2.1 hab)
            · exact hleftInj haM hbM hab
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | haM
          · rcases Finset.mem_insert.mp hb with rfl | hbM
            · rfl
            · exact False.elim
                ((Finset.mem_filter.mp (hmatchingRest hbM)).2.2 hab.symm)
          · rcases Finset.mem_insert.mp hb with rfl | hbM
            · exact False.elim
                ((Finset.mem_filter.mp (hmatchingRest haM)).2.2 hab)
            · exact hrightInj haM hbM hab
        · rw [Finset.card_insert_of_notMem heMatching]
          calc
            edges.card ≤ rest.card + 2 * d := hcoveredCard
            _ ≤ (2 * d * matching.card) + 2 * d :=
              Nat.add_le_add_right hcardRest _
            _ = 2 * d * (matching.card + 1) := by ring

/-! ## Endpoint multiplicity from host-edge load -/

section TerminalSkeleton

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {terminals : Finset V} {Delta : Nat}

/-- The selected skeleton paths using a prescribed host edge. -/
noncomputable def selectedHostEdgeUsers
    (S : TerminalPathSkeleton G terminals)
    (selected : Finset S.graph.Edge) (a : Sym2 V) :
    Finset S.graph.Edge := by
  classical
  exact selected.filter fun e => a ∈ (S.hostPath e).edgeSet

omit [Fintype V] in
theorem selectedHostEdgeUsers_card_le_two
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (selected : Finset S.graph.Edge) (a : Sym2 V)
    (haG : a ∈ G.edgeSet)
    (haTerminal :
      TerminalPathSkeleton.HostEdgeIncidentToTerminals
        (terminals := terminals) a) :
    (selectedHostEdgeUsers S selected a).card ≤ 2 := by
  classical
  calc
    (selectedHostEdgeUsers S selected a).card ≤
        (Finset.univ.filter fun e : S.graph.Edge =>
          a ∈ (S.hostPath e).edgeSet).card := by
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ e, (Finset.mem_filter.mp he).2⟩
    _ = S.hostEdgeLoad a := rfl
    _ ≤ 2 := hload a haG haTerminal

omit [Fintype V] in
/-- A common endpoint of selected nontrivial skeleton paths occurs on at most
`2 * Delta` paths.  The endpoint map is kept abstract so the same charging
argument applies to sources and targets. -/
theorem endpointFiber_card_le_two_mul_degree
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    (endpoint : S.graph.Edge → V)
    (hendpointVertex :
      ∀ e, endpoint e ∈ (S.hostPath e).vertexSet)
    (hnontrivial :
      ∀ e, (S.hostPath e).source ≠ (S.hostPath e).target)
    (t : V) (ht : t ∈ terminals) :
    (selected.filter fun e => endpoint e = t).card ≤ 2 * Delta := by
  classical
  let neighbors := MaxDegreeAtMost.neighborFinset hdegree t
  let users : V → Finset S.graph.Edge := fun u =>
    selectedHostEdgeUsers S selected s(t, u)
  have hcover :
      selected.filter (fun e => endpoint e = t) ⊆
        neighbors.biUnion users := by
    intro e he
    have heSelected : e ∈ selected := (Finset.mem_filter.mp he).1
    have hendpoint : endpoint e = t := (Finset.mem_filter.mp he).2
    have htPath : t ∈ (S.hostPath e).vertexSet := by
      rw [← hendpoint]
      exact hendpointVertex e
    rcases
        (S.hostPath e).exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          (hnontrivial e) htPath with
      ⟨a, haPath, hta⟩
    rcases Sym2.mem_iff_exists.mp hta with ⟨u, rfl⟩
    have haG : s(t, u) ∈ G.edgeSet :=
      (S.hostPath e).edgeSet_subset_edgeSet haPath
    have htu : G.Adj t u := by
      simpa [_root_.SimpleGraph.mem_edgeSet] using haG
    apply Finset.mem_biUnion.mpr
    refine ⟨u, ?_, ?_⟩
    · exact (MaxDegreeAtMost.mem_neighborFinset hdegree t u).2 htu
    · exact Finset.mem_filter.mpr ⟨heSelected, haPath⟩
  calc
    (selected.filter fun e => endpoint e = t).card ≤
        (neighbors.biUnion users).card :=
      Finset.card_le_card hcover
    _ ≤ neighbors.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro u hu
      have htu : G.Adj t u :=
        (MaxDegreeAtMost.mem_neighborFinset hdegree t u).1 hu
      have haG : s(t, u) ∈ G.edgeSet := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using htu
      exact selectedHostEdgeUsers_card_le_two S hload selected s(t, u)
        haG ⟨t, ht, by simp⟩
    _ ≤ Delta * 2 :=
      Nat.mul_le_mul_right 2
        (MaxDegreeAtMost.card_neighborFinset_le hdegree t)
    _ = 2 * Delta := Nat.mul_comm _ _

omit [Fintype V] [DecidableEq V] in
private theorem hostPath_nontrivial
    (S : TerminalPathSkeleton G terminals) (e : S.graph.Edge) :
    (S.hostPath e).source ≠ (S.hostPath e).target := by
  rw [S.host_source e, S.host_target e]
  intro h
  apply S.graph.end_ne e
  exact Subtype.ext h

omit [Fintype V] in
theorem sourceFiber_card_le_two_mul_degree
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    (t : V) (ht : t ∈ terminals) :
    (selected.filter fun e => (S.hostPath e).source = t).card ≤
      2 * Delta := by
  apply endpointFiber_card_le_two_mul_degree S hload hdegree selected
    (fun e => (S.hostPath e).source)
  · exact fun e => GraphPath.source_mem_vertexSet (S.hostPath e)
  · exact hostPath_nontrivial S
  · exact ht

omit [Fintype V] in
theorem targetFiber_card_le_two_mul_degree
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    (t : V) (ht : t ∈ terminals) :
    (selected.filter fun e => (S.hostPath e).target = t).card ≤
      2 * Delta := by
  apply endpointFiber_card_le_two_mul_degree S hload hdegree selected
    (fun e => (S.hostPath e).target)
  · exact fun e => GraphPath.target_mem_vertexSet (S.hostPath e)
  · exact hostPath_nontrivial S
  · exact ht

omit [Fintype V] in
/-- Paths whose source lies in a reserved terminal set are bounded by endpoint
capacity times the number of reserved vertices. -/
theorem sourceInReserved_card_le
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    (reserved : Finset V) (hreserved : reserved ⊆ terminals) :
    (selected.filter fun e => (S.hostPath e).source ∈ reserved).card ≤
      2 * Delta * reserved.card := by
  classical
  let fiber : V → Finset S.graph.Edge := fun t =>
    selected.filter fun e => (S.hostPath e).source = t
  have hcover :
      selected.filter (fun e => (S.hostPath e).source ∈ reserved) ⊆
        reserved.biUnion fiber := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_biUnion.mpr
      ⟨(S.hostPath e).source, he'.2,
        Finset.mem_filter.mpr ⟨he'.1, rfl⟩⟩
  calc
    (selected.filter fun e => (S.hostPath e).source ∈ reserved).card ≤
        (reserved.biUnion fiber).card :=
      Finset.card_le_card hcover
    _ ≤ reserved.card * (2 * Delta) := by
      apply Finset.card_biUnion_le_card_mul
      intro t ht
      exact sourceFiber_card_le_two_mul_degree S hload hdegree selected
        t (hreserved ht)
    _ = 2 * Delta * reserved.card := by ring

omit [Fintype V] in
/-- Target analogue of `sourceInReserved_card_le`. -/
theorem targetInReserved_card_le
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    (reserved : Finset V) (hreserved : reserved ⊆ terminals) :
    (selected.filter fun e => (S.hostPath e).target ∈ reserved).card ≤
      2 * Delta * reserved.card := by
  classical
  let fiber : V → Finset S.graph.Edge := fun t =>
    selected.filter fun e => (S.hostPath e).target = t
  have hcover :
      selected.filter (fun e => (S.hostPath e).target ∈ reserved) ⊆
        reserved.biUnion fiber := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_biUnion.mpr
      ⟨(S.hostPath e).target, he'.2,
        Finset.mem_filter.mpr ⟨he'.1, rfl⟩⟩
  calc
    (selected.filter fun e => (S.hostPath e).target ∈ reserved).card ≤
        (reserved.biUnion fiber).card :=
      Finset.card_le_card hcover
    _ ≤ reserved.card * (2 * Delta) := by
      apply Finset.card_biUnion_le_card_mul
      intro t ht
      exact targetFiber_card_le_two_mul_degree S hload hdegree selected
        t (hreserved ht)
    _ = 2 * Delta * reserved.card := by ring

/-- Paths avoiding the endpoint interfaces already reserved by neighboring
router pairs. -/
noncomputable def avoidingReservedEndpoints
    (S : TerminalPathSkeleton G terminals)
    (selected : Finset S.graph.Edge)
    (reservedLeft reservedRight : Finset V) :
    Finset S.graph.Edge := by
  classical
  exact selected.filter fun e =>
    (S.hostPath e).source ∉ reservedLeft ∧
      (S.hostPath e).target ∉ reservedRight

omit [Fintype V] in
@[simp] theorem mem_avoidingReservedEndpoints
    (S : TerminalPathSkeleton G terminals)
    {selected : Finset S.graph.Edge}
    {reservedLeft reservedRight : Finset V} {e : S.graph.Edge} :
    e ∈ avoidingReservedEndpoints S selected reservedLeft reservedRight ↔
      e ∈ selected ∧
        (S.hostPath e).source ∉ reservedLeft ∧
        (S.hostPath e).target ∉ reservedRight := by
  classical
  simp [avoidingReservedEndpoints]

omit [Fintype V] in
/-- Removing two reserved endpoint interfaces costs at most endpoint capacity
times their total cardinality. -/
theorem card_le_avoidingReservedEndpoints_add
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    (reservedLeft reservedRight : Finset V)
    (hleft : reservedLeft ⊆ terminals)
    (hright : reservedRight ⊆ terminals) :
    selected.card ≤
      (avoidingReservedEndpoints S selected
        reservedLeft reservedRight).card +
        2 * Delta * (reservedLeft.card + reservedRight.card) := by
  classical
  let available :=
    avoidingReservedEndpoints S selected reservedLeft reservedRight
  let badLeft :=
    selected.filter fun e => (S.hostPath e).source ∈ reservedLeft
  let badRight :=
    selected.filter fun e => (S.hostPath e).target ∈ reservedRight
  have hcover : selected ⊆ available ∪ (badLeft ∪ badRight) := by
    intro e he
    by_cases hl : (S.hostPath e).source ∈ reservedLeft
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨he, hl⟩))
    · by_cases hr : (S.hostPath e).target ∈ reservedRight
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨he, hr⟩))
      · exact Finset.mem_union_left _
          ((mem_avoidingReservedEndpoints S).2 ⟨he, hl, hr⟩)
  calc
    selected.card ≤ (available ∪ (badLeft ∪ badRight)).card :=
      Finset.card_le_card hcover
    _ ≤ available.card + (badLeft ∪ badRight).card :=
      Finset.card_union_le _ _
    _ ≤ available.card + (badLeft.card + badRight.card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ available.card +
        (2 * Delta * reservedLeft.card +
          2 * Delta * reservedRight.card) := by
      apply Nat.add_le_add_left
      exact Nat.add_le_add
        (by
          simpa [badLeft] using
            (sourceInReserved_card_le S hload hdegree selected
              reservedLeft hleft))
        (by
          simpa [badRight] using
            (targetInReserved_card_le S hload hdegree selected
              reservedRight hright))
    _ = available.card +
        2 * Delta * (reservedLeft.card + reservedRight.card) := by ring
    _ = (avoidingReservedEndpoints S selected
          reservedLeft reservedRight).card +
        2 * Delta * (reservedLeft.card + reservedRight.card) := by
      rfl

/-! ## The Section 5.4.1 endpoint thinning step -/

/-- The additive, constant-explicit endpoint-thinning statement.

The first term is the greedy Claim 2.3 loss on the paths left after removing
reserved interfaces.  The second term is the exact endpoint-capacity charge
for those reserves. -/
theorem exists_endpointMatching_avoiding_reserved
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal selected)
    (hinternal : S.OnePerGroupInternallyNodeDisjoint)
    (leftRouter rightRouter : Finset V)
    (hsourceRouter :
      ∀ e ∈ selected, (S.hostPath e).source ∈ leftRouter)
    (htargetRouter :
      ∀ e ∈ selected, (S.hostPath e).target ∈ rightRouter)
    (reservedLeft reservedRight : Finset V)
    (hleft : reservedLeft ⊆ terminals)
    (hright : reservedRight ⊆ terminals) :
    ∃ thinned : Finset S.graph.Edge,
      thinned ⊆ selected ∧
        selected.card ≤
          4 * Delta * thinned.card +
            2 * Delta * (reservedLeft.card + reservedRight.card) ∧
        Set.InjOn (fun e => (S.hostPath e).source) thinned ∧
        Set.InjOn (fun e => (S.hostPath e).target) thinned ∧
        (∀ e ∈ thinned,
          (S.hostPath e).source ∈ leftRouter \ reservedLeft) ∧
        (∀ e ∈ thinned,
          (S.hostPath e).target ∈ rightRouter \ reservedRight) ∧
        (∀ ⦃e⦄, e ∈ thinned → ∀ ⦃f⦄, f ∈ thinned → e ≠ f →
          (S.hostPath e).InternallyDisjoint (S.hostPath f)) := by
  classical
  let available :=
    avoidingReservedEndpoints S selected reservedLeft reservedRight
  have hsourceFiber :
      ∀ t : V,
        (available.filter fun e => (S.hostPath e).source = t).card ≤
          2 * Delta := by
    intro t
    by_cases ht : t ∈ terminals
    · exact sourceFiber_card_le_two_mul_degree S hload hdegree available
        t ht
    · have hempty :
          available.filter (fun e => (S.hostPath e).source = t) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        have het : (S.hostPath e).source = t :=
          (Finset.mem_filter.mp he).2
        exact ht (het ▸ S.hostPath_source_mem_terminals e)
      simp [hempty]
  have htargetFiber :
      ∀ t : V,
        (available.filter fun e => (S.hostPath e).target = t).card ≤
          2 * Delta := by
    intro t
    by_cases ht : t ∈ terminals
    · exact targetFiber_card_le_two_mul_degree S hload hdegree available
        t ht
    · have hempty :
          available.filter (fun e => (S.hostPath e).target = t) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        have het : (S.hostPath e).target = t :=
          (Finset.mem_filter.mp he).2
        exact ht (het ▸ S.hostPath_target_mem_terminals e)
      simp [hempty]
  rcases exists_boundedDegreeBipartiteMatching
      available
      (fun e => (S.hostPath e).source)
      (fun e => (S.hostPath e).target)
      (2 * Delta) hsourceFiber htargetFiber with
    ⟨thinned, hthinAvailable, hsourceInj, htargetInj,
      havailableCard⟩
  have hthinSelected : thinned ⊆ selected := by
    intro e he
    exact ((mem_avoidingReservedEndpoints S).1
      (hthinAvailable he)).1
  have hcard :
      selected.card ≤
        4 * Delta * thinned.card +
          2 * Delta * (reservedLeft.card + reservedRight.card) := by
    calc
      selected.card ≤
          available.card +
            2 * Delta * (reservedLeft.card + reservedRight.card) := by
        simpa [available] using
          card_le_avoidingReservedEndpoints_add S hload hdegree selected
            reservedLeft reservedRight hleft hright
      _ ≤ (2 * (2 * Delta) * thinned.card) +
            2 * Delta * (reservedLeft.card + reservedRight.card) :=
        Nat.add_le_add_right havailableCard _
      _ = 4 * Delta * thinned.card +
            2 * Delta * (reservedLeft.card + reservedRight.card) := by ring
  refine
    ⟨thinned, hthinSelected, hcard, hsourceInj, htargetInj,
      ?_, ?_, ?_⟩
  · intro e he
    have heAvailable :=
      (mem_avoidingReservedEndpoints S).1 (hthinAvailable he)
    exact Finset.mem_sdiff.mpr
      ⟨hsourceRouter e (hthinSelected he), heAvailable.2.1⟩
  · intro e he
    have heAvailable :=
      (mem_avoidingReservedEndpoints S).1 (hthinAvailable he)
    exact Finset.mem_sdiff.mpr
      ⟨htargetRouter e (hthinSelected he), heAvailable.2.2⟩
  · intro e he f hf hef
    exact hinternal selected htransversal
      (hthinSelected he) (hthinSelected hf) hef

/-- Source-facing Phase 1 endpoint thinning for two adjacent router clusters.

The reserve budget is the inequality used in the long-support-path iteration:
the paths charged to neighboring interfaces occupy at most half of the
current family.  After that deletion, the bounded-degree bipartite matching
lemma leaves at least the displayed floor. -/
theorem exists_longSupportPath_endpoint_thinning
    (S : TerminalPathSkeleton G terminals)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (selected : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal selected)
    (hinternal : S.OnePerGroupInternallyNodeDisjoint)
    (leftRouter rightRouter : Finset V)
    (hsourceRouter :
      ∀ e ∈ selected, (S.hostPath e).source ∈ leftRouter)
    (htargetRouter :
      ∀ e ∈ selected, (S.hostPath e).target ∈ rightRouter)
    (reservedLeft reservedRight : Finset V)
    (hleft : reservedLeft ⊆ terminals)
    (hright : reservedRight ⊆ terminals)
    (hreserve :
      4 * Delta * (reservedLeft.card + reservedRight.card) ≤
        selected.card) :
    ∃ thinned : Finset S.graph.Edge,
      thinned ⊆ selected ∧
        selected.card / (8 * Delta ^ 2) ≤ thinned.card ∧
        Set.InjOn (fun e => (S.hostPath e).source) thinned ∧
        Set.InjOn (fun e => (S.hostPath e).target) thinned ∧
        (∀ e ∈ thinned,
          (S.hostPath e).source ∈ leftRouter \ reservedLeft) ∧
        (∀ e ∈ thinned,
          (S.hostPath e).target ∈ rightRouter \ reservedRight) ∧
        (∀ ⦃e⦄, e ∈ thinned → ∀ ⦃f⦄, f ∈ thinned → e ≠ f →
          (S.hostPath e).InternallyDisjoint (S.hostPath f)) := by
  rcases exists_endpointMatching_avoiding_reserved
      S hload hdegree selected htransversal hinternal
      leftRouter rightRouter hsourceRouter htargetRouter
      reservedLeft reservedRight hleft hright with
    ⟨thinned, hsubset, hcardAdd, hsourceInj, htargetInj,
      hsourceAvoids, htargetAvoids, hthinInternal⟩
  have hreserveHalf :
      2 * (2 * Delta *
        (reservedLeft.card + reservedRight.card)) ≤ selected.card := by
    calc
      2 * (2 * Delta *
          (reservedLeft.card + reservedRight.card)) =
          4 * Delta * (reservedLeft.card + reservedRight.card) := by ring
      _ ≤ selected.card := hreserve
  have hcardEight :
      selected.card ≤ 8 * Delta * thinned.card := by
    calc
      selected.card ≤ 2 * (4 * Delta * thinned.card) := by omega
      _ = 8 * Delta * thinned.card := by ring
  have hDeltaSq : Delta ≤ Delta ^ 2 := by
    calc
      Delta = Delta * 1 := by simp
      _ ≤ Delta * Delta := Nat.mul_le_mul_left Delta hDelta
      _ = Delta ^ 2 := by ring
  have hcardDenominator :
      selected.card ≤ (8 * Delta ^ 2) * thinned.card := by
    calc
      selected.card ≤ 8 * Delta * thinned.card := hcardEight
      _ ≤ (8 * Delta ^ 2) * thinned.card :=
        Nat.mul_le_mul_right thinned.card
          (Nat.mul_le_mul_left 8 hDeltaSq)
  have hfloor :
      selected.card / (8 * Delta ^ 2) ≤ thinned.card := by
    apply Nat.div_le_of_le_mul
    exact hcardDenominator
  exact
    ⟨thinned, hsubset, hfloor, hsourceInj, htargetInj,
      hsourceAvoids, htargetAvoids, hthinInternal⟩

end TerminalSkeleton

/-! ## Native router-skeleton endpoint thinning -/

section RouterSkeleton

open ChekuriChuzhoySection5RouterSkeleton
open ChekuriChuzhoySection5TerminalSkeleton

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {n Delta : Nat} {cluster : Fin n → Finset V}

/-- The endpoint of a router-skeleton path belonging to router `i`.
For an edge whose stored left endpoint is not `i`, this is its host target. -/
def routerEndpointAt
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (e : S.graph.Edge) : V :=
  if S.graph.left e = i then (S.hostPath e).source
  else (S.hostPath e).target

/-- On a named edge joining distinct routers, `routerEndpointAt` orients the
two host endpoints toward the requested routers. -/
theorem routerEndpointAt_pair_of_joins
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j) (e : S.graph.Edge)
    (he : S.graph.Joins e i j) :
    (routerEndpointAt S i e = (S.hostPath e).source ∧
        routerEndpointAt S j e = (S.hostPath e).target) ∨
      (routerEndpointAt S i e = (S.hostPath e).target ∧
        routerEndpointAt S j e = (S.hostPath e).source) := by
  rcases he with he | he
  · left
    constructor
    · simp [routerEndpointAt, he.1]
    · have hleftNe : S.graph.left e ≠ j := by
        rw [he.1]
        exact hij
      simp [routerEndpointAt, hleftNe]
  · right
    constructor
    · have hleftNe : S.graph.left e ≠ i := by
        rw [he.2]
        exact hij.symm
      simp [routerEndpointAt, hleftNe]
    · simp [routerEndpointAt, he.2]

theorem routerEndpointAt_mem_cluster_of_joins
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j) (e : S.graph.Edge)
    (he : S.graph.Joins e i j) :
    routerEndpointAt S i e ∈ cluster i ∧
      routerEndpointAt S j e ∈ cluster j := by
  rcases he with he | he
  · constructor
    · simpa [routerEndpointAt, he.1] using S.host_source_mem e
    · have hleftNe : S.graph.left e ≠ j := by
        rw [he.1]
        exact hij
      simpa [routerEndpointAt, hleftNe, he.2] using S.host_target_mem e
  · constructor
    · have hleftNe : S.graph.left e ≠ i := by
        rw [he.2]
        exact hij.symm
      simpa [routerEndpointAt, hleftNe, he.1] using S.host_target_mem e
    · simpa [routerEndpointAt, he.2] using S.host_source_mem e

theorem routerEndpointAt_mem_vertexSet_of_joins
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j) (e : S.graph.Edge)
    (he : S.graph.Joins e i j) :
    routerEndpointAt S i e ∈ (S.hostPath e).vertexSet ∧
      routerEndpointAt S j e ∈ (S.hostPath e).vertexSet := by
  rcases routerEndpointAt_pair_of_joins S hij e he with he | he
  · exact
      ⟨he.1 ▸ GraphPath.source_mem_vertexSet (S.hostPath e),
        he.2 ▸ GraphPath.target_mem_vertexSet (S.hostPath e)⟩
  · exact
      ⟨he.1 ▸ GraphPath.target_mem_vertexSet (S.hostPath e),
        he.2 ▸ GraphPath.source_mem_vertexSet (S.hostPath e)⟩

theorem routerHostPath_nontrivial_of_joins
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hdisjoint : Disjoint (cluster i) (cluster j))
    (e : S.graph.Edge) (he : S.graph.Joins e i j) :
    (S.hostPath e).source ≠ (S.hostPath e).target := by
  intro hst
  have hendpoint :=
    routerEndpointAt_mem_cluster_of_joins S hij e he
  rcases routerEndpointAt_pair_of_joins S hij e he with horient | horient
  · have hatEq :
        routerEndpointAt S i e = routerEndpointAt S j e :=
        horient.1.trans (hst.trans horient.2.symm)
    exact (Finset.disjoint_left.mp hdisjoint)
      hendpoint.1 (by rw [hatEq]; exact hendpoint.2)
  · have hatEq :
        routerEndpointAt S i e = routerEndpointAt S j e :=
        horient.1.trans (hst.symm.trans horient.2.symm)
    exact (Finset.disjoint_left.mp hdisjoint)
      hendpoint.1 (by rw [hatEq]; exact hendpoint.2)

/-- Selected router paths using one original host edge. -/
noncomputable def routerSelectedHostEdgeUsers
    (S : RouterPathSkeleton G cluster)
    (selected : Finset S.graph.Edge) (a : Sym2 V) :
    Finset S.graph.Edge := by
  classical
  exact selected.filter fun e => a ∈ (S.hostPath e).edgeSet

theorem routerSelectedHostEdgeUsers_card_le_two
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (selected : Finset S.graph.Edge) (a : Sym2 V)
    (haG : a ∈ G.edgeSet)
    (haRouter :
      RouterPathSkeleton.HostEdgeIncidentToRouters
        (cluster := cluster) a) :
    (routerSelectedHostEdgeUsers S selected a).card ≤ 2 := by
  classical
  calc
    (routerSelectedHostEdgeUsers S selected a).card ≤
        (Finset.univ.filter fun e : S.graph.Edge =>
          a ∈ (S.hostPath e).edgeSet).card := by
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ e, (Finset.mem_filter.mp he).2⟩
    _ = S.hostEdgeLoad a := rfl
    _ ≤ 2 := hload a haG haRouter

/-- Endpoint load at one side of a fixed router pair is at most
`2 * Delta`. -/
theorem routerEndpointFiber_card_le_two_mul_degree
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    {i j : Fin n} (hij : i ≠ j)
    (hdisjoint : Disjoint (cluster i) (cluster j))
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (t : V) (ht : t ∈ cluster i) :
    (selected.filter fun e => routerEndpointAt S i e = t).card ≤
      2 * Delta := by
  classical
  let neighbors := MaxDegreeAtMost.neighborFinset hdegree t
  let users : V → Finset S.graph.Edge := fun u =>
    routerSelectedHostEdgeUsers S selected s(t, u)
  have hcover :
      selected.filter (fun e => routerEndpointAt S i e = t) ⊆
        neighbors.biUnion users := by
    intro e he
    have heSelected : e ∈ selected := (Finset.mem_filter.mp he).1
    have hendpoint : routerEndpointAt S i e = t :=
      (Finset.mem_filter.mp he).2
    have htPath : t ∈ (S.hostPath e).vertexSet := by
      rw [← hendpoint]
      exact
        (routerEndpointAt_mem_vertexSet_of_joins
          S hij e (hjoins e heSelected)).1
    rcases
        (S.hostPath e).exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
          (routerHostPath_nontrivial_of_joins
            S hij hdisjoint e (hjoins e heSelected)) htPath with
      ⟨a, haPath, hta⟩
    rcases Sym2.mem_iff_exists.mp hta with ⟨u, rfl⟩
    have haG : s(t, u) ∈ G.edgeSet :=
      (S.hostPath e).edgeSet_subset_edgeSet haPath
    have htu : G.Adj t u := by
      simpa [_root_.SimpleGraph.mem_edgeSet] using haG
    apply Finset.mem_biUnion.mpr
    refine ⟨u, ?_, Finset.mem_filter.mpr ⟨heSelected, haPath⟩⟩
    exact (MaxDegreeAtMost.mem_neighborFinset hdegree t u).2 htu
  calc
    (selected.filter fun e => routerEndpointAt S i e = t).card ≤
        (neighbors.biUnion users).card :=
      Finset.card_le_card hcover
    _ ≤ neighbors.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro u hu
      have htu : G.Adj t u :=
        (MaxDegreeAtMost.mem_neighborFinset hdegree t u).1 hu
      have haG : s(t, u) ∈ G.edgeSet := by
        simpa [_root_.SimpleGraph.mem_edgeSet] using htu
      exact routerSelectedHostEdgeUsers_card_le_two
        S hload selected s(t, u) haG
          ⟨i, t, ht, by simp⟩
    _ ≤ Delta * 2 :=
      Nat.mul_le_mul_right 2
        (MaxDegreeAtMost.card_neighborFinset_le hdegree t)
    _ = 2 * Delta := Nat.mul_comm _ _

/-- Source-faithful endpoint thinning before the history groups are sampled.

Unlike `exists_routerBundle_exact_endpoint_thinning`, this lemma does not
assume a one-per-group transversal.  It is the form used in the many-leaves
branch of Phase 1: all history groups remain available, and their overlap is
accounted for later as edge congestion.  The only loss here is the endpoint
multiplicity bound `2 * Delta` on each side. -/
theorem exists_routerBundle_exact_endpoint_matching
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    {i j : Fin n} (hij : i ≠ j)
    (hdisjoint : Disjoint (cluster i) (cluster j))
    (selected : Finset S.graph.Edge)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    {width : Nat}
    (hwidth : 4 * Delta * width ≤ selected.card) :
    ∃ exact : Finset S.graph.Edge,
      exact ⊆ selected ∧
        exact.card = width ∧
        Set.InjOn (routerEndpointAt S i) exact ∧
        Set.InjOn (routerEndpointAt S j) exact ∧
        (∀ e ∈ exact, routerEndpointAt S i e ∈ cluster i) ∧
        (∀ e ∈ exact, routerEndpointAt S j e ∈ cluster j) := by
  classical
  have hfiberI :
      ∀ t : V,
        (selected.filter fun e => routerEndpointAt S i e = t).card ≤
          2 * Delta := by
    intro t
    by_cases ht : t ∈ cluster i
    · exact routerEndpointFiber_card_le_two_mul_degree
        S hload hdegree selected hij hdisjoint hjoins t ht
    · have hempty :
          selected.filter (fun e => routerEndpointAt S i e = t) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        have heSelected := (Finset.mem_filter.mp he).1
        have het := (Finset.mem_filter.mp he).2
        exact ht (het ▸
          (routerEndpointAt_mem_cluster_of_joins
            S hij e (hjoins e heSelected)).1)
      simp [hempty]
  have hfiberJ :
      ∀ t : V,
        (selected.filter fun e => routerEndpointAt S j e = t).card ≤
          2 * Delta := by
    intro t
    by_cases ht : t ∈ cluster j
    · exact routerEndpointFiber_card_le_two_mul_degree
        S hload hdegree selected hij.symm hdisjoint.symm
          (fun e he => (S.graph.joins_comm e i j).mp (hjoins e he)) t ht
    · have hempty :
          selected.filter (fun e => routerEndpointAt S j e = t) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        have heSelected := (Finset.mem_filter.mp he).1
        have het := (Finset.mem_filter.mp he).2
        exact ht (het ▸
          (routerEndpointAt_mem_cluster_of_joins
            S hij e (hjoins e heSelected)).2)
      simp [hempty]
  rcases exists_boundedDegreeBipartiteMatching
      selected (routerEndpointAt S i) (routerEndpointAt S j)
      (2 * Delta) hfiberI hfiberJ with
    ⟨matching, hmatching, hinjI, hinjJ, hcard⟩
  have hmatchingWidth : width ≤ matching.card := by
    by_contra hnot
    have hsmall : matching.card < width := Nat.lt_of_not_ge hnot
    have : selected.card < 4 * Delta * width := by
      calc
        selected.card ≤ 2 * (2 * Delta) * matching.card := hcard
        _ = 4 * Delta * matching.card := by ring
        _ < 4 * Delta * width :=
          Nat.mul_lt_mul_of_pos_left hsmall (by positivity)
    omega
  rcases Finset.exists_subset_card_eq hmatchingWidth with
    ⟨exact, hexact, hexactCard⟩
  have hexactSelected : exact ⊆ selected := hexact.trans hmatching
  refine ⟨exact, hexactSelected, hexactCard,
    hinjI.mono hexact, hinjJ.mono hexact, ?_, ?_⟩
  · intro e he
    exact (routerEndpointAt_mem_cluster_of_joins
      S hij e (hjoins e (hexactSelected he))).1
  · intro e he
    exact (routerEndpointAt_mem_cluster_of_joins
      S hij e (hjoins e (hexactSelected he))).2

/-- Paths in a fixed router bundle whose endpoint at `i` is reserved. -/
theorem routerEndpointInReserved_card_le
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (selected : Finset S.graph.Edge)
    {i j : Fin n} (hij : i ≠ j)
    (hdisjoint : Disjoint (cluster i) (cluster j))
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (reserved : Finset V) (hreserved : reserved ⊆ cluster i) :
    (selected.filter fun e => routerEndpointAt S i e ∈ reserved).card ≤
      2 * Delta * reserved.card := by
  classical
  let fiber : V → Finset S.graph.Edge := fun t =>
    selected.filter fun e => routerEndpointAt S i e = t
  have hcover :
      selected.filter (fun e => routerEndpointAt S i e ∈ reserved) ⊆
        reserved.biUnion fiber := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_biUnion.mpr
      ⟨routerEndpointAt S i e, he'.2,
        Finset.mem_filter.mpr ⟨he'.1, rfl⟩⟩
  calc
    (selected.filter fun e => routerEndpointAt S i e ∈ reserved).card ≤
        (reserved.biUnion fiber).card :=
      Finset.card_le_card hcover
    _ ≤ reserved.card * (2 * Delta) := by
      apply Finset.card_biUnion_le_card_mul
      intro t ht
      exact routerEndpointFiber_card_le_two_mul_degree
        S hload hdegree selected hij hdisjoint hjoins t (hreserved ht)
    _ = 2 * Delta * reserved.card := by ring

/-- Paths avoiding the already reserved endpoint interfaces at routers
`i` and `j`. -/
noncomputable def routerAvoidingReservedEndpoints
    (S : RouterPathSkeleton G cluster)
    (selected : Finset S.graph.Edge) (i j : Fin n)
    (reservedI reservedJ : Finset V) :
    Finset S.graph.Edge := by
  classical
  exact selected.filter fun e =>
    routerEndpointAt S i e ∉ reservedI ∧
      routerEndpointAt S j e ∉ reservedJ

@[simp] theorem mem_routerAvoidingReservedEndpoints
    (S : RouterPathSkeleton G cluster)
    {selected : Finset S.graph.Edge} {i j : Fin n}
    {reservedI reservedJ : Finset V} {e : S.graph.Edge} :
    e ∈ routerAvoidingReservedEndpoints S selected i j
        reservedI reservedJ ↔
      e ∈ selected ∧
        routerEndpointAt S i e ∉ reservedI ∧
        routerEndpointAt S j e ∉ reservedJ := by
  classical
  simp [routerAvoidingReservedEndpoints]

/-- Native RouterPathSkeleton form of the long-support-path endpoint step in
Chekuri--Chuzhoy Section 5.4.1. -/
theorem exists_router_longSupportPath_endpoint_thinning
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    {i j : Fin n} (hij : i ≠ j)
    (hdisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (reservedI reservedJ : Finset V)
    (hreservedI : reservedI ⊆ cluster i)
    (hreservedJ : reservedJ ⊆ cluster j)
    (hreserve :
      4 * Delta * (reservedI.card + reservedJ.card) ≤ selected.card) :
    ∃ thinned : Finset S.graph.Edge,
      thinned ⊆ selected ∧
        selected.card / (8 * Delta ^ 2) ≤ thinned.card ∧
        Set.InjOn (routerEndpointAt S i) thinned ∧
        Set.InjOn (routerEndpointAt S j) thinned ∧
        (∀ e ∈ thinned,
          routerEndpointAt S i e ∈ cluster i \ reservedI) ∧
        (∀ e ∈ thinned,
          routerEndpointAt S j e ∈ cluster j \ reservedJ) ∧
        (∀ ⦃e⦄, e ∈ thinned → ∀ ⦃f⦄, f ∈ thinned → e ≠ f →
          (S.hostPath e).InternallyDisjoint (S.hostPath f)) := by
  classical
  let available :=
    routerAvoidingReservedEndpoints S selected i j reservedI reservedJ
  have havailableSubset : available ⊆ selected := by
    intro e he
    exact ((mem_routerAvoidingReservedEndpoints S).1 he).1
  have hjoinsAvailable :
      ∀ e ∈ available, S.graph.Joins e i j := by
    intro e he
    exact hjoins e (havailableSubset he)
  have hfiberI :
      ∀ t : V,
        (available.filter fun e => routerEndpointAt S i e = t).card ≤
          2 * Delta := by
    intro t
    by_cases ht : t ∈ cluster i
    · exact routerEndpointFiber_card_le_two_mul_degree
        S hload hdegree available hij hdisjoint hjoinsAvailable t ht
    · have hempty :
          available.filter (fun e => routerEndpointAt S i e = t) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        have heAvailable : e ∈ available := (Finset.mem_filter.mp he).1
        have het : routerEndpointAt S i e = t :=
          (Finset.mem_filter.mp he).2
        exact ht (het ▸
          (routerEndpointAt_mem_cluster_of_joins
            S hij e (hjoinsAvailable e heAvailable)).1)
      simp [hempty]
  have hfiberJ :
      ∀ t : V,
        (available.filter fun e => routerEndpointAt S j e = t).card ≤
          2 * Delta := by
    intro t
    by_cases ht : t ∈ cluster j
    · exact routerEndpointFiber_card_le_two_mul_degree
        S hload hdegree available hij.symm
          hdisjoint.symm
          (fun e he => (S.graph.joins_comm e i j).mp
            (hjoinsAvailable e he))
          t ht
    · have hempty :
          available.filter (fun e => routerEndpointAt S j e = t) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        have heAvailable : e ∈ available := (Finset.mem_filter.mp he).1
        have het : routerEndpointAt S j e = t :=
          (Finset.mem_filter.mp he).2
        exact ht (het ▸
          (routerEndpointAt_mem_cluster_of_joins
            S hij e (hjoinsAvailable e heAvailable)).2)
      simp [hempty]
  rcases exists_boundedDegreeBipartiteMatching
      available (routerEndpointAt S i) (routerEndpointAt S j)
      (2 * Delta) hfiberI hfiberJ with
    ⟨thinned, hthinAvailable, hinjI, hinjJ, hmatchingCard⟩
  have hthinSelected : thinned ⊆ selected :=
    hthinAvailable.trans havailableSubset
  let badI :=
    selected.filter fun e => routerEndpointAt S i e ∈ reservedI
  let badJ :=
    selected.filter fun e => routerEndpointAt S j e ∈ reservedJ
  have hcover : selected ⊆ available ∪ (badI ∪ badJ) := by
    intro e he
    by_cases hi : routerEndpointAt S i e ∈ reservedI
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨he, hi⟩))
    · by_cases hj : routerEndpointAt S j e ∈ reservedJ
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨he, hj⟩))
      · exact Finset.mem_union_left _
          ((mem_routerAvoidingReservedEndpoints S).2 ⟨he, hi, hj⟩)
  have hcardAvailable :
      selected.card ≤
        available.card +
          2 * Delta * (reservedI.card + reservedJ.card) := by
    calc
      selected.card ≤ (available ∪ (badI ∪ badJ)).card :=
        Finset.card_le_card hcover
      _ ≤ available.card + (badI ∪ badJ).card :=
        Finset.card_union_le _ _
      _ ≤ available.card + (badI.card + badJ.card) :=
        Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ ≤ available.card +
          (2 * Delta * reservedI.card +
            2 * Delta * reservedJ.card) := by
        apply Nat.add_le_add_left
        exact Nat.add_le_add
          (by
            simpa [badI] using
              (routerEndpointInReserved_card_le
                S hload hdegree selected hij hdisjoint hjoins
                  reservedI hreservedI))
          (by
            simpa [badJ] using
              (routerEndpointInReserved_card_le
                S hload hdegree selected hij.symm hdisjoint.symm
                  (fun e he => (S.graph.joins_comm e i j).mp (hjoins e he))
                  reservedJ hreservedJ))
      _ = available.card +
          2 * Delta * (reservedI.card + reservedJ.card) := by ring
  have hcardAdd :
      selected.card ≤
        4 * Delta * thinned.card +
          2 * Delta * (reservedI.card + reservedJ.card) := by
    calc
      selected.card ≤
          available.card +
            2 * Delta * (reservedI.card + reservedJ.card) :=
        hcardAvailable
      _ ≤ (2 * (2 * Delta) * thinned.card) +
            2 * Delta * (reservedI.card + reservedJ.card) :=
        Nat.add_le_add_right hmatchingCard _
      _ = 4 * Delta * thinned.card +
            2 * Delta * (reservedI.card + reservedJ.card) := by ring
  have hreserveHalf :
      2 * (2 * Delta * (reservedI.card + reservedJ.card)) ≤
        selected.card := by
    calc
      2 * (2 * Delta * (reservedI.card + reservedJ.card)) =
          4 * Delta * (reservedI.card + reservedJ.card) := by ring
      _ ≤ selected.card := hreserve
  have hcardEight :
      selected.card ≤ 8 * Delta * thinned.card := by
    calc
      selected.card ≤ 2 * (4 * Delta * thinned.card) := by omega
      _ = 8 * Delta * thinned.card := by ring
  have hDeltaSq : Delta ≤ Delta ^ 2 := by
    calc
      Delta = Delta * 1 := by simp
      _ ≤ Delta * Delta := Nat.mul_le_mul_left Delta hDelta
      _ = Delta ^ 2 := by ring
  have hfloor :
      selected.card / (8 * Delta ^ 2) ≤ thinned.card := by
    apply Nat.div_le_of_le_mul
    exact hcardEight.trans
      (Nat.mul_le_mul_right thinned.card
        (Nat.mul_le_mul_left 8 hDeltaSq))
  refine
    ⟨thinned, hthinSelected, hfloor, hinjI, hinjJ, ?_, ?_, ?_⟩
  · intro e he
    have heAvailable :=
      (mem_routerAvoidingReservedEndpoints S).1 (hthinAvailable he)
    exact Finset.mem_sdiff.mpr
      ⟨(routerEndpointAt_mem_cluster_of_joins
          S hij e (hjoins e (hthinSelected he))).1,
        heAvailable.2.1⟩
  · intro e he
    have heAvailable :=
      (mem_routerAvoidingReservedEndpoints S).1 (hthinAvailable he)
    exact Finset.mem_sdiff.mpr
      ⟨(routerEndpointAt_mem_cluster_of_joins
          S hij e (hjoins e (hthinSelected he))).2,
        heAvailable.2.2⟩
  · intro e he f hf hef
    exact S.one_per_group_internally_node_disjoint
      global htransversal
        (hselectedGlobal (hthinSelected he))
        (hselectedGlobal (hthinSelected hf)) hef

/-- Exact-width, empty-reserve specialization used by the Claim 5.14 support
path assembly.  Once the endpoint matching contains at least `width` paths,
an arbitrary exact-size subset retains both endpoint injectivity properties
and all source skeleton provenance. -/
theorem exists_routerBundle_exact_endpoint_thinning
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    {i j : Fin n} (hij : i ≠ j)
    (hdisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    {width : Nat}
    (hwidth : width ≤ selected.card / (8 * Delta ^ 2)) :
    ∃ exact : Finset S.graph.Edge,
      exact ⊆ selected ∧
        exact.card = width ∧
        Set.InjOn (routerEndpointAt S i) exact ∧
        Set.InjOn (routerEndpointAt S j) exact ∧
        (∀ e ∈ exact, routerEndpointAt S i e ∈ cluster i) ∧
        (∀ e ∈ exact, routerEndpointAt S j e ∈ cluster j) := by
  classical
  rcases exists_router_longSupportPath_endpoint_thinning
      S hload hdegree hDelta hij hdisjoint global htransversal
      selected hselectedGlobal hjoins
      (∅ : Finset V) (∅ : Finset V)
      (by simp) (by simp) (by simp) with
    ⟨thinned, hthinSelected, hthinLarge, hinjI, hinjJ,
      hmemI, hmemJ, _hinternal⟩
  have hwidthThin : width ≤ thinned.card :=
    hwidth.trans hthinLarge
  rcases Finset.exists_subset_card_eq hwidthThin with
    ⟨exact, hexactThin, hexactCard⟩
  refine
    ⟨exact, hexactThin.trans hthinSelected, hexactCard,
      hinjI.mono hexactThin, hinjJ.mono hexactThin, ?_, ?_⟩
  · intro e he
    exact (Finset.mem_sdiff.mp (hmemI e (hexactThin he))).1
  · intro e he
    exact (Finset.mem_sdiff.mp (hmemJ e (hexactThin he))).1

/-- Exact-width endpoint thinning with previously used endpoint sets excluded.

This is the iterative form needed by the long-support-path branch: after an
edge bundle has been selected, its endpoint set at the next router is passed
as a reserve to the following edge.  The returned exact bundle therefore has
fresh endpoints at both incident routers while remaining inside the single
global group transversal. -/
theorem exists_routerBundle_exact_endpoint_thinning_avoiding
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    {i j : Fin n} (hij : i ≠ j)
    (hdisjoint : Disjoint (cluster i) (cluster j))
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (selected : Finset S.graph.Edge)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (reservedI reservedJ : Finset V)
    (hreservedI : reservedI ⊆ cluster i)
    (hreservedJ : reservedJ ⊆ cluster j)
    {width : Nat}
    (hreserve :
      4 * Delta * (reservedI.card + reservedJ.card) ≤ selected.card)
    (hwidth : width ≤ selected.card / (8 * Delta ^ 2)) :
    ∃ exact : Finset S.graph.Edge,
      exact ⊆ selected ∧
        exact.card = width ∧
        Set.InjOn (routerEndpointAt S i) exact ∧
        Set.InjOn (routerEndpointAt S j) exact ∧
        (∀ e ∈ exact,
          routerEndpointAt S i e ∈ cluster i \ reservedI) ∧
        (∀ e ∈ exact,
          routerEndpointAt S j e ∈ cluster j \ reservedJ) := by
  classical
  rcases exists_router_longSupportPath_endpoint_thinning
      S hload hdegree hDelta hij hdisjoint global htransversal
      selected hselectedGlobal hjoins reservedI reservedJ
      hreservedI hreservedJ hreserve with
    ⟨thinned, hthinSelected, hthinLarge, hinjI, hinjJ,
      hmemI, hmemJ, _hinternal⟩
  have hwidthThin : width ≤ thinned.card := hwidth.trans hthinLarge
  rcases Finset.exists_subset_card_eq hwidthThin with
    ⟨exact, hexactThin, hexactCard⟩
  exact ⟨exact, hexactThin.trans hthinSelected, hexactCard,
    hinjI.mono hexactThin, hinjJ.mono hexactThin,
    fun e he => hmemI e (hexactThin he),
    fun e he => hmemJ e (hexactThin he)⟩

/-- Endpoints used by a selected router-skeleton bundle at one router. -/
noncomputable def routerBundleEndpointSet
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (selected : Finset S.graph.Edge) : Finset V := by
  classical
  exact selected.image (routerEndpointAt S i)

@[simp] theorem mem_routerBundleEndpointSet
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (selected : Finset S.graph.Edge) (v : V) :
    v ∈ routerBundleEndpointSet S i selected ↔
      ∃ e ∈ selected, routerEndpointAt S i e = v := by
  classical
  simp [routerBundleEndpointSet]

theorem routerBundleEndpointSet_card
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (selected : Finset S.graph.Edge)
    (hinj : Set.InjOn (routerEndpointAt S i) selected) :
    (routerBundleEndpointSet S i selected).card = selected.card := by
  classical
  exact Finset.card_image_iff.mpr hinj

theorem routerBundleEndpointSet_subset_cluster
    (S : RouterPathSkeleton G cluster) (i : Fin n)
    (selected : Finset S.graph.Edge)
    (hmem : ∀ e ∈ selected, routerEndpointAt S i e ∈ cluster i) :
    routerBundleEndpointSet S i selected ⊆ cluster i := by
  classical
  intro v hv
  rcases (mem_routerBundleEndpointSet S i selected v).mp hv with ⟨e, he, rfl⟩
  exact hmem e he

/-- Both endpoint sets used by one selected support edge. -/
noncomputable def routerBundleEndpointUnion
    (S : RouterPathSkeleton G cluster) (i j : Fin n)
    (selected : Finset S.graph.Edge) : Finset V :=
  routerBundleEndpointSet S i selected ∪
    routerBundleEndpointSet S j selected

theorem routerBundleEndpointUnion_card_le
    (S : RouterPathSkeleton G cluster) (i j : Fin n)
    (selected : Finset S.graph.Edge) {width : Nat}
    (hcard : selected.card = width)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected) :
    (routerBundleEndpointUnion S i j selected).card ≤ 2 * width := by
  classical
  calc
    (routerBundleEndpointUnion S i j selected).card ≤
        (routerBundleEndpointSet S i selected).card +
          (routerBundleEndpointSet S j selected).card :=
      Finset.card_union_le _ _
    _ = 2 * width := by
      rw [routerBundleEndpointSet_card S i selected hinjI,
        routerBundleEndpointSet_card S j selected hinjJ, hcard]
      omega

/-- A simultaneous exact selection for a finite family of requested support
edges.  Endpoint unions of distinct requests are disjoint; this is the
global invariant needed to upgrade the skeleton's internal disjointness to
node-disjoint tree-of-sets connectors. -/
structure RouterExactBundleFamily
    {R : Type*} [Fintype R] [DecidableEq R]
    (S : RouterPathSkeleton G cluster)
    (request : Finset R) (left right : R → Fin n)
    (candidate : R → Finset S.graph.Edge) (width : Nat) where
  exact : R → Finset S.graph.Edge
  exact_subset : ∀ r ∈ request, exact r ⊆ candidate r
  exact_card : ∀ r ∈ request, (exact r).card = width
  left_injective : ∀ r ∈ request,
    Set.InjOn (routerEndpointAt S (left r)) (exact r)
  right_injective : ∀ r ∈ request,
    Set.InjOn (routerEndpointAt S (right r)) (exact r)
  left_mem : ∀ r ∈ request, ∀ e ∈ exact r,
    routerEndpointAt S (left r) e ∈ cluster (left r)
  right_mem : ∀ r ∈ request, ∀ e ∈ exact r,
    routerEndpointAt S (right r) e ∈ cluster (right r)
  endpoint_disjoint : ∀ r (hr : r ∈ request) s (hs : s ∈ request),
    r ≠ s →
      Disjoint
        (routerBundleEndpointUnion S (left r) (right r) (exact r))
        (routerBundleEndpointUnion S (left s) (right s) (exact s))

namespace RouterExactBundleFamily

variable {R : Type*} [Fintype R] [DecidableEq R]
variable {S : RouterPathSkeleton G cluster}
variable {request : Finset R} {left right : R → Fin n}
variable {candidate : R → Finset S.graph.Edge} {width : Nat}

/-- All endpoints used by a partial exact-bundle family. -/
noncomputable def usedEndpoints
    (A : RouterExactBundleFamily S request left right candidate width) :
    Finset V := by
  classical
  exact request.biUnion fun r =>
    routerBundleEndpointUnion S (left r) (right r) (A.exact r)

theorem endpointUnion_subset_usedEndpoints
    (A : RouterExactBundleFamily S request left right candidate width)
    {r : R} (hr : r ∈ request) :
    routerBundleEndpointUnion S (left r) (right r) (A.exact r) ⊆
      A.usedEndpoints := by
  classical
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨r, hr, hv⟩

theorem usedEndpoints_card_le
    (A : RouterExactBundleFamily S request left right candidate width) :
    A.usedEndpoints.card ≤ request.card * (2 * width) := by
  classical
  apply Finset.card_biUnion_le_card_mul
  intro r hr
  exact routerBundleEndpointUnion_card_le S (left r) (right r) (A.exact r)
    (A.exact_card r hr) (A.left_injective r hr) (A.right_injective r hr)

end RouterExactBundleFamily

/-- Finite greedy endpoint thinning.  The reserve in each step consists of
all endpoints already used inside either new incident cluster.  The explicit
`16 * Delta * |request| * width` term pays for those reserves, while the
`8 * Delta^2 * width` term pays for endpoint-fiber thinning. -/
theorem exists_routerExactBundleFamily
    {R : Type*} [Fintype R] [DecidableEq R]
    (S : RouterPathSkeleton G cluster)
    (hload : S.EndpointCongestionAtMost 2)
    (hdegree : MaxDegreeAtMost G Delta)
    (hDelta : 0 < Delta)
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (request : Finset R) (left right : R → Fin n)
    (hleftRight : ∀ r ∈ request, left r ≠ right r)
    (hclusterDisjoint : ∀ r ∈ request,
      Disjoint (cluster (left r)) (cluster (right r)))
    (candidate : R → Finset S.graph.Edge)
    (hcandidateGlobal : ∀ r ∈ request, candidate r ⊆ global)
    (hcandidateJoins : ∀ r ∈ request, ∀ e ∈ candidate r,
      S.graph.Joins e (left r) (right r))
    {width : Nat}
    (hcandidateLarge : ∀ r ∈ request,
      16 * Delta * request.card * width + 8 * Delta ^ 2 * width ≤
        (candidate r).card) :
    Nonempty
      (RouterExactBundleFamily S request left right candidate width) := by
  classical
  induction request using Finset.induction_on with
  | empty =>
      exact ⟨{
        exact := fun _ => ∅
        exact_subset := by simp
        exact_card := by simp
        left_injective := by simp
        right_injective := by simp
        left_mem := by simp
        right_mem := by simp
        endpoint_disjoint := by simp }⟩
  | @insert a s ha ih =>
      have hleftRightS : ∀ r ∈ s, left r ≠ right r := by
        intro r hr
        exact hleftRight r (Finset.mem_insert_of_mem hr)
      have hclusterDisjointS : ∀ r ∈ s,
          Disjoint (cluster (left r)) (cluster (right r)) := by
        intro r hr
        exact hclusterDisjoint r (Finset.mem_insert_of_mem hr)
      have hcandidateGlobalS : ∀ r ∈ s, candidate r ⊆ global := by
        intro r hr
        exact hcandidateGlobal r (Finset.mem_insert_of_mem hr)
      have hcandidateJoinsS : ∀ r ∈ s, ∀ e ∈ candidate r,
          S.graph.Joins e (left r) (right r) := by
        intro r hr e he
        exact hcandidateJoins r (Finset.mem_insert_of_mem hr) e he
      have hcandidateLargeS : ∀ r ∈ s,
          16 * Delta * s.card * width + 8 * Delta ^ 2 * width ≤
            (candidate r).card := by
        intro r hr
        apply le_trans ?_ (hcandidateLarge r (Finset.mem_insert_of_mem hr))
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right width
            (Nat.mul_le_mul_left (16 * Delta)
              (Finset.card_le_card (Finset.subset_insert a s)))) _
      rcases ih hleftRightS hclusterDisjointS hcandidateGlobalS
          hcandidateJoinsS hcandidateLargeS with ⟨A⟩
      let used : Finset V := A.usedEndpoints
      let reserveLeft : Finset V := used ∩ cluster (left a)
      let reserveRight : Finset V := used ∩ cluster (right a)
      have hreserveLeft : reserveLeft ⊆ cluster (left a) :=
        Finset.inter_subset_right
      have hreserveRight : reserveRight ⊆ cluster (right a) :=
        Finset.inter_subset_right
      have hreserveCard :
          reserveLeft.card + reserveRight.card ≤ 4 * s.card * width := by
        have hleftCard : reserveLeft.card ≤ used.card :=
          Finset.card_le_card Finset.inter_subset_left
        have hrightCard : reserveRight.card ≤ used.card :=
          Finset.card_le_card Finset.inter_subset_left
        have husedCard : used.card ≤ s.card * (2 * width) :=
          A.usedEndpoints_card_le
        calc
          reserveLeft.card + reserveRight.card ≤ used.card + used.card :=
            Nat.add_le_add hleftCard hrightCard
          _ ≤ (s.card * (2 * width)) + (s.card * (2 * width)) :=
            Nat.add_le_add husedCard husedCard
          _ = 4 * s.card * width := by ring
      have hreserve :
          4 * Delta * (reserveLeft.card + reserveRight.card) ≤
            (candidate a).card := by
        calc
          4 * Delta * (reserveLeft.card + reserveRight.card) ≤
              4 * Delta * (4 * s.card * width) :=
            Nat.mul_le_mul_left (4 * Delta) hreserveCard
          _ = 16 * Delta * s.card * width := by ring
          _ ≤ 16 * Delta * (insert a s).card * width := by
            exact Nat.mul_le_mul_right width
              (Nat.mul_le_mul_left (16 * Delta)
                (Finset.card_le_card (Finset.subset_insert a s)))
          _ ≤ 16 * Delta * (insert a s).card * width +
              8 * Delta ^ 2 * width := Nat.le_add_right _ _
          _ ≤ (candidate a).card :=
            hcandidateLarge a (Finset.mem_insert_self a s)
      have hwidth :
          width ≤ (candidate a).card / (8 * Delta ^ 2) := by
        apply (Nat.le_div_iff_mul_le (by positivity : 0 < 8 * Delta ^ 2)).2
        calc
          width * (8 * Delta ^ 2) = 8 * Delta ^ 2 * width := by ring
          _ ≤ 16 * Delta * (insert a s).card * width +
              8 * Delta ^ 2 * width := Nat.le_add_left _ _
          _ ≤ (candidate a).card :=
            hcandidateLarge a (Finset.mem_insert_self a s)
      rcases exists_routerBundle_exact_endpoint_thinning_avoiding
          S hload hdegree hDelta
          (hleftRight a (Finset.mem_insert_self a s))
          (hclusterDisjoint a (Finset.mem_insert_self a s))
          global htransversal (candidate a)
          (hcandidateGlobal a (Finset.mem_insert_self a s))
          (hcandidateJoins a (Finset.mem_insert_self a s))
          reserveLeft reserveRight hreserveLeft hreserveRight
          hreserve hwidth with
        ⟨newExact, hnewSubset, hnewCard, hnewLeftInj, hnewRightInj,
          hnewLeftMem, hnewRightMem⟩
      let exact : R → Finset S.graph.Edge := fun r =>
        if r = a then newExact else A.exact r
      have hnewEndpointDisjointUsed :
          Disjoint
            (routerBundleEndpointUnion S (left a) (right a) newExact)
            used := by
        rw [Finset.disjoint_left]
        intro v hvNew hvUsed
        rcases Finset.mem_union.mp hvNew with hvLeft | hvRight
        · rcases (mem_routerBundleEndpointSet S (left a) newExact v).mp hvLeft with
            ⟨e, he, hev⟩
          have hmem := Finset.mem_sdiff.mp (hnewLeftMem e he)
          have hvCluster : v ∈ cluster (left a) := by simpa [← hev] using hmem.1
          have hvReserve : v ∈ reserveLeft :=
            Finset.mem_inter.mpr ⟨hvUsed, hvCluster⟩
          exact hmem.2 (by simpa [← hev] using hvReserve)
        · rcases (mem_routerBundleEndpointSet S (right a) newExact v).mp hvRight with
            ⟨e, he, hev⟩
          have hmem := Finset.mem_sdiff.mp (hnewRightMem e he)
          have hvCluster : v ∈ cluster (right a) := by simpa [← hev] using hmem.1
          have hvReserve : v ∈ reserveRight :=
            Finset.mem_inter.mpr ⟨hvUsed, hvCluster⟩
          exact hmem.2 (by simpa [← hev] using hvReserve)
      refine ⟨{
        exact := exact
        exact_subset := ?_
        exact_card := ?_
        left_injective := ?_
        right_injective := ?_
        left_mem := ?_
        right_mem := ?_
        endpoint_disjoint := ?_ }⟩
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · simpa [exact] using hnewSubset
        · have hra : r ≠ a := fun h => ha (h ▸ hr)
          simpa [exact, hra] using A.exact_subset r hr
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · simpa [exact] using hnewCard
        · have hra : r ≠ a := fun h => ha (h ▸ hr)
          simpa [exact, hra] using A.exact_card r hr
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · simpa [exact] using hnewLeftInj
        · have hra : r ≠ a := fun h => ha (h ▸ hr)
          simpa [exact, hra] using A.left_injective r hr
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · simpa [exact] using hnewRightInj
        · have hra : r ≠ a := fun h => ha (h ▸ hr)
          simpa [exact, hra] using A.right_injective r hr
      · intro r hr e he
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact (Finset.mem_sdiff.mp
            (hnewLeftMem e (by simpa [exact] using he))).1
        · have hra : r ≠ a := fun h => ha (h ▸ hr)
          exact A.left_mem r hr e (by simpa [exact, hra] using he)
      · intro r hr e he
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact (Finset.mem_sdiff.mp
            (hnewRightMem e (by simpa [exact] using he))).1
        · have hra : r ≠ a := fun h => ha (h ▸ hr)
          exact A.right_mem r hr e (by simpa [exact, hra] using he)
      · intro r hr t ht hrt
        by_cases hra : r = a
        · subst r
          have hta : t ≠ a := by simpa [eq_comm] using hrt
          have htS : t ∈ s :=
            (Finset.mem_insert.mp ht).resolve_left hta
          have hsubsetUsed := A.endpointUnion_subset_usedEndpoints htS
          simpa [exact, hta] using
            hnewEndpointDisjointUsed.mono_right hsubsetUsed
        · by_cases hta : t = a
          · subst t
            have hrS : r ∈ s :=
              (Finset.mem_insert.mp hr).resolve_left hra
            have hsubsetUsed := A.endpointUnion_subset_usedEndpoints hrS
            simpa [exact, hra] using
              hnewEndpointDisjointUsed.symm.mono_left hsubsetUsed
          · have hrS : r ∈ s :=
              (Finset.mem_insert.mp hr).resolve_left hra
            have htS : t ∈ s :=
              (Finset.mem_insert.mp ht).resolve_left hta
            simpa [exact, hra, hta] using
              A.endpoint_disjoint r hrS t htS hrt

theorem hostPath_endpoint_mem_routerBundleEndpointUnion
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j) {selected : Finset S.graph.Edge}
    {e : S.graph.Edge} (he : e ∈ selected)
    (hjoins : S.graph.Joins e i j) {v : V}
    (hv : (S.hostPath e).IsEndpoint v) :
    v ∈ routerBundleEndpointUnion S i j selected := by
  classical
  rcases routerEndpointAt_pair_of_joins S hij e hjoins with h | h
  · rcases hv with rfl | rfl
    · exact Finset.mem_union_left _ <|
        (mem_routerBundleEndpointSet S i selected _).mpr ⟨e, he, h.1⟩
    · exact Finset.mem_union_right _ <|
        (mem_routerBundleEndpointSet S j selected _).mpr ⟨e, he, h.2⟩
  · rcases hv with rfl | rfl
    · exact Finset.mem_union_right _ <|
        (mem_routerBundleEndpointSet S j selected _).mpr ⟨e, he, h.2⟩
    · exact Finset.mem_union_left _ <|
        (mem_routerBundleEndpointSet S i selected _).mpr ⟨e, he, h.1⟩

theorem router_ne_of_joins
    (S : RouterPathSkeleton G cluster) {i j : Fin n}
    (e : S.graph.Edge) (he : S.graph.Joins e i j) : i ≠ j := by
  intro hij
  rcases he with h | h
  · exact S.graph.end_ne e (h.1.trans (hij.trans h.2.symm))
  · exact S.graph.end_ne e (h.2.trans (hij.symm.trans h.1.symm))

/-- Within one exact bundle, internal disjointness from the global transversal
upgrades to node disjointness once both endpoint maps are injective. -/
theorem routerHostPath_nodeDisjoint_of_endpoint_injective
    (S : RouterPathSkeleton G cluster)
    {i j : Fin n} (hij : i ≠ j)
    (hclusterDisjoint : Disjoint (cluster i) (cluster j))
    (global selected : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (hselectedGlobal : selected ⊆ global)
    (hjoins : ∀ e ∈ selected, S.graph.Joins e i j)
    (hinjI : Set.InjOn (routerEndpointAt S i) selected)
    (hinjJ : Set.InjOn (routerEndpointAt S j) selected)
    {e f : S.graph.Edge} (he : e ∈ selected) (hf : f ∈ selected)
    (hef : e ≠ f) :
    (S.hostPath e).NodeDisjoint (S.hostPath f) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hve hvf
  have hinter := S.one_per_group_internally_node_disjoint
    global htransversal (hselectedGlobal he) (hselectedGlobal hf) hef hve hvf
  have endpoint_side : ∀ (g : S.graph.Edge), S.graph.Joins g i j →
      (S.hostPath g).IsEndpoint v →
        v = routerEndpointAt S i g ∨ v = routerEndpointAt S j g := by
    intro g hg hvg
    rcases routerEndpointAt_pair_of_joins S hij g hg with h | h <;>
      rcases hvg with rfl | rfl
    · exact Or.inl h.1.symm
    · exact Or.inr h.2.symm
    · exact Or.inr h.2.symm
    · exact Or.inl h.1.symm
  rcases endpoint_side e (hjoins e he) hinter.1 with hei | hej <;>
    rcases endpoint_side f (hjoins f hf) hinter.2 with hfi | hfj
  · exact hef (hinjI he hf (hei.symm.trans hfi))
  · exact Finset.disjoint_left.mp hclusterDisjoint
      (hei ▸ (routerEndpointAt_mem_cluster_of_joins S hij e (hjoins e he)).1)
      (hfj ▸ (routerEndpointAt_mem_cluster_of_joins S hij f (hjoins f hf)).2)
  · exact Finset.disjoint_left.mp hclusterDisjoint
      (hfi ▸ (routerEndpointAt_mem_cluster_of_joins S hij f (hjoins f hf)).1)
      (hej ▸ (routerEndpointAt_mem_cluster_of_joins S hij e (hjoins e he)).2)
  · exact hef (hinjJ he hf (hej.symm.trans hfj))

/-- Exact bundles belonging to distinct requests are node-disjoint. -/
theorem RouterExactBundleFamily.hostPath_nodeDisjoint_of_ne
    {R : Type*} [Fintype R] [DecidableEq R]
    (S : RouterPathSkeleton G cluster)
    (global : Finset S.graph.Edge)
    (htransversal : S.IsGroupTransversal global)
    (request : Finset R) (left right : R → Fin n)
    (candidate : R → Finset S.graph.Edge) {width : Nat}
    (A : RouterExactBundleFamily S request left right candidate width)
    (hcandidateGlobal : ∀ r ∈ request, candidate r ⊆ global)
    (hcandidateJoins : ∀ r ∈ request, ∀ e ∈ candidate r,
      S.graph.Joins e (left r) (right r))
    {r t : R} (hr : r ∈ request) (ht : t ∈ request) (hrt : r ≠ t)
    {e f : S.graph.Edge} (he : e ∈ A.exact r) (hf : f ∈ A.exact t) :
    (S.hostPath e).NodeDisjoint (S.hostPath f) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hve hvf
  have heCandidate := A.exact_subset r hr he
  have hfCandidate := A.exact_subset t ht hf
  have hef : e ≠ f := by
    intro hef
    have hvEndpoint :=
      hostPath_endpoint_mem_routerBundleEndpointUnion S
        (router_ne_of_joins S e (hcandidateJoins r hr e heCandidate))
        he (hcandidateJoins r hr e heCandidate)
        (Or.inl rfl)
    have hvEndpoint' :=
      hostPath_endpoint_mem_routerBundleEndpointUnion S
        (router_ne_of_joins S f (hcandidateJoins t ht f hfCandidate))
        hf (hcandidateJoins t ht f hfCandidate)
        (Or.inl rfl)
    exact Finset.disjoint_left.mp (A.endpoint_disjoint r hr t ht hrt)
      hvEndpoint (by simpa [hef] using hvEndpoint')
  have hinter := S.one_per_group_internally_node_disjoint global htransversal
    (hcandidateGlobal r hr heCandidate) (hcandidateGlobal t ht hfCandidate)
    hef hve hvf
  exact Finset.disjoint_left.mp (A.endpoint_disjoint r hr t ht hrt)
    (hostPath_endpoint_mem_routerBundleEndpointUnion S
      (router_ne_of_joins S e (hcandidateJoins r hr e heCandidate))
      he (hcandidateJoins r hr e heCandidate) hinter.1)
    (hostPath_endpoint_mem_routerBundleEndpointUnion S
      (router_ne_of_joins S f (hcandidateJoins t ht f hfCandidate))
      hf (hcandidateJoins t ht f hfCandidate) hinter.2)

end RouterSkeleton

end ChekuriChuzhoySection5EndpointThinning
end SimpleGraph

end Lax17Proofs
