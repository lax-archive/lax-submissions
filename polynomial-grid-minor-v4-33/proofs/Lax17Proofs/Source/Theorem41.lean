import Lax17Proofs.Source.Menger
import Lax17Proofs.Source.PathContraction
import Lax17Proofs.Source.PseudoGrid

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Theorem 4.1

This file collects the theorem-specific infrastructure for Section 4.1.  It
identifies the contracted graph `H_i`, its two terminal sets `S_i` and `X`,
and the finite Menger alternative used at every iteration.

The file proves the self-contained Menger step for each contracted graph, the
finite `D`-step control flow, the complete separator branch producing a
pseudo-grid, and the successful-linkage branch producing a crossbar in the
original graph.  The final theorem is `Theorem41Setup.theorem_four_one`.
-/

namespace SimpleGraph


namespace Theorem41Setup

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B X : Finset V}
variable {g kappa D : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

/-- The contracted graph used in one iteration of Theorem 4.1, obtained by
contracting the currently remaining `P`-paths indexed by `I`. -/
noncomputable def contractedGraph
    (_S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    _root_.SimpleGraph (ContractedPathVertex P I) :=
  contractedPathGraph G P I

/-- The `S_i` terminal set in the contracted graph: all vertices corresponding
to contracted remaining paths. -/
noncomputable def contractedPathTerminals
    (_S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    Finset (ContractedPathVertex P I) :=
  ContractedPathVertex.pathTerminalSet

/-- Vertices of `X` are outside every contracted `P`-path. -/
theorem x_outside_contracted_paths
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    ∀ x ∈ X, ∀ i : P.Index, i ∈ I → x ∉ (P.path i).vertexSet := by
  intro x hx i _hi hxP
  exact Finset.disjoint_left.mp (S.P_path_disjoint_X i) hxP hx

/-- The image of `X` in the contracted graph. -/
noncomputable def contractedXTerminals
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    Finset (ContractedPathVertex P I) :=
  ContractedPathVertex.vertexTerminalSet X (S.x_outside_contracted_paths I)

@[simp] theorem contractedPathTerminals_card
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    (S.contractedPathTerminals I).card = I.card := by
  simpa [contractedPathTerminals] using
    (ContractedPathVertex.pathTerminalSet_card (P := P) (I := I))

@[simp] theorem contractedXTerminals_card
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    (S.contractedXTerminals I).card = X.card := by
  simpa [contractedXTerminals] using
    (ContractedPathVertex.vertexTerminalSet_card
      (P := P) (I := I) X (S.x_outside_contracted_paths I))

/-- The two terminal sets used in the contracted Menger instance are
disjoint. -/
theorem disjoint_contractedPathTerminals_contractedXTerminals
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    Disjoint (S.contractedPathTerminals I) (S.contractedXTerminals I) := by
  simpa [contractedPathTerminals, contractedXTerminals] using
    (ContractedPathVertex.disjoint_pathTerminalSet_vertexTerminalSet
      (P := P) (I := I) X (S.x_outside_contracted_paths I))

/-- The projection, in the contracted graph, of the `Q`-path whose source is
matched with the `P`-path indexed by `i`. -/
noncomputable def contractedMatchedQPath
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) (i : P.Index) :
    GraphPath (S.contractedGraph I) :=
  ContractedPathVertex.ProjectionWalk.toGraphPath
    (P := P) (I := I) (Q.path (P.matchedSourceIndex Q i))

theorem contractedMatchedQPath_source_eq
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index} {i : P.Index} (hi : i ∈ I) :
    (S.contractedMatchedQPath I i).source =
      (Sum.inl ⟨i, hi⟩ : ContractedPathVertex P I) := by
  classical
  have hsource :
      (Q.path (P.matchedSourceIndex Q i)).source = (P.path i).source :=
    P.source_matchedSourceIndex Q i
  have hmem :
      (Q.path (P.matchedSourceIndex Q i)).source ∈ (P.path i).vertexSet := by
    simp [hsource]
  simpa [contractedMatchedQPath, contractedGraph,
    ContractedPathVertex.ProjectionWalk.toGraphPath] using
    (ContractedPathVertex.projection_eq_of_mem_path
      (P := P) (I := I) hi hmem)

theorem contractedMatchedQPath_source_mem
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index} {i : P.Index} (hi : i ∈ I) :
    (S.contractedMatchedQPath I i).source ∈ S.contractedPathTerminals I := by
  rw [S.contractedMatchedQPath_source_eq hi]
  exact ContractedPathVertex.mem_pathTerminalSet_of_mem (P := P) (I := I) i hi

theorem contractedMatchedQPath_target_eq
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) (i : P.Index) :
    (S.contractedMatchedQPath I i).target =
      (Sum.inr
        ⟨(Q.path (P.matchedSourceIndex Q i)).target,
          S.x_outside_contracted_paths I
            (Q.path (P.matchedSourceIndex Q i)).target
            (Q.target_mem (P.matchedSourceIndex Q i))⟩ :
        ContractedPathVertex P I) := by
  classical
  have hx :
      ∀ j : P.Index, j ∈ I →
        (Q.path (P.matchedSourceIndex Q i)).target ∉ (P.path j).vertexSet := by
    intro j hj
    exact S.x_outside_contracted_paths I
      (Q.path (P.matchedSourceIndex Q i)).target
      (Q.target_mem (P.matchedSourceIndex Q i)) j hj
  simpa [contractedMatchedQPath, contractedGraph,
    ContractedPathVertex.ProjectionWalk.toGraphPath] using
    (ContractedPathVertex.projection_eq_of_forall_not_mem
      (P := P) (I := I) hx)

theorem contractedMatchedQPath_target_mem
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) (i : P.Index) :
    (S.contractedMatchedQPath I i).target ∈ S.contractedXTerminals I := by
  classical
  rw [S.contractedMatchedQPath_target_eq I i]
  unfold contractedXTerminals ContractedPathVertex.vertexTerminalSet
  exact Finset.mem_image.mpr
    ⟨⟨(Q.path (P.matchedSourceIndex Q i)).target,
        Q.target_mem (P.matchedSourceIndex Q i)⟩,
      by simp,
      rfl⟩

theorem contractedMatchedQPath_connects
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index} {i : P.Index} (hi : i ∈ I) :
    (S.contractedMatchedQPath I i).Connects
      (S.contractedPathTerminals I) (S.contractedXTerminals I) :=
  Or.inl ⟨S.contractedMatchedQPath_source_mem hi,
    S.contractedMatchedQPath_target_mem I i⟩

/-- Each contracted graph used in Section 4.1 is a minor of the original
graph. -/
theorem contractedGraph_isMinor
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    IsMinor (S.contractedGraph I) G := by
  simpa [contractedGraph] using
    (contractedPathGraph.isMinor (G := G) (P := P) (I := I))

/-- The exact Menger alternative applied in one iteration of Theorem 4.1. -/
def stepMengerAlternative
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) : Prop :=
  MengerAlternative (S.contractedGraph I)
    (S.contractedPathTerminals I) (S.contractedXTerminals I) (g ^ 2)

/-- Applying finite vertex-Menger to the contracted graph used at one
iteration of Theorem 4.1. -/
theorem stepMengerAlternative_of_finiteVertexMenger
    (hmenger : FiniteVertexMengerStatement.{u})
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    S.stepMengerAlternative I := by
  exact hmenger (V := ContractedPathVertex P I) (S.contractedGraph I)
    (S.contractedPathTerminals I) (S.contractedXTerminals I) (g ^ 2)

/-- The exact form of the Menger step used by the iteration: either we obtain
`g^2` disjoint contracted paths, or a separator of size at most `g^2`. -/
theorem stepMenger_exact_or_separator
    (hmenger : FiniteVertexMengerStatement.{u})
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    (∃ L : PathPacking (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I),
        L.card = g ^ 2) ∨
      ∃ J : Finset (ContractedPathVertex P I),
        J.card ≤ g ^ 2 ∧
          BlocksAllPaths (S.contractedGraph I)
            (S.contractedPathTerminals I) (S.contractedXTerminals I) J := by
  exact (MengerAlternative.exists_exact_or_separator
    (S.stepMengerAlternative_of_finiteVertexMenger hmenger I))

/-- The Menger step used by Theorem 4.1, with the now-formal finite Menger
theorem supplied directly. -/
theorem stepMenger_exact_or_separator_selfContained
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    (∃ L : PathPacking (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I),
        L.card = g ^ 2) ∨
      ∃ J : Finset (ContractedPathVertex P I),
        J.card ≤ g ^ 2 ∧
          BlocksAllPaths (S.contractedGraph I)
            (S.contractedPathTerminals I) (S.contractedXTerminals I) J := by
  exact S.stepMenger_exact_or_separator Menger.finite_vertex_menger I

/-- The row `R_i` extracted from a separator in the contracted graph: take
exactly those separator vertices that represent contracted `P`-paths, and
forget the proof that their indices lie in the current remaining set. -/
noncomputable def reservedOfSeparator
    (_S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    (J : Finset (ContractedPathVertex P I)) : Finset P.Index :=
  ContractedPathVertex.pathIndicesIn J

/-- The original-vertex part `J_i''` of a separator in the contracted graph. -/
noncomputable def originalSeparatorVertices
    (_S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    (J : Finset (ContractedPathVertex P I)) : Finset V :=
  ContractedPathVertex.originalVertexSetIn J

/-- The original vertices represented by a contracted separator: original
singleton separator vertices, together with all vertices on `P`-paths whose
contracted vertices lie in the separator.  This is the paper's set
`V_i = J_i'' ∪ ⋃_{P ∈ R_i} V(P)`. -/
noncomputable def separatorTraceVertices
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    (J : Finset (ContractedPathVertex P I)) : Finset V :=
  S.originalSeparatorVertices J ∪
    (S.reservedOfSeparator J).biUnion fun i : P.Index => (P.path i).vertexSet

theorem reservedOfSeparator_subset
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    (J : Finset (ContractedPathVertex P I)) :
    S.reservedOfSeparator J ⊆ I := by
  simpa [reservedOfSeparator] using
    (ContractedPathVertex.pathIndicesIn_subset (P := P) (I := I) J)

/-- The Case-2 separator row has size at most the separator. -/
theorem reservedOfSeparator_card_le
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    (J : Finset (ContractedPathVertex P I)) :
    (S.reservedOfSeparator J).card ≤ J.card := by
  simpa [reservedOfSeparator] using
    (ContractedPathVertex.pathIndicesIn_card_le (P := P) (I := I) J)

/-- The original-vertex part of a separator has size at most the separator. -/
theorem originalSeparatorVertices_card_le
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    (J : Finset (ContractedPathVertex P I)) :
    (S.originalSeparatorVertices J).card ≤ J.card := by
  simpa [originalSeparatorVertices] using
    (ContractedPathVertex.originalVertexSetIn_card_le (P := P) (I := I) J)

theorem reservedOfSeparator_card_le_of_separator
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    {J : Finset (ContractedPathVertex P I)}
    (hJ : J.card ≤ g ^ 2) :
    (S.reservedOfSeparator J).card ≤ g ^ 2 :=
  (S.reservedOfSeparator_card_le J).trans hJ

theorem originalSeparatorVertices_card_le_of_separator
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    {J : Finset (ContractedPathVertex P I)}
    (hJ : J.card ≤ g ^ 2) :
    (S.originalSeparatorVertices J).card ≤ g ^ 2 :=
  (S.originalSeparatorVertices_card_le J).trans hJ

/-- A contracted separator forces every remaining matched `Q`-path to hit the
corresponding original trace set.  This is the formal version of the paper's
sentence: each path in `Q'_i = {Q_P | P ∈ P'_i}` must contain a vertex of
`V_i = J_i'' ∪ ⋃_{P ∈ R_i} V(P)`. -/
theorem matchedQPath_meets_separatorTraceVertices
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    {J : Finset (ContractedPathVertex P I)}
    (hJ :
      BlocksAllPaths (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I) J)
    {i : P.Index} (hi : i ∈ I) :
    ∃ v ∈ (Q.path (P.matchedSourceIndex Q i)).vertexSet,
      v ∈ S.separatorTraceVertices J := by
  classical
  rcases hJ (S.contractedMatchedQPath I i)
      (S.contractedMatchedQPath_connects hi) with
    ⟨z, hzPath, hzJ⟩
  rcases ContractedPathVertex.ProjectionWalk.toGraphPath_vertexSet_subset_projection
      (P := P) (I := I) (Q.path (P.matchedSourceIndex Q i)) z hzPath with
    ⟨v, hvQ, hvz⟩
  refine ⟨v, hvQ, ?_⟩
  cases z with
  | inl j =>
      have hvBranch :
          v ∈ (P.path j.1).vertexSet := by
        have hvb :=
          ContractedPathVertex.mem_branch_projection
            (P := P) (I := I) v
        rw [hvz] at hvb
        simpa [contractedPathBranch] using hvb
      have hjReserved : j.1 ∈ S.reservedOfSeparator J := by
        simpa [reservedOfSeparator] using
          (ContractedPathVertex.mem_pathIndicesIn_iff
            (P := P) (I := I) J j.1).2 ⟨j.2, hzJ⟩
      exact Finset.mem_union.2 (Or.inr
        (Finset.mem_biUnion.2 ⟨j.1, hjReserved, hvBranch⟩))
  | inr w =>
      have hvEq : v = w.1 := by
        have hvb :=
          ContractedPathVertex.mem_branch_projection
            (P := P) (I := I) v
        rw [hvz] at hvb
        simpa [contractedPathBranch] using hvb
      have hwOriginal : w.1 ∈ S.originalSeparatorVertices J := by
        simpa [originalSeparatorVertices] using
          (ContractedPathVertex.mem_originalVertexSetIn_iff
            (P := P) (I := I) J w.1).2 ⟨w.2, hzJ⟩
      exact Finset.mem_union.2 (Or.inl (by simpa [hvEq] using hwOriginal))

/-- If the projection of an original vertex lies in a contracted separator,
then the original vertex belongs to the separator trace. -/
theorem mem_separatorTraceVertices_of_projection_mem_separator
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    {J : Finset (ContractedPathVertex P I)}
    {v : V} {z : ContractedPathVertex P I}
    (hvz : ContractedPathVertex.projection (P := P) (I := I) v = z)
    (hzJ : z ∈ J) :
    v ∈ S.separatorTraceVertices J := by
  classical
  cases z with
  | inl j =>
      have hvBranch :
          v ∈ (P.path j.1).vertexSet := by
        have hvb :=
          ContractedPathVertex.mem_branch_projection
            (P := P) (I := I) v
        rw [hvz] at hvb
        simpa [contractedPathBranch] using hvb
      have hjReserved : j.1 ∈ S.reservedOfSeparator J := by
        simpa [reservedOfSeparator] using
          (ContractedPathVertex.mem_pathIndicesIn_iff
            (P := P) (I := I) J j.1).2 ⟨j.2, hzJ⟩
      exact Finset.mem_union.2 (Or.inr
        (Finset.mem_biUnion.2 ⟨j.1, hjReserved, hvBranch⟩))
  | inr w =>
      have hvEq : v = w.1 := by
        have hvb :=
          ContractedPathVertex.mem_branch_projection
            (P := P) (I := I) v
        rw [hvz] at hvb
        simpa [contractedPathBranch] using hvb
      have hwOriginal : w.1 ∈ S.originalSeparatorVertices J := by
        simpa [originalSeparatorVertices] using
          (ContractedPathVertex.mem_originalVertexSetIn_iff
            (P := P) (I := I) J w.1).2 ⟨w.2, hzJ⟩
      exact Finset.mem_union.2 (Or.inl (by simpa [hvEq] using hwOriginal))

/-- The separator outcome of one iteration, unpacked into the two pieces used
by the pseudo-grid construction. -/
theorem step_separator_data
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index}
    {J : Finset (ContractedPathVertex P I)}
    (hJcard : J.card ≤ g ^ 2)
    (hJ :
      BlocksAllPaths (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I) J) :
    (S.reservedOfSeparator J ⊆ I) ∧
      (S.reservedOfSeparator J).card ≤ g ^ 2 ∧
      (S.originalSeparatorVertices J).card ≤ g ^ 2 ∧
      ∀ ⦃i : P.Index⦄, i ∈ I →
        ∃ v ∈ (Q.path (P.matchedSourceIndex Q i)).vertexSet,
          v ∈ S.separatorTraceVertices J := by
  exact ⟨S.reservedOfSeparator_subset J,
    S.reservedOfSeparator_card_le_of_separator hJcard,
    S.originalSeparatorVertices_card_le_of_separator hJcard,
    fun {i} hi => S.matchedQPath_meets_separatorTraceVertices hJ hi⟩

/-- A fully unpacked one-step alternative: either the contracted graph has the
large linkage that the paper turns into a crossbar, or it supplies the bounded
row/separator trace data used by the pseudo-grid iteration. -/
theorem step_linkage_or_separator_data
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) :
    (∃ L : PathPacking (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I),
        L.card = g ^ 2) ∨
      ∃ J : Finset (ContractedPathVertex P I),
        J.card ≤ g ^ 2 ∧
          BlocksAllPaths (S.contractedGraph I)
            (S.contractedPathTerminals I) (S.contractedXTerminals I) J ∧
          S.reservedOfSeparator J ⊆ I ∧
          (S.reservedOfSeparator J).card ≤ g ^ 2 ∧
          (S.originalSeparatorVertices J).card ≤ g ^ 2 ∧
          ∀ ⦃i : P.Index⦄, i ∈ I →
            ∃ v ∈ (Q.path (P.matchedSourceIndex Q i)).vertexSet,
              v ∈ S.separatorTraceVertices J := by
  rcases S.stepMenger_exact_or_separator_selfContained I with hlink | hsep
  · exact Or.inl hlink
  · rcases hsep with ⟨J, hJcard, hJblocks⟩
    rcases S.step_separator_data hJcard hJblocks with
      ⟨hsub, hRcard, hOcard, hhit⟩
    exact Or.inr ⟨J, hJcard, hJblocks, hsub, hRcard, hOcard, hhit⟩

/-- Under the depth bound of Theorem 4.1, `D` rows of size at most `g^2`
occupy at most half of the original `κ` paths.  This is the formal version of
the paper's estimate following the `D` iterations. -/
theorem two_mul_reservedUnion_card_le_kappa
    (S : Theorem41Setup G A B X g kappa D P Q)
    (R : Fin D → Finset P.Index)
    (hR : ∀ i : Fin D, (R i).card ≤ g ^ 2) :
    2 * (pseudoGridReservedUnion R).card ≤ kappa := by
  have hunion : (pseudoGridReservedUnion R).card ≤ D * g ^ 2 :=
    pseudoGridReservedUnion_card_le R hR
  have hDmul :
      D * (2 * g ^ 2) ≤ (kappa / (2 * g ^ 2)) * (2 * g ^ 2) :=
    Nat.mul_le_mul_right (2 * g ^ 2) S.D_le
  have hdiv :
      (kappa / (2 * g ^ 2)) * (2 * g ^ 2) ≤ kappa :=
    Nat.div_mul_le_self kappa (2 * g ^ 2)
  calc
    2 * (pseudoGridReservedUnion R).card
        ≤ 2 * (D * g ^ 2) := Nat.mul_le_mul_left 2 hunion
    _ = D * (2 * g ^ 2) := by
      rw [← Nat.mul_assoc, Nat.mul_comm 2 D, Nat.mul_assoc]
    _ ≤ (kappa / (2 * g ^ 2)) * (2 * g ^ 2) := hDmul
    _ ≤ kappa := hdiv

/-- Consequently at least `κ / 4` original `P`-paths remain after the row
removals.  The paper obtains the stronger `κ/2` lower bound; this weaker form
is exactly what is needed to choose `⌊κ/4⌋` final `Q'` paths. -/
theorem kappa_div_four_le_remaining_card
    (S : Theorem41Setup G A B X g kappa D P Q)
    (R : Fin D → Finset P.Index)
    (hR : ∀ i : Fin D, (R i).card ≤ g ^ 2) :
    kappa / 4 ≤ (pseudoGridRemaining R).card := by
  classical
  let U := pseudoGridReservedUnion R
  have htwo : 2 * U.card ≤ kappa := by
    simpa [U] using S.two_mul_reservedUnion_card_le_kappa R hR
  have hcard :
      (pseudoGridRemaining R).card = Fintype.card P.Index - U.card := by
    have hsubset : U ⊆ (Finset.univ : Finset P.Index) := by
      intro x hx
      simp
    simp [pseudoGridRemaining, U, Finset.card_sdiff_of_subset hsubset]
  have hPcard : Fintype.card P.Index = kappa := by
    simpa [PerfectPathPacking.card] using S.P_card
  rw [hcard, hPcard]
  omega

/-- After the row removals one can choose the `⌊κ/4⌋` remaining parent paths
used to index the final family `Q'`. -/
theorem exists_parentSet_card_eq_quarter
    (S : Theorem41Setup G A B X g kappa D P Q)
    (R : Fin D → Finset P.Index)
    (hR : ∀ i : Fin D, (R i).card ≤ g ^ 2) :
    ∃ Parents : Finset P.Index,
      Parents ⊆ pseudoGridRemaining R ∧ Parents.card = P.card / 4 := by
  classical
  have hle : P.card / 4 ≤ (pseudoGridRemaining R).card := by
    simpa [S.P_card] using S.kappa_div_four_le_remaining_card R hR
  rcases Finset.exists_subset_card_eq hle with ⟨Parents, hsub, hcard⟩
  exact ⟨Parents, hsub, hcard⟩

/-- The last iteration index, available from the positive-depth hypothesis. -/
noncomputable def lastIterationIndex
    (S : Theorem41Setup G A B X g kappa D P Q) : Fin D :=
  ⟨D - 1, by
    have hD : 0 < D := S.D_pos_strict
    omega⟩

/-- The data obtained when every Menger step in Theorem 4.1 returns a
separator, expressed at the level needed to build the final pseudo-grid.

The fields `hit_trace`, `suffix_disjoint_remaining`, and
`good_final_intersects` are the formal versions of the two observations after
the separator construction in the paper: every remaining matched `Q`-path hits
the trace `V_i`; after the last hit its suffix avoids paths still remaining;
and an `i`-good plus final-good path has its final suffix intersecting row
`R_i`. -/
structure SeparatorRun
    (S : Theorem41Setup G A B X g kappa D P Q) where
  /-- The rows `R_i` selected by the separators. -/
  reserved : Fin D → Finset P.Index
  /-- The original-vertex separator part `J_i''`. -/
  original : Fin D → Finset V
  /-- The trace `V_i = J_i'' ∪ ⋃_{P ∈ R_i} V(P)` in the original graph. -/
  trace : Fin D → Finset V
  trace_eq :
    ∀ i : Fin D,
      trace i = original i ∪
        (reserved i).biUnion fun p : P.Index => (P.path p).vertexSet
  reserved_subset_remainingBefore :
    ∀ i : Fin D, reserved i ⊆ pseudoGridRemainingBefore reserved i
  reserved_card_le : ∀ i : Fin D, (reserved i).card ≤ g ^ 2
  original_card_le : ∀ i : Fin D, (original i).card ≤ g ^ 2
  hit_trace :
    ∀ (i : Fin D) (p : P.Index),
      p ∈ pseudoGridRemainingBefore reserved i →
        ((Q.path (P.matchedSourceIndex Q p)).vertexSet ∩ trace i).Nonempty
  suffix_disjoint_remaining :
    ∀ (p q : P.Index)
      (hp : p ∈ pseudoGridRemaining reserved)
      (_hq : q ∈ pseudoGridRemaining reserved),
          GraphPath.NodeDisjoint (P.path q)
            ((Q.path (P.matchedSourceIndex Q p)).cleanSuffixFromSet
              (trace (S.lastIterationIndex))
              (hit_trace (S.lastIterationIndex) p
                (pseudoGridRemaining_subset_remainingBefore reserved
                  (S.lastIterationIndex) hp)))
  good_final_intersects :
    ∀ (i : Fin D) (p : P.Index)
      (hp : p ∈ pseudoGridRemaining reserved),
      (∃ r ∈ reserved i,
        (Q.path (P.matchedSourceIndex Q p)).lastHitVertex (trace i)
          (hit_trace i p
            (pseudoGridRemaining_subset_remainingBefore reserved i hp)) ∈
          (P.path r).vertexSet) →
      (∃ r ∈ reserved (S.lastIterationIndex),
        (Q.path (P.matchedSourceIndex Q p)).lastHitVertex
          (trace (S.lastIterationIndex))
          (hit_trace (S.lastIterationIndex) p
            (pseudoGridRemaining_subset_remainingBefore reserved
              (S.lastIterationIndex) hp)) ∈
          (P.path r).vertexSet) →
      ∃ r ∈ reserved i,
        ¬ Disjoint (P.path r).vertexSet
          ((Q.path (P.matchedSourceIndex Q p)).cleanSuffixFromSet
            (trace (S.lastIterationIndex))
            (hit_trace (S.lastIterationIndex) p
              (pseudoGridRemaining_subset_remainingBefore reserved
                (S.lastIterationIndex) hp))).vertexSet

/-- The separator-run data before the two final geometric suffix facts are
attached.  This is exactly what the contracted Menger separators give
immediately: rows, original separator vertices, trace sets, their size bounds,
and the fact that every currently surviving matched `Q` path hits the trace. -/
structure SeparatorRunCore
    (S : Theorem41Setup G A B X g kappa D P Q) where
  reserved : Fin D → Finset P.Index
  original : Fin D → Finset V
  trace : Fin D → Finset V
  trace_eq :
    ∀ i : Fin D,
      trace i = original i ∪
        (reserved i).biUnion fun p : P.Index => (P.path p).vertexSet
  reserved_subset_remainingBefore :
    ∀ i : Fin D, reserved i ⊆ pseudoGridRemainingBefore reserved i
  reserved_card_le : ∀ i : Fin D, (reserved i).card ≤ g ^ 2
  original_card_le : ∀ i : Fin D, (original i).card ≤ g ^ 2
  hit_trace :
    ∀ (i : Fin D) (p : P.Index),
      p ∈ pseudoGridRemainingBefore reserved i →
        ((Q.path (P.matchedSourceIndex Q p)).vertexSet ∩ trace i).Nonempty

namespace SeparatorRunCore

variable {S : Theorem41Setup G A B X g kappa D P Q}

/-- Attach the two remaining geometric suffix facts to a core run. -/
def toSeparatorRun
    (C : SeparatorRunCore S)
    (suffix_disjoint_remaining :
      ∀ (p q : P.Index)
        (hp : p ∈ pseudoGridRemaining C.reserved)
        (_hq : q ∈ pseudoGridRemaining C.reserved),
          GraphPath.NodeDisjoint (P.path q)
            ((Q.path (P.matchedSourceIndex Q p)).cleanSuffixFromSet
              (C.trace (S.lastIterationIndex))
              (C.hit_trace (S.lastIterationIndex) p
                (pseudoGridRemaining_subset_remainingBefore C.reserved
                  (S.lastIterationIndex) hp))))
    (good_final_intersects :
      ∀ (i : Fin D) (p : P.Index)
        (hp : p ∈ pseudoGridRemaining C.reserved),
        (∃ r ∈ C.reserved i,
          (Q.path (P.matchedSourceIndex Q p)).lastHitVertex (C.trace i)
            (C.hit_trace i p
              (pseudoGridRemaining_subset_remainingBefore C.reserved i hp)) ∈
            (P.path r).vertexSet) →
        (∃ r ∈ C.reserved (S.lastIterationIndex),
          (Q.path (P.matchedSourceIndex Q p)).lastHitVertex
            (C.trace (S.lastIterationIndex))
            (C.hit_trace (S.lastIterationIndex) p
              (pseudoGridRemaining_subset_remainingBefore C.reserved
                (S.lastIterationIndex) hp)) ∈
            (P.path r).vertexSet) →
        ∃ r ∈ C.reserved i,
          ¬ Disjoint (P.path r).vertexSet
            ((Q.path (P.matchedSourceIndex Q p)).cleanSuffixFromSet
              (C.trace (S.lastIterationIndex))
              (C.hit_trace (S.lastIterationIndex) p
                (pseudoGridRemaining_subset_remainingBefore C.reserved
                  (S.lastIterationIndex) hp))).vertexSet) :
    SeparatorRun S where
  reserved := C.reserved
  original := C.original
  trace := C.trace
  trace_eq := C.trace_eq
  reserved_subset_remainingBefore := C.reserved_subset_remainingBefore
  reserved_card_le := C.reserved_card_le
  original_card_le := C.original_card_le
  hit_trace := C.hit_trace
  suffix_disjoint_remaining := suffix_disjoint_remaining
  good_final_intersects := good_final_intersects

end SeparatorRunCore

/-- A concrete choice of contracted separator at each row of the Section 4.1
iteration.  The contracted graph at row `i` uses exactly the paths remaining
before that row, so the type of `J i` depends on the earlier rows. -/
structure SeparatorChoiceRun
    (S : Theorem41Setup G A B X g kappa D P Q) where
  reserved : Fin D → Finset P.Index
  J : ∀ i : Fin D,
    Finset (ContractedPathVertex P (pseudoGridRemainingBefore reserved i))
  reserved_eq :
    ∀ i : Fin D, reserved i = S.reservedOfSeparator (J i)
  J_card_le : ∀ i : Fin D, (J i).card ≤ g ^ 2
  J_blocks :
    ∀ i : Fin D,
      BlocksAllPaths (S.contractedGraph (pseudoGridRemainingBefore reserved i))
        (S.contractedPathTerminals (pseudoGridRemainingBefore reserved i))
        (S.contractedXTerminals (pseudoGridRemainingBefore reserved i))
        (J i)

namespace SeparatorChoiceRun

variable {S : Theorem41Setup G A B X g kappa D P Q}

/-- The original-vertex separator part of a chosen row separator. -/
noncomputable def original (C : SeparatorChoiceRun S) (i : Fin D) :
    Finset V :=
  S.originalSeparatorVertices (C.J i)

/-- The original graph trace of a chosen row separator. -/
noncomputable def trace (C : SeparatorChoiceRun S) (i : Fin D) :
    Finset V :=
  S.separatorTraceVertices (C.J i)

/-- The immediate core run extracted from the chosen contracted separators. -/
noncomputable def toCore (C : SeparatorChoiceRun S) :
    SeparatorRunCore S where
  reserved := C.reserved
  original := C.original
  trace := C.trace
  trace_eq := by
    intro i
    change S.separatorTraceVertices (C.J i) =
      S.originalSeparatorVertices (C.J i) ∪
        (C.reserved i).biUnion fun p : P.Index => (P.path p).vertexSet
    rw [C.reserved_eq i]
    rfl
  reserved_subset_remainingBefore := by
    intro i
    rw [C.reserved_eq i]
    exact S.reservedOfSeparator_subset (C.J i)
  reserved_card_le := by
    intro i
    rw [C.reserved_eq i]
    exact S.reservedOfSeparator_card_le_of_separator (C.J_card_le i)
  original_card_le := by
    intro i
    exact S.originalSeparatorVertices_card_le_of_separator (C.J_card_le i)
  hit_trace := by
    intro i p hp
    rcases S.matchedQPath_meets_separatorTraceVertices (C.J_blocks i) hp with
      ⟨v, hvQ, hvTrace⟩
    exact ⟨v, Finset.mem_inter.2 ⟨hvQ, hvTrace⟩⟩

/-- A trace vertex cannot lie on a path that is still present before row `i`
and is not selected into row `i`. -/
theorem not_mem_trace_of_mem_remaining_path_of_not_reserved
    (C : SeparatorChoiceRun S) (i : Fin D) (q : P.Index)
    (hqBefore : q ∈ pseudoGridRemainingBefore C.reserved i)
    (hqNotReserved : q ∉ C.reserved i)
    {v : V} (hvPath : v ∈ (P.path q).vertexSet)
    (hvTrace : v ∈ C.trace i) : False := by
  classical
  have htraceEq := (C.toCore).trace_eq i
  change v ∈ (C.toCore).trace i at hvTrace
  rw [htraceEq] at hvTrace
  rcases Finset.mem_union.1 hvTrace with hvOriginal | hvRow
  · change v ∈ S.originalSeparatorVertices (C.J i) at hvOriginal
    rcases (ContractedPathVertex.mem_originalVertexSetIn_iff
        (P := P) (I := pseudoGridRemainingBefore C.reserved i)
        (C.J i) v).1 hvOriginal with ⟨hvOutside, _hvJ⟩
    exact hvOutside q hqBefore hvPath
  · rcases Finset.mem_biUnion.1 hvRow with ⟨r, hrReserved, hvR⟩
    have hrBefore : r ∈ pseudoGridRemainingBefore C.reserved i := by
      have hsub : C.reserved i ⊆ pseudoGridRemainingBefore C.reserved i := by
        rw [C.reserved_eq i]
        exact S.reservedOfSeparator_subset (C.J i)
      exact hsub hrReserved
    have hqr : q = r :=
      ContractedPathVertex.path_index_unique_of_mem
        (P := P) (I := pseudoGridRemainingBefore C.reserved i)
        hqBefore hrBefore hvPath hvR
    exact hqNotReserved (by simpa [hqr] using hrReserved)

/-- Observation 4.2 in its separator form: after the last hit of the separator
trace in row `i`, the matched `Q`-path cannot meet any path that remains after
that row. -/
theorem cleanSuffix_disjoint_remaining_of_separator
    (C : SeparatorChoiceRun S) (i : Fin D) (p q : P.Index)
    (hpBefore : p ∈ pseudoGridRemainingBefore C.reserved i)
    (hqBefore : q ∈ pseudoGridRemainingBefore C.reserved i)
    (hqNotReserved : q ∉ C.reserved i) :
    GraphPath.NodeDisjoint (P.path q)
      ((Q.path (P.matchedSourceIndex Q p)).cleanSuffixFromSet
        (C.trace i) ((C.toCore).hit_trace i p hpBefore)) := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvPq hvSuffix
  let I := pseudoGridRemainingBefore C.reserved i
  let Qp := Q.path (P.matchedSourceIndex Q p)
  let hhit : (Qp.vertexSet ∩ C.trace i).Nonempty :=
    (C.toCore).hit_trace i p hpBefore
  let suffix := Qp.cleanSuffixFromSet (C.trace i) hhit
  have hvSuffix' : v ∈ suffix.vertexSet := by
    simpa [suffix, Qp, hhit] using hvSuffix
  have hsourceTrace : suffix.source ∈ C.trace i := by
    simpa [suffix] using Qp.cleanSuffixFromSet_source_mem (C.trace i) hhit
  have hv_ne_source : v ≠ suffix.source := by
    intro hv
    exact C.not_mem_trace_of_mem_remaining_path_of_not_reserved i q
      hqBefore hqNotReserved (by simpa [hv] using hvPq) hsourceTrace
  let hsourceMem : suffix.source ∈ suffix.vertexSet :=
    GraphPath.source_mem_vertexSet suffix
  have hvInDropSource :
      v ∈ (suffix.dropUntil hsourceMem).vertexSet :=
    suffix.mem_dropUntil_source_of_mem hvSuffix'
  let hvSuffixOld : v ∈ suffix.vertexSet :=
    suffix.dropUntil_vertexSet_subset hsourceMem hvInDropSource
  let tail := suffix.dropUntil hvSuffixOld
  have hsource_not_tail : suffix.source ∉ tail.vertexSet := by
    simpa [tail, hvSuffixOld] using
      suffix.not_mem_dropUntil_of_mem_dropUntil_ne
        hsourceMem hvInDropSource hv_ne_source
  let tailProj :=
    ContractedPathVertex.ProjectionWalk.toGraphPath
      (P := P) (I := I) tail
  have hsourceProj :
      tailProj.source = (Sum.inl ⟨q, hqBefore⟩ : ContractedPathVertex P I) := by
    simpa [tailProj, tail, I] using
      (ContractedPathVertex.projection_eq_of_mem_path
        (P := P) (I := I) hqBefore hvPq)
  have hxOut :
      ∀ r : P.Index, r ∈ I →
        Qp.target ∉ (P.path r).vertexSet := by
    intro r hr
    exact S.x_outside_contracted_paths I Qp.target
      (by simpa [Qp] using Q.target_mem (P.matchedSourceIndex Q p)) r hr
  have htargetProj :
      tailProj.target =
        (Sum.inr ⟨Qp.target, hxOut⟩ : ContractedPathVertex P I) := by
    simpa [tailProj, tail, suffix, Qp, I] using
      (ContractedPathVertex.projection_eq_of_forall_not_mem
        (P := P) (I := I) hxOut)
  have hconnects :
      tailProj.Connects
        (S.contractedPathTerminals I) (S.contractedXTerminals I) := by
    refine Or.inl ⟨?_, ?_⟩
    · rw [hsourceProj]
      exact ContractedPathVertex.mem_pathTerminalSet_of_mem
        (P := P) (I := I) q hqBefore
    · rw [htargetProj]
      unfold Theorem41Setup.contractedXTerminals ContractedPathVertex.vertexTerminalSet
      exact Finset.mem_image.mpr
        ⟨⟨Qp.target, by simpa [Qp] using Q.target_mem (P.matchedSourceIndex Q p)⟩,
          by simp,
          rfl⟩
  rcases C.J_blocks i tailProj hconnects with ⟨z, hzTail, hzJ⟩
  rcases ContractedPathVertex.ProjectionWalk.toGraphPath_vertexSet_subset_projection
      (P := P) (I := I) tail z hzTail with
    ⟨w, hwTail, hwz⟩
  have hwTrace : w ∈ C.trace i := by
    change w ∈ S.separatorTraceVertices (C.J i)
    exact S.mem_separatorTraceVertices_of_projection_mem_separator hwz hzJ
  have hwSuffix : w ∈ suffix.vertexSet :=
    suffix.dropUntil_vertexSet_subset hvSuffixOld hwTail
  have hwEqSource : w = suffix.source := by
    have hwLast :
        w = Qp.lastHitVertex (C.trace i) hhit :=
      Qp.eq_lastHitVertex_of_mem_dropUntil_of_mem_set
        (C.trace i) hhit (by simpa [suffix] using hwSuffix) hwTrace
    simpa [suffix, GraphPath.cleanSuffixFromSet] using hwLast
  exact hsource_not_tail (by simpa [hwEqSource] using hwTail)

/-- The final-row instance of Observation 4.2, in exactly the form needed by
`SeparatorRunCore.toSeparatorRun`. -/
theorem finalSuffix_disjoint_remaining
    (C : SeparatorChoiceRun S) :
    ∀ (p q : P.Index)
      (hp : p ∈ pseudoGridRemaining (C.toCore).reserved)
      (_hq : q ∈ pseudoGridRemaining (C.toCore).reserved),
        GraphPath.NodeDisjoint (P.path q)
          ((Q.path (P.matchedSourceIndex Q p)).cleanSuffixFromSet
            ((C.toCore).trace (S.lastIterationIndex))
            ((C.toCore).hit_trace (S.lastIterationIndex) p
              (pseudoGridRemaining_subset_remainingBefore (C.toCore).reserved
                (S.lastIterationIndex) hp))) := by
  intro p q hp hq
  exact C.cleanSuffix_disjoint_remaining_of_separator
    (S.lastIterationIndex) p q
    (pseudoGridRemaining_subset_remainingBefore C.reserved
      (S.lastIterationIndex) hp)
    (pseudoGridRemaining_subset_remainingBefore C.reserved
      (S.lastIterationIndex) hq)
    (not_mem_reserved_of_mem_remaining C.reserved (S.lastIterationIndex) hq)

/-- The final comparison in the proof of property P2: if a surviving matched
`Q`-path is good at row `i` and good at the last row, then its final suffix
intersects row `i`. -/
theorem good_final_intersects
    (C : SeparatorChoiceRun S) :
    ∀ (i : Fin D) (p : P.Index)
      (hp : p ∈ pseudoGridRemaining (C.toCore).reserved),
      (∃ r ∈ (C.toCore).reserved i,
        (Q.path (P.matchedSourceIndex Q p)).lastHitVertex ((C.toCore).trace i)
          ((C.toCore).hit_trace i p
            (pseudoGridRemaining_subset_remainingBefore (C.toCore).reserved i hp)) ∈
          (P.path r).vertexSet) →
      (∃ r ∈ (C.toCore).reserved (S.lastIterationIndex),
        (Q.path (P.matchedSourceIndex Q p)).lastHitVertex
          ((C.toCore).trace (S.lastIterationIndex))
          ((C.toCore).hit_trace (S.lastIterationIndex) p
            (pseudoGridRemaining_subset_remainingBefore (C.toCore).reserved
              (S.lastIterationIndex) hp)) ∈
          (P.path r).vertexSet) →
      ∃ r ∈ (C.toCore).reserved i,
        ¬ Disjoint (P.path r).vertexSet
          ((Q.path (P.matchedSourceIndex Q p)).cleanSuffixFromSet
            ((C.toCore).trace (S.lastIterationIndex))
            ((C.toCore).hit_trace (S.lastIterationIndex) p
              (pseudoGridRemaining_subset_remainingBefore (C.toCore).reserved
                (S.lastIterationIndex) hp))).vertexSet := by
  classical
  intro i p hp hgood_i hgood_last
  let Qp := Q.path (P.matchedSourceIndex Q p)
  let last := S.lastIterationIndex
  let hpBefore_i :=
    pseudoGridRemaining_subset_remainingBefore C.reserved i hp
  let hpBefore_last :=
    pseudoGridRemaining_subset_remainingBefore C.reserved last hp
  let hhit_i : (Qp.vertexSet ∩ C.trace i).Nonempty :=
    (C.toCore).hit_trace i p hpBefore_i
  let hhit_last : (Qp.vertexSet ∩ C.trace last).Nonempty :=
    (C.toCore).hit_trace last p hpBefore_last
  let vi := Qp.lastHitVertex (C.trace i) hhit_i
  let vlast := Qp.lastHitVertex (C.trace last) hhit_last
  rcases hgood_i with ⟨ri, hri, hviRi⟩
  rcases hgood_last with ⟨rlast, hrlast, hvlastRlast⟩
  refine ⟨ri, hri, ?_⟩
  intro hdisj
  have hviQ : vi ∈ Qp.vertexSet :=
    Qp.lastHitVertex_mem_vertexSet (C.trace i) hhit_i
  have hvlastQ : vlast ∈ Qp.vertexSet :=
    Qp.lastHitVertex_mem_vertexSet (C.trace last) hhit_last
  by_cases hilast : i = last
  · subst hilast
    have hvi_eq_vlast : vi = vlast := rfl
    have hvSuffix :
        vi ∈ (Qp.cleanSuffixFromSet (C.trace last) hhit_last).vertexSet := by
      simpa [GraphPath.cleanSuffixFromSet, vi, vlast, hhit_last] using
        GraphPath.source_mem_vertexSet
          (Qp.cleanSuffixFromSet (C.trace last) hhit_last)
    exact Finset.disjoint_left.mp hdisj hviRi hvSuffix
  · have hi_lt_last : i.val < last.val := by
      have hD : 0 < D := S.D_pos_strict
      have hi_lt_D : i.val < D := i.isLt
      have hle : i.val ≤ D - 1 := by omega
      have hne : i.val ≠ D - 1 := by
        intro hval
        exact hilast (Fin.ext (by simpa [last, Theorem41Setup.lastIterationIndex] using hval))
      change i.val < D - 1
      omega
    have hrows_disjoint :
        ∀ ⦃a b : Fin D⦄, a ≠ b → Disjoint (C.reserved a) (C.reserved b) :=
      pseudoGridReserved_disjoint_of_subset_remainingBefore
        C.reserved (C.toCore).reserved_subset_remainingBefore
    have hrlast_before_i :
        rlast ∈ pseudoGridRemainingBefore C.reserved i := by
      rw [pseudoGridRemainingBefore]
      refine Finset.mem_sdiff.2 ⟨by simp, ?_⟩
      intro hprefix
      rcases Finset.mem_biUnion.1 hprefix with ⟨j, hjPrefix, hrj⟩
      have hj_lt_i : j.val < i.val := by
        simpa [pseudoGridPrefixRows] using hjPrefix
      have hj_ne_last : j ≠ last := by
        intro h
        have : last.val < last.val := by
          simpa [h] using Nat.lt_trans hj_lt_i hi_lt_last
        exact (Nat.lt_irrefl last.val) this
      exact Finset.disjoint_left.mp (hrows_disjoint hj_ne_last) hrj hrlast
    have hrlast_not_i : rlast ∉ C.reserved i := by
      intro hri_last
      exact Finset.disjoint_left.mp (hrows_disjoint hilast) hri_last hrlast
    have hsuffix_i_disj :
        GraphPath.NodeDisjoint (P.path rlast)
          (Qp.cleanSuffixFromSet (C.trace i) hhit_i) := by
      simpa [Qp, hhit_i] using
        C.cleanSuffix_disjoint_remaining_of_separator i p rlast
          hpBefore_i hrlast_before_i hrlast_not_i
    have hnot_vi_before_last : ¬ Qp.Before vi vlast := by
      intro hbefore
      have hvlast_suffix_i :
          vlast ∈ (Qp.cleanSuffixFromSet (C.trace i) hhit_i).vertexSet := by
        simpa [GraphPath.cleanSuffixFromSet, vi, hhit_i] using hbefore.2
      exact Finset.disjoint_left.mp hsuffix_i_disj hvlastRlast hvlast_suffix_i
    have hlast_before_vi : Qp.Before vlast vi := by
      have hnot_le :
          ¬ Qp.vertexIndex vi ≤ Qp.vertexIndex vlast := by
        intro hle
        exact hnot_vi_before_last
          ((Qp.before_iff_vertexIndex_le).2 ⟨hviQ, hvlastQ, hle⟩)
      have hlt : Qp.vertexIndex vlast < Qp.vertexIndex vi :=
        Nat.lt_of_not_ge hnot_le
      exact (Qp.before_iff_vertexIndex_le).2 ⟨hvlastQ, hviQ, hlt.le⟩
    have hvi_suffix_last :
        vi ∈ (Qp.cleanSuffixFromSet (C.trace last) hhit_last).vertexSet := by
      simpa [GraphPath.cleanSuffixFromSet, vlast, hhit_last] using
        hlast_before_vi.2
    exact Finset.disjoint_left.mp hdisj hviRi hvi_suffix_last

/-- A concrete separator choice at every row supplies the full separator run
used by the pseudo-grid construction. -/
noncomputable def toSeparatorRun (C : SeparatorChoiceRun S) :
    SeparatorRun S :=
  (C.toCore).toSeparatorRun
    C.finalSuffix_disjoint_remaining
    C.good_final_intersects

end SeparatorChoiceRun

/-- Transport a finite separator across an equality of the current
remaining-index sets.  Keeping this as a named definition prevents repeated
large reductions of raw equality casts in the iteration proof. -/
noncomputable def transportContractedSeparator
    {I I' : Finset P.Index} (h : I = I')
    (J : Finset (ContractedPathVertex P I)) :
    Finset (ContractedPathVertex P I') :=
  h ▸ J

/-- `reservedOfSeparator` is invariant under transporting a contracted
separator across an equality of current remaining-index sets. -/
theorem reservedOfSeparator_cast
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I I' : Finset P.Index} (h : I = I')
    (J : Finset (ContractedPathVertex P I)) :
    S.reservedOfSeparator (h ▸ J) = S.reservedOfSeparator J := by
  subst h
  rfl

theorem reservedOfSeparator_transportContractedSeparator
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I I' : Finset P.Index} (h : I = I')
    (J : Finset (ContractedPathVertex P I)) :
    S.reservedOfSeparator (transportContractedSeparator h J) =
      S.reservedOfSeparator J := by
  subst h
  rfl

omit [Fintype V] in
/-- Separator cardinality is invariant under transporting across an equality
of current remaining-index sets. -/
theorem separator_card_cast
    {I I' : Finset P.Index} (h : I = I')
    (J : Finset (ContractedPathVertex P I)) :
    (h ▸ J).card = J.card := by
  subst h
  rfl

omit [Fintype V] in
theorem transportContractedSeparator_card
    {I I' : Finset P.Index} (h : I = I')
    (J : Finset (ContractedPathVertex P I)) :
    (transportContractedSeparator h J).card = J.card := by
  subst h
  rfl

/-- The separator blocking predicate is invariant under transporting across
an equality of current remaining-index sets. -/
theorem blocksAllPaths_cast
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I I' : Finset P.Index} (h : I = I')
    {J : Finset (ContractedPathVertex P I)}
    (hJ :
      BlocksAllPaths (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I) J) :
    BlocksAllPaths (S.contractedGraph I')
      (S.contractedPathTerminals I') (S.contractedXTerminals I')
      (h ▸ J) := by
  subst h
  simpa using hJ

theorem blocksAllPaths_transportContractedSeparator
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I I' : Finset P.Index} (h : I = I')
    {J : Finset (ContractedPathVertex P I)}
    (hJ :
      BlocksAllPaths (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I) J) :
    BlocksAllPaths (S.contractedGraph I')
      (S.contractedPathTerminals I') (S.contractedXTerminals I')
      (transportContractedSeparator h J) := by
  subst h
  simpa using hJ


/-- A successful linkage outcome in one contracted graph.  The finite
iteration either finds such an outcome for some current remaining set `I`, or
it chooses separators for all `D` rows. -/
def ContractedLinkageAt
    (S : Theorem41Setup G A B X g kappa D P Q)
    (I : Finset P.Index) : Prop :=
  ∃ L : PathPacking (S.contractedGraph I)
      (S.contractedPathTerminals I) (S.contractedXTerminals I),
    L.card = g ^ 2

namespace ContractedLinkage

variable (S : Theorem41Setup G A B X g kappa D P Q)
variable {I : Finset P.Index}
variable (L : PathPacking (S.contractedGraph I)
    (S.contractedPathTerminals I) (S.contractedXTerminals I))

/-- The terminal-clean, oriented version of a contracted linkage. -/
noncomputable def clean :
    PathPacking (S.contractedGraph I)
      (S.contractedPathTerminals I) (S.contractedXTerminals I) :=
  L.cleanToTerminals.orient

@[simp] theorem clean_card :
    (clean S L).card = L.card := rfl

/-- Cleaning and orienting the contracted linkage leaves every cleaned path
internally disjoint from the two terminal sets. -/
theorem clean_terminalClean :
    (clean S L).TerminalClean := by
  change L.cleanToTerminals.orient.InternallyDisjointFromSet
    (S.contractedPathTerminals I ∪ S.contractedXTerminals I)
  exact PathPacking.orient_internallyDisjointFromSet
    (PathPacking.cleanToTerminals_terminalClean L)

/-- The source terminal of a cleaned contracted linkage path is represented by
some currently remaining `P`-path index. -/
theorem source_spec (a : L.Index) :
    ∃ (p : P.Index) (hp : p ∈ I),
      ((clean S L).path a).source =
        (Sum.inl ⟨p, hp⟩ : ContractedPathVertex P I) := by
  classical
  have hsource :
      ((clean S L).path a).source ∈ S.contractedPathTerminals I := by
    change (L.cleanToTerminals.orient.path a).source ∈
      S.contractedPathTerminals I
    simpa [clean] using
      GraphPath.orient_source_mem
        (L.cleanToTerminals.path a) (L.cleanToTerminals.connects a)
  exact (ContractedPathVertex.mem_pathTerminalSet_iff
    (P := P) (I := I) ((clean S L).path a).source).1 hsource

/-- The `P`-path index represented by the source terminal of a cleaned
contracted linkage path. -/
noncomputable def sourceIndex (a : L.Index) : P.Index :=
  Classical.choose (source_spec S L a)

theorem sourceIndex_mem (a : L.Index) : sourceIndex S L a ∈ I :=
  Classical.choose (Classical.choose_spec (source_spec S L a))

theorem clean_source_eq (a : L.Index) :
    ((clean S L).path a).source =
      (Sum.inl ⟨sourceIndex S L a, sourceIndex_mem S L a⟩ :
        ContractedPathVertex P I) :=
  Classical.choose_spec (Classical.choose_spec (source_spec S L a))

/-- The target terminal of a cleaned contracted linkage path is represented by
an original vertex of `X`. -/
theorem target_spec (a : L.Index) :
    ∃ (x : V) (_hx : x ∈ X)
      (hout : ∀ p : P.Index, p ∈ I → x ∉ (P.path p).vertexSet),
      ((clean S L).path a).target =
        (Sum.inr ⟨x, hout⟩ : ContractedPathVertex P I) := by
  classical
  have htarget :
      ((clean S L).path a).target ∈ S.contractedXTerminals I := by
    change (L.cleanToTerminals.orient.path a).target ∈
      S.contractedXTerminals I
    simpa [clean] using
      GraphPath.orient_target_mem
        (L.cleanToTerminals.path a) (L.cleanToTerminals.connects a)
  exact (ContractedPathVertex.mem_vertexTerminalSet_iff
    (P := P) (I := I) X (S.x_outside_contracted_paths I)
    ((clean S L).path a).target).1 htarget

/-- The original `X`-vertex represented by the target terminal of a cleaned
contracted linkage path. -/
noncomputable def targetVertex (a : L.Index) : V :=
  Classical.choose (target_spec S L a)

theorem targetVertex_mem_X (a : L.Index) : targetVertex S L a ∈ X :=
  Classical.choose (Classical.choose_spec (target_spec S L a))

theorem targetVertex_outside
    (a : L.Index) :
    ∀ p : P.Index, p ∈ I →
      targetVertex S L a ∉ (P.path p).vertexSet :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec (target_spec S L a)))

theorem clean_target_eq (a : L.Index) :
    ((clean S L).path a).target =
      (Sum.inr ⟨targetVertex S L a, targetVertex_outside S L a⟩ :
        ContractedPathVertex P I) :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec (target_spec S L a)))

/-- Distinct cleaned linkage paths use distinct contracted `P`-path source
terminals, hence distinct `P`-path indices. -/
theorem sourceIndex_injective :
    Function.Injective (sourceIndex S L) := by
  classical
  intro a b hab
  by_contra hne
  have hdisj := (clean S L).node_disjoint hne
  have hsource_a :
      ((clean S L).path a).source ∈ ((clean S L).path a).vertexSet :=
    GraphPath.source_mem_vertexSet ((clean S L).path a)
  have hsource_b :
      ((clean S L).path a).source ∈ ((clean S L).path b).vertexSet := by
    have hb :
        ((clean S L).path b).source ∈ ((clean S L).path b).vertexSet :=
      GraphPath.source_mem_vertexSet ((clean S L).path b)
    rw [clean_source_eq S L a]
    rw [clean_source_eq S L b] at hb
    simpa [hab] using hb
  exact Finset.disjoint_left.mp hdisj hsource_a hsource_b

/-- Distinct cleaned linkage paths also use distinct `X` target vertices. -/
theorem targetVertex_injective :
    Function.Injective (targetVertex S L) := by
  classical
  intro a b hab
  by_contra hne
  have hdisj := (clean S L).node_disjoint hne
  have htarget_a :
      ((clean S L).path a).target ∈ ((clean S L).path a).vertexSet :=
    GraphPath.target_mem_vertexSet ((clean S L).path a)
  have htarget_b :
      ((clean S L).path a).target ∈ ((clean S L).path b).vertexSet := by
    have hb :
        ((clean S L).path b).target ∈ ((clean S L).path b).vertexSet :=
      GraphPath.target_mem_vertexSet ((clean S L).path b)
    rw [clean_target_eq S L a]
    rw [clean_target_eq S L b] at hb
    simpa [hab] using hb
  exact Finset.disjoint_left.mp hdisj htarget_a htarget_b

/-- A cleaned contracted linkage path can meet the path-terminal set only at its
source endpoint. -/
theorem clean_eq_source_of_mem_pathTerminal
    (a : L.Index) {z : ContractedPathVertex P I}
    (hzPath : z ∈ ((clean S L).path a).vertexSet)
    (hzTerminal : z ∈ S.contractedPathTerminals I) :
    z = ((clean S L).path a).source := by
  classical
  have hend :
      ((clean S L).path a).IsEndpoint z :=
    clean_terminalClean S L a hzPath
      (Finset.mem_union_left _ hzTerminal)
  rcases hend with hsource | htarget
  · exact hsource
  · exfalso
    have htargetX :
        ((clean S L).path a).target ∈ S.contractedXTerminals I := by
      rw [clean_target_eq S L a]
      exact (ContractedPathVertex.mem_vertexTerminalSet_iff
        (P := P) (I := I) X (S.x_outside_contracted_paths I)
        (Sum.inr ⟨targetVertex S L a, targetVertex_outside S L a⟩)).2
        ⟨targetVertex S L a, targetVertex_mem_X S L a,
          targetVertex_outside S L a, rfl⟩
    exact Finset.disjoint_left.mp
      (S.disjoint_contractedPathTerminals_contractedXTerminals I)
      hzTerminal (by simpa [htarget] using htargetX)

/-- The main path in the original graph associated with a cleaned contracted
linkage path. -/
noncomputable def mainPath (a : L.Index) : GraphPath G :=
  P.path (sourceIndex S L a)

/-- The `A` endpoint of the source `P`-path lies in the branch represented by
the source terminal of the cleaned contracted linkage path. -/
theorem clean_source_branch_mem (a : L.Index) :
    (P.path (sourceIndex S L a)).source ∈
      contractedPathBranch ((clean S L).path a).source := by
  rw [clean_source_eq S L a]
  change (P.path (sourceIndex S L a)).source ∈
    (P.path (sourceIndex S L a)).vertexSet
  exact GraphPath.source_mem_vertexSet (P.path (sourceIndex S L a))

/-- The `X` endpoint represented by the target terminal of the cleaned
contracted linkage path lies in that target branch. -/
theorem clean_target_branch_mem (a : L.Index) :
    targetVertex S L a ∈
      contractedPathBranch ((clean S L).path a).target := by
  rw [clean_target_eq S L a]
  change targetVertex S L a ∈ ({targetVertex S L a} : Finset V)
  simp

/-- The loose original spoke obtained by lifting a cleaned contracted linkage
path from the source `P`-path's `A` endpoint to its `X` target.  This is not
yet the final crossbar spoke, because the final proof must trim the source
branch so that the spoke meets its main path in exactly one vertex. -/
noncomputable def looseSpoke (a : L.Index) : GraphPath G :=
  ContractedPathVertex.liftGraphPath (P := P) (I := I) ((clean S L).path a)
    (clean_source_branch_mem S L a)
    (clean_target_branch_mem S L a)

@[simp] theorem looseSpoke_source (a : L.Index) :
    (looseSpoke S L a).source = (P.path (sourceIndex S L a)).source := by
  exact ContractedPathVertex.liftGraphPath_source
    (P := P) (I := I) ((clean S L).path a)
    (clean_source_branch_mem S L a)
    (clean_target_branch_mem S L a)

@[simp] theorem looseSpoke_target (a : L.Index) :
    (looseSpoke S L a).target = targetVertex S L a := by
  exact ContractedPathVertex.liftGraphPath_target
    (P := P) (I := I) ((clean S L).path a)
    (clean_source_branch_mem S L a)
    (clean_target_branch_mem S L a)

theorem looseSpoke_target_mem_X (a : L.Index) :
    (looseSpoke S L a).target ∈ X := by
  simpa using targetVertex_mem_X S L a

theorem looseSpoke_vertexSet_subset_branchUnion (a : L.Index) :
    (looseSpoke S L a).vertexSet ⊆
      contractedPathBranchUnion ((clean S L).path a).vertexSet :=
  ContractedPathVertex.liftGraphPath_vertexSet_subset_branchUnion
    (P := P) (I := I) ((clean S L).path a)
    (clean_source_branch_mem S L a)
    (clean_target_branch_mem S L a)

/-- The loose lifted spoke already meets its associated main path at the `A`
endpoint of that main path. -/
theorem looseSpoke_meets_mainPath (a : L.Index) :
    ((looseSpoke S L a).vertexSet ∩ (mainPath S L a).vertexSet).Nonempty := by
  refine ⟨(mainPath S L a).source, Finset.mem_inter.2 ?_⟩
  constructor
  · simpa [mainPath] using GraphPath.source_mem_vertexSet (looseSpoke S L a)
  · exact GraphPath.source_mem_vertexSet (mainPath S L a)

/-- The final spoke used in the crossbar: trim the loose lifted path after its
last visit to the associated main path. -/
noncomputable def spokePath (a : L.Index) : GraphPath G :=
  (looseSpoke S L a).cleanSuffixFromSet (mainPath S L a).vertexSet
    (looseSpoke_meets_mainPath S L a)

theorem spokePath_vertexSet_subset_looseSpoke (a : L.Index) :
    (spokePath S L a).vertexSet ⊆ (looseSpoke S L a).vertexSet :=
  (looseSpoke S L a).cleanSuffixFromSet_vertexSet_subset
    (mainPath S L a).vertexSet (looseSpoke_meets_mainPath S L a)

theorem spokePath_source_mem_mainPath (a : L.Index) :
    (spokePath S L a).source ∈ (mainPath S L a).vertexSet := by
  simpa [spokePath] using
    (looseSpoke S L a).cleanSuffixFromSet_source_mem
      (mainPath S L a).vertexSet (looseSpoke_meets_mainPath S L a)

@[simp] theorem spokePath_target (a : L.Index) :
    (spokePath S L a).target = targetVertex S L a := by
  simp [spokePath]

theorem spokePath_target_mem_X (a : L.Index) :
    (spokePath S L a).target ∈ X := by
  simpa using targetVertex_mem_X S L a

theorem spokePath_connects (a : L.Index) :
    (spokePath S L a).ConnectsPathToSet (mainPath S L a) X := by
  exact Or.inl ⟨spokePath_source_mem_mainPath S L a,
    spokePath_target_mem_X S L a⟩

theorem spokePath_meets_mainPath_exactly (a : L.Index) :
    (mainPath S L a).MeetsExactlyAt (spokePath S L a)
      (spokePath S L a).source := by
  rw [GraphPath.MeetsExactlyAt]
  simpa [spokePath] using
    (looseSpoke S L a).cleanSuffixFromSet_inter_eq_singleton_source
      (mainPath S L a).vertexSet (looseSpoke_meets_mainPath S L a)

/-- The spoke endpoint opposite the attachment point lies outside the
associated main path. -/
theorem spokePath_otherEndpoint_source_not_mem_mainPath (a : L.Index) :
    (spokePath S L a).otherEndpoint (spokePath S L a).source ∉
      (mainPath S L a).vertexSet := by
  intro hmem
  have htarget_mem :
      (spokePath S L a).target ∈ (mainPath S L a).vertexSet := by
    simpa [GraphPath.otherEndpoint] using hmem
  exact Finset.disjoint_left.mp (S.P_path_disjoint_X (sourceIndex S L a))
    (by simpa [mainPath] using htarget_mem)
    (spokePath_target_mem_X S L a)

/-- The main paths selected by a contracted linkage are pairwise disjoint. -/
theorem mainPath_nodeDisjoint {a b : L.Index} (hab : a ≠ b) :
    GraphPath.NodeDisjoint (mainPath S L a) (mainPath S L b) := by
  unfold mainPath
  exact P.toPathPacking.node_disjoint
    (fun hidx => hab (sourceIndex_injective S L hidx))

/-- The loose lifted spokes of distinct contracted linkage paths are
node-disjoint. -/
theorem looseSpoke_nodeDisjoint {a b : L.Index} (hab : a ≠ b) :
    GraphPath.NodeDisjoint (looseSpoke S L a) (looseSpoke S L b) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hva hvb
  have hvaBranch := looseSpoke_vertexSet_subset_branchUnion S L a hva
  have hvbBranch := looseSpoke_vertexSet_subset_branchUnion S L b hvb
  exact Finset.disjoint_left.mp
    (contractedPathBranchUnion.disjoint_of_disjoint
      ((clean S L).node_disjoint hab))
    hvaBranch hvbBranch

/-- The final trimmed spokes of distinct contracted linkage paths are
node-disjoint. -/
theorem spokePath_nodeDisjoint {a b : L.Index} (hab : a ≠ b) :
    GraphPath.NodeDisjoint (spokePath S L a) (spokePath S L b) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hva hvb
  exact Finset.disjoint_left.mp (looseSpoke_nodeDisjoint S L hab)
    (spokePath_vertexSet_subset_looseSpoke S L a hva)
    (spokePath_vertexSet_subset_looseSpoke S L b hvb)

/-- A non-source `P`-path is disjoint from the union of original branches used
by a cleaned contracted linkage path. -/
theorem path_disjoint_clean_branchUnion_of_ne
    (a : L.Index) {p : P.Index} (hp : p ∈ I)
    (hne : p ≠ sourceIndex S L a) :
    Disjoint (P.path p).vertexSet
      (contractedPathBranchUnion ((clean S L).path a).vertexSet) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvBranchUnion
  rcases Finset.mem_biUnion.1 hvBranchUnion with ⟨z, hzPath, hvz⟩
  cases z with
  | inl q =>
      have hzTerminal :
          (Sum.inl q : ContractedPathVertex P I) ∈ S.contractedPathTerminals I := by
        exact ContractedPathVertex.mem_pathTerminalSet_of_mem (P := P) (I := I)
          q.1 q.2
      have hzSource :
          (Sum.inl q : ContractedPathVertex P I) =
            ((clean S L).path a).source :=
        clean_eq_source_of_mem_pathTerminal S L a hzPath hzTerminal
      have hq :
          q.1 = sourceIndex S L a := by
        rw [clean_source_eq S L a] at hzSource
        exact congrArg Subtype.val (Sum.inl.inj hzSource)
      have hdisj :
          Disjoint (P.path p).vertexSet
            (P.path (sourceIndex S L a)).vertexSet :=
        P.toPathPacking.node_disjoint hne
      exact Finset.disjoint_left.mp hdisj hvP (by simpa [contractedPathBranch, hq] using hvz)
  | inr x =>
      have hvx : v = x.1 := by
        simpa [contractedPathBranch] using hvz
      exact x.2 p hp (by simpa [hvx] using hvP)

/-- A trimmed spoke for one contracted linkage path is disjoint from every other
selected main path. -/
theorem mainPath_disjoint_spokePath_of_ne {a b : L.Index} (hab : a ≠ b) :
    GraphPath.NodeDisjoint (mainPath S L a) (spokePath S L b) := by
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvMain hvSpoke
  have hvLoose := spokePath_vertexSet_subset_looseSpoke S L b hvSpoke
  have hvBranch := looseSpoke_vertexSet_subset_branchUnion S L b hvLoose
  have hidx_ne : sourceIndex S L a ≠ sourceIndex S L b := by
    intro hidx
    exact hab (sourceIndex_injective S L hidx)
  exact Finset.disjoint_left.mp
    (path_disjoint_clean_branchUnion_of_ne S L b
      (sourceIndex_mem S L a) hidx_ne)
    (by simpa [mainPath] using hvMain) hvBranch

/-- A large contracted linkage lifts to an original-graph crossbar. -/
noncomputable def toCrossbar (hcard : L.card = g ^ 2) :
    Crossbar G A B X (g ^ 2) where
  Index := L.Index
  indexFintype := L.indexFintype
  indexDecidableEq := L.indexDecidableEq
  card_index := by
    simpa [PathPacking.card] using hcard
  mainPath := mainPath S L
  main_connects := by
    intro a
    exact Or.inl ⟨P.source_mem (sourceIndex S L a),
      P.target_mem (sourceIndex S L a)⟩
  main_nodeDisjoint := by
    intro a b hab
    exact mainPath_nodeDisjoint S L hab
  spokePath := spokePath S L
  spoke_connects := by
    intro a
    exact spokePath_connects S L a
  spoke_nodeDisjoint := by
    intro a b hab
    exact spokePath_nodeDisjoint S L hab
  spoke_meets_own_main := by
    intro a
    exact ⟨(spokePath S L a).source, Or.inl rfl,
      spokePath_meets_mainPath_exactly S L a⟩
  spoke_exits_own_main := by
    intro a
    exact ⟨(spokePath S L a).source, Or.inl rfl,
      spokePath_meets_mainPath_exactly S L a,
      by simpa [GraphPath.otherEndpoint] using spokePath_target_mem_X S L a,
      spokePath_otherEndpoint_source_not_mem_mainPath S L a⟩
  spoke_disjoint_other_main := by
    intro a b hab
    exact mainPath_disjoint_spokePath_of_ne S L hab

end ContractedLinkage

/-- A partially constructed no-linkage run through the first `n` rows.

Rows with index at least `n` are kept empty.  This lets the prefix use the
same `pseudoGridRemainingBefore` expression as the final `SeparatorChoiceRun`;
updating row `n` cannot alter earlier remaining sets because they only depend
on smaller row indices. -/
structure SeparatorChoicePrefix
    (S : Theorem41Setup G A B X g kappa D P Q) (n : ℕ) where
  n_le : n ≤ D
  reserved : Fin D → Finset P.Index
  empty_of_le : ∀ i : Fin D, n ≤ i.val → reserved i = ∅
  J : ∀ i : Fin D,
    Finset (ContractedPathVertex P (pseudoGridRemainingBefore reserved i))
  reserved_eq :
    ∀ (i : Fin D) (_hi : i.val < n),
      reserved i = S.reservedOfSeparator (J i)
  J_card_le :
    ∀ (i : Fin D) (_hi : i.val < n), (J i).card ≤ g ^ 2
  J_blocks :
    ∀ (i : Fin D) (_hi : i.val < n),
      BlocksAllPaths
        (S.contractedGraph (pseudoGridRemainingBefore reserved i))
        (S.contractedPathTerminals (pseudoGridRemainingBefore reserved i))
        (S.contractedXTerminals (pseudoGridRemainingBefore reserved i))
        (J i)

namespace SeparatorChoicePrefix

variable {S : Theorem41Setup G A B X g kappa D P Q} {n : ℕ}

/-- The empty prefix before any separator row has been selected. -/
noncomputable def empty (S : Theorem41Setup G A B X g kappa D P Q) :
    SeparatorChoicePrefix S 0 where
  n_le := Nat.zero_le D
  reserved := fun _ => ∅
  empty_of_le := by
    intro i _hi
    rfl
  J := fun _ => ∅
  reserved_eq := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i.val hi)
  J_card_le := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i.val hi)
  J_blocks := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i.val hi)

/-- Extend a no-linkage prefix by one row, using the Menger separator
alternative at the current remaining set. -/
noncomputable def extend
    (C : SeparatorChoicePrefix S n) (hn : n < D)
    (hNoLinkage : ∀ I : Finset P.Index, ¬ S.ContractedLinkageAt I) :
    SeparatorChoicePrefix S (n + 1) := by
  classical
  let row : Fin D := ⟨n, hn⟩
  let I : Finset P.Index := pseudoGridRemainingBefore C.reserved row
  have hsep :
      ∃ J : Finset (ContractedPathVertex P I),
        J.card ≤ g ^ 2 ∧
          BlocksAllPaths (S.contractedGraph I)
            (S.contractedPathTerminals I) (S.contractedXTerminals I) J := by
    rcases S.stepMenger_exact_or_separator_selfContained I with hlink | hsep
    · exact False.elim (hNoLinkage I hlink)
    · rcases hsep with ⟨J, hJcard, hJblocks⟩
      exact ⟨J, hJcard, hJblocks⟩
  let Jnew : Finset (ContractedPathVertex P I) := Classical.choose hsep
  have hJnew_card : Jnew.card ≤ g ^ 2 := (Classical.choose_spec hsep).1
  have hJnew_blocks :
      BlocksAllPaths (S.contractedGraph I)
        (S.contractedPathTerminals I) (S.contractedXTerminals I) Jnew :=
    (Classical.choose_spec hsep).2
  let Rnew : Fin D → Finset P.Index :=
    Function.update C.reserved row (S.reservedOfSeparator Jnew)
  let Jfield : ∀ i : Fin D,
      Finset (ContractedPathVertex P (pseudoGridRemainingBefore Rnew i)) :=
    fun i =>
      if hrow : i = row then
        by
          subst hrow
          have hrem :
              I = pseudoGridRemainingBefore Rnew row := by
            simpa [Rnew, I] using
              (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_self
                C.reserved row (S.reservedOfSeparator Jnew)).symm
          exact transportContractedSeparator hrem Jnew
      else
        by
          by_cases hi_old : i.val < n
          · have hlt_row : i.val < row.val := by
              simpa [row] using hi_old
            have hrem :
                pseudoGridRemainingBefore C.reserved i =
                  pseudoGridRemainingBefore Rnew i := by
              simpa [Rnew] using
                (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_later
                  C.reserved (i := row) (j := i)
                  (S.reservedOfSeparator Jnew) hlt_row).symm
            exact transportContractedSeparator hrem (C.J i)
          · exact ∅
  refine
    { n_le := Nat.succ_le_of_lt hn
      reserved := Rnew
      empty_of_le := ?_
      J := Jfield
      reserved_eq := ?_
      J_card_le := ?_
      J_blocks := ?_ }
  · intro i hi
    have hrow_ne : i ≠ row := by
      intro h
      subst h
      simp [row] at hi
    have hi_old : n ≤ i.val := by omega
    simpa [Rnew, Function.update, hrow_ne] using C.empty_of_le i hi_old
  · intro i hi
    by_cases hrow : i = row
    · subst hrow
      have hrem :
          I = pseudoGridRemainingBefore Rnew row := by
        simpa [Rnew, I] using
          (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_self
            C.reserved row (S.reservedOfSeparator Jnew)).symm
      dsimp [Jfield]
      simp only [if_true]
      rw [S.reservedOfSeparator_transportContractedSeparator hrem Jnew]
      simp [Rnew]
    · have hi_old : i.val < n := by
        have hle : i.val ≤ n := Nat.le_of_lt_succ hi
        have hne : i.val ≠ n := by
          intro hval
          exact hrow (Fin.ext (by simpa [row] using hval))
        omega
      have hlt_row : i.val < row.val := by
        simpa [row] using hi_old
      have hrem :
          pseudoGridRemainingBefore C.reserved i =
            pseudoGridRemainingBefore Rnew i := by
        simpa [Rnew] using
          (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_later
            C.reserved (i := row) (j := i)
            (S.reservedOfSeparator Jnew) hlt_row).symm
      dsimp [Jfield]
      rw [dif_neg hrow]
      rw [dif_pos hi_old]
      rw [S.reservedOfSeparator_transportContractedSeparator hrem (C.J i)]
      simpa [Rnew, Function.update, hrow] using C.reserved_eq i hi_old
  · intro i hi
    by_cases hrow : i = row
    · subst hrow
      have hrem :
          I = pseudoGridRemainingBefore Rnew row := by
        simpa [Rnew, I] using
          (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_self
            C.reserved row (S.reservedOfSeparator Jnew)).symm
      dsimp [Jfield]
      simp only [if_true]
      simpa [transportContractedSeparator_card hrem Jnew] using hJnew_card
    · have hi_old : i.val < n := by
        have hle : i.val ≤ n := Nat.le_of_lt_succ hi
        have hne : i.val ≠ n := by
          intro hval
          exact hrow (Fin.ext (by simpa [row] using hval))
        omega
      have hlt_row : i.val < row.val := by
        simpa [row] using hi_old
      have hrem :
          pseudoGridRemainingBefore C.reserved i =
            pseudoGridRemainingBefore Rnew i := by
        simpa [Rnew] using
          (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_later
            C.reserved (i := row) (j := i)
            (S.reservedOfSeparator Jnew) hlt_row).symm
      dsimp [Jfield]
      rw [dif_neg hrow]
      rw [dif_pos hi_old]
      simpa [transportContractedSeparator_card hrem (C.J i)] using C.J_card_le i hi_old
  · intro i hi
    by_cases hrow : i = row
    · subst hrow
      have hrem :
          I = pseudoGridRemainingBefore Rnew row := by
        simpa [Rnew, I] using
          (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_self
            C.reserved row (S.reservedOfSeparator Jnew)).symm
      dsimp [Jfield]
      simp only [if_true]
      exact S.blocksAllPaths_transportContractedSeparator hrem hJnew_blocks
    · have hi_old : i.val < n := by
        have hle : i.val ≤ n := Nat.le_of_lt_succ hi
        have hne : i.val ≠ n := by
          intro hval
          exact hrow (Fin.ext (by simpa [row] using hval))
        omega
      have hlt_row : i.val < row.val := by
        simpa [row] using hi_old
      have hrem :
          pseudoGridRemainingBefore C.reserved i =
            pseudoGridRemainingBefore Rnew i := by
        simpa [Rnew] using
          (Lax17Proofs.SimpleGraph.pseudoGridRemainingBefore_update_later
            C.reserved (i := row) (j := i)
            (S.reservedOfSeparator Jnew) hlt_row).symm
      dsimp [Jfield]
      rw [dif_neg hrow]
      rw [dif_pos hi_old]
      exact S.blocksAllPaths_transportContractedSeparator hrem (C.J_blocks i hi_old)

/-- Build a no-linkage prefix of any length `n ≤ D`. -/
noncomputable def build
    (S : Theorem41Setup G A B X g kappa D P Q)
    (hNoLinkage : ∀ I : Finset P.Index, ¬ S.ContractedLinkageAt I) :
    ∀ n : ℕ, n ≤ D → SeparatorChoicePrefix S n
  | 0, _ => empty S
  | n + 1, hnle =>
      let C := build S hNoLinkage n (Nat.le_of_succ_le hnle)
      C.extend (Nat.lt_of_succ_le hnle) hNoLinkage

/-- A full-length prefix is exactly a concrete separator choice run. -/
noncomputable def toSeparatorChoiceRun
    (C : SeparatorChoicePrefix S D) :
    SeparatorChoiceRun S where
  reserved := C.reserved
  J := fun i => C.J i
  reserved_eq := fun i => C.reserved_eq i i.isLt
  J_card_le := fun i => C.J_card_le i i.isLt
  J_blocks := fun i => C.J_blocks i i.isLt

end SeparatorChoicePrefix

/-- The finite `D`-step control flow of Theorem 4.1: either some contracted
Menger instance returns the large linkage, or all rows can be equipped with
bounded separator choices. -/
theorem exists_contractedLinkage_or_separatorChoiceRun
    (S : Theorem41Setup G A B X g kappa D P Q) :
    (∃ I : Finset P.Index, S.ContractedLinkageAt I) ∨
      Nonempty (SeparatorChoiceRun S) := by
  classical
  by_cases hlink : ∃ I : Finset P.Index, S.ContractedLinkageAt I
  · exact Or.inl hlink
  · have hNo : ∀ I : Finset P.Index, ¬ S.ContractedLinkageAt I := by
      intro I hI
      exact hlink ⟨I, hI⟩
    exact Or.inr
      ⟨(SeparatorChoicePrefix.build S hNo D (Nat.le_refl D)).toSeparatorChoiceRun⟩

namespace SeparatorRun

variable {S : Theorem41Setup G A B X g kappa D P Q}

/-- The matched `Q`-path associated with a `P`-path index. -/
noncomputable def matchedQPath
    (_R : SeparatorRun S) (p : P.Index) : GraphPath G :=
  Q.path (P.matchedSourceIndex Q p)

/-- The proof that a final remaining parent path has a matched `Q`-path hitting
the trace in row `i`. -/
def hitTraceOfRemaining
    (R : SeparatorRun S) (i : Fin D) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) :
    ((R.matchedQPath p).vertexSet ∩ R.trace i).Nonempty :=
  R.hit_trace i p (pseudoGridRemaining_subset_remainingBefore R.reserved i hp)

/-- The last trace vertex on the matched `Q`-path of a final remaining parent
at row `i`. -/
noncomputable def lastHitOfRemaining
    (R : SeparatorRun S) (i : Fin D) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) : V :=
  (R.matchedQPath p).lastHitVertex (R.trace i) (R.hitTraceOfRemaining i p hp)

/-- The final suffix `σ_D(Q_P)` selected for a parent path that survives all
rows. -/
noncomputable def finalSuffix
    (R : SeparatorRun S) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) : GraphPath G :=
  (R.matchedQPath p).cleanSuffixFromSet
    (R.trace (S.lastIterationIndex))
    (R.hitTraceOfRemaining (S.lastIterationIndex) p hp)

/-- A final remaining parent is good at row `i` if its last trace vertex in
that row lies on one of the row paths. -/
def rowGood
    (R : SeparatorRun S) (i : Fin D) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) : Prop :=
  ∃ r ∈ R.reserved i,
    R.lastHitOfRemaining i p hp ∈ (P.path r).vertexSet

/-- The selected suffix is a subpath, at the vertex-set level, of the matched
original `Q`-path. -/
theorem finalSuffix_vertexSet_subset
    (R : SeparatorRun S) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) :
    (R.finalSuffix p hp).vertexSet ⊆ (R.matchedQPath p).vertexSet :=
  (R.matchedQPath p).cleanSuffixFromSet_vertexSet_subset
    (R.trace (S.lastIterationIndex))
    (R.hitTraceOfRemaining (S.lastIterationIndex) p hp)

/-- The selected suffix is a subpath, at the edge-set level, of the matched
original `Q`-path. -/
theorem finalSuffix_edgeSet_subset
    (R : SeparatorRun S) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) :
    (R.finalSuffix p hp).edgeSet ⊆ (R.matchedQPath p).edgeSet :=
  (R.matchedQPath p).cleanSuffixFromSet_edgeSet_subset
    (R.trace (S.lastIterationIndex))
    (R.hitTraceOfRemaining (S.lastIterationIndex) p hp)

/-- The selected final suffix has the pseudo-grid endpoint convention with
respect to `X`. -/
theorem finalSuffix_exactlyOneEndpointIn_X
    (R : SeparatorRun S) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) :
    (R.finalSuffix p hp).ExactlyOneEndpointIn X := by
  exact (R.matchedQPath p).cleanSuffixFromSet_exactlyOneEndpointIn_of_target_mem_of_degree_one
    (R.trace (S.lastIterationIndex))
    (R.hitTraceOfRemaining (S.lastIterationIndex) p hp)
    (Q.target_mem (P.matchedSourceIndex Q p)) S.degree_X

theorem lastHitOfRemaining_mem_matchedQPath
    (R : SeparatorRun S) (i : Fin D) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) :
    R.lastHitOfRemaining i p hp ∈ (R.matchedQPath p).vertexSet :=
  (R.matchedQPath p).lastHitVertex_mem_vertexSet
    (R.trace i) (R.hitTraceOfRemaining i p hp)

theorem lastHitOfRemaining_mem_trace
    (R : SeparatorRun S) (i : Fin D) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved) :
    R.lastHitOfRemaining i p hp ∈ R.trace i :=
  (R.matchedQPath p).lastHitVertex_mem_set
    (R.trace i) (R.hitTraceOfRemaining i p hp)

/-- If a final remaining parent is not good at row `i`, its last trace vertex
lies in the original-vertex part of the separator. -/
theorem lastHit_mem_original_of_not_rowGood
    (R : SeparatorRun S) (i : Fin D) (p : P.Index)
    (hp : p ∈ pseudoGridRemaining R.reserved)
    (hbad : ¬ R.rowGood i p hp) :
    R.lastHitOfRemaining i p hp ∈ R.original i := by
  classical
  have htrace := R.lastHitOfRemaining_mem_trace i p hp
  rw [R.trace_eq i] at htrace
  rcases Finset.mem_union.1 htrace with horig | hrow
  · exact horig
  · rcases Finset.mem_biUnion.1 hrow with ⟨r, hr, hv⟩
    exact False.elim (hbad ⟨r, hr, hv⟩)

/-- The parent index type obtained from a selected finite set of surviving
`P`-paths. -/
abbrev ParentIndex (_R : SeparatorRun S) (Parents : Finset P.Index) :=
  {p : P.Index // p ∈ Parents}

/-- The final suffix associated with a selected parent. -/
noncomputable def selectedFinalSuffix
    (R : SeparatorRun S) {Parents : Finset P.Index}
    (hParents : Parents ⊆ pseudoGridRemaining R.reserved)
    (j : R.ParentIndex Parents) : GraphPath G :=
  R.finalSuffix j.1 (hParents j.2)

/-- Selected parents that are not good at row `i`. -/
noncomputable def badSet
    (R : SeparatorRun S) {Parents : Finset P.Index}
    (hParents : Parents ⊆ pseudoGridRemaining R.reserved)
    (i : Fin D) : Finset (R.ParentIndex Parents) :=
  by
    classical
    exact Finset.univ.filter fun j : R.ParentIndex Parents =>
      ¬ R.rowGood i j.1 (hParents j.2)

theorem mem_badSet_iff
    (R : SeparatorRun S) {Parents : Finset P.Index}
    (hParents : Parents ⊆ pseudoGridRemaining R.reserved)
    (i : Fin D) (j : R.ParentIndex Parents) :
    j ∈ R.badSet hParents i ↔ ¬ R.rowGood i j.1 (hParents j.2) := by
  classical
  simp [badSet]

/-- The bad selected parents at row `i` inject into the original-vertex part of
the separator trace, so there are at most `g^2` of them. -/
theorem badSet_card_le
    (R : SeparatorRun S) {Parents : Finset P.Index}
    (hParents : Parents ⊆ pseudoGridRemaining R.reserved)
    (i : Fin D) :
    (R.badSet hParents i).card ≤ g ^ 2 := by
  classical
  let Bad := R.badSet hParents i
  let f : {j : R.ParentIndex Parents // j ∈ Bad} →
      {v : V // v ∈ R.original i} :=
    fun j =>
      ⟨R.lastHitOfRemaining i j.1.1 (hParents j.1.2),
        R.lastHit_mem_original_of_not_rowGood i j.1.1 (hParents j.1.2)
          ((R.mem_badSet_iff hParents i j.1).1 j.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    by_contra hparent_ne
    have hlast :
        R.lastHitOfRemaining i a.1.1 (hParents a.1.2) =
          R.lastHitOfRemaining i b.1.1 (hParents b.1.2) :=
      congrArg Subtype.val hab
    have hQa :
        R.lastHitOfRemaining i a.1.1 (hParents a.1.2) ∈
          (Q.path (P.matchedSourceIndex Q a.1.1)).vertexSet := by
      simpa [matchedQPath] using
        R.lastHitOfRemaining_mem_matchedQPath i a.1.1 (hParents a.1.2)
    have hQb :
        R.lastHitOfRemaining i a.1.1 (hParents a.1.2) ∈
          (Q.path (P.matchedSourceIndex Q b.1.1)).vertexSet := by
      simpa [matchedQPath, hlast] using
        R.lastHitOfRemaining_mem_matchedQPath i b.1.1 (hParents b.1.2)
    have hq_ne :
        P.matchedSourceIndex Q a.1.1 ≠ P.matchedSourceIndex Q b.1.1 := by
      intro hq
      exact hparent_ne ((P.matchedSourceIndex_injective Q) hq)
    exact Finset.disjoint_left.mp (Q.toPathPacking.node_disjoint hq_ne) hQa hQb
  have hcard :
      Fintype.card {j : R.ParentIndex Parents // j ∈ Bad} ≤
        Fintype.card {v : V // v ∈ R.original i} :=
    Fintype.card_le_of_injective f hf
  calc
    Bad.card = Fintype.card {j : R.ParentIndex Parents // j ∈ Bad} := by
      simp [Fintype.card_coe]
    _ ≤ Fintype.card {v : V // v ∈ R.original i} := hcard
    _ = (R.original i).card := by simp [Fintype.card_coe]
    _ ≤ g ^ 2 := R.original_card_le i

/-- A completed separator run supplies the iteration data used by the
pseudo-grid assembly theorem.  This packages the final choice of
`⌊κ/4⌋` surviving parent paths, the final suffixes `σ_D(Q_P)`, and the
two bad sets used in the paper's `g^2 + g^2` counting argument. -/
theorem exists_iterationData
    (R : SeparatorRun S) :
    Nonempty (PseudoGridIterationData G A B X g D P Q) := by
  classical
  rcases S.exists_parentSet_card_eq_quarter R.reserved R.reserved_card_le with
    ⟨Parents, hParents, hParentsCard⟩
  let QIndex := R.ParentIndex Parents
  refine ⟨{
    depth_pos := S.D_pos_strict
    reserved := R.reserved
    reserved_card_le := R.reserved_card_le
    reserved_disjoint :=
      pseudoGridReserved_disjoint_of_subset_remainingBefore
        R.reserved R.reserved_subset_remainingBefore
    QIndex := QIndex
    q_card := ?q_card
    parent := fun j : QIndex => j.1
    parent_remaining := ?parent_remaining
    parent_injective := ?parent_injective
    qPath := fun j : QIndex => R.selectedFinalSuffix hParents j
    qPath_subset_matched := ?qPath_subset
    qPath_edgeSet_subset_matched := ?qPath_edge_subset
    qPath_exactly_one_endpoint_in_X := ?qPath_endpoint
    qPath_nodeDisjoint := ?qPath_disjoint
    remaining_disjoint_qPath := ?remaining_disjoint
    bad := fun i : Fin D => R.badSet hParents i
    bad_card_le := ?bad_card
    terminalBad := R.badSet hParents S.lastIterationIndex
    terminalBad_card_le := R.badSet_card_le hParents S.lastIterationIndex
    good_intersects_reserved := ?good_intersects
  }⟩
  · calc
      Fintype.card QIndex = Parents.card := by
        simp [QIndex, ParentIndex, Fintype.card_coe]
      _ = P.card / 4 := hParentsCard
  · intro j
    exact hParents j.2
  · intro i j hij
    exact Subtype.ext hij
  · intro j v hv
    exact R.finalSuffix_vertexSet_subset j.1 (hParents j.2) hv
  · intro j e he
    exact R.finalSuffix_edgeSet_subset j.1 (hParents j.2) he
  · intro j
    exact R.finalSuffix_exactlyOneEndpointIn_X j.1 (hParents j.2)
  · intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvi hvj
    have hviQ :
        v ∈ (Q.path (P.matchedSourceIndex Q i.1)).vertexSet :=
      R.finalSuffix_vertexSet_subset i.1 (hParents i.2) hvi
    have hvjQ :
        v ∈ (Q.path (P.matchedSourceIndex Q j.1)).vertexSet :=
      R.finalSuffix_vertexSet_subset j.1 (hParents j.2) hvj
    have hparent_ne : i.1 ≠ j.1 := by
      intro h
      exact hij (Subtype.ext h)
    have hq_ne :
        P.matchedSourceIndex Q i.1 ≠ P.matchedSourceIndex Q j.1 := by
      intro hq
      exact hparent_ne ((P.matchedSourceIndex_injective Q) hq)
    exact Finset.disjoint_left.mp (Q.toPathPacking.node_disjoint hq_ne) hviQ hvjQ
  · intro p hp j
    exact R.suffix_disjoint_remaining j.1 p (hParents j.2) hp
  · intro i
    exact R.badSet_card_le hParents i
  · intro i j hj_bad hj_terminal
    have hgood_i : R.rowGood i j.1 (hParents j.2) := by
      by_contra hnot
      exact hj_bad ((R.mem_badSet_iff hParents i j).2 hnot)
    have hgood_last :
        R.rowGood S.lastIterationIndex j.1 (hParents j.2) := by
      by_contra hnot
      exact hj_terminal
        ((R.mem_badSet_iff hParents S.lastIterationIndex j).2 hnot)
    rcases R.good_final_intersects i j.1 (hParents j.2) hgood_i hgood_last with
      ⟨r, hr, hhit⟩
    exact ⟨r, hr, by simpa [selectedFinalSuffix, finalSuffix] using hhit⟩

theorem theorem_four_one_of_separatorRun
    (R : SeparatorRun S) :
    Theorem41Conclusion G A B X g D P Q :=
  theorem_four_one_of_setup_and_iterationData S (Or.inr R.exists_iterationData)

end SeparatorRun

namespace SeparatorChoiceRun

variable {S : Theorem41Setup G A B X g kappa D P Q}

theorem theorem_four_one_of_separatorChoiceRun
    (C : SeparatorChoiceRun S) :
    Theorem41Conclusion G A B X g D P Q :=
  C.toSeparatorRun.theorem_four_one_of_separatorRun

end SeparatorChoiceRun

/-- The final Section 4.1 wrapper once the iteration has been run: either a
crossbar was produced in a linkage step, or the no-linkage branch produced
concrete separator choices for all rows. -/
theorem theorem_four_one_of_crossbar_or_separatorChoiceRun
    (S : Theorem41Setup G A B X g kappa D P Q)
    (h :
      Nonempty (Crossbar G A B X (g ^ 2)) ∨
        Nonempty (SeparatorChoiceRun S)) :
    Theorem41Conclusion G A B X g D P Q := by
  rcases h with hcross | hsep
  · exact Or.inl hcross
  · rcases hsep with ⟨C⟩
    exact C.theorem_four_one_of_separatorChoiceRun

/-- The unconditional Section 4.1 conclusion follows once every successful
contracted-linkage step has been lifted back to an original-graph crossbar. -/
theorem theorem_four_one_of_contractedLinkage_lift
    (S : Theorem41Setup G A B X g kappa D P Q)
    (hlift :
      ∀ I : Finset P.Index,
        S.ContractedLinkageAt I →
          Nonempty (Crossbar G A B X (g ^ 2))) :
    Theorem41Conclusion G A B X g D P Q := by
  rcases S.exists_contractedLinkage_or_separatorChoiceRun with hlink | hsep
  · rcases hlink with ⟨I, hI⟩
    exact Or.inl (hlift I hI)
  · exact S.theorem_four_one_of_crossbar_or_separatorChoiceRun (Or.inr hsep)

/-- The successful contracted-linkage outcome in one iteration lifts to an
actual original-graph crossbar. -/
theorem crossbar_of_contractedLinkageAt
    (S : Theorem41Setup G A B X g kappa D P Q)
    {I : Finset P.Index} (h : S.ContractedLinkageAt I) :
    Nonempty (Crossbar G A B X (g ^ 2)) := by
  rcases h with ⟨L, hcard⟩
  exact ⟨ContractedLinkage.toCrossbar S L hcard⟩

/-- Chuzhoy--Tan Theorem 4.1 in the pseudo-grid/crossbar form used by the
formal development.  Under the paper hypotheses, either there is an
`(A,B,X)`-crossbar of width `g^2`, or there is a depth-`D` pseudo-grid relative
to the chosen minimum pair of perfect path packings. -/
theorem theorem_four_one
    (S : Theorem41Setup G A B X g kappa D P Q) :
    Theorem41Conclusion G A B X g D P Q :=
  S.theorem_four_one_of_contractedLinkage_lift
    (fun _I hI => S.crossbar_of_contractedLinkageAt hI)

end Theorem41Setup

/-- Chuzhoy--Tan Theorem 4.1 with the hypotheses exposed in the same shape as
the paper statement.

The paper assumes that the pair of path families minimizes the total number of
edges in their union.  The Section 4.1 pseudo-grid/crossbar dichotomy proved
above is slightly stronger and does not use this minimality hypothesis; it is
kept here because later Section 4 arguments need the same selected pair. -/
theorem theorem_four_one_explicit
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {A B X : Finset V} {g kappa D : ℕ}
    (P : PerfectPathPacking H A B) (Q : PerfectPathPacking H A X)
    (hg : 2 ≤ g)
    (hg_power : CrossbarContract.IsPowerOfTwo g)
    (hA : A.card = kappa) (hB : B.card = kappa) (hX : X.card = kappa)
    (hAB : Disjoint A B) (hAX : Disjoint A X) (hBX : Disjoint B X)
    (hdegreeX : ∀ x ∈ X, DegreeEquals H x 1)
    (hPcard : P.card = kappa) (hQcard : Q.card = kappa)
    (hminimum : P.IsMinimumTheorem41Pair Q)
    (hDpos : 1 ≤ D) (hDle : D ≤ kappa / (2 * g ^ 2)) :
    Theorem41Conclusion H A B X g D P Q := by
  let S : Theorem41Setup H A B X g kappa D P Q :=
    { two_le_g := hg
      g_power_two := hg_power
      A_card := hA
      B_card := hB
      X_card := hX
      disjoint_A_B := hAB
      disjoint_A_X := hAX
      disjoint_B_X := hBX
      degree_X := hdegreeX
      P_card := hPcard
      Q_card := hQcard
      minimal_pair := hminimum
      D_pos := hDpos
      D_le := hDle }
  exact S.theorem_four_one

/-- Chuzhoy--Tan Theorem 4.1 from two concrete node-disjoint path families,
without asking the caller to provide a preselected minimum pair.

The theorem promotes the two equal-cardinality path packings to perfect
oriented packings, chooses a pair minimizing the edge-union count, and then
applies the self-contained Section 4.1 proof above to that chosen pair. -/
theorem theorem_four_one_of_pathPackings
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {A B X : Finset V} {g kappa D : ℕ}
    (hg : 2 ≤ g)
    (hg_power : CrossbarContract.IsPowerOfTwo g)
    (hA : A.card = kappa) (hB : B.card = kappa) (hX : X.card = kappa)
    (hAB : Disjoint A B) (hAX : Disjoint A X) (hBX : Disjoint B X)
    (hdegreeX : ∀ x ∈ X, DegreeEquals H x 1)
    (Pab : PathPacking H A B) (hPab : Pab.card = kappa)
    (Pax : PathPacking H A X) (hPax : Pax.card = kappa)
    (hDpos : 1 ≤ D) (hDle : D ≤ kappa / (2 * g ^ 2)) :
    ∃ (P : PerfectPathPacking H A B) (Q : PerfectPathPacking H A X),
      P.card = kappa ∧
        Q.card = kappa ∧
          P.IsMinimumTheorem41Pair Q ∧
            Theorem41Conclusion H A B X g D P Q := by
  classical
  let P₀ : PerfectPathPacking H A B :=
    Pab.toPerfectOfCardEq (hPab.trans hA.symm) (hPab.trans hB.symm)
  let Q₀ : PerfectPathPacking H A X :=
    Pax.toPerfectOfCardEq (hPax.trans hA.symm) (hPax.trans hX.symm)
  rcases PerfectPathPacking.exists_minimumTheorem41Pair P₀ Q₀ with
    ⟨P, Q, hminimum⟩
  have hPcard : P.card = kappa := P.card_eq_left_card.trans hA
  have hQcard : Q.card = kappa := Q.card_eq_left_card.trans hA
  refine ⟨P, Q, hPcard, hQcard, hminimum, ?_⟩
  exact theorem_four_one_explicit H P Q hg hg_power hA hB hX
    hAB hAX hBX hdegreeX hPcard hQcard hminimum hDpos hDle

/-- Chuzhoy--Tan Theorem 4.1 in a self-contained existence form.

This is the closest formal statement to the paper's phrasing: given the graph,
the three terminal sets, degree-one terminals in `X`, and the existence of the
two required node-disjoint path families, the theorem chooses a minimum pair
of such families and returns either a crossbar or a pseudo-grid with respect
to that chosen pair. -/
theorem theorem_four_one_selfContained
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {A B X : Finset V} {g kappa D : ℕ}
    (hg : 2 ≤ g)
    (hg_power : CrossbarContract.IsPowerOfTwo g)
    (hA : A.card = kappa) (hB : B.card = kappa) (hX : X.card = kappa)
    (hAB : Disjoint A B) (hAX : Disjoint A X) (hBX : Disjoint B X)
    (hdegreeX : ∀ x ∈ X, DegreeEquals H x 1)
    (hPab : ∃ Pab : PathPacking H A B, Pab.card = kappa)
    (hPax : ∃ Pax : PathPacking H A X, Pax.card = kappa)
    (hDpos : 1 ≤ D) (hDle : D ≤ kappa / (2 * g ^ 2)) :
    ∃ (P : PerfectPathPacking H A B) (Q : PerfectPathPacking H A X),
      P.card = kappa ∧
        Q.card = kappa ∧
          P.IsMinimumTheorem41Pair Q ∧
            Theorem41Conclusion H A B X g D P Q := by
  rcases hPab with ⟨Pab, hPab_card⟩
  rcases hPax with ⟨Pax, hPax_card⟩
  exact theorem_four_one_of_pathPackings H hg hg_power hA hB hX
    hAB hAX hBX hdegreeX Pab hPab_card Pax hPax_card hDpos hDle

end SimpleGraph

end Lax17Proofs
