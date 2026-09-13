import Lax17Proofs.Source.ChekuriChuzhoyTheorem35
import Lax17Proofs.Source.Flow
import Lax17Proofs.Source.Theorem214Contract
import Lax17Proofs.Source.TreewidthSparsifierContract
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Theorem 2.21, final boosting step

Appendix A.4 of Chekuri--Chuzhoy proves Theorem 2.21 by first building a
low-degree subgraph in which a large terminal set is cut-well-linked, then
applying Theorem 2.14 to extract a node-well-linked subset.

This file formalizes that last step.  The lower-level construction is exposed
as `CutWellLinkedCoreFromTreewidth`; the theorem below proves, without adding
an axiom, that it implies the `NodeWellLinkedCoreFromTreewidth` interface used
in the proof of Theorem 3.5.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open scoped Classical

/-- A terminal set with the routing property supplied by Chekuri--Chuzhoy
Lemma 2.17.

For every equal bipartition of `X`, there is a unit path flow from one side to
the other whose vertex congestion is at most `eta`.  The proof-facing
certificate also records an integral perfect path packing.  The direct WP1A
producer supplies this stronger field from node-well-linkedness; recording it
explicitly prevents an invalid bounded-degree argument from the support of a
fractional flow. -/
def RoutableSetIn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (X : Finset V) (eta : ℕ) : Prop :=
  0 < eta ∧
    ∀ Y Z : Finset V,
      Y ⊆ X →
        Z ⊆ X →
          Disjoint Y Z →
            Y ∪ Z = X →
              Y.card = Z.card →
                (∃ F : OrientedPathFlow G Y Z,
                  F.IsUnitFlow ∧
                    F.VertexCongestionAtMost (eta : ℚ)) ∧
                  Nonempty (PerfectPathPacking G Y Z)

namespace RoutableSetIn

variable {V : Type u} [DecidableEq V]
variable {G G' : _root_.SimpleGraph V} {X : Finset V} {eta : ℕ}

/-- Routability is preserved when edges are added to the ambient graph. -/
theorem mono_graph (h : RoutableSetIn G X eta) (hGG' : G ≤ G') :
    RoutableSetIn G' X eta := by
  refine ⟨h.1, ?_⟩
  intro Y Z hY hZ hdisj hcover hcard
  rcases h.2 Y Z hY hZ hdisj hcover hcard with
    ⟨⟨F, hunit, hcongestion⟩, ⟨P⟩⟩
  exact ⟨⟨F.mapLe hGG',
    F.mapLe_isUnitFlow hGG' hunit,
    F.mapLe_vertexCongestionAtMost hGG' hcongestion⟩,
    ⟨P.mapLe hGG'⟩⟩

end RoutableSetIn

namespace NodeWellLinkedIn

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {C X : Finset V} {eta : ℕ}

/-- A node-well-linked terminal set supplies the balanced-partition routing
property of Lemma 2.17 with any positive natural congestion bound. -/
theorem toRoutableSetIn (h : NodeWellLinkedIn G C X) (heta : 0 < eta) :
    RoutableSetIn G X eta := by
  refine ⟨heta, ?_⟩
  intro Y Z hY hZ hdisj hcover hcard
  rcases h.2 hY hZ hdisj with ⟨P, hPcard, _hstay⟩
  have hPcardY : P.card = Y.card := by
    simpa [hcard] using hPcard
  have hPcardZ : P.card = Z.card := hPcardY.trans hcard
  let F := OrientedPathFlow.ofPathPacking P
  have hflow :=
    OrientedPathFlow.ofPathPacking_isUnitFlow_and_vertexCongestionAtMost_one
      P hPcardY hPcardZ
  refine ⟨⟨F, hflow.1, ?_⟩, ⟨P.toPerfectOfCardEq hPcardY hPcardZ⟩⟩
  intro v
  have heta_one_nat : 1 ≤ eta := Nat.succ_le_of_lt heta
  have heta_one : (1 : ℚ) ≤ (eta : ℚ) := by exact_mod_cast heta_one_nat
  exact (hflow.2 v).trans heta_one

/-- The paper's equal-cardinality formulation of node-well-linkedness implies
the repository's maximum-packing formulation.

When the requested terminal sets have different cardinalities, trim the larger
one before applying the paper predicate and then widen the resulting packing's
terminal set again. -/
theorem of_paperNodeWellLinkedIn
    {T : Finset V}
    (h : TreewidthSparsifier.PaperNodeWellLinkedIn G C T) :
    NodeWellLinkedIn G C T := by
  classical
  refine ⟨h.1, ?_⟩
  intro A B hA hB _hdisj
  by_cases hle : A.card ≤ B.card
  · rcases Finset.exists_subset_card_eq hle with ⟨B₀, hB₀sub, hB₀card⟩
    rcases h.2 hA (subset_trans hB₀sub hB) (by simp [hB₀card]) with
      ⟨P, hPstay⟩
    refine ⟨P.toPathPacking.widenTerminals subset_rfl hB₀sub, ?_, ?_⟩
    · calc
        (P.toPathPacking.widenTerminals subset_rfl hB₀sub).card =
            P.toPathPacking.card := rfl
        _ = P.card := P.toPathPacking_card
        _ = A.card := P.card_eq_left_card
        _ = min A.card B.card := (Nat.min_eq_left hle).symm
    · intro i
      simpa [PathPacking.widenTerminals] using hPstay i
  · have hB_le_A : B.card ≤ A.card := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rcases Finset.exists_subset_card_eq hB_le_A with ⟨A₀, hA₀sub, hA₀card⟩
    rcases h.2 (subset_trans hA₀sub hA) hB (by simp [hA₀card]) with
      ⟨P, hPstay⟩
    refine ⟨P.toPathPacking.widenTerminals hA₀sub subset_rfl, ?_, ?_⟩
    · calc
        (P.toPathPacking.widenTerminals hA₀sub subset_rfl).card =
            P.toPathPacking.card := rfl
        _ = P.card := P.toPathPacking_card
        _ = B.card := P.card_eq_right_card
        _ = min A.card B.card := (Nat.min_eq_right hB_le_A).symm
    · intro i
      simpa [PathPacking.widenTerminals] using hPstay i

end NodeWellLinkedIn

/-- Chekuri--Chuzhoy Lemma 2.17, in the threshold form needed by Appendix A.4.

The statement says that a graph of treewidth at least `k` contains a requested
number `κ` of terminals satisfying the routability property, provided `κ` is
below `k / polylog(k)`.  The congestion loss is encoded by
`cRoute * log(k)^cRouteLog`. -/
def RoutableSetFromTreewidth
    (cSet cSetLog cRoute cRouteLog : ℕ) : Prop :=
  0 < cSet ∧ 0 < cSetLog ∧ 0 < cRoute ∧ 0 < cRouteLog ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {k κ : ℕ},
        1 < k →
          0 < κ →
            k ≤ treewidth G →
              cSet * κ * (Nat.log 2 k) ^ cSetLog < k →
                ∃ X : Finset V,
                  X.card = κ ∧
                    RoutableSetIn G X
                      (cRoute * (Nat.log 2 k) ^ cRouteLog)

/-- The Reed/Lemma 3.2 node-well-linked-set producer supplies the routable-set
input used by the R-card composition.

The producer is an explicit theorem argument with the same content as the
upper-bound direction of Lemma 3.2.  The proof itself does not invoke that
project axiom: it trims the produced set to the requested cardinality and uses
`NodeWellLinkedIn.toRoutableSetIn` with congestion `log₂(k)`. -/
theorem exists_routableSetFromTreewidth_of_large_paperNodeWellLinked
    (hproducer :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V),
          ∃ T : Finset V,
            TreewidthSparsifier.PaperNodeWellLinked G T ∧
              treewidth G ≤ 4 * T.card) :
    ∃ cSet cSetLog cRoute cRouteLog : ℕ,
      RoutableSetFromTreewidth.{u} cSet cSetLog cRoute cRouteLog := by
  refine ⟨4, 1, 1, 1, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro V _ _ G k κ hk _hκ htw hlarge
  let L := Nat.log 2 k
  have hLpos : 0 < L := by
    simpa [L] using
      Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
  rcases hproducer G with ⟨T, hTpaper, htwT⟩
  have hfourκL_lt : 4 * κ * L < 4 * T.card := by
    calc
      4 * κ * L < k := by simpa [L] using hlarge
      _ ≤ treewidth G := htw
      _ ≤ 4 * T.card := htwT
  have hfourκ_le : 4 * κ ≤ 4 * κ * L := by
    calc
      4 * κ = (4 * κ) * 1 := by simp
      _ ≤ (4 * κ) * L := Nat.mul_le_mul_left (4 * κ) hLone
      _ = 4 * κ * L := rfl
  have hκT : κ ≤ T.card := by
    have : 4 * κ < 4 * T.card := hfourκ_le.trans_lt hfourκL_lt
    omega
  rcases Finset.exists_subset_card_eq hκT with ⟨X, hXT, hXcard⟩
  refine ⟨X, hXcard, ?_⟩
  have hTnode : NodeWellLinkedIn G Finset.univ T :=
    NodeWellLinkedIn.of_paperNodeWellLinkedIn hTpaper
  have hXnode : NodeWellLinkedIn G Finset.univ X :=
    NodeWellLinkedIn.mono_terminals hTnode hXT
  simpa [L] using NodeWellLinkedIn.toRoutableSetIn hXnode hLpos

/-- The cut-matching/AARV part of Appendix A.4 after a Lemma 2.17 routable set
has been found.

From an even routable terminal set `X`, this produces a same-vertex subgraph in
which a terminal set of the same size is cut-well-linked.  Both the maximum
degree and the reciprocal well-linkedness scale linearly with the routing
congestion `eta`, as in Appendix A.4; the remaining losses are measured against
the original treewidth scale `k`.  The premise `kappa <= k` justifies replacing
the source's `log(kappa)` round bound by `log(k)`. -/
def CutWellLinkedCoreFromRoutableSet
    (cDeg cDegLog cAlpha cAlphaLog : ℕ) : Prop :=
  0 < cDeg ∧ 0 < cDegLog ∧ 0 < cAlpha ∧ 0 < cAlphaLog ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {k κ eta : ℕ} (X : Finset V),
        1 < k →
          0 < κ →
            Even κ →
              κ ≤ k →
                X.card = κ →
                  RoutableSetIn G X eta →
                  let L := Nat.log 2 k
                  let Δ := 3 * cDeg * eta * L ^ cDegLog
                  let alphaDen := cAlpha * eta * L ^ cAlphaLog
                  ∃ H : _root_.SimpleGraph V,
                    H ≤ G ∧
                      MaxDegreeAtMost H Δ ∧
                        ∃ C Y : Finset V,
                          IsCluster H C ∧
                            Y.card = κ ∧
                              Section46.ScaledEdgeWellLinkedIn H C Y 1 alphaDen

/-- Cut-well-linked low-degree core produced before the final Theorem 2.14
boost in the proof of Chekuri--Chuzhoy Theorem 2.21.

For a requested final node-well-linked size `x`, the lower-level construction
returns a larger cut-well-linked set of size
`10 * Δ * αDen * x`, where
`Δ = 3 * cDeg * log(k)^cDegLog` bounds the maximum degree and
`αDen = cAlpha * log(k)^cAlphaLog` encodes a `1 / αDen` cut-well-linkedness
loss.  The constant `10` matches the denominator in Theorem 2.14.
-/
def CutWellLinkedCoreFromTreewidth
    (cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ) : Prop :=
  0 < cCut ∧ 0 < cCutLog ∧ 0 < cDeg ∧ 0 < cDegLog ∧
    0 < cAlpha ∧ 0 < cAlphaLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {k x : ℕ},
          1 < k →
            0 < x →
              k ≤ treewidth G →
                let L := Nat.log 2 k
                let Δ := 3 * cDeg * L ^ cDegLog
                let alphaDen := cAlpha * L ^ cAlphaLog
                let κ := 10 * Δ * alphaDen * x
                cCut * κ * L ^ cCutLog < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H Δ ∧
                          ∃ C X : Finset V,
                            IsCluster H C ∧
                              X.card = κ ∧
                                Section46.ScaledEdgeWellLinkedIn H C X 1 alphaDen

/-- The explicit source inputs for Chekuri--Chuzhoy Theorem 3.5/A.2 along the
Appendix A.4 route used in this repository.

This is not a proof by itself.  It is the semantic closure boundary for the
current proof-facing A.2 route: Lemma 2.17 supplies a routable set, the
cut-matching/AARV construction turns that into a cut-well-linked low-degree
core, and Section 4 turns a node-well-linked core into a strong path-of-sets
system. -/
def TheoremA2SourceInputs : Prop :=
  (∃ cSet cSetLog cRoute cRouteLog : ℕ,
    RoutableSetFromTreewidth.{u}
      cSet cSetLog cRoute cRouteLog) ∧
  (∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
    CutWellLinkedCoreFromRoutableSet.{u}
      cDeg cDegLog cAlpha cAlphaLog) ∧
  (∃ cRoute cRouteLog cDeltaPow : ℕ,
    StrongPathOfSetsFromNodeWellLinkedCore.{u}
      cRoute cRouteLog cDeltaPow)

/-- More explicit source inputs for Chekuri--Chuzhoy Theorem 3.5/A.2.

This expands the last conjunct of `TheoremA2SourceInputs` into the Section 4
strong-tree construction and the only branch of Theorem 4.6 that is not already
proved by the finite-tree dichotomy and buffered-path conversion in
`ChekuriChuzhoyTheorem35.lean`. -/
def TheoremA2LeafSourceInputs : Prop :=
  (∃ cSet cSetLog cRoute cRouteLog : ℕ,
    RoutableSetFromTreewidth.{u}
      cSet cSetLog cRoute cRouteLog) ∧
  (∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
    CutWellLinkedCoreFromRoutableSet.{u}
      cDeg cDegLog cAlpha cAlphaLog) ∧
  (∃ cBuild cBuildLog cDeltaPow : ℕ,
    StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
      cBuild cBuildLog cDeltaPow) ∧
  StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}

/-- The leaf-source A.2 boundary implies the older direct source-input bundle.

The finite-tree dichotomy part of Theorem 4.6 is discharged by
`strongPathOfSetsFromStrongTreeOfSets_of_leafExtraction`, so this theorem does
not hide that branch behind an external assumption. -/
theorem theoremA2SourceInputs_of_leafSourceInputs
    (hinputs : TheoremA2LeafSourceInputs.{u}) :
    TheoremA2SourceInputs.{u} := by
  rcases hinputs with ⟨hroutable, hcutMatching, hbuild, hleaf⟩
  refine ⟨hroutable, hcutMatching, ?_⟩
  exact strongPathOfSetsFromNodeWellLinkedCore_of_strongTreeCore_and_extraction
    hbuild
    (strongPathOfSetsFromStrongTreeOfSets_of_leafExtraction hleaf)

/-- The Lemma 2.17 routable-set source and the cut-matching/AARV embedding
source imply the cut-well-linked low-degree core used before Theorem 2.14.

This is the formal composition of the first half of Appendix A.4's proof of
Theorem 2.21.  The final boost from this core to a node-well-linked set is
proved below by `nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore`. -/
theorem cutWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog) :
    ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
      CutWellLinkedCoreFromTreewidth.{u}
        cCut cCutLog cDeg cDegLog cAlpha cAlphaLog := by
  rcases hroutable with
    ⟨cSet, cSetLog, cRoute, cRouteLog,
      hcSet, hcSetLog, _hcRoute, _hcRouteLog, hroutable'⟩
  rcases hcutMatching with
    ⟨cDeg, cDegLog, cAlpha, cAlphaLog,
      hcDeg, hcDegLog, hcAlpha, hcAlphaLog, hcutMatching'⟩
  let cDegOut := cDeg * cRoute
  let cDegLogOut := cDegLog + cRouteLog
  let cAlphaOut := cAlpha * cRoute
  let cAlphaLogOut := cAlphaLog + cRouteLog
  refine ⟨cSet, cSetLog, cDegOut, cDegLogOut, cAlphaOut, cAlphaLogOut,
    hcSet, hcSetLog, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [cDegOut]
    positivity
  · dsimp [cDegLogOut]
    positivity
  · dsimp [cAlphaOut]
    positivity
  · dsimp [cAlphaLogOut]
    positivity
  intro V _ _ G k x hk hx htw
  dsimp
  let L := Nat.log 2 k
  let eta := cRoute * L ^ cRouteLog
  let Δ := 3 * cDegOut * L ^ cDegLogOut
  let alphaDen := cAlphaOut * L ^ cAlphaLogOut
  let κ := 10 * Δ * alphaDen * x
  intro hlarge
  have hlog_pos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hκ_pos : 0 < κ := by
    dsimp [κ, Δ, alphaDen]
    positivity
  rcases hroutable' G hk hκ_pos htw (by
      simpa [L, Δ, alphaDen, κ] using hlarge) with
    ⟨X, hXcard, hXroute⟩
  have hκ_even : Even κ := by
    refine ⟨5 * Δ * alphaDen * x, ?_⟩
    dsimp [κ]
    ring
  have hκ_le_k : κ ≤ k := by
    have hcSet_one : 1 ≤ cSet := Nat.succ_le_of_lt hcSet
    have hlog_one : 1 ≤ L := Nat.succ_le_of_lt hlog_pos
    have hfactor : κ ≤ cSet * κ * L ^ cSetLog := by
      calc
        κ = 1 * κ * 1 := by simp
        _ ≤ cSet * κ * L ^ cSetLog :=
          Nat.mul_le_mul
            (Nat.mul_le_mul hcSet_one (le_refl κ))
            (Nat.one_le_pow cSetLog L hlog_one)
    exact (hfactor.trans_lt (by
      simpa [L, Δ, alphaDen, κ] using hlarge)).le
  rcases hcutMatching' G X hk hκ_pos hκ_even hκ_le_k hXcard hXroute with
    ⟨H, hHG, hdegree, C, Y, hcluster, hYcard, hwell⟩
  refine ⟨H, hHG, ?_, C, Y, hcluster, hYcard, ?_⟩
  · have hDelta :
        3 * cDeg * eta * L ^ cDegLog = Δ := by
      dsimp [eta, Δ, cDegOut, cDegLogOut]
      rw [Nat.pow_add]
      ring
    simpa [L, eta, hDelta] using hdegree
  · have hAlphaDen :
        cAlpha * eta * L ^ cAlphaLog = alphaDen := by
      dsimp [eta, alphaDen, cAlphaOut, cAlphaLogOut]
      rw [Nat.pow_add]
      ring
    simpa [L, eta, hAlphaDen] using hwell

namespace NodeWellLinkedIn

variable {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
variable {C T : Finset V}

/-- A node-well-linked set in any finite region is also node-well-linked in
the whole same-vertex graph. -/
theorem to_univ (h : NodeWellLinkedIn G C T) :
    NodeWellLinkedIn G Finset.univ T := by
  refine ⟨?_, ?_⟩
  · intro v _hv
    simp
  · intro A B hA hB hdisj
    rcases h.2 hA hB hdisj with ⟨P, hcard, _hstay⟩
    refine ⟨P, hcard, ?_⟩
    intro i v _hv
    simp

end NodeWellLinkedIn

/-- The final boosting step in the proof of Chekuri--Chuzhoy Theorem 2.21.

Given the low-degree cut-well-linked core supplied by the cut-matching/AARV
part of Appendix A.4, Theorem 2.14 yields the node-well-linked core used by
Chekuri--Chuzhoy Theorem 3.5.  All logarithmic and maximum-degree losses are
absorbed into the output constants.
-/
theorem nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog) :
    ∃ cCore cCoreLog cDegOut cDegLogOut : ℕ,
      NodeWellLinkedCoreFromTreewidth.{u}
        cCore cCoreLog cDegOut cDegLogOut := by
  rcases hcut with
    ⟨cCut, cCutLog, cDeg, cDegLog, cAlpha, cAlphaLog,
      hcCut, hcCutLog, hcDeg, hcDegLog, hcAlpha, _hcAlphaLog, hcut'⟩
  let cCore := cCut * 10 * (3 * cDeg) * cAlpha
  let cCoreLog := cDegLog + cAlphaLog + cCutLog
  let cDegOut := 3 * cDeg
  let cDegLogOut := cDegLog
  refine ⟨cCore, cCoreLog, cDegOut, cDegLogOut, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [cCore]
    positivity
  · dsimp [cCoreLog]
    positivity
  · dsimp [cDegOut]
    positivity
  · dsimp [cDegLogOut]
    exact hcDegLog
  intro V _ _ G k x hk hx htw hlarge
  let L := Nat.log 2 k
  let Δ := 3 * cDeg * L ^ cDegLog
  let alphaDen := cAlpha * L ^ cAlphaLog
  let κ := 10 * Δ * alphaDen * x
  have hlog_pos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
  have hDelta_pos : 0 < Δ := by
    dsimp [Δ]
    positivity
  have hDelta_three : 3 ≤ Δ := by
    have hfactor_pos : 0 < cDeg * L ^ cDegLog := by
      positivity
    have hfactor_one : 1 ≤ cDeg * L ^ cDegLog :=
      Nat.succ_le_of_lt hfactor_pos
    calc
      3 = 3 * 1 := by omega
      _ ≤ 3 * (cDeg * L ^ cDegLog) :=
        Nat.mul_le_mul_left 3 hfactor_one
      _ = Δ := by
        dsimp [Δ]
        ring
  have halphaDen_pos : 0 < alphaDen := by
    dsimp [alphaDen]
    positivity
  have halphaDen_one : 1 ≤ alphaDen :=
    Nat.succ_le_of_lt halphaDen_pos
  have hcut_large : cCut * κ * L ^ cCutLog < k := by
    have heq :
        cCut * κ * L ^ cCutLog =
          cCore * x * L ^ cCoreLog := by
      dsimp [κ, Δ, alphaDen, cCore, cCoreLog]
      rw [Nat.pow_add, Nat.pow_add]
      ring
    simpa [heq, L] using hlarge
  rcases hcut' G hk hx htw (by
      simpa [L, Δ, alphaDen, κ] using hcut_large) with
    ⟨H, hHG, hdegree, C, X, hcluster, hXcard, hwell⟩
  rcases
      theorem214_nodeWellLinkedSubset_contract
        (G := H) (C := C) (T := X) (alphaNum := 1)
        (alphaDen := alphaDen) (Δ := Δ) (κ := κ)
        hcluster hdegree hDelta_three
        (by decide : 0 < 1) halphaDen_one hXcard hwell with
    ⟨X', hX'sub, hX'card, hX'node⟩
  have hden_pos : 0 < 10 * Δ * alphaDen := by
    positivity
  have hx_le_boost :
      x ≤ (3 * 1 * κ) / (10 * Δ * alphaDen) := by
    rw [Nat.le_div_iff_mul_le hden_pos]
    calc
      x * (10 * Δ * alphaDen)
          = (10 * Δ * alphaDen) * x := by ring
      _ = 1 * ((10 * Δ * alphaDen) * x) := by simp
      _ ≤ 3 * ((10 * Δ * alphaDen) * x) :=
        Nat.mul_le_mul_right ((10 * Δ * alphaDen) * x)
          (by decide : 1 ≤ 3)
      _ = 3 * 1 * κ := by
        simp [κ]
  have hx_le_X' : x ≤ X'.card := le_trans hx_le_boost hX'card
  rcases Finset.exists_subset_card_eq hx_le_X' with ⟨Y, hYsub, hYcard⟩
  refine ⟨H, hHG, ?_, Y, hYcard, ?_⟩
  · have hdegree_eq :
        Δ = cDegOut * L ^ cDegLogOut := by
      simp [Δ, cDegOut, cDegLogOut]
    simpa [L, hdegree_eq] using hdegree
  · exact NodeWellLinkedIn.to_univ
      (NodeWellLinkedIn.mono_terminals hX'node hYsub)

/-- Chekuri--Chuzhoy Theorem 2.21 from Lemma 2.17's routable set and the
cut-matching/AARV embedding source.

This is the proof-facing form closest to Appendix A.4: first build the
low-degree cut-well-linked core from the routable terminal set, then apply the
formalized Theorem 2.14 boost to get the node-well-linked core. -/
theorem nodeWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog) :
    ∃ cCore cCoreLog cDegOut cDegLogOut : ℕ,
      NodeWellLinkedCoreFromTreewidth.{u}
        cCore cCoreLog cDegOut cDegLogOut :=
  nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore
    (cutWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)

/-- Chekuri--Chuzhoy Theorem 3.5 from the cut-well-linked Theorem 2.21
boundary and the faithful direct Section 4 path route. -/
theorem exists_strongPathOfSets_of_treewidth_from_cutWellLinkedCore_and_pathRoute
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_and_pathRoute
    (nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore hcut)
    hroute

/-- Chekuri--Chuzhoy Theorem 3.5 from the cut-well-linked Theorem 2.21
boundary and the split Section 4 route: the strong-tree construction plus
Theorem 4.6 extraction. -/
theorem exists_strongPathOfSets_of_treewidth_from_cutWellLinkedCore_treeCore_and_extraction
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_and_extraction
    (nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore hcut)
    hbuild hextract

/-- Chekuri--Chuzhoy Theorem 3.5 from the cut-well-linked Theorem 2.21
boundary, the strong-tree construction, and the split proof of Theorem 4.6:
the buffered-path branch is proved, while the DFS/many-leaves branch is an
explicit input. -/
theorem exists_strongPathOfSets_of_treewidth_from_cutWellLinkedCore_treeCore_metaDichotomy_and_leafExtraction
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : StrongTreeMetaDichotomy.{u})
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_metaDichotomy_and_leafExtraction
    (nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore hcut)
    hbuild hdichotomy hleaf

/-- Chekuri--Chuzhoy Theorem 3.5 from the cut-well-linked Theorem 2.21
boundary, the strong-tree construction, the proved finite-tree dichotomy, and
the DFS/many-leaves branch of Theorem 4.6. -/
theorem exists_strongPathOfSets_of_treewidth_from_cutWellLinkedCore_treeCore_leafExtraction
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_leafExtraction
    (nodeWellLinkedCoreFromTreewidth_of_cutWellLinkedCore hcut)
    hbuild hleaf

/-- Chekuri--Chuzhoy Theorem 3.5 from the cut-well-linked Theorem 2.21
boundary and the long/buffered meta-path special case of the Section 4 route. -/
theorem exists_strongPathOfSets_of_treewidth_from_cutWellLinkedCore_and_treeRoute
    (hcut :
      ∃ cCut cCutLog cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromTreewidth.{u}
          cCut cCutLog cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) := by
  rcases hroute with ⟨cRoute, cRouteLog, cDeltaPow, hroute'⟩
  exact exists_strongPathOfSets_of_treewidth_from_cutWellLinkedCore_and_pathRoute
    hcut
    ⟨cRoute, cRouteLog, cDeltaPow,
      strongPathOfSetsFromNodeWellLinkedCore_of_strongTreeRoute hroute'⟩

/-- Chekuri--Chuzhoy Theorem 3.5 from the lower-level Appendix A.4 split
behind Theorem 2.21 and the faithful direct Section 4 path route. -/
theorem exists_strongPathOfSets_of_treewidth_from_routable_cutMatching_and_pathRoute
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        StrongPathOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_and_pathRoute
    (nodeWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)
    hroute

/-- Chekuri--Chuzhoy Theorem 3.5 from the lower-level Appendix A.4 split
behind Theorem 2.21 and the split Section 4 route: the strong-tree
construction plus Theorem 4.6 extraction. -/
theorem exists_strongPathOfSets_of_treewidth_from_routable_cutMatching_treeCore_and_extraction
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hextract : StrongPathOfSetsFromStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_and_extraction
    (nodeWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)
    hbuild hextract

/-- Chekuri--Chuzhoy Theorem 3.5 from the lower-level Appendix A.4 split,
the strong-tree construction, and the split proof of Theorem 4.6. -/
theorem exists_strongPathOfSets_of_treewidth_from_routable_cutMatching_treeCore_metaDichotomy_and_leafExtraction
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hdichotomy : StrongTreeMetaDichotomy.{u})
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_metaDichotomy_and_leafExtraction
    (nodeWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)
    hbuild hdichotomy hleaf

/-- Chekuri--Chuzhoy Theorem 3.5 from the lower-level Appendix A.4 split,
the strong-tree construction, the proved finite-tree dichotomy, and the
DFS/many-leaves branch of Theorem 4.6. -/
theorem exists_strongPathOfSets_of_treewidth_from_routable_cutMatching_treeCore_leafExtraction
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hbuild :
      ∃ cBuild cBuildLog cDeltaPow : ℕ,
        StrongTreeOfSetsCoreFromNodeWellLinkedCore.{u}
          cBuild cBuildLog cDeltaPow)
    (hleaf : StrongPathOfSetsFromLeafyStrongTreeOfSets.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_core_treeCore_leafExtraction
    (nodeWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)
    hbuild hleaf

/-- Chekuri--Chuzhoy Theorem 3.5 from the lower-level Appendix A.4 split
behind Theorem 2.21 and the long/buffered meta-path special case of the
Section 4 route. -/
theorem exists_strongPathOfSets_of_treewidth_from_routable_cutMatching_and_treeRoute
    (hroutable :
      ∃ cSet cSetLog cRoute cRouteLog : ℕ,
        RoutableSetFromTreewidth.{u}
          cSet cSetLog cRoute cRouteLog)
    (hcutMatching :
      ∃ cDeg cDegLog cAlpha cAlphaLog : ℕ,
        CutWellLinkedCoreFromRoutableSet.{u}
          cDeg cDegLog cAlpha cAlphaLog)
    (hroute :
      ∃ cRoute cRouteLog cDeltaPow : ℕ,
        StrongTreeOfSetsFromNodeWellLinkedCore.{u}
          cRoute cRouteLog cDeltaPow) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_cutWellLinkedCore_and_treeRoute
    (cutWellLinkedCoreFromTreewidth_of_routableSet_and_cutMatching
      hroutable hcutMatching)
    hroute

/-- Chekuri--Chuzhoy Theorem 3.5/A.2 from its explicit source-input bundle.

This theorem has the same threshold-shaped conclusion as the broad A.2 contract,
but its proof uses only the three exposed lower-level inputs in
`TheoremA2SourceInputs`.  Therefore it is the preferred audit point when
closing the self-contained proof: each conjunct of `TheoremA2SourceInputs` must
be proved separately from the local papers. -/
theorem exists_strongPathOfSets_of_treewidth_from_theoremA2SourceInputs
    (hinputs : TheoremA2SourceInputs.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) := by
  rcases hinputs with ⟨hroutable, hcutMatching, hroute⟩
  exact exists_strongPathOfSets_of_treewidth_from_routable_cutMatching_and_pathRoute
    hroutable hcutMatching hroute

/-- Chekuri--Chuzhoy Theorem 3.5/A.2 from the expanded leaf-source input
bundle.

Compared with `exists_strongPathOfSets_of_treewidth_from_theoremA2SourceInputs`,
this theorem exposes the Section 4 semantic closure more faithfully: the
strong-tree construction and the DFS/many-leaves extraction are separate
inputs, while the finite-tree dichotomy is the proved theorem
`strongTreeMetaDichotomy`. -/
theorem exists_strongPathOfSets_of_treewidth_from_theoremA2LeafSourceInputs
    (hinputs : TheoremA2LeafSourceInputs.{u}) :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  cPath * w * ell ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G ell w) :=
  exists_strongPathOfSets_of_treewidth_from_theoremA2SourceInputs
    (theoremA2SourceInputs_of_leafSourceInputs hinputs)

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
