import Lax17Proofs.Source.TreewidthSparsifierDefs
import Lax17Proofs.Source.TreewidthSparsifierSection2
import Lax17Proofs.Source.Theorem214Contract
import Lax17Proofs.Source.FlowDefs
import Lax17Proofs.Source.LocalSubgraph
import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.Treewidth
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Contract for `treewidth-sparsifier.pdf`

This file records the statement-level content of Chekuri--Chuzhoy,
*Degree-3 Treewidth Sparsifiers*, in the form needed for the grid-minor
formalization.

The public A.1 route used downstream is
`degreeThreeTopologicalTreewidthSparsifierThreshold`: it is the threshold form
of Theorem 1.1 of the paper with the randomized algorithm, running time, and the
`O(k^4)` vertex-count guarantee removed.  The output is deliberately a
topological minor, matching the paper.  The later same-vertex subgraph form used
by the Chuzhoy--Tan Appendix A.2 arithmetic is a separate bridge contract in
`DegreeThreeStrongPathOfSetsContract`.

The remaining definitions and axioms expose the semantic proof ingredients used
inside the paper: edge- and node-well-linkedness, path-of-sets, cut-matching
expanders, expander embeddings, and the degree-four/degree-three intermediate
sparsifier statements.  Theorem 1.3's two-pair routability sparsifier is proved
in `TreewidthSparsifierSection2` and imported here, not axiomatized.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


open scoped Classical

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Well-linkedness and path-of-sets inputs -/

/-- Paper Definition 1, using the repository's scaled cut form. -/
def ScaledWellLinked
    (G : _root_.SimpleGraph V) (T : Finset V)
    (alphaNum alphaDen : ℕ) : Prop :=
  ScaledEdgeWellLinked G T alphaNum alphaDen

/-- Paper Definition 2, localized to an ambient finite region `C`.

Unlike the repository's existing `NodeWellLinkedIn`, the paper quantifies over
equal-sized terminal subsets that need not be disjoint, and allows empty paths.
The perfect packing records that every vertex of each side is used exactly
once. -/
def PaperNodeWellLinkedIn
    (G : _root_.SimpleGraph V) (C T : Finset V) : Prop :=
  T ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → A.card = B.card →
      ∃ P : PerfectPathPacking G A B,
        P.toPathPacking.StaysIn C

/-- Paper Definition 2, with the ambient region specialized to the whole
finite graph. -/
def PaperNodeWellLinked
    (G : _root_.SimpleGraph V) (T : Finset V) : Prop :=
  PaperNodeWellLinkedIn G Finset.univ T

/-- A terminal-clean strengthening of the repository's local
node-well-linkedness predicate.

For disjoint terminal subsets the supplied maximum packing must not use any
terminal of `T` as an internal vertex.  This is the exact extra information
needed to recover the paper's overlapping-subset formulation: common terminals
of two equal-size subsets can then be routed by identity paths without
intersecting the remaining linkage. -/
def TerminalCleanNodeWellLinkedIn
    (G : _root_.SimpleGraph V) (C T : Finset V) : Prop :=
  T ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ T → B ⊆ T → Disjoint A B →
      ∃ P : PathPacking G A B,
        P.card = min A.card B.card ∧
          P.StaysIn C ∧
            P.InternallyDisjointFromSet T

omit [Fintype V] in
/-- Terminal-clean node-well-linkedness implies the paper-literal
node-well-linkedness predicate.

For equal-size terminal subsets `A` and `B`, route the disjoint remainders
`A \ B` and `B \ A`; the terminal-clean hypothesis keeps those paths away from
the common terminals `A ∩ B`, so they can be unioned with the identity packing
on the overlap. -/
theorem paperNodeWellLinkedIn_of_terminalCleanNodeWellLinkedIn
    {G : _root_.SimpleGraph V} {C T : Finset V}
    (h : TerminalCleanNodeWellLinkedIn G C T) :
    PaperNodeWellLinkedIn G C T := by
  classical
  refine ⟨h.1, ?_⟩
  intro A B hA hB hcardAB
  let A₀ : Finset V := A \ B
  let B₀ : Finset V := B \ A
  let I : Finset V := A ∩ B
  have hA₀T : A₀ ⊆ T := by
    intro x hx
    exact hA (Finset.mem_sdiff.mp hx).1
  have hB₀T : B₀ ⊆ T := by
    intro x hx
    exact hB (Finset.mem_sdiff.mp hx).1
  have hIT : I ⊆ T := by
    intro x hx
    exact hA (Finset.mem_inter.mp hx).1
  have hA₀B₀ : Disjoint A₀ B₀ := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_sdiff.mp hxB).1
  have hA₀I : Disjoint A₀ I := by
    rw [Finset.disjoint_left]
    intro x hxA hxI
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_inter.mp hxI).2
  have hB₀I : Disjoint B₀ I := by
    rw [Finset.disjoint_left]
    intro x hxB hxI
    exact (Finset.mem_sdiff.mp hxB).2 (Finset.mem_inter.mp hxI).1
  have hA_sdiff_inter : A \ (A ∩ B) = A₀ := by
    ext x
    simp [A₀]
  have hB_sdiff_inter : B \ (A ∩ B) = B₀ := by
    ext x
    simp [B₀]
  have hAcard :
      A₀.card + I.card = A.card := by
    have hIAsub : A ∩ B ⊆ A := Finset.inter_subset_left
    rw [← Finset.card_sdiff_add_card_eq_card hIAsub]
    simp [A₀, I, hA_sdiff_inter]
  have hBcard :
      B₀.card + I.card = B.card := by
    have hIBsub : A ∩ B ⊆ B := Finset.inter_subset_right
    rw [← Finset.card_sdiff_add_card_eq_card hIBsub]
    simp [B₀, I, hB_sdiff_inter]
  have hA₀B₀card : A₀.card = B₀.card := by
    omega
  rcases h.2 hA₀T hB₀T hA₀B₀ with
    ⟨P, hPcard, hPstay, hPclean⟩
  have hPcardA₀ : P.card = A₀.card := by
    simpa [hA₀B₀card] using hPcard
  have hPcardB₀ : P.card = B₀.card := by
    rw [hPcardA₀, hA₀B₀card]
  let P₀ : PerfectPathPacking G A₀ B₀ :=
    P.toPerfectOfCardEq hPcardA₀ hPcardB₀
  let Q : PerfectPathPacking G I I :=
    PerfectPathPacking.refl G I
  have hP₀stay : P₀.toPathPacking.StaysIn C := by
    simpa [P₀, PathPacking.toPerfectOfCardEq] using
      PathPacking.orient_staysIn (P := P) hPstay
  have hP₀clean : P₀.toPathPacking.InternallyDisjointFromSet T := by
    simpa [P₀, PathPacking.toPerfectOfCardEq] using
      PathPacking.orient_internallyDisjointFromSet (P := P) hPclean
  have hQstay : Q.toPathPacking.StaysIn C := by
    intro j v hv
    have hv_eq : v = (I.equivFin.symm j).1 := by
      simpa [Q, PerfectPathPacking.refl, GraphPath.refl_vertexSet] using hv
    have hvI : v ∈ I := by
      rw [hv_eq]
      exact (I.equivFin.symm j).2
    exact h.1 (hIT hvI)
  have hmutual : P₀.toPathPacking.MutuallyNodeDisjoint Q.toPathPacking := by
    intro i j
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvP hvQ
    have hv_eq : v = (I.equivFin.symm j).1 := by
      simpa [Q, PerfectPathPacking.refl, GraphPath.refl_vertexSet] using hvQ
    have hvI : v ∈ I := by
      rw [hv_eq]
      exact (I.equivFin.symm j).2
    have hvT : v ∈ T := hIT hvI
    rcases hP₀clean i hvP hvT with hsource | htarget
    · have hsourceA₀ : (P₀.path i).source ∈ A₀ := P₀.source_mem i
      exact (Finset.mem_sdiff.mp hsourceA₀).2
        (by simpa [hsource] using (Finset.mem_inter.mp hvI).2)
    · have htargetB₀ : (P₀.path i).target ∈ B₀ := P₀.target_mem i
      exact (Finset.mem_sdiff.mp htargetB₀).2
        (by simpa [htarget] using (Finset.mem_inter.mp hvI).1)
  let U : PerfectPathPacking G (A₀ ∪ I) (B₀ ∪ I) :=
    P₀.disjointUnion Q hA₀I hB₀I hmutual
  have hUstay : U.toPathPacking.StaysIn C := by
    intro i v hv
    cases i with
    | inl a =>
        exact hP₀stay a hv
    | inr b =>
        exact hQstay b hv
  have hAunion : A₀ ∪ I = A := by
    ext x
    by_cases hxB : x ∈ B <;> simp [A₀, I, hxB]
  have hBunion : B₀ ∪ I = B := by
    ext x
    by_cases hxA : x ∈ A <;> simp [B₀, I, hxA]
  refine ⟨U.copyTerminals hAunion hBunion, ?_⟩
  exact PerfectPathPacking.copyTerminals_staysIn U hAunion hBunion hUstay

omit [Fintype V] in
/-- Any terminal set of size at most one is paper-node-well-linked in its
ambient region.  The only equal-size subfamilies are equal, so the identity
perfect packing suffices. -/
theorem paperNodeWellLinkedIn_of_card_le_one
    {G : _root_.SimpleGraph V} {C T : Finset V}
    (hTC : T ⊆ C) (hcard : T.card ≤ 1) :
    PaperNodeWellLinkedIn G C T := by
  classical
  refine ⟨hTC, ?_⟩
  intro A B hA hB hcardAB
  have hTsubsingleton :
      ∀ ⦃x⦄, x ∈ T → ∀ ⦃y⦄, y ∈ T → x = y := by
    intro x hx y hy
    exact (Finset.card_le_one.mp hcard) x hx y hy
  have hAB : A = B := by
    apply Finset.Subset.antisymm
    · intro x hxA
      have hApos : 0 < A.card := Finset.card_pos.mpr ⟨x, hxA⟩
      have hBpos : 0 < B.card := by simpa [hcardAB] using hApos
      rcases Finset.card_pos.mp hBpos with ⟨b, hbB⟩
      have hxb : x = b := hTsubsingleton (hA hxA) (hB hbB)
      simpa [hxb] using hbB
    · intro x hxB
      have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨x, hxB⟩
      have hApos : 0 < A.card := by simpa [hcardAB] using hBpos
      rcases Finset.card_pos.mp hApos with ⟨a, haA⟩
      have hxa : x = a := hTsubsingleton (hB hxB) (hA haA)
      simpa [hxa] using haA
  subst B
  refine ⟨PerfectPathPacking.refl G A, ?_⟩
  intro i v hv
  have hv_eq : v = (A.equivFin.symm i).1 := by
    simpa [PerfectPathPacking.refl, GraphPath.refl_vertexSet] using hv
  simpa [hv_eq] using hTC (hA (A.equivFin.symm i).2)

/-- Global scaled well-linkedness is the local Section 4.6 predicate on the
whole vertex set. -/
theorem scaledEdgeWellLinkedIn_univ_of_scaledWellLinked
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {T : Finset V}
    {alphaNum alphaDen : ℕ}
    (h : ScaledWellLinked G T alphaNum alphaDen) :
    Section46.ScaledEdgeWellLinkedIn G Finset.univ T alphaNum alphaDen := by
  classical
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro v _hv
    simp
  · intro X Y _hX _hY hcover hdisj
    exact h.2.2 X Y (by simpa using hcover) hdisj

/-- Any terminal set of size at most one is locally node-well-linked in the
whole graph under the repository's maximum-packing definition. -/
theorem nodeWellLinkedIn_univ_of_card_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {T : Finset V}
    (hcard : T.card ≤ 1) :
    NodeWellLinkedIn G Finset.univ T := by
  classical
  refine ⟨by intro v _hv; simp, ?_⟩
  intro A B hA hB hdisj
  have hTsubsingleton : ∀ ⦃x⦄, x ∈ T → ∀ ⦃y⦄, y ∈ T → x = y := by
    intro x hx y hy
    exact (Finset.card_le_one.mp hcard) x hx y hy
  have hmin : min A.card B.card = 0 := by
    by_contra hnonzero
    have hpos : 0 < min A.card B.card := Nat.pos_of_ne_zero hnonzero
    have hApos : 0 < A.card := lt_of_lt_of_le hpos (Nat.min_le_left A.card B.card)
    have hBpos : 0 < B.card := lt_of_lt_of_le hpos (Nat.min_le_right A.card B.card)
    rcases Finset.card_pos.mp hApos with ⟨a, ha⟩
    rcases Finset.card_pos.mp hBpos with ⟨b, hb⟩
    have hab : a = b := hTsubsingleton (hA ha) (hB hb)
    exact Finset.disjoint_left.mp hdisj ha (by simpa [hab] using hb)
  let P : PathPacking G A B := {
    Index := Empty
    path := fun i => nomatch i
    connects := by
      intro i
      cases i
    node_disjoint := by
      intro i
      cases i
  }
  refine ⟨P, ?_, ?_⟩
  · simp [P, PathPacking.card, hmin]
  · intro i
    cases i

/-- Paper Definition 3, localized to an ambient finite region `C`.

The two sides themselves are disjoint, and every equal-sized pair of subfamilies
can be routed by node-disjoint paths inside `C`. -/
def PaperLinkedIn
    (G : _root_.SimpleGraph V) (C A B : Finset V) : Prop :=
  A ⊆ C ∧ B ⊆ C ∧ Disjoint A B ∧
    ∀ ⦃A' B' : Finset V⦄, A' ⊆ A → B' ⊆ B → A'.card = B'.card →
      ∃ P : PerfectPathPacking G A' B',
        P.toPathPacking.StaysIn C

/-- Paper Definition 3, with the ambient region specialized to the whole
finite graph. -/
def PaperLinked
    (G : _root_.SimpleGraph V) (A B : Finset V) : Prop :=
  PaperLinkedIn G Finset.univ A B

omit [Fintype V] in
/-- The repository's linkedness predicate implies the paper-literal linkedness
predicate: for equal-size subfamilies, a maximum packing can be oriented and
promoted to a perfect packing. -/
theorem paperLinkedIn_of_nodeLinkedIn
    {G : _root_.SimpleGraph V} {C A B : Finset V}
    (h : NodeLinkedIn G C A B) :
    PaperLinkedIn G C A B := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro A' B' hA' hB' hcard
  rcases NodeLinkedIn.exists_perfectPathPacking_of_card_eq
      (h.mono_terminals hA' hB') hcard with
    ⟨P, _hPcard, hstay⟩
  exact ⟨P, hstay⟩

/-- A paper-literal strong Path-of-Sets System.

The repository's `StrongPathOfSetsSystem` uses the local project
`NodeWellLinkedIn`; this structure uses the paper's equal-sized-subset
node-well-linkedness and linkedness predicates instead. -/
structure PaperStrongPathOfSetsSystem {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (ell w : ℕ)
    extends PathOfSetsSystem G ell w where
  /-- The left nails are node-well-linked in the paper sense. -/
  left_paperNodeWellLinked :
    ∀ i : Fin ell, PaperNodeWellLinkedIn G (cluster i) (left i)
  /-- The right nails are node-well-linked in the paper sense. -/
  right_paperNodeWellLinked :
    ∀ i : Fin ell, PaperNodeWellLinkedIn G (cluster i) (right i)
  /-- The left and right nail sets are linked in the paper sense. -/
  left_right_paperLinked :
    ∀ i : Fin ell, PaperLinkedIn G (cluster i) (left i) (right i)



/-- The fully proved local-node-well-linked version of Theorem 3.1.

This is what follows directly from the self-contained Theorem 2.14
formalization.  It deliberately concludes `NodeWellLinkedIn G univ T'` rather
than `PaperNodeWellLinked G T'`: the latter additionally requires equal-size
subsets that may overlap, and the current local maximum-packing predicate does
not by itself keep routed paths away from overlap terminals. -/
theorem theorem31_localNodeWellLinked_subset_of_wellLinked :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) (T : Finset V)
        {Δ alphaNum alphaDen : ℕ},
          G.Connected →
            MaxDegreeAtMost G Δ →
              ScaledWellLinked G T alphaNum alphaDen →
                0 < Δ →
                  0 < alphaNum →
                    alphaNum < alphaDen →
                      ∃ T' : Finset V,
                        T' ⊆ T ∧
                          NodeWellLinkedIn G Finset.univ T' ∧
                            alphaNum * T.card ≤ c * Δ * alphaDen * T'.card := by
  refine ⟨60, by decide, ?_⟩
  intro V _ _ G T Δ alphaNum alphaDen hconn hdegree hwell hΔ
    halphaNum halpha_lt
  let Δ' := 3 * Δ
  let denom := 10 * Δ' * alphaDen
  let num := 3 * alphaNum * T.card
  have halphaDen : 0 < alphaDen := lt_trans halphaNum halpha_lt
  have hdenom_pos : 0 < denom := by
    dsimp [denom, Δ']
    positivity
  have hdegree' : MaxDegreeAtMost G Δ' :=
    maxDegreeAtMost_mono hdegree (by dsimp [Δ']; omega)
  have hΔ' : 3 ≤ Δ' := by
    dsimp [Δ']
    nlinarith
  have hcluster : IsCluster G Finset.univ := by
    rw [IsCluster]
    have hset : {v : V | v ∈ (Finset.univ : Finset V)} = Set.univ := by
      ext v
      simp
    rw [hset]
    exact (_root_.SimpleGraph.induceUnivIso G).connected_iff.mpr hconn
  have hwellLocal :
      Section46.ScaledEdgeWellLinkedIn G Finset.univ T alphaNum alphaDen :=
    scaledEdgeWellLinkedIn_univ_of_scaledWellLinked hwell
  rcases
      Lax17Proofs.SimpleGraph.ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_contract
        (G := G) (C := Finset.univ) (T := T)
        (alphaNum := alphaNum) (alphaDen := alphaDen)
        (Δ := Δ') (κ := T.card)
        hcluster hdegree' hΔ' halphaNum (Nat.le_of_lt halpha_lt) rfl
        hwellLocal with
    ⟨T₀, hT₀sub, hT₀floor, hT₀node⟩
  by_cases hsmall : num < denom
  · by_cases hTempty : T.card = 0
    · refine ⟨∅, by simp, nodeWellLinkedIn_univ_of_card_le_one (by simp), ?_⟩
      simp [hTempty]
    · have hTpos : 0 < T.card := Nat.pos_of_ne_zero hTempty
      rcases Finset.card_pos.mp hTpos with ⟨v, hvT⟩
      refine ⟨{v}, ?_, nodeWellLinkedIn_univ_of_card_le_one (by simp), ?_⟩
      · intro x hx
        have hxv : x = v := by
          simpa using hx
        simpa [hxv] using hvT
      · have hnum_bound : alphaNum * T.card ≤ 60 * Δ * alphaDen := by
          have hle_num : alphaNum * T.card ≤ num := by
            dsimp [num]
            nlinarith [Nat.zero_le (alphaNum * T.card)]
          have hden_le : denom ≤ 60 * Δ * alphaDen := by
            dsimp [denom, Δ']
            nlinarith
          exact hle_num.trans (Nat.le_of_lt hsmall |>.trans hden_le)
        simpa using hnum_bound
  · have hden_le_num : denom ≤ num := Nat.le_of_not_gt hsmall
    let k := num / denom
    have hk_pos : 0 < k := Nat.div_pos hden_le_num hdenom_pos
    have hnum_lt : num < denom * (k + 1) := by
      calc
        num = num % denom + denom * (num / denom) := by
          rw [Nat.mod_add_div]
        _ < denom + denom * (num / denom) := by
          exact Nat.add_lt_add_right (Nat.mod_lt num hdenom_pos) _
        _ = denom * (k + 1) := by
          dsimp [k]
          ring
    have hkp1_le : k + 1 ≤ 2 * k := by
      omega
    have hnum_le :
        alphaNum * T.card ≤ 60 * Δ * alphaDen * T₀.card := by
      have hle_num : alphaNum * T.card ≤ num := by
        dsimp [num]
        nlinarith [Nat.zero_le (alphaNum * T.card)]
      have hnum_lt₂ : num < denom * (2 * k) :=
        hnum_lt.trans_le (Nat.mul_le_mul_left denom hkp1_le)
      have hnum_le₂ : num ≤ denom * (2 * k) := Nat.le_of_lt hnum_lt₂
      have hk_card : k ≤ T₀.card := by
        dsimp [k, num, denom, Δ'] at hT₀floor
        simpa [k, num, denom, Δ'] using hT₀floor
      have hden_two_card :
          denom * (2 * k) ≤ 60 * Δ * alphaDen * T₀.card := by
        calc
          denom * (2 * k) = 60 * Δ * alphaDen * k := by
            dsimp [denom, Δ']
            ring
          _ ≤ 60 * Δ * alphaDen * T₀.card := by
            exact Nat.mul_le_mul_left (60 * Δ * alphaDen) hk_card
      exact hle_num.trans (hnum_le₂.trans hden_two_card)
    exact ⟨T₀, hT₀sub, hT₀node, hnum_le⟩





/-- Theorem 3.4 of the paper: large treewidth produces a strong path-of-sets
system.  The paper's `k / log^c k > c' h r^50` is encoded without division. -/
def StrongPathOfSetsFromTreewidth
    (cPath cPathLog : ℕ) : Prop :=
  0 < cPath ∧ 0 < cPathLog ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {k height width : ℕ},
        1 < k →
          1 < height →
            1 < width →
              k ≤ treewidth G →
                cPath * height * width ^ 50 *
                    (Nat.log 2 k) ^ cPathLog < k →
                  Nonempty (PaperStrongPathOfSetsSystem G width height)


/-! ## Cut-matching expanders and embeddings -/

/-- A scaled edge-expander predicate for finite simple graphs.

`alphaNum / alphaDen` is the lower bound on `|E(S,V\S)| / |S|` for all
nonempty `S` of size at most half the vertex set.  Unlike well-linkedness, this
ratio may exceed one in high-degree graphs. -/
def ScaledEdgeExpander
    (G : _root_.SimpleGraph V) (alphaNum alphaDen : ℕ) : Prop :=
  0 < alphaNum ∧ 0 < alphaDen ∧
    ∀ S : Finset V,
      0 < S.card →
        2 * S.card ≤ Fintype.card V →
          alphaNum * S.card ≤
            alphaDen *
              (Section44.edgeBoundary G S (Finset.univ \ S)).card

/-- A paper-style embedding of a graph `X` into a graph `G`.

Each vertex of `X` is mapped to a connected subgraph `C_v` of `G`, represented
by a finite support set and an explicit edge subgraph.  Each edge of `X` is
mapped to a path in `G` between the corresponding vertex models. -/
structure GraphEmbeddingWithPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    (X : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) where
  /-- Vertex set of the connected model for each vertex of `X`. -/
  vertexModel : W → Finset V
  /-- Edge subgraph of the connected model for each vertex of `X`. -/
  vertexModelGraph : W → _root_.SimpleGraph V
  /-- Vertex-model subgraphs are contained in the host. -/
  vertexModelGraph_le : ∀ x : W, vertexModelGraph x ≤ G
  /-- Vertex-model edges are supported on the chosen finite vertex model. -/
  vertexModelGraph_supported :
    ∀ (x : W) ⦃a b : V⦄,
      (vertexModelGraph x).Adj a b →
        a ∈ vertexModel x ∧ b ∈ vertexModel x
  /-- Vertex models are nonempty. -/
  vertexModel_nonempty : ∀ x : W, (vertexModel x).Nonempty
  /-- Vertex models are connected using their explicit edge subgraphs. -/
  vertexModel_connected :
    ∀ x : W,
      ((vertexModelGraph x).induce {v : V | v ∈ vertexModel x}).Connected
  /-- An orientation of each edge of `X`. -/
  edgeSource : X.edgeSet → W
  /-- Target endpoint for the chosen orientation. -/
  edgeTarget : X.edgeSet → W
  /-- The chosen endpoints are adjacent in `X`. -/
  edge_adj : ∀ e : X.edgeSet, X.Adj (edgeSource e) (edgeTarget e)
  /-- The chosen endpoints represent the unordered edge. -/
  edge_eq : ∀ e : X.edgeSet, s(edgeSource e, edgeTarget e) = (e : Sym2 W)
  /-- The path of `G` realizing an edge of `X`. -/
  edgePath : X.edgeSet → GraphPath G
  /-- The realizing path starts in the source vertex model. -/
  edgePath_source_mem :
    ∀ e : X.edgeSet, (edgePath e).source ∈ vertexModel (edgeSource e)
  /-- The realizing path ends in the target vertex model. -/
  edgePath_target_mem :
    ∀ e : X.edgeSet, (edgePath e).target ∈ vertexModel (edgeTarget e)

namespace GraphEmbeddingWithPaths

/-- The number of embedded edge paths using a host edge. -/
noncomputable def edgePathLoad
    {W : Type u} [Fintype W] [DecidableEq W]
    {X : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    [Fintype X.edgeSet] (E : GraphEmbeddingWithPaths X G)
    (e : Sym2 V) : ℕ := by
  classical
  exact
    (Finset.univ.filter
      (fun f : X.edgeSet => e ∈ (E.edgePath f).edgeSet)).card

/-- The number of vertex-model subgraphs using a host edge. -/
noncomputable def vertexModelEdgeLoad
    {W : Type u} [Fintype W] [DecidableEq W]
    {X : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (E : GraphEmbeddingWithPaths X G)
    (e : Sym2 V) : ℕ := by
  classical
  exact
    (Finset.univ.filter
      (fun x : W => e ∈ (E.vertexModelGraph x).edgeSet)).card

end GraphEmbeddingWithPaths

/-- `X` embeds into `G` with congestion at most `eta`, in the paper's sense
that every host edge lies on at most `eta - 1` embedded edge paths and in at
most one vertex-model graph. -/
def HasEmbeddingWithCongestion
    {W : Type u} [Fintype W] [DecidableEq W]
    (X : _root_.SimpleGraph W) (G : _root_.SimpleGraph V)
    [Fintype X.edgeSet] (eta : ℕ) : Prop :=
  ∃ E : GraphEmbeddingWithPaths X G,
    ∀ e : Sym2 V, e ∈ G.edgeSet →
      E.edgePathLoad e < eta ∧ E.vertexModelEdgeLoad e ≤ 1

/-- A balanced cut chosen by the cut player in the cut-matching game. -/
structure BalancedCut (N : ℕ) where
  /-- One side of the cut. -/
  left : Finset (Fin N)
  /-- The left side has exactly half the vertices. -/
  left_card : 2 * left.card = N

namespace BalancedCut

/-- The complementary side of a balanced cut. -/
noncomputable def right {N : ℕ} (C : BalancedCut N) : Finset (Fin N) :=
  Finset.univ \ C.left

end BalancedCut

/-- A cut-matching-game transcript after a fixed number of rounds.

For each round it records the cut chosen by the cut player and the perfect
matching returned by the matching player across that cut.  This represents the
paper's multigraph: repeated matched pairs in different rounds are counted with
multiplicity by `edgeBoundaryCount`. -/
structure CutMatchingTranscript (N rounds : ℕ) where
  /-- The cut chosen in each round. -/
  cut : Fin rounds → BalancedCut N
  /-- The matching-player response across each chosen cut. -/
  matching :
    ∀ j : Fin rounds,
      {v : Fin N // v ∈ (cut j).left} ≃
        {v : Fin N // v ∈ (cut j).right}

namespace CutMatchingTranscript

/-- Multigraph boundary size for a cut in a cut-matching transcript, counting
one crossing edge per matching edge per round. -/
noncomputable def edgeBoundaryCount {N rounds : ℕ}
    (T : CutMatchingTranscript N rounds) (S : Finset (Fin N)) : ℕ := by
  classical
  exact Finset.univ.sum fun j : Fin rounds =>
    (Finset.univ.filter fun x : {v : Fin N // v ∈ (T.cut j).left} =>
      (x.1 ∈ S ∧ (T.matching j x).1 ∉ S) ∨
        (x.1 ∉ S ∧ (T.matching j x).1 ∈ S)).card

/-- Expansion of the multigraph produced by a cut-matching transcript. -/
def IsExpander {N rounds : ℕ}
    (T : CutMatchingTranscript N rounds)
    (alphaNum alphaDen : ℕ) : Prop :=
  0 < alphaNum ∧ 0 < alphaDen ∧
    ∀ S : Finset (Fin N),
      0 < S.card →
        2 * S.card ≤ N →
          alphaNum * S.card ≤ alphaDen * T.edgeBoundaryCount S

/-- The prefix consisting of the first `j` rounds of a full cut-matching
transcript.  This is the information available to an adaptive cut-player
strategy before choosing the cut in round `j`. -/
def roundPrefix {N rounds : ℕ}
    (T : CutMatchingTranscript N rounds) (j : Fin rounds) :
    CutMatchingTranscript N j.1 where
  cut i := T.cut ⟨i.1, lt_trans i.2 j.2⟩
  matching i := T.matching ⟨i.1, lt_trans i.2 j.2⟩

end CutMatchingTranscript

/-- An embedding of the cut-matching multigraph transcript into a host graph.

The transcript is a multigraph: in round `j` every vertex on the left side of
the cut has one matched partner on the right side, and repeated pairs in
different rounds remain distinct embedded edges.  This structure therefore
indexes edge paths by `(j, x)` rather than by the edge set of a collapsed
simple graph. -/
structure CutMatchingTranscriptEmbeddingWithPaths {N rounds : ℕ}
    (T : CutMatchingTranscript N rounds) (G : _root_.SimpleGraph V) where
  /-- Vertex set of the connected model for each transcript vertex. -/
  vertexModel : Fin N → Finset V
  /-- Edge subgraph of the connected model for each transcript vertex. -/
  vertexModelGraph : Fin N → _root_.SimpleGraph V
  /-- Vertex-model subgraphs are contained in the host. -/
  vertexModelGraph_le : ∀ x : Fin N, vertexModelGraph x ≤ G
  /-- Vertex-model edges are supported on the chosen finite vertex model. -/
  vertexModelGraph_supported :
    ∀ (x : Fin N) ⦃a b : V⦄,
      (vertexModelGraph x).Adj a b →
        a ∈ vertexModel x ∧ b ∈ vertexModel x
  /-- Vertex models are nonempty. -/
  vertexModel_nonempty : ∀ x : Fin N, (vertexModel x).Nonempty
  /-- Vertex models are connected using their explicit edge subgraphs. -/
  vertexModel_connected :
    ∀ x : Fin N,
      ((vertexModelGraph x).induce {v : V | v ∈ vertexModel x}).Connected
  /-- The host path realizing the matching edge selected for `x` in round
  `j`. -/
  matchingPath :
    ∀ j : Fin rounds,
      {x : Fin N // x ∈ (T.cut j).left} → GraphPath G
  /-- A realizing path starts in the vertex model of its left endpoint. -/
  matchingPath_source_mem :
    ∀ (j : Fin rounds) (x : {x : Fin N // x ∈ (T.cut j).left}),
      (matchingPath j x).source ∈ vertexModel x.1
  /-- A realizing path ends in the vertex model of its matched right
  endpoint. -/
  matchingPath_target_mem :
    ∀ (j : Fin rounds) (x : {x : Fin N // x ∈ (T.cut j).left}),
      (matchingPath j x).target ∈ vertexModel ((T.matching j x).1)

namespace CutMatchingTranscriptEmbeddingWithPaths

/-- The number of transcript matching-edge paths using a host edge, counted
with transcript multiplicity. -/
noncomputable def matchingPathEdgeLoad {N rounds : ℕ}
    {T : CutMatchingTranscript N rounds} {G : _root_.SimpleGraph V}
    (E : CutMatchingTranscriptEmbeddingWithPaths T G)
    (e : Sym2 V) : ℕ := by
  classical
  exact Finset.univ.sum fun j : Fin rounds =>
    (Finset.univ.filter
      (fun x : {v : Fin N // v ∈ (T.cut j).left} =>
        e ∈ (E.matchingPath j x).edgeSet)).card

/-- The number of vertex-model subgraphs using a host edge. -/
noncomputable def vertexModelEdgeLoad {N rounds : ℕ}
    {T : CutMatchingTranscript N rounds} {G : _root_.SimpleGraph V}
    (E : CutMatchingTranscriptEmbeddingWithPaths T G)
    (e : Sym2 V) : ℕ := by
  classical
  exact
    (Finset.univ.filter
      (fun x : Fin N => e ∈ (E.vertexModelGraph x).edgeSet)).card

end CutMatchingTranscriptEmbeddingWithPaths

/-- A cut-matching transcript embeds into `G` with congestion at most `eta`,
counting matching-edge paths with transcript multiplicity and allowing each
host edge in at most one vertex-model graph. -/
def HasCutMatchingTranscriptEmbeddingWithCongestion {N rounds : ℕ}
    (T : CutMatchingTranscript N rounds)
    (G : _root_.SimpleGraph V) (eta : ℕ) : Prop :=
  ∃ E : CutMatchingTranscriptEmbeddingWithPaths T G,
    ∀ e : Sym2 V, e ∈ G.edgeSet →
      E.matchingPathEdgeLoad e < eta ∧ E.vertexModelEdgeLoad e ≤ 1

/-- An abstract cut-player strategy for a fixed number of rounds.

The contract does not formalize the randomized algorithm itself; this type is
the semantic placeholder for the adaptive rule choosing the next balanced cut
from the transcript prefix seen so far. -/
structure CutPlayerStrategy (N rounds : ℕ) where
  /-- The cut chosen in round `j`, as a function of the first `j` rounds of
  matching-player responses. -/
  nextCut : ∀ j : Fin rounds, CutMatchingTranscript N j.1 → BalancedCut N

namespace CutPlayerStrategy

/-- A full transcript is legal for a cut-player strategy when every recorded
cut is exactly the cut selected by the strategy from the preceding transcript
prefix.  The transcript type itself stores the matching player's perfect
matching response across each selected cut, so this quantifies over all such
responses rather than over an arbitrary legality predicate. -/
def LegalTranscript {N rounds : ℕ}
    (S : CutPlayerStrategy N rounds)
    (T : CutMatchingTranscript N rounds) : Prop :=
  ∀ j : Fin rounds, T.cut j = S.nextCut j (T.roundPrefix j)

end CutPlayerStrategy

/-- A legal sequence of matching-player responses against a cut-player
strategy. -/
structure MatchingPlayerResponse {N rounds : ℕ}
    (S : CutPlayerStrategy N rounds) where
  /-- The resulting cut-matching transcript. -/
  transcript : CutMatchingTranscript N rounds
  /-- Proof that the transcript is legal for the chosen adaptive strategy. -/
  legal_against_strategy : S.LegalTranscript transcript

/-- A randomized cut-player strategy, represented non-algorithmically by a
finite seed space of deterministic adaptive strategies. -/
structure RandomizedCutPlayerStrategy (N rounds : ℕ) where
  /-- Random seed space. -/
  Seed : Type u
  /-- The seed space is finite. -/
  seedFintype : Fintype Seed
  /-- The seed space has decidable equality, used to count successful seeds. -/
  seedDecidableEq : DecidableEq Seed
  /-- The seed space is nonempty, so success probability is not vacuous. -/
  seed_nonempty : Nonempty Seed
  /-- The deterministic adaptive strategy selected by each seed. -/
  cutStrategy : Seed → CutPlayerStrategy N rounds
  /-- For each seed, the matching player has at least one legal play. -/
  response_nonempty :
    ∀ seed : Seed, Nonempty (MatchingPlayerResponse (cutStrategy seed))

namespace RandomizedCutPlayerStrategy

/-- Number of random seeds. -/
noncomputable def seedCount {N rounds : ℕ}
    (R : RandomizedCutPlayerStrategy N rounds) : ℕ := by
  letI := R.seedFintype
  exact Fintype.card R.Seed

end RandomizedCutPlayerStrategy

/-- A matching-player policy against a randomized cut-player strategy.

The policy is represented extensionally by the legal transcript it induces for
each seed.  The `matching_nonanticipative` field says that the matching chosen
in round `j` depends only on the transcript prefix seen before that round and
on the current cut, not on hidden random-seed information. -/
structure RandomizedMatchingPlayerResponse {N rounds : ℕ}
    (R : RandomizedCutPlayerStrategy N rounds) where
  /-- The legal response induced for each random seed. -/
  response : ∀ seed : R.Seed, MatchingPlayerResponse (R.cutStrategy seed)
  /-- The response is a genuine adaptive matching-player policy rather than a
  seed oracle. -/
  matching_nonanticipative :
    ∀ (s t : R.Seed) (j : Fin rounds),
      (response s).transcript.roundPrefix j =
        (response t).transcript.roundPrefix j →
      (response s).transcript.cut j =
        (response t).transcript.cut j →
      HEq ((response s).transcript.matching j)
        ((response t).transcript.matching j)

namespace RandomizedMatchingPlayerResponse

/-- Number of seeds for which the induced transcript is an expander. -/
noncomputable def successSeedCount {N rounds : ℕ}
    {R : RandomizedCutPlayerStrategy N rounds}
    (A : RandomizedMatchingPlayerResponse R)
    (alphaNum alphaDen : ℕ) : ℕ := by
  classical
  letI := R.seedFintype
  letI := R.seedDecidableEq
  exact
    (Finset.univ.filter fun seed : R.Seed =>
      (A.response seed).transcript.IsExpander alphaNum alphaDen).card

end RandomizedMatchingPlayerResponse

/-- Theorem 3.5: the cut-matching game can force an expander in
polylogarithmically many rounds with constant probability over the cut
player's randomness, no matter how the matching player responds.

The success-probability denominator `cSuccessDen` encodes a universal lower
bound `1 / cSuccessDen`: for every adaptive matching-player policy, at least
that fraction of random seeds yield an expanding cut-matching multigraph. -/
noncomputable def CutMatchingGameExpanderGuarantee
    (cRounds cRoundsLog cAlpha cSuccessDen : ℕ) : Prop :=
  0 < cRounds ∧ 0 < cRoundsLog ∧ 0 < cAlpha ∧ 0 < cSuccessDen ∧
    ∀ N : ℕ,
      1 < N →
        Even N →
          ∃ rounds : ℕ,
            rounds ≤ cRounds * (Nat.log 2 N) ^ cRoundsLog ∧
              ∃ strategy : RandomizedCutPlayerStrategy.{u} N rounds,
                Nonempty (RandomizedMatchingPlayerResponse.{u} strategy) ∧
                  ∀ response : RandomizedMatchingPlayerResponse.{u} strategy,
                    strategy.seedCount ≤
                      cSuccessDen *
                        response.successSeedCount (Nat.log 2 N) cAlpha




/-! ## Intermediate and final sparsifier statements -/

/-- A bounded-degree minor preserving treewidth up to a polylogarithmic loss. -/
def DegreeBoundedMinorTreewidthSparsifierOmega
    (degree cSparse cSparseLog : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {k : ℕ},
      1 < k →
        k ≤ treewidth G →
          ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
            (H : _root_.SimpleGraph W),
              IsMinor H G ∧
                MaxDegreeAtMost H degree ∧
                  k ≤ cSparse * treewidth H *
                    (Nat.log 2 k) ^ cSparseLog


/-- The proof-facing degree-three output of Theorem 5.1: from a sufficiently
wide strong path-of-sets system of height `height`, construct a degree-three
topological minor in which the first left nail set `A₁` is represented by a
well-linked terminal set.

This removes algorithmic/probabilistic language and keeps the semantic
conclusion used to derive Theorem 1.1.  The paper takes the width to be
`N * r* = Θ(log^3 height)` and assumes the height is even; this contract encodes
that width requirement by a polylogarithmic lower bound. -/
def DegreeThreeWellLinkedMinorFromStrongPathOfSets
    (cWidth cWidthLog cAlpha cAlphaLog : ℕ) : Prop :=
  0 < cWidth ∧ 0 < cWidthLog ∧ 0 < cAlpha ∧ 0 < cAlphaLog ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {height width : ℕ}
      (P : PaperStrongPathOfSetsSystem G width height),
        1 < height →
          Even height →
            cWidth * (Nat.log 2 height) ^ cWidthLog ≤ width →
              let first := P.toPathOfSetsSystem.firstIndex
              ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
                (H : _root_.SimpleGraph W),
                MaxDegreeAtMost H 3 ∧
                  ∃ A : Finset W,
                    A.card = height ∧
                      Nonempty
                        (TerminalRespectingTopologicalMinor
                          H G (P.left first) A) ∧
                        ScaledWellLinked H A
                          1
                          (cAlpha * (Nat.log 2 height) ^ cAlphaLog)


/-- Theorem 1.1 of `treewidth-sparsifier.pdf`, in paper shape and with the
algorithmic and `O(k^4)` vertex-count claims removed.

For every graph `G` of treewidth at least `k`, there is a degree-three
topological minor `H` whose treewidth loses only a polylogarithmic factor:

`k ≤ cSparse * treewidth(H) * log(k)^cSparseLog`.
-/
def DegreeThreeTopologicalTreewidthSparsifierOmega
    (cSparse cSparseLog : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {k : ℕ},
      1 < k →
        k ≤ treewidth G →
          ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
            (H : _root_.SimpleGraph W),
              IsTopologicalMinor H G ∧
                MaxDegreeAtMost H 3 ∧
                  k ≤ cSparse * treewidth H *
                    (Nat.log 2 k) ^ cSparseLog

/-- Threshold form of Theorem 1.1, matching the downstream Appendix A.2 use.

Instead of returning the asymptotic inequality for `k` itself, this states that
any requested target treewidth `t` below `k / polylog(k)` is achieved by a
degree-three topological minor. -/
def DegreeThreeTopologicalTreewidthSparsifierThreshold
    (cSparse cSparseLog : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {k t : ℕ},
      1 < k →
        k ≤ treewidth G →
          cSparse * t * (Nat.log 2 k) ^ cSparseLog < k →
            ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
              (H : _root_.SimpleGraph W),
                IsTopologicalMinor H G ∧
                  MaxDegreeAtMost H 3 ∧
                    t ≤ treewidth H

/-- The threshold form of Theorem 1.1 follows from the paper-internal
Theorem 3.4, Theorem 5.1, and Theorem 3.3 interfaces.

This is the formal version of the proof paragraph at the end of Section 5.2:
construct a strong path-of-sets system with polylogarithmic length, apply
Theorem 5.1 to obtain a degree-three topological minor with a well-linked
terminal set of size `height`, then use Theorem 3.3 to lower-bound the
treewidth of that minor. -/
theorem degreeThreeTopologicalTreewidthSparsifierThreshold_of_strongPath_wellLinkedMinor_treewidth
    (hpathInput :
      ∃ cPath cPathLog : ℕ,
        StrongPathOfSetsFromTreewidth.{u} cPath cPathLog)
    (hminorInput :
      ∃ cWidth cWidthLog cAlpha cAlphaLog : ℕ,
        DegreeThreeWellLinkedMinorFromStrongPathOfSets.{u}
          cWidth cWidthLog cAlpha cAlphaLog)
    (htwInput :
      ∃ cTw : ℕ, 0 < cTw ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) (T : Finset V)
          {Δ alphaNum alphaDen t : ℕ},
            MaxDegreeAtMost G Δ →
              ScaledWellLinked G T alphaNum alphaDen →
                0 < Δ →
                  0 < alphaNum →
                    0 < alphaDen →
                      cTw * Δ * alphaDen * t ≤ alphaNum * T.card →
                        t ≤ treewidth G) :
    ∃ cSparse cSparseLog : ℕ, 0 < cSparse ∧ 0 < cSparseLog ∧
      DegreeThreeTopologicalTreewidthSparsifierThreshold.{u}
        cSparse cSparseLog := by
  rcases hpathInput with
    ⟨cPath, cPathLog, hcPath, hcPathLog, hpath⟩
  rcases hminorInput with
    ⟨cWidth, cWidthLog, cAlpha, cAlphaLog,
      hcWidth, hcWidthLog, hcAlpha, hcAlphaLog, hminor⟩
  rcases htwInput with ⟨cTw, hcTw, htw⟩
  let cHeight := 2 * cTw * 3 * cAlpha
  let cLen := cWidth + 2
  let cSparse := cPath * cHeight * cLen ^ 50
  let cSparseLog := cAlphaLog + cWidthLog * 50 + cPathLog
  refine ⟨cSparse, cSparseLog, ?_, ?_, ?_⟩
  · dsimp [cSparse, cHeight, cLen]
    positivity
  · dsimp [cSparseLog]
    positivity
  intro V _ _ G k t hk hGtw hlarge
  classical
  by_cases htzero : t = 0
  · subst t
    refine ⟨PEmpty, inferInstance, inferInstance, (⊥ : _root_.SimpleGraph PEmpty),
      ?_, ?_, by simp⟩
    · refine ⟨{
        branchVertex := fun x => nomatch x
        branch_injective := by intro x; cases x
        edgeSource := fun e => False.elim (by simpa using e.2)
        edgeTarget := fun e => False.elim (by simpa using e.2)
        edge_adj := by intro e; exact False.elim (by simpa using e.2)
        edge_eq := by intro e; exact False.elim (by simpa using e.2)
        edgePath := fun e => False.elim (by simpa using e.2)
        edgePath_source := by intro e; exact False.elim (by simpa using e.2)
        edgePath_target := by intro e; exact False.elim (by simpa using e.2)
        edgePath_internal_disjoint_branches := by
          intro e
          exact False.elim (by simpa using e.2)
        edgePath_pairwise_internal_disjoint := by
          intro e
          exact False.elim (by simpa using e.2)
      }⟩
    · intro v
      cases v
  · let L := Nat.log 2 k
    let height := cHeight * t * L ^ cAlphaLog
    let width := cLen * L ^ cWidthLog
    have htpos : 0 < t := Nat.pos_of_ne_zero htzero
    have hLpos : 0 < L := by
      simpa [L] using Nat.log_pos (by decide : 1 < 2) (Nat.succ_le_of_lt hk)
    have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
    have hcHeight_pos : 0 < cHeight := by
      dsimp [cHeight]
      positivity
    have hcLen_pos : 0 < cLen := by
      dsimp [cLen]
      omega
    have hheight_gt_one : 1 < height := by
      have hrest :
          0 < cTw * 3 * cAlpha * t * L ^ cAlphaLog := by
        positivity
      have hrest_one :
          1 ≤ cTw * 3 * cAlpha * t * L ^ cAlphaLog :=
        Nat.succ_le_of_lt hrest
      dsimp [height, cHeight]
      calc
        1 < 2 := by norm_num
        _ = 2 * 1 := by norm_num
        _ ≤ 2 * (cTw * 3 * cAlpha * t * L ^ cAlphaLog) :=
          Nat.mul_le_mul_left 2 hrest_one
        _ = 2 * cTw * 3 * cAlpha * t * L ^ cAlphaLog := by ring
    have hwidth_gt_one : 1 < width := by
      have hpow_pos : 0 < L ^ cWidthLog := Nat.pow_pos hLpos
      have hcLen_three : 3 ≤ cLen := by
        dsimp [cLen]
        omega
      calc
        1 < 3 * 1 := by norm_num
        _ ≤ cLen * L ^ cWidthLog :=
          Nat.mul_le_mul hcLen_three (Nat.succ_le_of_lt hpow_pos)
    have hheight_even : Even height := by
      refine ⟨cTw * 3 * cAlpha * t * L ^ cAlphaLog, ?_⟩
      dsimp [height, cHeight]
      ring
    have hSparseLog_ge_alpha : cAlphaLog ≤ cSparseLog := by
      dsimp [cSparseLog]
      omega
    have hpow_alpha_le_sparse :
        L ^ cAlphaLog ≤ L ^ cSparseLog :=
      Nat.pow_le_pow_right hLpos hSparseLog_ge_alpha
    have hcoef_height_le_sparse :
        cHeight * t ≤ cSparse * t := by
      have hfactor_pos : 0 < cPath * cLen ^ 50 :=
        Nat.mul_pos hcPath (Nat.pow_pos hcLen_pos)
      have hfactor_one : 1 ≤ cPath * cLen ^ 50 :=
        Nat.succ_le_of_lt hfactor_pos
      calc
        cHeight * t = (cHeight * 1) * t := by ring
        _ ≤ (cHeight * (cPath * cLen ^ 50)) * t :=
          Nat.mul_le_mul_right t (Nat.mul_le_mul_left cHeight hfactor_one)
        _ = cSparse * t := by
          dsimp [cSparse]
          ring
    have hheight_le_sparse :
        height ≤ cSparse * t * L ^ cSparseLog := by
      dsimp [height]
      exact Nat.mul_le_mul hcoef_height_le_sparse hpow_alpha_le_sparse
    have hheight_le_k : height ≤ k :=
      hheight_le_sparse.trans (Nat.le_of_lt (by simpa [L, cSparseLog] using hlarge))
    have hlog_height_le : Nat.log 2 height ≤ L := by
      simpa [L] using Nat.log_mono_right hheight_le_k
    have hwidth_req :
        cWidth * (Nat.log 2 height) ^ cWidthLog ≤ width := by
      have hpow :
          (Nat.log 2 height) ^ cWidthLog ≤ L ^ cWidthLog :=
        Nat.pow_le_pow_left hlog_height_le cWidthLog
      calc
        cWidth * (Nat.log 2 height) ^ cWidthLog
            ≤ cWidth * L ^ cWidthLog := Nat.mul_le_mul_left cWidth hpow
        _ ≤ cLen * L ^ cWidthLog := by
          exact Nat.mul_le_mul_right (L ^ cWidthLog) (by dsimp [cLen]; omega)
        _ = width := by rfl
    have hpath_le_sparse :
        cPath * height * width ^ 50 * L ^ cPathLog ≤
          cSparse * t * L ^ cSparseLog := by
      dsimp [height, width, cSparse, cSparseLog]
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add, Nat.pow_add]
      ring_nf
      exact le_rfl
    have hpath_large :
        cPath * height * width ^ 50 * L ^ cPathLog < k :=
      lt_of_le_of_lt hpath_le_sparse (by simpa [L, cSparseLog] using hlarge)
    rcases hpath G (k := k) (height := height) (width := width)
        hk hheight_gt_one hwidth_gt_one hGtw hpath_large with ⟨P⟩
    rcases hminor G P hheight_gt_one hheight_even hwidth_req with
      ⟨W, instW, instDecW, H, hdegree, A, hAcard, htopRespect, hwell⟩
    letI : Fintype W := instW
    letI : DecidableEq W := instDecW
    have hlog_height_pos : 0 < Nat.log 2 height := by
      exact Nat.log_pos (by decide : 1 < 2)
        (Nat.succ_le_of_lt hheight_gt_one)
    have halphaDen_pos :
        0 < cAlpha * (Nat.log 2 height) ^ cAlphaLog := by
      positivity
    have hpow_alpha_height :
        (Nat.log 2 height) ^ cAlphaLog ≤ L ^ cAlphaLog :=
      Nat.pow_le_pow_left hlog_height_le cAlphaLog
    have htw_condition :
        cTw * 3 * (cAlpha * (Nat.log 2 height) ^ cAlphaLog) * t ≤
          1 * A.card := by
      have hle_height :
          cTw * 3 * (cAlpha * (Nat.log 2 height) ^ cAlphaLog) * t ≤
            height := by
        calc
          cTw * 3 * (cAlpha * (Nat.log 2 height) ^ cAlphaLog) * t
              ≤ cTw * 3 * (cAlpha * L ^ cAlphaLog) * t := by
                exact Nat.mul_le_mul_right t
                  (Nat.mul_le_mul_left (cTw * 3)
                    (Nat.mul_le_mul_left cAlpha hpow_alpha_height))
          _ = cTw * 3 * cAlpha * t * L ^ cAlphaLog := by ring
          _ ≤ 2 * (cTw * 3 * cAlpha * t * L ^ cAlphaLog) := by
            calc
              cTw * 3 * cAlpha * t * L ^ cAlphaLog =
                  1 * (cTw * 3 * cAlpha * t * L ^ cAlphaLog) := by simp
              _ ≤ 2 * (cTw * 3 * cAlpha * t * L ^ cAlphaLog) :=
                Nat.mul_le_mul_right _ (by decide : 1 ≤ 2)
          _ = height := by
            dsimp [height, cHeight]
            ring
      simpa [hAcard] using hle_height
    have ht_treewidth : t ≤ treewidth H :=
      htw H A hdegree hwell (by decide : 0 < 3) (by decide : 0 < 1)
        halphaDen_pos htw_condition
    rcases htopRespect with ⟨M⟩
    exact ⟨W, instW, instDecW, H, ⟨M.model⟩, hdegree, ht_treewidth⟩


end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
