import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Truncating a perfect packing at the first hit of a region

Chekuri--Chuzhoy Theorem 4.6 repeatedly directs root-to-leaf paths from a
leaf toward an ancestor cluster and keeps only the prefix through the first
vertex of that cluster.  This module packages that operation for a whole
perfect packing.
-/

namespace SimpleGraph
namespace PerfectPathPacking


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {S T C : Finset V}

/-- A perfect `S`-to-`T` packing, with `T ⊆ C`, truncated at the first hit of
`C`.  The left terminals and number of paths are unchanged; the new right
terminals are the distinct first-hit vertices in `C`. -/
structure FirstHitData (P : PerfectPathPacking G S T) (C : Finset V) where
  hit : Finset V
  hit_subset : hit ⊆ C
  packing : PerfectPathPacking G S hit
  packing_card : packing.card = P.card
  packing_internallyDisjoint :
    packing.toPathPacking.InternallyDisjointFromSet C
  path_vertexSet_subset :
    ∀ i : packing.Index,
      ∃ j : P.Index,
        (packing.path i).vertexSet ⊆ (P.path j).vertexSet

/-- Construct the first-hit truncation data. -/
theorem exists_firstHitData
    (P : PerfectPathPacking G S T) (hT : T ⊆ C) :
    Nonempty (FirstHitData P C) := by
  classical
  let widened : PathPacking G S C := {
    Index := P.Index
    path := P.path
    connects := by
      intro i
      exact Or.inl ⟨P.source_mem i, hT (P.target_mem i)⟩
    node_disjoint := P.node_disjoint }
  let cleaned : PathPacking G S C := widened.cleanToRight
  have hcleanedCard : cleaned.card = P.card := by
    rfl
  have hsourceSet : cleaned.sourceSet = S := by
    apply cleaned.sourceSet_eq_left_of_card_eq
    calc
      cleaned.card = P.card := hcleanedCard
      _ = S.card := P.card_eq_left_card
  let raw := cleaned.toPerfectUsedTerminals
  let hit : Finset V := cleaned.targetSet
  let Q : PerfectPathPacking G S hit :=
    raw.copyTerminals hsourceSet (by rfl)
  have hQcard : Q.card = P.card := by
    calc
      Q.card = raw.card := PerfectPathPacking.copyTerminals_card _ _ _
      _ = cleaned.card := PathPacking.toPerfectUsedTerminals_card cleaned
      _ = P.card := hcleanedCard
  exact ⟨{
    hit := hit
    hit_subset := by
      exact cleaned.targetSet_subset_right
    packing := Q
    packing_card := hQcard
    packing_internallyDisjoint := by
      intro i v hv hvC
      have hcleaned :
          cleaned.InternallyDisjointFromSet C := by
        simpa [cleaned] using widened.cleanToRight_internallyDisjointFromSet
      have hraw :=
        PathPacking.toPerfectUsedTerminals_internallyDisjointFromSet
          cleaned hcleaned
      simpa [Q, raw, PerfectPathPacking.copyTerminals] using
        hraw i hv hvC
    path_vertexSet_subset := by
      intro i
      refine ⟨i, ?_⟩
      change
        ((cleaned.toPerfectUsedTerminals.path i).vertexSet ⊆
          (P.path i).vertexSet)
      intro v hv
      have hvCleaned : v ∈ (cleaned.path i).vertexSet := by
        simpa [PathPacking.toPerfectUsedTerminals,
          PathPacking.orient_path_vertexSet] using hv
      exact widened.cleanToRight_path_vertexSet_subset i hvCleaned }⟩

/-! ## Simultaneous first-hit prefix and suffix -/

/-- Split every path of a perfect packing at its first hit of `C`.

The prefix and suffix use the same index type and meet at the same first-hit
vertex.  This is the formal version of the `v_Q` split in Step 2 of
Chekuri--Chuzhoy Theorem 4.6. -/
structure FirstHitSplitData
    (P : PerfectPathPacking G S T) (C : Finset V) where
  hit : Finset V
  hit_subset : hit ⊆ C
  initial : PerfectPathPacking G S hit
  terminal : PerfectPathPacking G hit T
  initial_card : initial.card = P.card
  terminal_card : terminal.card = P.card
  initial_internallyDisjoint :
    initial.toPathPacking.InternallyDisjointFromSet C
  initialOriginal : initial.Index → P.Index
  terminalOriginal : terminal.Index → P.Index
  initial_path_vertexSet_subset :
    ∀ i : initial.Index,
      (initial.path i).vertexSet ⊆ (P.path (initialOriginal i)).vertexSet
  terminal_path_vertexSet_subset :
    ∀ i : terminal.Index,
      (terminal.path i).vertexSet ⊆ (P.path (terminalOriginal i)).vertexSet

/-- Construct the simultaneous first-hit prefix/suffix split. -/
theorem exists_firstHitSplitData
    (P : PerfectPathPacking G S T) (hT : T ⊆ C) :
    Nonempty (FirstHitSplitData P C) := by
  classical
  let meets : ∀ i : P.Index, ((P.path i).vertexSet ∩ C).Nonempty :=
    fun i =>
      ⟨(P.path i).target,
        Finset.mem_inter.2
          ⟨GraphPath.target_mem_vertexSet (P.path i),
            hT (P.target_mem i)⟩⟩
  let first : P.Index → V :=
    fun i => (P.path i).firstHitVertex C (meets i)
  let hit : Finset V := Finset.univ.image first
  have hfirst_mem : ∀ i, first i ∈ C := by
    intro i
    exact (P.path i).firstHitVertex_mem_set C (meets i)
  have hfirst_injective : Function.Injective first := by
    intro i j hij
    by_contra hne
    have hi :
        first i ∈ (P.path i).vertexSet :=
      (P.path i).firstHitVertex_mem_vertexSet C (meets i)
    have hj :
        first j ∈ (P.path j).vertexSet :=
      (P.path j).firstHitVertex_mem_vertexSet C (meets j)
    exact Finset.disjoint_left.mp (P.node_disjoint hne)
      hi (by simpa [hij] using hj)
  let initial : PerfectPathPacking G S hit := {
    Index := P.Index
    path := fun i => (P.path i).cleanPrefixToSet C (meets i)
    connects := by
      intro i
      exact Or.inl
        ⟨by simpa [first] using P.source_mem i,
          Finset.mem_image.mpr ⟨i, by simp, by simp [first]⟩⟩
    node_disjoint := by
      intro i j hij
      exact (P.node_disjoint hij).mono
        ((P.path i).cleanPrefixToSet_vertexSet_subset C (meets i))
        ((P.path j).cleanPrefixToSet_vertexSet_subset C (meets j))
    source_mem := by
      intro i
      simpa [first] using P.source_mem i
    target_mem := by
      intro i
      exact Finset.mem_image.mpr ⟨i, by simp, by simp [first]⟩
    source_bijective := by
      simpa [first] using P.source_bijective
    target_bijective := by
      constructor
      · intro i j hij
        apply hfirst_injective
        exact congrArg Subtype.val hij
      · intro x
        rcases Finset.mem_image.mp x.2 with ⟨i, _hi, hx⟩
        refine ⟨i, Subtype.ext ?_⟩
        simpa [first] using hx }
  let terminal : PerfectPathPacking G hit T := {
    Index := P.Index
    path := fun i =>
      (P.path i).dropUntil
        ((P.path i).firstHitVertex_mem_vertexSet C (meets i))
    connects := by
      intro i
      exact Or.inl
        ⟨Finset.mem_image.mpr ⟨i, by simp, by simp [first]⟩,
          by simpa using P.target_mem i⟩
    node_disjoint := by
      intro i j hij
      exact (P.node_disjoint hij).mono
        ((P.path i).dropUntil_vertexSet_subset
          ((P.path i).firstHitVertex_mem_vertexSet C (meets i)))
        ((P.path j).dropUntil_vertexSet_subset
          ((P.path j).firstHitVertex_mem_vertexSet C (meets j)))
    source_mem := by
      intro i
      exact Finset.mem_image.mpr ⟨i, by simp, by simp [first]⟩
    target_mem := by
      intro i
      simpa using P.target_mem i
    source_bijective := by
      constructor
      · intro i j hij
        apply hfirst_injective
        exact congrArg Subtype.val hij
      · intro x
        rcases Finset.mem_image.mp x.2 with ⟨i, _hi, hx⟩
        refine ⟨i, Subtype.ext ?_⟩
        simpa [first] using hx
    target_bijective := by
      simpa [first] using P.target_bijective }
  exact ⟨{
    hit := hit
    hit_subset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      exact hfirst_mem i
    initial := initial
    terminal := terminal
    initial_card := rfl
    terminal_card := rfl
    initial_internallyDisjoint := by
      intro i
      exact (P.path i).cleanPrefixToSet_internallyDisjointFromSet C (meets i)
    initialOriginal := fun i => i
    terminalOriginal := fun i => i
    initial_path_vertexSet_subset := by
      intro i
      exact (P.path i).cleanPrefixToSet_vertexSet_subset C (meets i)
    terminal_path_vertexSet_subset := by
      intro i
      exact (P.path i).dropUntil_vertexSet_subset
        ((P.path i).firstHitVertex_mem_vertexSet C (meets i)) }⟩

end PerfectPathPacking
end SimpleGraph

end Lax17Proofs
