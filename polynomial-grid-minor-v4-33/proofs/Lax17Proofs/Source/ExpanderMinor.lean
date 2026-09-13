import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Tactic
import Lax17Proofs.Source.Degree
import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.MinorTransitivity
import Lax17Proofs.Source.Separator

namespace Lax17Proofs

universe u v w

/-!
# Separator/minor alternative from expander-minor universality

This file formalizes the finite objects that occur in Theorem 8.1 of
`expander.pdf` ("Expanders -- how to find them, and what to find in them").

The paper states the theorem with a real parameter `α > 0` and a bound
`O(n / log n)` on the number of vertices and edges of the target graph.  The
Lean interface below uses the project convention of natural-number scales:

* `separatorScale = D` means a separator of size at most `|V(G)| / D`;
* `targetScale = C` means
  `C * (|V(H)| + |E(H)|) * log₂ |V(G)| ≤ |V(G)|`.

The paper uses "separator" for the usual balanced separator.  Accordingly, the
public theorem below returns `HasSmallBalancedSeparator`; the unbalanced
`VertexSeparator` structure is only an internal bookkeeping object used to
assemble the balanced separator at the first crossing of the algorithm.
-/

namespace SimpleGraph


/-- A three-part, not-necessarily-balanced vertex separator: `A`, `B`, and `S`
cover the vertex set,
`A` and `B` are disjoint from each other and from `S`, and no edge joins `A`
to `B`.

This is intentionally weaker than the paper's separator convention.  Theorem
8.1 uses balanced separators; this structure exists only so that relative
external-neighborhood calculations can be oriented before the balance
inequalities are available. -/
structure VertexSeparator {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (A B S : Finset V) : Prop where
  /-- The three parts cover all vertices. -/
  cover : A ∪ B ∪ S = Finset.univ
  /-- The two sides are disjoint. -/
  disjoint_left_right : Disjoint A B
  /-- The left side avoids the separator. -/
  disjoint_left_separator : Disjoint A S
  /-- The right side avoids the separator. -/
  disjoint_right_separator : Disjoint B S
  /-- There is no graph edge between the two sides. -/
  no_edge_left_right : ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ¬ G.Adj a b

/-- A graph has a separator of size at most `|V| / separatorScale`, encoded
without division as `separatorScale * |S| ≤ |V|`. -/
def HasSmallSeparator {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (separatorScale : ℕ) : Prop :=
  ∃ A B S : Finset V,
    VertexSeparator G A B S ∧ separatorScale * S.card ≤ Fintype.card V

/-- Existing balanced-separator version of `HasSmallSeparator`. -/
def HasSmallBalancedSeparator {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (separatorScale : ℕ) : Prop :=
  ∃ A B S : Finset V,
    BalancedSeparator G A B S ∧ separatorScale * S.card ≤ Fintype.card V

/-- The target-size complexity in Theorem 8.1: vertices plus edges. -/
noncomputable def targetComplexity {W : Type v} [Fintype W]
    (H : _root_.SimpleGraph W) [Fintype H.edgeSet] : ℕ :=
  Fintype.card W + H.edgeFinset.card

/-- Target-size hypothesis corresponding to `O(n / log n)`.

The constant is represented as a denominator: larger `targetScale` gives a
smaller admissible target graph. -/
def TargetSmallForHost {V : Type u} [Fintype V]
    {W : Type v} [Fintype W]
    (H : _root_.SimpleGraph W) [Fintype H.edgeSet]
    (targetScale : ℕ) : Prop :=
  targetScale * targetComplexity H * Nat.log 2 (Fintype.card V) ≤
    Fintype.card V

/-- The finite natural-number-scale form of Theorem 8.1 at fixed constants.

The separator alternative is stated using the repository's balanced-separator
interface from Definition 5.1 of `expander.pdf`: after orienting the smaller
side first, the larger side has size at most `2|V|/3`. -/
def ExpanderMinorTheoremAt (separatorScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet],
      n₀ ≤ Fintype.card V →
        TargetSmallForHost (V := V) H targetScale →
          HasSmallBalancedSeparator G separatorScale ∨ IsMinor H G

/-- The no-small-balanced-separator branch of Theorem 8.1 at fixed constants.

This is the form in which separator/minor technology is usually used: if the
host has no balanced separator of size `|V| / separatorScale` and the target
graph is small enough, then the target is a minor of the host. -/
def MinorUniversalNoSmallSeparatorAt
    (separatorScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet],
      n₀ ≤ Fintype.card V →
        TargetSmallForHost (V := V) H targetScale →
          ¬ HasSmallBalancedSeparator G separatorScale →
            IsMinor H G

/-- The theorem-family statement: for each positive separator scale, some
positive target denominator and threshold make the separator/minor alternative
hold. -/
def ExpanderMinorTheorem : Prop :=
  ∀ separatorScale : ℕ, 0 < separatorScale →
    ∃ targetScale n₀ : ℕ,
      0 < targetScale ∧ ExpanderMinorTheoremAt.{u, v}
        separatorScale targetScale n₀

/-- Already embedded neighbors of a target vertex.  In the proof of
Theorem 8.1, when the target has maximum degree at most three, this finset has
cardinality at most three. -/
noncomputable def activeNeighborFinset {W : Type u}
    [DecidableEq W]
    (H : _root_.SimpleGraph W) [DecidableRel H.Adj]
    (I : Finset W) (i : W) : Finset W :=
  I.filter fun j => H.Adj i j

@[simp] theorem mem_activeNeighborFinset {W : Type u}
    [DecidableEq W]
    {H : _root_.SimpleGraph W} [DecidableRel H.Adj]
    {I : Finset W} {i j : W} :
    j ∈ activeNeighborFinset H I i ↔ j ∈ I ∧ H.Adj i j := by
  simp [activeNeighborFinset]

/-- The active-neighbor set is bounded by the degree bound of the target
vertex. -/
theorem activeNeighborFinset_card_le_degreeAtMost {W : Type u}
    [DecidableEq W]
    {H : _root_.SimpleGraph W} [DecidableRel H.Adj]
    {I : Finset W} {i : W} {d : ℕ}
    (hdeg : DegreeAtMost H i d) :
    (activeNeighborFinset H I i).card ≤ d := by
  rcases hdeg with ⟨N, hN, hNcard⟩
  have hsubset : activeNeighborFinset H I i ⊆ N := by
    intro j hj
    exact (hN j).2 ((mem_activeNeighborFinset.1 hj).2)
  exact (Finset.card_le_card hsubset).trans hNcard

/-- If the target graph has maximum degree at most `d`, then every active
neighbor set has size at most `d`. -/
theorem activeNeighborFinset_card_le_maxDegreeAtMost {W : Type u}
    [DecidableEq W]
    {H : _root_.SimpleGraph W} [DecidableRel H.Adj]
    {I : Finset W} {i : W} {d : ℕ}
    (hmax : MaxDegreeAtMost H d) :
    (activeNeighborFinset H I i).card ≤ d :=
  activeNeighborFinset_card_le_degreeAtMost (hmax i)

/-- Subcubic target graphs have at most three active neighbors at every step of
the embedding algorithm. -/
theorem activeNeighborFinset_card_le_three_of_subcubic {W : Type u}
    [DecidableEq W]
    {H : _root_.SimpleGraph W} [DecidableRel H.Adj]
    {I : Finset W} {i : W}
    (hmax : MaxDegreeAtMost H 3) :
    (activeNeighborFinset H I i).card ≤ 3 :=
  activeNeighborFinset_card_le_maxDegreeAtMost hmax

@[simp] theorem activeNeighborFinset_eq_empty_iff {W : Type u}
    [DecidableEq W]
    {H : _root_.SimpleGraph W} [DecidableRel H.Adj]
    {I : Finset W} {i : W} :
    activeNeighborFinset H I i = ∅ ↔
      ∀ j : W, j ∈ I → ¬ H.Adj i j := by
  classical
  constructor
  · intro h j hj hij
    have : j ∈ activeNeighborFinset H I i :=
      (mem_activeNeighborFinset).2 ⟨hj, hij⟩
    simp [h] at this
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.2
    intro j hj
    rcases (mem_activeNeighborFinset).1 hj with ⟨hjI, hij⟩
    exact h j hjI hij

/-- `S` is the external neighborhood of `A`: it consists exactly of vertices
outside `A` adjacent to at least one vertex of `A`. -/
def IsExternalNeighborhood {V : Type u}
    (G : _root_.SimpleGraph V) (A S : Finset V) : Prop :=
  ∀ v : V, v ∈ S ↔ v ∉ A ∧ ∃ a ∈ A, G.Adj v a

/-- The external neighborhood of a finite vertex set, as a finset. -/
noncomputable def externalNeighborhood {V : Type u}
    [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∉ A ∧ ∃ a ∈ A, G.Adj v a

@[simp] theorem mem_externalNeighborhood {V : Type u}
    [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {v : V} :
    v ∈ externalNeighborhood G A ↔
      v ∉ A ∧ ∃ a ∈ A, G.Adj v a := by
  simp [externalNeighborhood]

/-- The concrete finset `externalNeighborhood` satisfies the relational
specification. -/
theorem isExternalNeighborhood_externalNeighborhood {V : Type u}
    [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    IsExternalNeighborhood G A (externalNeighborhood G A) := by
  intro v
  simp

/-- `S` is the external neighborhood of `A` inside the reservoir `C`.

When `A` and `C` are disjoint this is exactly the paper notation
`N_G(A,C)`: the subset of vertices of `C` that have a neighbor in `A`.
The explicit `v ∉ A` conjunct is harmless in the algorithm, where the reservoir
is disjoint from the side being expanded, and is useful for general monotonicity
lemmas. -/
def IsRelativeExternalNeighborhood {V : Type u}
    (G : _root_.SimpleGraph V) (A C S : Finset V) : Prop :=
  ∀ v : V, v ∈ S ↔ v ∈ C ∧ v ∉ A ∧ ∃ a ∈ A, G.Adj v a

/-- The external neighborhood of `A` restricted to a finite reservoir `C`. -/
noncomputable def relativeExternalNeighborhood {V : Type u}
    [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) : Finset V :=
  C.filter fun v => v ∉ A ∧ ∃ a ∈ A, G.Adj v a

@[simp] theorem mem_relativeExternalNeighborhood {V : Type u}
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {v : V} :
    v ∈ relativeExternalNeighborhood G A C ↔
      v ∈ C ∧ v ∉ A ∧ ∃ a ∈ A, G.Adj v a := by
  simp [relativeExternalNeighborhood]

/-- The concrete finset `relativeExternalNeighborhood` satisfies the relational
specification. -/
theorem isRelativeExternalNeighborhood_relativeExternalNeighborhood
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) :
    IsRelativeExternalNeighborhood G A C
      (relativeExternalNeighborhood G A C) := by
  intro v
  simp

/-- Paper-facing membership form for `N_G(A,C)`: when `A` and `C` are
disjoint, the relative external neighborhood is the subset of `C` consisting of
vertices with a neighbor in `A`.  This is the convention used in Definition 5.1
and Theorem 8.1 of `expander.pdf`. -/
theorem mem_relativeExternalNeighborhood_iff_neighbor_left
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} (hAC : Disjoint A C) {v : V} :
    v ∈ relativeExternalNeighborhood G A C ↔
      v ∈ C ∧ ∃ a ∈ A, G.Adj a v := by
  rw [mem_relativeExternalNeighborhood]
  constructor
  · rintro ⟨hvC, _hvA, a, haA, hva⟩
    exact ⟨hvC, a, haA, hva.symm⟩
  · rintro ⟨hvC, a, haA, hav⟩
    exact ⟨hvC, fun hvA => Finset.disjoint_left.mp hAC hvA hvC,
      a, haA, hav.symm⟩

namespace IsExternalNeighborhood

variable {V : Type u} {G : _root_.SimpleGraph V} {A S : Finset V}

/-- The external neighborhood is disjoint from the set it expands. -/
theorem disjoint (hS : IsExternalNeighborhood G A S) :
    Disjoint A S := by
  rw [Finset.disjoint_left]
  intro v hvA hvS
  exact (hS v).1 hvS |>.1 hvA

/-- If a vertex is outside `A` but adjacent to `A`, then it lies in the
external neighborhood. -/
theorem mem_of_adj {v a : V} (hS : IsExternalNeighborhood G A S)
    (hvA : v ∉ A) (ha : a ∈ A) (hva : G.Adj v a) :
    v ∈ S :=
  (hS v).2 ⟨hvA, a, ha, hva⟩

end IsExternalNeighborhood

namespace IsRelativeExternalNeighborhood

variable {V : Type u} {G : _root_.SimpleGraph V}
variable {A C S : Finset V}

/-- A relative external neighborhood is contained in its reservoir. -/
theorem subset_reservoir (hS : IsRelativeExternalNeighborhood G A C S) :
    S ⊆ C := by
  intro v hv
  exact ((hS v).1 hv).1

/-- A relative external neighborhood is disjoint from the set it expands. -/
theorem disjoint_left (hS : IsRelativeExternalNeighborhood G A C S) :
    Disjoint A S := by
  rw [Finset.disjoint_left]
  intro v hvA hvS
  exact ((hS v).1 hvS).2.1 hvA

/-- If a reservoir vertex outside `A` is adjacent to `A`, then it lies in the
relative external neighborhood. -/
theorem mem_of_adj {v a : V} (hS : IsRelativeExternalNeighborhood G A C S)
    (hvC : v ∈ C) (hvA : v ∉ A) (ha : a ∈ A) (hva : G.Adj v a) :
    v ∈ S :=
  (hS v).2 ⟨hvC, hvA, a, ha, hva⟩

/-- Relational version of the paper-facing `N_G(A,C)` convention: if `A` and
`C` are disjoint, then `S` is the relative external neighborhood exactly when
it contains the vertices of `C` with a neighbor in `A`. -/
theorem iff_neighbor_left
    (hAC : Disjoint A C) :
    IsRelativeExternalNeighborhood G A C S ↔
      ∀ v : V, v ∈ S ↔ v ∈ C ∧ ∃ a ∈ A, G.Adj a v := by
  constructor
  · intro hS v
    rw [hS v]
    constructor
    · rintro ⟨hvC, _hvA, a, haA, hva⟩
      exact ⟨hvC, a, haA, hva.symm⟩
    · rintro ⟨hvC, a, haA, hav⟩
      exact ⟨hvC, fun hvA => Finset.disjoint_left.mp hAC hvA hvC,
        a, haA, hav.symm⟩
  · intro hS v
    rw [hS v]
    constructor
    · rintro ⟨hvC, a, haA, hav⟩
      exact ⟨hvC, fun hvA => Finset.disjoint_left.mp hAC hvA hvC,
        a, haA, hav.symm⟩
    · rintro ⟨hvC, _hvA, a, haA, hva⟩
      exact ⟨hvC, a, haA, hva.symm⟩

/-- Adding a set `X` to the expanded side does not change the relative
external neighborhood inside `C` when `X` is disjoint from `C` and has no edge
to `C`. -/
theorem union_right_of_no_reservoir_neighbor
    [DecidableEq V]
    {X : Finset V}
    (hS : IsRelativeExternalNeighborhood G A C S)
    (hXC : Disjoint X C)
    (hno : ∀ ⦃x c : V⦄, x ∈ X → c ∈ C → ¬ G.Adj c x) :
    IsRelativeExternalNeighborhood G (A ∪ X) C S := by
  intro v
  constructor
  · intro hvS
    rcases (hS v).1 hvS with ⟨hvC, hvA, a, ha, hva⟩
    refine ⟨hvC, ?_, a, ?_, hva⟩
    · rw [Finset.mem_union]
      exact fun hvAX => hvAX.elim hvA
        (fun hvX => Finset.disjoint_left.mp hXC hvX hvC)
    · exact Finset.mem_union_left X ha
  · intro hv
    rcases hv with ⟨hvC, hvAX, a, haAX, hva⟩
    rw [Finset.mem_union] at haAX
    rw [Finset.mem_union] at hvAX
    rcases haAX with haA | haX
    · exact (hS v).2 ⟨hvC, fun hvA => hvAX (Or.inl hvA),
        a, haA, hva⟩
    · exact False.elim (hno haX hvC hva)

/-- If the expanded side grows from `A` to `A ∪ U` while the reservoir shrinks
from `C` to `C \ U`, then the new relative frontier is contained in the union
of the old frontier of `A` and the frontier of `U` inside `C \ U`. -/
theorem subset_union_of_union_left
    [DecidableEq V]
    {U FOld FU FNew : Finset V}
    (hOld : IsRelativeExternalNeighborhood G A C FOld)
    (hU : IsRelativeExternalNeighborhood G U (C \ U) FU)
    (hNew : IsRelativeExternalNeighborhood G (A ∪ U) (C \ U) FNew) :
    FNew ⊆ FOld ∪ FU := by
  intro v hvNew
  rcases (hNew v).1 hvNew with ⟨hvCU, hvAU, a, haAU, hva⟩
  rcases Finset.mem_sdiff.mp hvCU with ⟨hvC, hvnotU⟩
  rw [Finset.mem_union] at haAU
  rw [Finset.mem_union]
  rcases haAU with haA | haU
  · left
    exact (hOld v).2 ⟨hvC, fun hvA => hvAU (Finset.mem_union_left U hvA),
      a, haA, hva⟩
  · right
    exact (hU v).2 ⟨hvCU, hvnotU, a, haU, hva⟩

/-- Shrinking the reservoir can only shrink the relative external
neighborhood. -/
theorem subset_of_reservoir_subset
    {C' S' : Finset V}
    (hOld : IsRelativeExternalNeighborhood G A C S)
    (hNew : IsRelativeExternalNeighborhood G A C' S')
    (hC' : C' ⊆ C) :
    S' ⊆ S := by
  intro v hv
  rcases (hNew v).1 hv with ⟨hvC', hvA, a, ha, hva⟩
  exact (hOld v).2 ⟨hC' hvC', hvA, a, ha, hva⟩

end IsRelativeExternalNeighborhood

namespace VertexSeparator

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A S : Finset V}

/-- The side remaining after deleting `A` and its separator. -/
def remainder (A S : Finset V) : Finset V :=
  Finset.univ \ (A ∪ S)

@[simp] theorem mem_remainder {v : V} :
    v ∈ remainder A S ↔ v ∉ A ∧ v ∉ S := by
  simp [remainder]

/-- The external neighborhood of `A` separates `A` from the remaining vertices. -/
theorem of_externalNeighborhood (hS : IsExternalNeighborhood G A S) :
    VertexSeparator G A (remainder A S) S := by
  classical
  refine {
    cover := ?_
    disjoint_left_right := ?_
    disjoint_left_separator := hS.disjoint
    disjoint_right_separator := ?_
    no_edge_left_right := ?_
  }
  · ext v
    by_cases hvA : v ∈ A
    · simp [remainder, hvA]
    · by_cases hvS : v ∈ S
      · simp [remainder, hvA, hvS]
      · simp [remainder, hvA, hvS]
  · rw [Finset.disjoint_left]
    intro v hvA hvB
    exact (mem_remainder.1 hvB).1 hvA
  · rw [Finset.disjoint_left]
    intro v hvB hvS
    exact (mem_remainder.1 hvB).2 hvS
  · intro a b ha hb hab
    have hbA : b ∉ A := (mem_remainder.1 hb).1
    have hbS : b ∉ S := (mem_remainder.1 hb).2
    exact hbS (hS.mem_of_adj hbA ha hab.symm)

/-- If `A`, `B`, and `C` partition the host vertices and `S` is the
neighborhood of `A` inside `C`, then `B ∪ S` separates `A` from the part of
`C` not adjacent to `A`. This is the separator produced when the Theorem 8.1
algorithm stops with a medium-sized `A`. -/
theorem of_relativeExternalNeighborhood_partition
    {B C S : Finset V}
    (hcover : A ∪ B ∪ C = Finset.univ)
    (hAB : Disjoint A B)
    (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hS : IsRelativeExternalNeighborhood G A C S) :
    VertexSeparator G A (C \ S) (B ∪ S) := by
  classical
  refine {
    cover := ?_
    disjoint_left_right := ?_
    disjoint_left_separator := ?_
    disjoint_right_separator := ?_
    no_edge_left_right := ?_
  }
  · ext v
    constructor
    · intro _hv
      simp
    · intro _hv
      have hvABC : v ∈ A ∪ B ∪ C := by
        simp [hcover]
      rw [Finset.mem_union, Finset.mem_union] at hvABC
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_union]
      rcases hvABC with hvAB | hvC
      · rcases hvAB with hvA | hvB
        · exact Or.inl (Or.inl hvA)
        · exact Or.inr (Or.inl hvB)
      · by_cases hvS : v ∈ S
        · exact Or.inr (Or.inr hvS)
        · exact Or.inl (Or.inr ⟨hvC, hvS⟩)
  · rw [Finset.disjoint_left]
    intro v hvA hvC
    exact Finset.disjoint_left.mp hAC hvA (Finset.mem_sdiff.mp hvC).1
  · rw [Finset.disjoint_left]
    intro v hvA hvSep
    rw [Finset.mem_union] at hvSep
    rcases hvSep with hvB | hvS
    · exact Finset.disjoint_left.mp hAB hvA hvB
    · exact ((hS v).1 hvS).2.1 hvA
  · rw [Finset.disjoint_left]
    intro v hvC hvSep
    rw [Finset.mem_union] at hvSep
    rcases hvSep with hvB | hvS
    · exact Finset.disjoint_left.mp hBC hvB (Finset.mem_sdiff.mp hvC).1
    · exact (Finset.mem_sdiff.mp hvC).2 hvS
  · intro a c ha hc hac
    have hcC : c ∈ C := (Finset.mem_sdiff.mp hc).1
    have hcS : c ∉ S := (Finset.mem_sdiff.mp hc).2
    have hcA : c ∉ A := by
      exact fun hcA => Finset.disjoint_left.mp hAC hcA hcC
    exact hcS (hS.mem_of_adj hcC hcA ha hac.symm)

/-- A vertex separator whose sides are balanced in the orientation used by
`BalancedSeparator` gives the existing balanced-separator object. -/
theorem toBalanced
    {B : Finset V} (h : VertexSeparator G A B S)
    (hAleB : A.card ≤ B.card)
    (hBbal : 3 * B.card ≤ 2 * Fintype.card V) :
    BalancedSeparator G A B S where
  cover := h.cover
  disjoint_left_right := h.disjoint_left_right
  disjoint_left_separator := h.disjoint_left_separator
  disjoint_right_separator := h.disjoint_right_separator
  left_card_le_right_card := hAleB
  right_balanced := hBbal
  no_edge_left_right := h.no_edge_left_right

/-- A vertex separator whose sides are balanced after swapping also gives a
`BalancedSeparator`. -/
theorem toBalanced_swap
    {B : Finset V} (h : VertexSeparator G A B S)
    (hBleA : B.card ≤ A.card)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V) :
    BalancedSeparator G B A S where
  cover := by
    simpa [Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using
      h.cover
  disjoint_left_right := h.disjoint_left_right.symm
  disjoint_left_separator := h.disjoint_right_separator
  disjoint_right_separator := h.disjoint_left_separator
  left_card_le_right_card := hBleA
  right_balanced := hAbal
  no_edge_left_right := by
    intro b a hb ha hba
    exact h.no_edge_left_right ha hb hba.symm

end VertexSeparator

namespace HasSmallSeparator

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A separator remains small when the requested scale is weakened. -/
theorem mono_scale {d e : ℕ} (hG : HasSmallSeparator G d) (hed : e ≤ d) :
    HasSmallSeparator G e := by
  rcases hG with ⟨A, B, S, hsep, hsmall⟩
  refine ⟨A, B, S, hsep, ?_⟩
  exact (Nat.mul_le_mul_right S.card hed).trans hsmall

/-- An external-neighborhood separator is small when its frontier is small. -/
theorem of_externalNeighborhood {A S : Finset V} {d : ℕ}
    (hS : IsExternalNeighborhood G A S)
    (hsmall : d * S.card ≤ Fintype.card V) :
    HasSmallSeparator G d :=
  ⟨A, VertexSeparator.remainder A S, S,
    VertexSeparator.of_externalNeighborhood hS, hsmall⟩

/-- Concrete external-neighborhood version of `of_externalNeighborhood`. -/
theorem of_externalNeighborhood_finset
    [DecidableRel G.Adj] {A : Finset V} {d : ℕ}
    (hsmall : d * (externalNeighborhood G A).card ≤ Fintype.card V) :
    HasSmallSeparator G d :=
  of_externalNeighborhood
    (isExternalNeighborhood_externalNeighborhood G A) hsmall

end HasSmallSeparator

namespace HasSmallBalancedSeparator

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A small balanced separator is, in particular, a small separator in the
unbalanced sense used by Theorem 8.1. -/
theorem to_hasSmallSeparator {d : ℕ}
    (hG : HasSmallBalancedSeparator G d) :
    HasSmallSeparator G d := by
  rcases hG with ⟨A, B, S, hbal, hsmall⟩
  refine ⟨A, B, S, ?_, hsmall⟩
  exact {
    cover := hbal.cover
    disjoint_left_right := hbal.disjoint_left_right
    disjoint_left_separator := hbal.disjoint_left_separator
    disjoint_right_separator := hbal.disjoint_right_separator
    no_edge_left_right := hbal.no_edge_left_right
  }

/-- A balanced separator remains small when the requested scale is weakened. -/
theorem mono_scale {d e : ℕ} (hG : HasSmallBalancedSeparator G d)
    (hed : e ≤ d) :
    HasSmallBalancedSeparator G e := by
  rcases hG with ⟨A, B, S, hsep, hsmall⟩
  refine ⟨A, B, S, hsep, ?_⟩
  exact (Nat.mul_le_mul_right S.card hed).trans hsmall

/-- A balanced orientation of a small separator gives the existing
balanced-separator smallness predicate. -/
theorem of_vertexSeparator
    {A B S : Finset V} {d : ℕ}
    (h : VertexSeparator G A B S)
    (hAleB : A.card ≤ B.card)
    (hBbal : 3 * B.card ≤ 2 * Fintype.card V)
    (hsmall : d * S.card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  ⟨A, B, S, h.toBalanced hAleB hBbal, hsmall⟩

/-- A swapped balanced orientation of a small separator gives the existing
balanced-separator smallness predicate. -/
theorem of_vertexSeparator_swap
    {A B S : Finset V} {d : ℕ}
    (h : VertexSeparator G A B S)
    (hBleA : B.card ≤ A.card)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hsmall : d * S.card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  ⟨B, A, S, h.toBalanced_swap hBleA hAbal, hsmall⟩

/-- A small vertex separator gives a small balanced separator when each side is
individually at most `2|V|/3`; the orientation is chosen by comparing the two
side cardinalities. -/
theorem of_vertexSeparator_either_orientation
    {A B S : Finset V} {d : ℕ}
    (h : VertexSeparator G A B S)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hBbal : 3 * B.card ≤ 2 * Fintype.card V)
    (hsmall : d * S.card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d := by
  by_cases hAleB : A.card ≤ B.card
  · exact of_vertexSeparator h hAleB hBbal hsmall
  · exact of_vertexSeparator_swap h (Nat.le_of_not_ge hAleB)
      hAbal hsmall

/-- An external-neighborhood separator gives a small balanced separator once
the two resulting sides satisfy the balance inequalities in the displayed
orientation. -/
theorem of_externalNeighborhood
    {A S : Finset V} {d : ℕ}
    (hS : IsExternalNeighborhood G A S)
    (hAleB : A.card ≤ (VertexSeparator.remainder A S).card)
    (hBbal :
      3 * (VertexSeparator.remainder A S).card ≤ 2 * Fintype.card V)
    (hsmall : d * S.card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  of_vertexSeparator (VertexSeparator.of_externalNeighborhood hS)
    hAleB hBbal hsmall

/-- An external-neighborhood separator gives a small balanced separator once
the two resulting sides satisfy the balance inequalities after swapping. -/
theorem of_externalNeighborhood_swap
    {A S : Finset V} {d : ℕ}
    (hS : IsExternalNeighborhood G A S)
    (hBleA : (VertexSeparator.remainder A S).card ≤ A.card)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hsmall : d * S.card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  of_vertexSeparator_swap (VertexSeparator.of_externalNeighborhood hS)
    hBleA hAbal hsmall

/-- Concrete external-neighborhood version in the displayed orientation. -/
theorem of_externalNeighborhood_finset
    [DecidableRel G.Adj] {A : Finset V} {d : ℕ}
    (hAleB :
      A.card ≤ (VertexSeparator.remainder A
        (externalNeighborhood G A)).card)
    (hBbal :
      3 * (VertexSeparator.remainder A
        (externalNeighborhood G A)).card ≤ 2 * Fintype.card V)
    (hsmall : d * (externalNeighborhood G A).card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  of_externalNeighborhood
    (isExternalNeighborhood_externalNeighborhood G A)
    hAleB hBbal hsmall

/-- Concrete external-neighborhood version after swapping the two sides. -/
theorem of_externalNeighborhood_finset_swap
    [DecidableRel G.Adj] {A : Finset V} {d : ℕ}
    (hBleA :
      (VertexSeparator.remainder A
        (externalNeighborhood G A)).card ≤ A.card)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hsmall : d * (externalNeighborhood G A).card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  of_externalNeighborhood_swap
    (isExternalNeighborhood_externalNeighborhood G A)
    hBleA hAbal hsmall

/-- Stopping-state separator for the Theorem 8.1 algorithm.  If `A`, `B`, and
`C` partition the host vertices, `S` is the neighborhood of `A` inside `C`, the
two sides `A` and `C \ S` are balanced in the sense of Definition 5.1, and
`B ∪ S` is small, then `B ∪ S` is a small balanced separator. -/
theorem of_relativeExternalNeighborhood_partition
    {A B C S : Finset V} {d : ℕ}
    (hcover : A ∪ B ∪ C = Finset.univ)
    (hAB : Disjoint A B)
    (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hS : IsRelativeExternalNeighborhood G A C S)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hRbal : 3 * (C \ S).card ≤ 2 * Fintype.card V)
    (hsmall : d * (B ∪ S).card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  of_vertexSeparator_either_orientation
    (VertexSeparator.of_relativeExternalNeighborhood_partition
      hcover hAB hAC hBC hS)
    hAbal hRbal hsmall

/-- Concrete stopping-state separator using the computable relative external
neighborhood finset. -/
theorem of_relativeExternalNeighborhood_finset_partition
    [DecidableRel G.Adj]
    {A B C : Finset V} {d : ℕ}
    (hcover : A ∪ B ∪ C = Finset.univ)
    (hAB : Disjoint A B)
    (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hRbal :
      3 * (C \ relativeExternalNeighborhood G A C).card ≤
        2 * Fintype.card V)
    (hsmall :
      d * (B ∪ relativeExternalNeighborhood G A C).card ≤
        Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  of_relativeExternalNeighborhood_partition
    hcover hAB hAC hBC
    (isRelativeExternalNeighborhood_relativeExternalNeighborhood G A C)
    hAbal hRbal hsmall

/-- Stopping-state separator with the separator-size bound supplied separately
for the used branch vertices `B` and the frontier `S`. -/
theorem of_relativeExternalNeighborhood_partition_of_separate_bounds
    {A B C S : Finset V} {d : ℕ}
    (hcover : A ∪ B ∪ C = Finset.univ)
    (hAB : Disjoint A B)
    (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hS : IsRelativeExternalNeighborhood G A C S)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hRbal : 3 * (C \ S).card ≤ 2 * Fintype.card V)
    (hsmall : d * B.card + d * S.card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d := by
  have hBS : Disjoint B S := by
    rw [Finset.disjoint_left]
    intro v hvB hvS
    exact Finset.disjoint_left.mp hBC hvB (hS.subset_reservoir hvS)
  refine of_relativeExternalNeighborhood_partition
    hcover hAB hAC hBC hS hAbal hRbal ?_
  calc
    d * (B ∪ S).card = d * (B.card + S.card) := by
      rw [Finset.card_union_of_disjoint hBS]
    _ = d * B.card + d * S.card := by
      rw [Nat.mul_add]
    _ ≤ Fintype.card V := hsmall

/-- Concrete stopping-state separator with separate bounds for the used branch
vertices and the computable relative frontier. -/
theorem of_relativeExternalNeighborhood_finset_partition_of_separate_bounds
    [DecidableRel G.Adj]
    {A B C : Finset V} {d : ℕ}
    (hcover : A ∪ B ∪ C = Finset.univ)
    (hAB : Disjoint A B)
    (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hAbal : 3 * A.card ≤ 2 * Fintype.card V)
    (hRbal :
      3 * (C \ relativeExternalNeighborhood G A C).card ≤
        2 * Fintype.card V)
    (hsmall :
      d * B.card + d * (relativeExternalNeighborhood G A C).card ≤
        Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  of_relativeExternalNeighborhood_partition_of_separate_bounds
    hcover hAB hAC hBC
    (isRelativeExternalNeighborhood_relativeExternalNeighborhood G A C)
    hAbal hRbal hsmall

end HasSmallBalancedSeparator

/-- A partial branch-set minor model for the subgraph of `H` induced by the
currently active target vertices `I`.

This is the invariant maintained by the constructive proof of Theorem 8.1:
branch sets are only required for vertices in `I`; they are connected,
pairwise disjoint, and realize all target edges whose endpoints both lie in
`I`. -/
structure PartialMinorModel {W : Type u} {V : Type v}
    [Fintype W] [DecidableEq W]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V)
    (I : Finset W) where
  /-- The current branch set assigned to each target vertex. Values outside
  `I` are ignored. -/
  branchSet : W → Finset V
  /-- Active branch sets are nonempty. -/
  branch_nonempty : ∀ w : W, w ∈ I → (branchSet w).Nonempty
  /-- Active branch sets induce connected subgraphs in the host. -/
  branch_connected :
    ∀ w : W, w ∈ I → (G.induce {v : V | v ∈ branchSet w}).Connected
  /-- Distinct active target vertices have disjoint branch sets. -/
  branch_disjoint :
    ∀ ⦃u v : W⦄, u ∈ I → v ∈ I → u ≠ v →
      Disjoint (branchSet u) (branchSet v)
  /-- Every target edge whose endpoints are both active is realized by an edge
  between the corresponding branch sets. -/
  adjacent :
    ∀ ⦃u v : W⦄, u ∈ I → v ∈ I → H.Adj u v →
      ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

namespace PartialMinorModel

variable {W : Type u} {V : Type v}
variable [Fintype W] [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
variable {I : Finset W}

/-- The empty partial model, before any target vertex has been embedded. -/
def empty (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) :
    PartialMinorModel H G (∅ : Finset W) where
  branchSet := fun _ => ∅
  branch_nonempty := by
    intro w hw
    simp at hw
  branch_connected := by
    intro w hw
    simp at hw
  branch_disjoint := by
    intro u v hu
    simp at hu
  adjacent := by
    intro u v hu
    simp at hu

/-- The host vertices already occupied by active branch sets. -/
def usedVertices [DecidableEq V] (M : PartialMinorModel H G I) : Finset V :=
  I.biUnion M.branchSet

@[simp] theorem mem_usedVertices [DecidableEq V]
    (M : PartialMinorModel H G I)
    {x : V} :
    x ∈ M.usedVertices ↔ ∃ w ∈ I, x ∈ M.branchSet w := by
  simp [usedVertices]

/-- If every active branch set has size at most `r`, then the union of all
active branch sets has size at most `|I| * r`. -/
theorem usedVertices_card_le_card_mul
    [DecidableEq V]
    (M : PartialMinorModel H G I) {r : ℕ}
    (hcard : ∀ w : W, w ∈ I → (M.branchSet w).card ≤ r) :
    M.usedVertices.card ≤ I.card * r := by
  simpa [usedVertices, Nat.mul_comm] using
    (Finset.card_biUnion_le_card_mul I M.branchSet r hcard)

/-- A partial model whose active set is all target vertices is a genuine minor
model. -/
theorem isMinor_of_active_univ
    (M : PartialMinorModel H G I) (hI : I = Finset.univ) :
    IsMinor H G := by
  refine ⟨{
    branchSet := M.branchSet
    branch_nonempty := ?_
    branch_connected := ?_
    branch_disjoint := ?_
    adjacent := ?_
  }⟩
  · intro w
    exact M.branch_nonempty w (by simp [hI])
  · intro w
    exact M.branch_connected w (by simp [hI])
  · intro u v huv
    exact M.branch_disjoint (by simp [hI]) (by simp [hI]) huv
  · intro u v huv
    exact M.adjacent (by simp [hI]) (by simp [hI]) huv

/-- Update a partial model's branch-set function by assigning a new branch set
to one target vertex. -/
def insertBranchSet (M : PartialMinorModel H G I) (i : W)
    (Y : Finset V) : W → Finset V :=
  fun w => if w = i then Y else M.branchSet w

@[simp] theorem insertBranchSet_self
    (M : PartialMinorModel H G I) (i : W) (Y : Finset V) :
    M.insertBranchSet i Y i = Y := by
  simp [insertBranchSet]

@[simp] theorem insertBranchSet_of_ne
    (M : PartialMinorModel H G I) {i w : W} (Y : Finset V)
    (hwi : w ≠ i) :
    M.insertBranchSet i Y w = M.branchSet w := by
  simp [insertBranchSet, hwi]

/-- Add one target vertex to a partial model.  The new branch set must be
nonempty, connected, disjoint from the currently used vertices, and adjacent to
the already embedded branch sets corresponding to the new vertex's active
neighbors. -/
def insertVertex [DecidableEq V] (M : PartialMinorModel H G I)
    {i : W} (_hi : i ∉ I) {Y : Finset V}
    (hYnonempty : Y.Nonempty)
    (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
    (hYdisj : Disjoint Y M.usedVertices)
    (hadj :
      ∀ j : W, j ∈ I → H.Adj i j →
        ∃ x ∈ Y, ∃ y ∈ M.branchSet j, G.Adj x y) :
    PartialMinorModel H G (insert i I) where
  branchSet := M.insertBranchSet i Y
  branch_nonempty := by
    intro w hw
    by_cases hwi : w = i
    · simpa [insertBranchSet, hwi] using hYnonempty
    · have hwI : w ∈ I := by
        simpa [hwi] using hw
      simpa [insertBranchSet, hwi] using M.branch_nonempty w hwI
  branch_connected := by
    intro w hw
    by_cases hwi : w = i
    · have hset : M.insertBranchSet i Y w = Y := by
        simp [insertBranchSet, hwi]
      rw [hset]
      exact hYconnected
    · have hwI : w ∈ I := by
        simpa [hwi] using hw
      have hset : M.insertBranchSet i Y w = M.branchSet w := by
        simp [insertBranchSet, hwi]
      rw [hset]
      exact M.branch_connected w hwI
  branch_disjoint := by
    intro u v hu hv huv
    by_cases hui : u = i
    ·
      by_cases hvi : v = i
      · exact (huv (hui.trans hvi.symm)).elim
      · have hvI : v ∈ I := by
          simpa [hvi] using hv
        rw [Finset.disjoint_left]
        intro x hxu hxv
        have hxY : x ∈ Y := by
          simpa [insertBranchSet, hui] using hxu
        have hxv' : x ∈ M.branchSet v := by
          simpa [insertBranchSet, hvi] using hxv
        exact Finset.disjoint_left.mp hYdisj hxY
          ((M.mem_usedVertices).2 ⟨v, hvI, hxv'⟩)
    · have huI : u ∈ I := by
        simpa [hui] using hu
      by_cases hvi : v = i
      ·
        rw [Finset.disjoint_left]
        intro x hxu hxv
        have hxu' : x ∈ M.branchSet u := by
          simpa [insertBranchSet, hui] using hxu
        have hxY : x ∈ Y := by
          simpa [insertBranchSet, hvi] using hxv
        exact Finset.disjoint_left.mp hYdisj hxY
          ((M.mem_usedVertices).2 ⟨u, huI, hxu'⟩)
      · have hvI : v ∈ I := by
          simpa [hvi] using hv
        rw [insertBranchSet_of_ne M Y hui, insertBranchSet_of_ne M Y hvi]
        exact M.branch_disjoint huI hvI huv
  adjacent := by
    intro u v hu hv huv
    by_cases hui : u = i
    ·
      by_cases hvi : v = i
      · have hii : H.Adj i i := by
          subst u
          subst v
          exact huv
        exact (H.irrefl hii).elim
      · have hvI : v ∈ I := by
          simpa [hvi] using hv
        have hiv : H.Adj i v := by
          simpa [hui] using huv
        rcases hadj v hvI hiv with ⟨x, hx, y, hy, hxy⟩
        refine ⟨x, ?_, y, ?_, hxy⟩
        · simpa [insertBranchSet, hui] using hx
        · simpa [insertBranchSet, hvi] using hy
    · have huI : u ∈ I := by
        simpa [hui] using hu
      by_cases hvi : v = i
      · have hiu : H.Adj i u := by
          simpa [hvi] using huv.symm
        rcases hadj u huI hiu with ⟨x, hx, y, hy, hxy⟩
        refine ⟨y, ?_, x, ?_, hxy.symm⟩
        · simpa [insertBranchSet, hui] using hy
        · simpa [insertBranchSet, hvi] using hx
      · have hvI : v ∈ I := by
          simpa [hvi] using hv
        rcases M.adjacent huI hvI huv with ⟨x, hx, y, hy, hxy⟩
        refine ⟨x, ?_, y, ?_, hxy⟩
        · simpa [insertBranchSet, hui] using hx
        · simpa [insertBranchSet, hvi] using hy

/-- Remove one active target vertex from a partial model.  The branch-set
function is left unchanged, but all obligations are restricted to
`I.erase i`. -/
def eraseVertex (M : PartialMinorModel H G I) (i : W) :
    PartialMinorModel H G (I.erase i) where
  branchSet := M.branchSet
  branch_nonempty := by
    intro w hw
    exact M.branch_nonempty w (Finset.mem_of_mem_erase hw)
  branch_connected := by
    intro w hw
    exact M.branch_connected w (Finset.mem_of_mem_erase hw)
  branch_disjoint := by
    intro u v hu hv huv
    exact M.branch_disjoint
      (Finset.mem_of_mem_erase hu) (Finset.mem_of_mem_erase hv) huv
  adjacent := by
    intro u v hu hv huv
    exact M.adjacent
      (Finset.mem_of_mem_erase hu) (Finset.mem_of_mem_erase hv) huv

end PartialMinorModel

/-- The state invariant for the constructive proof of Theorem 8.1.

The host vertices are partitioned as `A ∪ B ∪ C`.  The set `B` is exactly the
union of branch sets in a partial minor model of the target graph on the active
target vertices.  The finset `frontier` is the relative external neighborhood
of `A` inside the reservoir `C`; bounding this frontier is what eventually
produces the separator alternative. -/
structure Theorem81State {W : Type u} {V : Type v}
    [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) where
  /-- Target vertices currently embedded as branch sets. -/
  active : Finset W
  /-- The partial branch-set model on the active target vertices. -/
  model : PartialMinorModel H G active
  /-- The accumulated low-expansion side. -/
  A : Finset V
  /-- Vertices occupied by the current branch sets. -/
  B : Finset V
  /-- The remaining reservoir. -/
  C : Finset V
  /-- The neighborhood of `A` inside `C`. -/
  frontier : Finset V
  /-- `A`, `B`, and `C` cover the host vertices. -/
  cover : A ∪ B ∪ C = Finset.univ
  /-- `A` is disjoint from the branch-set vertices. -/
  disjoint_A_B : Disjoint A B
  /-- `A` is disjoint from the reservoir. -/
  disjoint_A_C : Disjoint A C
  /-- Branch-set vertices are disjoint from the reservoir. -/
  disjoint_B_C : Disjoint B C
  /-- `B` is exactly the union of active branch sets. -/
  B_eq_used : B = model.usedVertices
  /-- `frontier` is the relative external neighborhood of `A` inside `C`. -/
  frontier_spec : IsRelativeExternalNeighborhood G A C frontier

namespace Theorem81State

variable {W : Type u} {V : Type v}
variable [Fintype W] [DecidableEq W] [DecidableEq V] [Fintype V]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}

/-- Initial state of the Theorem 8.1 embedding procedure. -/
def initial (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) :
    Theorem81State H G where
  active := ∅
  model := PartialMinorModel.empty H G
  A := ∅
  B := ∅
  C := Finset.univ
  frontier := ∅
  cover := by simp
  disjoint_A_B := by simp
  disjoint_A_C := by simp
  disjoint_B_C := by simp
  B_eq_used := by
    simp [PartialMinorModel.usedVertices]
  frontier_spec := by
    intro v
    simp

@[simp] theorem initial_active :
    (initial H G).active = (∅ : Finset W) := rfl

@[simp] theorem initial_A :
    (initial H G).A = (∅ : Finset V) := rfl

@[simp] theorem initial_B :
    (initial H G).B = (∅ : Finset V) := rfl

@[simp] theorem initial_C :
    (initial H G).C = Finset.univ := rfl

@[simp] theorem initial_frontier :
    (initial H G).frontier = (∅ : Finset V) := rfl

/-- The initial state satisfies every frontier-size bound. -/
theorem initial_frontier_bound (d : ℕ) :
    d * (initial H G).frontier.card ≤ (initial H G).A.card := by
  simp

/-- The initial state satisfies every uniform branch-size bound. -/
theorem initial_branch_bound (r : ℕ) :
    ∀ w : W, w ∈ (initial H G).active →
      ((initial H G).model.branchSet w).card ≤ r := by
  intro w hw
  simp at hw

/-- The embedding-step transition of the Theorem 8.1 procedure.  A connected
set `Y` inside the reservoir becomes the branch set for a new target vertex;
`Y` is moved from the reservoir into `B`, and the frontier of `A` is recomputed
inside the smaller reservoir. -/
def insertVertex (S : Theorem81State H G)
    {i : W} (hi : i ∉ S.active) {Y frontier' : Finset V}
    (hYsubsetC : Y ⊆ S.C)
    (hYnonempty : Y.Nonempty)
    (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
    (hadj :
      ∀ j : W, j ∈ S.active → H.Adj i j →
        ∃ x ∈ Y, ∃ y ∈ S.model.branchSet j, G.Adj x y)
    (hfrontier' :
      IsRelativeExternalNeighborhood G S.A (S.C \ Y) frontier') :
    Theorem81State H G where
  active := insert i S.active
  model := by
    have hYdisj : Disjoint Y S.model.usedVertices := by
      rw [← S.B_eq_used]
      rw [Finset.disjoint_left]
      intro x hxY hxB
      exact Finset.disjoint_left.mp S.disjoint_B_C hxB (hYsubsetC hxY)
    exact S.model.insertVertex hi hYnonempty hYconnected hYdisj hadj
  A := S.A
  B := S.B ∪ Y
  C := S.C \ Y
  frontier := frontier'
  cover := by
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      have hxABC : x ∈ S.A ∪ S.B ∪ S.C := by
        simp [S.cover]
      rw [Finset.mem_union, Finset.mem_union] at hxABC
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union,
        Finset.mem_sdiff]
      rcases hxABC with hxAB | hxC
      · rcases hxAB with hxA | hxB
        · exact Or.inl (Or.inl hxA)
        · exact Or.inl (Or.inr (Or.inl hxB))
      · by_cases hxY : x ∈ Y
        · exact Or.inl (Or.inr (Or.inr hxY))
        · exact Or.inr ⟨hxC, hxY⟩
  disjoint_A_B := by
    rw [Finset.disjoint_left]
    intro x hxA hxBY
    rw [Finset.mem_union] at hxBY
    rcases hxBY with hxB | hxY
    · exact Finset.disjoint_left.mp S.disjoint_A_B hxA hxB
    · exact Finset.disjoint_left.mp S.disjoint_A_C hxA (hYsubsetC hxY)
  disjoint_A_C := by
    rw [Finset.disjoint_left]
    intro x hxA hxCY
    exact Finset.disjoint_left.mp S.disjoint_A_C hxA
      (Finset.mem_sdiff.mp hxCY).1
  disjoint_B_C := by
    rw [Finset.disjoint_left]
    intro x hxBY hxCY
    rw [Finset.mem_union] at hxBY
    rcases hxBY with hxB | hxY
    · exact Finset.disjoint_left.mp S.disjoint_B_C hxB
        (Finset.mem_sdiff.mp hxCY).1
    · exact (Finset.mem_sdiff.mp hxCY).2 hxY
  B_eq_used := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_union] at hx
      rcases hx with hxB | hxY
      · rw [S.B_eq_used] at hxB
        rcases S.model.mem_usedVertices.1 hxB with ⟨w, hw, hxw⟩
        refine (PartialMinorModel.mem_usedVertices _).2 ⟨w, ?_, ?_⟩
        · exact Finset.mem_insert_of_mem hw
        · have hwi : w ≠ i := by
            exact fun h => hi (h ▸ hw)
          simpa [PartialMinorModel.insertVertex,
            PartialMinorModel.insertBranchSet, hwi] using hxw
      · refine (PartialMinorModel.mem_usedVertices _).2 ⟨i, ?_, ?_⟩
        · simp
        · simpa [PartialMinorModel.insertVertex,
            PartialMinorModel.insertBranchSet] using hxY
    · intro hx
      rcases (PartialMinorModel.mem_usedVertices _).1 hx with ⟨w, hw, hxw⟩
      rw [Finset.mem_union]
      rw [Finset.mem_insert] at hw
      rcases hw with hwi | hwI
      · right
        simpa [PartialMinorModel.insertVertex,
          PartialMinorModel.insertBranchSet, hwi] using hxw
      · left
        rw [S.B_eq_used]
        refine (PartialMinorModel.mem_usedVertices _).2 ⟨w, hwI, ?_⟩
        have hwi : w ≠ i := by
          exact fun h => hi (h ▸ hwI)
        simpa [PartialMinorModel.insertVertex,
          PartialMinorModel.insertBranchSet, hwi] using hxw
  frontier_spec := hfrontier'

/-- Inserting a branch set preserves the frontier-size invariant because the
side `A` is unchanged and the reservoir only shrinks. -/
theorem frontier_bound_insertVertex
    (S : Theorem81State H G)
    {i : W} (hi : i ∉ S.active) {Y frontier' : Finset V}
    (hYsubsetC : Y ⊆ S.C)
    (hYnonempty : Y.Nonempty)
    (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
    (hadj :
      ∀ j : W, j ∈ S.active → H.Adj i j →
        ∃ x ∈ Y, ∃ y ∈ S.model.branchSet j, G.Adj x y)
    (hfrontier' :
      IsRelativeExternalNeighborhood G S.A (S.C \ Y) frontier')
    {d : ℕ}
    (hOld : d * S.frontier.card ≤ S.A.card) :
    d * (S.insertVertex hi hYsubsetC hYnonempty hYconnected hadj
        hfrontier').frontier.card ≤
      (S.insertVertex hi hYsubsetC hYnonempty hYconnected hadj
        hfrontier').A.card := by
  have hsubset : frontier' ⊆ S.frontier :=
    S.frontier_spec.subset_of_reservoir_subset hfrontier'
      (by intro x hx; exact (Finset.mem_sdiff.mp hx).1)
  calc
    d * (S.insertVertex hi hYsubsetC hYnonempty hYconnected hadj
        hfrontier').frontier.card = d * frontier'.card := rfl
    _ ≤ d * S.frontier.card :=
        Nat.mul_le_mul_left d (Finset.card_le_card hsubset)
    _ ≤ S.A.card := hOld

/-- Inserting a branch set preserves the uniform branch-size invariant when the
new branch set satisfies the same size bound. -/
theorem branch_bound_insertVertex
    (S : Theorem81State H G)
    {i : W} (hi : i ∉ S.active) {Y frontier' : Finset V}
    (hYsubsetC : Y ⊆ S.C)
    (hYnonempty : Y.Nonempty)
    (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
    (hadj :
      ∀ j : W, j ∈ S.active → H.Adj i j →
        ∃ x ∈ Y, ∃ y ∈ S.model.branchSet j, G.Adj x y)
    (hfrontier' :
      IsRelativeExternalNeighborhood G S.A (S.C \ Y) frontier')
    {r : ℕ}
    (hOld :
      ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r)
    (hYcard : Y.card ≤ r) :
    ∀ w : W,
      w ∈ (S.insertVertex hi hYsubsetC hYnonempty hYconnected hadj
        hfrontier').active →
        ((S.insertVertex hi hYsubsetC hYnonempty hYconnected hadj
          hfrontier').model.branchSet w).card ≤ r := by
  intro w hw
  change w ∈ insert i S.active at hw
  rw [Finset.mem_insert] at hw
  rcases hw with hwi | hwOld
  · subst hwi
    simpa [insertVertex, PartialMinorModel.insertVertex,
      PartialMinorModel.insertBranchSet] using hYcard
  · have hne : w ≠ i := by
      exact fun h => hi (h ▸ hwOld)
    simpa [insertVertex, PartialMinorModel.insertVertex,
      PartialMinorModel.insertBranchSet, hne] using hOld w hwOld

/-- Move a reservoir set into `A`, the separator-building transition in the
Theorem 8.1 procedure.  The active partial minor model and used branch-set set
`B` are unchanged; only `A`, `C`, and the relative frontier are updated. -/
def moveReservoirSetToA (S : Theorem81State H G)
    {U frontier' : Finset V}
    (hUsubsetC : U ⊆ S.C)
    (hfrontier' :
      IsRelativeExternalNeighborhood G (S.A ∪ U) (S.C \ U) frontier') :
    Theorem81State H G where
  active := S.active
  model := S.model
  A := S.A ∪ U
  B := S.B
  C := S.C \ U
  frontier := frontier'
  cover := by
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      have hxABC : x ∈ S.A ∪ S.B ∪ S.C := by
        simp [S.cover]
      rw [Finset.mem_union, Finset.mem_union] at hxABC
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union,
        Finset.mem_sdiff]
      rcases hxABC with hxAB | hxC
      · rcases hxAB with hxA | hxB
        · exact Or.inl (Or.inl (Or.inl hxA))
        · exact Or.inl (Or.inr hxB)
      · by_cases hxU : x ∈ U
        · exact Or.inl (Or.inl (Or.inr hxU))
        · exact Or.inr ⟨hxC, hxU⟩
  disjoint_A_B := by
    rw [Finset.disjoint_left]
    intro x hxAU hxB
    rw [Finset.mem_union] at hxAU
    rcases hxAU with hxA | hxU
    · exact Finset.disjoint_left.mp S.disjoint_A_B hxA hxB
    · exact Finset.disjoint_left.mp S.disjoint_B_C hxB (hUsubsetC hxU)
  disjoint_A_C := by
    rw [Finset.disjoint_left]
    intro x hxAU hxCU
    rw [Finset.mem_union] at hxAU
    rcases hxAU with hxA | hxU
    · exact Finset.disjoint_left.mp S.disjoint_A_C hxA
        (Finset.mem_sdiff.mp hxCU).1
    · exact (Finset.mem_sdiff.mp hxCU).2 hxU
  disjoint_B_C := by
    rw [Finset.disjoint_left]
    intro x hxB hxCU
    exact Finset.disjoint_left.mp S.disjoint_B_C hxB
      (Finset.mem_sdiff.mp hxCU).1
  B_eq_used := S.B_eq_used
  frontier_spec := hfrontier'

/-- Moving a low-expansion reservoir set into `A` preserves the frontier-size
invariant. -/
theorem frontier_bound_moveReservoirSetToA
    (S : Theorem81State H G) {U frontier' frontierU : Finset V}
    (hUsubsetC : U ⊆ S.C)
    (hfrontier' :
      IsRelativeExternalNeighborhood G (S.A ∪ U) (S.C \ U) frontier')
    (hfrontierU :
      IsRelativeExternalNeighborhood G U (S.C \ U) frontierU)
    {d : ℕ}
    (hOld : d * S.frontier.card ≤ S.A.card)
    (hUsmall : d * frontierU.card ≤ U.card) :
    d * (S.moveReservoirSetToA hUsubsetC hfrontier').frontier.card ≤
      (S.moveReservoirSetToA hUsubsetC hfrontier').A.card := by
  have hsubset :
      frontier' ⊆ S.frontier ∪ frontierU :=
    IsRelativeExternalNeighborhood.subset_union_of_union_left
      S.frontier_spec hfrontierU hfrontier'
  have hcard :
      frontier'.card ≤ S.frontier.card + frontierU.card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hdisjAU : Disjoint S.A U := by
    rw [Finset.disjoint_left]
    intro x hxA hxU
    exact Finset.disjoint_left.mp S.disjoint_A_C hxA (hUsubsetC hxU)
  calc
    d * (S.moveReservoirSetToA hUsubsetC hfrontier').frontier.card
        = d * frontier'.card := rfl
    _ ≤ d * (S.frontier.card + frontierU.card) :=
        Nat.mul_le_mul_left d hcard
    _ = d * S.frontier.card + d * frontierU.card := by
        rw [Nat.mul_add]
    _ ≤ S.A.card + U.card := Nat.add_le_add hOld hUsmall
    _ = (S.A ∪ U).card := by
        rw [Finset.card_union_of_disjoint hdisjAU]

/-- Moving a reservoir set into `A` leaves all active branch sets unchanged, so
the uniform branch-size invariant is preserved. -/
theorem branch_bound_moveReservoirSetToA
    (S : Theorem81State H G) {U frontier' : Finset V}
    (hUsubsetC : U ⊆ S.C)
    (hfrontier' :
      IsRelativeExternalNeighborhood G (S.A ∪ U) (S.C \ U) frontier')
    {r : ℕ}
    (hOld :
      ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r) :
    ∀ w : W,
      w ∈ (S.moveReservoirSetToA hUsubsetC hfrontier').active →
        ((S.moveReservoirSetToA hUsubsetC hfrontier').model.branchSet w).card ≤ r := by
  intro w hw
  exact hOld w hw

/-- Move one active branch set from `B` into `A`, removing the corresponding
target vertex from the active partial model.  This is the transition used when
an already embedded branch set has no available neighbor in the reservoir. -/
def moveActiveBranchToA (S : Theorem81State H G)
    {i : W} (hi : i ∈ S.active) {frontier' : Finset V}
    (hfrontier' :
      IsRelativeExternalNeighborhood G
        (S.A ∪ S.model.branchSet i) S.C frontier') :
    Theorem81State H G where
  active := S.active.erase i
  model := S.model.eraseVertex i
  A := S.A ∪ S.model.branchSet i
  B := S.B \ S.model.branchSet i
  C := S.C
  frontier := frontier'
  cover := by
    have hbranch_subset_B : S.model.branchSet i ⊆ S.B := by
      intro x hx
      rw [S.B_eq_used]
      exact (PartialMinorModel.mem_usedVertices _).2 ⟨i, hi, hx⟩
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      have hxABC : x ∈ S.A ∪ S.B ∪ S.C := by
        simp [S.cover]
      rw [Finset.mem_union, Finset.mem_union] at hxABC
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union,
        Finset.mem_sdiff]
      rcases hxABC with hxAB | hxC
      · rcases hxAB with hxA | hxB
        · exact Or.inl (Or.inl (Or.inl hxA))
        · by_cases hxi : x ∈ S.model.branchSet i
          · exact Or.inl (Or.inl (Or.inr hxi))
          · exact Or.inl (Or.inr ⟨hxB, hxi⟩)
      · exact Or.inr hxC
  disjoint_A_B := by
    rw [Finset.disjoint_left]
    intro x hxAbranch hxB
    rw [Finset.mem_union] at hxAbranch
    have hxBold : x ∈ S.B := (Finset.mem_sdiff.mp hxB).1
    have hxnotBranch : x ∉ S.model.branchSet i := (Finset.mem_sdiff.mp hxB).2
    rcases hxAbranch with hxA | hxBranch
    · exact Finset.disjoint_left.mp S.disjoint_A_B hxA hxBold
    · exact hxnotBranch hxBranch
  disjoint_A_C := by
    rw [Finset.disjoint_left]
    intro x hxAbranch hxC
    rw [Finset.mem_union] at hxAbranch
    rcases hxAbranch with hxA | hxBranch
    · exact Finset.disjoint_left.mp S.disjoint_A_C hxA hxC
    · have hxB : x ∈ S.B := by
        rw [S.B_eq_used]
        exact (PartialMinorModel.mem_usedVertices _).2 ⟨i, hi, hxBranch⟩
      exact Finset.disjoint_left.mp S.disjoint_B_C hxB hxC
  disjoint_B_C := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    exact Finset.disjoint_left.mp S.disjoint_B_C
      (Finset.mem_sdiff.mp hxB).1 hxC
  B_eq_used := by
    ext x
    constructor
    · intro hx
      have hxB : x ∈ S.B := (Finset.mem_sdiff.mp hx).1
      have hxNot : x ∉ S.model.branchSet i := (Finset.mem_sdiff.mp hx).2
      rw [S.B_eq_used] at hxB
      rcases (PartialMinorModel.mem_usedVertices _).1 hxB with
        ⟨w, hw, hxw⟩
      have hwi : w ≠ i := by
        intro hwi
        exact hxNot (by simpa [hwi] using hxw)
      refine (PartialMinorModel.mem_usedVertices _).2 ⟨w, ?_, hxw⟩
      exact Finset.mem_erase.mpr ⟨hwi, hw⟩
    · intro hx
      rcases (PartialMinorModel.mem_usedVertices _).1 hx with
        ⟨w, hwErase, hxw⟩
      rcases Finset.mem_erase.mp hwErase with ⟨hwi, hw⟩
      rw [Finset.mem_sdiff]
      constructor
      · rw [S.B_eq_used]
        exact (PartialMinorModel.mem_usedVertices _).2 ⟨w, hw, hxw⟩
      · intro hxi
        exact Finset.disjoint_left.mp
          (S.model.branch_disjoint hw hi hwi) hxw hxi
  frontier_spec := hfrontier'

/-- Specialized deletion transition for the case used in the proof: an active
branch set with no reservoir neighbor is moved into `A`, and the old frontier
is still the frontier after the move. -/
def moveActiveBranchToA_noReservoirNeighbor
    (S : Theorem81State H G)
    {i : W} (hi : i ∈ S.active)
    (hno :
      ∀ ⦃x c : V⦄, x ∈ S.model.branchSet i → c ∈ S.C →
        ¬ G.Adj c x) :
    Theorem81State H G :=
  S.moveActiveBranchToA hi (frontier' := S.frontier) (by
    have hXC : Disjoint (S.model.branchSet i) S.C := by
      rw [Finset.disjoint_left]
      intro x hxi hxC
      have hxB : x ∈ S.B := by
        rw [S.B_eq_used]
        exact (PartialMinorModel.mem_usedVertices _).2 ⟨i, hi, hxi⟩
      exact Finset.disjoint_left.mp S.disjoint_B_C hxB hxC
    exact S.frontier_spec.union_right_of_no_reservoir_neighbor hXC hno)

/-- The frontier-size invariant is preserved by
`moveActiveBranchToA_noReservoirNeighbor`. -/
theorem frontier_bound_moveActiveBranchToA_noReservoirNeighbor
    (S : Theorem81State H G) {i : W} (hi : i ∈ S.active)
    {d : ℕ}
    (hno :
      ∀ ⦃x c : V⦄, x ∈ S.model.branchSet i → c ∈ S.C →
        ¬ G.Adj c x)
    (hfrontier : d * S.frontier.card ≤ S.A.card) :
    d * (S.moveActiveBranchToA_noReservoirNeighbor hi hno).frontier.card ≤
      (S.moveActiveBranchToA_noReservoirNeighbor hi hno).A.card := by
  calc
    d * (S.moveActiveBranchToA_noReservoirNeighbor hi hno).frontier.card
        = d * S.frontier.card := rfl
    _ ≤ S.A.card := hfrontier
    _ ≤ (S.A ∪ S.model.branchSet i).card :=
        Finset.card_le_card (Finset.subset_union_left)

/-- Moving one active branch set into `A` preserves the uniform branch-size
bound for the remaining active vertices. -/
theorem branch_bound_moveActiveBranchToA
    (S : Theorem81State H G) {i : W} (hi : i ∈ S.active)
    {frontier' : Finset V}
    (hfrontier' :
      IsRelativeExternalNeighborhood G
        (S.A ∪ S.model.branchSet i) S.C frontier')
    {r : ℕ}
    (hOld :
      ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r) :
    ∀ w : W,
      w ∈ (S.moveActiveBranchToA hi hfrontier').active →
        ((S.moveActiveBranchToA hi hfrontier').model.branchSet w).card ≤ r := by
  intro w hw
  exact hOld w (Finset.mem_of_mem_erase hw)

/-- Specialized no-reservoir-neighbor deletion also preserves the uniform
branch-size invariant. -/
theorem branch_bound_moveActiveBranchToA_noReservoirNeighbor
    (S : Theorem81State H G) {i : W} (hi : i ∈ S.active)
    (hno :
      ∀ ⦃x c : V⦄, x ∈ S.model.branchSet i → c ∈ S.C →
        ¬ G.Adj c x)
    {r : ℕ}
    (hOld :
      ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r) :
    ∀ w : W,
      w ∈ (S.moveActiveBranchToA_noReservoirNeighbor hi hno).active →
        ((S.moveActiveBranchToA_noReservoirNeighbor hi hno).model.branchSet w).card ≤ r := by
  intro w hw
  exact hOld w (Finset.mem_of_mem_erase hw)

/-- A terminal state with every target vertex active supplies the desired
minor model. -/
theorem isMinor_of_active_univ (S : Theorem81State H G)
    (hactive : S.active = Finset.univ) :
    IsMinor H G :=
  S.model.isMinor_of_active_univ hactive

/-- Bound the number of used branch-set vertices from a uniform bound on the
size of each active branch set. -/
theorem B_card_le_active_card_mul (S : Theorem81State H G) {r : ℕ}
    (hcard : ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r) :
    S.B.card ≤ S.active.card * r := by
  rw [S.B_eq_used]
  exact S.model.usedVertices_card_le_card_mul hcard

/-- The number of currently active target vertices is bounded by the target
complexity `|V(H)| + |E(H)|`. -/
theorem active_card_le_targetComplexity (S : Theorem81State H G)
    [Fintype H.edgeSet] :
    S.active.card ≤ targetComplexity H := by
  calc
    S.active.card ≤ Fintype.card W := S.active.card_le_univ
    _ ≤ Fintype.card W + H.edgeFinset.card := Nat.le_add_right _ _

/-- A terminal state with a medium-sized side `A`, balanced remaining side
`C \ frontier`, and small separator set `B ∪ frontier` gives the separator
alternative of Theorem 8.1. -/
theorem hasSmallBalancedSeparator_of_terminal_A
    (S : Theorem81State H G) {d : ℕ}
    (hAbal : 3 * S.A.card ≤ 2 * Fintype.card V)
    (hRbal : 3 * (S.C \ S.frontier).card ≤ 2 * Fintype.card V)
    (hsmall :
      d * S.B.card + d * S.frontier.card ≤ Fintype.card V) :
    HasSmallBalancedSeparator G d :=
  HasSmallBalancedSeparator.of_relativeExternalNeighborhood_partition_of_separate_bounds
    S.cover S.disjoint_A_B S.disjoint_A_C S.disjoint_B_C
    S.frontier_spec hAbal hRbal hsmall

/-- If the side `A` has size at least one third of the host, then the opposite
side `C \ frontier` in the separator terminal state has size at most
`2|V|/3`. -/
theorem right_remainder_balanced_of_one_third_A
    (S : Theorem81State H G)
    (hAthird : Fintype.card V ≤ 3 * S.A.card) :
    3 * (S.C \ S.frontier).card ≤ 2 * Fintype.card V := by
  have hdisj : Disjoint S.A (S.C \ S.frontier) := by
    rw [Finset.disjoint_left]
    intro x hxA hxR
    exact Finset.disjoint_left.mp S.disjoint_A_C hxA
      (Finset.mem_sdiff.mp hxR).1
  have hsubset : S.A ∪ (S.C \ S.frontier) ⊆ (Finset.univ : Finset V) := by
    intro x hx
    simp
  have hcardUnion :
      S.A.card + (S.C \ S.frontier).card =
        (S.A ∪ (S.C \ S.frontier)).card := by
    rw [Finset.card_union_of_disjoint hdisj]
  have hsum_le :
      S.A.card + (S.C \ S.frontier).card ≤ Fintype.card V := by
    rw [hcardUnion]
    exact Finset.card_le_univ _
  omega

/-- The separator terminal condition for the Theorem 8.1 state machine. -/
def SeparatorTerminal (S : Theorem81State H G) (d : ℕ) : Prop :=
  3 * S.A.card ≤ 2 * Fintype.card V ∧
  3 * (S.C \ S.frontier).card ≤ 2 * Fintype.card V ∧
  d * S.B.card + d * S.frontier.card ≤ Fintype.card V

namespace SeparatorTerminal

/-- Build the terminal separator condition from the separate scaled bounds used
in the paper: occupied branch vertices consume at most one third of the scaled
budget, and the current frontier consumes at most two thirds. -/
theorem of_scaled_bounds (S : Theorem81State H G) {d : ℕ}
    (hAbal : 3 * S.A.card ≤ 2 * Fintype.card V)
    (hRbal : 3 * (S.C \ S.frontier).card ≤ 2 * Fintype.card V)
    (hBsmall : 3 * (d * S.B.card) ≤ Fintype.card V)
    (hfrontierSmall : 3 * (d * S.frontier.card) ≤
      2 * Fintype.card V) :
    SeparatorTerminal S d := by
  refine ⟨hAbal, hRbal, ?_⟩
  omega

/-- Terminal condition from the paper's first-crossing bounds on `A`: `A` is
between one and two thirds of the host, and the branch/frontier separator
budgets are small. -/
theorem of_first_crossing_bounds (S : Theorem81State H G) {d : ℕ}
    (hAthird : Fintype.card V ≤ 3 * S.A.card)
    (hAbal : 3 * S.A.card ≤ 2 * Fintype.card V)
    (hBsmall : 3 * (d * S.B.card) ≤ Fintype.card V)
    (hfrontierSmall : 3 * (d * S.frontier.card) ≤
      2 * Fintype.card V) :
    SeparatorTerminal S d :=
  of_scaled_bounds S hAbal
    (S.right_remainder_balanced_of_one_third_A hAthird)
    hBsmall hfrontierSmall

end SeparatorTerminal

/-- The uniform branch-set size invariant gives the scaled bound on occupied
branch vertices needed by `SeparatorTerminal.of_scaled_bounds`. -/
theorem three_mul_d_mul_B_card_le_of_active_branch_bound
    (S : Theorem81State H G) {d r : ℕ}
    (hcard : ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r)
    (hbudget : 3 * (d * (S.active.card * r)) ≤ Fintype.card V) :
    3 * (d * S.B.card) ≤ Fintype.card V := by
  have hB := S.B_card_le_active_card_mul hcard
  have hmul : d * S.B.card ≤ d * (S.active.card * r) :=
    Nat.mul_le_mul_left d hB
  exact (Nat.mul_le_mul_left 3 hmul).trans hbudget

/-- Convert the target-size hypothesis of Theorem 8.1 into the occupied-branch
budget, assuming every active branch set has size at most
`branchScale * log₂ |V|` and the target denominator dominates
`3 * d * branchScale`. -/
theorem active_branch_budget_of_targetSmall
    (S : Theorem81State H G) [Fintype H.edgeSet]
    {d r branchScale targetScale : ℕ}
    (hactive : S.active.card ≤ targetComplexity H)
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * d * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale) :
    3 * (d * (S.active.card * r)) ≤ Fintype.card V := by
  let L := Nat.log 2 (Fintype.card V)
  let T := targetComplexity H
  have hprod : S.active.card * r ≤ T * (branchScale * L) :=
    Nat.mul_le_mul hactive hr
  calc
    3 * (d * (S.active.card * r))
        ≤ 3 * (d * (T * (branchScale * L))) := by
          exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left d hprod)
    _ = (3 * d * branchScale) * (T * L) := by
          ring
    _ ≤ targetScale * (T * L) := by
          exact Nat.mul_le_mul_right (T * L) hscale
    _ = targetScale * T * L := by
          ring
    _ ≤ Fintype.card V := by
          simpa [TargetSmallForHost, T, L] using hsmall

/-- A single active branch set is at most one third of the host when branch
sets are logarithmic and the target-size denominator dominates
`3 * branchScale`.  This is the local size estimate used when a stranded branch
is dumped into `A` at the first crossing. -/
theorem branch_card_third_of_targetSmall
    (S : Theorem81State H G) [Fintype H.edgeSet]
    {i : W} (_hi : i ∈ S.active)
    {r branchScale targetScale : ℕ}
    (hbranch : (S.model.branchSet i).card ≤ r)
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale) :
    3 * (S.model.branchSet i).card ≤ Fintype.card V := by
  let L := Nat.log 2 (Fintype.card V)
  let T := targetComplexity H
  have hcard_le : (S.model.branchSet i).card ≤ branchScale * L :=
    hbranch.trans hr
  have hTpos : 1 ≤ T := by
    have hWpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨i⟩
    simp [T, targetComplexity]
    omega
  have hLle : L ≤ T * L := by
    calc
      L = 1 * L := by rw [one_mul]
      _ ≤ T * L := Nat.mul_le_mul_right L hTpos
  calc
    3 * (S.model.branchSet i).card
        ≤ 3 * (branchScale * L) := Nat.mul_le_mul_left 3 hcard_le
    _ = (3 * branchScale) * L := by ring
    _ ≤ targetScale * (T * L) :=
        Nat.mul_le_mul hscale hLle
    _ = targetScale * T * L := by ring
    _ ≤ Fintype.card V := by
        simpa [TargetSmallForHost, T, L] using hsmall

/-- First-crossing arithmetic for a low-expansion move: if `A` was still below
one third of the host and the moved reservoir piece has size at most half of
the current reservoir, then the new side `A ∪ U` is at most two thirds of the
host. -/
theorem A_union_reservoir_subset_balanced_of_below_one_third
    (S : Theorem81State H G) {U : Finset V}
    (hUsubsetC : U ⊆ S.C)
    (hUhalf : 2 * U.card ≤ S.C.card)
    (hbelow : 3 * S.A.card < Fintype.card V) :
    3 * (S.A ∪ U).card ≤ 2 * Fintype.card V := by
  have hdisjAU : Disjoint S.A U := by
    rw [Finset.disjoint_left]
    intro x hxA hxU
    exact Finset.disjoint_left.mp S.disjoint_A_C hxA (hUsubsetC hxU)
  have hAUcard : (S.A ∪ U).card = S.A.card + U.card := by
    rw [Finset.card_union_of_disjoint hdisjAU]
  have hdisjAC : Disjoint S.A S.C := S.disjoint_A_C
  have hACcard : (S.A ∪ S.C).card = S.A.card + S.C.card := by
    rw [Finset.card_union_of_disjoint hdisjAC]
  have hACle : S.A.card + S.C.card ≤ Fintype.card V := by
    rw [← hACcard]
    exact Finset.card_le_univ _
  omega

/-- First-crossing arithmetic for dumping an active branch set: if `A` was
below one third and the dumped branch set has size at most one third, then the
new side is at most two thirds of the host. -/
theorem A_union_branch_balanced_of_below_one_third
    (S : Theorem81State H G) {i : W} (hi : i ∈ S.active)
    (hbranchThird :
      3 * (S.model.branchSet i).card ≤ Fintype.card V)
    (hbelow : 3 * S.A.card < Fintype.card V) :
    3 * (S.A ∪ S.model.branchSet i).card ≤
      2 * Fintype.card V := by
  have hbranch_subset_B : S.model.branchSet i ⊆ S.B := by
    intro x hx
    rw [S.B_eq_used]
    exact (PartialMinorModel.mem_usedVertices _).2 ⟨i, hi, hx⟩
  have hdisj : Disjoint S.A (S.model.branchSet i) := by
    rw [Finset.disjoint_left]
    intro x hxA hxi
    exact Finset.disjoint_left.mp S.disjoint_A_B hxA
      (hbranch_subset_B hxi)
  have hcard :
      (S.A ∪ S.model.branchSet i).card =
        S.A.card + (S.model.branchSet i).card := by
    rw [Finset.card_union_of_disjoint hdisj]
  omega

/-- The maintained frontier-expansion invariant `d * |frontier| ≤ |A|`,
together with the balance bound on `A`, gives the two-thirds frontier budget. -/
theorem three_mul_d_mul_frontier_card_le_of_frontier_le_A
    (S : Theorem81State H G) {d : ℕ}
    (hfrontier : d * S.frontier.card ≤ S.A.card)
    (hAbal : 3 * S.A.card ≤ 2 * Fintype.card V) :
    3 * (d * S.frontier.card) ≤ 2 * Fintype.card V :=
  (Nat.mul_le_mul_left 3 hfrontier).trans hAbal

/-- Terminal separator condition from the exact invariants maintained in the
algorithmic proof: logarithmic branch sets, target-size smallness, and the
frontier-expansion bound. -/
theorem separatorTerminal_of_targetSmall_and_frontier_bound
    (S : Theorem81State H G) [Fintype H.edgeSet]
    {d r branchScale targetScale : ℕ}
    (hAbal : 3 * S.A.card ≤ 2 * Fintype.card V)
    (hRbal : 3 * (S.C \ S.frontier).card ≤ 2 * Fintype.card V)
    (hbranch :
      ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r)
    (hactive : S.active.card ≤ targetComplexity H)
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * d * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale)
    (hfrontier : d * S.frontier.card ≤ S.A.card) :
    SeparatorTerminal S d :=
  SeparatorTerminal.of_scaled_bounds S hAbal hRbal
    (S.three_mul_d_mul_B_card_le_of_active_branch_bound hbranch
      (S.active_branch_budget_of_targetSmall hactive hr hscale hsmall))
    (S.three_mul_d_mul_frontier_card_le_of_frontier_le_A
      hfrontier hAbal)

/-- Same as `separatorTerminal_of_targetSmall_and_frontier_bound`, using the
automatic active-cardinality bound by `targetComplexity`. -/
theorem separatorTerminal_of_targetSmall_and_frontier_bound'
    (S : Theorem81State H G) [Fintype H.edgeSet]
    {d r branchScale targetScale : ℕ}
    (hAbal : 3 * S.A.card ≤ 2 * Fintype.card V)
    (hRbal : 3 * (S.C \ S.frontier).card ≤ 2 * Fintype.card V)
    (hbranch :
      ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r)
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * d * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale)
    (hfrontier : d * S.frontier.card ≤ S.A.card) :
    SeparatorTerminal S d :=
  S.separatorTerminal_of_targetSmall_and_frontier_bound
    hAbal hRbal hbranch
    S.active_card_le_targetComplexity hr hscale hsmall hfrontier

/-- First-crossing terminal condition using the target-size hypothesis and the
maintained frontier bound. -/
theorem separatorTerminal_of_first_crossing_targetSmall
    (S : Theorem81State H G) [Fintype H.edgeSet]
    {d r branchScale targetScale : ℕ}
    (hAthird : Fintype.card V ≤ 3 * S.A.card)
    (hAbal : 3 * S.A.card ≤ 2 * Fintype.card V)
    (hbranch :
      ∀ w : W, w ∈ S.active → (S.model.branchSet w).card ≤ r)
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * d * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale)
    (hfrontier : d * S.frontier.card ≤ S.A.card) :
    SeparatorTerminal S d :=
  SeparatorTerminal.of_first_crossing_bounds S
    hAthird hAbal
    (S.three_mul_d_mul_B_card_le_of_active_branch_bound hbranch
      (S.active_branch_budget_of_targetSmall
        S.active_card_le_targetComplexity hr hscale hsmall))
    (S.three_mul_d_mul_frontier_card_le_of_frontier_le_A
      hfrontier hAbal)

/-- A terminal state gives exactly the separator/minor alternative in the fixed
constant form of Theorem 8.1. -/
theorem separator_or_minor_of_terminal_state
    (S : Theorem81State H G) {d : ℕ}
    (hterminal : SeparatorTerminal S d ∨ S.active = Finset.univ) :
    HasSmallBalancedSeparator G d ∨ IsMinor H G := by
  rcases hterminal with hsep | hminor
  · rcases hsep with ⟨hAbal, hRbal, hsmall⟩
    exact Or.inl
      (S.hasSmallBalancedSeparator_of_terminal_A
        hAbal hRbal hsmall)
  · exact Or.inr (S.isMinor_of_active_univ hminor)

end Theorem81State

/-- A Theorem 8.1 algorithm state bundled with the two global invariants used
throughout the proof: a frontier-size bound and a uniform branch-size bound. -/
structure Theorem81InvariantState {W : Type u} {V : Type v}
    [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V)
    (d r : ℕ) where
  /-- The underlying partition/partial-minor state. -/
  state : Theorem81State H G
  /-- The maintained frontier-expansion inequality. -/
  frontier_bound : d * state.frontier.card ≤ state.A.card
  /-- Uniform bound on all active branch sets. -/
  branch_bound :
    ∀ w : W, w ∈ state.active → (state.model.branchSet w).card ≤ r

namespace Theorem81InvariantState

variable {W : Type u} {V : Type v}
variable [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
variable {d r : ℕ}

/-- Initial invariant state. -/
def initial (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V)
    (d r : ℕ) : Theorem81InvariantState H G d r where
  state := Theorem81State.initial H G
  frontier_bound := Theorem81State.initial_frontier_bound (H := H) (G := G) d
  branch_bound := Theorem81State.initial_branch_bound (H := H) (G := G) r

/-- Invariant-state version of the embedding transition. -/
def insertVertex (R : Theorem81InvariantState H G d r)
    {i : W} (hi : i ∉ R.state.active) {Y frontier' : Finset V}
    (hYsubsetC : Y ⊆ R.state.C)
    (hYnonempty : Y.Nonempty)
    (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
    (hadj :
      ∀ j : W, j ∈ R.state.active → H.Adj i j →
        ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j, G.Adj x y)
    (hfrontier' :
      IsRelativeExternalNeighborhood G R.state.A (R.state.C \ Y) frontier')
    (hYcard : Y.card ≤ r) :
    Theorem81InvariantState H G d r where
  state := R.state.insertVertex hi hYsubsetC hYnonempty hYconnected
    hadj hfrontier'
  frontier_bound :=
    R.state.frontier_bound_insertVertex hi hYsubsetC hYnonempty
      hYconnected hadj hfrontier' R.frontier_bound
  branch_bound :=
    R.state.branch_bound_insertVertex hi hYsubsetC hYnonempty
      hYconnected hadj hfrontier' R.branch_bound hYcard

/-- Invariant-state version of the low-expansion reservoir deletion
transition. -/
def moveReservoirSetToA (R : Theorem81InvariantState H G d r)
    {U frontier' frontierU : Finset V}
    (hUsubsetC : U ⊆ R.state.C)
    (hfrontier' :
      IsRelativeExternalNeighborhood G (R.state.A ∪ U)
        (R.state.C \ U) frontier')
    (hfrontierU :
      IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU)
    (hUsmall : d * frontierU.card ≤ U.card) :
    Theorem81InvariantState H G d r where
  state := R.state.moveReservoirSetToA hUsubsetC hfrontier'
  frontier_bound :=
    R.state.frontier_bound_moveReservoirSetToA hUsubsetC hfrontier'
      hfrontierU R.frontier_bound hUsmall
  branch_bound :=
    R.state.branch_bound_moveReservoirSetToA hUsubsetC hfrontier'
      R.branch_bound

/-- Invariant-state version of the stranded-branch deletion transition. -/
def moveActiveBranchToA_noReservoirNeighbor
    (R : Theorem81InvariantState H G d r)
    {i : W} (hi : i ∈ R.state.active)
    (hno :
      ∀ ⦃x c : V⦄, x ∈ R.state.model.branchSet i →
        c ∈ R.state.C → ¬ G.Adj c x) :
    Theorem81InvariantState H G d r where
  state := R.state.moveActiveBranchToA_noReservoirNeighbor hi hno
  frontier_bound :=
    R.state.frontier_bound_moveActiveBranchToA_noReservoirNeighbor
      hi hno R.frontier_bound
  branch_bound :=
    R.state.branch_bound_moveActiveBranchToA_noReservoirNeighbor
      hi hno R.branch_bound

/-- A terminal invariant state satisfying the first-crossing size bounds gives
the separator/minor alternative. -/
theorem separator_or_minor_of_first_crossing
    (R : Theorem81InvariantState H G d r) [Fintype H.edgeSet]
    {branchScale targetScale : ℕ}
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * d * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale)
    (hterminal :
      R.state.active = Finset.univ ∨
        (Fintype.card V ≤ 3 * R.state.A.card ∧
          3 * R.state.A.card ≤ 2 * Fintype.card V)) :
    HasSmallBalancedSeparator G d ∨ IsMinor H G := by
  rcases hterminal with hminor | hsep
  · exact Or.inr (R.state.isMinor_of_active_univ hminor)
  · rcases hsep with ⟨hAthird, hAbal⟩
    have hterm :
        Theorem81State.SeparatorTerminal R.state d :=
      R.state.separatorTerminal_of_first_crossing_targetSmall
        hAthird hAbal R.branch_bound hr hscale
        hsmall R.frontier_bound
    exact Or.inl
      (R.state.hasSmallBalancedSeparator_of_terminal_A
        hterm.1 hterm.2.1 hterm.2.2)

/-- Invariant-state wrapper for the single-branch target-size budget. -/
theorem branch_card_third_of_targetSmall
    (R : Theorem81InvariantState H G d r) [Fintype H.edgeSet]
    {i : W} (hi : i ∈ R.state.active)
    {branchScale targetScale : ℕ}
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale) :
    3 * (R.state.model.branchSet i).card ≤ Fintype.card V :=
  R.state.branch_card_third_of_targetSmall hi
    (R.branch_bound i hi) hr hscale hsmall

/-- Invariant-state wrapper for the first-crossing arithmetic when dumping a
stranded active branch set. -/
theorem A_union_branch_balanced_of_targetSmall
    (R : Theorem81InvariantState H G d r) [Fintype H.edgeSet]
    {i : W} (hi : i ∈ R.state.active)
    {branchScale targetScale : ℕ}
    (hr : r ≤ branchScale * Nat.log 2 (Fintype.card V))
    (hscale : 3 * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale)
    (hbelow : 3 * R.state.A.card < Fintype.card V) :
    3 * (R.state.A ∪ R.state.model.branchSet i).card ≤
      2 * Fintype.card V :=
  R.state.A_union_branch_balanced_of_below_one_third hi
    (R.branch_card_third_of_targetSmall hi hr hscale hsmall) hbelow

/-- Invariant-state wrapper for the first-crossing arithmetic when moving a
low-expansion subset of the reservoir to `A`. -/
theorem A_union_reservoir_subset_balanced_of_below_one_third
    (R : Theorem81InvariantState H G d r) {U : Finset V}
    (hUsubsetC : U ⊆ R.state.C)
    (hUhalf : 2 * U.card ≤ R.state.C.card)
    (hbelow : 3 * R.state.A.card < Fintype.card V) :
    3 * (R.state.A ∪ U).card ≤ 2 * Fintype.card V :=
  R.state.A_union_reservoir_subset_balanced_of_below_one_third
    hUsubsetC hUhalf hbelow

/-- Terminal predicate for the first-crossing version of the Theorem 8.1
algorithm.  Either every target vertex has been embedded, or the separator side
has crossed one third of the host while remaining at most two thirds. -/
def FirstCrossingTerminal (R : Theorem81InvariantState H G d r) : Prop :=
  R.state.active = Finset.univ ∨
    (Fintype.card V ≤ 3 * R.state.A.card ∧
      3 * R.state.A.card ≤ 2 * Fintype.card V)

/-- A nonterminal first-crossing state has at least one target vertex not yet
active. -/
theorem exists_inactive_of_not_firstCrossingTerminal
    {R : Theorem81InvariantState H G d r}
    (hnot : ¬ FirstCrossingTerminal R) :
    ∃ i : W, i ∉ R.state.active := by
  classical
  have hactive : R.state.active ≠ Finset.univ := by
    intro h
    exact hnot (Or.inl h)
  by_contra hnone
  apply hactive
  ext i
  constructor
  · intro _hi
    simp
  · intro _hi
    by_contra hi
    exact hnone ⟨i, hi⟩

/-- One certified iteration of the proof of Theorem 8.1, at the invariant-state
level.  The constructors are exactly the three updates in the paper:
embedding a new target vertex, moving a low-expansion reservoir set to `A`, and
dumping a stranded active branch set into `A`. -/
inductive Step :
    Theorem81InvariantState H G d r →
      Theorem81InvariantState H G d r → Prop
  | insert
      (R : Theorem81InvariantState H G d r)
      {i : W} (hi : i ∉ R.state.active) {Y frontier' : Finset V}
      (hYsubsetC : Y ⊆ R.state.C)
      (hYnonempty : Y.Nonempty)
      (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
      (hadj :
        ∀ j : W, j ∈ R.state.active → H.Adj i j →
          ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j, G.Adj x y)
      (hfrontier' :
        IsRelativeExternalNeighborhood G R.state.A
          (R.state.C \ Y) frontier')
      (hYcard : Y.card ≤ r) :
      Step R
        (R.insertVertex hi hYsubsetC hYnonempty hYconnected
          hadj hfrontier' hYcard)
  | moveReservoir
      (R : Theorem81InvariantState H G d r)
      {U frontier' frontierU : Finset V}
      (hUsubsetC : U ⊆ R.state.C)
      (hUnonempty : U.Nonempty)
      (hfrontier' :
        IsRelativeExternalNeighborhood G (R.state.A ∪ U)
          (R.state.C \ U) frontier')
      (hfrontierU :
        IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU)
      (hUsmall : d * frontierU.card ≤ U.card) :
      Step R
        (R.moveReservoirSetToA hUsubsetC hfrontier'
          hfrontierU hUsmall)
  | moveActive
      (R : Theorem81InvariantState H G d r)
      {i : W} (hi : i ∈ R.state.active)
      (hno :
        ∀ ⦃x c : V⦄, x ∈ R.state.model.branchSet i →
          c ∈ R.state.C → ¬ G.Adj c x) :
      Step R (R.moveActiveBranchToA_noReservoirNeighbor hi hno)

/-- A currently active branch set has an available neighbor in the reservoir
when some reservoir vertex is adjacent to one of its branch vertices. -/
def BranchHasReservoirNeighbor
    (R : Theorem81InvariantState H G d r) (j : W) : Prop :=
  ∃ x ∈ R.state.model.branchSet j, ∃ c ∈ R.state.C, G.Adj c x

/-- Negating the reservoir-neighbor predicate gives exactly the no-neighbor
hypothesis required by the stranded-branch transition. -/
theorem noReservoirNeighbor_of_not_branchHasReservoirNeighbor
    {R : Theorem81InvariantState H G d r} {j : W}
    (hno : ¬ BranchHasReservoirNeighbor R j) :
    ∀ ⦃x c : V⦄, x ∈ R.state.model.branchSet j →
      c ∈ R.state.C → ¬ G.Adj c x := by
  intro x c hx hc hcx
  exact hno ⟨x, hx, c, hc, hcx⟩

/-- If every active neighbor of a new target vertex has some reservoir contact,
then there is a finite set of chosen contact vertices in the reservoir, with
cardinality bounded by the number of active neighbors. -/
theorem exists_contactSet_of_all_branchHasReservoirNeighbor
    [DecidableRel H.Adj]
    {R : Theorem81InvariantState H G d r} {i : W}
    (hcontacts :
      ∀ j : W, j ∈ activeNeighborFinset H R.state.active i →
        BranchHasReservoirNeighbor R j) :
    ∃ Cts : Finset V,
      Cts ⊆ R.state.C ∧
      Cts.card ≤ (activeNeighborFinset H R.state.active i).card ∧
      (∀ j : W, j ∈ activeNeighborFinset H R.state.active i →
        ∃ c ∈ Cts, ∃ x ∈ R.state.model.branchSet j, G.Adj c x) := by
  classical
  let N := activeNeighborFinset H R.state.active i
  have hsub : ∀ j : {j // j ∈ N},
      BranchHasReservoirNeighbor R j.1 := by
    intro j
    exact hcontacts j.1 j.2
  choose x hx c hc hcx using hsub
  let Cts : Finset V := N.attach.image fun j => c j
  refine ⟨Cts, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, _hj, rfl⟩
    exact hc j
  · simpa [Cts] using
      (Finset.card_image_le :
        (N.attach.image fun j => c j).card ≤ N.attach.card)
  · intro j hj
    let jj : {j // j ∈ N} := ⟨j, hj⟩
    refine ⟨c jj, ?_, x jj, hx jj, hcx jj⟩
    simp [Cts, jj]

/-- A set containing chosen reservoir contacts for all active neighbors gives
the adjacency obligation needed to insert the next branch set. -/
theorem adjacency_of_contactSet
    [DecidableRel H.Adj]
    {R : Theorem81InvariantState H G d r} {i : W}
    {Cts Y : Finset V}
    (hcontacts :
      ∀ j : W, j ∈ activeNeighborFinset H R.state.active i →
        ∃ c ∈ Cts, ∃ x ∈ R.state.model.branchSet j, G.Adj c x)
    (hCtsY : Cts ⊆ Y) :
    ∀ j : W, j ∈ R.state.active → H.Adj i j →
      ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j, G.Adj x y := by
  intro j hjactive hij
  have hjN : j ∈ activeNeighborFinset H R.state.active i := by
    exact (mem_activeNeighborFinset).2 ⟨hjactive, hij⟩
  rcases hcontacts j hjN with ⟨c, hcCts, x, hx, hcx⟩
  exact ⟨c, hCtsY hcCts, x, hx, hcx⟩

/-- The paper loop has three possible nonterminal choices:

* dump a stranded active branch set into `A`;
* move a low-expansion reservoir set into `A`;
* embed a new target vertex using a connected set in the reservoir.

This predicate isolates the remaining local graph-theoretic work: Lemma 8.2
and the bounded-diameter path construction are precisely what supply the last
two alternatives. -/
def LoopChoice (R : Theorem81InvariantState H G d r) : Prop :=
  ∃ i : W, i ∉ R.state.active ∧
    ((∃ j : W, j ∈ R.state.active ∧ H.Adj i j ∧
        ¬ BranchHasReservoirNeighbor R j) ∨
      (∃ U frontier' frontierU : Finset V,
        U ⊆ R.state.C ∧ U.Nonempty ∧
          IsRelativeExternalNeighborhood G (R.state.A ∪ U)
            (R.state.C \ U) frontier' ∧
          IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU ∧
          d * frontierU.card ≤ U.card) ∨
      (∃ Y frontier' : Finset V,
        Y ⊆ R.state.C ∧ Y.Nonempty ∧
          (G.induce {v : V | v ∈ Y}).Connected ∧
          (∀ j : W, j ∈ R.state.active → H.Adj i j →
            ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j, G.Adj x y) ∧
          IsRelativeExternalNeighborhood G R.state.A
            (R.state.C \ Y) frontier' ∧
          Y.card ≤ r))

/-- A small connected hull inside the current reservoir.  In the proof of
Theorem 8.1 this is produced in the diameter branch of Lemma 8.2 by connecting
the at most three contact vertices through a pivot. -/
def ConnectedReservoirHull (R : Theorem81InvariantState H G d r)
    (Cts : Finset V) : Prop :=
  ∃ Y frontier' : Finset V,
    Cts ⊆ Y ∧
    Y ⊆ R.state.C ∧
    Y.Nonempty ∧
    (G.induce {v : V | v ∈ Y}).Connected ∧
    IsRelativeExternalNeighborhood G R.state.A
      (R.state.C \ Y) frontier' ∧
    Y.card ≤ r

/-- A concrete path-union certificate for the bounded-diameter branch of
Theorem 8.1.  The pivot and every contact lie in `Cts`, and each contact is
joined to the pivot by a walk whose whole support stays inside the current
reservoir. -/
structure ReservoirWalkHull (R : Theorem81InvariantState H G d r)
    (Cts : Finset V) (m : ℕ) where
  /-- The pivot contact used to connect the short paths. -/
  pivot : V
  /-- The pivot is one of the selected contacts. -/
  pivot_mem : pivot ∈ Cts
  /-- A reservoir walk from the pivot to each selected contact. -/
  walk : ∀ c : {x : V // x ∈ Cts}, G.Walk pivot c.1
  /-- Every walk support remains inside the reservoir. -/
  support_subset_reservoir :
    ∀ c : {x : V // x ∈ Cts}, ∀ x : V,
      x ∈ (walk c).support → x ∈ R.state.C
  /-- Each connecting walk has length at most `m`. -/
  length_le : ∀ c : {x : V // x ∈ Cts}, (walk c).length ≤ m

namespace ReservoirWalkHull

/-- The union of the supports of all pivot-to-contact walks. -/
noncomputable def vertexSet
    {R : Theorem81InvariantState H G d r} {Cts : Finset V} {m : ℕ}
    (K : ReservoirWalkHull R Cts m) : Finset V :=
  Cts.attach.biUnion fun c => (K.walk c).support.toFinset

/-- The path-union certificate yields the connected reservoir hull used by the
state-machine proof.  The size estimate is intentionally stated separately so
that later diameter bounds can feed in whatever constant convention they use. -/
theorem connectedReservoirHull
    [DecidableRel G.Adj]
    {R : Theorem81InvariantState H G d r} {Cts : Finset V} {m : ℕ}
    (K : ReservoirWalkHull R Cts m)
    (hcard : Cts.card * (m + 1) ≤ r) :
    ConnectedReservoirHull R Cts := by
  classical
  let Y : Finset V := K.vertexSet
  let frontier' : Finset V :=
    relativeExternalNeighborhood G R.state.A (R.state.C \ Y)
  have hCtsY : Cts ⊆ Y := by
    intro c hc
    let cc : {x : V // x ∈ Cts} := ⟨c, hc⟩
    have hcSupport : c ∈ (K.walk cc).support.toFinset :=
      List.mem_toFinset.mpr (K.walk cc).end_mem_support
    exact Finset.mem_biUnion.mpr ⟨cc, by simp, hcSupport⟩
  have hYsubsetC : Y ⊆ R.state.C := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, _hc, hxSupport⟩
    exact K.support_subset_reservoir c x (List.mem_toFinset.mp hxSupport)
  have hYnonempty : Y.Nonempty := by
    exact ⟨K.pivot, hCtsY K.pivot_mem⟩
  have hYconnected : (G.induce {v : V | v ∈ Y}).Connected := by
    have hpivotY : K.pivot ∈ Y := hCtsY K.pivot_mem
    apply G.induce_connected_of_patches K.pivot (by simpa using hpivotY)
    intro v hv
    change v ∈ Y at hv
    rcases Finset.mem_biUnion.mp hv with ⟨c, _hc, hvSupportFin⟩
    let s' : Set V := {x : V | x ∈ (K.walk c).support}
    refine ⟨s', ?_, ?_, ?_, ?_⟩
    · intro x hx
      change x ∈ Y
      exact Finset.mem_biUnion.mpr
        ⟨c, by simp, List.mem_toFinset.mpr hx⟩
    · exact (K.walk c).start_mem_support
    · exact List.mem_toFinset.mp hvSupportFin
    · exact
        ((K.walk c).connected_induce_support).preconnected
          ⟨K.pivot, (K.walk c).start_mem_support⟩
          ⟨v, List.mem_toFinset.mp hvSupportFin⟩
  have hfrontier' :
      IsRelativeExternalNeighborhood G R.state.A (R.state.C \ Y)
        frontier' := by
    exact isRelativeExternalNeighborhood_relativeExternalNeighborhood
      G R.state.A (R.state.C \ Y)
  have hYcard : Y.card ≤ r := by
    have hYcard_bound : Y.card ≤ Cts.card * (m + 1) := by
      calc
        Y.card =
            (Cts.attach.biUnion
              fun c => (K.walk c).support.toFinset).card := rfl
        _ ≤ ∑ c ∈ Cts.attach, ((K.walk c).support.toFinset).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _c ∈ Cts.attach, (m + 1) := by
            refine Finset.sum_le_sum ?_
            intro c _hc
            have hsupport :
                ((K.walk c).support.toFinset).card ≤
                  (K.walk c).support.length :=
              List.toFinset_card_le (K.walk c).support
            have hlength :
                (K.walk c).support.length ≤ m + 1 := by
              rw [(K.walk c).length_support]
              have hlen := K.length_le c
              omega
            exact hsupport.trans hlength
        _ = Cts.card * (m + 1) := by simp
    exact hYcard_bound.trans hcard
  exact ⟨Y, frontier', hCtsY, hYsubsetC, hYnonempty, hYconnected,
    hfrontier', hYcard⟩

end ReservoirWalkHull

/-- A bounded-diameter reservoir certificate: any two current reservoir
vertices can be joined by a walk of length at most `m` whose support remains in
the reservoir.  This is the finitary form of applying Lemma 8.2 to `G[C]` and
landing in the diameter branch. -/
def ReservoirDiameterBound (R : Theorem81InvariantState H G d r)
    (m : ℕ) : Prop :=
  ∀ x : V, x ∈ R.state.C →
    ∀ y : V, y ∈ R.state.C →
      ∃ p : G.Walk x y,
        p.length ≤ m ∧ ∀ z : V, z ∈ p.support → z ∈ R.state.C

/-- A bounded-diameter reservoir gives connected hulls for every nonempty
contact set whose path-union size fits in the current branch-size budget. -/
theorem connectedReservoirHull_of_reservoirDiameterBound
    [DecidableRel G.Adj]
    {R : Theorem81InvariantState H G d r} {Cts : Finset V} {m : ℕ}
    (hdiam : ReservoirDiameterBound R m)
    (hCtsC : Cts ⊆ R.state.C)
    (hCtsNonempty : Cts.Nonempty)
    (hcard : Cts.card * (m + 1) ≤ r) :
    ConnectedReservoirHull R Cts := by
  classical
  rcases hCtsNonempty with ⟨pivot, hpivotCts⟩
  have hpivotC : pivot ∈ R.state.C := hCtsC hpivotCts
  have hwalk :
      ∀ c : {x : V // x ∈ Cts},
        ∃ p : G.Walk pivot c.1,
          p.length ≤ m ∧ ∀ z : V, z ∈ p.support → z ∈ R.state.C := by
    intro c
    exact hdiam pivot hpivotC c.1 (hCtsC c.2)
  choose p hpLength hpSupport using hwalk
  let K : ReservoirWalkHull R Cts m := {
    pivot := pivot
    pivot_mem := hpivotCts
    walk := p
    support_subset_reservoir := hpSupport
    length_le := hpLength }
  exact K.connectedReservoirHull hcard

/-- A connected reservoir set containing contact vertices for all active
neighbors gives the embedding alternative of the paper loop. -/
theorem loopChoice_of_connected_contactSet
    [DecidableRel H.Adj]
    {R : Theorem81InvariantState H G d r} {i : W}
    {Cts Y frontier' : Finset V}
    (hi : i ∉ R.state.active)
    (hcontacts :
      ∀ j : W, j ∈ activeNeighborFinset H R.state.active i →
        ∃ c ∈ Cts, ∃ x ∈ R.state.model.branchSet j, G.Adj c x)
    (hCtsY : Cts ⊆ Y)
    (hYsubsetC : Y ⊆ R.state.C)
    (hYnonempty : Y.Nonempty)
    (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
    (hfrontier' :
      IsRelativeExternalNeighborhood G R.state.A
        (R.state.C \ Y) frontier')
    (hYcard : Y.card ≤ r) :
    LoopChoice R := by
  refine ⟨i, hi, Or.inr (Or.inr ?_)⟩
  refine ⟨Y, frontier', hYsubsetC, hYnonempty, hYconnected, ?_,
    hfrontier', hYcard⟩
  exact adjacency_of_contactSet hcontacts hCtsY

/-- If the next target vertex has no active neighbors, any reservoir vertex can
serve as a singleton connected branch set.  This is the `X = ∅` case in the
paper's diameter branch. -/
theorem loopChoice_of_no_active_neighbors
    [DecidableRel G.Adj]
    {R : Theorem81InvariantState H G d r} {i : W} {c : V}
    (hi : i ∉ R.state.active)
    (hc : c ∈ R.state.C)
    (hnoActiveNeighbor :
      ∀ j : W, j ∈ R.state.active → ¬ H.Adj i j)
    (hr : 1 ≤ r) :
    LoopChoice R := by
  classical
  let Y : Finset V := {c}
  let frontier' : Finset V :=
    relativeExternalNeighborhood G R.state.A (R.state.C \ Y)
  have hYsubsetC : Y ⊆ R.state.C := by
    intro x hx
    have hxc : x = c := by simpa [Y] using hx
    simpa [hxc] using hc
  have hYnonempty : Y.Nonempty := by
    exact ⟨c, by simp [Y]⟩
  have hYconnected : (G.induce {v : V | v ∈ Y}).Connected := by
    haveI : Nonempty {v : V | v ∈ Y} := ⟨⟨c, by simp [Y]⟩⟩
    haveI : Subsingleton {v : V | v ∈ Y} := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : x.1 = c := by simpa [Y] using x.2
      have hy : y.1 = c := by simpa [Y] using y.2
      exact hx.trans hy.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  have hadj :
      ∀ j : W, j ∈ R.state.active → H.Adj i j →
        ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j, G.Adj x y := by
    intro j hj hij
    exact False.elim (hnoActiveNeighbor j hj hij)
  have hfrontier' :
      IsRelativeExternalNeighborhood G R.state.A
        (R.state.C \ Y) frontier' := by
    exact isRelativeExternalNeighborhood_relativeExternalNeighborhood
      G R.state.A (R.state.C \ Y)
  have hYcard : Y.card ≤ r := by
    simpa [Y] using hr
  refine ⟨i, hi, Or.inr (Or.inr ?_)⟩
  exact ⟨Y, frontier', hYsubsetC, hYnonempty, hYconnected, hadj,
    hfrontier', hYcard⟩

/-- A low-expansion reservoir set gives the low-expansion alternative of the
paper loop.  The new frontier of `A ∪ U` is recomputed concretely. -/
theorem loopChoice_of_lowExpansionSet
    [DecidableRel G.Adj]
    {R : Theorem81InvariantState H G d r} {i : W}
    {U frontierU : Finset V}
    (hi : i ∉ R.state.active)
    (hUsubsetC : U ⊆ R.state.C)
    (hUnonempty : U.Nonempty)
    (hfrontierU :
      IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU)
    (hUsmall : d * frontierU.card ≤ U.card) :
    LoopChoice R := by
  classical
  refine ⟨i, hi, Or.inr (Or.inl ?_)⟩
  refine ⟨U,
    relativeExternalNeighborhood G (R.state.A ∪ U) (R.state.C \ U),
    frontierU, hUsubsetC, hUnonempty, ?_, hfrontierU, hUsmall⟩
  exact isRelativeExternalNeighborhood_relativeExternalNeighborhood
    G (R.state.A ∪ U) (R.state.C \ U)

/-- If every active neighbor of the next target vertex has a reservoir contact
and every nonempty at-most-three contact set has a small connected reservoir
hull, then the diameter branch supplies the embedding alternative of the paper
loop.  The `X = ∅` case of the paper is handled separately by
`loopChoice_of_no_active_neighbors`. -/
theorem loopChoice_of_contacts_and_connectedReservoirHull
    [DecidableRel H.Adj]
    {R : Theorem81InvariantState H G d r} {i : W}
    (hi : i ∉ R.state.active)
    (hNnonempty :
      (activeNeighborFinset H R.state.active i).Nonempty)
    (hmax : MaxDegreeAtMost H 3)
    (hcontacts :
      ∀ j : W, j ∈ activeNeighborFinset H R.state.active i →
        BranchHasReservoirNeighbor R j)
    (hhull :
      ∀ Cts : Finset V, Cts ⊆ R.state.C → Cts.Nonempty →
        Cts.card ≤ 3 →
        ConnectedReservoirHull R Cts) :
    LoopChoice R := by
  classical
  rcases exists_contactSet_of_all_branchHasReservoirNeighbor
      (R := R) (i := i) hcontacts with
    ⟨Cts, hCtsC, hCtsCard, hCtsContacts⟩
  have hCtsNonempty : Cts.Nonempty := by
    rcases hNnonempty with ⟨j, hjN⟩
    rcases hCtsContacts j hjN with ⟨c, hcCts, _x, _hx, _hcx⟩
    exact ⟨c, hcCts⟩
  have hCtsCard3 : Cts.card ≤ 3 :=
    hCtsCard.trans (activeNeighborFinset_card_le_three_of_subcubic
      (H := H) (I := R.state.active) (i := i) hmax)
  rcases hhull Cts hCtsC hCtsNonempty hCtsCard3 with
    ⟨Y, frontier', hCtsY, hYsubsetC, hYnonempty, hYconnected,
      hfrontier', hYcard⟩
  exact loopChoice_of_connected_contactSet hi hCtsContacts hCtsY
    hYsubsetC hYnonempty hYconnected hfrontier' hYcard

/-- Any explicit loop choice produces one certified descending step. -/
theorem exists_step_of_loopChoice
    {R : Theorem81InvariantState H G d r}
    (hchoice : LoopChoice R) :
    ∃ R' : Theorem81InvariantState H G d r, Step R R' := by
  classical
  rcases hchoice with ⟨i, hi, hstranded | hlow | hembed⟩
  · rcases hstranded with ⟨j, hj, _hij, hno⟩
    refine ⟨R.moveActiveBranchToA_noReservoirNeighbor hj
      (noReservoirNeighbor_of_not_branchHasReservoirNeighbor hno), ?_⟩
    exact Step.moveActive R hj
      (noReservoirNeighbor_of_not_branchHasReservoirNeighbor hno)
  · rcases hlow with
      ⟨U, frontier', frontierU, hUsubsetC, hUnonempty, hfrontier',
        hfrontierU, hUsmall⟩
    refine ⟨R.moveReservoirSetToA hUsubsetC hfrontier'
      hfrontierU hUsmall, ?_⟩
    exact Step.moveReservoir R hUsubsetC hUnonempty hfrontier'
      hfrontierU hUsmall
  · rcases hembed with
      ⟨Y, frontier', hYsubsetC, hYnonempty, hYconnected, hadj,
        hfrontier', hYcard⟩
    refine ⟨R.insertVertex hi hYsubsetC hYnonempty hYconnected
      hadj hfrontier' hYcard, ?_⟩
    exact Step.insert R hi hYsubsetC hYnonempty hYconnected
      hadj hfrontier' hYcard

/-- The lexicographic descent measure used to prove that certified iterations
of the algorithm terminate: first maximize `A`; while `A` is unchanged,
maximize the active target set. -/
def descentMeasure (R : Theorem81InvariantState H G d r) : ℕ × ℕ :=
  (Fintype.card V - R.state.A.card,
    Fintype.card W - R.state.active.card)

/-- Strict descent for invariant states, lexicographically on
`(n - |A|, |V(H)| - |active|)`. -/
def Descends : Theorem81InvariantState H G d r →
    Theorem81InvariantState H G d r → Prop :=
  InvImage (Prod.Lex (· < ·) (· < ·)) descentMeasure

theorem descends_wellFounded :
    WellFounded (Descends (H := H) (G := G) (d := d) (r := r)) := by
  unfold Descends
  exact InvImage.wf
    (descentMeasure (H := H) (G := G) (d := d) (r := r))
    (IsWellFounded.wf (α := ℕ × ℕ)
      (r := Prod.Lex (· < ·) (· < ·)))

/-- Every certified paper-step strictly decreases the termination measure. -/
theorem step_descends {R R' : Theorem81InvariantState H G d r}
    (hstep : Step R R') :
    Descends R' R := by
  classical
  cases hstep with
  | insert hi hYsubsetC hYnonempty hYconnected hadj hfrontier' hYcard =>
      rename_i i Y frontier'
      simp [Descends, descentMeasure, InvImage, Prod.lex_def]
      right
      constructor
      · rfl
      · have hcard :
            (insert i R.state.active).card = R.state.active.card + 1 := by
          simp [hi]
        have hinsert_le :
            (insert i R.state.active).card ≤ Fintype.card W :=
          Finset.card_le_univ _
        rw [hcard] at hinsert_le
        have hlt :
            Fintype.card W - (insert i R.state.active).card <
              Fintype.card W - R.state.active.card := by
          rw [hcard]
          omega
        simpa [Theorem81InvariantState.insertVertex,
          Theorem81State.insertVertex] using hlt
  | moveReservoir hUsubsetC hUnonempty hfrontier' hfrontierU hUsmall =>
      rename_i U frontier' frontierU
      simp [Descends, descentMeasure, InvImage, Prod.lex_def]
      left
      have hdisj : Disjoint R.state.A U := by
        rw [Finset.disjoint_left]
        intro x hxA hxU
        exact Finset.disjoint_left.mp R.state.disjoint_A_C hxA
          (hUsubsetC hxU)
      have hcard :
          (R.state.A ∪ U).card = R.state.A.card + U.card := by
        rw [Finset.card_union_of_disjoint hdisj]
      have hUpos : 0 < U.card := Finset.card_pos.mpr hUnonempty
      have hnew_le :
          (R.state.A ∪ U).card ≤ Fintype.card V :=
        Finset.card_le_univ _
      have hlt :
          Fintype.card V - (R.state.A ∪ U).card <
            Fintype.card V - R.state.A.card := by
        omega
      simpa [Theorem81InvariantState.moveReservoirSetToA,
        Theorem81State.moveReservoirSetToA] using hlt
  | moveActive hi hno =>
      rename_i i
      simp [Descends, descentMeasure, InvImage, Prod.lex_def]
      left
      have hbranch_subset_B :
          R.state.model.branchSet i ⊆ R.state.B := by
        intro x hx
        rw [R.state.B_eq_used]
        exact (PartialMinorModel.mem_usedVertices _).2 ⟨i, hi, hx⟩
      have hdisj : Disjoint R.state.A (R.state.model.branchSet i) := by
        rw [Finset.disjoint_left]
        intro x hxA hxi
        exact Finset.disjoint_left.mp R.state.disjoint_A_B hxA
          (hbranch_subset_B hxi)
      have hcard :
          (R.state.A ∪ R.state.model.branchSet i).card =
            R.state.A.card + (R.state.model.branchSet i).card := by
        rw [Finset.card_union_of_disjoint hdisj]
      have hbranch_pos :
          0 < (R.state.model.branchSet i).card := by
        exact Finset.card_pos.mpr (R.state.model.branch_nonempty i hi)
      have hnew_le :
          (R.state.A ∪ R.state.model.branchSet i).card ≤
            Fintype.card V :=
        Finset.card_le_univ _
      have hlt :
          Fintype.card V -
              (R.state.A ∪ R.state.model.branchSet i).card <
            Fintype.card V - R.state.A.card := by
        omega
      simpa [Theorem81InvariantState.moveActiveBranchToA_noReservoirNeighbor,
        Theorem81State.moveActiveBranchToA_noReservoirNeighbor,
        Theorem81State.moveActiveBranchToA] using hlt

/-- If every nonterminal invariant state admits either an immediate terminal
certificate or one certified descending step, then a first-crossing terminal
state exists from the initial state. -/
theorem exists_firstCrossingTerminal_of_progress
    (hprogress :
      ∀ R : Theorem81InvariantState H G d r,
        ¬ FirstCrossingTerminal R →
          ∃ R' : Theorem81InvariantState H G d r,
            FirstCrossingTerminal R' ∨ Step R R') :
    ∃ R : Theorem81InvariantState H G d r,
      FirstCrossingTerminal R := by
  classical
  let rel := Descends (H := H) (G := G) (d := d) (r := r)
  have hwf : WellFounded rel :=
    descends_wellFounded (H := H) (G := G) (d := d) (r := r)
  have hfrom :
      ∀ R : Theorem81InvariantState H G d r,
        ∃ T : Theorem81InvariantState H G d r,
          FirstCrossingTerminal T := by
    intro R
    refine hwf.induction
      (C := fun _ : Theorem81InvariantState H G d r =>
        ∃ T : Theorem81InvariantState H G d r,
          FirstCrossingTerminal T) R ?_
    intro R ih
    by_cases hterm : FirstCrossingTerminal R
    · exact ⟨R, hterm⟩
    · rcases hprogress R hterm with ⟨R', hR' | hstep⟩
      · exact ⟨R', hR'⟩
      · exact ih R' (step_descends hstep)
  exact hfrom (initial H G d r)

end Theorem81InvariantState

/-- The remaining algorithmic content of Theorem 8.1 at fixed constants.

For every admissible host/target pair, the constructive procedure must produce
a state whose partial model is complete, or whose separator side satisfies the
paper's terminal balance, branch-size, and frontier-expansion invariants.  This
definition is intentionally proof-facing: the theorems below prove that this
state-level terminal certificate is sufficient for the public
separator/minor alternative. -/
def Theorem81AlgorithmTerminatesAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet],
      n₀ ≤ Fintype.card V →
        TargetSmallForHost (V := V) H targetScale →
          ∃ S : Theorem81State H G,
            S.active = Finset.univ ∨
              (3 * S.A.card ≤ 2 * Fintype.card V ∧
                3 * (S.C \ S.frontier).card ≤ 2 * Fintype.card V ∧
                (∀ w : W, w ∈ S.active →
                  (S.model.branchSet w).card ≤
                    branchScale * Nat.log 2 (Fintype.card V)) ∧
                separatorScale * S.frontier.card ≤ S.A.card)

/-- First-crossing version of the remaining algorithmic content.  This matches
the paper proof more directly: in the separator branch the set `A` has just
crossed one third of the host and is still at most two thirds. -/
def Theorem81AlgorithmFirstCrossingTerminatesAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet],
      n₀ ≤ Fintype.card V →
        TargetSmallForHost (V := V) H targetScale →
          ∃ S : Theorem81State H G,
            S.active = Finset.univ ∨
              (Fintype.card V ≤ 3 * S.A.card ∧
                3 * S.A.card ≤ 2 * Fintype.card V ∧
                (∀ w : W, w ∈ S.active →
                  (S.model.branchSet w).card ≤
                    branchScale * Nat.log 2 (Fintype.card V)) ∧
                separatorScale * S.frontier.card ≤ S.A.card)

/-- Bundled-invariant version of the first-crossing termination certificate.
The branch-size and frontier-size invariants are stored in the returned
`Theorem81InvariantState`, leaving only the terminal shape to state. -/
def Theorem81InvariantFirstCrossingTerminatesAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet],
      n₀ ≤ Fintype.card V →
        TargetSmallForHost (V := V) H targetScale →
          ∃ R : Theorem81InvariantState H G separatorScale
              (branchScale * Nat.log 2 (Fintype.card V)),
            Theorem81InvariantState.FirstCrossingTerminal R

/-- Local-progress formulation of the remaining algorithmic proof.  From every
nonterminal invariant state, the proof must either produce an immediate
first-crossing terminal state or one of the three certified descending steps.
The well-founded descent theorem above turns this local statement into global
termination. -/
def Theorem81InvariantProgressOracleAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet],
      n₀ ≤ Fintype.card V →
        TargetSmallForHost (V := V) H targetScale →
          ∀ R : Theorem81InvariantState H G separatorScale
              (branchScale * Nat.log 2 (Fintype.card V)),
            ¬ Theorem81InvariantState.FirstCrossingTerminal R →
              ∃ R' : Theorem81InvariantState H G separatorScale
                  (branchScale * Nat.log 2 (Fintype.card V)),
                Theorem81InvariantState.FirstCrossingTerminal R' ∨
                  Theorem81InvariantState.Step R R'

/-- Local loop-choice formulation of the remaining algorithmic proof.  Compared
with `Theorem81InvariantProgressOracleAt`, this asks only for one of the three
paper loop choices at each nonterminal state; the conversion to a descending
step is proved above. -/
def Theorem81LoopChoiceOracleAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet],
      n₀ ≤ Fintype.card V →
        TargetSmallForHost (V := V) H targetScale →
          ∀ R : Theorem81InvariantState H G separatorScale
              (branchScale * Nat.log 2 (Fintype.card V)),
            ¬ Theorem81InvariantState.FirstCrossingTerminal R →
              Theorem81InvariantState.LoopChoice R

/-- Subcubic version of the loop-choice oracle.  This is the exact target of
the proof after the standard reduction of the target graph to maximum degree
three. -/
def Theorem81SubcubicLoopChoiceOracleAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (H : _root_.SimpleGraph W) [DecidableRel H.Adj] [Fintype H.edgeSet],
      MaxDegreeAtMost H 3 →
        n₀ ≤ Fintype.card V →
          TargetSmallForHost (V := V) H targetScale →
            ∀ R : Theorem81InvariantState H G separatorScale
                (branchScale * Nat.log 2 (Fintype.card V)),
              ¬ Theorem81InvariantState.FirstCrossingTerminal R →
                Theorem81InvariantState.LoopChoice R

/-- Local geometric content needed by the subcubic Theorem 8.1 loop.  At each
nonterminal state and for some inactive target vertex, either Lemma 8.2 supplies
a low-expansion reservoir set, or the complementary bounded-diameter branch
supplies the data used in the paper:

* a nonempty reservoir and room for a singleton branch set, covering the
  `X = ∅` case;
* connected hulls for all nonempty contact sets of size at most three,
  covering the `|X| ≤ 3` case. -/
def Theorem81SubcubicLocalGeometryAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (H : _root_.SimpleGraph W) [DecidableRel H.Adj] [Fintype H.edgeSet],
      MaxDegreeAtMost H 3 →
        n₀ ≤ Fintype.card V →
          TargetSmallForHost (V := V) H targetScale →
            ∀ R : Theorem81InvariantState H G separatorScale
                (branchScale * Nat.log 2 (Fintype.card V)),
              ¬ Theorem81InvariantState.FirstCrossingTerminal R →
                ∃ i : W, i ∉ R.state.active ∧
                  ((∃ U frontierU : Finset V,
                    U ⊆ R.state.C ∧
                    U.Nonempty ∧
                    IsRelativeExternalNeighborhood G U
                      (R.state.C \ U) frontierU ∧
                    separatorScale * frontierU.card ≤ U.card) ∨
                  (1 ≤ branchScale * Nat.log 2 (Fintype.card V) ∧
                    R.state.C.Nonempty ∧
                    ∀ Cts : Finset V, Cts ⊆ R.state.C →
                    Cts.Nonempty →
                    Cts.card ≤ 3 →
                      Theorem81InvariantState.ConnectedReservoirHull R Cts))

/-- Lemma-8.2-shaped local input for the subcubic proof.  It is slightly lower
level than `Theorem81SubcubicLocalGeometryAt`: the diameter branch supplies a
short-walk diameter certificate for the current reservoir, plus the arithmetic
showing that three such paths fit in the branch-size budget. -/
def Theorem81ReservoirGeometryAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (H : _root_.SimpleGraph W) [DecidableRel H.Adj] [Fintype H.edgeSet],
      MaxDegreeAtMost H 3 →
        n₀ ≤ Fintype.card V →
          TargetSmallForHost (V := V) H targetScale →
            ∀ R : Theorem81InvariantState H G separatorScale
                (branchScale * Nat.log 2 (Fintype.card V)),
              ¬ Theorem81InvariantState.FirstCrossingTerminal R →
                ∃ i : W, i ∉ R.state.active ∧
                  ((∃ U frontierU : Finset V,
                    U ⊆ R.state.C ∧
                    U.Nonempty ∧
                    IsRelativeExternalNeighborhood G U
                      (R.state.C \ U) frontierU ∧
                    separatorScale * frontierU.card ≤ U.card) ∨
                  (R.state.C.Nonempty ∧
                    ∃ m : ℕ,
                      Theorem81InvariantState.ReservoirDiameterBound R m ∧
                      3 * (m + 1) ≤
                        branchScale * Nat.log 2 (Fintype.card V)))

/-- Same reservoir geometry input as `Theorem81ReservoirGeometryAt`, but
without bundling the choice of the next inactive target vertex.  The inactive
vertex is a state-machine consequence of being nonterminal, so this is the
cleaner target for the formal Lemma 8.2 application. -/
def Theorem81ReservoirAlternativeAt
    (separatorScale branchScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (H : _root_.SimpleGraph W) [DecidableRel H.Adj] [Fintype H.edgeSet],
      MaxDegreeAtMost H 3 →
        n₀ ≤ Fintype.card V →
          TargetSmallForHost (V := V) H targetScale →
            ∀ R : Theorem81InvariantState H G separatorScale
                (branchScale * Nat.log 2 (Fintype.card V)),
              ¬ Theorem81InvariantState.FirstCrossingTerminal R →
                ((∃ U frontierU : Finset V,
                    U ⊆ R.state.C ∧
                    U.Nonempty ∧
                    IsRelativeExternalNeighborhood G U
                      (R.state.C \ U) frontierU ∧
                    separatorScale * frontierU.card ≤ U.card) ∨
                  (R.state.C.Nonempty ∧
                    ∃ m : ℕ,
                      Theorem81InvariantState.ReservoirDiameterBound R m ∧
                      3 * (m + 1) ≤
                        branchScale * Nat.log 2 (Fintype.card V)))

/-- A bounded-degree expansion of a target graph for the first reduction in
Theorem 8.1.  The expansion `H'` has maximum degree at most three, contains the
original target as a minor, and has vertices-plus-edges controlled by
`complexityScale * targetComplexity H`. -/
structure SubcubicMinorExpansion {W : Type v} [Fintype W]
    (H : _root_.SimpleGraph W) [Fintype H.edgeSet]
    (complexityScale : ℕ) where
  /-- Vertex type of the bounded-degree expansion. -/
  W' : Type v
  /-- The expansion is finite. -/
  instFintype : Fintype W'
  /-- The expansion has decidable vertex equality. -/
  instDecidableEq : DecidableEq W'
  /-- The bounded-degree expansion graph. -/
  H' : _root_.SimpleGraph W'
  /-- The expansion has decidable adjacency for algorithmic use. -/
  instDecidableRel : DecidableRel H'.Adj
  /-- The expansion has finite edge set. -/
  instEdgeSet : Fintype H'.edgeSet
  /-- The expansion is subcubic. -/
  maxDegree : MaxDegreeAtMost H' 3
  /-- Contracting the split vertices recovers `H` as a minor. -/
  minor : IsMinor H H'
  /-- The expansion has controlled target complexity. -/
  complexity_bound :
    letI : Fintype W' := instFintype
    letI : Fintype H'.edgeSet := instEdgeSet
    targetComplexity H' ≤ complexityScale * targetComplexity H

/-- Provider for the standard reduction from arbitrary targets to subcubic
targets used at the start of Theorem 8.1. -/
def SubcubicMinorExpansionProvider (complexityScale : ℕ) : Prop :=
  ∀ {W : Type v} [Fintype W] [DecidableEq W]
    (H : _root_.SimpleGraph W) [Fintype H.edgeSet],
      Nonempty (SubcubicMinorExpansion H complexityScale)

/-- Fixed-constant Theorem 8.1 after the target graph has already been reduced
to maximum degree at most three. -/
def ExpanderMinorTheoremAtSubcubic
    (separatorScale targetScale n₀ : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (H : _root_.SimpleGraph W) [DecidableRel H.Adj] [Fintype H.edgeSet],
      MaxDegreeAtMost H 3 →
        n₀ ≤ Fintype.card V →
          TargetSmallForHost (V := V) H targetScale →
            HasSmallBalancedSeparator G separatorScale ∨ IsMinor H G

/-- The reservoir alternative plus the state-machine inactive-vertex lemma
gives the bundled reservoir geometry input. -/
theorem reservoirGeometryAt_of_reservoirAlternativeAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (halt : Theorem81ReservoirAlternativeAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    Theorem81ReservoirGeometryAt.{u, v}
      separatorScale branchScale targetScale n₀ := by
  intro V _ _ W _ _ G _ H _ _ hmax hn hsmall R hnot
  rcases
      Theorem81InvariantState.exists_inactive_of_not_firstCrossingTerminal
        (R := R) hnot with
    ⟨i, hi⟩
  exact ⟨i, hi, halt G H hmax hn hsmall R hnot⟩

/-- The subcubic separator/minor theorem plus the standard target-splitting
reduction implies the unrestricted fixed-constant theorem. -/
theorem expanderMinorTheoremAt_of_subcubicExpansion
    {separatorScale subcubicTargetScale targetScale n₀ complexityScale : ℕ}
    (htarget : subcubicTargetScale * complexityScale ≤ targetScale)
    (hexpand : SubcubicMinorExpansionProvider.{v} complexityScale)
    (hsub : ExpanderMinorTheoremAtSubcubic.{u, v}
      separatorScale subcubicTargetScale n₀) :
    ExpanderMinorTheoremAt.{u, v} separatorScale targetScale n₀ := by
  intro V _ _ W _ _ G H _ hn hsmall
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rcases hexpand H with ⟨E⟩
  letI : Fintype E.W' := E.instFintype
  letI : DecidableEq E.W' := E.instDecidableEq
  letI : DecidableRel E.H'.Adj := E.instDecidableRel
  letI : Fintype E.H'.edgeSet := E.instEdgeSet
  have hsmall' :
      TargetSmallForHost (V := V) E.H' subcubicTargetScale := by
    calc
      subcubicTargetScale * targetComplexity E.H' *
          Nat.log 2 (Fintype.card V)
          ≤ subcubicTargetScale *
              (complexityScale * targetComplexity H) *
              Nat.log 2 (Fintype.card V) := by
              exact Nat.mul_le_mul_right (Nat.log 2 (Fintype.card V))
                (Nat.mul_le_mul_left subcubicTargetScale E.complexity_bound)
      _ = (subcubicTargetScale * complexityScale) *
              targetComplexity H * Nat.log 2 (Fintype.card V) := by
              ac_rfl
      _ ≤ targetScale * targetComplexity H *
              Nat.log 2 (Fintype.card V) := by
              exact Nat.mul_le_mul_right (Nat.log 2 (Fintype.card V))
                (Nat.mul_le_mul_right (targetComplexity H) htarget)
      _ ≤ Fintype.card V := hsmall
  rcases hsub G E.H' E.maxDegree hn hsmall' with hsep | hminor
  · exact Or.inl hsep
  · exact Or.inr (E.minor.trans hminor)

/-- The Lemma-8.2-shaped reservoir geometry input implies the local geometry
oracle used by the state machine. -/
theorem subcubicLocalGeometryAt_of_reservoirGeometryAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hgeom : Theorem81ReservoirGeometryAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    Theorem81SubcubicLocalGeometryAt.{u, v}
      separatorScale branchScale targetScale n₀ := by
  intro V _ _ W _ _ G _ H _ _ hmax hn hsmall R hnot
  rcases hgeom G H hmax hn hsmall R hnot with
    ⟨i, hi, hlow | hdiam⟩
  · exact ⟨i, hi, Or.inl hlow⟩
  · rcases hdiam with ⟨hCnonempty, m, hdiam, hdiamCard⟩
    refine ⟨i, hi, Or.inr ?_⟩
    refine ⟨?_, hCnonempty, ?_⟩
    · have hmpos : 1 ≤ 3 * (m + 1) := by omega
      exact hmpos.trans hdiamCard
    · intro Cts hCtsC hCtsNonempty hCtsCard
      apply Theorem81InvariantState.connectedReservoirHull_of_reservoirDiameterBound
        (R := R) (Cts := Cts) (m := m) hdiam hCtsC hCtsNonempty
      exact (Nat.mul_le_mul_right (m + 1) hCtsCard).trans hdiamCard

/-- The local geometric alternatives imply the subcubic loop-choice oracle. -/
theorem subcubicLoopChoiceOracleAt_of_localGeometryAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hgeom : Theorem81SubcubicLocalGeometryAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    Theorem81SubcubicLoopChoiceOracleAt.{u, v}
      separatorScale branchScale targetScale n₀ := by
  intro V _ _ W _ _ G _ H _ _ hmax hn hsmall R hnot
  rcases hgeom G H hmax hn hsmall R hnot with
    ⟨i, hi, hlow | hhull⟩
  · rcases hlow with
      ⟨U, frontierU, hUsubsetC, hUnonempty, hfrontierU, hUsmall⟩
    exact Theorem81InvariantState.loopChoice_of_lowExpansionSet
      (R := R) hi hUsubsetC hUnonempty hfrontierU hUsmall
  · classical
    rcases hhull with ⟨hr, hCnonempty, hhull⟩
    by_cases hNnonempty :
        (activeNeighborFinset H R.state.active i).Nonempty
    · by_cases hcontacts :
        ∀ j : W, j ∈ activeNeighborFinset H R.state.active i →
          Theorem81InvariantState.BranchHasReservoirNeighbor R j
      · exact
          Theorem81InvariantState.loopChoice_of_contacts_and_connectedReservoirHull
            (R := R) hi hNnonempty hmax hcontacts hhull
      · push Not at hcontacts
        rcases hcontacts with ⟨j, hjN, hno⟩
        rcases (mem_activeNeighborFinset).1 hjN with ⟨hjactive, hij⟩
        exact ⟨i, hi, Or.inl ⟨j, hjactive, hij, hno⟩⟩
    · rcases hCnonempty with ⟨c, hc⟩
      have hnoActiveNeighbor :
          ∀ j : W, j ∈ R.state.active → ¬ H.Adj i j := by
        intro j hjactive hij
        exact hNnonempty ⟨j, (mem_activeNeighborFinset).2 ⟨hjactive, hij⟩⟩
      exact Theorem81InvariantState.loopChoice_of_no_active_neighbors
        (R := R) hi hc hnoActiveNeighbor hr

/-- The subcubic loop-choice oracle implies the fixed-constant subcubic
separator/minor alternative. -/
theorem expanderMinorTheoremAtSubcubic_of_subcubicLoopChoiceOracleAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (hchoice : Theorem81SubcubicLoopChoiceOracleAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAtSubcubic.{u, v}
      separatorScale targetScale n₀ := by
  intro V _ _ W _ _ G _ H _ _ hmax hn hsmall
  let r := branchScale * Nat.log 2 (Fintype.card V)
  have hprogress :
      ∀ R : Theorem81InvariantState H G separatorScale r,
        ¬ Theorem81InvariantState.FirstCrossingTerminal R →
          ∃ R' : Theorem81InvariantState H G separatorScale r,
            Theorem81InvariantState.FirstCrossingTerminal R' ∨
              Theorem81InvariantState.Step R R' := by
    intro R hnot
    rcases Theorem81InvariantState.exists_step_of_loopChoice
        (hchoice G H hmax hn hsmall R hnot) with ⟨R', hstep⟩
    exact ⟨R', Or.inr hstep⟩
  rcases Theorem81InvariantState.exists_firstCrossingTerminal_of_progress
      (H := H) (G := G) (d := separatorScale) (r := r)
      hprogress with ⟨R, hR⟩
  exact R.separator_or_minor_of_first_crossing
    (branchScale := branchScale) (targetScale := targetScale)
    le_rfl hscale hsmall hR

/-- The local geometric alternatives imply the fixed-constant subcubic
separator/minor alternative. -/
theorem expanderMinorTheoremAtSubcubic_of_localGeometryAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (hgeom : Theorem81SubcubicLocalGeometryAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAtSubcubic.{u, v}
      separatorScale targetScale n₀ :=
  expanderMinorTheoremAtSubcubic_of_subcubicLoopChoiceOracleAt hscale
    (subcubicLoopChoiceOracleAt_of_localGeometryAt hgeom)

/-- The Lemma-8.2-shaped reservoir geometry input implies the fixed-constant
subcubic separator/minor alternative. -/
theorem expanderMinorTheoremAtSubcubic_of_reservoirGeometryAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (hgeom : Theorem81ReservoirGeometryAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAtSubcubic.{u, v}
      separatorScale targetScale n₀ :=
  expanderMinorTheoremAtSubcubic_of_localGeometryAt hscale
    (subcubicLocalGeometryAt_of_reservoirGeometryAt hgeom)

/-- The unbundled reservoir alternative is enough for the fixed-constant
subcubic separator/minor alternative. -/
theorem expanderMinorTheoremAtSubcubic_of_reservoirAlternativeAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (halt : Theorem81ReservoirAlternativeAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAtSubcubic.{u, v}
      separatorScale targetScale n₀ :=
  expanderMinorTheoremAtSubcubic_of_reservoirGeometryAt hscale
    (reservoirGeometryAt_of_reservoirAlternativeAt halt)

/-- Full fixed-constant Theorem 8.1 from the two remaining mathematical
ingredients: the target-splitting reduction to subcubic graphs and the
Lemma-8.2-style reservoir alternative for subcubic targets. -/
theorem expanderMinorTheoremAt_of_subcubicExpansion_and_reservoirAlternativeAt
    {separatorScale branchScale subcubicTargetScale targetScale n₀
      complexityScale : ℕ}
    (hsubTarget : 3 * separatorScale * branchScale ≤ subcubicTargetScale)
    (htarget : subcubicTargetScale * complexityScale ≤ targetScale)
    (hexpand : SubcubicMinorExpansionProvider.{v} complexityScale)
    (halt : Theorem81ReservoirAlternativeAt.{u, v}
      separatorScale branchScale subcubicTargetScale n₀) :
    ExpanderMinorTheoremAt.{u, v} separatorScale targetScale n₀ :=
  expanderMinorTheoremAt_of_subcubicExpansion htarget hexpand
    (expanderMinorTheoremAtSubcubic_of_reservoirAlternativeAt
      hsubTarget halt)

/-- A loop-choice oracle gives the progress oracle by applying the appropriate
state transition. -/
theorem invariantProgressOracleAt_of_loopChoiceOracleAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hchoice : Theorem81LoopChoiceOracleAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    Theorem81InvariantProgressOracleAt.{u, v}
      separatorScale branchScale targetScale n₀ := by
  intro V _ _ W _ _ G H _ hn hsmall R hnonterminal
  rcases Theorem81InvariantState.exists_step_of_loopChoice
      (hchoice G H hn hsmall R hnonterminal) with ⟨R', hstep⟩
  exact ⟨R', Or.inr hstep⟩

/-- A local progress proof for the paper loop yields a bundled first-crossing
terminal certificate. -/
theorem invariantFirstCrossingTerminatesAt_of_progressOracleAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hprogress : Theorem81InvariantProgressOracleAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    Theorem81InvariantFirstCrossingTerminatesAt.{u, v}
      separatorScale branchScale targetScale n₀ := by
  intro V _ _ W _ _ G H _ hn hsmall
  exact Theorem81InvariantState.exists_firstCrossingTerminal_of_progress
    (H := H) (G := G) (d := separatorScale)
    (r := branchScale * Nat.log 2 (Fintype.card V))
    (hprogress G H hn hsmall)

/-- Forgetting the bundled invariant state gives the earlier unbundled
first-crossing termination interface. -/
theorem algorithmFirstCrossingTerminatesAt_of_invariantFirstCrossingTerminatesAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hterm : Theorem81InvariantFirstCrossingTerminatesAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    Theorem81AlgorithmFirstCrossingTerminatesAt.{u, v}
      separatorScale branchScale targetScale n₀ := by
  intro V _ _ W _ _ G H _ hn hsmall
  rcases hterm G H hn hsmall with ⟨R, hR⟩
  refine ⟨R.state, ?_⟩
  rcases hR with hminor | hsep
  · exact Or.inl hminor
  · rcases hsep with ⟨hAthird, hAbal⟩
    exact Or.inr
      ⟨hAthird, hAbal, R.branch_bound, R.frontier_bound⟩

/-- A completed state-machine proof of the Theorem 8.1 algorithm implies the
fixed-constant separator/minor alternative. -/
theorem expanderMinorTheoremAt_of_algorithmTerminatesAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (hterm : Theorem81AlgorithmTerminatesAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAt.{u, v}
      separatorScale targetScale n₀ := by
  intro V _ _ W _ _ G H _ hn hsmall
  rcases hterm G H hn hsmall with ⟨S, hS⟩
  rcases hS with hminor | hsep
  · exact Or.inr (S.isMinor_of_active_univ hminor)
  · rcases hsep with
      ⟨hAbal, hRbal, hbranch, hfrontier⟩
    have hterminal :
        Theorem81State.SeparatorTerminal S separatorScale :=
      S.separatorTerminal_of_targetSmall_and_frontier_bound'
        hAbal hRbal hbranch le_rfl
        hscale hsmall hfrontier
    exact Or.inl
      (S.hasSmallBalancedSeparator_of_terminal_A
        hterminal.1 hterminal.2.1 hterminal.2.2)

/-- First-crossing terminal certificates imply the fixed-constant
separator/minor alternative. -/
theorem expanderMinorTheoremAt_of_firstCrossingAlgorithmTerminatesAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (hterm : Theorem81AlgorithmFirstCrossingTerminatesAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAt.{u, v}
      separatorScale targetScale n₀ := by
  intro V _ _ W _ _ G H _ hn hsmall
  rcases hterm G H hn hsmall with ⟨S, hS⟩
  rcases hS with hminor | hsep
  · exact Or.inr (S.isMinor_of_active_univ hminor)
  · rcases hsep with
      ⟨hAthird, hAbal, hbranch, hfrontier⟩
    have hterminal :
        Theorem81State.SeparatorTerminal S separatorScale :=
      S.separatorTerminal_of_first_crossing_targetSmall
        hAthird hAbal hbranch le_rfl
        hscale hsmall hfrontier
    exact Or.inl
      (S.hasSmallBalancedSeparator_of_terminal_A
        hterminal.1 hterminal.2.1 hterminal.2.2)

/-- A local-progress proof for the bundled invariant state machine implies the
fixed-constant separator/minor alternative. -/
theorem expanderMinorTheoremAt_of_invariantProgressOracleAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (hprogress : Theorem81InvariantProgressOracleAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAt.{u, v}
      separatorScale targetScale n₀ :=
  expanderMinorTheoremAt_of_firstCrossingAlgorithmTerminatesAt hscale
    (algorithmFirstCrossingTerminatesAt_of_invariantFirstCrossingTerminatesAt
      (invariantFirstCrossingTerminatesAt_of_progressOracleAt hprogress))

/-- The loop-choice formulation of the paper algorithm implies the
fixed-constant separator/minor alternative. -/
theorem expanderMinorTheoremAt_of_loopChoiceOracleAt
    {separatorScale branchScale targetScale n₀ : ℕ}
    (hscale : 3 * separatorScale * branchScale ≤ targetScale)
    (hchoice : Theorem81LoopChoiceOracleAt.{u, v}
      separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheoremAt.{u, v}
      separatorScale targetScale n₀ :=
  expanderMinorTheoremAt_of_invariantProgressOracleAt hscale
    (invariantProgressOracleAt_of_loopChoiceOracleAt hchoice)

/-- Family-level bridge from the completed algorithmic proof to the theorem
family. -/
theorem expanderMinorTheorem_of_algorithmTerminates
    (h :
      ∀ separatorScale : ℕ, 0 < separatorScale →
        ∃ branchScale targetScale n₀ : ℕ,
          0 < targetScale ∧
          3 * separatorScale * branchScale ≤ targetScale ∧
          Theorem81AlgorithmTerminatesAt.{u, v}
            separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheorem.{u, v} := by
  intro separatorScale hsep
  rcases h separatorScale hsep with
    ⟨branchScale, targetScale, n₀, htargetPos, hscale, hterm⟩
  exact ⟨targetScale, n₀, htargetPos,
    expanderMinorTheoremAt_of_algorithmTerminatesAt hscale hterm⟩

/-- Family-level bridge from the first-crossing algorithmic proof to the
theorem family. -/
theorem expanderMinorTheorem_of_firstCrossingAlgorithmTerminates
    (h :
      ∀ separatorScale : ℕ, 0 < separatorScale →
        ∃ branchScale targetScale n₀ : ℕ,
          0 < targetScale ∧
          3 * separatorScale * branchScale ≤ targetScale ∧
          Theorem81AlgorithmFirstCrossingTerminatesAt.{u, v}
            separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheorem.{u, v} := by
  intro separatorScale hsep
  rcases h separatorScale hsep with
    ⟨branchScale, targetScale, n₀, htargetPos, hscale, hterm⟩
  exact ⟨targetScale, n₀, htargetPos,
    expanderMinorTheoremAt_of_firstCrossingAlgorithmTerminatesAt
      hscale hterm⟩

/-- Family-level bridge from local progress for the invariant state machine to
Theorem 8.1. -/
theorem expanderMinorTheorem_of_invariantProgressOracle
    (h :
      ∀ separatorScale : ℕ, 0 < separatorScale →
        ∃ branchScale targetScale n₀ : ℕ,
          0 < targetScale ∧
          3 * separatorScale * branchScale ≤ targetScale ∧
          Theorem81InvariantProgressOracleAt.{u, v}
            separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheorem.{u, v} := by
  intro separatorScale hsep
  rcases h separatorScale hsep with
    ⟨branchScale, targetScale, n₀, htargetPos, hscale, hprogress⟩
  exact ⟨targetScale, n₀, htargetPos,
    expanderMinorTheoremAt_of_invariantProgressOracleAt
      hscale hprogress⟩

/-- Family-level bridge from loop choices for the invariant state machine to
Theorem 8.1. -/
theorem expanderMinorTheorem_of_loopChoiceOracle
    (h :
      ∀ separatorScale : ℕ, 0 < separatorScale →
        ∃ branchScale targetScale n₀ : ℕ,
          0 < targetScale ∧
          3 * separatorScale * branchScale ≤ targetScale ∧
          Theorem81LoopChoiceOracleAt.{u, v}
            separatorScale branchScale targetScale n₀) :
    ExpanderMinorTheorem.{u, v} := by
  intro separatorScale hsep
  rcases h separatorScale hsep with
    ⟨branchScale, targetScale, n₀, htargetPos, hscale, hchoice⟩
  exact ⟨targetScale, n₀, htargetPos,
    expanderMinorTheoremAt_of_loopChoiceOracleAt hscale hchoice⟩

/-- If the fixed-constant Theorem 8.1 statement is available, then any graph
satisfying the target-size hypothesis has the advertised separator/minor
alternative. -/
theorem separator_or_minor_of_expanderMinorTheoremAt
    {separatorScale targetScale n₀ : ℕ}
    (h : ExpanderMinorTheoremAt.{u, v} separatorScale targetScale n₀)
    {V : Type u} [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    [Fintype H.edgeSet]
    (hn : n₀ ≤ Fintype.card V)
    (hsmall : TargetSmallForHost (V := V) H targetScale) :
    HasSmallBalancedSeparator G separatorScale ∨ IsMinor H G :=
  h G H hn hsmall

/-- The no-small-separator minor-universality branch implies the full
separator/minor alternative of Theorem 8.1. -/
theorem expanderMinorTheoremAt_of_minorUniversalNoSmallSeparatorAt
    {separatorScale targetScale n₀ : ℕ}
    (h : MinorUniversalNoSmallSeparatorAt.{u, v}
      separatorScale targetScale n₀) :
    ExpanderMinorTheoremAt.{u, v} separatorScale targetScale n₀ := by
  intro V _ _ W _ _ G H _ hn hsmall
  by_cases hsep : HasSmallBalancedSeparator G separatorScale
  · exact Or.inl hsep
  · exact Or.inr (h G H hn hsmall hsep)

/-- Family-level version of
`expanderMinorTheoremAt_of_minorUniversalNoSmallSeparatorAt`. -/
theorem expanderMinorTheorem_of_minorUniversalNoSmallSeparator
    (h :
      ∀ separatorScale : ℕ, 0 < separatorScale →
        ∃ targetScale n₀ : ℕ,
          0 < targetScale ∧
            MinorUniversalNoSmallSeparatorAt.{u, v}
              separatorScale targetScale n₀) :
    ExpanderMinorTheorem.{u, v} := by
  intro separatorScale hsep
  rcases h separatorScale hsep with ⟨targetScale, n₀, htarget, hminor⟩
  exact ⟨targetScale, n₀, htarget,
    expanderMinorTheoremAt_of_minorUniversalNoSmallSeparatorAt hminor⟩

/-- Unpack the theorem-family statement at a fixed separator scale. -/
theorem exists_constants_for_separatorScale
    (h : ExpanderMinorTheorem.{u, v})
    {separatorScale : ℕ} (hsep : 0 < separatorScale) :
    ∃ targetScale n₀ : ℕ,
      0 < targetScale ∧ ExpanderMinorTheoremAt.{u, v}
        separatorScale targetScale n₀ :=
  h separatorScale hsep

end SimpleGraph

end Lax17Proofs
