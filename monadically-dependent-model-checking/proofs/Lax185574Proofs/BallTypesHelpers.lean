import Lax185574.PhiPatterns
import Lax185574.DefinableFlips
import Lax185574Proofs.BipartiteBasics
import Lax185574Proofs.FlipBasics
import Mathlib.Data.Fin.Tuple.Basic

/-!
Auxiliary facts for the few-types-in-balls lemma: adjacency in a
definable flip, writing a flip over a small set as `G ⊕ (p̄, R)`, the
two edge formulas, extending a pattern by a row, and the atomic types of
a set as those of a bipartite graph.
-/

namespace Lax185574Proofs.BallTypesHelpers

open FirstOrder FirstOrder.Language
open Lax185574.Flips Lax185574.Partitions Lax185574.AtomicTypes Lax185574.DefinableFlips
open Lax185574.PhiPsiPatterns Lax185574.PhiPatterns Lax185574.BipartiteGraphs

universe u

variable {V : Type u}

theorem flipOver_adj (G : SimpleGraph V) {s : ℕ} (p : Fin s → V)
    (R : (Fin s → PairType) → (Fin s → PairType) → Prop) (hR : ∀ P Q, R P Q → R Q P)
    (x y : V) :
    (flipOver G p R).Adj x y ↔
      x ≠ y ∧ Xor (G.Adj x y) (R (atomicTypeOver G p x) (atomicTypeOver G p y)) := by
  unfold flipOver
  rw [SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ?_
  have h : Xor (G.Adj y x) (R (atomicTypeOver G p y) (atomicTypeOver G p x)) ↔
      Xor (G.Adj x y) (R (atomicTypeOver G p x) (atomicTypeOver G p y)) := by
    rw [G.adj_comm]
    have : R (atomicTypeOver G p y) (atomicTypeOver G p x) ↔
        R (atomicTypeOver G p x) (atomicTypeOver G p y) := ⟨hR _ _, hR _ _⟩
    simp only [Xor, this]
  rw [h, or_self]

/-- Two vertices have the same atomic type over a tuple exactly when they
lie in the same part of the partition into atomic types over its set of
entries. -/
theorem atomicTypeOver_eq_iff (G : SimpleGraph V) {s : ℕ} (p : Fin s → V) (x y : V) :
    atomicTypeOver G p x = atomicTypeOver G p y ↔ atomicTypes G (Set.range p) x y := by
  classical
  rw [Lax185574Proofs.FlipBasics.atomicTypes_rel_iff', funext_iff]
  simp only [atomicTypeOver, pairType]
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    right
    have hx : x ∉ Set.range p := by
      rintro ⟨i, rfl⟩
      have := h i
      simp only [if_true] at this
      split_ifs at this with h1
      exact hxy h1.symm
    have hy : y ∉ Set.range p := by
      rintro ⟨i, rfl⟩
      have := h i
      simp only [if_true] at this
      split_ifs at this
    refine ⟨hx, hy, ?_⟩
    rintro _ ⟨i, rfl⟩
    have := h i
    have h1 : x ≠ p i := fun e => hx ⟨i, e.symm⟩
    have h2 : y ≠ p i := fun e => hy ⟨i, e.symm⟩
    simp only [h1, h2, if_false] at this
    split_ifs at this <;> simp_all
  · rintro (rfl | ⟨hx, hy, h⟩) i
    · rfl
    have h1 : x ≠ p i := fun e => hx ⟨i, e.symm⟩
    have h2 : y ≠ p i := fun e => hy ⟨i, e.symm⟩
    simp only [h1, h2, if_false, h (p i) ⟨i, rfl⟩]

/-- Every flip over a set of at most `s` vertices is `G ⊕ (p̄, R)` for an
`s`-tuple `p̄` and a symmetric relation `R`, provided there is a vertex. -/
theorem exists_eq_flipOver (G H : SimpleGraph V) {s : ℕ} (hH : IsDefinableFlip G s H) (v₀ : V) :
    ∃ (p : Fin s → V) (R : (Fin s → PairType) → (Fin s → PairType) → Prop),
      (∀ P Q, R P Q → R Q P) ∧ H = flipOver G p R := by
  classical
  obtain ⟨S, hS, hflip⟩ := hH
  let e := S.equivFin
  let p : Fin s → V := fun i => if h : (i : ℕ) < S.card then (e.symm ⟨i, h⟩ : V) else v₀
  have hSp : (S : Set V) ⊆ Set.range p := by
    intro x hx
    refine ⟨⟨e ⟨x, hx⟩, by omega⟩, ?_⟩
    simp [p]
  have hflip : IsFlip G (atomicTypes G (Set.range p)) H :=
    Lax185574Proofs.FlipBasics.isFlip_mono (Lax185574Proofs.FlipBasics.atomicTypes_anti G hSp) hflip
  let R : (Fin s → PairType) → (Fin s → PairType) → Prop := fun P Q =>
    ∃ x y, atomicTypeOver G p x = P ∧ atomicTypeOver G p y = Q ∧ x ≠ y ∧ ¬ (H.Adj x y ↔ G.Adj x y)
  have hR : ∀ P Q, R P Q → R Q P := by
    rintro P Q ⟨x, y, hx, hy, hxy, h⟩
    exact ⟨y, x, hy, hx, hxy.symm, by rwa [H.adj_comm, G.adj_comm]⟩
  refine ⟨p, R, hR, ?_⟩
  ext x y
  rw [flipOver_adj G p R hR]
  by_cases hxy : x = y
  · subst hxy; simp
  rcases hflip x y with h | h
  · have hn : ¬ R (atomicTypeOver G p x) (atomicTypeOver G p y) := by
      rintro ⟨x', y', hx', hy', hxy', h'⟩
      exact h' (h x' y' ((atomicTypeOver_eq_iff G p x' x).mp hx')
        ((atomicTypeOver_eq_iff G p y' y).mp hy') hxy')
    have := h x y (Setoid.refl' _ x) (Setoid.refl' _ y) hxy
    simp only [Xor, hn, this]
    tauto
  · by_cases hd : R (atomicTypeOver G p x) (atomicTypeOver G p y)
    · have := h x y (Setoid.refl' _ x) (Setoid.refl' _ y) hxy
      simp only [Xor, hd, this]
      tauto
    · exfalso
      exact hd ⟨x, y, rfl, rfl, hxy, by
        rw [h x y (Setoid.refl' _ x) (Setoid.refl' _ y) hxy]; tauto⟩

/-- The edge formula `E(y, z)` or its negation, according to `N`. -/
def edgeOrNot (N : Bool) : Language.graph.Formula (Fin 1 ⊕ Fin 1) :=
  if N then edgeFormula else edgeFormula.not

theorem holds_edgeOrNot (G : SimpleGraph V) (N : Bool) (w c : V) :
    Holds G (edgeOrNot N) ![w] c ↔ (G.Adj w c ↔ N = true) := by
  cases N
  · simp only [edgeOrNot, Bool.false_eq_true, if_false]
    change ¬ G.Adj w c ↔ _
    simp
  · simp only [edgeOrNot, if_true]
    change G.Adj w c ↔ _
    simp

/-- Adding a row to a pattern. -/
theorem isPattern_snoc (G : SimpleGraph V) {p p' : ℕ}
    {φ : Language.graph.Formula (Fin p ⊕ Fin 1)} {ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)}
    {ℓ t : ℕ} {a : Fin ℓ → Fin p → V} {b : Fin t → Fin p' → V} {c : Fin ℓ → Fin t → V}
    (h : IsPattern G φ ψ a b c) (a' : Fin p → V) (c' : Fin t → V)
    (h1 : ∀ j, Holds G φ a' (c' j)) (h2 : ∀ i j, ¬ Holds G φ a' (c i j))
    (h3 : ∀ j, Holds G ψ (b j) (c' j)) (h4 : ∀ j j', j < j' → ¬ Holds G ψ (b j') (c' j)) :
    IsPattern G φ ψ (Fin.snoc a a') b (Fin.snoc c c') := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last]
    refine ⟨⟨h1 j, fun i' hi' => absurd hi' (not_lt.mpr (Fin.le_last i'))⟩, h3 j, h4 j⟩
  · simp only [Fin.snoc_castSucc]
    obtain ⟨⟨k1, k2⟩, k3, k4⟩ := h i j
    refine ⟨⟨k1, fun i' => ?_⟩, k3, k4⟩
    refine Fin.lastCases ?_ (fun i' => ?_) i'
    · intro _; simp only [Fin.snoc_last]; exact h2 i j
    · intro hi'
      simp only [Fin.snoc_castSucc]
      exact k2 i' (Fin.castSucc_lt_castSucc_iff.mp hi')

/-- The atomic types over `A` of the vertices of a set `B` disjoint from
`A` are those of the bipartite graph between `B` and `A`. -/
theorem atomicTypeCount_eq_bipartite (H : SimpleGraph V) (B A : Set V) (hBA : Disjoint B A) :
    atomicTypeCount H B A =
      atomicTypeCount (bipartiteGraph fun (x : B) (y : A) => H.Adj x y)
        (Set.range Sum.inl) (Set.range Sum.inr) := by
  classical
  rw [Lax185574Proofs.AtomicTypeBridge.atomicTypeCount_eq_partCount,
    Lax185574Proofs.AtomicTypeBridge.atomicTypeCount_eq_partCount, partCount, partCount]
  have e1 : Quotient.mk (atomicTypes H A) '' B =
      (Quotient.mk (atomicTypes H A) ∘ Subtype.val) '' (Set.univ : Set B) := by
    rw [Set.image_comp]; simp
  have e2 : ∀ (P : Setoid (B ⊕ A)), Quotient.mk P '' Set.range (Sum.inl : B → B ⊕ A) =
      (Quotient.mk P ∘ Sum.inl) '' (Set.univ : Set B) := by
    intro P; rw [Set.image_comp, Set.image_univ]
  rw [e1, e2]
  refine Lax185574Proofs.AtomicTypeBridge.ncard_image_congr _ _ fun x _ y _ => ?_
  simp only [Function.comp_apply]
  rw [Quotient.eq, Quotient.eq, Lax185574Proofs.FlipBasics.atomicTypes_rel_iff',
    Lax185574Proofs.FlipBasics.atomicTypes_rel_iff']
  have hx : (x : V) ∉ A := Set.disjoint_left.mp hBA x.2
  have hy : (y : V) ∉ A := Set.disjoint_left.mp hBA y.2
  constructor
  · rintro (h | ⟨-, -, h⟩)
    · exact Or.inl (by rw [Subtype.ext h])
    · right
      refine ⟨by simp, by simp, ?_⟩
      rintro _ ⟨z, rfl⟩
      simpa using h z z.2
  · rintro (h | ⟨-, -, h⟩)
    · exact Or.inl (by rw [Sum.inl_injective h])
    · right
      refine ⟨hx, hy, fun z hz => ?_⟩
      simpa using h (Sum.inr ⟨z, hz⟩) ⟨⟨z, hz⟩, rfl⟩

end Lax185574Proofs.BallTypesHelpers
