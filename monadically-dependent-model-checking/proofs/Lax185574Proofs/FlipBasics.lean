import Lax185574.DefinableFlips

/-!
Basic facts about flips over partitions and about the partition into
atomic types: reflexivity, composition of flips, refinement of atomic
types under enlarging the parameter set and under flipping.
-/

namespace Lax185574Proofs.FlipBasics

open Lax185574.Flips Lax185574.Partitions Lax185574.DefinableFlips

universe u

variable {V : Type u}

/-- Every graph is a flip of itself for every partition. -/
theorem isFlip_refl (G : SimpleGraph V) (P : Setoid V) : IsFlip G P G :=
  fun _ _ => Or.inl fun _ _ _ _ _ => Iff.rfl

/-- A refinement of the partition of a flip still carries the flip. -/
theorem isFlip_mono {G H : SimpleGraph V} {P Q : Setoid V} (hQP : Q ≤ P)
    (h : IsFlip G P H) : IsFlip G Q H := by
  intro a b
  rcases h a b with h | h
  · exact Or.inl fun x y hx hy hxy => h x y (hQP hx) (hQP hy) hxy
  · exact Or.inr fun x y hx hy hxy => h x y (hQP hx) (hQP hy) hxy

/-- A flip of a flip is a flip for every common refinement of the two
partitions. -/
theorem isFlip_trans {G₀ G₁ G₂ : SimpleGraph V} {P P₁ P₂ : Setoid V}
    (h₁ : IsFlip G₀ P₁ G₁) (h₂ : IsFlip G₁ P₂ G₂) (hP₁ : P ≤ P₁) (hP₂ : P ≤ P₂) :
    IsFlip G₀ P G₂ := by
  intro a b
  rcases h₁ a b with k | k <;> rcases h₂ a b with l | l
  · exact Or.inl fun x y hx hy hxy => (l x y (hP₂ hx) (hP₂ hy) hxy).trans
      (k x y (hP₁ hx) (hP₁ hy) hxy)
  · exact Or.inr fun x y hx hy hxy => (l x y (hP₂ hx) (hP₂ hy) hxy).trans
      (not_congr (k x y (hP₁ hx) (hP₁ hy) hxy))
  · exact Or.inr fun x y hx hy hxy => (l x y (hP₂ hx) (hP₂ hy) hxy).trans
      (k x y (hP₁ hx) (hP₁ hy) hxy)
  · exact Or.inl fun x y hx hy hxy => by
      rw [l x y (hP₂ hx) (hP₂ hy) hxy, k x y (hP₁ hx) (hP₁ hy) hxy, not_not]

/-- Unfolding the partition into atomic types. -/
theorem atomicTypes_rel_iff (G : SimpleGraph V) (S : Set V) (x y : V) :
    atomicTypes G S x y ↔ (S ∩ {x} = S ∩ {y} ∧ S ∩ G.neighborSet x = S ∩ G.neighborSet y) := by
  change (S ∩ {x}, S ∩ G.neighborSet x) = (S ∩ {y}, S ∩ G.neighborSet y) ↔ _
  exact Prod.ext_iff

/-- Two vertices have the same atomic type over `S` if and only if they
are equal, or both lie outside `S` and agree on adjacency to every vertex
of `S`. -/
theorem atomicTypes_rel_iff' (G : SimpleGraph V) (S : Set V) (x y : V) :
    atomicTypes G S x y ↔
      (x = y ∨ (x ∉ S ∧ y ∉ S ∧ ∀ s ∈ S, (G.Adj x s ↔ G.Adj y s))) := by
  rw [atomicTypes_rel_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hxy : x = y
    · exact Or.inl hxy
    right
    have hx : x ∉ S := fun hx => by
      have : x ∈ S ∩ {y} := h1 ▸ ⟨hx, rfl⟩
      exact hxy this.2
    have hy : y ∉ S := fun hy => by
      have : y ∈ S ∩ {x} := h1.symm ▸ ⟨hy, rfl⟩
      exact hxy this.2.symm
    refine ⟨hx, hy, fun s hs => ?_⟩
    have := congrArg (fun T => s ∈ T) h2
    simpa [hs, SimpleGraph.mem_neighborSet] using this
  · rintro (rfl | ⟨hx, hy, h⟩)
    · exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · ext z; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz, rfl⟩; exact absurd hz hx
      · rintro ⟨hz, rfl⟩; exact absurd hz hy
    · ext z; simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
      exact ⟨fun ⟨hz, h'⟩ => ⟨hz, (h z hz).1 h'⟩, fun ⟨hz, h'⟩ => ⟨hz, (h z hz).2 h'⟩⟩

/-- Enlarging the parameter set refines the partition into atomic types. -/
theorem atomicTypes_anti (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) :
    atomicTypes G T ≤ atomicTypes G S := by
  intro x y h
  rw [atomicTypes_rel_iff'] at h ⊢
  rcases h with h | ⟨hx, hy, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨fun h' => hx (hST h'), fun h' => hy (hST h'), fun s hs => h s (hST hs)⟩

/-- If `G₁` is an `S₁`-flip of `G₀` and `S₂` is another set, then the
partition into atomic types over `S₁ ∪ S₂` in `G₀` refines the partition
into atomic types over `S₂` in `G₁`. -/
theorem atomicTypes_union_le_of_isFlip {G₀ G₁ : SimpleGraph V} {S₁ S₂ : Set V}
    (h : IsFlip G₀ (atomicTypes G₀ S₁) G₁) :
    atomicTypes G₀ (S₁ ∪ S₂) ≤ atomicTypes G₁ S₂ := by
  intro x y hxy
  have h1 : atomicTypes G₀ S₁ x y := atomicTypes_anti G₀ Set.subset_union_left hxy
  rw [atomicTypes_rel_iff'] at hxy ⊢
  rcases hxy with hxy | ⟨hx, hy, hxy⟩
  · exact Or.inl hxy
  refine Or.inr ⟨fun h' => hx (Set.mem_union_right _ h'),
    fun h' => hy (Set.mem_union_right _ h'), fun s hs => ?_⟩
  have hsx : x ≠ s := fun e => hx (e ▸ Set.mem_union_right _ hs)
  have hsy : y ≠ s := fun e => hy (e ▸ Set.mem_union_right _ hs)
  have hG := hxy s (Set.mem_union_right _ hs)
  rcases h x s with k | k
  · rw [k x s (Setoid.refl' _ x) (Setoid.refl' _ s) hsx,
      k y s (Setoid.symm' _ h1) (Setoid.refl' _ s) hsy]
    exact hG
  · rw [k x s (Setoid.refl' _ x) (Setoid.refl' _ s) hsx,
      k y s (Setoid.symm' _ h1) (Setoid.refl' _ s) hsy]
    exact not_congr hG

end Lax185574Proofs.FlipBasics
