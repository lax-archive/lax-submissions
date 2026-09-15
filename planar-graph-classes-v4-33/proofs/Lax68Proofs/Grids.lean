import Lax68
import Mathlib
set_option autoImplicit false
namespace Lax68Proofs
open SimpleGraph Set

private def gp {m n : ℕ} (v : Fin m × Fin n) : Lax68.StraightLineDrawings.Point :=
  ((v.1.val : ℝ), (v.2.val : ℝ))

private theorem gp_inj {m n : ℕ} : Function.Injective (@gp m n) := by
  intro u v h; apply Prod.ext
  · apply Fin.ext; exact_mod_cast (by simpa [gp] using congrArg Prod.fst h)
  · apply Fin.ext; exact_mod_cast (by simpa [gp] using congrArg Prod.snd h)

private theorem grid_adj {m n : ℕ} {a b : Fin m × Fin n}
    (h : (pathGraph m □ pathGraph n).Adj a b) :
    (Lax68.GridsAndWalls.consecutive a.1.val b.1.val ∧ a.2 = b.2) ∨
    (Lax68.GridsAndWalls.consecutive a.2.val b.2.val ∧ a.1 = b.1) := by
  rcases h with h | h
  · exact Or.inl ⟨pathGraph_adj.mp h.1, h.2⟩
  · exact Or.inr ⟨pathGraph_adj.mp h.1, h.2⟩

private theorem same_seg {x y : ℝ} (h : y ∈ segment ℝ x x) : y = x := by
  simpa [segment_same] using h

private theorem nat_unit {a b c : ℕ} (hab : Lax68.GridsAndWalls.consecutive a b)
    (hc : (c : ℝ) ∈ segment ℝ (a : ℝ) (b : ℝ)) : c = a ∨ c = b := by
  rw [segment_eq_uIcc] at hc
  rcases Set.mem_uIcc.mp hc with ⟨hl, hu⟩ | ⟨hl, hu⟩
  · have hl' : a ≤ c := by exact_mod_cast hl
    have hu' : c ≤ b := by exact_mod_cast hu
    rcases hab with hab | hab <;> omega
  · have hl' : b ≤ c := by exact_mod_cast hl
    have hu' : c ≤ a := by exact_mod_cast hu
    rcases hab with hab | hab <;> omega

private theorem succ_overlap {a c : ℕ} {x : ℝ}
    (ha : x ∈ segment ℝ (a : ℝ) ((a + 1 : ℕ) : ℝ))
    (hc : x ∈ segment ℝ (c : ℝ) ((c + 1 : ℕ) : ℝ)) :
    a = c ∨ a = c + 1 ∨ a + 1 = c ∨ a + 1 = c + 1 := by
  rw [segment_eq_uIcc, Set.uIcc_of_le (by norm_num)] at ha
  rw [segment_eq_uIcc, Set.uIcc_of_le (by norm_num)] at hc
  have h₁ : a ≤ c + 1 := by exact_mod_cast (le_trans ha.1 hc.2)
  have h₂ : c ≤ a + 1 := by exact_mod_cast (le_trans hc.1 ha.2)
  omega

private theorem unit_overlap {a b c d : ℕ} {x : ℝ}
    (hab : Lax68.GridsAndWalls.consecutive a b)
    (hcd : Lax68.GridsAndWalls.consecutive c d)
    (ha : x ∈ segment ℝ (a : ℝ) (b : ℝ))
    (hc : x ∈ segment ℝ (c : ℝ) (d : ℝ)) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  rcases hab with hab | hab <;> rcases hcd with hcd | hcd
  · subst b; subst d; exact succ_overlap ha hc
  · subst b; subst c
    rcases succ_overlap ha (by simpa [segment_symm] using hc) with h | h | h | h <;> omega
  · subst a; subst d
    rcases succ_overlap (by simpa [segment_symm] using ha) hc with h | h | h | h <;> omega
  · subst a; subst c
    rcases succ_overlap (by simpa [segment_symm] using ha)
      (by simpa [segment_symm] using hc) with h | h | h | h <;> omega

private theorem horizontal {m n : ℕ} {a b c d : Fin m × Fin n} {x : ℝ × ℝ}
    (hab : Lax68.GridsAndWalls.consecutive a.1.val b.1.val) (hab₂ : a.2 = b.2)
    (hcd : Lax68.GridsAndWalls.consecutive c.1.val d.1.val) (hcd₂ : c.2 = d.2)
    (ha : x ∈ segment ℝ (gp a) (gp b)) (hc : x ∈ segment ℝ (gp c) (gp d)) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  have ha' := Prod.segment_subset (𝕜 := ℝ) _ _ ha
  have hc' := Prod.segment_subset (𝕜 := ℝ) _ _ hc
  have hax : x.2 = (a.2.val : ℝ) := by simpa [gp, hab₂, segment_same] using ha'.2
  have hcx : x.2 = (c.2.val : ℝ) := by simpa [gp, hcd₂, segment_same] using hc'.2
  have hac₂ : a.2 = c.2 := by apply Fin.ext; exact_mod_cast hax.symm.trans hcx
  rcases unit_overlap hab hcd (by simpa [gp] using ha'.1)
      (by simpa [gp] using hc'.1) with h | h | h | h
  · exact Or.inl (Prod.ext (Fin.ext h) hac₂)
  · exact Or.inr (Or.inl (Prod.ext (Fin.ext h) (hac₂.trans hcd₂)))
  · exact Or.inr (Or.inr (Or.inl (Prod.ext (Fin.ext h) (hab₂.symm.trans hac₂))))
  · exact Or.inr (Or.inr (Or.inr (Prod.ext (Fin.ext h) ((hab₂.symm.trans hac₂).trans hcd₂))))

private theorem vertical {m n : ℕ} {a b c d : Fin m × Fin n} {x : ℝ × ℝ}
    (hab : Lax68.GridsAndWalls.consecutive a.2.val b.2.val) (hab₁ : a.1 = b.1)
    (hcd : Lax68.GridsAndWalls.consecutive c.2.val d.2.val) (hcd₁ : c.1 = d.1)
    (ha : x ∈ segment ℝ (gp a) (gp b)) (hc : x ∈ segment ℝ (gp c) (gp d)) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  have ha' := Prod.segment_subset (𝕜 := ℝ) _ _ ha
  have hc' := Prod.segment_subset (𝕜 := ℝ) _ _ hc
  have hax : x.1 = (a.1.val : ℝ) := by simpa [gp, hab₁, segment_same] using ha'.1
  have hcx : x.1 = (c.1.val : ℝ) := by simpa [gp, hcd₁, segment_same] using hc'.1
  have hac₁ : a.1 = c.1 := by apply Fin.ext; exact_mod_cast hax.symm.trans hcx
  rcases unit_overlap hab hcd (by simpa [gp] using ha'.2)
      (by simpa [gp] using hc'.2) with h | h | h | h
  · exact Or.inl (Prod.ext hac₁ (Fin.ext h))
  · exact Or.inr (Or.inl (Prod.ext (hac₁.trans hcd₁) (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inl (Prod.ext (hab₁.symm.trans hac₁) (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Prod.ext ((hab₁.symm.trans hac₁).trans hcd₁) (Fin.ext h))))

private theorem crossing {m n : ℕ} {a b c d : Fin m × Fin n} {x : ℝ × ℝ}
    (hab : Lax68.GridsAndWalls.consecutive a.1.val b.1.val) (hab₂ : a.2 = b.2)
    (hcd : Lax68.GridsAndWalls.consecutive c.2.val d.2.val) (hcd₁ : c.1 = d.1)
    (ha : x ∈ segment ℝ (gp a) (gp b)) (hc : x ∈ segment ℝ (gp c) (gp d)) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  have ha' := Prod.segment_subset (𝕜 := ℝ) _ _ ha
  have hc' := Prod.segment_subset (𝕜 := ℝ) _ _ hc
  have hx₁ : x.1 = (c.1.val : ℝ) := by simpa [gp, hcd₁, segment_same] using hc'.1
  have hx₂ : x.2 = (a.2.val : ℝ) := by simpa [gp, hab₂, segment_same] using ha'.2
  have hf := nat_unit hab (c := c.1.val) (by simpa [gp, hx₁] using ha'.1)
  have hs := nat_unit hcd (c := a.2.val) (by simpa [gp, hx₂] using hc'.2)
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · exact Or.inl (Prod.ext (Fin.ext hf.symm) (Fin.ext hs))
  · exact Or.inr (Or.inl (Prod.ext ((Fin.ext hf.symm).trans hcd₁) (Fin.ext hs)))
  · exact Or.inr (Or.inr (Or.inl (Prod.ext (Fin.ext hf.symm) (hab₂.symm.trans (Fin.ext hs)))))
  · exact Or.inr (Or.inr (Or.inr (Prod.ext ((Fin.ext hf.symm).trans hcd₁)
      (hab₂.symm.trans (Fin.ext hs)))))

private def gridDrawing (m n : ℕ) :
    Lax68.StraightLineDrawings.StraightLineDrawing (pathGraph m □ pathGraph n) where
  point := gp
  injective := gp_inj
  noVertexOnEdge := by
    intro a b c hab hca hcb hc
    have hc' := Prod.segment_subset (𝕜 := ℝ) _ _ hc
    rcases grid_adj hab with ⟨hab, hab₂⟩ | ⟨hab, hab₁⟩
    · have hc₂ : c.2 = b.2 := by
        apply Fin.ext
        have hreal : (c.2.val : ℝ) = (b.2.val : ℝ) :=
          same_seg (by simpa [gp, hab₂] using hc'.2)
        exact_mod_cast hreal
      rcases nat_unit hab (by simpa [gp] using hc'.1) with h | h
      · exact hca (Prod.ext (Fin.ext h) (hc₂.trans hab₂.symm))
      · exact hcb (Prod.ext (Fin.ext h) hc₂)
    · have hc₁ : c.1 = b.1 := by
        apply Fin.ext
        have hreal : (c.1.val : ℝ) = (b.1.val : ℝ) :=
          same_seg (by simpa [gp, hab₁] using hc'.1)
        exact_mod_cast hreal
      rcases nat_unit hab (by simpa [gp] using hc'.2) with h | h
      · exact hca (Prod.ext (hc₁.trans hab₁.symm) (Fin.ext h))
      · exact hcb (Prod.ext hc₁ (Fin.ext h))
  disjointEdges := by
    intro a b c d hab hcd hd
    rw [Set.disjoint_left]; intro x hax hcx
    have ne : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
      constructor
      · intro h
        exact Set.disjoint_left.mp hd (show a ∈ ({a, b} : Set _) by simp)
          (show a ∈ ({c, d} : Set _) by simp [h])
      constructor
      · intro h
        exact Set.disjoint_left.mp hd (show a ∈ ({a, b} : Set _) by simp)
          (show a ∈ ({c, d} : Set _) by simp [h])
      constructor
      · intro h
        exact Set.disjoint_left.mp hd (show b ∈ ({a, b} : Set _) by simp)
          (show b ∈ ({c, d} : Set _) by simp [h])
      · intro h
        exact Set.disjoint_left.mp hd (show b ∈ ({a, b} : Set _) by simp)
          (show b ∈ ({c, d} : Set _) by simp [h])
    rcases grid_adj hab with ⟨hab, h₂⟩ | ⟨hab, h₁⟩ <;>
      rcases grid_adj hcd with ⟨hcd, k₂⟩ | ⟨hcd, k₁⟩
    · rcases horizontal hab h₂ hcd k₂ hax hcx with h | h | h | h
      · exact ne.1 h
      · exact ne.2.1 h
      · exact ne.2.2.1 h
      · exact ne.2.2.2 h
    · rcases crossing hab h₂ hcd k₁ hax hcx with h | h | h | h
      · exact ne.1 h
      · exact ne.2.1 h
      · exact ne.2.2.1 h
      · exact ne.2.2.2 h
    · rcases crossing hcd k₂ hab h₁ hcx hax with h | h | h | h
      · exact ne.1 h.symm
      · exact ne.2.2.1 h.symm
      · exact ne.2.1 h.symm
      · exact ne.2.2.2 h.symm
    · rcases vertical hab h₁ hcd k₁ hax hcx with h | h | h | h
      · exact ne.1 h
      · exact ne.2.1 h
      · exact ne.2.2.1 h
      · exact ne.2.2.2 h

/--
---
conclusion: Lax68.GridPlanar.grid_planar
---
Place grid vertices at integer row-column coordinates. Grid edges become
unit axis-aligned segments, which meet only at common endpoints.
-/
theorem grid_planar {V : Type*} {G : SimpleGraph V} :
    Lax68.GridsAndWalls.IsGrid G → Lax68.Planar.IsPlanar G := by
  rintro ⟨m, n, _, _, ⟨e⟩⟩
  let D := gridDrawing m n
  refine ⟨{
    point := fun v => D.point (e v)
    injective := D.injective.comp e.injective
    noVertexOnEdge := ?_
    disjointEdges := ?_
  }⟩
  · intro a b c hab hca hcb
    exact D.noVertexOnEdge (e.map_adj_iff.mpr hab)
      (fun h => hca (e.injective h)) (fun h => hcb (e.injective h))
  · intro a b c d hab hcd hd
    apply D.disjointEdges (e.map_adj_iff.mpr hab) (e.map_adj_iff.mpr hcd)
    rw [Set.disjoint_left] at hd ⊢
    intro x hx hy
    apply hd (a := e.symm x)
    · rcases hx with hx | hx
      · left; simpa [hx]
      · right
        rw [Set.mem_singleton_iff] at hx
        simpa [hx]
    · rcases hy with hy | hy
      · left; simpa [hy]
      · right
        rw [Set.mem_singleton_iff] at hy
        simpa [hy]

end Lax68Proofs
