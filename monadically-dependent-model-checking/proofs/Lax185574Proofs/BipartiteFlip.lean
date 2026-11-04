import Lax185574.BipartiteFlip
import Lax185574Proofs.BipartiteWalks

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/

namespace Lax185574Proofs.BipartiteFlip

open Lax185574.BipartiteGraphs Lax185574.GaifmanGraph
open Lax185574Proofs.WithinDistBasics Lax185574Proofs.BipartiteWalks

universe u w

theorem within_mono {W : Type*} {G : SimpleGraph W} {d e : ℕ} {a b : W}
    (h : WithinDist G d a b) (hde : d ≤ e) : WithinDist G e a b :=
  withinDist_mono hde h

theorem cross_edge {U : Type u} {V : Type w} {R : U → V → Prop} {x : U} {y : V} (h : R x y) :
    WithinDist (bipartiteGraph R) 1 (.inl x) (.inr y) :=
  withinDist_adj ((adj_inl_inr R x y).mpr h)

theorem cross_three {U : Type u} {V : Type w} {R : U → V → Prop} {x z : U} {y w : V}
    (hxy : R x y) (hzy : R z y) (hzw : R z w) :
    WithinDist (bipartiteGraph R) 3 (.inl x) (.inr w) :=
  withinDist_trans (withinDist_trans (cross_edge hxy) (withinDist_symm' (cross_edge hzy)))
    (cross_edge hzw)

theorem cross_five {U : Type u} {V : Type w} {R : U → V → Prop}
    {a b c : U} {x y z : V}
    (hax : R a x) (hbx : R b x) (hby : R b y) (hcy : R c y) (hcz : R c z) :
    WithinDist (bipartiteGraph R) 5 (.inl a) (.inr z) :=
  withinDist_trans (cross_three hax hbx hby)
    (withinDist_trans (withinDist_symm' (cross_edge hcy)) (cross_edge hcz))

/-- Two conflicting pairs with the same adjacency to the representatives
give a short walk in one of the two polarities: an edge `x₁y₁` and a
non-edge `x₂y₂`, where `x₁, x₂` agree on `y₀` and `y₁, y₂` agree on
`x₀`. -/
theorem conflicting_pairs_short {U : Type u} {V : Type w} (R : U → V → Prop)
    (x₀ x₁ x₂ : U) (y₀ y₁ y₂ : V)
    (_hpos : R x₁ y₁) (hneg : ¬R x₂ y₂)
    (hleft : R x₁ y₀ ↔ R x₂ y₀) (hright : R x₀ y₁ ↔ R x₀ y₂) :
    WithinDist (bipartiteGraph (fun x y => ¬R x y)) 6 (.inl x₁) (.inr y₁) ∨
      WithinDist (bipartiteGraph R) 6 (.inl x₂) (.inr y₂) := by
  classical
  by_cases ha : R x₁ y₀
  · by_cases hb : R x₀ y₁
    · by_cases hc : R x₀ y₀
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three h20 hc h02) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three h20 hc h02) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three h20 hc h02) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inl (within_mono (cross_three hd hneg he) (by omega))
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three h20 ha hd) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three h20 ha hd) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three he hb h02) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inl (within_mono (cross_three hd hneg he) (by omega))
    · by_cases hc : R x₀ y₀
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inr (within_mono (cross_three h20 ha hd) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inr (within_mono (cross_three h20 ha hd) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three hd h02 hb) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three hd h02 hb) (by omega))
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inr (within_mono (cross_three h20 ha hd) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inr (within_mono (cross_three h20 ha hd) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three hd h02 hb) (by omega))
          · have h20 : R x₂ y₀ := hleft.mp ha
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three hd h02 hb) (by omega))
  · by_cases hb : R x₀ y₁
    · by_cases hc : R x₀ y₀
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three he hb h02) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inl (within_mono (cross_three ha h20 he) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three he hb h02) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inl (within_mono (cross_three ha h20 he) (by omega))
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three he hb h02) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inl (within_mono (cross_three ha h20 he) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inr (within_mono (cross_three he hb h02) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : R x₀ y₂ := hright.mp hb
            exact Or.inl (within_mono (cross_three ha h20 he) (by omega))
    · by_cases hc : R x₀ y₀
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_five ha h20 hneg h02 hb) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three ha h20 he) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three hd h02 hb) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three ha h20 he) (by omega))
      · by_cases hd : R x₁ y₂
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three ha hc hb) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three ha hc hb) (by omega))
        · by_cases he : R x₂ y₁
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three ha hc hb) (by omega))
          · have h20 : ¬R x₂ y₀ := fun h => ha (hleft.mpr h)
            have h02 : ¬R x₀ y₂ := fun h => hb (hright.mpr h)
            exact Or.inl (within_mono (cross_three ha hc hb) (by omega))

/--
---
conclusion: Lax185574.BipartiteFlip.exists_flip_close
---
Flip a cell of the four-part partition exactly when it contains an
edge `uv` of `B` with no walk of length at most `6` in `B̄`. Then every
edge of `B'` that is an edge of `B` has a short walk in `B̄`, by the
choice of the flipped cells. Every edge of `B'` that is a non-edge of
`B` lies in a flipped cell, and comparing it with the edge that caused
the flip gives a walk of length at most `6` in `B` between its ends, by
a case analysis over the adjacencies to the representatives. Walks
between the two sides of a bipartite graph have odd length, so the
bound `6` improves to `5`.

The construction is adapted from an earlier formalization that proves
the statement with bound `6` for flips given by Boolean toggles, see
PROVENANCE.md.
-/
theorem exists_flip_close {X : Type u} {Y : Type w} (E : X → Y → Prop) (x : X) (y : Y) :
    ∃ E' : X → Y → Prop,
      (∀ (u u' : X) (v v' : Y), (E u y ↔ E u' y) → (E x v ↔ E x v') →
        ((E' u v ↔ E u v) ↔ (E' u' v' ↔ E u' v'))) ∧
      ∀ (u : X) (v : Y), E' u v →
        WithinDist (bipartiteGraph E) 5 (.inl u) (.inr v) ∧
          WithinDist (bipartiteGraph fun a b => ¬ E a b) 5 (.inl u) (.inr v) := by
  classical
  -- a cell is flipped if it contains an edge that is far in the complement
  let bad : X → Y → Prop := fun u v => ∃ u' v', (E u' y ↔ E u y) ∧ (E x v' ↔ E x v) ∧
    E u' v' ∧ ¬ WithinDist (bipartiteGraph fun a b => ¬ E a b) 6 (.inl u') (.inr v')
  have bad_congr : ∀ u u' v v', (E u y ↔ E u' y) → (E x v ↔ E x v') → (bad u v ↔ bad u' v') := by
    intro u u' v v' hu hv
    constructor
    · rintro ⟨a, b, ha, hb, h⟩; exact ⟨a, b, ha.trans hu, hb.trans hv, h⟩
    · rintro ⟨a, b, ha, hb, h⟩; exact ⟨a, b, ha.trans hu.symm, hb.trans hv.symm, h⟩
  refine ⟨fun u v => (E u v ∧ ¬ bad u v) ∨ (¬ E u v ∧ bad u v), ?_, ?_⟩
  · intro u u' v v' hu hv
    have := bad_congr u u' v v' hu hv
    by_cases h1 : E u v <;> by_cases h2 : E u' v' <;> by_cases h3 : bad u v <;> simp_all
  · intro u v huv
    rcases huv with ⟨he, hnb⟩ | ⟨hne, hb⟩
    · refine ⟨within_mono (cross_edge he) (by omega), ?_⟩
      refine withinDist_odd (d := 2) ?_
      by_contra hfar
      exact hnb ⟨u, v, Iff.rfl, Iff.rfl, he, hfar⟩
    · refine ⟨withinDist_odd (d := 2) ?_, within_mono (cross_edge (R := fun a b => ¬ E a b) hne)
        (by omega)⟩
      obtain ⟨u', v', hu, hv, he', hfar⟩ := hb
      exact (conflicting_pairs_short E x u' u y v' v he' hne hu hv).resolve_left hfar

end Lax185574Proofs.BipartiteFlip
