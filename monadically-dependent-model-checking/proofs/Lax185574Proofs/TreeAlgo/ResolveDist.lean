import Lax185574.ConstructionSequences
import Lax185574.DistanceLogic
import Lax185574Proofs.WalkDistance

/-!
Distances after a resolve, following the proof of lem:resolve-lift. Both
resolves add the pairs `P^G Q^G` to the resolved pairs. A shortest walk in
the new Gaifman graph uses at most two of the new pairs: it runs in `G`
from `u` to `P^G` or `Q^G`, crosses to the other part, or returns to the
same part through the other one, and runs in `G` to `v`. The predicate
`Hop` describes the second kind of walk by distances to color classes in
`G`, which are unary distance atoms.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.ConstructionSequences
open Lax185574.DistanceLogic.DistFO
open Lax185574Proofs.WalkDistance

variable {V : Type*} (G : PartialGraph V) (P Q : ℕ)

theorem resolved_resolvePos : (resolvePos G P Q).resolved = G.resolved ⊔ between G P Q := by
  ext x y
  simp only [PartialGraph.resolved, resolvePos, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  tauto

theorem resolved_resolveNeg : (resolveNeg G P Q).resolved = G.resolved ⊔ between G P Q := by
  ext x y
  simp only [PartialGraph.resolved, resolveNeg, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  tauto

/-- Some vertex of color `X` is within distance `s` of `u` in `G`. -/
def NearC (u : V) (X s : ℕ) : Prop := ∃ x, G.color x = X ∧ WithinDist G.resolved s u x

/-- Some vertex has color `X`. -/
def Occurs (X : ℕ) : Prop := ∃ x : V, G.color x = X

/-- A walk through the new pairs: from `u` within `s₁` to one part, one
new pair to the other part or two new pairs back to the same part, and
within `s₂` to `v`. -/
def Hop (s : ℕ) (u v : V) : Prop :=
  ∃ s₁ s₂, (s₁ + 1 + s₂ ≤ s ∧
      ((NearC G u P s₁ ∧ NearC G v Q s₂) ∨ (NearC G u Q s₁ ∧ NearC G v P s₂))) ∨
    (s₁ + 2 + s₂ ≤ s ∧
      ((NearC G u P s₁ ∧ NearC G v P s₂ ∧ Occurs G Q) ∨
        (NearC G u Q s₁ ∧ NearC G v Q s₂ ∧ Occurs G P)))

variable {G P Q}

theorem withinDist_of_le {H H' : SimpleGraph V} (h : H ≤ H') {s : ℕ} {u v : V}
    (hd : WithinDist H s u v) : WithinDist H' s u v := by
  obtain ⟨p, hp⟩ := hd
  exact ⟨p.mapLe h, by simpa using hp⟩

theorem nearC_mono {u : V} {X s s' : ℕ} (h : s ≤ s') (hn : NearC G u X s) : NearC G u X s' := by
  obtain ⟨x, hx, hd⟩ := hn
  exact ⟨x, hx, withinDist_mono h hd⟩

theorem hop_mono {s s' : ℕ} {u v : V} (h : s ≤ s') (hh : Hop G P Q s u v) : Hop G P Q s' u v := by
  obtain ⟨s₁, s₂, h'⟩ := hh
  refine ⟨s₁, s₂, ?_⟩
  rcases h' with ⟨hs, h'⟩ | ⟨hs, h'⟩
  · exact Or.inl ⟨by omega, h'⟩
  · exact Or.inr ⟨by omega, h'⟩

theorem hop_symm {s : ℕ} {u v : V} (hh : Hop G P Q s u v) : Hop G P Q s v u := by
  obtain ⟨s₁, s₂, h⟩ := hh
  refine ⟨s₂, s₁, ?_⟩
  rcases h with ⟨hs, h⟩ | ⟨hs, h⟩
  · exact Or.inl ⟨by omega, by tauto⟩
  · exact Or.inr ⟨by omega, by tauto⟩

/-- Two vertices of colors `P` and `Q` are within distance `1` after the
resolve. -/
theorem withinDist_one_cross {x z : V} (hx : G.color x = P) (hz : G.color z = Q) :
    WithinDist (G.resolved ⊔ between G P Q) 1 x z := by
  by_cases hxz : x = z
  · subst hxz; exact withinDist_mono (Nat.zero_le _) (withinDist_refl _ _ _)
  · have : (between G P Q).Adj x z := by
      simp only [between, SimpleGraph.fromRel_adj]
      exact ⟨hxz, Or.inl ⟨hx, hz⟩⟩
    exact ⟨SimpleGraph.Walk.cons (Or.inr this) .nil, by simp⟩

/-- Two vertices of color `P` are within distance `2` after the resolve if
some vertex has color `Q`. -/
theorem withinDist_two_same {x z y : V} (hx : G.color x = P) (hz : G.color z = P)
    (hy : G.color y = Q) : WithinDist (G.resolved ⊔ between G P Q) 2 x z := by
  have h1 := withinDist_one_cross (G := G) hx hy
  have h2 : WithinDist (G.resolved ⊔ between G P Q) 1 y z := by
    by_cases hyz : y = z
    · subst hyz; exact withinDist_mono (Nat.zero_le _) (withinDist_refl _ _ _)
    · have : (between G P Q).Adj y z := by
        simp only [between, SimpleGraph.fromRel_adj]
        exact ⟨hyz, Or.inr ⟨hz, hy⟩⟩
      exact ⟨SimpleGraph.Walk.cons (Or.inr this) .nil, by simp⟩
  exact withinDist_trans h1 h2

theorem withinDist_two_same' {x z y : V} (hx : G.color x = Q) (hz : G.color z = Q)
    (hy : G.color y = P) : WithinDist (G.resolved ⊔ between G P Q) 2 x z := by
  have hb : between G P Q = between G Q P := by
    ext a b
    simp only [between, SimpleGraph.fromRel_adj]
    tauto
  rw [hb]
  exact withinDist_two_same (G := G) hx hz hy

/-- **Soundness of `Hop`.** -/
theorem withinDist_of_hop {s : ℕ} {u v : V} (hh : Hop G P Q s u v) :
    WithinDist (G.resolved ⊔ between G P Q) s u v := by
  have hle : G.resolved ≤ G.resolved ⊔ between G P Q := le_sup_left
  obtain ⟨s₁, s₂, h⟩ := hh
  rcases h with ⟨hs, h⟩ | ⟨hs, h⟩
  · refine withinDist_mono hs ?_
    rcases h with ⟨⟨x, hx, hux⟩, ⟨z, hz, hvz⟩⟩ | ⟨⟨x, hx, hux⟩, ⟨z, hz, hvz⟩⟩
    · exact withinDist_trans (withinDist_trans (withinDist_of_le hle hux)
        (withinDist_one_cross hx hz)) (withinDist_of_le hle (withinDist_symm hvz))
    · exact withinDist_trans (withinDist_trans (withinDist_of_le hle hux)
        (withinDist_symm (withinDist_one_cross hz hx))) (withinDist_of_le hle (withinDist_symm hvz))
  · refine withinDist_mono hs ?_
    rcases h with ⟨⟨x, hx, hux⟩, ⟨z, hz, hvz⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx, hux⟩, ⟨z, hz, hvz⟩, ⟨y, hy⟩⟩
    · exact withinDist_trans (withinDist_trans (withinDist_of_le hle hux)
        (withinDist_two_same hx hz hy)) (withinDist_of_le hle (withinDist_symm hvz))
    · exact withinDist_trans (withinDist_trans (withinDist_of_le hle hux)
        (withinDist_two_same' hx hz hy)) (withinDist_of_le hle (withinDist_symm hvz))

/-- Closure of the walks of `G` and `Hop` under adding a first step. -/
theorem reach_cons {s : ℕ} {u w v : V} (hadj : (G.resolved ⊔ between G P Q).Adj u w)
    (h : WithinDist G.resolved s w v ∨ Hop G P Q s w v) :
    WithinDist G.resolved (s + 1) u v ∨ Hop G P Q (s + 1) u v := by
  rcases hadj with hG | hB
  · have h1 : WithinDist G.resolved 1 u w := ⟨SimpleGraph.Walk.cons hG .nil, by simp⟩
    rcases h with h | ⟨s₁, s₂, h⟩
    · left; rw [add_comm]; exact withinDist_trans h1 h
    · right
      have hn : ∀ {X t}, NearC G w X t → NearC G u X (t + 1) := by
        rintro X t ⟨x, hx, hwx⟩
        exact ⟨x, hx, by rw [add_comm]; exact withinDist_trans h1 hwx⟩
      refine ⟨s₁ + 1, s₂, ?_⟩
      rcases h with ⟨hs, h⟩ | ⟨hs, h⟩
      · left; refine ⟨by omega, ?_⟩
        rcases h with ⟨a, b⟩ | ⟨a, b⟩
        · exact Or.inl ⟨hn a, b⟩
        · exact Or.inr ⟨hn a, b⟩
      · right; refine ⟨by omega, ?_⟩
        rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩
        · exact Or.inl ⟨hn a, b, c⟩
        · exact Or.inr ⟨hn a, b, c⟩
  · simp only [between, SimpleGraph.fromRel_adj] at hB
    obtain ⟨-, hc⟩ := hB
    have hn0 : ∀ {X}, G.color u = X → NearC G u X 0 := fun hX => ⟨u, hX, withinDist_refl _ _ _⟩
    right
    -- the cases of the colors of `u` and `w`
    have key : ∀ {A B : ℕ}, G.color u = A → G.color w = B →
        (∀ {t}, NearC G v B t → Hop G P Q (t + 1) u v) →
        (∀ {t}, NearC G v A t → Occurs G B → Hop G P Q (t + 2) u v) →
        (∀ {t}, NearC G v B t → Occurs G A → Hop G P Q (t + 2) u v) →
        ({A, B} : Set ℕ) = {P, Q} → Hop G P Q (s + 1) u v := by
      intro A B hu hw h1 h2 h3 hAB
      have hBocc : Occurs G B := ⟨w, hw⟩
      have hAocc : Occurs G A := ⟨u, hu⟩
      rcases h with h | ⟨s₁, s₂, h⟩
      · exact hop_mono (by omega) (h1 ⟨w, hw, withinDist_symm h⟩)
      · have hPQ : (A = P ∧ B = Q) ∨ (A = Q ∧ B = P) ∨ (A = P ∧ B = P ∧ P = Q) := by
          have h1' : A ∈ ({P, Q} : Set ℕ) := hAB ▸ Or.inl rfl
          have h2' : B ∈ ({P, Q} : Set ℕ) := hAB ▸ Or.inr rfl
          have h3' : P ∈ ({A, B} : Set ℕ) := hAB ▸ Or.inl rfl
          have h4' : Q ∈ ({A, B} : Set ℕ) := hAB ▸ Or.inr rfl
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1' h2' h3' h4'
          omega
        rcases h with ⟨hs, h⟩ | ⟨hs, h⟩
        · rcases h with ⟨_, b⟩ | ⟨_, b⟩
          · rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact hop_mono (by omega) (h1 b)
            · exact hop_mono (by omega) (h2 b hBocc)
            · exact hop_mono (by omega) (h1 b)
          · rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact hop_mono (by omega) (h2 b hBocc)
            · exact hop_mono (by omega) (h1 b)
            · exact hop_mono (by omega) (h1 b)
        · rcases h with ⟨_, b, _⟩ | ⟨_, b, _⟩
          · rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact hop_mono (by omega) (h2 b hBocc)
            · exact hop_mono (by omega) (h1 b)
            · exact hop_mono (by omega) (h1 b)
          · rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact hop_mono (by omega) (h1 b)
            · exact hop_mono (by omega) (h2 b hBocc)
            · exact hop_mono (by omega) (h1 b)
    rcases hc with ⟨hu, hw⟩ | ⟨hw, hu⟩
    · refine key hu hw (fun b => ⟨0, _, Or.inl ⟨by omega, Or.inl ⟨hn0 hu, b⟩⟩⟩)
        (fun b hB => ⟨0, _, Or.inr ⟨by omega, Or.inl ⟨hn0 hu, b, hB⟩⟩⟩)
        (fun b hA => ⟨0, _, Or.inl ⟨by omega, Or.inl ⟨hn0 hu, b⟩⟩⟩) rfl
    · refine key hu hw (fun b => ⟨0, _, Or.inl ⟨by omega, Or.inr ⟨hn0 hu, b⟩⟩⟩)
        (fun b hB => ⟨0, _, Or.inr ⟨by omega, Or.inr ⟨hn0 hu, b, hB⟩⟩⟩)
        (fun b hA => ⟨0, _, Or.inl ⟨by omega, Or.inr ⟨hn0 hu, b⟩⟩⟩) (Set.pair_comm _ _)

theorem reach_of_walk {u v : V} (p : (G.resolved ⊔ between G P Q).Walk u v) :
    WithinDist G.resolved p.length u v ∨ Hop G P Q p.length u v := by
  induction p with
  | nil => exact Or.inl (withinDist_refl _ _ _)
  | cons hadj p ih =>
    rw [SimpleGraph.Walk.length_cons]
    exact reach_cons hadj ih

/-- **Distances after a resolve.** -/
theorem withinDist_resolve_iff {s : ℕ} {u v : V} :
    WithinDist (G.resolved ⊔ between G P Q) s u v ↔
      WithinDist G.resolved s u v ∨ Hop G P Q s u v := by
  constructor
  · rintro ⟨p, hp⟩
    rcases reach_of_walk p with h | h
    · exact Or.inl (withinDist_mono hp h)
    · exact Or.inr (hop_mono hp h)
  · rintro (h | h)
    · exact withinDist_of_le le_sup_left h
    · exact withinDist_of_hop h

end Lax185574Proofs.TreeAlgo
