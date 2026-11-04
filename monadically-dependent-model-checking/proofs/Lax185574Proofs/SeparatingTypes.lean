import Lax185574.LocalToGlobal
import Lax185574.SeparatingTypes
import Lax185574Proofs.TypeCodes
import Lax185574Proofs.ParameterExpansion
import Mathlib.Tactic.FinCases

/-!
Proof that the tuples far from a parameter set realize few types over it,
following the proof of lem:sep-types: name the parameters by relations, so
that types over `U` become types without parameters, and apply
`LocalToGlobal` to the expanded structure, whose relations involving
parameters vanish near tuples far from `U`.
-/

namespace Lax185574Proofs.SeparatingTypes

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.FirstOrderTypes Lax185574.GaifmanGraph Lax185574.GraphBalls
open Lax185574.Colorings Lax185574Proofs.TypeCodes Lax185574Proofs.ParameterExpansion

universe z

instance colorLanguage_finite (c : ℕ) : Finite (Σ l, (withColors Language.graph c).Relations l) := by
  let f : (Σ l, (withColors Language.graph c).Relations l) → Option (Fin c) := fun R =>
    match R with
    | ⟨_, Sum.inl _⟩ => none
    | ⟨_, Sum.inr (ColorRel.color i)⟩ => some i
  refine Finite.of_injective f ?_
  rintro ⟨l₁, R₁ | R₁⟩ ⟨l₂, R₂ | R₂⟩ h
  · cases R₁; cases R₂; rfl
  · cases R₂; simp [f] at h
  · cases R₁; simp [f] at h
  · cases R₁; cases R₂
    simp only [f, Option.some.injEq] at h
    subst h
    rfl

theorem colorLanguage_arity (c : ℕ) :
    ∀ l, 2 < l → IsEmpty ((withColors Language.graph c).Relations l) := by
  intro l hl
  refine ⟨fun R => ?_⟩
  rcases R with R | R
  · cases R; omega
  · cases R; omega

theorem gaifman_expansion_le {V : Type z} (G : SimpleGraph V) {c : ℕ} (colors : Fin c → Set V) :
    @gaifmanGraph (withColors Language.graph c) V (expansion G colors) ≤ G := by
  intro a b h
  unfold gaifmanGraph at h
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨hab, h⟩ := h
  have key : ∀ a b : V, a ≠ b → (∃ (l : ℕ) (R : (withColors Language.graph c).Relations l)
      (x : Fin l → V), @Structure.RelMap _ V (expansion G colors) l R x ∧ a ∈ Set.range x ∧
        b ∈ Set.range x) → G.Adj a b := by
    rintro a b hab ⟨l, R | R, x, hx, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
    · cases R
      change G.Adj (x 0) (x 1) at hx
      fin_cases i <;> fin_cases j
      · exact absurd rfl hab
      · exact hx
      · exact hx.symm
      · exact absurd rfl hab
    · cases R
      exact absurd (congrArg x (Subsingleton.elim i j)) hab
  rcases h with h | h
  · exact key a b hab h
  · exact (key b a (Ne.symm hab) h).symm

theorem withinDist_mono_graph {W : Type*} {G H : SimpleGraph W} (hGH : G ≤ H) {d : ℕ}
    {a b : W} (h : WithinDist G d a b) : WithinDist H d a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.mapLe hGH, by rw [SimpleGraph.Walk.length_mapLe]; exact hp⟩

theorem withinDist_symm {W : Type*} {G : SimpleGraph W} {d : ℕ} {a b : W}
    (h : WithinDist G d a b) : WithinDist G d b a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by rw [SimpleGraph.Walk.length_reverse]; exact hp⟩

/--
---
conclusion: Lax185574.SeparatingTypes.typeCountOver_far_le
---
Let `h = 7^q` and `r = h + 1`. Expand the colored graph by a relation for
every relation symbol with some positions filled by parameters from `U`,
and by a unary relation `P_u` for every `u ∈ U`. Formulas with parameters
become formulas of the expansion without parameters and with the same
quantifier rank. For a tuple far from `U`, the ball `B` of radius `h` around
it in the expansion avoids `U` and its neighbors, so the new relations are
trivial on `B`, and the type of rank `q'` of the tuple in the expansion of
`B` is determined by its type in the colored graph induced on `B`. By
`LocalToGlobal`, that type determines the type of rank `q` in the expansion,
hence the type over `U` in the colored graph. The types of rank `q'` of
`k`-tuples in colored graphs are bounded by the number of their finite
codes, which depends on `q`, `k` and `c` only.
-/
theorem typeCountOver_far_le (q : ℕ) :
    ∃ r : ℕ, ∀ k c : ℕ, ∃ T : ℕ,
      ∀ (V : Type z) [Finite V] (G : SimpleGraph V) (colors : Fin c → Set V)
        (U : Set V),
        @typeCountOver (withColors Language.graph c) V (expansion G colors) k q
            (graphBall G r U)ᶜ U ≤ T := by
  refine ⟨7 ^ q + 1, fun k c => ?_⟩
  obtain ⟨q', hq'⟩ := Lax185574.LocalToGlobal.rankType_eq_of_rankType_induced_eq.{0, z, z} k q 2
  refine ⟨Nat.card (Code (withColors Language.graph c) q' k), fun V _ G colors U => ?_⟩
  let Lc := withColors Language.graph c
  let _ : Lc.Structure V := expansion G colors
  let e : U → V := Subtype.val
  have he : Function.Injective e := Subtype.val_injective
  let Lp := plusLang Lc U
  let Mp : Lp.Structure V := plusStructure e
  -- the ball of radius `7^q` in the expansion, and the tuple inside it
  let Bl : (Fin k → V) → Set V := fun a => ball Lp (7 ^ q) a
  let inB : ∀ a : Fin k → V, Fin k → Bl a := fun a i => ⟨a i, ⟨i, SimpleGraph.Walk.nil, by simp⟩⟩
  let τ : (Fin k → V) → Code Lc q' k := fun a => @code Lc (Bl a) (induced (Bl a)) q' k (inB a)
  let F := {a : Fin k → V | ∀ i, a i ∈ (graphBall G (7 ^ q + 1) U)ᶜ}
  -- the balls around far tuples avoid `U` and its neighbors
  have hfar : ∀ a ∈ F, ∀ w ∈ Bl a, ∀ u : U,
      w ≠ e u ∧ ¬ (gaifmanGraph Lc (V := V)).Adj w (e u) := by
    intro a ha w hw u
    obtain ⟨i, hi⟩ := hw
    have hiG : WithinDist G (7 ^ q) (a i) w :=
      withinDist_mono_graph (gaifman_expansion_le G colors) (withinDist_of_plus e hi)
    obtain ⟨p, hp⟩ := hiG
    refine ⟨fun hwu => ha i ⟨u.1, u.2, withinDist_symm ⟨p.copy rfl hwu, ?_⟩⟩, fun hadj => ?_⟩
    · rw [SimpleGraph.Walk.length_copy]; omega
    · have hG : G.Adj w u.1 := gaifman_expansion_le G colors hadj
      exact ha i ⟨u.1, u.2, withinDist_symm ⟨p.concat hG, by
        rw [SimpleGraph.Walk.length_concat]; omega⟩⟩
  -- types in the expansion of the ball are determined by types in the colored graph
  have hplus : ∀ a ∈ F, ∀ (φ : Lp.Formula (Fin k)),
      φ ∈ @rankType Lp (Bl a) (@induced Lp V Mp _ (Bl a)) q' k (inB a) ↔
        fromPlus e φ ∈ @rankType Lc (Bl a) (induced (Bl a)) q' k (inB a) := by
    intro a ha φ
    simp only [rankType, Set.mem_ofPred_eq, quantifierRank_fromPlus]
    refine and_congr_right fun _ => ?_
    unfold Formula.Realize
    exact (realize_fromPlus e (Bl a) (hfar a ha) φ (inB a) default).symm
  have hover : ∀ (a : Fin k → V) (φ : Lc.Formula (Fin k ⊕ U)),
      φ ∈ rankTypeOver (L := Lc) q U a ↔ toPlus φ ∈ rankType (L := Lp) q a := by
    intro a φ
    simp only [rankTypeOver, Set.mem_ofPred_eq]
    change _ ↔ quantifierRank (toPlus φ) ≤ q ∧ @Formula.Realize Lp V Mp _ (toPlus φ) a
    rw [quantifierRank_toPlus]
    refine and_congr_right fun _ => ?_
    unfold Formula.Realize
    exact (realize_toPlus e he φ a default).symm
  have hfactor : ∀ a ∈ F, ∀ b ∈ F, τ a = τ b →
      rankTypeOver (L := Lc) q U a = rankTypeOver (L := Lc) q U b := by
    intro a ha b hb hab
    have h1 := @rankType_eq_of_code_eq Lc (Bl a) (induced (Bl a)) (Bl b) (induced (Bl b)) _
      k q' (inB a) (inB b) hab
    have h2 : @rankType Lp (Bl a) (@induced Lp V Mp _ (Bl a)) q' k (inB a) =
        @rankType Lp (Bl b) (@induced Lp V Mp _ (Bl b)) q' k (inB b) := by
      ext φ
      rw [hplus a ha, hplus b hb, h1]
    have h3 := hq' Lp (plusLang_arity 2 (colorLanguage_arity c) (by omega)) V (Bl a) (Bl b)
      (inB a) (inB b) (subset_refl _) (subset_refl _) h2
    ext φ
    rw [hover, hover]
    exact Set.ext_iff.mp h3 (toPlus φ)
  unfold typeCountOver typesOver
  calc (rankTypeOver (L := Lc) q U '' {v | ∀ i, v i ∈ (graphBall G (7 ^ q + 1) U)ᶜ}).ncard
      ≤ (τ '' F).ncard := ncard_image_le_of_factor (Set.toFinite _) _ τ hfactor
    _ ≤ Nat.card (Code Lc q' k) := Set.ncard_le_card _

end Lax185574Proofs.SeparatingTypes
