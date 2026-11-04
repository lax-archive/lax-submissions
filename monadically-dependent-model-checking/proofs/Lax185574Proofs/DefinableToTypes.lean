import Lax185574.DefinableToTypes
import Lax185574.LocalToGlobal
import Lax185574.TypeBound
import Lax185574Proofs.Lib.InterpretationTypeBound
import Lax185574Proofs.DistanceFormulaRank
import Lax185574Proofs.WithinDistBasics
import Lax185574Proofs.FormulaRank
import Lax185574Proofs.Interface.Shim.TypeBound

/-!
Proof that local definability bounds the width, following the proof of
lem:skel-def-to-types. A type of a tuple from a ball is determined, by
`LocalToGlobal`, by its type in the induced partial graph on the larger
ball. That partial graph is definable in an expansion of the graph, so a
type over the parameters there determines it. `TypeBound` counts the
latter.
-/

namespace Lax185574Proofs.DefinableToTypes

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence Lax710763.Transductions
open Lax185574.FirstOrderTypes Lax185574.GaifmanGraph Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.LocalDefinability Lax185574.Width
open Lax185574.Colorings
open Lax185574Proofs.Lib.InterpretationTypeBound Lax185574Proofs.FormulaRank
open Lax185574Proofs.DistanceFormulaRank Lax185574Proofs.WithinDistBasics

universe z

variable {V : Type z}

/-- The Gaifman graph of a partial graph is contained in its graph of
resolved pairs. -/
theorem gaifman_le_resolved (H : PartialGraph V) :
    @gaifmanGraph language V H.structure ≤ H.resolved := by
  intro a b h
  unfold gaifmanGraph at h
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨hab, h⟩ := h
  have key : ∀ a b : V, a ≠ b → (∃ (l : ℕ) (R : language.Relations l) (x : Fin l → V),
      @Structure.RelMap _ V H.structure l R x ∧ a ∈ Set.range x ∧ b ∈ Set.range x) →
      H.resolved.Adj a b := by
    rintro a b hab ⟨l, R, x, hx, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
    cases R with
    | edge =>
      change H.edge.Adj (x 0) (x 1) at hx
      have hx' : H.resolved.Adj (x 0) (x 1) := (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hx)
      fin_cases i <;> fin_cases j
      · exact absurd rfl hab
      · exact hx'
      · exact hx'.symm
      · exact absurd rfl hab
    | nonEdge =>
      change H.nonEdge.Adj (x 0) (x 1) at hx
      have hx' : H.resolved.Adj (x 0) (x 1) := (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr hx)
      fin_cases i <;> fin_cases j
      · exact absurd rfl hab
      · exact hx'
      · exact hx'.symm
      · exact absurd rfl hab
    | color Y =>
      exact absurd (congrArg x (Subsingleton.elim i j)) hab
  rcases h with h | h
  · exact key a b hab h
  · exact (key b a (Ne.symm hab) h).symm

/-- A step keeps every resolved pair resolved. -/
theorem resolved_le_of_isStep {G H : PartialGraph V} (h : IsStep G H) :
    G.resolved ≤ H.resolved := by
  obtain ⟨P, Q, ⟨-, rfl⟩ | rfl | rfl⟩ := h
  · exact le_rfl
  · exact sup_le_sup le_sup_left le_rfl
  · exact sup_le_sup le_rfl le_sup_left

/-- The partial graphs have relations of arity at most 2. -/
theorem language_arity : ∀ l, 2 < l → IsEmpty (language.Relations l) := by
  intro l hl
  refine ⟨fun R => ?_⟩
  cases R <;> omega

/-- The core counting step: if the induced partial graph `H[W]` is
definable in a structure on `V` with parameters `S` by formulas of rank
at most `q₀`, and `W` contains the radius-`7^q` balls in `H` of all
tuples from `B`, then the rank-`q` types in `H` of `q`-tuples from `B`
are at most as many as the rank-`(q' + q₀)` types over `S`. -/
theorem partialTypeCount_le {L : Language.{0, 0}} {n : ℕ} [L.Structure (Fin n)]
    (q q' q₀ : ℕ) (H : PartialGraph (Fin n))
    (hq' : ∀ (B B' : Set (Fin n)) (a : Fin q → B) (b : Fin q → B'),
      @ball language (Fin n) H.structure (7 ^ q) q (Subtype.val ∘ a) ⊆ B →
      @ball language (Fin n) H.structure (7 ^ q) q (Subtype.val ∘ b) ⊆ B' →
      @rankType language B (@induced language (Fin n) H.structure _ B) q' q a =
        @rankType language B' (@induced language (Fin n) H.structure _ B') q' q b →
      @rankType language (Fin n) H.structure q q (Subtype.val ∘ a) =
        @rankType language (Fin n) H.structure q q (Subtype.val ∘ b))
    (B W : Set (Fin n)) (S : Set (Fin n)) (hD : @DefinableIn (Fin n) L _ q₀ S H W)
    (hBW : ∀ u : Fin q → Fin n, (∀ i, u i ∈ B) →
      @ball language (Fin n) H.structure (7 ^ q) q u ⊆ W) :
    partialTypeCount H q q B ≤ typeCountOver ‹L.Structure (Fin n)› q (q' + q₀) Set.univ S := by
  classical
  choose ρ hρq hρ using fun {l : ℕ} (R : language.Relations l) => hD R
  let δ : L.Formula (Fin 1 ⊕ S) :=
    BoundedFormula.iSup fun u : Fin n => ρ (Rel.color (H.color u))
  have hδq : quantifierRank δ ≤ q₀ := qr_iSup_le _ _ fun u => hρq _
  have hδ : ∀ v : Fin n, δ.Realize (Sum.elim (fun _ => v) Subtype.val) ↔ v ∈ W := by
    intro v
    simp only [δ, Formula.Realize, BoundedFormula.realize_iSup]
    constructor
    · rintro ⟨u, hu⟩
      exact ((hρ _ _).1 hu).1 0
    · intro hv
      refine ⟨v, (hρ _ _).2 ⟨fun _ => hv, rfl⟩⟩
  have hρ' : ∀ {l : ℕ} (R : language.Relations l) (x : Fin l → W),
      (ρ R).Realize (Sum.elim (fun i => (x i : Fin n)) Subtype.val) ↔
        @Structure.RelMap language W (@induced language (Fin n) H.structure _ W) l R x := by
    intro l R x
    rw [hρ R]
    exact and_iff_right fun i => (x i).2
  unfold partialTypeCount typeCount typeCountOver types typesOver
  refine (ncard_image_le_of_factor (X := {u : Fin q → Fin n | ∀ i, u i ∈ B})
    (@rankType language (Fin n) H.structure q q)
    (fun u => rankTypeOver (L := L) (q' + q₀) S u) ?_ ((Set.toFinite _).image _)).trans ?_
  · intro u hu u' hu' huu
    have hW : ∀ i, u i ∈ W := fun i => hBW u hu ⟨i, withinDist_refl _ _⟩
    have hW' : ∀ i, u' i ∈ W := fun i => hBW u' hu' ⟨i, withinDist_refl _ _⟩
    let a : Fin q → W := fun i => ⟨u i, hW i⟩
    let a' : Fin q → W := fun i => ⟨u' i, hW' i⟩
    have key : ∀ (z : Fin q → W) (ψ : language.Formula (Fin q)), quantifierRank ψ ≤ q' →
        (@Formula.Realize language W (@induced language (Fin n) H.structure _ W) _ ψ z ↔
          tr δ (fun R => ρ R) ψ ∈ rankTypeOver (L := L) (q' + q₀) S (Subtype.val ∘ z)) := by
      intro z ψ hψ
      have hr : quantifierRank (tr δ (fun R => ρ R) ψ) ≤ q' + q₀ :=
        (quantifierRank_tr δ (fun R => ρ R) hδq (fun R => hρq R) ψ).trans (by omega)
      simp only [rankTypeOver, Set.mem_ofPred_eq, hr, true_and]
      unfold Formula.Realize
      rw [← realize_tr δ (fun R => ρ R) (@induced language (Fin n) H.structure _ W) hδ
        (fun R => hρ' R) ψ z default]
      exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))
    have hind : @rankType language W (@induced language (Fin n) H.structure _ W) q' q a =
        @rankType language W (@induced language (Fin n) H.structure _ W) q' q a' := by
      ext ψ
      simp only [rankType, Set.mem_ofPred_eq]
      refine and_congr_right fun hψ => ?_
      rw [key a ψ hψ, key a' ψ hψ]
      change _ ∈ rankTypeOver (L := L) (q' + q₀) S u ↔ _ ∈ rankTypeOver (L := L) (q' + q₀) S u'
      rw [show rankTypeOver (L := L) (q' + q₀) S u = rankTypeOver (L := L) (q' + q₀) S u'
        from huu]
    exact hq' W W a a' (hBW u hu) (hBW u' hu') hind
  · refine Set.ncard_le_ncard ?_ ((Set.toFinite _).image _)
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, fun _ => Set.mem_univ _, rfl⟩

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem width_le_of_isRadiusDefinable_old (q : ℕ) :
    ∀ (C : GraphClass), MonadicallyDependent C →
      ∀ q₀ : ℕ, ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ,
        ∀ (r s : ℕ) (n : ℕ) (G : SimpleGraph (Fin n))
          (seq : List (PartialGraph (Fin n))),
          C n G → IsConstructionSequence G seq →
          IsRadiusDefinable G seq (r + 7 ^ q) c s q₀ →
          width r q seq ≤ F * (s + 1) ^ a := by
  intro C hC q₀
  obtain ⟨q', hq'⟩ := Lax185574.LocalToGlobal.rankType_eq_of_rankType_induced_eq.{0, 0, 0} q q 2
  obtain ⟨a, ha⟩ := Lax185574Proofs.Shim.TypeBound.typeCountOver_le C hC q (q' + q₀)
  refine ⟨a, fun c => ?_⟩
  obtain ⟨F, hF⟩ := ha c
  refine ⟨F, fun r s n G seq hG hseq hdef => ?_⟩
  obtain ⟨-, -, hstep, -⟩ := hseq
  apply csSup_le'
  rintro K ⟨t, ht, v, rfl⟩
  obtain ⟨colors, S, hS, hD⟩ := hdef t ht v
  have hle : seq[t].resolved ≤ seq[t + 1].resolved := resolved_le_of_isStep (hstep t ht)
  let _ := expansion G colors
  refine (partialTypeCount_le (L := withColors Language.graph c) q q' q₀ seq[t]
    (fun B B' a b ha hb hab =>
      @hq' language _ language_arity (Fin n) _ seq[t].structure B B' a b ha hb hab)
    (seq[t + 1].ball r v) (seq[t + 1].ball (r + 7 ^ q) v) (S : Set (Fin n)) hD ?_).trans ?_
  · rintro u hu x ⟨i, hx⟩
    have h1 : WithinDist seq[t + 1].resolved (7 ^ q) (u i) x :=
      withinDist_le_graph ((gaifman_le_resolved seq[t]).trans hle) hx
    exact withinDist_trans (hu i) h1
  · refine (hF n G hG colors S).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

end Lax185574Proofs.DefinableToTypes

namespace Lax185574Proofs.DefinableToTypes

open Lax185574.Graphs Lax185574.MonadicDependence
open Lax185574.ConstructionSequences Lax185574.LocalDefinability Lax185574.PartialGraphs
open Lax185574.Width Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.DefinableToTypes.width_le_of_isRadiusDefinable
---
Let `q'` be the rank of `LocalToGlobal` for `q`-tuples, rank `q` and arity
2, and let `a` and `F` be the exponent and factor of `TypeBound` for
`q`-tuples and rank `q' + q₀`. Fix a step `t` and a vertex `v`, and let
`B` and `W` be the balls of radius `r` and `r + 7^q` around `v` in the
next partial graph. A step keeps resolved pairs, so the radius-`7^q` ball
in the current partial graph of a tuple from `B` lies in `W`. By
`LocalToGlobal`, the type of such a tuple is determined by its type of
rank `q'` in the induced partial graph on `W`. This partial graph is
definable in an expansion of the graph by `c` predicates with at most `s`
parameters, so the type over the parameters of rank `q' + q₀` determines
the latter. `TypeBound` bounds the number of these types by
`F · (s + 1)^a`.

The argument is carried out for the graph classes of the archive and
their monadic dependence, and transferred to the graph classes used
here.
-/
theorem width_le_of_isRadiusDefinable (q : ℕ) (C : GraphClass) (hC : MonadicallyDependent C)
    (q₀ : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ, ∀ r s : ℕ, ∀ G ∈ C,
      ∀ seq : List (PartialGraph (Fin G.n)), IsConstructionSequence G.toSimpleGraph seq →
        IsRadiusDefinable G.toSimpleGraph seq (r + 7 ^ q) c s q₀ →
          width r q seq ≤ F * (s + 1) ^ a := by
  obtain ⟨a, h⟩ := width_le_of_isRadiusDefinable_old q (toOld C) (monadicallyDependent_toOld hC) q₀
  refine ⟨a, fun c => ?_⟩
  obtain ⟨F, hF⟩ := h c
  exact ⟨F, fun r s G hG seq => hF r s G.n G.toSimpleGraph seq hG⟩

end Lax185574Proofs.DefinableToTypes
