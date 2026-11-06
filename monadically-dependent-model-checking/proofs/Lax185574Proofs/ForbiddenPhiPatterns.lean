import Lax185574.ForbiddenPhiPatterns
import Lax185574.ForbiddenPhiPsiPatterns
import Lax185574Proofs.Interface.Shim.ForbiddenPhiPsiPatterns

namespace Lax185574Proofs.ForbiddenPhiPatterns

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax185574.PhiPatterns Lax185574.PhiPsiPatterns

universe u

/-- A pattern contains patterns of every smaller order: keep the first
rows and columns. -/
theorem hasPattern_mono {V : Type u} {G : SimpleGraph V} {p p' : ℕ}
    {φ : Language.graph.Formula (Fin p ⊕ Fin 1)} {ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)}
    {s t s' t' : ℕ} (hs : s' ≤ s) (ht : t' ≤ t) (h : HasPattern G φ ψ s t) :
    HasPattern G φ ψ s' t' := by
  obtain ⟨a, b, c, hp⟩ := h
  refine ⟨fun i => a (Fin.castLE hs i), fun j => b (Fin.castLE ht j),
    fun i j => c (Fin.castLE hs i) (Fin.castLE ht j), fun i j => ?_⟩
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp (Fin.castLE hs i) (Fin.castLE ht j)
  exact ⟨⟨h1, fun i' hi' => h2 _ (hi')⟩,
    ⟨h3, fun j' hj' => h4 _ (hj')⟩⟩

/-- Forbidden `(φ, E)`- and `(φ, ¬E)`-patterns on a class forbid
`φ`-patterns on it. -/
theorem forbidden_phi_patterns_of_phiPsi (C : GraphClass) {p : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (hE : ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ¬ HasPattern G φ edgeFormula t t)
    (hN : ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ¬ HasPattern G φ edgeFormula.not t t) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ¬ HasPhiPattern G φ t t := by
  obtain ⟨t₁, h₁⟩ := hE
  obtain ⟨t₂, h₂⟩ := hN
  refine ⟨max t₁ t₂, fun n G hG h => ?_⟩
  rcases h with h | h
  · exact h₁ n G hG (hasPattern_mono (le_max_left _ _) (le_max_left _ _) h)
  · exact h₂ n G hG (hasPattern_mono (le_max_right _ _) (le_max_right _ _) h)

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem forbidden_phi_patterns_old (C : GraphClass) (hC : MonadicallyDependent C)
    {p : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ¬ HasPhiPattern G φ t t :=
  forbidden_phi_patterns_of_phiPsi C φ
    (Lax185574Proofs.Shim.ForbiddenPhiPsiPatterns.forbidden_phiPsi_patterns C hC φ edgeFormula)
    (Lax185574Proofs.Shim.ForbiddenPhiPsiPatterns.forbidden_phiPsi_patterns C hC φ
      edgeFormula.not)

end Lax185574Proofs.ForbiddenPhiPatterns

namespace Lax185574Proofs.ForbiddenPhiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.PhiPatterns
open Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.ForbiddenPhiPatterns.forbidden_phi_patterns
---
A `φ`-pattern is a `(φ, E)`-pattern or a `(φ, ¬E)`-pattern. Take the
larger of the two bounds of the lemma on `(φ, ψ)`-patterns, and use that
a pattern contains patterns of all smaller orders.

The argument is carried out for the graph classes of the archive and
their monadic dependence, and transferred to the graph classes used
here.
-/
theorem forbidden_phi_patterns (C : GraphClass) (hC : MonadicallyDependent C)
    {p : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasPhiPattern G.toSimpleGraph φ t t := by
  obtain ⟨t, ht⟩ := forbidden_phi_patterns_old (toOld C) (monadicallyDependent_toOld hC) φ
  exact ⟨t, fun G hG => ht G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.ForbiddenPhiPatterns
