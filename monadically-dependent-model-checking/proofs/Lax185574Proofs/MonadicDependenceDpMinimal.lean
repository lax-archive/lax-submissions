import Lax185574.MonadicDependenceDpMinimal
import Lax185574Proofs.Interface.Shim.IndependenceProperty
import Lax185574Proofs.PatternFormula

namespace Lax185574Proofs.MonadicDependenceDpMinimal

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence Lax710763.Transductions
open Lax185574.PhiPsiPatterns Lax185574.DpMinimality Lax185574Proofs.Interface.Old
open Lax185574Proofs.PatternFormula

/-- The bound on clean patterns for the graph classes of the archive and
their monadic dependence. -/
theorem exists_not_hasCleanPattern_old (C : GraphClass) (hC : MonadicallyDependent C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ¬ HasCleanPattern G φ ψ t t := by
  classical
  have hIP :=
    Lax185574Proofs.Shim.IndependenceProperty.not_hasIP_of_monadicallyDependent C hC
      (gamma φ ψ)
  unfold HasIP at hIP
  push Not at hIP
  obtain ⟨k, hk⟩ := hIP
  refine ⟨2 ^ k, fun n G hG ⟨a, b, c, hpat⟩ => ?_⟩
  let ι : Fin k → Fin (2 ^ k) := Fin.castLE (Nat.lt_two_pow_self).le
  have hcard : Fintype.card (Finset (Fin k)) = 2 ^ k := by simp
  let h : Finset (Fin k) → Fin (2 ^ k) := fun J => Fin.cast hcard (Fintype.equivFin _ J)
  have hinj : Function.Injective h := fun J J' e =>
    (Fintype.equivFin _).injective (Fin.cast_injective hcard e)
  let U : Set (Fin n) := {z | ∃ (i : Fin k) (J : Finset (Fin k)), i ∈ J ∧ z = c (ι i) (h J)}
  obtain ⟨i, J, hiJ⟩ := hk n G hG ![U] (fun i => a (ι i)) (fun J => b (h J))
  have key : RealizeIn G.structure ![U] (gamma φ ψ) (Sum.elim (a (ι i)) (b (h J))) ↔ i ∈ J := by
    rw [realizeIn_gamma]
    constructor
    · rintro ⟨z, ⟨i', J', hi'J', rfl⟩, hz₁, hz₂⟩
      have hi := ((hpat (ι i') (h J')).1 (ι i)).mp hz₁
      have hJ := ((hpat (ι i') (h J')).2 (h J)).mp hz₂
      rw [Fin.castLE_injective _ hi, hinj hJ]
      exact hi'J'
    · intro hi
      exact ⟨c (ι i) (h J), ⟨i, J, hi, rfl⟩, ((hpat _ _).1 _).mpr rfl, ((hpat _ _).2 _).mpr rfl⟩
  rcases hiJ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact h₂ (key.mp h₁)
  · exact h₁ (key.mpr h₂)

end Lax185574Proofs.MonadicDependenceDpMinimal

namespace Lax185574Proofs.MonadicDependenceDpMinimal

open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.DpMinimality
open Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.MonadicDependenceDpMinimal.dpMinimal_of_monadicallyDependent
---
The proof in the paper. Let `āᵢ`, `b̄ⱼ`, `c_{i,j}` be a clean
`(φ, ψ)`-pattern of order `m × m`, where `m = 2^k`. Fix an injection `h`
of the subsets of `[k]` into `[m]`, and let `U` color the vertices
`c_{i, h(J)}` with `i ∈ J`. Then the formula `γ(x̄, ȳ) = ∃z (U(z) ∧
φ(x̄, z) ∧ ψ(ȳ, z))` holds of `āᵢ`, `b̄_{h(J)}` exactly when `i ∈ J`: for
`i ∈ J` the vertex `c_{i, h(J)}` is a witness, and a witness `c_{i', j'}`
has `i' = i` and `j' = h(J)` because the pattern is clean. So `γ` has the
independence property up to `k`, and by Baldwin–Shelah `k` is bounded in
terms of the class, `φ` and `ψ` alone.

The argument is carried out for the graph classes of the archive and
their monadic dependence, and transferred to the graph classes used
here.
-/
theorem dpMinimal_of_monadicallyDependent (C : GraphClass) (hC : MonadicallyDependent C) :
    DpMinimal C := by
  intro p p' φ ψ
  obtain ⟨t, ht⟩ := exists_not_hasCleanPattern_old (toOld C) (monadicallyDependent_toOld hC) φ ψ
  exact ⟨t, fun G hG => ht G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.MonadicDependenceDpMinimal
