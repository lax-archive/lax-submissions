import Lax185574Proofs.IP.Shelah
import Lax185574Proofs.IP.CodingReduction
import Lax185574Proofs.Interface.IndependenceProperty

/-!
The tuple form of the independence property on monadically dependent
classes (Baldwin–Shelah).

A formula `φ(x̄; ȳ)` with the independence property yields one with a
single left variable (Shelah's reduction, `IP/Shelah`). Its dual has a
single right variable `z`, and `ψ(x̄; z) ∧ ψ(x̄'; z)` is a coding formula.
A coding formula of least total arity has single variables only
(`IP/CodingReduction`). A coding formula in single variables gives a
formula `φ(x, y)` with the independence property, so the class is not
monadically dependent.
-/

namespace Lax185574Proofs.IndependencePropertyTuples

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence Lax710763.Transductions
open Lax185574Proofs.Interface.Old Lax185574Proofs.IP

/-- Coding is invariant under renaming the variables of the two tuples. -/
theorem CodesAll.relabel {C : GraphClass} {k : ℕ} {α β α' β' : Type*}
    {θ : (CL k).Formula ((α ⊕ β) ⊕ Fin 1)} (h : CodesAll C θ) (e₁ : α' ≃ α) (e₂ : β' ≃ β) :
    CodesAll C (θ.relabel (Sum.map (Sum.map e₁.symm e₂.symm) id)) := by
  intro m
  obtain ⟨n, G, hG, colors, a, b, c, hc⟩ := h m
  refine ⟨n, G, hG, colors, fun i => a i ∘ e₁, fun j => b j ∘ e₂, c, fun i j i' j' => ?_⟩
  rw [realizeIn_relabel, ← hc i j i' j']
  apply iff_of_eq
  congr 1
  funext v
  rcases v with (v | v) | v <;> simp

/-- If `θ` with at least two left variables codes on `C`, then a formula
with one left variable fewer, or with a single left variable, codes. -/
theorem coding_reduction {C : GraphClass} {k p q : ℕ}
    (θ : (CL k).Formula ((Fin (p + 2) ⊕ Fin q) ⊕ Fin 1)) (hθ : CodesAll C θ) :
    CodesAll C (theta₁ θ) ∨ ∃ μ, CodesAll C (thetaParam θ μ) := by
  classical
  obtain ⟨o, ho⟩ := exists_forall_of_finite
    (ι := Option (Fin (p + 2) → Fin (p + 1) ⊕ Fin (p + 2)))
    (fun o m => match o with
      | none => CodesAt C (theta₁ θ) m
      | some μ => CodesAt C (thetaParam θ μ) m)
    (fun o m m' h hm => match o with
      | none => CodesAt.mono h hm
      | some _ => CodesAt.mono h hm)
    (fun m => (coding_reduction_at θ hθ m).elim (fun h => ⟨none, h⟩)
      (fun ⟨μ, h⟩ => ⟨some μ, h⟩))
  match o with
  | none => exact Or.inl ho
  | some μ => exact Or.inr ⟨μ, ho⟩

/-- A coding formula on `C` gives one in three single variables. -/
theorem exists_singleton_coding {C : GraphClass} :
    ∀ (s k p q : ℕ) (θ : (CL k).Formula ((Fin p ⊕ Fin q) ⊕ Fin 1)), p + q = s → CodesAll C θ →
      ∃ (k' : ℕ) (θ' : (CL k').Formula ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)), CodesAll C θ' := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have reduce : ∀ (k p₀ q : ℕ) (θ : (CL k).Formula ((Fin (p₀ + 2) ⊕ Fin q) ⊕ Fin 1)),
        p₀ + 2 + q = s → CodesAll C θ →
          ∃ (k' : ℕ) (θ' : (CL k').Formula ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)), CodesAll C θ' := by
      intro k p₀ q θ hs hθ
      rcases coding_reduction θ hθ with h | ⟨μ, h⟩
      · exact ih (1 + q) (by omega) _ 1 q _ rfl h
      · exact ih (p₀ + 1 + q) (by omega) _ (p₀ + 1) q _ rfl h
    intro k p q θ hs hθ
    match p, q, θ, hs, hθ with
    | 0, _, θ, _, hθ => exact absurd (hθ 2) (not_codesAt_two_of_isEmpty_left θ)
    | _ + 1, 0, θ, _, hθ =>
      exact absurd (hθ.swap 2) (not_codesAt_two_of_isEmpty_left (swapCoding θ))
    | 1, 1, θ, _, hθ => exact ⟨k, θ, hθ⟩
    | p₀ + 2, q + 1, θ, hs, hθ => exact reduce k p₀ (q + 1) θ hs hθ
    | 1, q₀ + 2, θ, hs, hθ => exact reduce k q₀ 1 (swapCoding θ) (by omega) hθ.swap

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem not_hasIP_of_monadicallyDependent_old (C : GraphClass)
    (hC : MonadicallyDependent C) {k p p' : ℕ}
    (φ : (withColors Language.graph k).Formula (Fin p ⊕ Fin p')) :
    ¬ HasIP C φ := by
  intro hφ
  match p, φ, hφ with
  | 0, φ, hφ =>
    obtain ⟨n, G, hG, colors, a, b, hab⟩ := hφ 2
    have h0 := (hab 0 {0}).mpr (Finset.mem_singleton_self 0)
    have ha : a 1 = a 0 := funext fun x => x.elim0
    rw [← ha, hab] at h0
    exact absurd h0 (by decide)
  | p + 1, φ, hφ =>
    obtain ⟨β', _, ψ, hψ⟩ := exists_single_left p φ hφ
    have h₂ := CodesAll.of_IPAll (IPAll.toDual hψ)
    let e := Fintype.equivFin β'
    have h₃ := CodesAll.relabel h₂ e.symm e.symm
    obtain ⟨k', θ', h₄⟩ := exists_singleton_coding _ _ _ _ _ rfl h₃
    exact (Lax185574Proofs.IndependenceProperty.monadicallyDependent_iff_forall_not_hasIP_old C).mp hC
      _ _ (hasIP_codeFormula h₄)

end Lax185574Proofs.IndependencePropertyTuples

namespace Lax185574Proofs.IndependencePropertyTuples

open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.MonadicDependence
open Lax185574.IndependenceProperty Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.IndependenceProperty.not_hasIP_of_monadicallyDependent
---
Suppose `φ(x̄; ȳ)` has the independence property on `C`. The left tuple is
not empty, since otherwise all `aᵢ` agree. By Shelah's reduction, carried
out with Ramsey's theorem on finite shattered sequences, some formula
`ψ(x; z̄)` with a single left variable has the independence property, and
so has its dual `ψ*(z̄; x)`. Then `ψ*(z̄; x) ∧ ψ*(z̄'; x)` codes pairs: for
tuples `aᵢ` and `a_{n+j}` the elements `b_{{k, n+l}}` satisfy it exactly
when `(i, j) = (k, l)`. Among all formulas coding on `C`, with any number
of colors, take one of least total arity. If it has two left variables,
then either `x` extends by elements of a color `A` to a tuple coding `z`
and no other element of a color `C`, which is a coding formula with a
single left variable, or a spurious witness gives a coding formula with
parameters and fewer left variables. By symmetry the minimal formula is
`θ(x, y, z)` in single variables. With a color `C₀` for the codes `c_{i,J}`
with `i ∈ J`, the formula `∃z (C₀(z) ∧ θ(x, y, z))` has the independence
property. So `C` is not monadically dependent.

The argument is carried out for the graph classes of the archive and
mathlib formulas, and transferred to the graph classes used
here and the translation
of formulas.
-/
theorem not_hasIP_of_monadicallyDependent (C : GraphClass) (hC : MonadicallyDependent C)
    {k p p' : ℕ} (φ : Formula (Fin k) (p + p')) : ¬ HasIP C φ := fun h =>
  not_hasIP_of_monadicallyDependent_old (toOld C) (monadicallyDependent_toOld hC) _
    (hasIP_toOld h)

end Lax185574Proofs.IndependencePropertyTuples
