import Lax185574.DpMinimalEquivalence
import Lax185574.DpMinimalTypeBound
import Lax185574.MonadicDependenceDpMinimal
import Lax185574Proofs.FormulaRank
import Lax185574Proofs.Interface.IndependenceProperty
import Mathlib.Analysis.SpecificLimits.Normed

namespace Lax185574Proofs.DpMinimalEquivalence

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.MonadicDependence
open Lax185574.DpMinimality Lax185574.IndependenceProperty
open Lax185574.FirstOrderTypes Lax185574.Colorings
open Lax185574Proofs.FormulaRank Lax185574Proofs.Interface
open Lax710763.Transductions

/-- Exponentials beat polynomials. -/
theorem exists_mul_pow_lt_two_pow (F a : ℕ) : ∃ N : ℕ, F * (N + 1) ^ a < 2 ^ N := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt a (r := (2 : ℝ)) (by norm_num)
  have hpos : (0 : ℝ) < 1 / (2 * F + 1) := by positivity
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
  refine ⟨M, ?_⟩
  have h₁ := hM (M + 1) (Nat.le_succ M)
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at h₁
  have h₂ : (M + 1) ^ a * (2 * F + 1) < 2 ^ (M + 1) := by exact_mod_cast h₁
  rw [pow_succ] at h₂
  generalize (M + 1) ^ a = X at h₂ ⊢
  generalize 2 ^ M = Y at h₂ ⊢
  have h₃ : X * (2 * F + 1) = 2 * (F * X) + X := by ring
  omega

/-- The formula `ψ(w, y)`, with the parameter `w` for the left variable
and the single tuple variable for the right one. -/
noncomputable def paramFormula {V : Type} {c : ℕ}
    (ψ : (withColors Language.graph c).Formula (Fin 1 ⊕ Fin 1)) {W : Set V} (w : W) : (withColors Language.graph c).Formula (Fin 1 ⊕ W) :=
  ψ.relabel (Sum.elim (fun _ => Sum.inr w) Sum.inl)

theorem two_pow_le_typeCountOver {c N q : ℕ} (G : Graph) (col : Fin c → Set (Fin G.n))
    (ψ : (withColors Language.graph c).Formula (Fin 1 ⊕ Fin 1)) (hq : quantifierRank ψ ≤ q)
    (a : Fin N → Fin 1 → Fin G.n) (b : Finset (Fin N) → Fin 1 → Fin G.n)
    (hab : ∀ i J, RealizeIn G.toSimpleGraph.structure col ψ (Sum.elim (a i) (b J)) ↔ i ∈ J)
    (U : Finset (Fin G.n)) (hU : ∀ i, a i 0 ∈ U) :
    2 ^ N ≤ typeCountOver (expansion G.toSimpleGraph col) 1 q Set.univ
      (U : Set (Fin G.n)) := by
  let _ : (withColors Language.graph c).Structure (Fin G.n) := expansion G.toSimpleGraph col
  have hreal : ∀ i J, (paramFormula ψ (⟨a i 0, hU i⟩ : (U : Set (Fin G.n)))).Realize
      (Sum.elim (b J) Subtype.val) ↔ i ∈ J := by
    intro i J
    unfold paramFormula
    rw [Formula.realize_relabel]
    refine Iff.trans (iff_of_eq (congrArg (fun v => ψ.Realize v)
      (?_ : _ = Sum.elim (a i) (b J)))) (hab i J)
    funext x
    rcases x with x | x
    · have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      rfl
    · rfl
  have hinj : Function.Injective fun J : Finset (Fin N) =>
      rankTypeOver (L := withColors Language.graph c) q (U : Set (Fin G.n)) (b J) := by
    intro J J' hJ
    ext i
    have hmem : ∀ J, paramFormula ψ (⟨a i 0, hU i⟩ : (U : Set (Fin G.n))) ∈
        rankTypeOver (L := withColors Language.graph c) q (U : Set (Fin G.n)) (b J) ↔ i ∈ J := by
      intro J
      refine ⟨fun h => (hreal i J).mp h.2, fun h => ⟨?_, (hreal i J).mpr h⟩⟩
      unfold paramFormula
      rw [quantifierRank_formula_relabel]
      exact hq
    have hJ' : rankTypeOver (L := withColors Language.graph c) q (U : Set (Fin G.n)) (b J) =
        rankTypeOver (L := withColors Language.graph c) q (U : Set (Fin G.n)) (b J') := hJ
    rw [← hmem J, ← hmem J', hJ']
  unfold typeCountOver typesOver
  have hfin : (rankTypeOver (L := withColors Language.graph c) (k := 1) q (U : Set (Fin G.n)) ''
      {v | ∀ i, v i ∈ (Set.univ : Set (Fin G.n))}).Finite := (Set.toFinite _).image _
  calc 2 ^ N = (Set.range fun J : Finset (Fin N) =>
        rankTypeOver (L := withColors Language.graph c) q (U : Set (Fin G.n)) (b J)).ncard := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
          Nat.card_eq_fintype_card,
          Fintype.card_finset, Fintype.card_fin]
    _ ≤ _ := Set.ncard_le_ncard (by
        rintro _ ⟨J, rfl⟩
        exact ⟨b J, fun _ => trivial, rfl⟩) hfin

/--
---
conclusion: Lax185574.DpMinimalEquivalence.monadicallyDependent_iff_dpMinimal
---
A monadically dependent class is dp-minimal by the lemma on monadically
dependent classes. Conversely, let the class be dp-minimal, and suppose
a formula `φ(x, y)` with `c` colors has the independence property on it.
Let `q` be the quantifier rank of `φ`, and take `a` and `F` from the
type bound for dp-minimal classes, for `k = 1`, `q` and `c`. Choose `N`
with `F · (N + 1)^a < 2^N`, and take a colored graph, vertices
`a₁, …, a_N` and vertices `b_J` for `J ⊆ [N]` such that `φ(aᵢ, b_J)`
holds exactly when `i ∈ J`. With `U = {a₁, …, a_N}`, the formulas
`φ(aᵢ, y)` have parameters from `U` and rank at most `q`, so the
vertices `b_J` have pairwise different types of rank `q` over `U`. Hence
`2^N ≤ F · (|U| + 1)^a`, a contradiction. A class on which no formula
has the independence property is monadically dependent.
-/
theorem monadicallyDependent_iff_dpMinimal (C : GraphClass) :
    MonadicallyDependent C ↔ DpMinimal C := by
  refine ⟨Lax185574.MonadicDependenceDpMinimal.dpMinimal_of_monadicallyDependent C, fun hC => ?_⟩
  refine (monadicallyDependent_iff_forall_not_hasIP C).mpr fun c φ hφ => ?_
  let ψ := Formula.toMathlibSplit φ
  obtain ⟨a, ha⟩ := Lax185574.DpMinimalTypeBound.typeCountOver_le C hC 1 (quantifierRank ψ)
  obtain ⟨F, hF⟩ := ha c
  obtain ⟨N, hN⟩ := exists_mul_pow_lt_two_pow F a
  obtain ⟨G, hG, col, x, y, hxy⟩ := hφ N
  have hreal : ∀ i J, RealizeIn G.toSimpleGraph.structure col ψ (Sum.elim (x i) (y J)) ↔ i ∈ J :=
    fun i J => (realizeIn_toMathlibSplit_iff G col φ (x i) (y J)).trans (hxy i J)
  let U : Finset (Fin G.n) := Finset.univ.image fun i => x i 0
  have hU : ∀ i, x i 0 ∈ U := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hcard : U.card ≤ N := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := fun i => x i 0)
  have h₁ := two_pow_le_typeCountOver G col ψ le_rfl x y hreal U hU
  have h₂ := hF G hG col U
  have h₃ : F * (U.card + 1) ^ a ≤ F * (N + 1) ^ a :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  omega

end Lax185574Proofs.DpMinimalEquivalence
