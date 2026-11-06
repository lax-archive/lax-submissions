import Lax185574.BipartiteHomogeneity
import Lax185574.ForbiddenPhiPsiPatterns
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases

/-!
The two conditions of a `(φ, ψ)`-pattern constrain only later rows and
columns. On homogeneous subsets of the rows and columns, the exclusive
or of `φ` on two consecutive rows, and of `ψ` on two consecutive
columns, turns the pattern into a clean one.
-/

namespace Lax185574Proofs.ForbiddenPhiPsiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.PhiPsiPatterns Lax185574.DpMinimality
open Lax185574.BipartiteHomogeneity

universe u

variable {V : Type u} {p p' : ℕ}

/-- The formula `φ(x̄₁, z) ⊕ φ(x̄₂, z)` on the concatenated tuple `x̄₁x̄₂`. -/
def xorFormula {q : ℕ} (φ : Language.graph.Formula (Fin q ⊕ Fin 1)) :
    Language.graph.Formula (Fin (q + q) ⊕ Fin 1) :=
  let A : Language.graph.Formula (Fin (q + q) ⊕ Fin 1) :=
    φ.relabel (Sum.map (Fin.castAdd q) id)
  let B : Language.graph.Formula (Fin (q + q) ⊕ Fin 1) :=
    φ.relabel (Sum.map (Fin.natAdd q) id)
  (A ⊓ B.not) ⊔ (A.not ⊓ B)

theorem holds_xorFormula (G : SimpleGraph V) {q : ℕ}
    (φ : Language.graph.Formula (Fin q ⊕ Fin 1)) (a a' : Fin q → V) (z : V) :
    Holds G (xorFormula φ) (Fin.append a a') z ↔ Xor (Holds G φ a z) (Holds G φ a' z) := by
  let _ := G.structure
  have h₁ : Sum.elim (Fin.append a a') ![z] ∘ Sum.map (Fin.castAdd q) id = Sum.elim a ![z] := by
    funext x
    rcases x with i | i <;> simp
  have h₂ : Sum.elim (Fin.append a a') ![z] ∘ Sum.map (Fin.natAdd q) id = Sum.elim a' ![z] := by
    funext x
    rcases x with i | i
    · exact Fin.append_right a a' i
    · rfl
  unfold Holds xorFormula Xor
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_relabel, h₁, h₂]
  tauto

theorem orderType_pair_lt {t : ℕ} {x y x' y' : Fin t} (h : y < x) (h' : y' < x') :
    orderType ![x, y] = orderType ![x', y'] := by
  funext i j
  change compare (![x, y] i) (![x, y] j) = compare (![x', y'] i) (![x', y'] j)
  fin_cases i <;> fin_cases j <;>
    simp [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr h',
      compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr h']

/-- Two truth values, as one of four colors. -/
def enc (P Q : Prop) [Decidable P] [Decidable Q] : Fin 4 :=
  ⟨(if P then 2 else 0) + (if Q then 1 else 0), by split_ifs <;> decide⟩

theorem enc_inj {P Q P' Q' : Prop} [Decidable P] [Decidable Q] [Decidable P'] [Decidable Q']
    (h : enc P Q = enc P' Q') : (P ↔ P') ∧ (Q ↔ Q') := by
  unfold enc at h
  rw [Fin.mk.injEq] at h
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hP' : P' <;> by_cases hQ' : Q' <;>
    simp [hP, hQ, hP', hQ'] at h ⊢

/-- A large `(φ, ψ)`-pattern contains a clean pattern of order `m × m` of
the exclusive or formulas, on pairs of consecutive tuples. -/
theorem exists_hasCleanPattern_xorFormula (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) (m : ℕ) :
    ∃ t : ℕ, ∀ (V : Type u) (G : SimpleGraph V), HasPattern G φ ψ t t →
      HasCleanPattern G (xorFormula φ) (xorFormula ψ) m m := by
  classical
  obtain ⟨Uf, -, hUunb, hhom⟩ := exists_orderType_homogeneous 4 2
  obtain ⟨t, ht⟩ := hUunb (2 * m)
  refine ⟨t, fun V G ⟨a, b, c, hpat⟩ => ?_⟩
  let col : (Fin 2 → Fin t) → (Fin 2 → Fin t) → Fin 4 := fun I J =>
    enc (Holds G φ (a (I 1)) (c (I 0) (J 0))) (Holds G ψ (b (J 1)) (c (I 0) (J 0)))
  obtain ⟨I, J, hI, hJ, hc⟩ := hhom t col
  let σ := I.orderEmbOfFin hI
  let τ := J.orderEmbOfFin hJ
  have hσ : ∀ x, σ x ∈ I := fun x => Finset.orderEmbOfFin_mem I hI x
  have hτ : ∀ x, τ x ∈ J := fun x => Finset.orderEmbOfFin_mem J hJ x
  let r : Fin m → Fin t := fun i => σ ⟨2 * i, by omega⟩
  let r' : Fin m → Fin t := fun i => σ ⟨2 * i + 1, by omega⟩
  let s : Fin m → Fin t := fun j => τ ⟨2 * j, by omega⟩
  let s' : Fin m → Fin t := fun j => τ ⟨2 * j + 1, by omega⟩
  have hrr' : ∀ i, r i < r' i := fun i => σ.strictMono (by simp [Fin.lt_def])
  have hr'r : ∀ i' i : Fin m, i' < i → r' i' < r i := fun i' i h =>
    σ.strictMono (by simp only [Fin.lt_def]; omega)
  have hrr : ∀ i' i : Fin m, i' < i → r i' < r i := fun i' i h =>
    σ.strictMono (by simp only [Fin.lt_def]; omega)
  have hss' : ∀ j, s j < s' j := fun j => τ.strictMono (by simp [Fin.lt_def])
  have hs's : ∀ j' j : Fin m, j' < j → s' j' < s j := fun j' j h =>
    τ.strictMono (by simp only [Fin.lt_def]; omega)
  have hss : ∀ j' j : Fin m, j' < j → s j' < s j := fun j' j h =>
    τ.strictMono (by simp only [Fin.lt_def]; omega)
  let d : Fin m → Fin m → V := fun i j => c (r i) (s j)
  have hα : ∀ i' i j : Fin m,
      Xor (Holds G φ (a (r i')) (d i j)) (Holds G φ (a (r' i')) (d i j)) ↔ i' = i := by
    intro i' i j
    rcases lt_trichotomy i' i with h | rfl | h
    · have hcol := hc ![r i, r i'] ![r i, r' i'] ![s j, s j] ![s j, s j]
        (by intro x; fin_cases x <;> exact hσ _) (by intro x; fin_cases x <;> exact hσ _)
        (by intro x; fin_cases x <;> exact hτ _) (by intro x; fin_cases x <;> exact hτ _)
        (orderType_pair_lt (hrr i' i h) (hr'r i' i h)) rfl
      have := (enc_inj hcol).1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [d, Xor, this, h.ne]
      tauto
    · have h1 := (hpat (r i') (s j)).1.1
      have h2 := (hpat (r i') (s j)).1.2 (r' i') (hrr' i')
      simp only [d, Xor]
      tauto
    · have h1 := (hpat (r i) (s j)).1.2 (r i') (hrr i i' h)
      have h2 := (hpat (r i) (s j)).1.2 (r' i') ((hrr i i' h).trans (hrr' i'))
      simp only [d, Xor, h.ne']
      tauto
  have hβ : ∀ j' i j : Fin m,
      Xor (Holds G ψ (b (s j')) (d i j)) (Holds G ψ (b (s' j')) (d i j)) ↔ j' = j := by
    intro j' i j
    rcases lt_trichotomy j' j with h | rfl | h
    · have hcol := hc ![r i, r i] ![r i, r i] ![s j, s j'] ![s j, s' j']
        (by intro x; fin_cases x <;> exact hσ _) (by intro x; fin_cases x <;> exact hσ _)
        (by intro x; fin_cases x <;> exact hτ _) (by intro x; fin_cases x <;> exact hτ _)
        rfl (orderType_pair_lt (hss j' j h) (hs's j' j h))
      have := (enc_inj hcol).2
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [d, Xor, this, h.ne]
      tauto
    · have h1 := (hpat (r i) (s j')).2.1
      have h2 := (hpat (r i) (s j')).2.2 (s' j') (hss' j')
      simp only [d, Xor]
      tauto
    · have h1 := (hpat (r i) (s j)).2.2 (s j') (hss j j' h)
      have h2 := (hpat (r i) (s j)).2.2 (s' j') ((hss j j' h).trans (hss' j'))
      simp only [d, Xor, h.ne']
      tauto
  refine ⟨fun i => Fin.append (a (r i)) (a (r' i)), fun j => Fin.append (b (s j)) (b (s' j)), d,
    fun i j => ⟨fun i' => ?_, fun j' => ?_⟩⟩
  · exact (holds_xorFormula G φ _ _ _).trans (hα i' i j)
  · exact (holds_xorFormula G ψ _ _ _).trans (hβ j' i j)

/--
---
conclusion: Lax185574.ForbiddenPhiPsiPatterns.forbidden_phiPsi_patterns
---
The proof in the paper. Let `m` bound the order of the clean patterns of
the formulas `α(x̄₁x̄₂, z) = φ(x̄₁, z) ⊕ φ(x̄₂, z)` and `β(ȳ₁ȳ₂, z) =
ψ(ȳ₁, z) ⊕ ψ(ȳ₂, z)`, which dp-minimality provides. Color a pair of
index pairs `((i, i'), (j, j'))` by the truth values of `φ(āᵢ', c_{i,j})`
and `ψ(b̄ⱼ', c_{i,j})`, and take homogeneous sets `I`, `J` by the
bipartite Ramsey lemma, of size `2m` when `t` is large enough. Pair up
consecutive elements of `I` and `J`: with `ūᵢ = āᵣ āᵣ'` for the `2i`-th
and `(2i+1)`-st elements `r < r'` of `I`, likewise `w̄ⱼ`, and `d_{i,j} =
c_{r,s}`, the formula `α` holds of `ūᵢ', d_{i,j}` exactly when `i' = i`:
earlier pairs see two equal truth values by homogeneity, the pair itself
sees true then false, and later pairs see false twice. The same holds
for `β` and the columns. So `ū`, `w̄`, `d` form a clean `(α, β)`-pattern
of order `m × m`, which is excluded.
-/
theorem forbidden_phiPsi_patterns (C : GraphClass) (hC : DpMinimal C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasPattern G.toSimpleGraph φ ψ t t := by
  obtain ⟨m, hm⟩ := hC (xorFormula φ) (xorFormula ψ)
  obtain ⟨t, ht⟩ := exists_hasCleanPattern_xorFormula φ ψ m
  exact ⟨t, fun G hG hpat => hm G hG (ht _ _ hpat)⟩

end Lax185574Proofs.ForbiddenPhiPsiPatterns
