import Lax185574.ForbiddenPhiPsiPatterns
import Lax185574.BipartiteHomogeneity
import Lax185574Proofs.PatternFormula
import Mathlib.Data.Finset.Sort
import Lax185574Proofs.Interface.Shim.IndependenceProperty

namespace Lax185574Proofs.ForbiddenPhiPsiPatterns

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence Lax710763.Transductions
open Lax185574.PhiPsiPatterns Lax185574.BipartiteHomogeneity Lax185574Proofs.Interface.Old
open Lax185574Proofs.PatternFormula

theorem orderType_pair_lt {t : ℕ} {x y x' y' : Fin t} (h : y < x) (h' : y' < x') :
    orderType ![x, y] = orderType ![x', y'] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [orderType, compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr h',
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

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem forbidden_phiPsi_patterns_old (C : GraphClass) (hC : MonadicallyDependent C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ¬ HasPattern G φ ψ t t := by
  classical
  have hIP :=
    Lax185574Proofs.Shim.IndependenceProperty.not_hasIP_of_monadicallyDependent C hC
      (gamma φ ψ)
  unfold HasIP at hIP
  push Not at hIP
  obtain ⟨m₀, hm₀⟩ := hIP
  obtain ⟨Uf, -, hUunb, hhom⟩ := exists_orderType_homogeneous 4 2
  obtain ⟨t, ht⟩ := hUunb (2 * 2 ^ m₀ + 2)
  refine ⟨t, fun n G hG ⟨a, b, c, hpat⟩ => ?_⟩
  let col : (Fin 2 → Fin t) → (Fin 2 → Fin t) → Fin 4 := fun I J =>
    enc (Holds G φ (a (I 1)) (c (I 0) (J 0))) (Holds G ψ (b (J 1)) (c (I 0) (J 0)))
  obtain ⟨I, J, hI, hJ, hc⟩ := hhom t col
  let σ := I.orderEmbOfFin hI
  let τ := J.orderEmbOfFin hJ
  let m := 2 ^ m₀
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
  let d : Fin m → Fin m → Fin n := fun i j => c (r i) (s j)
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
  -- the independence pattern
  let ι : Fin m₀ → Fin m := Fin.castLE (Nat.lt_two_pow_self).le
  have hcard : Fintype.card (Finset (Fin m₀)) = m := by simp [m]
  let h : Finset (Fin m₀) → Fin m := fun K => Fin.cast hcard (Fintype.equivFin _ K)
  have hinj : Function.Injective h := fun K K' e =>
    (Fintype.equivFin _).injective (Fin.cast_injective hcard e)
  let U : Set (Fin n) := {z | ∃ (i : Fin m₀) (K : Finset (Fin m₀)), i ∈ K ∧ z = d (ι i) (h K)}
  let u : Fin m → Fin (p + p) → Fin n := fun i => Fin.append (a (r i)) (a (r' i))
  let w : Fin m → Fin (p' + p') → Fin n := fun j => Fin.append (b (s j)) (b (s' j))
  obtain ⟨i, K, hiK⟩ := hm₀ n G hG ![U] (fun i => u (ι i)) (fun K => w (h K))
  have key : RealizeIn G.structure ![U] (gamma φ ψ) (Sum.elim (u (ι i)) (w (h K))) ↔ i ∈ K := by
    rw [realizeIn_gamma]
    have e1 : u (ι i) ∘ Fin.castAdd p = a (r (ι i)) := by funext x; simp [u]
    have e2 : u (ι i) ∘ Fin.natAdd p = a (r' (ι i)) := by funext x; exact Fin.append_right _ _ x
    have e3 : w (h K) ∘ Fin.castAdd p' = b (s (h K)) := by funext x; simp [w]
    have e4 : w (h K) ∘ Fin.natAdd p' = b (s' (h K)) := by funext x; exact Fin.append_right _ _ x
    rw [e1, e2, e3, e4]
    constructor
    · rintro ⟨z, ⟨i', K', hi'K', rfl⟩, hz1, hz2⟩
      have hi := (hα (ι i) (ι i') (h K')).mp hz1
      have hK := (hβ (h K) (ι i') (h K')).mp hz2
      rw [Fin.castLE_injective _ hi, hinj hK]
      exact hi'K'
    · intro hi
      exact ⟨d (ι i) (h K), ⟨i, K, hi, rfl⟩, (hα _ _ _).mpr rfl, (hβ _ _ _).mpr rfl⟩
  rcases hiK with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.mp h1)
  · exact h1 (key.mpr h2)

end Lax185574Proofs.ForbiddenPhiPsiPatterns

namespace Lax185574Proofs.ForbiddenPhiPsiPatterns

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.MonadicDependence Lax185574.PhiPsiPatterns
open Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.ForbiddenPhiPsiPatterns.forbidden_phiPsi_patterns
---
The proof in the paper. Color a pair of index pairs `((i, i'), (j, j'))`
by the truth values of `φ(āᵢ', c_{i,j})` and `ψ(b̄ⱼ', c_{i,j})`, and
take homogeneous sets `I`, `J` by the bipartite Ramsey lemma. Pair up
consecutive elements of `I` and `J`: with `ūᵢ = āᵣ āᵣ'` for the `2i`-th
and `(2i+1)`-st elements `r < r'` of `I`, likewise `w̄ⱼ`, and `d_{i,j} =
c_{r,s}`, the exclusive or `φ(x̄₁, z) ⊕ φ(x̄₂, z)` holds of `ūᵢ',
d_{i,j}` exactly when `i' = i`: earlier pairs see two equal truth values
by homogeneity, the pair itself sees true then false, and later pairs
see false twice. The same holds for the columns. Then the formula `γ =
∃z (U(z) ∧ (φ ⊕ φ) ∧ (ψ ⊕ ψ))`, with `U` coloring the grid points `d_{i,
h(J)}` for `i ∈ J`, encodes membership `i ∈ J` for an injection `h` of
the subsets of `[k]` into the columns. By Baldwin–Shelah this bounds
`k`, hence the order of the pattern.

The argument is carried out for the graph classes of the archive and
their monadic dependence, and transferred to the graph classes used
here.
-/
theorem forbidden_phiPsi_patterns (C : GraphClass) (hC : MonadicallyDependent C)
    {p p' : ℕ} (φ : Language.graph.Formula (Fin p ⊕ Fin 1))
    (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)) :
    ∃ t : ℕ, ∀ G ∈ C, ¬ HasPattern G.toSimpleGraph φ ψ t t := by
  obtain ⟨t, ht⟩ := forbidden_phiPsi_patterns_old (toOld C) (monadicallyDependent_toOld hC) φ ψ
  exact ⟨t, fun G hG => ht G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.ForbiddenPhiPsiPatterns
