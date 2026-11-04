import Lax185574Proofs.IP.Basics
import Lax185574Proofs.IP.Ramsey
import Lax185574Proofs.IP.Alternation

/-!
Shelah's reduction to a single variable on the left, in a finite form.

If a formula `φ(x̄; ȳ)` of colored graphs has the independence property on
a class, then some formula `ψ(x; z̄)` with a single left variable has it.
The proof is by induction on the length of `x̄ = x₁ x̄₂`. Suppose neither
`φ(x₁ x̄₂; ȳ)`, read as `ψ₂(x̄₂; x₁ ȳ)`, nor any of the pattern formulas
`χ_S(x₁; ȳ₁ … ȳ_d) = ∃x̄₂ ⋀_s φ(x₁ x̄₂; ȳ_s)^{[s ∈ S]}` has the independence
property. Take a long sequence of `ȳ`-tuples shattered by `x̄`-tuples, and
use Ramsey's theorem to make all shattering properties of the `χ_S` along
blocks constant. Take the witness `(a₁, ā₂)` of the even positions. No
`χ_S(a₁; ·)` alternates along successive blocks, so there is a long window
on which every `χ_S(a₁; ·)` is constant. On this window `φ(a₁ ā₂; ·)`
alternates, and so `ψ₂` shatters `d` tuples, a contradiction.
-/

namespace Lax185574Proofs.IP

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.Transductions

/-! ## The two auxiliary formulas -/

/-- Move the first left variable to the right. -/
def splitFirst {p : ℕ} {β : Type*} : Fin (p + 1) ⊕ β → Fin p ⊕ (Fin 1 ⊕ β)
  | Sum.inl i => Fin.cases (Sum.inr (Sum.inl 0)) Sum.inl i
  | Sum.inr b => Sum.inr (Sum.inr b)

/-- The formula `ψ₂(x̄₂; x₁ ȳ) = φ(x₁ x̄₂; ȳ)`. -/
def restFormula {k p : ℕ} {β : Type*} (φ : (CL k).Formula (Fin (p + 1) ⊕ β)) :
    (CL k).Formula (Fin p ⊕ (Fin 1 ⊕ β)) :=
  φ.relabel splitFirst

theorem realizeIn_restFormula {k n p : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n))
    {β : Type*} (φ : (CL k).Formula (Fin (p + 1) ⊕ β)) (x₂ : Fin p → Fin n) (a₁ : Fin n)
    (y : β → Fin n) :
    RealizeIn G.structure colors (restFormula φ) (Sum.elim x₂ (Sum.elim (fun _ => a₁) y)) ↔
      RealizeIn G.structure colors φ (Sum.elim (Fin.cons a₁ x₂) y) := by
  unfold restFormula
  rw [realizeIn_relabel]
  have : (Sum.elim x₂ (Sum.elim (fun _ => a₁) y) ∘ splitFirst) = Sum.elim (Fin.cons a₁ x₂) y := by
    funext v
    rcases v with i | b
    · cases i using Fin.cases <;> rfl
    · rfl
  rw [this]

/-- The variables of the `s`-th copy of `φ` in a pattern formula. -/
def patVar {p d : ℕ} {β : Type*} (s : Fin d) :
    Fin (p + 1) ⊕ β → (Fin 1 ⊕ (Fin d × β)) ⊕ Fin p
  | Sum.inl i => Fin.cases (Sum.inl (Sum.inl 0)) Sum.inr i
  | Sum.inr b => Sum.inl (Sum.inr (s, b))

/-- The pattern formula `χ_S(x₁; ȳ₀ … ȳ_{d-1}) = ∃x̄₂ ⋀_s φ(x₁ x̄₂; ȳ_s)^{[s ∈ S]}`. -/
noncomputable def patFormula {k p : ℕ} {β : Type*} [Finite β]
    (φ : (CL k).Formula (Fin (p + 1) ⊕ β)) (d : ℕ) (S : Finset (Fin d)) :
    (CL k).Formula (Fin 1 ⊕ (Fin d × β)) :=
  Formula.iExs (Fin p) (Formula.iInf fun s : Fin d => signed (s ∈ S) (φ.relabel (patVar s)))

theorem realizeIn_patFormula {k n p : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n))
    {β : Type*} [Finite β] (φ : (CL k).Formula (Fin (p + 1) ⊕ β)) (d : ℕ) (S : Finset (Fin d))
    (x₁ : Fin 1 → Fin n) (w : Fin d → β → Fin n) :
    RealizeIn G.structure colors (patFormula φ d S) (Sum.elim x₁ (fun sb => w sb.1 sb.2)) ↔
      ∃ x₂ : Fin p → Fin n, ∀ s,
        (RealizeIn G.structure colors φ (Sum.elim (Fin.cons (x₁ 0) x₂) (w s)) ↔ s ∈ S) := by
  unfold patFormula
  rw [realizeIn_iExs]
  apply exists_congr
  intro x₂
  rw [realizeIn_iInf]
  apply forall_congr'
  intro s
  rw [realizeIn_signed, realizeIn_relabel]
  have : (Sum.elim (Sum.elim x₁ (fun sb => w sb.1 sb.2)) x₂ ∘ patVar s) =
      Sum.elim (Fin.cons (x₁ 0) x₂) (w s) := by
    funext v
    rcases v with i | b
    · cases i using Fin.cases <;> rfl
    · rfl
  rw [this]

/-! ## The reduction step -/

/-- If `φ(x₁ x̄₂; ȳ)` has the independence property, then so has `ψ₂` or
one of the pattern formulas. -/
theorem reduction_step {C : GraphClass} {k p : ℕ} {β : Type} [Fintype β]
    (φ : (CL k).Formula (Fin (p + 1) ⊕ β)) (hφ : IPAll C φ)
    (h₂ : ¬ IPAll C (restFormula φ)) (hpat : ∀ d S, ¬ IPAll C (patFormula φ d S)) : False := by
  classical
  obtain ⟨d₂, hd₂⟩ := exists_not_IPAt (fun h => h₂ (IPAll.of_dual h))
  have hD' : ∀ S : Finset (Fin d₂), ∃ D, ∀ m, D ≤ m → ¬ IPAt C (dual (patFormula φ d₂ S)) m :=
    fun S => exists_not_IPAt (fun h => hpat d₂ S (IPAll.of_dual h))
  choose DS hDS using hD'
  let D := Finset.univ.sup DS
  have hD : ∀ S, ¬ IPAt C (dual (patFormula φ d₂ S)) D :=
    fun S => hDS S D (Finset.le_sup (Finset.mem_univ S))
  let W := 2 * d₂ + 1
  let L := (Fintype.card (Finset (Fin d₂)) * (2 * D) + 1) * W
  let eJ := Fintype.equivFin (Finset (Fin d₂) × Finset (Fin D))
  obtain ⟨Nb, hNb⟩ := exists_homogeneous_seq (D * d₂)
    (Fintype.card (Finset (Fin d₂) × Finset (Fin D))) L
  obtain ⟨n, G, hG, colors, bseq, wit, hbw⟩ := (hφ (2 ^ Nb)).toDual
  have hbw' : ∀ t S, RealizeIn G.structure colors φ (Sum.elim (wit S) (bseq t)) ↔ t ∈ S :=
    fun t S => (realizeIn_dual G colors φ (bseq t) (wit S)).symm.trans (hbw t S)
  -- Ramsey for the shattering properties of the pattern formulas along blocks
  let P : Fin (Fintype.card (Finset (Fin d₂) × Finset (Fin D))) → (Fin (D * d₂) → Fin Nb) → Prop :=
    fun j τ => ∃ x₁ : Fin 1 → Fin n, ∀ s : Fin D,
      (RealizeIn G.structure colors (patFormula φ d₂ (eJ.symm j).1)
        (Sum.elim x₁ (fun sb => bseq (τ (finProdFinEquiv (s, sb.1))) sb.2)) ↔ s ∈ (eJ.symm j).2)
  obtain ⟨ι, hι⟩ := hNb (le_refl Nb) P
  let b : Fin L → β → Fin n := fun t => bseq (ι t)
  -- the witness of the even positions
  let Sev : Finset (Fin Nb) := (Finset.univ.filter fun u : Fin L => Even u.val).map ι.toEmbedding
  let x := wit Sev
  have hx : ∀ u : Fin L, RealizeIn G.structure colors φ (Sum.elim x (b u)) ↔ Even u.val := by
    intro u
    rw [hbw']
    simp [Sev]
  let a₁ := x 0
  let a₂ : Fin p → Fin n := Fin.tail x
  have hxa : (Fin.cons a₁ a₂ : Fin (p + 1) → Fin n) = x := Fin.cons_self_tail x
  -- no pattern formula at `a₁` alternates along successive blocks
  let Q : Finset (Fin d₂) → (Fin d₂ → Fin L) → Prop := fun S σ =>
    RealizeIn G.structure colors (patFormula φ d₂ S)
      (Sum.elim (fun _ => a₁) (fun sb => b (σ sb.1) sb.2))
  have hQ : ∀ S, ¬ ∃ B : Fin (2 * D) → Fin d₂ → Fin L, (∀ u, StrictMono (B u)) ∧
      Successive B ∧ ∀ u, (Q S (B u) ↔ Even u.val) := by
    rintro S ⟨B, hBm, hBs, hBalt⟩
    apply hD S
    refine Shatters.IPAt_dual hG (colors := colors) (w := fun s sb => b (B (Fin.castLE (by omega) s) sb.1) sb.2) ?_
    intro S'
    refine shatters_of_alternation
      (fun (x₁ : Fin 1 → Fin n) (w : Fin d₂ × β → Fin n) =>
        RealizeIn G.structure colors (patFormula φ d₂ S) (Sum.elim x₁ w))
      (fun u sb => b (B u sb.1) sb.2) ?_ (fun _ => a₁) id strictMono_id (fun u => hBalt u)
      (Fin.castLE (by omega)) (Fin.strictMono_castLE _) S'
    intro S'' ρ ρ' hρ hρ'
    have key := hι (eJ (S, S'')) (concat (B ∘ ρ)) (concat (B ∘ ρ'))
      (concat_strictMono _ (fun u => hBm _) (hBs.comp hρ))
      (concat_strictMono _ (fun u => hBm _) (hBs.comp hρ'))
    simp only [P, Equiv.symm_apply_apply, Function.comp_apply, concat,
      Equiv.symm_apply_apply] at key
    exact key
  obtain ⟨w₀, hw₀, hconst⟩ := exists_window Q hQ le_rfl
  -- on the window, `ψ₂` shatters `d₂` tuples
  apply hd₂ d₂ le_rfl
  let e' : Fin W → Fin 1 ⊕ β → Fin n := fun u =>
    Sum.elim (fun _ => a₁) (b ⟨w₀ + u.val, by have := u.isLt; omega⟩)
  refine Shatters.IPAt_dual hG (colors := colors) (w := fun s => e' (Fin.castLE (by omega) s)) ?_
  intro S
  refine shatters_of_alternation
    (fun (x₂ : Fin p → Fin n) (w : Fin 1 ⊕ β → Fin n) =>
      RealizeIn G.structure colors (restFormula φ) (Sum.elim x₂ w))
    e' ?_ a₂ (fun u => ⟨w₀ % 2 + u.val, by have := u.isLt; omega⟩) ?_ ?_
    (Fin.castLE (by omega)) (Fin.strictMono_castLE _) S
  · intro S' ρ ρ' hρ hρ'
    simp only [e', realizeIn_restFormula]
    let σ : Fin d₂ → Fin L := fun s => ⟨w₀ + (ρ s).val, by have := (ρ s).isLt; omega⟩
    let σ' : Fin d₂ → Fin L := fun s => ⟨w₀ + (ρ' s).val, by have := (ρ' s).isLt; omega⟩
    have h := hconst S' σ σ' (fun s t hst => by
        show w₀ + (ρ s).val < w₀ + (ρ t).val
        have := hρ hst; exact Nat.add_lt_add_left this w₀)
      (fun s t hst => by
        show w₀ + (ρ' s).val < w₀ + (ρ' t).val
        have := hρ' hst; exact Nat.add_lt_add_left this w₀)
      (fun s => ⟨Nat.le_add_right _ _, by have := (ρ s).isLt; show w₀ + _ < _; omega⟩)
      (fun s => ⟨Nat.le_add_right _ _, by have := (ρ' s).isLt; show w₀ + _ < _; omega⟩)
    simp only [Q] at h
    rw [realizeIn_patFormula G colors φ d₂ S' (fun _ => a₁) (fun s => b (σ s)),
      realizeIn_patFormula G colors φ d₂ S' (fun _ => a₁) (fun s => b (σ' s))] at h
    exact h
  · intro u v huv
    show w₀ % 2 + u.val < w₀ % 2 + v.val
    have : u.val < v.val := huv
    omega
  · intro u
    simp only [e', realizeIn_restFormula]
    rw [hxa, hx, Nat.even_iff, Nat.even_iff]
    show (w₀ + (w₀ % 2 + u.val)) % 2 = 0 ↔ u.val % 2 = 0
    omega

/-! ## Shelah's reduction -/

/-- If a formula of colored graphs has the independence property on `C`,
then so has some formula with a single left variable. -/
theorem exists_single_left {C : GraphClass} {k : ℕ} :
    ∀ (p : ℕ) {β : Type} [Fintype β] (φ : (CL k).Formula (Fin (p + 1) ⊕ β)), IPAll C φ →
      ∃ (β' : Type) (_ : Fintype β') (ψ : (CL k).Formula (Fin 1 ⊕ β')), IPAll C ψ := by
  intro p
  induction p with
  | zero => intro β _ φ hφ; exact ⟨β, inferInstance, φ, hφ⟩
  | succ p ih =>
    intro β _ φ hφ
    by_cases h₂ : IPAll C (restFormula φ)
    · exact ih (restFormula φ) h₂
    by_cases hpat : ∃ d S, IPAll C (patFormula φ d S)
    · obtain ⟨d, S, h⟩ := hpat
      exact ⟨Fin d × β, inferInstance, _, h⟩
    push Not at hpat
    exact (reduction_step φ hφ h₂ hpat).elim

end Lax185574Proofs.IP
