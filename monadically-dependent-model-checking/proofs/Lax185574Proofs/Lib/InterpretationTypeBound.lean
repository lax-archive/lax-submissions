import Lax185574.FirstOrderTypes
import Lax185574Proofs.FormulaRank
import Lax185574Proofs.AtomicTypeBridge

/-!
Types in a structure that is definable in another one, after lem:interp-bound
of an earlier version of the source. Fix k, q, q₀ ∈ ℕ. Let B be a structure
and A be definable on a subset of V(B) with parameters S by formulas of
quantifier rank at most q₀, including the formula defining its domain. Then
|Types^A_{k,q}(V(A))| ≤ |Types^B_{k,q+q₀}(V(B)/S)|.

The translation `tr` of formulas over A into formulas over B, with its rank
bound `quantifierRank_tr` and its correctness `realize_tr`, is the
interpretation step used in the proof of lem:skel-def-to-types.
-/

namespace Lax185574Proofs.Lib.InterpretationTypeBound

open FirstOrder FirstOrder.Language Structure Lax185574.FirstOrderTypes
open Lax185574Proofs.AtomicTypeBridge Lax185574Proofs.FormulaRank

universe u v u' v' z w

section Translation

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L'.IsRelational]
variable {V : Type z} [L.Structure V] {D : Set V} {S : Set V}
variable (δ : L.Formula (Fin 1 ⊕ S))
variable (ρ : ∀ {l : ℕ}, L'.Relations l → L.Formula (Fin l ⊕ S))
variable {α : Type w}

/-- The variable map from `α ⊕ Fin n` to `(α ⊕ S) ⊕ Fin n`. -/
def vmap {n : ℕ} : α ⊕ Fin n → (α ⊕ S) ⊕ Fin n := Sum.map Sum.inl id

/-- The translation of a formula over the defined structure into a formula
over the defining structure: relations are replaced by their definitions
and quantifiers are relativized to the domain. -/
def tr : ∀ {n : ℕ}, L'.BoundedFormula α n → L.BoundedFormula (α ⊕ S) n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (.var (vmap (termVar t₁))) (.var (vmap (termVar t₂)))
  | _, .rel R ts => BoundedFormula.relabel
      (Sum.elim (fun m => vmap (termVar (ts m))) fun s => Sum.inl (Sum.inr s)) (ρ R)
  | _, .imp φ ψ => .imp (tr φ) (tr ψ)
  | n, .all φ => .all (.imp (BoundedFormula.relabel
      (Sum.elim (fun _ : Fin 1 => (Sum.inr (Fin.last n) : (α ⊕ S) ⊕ Fin (n + 1)))
        fun s => Sum.inl (Sum.inr s)) δ) (tr φ))

omit [L.Structure V] in
theorem quantifierRank_tr {q₀ : ℕ} (hδ : quantifierRank δ ≤ q₀)
    (hρ : ∀ {l : ℕ} (R : L'.Relations l), quantifierRank (ρ R) ≤ q₀) :
    ∀ {n : ℕ} (φ : L'.BoundedFormula α n), quantifierRank (tr δ ρ φ) ≤ quantifierRank φ + q₀
  | _, .falsum => by simp [tr, quantifierRank]
  | _, .equal _ _ => by simp [tr, quantifierRank]
  | _, .rel R _ => by
      simp only [tr, quantifierRank, zero_add]
      rw [quantifierRank_relabel]
      exact hρ R
  | _, .imp φ ψ => by
      have h1 := quantifierRank_tr hδ hρ φ
      have h2 := quantifierRank_tr hδ hρ ψ
      simp only [tr, quantifierRank] at h1 h2 ⊢
      omega
  | _, .all φ => by
      have h1 := quantifierRank_tr hδ hρ φ
      simp only [tr, quantifierRank] at h1 ⊢
      rw [quantifierRank_relabel]
      omega

theorem realize_tr (A : L'.Structure D)
    (hδ : ∀ v : V, δ.Realize (Sum.elim (fun _ => v) Subtype.val) ↔ v ∈ D)
    (hρ : ∀ {l : ℕ} (R : L'.Relations l) (x : Fin l → D),
      (ρ R).Realize (Sum.elim (fun i => (x i : V)) Subtype.val) ↔
        @Structure.RelMap L' D A l R x) :
    ∀ {n : ℕ} (φ : L'.BoundedFormula α n) (x : α → D) (xs : Fin n → D),
      (tr δ ρ φ).Realize (Sum.elim (Subtype.val ∘ x) Subtype.val) (Subtype.val ∘ xs) ↔
        @BoundedFormula.Realize L' D A α n φ x xs := by
  have hv : ∀ {n : ℕ} (x : α → D) (xs : Fin n → D) (a : α ⊕ Fin n),
      Sum.elim (Sum.elim (Subtype.val ∘ x) (Subtype.val : S → V)) (Subtype.val ∘ xs)
        (vmap (S := S) a) =
        ((Sum.elim x xs a : D) : V) := by
    intro n x xs a
    rcases a with a | a <;> rfl
  intro n φ
  induction φ with
  | falsum => intro x xs; exact Iff.rfl
  | equal t₁ t₂ =>
    intro x xs
    simp only [tr, BoundedFormula.Realize, Term.realize_var, hv]
    rw [@realize_term L' _ D A _ t₁, @realize_term L' _ D A _ t₂]
    exact Subtype.val_injective.eq_iff
  | rel R ts =>
    intro x xs
    simp only [tr]
    rw [BoundedFormula.realize_relabel]
    have := hρ R fun m => Sum.elim x xs (termVar (ts m))
    unfold Formula.Realize at this
    simp only [BoundedFormula.Realize, @realize_term L' _ D A _]
    convert this using 2
    · funext y
      rcases y with m | s'
      · simp only [Function.comp_apply, Sum.elim_inl]
        rw [← hv x xs (termVar (ts m))]
        rfl
      · rfl
  | imp φ ψ ihφ ihψ =>
    intro x xs
    simp only [tr, BoundedFormula.Realize, ihφ, ihψ]
  | @all n φ ih =>
    intro x xs
    simp only [tr, BoundedFormula.Realize]
    constructor
    · intro h d
      have h1 := h (d : V)
      rw [BoundedFormula.realize_relabel] at h1
      have h2 : (Sum.elim (Sum.elim (Subtype.val ∘ x) Subtype.val)
          (Fin.snoc (Subtype.val ∘ xs) (d : V) ∘ Fin.castAdd 0) ∘
          Sum.elim (fun _ : Fin 1 => (Sum.inr (Fin.last n) : (α ⊕ S) ⊕ Fin (n + 1)))
            fun s => Sum.inl (Sum.inr s)) = Sum.elim (fun _ => (d : V)) Subtype.val := by
        funext y
        rcases y with i | s
        · simp
        · rfl
      rw [h2, show (Fin.snoc (Subtype.val ∘ xs) (d : V) ∘ Fin.natAdd (n + 1) : Fin 0 → V) =
        default from Subsingleton.elim _ _] at h1
      have h3 := h1 ((hδ d).mpr d.2)
      rw [← ih x (Fin.snoc xs d)]
      convert h3 using 2
      exact Fin.comp_snoc _ _ _
    · intro h y hy
      rw [BoundedFormula.realize_relabel] at hy
      have h2 : (Sum.elim (Sum.elim (Subtype.val ∘ x) Subtype.val)
          (Fin.snoc (Subtype.val ∘ xs) y ∘ Fin.castAdd 0) ∘
          Sum.elim (fun _ : Fin 1 => (Sum.inr (Fin.last n) : (α ⊕ S) ⊕ Fin (n + 1)))
            fun s => Sum.inl (Sum.inr s)) = Sum.elim (fun _ => y) Subtype.val := by
        funext z
        rcases z with i | s
        · simp
        · rfl
      rw [h2, show (Fin.snoc (Subtype.val ∘ xs) y ∘ Fin.natAdd (n + 1) : Fin 0 → V) =
        default from Subsingleton.elim _ _] at hy
      have hyD : y ∈ D := (hδ y).mp hy
      have := (ih x (Fin.snoc xs ⟨y, hyD⟩)).mpr (h ⟨y, hyD⟩)
      convert this using 2
      rw [Fin.comp_snoc]

end Translation

/-- The structure `A` on the subtype of `D` is definable in the
structure on `V` by formulas of quantifier rank at most `q₀` with
parameters from `S`: one formula defines `D`, and for every relation
symbol one formula defines its interpretation on tuples from `D`. -/
def IsDefinableOn {L : Language.{u, v}} {L' : Language.{u', v'}} {V : Type z}
    [L.Structure V] (D : Set V) (A : L'.Structure D) (S : Set V) (q₀ : ℕ) : Prop :=
  (∃ δ : L.Formula (Fin 1 ⊕ S), quantifierRank δ ≤ q₀ ∧
    ∀ v : V, δ.Realize (Sum.elim (fun _ => v) Subtype.val) ↔ v ∈ D) ∧
  ∀ {l : ℕ} (R : L'.Relations l), ∃ φ : L.Formula (Fin l ⊕ S), quantifierRank φ ≤ q₀ ∧
    ∀ x : Fin l → D,
      φ.Realize (Sum.elim (fun i => (x i : V)) Subtype.val) ↔ @Structure.RelMap L' D A l R x

/-- **Type bound for definable structures.** The number of rank-`q`
types of `k`-tuples in a structure definable with parameters `S` by
formulas of rank at most `q₀` is at most the number of rank-`(q+q₀)`
types over `S` of `k`-tuples in the defining structure.

Translate every formula `ψ(x̄)` over `A` into a formula `ψ*(x̄)` over the
defining structure with parameters from `S`: replace each relation by its
defining formula and relativize each quantifier to the domain formula. By
induction `ψ*` has quantifier rank at most that of `ψ` plus `q₀`, and
`A ⊨ ψ(ā)` holds exactly when `ψ*(ā)` holds in the defining structure. So
the type of quantifier rank `q + q₀` over `S` of a tuple of `A` determines
its type of rank `q` in `A`.
-/
theorem typeCount_le_typeCountOver {L : Language.{u, v}} {L' : Language.{u', v'}}
    [L'.IsRelational] {V : Type z} [Finite V] [L.Structure V] (D : Set V)
    (A : L'.Structure D) (S : Set V) (k q q₀ : ℕ)
    (hA : IsDefinableOn (L := L) D A S q₀) :
    @typeCount L' D A k q Set.univ ≤ typeCountOver ‹L.Structure V› k (q + q₀) Set.univ S := by
  classical
  obtain ⟨⟨δ, hδq, hδ⟩, hrel⟩ := hA
  choose ρ hρq hρ using fun {l : ℕ} (R : L'.Relations l) => hrel R
  unfold typeCount typeCountOver types typesOver
  have hX : {x : Fin k → D | ∀ i, x i ∈ Set.univ} = Set.univ := by simp
  refine (ncard_image_le_of_factor (X := {x : Fin k → D | ∀ i, x i ∈ Set.univ})
    (@rankType L' D A q k) (fun x => rankTypeOver (L := L) (q + q₀) S (Subtype.val ∘ x))
    ?_ (Set.toFinite _)).trans ?_
  · intro x _ y _ hxy
    ext ψ
    simp only [rankType, Set.mem_ofPred_eq]
    refine and_congr_right fun hψ => ?_
    have hr : quantifierRank (tr δ (fun R => ρ R) ψ) ≤ q + q₀ :=
      (quantifierRank_tr δ (fun R => ρ R) hδq (fun R => hρq R) ψ).trans (by omega)
    have key : ∀ z : Fin k → D, @Formula.Realize L' D A _ ψ z ↔
        tr δ (fun R => ρ R) ψ ∈ rankTypeOver (L := L) (q + q₀) S (Subtype.val ∘ z) := by
      intro z
      simp only [rankTypeOver, Set.mem_ofPred_eq, hr, true_and]
      unfold Formula.Realize
      rw [← realize_tr δ (fun R => ρ R) A hδ (fun R => hρ R) ψ z default]
      exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))
    rw [key, key, hxy]
  · refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨x, -, rfl⟩
    exact ⟨Subtype.val ∘ x, fun _ => Set.mem_univ _, rfl⟩

end Lax185574Proofs.Lib.InterpretationTypeBound
