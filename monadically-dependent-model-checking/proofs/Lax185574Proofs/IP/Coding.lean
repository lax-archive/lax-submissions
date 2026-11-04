import Lax185574Proofs.IP.Basics
import Lax185574Proofs.IndependenceProperty

/-!
Coding configurations.

A formula `θ(x̄, ȳ, z)` with a single variable `z` *codes* `m × m` pairs in
a colored graph if there are tuples `a i`, `b j` and elements `c k l` with
`θ(a i, b j, c k l)` exactly when `(i, j) = (k, l)`. This file proves the
following.

- Coding is monotone in `m` and symmetric in the two tuples.
- A formula `ψ(x̄; z)` with the independence property and a single right
  variable gives the coding formula `ψ(x̄; z) ∧ ψ(x̄'; z)`.
- A coding formula with three single variables gives a formula `φ(x, y)`
  with the independence property, using one more color for a set of
  codes.
-/

namespace Lax185574Proofs.IP

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.Transductions
open Lax185574Proofs.Interface.Old Lax185574Proofs.IndependenceProperty

/-- The formula `θ` codes `m × m` pairs in some colored member of `C`. -/
def CodesAt (C : GraphClass) {k : ℕ} {α β : Type*} (θ : (CL k).Formula ((α ⊕ β) ⊕ Fin 1))
    (m : ℕ) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
    ∃ (colors : Fin k → Set (Fin n)) (a : Fin m → α → Fin n) (b : Fin m → β → Fin n)
      (c : Fin m → Fin m → Fin n), ∀ i j i' j',
        RealizeIn G.structure colors θ (Sum.elim (Sum.elim (a i) (b j)) (fun _ : Fin 1 => c i' j')) ↔
          (i = i' ∧ j = j')

/-- The formula `θ` codes pairs at every size. -/
def CodesAll (C : GraphClass) {k : ℕ} {α β : Type*}
    (θ : (CL k).Formula ((α ⊕ β) ⊕ Fin 1)) : Prop :=
  ∀ m, CodesAt C θ m

theorem CodesAt.mono {C : GraphClass} {k : ℕ} {α β : Type*}
    {θ : (CL k).Formula ((α ⊕ β) ⊕ Fin 1)} {m m' : ℕ} (h : CodesAt C θ m) (hm : m' ≤ m) :
    CodesAt C θ m' := by
  obtain ⟨n, G, hG, colors, a, b, c, h⟩ := h
  refine ⟨n, G, hG, colors, fun i => a (Fin.castLE hm i), fun j => b (Fin.castLE hm j),
    fun i j => c (Fin.castLE hm i) (Fin.castLE hm j), fun i j i' j' => ?_⟩
  rw [h]
  simp [Fin.castLE_inj]

/-- Exchange the two tuples of a coding formula. -/
def swapCoding {k : ℕ} {α β : Type*} (θ : (CL k).Formula ((α ⊕ β) ⊕ Fin 1)) :
    (CL k).Formula ((β ⊕ α) ⊕ Fin 1) :=
  θ.relabel (Sum.map Sum.swap id)

theorem CodesAll.swap {C : GraphClass} {k : ℕ} {α β : Type*}
    {θ : (CL k).Formula ((α ⊕ β) ⊕ Fin 1)} (h : CodesAll C θ) : CodesAll C (swapCoding θ) := by
  intro m
  obtain ⟨n, G, hG, colors, a, b, c, h⟩ := h m
  refine ⟨n, G, hG, colors, b, a, fun j i => c i j, fun j i j' i' => ?_⟩
  unfold swapCoding
  rw [realizeIn_relabel]
  have : (Sum.elim (Sum.elim (b j) (a i)) (fun _ : Fin 1 => c i' j') ∘ Sum.map Sum.swap id) =
      Sum.elim (Sum.elim (a i) (b j)) (fun _ : Fin 1 => c i' j') := by
    funext v
    rcases v with (v | v) | v <;> rfl
  rw [this, h]
  tauto

/-- A coding with an empty left tuple has size at most one. -/
theorem not_codesAt_two_of_isEmpty_left {C : GraphClass} {k : ℕ} {α β : Type*} [IsEmpty α]
    (θ : (CL k).Formula ((α ⊕ β) ⊕ Fin 1)) : ¬ CodesAt C θ 2 := by
  rintro ⟨n, G, hG, colors, a, b, c, h⟩
  have h0 := (h 0 0 0 0).mpr ⟨rfl, rfl⟩
  have ha : a 1 = a 0 := funext fun x => isEmptyElim x
  rw [← ha, h] at h0
  exact absurd h0.1 (by decide)

/-- If for every size one of finitely many monotone properties holds, then
one of them holds at every size. -/
theorem exists_forall_of_finite {ι : Type*} [Finite ι] (P : ι → ℕ → Prop)
    (hmono : ∀ x m m', P x m → m' ≤ m → P x m') (h : ∀ m, ∃ x, P x m) : ∃ x, ∀ m, P x m := by
  classical
  have := Fintype.ofFinite ι
  by_contra hne
  push Not at hne
  choose B hB using hne
  obtain ⟨x, hx⟩ := h (Finset.univ.sup B)
  exact hB x (hmono x _ _ hx (Finset.le_sup (Finset.mem_univ x)))

/-! ## From the independence property to coding -/

/-- The coding formula `ψ(x̄; z) ∧ ψ(x̄'; z)`. -/
def pairFormula {k : ℕ} {α : Type*} (ψ : (CL k).Formula (α ⊕ Fin 1)) :
    (CL k).Formula ((α ⊕ α) ⊕ Fin 1) :=
  ψ.relabel (Sum.elim (fun a => Sum.inl (Sum.inl a)) fun _ => Sum.inr 0) ⊓
    ψ.relabel (Sum.elim (fun a => Sum.inl (Sum.inr a)) fun _ => Sum.inr 0)

theorem CodesAll.of_IPAll {C : GraphClass} {k : ℕ} {α : Type*} {ψ : (CL k).Formula (α ⊕ Fin 1)}
    (h : IPAll C ψ) : CodesAll C (pairFormula ψ) := by
  classical
  intro m
  obtain ⟨n, G, hG, colors, A, B, hAB⟩ := h (m + m)
  have hAB' : ∀ i J, RealizeIn G.structure colors ψ (Sum.elim (A i) (fun _ => B J 0)) ↔ i ∈ J := by
    intro i J
    rw [← single_eq (B J)]
    exact hAB i J
  refine ⟨n, G, hG, colors, fun i => A (Fin.castAdd m i), fun j => A (Fin.natAdd m j),
    fun i j => B {Fin.castAdd m i, Fin.natAdd m j} 0, fun i j i' j' => ?_⟩
  unfold pairFormula
  rw [realizeIn_inf, realizeIn_relabel, realizeIn_relabel]
  have e1 : (Sum.elim (Sum.elim (A (Fin.castAdd m i)) (A (Fin.natAdd m j)))
      (fun _ : Fin 1 => B {Fin.castAdd m i', Fin.natAdd m j'} 0) ∘
        Sum.elim (fun a => Sum.inl (Sum.inl a)) fun _ => Sum.inr 0) =
      Sum.elim (A (Fin.castAdd m i)) (fun _ : Fin 1 => B {Fin.castAdd m i', Fin.natAdd m j'} 0) := by
    funext v; rcases v with v | v <;> rfl
  have e2 : (Sum.elim (Sum.elim (A (Fin.castAdd m i)) (A (Fin.natAdd m j)))
      (fun _ : Fin 1 => B {Fin.castAdd m i', Fin.natAdd m j'} 0) ∘
        Sum.elim (fun a => Sum.inl (Sum.inr a)) fun _ => Sum.inr 0) =
      Sum.elim (A (Fin.natAdd m j)) (fun _ : Fin 1 => B {Fin.castAdd m i', Fin.natAdd m j'} 0) := by
    funext v; rcases v with v | v <;> rfl
  rw [e1, e2, hAB', hAB']
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd,
    Fin.val_natAdd]
  have := i.isLt; have := j.isLt; have := i'.isLt; have := j'.isLt
  omega

/-! ## From coding in single variables to the independence property -/

/-- The formula `∃z (C₀(z) ∧ θ(x, y, z))`, with `C₀` a new color. -/
noncomputable def codeFormula {k : ℕ} (θ : (CL k).Formula ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)) :
    (CL (k + 1)).Formula (Fin 1 ⊕ Fin 1) :=
  Formula.iExs (Fin 1) (colorAtom (Fin.natAdd k 0) (Sum.inr 0) ⊓ liftColors 1 θ)

theorem hasIP_codeFormula {C : GraphClass} {k : ℕ} {θ : (CL k).Formula ((Fin 1 ⊕ Fin 1) ⊕ Fin 1)}
    (h : CodesAll C θ) : HasIP C (codeFormula θ) := by
  classical
  intro m
  have hcard : Fintype.card (Finset (Fin m)) = 2 ^ m := by
    rw [Fintype.card_finset, Fintype.card_fin]
  let e : Finset (Fin m) ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq hcard
  have hm : m ≤ 2 ^ m := (Nat.lt_two_pow_self).le
  obtain ⟨n, G, hG, colors, a, b, c, hc⟩ := h (2 ^ m)
  let C₀ : Set (Fin n) := {z | ∃ i J, i ∈ J ∧ z = c (Fin.castLE hm i) (e J)}
  refine ⟨n, G, hG, Fin.append colors ![C₀], fun i => a (Fin.castLE hm i), fun J => b (e J),
    fun i J => ?_⟩
  unfold codeFormula
  rw [realizeIn_iExs]
  simp only [realizeIn_inf]
  have hC : Fin.append colors ![C₀] (Fin.natAdd k 0) = C₀ := by rw [Fin.append_right]; rfl
  simp only [Lax185574Proofs.IndependenceProperty.realizeIn_colorAtom, hC, Sum.elim_inr]
  constructor
  · rintro ⟨u, ⟨i', J', hi', hu⟩, hθ⟩
    rw [realizeIn_liftColors] at hθ
    have hθ' : RealizeIn G.structure colors θ
        (Sum.elim (Sum.elim (a (Fin.castLE hm i)) (b (e J)))
          (fun _ : Fin 1 => c (Fin.castLE hm i') (e J'))) := by
      convert hθ using 2
      funext v
      rw [Subsingleton.elim v 0, hu]
    obtain ⟨h1, h2⟩ := (hc _ _ _ _).mp hθ'
    rw [Fin.castLE_inj.mp h1, e.injective h2]
    exact hi'
  · intro hi
    refine ⟨fun _ : Fin 1 => c (Fin.castLE hm i) (e J), ⟨i, J, hi, rfl⟩, ?_⟩
    rw [realizeIn_liftColors]
    exact (hc _ _ _ _).mpr ⟨rfl, rfl⟩

end Lax185574Proofs.IP
