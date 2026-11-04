import Lax185574Proofs.Interface.IndependenceProperty

/-!
Basic tools for the independence property of formulas of colored graphs.

`IPAt C φ m` says that some colored member of `C` contains `m` tuples
shattered by `φ`. The free variables of `φ` form an arbitrary sum
`α ⊕ β` of a left and a right part, and `HasIP` is the case of the
types `Fin p` and `Fin p'`. The statement is monotone in `m` and
invariant under renaming the variables of either part. The dual of a
formula exchanges the two parts. If `φ` shatters `2^m` tuples, its dual
shatters `m` tuples.

The second part collects the semantics of the connectives used later.
-/

namespace Lax185574Proofs.IP

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.Transductions Lax185574Proofs.Interface.Old

/-- Graphs with `k` colors, the language of all formulas below. -/
abbrev CL (k : ℕ) : Language := withColors Language.graph k

/-! ## Semantics of connectives -/

section Semantics

variable {k n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n))

theorem realizeIn_inf {α : Type*} (ψ χ : (CL k).Formula α) (w : α → Fin n) :
    RealizeIn G.structure colors (ψ ⊓ χ) w ↔
      RealizeIn G.structure colors ψ w ∧ RealizeIn G.structure colors χ w := by
  unfold RealizeIn
  let _ := G.structure
  let _ := colorStructure colors
  exact Formula.realize_inf

theorem realizeIn_not {α : Type*} (ψ : (CL k).Formula α) (w : α → Fin n) :
    RealizeIn G.structure colors ψ.not w ↔ ¬ RealizeIn G.structure colors ψ w := by
  unfold RealizeIn
  let _ := G.structure
  let _ := colorStructure colors
  exact Formula.realize_not

theorem realizeIn_relabel {α β : Type*} (ψ : (CL k).Formula α) (g : α → β) (w : β → Fin n) :
    RealizeIn G.structure colors (ψ.relabel g) w ↔ RealizeIn G.structure colors ψ (w ∘ g) := by
  unfold RealizeIn
  let _ := G.structure
  let _ := colorStructure colors
  exact Formula.realize_relabel

theorem realizeIn_iExs {α γ : Type*} [Finite γ] (ψ : (CL k).Formula (α ⊕ γ)) (w : α → Fin n) :
    RealizeIn G.structure colors (ψ.iExs γ) w ↔
      ∃ u : γ → Fin n, RealizeIn G.structure colors ψ (Sum.elim w u) := by
  unfold RealizeIn
  let _ := G.structure
  let _ := colorStructure colors
  exact Formula.realize_iExs

theorem realizeIn_iInf {α γ : Type*} [Finite γ] (f : γ → (CL k).Formula α) (w : α → Fin n) :
    RealizeIn G.structure colors (Formula.iInf f) w ↔
      ∀ g, RealizeIn G.structure colors (f g) w := by
  unfold RealizeIn
  let _ := G.structure
  let _ := colorStructure colors
  exact Formula.realize_iInf

/-- The formula `ψ` if `b` holds, and its negation otherwise. -/
def signed {k : ℕ} {α : Type*} (b : Prop) [Decidable b] (ψ : (CL k).Formula α) :
    (CL k).Formula α :=
  if b then ψ else ψ.not

theorem realizeIn_signed {α : Type*} (b : Prop) [Decidable b] (ψ : (CL k).Formula α)
    (w : α → Fin n) :
    RealizeIn G.structure colors (signed b ψ) w ↔ (RealizeIn G.structure colors ψ w ↔ b) := by
  unfold signed
  split_ifs with h
  · simp [h]
  · rw [realizeIn_not]; simp [h]

end Semantics

/-! ## The independence property at a fixed size -/

/-- Some colored member of `C` has tuples `a i` for `i < m` and `b J` for
`J ⊆ {0, …, m-1}` with `φ(a i, b J)` exactly when `i ∈ J`. -/
def IPAt (C : GraphClass) {k : ℕ} {α β : Type*} (φ : (CL k).Formula (α ⊕ β)) (m : ℕ) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
    ∃ (colors : Fin k → Set (Fin n)) (a : Fin m → α → Fin n) (b : Finset (Fin m) → β → Fin n),
      ∀ (i : Fin m) (J : Finset (Fin m)),
        RealizeIn G.structure colors φ (Sum.elim (a i) (b J)) ↔ i ∈ J

theorem hasIP_iff {C : GraphClass} {k p p' : ℕ} (φ : (CL k).Formula (Fin p ⊕ Fin p')) :
    HasIP C φ ↔ ∀ m, IPAt C φ m := Iff.rfl

theorem IPAt.mono {C : GraphClass} {k : ℕ} {α β : Type*} {φ : (CL k).Formula (α ⊕ β)}
    {m m' : ℕ} (h : IPAt C φ m) (hm : m' ≤ m) : IPAt C φ m' := by
  classical
  obtain ⟨n, G, hG, colors, a, b, hab⟩ := h
  refine ⟨n, G, hG, colors, fun i => a (Fin.castLE hm i),
    fun J => b (J.map (Fin.castLEEmb hm)), fun i J => ?_⟩
  rw [hab]
  simp only [Finset.mem_map, Fin.castLEEmb_apply]
  constructor
  · rintro ⟨j, hj, hji⟩
    rwa [Fin.castLE_inj.mp hji] at hj
  · intro hi; exact ⟨i, hi, rfl⟩

/-- A formula has the independence property at every size. -/
def IPAll (C : GraphClass) {k : ℕ} {α β : Type*} (φ : (CL k).Formula (α ⊕ β)) : Prop :=
  ∀ m, IPAt C φ m

/-- Without the independence property, some size is not shattered. -/
theorem exists_not_IPAt {C : GraphClass} {k : ℕ} {α β : Type*} {φ : (CL k).Formula (α ⊕ β)}
    (h : ¬ IPAll C φ) : ∃ d, ∀ m, d ≤ m → ¬ IPAt C φ m := by
  unfold IPAll at h
  push Not at h
  obtain ⟨d, hd⟩ := h
  exact ⟨d, fun m hm hm' => hd (hm'.mono hm)⟩

/-- Renaming the variables of both parts along bijections. -/
theorem IPAt.relabel {C : GraphClass} {k : ℕ} {α β α' β' : Type*} {φ : (CL k).Formula (α ⊕ β)}
    (e₁ : α' ≃ α) (e₂ : β' ≃ β) {m : ℕ} (h : IPAt C φ m) :
    IPAt C (φ.relabel (Sum.map e₁.symm e₂.symm)) m := by
  obtain ⟨n, G, hG, colors, a, b, hab⟩ := h
  refine ⟨n, G, hG, colors, fun i => a i ∘ e₁, fun J => b J ∘ e₂, fun i J => ?_⟩
  rw [realizeIn_relabel, ← hab i J]
  apply iff_of_eq
  congr 1
  funext x
  rcases x with x | x <;> simp

/-- The dual formula, with the two parts of the free variables exchanged. -/
def dual {k : ℕ} {α β : Type*} (φ : (CL k).Formula (α ⊕ β)) : (CL k).Formula (β ⊕ α) :=
  φ.relabel Sum.swap

theorem realizeIn_dual {k n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n))
    {α β : Type*} (φ : (CL k).Formula (α ⊕ β)) (u : β → Fin n) (w : α → Fin n) :
    RealizeIn G.structure colors (dual φ) (Sum.elim u w) ↔
      RealizeIn G.structure colors φ (Sum.elim w u) := by
  unfold dual
  rw [realizeIn_relabel]
  apply iff_of_eq
  congr 1
  funext x
  rcases x with x | x <;> rfl

/-- If `φ` shatters `2^m` tuples, its dual shatters `m` tuples. -/
theorem IPAt.toDual {C : GraphClass} {k : ℕ} {α β : Type*} {φ : (CL k).Formula (α ⊕ β)} {m : ℕ}
    (h : IPAt C φ (2 ^ m)) : IPAt C (dual φ) m := by
  classical
  obtain ⟨n, G, hG, colors, a, b, hab⟩ := h
  have hcard : Fintype.card (Finset (Fin m)) = 2 ^ m := by
    rw [Fintype.card_finset, Fintype.card_fin]
  let e : Finset (Fin m) ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq hcard
  let Jj : Fin m → Finset (Fin (2 ^ m)) := fun j => Finset.univ.filter fun i => j ∈ e.symm i
  refine ⟨n, G, hG, colors, fun j => b (Jj j), fun S => a (e S), fun j S => ?_⟩
  rw [realizeIn_dual, hab]
  simp [Jj]

/-- Shattering in a single colored member: every subset `S` of the
tuples `w s` is cut out by some left tuple. -/
def Shatters {k n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n)) {α β : Type*}
    (φ : (CL k).Formula (α ⊕ β)) {d : ℕ} (w : Fin d → β → Fin n) : Prop :=
  ∀ S : Finset (Fin d), ∃ x : α → Fin n,
    ∀ s, RealizeIn G.structure colors φ (Sum.elim x (w s)) ↔ s ∈ S

/-- Shattering of `d` right tuples gives the independence property of the
dual at size `d`. -/
theorem Shatters.IPAt_dual {C : GraphClass} {k n : ℕ} {G : SimpleGraph (Fin n)} (hG : C n G)
    {colors : Fin k → Set (Fin n)} {α β : Type*} {φ : (CL k).Formula (α ⊕ β)} {d : ℕ}
    {w : Fin d → β → Fin n} (h : Shatters G colors φ w) : IPAt C (dual φ) d := by
  choose x hx using h
  refine ⟨n, G, hG, colors, w, x, fun s S => ?_⟩
  rw [realizeIn_dual]
  exact hx S s

theorem IPAll.toDual {C : GraphClass} {k : ℕ} {α β : Type*} {φ : (CL k).Formula (α ⊕ β)}
    (h : IPAll C φ) : IPAll C (dual φ) :=
  fun m => (h (2 ^ m)).toDual

theorem IPAll.of_dual {C : GraphClass} {k : ℕ} {α β : Type*} {φ : (CL k).Formula (α ⊕ β)}
    (h : IPAll C (dual φ)) : IPAll C φ := by
  intro m
  obtain ⟨n, G, hG, colors, a, b, hab⟩ := (h (2 ^ m)).toDual
  refine ⟨n, G, hG, colors, a, b, fun i J => ?_⟩
  rw [← hab i J]
  unfold dual
  rw [realizeIn_relabel, realizeIn_relabel]
  apply iff_of_eq
  congr 1
  funext x
  rcases x with x | x <;> rfl

end Lax185574Proofs.IP
