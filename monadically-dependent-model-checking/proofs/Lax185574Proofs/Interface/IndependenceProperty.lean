import Lax185574.IndependenceProperty
import Lax185574Proofs.Interface.MDBridge

/-!
The independence property of `Lax185574.IndependenceProperty` and the
one for mathlib formulas over the classes of the archive.

`Old.HasIP` is the independence property for a mathlib formula over
graphs with colors, whose free variables are `Fin p ⊕ Fin p'`, on a
graph class of the archive. The proofs of the independence property
are written for it. A formula of `Lax185574.FirstOrderLogic` with the
free variables `x₀, …, x_{p+p'-1}` becomes such a formula by
`Formula.toMathlib` and the relabelling `finSumFinEquiv.symm`, and
conversely by `finSumFinEquiv` and `Formula.ofMathlib`. The assignment
`Fin.append a b` of the free variables corresponds to `Sum.elim a b`.
Under `toOld` and `ofOld` the independence property is preserved in
both directions.
-/

namespace Lax185574Proofs.Interface

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.FirstOrderLogic Lax710763.Transductions

namespace Old

/-- The formula `φ(x̄, ȳ)` over graphs with `k` colors has the
independence property on the class `C` of the archive: for every `m`
there are a colored member of `C`, tuples `a i` for `i < m` and tuples
`b J` for `J ⊆ {0, …, m-1}`, such that `φ(a i, b J)` holds exactly when
`i ∈ J`. -/
def HasIP (C : Lax199508.GraphClasses.GraphClass) {k p p' : ℕ}
    (φ : (withColors Language.graph k).Formula (Fin p ⊕ Fin p')) : Prop :=
  ∀ m : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧
    ∃ (colors : Fin k → Set (Fin n)) (a : Fin m → Fin p → Fin n)
      (b : Finset (Fin m) → Fin p' → Fin n),
      ∀ (i : Fin m) (J : Finset (Fin m)),
        RealizeIn G.structure colors φ (Sum.elim (a i) (b J)) ↔ i ∈ J

end Old

variable {k p p' : ℕ}

/-- A formula with the free variables `x₀, …, x_{p+p'-1}`, as a mathlib
formula with the free variables `Fin p ⊕ Fin p'`. -/
noncomputable def Formula.toMathlibSplit
    (φ : Lax185574.FirstOrderLogic.Formula (Fin k) (p + p')) :
    (withColors Language.graph k).Formula (Fin p ⊕ Fin p') :=
  (Formula.toMathlib φ).relabel finSumFinEquiv.symm

/-- A mathlib formula with the free variables `Fin p ⊕ Fin p'`, as a
formula with the free variables `x₀, …, x_{p+p'-1}`. -/
def Formula.ofMathlibSplit (ψ : (withColors Language.graph k).Formula (Fin p ⊕ Fin p')) :
    Lax185574.FirstOrderLogic.Formula (Fin k) (p + p') :=
  Formula.ofMathlib (ψ.relabel finSumFinEquiv)

theorem sumElim_comp_finSumFinEquiv_symm {α : Type*} (a : Fin p → α) (b : Fin p' → α) :
    Sum.elim a b ∘ finSumFinEquiv.symm = Fin.append a b := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl,
      Fin.append_left]
  · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr,
      Fin.append_right]

theorem append_comp_finSumFinEquiv {α : Type*} (a : Fin p → α) (b : Fin p' → α) :
    Fin.append a b ∘ finSumFinEquiv = Sum.elim a b := by
  rw [← sumElim_comp_finSumFinEquiv_symm, Function.comp_assoc, Equiv.symm_comp_self,
    Function.comp_id]

theorem realizeIn_relabel' {c n : ℕ} (M : Language.graph.Structure (Fin n))
    (colors : Fin c → Set (Fin n)) {α β : Type*} (ψ : (withColors Language.graph c).Formula α)
    (g : α → β) (w : β → Fin n) :
    RealizeIn M colors (ψ.relabel g) w ↔ RealizeIn M colors ψ (w ∘ g) := by
  unfold RealizeIn
  let _ := M
  let _ := colorStructure colors
  exact Formula.realize_relabel

theorem realizeIn_toMathlibSplit_iff (G : Graph) (col : Fin k → Set (Fin G.n))
    (φ : Lax185574.FirstOrderLogic.Formula (Fin k) (p + p')) (a : Fin p → Fin G.n)
    (b : Fin p' → Fin G.n) :
    RealizeIn G.toSimpleGraph.structure col (Formula.toMathlibSplit φ) (Sum.elim a b) ↔
      φ.Holds G col (Fin.append a b) := by
  unfold Formula.toMathlibSplit
  rw [realizeIn_relabel', sumElim_comp_finSumFinEquiv_symm, realizeIn_toMathlib_iff]

theorem holds_ofMathlibSplit_iff (G : Graph) (col : Fin k → Set (Fin G.n))
    (ψ : (withColors Language.graph k).Formula (Fin p ⊕ Fin p')) (a : Fin p → Fin G.n)
    (b : Fin p' → Fin G.n) :
    (Formula.ofMathlibSplit ψ).Holds G col (Fin.append a b) ↔
      RealizeIn G.toSimpleGraph.structure col ψ (Sum.elim a b) := by
  unfold Formula.ofMathlibSplit
  rw [holds_ofMathlib_iff, realizeIn_relabel', append_comp_finSumFinEquiv]

/-- The independence property on a graph class gives it on the class of
the archive, for the translated formula. -/
theorem hasIP_toOld {C : GraphClass} {φ : Lax185574.FirstOrderLogic.Formula (Fin k) (p + p')}
    (h : Lax185574.IndependenceProperty.HasIP C φ) :
    Old.HasIP (toOld C) (Formula.toMathlibSplit φ) := by
  intro m
  obtain ⟨G, hG, col, a, b, hab⟩ := h m
  exact ⟨G.n, G.toSimpleGraph, hG, col, a, b, fun i J =>
    (realizeIn_toMathlibSplit_iff G col φ (a i) (b J)).trans (hab i J)⟩

/-- The independence property on a class of the archive gives it on the
graph class, for the translated formula. -/
theorem hasIP_ofOld {D : Lax199508.GraphClasses.GraphClass}
    {ψ : (withColors Language.graph k).Formula (Fin p ⊕ Fin p')} (h : Old.HasIP D ψ) :
    Lax185574.IndependenceProperty.HasIP (ofOld D) (Formula.ofMathlibSplit ψ) := by
  intro m
  obtain ⟨n, G, hG, col, a, b, hab⟩ := h m
  exact ⟨Graph.ofSimpleGraph G, hG, col, a, b, fun i J =>
    (holds_ofMathlibSplit_iff (Graph.ofSimpleGraph G) col ψ (a i) (b J)).trans (hab i J)⟩

/-- No formula in two single variables has the independence property on
the class of the archive exactly when none has it on the graph class. -/
theorem forall_not_hasIP_toOld_iff (C : GraphClass) :
    (∀ (k : ℕ) (ψ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)),
        ¬ Old.HasIP (toOld C) ψ) ↔
      ∀ (k : ℕ) (φ : Lax185574.FirstOrderLogic.Formula (Fin k) (1 + 1)),
        ¬ Lax185574.IndependenceProperty.HasIP C φ :=
  ⟨fun h k _ hφ => h k _ (hasIP_toOld hφ), fun h k _ hψ => h k _ (hasIP_ofOld hψ)⟩

end Lax185574Proofs.Interface
