import Lax185574.DpMinimalInterpretations
import Lax185574Proofs.AtomicTypeBridge

/-!
Dp-minimality is preserved under interpretations with parameters. A
formula over `α(G, ū)` translates into a formula over `G` with the extra
parameters `ū`, by substituting the definition of the edges for each
edge atom. A clean pattern in `α(G, ū)` is thereby a clean pattern in `G`
for the translated formulas, with `ū` appended to each tuple.
-/

namespace Lax185574Proofs.DpMinimalInterpretations

open FirstOrder FirstOrder.Language Structure
open Lax185574.Graphs Lax185574.PhiPsiPatterns Lax185574.DpMinimality
open Lax185574.DpMinimalInterpretations
open Lax185574Proofs.AtomicTypeBridge

universe u w

variable {V : Type u} {β : Type w} {ℓ : ℕ}

/-- The edge formula of `α(G, w̄)`: `x₁ ≠ x₂ ∧ (α(x₁, x₂; w̄) ∨ α(x₂, x₁; w̄))`. -/
def edgeF (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ)) :
    Language.graph.Formula (Fin 2 ⊕ Fin ℓ) :=
  (Term.equal (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))).not ⊓
    (α ⊔ α.relabel (Sum.elim ![Sum.inl 1, Sum.inl 0] Sum.inr))

/-- The definition of a relation of the language of graphs. -/
def atomF (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ)) :
    ∀ {l : ℕ}, Language.graph.Relations l → Language.graph.Formula (Fin l ⊕ Fin ℓ)
  | _, .adj => edgeF α

/-- The variable map from `β ⊕ Fin n` to `(β ⊕ Fin ℓ) ⊕ Fin n`. -/
def vmap {n : ℕ} : β ⊕ Fin n → (β ⊕ Fin ℓ) ⊕ Fin n := Sum.map Sum.inl id

/-- The translation of a formula over `α(G, w̄)` into a formula over `G`
with the parameters `w̄`: edge atoms are replaced by their definition,
equalities and quantifiers stay. -/
def tr (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ)) :
    ∀ {n : ℕ}, Language.graph.BoundedFormula β n →
      Language.graph.BoundedFormula (β ⊕ Fin ℓ) n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (.var (vmap (termVar t₁))) (.var (vmap (termVar t₂)))
  | _, .rel R ts => BoundedFormula.relabel
      (Sum.elim (fun m => vmap (termVar (ts m))) fun k => Sum.inl (Sum.inr k)) (atomF α R)
  | _, .imp φ ψ => .imp (tr α φ) (tr α ψ)
  | _, .all φ => .all (tr α φ)

theorem realize_edgeF (G : SimpleGraph V) (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ))
    (u : Fin ℓ → V) (x y : V) :
    @Formula.Realize Language.graph V G.structure _ (edgeF α) (Sum.elim ![x, y] u) ↔
      (interpretedGraph G α u).Adj x y := by
  let _ := G.structure
  have hswap : (Sum.elim ![x, y] u ∘
      Sum.elim ![Sum.inl 1, Sum.inl 0] Sum.inr : Fin 2 ⊕ Fin ℓ → V) = Sum.elim ![y, x] u := by
    funext z
    rcases z with z | z
    · fin_cases z <;> rfl
    · rfl
  unfold edgeF interpretedGraph
  rw [SimpleGraph.fromRel_adj, Formula.realize_inf, Formula.realize_not, Formula.realize_sup,
    Formula.realize_relabel, hswap, Formula.realize_equal]
  rfl

theorem realize_atomF (G : SimpleGraph V) (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ))
    (u : Fin ℓ → V) {l : ℕ} (R : Language.graph.Relations l) (y : Fin l → V) :
    @Formula.Realize Language.graph V G.structure _ (atomF α R) (Sum.elim y u) ↔
      @RelMap Language.graph V (interpretedGraph G α u).structure l R y := by
  match l, R with
  | 2, .adj =>
    have hy : y = ![y 0, y 1] := by
      funext i
      fin_cases i <;> rfl
    change @Formula.Realize Language.graph V G.structure _ (edgeF α) (Sum.elim y u) ↔ _
    rw [hy, realize_edgeF]
    rfl

theorem realize_tr (G : SimpleGraph V) (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ))
    (u : Fin ℓ → V) {n : ℕ} (φ : Language.graph.BoundedFormula β n) (x : β → V)
    (xs : Fin n → V) :
    @BoundedFormula.Realize Language.graph V G.structure _ _ (tr α φ) (Sum.elim x u) xs ↔
      @BoundedFormula.Realize Language.graph V (interpretedGraph G α u).structure _ _ φ x xs := by
  have hv : ∀ {n : ℕ} (xs : Fin n → V) (a : β ⊕ Fin n),
      Sum.elim (Sum.elim x u) xs (vmap (ℓ := ℓ) a) = Sum.elim x xs a := by
    intro n xs a
    rcases a with a | a <;> rfl
  let _ := G.structure
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    simp only [tr, BoundedFormula.Realize, Term.realize_var, hv]
    rw [@realize_term _ _ V (interpretedGraph G α u).structure _ t₁,
      @realize_term _ _ V (interpretedGraph G α u).structure _ t₂]
  | rel R ts =>
    simp only [tr]
    rw [BoundedFormula.realize_relabel]
    have := realize_atomF G α u R fun m => Sum.elim x xs (termVar (ts m))
    unfold Formula.Realize at this
    simp only [BoundedFormula.Realize, @realize_term _ _ V (interpretedGraph G α u).structure]
    convert this using 2
    · funext y
      rcases y with m | k
      · simp only [Function.comp_apply, Sum.elim_inl]
        rw [← hv xs (termVar (ts m))]
        rfl
      · rfl
  | imp φ ψ ihφ ihψ =>
    simp only [tr, BoundedFormula.Realize, ihφ, ihψ]
  | all φ ih =>
    simp only [tr, BoundedFormula.Realize, ih]

/-- The translated formula `φ'(x̄ w̄, z)` of a formula `φ(x̄, z)`. -/
def liftF {p : ℕ} (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ))
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) :
    Language.graph.Formula (Fin (p + ℓ) ⊕ Fin 1) :=
  Formula.relabel
    (Sum.elim (Sum.elim (fun i => Sum.inl (Fin.castAdd ℓ i)) Sum.inr)
      fun k => Sum.inl (Fin.natAdd p k))
    (tr α φ)

theorem holds_liftF (G : SimpleGraph V) {p : ℕ} (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ))
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) (u : Fin ℓ → V) (a : Fin p → V) (c : V) :
    Holds G (liftF α φ) (Fin.append a u) c ↔ Holds (interpretedGraph G α u) φ a c := by
  let _ := G.structure
  unfold Holds liftF
  rw [Formula.realize_relabel]
  have hv : (Sum.elim (Fin.append a u) ![c] ∘
      Sum.elim (Sum.elim (fun i => Sum.inl (Fin.castAdd ℓ i)) Sum.inr)
        fun k => Sum.inl (Fin.natAdd p k)) = Sum.elim (Sum.elim a ![c]) u := by
    funext y
    rcases y with (i | z) | k
    · simp
    · rfl
    · simp
  rw [hv]
  exact realize_tr G α u φ _ _

/-- A clean pattern in `α(G, ū)` is a clean pattern in `G` for the
translated formulas, with `ū` appended to each tuple. -/
theorem hasCleanPattern_liftF (G : SimpleGraph V) {p p' : ℕ}
    (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ))
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1))
    (u : Fin ℓ → V) {s t : ℕ} (h : HasCleanPattern (interpretedGraph G α u) φ ψ s t) :
    HasCleanPattern G (liftF α φ) (liftF α ψ) s t := by
  obtain ⟨a, b, c, hp⟩ := h
  refine ⟨fun i => Fin.append (a i) u, fun j => Fin.append (b j) u, c, fun i j =>
    ⟨fun i' => ?_, fun j' => ?_⟩⟩
  · rw [holds_liftF]
    exact (hp i j).1 i'
  · rw [holds_liftF]
    exact (hp i j).2 j'

/--
---
conclusion: Lax185574.DpMinimalInterpretations.dpMinimal_interpretationClass
---
For formulas `φ(x̄, z)` and `ψ(ȳ, z)`, let `φ'(x̄ w̄, z)` and `ψ'(ȳ w̄, z)`
be obtained by replacing each atom `E(x₁, x₂)` by
`x₁ ≠ x₂ ∧ (α(x₁, x₂; w̄) ∨ α(x₂, x₁; w̄))`, which defines the edges of
`α(G, ū)` in `G` for `w̄ = ū`. Quantifiers and equality stay, as the two
graphs have the same vertices. So `G ⊨ φ'(ā ū, c)` if and only if
`α(G, ū) ⊨ φ(ā, c)`, and a clean `(φ, ψ)`-pattern of order `t × t` in
`α(G, ū)` with tuples `āᵢ`, `b̄ⱼ` gives a clean `(φ', ψ')`-pattern of the
same order in `G` with tuples `āᵢ ū`, `b̄ⱼ ū`. The order bound for
`(φ', ψ')` on the class depends only on the class, `φ`, `ψ` and `α`.
-/
theorem dpMinimal_interpretationClass (C : GraphClass) (hC : DpMinimal C) {ℓ : ℕ}
    (α : Language.graph.Formula (Fin 2 ⊕ Fin ℓ)) : DpMinimal (interpretationClass C α) := by
  intro p p' φ ψ
  obtain ⟨t, ht⟩ := hC (liftF α φ) (liftF α ψ)
  refine ⟨t, ?_⟩
  rintro _ ⟨G, hG, u, rfl⟩ h
  exact ht G hG (hasCleanPattern_liftF G.toSimpleGraph α φ ψ u h)

end Lax185574Proofs.DpMinimalInterpretations
