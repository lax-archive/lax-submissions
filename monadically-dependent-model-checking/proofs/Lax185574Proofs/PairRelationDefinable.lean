import Lax185574.PairRelationDefinable
import Lax185574Proofs.BipartiteWalks
import Lax185574Proofs.DistanceFormulaRank
import Mathlib.Tactic.FinCases

namespace Lax185574Proofs.PairRelationDefinable

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Partitions Lax185574.PairRelation Lax185574.Colorings
open Lax185574.FirstOrderTypes Lax185574.BipartiteGraphs Lax185574.GaifmanGraph
open Lax185574Proofs.WithinDistBasics Lax185574Proofs.BipartiteWalks
open Lax185574Proofs.DistanceFormulaRank

universe z

/-! ## Semantics: chains of five steps -/

section Semantics

variable {V : Type z}

/-- One step of a walk between opposite copies in the bipartite graph
on the parts of `x` and `y`: `a` and `b` lie in opposite parts, and they
are equal or related by `A`. -/
def Step (P : Setoid V) (A : V → V → Prop) (x y a b : V) : Prop :=
  ((P a x ∧ P b y) ∨ (P b x ∧ P a y)) ∧ (a = b ∨ A a b)

/-- The bipartite graph on the parts of `x` and `y` with diagonal edges
and the edges of `A`. -/
def partGraph (P : Setoid V) (A : V → V → Prop) (x y : V) : SimpleGraph (V ⊕ V) :=
  bipartiteGraph fun u v => P u x ∧ P v y ∧ (u = v ∨ A u v)

/-- The chain `x, z₁, z₂, z₃, z₄, y`. -/
def chain (x : V) (zs : Fin 4 → V) (y : V) : Fin 6 → V :=
  ![x, zs 0, zs 1, zs 2, zs 3, y]

theorem step_left {P : Setoid V} {A : V → V → Prop} {x y a b : V} (ha : P a x)
    (h : Step P A x y a b) : P b y ∧ (partGraph P A x y).Adj (.inl a) (.inr b) := by
  obtain ⟨hp | hp, he⟩ := h
  · exact ⟨hp.2, (adj_inl_inr _ _ _).mpr ⟨ha, hp.2, he⟩⟩
  · have hb : P b y := P.trans hp.1 (P.trans (P.symm ha) hp.2)
    exact ⟨hb, (adj_inl_inr _ _ _).mpr ⟨ha, hb, he⟩⟩

theorem step_right {P : Setoid V} {A : V → V → Prop} (hA : ∀ a b, A a b → A b a)
    {x y a b : V} (ha : P a y) (h : Step P A x y a b) :
    P b x ∧ (partGraph P A x y).Adj (.inr a) (.inl b) := by
  have he : b = a ∨ A b a := h.2.imp Eq.symm (hA a b)
  obtain ⟨hp | hp, -⟩ := h
  · have hb : P b x := P.trans hp.2 (P.trans (P.symm ha) hp.1)
    exact ⟨hb, (adj_inr_inl _ _ _).mpr ⟨hb, ha, he⟩⟩
  · exact ⟨hp.1, (adj_inr_inl _ _ _).mpr ⟨hp.1, ha, he⟩⟩

theorem step_of_adj {P : Setoid V} {A : V → V → Prop} (hA : ∀ a b, A a b → A b a)
    {x y : V} {s t : V ⊕ V} (h : (partGraph P A x y).Adj s t) :
    Step P A x y (Sum.elim id id s) (Sum.elim id id t) := by
  rcases s with a | a <;> rcases t with b | b
  · exact absurd h (not_adj_inl_inl _ _ _)
  · obtain ⟨ha, hb, he⟩ := (adj_inl_inr _ _ _).mp h
    exact ⟨Or.inl ⟨ha, hb⟩, he⟩
  · obtain ⟨hb, ha, he⟩ := (adj_inr_inl _ _ _).mp h
    exact ⟨Or.inr ⟨hb, ha⟩, he.imp Eq.symm (hA b a)⟩
  · exact absurd h (not_adj_inr_inr _ _ _)

/-- A walk of odd length at most `5` can be padded to length exactly `5`
by going back and forth along its first edge. -/
theorem exists_walk_five {W : Type*} {K : SimpleGraph W} {s t : W} (p : K.Walk s t)
    (hp : p.length ≤ 5) (hodd : p.length % 2 = 1) : ∃ q : K.Walk s t, q.length = 5 := by
  have pad : ∀ (q : K.Walk s t), 1 ≤ q.length → ∃ q' : K.Walk s t, q'.length = q.length + 2 := by
    intro q hq
    cases q with
    | nil => simp at hq
    | cons h q =>
      exact ⟨.cons h (.cons h.symm (.cons h q)), by simp⟩
  have hcases : p.length = 1 ∨ p.length = 3 ∨ p.length = 5 := by omega
  rcases hcases with h | h | h
  · obtain ⟨q, hq⟩ := pad p (by omega)
    obtain ⟨q', hq'⟩ := pad q (by omega)
    exact ⟨q', by omega⟩
  · obtain ⟨q, hq⟩ := pad p (by omega)
    exact ⟨q, by omega⟩
  · exact ⟨p, h⟩

/-- Walks of length at most `5` between opposite copies of `x` and `y`
are chains of five steps. -/
theorem withinDist_iff_chain (P : Setoid V) (A : V → V → Prop) (hA : ∀ a b, A a b → A b a)
    (x y : V) :
    WithinDist (partGraph P A x y) 5 (.inl x) (.inr y) ↔
      ∃ zs : Fin 4 → V, ∀ i : Fin 5, Step P A x y (chain x zs y i.castSucc) (chain x zs y i.succ) := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq⟩ := exists_walk_five p hp (by
      have := odd_length (E := fun u v => P u x ∧ P v y ∧ (u = v ∨ A u v)) p
      exact this)
    let w : ℕ → V := fun i => Sum.elim id id (q.getVert i)
    have hw : ∀ i < 5, Step P A x y (w i) (w (i + 1)) := fun i hi =>
      step_of_adj hA (q.adj_getVert_succ (by omega))
    have h0 : w 0 = x := by simp [w]
    have h5 : w 5 = y := by simp [w, q.getVert_of_length_le hq.le]
    refine ⟨fun j => w (j + 1), fun i => ?_⟩
    fin_cases i
    · simpa [chain, h0] using hw 0 (by omega)
    · simpa [chain] using hw 1 (by omega)
    · simpa [chain] using hw 2 (by omega)
    · simpa [chain] using hw 3 (by omega)
    · simpa [chain, h5] using hw 4 (by omega)
  · rintro ⟨zs, hzs⟩
    have s0 := hzs 0
    have s1 := hzs 1
    have s2 := hzs 2
    have s3 := hzs 3
    have s4 := hzs 4
    simp only [chain] at s0 s1 s2 s3 s4
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
      Matrix.cons_val_one] at s0
    obtain ⟨p1, e1⟩ := step_left (P.refl x) s0
    obtain ⟨p2, e2⟩ := step_right hA p1 (by simpa using s1)
    obtain ⟨p3, e3⟩ := step_left p2 (by simpa using s2)
    obtain ⟨p4, e4⟩ := step_right hA p3 (by simpa using s3)
    obtain ⟨-, e5⟩ := step_left p4 (by simpa using s4)
    refine ⟨.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 .nil)))), by simp⟩

end Semantics

/-! ## The formula -/

/-- The language of graphs with one color. -/
abbrev L1 : Language := withColors Language.graph 1

section Syntax

variable {β : Type} {n : ℕ}

/-- The adjacency atom. -/
def adjF (t s : L1.Term (β ⊕ Fin n)) : L1.BoundedFormula β n :=
  Relations.boundedFormula₂ (Sum.inl Language.adj : L1.Relations 2) t s

/-- The color atom `S(t)`. -/
def colF (t : L1.Term (β ⊕ Fin n)) : L1.BoundedFormula β n :=
  Relations.boundedFormula₁ (Sum.inr (ColorRel.color 0) : L1.Relations 1) t

/-- The free variable `b`. -/
def fv (b : β) : L1.Term (β ⊕ Fin n) := Term.var (Sum.inl b)

/-- `θ_S(a, b)`: `a` and `b` have the same atomic type over `S`. -/
def theta (a b : β) : L1.Formula β :=
  (fv a).bdEqual (fv b) ⊔
    (∼(colF (fv a)) ⊓ ∼(colF (fv b)) ⊓
      BoundedFormula.all ((colF (Term.var (Sum.inr 0))).imp
        ((adjF (fv a) (Term.var (Sum.inr 0))).iff (adjF (fv b) (Term.var (Sum.inr 0))))))

/-- `e^σ_S(a, b; x, y)`: `a` and `b` lie in opposite parts among the
parts of `x` and `y`, and they are equal or adjacent (if `σ` is true),
respectively non-adjacent (if `σ` is false). -/
def edgeF (σ : Bool) (x y a b : β) : L1.Formula β :=
  ((theta a x ⊓ theta b y) ⊔ (theta b x ⊓ theta a y)) ⊓
    ((fv a).bdEqual (fv b) ⊔
      (if σ then adjF (fv a) (fv b) else ∼(adjF (fv a) (fv b))))

end Syntax

/-- The variables of the chain: `x`, the four bound variables, `y`. -/
def chainVar : Fin 6 → Fin 2 ⊕ Fin 4 :=
  ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl 1]

/-- `ρ^σ_S(x, y)`: a chain of five steps from `x` to `y`. -/
noncomputable def rhoF (σ : Bool) : L1.Formula (Fin 2) :=
  BoundedFormula.exs (BoundedFormula.relabel (id : Fin 2 ⊕ Fin 4 → Fin 2 ⊕ Fin 4)
    (BoundedFormula.iInf fun i : Fin 5 =>
      edgeF σ (Sum.inl 0) (Sum.inl 1) (chainVar i.castSucc) (chainVar i.succ)))

/-- `φ_R(x, y) = x ≠ y ∧ ρ⁺_S(x, y) ∧ ρ⁻_S(x, y)`. -/
noncomputable def phiR : L1.Formula (Fin 2) :=
  ∼((fv 0).bdEqual (fv 1)) ⊓ rhoF true ⊓ rhoF false

/-! ## Quantifier rank -/

theorem qr_theta {β : Type} (a b : β) : quantifierRank (theta a b) ≤ 1 := by
  simp only [theta, qr_sup, qr_inf, qr_not]
  simp [quantifierRank, colF, adjF, Relations.boundedFormula₁, Relations.boundedFormula₂, Relations.boundedFormula,
    Term.bdEqual, BoundedFormula.iff, qr_inf]

theorem qr_edgeF {β : Type} (σ : Bool) (x y a b : β) : quantifierRank (edgeF σ x y a b) ≤ 1 := by
  have h1 := qr_theta a x
  have h2 := qr_theta b y
  have h3 := qr_theta b x
  have h4 := qr_theta a y
  cases σ <;>
  simp only [edgeF, qr_sup, qr_inf, qr_not, if_true, if_false, Bool.false_eq_true] <;>
  simp [quantifierRank, adjF, Relations.boundedFormula₂, Relations.boundedFormula, Term.bdEqual, h1, h2, h3, h4]

theorem qr_rhoF (σ : Bool) : quantifierRank (rhoF σ) ≤ 5 := by
  rw [rhoF, qr_exs, qr_relabel]
  have := qr_iInf_le (fun i : Fin 5 =>
      edgeF σ (Sum.inl 0) (Sum.inl 1) (chainVar i.castSucc) (chainVar i.succ)) 1
      (fun i => qr_edgeF _ _ _ _ _)
  omega

theorem qr_phiR : quantifierRank phiR ≤ 5 := by
  simp only [phiR, qr_inf, qr_not]
  have h1 := qr_rhoF true
  have h2 := qr_rhoF false
  simp [quantifierRank, Term.bdEqual, h1, h2]

/-! ## Realization -/

section Realize

variable {V : Type z} (G : SimpleGraph V) (S : Set V)

theorem realize_colF {β : Type} {n : ℕ} (t : L1.Term (β ⊕ Fin n)) (v : β → V) (xs : Fin n → V) :
    @BoundedFormula.Realize _ V (expansion G fun (_ : Fin 1) => S) _ _ (colF t) v xs ↔
      @Term.realize _ V (expansion G fun (_ : Fin 1) => S) _ (Sum.elim v xs) t ∈ S :=
  Iff.rfl

theorem realize_adjF {β : Type} {n : ℕ} (t s : L1.Term (β ⊕ Fin n)) (v : β → V) (xs : Fin n → V) :
    @BoundedFormula.Realize _ V (expansion G fun (_ : Fin 1) => S) _ _ (adjF t s) v xs ↔
      G.Adj (@Term.realize _ V (expansion G fun (_ : Fin 1) => S) _ (Sum.elim v xs) t)
        (@Term.realize _ V (expansion G fun (_ : Fin 1) => S) _ (Sum.elim v xs) s) :=
  Iff.rfl

theorem theta_iff {β : Type} (a b : β) (v : β → V) :
    @Formula.Realize _ V (expansion G fun (_ : Fin 1) => S) _ (theta a b) v ↔
      atomicTypes G S (v a) (v b) := by
  let _ := expansion G fun (_ : Fin 1) => S
  have hker : atomicTypes G S (v a) (v b) ↔
      (S ∩ {v a}, S ∩ G.neighborSet (v a)) = (S ∩ {v b}, S ∩ G.neighborSet (v b)) := Iff.rfl
  rw [hker]
  simp only [theta, Formula.Realize, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_iff, BoundedFormula.realize_bdEqual, realize_colF, realize_adjF, fv,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  have hsnoc : ∀ w : V, (Fin.snoc (α := fun _ => V) (default : Fin 0 → V) w 0 : V) = w :=
    fun w => rfl
  simp only [hsnoc]
  constructor
  · rintro (h | ⟨⟨ha, hb⟩, h⟩)
    · rw [h]
    · refine Prod.ext ?_ ?_
      · ext w
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hw, rfl⟩; exact absurd hw ha
        · rintro ⟨hw, rfl⟩; exact absurd hw hb
      · ext w
        simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
        exact ⟨fun hw => ⟨hw.1, (h w hw.1).mp hw.2⟩, fun hw => ⟨hw.1, (h w hw.1).mpr hw.2⟩⟩
  · intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    by_cases ha : v a ∈ S
    · have : v a ∈ S ∩ {v b} := h1 ▸ ⟨ha, rfl⟩
      exact Or.inl this.2
    by_cases hb : v b ∈ S
    · have : v b ∈ S ∩ {v a} := h1.symm ▸ ⟨hb, rfl⟩
      exact Or.inl this.2.symm
    refine Or.inr ⟨⟨ha, hb⟩, fun w hw => ?_⟩
    have := Set.ext_iff.mp h2 w
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at this
    exact ⟨fun h' => (this.mp ⟨hw, h'⟩).2, fun h' => (this.mpr ⟨hw, h'⟩).2⟩

/-- The relation of the steps: adjacency for `σ = true`, non-adjacency
for `σ = false`. -/
def relOf (σ : Bool) : V → V → Prop := fun u w => if σ then G.Adj u w else ¬ G.Adj u w

theorem relOf_symm (σ : Bool) : ∀ a b, relOf G σ a b → relOf G σ b a := by
  intro a b h
  cases σ
  · exact fun h' => h h'.symm
  · exact (h : G.Adj a b).symm

theorem edgeF_iff {β : Type} (σ : Bool) (x y a b : β) (v : β → V) :
    @Formula.Realize _ V (expansion G fun (_ : Fin 1) => S) _ (edgeF σ x y a b) v ↔
      Step (atomicTypes G S) (relOf G σ) (v x) (v y) (v a) (v b) := by
  let _ := expansion G fun (_ : Fin 1) => S
  unfold edgeF Step
  simp only [Formula.realize_inf, Formula.realize_sup, theta_iff]
  cases σ <;>
  simp [relOf, Formula.Realize, BoundedFormula.realize_bdEqual, realize_adjF, fv,
    Term.realize_var, Sum.elim_inl]

theorem rhoF_iff (σ : Bool) (v : Fin 2 → V) :
    @Formula.Realize _ V (expansion G fun (_ : Fin 1) => S) _ (rhoF σ) v ↔
      ∃ zs : Fin 4 → V, ∀ i : Fin 5, Step (atomicTypes G S) (relOf G σ) (v 0) (v 1)
        (chain (v 0) zs (v 1) i.castSucc) (chain (v 0) zs (v 1) i.succ) := by
  let _ := expansion G fun (_ : Fin 1) => S
  unfold rhoF
  rw [BoundedFormula.realize_exs]
  refine exists_congr fun zs => ?_
  rw [BoundedFormula.realize_relabel, BoundedFormula.realize_iInf]
  refine forall_congr' fun i => ?_
  have hw : ∀ j : Fin 6,
      (Sum.elim v (zs ∘ Fin.castAdd 0) ∘ (id : Fin 2 ⊕ Fin 4 → Fin 2 ⊕ Fin 4)) (chainVar j) =
        chain (v 0) zs (v 1) j := by
    intro j; fin_cases j <;> rfl
  have := edgeF_iff G S σ (Sum.inl 0) (Sum.inl 1) (chainVar i.castSucc) (chainVar i.succ)
    (Sum.elim v (zs ∘ Fin.castAdd 0) ∘ (id : Fin 2 ⊕ Fin 4 → Fin 2 ⊕ Fin 4))
  rw [hw, hw] at this
  refine Iff.trans ?_ this
  rw [Formula.Realize]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- Exchanging the two copies of `V`. -/
def swapHom (P : Setoid V) (A : V → V → Prop) (hA : ∀ a b, A a b → A b a) (x y : V) :
    partGraph P A x y →g partGraph P A y x where
  toFun := Sum.swap
  map_rel' := by
    intro s t hst
    rcases s with a | a <;> rcases t with b | b
    · exact absurd hst (not_adj_inl_inl _ _ _)
    · obtain ⟨ha, hb, he⟩ := (adj_inl_inr _ _ _).mp hst
      exact (adj_inr_inl _ _ _).mpr ⟨hb, ha, he.imp Eq.symm (hA a b)⟩
    · obtain ⟨hb, ha, he⟩ := (adj_inr_inl _ _ _).mp hst
      exact (adj_inl_inr _ _ _).mpr ⟨ha, hb, he.imp Eq.symm (hA b a)⟩
    · exact absurd hst (not_adj_inr_inr _ _ _)

theorem withinDist_swap (P : Setoid V) (A : V → V → Prop) (hA : ∀ a b, A a b → A b a)
    {x y : V} (h : WithinDist (partGraph P A x y) 5 (.inl x) (.inr y)) :
    WithinDist (partGraph P A y x) 5 (.inl y) (.inr x) :=
  withinDist_symm' (withinDist_map' (swapHom P A hA x y) h)

theorem phiR_iff (x : Fin 2 → V) :
    @Formula.Realize _ V (expansion G fun (_ : Fin 1) => S) _ phiR x ↔
      (pairRelation G (atomicTypes G S)).Adj (x 0) (x 1) := by
  let _ := expansion G fun (_ : Fin 1) => S
  set P := atomicTypes G S
  have hρ : ∀ σ : Bool, @Formula.Realize _ V (expansion G fun (_ : Fin 1) => S) _ (rhoF σ) x ↔
      WithinDist (partGraph P (relOf G σ) (x 0) (x 1)) 5 (.inl (x 0)) (.inr (x 1)) := fun σ =>
    (rhoF_iff G S σ x).trans (withinDist_iff_chain P _ (relOf_symm G σ) _ _).symm
  have hrel : ∀ u v : V,
      (WithinDist (pairGraph G (part P u) (part P v)) 5 (.inl u) (.inr v) ∧
        WithinDist (coPairGraph G (part P u) (part P v)) 5 (.inl u) (.inr v)) ↔
      (WithinDist (partGraph P (relOf G true) u v) 5 (.inl u) (.inr v) ∧
        WithinDist (partGraph P (relOf G false) u v) 5 (.inl u) (.inr v)) := fun u v => Iff.rfl
  unfold phiR
  simp only [Formula.realize_inf, Formula.realize_not, hρ]
  rw [pairRelation, SimpleGraph.fromRel_adj, hrel, hrel]
  have hne : (@Formula.Realize _ V (expansion G fun (_ : Fin 1) => S) _
      ((fv 0).bdEqual (fv 1)) x) ↔ x 0 = x 1 := Iff.rfl
  rw [hne]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨h0, Or.inl ⟨h1, h2⟩⟩
  · rintro ⟨h0, h | h⟩
    · exact ⟨⟨h0, h.1⟩, h.2⟩
    · exact ⟨⟨h0, withinDist_swap P _ (relOf_symm G true) h.1⟩,
        withinDist_swap P _ (relOf_symm G false) h.2⟩

end Realize

/--
---
conclusion: Lax185574.PairRelationDefinable.exists_formula_pairRelation
---
The formula of the paper. `θ_S(a, b)` says that `a` and `b` have the
same atomic type over `S`, with one quantifier. `e^±_S(a, b; x, y)` says
that `a` and `b` lie in opposite parts among the parts of `x` and `y`
and are equal or adjacent, respectively non-adjacent. `ρ^±_S(x, y)` says
that there are `z₁, …, z₄` such that every consecutive pair of `x, z₁,
…, z₄, y` satisfies `e^±_S`, and `φ_R = x ≠ y ∧ ρ⁺_S ∧ ρ⁻_S`. Such a
chain is a walk of length `5` between opposite copies of `x` and `y` in
`G[X, Y]`, respectively `Ḡ[X, Y]`. Conversely, every walk of length at
most `5` between opposite copies has odd length and can be padded to
length exactly `5` by going back and forth along an edge. The pair
relation is symmetric, as exchanging the two copies maps `G[X, Y]` to
`G[Y, X]`. The rank is `4 + 1 = 5`.

The paper's formula takes the disjunction over walks of length `1`, `3`
and `5`. The padding argument makes the walks of length `5` suffice.
-/
theorem exists_formula_pairRelation :
    ∃ φ : (withColors Language.graph 1).Formula (Fin 2), quantifierRank φ ≤ 5 ∧
      ∀ {V : Type z} (G : SimpleGraph V) (S : Set V) (x : Fin 2 → V),
        @Formula.Realize _ V (expansion G fun _ => S) _ φ x ↔
          (pairRelation G (atomicTypes G S)).Adj (x 0) (x 1) :=
  ⟨phiR, qr_phiR, fun G S x => phiR_iff G S x⟩

end Lax185574Proofs.PairRelationDefinable
