import Lax185574.IndependenceProperty
import Lax185574Proofs.Interface.IndependenceProperty

/-!
Monadic dependence through the independence property.

A formula `φ(x, y)` with the independence property on a class yields a
transduction of every graph: the vertices of a graph `H` on `m` vertices
are the elements `aᵢ`, and two of them are adjacent when they have a
common `φ`-neighbor among the elements `b_{ij}` with `ij ∈ E(H)`.
Conversely, a transduction of all graphs produces every incidence graph
between `{0, …, m-1}` and its subsets, and its edge formula has the
independence property.

The inclusion of color blocks is adapted from `Lib/TransductionCalculus`,
which adapts it from lax-710763, file
`proofs/Lax710763Proofs/TransductionCalculus.lean`.
-/

namespace Lax185574Proofs.IndependenceProperty

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.GraphClasses Lax710763.MonadicDependence
open Lax710763.Transductions Lax185574Proofs.Interface.Old

/-! ## Syntax -/

/-- Include the first block of colors into a sum of two color blocks. -/
def firstColorHom (c₁ c₂ : ℕ) : colorLanguage c₁ →ᴸ colorLanguage (c₁ + c₂) where
  onFunction := fun {_} f => isEmptyElim (α := Empty) f
  onRelation := fun {_} R => match R with
    | .color i => .color (i.castAdd c₂)

/-- Regard a formula with `c₁` colors as a formula with `c₁ + c₂` colors. -/
def liftColors {c₁ : ℕ} (c₂ : ℕ) {α : Type*}
    (φ : (withColors Language.graph c₁).Formula α) :
    (withColors Language.graph (c₁ + c₂)).Formula α :=
  (LHom.sumMap (LHom.id Language.graph) (firstColorHom c₁ c₂)).onFormula φ

theorem realizeIn_liftColors {c₁ c₂ n : ℕ} (G : SimpleGraph (Fin n))
    (colors₁ : Fin c₁ → Set (Fin n)) (colors₂ : Fin c₂ → Set (Fin n))
    {α : Type*} (φ : (withColors Language.graph c₁).Formula α) (v : α → Fin n) :
    RealizeIn G.structure (Fin.append colors₁ colors₂) (liftColors c₂ φ) v ↔
      RealizeIn G.structure colors₁ φ v := by
  let _ := G.structure
  let _ := colorStructure (Fin.append colors₁ colors₂)
  let _ := colorStructure colors₁
  have : (firstColorHom c₁ c₂).IsExpansionOn (Fin n) :=
    ⟨fun f => isEmptyElim (α := Empty) f, fun R x => by
      cases R with
      | color i =>
        show (x 0 ∈ Fin.append colors₁ colors₂ (Fin.castAdd c₂ i)) = (x 0 ∈ colors₁ i)
        exact congrFun (Fin.append_left colors₁ colors₂ i) (x 0)⟩
  exact LHom.realize_onFormula (LHom.sumMap (LHom.id Language.graph) (firstColorHom c₁ c₂)) φ

/-- The atomic formula stating that the variable `x` has color `i`. -/
def colorAtom {c : ℕ} {α : Type*} (i : Fin c) (x : α) :
    (withColors Language.graph c).Formula α :=
  Relations.formula₁ (Sum.inr (ColorRel.color i) : (withColors Language.graph c).Relations 1)
    (Term.var x)

theorem realizeIn_colorAtom {c n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin c → Set (Fin n))
    {α : Type*} (i : Fin c) (x : α) (v : α → Fin n) :
    RealizeIn G.structure colors (colorAtom i x) v ↔ v x ∈ colors i := by
  unfold RealizeIn colorAtom
  let _ := G.structure
  let _ := colorStructure colors
  exact Iff.rfl

theorem realizeIn_inf {c n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin c → Set (Fin n))
    {α : Type*} (ψ χ : (withColors Language.graph c).Formula α) (w : α → Fin n) :
    RealizeIn G.structure colors (ψ ⊓ χ) w ↔
      RealizeIn G.structure colors ψ w ∧ RealizeIn G.structure colors χ w := by
  unfold RealizeIn
  let _ := G.structure
  let _ := colorStructure colors
  exact Formula.realize_inf

theorem realizeIn_relabel {c n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin c → Set (Fin n))
    {α β : Type*} (ψ : (withColors Language.graph c).Formula α) (g : α → β) (w : β → Fin n) :
    RealizeIn G.structure colors (ψ.relabel g) w ↔ RealizeIn G.structure colors ψ (w ∘ g) := by
  unfold RealizeIn
  let _ := G.structure
  let _ := colorStructure colors
  exact Formula.realize_relabel

/-- The formula `φ(x_j, z)` with `x_j` among two free variables and `z`
an extra variable. -/
def atVar {L : Language} (φ : L.Formula (Fin 1 ⊕ Fin 1)) (j : Fin 2) :
    L.Formula (Fin 2 ⊕ Fin 1) :=
  φ.relabel (Sum.elim (fun _ => Sum.inl j) (fun _ => Sum.inr 0))

/-- The edge formula of the transduction built from `φ`: two distinct
elements with a common `φ`-neighbor of the last color. -/
noncomputable def commonNeighborFormula {k : ℕ} (φ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)) :
    (withColors Language.graph (k + 2)).Formula (Fin 2) :=
  ((Term.var 0).equal (Term.var 1)).not ⊓
    Formula.iExs (Fin 1)
      (colorAtom (Fin.natAdd k 1) (Sum.inr 0) ⊓ atVar (liftColors 2 φ) 0 ⊓
        atVar (liftColors 2 φ) 1)

theorem realizeIn_commonNeighborFormula {k n : ℕ} (G : SimpleGraph (Fin n))
    (colors : Fin k → Set (Fin n)) (A B : Set (Fin n))
    (φ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)) (v : Fin 2 → Fin n) :
    RealizeIn G.structure (Fin.append colors ![A, B]) (commonNeighborFormula φ) v ↔
      v 0 ≠ v 1 ∧ ∃ z ∈ B,
        RealizeIn G.structure colors φ (Sum.elim (fun _ => v 0) (fun _ => z)) ∧
        RealizeIn G.structure colors φ (Sum.elim (fun _ => v 1) (fun _ => z)) := by
  have hφ : ∀ (j : Fin 2) (w : Fin 2 ⊕ Fin 1 → Fin n),
      RealizeIn G.structure (Fin.append colors ![A, B]) (atVar (liftColors 2 φ) j) w ↔
        RealizeIn G.structure colors φ (Sum.elim (fun _ => w (Sum.inl j)) (fun _ => w (Sum.inr 0))) := by
    intro j w
    rw [← realizeIn_liftColors G colors (![A, B])]
    unfold RealizeIn atVar
    let _ := G.structure
    let _ := colorStructure (Fin.append colors ![A, B])
    rw [Formula.realize_relabel]
    apply iff_of_eq
    congr 1
    funext x
    rcases x with x | x <;> rfl
  have hB : ∀ w : Fin 2 ⊕ Fin 1 → Fin n,
      RealizeIn G.structure (Fin.append colors ![A, B]) (colorAtom (Fin.natAdd k 1) (Sum.inr 0)) w ↔
        w (Sum.inr 0) ∈ B := by
    intro w
    rw [realizeIn_colorAtom]
    have : Fin.append colors ![A, B] (Fin.natAdd k 1) = B := by
      rw [Fin.append_right]; rfl
    rw [this]
  have hex : RealizeIn G.structure (Fin.append colors ![A, B])
      (Formula.iExs (Fin 1)
        (colorAtom (Fin.natAdd k 1) (Sum.inr 0) ⊓ atVar (liftColors 2 φ) 0 ⊓
          atVar (liftColors 2 φ) 1)) v ↔
      ∃ i : Fin 1 → Fin n, RealizeIn G.structure (Fin.append colors ![A, B])
        (colorAtom (Fin.natAdd k 1) (Sum.inr 0) ⊓ atVar (liftColors 2 φ) 0 ⊓
          atVar (liftColors 2 φ) 1) (Sum.elim v i) := by
    unfold RealizeIn
    let _ := G.structure
    let _ := colorStructure (Fin.append colors ![A, B])
    exact Formula.realize_iExs
  have hne : RealizeIn G.structure (Fin.append colors ![A, B])
      ((Term.var 0).equal (Term.var 1)).not v ↔ v 0 ≠ v 1 := by
    unfold RealizeIn
    let _ := G.structure
    let _ := colorStructure (Fin.append colors ![A, B])
    simp only [Formula.realize_not, Formula.realize_equal, Term.realize_var]
  unfold commonNeighborFormula
  rw [realizeIn_inf, hne, hex]
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨i, hi⟩
    rw [realizeIn_inf, realizeIn_inf, hB, hφ, hφ] at hi
    exact ⟨i 0, hi.1.1, hi.1.2, hi.2⟩
  · rintro ⟨z, hz, h0, h1⟩
    refine ⟨fun _ => z, ?_⟩
    rw [realizeIn_inf, realizeIn_inf, hB, hφ, hφ]
    exact ⟨⟨hz, h0⟩, h1⟩

/-! ## Independence property gives a transduction of all graphs -/

/-- The transduction built from a formula `φ(x, y)` with `k` colors. -/
noncomputable def ipTransduction {k : ℕ}
    (φ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)) :
    Transduction Language.graph Language.graph where
  colors := k + 2
  domain := colorAtom (Fin.natAdd k 0) 0
  rel := fun {r} R => match r, R with
    | 2, .adj => commonNeighborFormula φ

theorem single_eq {n : ℕ} (u : Fin 1 → Fin n) : u = fun _ => u 0 := by
  funext x; rw [Subsingleton.elim x 0]

/-- A class on which some `φ(x, y)` has the independence property
transduces all graphs. -/
theorem transduces_of_hasIP (C : GraphClass) {k : ℕ}
    (φ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)) (h : HasIP C φ) :
    Lax710763.GraphTransductions.Transduces C allGraphs := by
  classical
  refine ⟨ipTransduction φ, ?_⟩
  rintro m N ⟨H, -, rfl⟩
  obtain ⟨n, G, hG, colors, a, b, hab⟩ := h m
  have hab' : ∀ (i : Fin m) (J : Finset (Fin m)),
      RealizeIn G.structure colors φ (Sum.elim (fun _ => a i 0) (fun _ => b J 0)) ↔ i ∈ J := by
    intro i J
    rw [← single_eq (a i), ← single_eq (b J)]
    exact hab i J
  have hinj : Function.Injective fun i => a i 0 := by
    intro i j hij
    have h1 := (hab' i {i}).mpr (Finset.mem_singleton_self i)
    simp only at hij
    rw [hij, hab'] at h1
    exact (Finset.mem_singleton.mp h1).symm
  let f : Fin m ↪ Fin n := ⟨fun i => a i 0, hinj⟩
  let Bset : Set (Fin n) := {z | ∃ i j, H.Adj i j ∧ z = b {i, j} 0}
  refine ⟨n, G.structure, ⟨G, hG, rfl⟩, Fin.append colors ![Set.range f, Bset], f, ?_, ?_⟩
  · intro x
    show _ ↔ RealizeIn G.structure _ (colorAtom (Fin.natAdd k 0) 0) ![x]
    rw [realizeIn_colorAtom]
    have : Fin.append colors ![Set.range f, Bset] (Fin.natAdd k 0) = Set.range f := by
      rw [Fin.append_right]; rfl
    rw [this]
    rfl
  · intro r R v
    match r, R with
    | 2, .adj =>
      show H.Adj (v 0) (v 1) ↔ RealizeIn G.structure _ (commonNeighborFormula φ) (f ∘ v)
      rw [realizeIn_commonNeighborFormula]
      simp only [Function.comp_apply]
      constructor
      · intro hadj
        refine ⟨fun he => hadj.ne (f.injective he), b {v 0, v 1} 0, ⟨v 0, v 1, hadj, rfl⟩, ?_, ?_⟩
        · exact (hab' _ _).mpr (by simp)
        · exact (hab' _ _).mpr (by simp)
      · rintro ⟨hne, z, ⟨i, j, hij, rfl⟩, h0, h1⟩
        have hne' : v 0 ≠ v 1 := fun he => hne (by rw [he])
        have h0' : v 0 = i ∨ v 0 = j := by simpa using (hab' _ _).mp h0
        have h1' : v 1 = i ∨ v 1 = j := by simpa using (hab' _ _).mp h1
        rcases h0' with h0' | h0' <;> rcases h1' with h1' | h1'
        · exact absurd (h0'.trans h1'.symm) hne'
        · rw [h0', h1']; exact hij
        · rw [h0', h1']; exact hij.symm
        · exact absurd (h0'.trans h1'.symm) hne'

/-! ## A transduction of all graphs gives the independence property -/

/-- The incidence graph between the elements of `{0, …, m-1}` and its
subsets. -/
def incidenceGraph (m : ℕ) : SimpleGraph (Fin m ⊕ Finset (Fin m)) where
  Adj u w := (∃ i J, u = Sum.inl i ∧ w = Sum.inr J ∧ i ∈ J) ∨
    (∃ i J, w = Sum.inl i ∧ u = Sum.inr J ∧ i ∈ J)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨i, J, rfl, h, -⟩ | ⟨i, J, rfl, h, -⟩ <;> cases h⟩

theorem incidenceGraph_adj (m : ℕ) (i : Fin m) (J : Finset (Fin m)) :
    (incidenceGraph m).Adj (Sum.inl i) (Sum.inr J) ↔ i ∈ J := by
  constructor
  · rintro (⟨i', J', h1, h2, h⟩ | ⟨i', J', h1, h2, h⟩)
    · cases h1; cases h2; exact h
    · cases h1
  · intro h; exact Or.inl ⟨i, J, rfl, rfl, h⟩

/-- The edge formula of a transduction as a formula `φ(x, y)`. -/
def edgeFormulaOf {c : ℕ} (ψ : (withColors Language.graph c).Formula (Fin 2)) :
    (withColors Language.graph c).Formula (Fin 1 ⊕ Fin 1) :=
  ψ.relabel ![Sum.inl 0, Sum.inr 0]

/-- A class that transduces all graphs has a formula `φ(x, y)` with the
independence property. -/
theorem hasIP_of_transduces (C : GraphClass) (h : Lax710763.GraphTransductions.Transduces C allGraphs) :
    ∃ (k : ℕ) (φ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)), HasIP C φ := by
  classical
  obtain ⟨T, hT⟩ := h
  refine ⟨T.colors, edgeFormulaOf (T.rel Language.adj), fun m => ?_⟩
  let e := Fintype.equivFin (Fin m ⊕ Finset (Fin m))
  let H : SimpleGraph (Fin (Fintype.card (Fin m ⊕ Finset (Fin m)))) :=
    (incidenceGraph m).comap e.symm
  obtain ⟨n, M, ⟨G, hG, rfl⟩, colors, f, -, hrel⟩ := hT _ H.structure ⟨H, trivial, rfl⟩
  refine ⟨n, G, hG, colors, fun i _ => f (e (Sum.inl i)), fun J _ => f (e (Sum.inr J)), ?_⟩
  intro i J
  have := (hrel Language.adj ![e (Sum.inl i), e (Sum.inr J)]).symm
  have hv : (Sum.elim (fun _ : Fin 1 => f (e (Sum.inl i))) (fun _ : Fin 1 => f (e (Sum.inr J))) ∘
      ![Sum.inl 0, Sum.inr 0]) = f ∘ ![e (Sum.inl i), e (Sum.inr J)] := by
    funext x
    match x with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  unfold edgeFormulaOf
  refine (realizeIn_relabel G colors _ _ _).trans ?_
  refine (iff_of_eq (congrArg (RealizeIn G.structure colors (T.rel Language.adj)) hv)).trans ?_
  refine this.trans ?_
  show (incidenceGraph m).Adj (e.symm (e (Sum.inl i))) (e.symm (e (Sum.inr J))) ↔ i ∈ J
  simp only [Equiv.symm_apply_apply]
  exact incidenceGraph_adj m i J

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem monadicallyDependent_iff_forall_not_hasIP_old (C : GraphClass) :
    MonadicallyDependent C ↔
      ∀ (k : ℕ) (φ : (withColors Language.graph k).Formula (Fin 1 ⊕ Fin 1)),
        ¬ HasIP C φ := by
  constructor
  · intro hC k φ hφ
    exact hC (transduces_of_hasIP C φ hφ)
  · intro h hT
    obtain ⟨k, φ, hφ⟩ := hasIP_of_transduces C hT
    exact h k φ hφ

end Lax185574Proofs.IndependenceProperty

namespace Lax185574Proofs.IndependenceProperty

open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.MonadicDependence
open Lax185574.IndependenceProperty Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.IndependenceProperty.monadicallyDependent_iff_forall_not_hasIP
---
If a formula `φ(x, y)` has the independence property on `C`, then for a
graph `H` on `m` vertices take the elements `a₀, …, a_{m-1}` and color
the set `A` of them and the set `B` of the elements `b_{ij}` for the
edges `ij` of `H`. Two distinct elements of `A` are adjacent in `H` if
and only if they have a common `φ`-neighbor in `B`. So `C` transduces
all graphs. Conversely, a transduction of all graphs produces the
incidence graph between `{0, …, m-1}` and its subsets, so its edge
formula has the independence property.

The argument is carried out for the graph classes of the archive and
mathlib formulas, and transferred to the graph classes used
here and the translation
of formulas.
-/
theorem monadicallyDependent_iff_forall_not_hasIP (C : GraphClass) :
    MonadicallyDependent C ↔ ∀ (k : ℕ) (φ : Formula (Fin k) (1 + 1)), ¬ HasIP C φ :=
  (monadicallyDependent_iff C).trans
    ((monadicallyDependent_iff_forall_not_hasIP_old (toOld C)).trans
      (forall_not_hasIP_toOld_iff C))

end Lax185574Proofs.IndependenceProperty
