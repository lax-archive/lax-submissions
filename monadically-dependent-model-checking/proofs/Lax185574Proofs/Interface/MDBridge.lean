import Lax185574.MonadicDependence
import Lax710763.MonadicDependence
import Lax185574Proofs.Interface.Formula
import Lax185574Proofs.Interface.OfMathlib

/-!
Graph classes and monadic dependence of `Lax185574.Graphs` and
`Lax185574.MonadicDependence` agree with those of the archive
(`Lax199508.GraphClasses`, `Lax710763.MonadicDependence`).

A graph on `n` vertices is the same data as a simple graph on `Fin n`.
So a graph class of `Lax185574.Graphs` is the same as a graph class of
`Lax199508.GraphClasses`, through `toOld` and `ofOld`, which are inverse
to each other. Neither notion of class asks for closure under
isomorphism, and none is needed.

The two definitions of monadic dependence are equivalent under this
correspondence (`monadicallyDependent_iff`). A transduction of the
archive has a domain formula, an edge formula that must define the
adjacency on every pair of output vertices, and an embedding whose range
is exactly the domain. Forgetting the domain gives the data of
`TransducesAllGraphs`, which constrains distinct vertices only.
Conversely, a fresh color marking the range of the embedding serves as
the domain formula, and the edge formula `ψ(x₀, x₁) ∧ x₀ ≠ x₁` is false
on the diagonal.
-/

namespace Lax185574Proofs.Interface

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.FirstOrderLogic Lax710763.Transductions

/-! ## Graphs and graph classes -/

@[simp]
theorem toSimpleGraph_ofSimpleGraph {n : ℕ} (H : SimpleGraph (Fin n)) :
    (Graph.ofSimpleGraph H).toSimpleGraph = H := rfl

@[simp]
theorem ofSimpleGraph_toSimpleGraph (G : Graph) : Graph.ofSimpleGraph G.toSimpleGraph = G := rfl

/-- A graph class as a graph class of the archive: the simple graphs on
`Fin n` that are members as graphs. -/
def toOld (C : GraphClass) : Lax199508.GraphClasses.GraphClass :=
  fun _ H => Graph.ofSimpleGraph H ∈ C

/-- A graph class of the archive as a graph class: the graphs whose
simple graph is a member. -/
def ofOld (D : Lax199508.GraphClasses.GraphClass) : GraphClass :=
  {G | D G.n G.toSimpleGraph}

theorem toOld_iff (C : GraphClass) (G : Graph) : toOld C G.n G.toSimpleGraph ↔ G ∈ C :=
  Iff.rfl

@[simp]
theorem ofOld_toOld (C : GraphClass) : ofOld (toOld C) = C := rfl

@[simp]
theorem toOld_ofOld (D : Lax199508.GraphClasses.GraphClass) : toOld (ofOld D) = D := rfl

/-! ## Changing the colors of a formula -/

/-- The formula `φ` with each color `d` replaced by `g d`. -/
def Formula.mapColor {K K' : Type} (g : K → K') :
    {k : ℕ} → Lax185574.FirstOrderLogic.Formula K k → Lax185574.FirstOrderLogic.Formula K' k
  | _, .adj i j => .adj i j
  | _, .eq i j => .eq i j
  | _, .not φ => .not (Formula.mapColor g φ)
  | _, .and φ ψ => .and (Formula.mapColor g φ) (Formula.mapColor g ψ)
  | _, .ex φ => .ex (Formula.mapColor g φ)
  | _, .color d i => .color (g d) i

theorem holds_mapColor {K K' : Type} (g : K → K') (G : Graph) (col : K' → Set (Fin G.n))
    {k : ℕ} (φ : Lax185574.FirstOrderLogic.Formula K k) (a : Fin k → Fin G.n) :
    (Formula.mapColor g φ).Holds G col a ↔ φ.Holds G (col ∘ g) a := by
  induction φ with
  | adj i j => exact Iff.rfl
  | eq i j => exact Iff.rfl
  | not φ ih => exact not_congr (ih a)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ a) (ihψ a)
  | ex φ ih => exact exists_congr fun v => ih (Fin.snoc a v)
  | color d i => exact Iff.rfl

/-! ## Monadic dependence -/

theorem comp_vec_two {α β : Type*} (f : α → β) (v : Fin 2 → α) : f ∘ v = ![f (v 0), f (v 1)] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- A transduction of the archive that produces all graphs gives the
data of `TransducesAllGraphs`: the edge formula, translated, and the
same colorings and embeddings. -/
theorem transducesAllGraphs_of_transduces {C : GraphClass}
    (h : Lax710763.GraphTransductions.Transduces (toOld C) Lax710763.GraphClasses.allGraphs) :
    Lax185574.MonadicDependence.TransducesAllGraphs C := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.colors, Formula.ofMathlib (T.rel adj), fun H => ?_⟩
  obtain ⟨n, _, ⟨G', hG', rfl⟩, col, f, -, hrel⟩ :=
    hT H.n H.toSimpleGraph.structure ⟨H.toSimpleGraph, trivial, rfl⟩
  refine ⟨Graph.ofSimpleGraph G', hG', col, f, fun u v _ => ?_⟩
  have h2 : RealizeIn G'.structure col (T.rel adj) (f ∘ ![u, v]) ↔
      RealizeIn G'.structure col (T.rel adj) ![f u, f v] := by
    rw [comp_vec_two]
    rfl
  exact (hrel adj ![u, v]).trans
    (h2.trans (holds_ofMathlib_iff (Graph.ofSimpleGraph G') col (T.rel adj) ![f u, f v]).symm)

/-- The transduction of the archive built from the data of
`TransducesAllGraphs`: the color `k` marks the range of the embedding,
and the edge formula is `ψ(x₀, x₁) ∧ x₀ ≠ x₁`. -/
noncomputable def transductionOf {k : ℕ} (ψ : Lax185574.FirstOrderLogic.Formula (Fin k) 2) :
    Transduction Language.graph Language.graph where
  colors := k + 1
  domain := Formula.toMathlib (.color (Fin.last k) 0)
  rel := @fun r R =>
    match r, R with
    | _, .adj => Formula.toMathlib (.and (Formula.mapColor Fin.castSucc ψ) (.not (.eq 0 1)))

theorem transduces_of_transducesAllGraphs {C : GraphClass}
    (h : Lax185574.MonadicDependence.TransducesAllGraphs C) :
    Lax710763.GraphTransductions.Transduces (toOld C) Lax710763.GraphClasses.allGraphs := by
  obtain ⟨k, ψ, hψ⟩ := h
  refine ⟨transductionOf ψ, fun m N hN => ?_⟩
  obtain ⟨H', -, rfl⟩ := hN
  have hH : ∃ G ∈ C, ∃ (col : Fin k → Set (Fin G.n)) (f : Fin m ↪ Fin G.n),
      ∀ u v : Fin m, u ≠ v → (H'.Adj u v ↔ ψ.Holds G col ![f u, f v]) :=
    hψ (Graph.ofSimpleGraph H')
  obtain ⟨G, hG, col, f, hf⟩ := hH
  let col' : Fin (k + 1) → Set (Fin G.n) := Fin.snoc (α := fun _ => Set (Fin G.n)) col (Set.range f)
  have hcol : col' ∘ Fin.castSucc = col := by
    funext d
    exact Fin.snoc_castSucc (α := fun _ => Set (Fin G.n)) ..
  have hlast : col' (Fin.last k) = Set.range f := Fin.snoc_last (α := fun _ => Set (Fin G.n)) ..
  refine ⟨G.n, G.toSimpleGraph.structure, ⟨G.toSimpleGraph, hG, rfl⟩, col', f, fun x => ?_,
    @fun r R v => ?_⟩
  · change x ∈ Set.range f ↔ RealizeIn G.toSimpleGraph.structure col'
      (Formula.toMathlib (.color (Fin.last k) 0)) ![x]
    rw [realizeIn_toMathlib_iff]
    change x ∈ Set.range f ↔ x ∈ col' (Fin.last k)
    rw [hlast]
  · match r, R with
    | _, .adj =>
      change H'.Adj (v 0) (v 1) ↔ RealizeIn G.toSimpleGraph.structure col'
        (Formula.toMathlib (.and (Formula.mapColor Fin.castSucc ψ) (.not (.eq 0 1)))) (f ∘ v)
      rw [realizeIn_toMathlib_iff]
      change H'.Adj (v 0) (v 1) ↔
        (Formula.mapColor Fin.castSucc ψ).Holds G col' (f ∘ v) ∧ ¬ f (v 0) = f (v 1)
      rw [holds_mapColor, hcol, comp_vec_two]
      by_cases huv : v 0 = v 1
      · rw [huv]
        simp only [SimpleGraph.irrefl, not_true_eq_false, and_false]
      · rw [hf (v 0) (v 1) huv]
        simp only [f.injective.ne huv, not_false_eq_true, and_true]

/-- The two definitions of monadic dependence agree. -/
theorem monadicallyDependent_iff (C : GraphClass) :
    Lax185574.MonadicDependence.MonadicallyDependent C ↔
      Lax710763.MonadicDependence.MonadicallyDependent (toOld C) :=
  not_congr ⟨transduces_of_transducesAllGraphs, transducesAllGraphs_of_transduces⟩

/-- A monadically dependent class is monadically dependent in the sense
of the archive. -/
theorem monadicallyDependent_toOld {C : GraphClass}
    (hC : Lax185574.MonadicDependence.MonadicallyDependent C) :
    Lax710763.MonadicDependence.MonadicallyDependent (toOld C) :=
  (monadicallyDependent_iff C).mp hC

/-- The two definitions of monadic dependence agree, for a class of the
archive. -/
theorem monadicallyDependent_ofOld_iff (D : Lax199508.GraphClasses.GraphClass) :
    Lax185574.MonadicDependence.MonadicallyDependent (ofOld D) ↔
      Lax710763.MonadicDependence.MonadicallyDependent D :=
  monadicallyDependent_iff (ofOld D)

end Lax185574Proofs.Interface
