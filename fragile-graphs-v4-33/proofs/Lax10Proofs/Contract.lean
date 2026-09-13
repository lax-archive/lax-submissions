import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

/-!
# Contract for the fragile graph formalization

This file fixes the local definitions and the public theorem statements for the
formalization of Bonnet--Feghali--Nguyen--Scott--Seymour--Thomasse--Trotignon,
*Graphs without a 3-Connected Subgraph are 4-Colourable*.

The paper-level results are proved in the implementation files importing this
contract.
-/

open Finset

namespace Lax10Proofs

universe u

variable {V : Type u}

/-- A proper coloring of $G$ using the palette $Fin m$. -/
structure KColoring (m : Nat) (G : SimpleGraph V) where
  color : V → Fin m
  valid : ∀ ⦃x y : V⦄, G.Adj x y → color x ≠ color y

/-- $G$ is colorable with at most $m$ colors. -/
def KColorable (m : Nat) (G : SimpleGraph V) : Prop :=
  Nonempty (KColoring m G)

namespace KColoring

/-- Convert the local coloring wrapper to mathlib's coloring API. -/
def toMathlib {m : Nat} {G : SimpleGraph V} (c : KColoring m G) :
    G.Coloring (Fin m) :=
  SimpleGraph.Coloring.mk c.color (by
    intro x y h
    exact c.valid h)

/-- Convert mathlib's coloring API to the local coloring wrapper. -/
def ofMathlib {m : Nat} {G : SimpleGraph V} (c : G.Coloring (Fin m)) :
    KColoring m G where
  color := c
  valid := by
    intro x y h
    exact c.valid h

/-- Restrict a coloring to an induced subgraph. -/
def restrict {m : Nat} {G : SimpleGraph V} (c : KColoring m G) (s : Set V) :
    KColoring m (G.induce s) where
  color x := c.color x
  valid := by
    intro x y h
    exact c.valid h

@[simp]
theorem restrict_color {m : Nat} {G : SimpleGraph V} (c : KColoring m G)
    (s : Set V) (x : s) :
    (c.restrict s).color x = c.color x :=
  rfl

/-- Relabel colors by a permutation of the palette. -/
def relabel {m : Nat} {G : SimpleGraph V} (c : KColoring m G)
    (σ : Equiv.Perm (Fin m)) : KColoring m G where
  color x := σ (c.color x)
  valid := by
    intro x y h hsame
    exact c.valid h (σ.injective hsame)

@[simp]
theorem relabel_color {m : Nat} {G : SimpleGraph V} (c : KColoring m G)
    (σ : Equiv.Perm (Fin m)) (x : V) :
    (c.relabel σ).color x = σ (c.color x) :=
  rfl

end KColoring

theorem kColorable_iff_mathlib_colorable {m : Nat} {G : SimpleGraph V} :
    KColorable m G ↔ G.Colorable m := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.toMathlib⟩
  · rintro ⟨c⟩
    exact ⟨KColoring.ofMathlib c⟩

/-- The induced graph obtained after deleting the vertices in $S$. -/
abbrev deleteVertices (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v : V // v ∉ S} :=
  G.induce {v : V | v ∉ S}

/-- $S$ separates two remaining vertices after deletion. -/
def IsVertexSeparator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ x y : {v : V // v ∉ S}, ¬ (deleteVertices G S).Reachable x y

/--
3-connected in the sense used by the paper: at least 4 vertices and no
vertex cutset of size at most two.
-/
def ThreeConnected [Finite V] (G : SimpleGraph V) : Prop :=
  4 ≤ Nat.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → ¬ IsVertexSeparator G S

/--
An $m$-fragile graph: every 3-connected subgraph is $(m - 1)$-colorable.

The subgraph is represented by mathlib's $SimpleGraph.Subgraph$; its vertex type
is $H.verts$, and $H.coe$ is the corresponding simple graph.
-/
def MFragile [Finite V] (m : Nat) (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ThreeConnected H.coe → KColorable (m - 1) H.coe

/-- A graph with no 3-connected subgraph. -/
def HasNoThreeConnectedSubgraph [Finite V] (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ¬ ThreeConnected H.coe

/-- The 4 coloring-extension conditions from Theorem 3. -/
structure T3Conditions [DecidableEq V] (m : Nat) (G : SimpleGraph V) : Prop where
  c1 : ∀ ⦃x y : V⦄, ¬ G.Adj x y →
    ∃ c : KColoring m G, c.color x = c.color y
  c2 : ∀ ⦃x y : V⦄, x ≠ y →
    ∃ c : KColoring m G, c.color x ≠ c.color y
  c3 : ∀ ⦃x y z : V⦄, x ≠ y → x ≠ z → y ≠ z →
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m))
  c4 : ∀ ⦃x y z : V⦄, x ≠ y → x ≠ z → y ≠ z →
    ¬ (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) →
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2

end Lax10Proofs
