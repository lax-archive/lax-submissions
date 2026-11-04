import Lax185574.TypeTrees
import Lax185574.ConstructionSequences
import Mathlib.Tactic
import Lax185574Proofs.Legacy

/-!
The type trees of an initial partial graph (proof of thm:mc,
model-checking.tex, "Initially, for t = 1, ...").

In a partial graph without resolved pairs every ball is a singleton.
So every guard admits only the vertex of the guarded tuple itself, and
the type tree of a constant tuple is determined by its rank, its arity
and the color of its vertex. The function `initNode` gives this tree.
The injectivity of the coloring of an initial partial graph is not
needed.
-/

namespace Lax185574Proofs.MC

open Lax185574.PartialGraphs Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.GaifmanGraph Lax185574.TypeTrees Lax185574.WordEncoding
open Lax3.DistFO (rhoMinus rhoPlus)

open Classical in
/-- The atoms of distance rank `(k, q)` satisfied by a constant tuple of
arity `ℓ` whose vertex has color `c`, in a partial graph without
resolved pairs. -/
noncomputable def initAtoms (k q ℓ c : ℕ) : Finset (DistFO ℓ) :=
  (Finset.univ.image fun p : Fin ℓ × Fin ℓ => DistFO.eq p.1 p.2) ∪
  (Finset.univ.image fun i : Fin ℓ => DistFO.color c i) ∪
  ((Finset.range (rhoMinus k q + 1) ×ˢ (Finset.univ : Finset (Fin ℓ × Fin ℓ))).image
      fun p => DistFO.distLe p.1 p.2.1 p.2.2) ∪
  ((Finset.Icc 1 (rhoPlus k q) ×ˢ (Finset.univ : Finset (Fin ℓ))).image
      fun p => DistFO.distColorLt p.1 c p.2)

open Classical in
/-- The root of the type tree of rank `(k, q)` of a constant tuple of
arity `ℓ` whose vertex has color `c`, in a partial graph without
resolved pairs. Every extension repeats the vertex. -/
noncomputable def initNode : (k q ℓ c : ℕ) → Node q ℓ
  | k, 0, ℓ, c => (initAtoms k 0 ℓ c : Finset (DistFO ℓ))
  | k, q + 1, ℓ, c =>
      ((initAtoms k (q + 1) ℓ c : Finset (DistFO ℓ)),
       (Finset.univ.image fun i : Fin ℓ => (i, initNode (k + 1) q (ℓ + 1) c)))

variable {V : Type*}

theorem finsetOf_coe {α : Type*} (F : Finset α) : finsetOf (F : Set α) = F := by
  unfold finsetOf
  rw [dif_pos F.finite_toSet]
  simp

theorem walk_bot {u v : V} (p : (⊥ : SimpleGraph V).Walk u v) : u = v ∧ p.length = 0 := by
  cases p with
  | nil => exact ⟨rfl, rfl⟩
  | cons h _ => exact absurd h (by simp)

theorem withinDist_bot {r : ℕ} {u v : V} : WithinDist (⊥ : SimpleGraph V) r u v ↔ u = v := by
  constructor
  · rintro ⟨p, -⟩; exact (walk_bot p).1
  · rintro rfl; exact ⟨SimpleGraph.Walk.nil, by simp⟩

theorem withinDistLt_bot {r : ℕ} {u v : V} :
    WithinDistLt (⊥ : SimpleGraph V) r u v ↔ u = v ∧ 1 ≤ r := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨h, h0⟩ := walk_bot p
    exact ⟨h, by omega⟩
  · rintro ⟨rfl, hr⟩; exact ⟨SimpleGraph.Walk.nil, by simp; omega⟩

theorem drank_distLe_iff {k q ℓ r : ℕ} {i j : Fin ℓ} :
    DRank k q (DistFO.distLe r i j) ↔ r ≤ rhoMinus k q := by
  constructor
  · intro h; cases h; assumption
  · exact DRank.distLe r i j

theorem drank_distColorLt_iff {k q ℓ r Y : ℕ} {i : Fin ℓ} :
    DRank k q (DistFO.distColorLt r Y i) ↔ r ≤ rhoPlus k q := by
  constructor
  · intro h; cases h; assumption
  · exact DRank.distColorLt r Y i

/-- The atoms of a constant tuple in a partial graph without resolved
pairs. -/
theorem atp_unresolved (G : PartialGraph V) (hE : G.edge = ⊥) (hN : G.nonEdge = ⊥) (a : V)
    (k q ℓ : ℕ) :
    atp G k q (fun _ : Fin ℓ => a) = ↑(initAtoms k q ℓ (G.color a)) := by
  have hR : G.resolved = ⊥ := by simp [PartialGraph.resolved, hE, hN]
  ext φ
  simp only [atp, Set.mem_ofPred_eq, Finset.mem_coe, initAtoms, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_product, Finset.mem_range,
    Finset.mem_Icc, Prod.exists]
  cases φ with
  | eq i j =>
      have := DRank.eq (k := k) (q := q) i j
      simp [DistFO.IsAtom, Sat, this]
  | edge i j => simp [DistFO.IsAtom, Sat, hE]
  | nonEdge i j => simp [DistFO.IsAtom, Sat, hN]
  | color Y i =>
      have := DRank.color (k := k) (q := q) Y i
      simp [DistFO.IsAtom, Sat, this, eq_comm]
  | distLe r i j =>
      simp [DistFO.IsAtom, Sat, drank_distLe_iff, hR, withinDist_bot]
  | distColorLt r Y i =>
      simp only [DistFO.IsAtom, Sat, drank_distColorLt_iff, hR, withinDistLt_bot]
      simp only [true_and, reduceCtorEq, exists_false, false_or, or_false, and_false,
        DistFO.distColorLt.injEq]
      constructor
      · rintro ⟨h, v, hv, rfl, h1⟩
        exact ⟨r, i, ⟨⟨h1, h⟩, trivial⟩, rfl, hv, rfl⟩
      · rintro ⟨r', i', ⟨⟨h1, h⟩, -⟩, rfl, rfl, rfl⟩
        exact ⟨h, a, rfl, rfl, h1⟩
  | not φ => simp [DistFO.IsAtom]
  | and φ ψ => simp [DistFO.IsAtom]
  | exLocal i s φ => simp [DistFO.IsAtom]

theorem snoc_const (a : V) (ℓ : ℕ) :
    (Fin.snoc (fun _ : Fin ℓ => a) a : Fin (ℓ + 1) → V) = fun _ => a := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Fin.snoc]

/-- **The trees of an initial partial graph.** In a partial graph
without resolved pairs, the root of the type tree of a constant tuple is
`initNode`. -/
theorem node_unresolved (G : PartialGraph V) (hE : G.edge = ⊥) (hN : G.nonEdge = ⊥) (a : V) :
    ∀ (q k ℓ : ℕ), node G k q (fun _ : Fin ℓ => a) = initNode k q ℓ (G.color a)
  | 0, k, ℓ => by
      rw [node, initNode, atp_unresolved G hE hN, finsetOf_coe]
  | q + 1, k, ℓ => by
      have hR : G.resolved = ⊥ := by simp [PartialGraph.resolved, hE, hN]
      rw [node, initNode, atp_unresolved G hE hN, finsetOf_coe]
      congr 1
      classical
      have hS : {e : Fin ℓ × Node q (ℓ + 1) | ∃ (i : Fin ℓ) (b : V),
          WithinDist G.resolved (rhoPlus (k + 1) q) a b ∧
          e = (i, node G (k + 1) q (Fin.snoc (fun _ : Fin ℓ => a) b))} =
          ↑(Finset.univ.image fun i : Fin ℓ => (i, initNode (k + 1) q (ℓ + 1) (G.color a))) := by
        ext e
        simp only [Set.mem_ofPred_eq, hR, withinDist_bot, Finset.coe_image, Finset.coe_univ,
          Set.image_univ, Set.mem_range]
        constructor
        · rintro ⟨i, b, rfl, rfl⟩
          exact ⟨i, by rw [snoc_const, node_unresolved G hE hN a q (k + 1) (ℓ + 1)]⟩
        · rintro ⟨i, rfl⟩
          exact ⟨i, a, rfl, by rw [snoc_const, node_unresolved G hE hN a q (k + 1) (ℓ + 1)]⟩
      rw [hS, finsetOf_coe]

/-- The type tree of a vertex in a partial graph without resolved
pairs. -/
theorem tree_unresolved (G : PartialGraph V) (hE : G.edge = ⊥) (hN : G.nonEdge = ⊥) (a : V)
    (k q : ℕ) : tree G k q ![a] = ⟨k, q, 1, initNode k q 1 (G.color a)⟩ := by
  have : (![a] : Fin 1 → V) = fun _ => a := by funext j; fin_cases j; rfl
  rw [tree, this, node_unresolved G hE hN a q k 1]

end Lax185574Proofs.MC
