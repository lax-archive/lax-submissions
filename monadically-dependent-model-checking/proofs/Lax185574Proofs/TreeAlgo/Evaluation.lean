import Lax185574Proofs.TreeAlgo.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
The semantic core of lem:eval. The function `evalNode` decides a formula
on a type tree: an atom is looked up in the root label, Boolean
connectives are evaluated directly, and `∃ y (dist(xᵢ, y) ≤ s ∧ ψ)` holds if
some extension with guard `i` satisfies `ψ`. For the type tree of a tuple
and a formula of the rank of the tree, this is satisfaction of the formula
by the tuple, as in the proof of lem:eval. The cost `evalCost` counts the
node visits of the recursion, at most `|φ| · (number of nodes)`.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

/-- Evaluation of a formula on a type tree. -/
def evalNode : {q ℓ : ℕ} → Node q ℓ → DistFO ℓ → Bool
  | _, _, t, .not φ => !evalNode t φ
  | _, _, t, .and φ ψ => evalNode t φ && evalNode t ψ
  | q, _, t, .exLocal i _ φ =>
      match q, t with
      | 0, _ => false
      | _ + 1, t => decide (∃ e ∈ Node.exts t, e.1 = i ∧ evalNode e.2 φ = true)
  | _, _, t, φ => decide (φ ∈ Node.atoms t)

/-- The number of node visits of `evalNode`: one per visit of a
subformula at a node. -/
def evalCost : {q ℓ : ℕ} → Node q ℓ → DistFO ℓ → ℕ
  | _, _, t, .not φ => 1 + evalCost t φ
  | _, _, t, .and φ ψ => 1 + evalCost t φ + evalCost t ψ
  | q, _, t, .exLocal i _ φ =>
      match q, t with
      | 0, _ => 1
      | _ + 1, t => 1 + ∑ e ∈ (Node.exts t).filter (·.1 = i), evalCost e.2 φ
  | _, _, _, _ => 1

variable {V : Type*}

theorem evalNode_atom {q ℓ : ℕ} (t : Node q ℓ) (φ : DistFO ℓ) (h : IsAtom φ) :
    evalNode t φ = decide (φ ∈ Node.atoms t) := by
  cases φ <;> first | exact absurd h id | rfl

theorem evalNode_node_atom [Finite V] (G : PartialGraph V) {k q ℓ : ℕ} {φ : DistFO ℓ}
    (hat : IsAtom φ) (hφ : DRank k q φ) (u : Fin ℓ → V) :
    evalNode (node G k q u) φ = true ↔ Sat G u φ := by
  rw [evalNode_atom _ _ hat, decide_eq_true_iff, mem_atoms_node]
  exact ⟨fun h => h.2.2, fun h => ⟨hat, hφ, h⟩⟩

/-- **Correctness of evaluation.** On the type tree of `u`, `evalNode`
decides the formulas of the rank of the tree. -/
theorem evalNode_node [Finite V] (G : PartialGraph V) {k q ℓ : ℕ} {φ : DistFO ℓ}
    (hφ : DRank k q φ) (u : Fin ℓ → V) : evalNode (node G k q u) φ = true ↔ Sat G u φ := by
  induction hφ with
  | eq i j => exact evalNode_node_atom (φ := .eq i j) G trivial (.eq i j) u
  | edge i j => exact evalNode_node_atom (φ := .edge i j) G trivial (.edge i j) u
  | nonEdge i j => exact evalNode_node_atom (φ := .nonEdge i j) G trivial (.nonEdge i j) u
  | color Y i => exact evalNode_node_atom (φ := .color Y i) G trivial (.color Y i) u
  | distLe r i j h => exact evalNode_node_atom (φ := .distLe r i j) G trivial (.distLe r i j h) u
  | distColorLt r Y i h =>
    exact evalNode_node_atom (φ := .distColorLt r Y i) G trivial (.distColorLt r Y i h) u
  | not _ ih => simp [evalNode, ← ih u, Sat]
  | and _ _ ih ih' => simp [evalNode, ← ih u, ← ih' u, Sat]
  | @exLocal k q ℓ i φ _ ih =>
    simp only [evalNode, Sat, decide_eq_true_iff]
    constructor
    · rintro ⟨e, he, rfl, hev⟩
      obtain ⟨i, b, hb, rfl⟩ := (mem_exts_node G k q u e).1 he
      exact ⟨b, hb, (ih _).1 hev⟩
    · rintro ⟨b, hb, hs⟩
      exact ⟨_, (mem_exts_node G k q u _).2 ⟨i, b, hb, rfl⟩, rfl, (ih _).2 hs⟩

/-- The code of a formula is not empty. -/
theorem one_le_code_length {ℓ : ℕ} (φ : DistFO ℓ) : 1 ≤ (code φ).length := by
  cases φ <;> simp [code]

/-- **Cost of evaluation.** The number of node visits is at most the
length of the formula times the number of nodes of the tree. -/
theorem evalCost_le : {q ℓ : ℕ} → (t : Node q ℓ) → (φ : DistFO ℓ) →
    evalCost t φ ≤ (code φ).length * Node.count t
  | _, _, t, .not φ => by
    have := evalCost_le t φ
    simp only [evalCost, code, List.length_cons]
    have := Node.one_le_count t
    nlinarith
  | _, _, t, .and φ ψ => by
    have h1 := evalCost_le t φ
    have h2 := evalCost_le t ψ
    simp only [evalCost, code, List.length_cons, List.length_append]
    have := Node.one_le_count t
    nlinarith
  | 0, _, t, .exLocal i s φ => by
    simp [evalCost, code, Node.count]
  | q + 1, _, t, .exLocal i s φ => by
    simp only [evalCost, code, List.length_cons]
    have hsum : ∑ e ∈ (Node.exts t).filter (·.1 = i), evalCost e.2 φ ≤
        (code φ).length * (Node.count t - 1) := by
      calc _ ≤ ∑ e ∈ (Node.exts t).filter (·.1 = i), (code φ).length * Node.count e.2 :=
            Finset.sum_le_sum fun e _ => evalCost_le e.2 φ
        _ ≤ ∑ e ∈ Node.exts t, (code φ).length * Node.count e.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Nat.zero_le _)
        _ = (code φ).length * (Node.count t - 1) := by
            rw [← Finset.mul_sum]
            simp [Node.count, Node.exts_def]
    have := Node.one_le_count t
    have h1 : (code φ).length * (Node.count t - 1) ≤ (code φ).length * Node.count t :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith
  | _, _, t, .eq _ _ | _, _, t, .edge _ _ | _, _, t, .nonEdge _ _ | _, _, t, .color _ _
  | _, _, t, .distLe _ _ _ | _, _, t, .distColorLt _ _ _ => by
    have := Node.one_le_count t
    simp [evalCost, code]
    omega

end Lax185574Proofs.TreeAlgo
