import Lax185574Proofs.TreeAlgo.Restriction

/-!
The semantic core of lem:shift. The rank shift of a tree of positive
depth takes an extension with guard `0` and restricts it to the old
positions. In the tree of a nonempty tuple `ā`, every extension with guard
`0` is `tree_{k+1,q}(ā b)` for some `b`, and its restriction is
`tree_{k+1,q}(ā)`. So all of them give the same result, and there is at
least one, for `b = a₀`. The function `shiftNode` returns the unique
member of the set of these restrictions. A program may take the first
extension with guard `0` instead, which gives the same tree.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The only member of a finite set with one member, and nothing
otherwise. -/
def Finset.theOnly {α : Type*} (s : Finset α) : Option α :=
  Quot.liftOn s.val (fun l => match l with | [x] => some x | _ => none) (by
    intro a b (h : a.Perm b)
    rcases a with _ | ⟨x, _ | ⟨x', a⟩⟩ <;> rcases b with _ | ⟨y, _ | ⟨y', b⟩⟩ <;>
      first
      | rfl
      | (have := h.length_eq; simp at this; done)
      | simp [List.singleton_perm_singleton.1 h])

theorem Finset.mem_of_theOnly {α : Type*} {s : Finset α} {x : α} (h : Finset.theOnly s = some x) :
    x ∈ s := by
  rcases s with ⟨⟨l⟩, hl⟩
  rcases l with _ | ⟨y, _ | ⟨y', l⟩⟩
  · exact absurd h (by simp [Finset.theOnly, Quot.liftOn])
  · simp only [Finset.theOnly, Quot.liftOn, Option.some.injEq] at h
    subst h
    exact Multiset.mem_singleton_self _
  · exact absurd h (by simp [Finset.theOnly, Quot.liftOn])

theorem Finset.theOnly_singleton {α : Type*} (x : α) : Finset.theOnly {x} = some x := rfl

/-- The empty node, the default value. -/
def Node.empty : {q ℓ : ℕ} → Node q ℓ
  | 0, _ => (∅ : Finset (DistFO _))
  | _ + 1, _ => ((∅ : Finset (DistFO _)), ∅)

/-- The partial inverse of `Fin.castSucc`: the old positions. -/
def initPInv (ℓ : ℕ) : Fin (ℓ + 1) → Option (Fin ℓ) := Fin.lastCases none some

theorem isPInv_initPInv (ℓ : ℕ) : IsPInv (Fin.castSucc : Fin ℓ → Fin (ℓ + 1)) (initPInv ℓ) := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [initPInv, (Fin.castSucc_ne_last j)]
  · simp [initPInv, eq_comm]

/-- The candidates of the rank shift: the restrictions of the extensions
with guard `0` to the old positions. -/
def shiftCandidates {q ℓ : ℕ} (t : Node (q + 1) ℓ) : Finset (Node q ℓ) :=
  ((Node.exts t).filter (fun e => e.1.val = 0)).image fun e => restrictNode (initPInv ℓ) e.2

/-- The rank shift of a node. -/
def shiftNode {q ℓ : ℕ} (t : Node (q + 1) ℓ) : Node q ℓ :=
  (Finset.theOnly (shiftCandidates t)).getD Node.empty

variable {V : Type*}

theorem shiftCandidates_node [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (u : Fin ℓ → V) : shiftCandidates (node G k (q + 1) u) = {node G (k + 1) q u} := by
  ext μ
  simp only [shiftCandidates, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨e, ⟨he, -⟩, rfl⟩
    obtain ⟨i, b, -, rfl⟩ := (mem_exts_node G k q u e).1 he
    rw [restrictNode_node G q (k + 1) (isPInv_initPInv ℓ), Fin.snoc_comp_castSucc]
  · rintro rfl
    let i0 : Fin ℓ := ⟨0, hℓ⟩
    refine ⟨(i0, node G (k + 1) q (Fin.snoc u (u i0))),
      ⟨(mem_exts_node G k q u _).2 ⟨i0, u i0, ⟨.nil, Nat.zero_le _⟩, rfl⟩, rfl⟩, ?_⟩
    rw [restrictNode_node G q (k + 1) (isPInv_initPInv ℓ), Fin.snoc_comp_castSucc]

/-- **Correctness of the rank shift.** For a nonempty tuple, the shift of
`tree_{k,q+1}(u)` is `tree_{k+1,q}(u)`. -/
theorem shiftNode_node [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (u : Fin ℓ → V) : shiftNode (node G k (q + 1) u) = node G (k + 1) q u := by
  rw [shiftNode, shiftCandidates_node G k q hℓ u, Finset.theOnly_singleton]
  rfl

theorem count_empty : {q ℓ : ℕ} → Node.count (Node.empty : Node q ℓ) = 1
  | 0, _ => rfl
  | _ + 1, _ => rfl

/-- **Size of the rank shift.** The shift has at most as many nodes as the
input. -/
theorem count_shiftNode_le {q ℓ : ℕ} (t : Node (q + 1) ℓ) :
    Node.count (shiftNode t) ≤ Node.count t := by
  unfold shiftNode
  cases h : Finset.theOnly (shiftCandidates t) with
  | none => simp only [Option.getD_none, count_empty]; exact Node.one_le_count t
  | some μ =>
    simp only [Option.getD_some]
    have hmem : μ ∈ shiftCandidates t := Finset.mem_of_theOnly h
    simp only [shiftCandidates, Finset.mem_image, Finset.mem_filter] at hmem
    obtain ⟨e, ⟨he, -⟩, rfl⟩ := hmem
    exact (count_restrictNode_le _ _).trans (Node.count_child_lt t he).le

/-! ### Rank shift of type trees -/

/-- The rank shift of a type tree of positive depth, and the identity at
depth `0`. -/
def shiftTree (τ : TypeTree) : TypeTree :=
  match τ with
  | ⟨k, q + 1, ℓ, t⟩ => ⟨k + 1, q, ℓ, shiftNode t⟩
  | τ => τ

/-- **lem:shift, semantic form.** -/
theorem shiftTree_tree [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (u : Fin ℓ → V) : shiftTree (tree G k (q + 1) u) = tree G (k + 1) q u := by
  simp only [shiftTree, tree, shiftNode_node G k q hℓ u]

/-- Iterated rank shift: `i ≤ q` shifts of `tree_{k,q}(u)` give
`tree_{k+i,q−i}(u)`. -/
theorem shiftTree_iterate_tree [Finite V] (G : PartialGraph V) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (u : Fin ℓ → V) : ∀ (i k q : ℕ), i ≤ q →
      shiftTree^[i] (tree G k q u) = tree G (k + i) (q - i) u
  | 0, k, q, _ => by simp
  | i + 1, k, q, hi => by
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Function.iterate_succ_apply, shiftTree_tree G k q hℓ u,
      shiftTree_iterate_tree G hℓ u i (k + 1) q (by omega)]
    rw [show k + 1 + i = k + (i + 1) by omega, show q - i = q + 1 - (i + 1) by omega]

end Lax185574Proofs.TreeAlgo
