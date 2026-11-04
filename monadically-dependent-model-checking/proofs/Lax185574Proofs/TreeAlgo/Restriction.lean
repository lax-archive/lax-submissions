import Lax185574Proofs.TreeAlgo.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The semantic core of lem:restrict. Restricting a type tree to a subtuple is
given by a partial inverse `g` of the map `f` of positions, which sends a
position of the tuple to its position in the subtuple, if any. The root
keeps the atoms all of whose positions survive, renamed along `g`, and an
extension survives if its guard does, and is restricted along `g`
extended by the new last position. This is one pass over the tree, as in
the proof of lem:restrict. The restriction to a list `J` of distinct
positions uses the partial inverse `i ↦ J.finIdxOf? i`.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The atoms of a root label that survive the partial inverse `g`,
renamed along it. -/
def pullAtoms {ℓ p : ℕ} (g : Fin ℓ → Option (Fin p)) (A : Finset (DistFO ℓ)) :
    Finset (DistFO p) :=
  A.biUnion fun φ => (pullAtom g φ).toFinset

/-- Restriction of a tree along the partial inverse `g` of a map of
positions. -/
def restrictNode : {q ℓ p : ℕ} → (Fin ℓ → Option (Fin p)) → Node q ℓ → Node q p
  | 0, _, _, g, t => pullAtoms g (Node.atoms t)
  | _ + 1, _, _, g, t =>
      (pullAtoms g (Node.atoms t),
       (Node.exts t).biUnion fun e =>
         ((g e.1).map fun j => (j, restrictNode (liftPInv g) e.2)).toFinset)

theorem atoms_restrictNode {q ℓ p : ℕ} (g : Fin ℓ → Option (Fin p)) (t : Node q ℓ) :
    Node.atoms (restrictNode g t) = pullAtoms g (Node.atoms t) := by
  cases q <;> rfl

theorem mem_exts_restrictNode {q ℓ p : ℕ} (g : Fin ℓ → Option (Fin p)) (t : Node (q + 1) ℓ)
    (e' : Fin p × Node q (p + 1)) :
    e' ∈ Node.exts (restrictNode g t) ↔
      ∃ e ∈ Node.exts t, ∃ j, g e.1 = some j ∧ e' = (j, restrictNode (liftPInv g) e.2) := by
  show e' ∈ (Node.exts t).biUnion (fun e =>
    ((g e.1).map fun j => (j, restrictNode (liftPInv g) e.2)).toFinset) ↔ _
  simp only [Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff]
  constructor
  · rintro ⟨e, he, j, hj, rfl⟩
    exact ⟨e, he, j, hj, rfl⟩
  · rintro ⟨e, he, j, hj, rfl⟩
    exact ⟨e, he, j, hj, rfl⟩

variable {V : Type*}

theorem mem_pullAtoms_node [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ p : ℕ}
    {f : Fin p → Fin ℓ} {g : Fin ℓ → Option (Fin p)} (hfg : IsPInv f g) (u : Fin ℓ → V)
    (ψ : DistFO p) :
    ψ ∈ pullAtoms g (Node.atoms (node G k q u)) ↔ IsAtom ψ ∧ DRank k q ψ ∧ Sat G (u ∘ f) ψ := by
  simp only [pullAtoms, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def,
    pullAtom_eq_some hfg, mem_atoms_node]
  constructor
  · rintro ⟨φ, ⟨-, hr, hs⟩, hat, rfl⟩
    exact ⟨hat, (drank_rename_atom_iff f hat).1 hr, (sat_rename G f u ψ).1 hs⟩
  · rintro ⟨hat, hr, hs⟩
    exact ⟨rename f ψ, ⟨(isAtom_rename f).2 hat, drank_rename f hr, (sat_rename G f u ψ).2 hs⟩,
      hat, rfl⟩

/-- **Correctness of restriction.** Restricting the type tree of `u` along
a partial inverse of `f` gives the type tree of `u ∘ f`. -/
theorem restrictNode_node [Finite V] (G : PartialGraph V) :
    ∀ (q k : ℕ) {ℓ p : ℕ} {f : Fin p → Fin ℓ} {g : Fin ℓ → Option (Fin p)}, IsPInv f g →
      ∀ u : Fin ℓ → V, restrictNode g (node G k q u) = node G k q (u ∘ f)
  | 0, k, ℓ, p, f, g, hfg, u => by
    show pullAtoms g (Node.atoms (node G k 0 u)) = Node.atoms (node G k 0 (u ∘ f))
    ext ψ
    rw [mem_pullAtoms_node G k 0 hfg, mem_atoms_node]
  | q + 1, k, ℓ, p, f, g, hfg, u => by
    refine Node.ext_succ ?_ ?_
    · rw [atoms_restrictNode]
      ext ψ
      rw [mem_pullAtoms_node G k (q + 1) hfg, mem_atoms_node]
    · ext e'
      rw [mem_exts_restrictNode, mem_exts_node]
      constructor
      · rintro ⟨e, he, j, hj, rfl⟩
        obtain ⟨i, b, hb, rfl⟩ := (mem_exts_node G k q u e).1 he
        have hfj : f j = i := (hfg i j).1 hj
        refine ⟨j, b, by simpa [hfj] using hb, ?_⟩
        rw [restrictNode_node G q (k + 1) hfg.lift, snoc_comp_liftMap]
      · rintro ⟨j, b, hb, rfl⟩
        refine ⟨(f j, node G (k + 1) q (Fin.snoc u b)),
          (mem_exts_node G k q u _).2 ⟨f j, b, hb, rfl⟩, j, (hfg (f j) j).2 rfl, ?_⟩
        rw [restrictNode_node G q (k + 1) hfg.lift, snoc_comp_liftMap]

/-- **Size of the restriction.** Restriction does not increase the number
of nodes. -/
theorem count_restrictNode_le : ∀ {q ℓ p : ℕ} (g : Fin ℓ → Option (Fin p)) (t : Node q ℓ),
    Node.count (restrictNode g t) ≤ Node.count t
  | 0, _, _, _, _ => le_rfl
  | q + 1, ℓ, p, g, t => by
    show 1 + ∑ e ∈ Node.exts (restrictNode g t), Node.count e.2 ≤
      1 + ∑ e ∈ Node.exts t, Node.count e.2
    have : ∑ e ∈ Node.exts (restrictNode g t), Node.count e.2 ≤
        ∑ e ∈ Node.exts t, ∑ e' ∈ ((g e.1).map fun j => (j, restrictNode (liftPInv g) e.2)).toFinset,
          Node.count e'.2 :=
      sum_biUnion_le_nat _ _ _
    refine Nat.add_le_add_left (this.trans (Finset.sum_le_sum fun e _ => ?_)) 1
    cases g e.1 with
    | none => simp
    | some j => simpa using count_restrictNode_le (liftPInv g) e.2

/-- Restriction does not increase the number of atoms of the root. -/
theorem card_atoms_restrictNode_le {q ℓ p : ℕ} (g : Fin ℓ → Option (Fin p)) (t : Node q ℓ) :
    (Node.atoms (restrictNode g t)).card ≤ (Node.atoms t).card := by
  rw [atoms_restrictNode, pullAtoms]
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ φ ∈ Node.atoms t, ((pullAtom g φ).toFinset).card ≤ ∑ _φ ∈ Node.atoms t, 1 :=
        Finset.sum_le_sum fun φ _ => by cases pullAtom g φ <;> simp
    _ = _ := by simp

/-! ### Restriction to a list of positions -/

/-- The partial inverse of `J.get`: the position of `i` in `J`. -/
def listPInv {ℓ : ℕ} (J : List (Fin ℓ)) : Fin ℓ → Option (Fin J.length) := fun i => J.finIdxOf? i

theorem isPInv_listPInv {ℓ : ℕ} {J : List (Fin ℓ)} (hJ : J.Nodup) : IsPInv J.get (listPInv J) := by
  intro i j
  simp only [listPInv, List.finIdxOf?_eq_some_iff, List.get_eq_getElem]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun j' hj' hj'i => ?_⟩
    have := (List.Nodup.getElem_inj_iff hJ).1 (hj'i.trans h.symm)
    exact absurd this (Nat.ne_of_lt hj')

/-- The restriction `τ ↾ J` of a type tree to the list `J` of positions. -/
def restrictTree (k q ℓ : ℕ) (t : Node q ℓ) (J : List (Fin ℓ)) : TypeTree :=
  ⟨k, q, J.length, restrictNode (listPInv J) t⟩

/-- **lem:restrict, semantic form.** -/
theorem restrictTree_tree [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → V)
    (J : List (Fin ℓ)) (hJ : J.Nodup) :
    restrictTree k q ℓ (node G k q u) J = tree G k q (fun i => u (J.get i)) := by
  simp only [restrictTree, tree, restrictNode_node G q k (isPInv_listPInv hJ)]
  rfl

end Lax185574Proofs.TreeAlgo
