import Lax185574Proofs.TreeAlgo.Basic
import Lax185574.ConstructionSequences

/-!
The semantic core of lem:merge-lift. A merge recolors the vertices of
color `Q` to `P` and keeps all resolved pairs. More generally, a recoloring
along any map `f` of colors keeps all distances, and an atom holds after
the recoloring exactly when some atom with the old colors holds before and
is mapped to it by `f`. So the new root label is the image of the old one
under `f`, and the extensions are lifted recursively, as in the proof of
lem:merge-lift. The merge is the recoloring along
`Y ↦ if Y = Q then P else Y`.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ConstructionSequences
open Lax3.DistFO (rhoMinus rhoPlus)

/-- Recoloring an atom along the map `f` of colors. -/
def recolorAtom (f : ℕ → ℕ) {ℓ : ℕ} : DistFO ℓ → DistFO ℓ
  | .color Y i => .color (f Y) i
  | .distColorLt r Y i => .distColorLt r (f Y) i
  | φ => φ

/-- Recoloring a tree along `f`. -/
def recolorNode (f : ℕ → ℕ) : {q ℓ : ℕ} → Node q ℓ → Node q ℓ
  | 0, _, t => (Node.atoms t).image (recolorAtom f)
  | _ + 1, _, t => ((Node.atoms t).image (recolorAtom f),
      (Node.exts t).image fun e => (e.1, recolorNode f e.2))

/-- The merge map of colors. -/
def mergeColor (P Q : ℕ) (Y : ℕ) : ℕ := if Y = Q then P else Y

/-- The core of the merge lift. -/
def mergeNode (P Q : ℕ) {q ℓ : ℕ} (t : Node q ℓ) : Node q ℓ := recolorNode (mergeColor P Q) t

variable {V : Type*}

/-- The partial graph with colors mapped along `f`. -/
def recolorGraph (G : PartialGraph V) (f : ℕ → ℕ) : PartialGraph V :=
  { G with color := fun v => f (G.color v) }

theorem merge_eq_recolor (G : PartialGraph V) (P Q : ℕ) :
    merge G P Q = recolorGraph G (mergeColor P Q) := rfl

theorem atoms_recolorNode (f : ℕ → ℕ) {q ℓ : ℕ} (t : Node q ℓ) :
    Node.atoms (recolorNode f t) = (Node.atoms t).image (recolorAtom f) := by
  cases q <;> rfl

theorem isAtom_recolorAtom (f : ℕ → ℕ) {ℓ : ℕ} (φ : DistFO ℓ) :
    IsAtom (recolorAtom f φ) ↔ IsAtom φ := by
  cases φ <;> simp [recolorAtom, IsAtom]

theorem drank_recolorAtom_iff (f : ℕ → ℕ) {k q ℓ : ℕ} {φ : DistFO ℓ} (h : IsAtom φ) :
    DRank k q (recolorAtom f φ) ↔ DRank k q φ := by
  cases φ with
  | eq => exact ⟨fun _ => .eq _ _, fun _ => .eq _ _⟩
  | edge => exact ⟨fun _ => .edge _ _, fun _ => .edge _ _⟩
  | nonEdge => exact ⟨fun _ => .nonEdge _ _, fun _ => .nonEdge _ _⟩
  | color => exact ⟨fun _ => .color _ _, fun _ => .color _ _⟩
  | distLe => exact Iff.rfl
  | distColorLt r Y i =>
    constructor
    · intro hr; cases hr with | distColorLt _ _ _ h => exact .distColorLt _ _ _ h
    · intro hr; cases hr with | distColorLt _ _ _ h => exact .distColorLt _ _ _ h
  | not => exact absurd h id
  | and => exact absurd h id
  | exLocal => exact absurd h id

/-- An atom holds after the recoloring exactly when an atom that is mapped
to it holds before. -/
theorem sat_recolor_atom (G : PartialGraph V) (f : ℕ → ℕ) {ℓ : ℕ} (u : Fin ℓ → V)
    (ψ : DistFO ℓ) (hψ : IsAtom ψ) :
    Sat (recolorGraph G f) u ψ ↔ ∃ φ, IsAtom φ ∧ recolorAtom f φ = ψ ∧ Sat G u φ := by
  cases ψ with
  | color Y i =>
    constructor
    · intro h
      exact ⟨.color (G.color (u i)) i, trivial, by simpa [recolorAtom, Sat, recolorGraph] using h, rfl⟩
    · rintro ⟨φ, hφ, hφψ, hs⟩
      cases φ <;> simp_all [recolorAtom, IsAtom, Sat, recolorGraph]
  | distColorLt r Y i =>
    constructor
    · rintro ⟨v, hv, hd⟩
      exact ⟨.distColorLt r (G.color v) i, trivial,
        by simpa [recolorAtom, recolorGraph] using hv, v, rfl, hd⟩
    · rintro ⟨φ, hφ, hφψ, hs⟩
      cases φ <;> simp_all [recolorAtom, IsAtom, Sat, recolorGraph]
      obtain ⟨-, rfl, rfl⟩ := hφψ
      obtain ⟨v, rfl, hd⟩ := hs
      exact ⟨v, rfl, hd⟩
  | not => exact absurd hψ id
  | and => exact absurd hψ id
  | exLocal => exact absurd hψ id
  | eq i j | edge i j | nonEdge i j | distLe r i j =>
    constructor
    · intro h; exact ⟨_, hψ, rfl, h⟩
    · rintro ⟨φ, hφ, hφψ, hs⟩
      cases φ <;> simp_all [recolorAtom, IsAtom, Sat, recolorGraph, PartialGraph.resolved]

/-- **Correctness of the recoloring lift.** -/
theorem recolorNode_node [Finite V] (G : PartialGraph V) (f : ℕ → ℕ) :
    ∀ (q k : ℕ) {ℓ : ℕ} (u : Fin ℓ → V),
      recolorNode f (node G k q u) = node (recolorGraph G f) k q u := by
  have hatoms : ∀ (q k : ℕ) {ℓ : ℕ} (u : Fin ℓ → V),
      (Node.atoms (node G k q u)).image (recolorAtom f) =
        Node.atoms (node (recolorGraph G f) k q u) := by
    intro q k ℓ u
    ext ψ
    simp only [Finset.mem_image, mem_atoms_node]
    constructor
    · rintro ⟨φ, ⟨hat, hr, hs⟩, rfl⟩
      refine ⟨(isAtom_recolorAtom f φ).2 hat, (drank_recolorAtom_iff f hat).2 hr, ?_⟩
      exact (sat_recolor_atom G f u _ ((isAtom_recolorAtom f φ).2 hat)).2 ⟨φ, hat, rfl, hs⟩
    · rintro ⟨hat, hr, hs⟩
      obtain ⟨φ, hφ, rfl, hs'⟩ := (sat_recolor_atom G f u ψ hat).1 hs
      exact ⟨φ, ⟨hφ, (drank_recolorAtom_iff f hφ).1 hr, hs'⟩, rfl⟩
  intro q
  induction q with
  | zero => intro k ℓ u; exact hatoms 0 k u
  | succ q ih =>
    intro k ℓ u
    refine Node.ext_succ (hatoms (q + 1) k u) ?_
    ext e
    show e ∈ (Node.exts (node G k (q + 1) u)).image (fun e => (e.1, recolorNode f e.2)) ↔ _
    rw [Finset.mem_image, mem_exts_node]
    constructor
    · rintro ⟨e', he', rfl⟩
      obtain ⟨i, b, hb, rfl⟩ := (mem_exts_node G k q u e').1 he'
      exact ⟨i, b, hb, by rw [ih]⟩
    · rintro ⟨i, b, hb, rfl⟩
      exact ⟨_, (mem_exts_node G k q u _).2 ⟨i, b, hb, rfl⟩, by rw [ih]⟩

/-- **lem:merge-lift, semantic form.** -/
theorem mergeNode_node [Finite V] (G : PartialGraph V) (P Q k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → V) :
    mergeNode P Q (node G k q u) = node (merge G P Q) k q u :=
  recolorNode_node G _ q k u

/-- **Size of the merge lift.** The recoloring does not increase the
number of nodes. -/
theorem count_recolorNode_le (f : ℕ → ℕ) : ∀ {q ℓ : ℕ} (t : Node q ℓ),
    Node.count (recolorNode f t) ≤ Node.count t
  | 0, _, _ => le_rfl
  | q + 1, ℓ, t => by
    show 1 + ∑ e ∈ (Node.exts t).image (fun e : Fin ℓ × Node q (ℓ + 1) => (e.1, recolorNode f e.2)),
        Node.count e.2 ≤
      1 + ∑ e ∈ Node.exts t, Node.count e.2
    exact Nat.add_le_add_left ((sum_image_le_nat (Node.exts t)
      (fun e : Fin ℓ × Node q (ℓ + 1) => (e.1, recolorNode f e.2)) (fun e => Node.count e.2)).trans
      (Finset.sum_le_sum fun (e : Fin ℓ × Node q (ℓ + 1)) _ => count_recolorNode_le f e.2)) 1

theorem card_atoms_recolorNode_le (f : ℕ → ℕ) {q ℓ : ℕ} (t : Node q ℓ) :
    (Node.atoms (recolorNode f t)).card ≤ (Node.atoms t).card := by
  rw [atoms_recolorNode]; exact Finset.card_image_le

end Lax185574Proofs.TreeAlgo
