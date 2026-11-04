import Lax185574Proofs.Words.Read
import Lax185574.TypeTrees

/-!
The entries of the word of a type tree. Every entry is at most the
length of the word, at most a constant of the rank and the arity (a
radius, an index, an opcode), or the color of a vertex. Colors occur
only in the atoms `Y(xᵢ)` and `dist(xᵢ, Y) < r`, which hold only if `Y`
is a color of some vertex.
-/

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574Proofs.Words
open Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus rhoPlus)

theorem mem_frames {ws : List (List ℕ)} {e : ℕ} (he : e ∈ frames ws) :
    ∃ u ∈ ws, e = u.length ∨ e ∈ u := by
  simp only [frames, List.mem_flatten, List.mem_map] at he
  obtain ⟨l, ⟨u, hu, rfl⟩, hel⟩ := he
  rcases List.mem_cons.1 hel with h | h
  · exact ⟨u, hu, Or.inl h⟩
  · exact ⟨u, hu, Or.inr h⟩

theorem length_le_frames {ws : List (List ℕ)} {u : List ℕ} (hu : u ∈ ws) :
    u.length + 1 ≤ (frames ws).length := by
  induction ws with
  | nil => simp at hu
  | cons a ws ih =>
    simp only [frames, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at ih ⊢
    rcases List.mem_cons.1 hu with rfl | h
    · omega
    · have := ih h; omega

/-- Entries of the word of a finite set. -/
theorem mem_toWord_finset {α : Type*} [WordEncoding α] (S : Finset α) {e : ℕ}
    (he : e ∈ toWord S) :
    e ≤ (toWord S).length ∨ ∃ a ∈ S, (toWord a).length < (toWord S).length ∧ e ∈ toWord a := by
  change e ∈ toWord (Finset.words S) at he
  change e ≤ (toWord (Finset.words S)).length ∨
    ∃ a ∈ S, (toWord a).length < (toWord (Finset.words S)).length ∧ e ∈ toWord a
  rw [toWord_words] at he ⊢
  rcases List.mem_cons.1 he with rfl | he
  · left
    simp only [List.length_cons]
    have : (Finset.words S).length ≤ (frames (Finset.words S)).length := by
      clear he
      generalize Finset.words S = ws
      induction ws with
      | nil => simp [frames]
      | cons a ws ih => simp only [frames, List.map_cons, List.flatten_cons, List.length_append,
          List.length_cons] at ih ⊢; omega
    omega
  · obtain ⟨u, hu, h⟩ := mem_frames he
    have hl := length_le_frames hu
    have hu' : u ∈ S.image toWord := (Finset.mem_sort _).1 hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu'
    rcases h with rfl | h
    · left; simp only [List.length_cons]; omega
    · right; exact ⟨a, ha, by simp only [List.length_cons]; omega, h⟩

theorem mem_of_mem_finsetOf {α : Type*} {S : Set α} {a : α} (h : a ∈ finsetOf S) : a ∈ S := by
  unfold finsetOf at h
  split_ifs at h with hf
  · exact (Set.Finite.mem_toFinset hf).1 h
  · simp at h

/-- The constant of the entries of atoms: radii, indices and opcodes. -/
def atomCst (k q ℓ : ℕ) : ℕ := rhoPlus k q + rhoMinus k q + ℓ + 8

/-- Entries of a true atom. -/
theorem atom_entry {V : Type*} {G : PartialGraph V} {k q ℓ : ℕ} {a : Fin ℓ → V} {φ : DistFO ℓ}
    (hφ : φ ∈ atp G k q a) {e : ℕ} (he : e ∈ toWord φ) :
    e ≤ atomCst k q ℓ ∨ ∃ v, e = G.color v := by
  obtain ⟨hA, hR, hS⟩ := hφ
  have hi : ∀ i : Fin ℓ, (i : ℕ) ≤ atomCst k q ℓ := fun i => by
    have := i.2; simp only [atomCst]; omega
  rw [Lax185574Proofs.Legacy.encode_eq_code] at he
  cases φ with
  | eq i j =>
    simp only [code, List.mem_cons, List.not_mem_nil, or_false] at he
    left; rcases he with rfl | rfl | rfl
    · simp [atomCst]
    · exact hi i
    · exact hi j
  | edge i j =>
    simp only [code, List.mem_cons, List.not_mem_nil, or_false] at he
    left; rcases he with rfl | rfl | rfl
    · simp only [atomCst]; omega
    · exact hi i
    · exact hi j
  | nonEdge i j =>
    simp only [code, List.mem_cons, List.not_mem_nil, or_false] at he
    left; rcases he with rfl | rfl | rfl
    · simp only [atomCst]; omega
    · exact hi i
    · exact hi j
  | color Y i =>
    simp only [code, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · left; simp [atomCst]
    · right; exact ⟨a i, hS.symm⟩
    · left; exact hi i
  | distLe r i j =>
    simp only [code, List.mem_cons, List.not_mem_nil, or_false] at he
    cases hR with
    | distLe _ _ _ hr =>
      rcases he with rfl | rfl | rfl | rfl
      · left; simp [atomCst]
      · left; simp only [atomCst]; omega
      · left; exact hi i
      · left; exact hi j
  | distColorLt r Y i =>
    simp only [code, List.mem_cons, List.not_mem_nil, or_false] at he
    cases hR with
    | distColorLt _ _ _ hr =>
      rcases he with rfl | rfl | rfl | rfl
      · left; simp [atomCst]
      · left; simp only [atomCst]; omega
      · right; obtain ⟨v, hv, -⟩ := hS; exact ⟨v, hv.symm⟩
      · left; exact hi i
  | not φ => exact absurd hA id
  | and φ ψ => exact absurd hA id
  | exLocal i s φ => exact absurd hA id

/-- The constant of the entries of a root of depth `q`. -/
def nodeCst : ℕ → ℕ → ℕ → ℕ
  | k, 0, ℓ => atomCst k 0 ℓ
  | k, q + 1, ℓ => atomCst k (q + 1) ℓ + nodeCst (k + 1) q (ℓ + 1)

/-- Entries of the atoms of a root. -/
theorem atoms_entry {V : Type*} {G : PartialGraph V} {k q ℓ : ℕ} {a : Fin ℓ → V} {e : ℕ}
    (he : e ∈ toWord (finsetOf (atp G k q a))) :
    e ≤ (toWord (finsetOf (atp G k q a))).length ∨ e ≤ atomCst k q ℓ ∨ ∃ v, e = G.color v := by
  rcases mem_toWord_finset _ he with h | ⟨φ, hφ, -, he'⟩
  · exact Or.inl h
  · exact Or.inr (atom_entry (mem_of_mem_finsetOf hφ) he')

/-- **Entries of a root.** -/
theorem node_entry {V : Type*} (G : PartialGraph V) :
    ∀ (q k ℓ : ℕ) (a : Fin ℓ → V) (e : ℕ), e ∈ toWord (node G k q a) →
      e ≤ (toWord (node G k q a)).length ∨ e ≤ nodeCst k q ℓ ∨ ∃ v, e = G.color v
  | 0, k, ℓ, a, e, he => by
    exact atoms_entry (G := G) (k := k) (q := 0) (a := a) he
  | q + 1, k, ℓ, a, e, he => by
    have hw : toWord (node G k (q + 1) a) =
        toWord (finsetOf (atp G k (q + 1) a)) ++
          toWord (finsetOf {e : Fin ℓ × Node q (ℓ + 1) | ∃ (i : Fin ℓ) (b : V),
            WithinDist G.resolved (rhoPlus (k + 1) q) (a i) b ∧
            e = (i, node G (k + 1) q (Fin.snoc a b))}) := rfl
    rw [hw] at he ⊢
    simp only [List.length_append]
    rcases List.mem_append.1 he with h | h
    · rcases atoms_entry h with h' | h' | h'
      · left; omega
      · right; left; simp only [nodeCst]; omega
      · right; right; exact h'
    · rcases mem_toWord_finset _ h with h' | ⟨x, hx, hxl, hex⟩
      · left; omega
      · obtain ⟨i, b, -, rfl⟩ := mem_of_mem_finsetOf hx
        have hpair : toWord (i, node G (k + 1) q (Fin.snoc a b)) =
            [(i : ℕ)] ++ toWord (node G (k + 1) q (Fin.snoc a b)) := rfl
        rw [hpair] at hex hxl
        rcases List.mem_append.1 hex with h1 | h1
        · right; left
          simp only [List.mem_singleton] at h1
          subst h1
          have := i.2; simp only [nodeCst, atomCst]; omega
        · rcases node_entry G q (k + 1) (ℓ + 1) _ e h1 with h2 | h2 | h2
          · left; simp only [List.length_append, List.length_singleton] at hxl; omega
          · right; left; simp only [nodeCst]; omega
          · right; right; exact h2

/-- **Entries of a type tree.** Every entry of the word of
`tree_{k,q}(a)` is at most its length, at most `k + q + nodeCst k q ℓ`,
or a color. -/
theorem tree_entry {V : Type*} (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) {e : ℕ}
    (he : e ∈ toWord (tree G k q a)) :
    e ≤ (toWord (tree G k q a)).length ∨ e ≤ k + q + nodeCst k q ℓ ∨ ∃ v, e = G.color v := by
  have hw : toWord (tree G k q a) = [k, q, ℓ] ++ toWord (node G k q a) := rfl
  rw [hw] at he ⊢
  simp only [List.length_append, List.length_cons, List.length_nil]
  rcases List.mem_append.1 he with h | h
  · right; left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have : ℓ ≤ nodeCst k q ℓ := by cases q <;> simp [nodeCst, atomCst] <;> omega
    rcases h with rfl | rfl | rfl <;> omega
  · rcases node_entry G q k ℓ a e h with h' | h' | h'
    · left; omega
    · right; left; omega
    · right; right; exact h'

end Lax185574Proofs.MC
