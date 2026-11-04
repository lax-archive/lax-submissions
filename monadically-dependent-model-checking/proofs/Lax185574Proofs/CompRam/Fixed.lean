import Lax185574Proofs.CompRam.Word
import Lax185574Proofs.WalkDistance

/-!
The fixed question to the rank shift as an explicit word.

On the graph `G1` with one vertex of color `0`, every tuple is constant,
so the atoms of a tuple of arity `ℓ` at rank `(k, q)` are all equalities
`xᵢ = xⱼ`, the colors `0(xᵢ)`, the distance atoms `dist(xᵢ, xⱼ) ≤ r` for
`r ≤ ρ⁻(k, q)` and `dist(xᵢ, 0) < r` for `1 ≤ r ≤ ρ⁺(k, q)`. Their codes
in increasing order are the list `atL ℓ ρ⁻ ρ⁺` (`words_atoms_G1`). The
only extension of a tuple of arity `1` is the tuple of arity `2`. So the
fixed question `dSq = tree_{1,1}(0)` is
`[1, 1, 1] ++ toWord (atL 1 729 6561) ++ toWord [0 :: toWord (atL 2 1 81)]`
and its answer `dSa = tree_{2,0}(0)` is `[2, 0, 1] ++ toWord (atL 1 1 81)`,
a word of length `427`.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574.DistanceLogic
open Lax185574.DistanceLogic.DistFO Lax185574.GaifmanGraph Lax185574.SequenceEncoding
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The codes of the equalities of arity `ℓ`. -/
def atEq (ℓ : ℕ) : List (List ℕ) := (List.range ℓ).flatMap fun i => (List.range ℓ).map fun j => [0, i, j]

/-- The codes of the colors `0(xᵢ)`. -/
def atCol (ℓ : ℕ) : List (List ℕ) := (List.range ℓ).map fun i => [3, 0, i]

/-- The codes of the binary distance atoms of radius at most `R`. -/
def atDist (ℓ R : ℕ) : List (List ℕ) :=
  (List.range (R + 1)).flatMap fun r => (List.range ℓ).flatMap fun i => (List.range ℓ).map fun j => [4, r, i, j]

/-- The codes of the unary distance atoms `dist(xᵢ, 0) < r`, `1 ≤ r ≤ R`. -/
def atDcol (ℓ R : ℕ) : List (List ℕ) := (List.range R).flatMap fun r => (List.range ℓ).map fun i => [5, r + 1, 0, i]

/-- The codes of the atoms of a constant tuple of arity `ℓ` in `G1`, in
increasing order. -/
def atL (ℓ R₁ R₂ : ℕ) : List (List ℕ) := atEq ℓ ++ atCol ℓ ++ atDist ℓ R₁ ++ atDcol ℓ R₂

theorem mem_atL {ℓ R₁ R₂ : ℕ} {c : List ℕ} : c ∈ atL ℓ R₁ R₂ ↔
    (∃ i < ℓ, ∃ j < ℓ, c = [0, i, j]) ∨ (∃ i < ℓ, c = [3, 0, i]) ∨
      (∃ r ≤ R₁, ∃ i < ℓ, ∃ j < ℓ, c = [4, r, i, j]) ∨
      (∃ r, 1 ≤ r ∧ r ≤ R₂ ∧ ∃ i < ℓ, c = [5, r, 0, i]) := by
  simp only [atL, atEq, atCol, atDist, atDcol, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range, or_assoc]
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ ?_))
  · constructor
    · rintro ⟨i, hi, j, hj, rfl⟩; exact ⟨i, hi, j, hj, rfl⟩
    · rintro ⟨i, hi, j, hj, rfl⟩; exact ⟨i, hi, j, hj, rfl⟩
  · constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · constructor
    · rintro ⟨r, hr, i, hi, j, hj, rfl⟩; exact ⟨r, by omega, i, hi, j, hj, rfl⟩
    · rintro ⟨r, hr, i, hi, j, hj, rfl⟩; exact ⟨r, by omega, i, hi, j, hj, rfl⟩
  · constructor
    · rintro ⟨r, hr, i, hi, rfl⟩; exact ⟨r + 1, by omega, by omega, i, hi, rfl⟩
    · rintro ⟨r, h1, hr, i, hi, rfl⟩
      exact ⟨r - 1, by omega, i, hi, by rw [Nat.sub_add_cancel h1]⟩

theorem lt3 {a b c a' b' c' : ℕ} : [a, b, c] < [a', b', c'] ↔
    a < a' ∨ a = a' ∧ (b < b' ∨ b = b' ∧ c < c') := by
  simp [List.cons_lt_cons_iff]

theorem lt4 {a b c d a' b' c' d' : ℕ} : [a, b, c, d] < [a', b', c', d'] ↔
    a < a' ∨ a = a' ∧ (b < b' ∨ b = b' ∧ (c < c' ∨ c = c' ∧ d < d')) := by
  simp [List.cons_lt_cons_iff]

theorem lt34 {a b c a' b' c' d' : ℕ} (h : a < a') : [a, b, c] < [a', b', c', d'] := by
  simp [List.cons_lt_cons_iff, h]

theorem atEq_sorted (ℓ : ℕ) : (atEq ℓ).Pairwise (· < ·) := by
  refine List.pairwise_flatMap.2 ⟨fun i _ => List.pairwise_map.2 (List.pairwise_lt_range.imp
    fun h => lt3.2 (by omega)), List.pairwise_lt_range.imp fun h => ?_⟩
  simp only [List.mem_map, List.mem_range]
  rintro _ ⟨j, -, rfl⟩ _ ⟨j', -, rfl⟩; exact lt3.2 (by omega)

theorem atCol_sorted (ℓ : ℕ) : (atCol ℓ).Pairwise (· < ·) :=
  List.pairwise_map.2 (List.pairwise_lt_range.imp fun h => lt3.2 (by omega))

theorem atDist_sorted (ℓ R : ℕ) : (atDist ℓ R).Pairwise (· < ·) := by
  refine List.pairwise_flatMap.2 ⟨fun r _ => List.pairwise_flatMap.2 ⟨fun i _ =>
    List.pairwise_map.2 (List.pairwise_lt_range.imp fun h => lt4.2 (by omega)),
      List.pairwise_lt_range.imp fun h => ?_⟩, List.pairwise_lt_range.imp fun h => ?_⟩
  · simp only [List.mem_map, List.mem_range]
    rintro _ ⟨j, -, rfl⟩ _ ⟨j', -, rfl⟩; exact lt4.2 (by omega)
  · simp only [List.mem_map, List.mem_range, List.mem_flatMap]
    rintro _ ⟨i, -, j, -, rfl⟩ _ ⟨i', -, j', -, rfl⟩; exact lt4.2 (by omega)

theorem atDcol_sorted (ℓ R : ℕ) : (atDcol ℓ R).Pairwise (· < ·) := by
  refine List.pairwise_flatMap.2 ⟨fun r _ => List.pairwise_map.2 (List.pairwise_lt_range.imp
    fun h => lt4.2 (by omega)), List.pairwise_lt_range.imp fun h => ?_⟩
  simp only [List.mem_map, List.mem_range]
  rintro _ ⟨j, -, rfl⟩ _ ⟨j', -, rfl⟩; exact lt4.2 (by omega)

theorem atL_sorted (ℓ R₁ R₂ : ℕ) : (atL ℓ R₁ R₂).Pairwise (· < ·) := by
  unfold atL
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨List.pairwise_append.2
    ⟨atEq_sorted ℓ, atCol_sorted ℓ, ?_⟩, atDist_sorted ℓ R₁, ?_⟩, atDcol_sorted ℓ R₂, ?_⟩ <;>
    simp only [atEq, atCol, atDist, atDcol, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_range]
  · rintro _ ⟨i, -, j, -, rfl⟩ _ ⟨i', -, rfl⟩; exact lt3.2 (by omega)
  · rintro _ (⟨i, -, j, -, rfl⟩ | ⟨i, -, rfl⟩) _ ⟨r, -, i', -, j', -, rfl⟩ <;> exact lt34 (by omega)
  · rintro _ ((⟨i, -, j, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨r, -, i, -, j, -, rfl⟩) _ ⟨r', -, i', -, rfl⟩
    · exact lt34 (by omega)
    · exact lt34 (by omega)
    · exact lt4.2 (by omega)

theorem sortedDistinct_of_sorted {L : List (List ℕ)} (h : L.Pairwise (· < ·)) : sortedDistinct L = L := by
  unfold sortedDistinct
  have hnd : L.Nodup := h.imp fun h' => ne_of_lt h'
  exact (List.toFinset_sort (· ≤ ·) hnd).2 (h.imp le_of_lt)

/-! ### The atoms in `G1` -/

theorem g1_const {ℓ : ℕ} (u : Fin ℓ → Fin 1) (i j : Fin ℓ) : u i = u j := Subsingleton.elim _ _

theorem drank_distLe {k q ℓ r : ℕ} {i j : Fin ℓ} : DRank k q (.distLe r i j) ↔ r ≤ rhoMinus k q :=
  ⟨fun h => by cases h with | distLe _ _ _ h => exact h, fun h => .distLe r i j h⟩

theorem drank_distColorLt {k q ℓ r Y : ℕ} {i : Fin ℓ} :
    DRank k q (.distColorLt r Y i) ↔ r ≤ rhoPlus k q :=
  ⟨fun h => by cases h with | distColorLt _ _ _ h => exact h, fun h => .distColorLt r Y i h⟩

theorem withinDist_G1 (r : ℕ) (a b : Fin 1) : WithinDist G1.resolved r a b := by
  rw [Subsingleton.elim a b]; exact Lax185574Proofs.WalkDistance.withinDist_refl _ _ _

theorem atoms_G1_iff (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin 1) (φ : DistFO ℓ) :
    φ ∈ Node.atoms (node G1 k q u) ↔ code φ ∈ atL ℓ (rhoMinus k q) (rhoPlus k q) := by
  rw [mem_atoms_node, mem_atL]
  constructor
  · rintro ⟨hat, hr, hs⟩
    cases φ with
    | eq i j => exact Or.inl ⟨i, i.2, j, j.2, rfl⟩
    | edge i j => simp [Sat, G1, unresolved] at hs
    | nonEdge i j => simp [Sat, G1, unresolved] at hs
    | color Y i =>
      simp only [Sat, G1, unresolved] at hs
      subst hs; exact Or.inr (Or.inl ⟨i, i.2, rfl⟩)
    | distLe r i j => exact Or.inr (Or.inr (Or.inl ⟨r, drank_distLe.1 hr, i, i.2, j, j.2, rfl⟩))
    | distColorLt r Y i =>
      obtain ⟨v, hv, p, hp⟩ := hs
      simp only [G1, unresolved] at hv
      subst hv
      exact Or.inr (Or.inr (Or.inr ⟨r, by omega, drank_distColorLt.1 hr, i, i.2, rfl⟩))
    | not => exact hat.elim
    | and => exact hat.elim
    | exLocal => exact hat.elim
  · rintro (⟨i', -, j', -, he⟩ | ⟨i', -, he⟩ | ⟨r', hr', i', -, j', -, he⟩ | ⟨r', h1, hr', i', -, he⟩) <;>
      cases φ <;> simp [code] at he
    all_goals first
      | exact ⟨trivial, .eq _ _, g1_const u _ _⟩
      | (obtain ⟨rfl, -⟩ := he; exact ⟨trivial, .color _ _, rfl⟩)
      | (obtain ⟨rfl, -⟩ := he
         exact ⟨trivial, .distLe _ _ _ hr', withinDist_G1 _ _ _⟩)
      | (obtain ⟨rfl, rfl, -⟩ := he
         refine ⟨trivial, .distColorLt _ _ _ hr', u _, rfl, SimpleGraph.Walk.nil, ?_⟩
         simp only [SimpleGraph.Walk.length_nil]; omega)

/-- **The atoms of a constant tuple in `G1`.** -/
theorem words_atoms_G1 (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin 1) :
    (Node.atoms (node G1 k q u)).words = atL ℓ (rhoMinus k q) (rhoPlus k q) := by
  rw [← sortedDistinct_of_sorted (atL_sorted ℓ _ _)]
  symm
  refine sortedDistinct_eq_words _ _ fun c => ⟨fun hc => ?_, ?_⟩
  · rcases mem_atL.1 hc with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨r, hr, i, hi, j, hj, rfl⟩ |
        ⟨r, h1, hr, i, hi, rfl⟩
    · exact ⟨.eq ⟨i, hi⟩ ⟨j, hj⟩, (atoms_G1_iff k q u _).2 (mem_atL.2 (Or.inl ⟨i, hi, j, hj, rfl⟩)), rfl⟩
    · exact ⟨.color 0 ⟨i, hi⟩, (atoms_G1_iff k q u _).2 (mem_atL.2 (Or.inr (Or.inl ⟨i, hi, rfl⟩))), rfl⟩
    · exact ⟨.distLe r ⟨i, hi⟩ ⟨j, hj⟩, (atoms_G1_iff k q u _).2
        (mem_atL.2 (Or.inr (Or.inr (Or.inl ⟨r, hr, i, hi, j, hj, rfl⟩)))), rfl⟩
    · exact ⟨.distColorLt r 0 ⟨i, hi⟩, (atoms_G1_iff k q u _).2
        (mem_atL.2 (Or.inr (Or.inr (Or.inr ⟨r, h1, hr, i, hi, rfl⟩)))), rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    rw [Lax185574Proofs.Legacy.encode_eq_code]; exact (atoms_G1_iff k q u φ).1 hφ

/-- The extensions of a constant tuple in `G1`. -/
theorem exts_G1 (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin 1) (e : Fin ℓ × Node q (ℓ + 1)) :
    e ∈ Node.exts (node G1 k (q + 1) u) ↔ e.2 = node G1 (k + 1) q (fun _ => 0) := by
  rw [mem_exts_node]
  constructor
  · rintro ⟨i, b, -, rfl⟩
    exact congrArg (node G1 (k + 1) q) (Subsingleton.elim (α := Fin (ℓ + 1) → Fin 1) _ _)
  · intro h
    refine ⟨e.1, 0, ?_, ?_⟩
    · rw [Subsingleton.elim (u e.1) 0]; exact Lax185574Proofs.WalkDistance.withinDist_refl _ _ _
    · rw [Subsingleton.elim (Fin.snoc u 0) (fun _ => (0 : Fin 1)), ← h]

theorem exts_G1_one (k q : ℕ) (u : Fin 1 → Fin 1) :
    Node.exts (node G1 k (q + 1) u) = {((0 : Fin 1), node G1 (k + 1) q (fun _ => 0))} := by
  ext e
  rw [exts_G1, Finset.mem_singleton]
  obtain ⟨i, t⟩ := e
  rw [Subsingleton.elim i 0]
  simp

/-! ### The fixed question and its answer -/

theorem rho_vals : rhoMinus 1 (0 + 1) = 729 ∧ rhoPlus 1 (0 + 1) = 6561 ∧ rhoMinus (1 + 1) 0 = 1 ∧
    rhoPlus (1 + 1) 0 = 81 := by
  simp [rhoMinus, rhoPlus]

/-- **The fixed question to the rank shift.** -/
theorem dSq_eq : dSq = [1, 1, 1] ++ toWord (atL 1 729 6561) ++ toWord [0 :: toWord (atL 2 1 81)] := by
  obtain ⟨h1, h2, h3, h4⟩ := rho_vals
  have he : (({((0 : Fin 1), node G1 (1 + 1) 0 (fun _ => 0))} : Finset (Fin 1 × Node 0 2))).words =
      [0 :: toWord (atL 2 1 81)] := by
    rw [Finset.words, Finset.image_singleton, Finset.sort_singleton, toWord_ext, toWord_node_zero,
      words_atoms_G1, h3, h4]
    rfl
  rw [dSq_tree, toWord_tree_eq, toWord_node_succ, words_atoms_G1, exts_G1_one, he, h1, h2, List.append_assoc]

/-- **The answer to the fixed question.** -/
theorem dSa_eq : dSa = [2, 0, 1] ++ toWord (atL 1 1 81) := by
  obtain ⟨-, -, h3, h4⟩ := rho_vals
  rw [dSa_tree, toWord_tree_eq, toWord_node_zero, words_atoms_G1, h3, h4]

theorem length_toWord_nat (w : List ℕ) : (toWord w).length = w.length + 1 := by
  show (w.length :: (w.map toWord).flatten).length = _
  rw [List.length_cons]
  congr 1
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]
    change 1 + w.length = _; omega

theorem length_toWord_words (ws : List (List ℕ)) :
    (toWord ws).length = 1 + (ws.map fun w => w.length + 1).sum := by
  show (ws.length :: (ws.map toWord).flatten).length = _
  simp only [List.length_cons, List.length_flatten, List.map_map]
  rw [Nat.add_comm]
  congr 2
  exact List.map_congr_left fun w _ => length_toWord_nat w

theorem length_dSa : dSa.length = 427 := by
  rw [dSa_eq, List.length_append, length_toWord_words]
  decide

end Lax185574Proofs.CompRam
