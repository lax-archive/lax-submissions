import Lax185574Proofs.MC.InitTree

/-!
The word of the type tree of an initial partial graph.

The atoms of `initAtoms k q ℓ c` sorted by their codes are the
equalities `[0, i, j]` (by `i`, then `j`), the colors `[3, c, i]` (by
`i`), the distance atoms `[4, r, i, j]` (by `r ≤ ρ⁻(k, q)`, then `i`,
then `j`) and the color distance atoms `[5, r, c, i]` (by
`1 ≤ r ≤ ρ⁺(k, q)`, then `i`). The extensions `(i, initNode …)` are
sorted by `i`, and all have the same child. `initWord` is the resulting
word, written as a function of the rank, the arity and the color, and
`toWord_initNode` identifies it with the word of `initNode`.
-/

namespace Lax185574Proofs.MC

open Lax185574.PartialGraphs Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.TypeTrees Lax185574.WordEncoding
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The sorted codes of the atoms of `initAtoms k q ℓ c`. -/
def atomWords (k q ℓ c : ℕ) : List (List ℕ) :=
  ((List.range ℓ).flatMap fun i => (List.range ℓ).map fun j => [0, i, j]) ++
  ((List.range ℓ).map fun i => [3, c, i]) ++
  ((List.range (rhoMinus k q + 1)).flatMap fun r =>
    (List.range ℓ).flatMap fun i => (List.range ℓ).map fun j => [4, r, i, j]) ++
  ((List.range (rhoPlus k q)).flatMap fun r => (List.range ℓ).map fun i => [5, r + 1, c, i])

/-- The word of `initNode k q ℓ c`. -/
def initWord : (k q ℓ c : ℕ) → List ℕ
  | k, 0, ℓ, c => toWord (atomWords k 0 ℓ c)
  | k, q + 1, ℓ, c =>
      toWord (atomWords k (q + 1) ℓ c) ++
        toWord ((List.range ℓ).map fun i => i :: initWord (k + 1) q (ℓ + 1) c)

/-! ### Sorted lists of words -/

theorem pairwise_flatMap_range {n : ℕ} {f : ℕ → List (List ℕ)}
    (hf : ∀ a < n, (f a).Pairwise (· < ·))
    (hlt : ∀ a b, a < b → b < n → ∀ x ∈ f a, ∀ y ∈ f b, x < y) :
    ((List.range n).flatMap f).Pairwise (· < ·) := by
  rw [List.pairwise_flatMap]
  refine ⟨fun a ha => hf a (List.mem_range.mp ha), ?_⟩
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) List.pairwise_lt_range
  exact hlt a b hab (List.mem_range.mp hb)

theorem cons_lt_cons_of_lt {h a b : ℕ} {u v : List ℕ} (hab : a < b) :
    h :: a :: u < h :: b :: v :=
  List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl hab)⟩)

theorem cons_lt_cons_of_head {a b : ℕ} {u v : List ℕ} (hab : a < b) : a :: u < b :: v :=
  List.cons_lt_cons_iff.mpr (Or.inl hab)

theorem cons_lt_cons_same {a : ℕ} {u v : List ℕ} (h : u < v) : a :: u < a :: v :=
  List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩)

theorem atomWords_pairwise (k q ℓ c : ℕ) : (atomWords k q ℓ c).Pairwise (· < ·) := by
  have hrow : ∀ (h : ℕ) (pre : List ℕ), ((List.range ℓ).map fun j => h :: (pre ++ [j])).Pairwise
      (· < ·) := by
    intro h pre
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp fun {a b} hab => cons_lt_cons_same ?_
    induction pre with
    | nil => exact cons_lt_cons_of_head hab
    | cons x pre ih => exact cons_lt_cons_same ih
  simp only [atomWords]
  refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨List.pairwise_append.mpr
    ⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · refine pairwise_flatMap_range (fun i _ => by simpa using hrow 0 [i]) ?_
    intro a b hab _ x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨j, -, rfl⟩ := hx; obtain ⟨j', -, rfl⟩ := hy
    exact cons_lt_cons_of_lt hab
  · simpa using hrow 3 [c]
  · intro a ha b hb
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ha hb
    obtain ⟨_, _, _, _, rfl⟩ := ha; obtain ⟨_, _, rfl⟩ := hb
    exact cons_lt_cons_of_head (by norm_num)
  · refine pairwise_flatMap_range (fun r _ => pairwise_flatMap_range
      (fun i _ => by simpa using hrow 4 [r, i]) ?_) ?_
    · intro a b hab _ x hx y hy
      simp only [List.mem_map, List.mem_range] at hx hy
      obtain ⟨j, -, rfl⟩ := hx; obtain ⟨j', -, rfl⟩ := hy
      exact cons_lt_cons_same (cons_lt_cons_of_lt hab)
    · intro a b hab _ x hx y hy
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hy
      obtain ⟨_, _, _, _, rfl⟩ := hx; obtain ⟨_, _, _, _, rfl⟩ := hy
      exact cons_lt_cons_of_lt hab
  · intro a ha b hb
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at ha hb
    obtain ⟨_, _, _, _, _, _, rfl⟩ := hb
    rcases ha with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact cons_lt_cons_of_head (by norm_num)
  · refine pairwise_flatMap_range (fun r _ => by simpa using hrow 5 [r + 1, c]) ?_
    intro a b hab _ x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨i, -, rfl⟩ := hx; obtain ⟨i', -, rfl⟩ := hy
    exact cons_lt_cons_of_lt (by omega)
  · intro a ha b hb
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at ha hb
    obtain ⟨_, _, _, _, rfl⟩ := hb
    rcases ha with (⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, _, _, _, _, rfl⟩ <;>
      exact cons_lt_cons_of_head (by norm_num)

/-- A sorted list of distinct words with the right elements is the
list of words of a finite set. -/
theorem words_eq_of_pairwise {α : Type*} [WordEncoding α] (S : Finset α) (L : List (List ℕ))
    (hL : L.Pairwise (· < ·)) (hmem : ∀ u, u ∈ L ↔ ∃ a ∈ S, toWord a = u) :
    Finset.words S = L := by
  classical
  unfold Finset.words
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
  · exact hL.imp le_of_lt
  · apply List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _)
    · exact hL.imp fun h => ne_of_lt h
    · rw [Finset.sort_toFinset]
      ext u
      simp only [Finset.mem_image, List.mem_toFinset, hmem]

theorem toWord_distFO {ℓ : ℕ} (φ : DistFO ℓ) : toWord φ = DistFO.code φ :=
  Lax185574Proofs.Legacy.encode_eq_code φ

theorem mem_atomWords {k q ℓ c : ℕ} (u : List ℕ) :
    u ∈ atomWords k q ℓ c ↔ ∃ a ∈ initAtoms k q ℓ c, toWord a = u := by
  classical
  simp only [atomWords, initAtoms, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_product, Finset.mem_range, Finset.mem_Icc, Prod.exists, toWord_distFO]
  constructor
  · rintro (((⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨r, hr, i, hi, j, hj, rfl⟩) | ⟨r, hr, i, hi, rfl⟩)
    · exact ⟨_, Or.inl (Or.inl (Or.inl ⟨⟨i, hi⟩, ⟨j, hj⟩, rfl⟩)), rfl⟩
    · exact ⟨_, Or.inl (Or.inl (Or.inr ⟨⟨i, hi⟩, rfl⟩)), rfl⟩
    · exact ⟨_, Or.inl (Or.inr ⟨r, ⟨i, hi⟩, ⟨j, hj⟩, ⟨hr, trivial⟩, rfl⟩), rfl⟩
    · exact ⟨_, Or.inr ⟨r + 1, ⟨i, hi⟩, ⟨⟨by omega, by omega⟩, trivial⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ((⟨i, j, rfl⟩ | ⟨i, rfl⟩) | ⟨r, i, j, ⟨hr, -⟩, rfl⟩) | ⟨r, i, ⟨⟨h1, hr⟩, -⟩, rfl⟩,
      rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨i, i.isLt, j, j.isLt, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨i, i.isLt, rfl⟩))
    · exact Or.inl (Or.inr ⟨r, hr, i, i.isLt, j, j.isLt, rfl⟩)
    · refine Or.inr ⟨r - 1, by omega, i, i.isLt, ?_⟩
      simp only [DistFO.code]
      congr 2; omega

theorem words_initAtoms (k q ℓ c : ℕ) :
    Finset.words (initAtoms k q ℓ c) = atomWords k q ℓ c :=
  words_eq_of_pairwise _ _ (atomWords_pairwise k q ℓ c) mem_atomWords

open Classical in
theorem words_initExts (k q ℓ c : ℕ) :
    Finset.words (Finset.univ.image fun i : Fin ℓ => (i, initNode (k + 1) q (ℓ + 1) c)) =
      (List.range ℓ).map fun i => i :: toWord (initNode (k + 1) q (ℓ + 1) c) := by
  classical
  apply words_eq_of_pairwise
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun hab => cons_lt_cons_of_head hab
  · intro u
    simp only [List.mem_map, List.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, i.isLt, rfl⟩

open Classical in
/-- **The word of an initial tree.** -/
theorem toWord_initNode : ∀ (k q ℓ c : ℕ), toWord (initNode k q ℓ c) = initWord k q ℓ c
  | k, 0, ℓ, c => by
      show toWord (Finset.words (initAtoms k 0 ℓ c)) = _
      rw [words_initAtoms]; rfl
  | k, q + 1, ℓ, c => by
      show toWord (Finset.words (initAtoms k (q + 1) ℓ c)) ++
        toWord (Finset.words (Finset.univ.image fun i : Fin ℓ =>
          (i, initNode (k + 1) q (ℓ + 1) c))) = _
      rw [words_initAtoms, words_initExts, toWord_initNode (k + 1) q (ℓ + 1) c]
      rfl

/-- The word of the type tree of a vertex of color `c` in a partial
graph without resolved pairs. -/
theorem toWord_tree_unresolved {V : Type*} (G : PartialGraph V) (hE : G.edge = ⊥)
    (hN : G.nonEdge = ⊥) (a : V) (k q : ℕ) :
    toWord (tree G k q ![a]) = [k, q, 1] ++ initWord k q 1 (G.color a) := by
  rw [tree_unresolved G hE hN a k q]
  show toWord (k, q, 1) ++ toWord (initNode k q 1 (G.color a)) = _
  rw [toWord_initNode]; rfl

end Lax185574Proofs.MC
