import Lax185574Proofs.TreeAlgo.ToFarTree
import Lax185574Proofs.EvalRam.Scan
import Lax185574Proofs.EncodingInjectivity


/-!
The far tree on words.

The program of lem:to-ftree works on the word of the root of
`τ = tree_{k,q+1}(ā)`, on the words of the entries of the scatter type
`σ`, and on the answers of the restriction program, one per extension.
This module defines what it computes, as functions of these words, and
shows that on the words of `τ` and `σ` the result is the word of the
far tree `farTreeNode`, the semantic core of lem:to-ftree.
-/

namespace Lax185574Proofs.FarRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574Proofs.TreeAlgo Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### Distance atoms read off a node -/

/-- The atom `dist(xᵢ, xⱼ) ≤ s` is among the atoms of the node at `y`. -/
def hit (X : List ℕ) (y s i j : ℕ) : Bool := atHit X [4, s, i, j] y 0 4 (xg X y)

theorem atoms_drop {h ℓ : ℕ} {X : List ℕ} {y : ℕ} {t : Node h ℓ} {r : List ℕ}
    (hx : X.drop y = toWord t ++ r) : ∃ r', X.drop y = toWord (Node.atoms t).words ++ r' := by
  cases h with
  | zero => exact ⟨r, by rw [hx, toWord_node_zero]⟩
  | succ h => exact ⟨_, (nodeSplit hx).1⟩

theorem hit_iff {h ℓ : ℕ} {X : List ℕ} {y : ℕ} {t : Node h ℓ} {r : List ℕ}
    (hx : X.drop y = toWord t ++ r) (s : ℕ) (i j : Fin ℓ) :
    hit X y s i j = true ↔ DistFO.distLe s i j ∈ Node.atoms t := by
  obtain ⟨r', hr'⟩ := atoms_drop hx
  have := atHit_iff (F := [4, s, i, j]) (p := 0) (w := [4, s, i, j]) (r' := []) hr' (by simp)
    (by simp)
  unfold hit
  exact this.trans (code_mem_words (φ := DistFO.distLe s i j))

/-! ### The radius and the blocks -/

/-- The canonical block of position `i` for the test radius `s`. -/
def canonW (X : List ℕ) (s ℓ i : ℕ) : ℕ := ((List.range ℓ).find? (fun j => hit X 0 s i j)).getD i

/-- The pair `i, j` violates the admissibility of the canonical partition
at the test radii `s₁ = 4ρ − 2r` and `s₂ = 4ρ + 2r`. -/
def badW (X : List ℕ) (s₁ s₂ ℓ i j : ℕ) : Bool :=
  (canonW X s₁ ℓ i == canonW X s₁ ℓ j && !hit X 0 s₁ i j) ||
    (canonW X s₁ ℓ i != canonW X s₁ ℓ j && hit X 0 s₂ i j)

/-- The radius `ρ` is admissible with its canonical partition. -/
def admW (X : List ℕ) (r ρ ℓ : ℕ) : Bool :=
  !((List.range ℓ).any fun i => (List.range ℓ).any fun j => badW X (4 * ρ - 2 * r) (4 * ρ + 2 * r) ℓ i j)

/-- The first admissible radius between `r` and `9^(ℓ−1) r`. -/
def radW (X : List ℕ) (r ℓ : ℕ) : ℕ :=
  ((List.range' r (9 ^ (ℓ - 1) * r - r + 1)).find? (fun ρ => admW X r ρ ℓ)).getD r

section Root

variable {q ℓ : ℕ} {X : List ℕ} {t : Node q ℓ} {rest : List ℕ}

theorem hit_root (hx : X.drop 0 = toWord t ++ rest) (s : ℕ) (i j : Fin ℓ) :
    hit X 0 s i j = distTest t s i j := by
  rw [Bool.eq_iff_iff, hit_iff hx, distTest, decide_eq_true_iff]

theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem canonW_root (hx : X.drop 0 = toWord t ++ rest) (s : ℕ) (i : Fin ℓ) :
    canonW X s ℓ i = (canonBlock t s i).val := by
  rw [canonW, canonBlock, ← map_val_finRange, List.find?_map]
  have : ((fun j => hit X 0 s i j) ∘ Fin.val) = fun j => distTest t s i j := by
    funext j; exact hit_root hx s i j
  rw [this]
  cases (List.finRange ℓ).find? (fun j => distTest t s i j) <;> rfl

theorem badW_root (hx : X.drop 0 = toWord t ++ rest) (s₁ s₂ : ℕ) (i j : Fin ℓ) :
    badW X s₁ s₂ ℓ i j = !(decide ((canonBlock t s₁ i = canonBlock t s₁ j → distTest t s₁ i j = true) ∧
      (canonBlock t s₁ i ≠ canonBlock t s₁ j → distTest t s₂ i j = false))) := by
  rw [badW, canonW_root hx, canonW_root hx, hit_root hx, hit_root hx]
  by_cases h : canonBlock t s₁ i = canonBlock t s₁ j
  · simp [h]
  · have h' : (canonBlock t s₁ i).val ≠ (canonBlock t s₁ j).val := fun e => h (Fin.ext e)
    have e1 : ((canonBlock t s₁ i).val == (canonBlock t s₁ j).val) = false :=
      beq_eq_false_iff_ne.mpr h'
    have e2 : ((canonBlock t s₁ i).val != (canonBlock t s₁ j).val) = true := by
      simpa [bne_iff_ne] using h'
    simp [e1, e2, h]

theorem any_range_fin (n : ℕ) (f : ℕ → Bool) :
    (List.range n).any f = true ↔ ∃ i : Fin n, f i = true := by
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩

theorem admW_root (hx : X.drop 0 = toWord t ++ rest) (r ρ : ℕ) :
    admW X r ρ ℓ = admissibleB t r ρ (canonBlock t (4 * ρ - 2 * r)) := by
  rw [admW, admissibleB, Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_true_iff]
  rw [← Bool.not_eq_true, any_range_fin]
  simp only [any_range_fin, badW_root hx, Bool.not_eq_true', decide_eq_false_iff_not]
  push Not
  rfl

theorem radW_root (hx : X.drop 0 = toWord t ++ rest) (r : ℕ) : radW X r ℓ = findRadius t r := by
  rw [radW, findRadius]
  congr 2
  funext ρ
  exact admW_root hx r ρ

end Root

/-! ### The extensions -/

/-- The new vertex of extension `e` is within distance `r` of position `j`. -/
def mtW (X : List ℕ) (r ℓ e j : ℕ) : Bool := hit X (frPos X (listEnd X 0) e + 2) r j ℓ

/-- The new vertex of extension `e` is far from all positions. -/
def farW (X : List ℕ) (r ℓ e : ℕ) : Bool := !((List.range ℓ).any fun j => mtW X r ℓ e j)

section Exts

variable {q ℓ r : ℕ} {X : List ℕ} {t : Node (q + 1) ℓ} {rest : List ℕ}

theorem ext_index (a : Fin ℓ × Node q (ℓ + 1)) (ha : a ∈ Node.exts t) :
    ∃ e, ∃ he : e < (Node.exts t).words.length, (Node.exts t).words[e] = toWord a :=
  List.getElem_of_mem (mem_words.mpr ⟨a, ha, rfl⟩)

theorem mtW_ext (hx : X.drop 0 = toWord t ++ rest) {e : ℕ} (he : e < (Node.exts t).words.length)
    {a : Fin ℓ × Node q (ℓ + 1)} (ha : toWord a = (Node.exts t).words[e]) (j : Fin ℓ) :
    mtW X r ℓ e j = true ↔ DistFO.distLe r j.castSucc (Fin.last ℓ) ∈ Node.atoms a.2 := by
  obtain ⟨-, h2⟩ := nodeSplit hx
  obtain ⟨-, r', hr'⟩ := extFrame h2 he ha
  have := hit_iff hr' r j.castSucc (Fin.last ℓ)
  simpa [mtW] using this

theorem farW_ext (hx : X.drop 0 = toWord t ++ rest) {e : ℕ} (he : e < (Node.exts t).words.length)
    {a : Fin ℓ × Node q (ℓ + 1)} (ha : toWord a = (Node.exts t).words[e]) :
    farW X r ℓ e = isFarExt r a.2 := by
  rw [farW, isFarExt, Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_true_iff, ← Bool.not_eq_true,
    any_range_fin]
  simp only [mtW_ext hx he ha]
  push Not
  rfl

end Exts

/-! ### The scan of the scatter type -/

/-- The word of the tree inside the word `s :: ν ++ [m]` of an entry. -/
def nuPart (w : List ℕ) : List ℕ := (w.drop 1).take (w.length - 2)

/-- The last entry of a word. -/
def lastE (w : List ℕ) : ℕ := xg w (w.length - 1)

/-- Some extension far from the tuple has the tree `ν` at its new
vertex. -/
def inNW (X : List ℕ) (Ans : List (List ℕ)) (r ℓ : ℕ) (ν : List ℕ) : Bool :=
  (List.range Ans.length).any fun e => (Ans.getD e [] == ν) && farW X r ℓ e

/-- The block `b` is met by a vertex with the tree `ν`. -/
def blkW (X : List ℕ) (Ans : List (List ℕ)) (r ℓ : ℕ) (bt : ℕ → ℕ) (ν : List ℕ) (b : ℕ) : Bool :=
  (List.range Ans.length).any fun e => (Ans.getD e [] == ν) &&
    (List.range ℓ).any fun j => mtW X r ℓ e j && (bt j == b)

/-- The number of blocks met by a vertex with the tree `ν`. -/
def cntW (X : List ℕ) (Ans : List (List ℕ)) (r ℓ : ℕ) (bt : ℕ → ℕ) (ν : List ℕ) : ℕ :=
  ((List.range ℓ).filter (blkW X Ans r ℓ bt ν)).length

/-- The entry with word `w` is selected. -/
def selW (X : List ℕ) (Ans : List (List ℕ)) (k q r ρ ℓ : ℕ) (bt : ℕ → ℕ) (w : List ℕ) : Bool :=
  (xg w 0 == 4 * ρ) && (xg w 1 == k + 1) && (xg w 2 == q) &&
    (inNW X Ans r ℓ (nuPart w) || decide (cntW X Ans r ℓ bt (nuPart w) < lastE w))

/-- The words of the far tree: the trees of the selected entries, for the
radius and the blocks read off the root. -/
def farList (X : List ℕ) (Ans : List (List ℕ)) (k q ℓ : ℕ) (S : List (List ℕ)) : List (List ℕ) :=
  (S.filter (selW X Ans k q (rhoMinus (k + 1) q) (radW X (rhoMinus (k + 1) q) ℓ) ℓ
    (canonW X (4 * radW X (rhoMinus (k + 1) q) ℓ - 2 * rhoMinus (k + 1) q) ℓ))).map nuPart

theorem toWord_entry (p : (ℕ × TypeTree) × ℕ) : toWord p = p.1.1 :: (toWord p.1.2 ++ [p.2]) := rfl

theorem toWord_typeTree (ν : TypeTree) : toWord ν = ν.k :: ν.q :: ν.ℓ :: toWord ν.root := rfl

theorem nuPart_entry (p : (ℕ × TypeTree) × ℕ) : nuPart (toWord p) = toWord p.1.2 := by
  rw [toWord_entry]; simp [nuPart]

theorem lastE_entry (p : (ℕ × TypeTree) × ℕ) : lastE (toWord p) = p.2 := by
  rw [toWord_entry]; simp [lastE, xg]

theorem toWord_tree_inj {ν ν' : TypeTree} (h : toWord ν = toWord ν') : ν = ν' :=
  (Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree.prefix_inj ν ν' [] [] (by simpa)).1

/-- The answers of the restriction program, one per extension. -/
structure AnsOK (k q ℓ : ℕ) (t : Node (q + 1) ℓ) (Ans : List (List ℕ)) : Prop where
  len : Ans.length = (Node.exts t).words.length
  ans : ∀ e (he : e < (Node.exts t).words.length) (a : Fin ℓ × Node q (ℓ + 1)),
    toWord a = (Node.exts t).words[e] → Ans.getD e [] = toWord (lastTree k q ℓ a.2)

section Scan

variable {k q ℓ r : ℕ} {X : List ℕ} {t : Node (q + 1) ℓ} {rest : List ℕ} {Ans : List (List ℕ)}

theorem inNW_eq (hx : X.drop 0 = toWord t ++ rest) (hA : AnsOK k q ℓ t Ans) (ν : TypeTree) :
    inNW X Ans r ℓ (toWord ν) = decide (ν ∈ nearFarSet k q ℓ r t) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, inNW, List.any_eq_true]
  simp only [nearFarSet, Finset.mem_image, Finset.mem_filter, List.mem_range, Bool.and_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨e, he, heq, hfar⟩
    rw [hA.len] at he
    obtain ⟨a, ha, haw⟩ := getElem_words he
    rw [hA.ans e he a haw] at heq
    rw [farW_ext hx he haw] at hfar
    exact ⟨a, ⟨ha, hfar⟩, toWord_tree_inj heq⟩
  · rintro ⟨a, ⟨ha, hfar⟩, rfl⟩
    obtain ⟨e, he, hew⟩ := ext_index a ha
    refine ⟨e, by rw [hA.len]; exact he, hA.ans e he a hew.symm, ?_⟩
    rw [farW_ext hx he hew.symm]; exact hfar

theorem length_filter_range (T : Finset (Fin ℓ)) (f : ℕ → Bool)
    (hf : ∀ b : Fin ℓ, f b = true ↔ b ∈ T) : ((List.range ℓ).filter f).length = T.card := by
  rw [← map_val_finRange, List.filter_map, List.length_map]
  have hT : ((List.finRange ℓ).filter (f ∘ Fin.val)).toFinset = T := by
    ext b; simp [hf]
  rw [← hT, List.toFinset_card_of_nodup ((List.nodup_finRange ℓ).filter _)]

theorem cntW_eq (hx : X.drop 0 = toWord t ++ rest) (hA : AnsOK k q ℓ t Ans) (ν : TypeTree)
    (β : Fin ℓ → Fin ℓ) (bt : ℕ → ℕ) (hbt : ∀ j : Fin ℓ, bt j = (β j).val) :
    cntW X Ans r ℓ bt (toWord ν) = ((metPositions k q ℓ r t ν).image β).card := by
  refine length_filter_range _ _ fun b => ?_
  rw [blkW, List.any_eq_true]
  simp only [metPositions, Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and, List.mem_range, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  constructor
  · rintro ⟨e, he, heq, j, hj, hm, hb⟩
    rw [hA.len] at he
    obtain ⟨a, ha, haw⟩ := getElem_words he
    rw [hA.ans e he a haw] at heq
    have hm' := (mtW_ext hx he haw ⟨j, hj⟩).1 hm
    refine ⟨⟨j, hj⟩, ⟨a, ⟨ha, toWord_tree_inj heq⟩, hm'⟩, Fin.ext ?_⟩
    rw [← hbt]; exact hb
  · rintro ⟨i, ⟨a, ⟨ha, hν⟩, hm⟩, rfl⟩
    obtain ⟨e, he, hew⟩ := ext_index a ha
    refine ⟨e, by rw [hA.len]; exact he, by rw [hA.ans e he a hew.symm, hν], i, i.2,
      (mtW_ext hx he hew.symm i).2 hm, by rw [hbt]⟩

end Scan

/-! ### Sorted output -/

theorem lt_of_append_lt : ∀ {u v a b : List ℕ}, u ++ a < v ++ b → (∀ c, u ≠ v ++ c) →
    (∀ c, v ≠ u ++ c) → u < v
  | [], v, _, _, _, _, hv => absurd (by simp) (hv v)
  | x :: u, [], _, _, _, hu, _ => absurd (by simp) (hu (x :: u))
  | x :: u, y :: v, a, b, h, hu, hv => by
    simp only [List.cons_append, List.cons_lt_cons_iff] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨rfl, lt_of_append_lt h (fun c hc => hu c (by rw [hc]; rfl))
        (fun c hc => hv c (by rw [hc]; rfl))⟩

theorem pairwise_lt_words {α : Type*} [WordEncoding α] (S : Finset α) :
    S.words.Pairwise (· < ·) := by
  have h1 : S.words.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have h2 : S.words.Nodup := Finset.sort_nodup _ _
  exact (List.pairwise_and_iff.mpr ⟨h1, h2⟩).imp fun ⟨h, h'⟩ => lt_of_le_of_ne h h'

/-- **The selected entries in the order of the scatter type.** If all
selected entries have the same radius and the scatter type is a
function, the trees of the selected entries, in the order of the word of
the scatter type, are the word list of the set of these trees. -/
theorem words_filter_image (σ : Finset ((ℕ × TypeTree) × ℕ))
    (hfun : ∀ p ∈ σ, ∀ p' ∈ σ, p.1 = p'.1 → p = p') (P : (ℕ × TypeTree) × ℕ → Prop)
    [DecidablePred P] (s : ℕ) (hs : ∀ p ∈ σ, P p → p.1.1 = s) (sel : List ℕ → Bool)
    (hsel : ∀ p ∈ σ, sel (toWord p) = decide (P p)) :
    (σ.words.filter sel).map nuPart = ((σ.filter P).image fun p => p.1.2).words := by
  have hmem : ∀ w ∈ σ.words, ∃ p ∈ σ, toWord p = w := fun w hw => mem_words.mp hw
  have hL : ((σ.words.filter sel).map nuPart).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    refine ((pairwise_lt_words σ).filter sel).imp_of_mem ?_
    intro w₁ w₂ h₁ h₂ hlt
    obtain ⟨hw₁, hs₁⟩ := List.mem_filter.mp h₁
    obtain ⟨hw₂, hs₂⟩ := List.mem_filter.mp h₂
    obtain ⟨p₁, hp₁, rfl⟩ := hmem w₁ hw₁
    obtain ⟨p₂, hp₂, rfl⟩ := hmem w₂ hw₂
    rw [hsel p₁ hp₁, decide_eq_true_iff] at hs₁
    rw [hsel p₂ hp₂, decide_eq_true_iff] at hs₂
    have e₁ := hs p₁ hp₁ hs₁
    have e₂ := hs p₂ hp₂ hs₂
    rw [nuPart_entry, nuPart_entry]
    rw [toWord_entry, toWord_entry, e₁, e₂, List.cons_lt_cons_iff] at hlt
    have hlt' : toWord p₁.1.2 ++ [p₁.2] < toWord p₂.1.2 ++ [p₂.2] := by
      rcases hlt with h | ⟨-, h⟩
      · exact absurd h (lt_irrefl _)
      · exact h
    have hne : p₁.1.2 ≠ p₂.1.2 := by
      intro hν
      have : p₁ = p₂ := hfun p₁ hp₁ p₂ hp₂ (Prod.ext (e₁.trans e₂.symm) hν)
      subst this
      exact lt_irrefl _ hlt'
    have pf := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
    refine lt_of_append_lt hlt' (fun c hc => hne ?_) (fun c hc => hne ?_)
    · exact (pf.prefix_inj p₁.1.2 p₂.1.2 [] c (by simpa using hc)).1
    · exact (pf.prefix_inj p₁.1.2 p₂.1.2 c [] (by simpa using hc.symm)).1
  have hnd : ((σ.words.filter sel).map nuPart).Nodup := hL.imp ne_of_lt
  have hnd2 : (((σ.filter P).image fun p => p.1.2).words).Nodup := Finset.sort_nodup _ _
  have hperm := List.perm_of_nodup_nodup_toFinset_eq hnd hnd2 (by
    ext x
    rw [List.mem_toFinset, List.mem_toFinset, mem_words]
    simp only [List.mem_map, List.mem_filter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨w, ⟨hw, hsw⟩, rfl⟩
      obtain ⟨p, hp, rfl⟩ := hmem w hw
      rw [hsel p hp, decide_eq_true_iff] at hsw
      exact ⟨p.1.2, ⟨p, ⟨hp, hsw⟩, rfl⟩, (nuPart_entry p).symm⟩
    · rintro ⟨ν, ⟨p, ⟨hp, hP⟩, rfl⟩, rfl⟩
      refine ⟨toWord p, ⟨mem_words.mpr ⟨p, hp, rfl⟩, by rw [hsel p hp, decide_eq_true_iff]; exact hP⟩,
        nuPart_entry p⟩)
  have hp2 : (((σ.filter P).image fun p => p.1.2).words).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  exact hperm.eq_of_pairwise' (hL.imp le_of_lt) hp2

/-! ### The far tree -/

theorem stp_fun {n : ℕ} (G : Lax185574.PartialGraphs.PartialGraph (Fin n)) (k q : ℕ) :
    ∀ p ∈ stp G k q, ∀ p' ∈ stp G k q, p.1 = p'.1 → p = p' := by
  intro p hp p' hp' h
  rw [mem_stp] at hp hp'
  exact Prod.ext h (by rw [hp.2, hp'.2, h])

theorem xg_entry (p : (ℕ × TypeTree) × ℕ) :
    xg (toWord p) 0 = p.1.1 ∧ xg (toWord p) 1 = p.1.2.k ∧ xg (toWord p) 2 = p.1.2.q := by
  rw [toWord_entry, toWord_typeTree]
  exact ⟨rfl, rfl, rfl⟩

/-- **The far tree on words.** On the word of the root of a tree of rank
`(k, q+1)`, with the right answers of the restriction program, the
selected trees of the entries of a scatter type that is a function are
the word list of the far tree `farTreeNode`. -/
theorem farList_eq {k q ℓ : ℕ} {X : List ℕ} {t : Node (q + 1) ℓ} {rest : List ℕ}
    {Ans : List (List ℕ)} (hx : X.drop 0 = toWord t ++ rest) (hA : AnsOK k q ℓ t Ans)
    (σ : Finset ((ℕ × TypeTree) × ℕ)) (hfun : ∀ p ∈ σ, ∀ p' ∈ σ, p.1 = p'.1 → p = p') :
    farList X Ans k q ℓ σ.words = (farTreeNode k q ℓ t σ).words := by
  have hρ := radW_root hx (rhoMinus (k + 1) q)
  unfold farList farTreeNode
  simp only []
  rw [hρ]
  refine words_filter_image σ hfun _ (4 * findRadius t (rhoMinus (k + 1) q)) (fun p _ hp => hp.1) _
    fun p _ => ?_
  obtain ⟨h0, h1, h2⟩ := xg_entry p
  rw [selW, h0, h1, h2, nuPart_entry, lastE_entry, inNW_eq hx hA,
    cntW_eq hx hA p.1.2 (canonBlock t (4 * findRadius t (rhoMinus (k + 1) q) - 2 * rhoMinus (k + 1) q))
      _ (fun j => canonW_root hx _ j)]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_iff, and_assoc]

end Lax185574Proofs.FarRam
