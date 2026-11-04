import Lax185574Proofs.Conversions.Ram.MergeSpec
import Lax185574Proofs.Conversions.Ram.Output

/-!
The words of graphs and partitions on `Fin n`, in the form in which the
programs write them.

A graph is written as `n` followed, for every vertex in order, by its
degree and the frames of its neighbors in increasing order. A partition
is written as the number of its parts followed by the frames of the
words of its parts in the order of these words: by size, and among
parts of equal size by least vertex.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax185574.WordEncoding Lax185574.Partitions
open Lax185574Proofs.Words Lax185574Proofs.Conversions.MergeConstruction

variable {n : ℕ}

theorem ofFn_eq_range_map {α : Type*} (n : ℕ) (g : ℕ → α) :
    List.ofFn (fun v : Fin n => g v) = (List.range n).map g := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

/-- A finite set of vertices given by a predicate on numbers. -/
theorem sortedVals_eq_below (A : Finset (Fin n)) (p : ℕ → Prop)
    (hA : ∀ u : Fin n, u ∈ A ↔ p u) : sortedVals A = below n p := by
  refine List.SortedLT.eq_of_mem_iff (sortedVals_pairwise A).sortedLT
    (below_pairwise n p).sortedLT fun w => ?_
  rw [mem_sortedVals, mem_below]
  constructor
  · rintro ⟨h, hw⟩; exact ⟨h, (hA _).mp hw⟩
  · rintro ⟨h, hw⟩; exact ⟨h, (hA ⟨w, h⟩).mpr hw⟩

/-- The word a program writes for the neighborhoods `N v`. -/
noncomputable def graphWord (n : ℕ) (N : ℕ → ℕ → Prop) : List ℕ :=
  n :: (List.range n).flatMap fun v => (below n (N v)).length :: elemFrames (below n (N v))

/-- **The word of a graph.** -/
theorem toWord_graph (R : SimpleGraph (Fin n)) : toWord R = graphWord n (gA R) := by
  classical
  change toWord (List.ofFn fun v : Fin n => Finset.univ.filter (R.Adj v)) = _
  let g : ℕ → Finset (Fin n) := fun v => if h : v < n then Finset.univ.filter (R.Adj ⟨v, h⟩) else ∅
  have hg : (fun v : Fin n => Finset.univ.filter (R.Adj v)) = fun v : Fin n => g v := by
    funext v; simp [g, v.2]
  have hgw : ∀ v ∈ List.range n, toWord (g v) =
      (below n (gA R v)).length :: elemFrames (below n (gA R v)) := by
    intro v hv
    have hvn : v < n := List.mem_range.mp hv
    have hs : sortedVals (g v) = below n (gA R v) :=
      sortedVals_eq_below _ _ fun u => by simp [g, hvn, gA]
    rw [toWord_finset_fin, hs, ← length_sortedVals, hs]
  rw [hg, ofFn_eq_range_map]
  change (List.map g (List.range n)).length :: ((List.map g (List.range n)).map toWord).flatten = _
  simp only [List.length_map, List.length_range, graphWord, List.map_map, List.flatMap]
  congr 1
  congr 1
  exact List.map_congr_left fun v hv => hgw v hv

/-- The members of the part with least vertex `r`, for labels `q`. -/
noncomputable def members (n : ℕ) (q : ℕ → ℕ) (r : ℕ) : List ℕ := below n fun v => q v = r

/-- The word of the part with least vertex `r`. -/
noncomputable def partWord (n : ℕ) (q : ℕ → ℕ) (r : ℕ) : List ℕ :=
  (members n q r).length :: elemFrames (members n q r)

/-- The frames a program writes for the parts with labels `q`: by size
`k`, and for each size by least vertex. -/
noncomputable def partsOut (n : ℕ) (q : ℕ → ℕ) : List ℕ :=
  (List.range (n + 1)).flatMap fun k => (List.range n).flatMap fun r =>
    open Classical in
    if q r = r ∧ (members n q r).length = k then
      (2 * k + 1) :: k :: elemFrames (members n q r) else []

/-- The sorted list of the words of the parts. -/
noncomputable def partsList (n : ℕ) (q : ℕ → ℕ) : List (List ℕ) :=
  (List.range (n + 1)).flatMap fun k => (List.range n).flatMap fun r =>
    open Classical in
    if q r = r ∧ (members n q r).length = k then [partWord n q r] else []

theorem length_partWord (q : ℕ → ℕ) (r : ℕ) :
    (partWord n q r).length = 2 * (members n q r).length + 1 := by
  simp [partWord, length_elemFrames]

theorem frames_flatMap {α : Type*} (l : List α) (f : α → List (List ℕ)) :
    frames (l.flatMap f) = l.flatMap fun a => frames (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, ← ih]; simp [frames]

theorem frames_partsList (q : ℕ → ℕ) : frames (partsList n q) = partsOut n q := by
  classical
  simp only [partsList, partsOut, frames_flatMap]
  refine List.flatMap_congr fun k _ => List.flatMap_congr fun r _ => ?_
  split
  · rename_i h
    simp only [frames, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, length_partWord, h.2]
    simp [partWord, h.2]
  · rfl

theorem below_eq_cons {p : ℕ → Prop} {r : ℕ} (hr : r < n) (hp : p r)
    (hmin : ∀ v < n, p v → r ≤ v) : ∃ t, below n p = r :: t := by
  have hmem : r ∈ below n p := mem_below.mpr ⟨hr, hp⟩
  have hpw := below_pairwise n p
  rcases h : below n p with _ | ⟨a, t⟩
  · rw [h] at hmem; simp at hmem
  · rw [h] at hmem hpw
    have ha : a ∈ below n p := by rw [h]; simp
    obtain ⟨han, hpa⟩ := mem_below.mp ha
    have hra := hmin a han hpa
    rcases List.mem_cons.mp hmem with rfl | hrt
    · exact ⟨t, rfl⟩
    · have := List.rel_of_pairwise_cons hpw hrt
      omega

theorem length_below_le (n : ℕ) (p : ℕ → Prop) : (below n p).length ≤ n := by
  classical
  simp only [below]; exact (List.length_filter_le _ _).trans (by simp)

section Partition

variable (Q : Setoid (Fin n))

theorem repN_le {v : ℕ} (hv : v < n) : repN Q v ≤ v := by
  simp only [repN, dif_pos hv]; exact rep_le Q (Q.refl _)

theorem repN_repN {v : ℕ} (hv : v < n) : repN Q (repN Q v) = repN Q v := by
  have h1 := repN_lt Q hv
  have : repN Q (repN Q v) = repN Q ((⟨repN Q v, h1⟩ : Fin n) : ℕ) := rfl
  rw [this, repN_fin]
  simp only [repN, dif_pos hv]
  rw [Fin.eta, rep_rep]

theorem members_eq_cons {r : ℕ} (hr : r < n) (hq : repN Q r = r) :
    ∃ t, members n (repN Q) r = r :: t :=
  below_eq_cons hr hq fun v hv hqv => by rw [← hqv]; exact repN_le Q hv

theorem partWord_eq_cons {r : ℕ} (hr : r < n) (hq : repN Q r = r) :
    ∃ t, partWord n (repN Q) r = (members n (repN Q) r).length :: 1 :: r :: t := by
  obtain ⟨t, ht⟩ := members_eq_cons Q hr hq
  refine ⟨elemFrames t, ?_⟩
  simp only [partWord]
  rw [ht, elemFrames_cons]

/-- The word of the part of `v`. -/
theorem toWord_class (v : Fin n) :
    toWord (open Classical in Finset.univ.filter fun u => Q u v) = partWord n (repN Q) (repN Q v) := by
  classical
  have hs : sortedVals (Finset.univ.filter fun u => Q u v) = members n (repN Q) (repN Q v) :=
    sortedVals_eq_below _ _ fun u => by simp [repN_eq_iff]
  rw [toWord_finset_fin, ← length_sortedVals, hs]
  rfl

theorem mem_partsList {x : List ℕ} :
    x ∈ partsList n (repN Q) ↔ ∃ r < n, repN Q r = r ∧ x = partWord n (repN Q) r := by
  classical
  simp only [partsList, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, -, r, hr, hx⟩
    split at hx
    · rename_i h; exact ⟨r, hr, h.1, by simpa using hx⟩
    · simp at hx
  · rintro ⟨r, hr, hq, rfl⟩
    refine ⟨(members n (repN Q) r).length, ?_, r, hr, ?_⟩
    · have := length_below_le n (fun v => repN Q v = r); simp only [members]; omega
    · rw [if_pos ⟨hq, rfl⟩]; simp

theorem partWord_lt {r r' : ℕ} (hr : r < n) (hr' : r' < n) (hq : repN Q r = r)
    (hq' : repN Q r' = r')
    (h : (members n (repN Q) r).length < (members n (repN Q) r').length ∨
      ((members n (repN Q) r).length = (members n (repN Q) r').length ∧ r < r')) :
    partWord n (repN Q) r < partWord n (repN Q) r' := by
  obtain ⟨t, ht⟩ := partWord_eq_cons Q hr hq
  obtain ⟨t', ht'⟩ := partWord_eq_cons Q hr' hq'
  rw [ht, ht', List.cons_lt_cons_iff]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, ?_⟩
    rw [List.cons_lt_cons_iff]
    refine Or.inr ⟨rfl, ?_⟩
    rw [List.cons_lt_cons_iff]
    exact Or.inl h2

theorem partsList_pairwise : (partsList n (repN Q)).Pairwise (· < ·) := by
  classical
  simp only [partsList]
  rw [List.pairwise_flatMap]
  refine ⟨fun k _ => ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun r _ => by split <;> simp, ?_⟩
    refine List.pairwise_lt_range.imp_of_mem fun {r r'} hr hr' hrr' => ?_
    intro x hx y hy
    split at hx <;> split at hy <;> simp at hx hy
    rename_i h h'
    subst hx; subst hy
    exact partWord_lt Q (List.mem_range.mp hr) (List.mem_range.mp hr') h.1 h'.1
      (Or.inr ⟨by rw [h.2, h'.2], hrr'⟩)
  · refine List.pairwise_lt_range.imp_of_mem fun {k k'} _ _ hkk' => ?_
    intro x hx y hy
    simp only [List.mem_flatMap, List.mem_range] at hx hy
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨r', hr', hy⟩ := hy
    split at hx <;> split at hy <;> simp at hx hy
    rename_i h h'
    subst hx; subst hy
    exact partWord_lt Q hr hr' h.1 h'.1 (Or.inl (by rw [h.2, h'.2]; exact hkk'))

theorem words_parts : Finset.words (parts Q) = partsList n (repN Q) := by
  classical
  have hpw := partsList_pairwise Q
  have hnd : (partsList n (repN Q)).Nodup := hpw.imp (fun h => ne_of_lt h)
  have hset : (parts Q).image toWord = (partsList n (repN Q)).toFinset := by
    ext x
    simp only [parts, Finset.image_image, Finset.mem_image, Finset.mem_univ, true_and,
      List.mem_toFinset, mem_partsList]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨repN Q v, repN_lt Q v.2, repN_repN Q v.2, ?_⟩
      simp only [Function.comp]
      convert toWord_class Q v
    · rintro ⟨r, hr, hq, rfl⟩
      refine ⟨⟨r, hr⟩, ?_⟩
      simp only [Function.comp]
      convert toWord_class Q ⟨r, hr⟩ using 2
      simp [hq]
  unfold Finset.words
  rw [hset]
  exact (List.toFinset_sort (· ≤ ·) hnd).mpr (hpw.imp fun h => le_of_lt h)

theorem length_partsList :
    (partsList n (repN Q)).length = (below n fun r => repN Q r = r).length := by
  classical
  have hpw := partsList_pairwise Q
  have hnd : (partsList n (repN Q)).Nodup := hpw.imp (fun h => ne_of_lt h)
  have hinj : ∀ r ∈ below n (fun r => repN Q r = r), ∀ r' ∈ below n (fun r => repN Q r = r),
      partWord n (repN Q) r = partWord n (repN Q) r' → r = r' := by
    intro r hr r' hr' he
    obtain ⟨hrn, hq⟩ := mem_below.mp hr
    obtain ⟨hrn', hq'⟩ := mem_below.mp hr'
    obtain ⟨t, ht⟩ := partWord_eq_cons Q hrn hq
    obtain ⟨t', ht'⟩ := partWord_eq_cons Q hrn' hq'
    rw [ht, ht'] at he
    have := congrArg (fun l => l[2]?) he
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at this
    exact this
  have hnd2 : ((below n fun r => repN Q r = r).map (partWord n (repN Q))).Nodup :=
    List.Nodup.map_on hinj ((below_pairwise n _).imp fun h => ne_of_lt h)
  have hfs : (partsList n (repN Q)).toFinset =
      ((below n fun r => repN Q r = r).map (partWord n (repN Q))).toFinset := by
    ext x
    simp only [List.mem_toFinset, mem_partsList, List.mem_map, mem_below]
    constructor
    · rintro ⟨r, hr, hq, rfl⟩; exact ⟨r, ⟨hr, hq⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hq⟩, rfl⟩; exact ⟨r, hr, hq, rfl⟩
  rw [← List.toFinset_card_of_nodup hnd, hfs, List.toFinset_card_of_nodup hnd2, List.length_map]

/-- **The word of a partition**, as a program writes it. -/
theorem toWord_setoid : toWord Q = (below n fun r => repN Q r = r).length :: partsOut n (repN Q) := by
  change toWord (Finset.words (parts Q)) = _
  rw [toWord_words, words_parts, length_partsList, frames_partsList]

end Partition

end Lax185574Proofs.Conversions.Ram
