import Lax235315Proofs.Construction.NeighborScan
import Lax808846Proofs.Lib.Stack
import Lax808846Proofs.Lib.Trail
import Mathlib.Tactic

/-! Finite counting identities behind a partition-refinement pass. -/

namespace Lax235315Proofs.Construction.MarkingMath

open Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib

/-- Vertices selected by a zero-one activity array. -/
def activeVertices (n : ℕ) (active : ℕ → ℕ) : Finset ℕ :=
  (Finset.range n).filter fun v => active v = 1

/-- Classes met by a finite set of vertices. -/
def touchedClasses (label : ℕ → ℕ) (M : Finset ℕ) : Finset ℕ :=
  M.image label

/-- Number of vertices of `M` carrying class `q`. -/
def classMultiplicity (label : ℕ → ℕ) (M : Finset ℕ) (q : ℕ) : ℕ :=
  (M.filter fun v => label v = q).card

lemma mem_activeVertices {n : ℕ} {active : ℕ → ℕ} {v : ℕ} :
    v ∈ activeVertices n active ↔ v < n ∧ active v = 1 := by
  simp [activeVertices]

lemma mem_touchedClasses {label : ℕ → ℕ} {M : Finset ℕ} {q : ℕ} :
    q ∈ touchedClasses label M ↔ ∃ v ∈ M, label v = q := by
  simp [touchedClasses]

lemma classMultiplicity_le_card (label : ℕ → ℕ) (M : Finset ℕ) (q : ℕ) :
    classMultiplicity label M q ≤ M.card := by
  exact Finset.card_filter_le _ _

@[simp] lemma classMultiplicity_empty (label : ℕ → ℕ) (q : ℕ) :
    classMultiplicity label ∅ q = 0 := by
  simp [classMultiplicity]

/-- Adding a fresh vertex increments exactly its class multiplicity. -/
lemma classMultiplicity_insert {label : ℕ → ℕ} {M : Finset ℕ} {v q : ℕ}
    (hv : v ∉ M) :
    classMultiplicity label (insert v M) q =
      if label v = q then classMultiplicity label M q + 1
      else classMultiplicity label M q := by
  by_cases hq : label v = q
  · rw [classMultiplicity, Finset.filter_insert]
    simp [hq, hv]
    rfl
  · rw [classMultiplicity, Finset.filter_insert]
    simp [hq]
    rfl

@[simp] lemma touchedClasses_empty (label : ℕ → ℕ) :
    touchedClasses label ∅ = ∅ := by
  simp [touchedClasses]

lemma touchedClasses_insert (label : ℕ → ℕ) (M : Finset ℕ) (v : ℕ) :
    touchedClasses label (insert v M) =
      insert (label v) (touchedClasses label M) := by
  simp [touchedClasses, Finset.image_insert]

/-- The occupied prefix of a scratch array enumerates a finite set without
duplicates. -/
def PrefixEnumerates (height : ℕ) (entry : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  (Stack.toList height entry).Nodup ∧
    ∀ v, v ∈ Stack.toList height entry ↔ v ∈ S

lemma PrefixEnumerates.of_list_prefix
    {height : ℕ} {entry : ℕ → ℕ} {xs : List ℕ}
    (hheight : height ≤ xs.length)
    (hentry : ∀ i < height, entry i = xs.getD i 0)
    (hxs : xs.Nodup) :
    PrefixEnumerates height entry (xs.take height).toFinset := by
  have hlist : Stack.toList height entry = xs.take height := by
    apply List.ext_getElem
    · simp [Stack.toList, hheight]
    · intro i hi hi'
      have hih : i < height := by simpa [Stack.toList] using hi
      have hix : i < xs.length := hih.trans_le hheight
      simp only [Stack.toList, arrOf, List.getElem_map, List.getElem_range]
      rw [hentry i hih]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix]
  rw [PrefixEnumerates, hlist]
  exact ⟨hxs.take, by simp⟩

lemma PrefixEnumerates.injective_on_prefix
    {height : ℕ} {entry : ℕ → ℕ} {S : Finset ℕ}
    (h : PrefixEnumerates height entry S) :
    ∀ i < height, ∀ j < height, entry i = entry j → i = j := by
  intro i hi j hj hij
  have hi' : i < (Stack.toList height entry).length := by simpa
  have hj' : j < (Stack.toList height entry).length := by simpa
  apply (h.1.getElem_inj_iff (hi := hi') (hj := hj')).mp
  simpa [Stack.toList, hi, hj] using hij

@[simp] lemma prefixEnumerates_zero (entry : ℕ → ℕ) :
    PrefixEnumerates 0 entry ∅ := by
  simp [PrefixEnumerates]

/-- Recording a fresh entry extends the represented finite set by insertion. -/
lemma PrefixEnumerates.push {height : ℕ} {entry : ℕ → ℕ}
    {S : Finset ℕ} (h : PrefixEnumerates height entry S)
    {v : ℕ} (hv : v ∉ S) :
    PrefixEnumerates (height + 1) (upd entry height v) (insert v S) := by
  rw [PrefixEnumerates, Stack.toList_push]
  constructor
  · rw [List.nodup_append]
    refine ⟨h.1, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    apply hv
    apply (h.2 v).mp
    simpa [hab, hb] using ha
  · intro u
    rw [List.mem_append, h.2]
    simp [or_comm]

/-- Scratch-array effect of recording a class only on its first occurrence. -/
def updateTouched (label : ℕ → ℕ) (M : Finset ℕ)
    (touched : ℕ → ℕ) (v : ℕ) : ℕ → ℕ :=
  if label v ∈ touchedClasses label M then touched
  else upd touched (touchedClasses label M).card (label v)

lemma prefixEnumerates_updateTouched {label touched : ℕ → ℕ}
    {M : Finset ℕ} {v : ℕ}
    (h : PrefixEnumerates (touchedClasses label M).card touched
      (touchedClasses label M)) :
    PrefixEnumerates (touchedClasses label (insert v M)).card
      (updateTouched label M touched v)
      (touchedClasses label (insert v M)) := by
  rw [touchedClasses_insert]
  by_cases hv : label v ∈ touchedClasses label M
  · have hins : insert (label v) (touchedClasses label M) =
        touchedClasses label M := Finset.insert_eq_self.mpr hv
    simp [updateTouched, hv, hins, h]
  · have hcard : (insert (label v) (touchedClasses label M)).card =
        (touchedClasses label M).card + 1 := Finset.card_insert_of_notMem hv
    rw [hcard]
    simpa [updateTouched, hv] using h.push hv

lemma upd_eq_token_iff_insert {stamp : ℕ → ℕ} {M : Finset ℕ}
    {v token u : ℕ} (hold : stamp u = token ↔ u ∈ M) :
    upd stamp v token u = token ↔ u ∈ insert v M := by
  by_cases huv : u = v
  · simp [upd, huv]
  · simp [upd, huv, hold]

/-- Updating the numeric counter at the inserted vertex's class realizes
all new class multiplicities. -/
lemma updateMultiplicity {label counts : ℕ → ℕ} {M : Finset ℕ}
    {v : ℕ} (hv : v ∉ M)
    (hcounts : ∀ q, counts q = classMultiplicity label M q) (q : ℕ) :
    upd counts (label v) (counts (label v) + 1) q =
      classMultiplicity label (insert v M) q := by
  rw [classMultiplicity_insert hv]
  by_cases hq : label v = q
  · subst q
    simp [upd, hcounts]
  · have hq' : q ≠ label v := Ne.symm hq
    simp [upd, hq, hq', hcounts]

lemma classMultiplicity_pos_iff {label : ℕ → ℕ} {M : Finset ℕ} {q : ℕ} :
    0 < classMultiplicity label M q ↔ q ∈ touchedClasses label M := by
  constructor
  · intro h
    have hne : (M.filter fun v => label v = q).Nonempty := by
      exact Finset.card_pos.mp h
    obtain ⟨v, hv⟩ := hne
    have hv' := Finset.mem_filter.mp hv
    exact mem_touchedClasses.mpr ⟨v, hv'.1, hv'.2⟩
  · intro h
    obtain ⟨v, hvM, hvq⟩ := mem_touchedClasses.mp h
    apply Finset.card_pos.mpr
    exact ⟨v, Finset.mem_filter.mpr ⟨hvM, hvq⟩⟩

/-- Exact class sizes of the currently active vertices. -/
def ClassSizes (n classCount : ℕ) (active label size : ℕ → ℕ) : Prop :=
  (∀ v < n, active v = 1 → label v < classCount) ∧
  ∀ q < classCount,
    size q = classMultiplicity label (activeVertices n active) q

/-- Every number below `classCount` is the label of an active vertex.  This
is the compactness property maintained by the refinement implementation. -/
def LabelsOccupyPrefix (classCount : ℕ) (label : ℕ → ℕ)
    (A : Finset ℕ) : Prop :=
  ∀ q < classCount, 0 < classMultiplicity label A q

/-- The class multiplicities over a prefix containing every label partition
the underlying finite set. -/
lemma sum_classMultiplicity_of_bounded
    {classCount : ℕ} {label : ℕ → ℕ} {A : Finset ℕ}
    (hlabel : ∀ v ∈ A, label v < classCount) :
    ∑ q ∈ Finset.range classCount, classMultiplicity label A q = A.card := by
  have hfilter : A.filter (fun v => label v ∈ Finset.range classCount) = A := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    simpa using hlabel v hv
  have h := Finset.sum_card_fiberwise_eq_card_filter
    A (Finset.range classCount) label
  rw [hfilter] at h
  simpa only [classMultiplicity] using h

/-- At most one new label is allocated for each old class that has both a
marked and an unmarked vertex.  Compactness therefore leaves enough cells in
the length-`n` class arrays for all allocations. -/
lemma compact_split_capacity
    {classCount : ℕ} {label size counts : ℕ → ℕ}
    {A M : Finset ℕ}
    (hlabel : ∀ v ∈ A, label v < classCount)
    (hoccupied : LabelsOccupyPrefix classCount label A)
    (hsizes : ∀ q < classCount, size q = classMultiplicity label A q)
    (hM : M ⊆ A)
    (hcounts : ∀ q < classCount, counts q = classMultiplicity label M q) :
    classCount +
        ((touchedClasses label M).filter fun q => counts q < size q).card ≤
      A.card := by
  let P := (touchedClasses label M).filter fun q => counts q < size q
  have hPsub : P ⊆ Finset.range classCount := by
    intro q hq
    obtain ⟨hqTouched, -⟩ := Finset.mem_filter.mp hq
    obtain ⟨v, hvM, rfl⟩ := mem_touchedClasses.mp hqTouched
    exact Finset.mem_range.mpr (hlabel v (hM hvM))
  have hterm : ∀ q ∈ Finset.range classCount,
      1 + (if q ∈ P then 1 else 0) ≤ classMultiplicity label A q := by
    intro q hq
    have hqCount : q < classCount := Finset.mem_range.mp hq
    by_cases hqP : q ∈ P
    · obtain ⟨hqTouched, hpartial⟩ := Finset.mem_filter.mp hqP
      have hpositive : 0 < counts q := by
        rw [hcounts q hqCount]
        exact classMultiplicity_pos_iff.mpr hqTouched
      rw [hsizes q hqCount] at hpartial
      simp [hqP]
      omega
    · simp [hqP]
      exact hoccupied q hqCount
  calc
    classCount + P.card =
        ∑ q ∈ Finset.range classCount, (1 + if q ∈ P then 1 else 0) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      rw [Finset.card_eq_sum_ite hPsub]
    _ ≤ ∑ q ∈ Finset.range classCount, classMultiplicity label A q := by
      exact Finset.sum_le_sum hterm
    _ = A.card := sum_classMultiplicity_of_bounded hlabel

lemma activeVertices_card_le (n : ℕ) (active : ℕ → ℕ) :
    (activeVertices n active).card ≤ n := by
  calc
    (activeVertices n active).card ≤ (Finset.range n).card := by
      apply Finset.card_le_card
      intro v hv
      exact (Finset.mem_filter.mp hv).1
    _ = n := Finset.card_range n

lemma ClassSizes.split_capacity
    {n classCount : ℕ} {active label size counts : ℕ → ℕ}
    (hsizes : ClassSizes n classCount active label size)
    (hoccupied : LabelsOccupyPrefix classCount label (activeVertices n active))
    {M : Finset ℕ} (hM : M ⊆ activeVertices n active)
    (hcounts : ∀ q < classCount, counts q = classMultiplicity label M q) :
    classCount +
        ((touchedClasses label M).filter fun q => counts q < size q).card ≤ n := by
  apply (compact_split_capacity (A := activeVertices n active)
    (M := M) (fun v hv => hsizes.1 v (mem_activeVertices.mp hv).1
      (mem_activeVertices.mp hv).2) hoccupied hsizes.2 hM hcounts).trans
  exact activeVertices_card_le n active

lemma classMultiplicity_mono {label : ℕ → ℕ} {M A : Finset ℕ}
    (hMA : M ⊆ A) (q : ℕ) :
    classMultiplicity label M q ≤ classMultiplicity label A q := by
  apply Finset.card_le_card
  intro v hv
  simp only [classMultiplicity, Finset.mem_filter] at hv ⊢
  exact ⟨hMA hv.1, hv.2⟩

/-- Before a fresh vertex of a class is inserted into the marked set, that
class's marked count is strictly below its full active size. -/
lemma classMultiplicity_lt_size_of_fresh
    {n classCount : ℕ} {active label size : ℕ → ℕ}
    (hsizes : ClassSizes n classCount active label size)
    {M : Finset ℕ} (hM : M ⊆ activeVertices n active)
    {v : ℕ} (hvA : v ∈ activeVertices n active) (hvM : v ∉ M) :
    classMultiplicity label M (label v) < size (label v) := by
  have hlabel : label v < classCount :=
    hsizes.1 v (mem_activeVertices.mp hvA).1 (mem_activeVertices.mp hvA).2
  rw [hsizes.2 (label v) hlabel]
  let F := (activeVertices n active).filter fun u => label u = label v
  have hsub : (M.filter fun u => label u = label v) ⊆ F := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨hM (Finset.mem_filter.mp hu).1,
      (Finset.mem_filter.mp hu).2⟩
  have hvF : v ∈ F := by simp [F, hvA]
  have hvnot : v ∉ M.filter fun u => label u = label v := by simp [hvM]
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun heq => hvnot (heq ▸ hvF)⟩)

end Lax235315Proofs.Construction.MarkingMath
