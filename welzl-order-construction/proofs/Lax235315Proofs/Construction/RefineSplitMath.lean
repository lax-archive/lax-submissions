import Lax235315Proofs.Construction.MarkingMath
import Mathlib.Tactic

/-! The finite-set correctness certificate for the class-splitting half of
`refineOne`. -/

namespace Lax235315Proofs.Construction.RefineSplitMath

open Lax235315Proofs.Construction.MarkingMath
open Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib

/-- The label after marked vertices have been moved according to `split`.
Unmarked vertices retain their old compact class. -/
def refinedLabel (M : Finset ℕ) (label split : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v ∈ M then split (label v) else label v

/-- Intermediate label function while the marked stack is being replayed. -/
def partiallyRefinedLabel (processed : Finset ℕ)
    (label split : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v ∈ processed then split (label v) else label v

lemma update_partiallyRefinedLabel
    {processed : Finset ℕ} {label split : ℕ → ℕ} {v : ℕ}
    (hv : v ∉ processed) :
    upd (partiallyRefinedLabel processed label split) v (split (label v)) =
      partiallyRefinedLabel (insert v processed) label split := by
  funext u
  by_cases huv : u = v
  · subst u
    simp [upd, partiallyRefinedLabel]
  · simp [upd, partiallyRefinedLabel, huv]

lemma partiallyRefinedLabel_eq_refinedLabel
    (M : Finset ℕ) (label split : ℕ → ℕ) :
    partiallyRefinedLabel M label split = refinedLabel M label split := rfl

/-- Intermediate counter function while touched class counters are reset. -/
def partiallyCleared (processed : Finset ℕ) (counts : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q ∈ processed then 0 else counts q

@[simp] lemma partiallyRefinedLabel_empty (label split : ℕ → ℕ) :
    partiallyRefinedLabel ∅ label split = label := by
  funext v
  simp [partiallyRefinedLabel]

@[simp] lemma partiallyCleared_empty (counts : ℕ → ℕ) :
    partiallyCleared ∅ counts = counts := by
  funext v
  simp [partiallyCleared]

lemma update_partiallyCleared
    {processed : Finset ℕ} {counts : ℕ → ℕ} {q : ℕ}
    (hq : q ∉ processed) :
    upd (partiallyCleared processed counts) q 0 =
      partiallyCleared (insert q processed) counts := by
  funext r
  by_cases hrq : r = q
  · subst r
    simp [upd, partiallyCleared]
  · simp [upd, partiallyCleared, hrq]

/-- What the split-allocation loop must establish.  A partially marked old
class receives a distinct fresh label; a fully marked class keeps its old
label. -/
def ValidSplits (classCount : ℕ) (touched : Finset ℕ)
    (counts size split : ℕ → ℕ) : Prop :=
  (∀ q ∈ touched, counts q < size q → classCount ≤ split q) ∧
  (∀ q ∈ touched, size q ≤ counts q → split q = q) ∧
  ∀ q ∈ touched, counts q < size q →
    ∀ r ∈ touched, counts r < size r →
      (split q = split r ↔ q = r)

/-- Classes in the occupied prefix of the touched stack. -/
def processedClasses (i : ℕ) (entry : ℕ → ℕ) : Finset ℕ :=
  (Stack.toList i entry).toFinset

@[simp] lemma processedClasses_succ (i : ℕ) (entry : ℕ → ℕ) :
    processedClasses (i + 1) entry = insert (entry i) (processedClasses i entry) := by
  simp [processedClasses, Stack.toList_succ]

lemma toList_prefix {i height : ℕ} (entry : ℕ → ℕ) (hi : i ≤ height) :
    Stack.toList i entry = (Stack.toList height entry).take i := by
  simp only [Stack.toList, arrOf, ← List.map_take, List.take_range,
    Nat.min_eq_left hi]

/-- In a duplicate-free touched stack, the next entry belongs to the
represented set and has not occurred in the processed prefix. -/
lemma PrefixEnumerates.next_mem_not_processed
    {height i : ℕ} {entry : ℕ → ℕ} {S : Finset ℕ}
    (h : PrefixEnumerates height entry S) (hi : i < height) :
    entry i ∈ S ∧ entry i ∉ processedClasses i entry := by
  have hprefix : Stack.toList (i + 1) entry =
      (Stack.toList height entry).take (i + 1) :=
    toList_prefix entry (by omega)
  have hnodup : (Stack.toList (i + 1) entry).Nodup := by
    rw [hprefix]
    exact h.1.take
  have hdecomp : Stack.toList (i + 1) entry =
      Stack.toList i entry ++ [entry i] := Stack.toList_succ i entry
  have hnot : entry i ∉ Stack.toList i entry := by
    rw [hdecomp, List.nodup_append] at hnodup
    intro hmem
    exact (hnodup.2.2 (entry i) hmem (entry i) (by simp)) rfl
  constructor
  · apply (h.2 (entry i)).mp
    exact List.mem_map.mpr ⟨i, by simp [hi], rfl⟩
  · simpa [processedClasses] using hnot

lemma PrefixEnumerates.processedClasses_subset
    {height i : ℕ} {entry : ℕ → ℕ} {S : Finset ℕ}
    (h : PrefixEnumerates height entry S) (hi : i ≤ height) :
    processedClasses i entry ⊆ S := by
  intro q hq
  apply (h.2 q).mp
  have hprefix := toList_prefix entry hi
  have hqList : q ∈ Stack.toList i entry := by
    simpa [processedClasses] using hq
  rw [hprefix] at hqList
  exact List.mem_of_mem_take hqList

lemma PrefixEnumerates.processedClasses_eq
    {height : ℕ} {entry : ℕ → ℕ} {S : Finset ℕ}
    (h : PrefixEnumerates height entry S) :
    processedClasses height entry = S := by
  ext q
  simpa [processedClasses] using h.2 q

/-- A loop certificate for allocating compact labels.  The current class
counter is the old counter plus the number of partial classes already seen;
their allocated labels are fresh, bounded by the current counter, and
pairwise distinct. -/
def SplitPrefix (base current : ℕ) (processed : Finset ℕ)
    (counts size split : ℕ → ℕ) : Prop :=
  current = base + (processed.filter fun q => counts q < size q).card ∧
  (∀ q ∈ processed, counts q < size q →
    base ≤ split q ∧ split q < current) ∧
  (∀ q ∈ processed, size q ≤ counts q → split q = q) ∧
  ∀ q ∈ processed, counts q < size q →
    ∀ r ∈ processed, counts r < size r →
      (split q = split r ↔ q = r)

/-- Exact class sizes maintained alongside a prefix of allocated splits. -/
def SplitSizes (processed : Finset ℕ) (counts oldSize split workSize : ℕ → ℕ) :
    Prop :=
  (∀ q ∈ processed, counts q < oldSize q →
    workSize q = oldSize q - counts q ∧ workSize (split q) = counts q) ∧
  ∀ q ∈ processed, oldSize q ≤ counts q → workSize q = oldSize q

lemma splitSizes_empty (counts oldSize split workSize : ℕ → ℕ) :
    SplitSizes ∅ counts oldSize split workSize := by
  simp [SplitSizes]

lemma SplitSizes.insert_partial
    {base current q : ℕ} {processed : Finset ℕ}
    {counts oldSize split workSize : ℕ → ℕ}
    (hp : SplitPrefix base current processed counts oldSize split)
    (hs : SplitSizes processed counts oldSize split workSize)
    (hrange : ∀ r ∈ insert q processed, r < base)
    (hq : q ∉ processed) (hpartial : counts q < oldSize q) :
    SplitSizes (insert q processed) counts oldSize (upd split q current)
      (upd (upd workSize current (counts q)) q (oldSize q - counts q)) := by
  have hbaseCurrent : base ≤ current := by rw [hp.1]; omega
  have hqCurrent : q ≠ current := by
    have := hrange q (by simp)
    omega
  rcases hs with ⟨hpartialOld, hfullOld⟩
  constructor
  · intro r hr hrpartial
    by_cases hrq : r = q
    · subst r
      constructor
      · simp [upd]
      · simp [upd, Ne.symm hqCurrent]
    · have hrP : r ∈ processed := by simpa [hrq] using hr
      obtain ⟨hrSize, hrFresh⟩ := hpartialOld r hrP hrpartial
      have hrCurrent : r ≠ current := by
        have := hrange r (by simp [hrP])
        omega
      have hrsplitRange := (hp.2.1 r hrP hrpartial)
      have hrsplitCurrent : split r ≠ current := by omega
      have hrsplitq : split r ≠ q := by
        have hqBase := hrange q (by simp)
        omega
      simp [upd, hrq, hrCurrent, hrsplitCurrent, hrsplitq, hrSize, hrFresh]
  · intro r hr hrfull
    have hrq : r ≠ q := by
      intro heq
      subst r
      omega
    have hrP : r ∈ processed := by simpa [hrq] using hr
    have hrCurrent : r ≠ current := by
      have := hrange r (by simp [hrP])
      omega
    simp [upd, hrq, hrCurrent, hfullOld r hrP hrfull]

lemma SplitSizes.insert_full
    {q : ℕ} {processed : Finset ℕ}
    {counts oldSize split workSize : ℕ → ℕ}
    (hs : SplitSizes processed counts oldSize split workSize)
    (hq : q ∉ processed) (hfullq : oldSize q ≤ counts q)
    (hqSize : workSize q = oldSize q) :
    SplitSizes (insert q processed) counts oldSize (upd split q q) workSize := by
  rcases hs with ⟨hpartialOld, hfullOld⟩
  constructor
  · intro r hr hrpartial
    have hrq : r ≠ q := by
      intro heq
      subst r
      omega
    have hrP : r ∈ processed := by simpa [hrq] using hr
    simpa [upd, hrq] using hpartialOld r hrP hrpartial
  · intro r hr hrfull
    by_cases hrq : r = q
    · subst r
      exact hqSize
    · exact hfullOld r (by simpa [hrq] using hr) hrfull

lemma splitPrefix_empty (base : ℕ) (counts size split : ℕ → ℕ) :
    SplitPrefix base base ∅ counts size split := by
  simp [SplitPrefix]

/-- Allocating the current counter to one previously unprocessed partial
class extends the compact-label certificate. -/
lemma SplitPrefix.insert_partial
    {base current q : ℕ} {processed : Finset ℕ}
    {counts size split : ℕ → ℕ}
    (h : SplitPrefix base current processed counts size split)
    (hq : q ∉ processed) (hpartial : counts q < size q) :
    SplitPrefix base (current + 1) (insert q processed) counts size
      (upd split q current) := by
  rcases h with ⟨hcurrent, hrange, hfull, hinj⟩
  have hfilter :
      (insert q processed).filter (fun r => counts r < size r) =
        insert q (processed.filter fun r => counts r < size r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_insert]
    by_cases hrq : r = q
    · subst r
      simp [hpartial]
    · simp [hrq]
  have hqfilter : q ∉ processed.filter (fun r => counts r < size r) := by
    simp [hq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfilter, Finset.card_insert_of_notMem hqfilter, hcurrent]
    omega
  · intro r hr hpart
    by_cases hrq : r = q
    · subst r
      simp [upd]
      omega
    · have hrP : r ∈ processed := by
        simpa [hrq] using hr
      have hrange' := hrange r hrP hpart
      simp [upd, hrq]
      omega
  · intro r hr hnotpart
    by_cases hrq : r = q
    · subst r
      omega
    · have hrP : r ∈ processed := by
        simpa [hrq] using hr
      simp [upd, hrq, hfull r hrP hnotpart]
  · intro r hr hpart s hs hspart
    by_cases hrq : r = q
    · subst r
      by_cases hsq : s = q
      · simp [hsq]
      · have hsP : s ∈ processed := by simpa [hsq] using hs
        have hslt := (hrange s hsP hspart).2
        simp [upd, hsq]
        omega
    · have hrP : r ∈ processed := by simpa [hrq] using hr
      by_cases hsq : s = q
      · subst s
        have hrlt := (hrange r hrP hpart).2
        simp [upd, hrq]
        omega
      · have hsP : s ∈ processed := by simpa [hsq] using hs
        simpa [upd, hrq, hsq] using hinj r hrP hpart s hsP hspart

/-- A fully marked class retains its old label and does not consume a new
class number. -/
lemma SplitPrefix.insert_full
    {base current q : ℕ} {processed : Finset ℕ}
    {counts size split : ℕ → ℕ}
    (h : SplitPrefix base current processed counts size split)
    (hq : q ∉ processed) (hfullq : size q ≤ counts q) :
    SplitPrefix base current (insert q processed) counts size
      (upd split q q) := by
  rcases h with ⟨hcurrent, hrange, hfull, hinj⟩
  have hnotpartial : ¬ counts q < size q := by omega
  have hfilter :
      (insert q processed).filter (fun r => counts r < size r) =
        processed.filter fun r => counts r < size r := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_insert]
    by_cases hrq : r = q
    · subst r
      simp [hnotpartial]
    · simp [hrq]
  refine ⟨by simpa [hfilter] using hcurrent, ?_, ?_, ?_⟩
  · intro r hr hpart
    have hrq : r ≠ q := by
      intro heq
      subst r
      omega
    have hrP : r ∈ processed := by simpa [hrq] using hr
    simpa [upd, hrq] using hrange r hrP hpart
  · intro r hr hfullr
    by_cases hrq : r = q
    · subst r
      simp [upd]
    · have hrP : r ∈ processed := by simpa [hrq] using hr
      simpa [upd, hrq] using hfull r hrP hfullr
  · intro r hr hpart s hs hspart
    have hrq : r ≠ q := by
      intro heq
      subst r
      omega
    have hsq : s ≠ q := by
      intro heq
      subst s
      omega
    have hrP : r ∈ processed := by simpa [hrq] using hr
    have hsP : s ∈ processed := by simpa [hsq] using hs
    simpa [upd, hrq, hsq] using hinj r hrP hpart s hsP hspart

lemma SplitPrefix.validSplits
    {base current : ℕ} {touched : Finset ℕ}
    {counts size split : ℕ → ℕ}
    (h : SplitPrefix base current touched counts size split) :
    ValidSplits base touched counts size split := by
  rcases h with ⟨-, hrange, hfull, hinj⟩
  exact ⟨fun q hq hp => (hrange q hq hp).1, hfull, hinj⟩

lemma SplitPrefix.current_le
    {base current : ℕ} {processed total : Finset ℕ}
    {counts size split : ℕ → ℕ}
    (h : SplitPrefix base current processed counts size split)
    (hsub : processed ⊆ total) :
    current ≤ base + (total.filter fun q => counts q < size q).card := by
  rw [h.1]
  apply Nat.add_le_add_left
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter] at hq ⊢
  exact ⟨hsub hq.1, hq.2⟩

lemma SplitPrefix.current_lt_of_unprocessed_partial
    {base current q : ℕ} {processed total : Finset ℕ}
    {counts size split : ℕ → ℕ}
    (h : SplitPrefix base current processed counts size split)
    (hsub : processed ⊆ total) (hq : q ∈ total)
    (hqnot : q ∉ processed) (hpartial : counts q < size q) :
    current < base + (total.filter fun r => counts r < size r).card := by
  rw [h.1]
  apply Nat.add_lt_add_left
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_filter] at hr ⊢
    exact ⟨hsub hr.1, hr.2⟩
  · intro heq
    have hqTotal : q ∈ total.filter fun r => counts r < size r := by
      simp [hq, hpartial]
    have hqProcessed : q ∈ processed.filter fun r => counts r < size r :=
      heq ▸ hqTotal
    exact hqnot (Finset.mem_filter.mp hqProcessed).1

/-- At the end of allocation, the images of the partial old classes are
exactly the consecutive fresh labels. -/
lemma SplitPrefix.image_partial_eq_Ico
    {base current : ℕ} {touched : Finset ℕ}
    {counts size split : ℕ → ℕ}
    (h : SplitPrefix base current touched counts size split) :
    ((touched.filter fun q => counts q < size q).image split) =
      Finset.Ico base current := by
  let P := touched.filter fun q => counts q < size q
  have hsub : P.image split ⊆ Finset.Ico base current := by
    intro r hr
    obtain ⟨q, hqP, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hqTouched, hqPartial⟩ := Finset.mem_filter.mp hqP
    exact Finset.mem_Ico.mpr (h.2.1 q hqTouched hqPartial)
  have hinj : Set.InjOn split P := by
    intro q hq r hr hqr
    obtain ⟨hqTouched, hqPartial⟩ := Finset.mem_filter.mp hq
    obtain ⟨hrTouched, hrPartial⟩ := Finset.mem_filter.mp hr
    exact (h.2.2.2 q hqTouched hqPartial r hrTouched hrPartial).mp hqr
  have hcurrent : current = base + P.card := by
    simpa [P] using h.1
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Nat.card_Ico, Finset.card_image_iff.mpr hinj, hcurrent]
  omega

lemma touched_of_mem {label : ℕ → ℕ} {M : Finset ℕ} {v : ℕ}
    (hv : v ∈ M) : label v ∈ touchedClasses label M := by
  exact mem_touchedClasses.mpr ⟨v, hv, rfl⟩

lemma multiplicity_le_of_subset {label : ℕ → ℕ} {M A : Finset ℕ}
    (hMA : M ⊆ A) (q : ℕ) :
    classMultiplicity label M q ≤ classMultiplicity label A q :=
  classMultiplicity_mono hMA q

/-- The abstract split certificate realizes exactly the binary refinement by
membership in `M`.  This is the core semantic fact consumed by the graph
partition proof. -/
lemma refinedLabel_eq_iff
    {n classCount : ℕ} {active label size counts split : ℕ → ℕ}
    {M : Finset ℕ}
    (hM : M ⊆ activeVertices n active)
    (hlabels : ∀ v < n, active v = 1 → label v < classCount)
    (hsizes : ∀ q < classCount,
      size q = classMultiplicity label (activeVertices n active) q)
    (hcounts : ∀ q < classCount,
      counts q = classMultiplicity label M q)
    (hsplit : ValidSplits classCount (touchedClasses label M)
      counts size split)
    {u v : ℕ} (hu : u ∈ activeVertices n active)
    (hv : v ∈ activeVertices n active) :
    refinedLabel M label split u = refinedLabel M label split v ↔
      label u = label v ∧ (u ∈ M ↔ v ∈ M) := by
  have hulabel : label u < classCount :=
    hlabels u (mem_activeVertices.mp hu).1 (mem_activeVertices.mp hu).2
  have hvlabel : label v < classCount :=
    hlabels v (mem_activeVertices.mp hv).1 (mem_activeVertices.mp hv).2
  have hcountLe (q : ℕ) (hq : q < classCount) : counts q ≤ size q := by
    rw [hcounts q hq, hsizes q hq]
    exact classMultiplicity_mono hM q
  have full_mem (q x : ℕ) (hq : q < classCount)
      (hx : x ∈ activeVertices n active) (hxq : label x = q)
      (hfull : size q ≤ counts q) : x ∈ M := by
    have heq : classMultiplicity label M q =
        classMultiplicity label (activeVertices n active) q := by
      rw [← hcounts q hq, ← hsizes q hq]
      exact Nat.le_antisymm (hcountLe q hq) hfull
    have hsub : (M.filter fun z => label z = q) ⊆
        ((activeVertices n active).filter fun z => label z = q) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨hM (Finset.mem_filter.mp hz).1,
        (Finset.mem_filter.mp hz).2⟩
    have hsets : (M.filter fun z => label z = q) =
        ((activeVertices n active).filter fun z => label z = q) := by
      apply Finset.eq_of_subset_of_card_le hsub
      simpa [classMultiplicity] using heq.ge
    have hxfilter : x ∈
        ((activeVertices n active).filter fun z => label z = q) :=
      Finset.mem_filter.mpr ⟨hx, hxq⟩
    exact (Finset.mem_filter.mp (hsets.symm ▸ hxfilter)).1
  by_cases huM : u ∈ M <;> by_cases hvM : v ∈ M
  · simp only [refinedLabel]
    rw [if_pos huM, if_pos hvM]
    constructor
    · intro heq
      refine ⟨?_, ⟨fun _ => hvM, fun _ => huM⟩⟩
      by_contra huv
      have huTouched := touched_of_mem (label := label) huM
      have hvTouched := touched_of_mem (label := label) hvM
      by_cases hup : counts (label u) < size (label u)
      · by_cases hvp : counts (label v) < size (label v)
        · exact huv ((hsplit.2.2 _ huTouched hup _ hvTouched hvp).mp heq)
        · have hvfull : size (label v) ≤ counts (label v) := by
            omega
          have hvsplit := hsplit.2.1 _ hvTouched hvfull
          have hufresh := hsplit.1 _ huTouched hup
          rw [hvsplit] at heq
          rw [heq] at hufresh
          omega
      · have hufull : size (label u) ≤ counts (label u) := by omega
        have husplit := hsplit.2.1 _ huTouched hufull
        by_cases hvp : counts (label v) < size (label v)
        · have hvfresh := hsplit.1 _ hvTouched hvp
          rw [husplit] at heq
          rw [← heq] at hvfresh
          omega
        · have hvfull : size (label v) ≤ counts (label v) := by omega
          rw [hsplit.2.1 _ huTouched hufull,
            hsplit.2.1 _ hvTouched hvfull] at heq
          exact huv heq
    · rintro ⟨huv, -⟩
      rw [huv]
  · simp only [refinedLabel]
    rw [if_pos huM, if_neg hvM]
    constructor
    · intro heq
      have huTouched := touched_of_mem (label := label) huM
      have hpartial : counts (label u) < size (label u) := by
        by_contra hnot
        have hfull : size (label u) ≤ counts (label u) := by omega
        have husplit := hsplit.2.1 _ huTouched hfull
        have hlabelsEq : label u = label v := by
          simpa [husplit] using heq
        exact hvM (full_mem (label u) v hulabel hv hlabelsEq.symm hfull)
      have hfresh := hsplit.1 _ huTouched hpartial
      rw [heq] at hfresh
      omega
    · rintro ⟨-, hmem⟩
      exact (hvM (hmem.mp huM)).elim
  · simp only [refinedLabel]
    rw [if_neg huM, if_pos hvM]
    constructor
    · intro heq
      have hvTouched := touched_of_mem (label := label) hvM
      have hpartial : counts (label v) < size (label v) := by
        by_contra hnot
        have hfull : size (label v) ≤ counts (label v) := by omega
        have hvsplit := hsplit.2.1 _ hvTouched hfull
        have hlabelsEq : label u = label v := by
          simpa [hvsplit] using heq
        exact huM (full_mem (label v) u hvlabel hu hlabelsEq hfull)
      have hfresh := hsplit.1 _ hvTouched hpartial
      rw [← heq] at hfresh
      omega
    · rintro ⟨-, hmem⟩
      exact (huM (hmem.mpr hvM)).elim
  · simp only [refinedLabel]
    rw [if_neg huM, if_neg hvM]
    constructor
    · intro heq
      exact ⟨heq, ⟨fun h => (huM h).elim, fun h => (hvM h).elim⟩⟩
    · exact fun h => h.1

/-- The refined fiber through an active vertex is its marked part when the
vertex is marked, and its unmarked part otherwise. -/
lemma classMultiplicity_refinedLabel_at
    {n classCount : ℕ} {active label size counts split : ℕ → ℕ}
    {M : Finset ℕ}
    (hM : M ⊆ activeVertices n active)
    (hlabels : ∀ v < n, active v = 1 → label v < classCount)
    (hsizes : ∀ q < classCount,
      size q = classMultiplicity label (activeVertices n active) q)
    (hcounts : ∀ q < classCount,
      counts q = classMultiplicity label M q)
    (hsplit : ValidSplits classCount (touchedClasses label M)
      counts size split)
    {u : ℕ} (hu : u ∈ activeVertices n active) :
    classMultiplicity (refinedLabel M label split) (activeVertices n active)
        (refinedLabel M label split u) =
      if u ∈ M then classMultiplicity label M (label u)
      else classMultiplicity label (activeVertices n active) (label u) -
        classMultiplicity label M (label u) := by
  classical
  let A := activeVertices n active
  by_cases huM : u ∈ M
  · have hfiber :
        A.filter (fun v => refinedLabel M label split v =
          refinedLabel M label split u) =
        M.filter (fun v => label v = label u) := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvA, href⟩ := Finset.mem_filter.mp hv
        have hsem := (refinedLabel_eq_iff hM hlabels hsizes hcounts hsplit
          hvA hu).mp href
        exact Finset.mem_filter.mpr ⟨(hsem.2.mpr huM), hsem.1⟩
      · intro hv
        obtain ⟨hvM, hlabel⟩ := Finset.mem_filter.mp hv
        have hvA := hM hvM
        apply Finset.mem_filter.mpr
        refine ⟨hvA, (refinedLabel_eq_iff hM hlabels hsizes hcounts hsplit
          hvA hu).mpr ⟨hlabel, ?_⟩⟩
        exact ⟨fun _ => huM, fun _ => hvM⟩
    simp only [classMultiplicity]
    rw [hfiber]
    simp [huM]
  · let F := A.filter fun v => label v = label u
    let FM := M.filter fun v => label v = label u
    have hFM : FM ⊆ F := by
      intro v hv
      obtain ⟨hvM, hlabel⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨hM hvM, hlabel⟩
    have hfiber :
        A.filter (fun v => refinedLabel M label split v =
          refinedLabel M label split u) = F \ FM := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvA, href⟩ := Finset.mem_filter.mp hv
        have hsem := (refinedLabel_eq_iff hM hlabels hsizes hcounts hsplit
          hvA hu).mp href
        have hvNot : v ∉ M := by
          intro hvM
          exact huM (hsem.2.mp hvM)
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨hvA, hsem.1⟩, by simp [FM, hvNot]⟩
      · intro hv
        obtain ⟨hvF, hvNotFM⟩ := Finset.mem_sdiff.mp hv
        obtain ⟨hvA, hlabel⟩ := Finset.mem_filter.mp hvF
        have hvNot : v ∉ M := by
          intro hvM
          exact hvNotFM (Finset.mem_filter.mpr ⟨hvM, hlabel⟩)
        apply Finset.mem_filter.mpr
        refine ⟨hvA, (refinedLabel_eq_iff hM hlabels hsizes hcounts hsplit
          hvA hu).mpr ⟨hlabel, ?_⟩⟩
        exact ⟨fun hvM => (hvNot hvM).elim, fun huM' => (huM huM').elim⟩
    simp only [classMultiplicity]
    rw [hfiber, Finset.card_sdiff_of_subset hFM]
    simp [F, FM, A, huM]

/-- A completed compact split preserves the exact size table and occupancy
of the class-label prefix. -/
lemma refinedLabel_classSizes_and_occupancy
    {n base current : ℕ} {active label size counts split workSize : ℕ → ℕ}
    {M : Finset ℕ}
    (hM : M ⊆ activeVertices n active)
    (hsizes : ClassSizes n base active label size)
    (hoccupied : LabelsOccupyPrefix base label (activeVertices n active))
    (hcounts : ∀ q < base, counts q = classMultiplicity label M q)
    (hprefix : SplitPrefix base current (touchedClasses label M)
      counts size split)
    (hsplitSizes : SplitSizes (touchedClasses label M)
      counts size split workSize)
    (hunchanged : ∀ q < base, q ∉ touchedClasses label M →
      workSize q = size q) :
    ClassSizes n current active (refinedLabel M label split) workSize ∧
      LabelsOccupyPrefix current (refinedLabel M label split)
        (activeVertices n active) := by
  classical
  let A := activeVertices n active
  have hbaseCurrent : base ≤ current := by
    rw [hprefix.1]
    omega
  have hlabelA : ∀ v ∈ A, label v < base := by
    intro v hv
    exact hsizes.1 v (mem_activeVertices.mp hv).1
      (mem_activeVertices.mp hv).2
  have hmarked (q : ℕ) (hqTouched : q ∈ touchedClasses label M) :
      ∃ u ∈ A, u ∈ M ∧ label u = q := by
    obtain ⟨u, huM, hulabel⟩ := mem_touchedClasses.mp hqTouched
    exact ⟨u, hM huM, huM, hulabel⟩
  have hunmarked (q : ℕ) (hq : q < base)
      (hpartial : counts q < size q) :
      ∃ u ∈ A, u ∉ M ∧ label u = q := by
    let F := A.filter fun v => label v = q
    let FM := M.filter fun v => label v = q
    have hFM : FM ⊆ F := by
      intro v hv
      obtain ⟨hvM, hvlabel⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨hM hvM, hvlabel⟩
    have hcard : FM.card < F.card := by
      have hpartial' := hpartial
      rw [hcounts q hq, hsizes.2 q hq] at hpartial'
      simpa [FM, F, A, classMultiplicity] using hpartial'
    obtain ⟨u, huF, huNotFM⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    obtain ⟨huA, hulabel⟩ := Finset.mem_filter.mp huF
    have huNotM : u ∉ M := by
      intro huM
      exact huNotFM (Finset.mem_filter.mpr ⟨huM, hulabel⟩)
    exact ⟨u, huA, huNotM, hulabel⟩
  have hvalid : ValidSplits base (touchedClasses label M) counts size split :=
    hprefix.validSplits
  have hcountLe (q : ℕ) (hq : q < base) : counts q ≤ size q := by
    rw [hcounts q hq, hsizes.2 q hq]
    exact classMultiplicity_mono hM q
  have hrepresentative : ∀ q < current,
      ∃ u ∈ A, refinedLabel M label split u = q := by
    intro q hqCurrent
    by_cases hqBase : q < base
    · by_cases hqTouched : q ∈ touchedClasses label M
      · by_cases hpartial : counts q < size q
        · obtain ⟨u, huA, huNotM, hulabel⟩ := hunmarked q hqBase hpartial
          exact ⟨u, huA, by simp [refinedLabel, huNotM, hulabel]⟩
        · have hfull : size q ≤ counts q := by omega
          obtain ⟨u, huA, huM, hulabel⟩ := hmarked q hqTouched
          have hsplitq := hvalid.2.1 q hqTouched hfull
          exact ⟨u, huA, by simp [refinedLabel, huM, hulabel, hsplitq]⟩
      · have hqPositive := hoccupied q hqBase
        obtain ⟨u, huA, hulabel⟩ :=
          mem_touchedClasses.mp (classMultiplicity_pos_iff.mp hqPositive)
        have huNotM : u ∉ M := by
          intro huM
          exact hqTouched (mem_touchedClasses.mpr ⟨u, huM, hulabel⟩)
        exact ⟨u, huA, by simp [refinedLabel, huNotM, hulabel]⟩
    · have hqIco : q ∈ Finset.Ico base current :=
        Finset.mem_Ico.mpr ⟨by omega, hqCurrent⟩
      rw [← hprefix.image_partial_eq_Ico] at hqIco
      obtain ⟨r, hrPartial, hrsplit⟩ := Finset.mem_image.mp hqIco
      obtain ⟨hrTouched, -⟩ := Finset.mem_filter.mp hrPartial
      obtain ⟨u, huA, huM, hulabel⟩ := hmarked r hrTouched
      refine ⟨u, huA, ?_⟩
      simp [refinedLabel, huM, hulabel, hrsplit]
  constructor
  · constructor
    · intro v hvn hvactive
      have hvA : v ∈ A := mem_activeVertices.mpr ⟨hvn, hvactive⟩
      have hvBase := hlabelA v hvA
      by_cases hvM : v ∈ M
      · have htouched : label v ∈ touchedClasses label M :=
          mem_touchedClasses.mpr ⟨v, hvM, rfl⟩
        by_cases hpartial : counts (label v) < size (label v)
        · simp only [refinedLabel, if_pos hvM]
          exact (hprefix.2.1 (label v) htouched hpartial).2
        · have hfull : size (label v) ≤ counts (label v) := by omega
          rw [refinedLabel, if_pos hvM, hvalid.2.1 (label v) htouched hfull]
          exact hvBase.trans_le hbaseCurrent
      · rw [refinedLabel, if_neg hvM]
        exact hvBase.trans_le hbaseCurrent
    · intro q hqCurrent
      by_cases hqBase : q < base
      · by_cases hqTouched : q ∈ touchedClasses label M
        · by_cases hpartial : counts q < size q
          · obtain ⟨u, huA, huNotM, hulabel⟩ := hunmarked q hqBase hpartial
            have href : refinedLabel M label split u = q := by
              simp [refinedLabel, huNotM, hulabel]
            have hfiber := classMultiplicity_refinedLabel_at hM hsizes.1
              hsizes.2 hcounts hvalid huA
            rw [href] at hfiber
            simp [huNotM, hulabel, A] at hfiber
            calc
              workSize q = size q - counts q :=
                (hsplitSizes.1 q hqTouched hpartial).1
              _ = classMultiplicity label A q - classMultiplicity label M q := by
                rw [hsizes.2 q hqBase, hcounts q hqBase]
              _ = classMultiplicity (refinedLabel M label split) A q :=
                hfiber.symm
          · have hfull : size q ≤ counts q := by omega
            obtain ⟨u, huA, huM, hulabel⟩ := hmarked q hqTouched
            have hsplitq := hvalid.2.1 q hqTouched hfull
            have href : refinedLabel M label split u = q := by
              simp [refinedLabel, huM, hulabel, hsplitq]
            have hfiber := classMultiplicity_refinedLabel_at hM hsizes.1
              hsizes.2 hcounts hvalid huA
            rw [href] at hfiber
            simp [huM, hulabel, A] at hfiber
            calc
              workSize q = size q := hsplitSizes.2 q hqTouched hfull
              _ = counts q := Nat.le_antisymm hfull (hcountLe q hqBase)
              _ = classMultiplicity label M q := hcounts q hqBase
              _ = classMultiplicity (refinedLabel M label split) A q :=
                hfiber.symm
        · have hqPositive := hoccupied q hqBase
          obtain ⟨u, huA, hulabel⟩ :=
            mem_touchedClasses.mp (classMultiplicity_pos_iff.mp hqPositive)
          have huNotM : u ∉ M := by
            intro huM
            exact hqTouched (mem_touchedClasses.mpr ⟨u, huM, hulabel⟩)
          have href : refinedLabel M label split u = q := by
            simp [refinedLabel, huNotM, hulabel]
          have hzero : classMultiplicity label M q = 0 := by
            exact Nat.eq_zero_of_not_pos
              (fun hp => hqTouched (classMultiplicity_pos_iff.mp hp))
          have hfiber := classMultiplicity_refinedLabel_at hM hsizes.1
            hsizes.2 hcounts hvalid huA
          rw [href] at hfiber
          simp [huNotM, hulabel, hzero] at hfiber
          calc
            workSize q = size q := hunchanged q hqBase hqTouched
            _ = classMultiplicity label A q := hsizes.2 q hqBase
            _ = classMultiplicity (refinedLabel M label split) A q :=
              hfiber.symm
      · have hqIco : q ∈ Finset.Ico base current :=
          Finset.mem_Ico.mpr ⟨by omega, hqCurrent⟩
        rw [← hprefix.image_partial_eq_Ico] at hqIco
        obtain ⟨r, hrPartial, hrsplit⟩ := Finset.mem_image.mp hqIco
        obtain ⟨hrTouched, hrPart⟩ := Finset.mem_filter.mp hrPartial
        obtain ⟨u, huA, huM, hulabel⟩ := hmarked r hrTouched
        have hrBase := hlabelA u huA
        rw [hulabel] at hrBase
        have href : refinedLabel M label split u = q := by
          simp [refinedLabel, huM, hulabel, hrsplit]
        have hfiber := classMultiplicity_refinedLabel_at hM hsizes.1
          hsizes.2 hcounts hvalid huA
        rw [href] at hfiber
        simp [huM, hulabel] at hfiber
        calc
          workSize q = workSize (split r) := by rw [hrsplit]
          _ = counts r := (hsplitSizes.1 r hrTouched hrPart).2
          _ = classMultiplicity label M r := hcounts r hrBase
          _ = classMultiplicity (refinedLabel M label split) A q :=
            hfiber.symm
  · intro q hqCurrent
    obtain ⟨u, huA, href⟩ := hrepresentative q hqCurrent
    apply classMultiplicity_pos_iff.mpr
    exact mem_touchedClasses.mpr ⟨u, huA, href⟩

end Lax235315Proofs.Construction.RefineSplitMath
