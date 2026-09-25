import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-! Mathematical stable bucket sorting used by the eight radix passes. -/

namespace Lax235315Proofs.Construction.RadixMath

/-- Stable bucket sort by a natural-valued digit in `[0,q)`. -/
def bucketSort {α : Type*} (q : ℕ) (key : α → ℕ) (xs : List α) : List α :=
  (List.range q).flatMap fun d => xs.filter fun x => key x = d

def countDigit {α : Type*} (key : α → ℕ) (xs : List α) (d : ℕ) : ℕ :=
  (xs.filter fun x => key x = d).length

def startDigit {α : Type*} (key : α → ℕ) (xs : List α) (d : ℕ) : ℕ :=
  ((List.range d).map fun e => countDigit key xs e).sum

@[simp] theorem startDigit_zero {α : Type*} (key : α → ℕ) (xs : List α) :
    startDigit key xs 0 = 0 := rfl

theorem startDigit_succ {α : Type*} (key : α → ℕ) (xs : List α) (d : ℕ) :
    startDigit key xs (d + 1) = startDigit key xs d + countDigit key xs d := by
  simp [startDigit, List.range_succ, List.map_append]

theorem startDigit_mono {α : Type*} (key : α → ℕ) (xs : List α)
    {d e : ℕ} (hde : d ≤ e) : startDigit key xs d ≤ startDigit key xs e := by
  induction e with
  | zero => simp_all
  | succ e ih =>
      by_cases h : d ≤ e
      · exact (ih h).trans (by rw [startDigit_succ]; omega)
      · have : d = e + 1 := by omega
        simp [this]

theorem countDigit_take_succ {α : Type*} (key : α → ℕ) (xs : List α)
    {i : ℕ} (hi : i < xs.length) (d : ℕ) :
    countDigit key (xs.take (i + 1)) d =
      countDigit key (xs.take i) d + if key xs[i] = d then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hi]
  unfold countDigit
  rw [List.filter_append, List.length_append]
  by_cases h : key xs[i] = d <;> simp [h]

theorem countDigit_take_le {α : Type*} (key : α → ℕ) (xs : List α)
    (i d : ℕ) : countDigit key (xs.take i) d ≤ countDigit key xs d := by
  unfold countDigit
  apply List.Sublist.length_le
  exact (List.take_sublist _ _).filter _

theorem digit_intervals_separated {α : Type*} (key : α → ℕ)
    (xs : List α) {d e : ℕ} (hde : d < e) :
    startDigit key xs d + countDigit key xs d ≤ startDigit key xs e := by
  rw [← startDigit_succ]
  exact startDigit_mono key xs (by omega)

theorem length_bucketSort_eq_startDigit {α : Type*} (key : α → ℕ)
    (xs : List α) (d : ℕ) :
    (bucketSort d key xs).length = startDigit key xs d := by
  simp [bucketSort, startDigit, countDigit]

private theorem range_split_at {d q : ℕ} (hdq : d < q) :
    List.range q = List.range d ++ d :: List.range' (d + 1) (q - (d + 1)) := by
  simp only [List.range_eq_range']
  rw [show q = d + (q - d) by omega, ← List.range'_append_1]
  congr 1
  rw [show q - d = (q - (d + 1)) + 1 by omega, List.range'_succ]
  simp only [Nat.zero_add]
  congr 2 <;> omega

theorem bucketSort_split_at {α : Type*} (key : α → ℕ) (xs : List α)
    {d q : ℕ} (hdq : d < q) :
    bucketSort q key xs = bucketSort d key xs ++
      (xs.filter fun x => key x = d) ++
      (List.range' (d + 1) (q - (d + 1))).flatMap
        (fun e => xs.filter fun x => key x = e) := by
  simp only [bucketSort, range_split_at hdq, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem getD_bucketSort {α : Type*} [Inhabited α]
    (key : α → ℕ) (xs : List α) {d q j : ℕ}
    (hdq : d < q) (hj : j < countDigit key xs d) :
    (bucketSort q key xs).getD (startDigit key xs d + j) default =
      (xs.filter fun x => key x = d).getD j default := by
  rw [bucketSort_split_at key xs hdq]
  rw [List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by
    rw [length_bucketSort_eq_startDigit]; omega)]
  rw [length_bucketSort_eq_startDigit, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa [countDigit] using hj)]

def natUpdate (f : ℕ → ℕ) (k v : ℕ) : ℕ → ℕ :=
  fun i => if i = k then v else f i

@[simp] theorem natUpdate_self (f : ℕ → ℕ) (k v : ℕ) :
    natUpdate f k v k = v := by simp [natUpdate]

theorem natUpdate_of_ne (f : ℕ → ℕ) {i k v : ℕ} (h : i ≠ k) :
    natUpdate f k v i = f i := by simp [natUpdate, h]

/-- Array contents after scattering the first `i` entries to their stable
bucket positions. -/
def scatterPrefix (key : ℕ → ℕ) (xs : List ℕ) (initial : ℕ → ℕ) :
    ℕ → ℕ → ℕ
  | 0 => initial
  | i + 1 =>
      let x := xs.getD i 0
      natUpdate (scatterPrefix key xs initial i)
        (startDigit key xs (key x) + countDigit key (xs.take i) (key x)) x

private theorem getD_filter_at_count_take (key : ℕ → ℕ) (xs : List ℕ)
    {i : ℕ} (hi : i < xs.length) :
    (xs.filter fun x => key x = key xs[i]).getD
        (countDigit key (xs.take i) (key xs[i])) 0 = xs[i] := by
  let xi := xs[i]
  change (xs.filter fun x => key x = key xi).getD
      (countDigit key (xs.take i) (key xi)) 0 = xi
  have hsplit : xs = xs.take i ++ xi :: xs.drop (i + 1) := by
    calc
      xs = xs.take i ++ xs.drop i := (List.take_append_drop i xs).symm
      _ = xs.take i ++ xi :: xs.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hi]
  have hfilter :
      (xs.filter fun x => key x = key xi) =
        (xs.take i).filter (fun x => key x = key xi) ++
          xi :: (xs.drop (i + 1)).filter (fun x => key x = key xi) := by
    conv_lhs => rw [hsplit]
    simp
  rw [hfilter]
  rw [List.getD_append_right _ _ _ _ (by
    simp [countDigit])]
  simp [countDigit]

private theorem scatter_position_ne (key : ℕ → ℕ) (xs : List ℕ)
    {i d e j : ℕ} (hi : i < xs.length) (he : key xs[i] = e)
    (hj : j < countDigit key (xs.take i) d) :
    startDigit key xs d + j ≠
      startDigit key xs e + countDigit key (xs.take i) e := by
  have hestep := countDigit_take_succ key xs hi e
  rw [he, if_pos rfl] at hestep
  have hele := countDigit_take_le key xs (i + 1) e
  have hefull : countDigit key (xs.take i) e < countDigit key xs e := by
    omega
  intro heq
  by_cases hde : d = e
  · rw [hde] at hj heq
    omega
  · rcases lt_or_gt_of_ne hde with hlt | hgt
    · have hsep := digit_intervals_separated key xs hlt
      have hjfull := countDigit_take_le key xs i d
      omega
    · have hsep := digit_intervals_separated key xs hgt
      omega

/-- Every cell already scattered into a bucket has the corresponding
stable-filter value. -/
theorem scatterPrefix_correct (key : ℕ → ℕ) (xs : List ℕ)
    (initial : ℕ → ℕ) {i : ℕ} (hi : i ≤ xs.length) :
    ∀ d j, j < countDigit key (xs.take i) d →
      scatterPrefix key xs initial i (startDigit key xs d + j) =
        (xs.filter fun x => key x = d).getD j 0 := by
  induction i with
  | zero => simp [countDigit]
  | succ i ih =>
      have hilength : i < xs.length := by omega
      intro d j hj
      rw [countDigit_take_succ key xs hilength d] at hj
      by_cases hxd : key xs[i] = d
      · simp only [hxd, if_pos, Nat.lt_add_one_iff] at hj
        by_cases hjold : j < countDigit key (xs.take i) d
        · rw [scatterPrefix]
          rw [List.getD_eq_getElem _ _ hilength]
          rw [natUpdate_of_ne _ (scatter_position_ne key xs hilength rfl hjold)]
          exact ih (by omega) d j hjold
        · have hjeq : j = countDigit key (xs.take i) d := by omega
          subst j
          rw [scatterPrefix]
          rw [List.getD_eq_getElem _ _ hilength]
          rw [hxd, natUpdate_self]
          simpa [hxd] using (getD_filter_at_count_take key xs hilength).symm
      · simp only [hxd, if_false, Nat.add_zero] at hj
        rw [scatterPrefix]
        rw [List.getD_eq_getElem _ _ hilength]
        rw [natUpdate_of_ne _ (scatter_position_ne key xs hilength rfl hj)]
        exact ih (by omega) d j hj

theorem exists_digit_position {α : Type*} (key : α → ℕ) (xs : List α)
    {q k : ℕ} (hk : k < startDigit key xs q) :
    ∃ d < q, ∃ j < countDigit key xs d, k = startDigit key xs d + j := by
  induction q with
  | zero => simp at hk
  | succ q ih =>
      rw [startDigit_succ] at hk
      by_cases hprefix : k < startDigit key xs q
      · obtain ⟨d, hdq, j, hj, rfl⟩ := ih hprefix
        exact ⟨d, by omega, j, hj, rfl⟩
      · refine ⟨q, by omega, k - startDigit key xs q, by omega, ?_⟩
        omega

@[simp] theorem mem_bucketSort {α : Type*} {q : ℕ} {key : α → ℕ}
    {xs : List α} {x : α} :
    x ∈ bucketSort q key xs ↔ x ∈ xs ∧ key x < q := by
  simp only [bucketSort, List.mem_flatMap, List.mem_range, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨d, hd, hx, hkey⟩
    exact ⟨hx, hkey.trans_lt hd⟩
  · rintro ⟨hx, hkey⟩
    exact ⟨key x, hkey, hx, rfl⟩

theorem nodup_bucketSort {α : Type*} [DecidableEq α] {q : ℕ}
    {key : α → ℕ} {xs : List α} (hxs : xs.Nodup) :
    (bucketSort q key xs).Nodup := by
  rw [bucketSort, List.nodup_flatMap]
  constructor
  · intro d hd
    exact hxs.filter _
  · rw [List.pairwise_iff_get]
    intro i j hij
    have hdij : (List.range q)[i] ≠ (List.range q)[j] := by
      change (List.range q).get i ≠ (List.range q).get j
      have hi : (List.range q).get i = i.val := by
        simpa [List.get_eq_getElem] using List.getElem_range (n := q) i.isLt
      have hj : (List.range q).get j = j.val := by
        simpa [List.get_eq_getElem] using List.getElem_range (n := q) j.isLt
      rw [hi, hj]
      exact Nat.ne_of_lt hij
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro x hxi hxj
    have hiKey := of_decide_eq_true (List.mem_filter.mp hxi).2
    have hjKey := of_decide_eq_true (List.mem_filter.mp hxj).2
    exact hdij (hiKey.symm.trans hjKey)

theorem bucketSort_perm {α : Type*} [DecidableEq α] {q : ℕ}
    {key : α → ℕ} {xs : List α} (hxs : xs.Nodup)
    (hkey : ∀ x ∈ xs, key x < q) :
    List.Perm (bucketSort q key xs) xs := by
  apply (List.perm_ext_iff_of_nodup (nodup_bucketSort hxs) hxs).2
  intro x
  rw [mem_bucketSort]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, hkey x hx⟩

/-- At the end of scattering, the first `|xs|` cells are exactly the stable
bucket-sort output. -/
theorem scatterPrefix_eq_bucketSort (key : ℕ → ℕ) (xs : List ℕ)
    (initial : ℕ → ℕ) {q k : ℕ} (hxs : xs.Nodup)
    (hkey : ∀ x ∈ xs, key x < q) (hk : k < xs.length) :
    scatterPrefix key xs initial xs.length k =
      (bucketSort q key xs).getD k 0 := by
  have hstart : startDigit key xs q = xs.length := by
    rw [← length_bucketSort_eq_startDigit]
    exact (bucketSort_perm hxs hkey).length_eq
  obtain ⟨d, hdq, j, hj, hkpos⟩ :=
    exists_digit_position key xs (by rwa [hstart])
  subst k
  rw [scatterPrefix_correct key xs initial (le_refl _) d j (by
      simpa using hj)]
  exact (getD_bucketSort key xs hdq hj).symm

@[simp] theorem length_bucketSort {α : Type*} [DecidableEq α] {q : ℕ}
    {key : α → ℕ} {xs : List α} (hxs : xs.Nodup)
    (hkey : ∀ x ∈ xs, key x < q) :
    (bucketSort q key xs).length = xs.length :=
  (bucketSort_perm hxs hkey).length_eq

/-- One stable pass promotes an ordering relation `R` to lexicographic
ordering by the new, more significant digit. -/
theorem pairwise_bucketSort_lex {α : Type*} {q : ℕ} {key : α → ℕ}
    {xs : List α} {R : α → α → Prop}
    (hpair : xs.Pairwise R) :
    (bucketSort q key xs).Pairwise
      (fun x y => key x < key y ∨ key x = key y ∧ R x y) := by
  rw [bucketSort, List.pairwise_flatMap]
  constructor
  · intro d hd
    have hf := hpair.filter (fun x => decide (key x = d))
    rw [List.pairwise_iff_get]
    intro i j hij
    have hxi := List.getElem_mem (l := xs.filter fun x => key x = d) i.isLt
    have hyj := List.getElem_mem (l := xs.filter fun x => key x = d) j.isLt
    have hxkey := of_decide_eq_true (List.mem_filter.mp hxi).2
    have hykey := of_decide_eq_true (List.mem_filter.mp hyj).2
    exact Or.inr ⟨hxkey.trans hykey.symm,
      (List.pairwise_iff_get.mp hf) i j hij⟩
  · rw [List.pairwise_iff_get]
    intro i j hij x hx y hy
    have hi : (List.range q).get i = i.val := by
      simpa [List.get_eq_getElem] using List.getElem_range (n := q) i.isLt
    have hj : (List.range q).get j = j.val := by
      simpa [List.get_eq_getElem] using List.getElem_range (n := q) j.isLt
    have hix := of_decide_eq_true (List.mem_filter.mp hx).2
    have hjy := of_decide_eq_true (List.mem_filter.mp hy).2
    exact Or.inl (by rw [hix, hjy, hi, hj]; exact hij)

/-- Lexicographic comparison along a specified list of digit positions. -/
def LexOn {α : Type*} (digits : Fin 8 → α → ℕ) :
    List (Fin 8) → α → α → Prop
  | [], _, _ => True
  | d :: ds, x, y =>
      digits d x < digits d y ∨
        digits d x = digits d y ∧ LexOn digits ds x y

def digitOrder : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The eight fixed stable passes, least significant digit first. -/
def radixSort8 {α : Type*} (q : ℕ) (digits : Fin 8 → α → ℕ)
    (xs : List α) : List α :=
  bucketSort q (digits 0) <|
  bucketSort q (digits 1) <|
  bucketSort q (digits 2) <|
  bucketSort q (digits 3) <|
  bucketSort q (digits 4) <|
  bucketSort q (digits 5) <|
  bucketSort q (digits 6) <|
  bucketSort q (digits 7) xs

theorem radixSort8_perm {α : Type*} [DecidableEq α]
    {q : ℕ} {digits : Fin 8 → α → ℕ} {xs : List α}
    (hxs : xs.Nodup) (hkey : ∀ d x, x ∈ xs → digits d x < q) :
    List.Perm (radixSort8 q digits xs) xs := by
  let x₇ := bucketSort q (digits 7) xs
  let x₆ := bucketSort q (digits 6) x₇
  let x₅ := bucketSort q (digits 5) x₆
  let x₄ := bucketSort q (digits 4) x₅
  let x₃ := bucketSort q (digits 3) x₄
  let x₂ := bucketSort q (digits 2) x₃
  let x₁ := bucketSort q (digits 1) x₂
  let x₀ := bucketSort q (digits 0) x₁
  have p₇ : List.Perm x₇ xs := bucketSort_perm hxs (hkey 7)
  have nd₇ : x₇.Nodup := p₇.symm.nodup hxs
  have p₆ : List.Perm x₆ x₇ := bucketSort_perm nd₇
    (fun x hx => hkey 6 x (p₇.subset hx))
  have nd₆ : x₆.Nodup := p₆.symm.nodup nd₇
  have p₅ : List.Perm x₅ x₆ := bucketSort_perm nd₆
    (fun x hx => hkey 5 x (p₇.subset (p₆.subset hx)))
  have nd₅ : x₅.Nodup := p₅.symm.nodup nd₆
  have p₄ : List.Perm x₄ x₅ := bucketSort_perm nd₅
    (fun x hx => hkey 4 x (p₇.subset (p₆.subset (p₅.subset hx))))
  have nd₄ : x₄.Nodup := p₄.symm.nodup nd₅
  have p₃ : List.Perm x₃ x₄ := bucketSort_perm nd₄
    (fun x hx => hkey 3 x
      (p₇.subset (p₆.subset (p₅.subset (p₄.subset hx)))))
  have nd₃ : x₃.Nodup := p₃.symm.nodup nd₄
  have p₂ : List.Perm x₂ x₃ := bucketSort_perm nd₃
    (fun x hx => hkey 2 x
      (p₇.subset (p₆.subset (p₅.subset (p₄.subset (p₃.subset hx))))))
  have nd₂ : x₂.Nodup := p₂.symm.nodup nd₃
  have p₁ : List.Perm x₁ x₂ := bucketSort_perm nd₂
    (fun x hx => hkey 1 x
      (p₇.subset (p₆.subset (p₅.subset (p₄.subset (p₃.subset
        (p₂.subset hx)))))))
  have nd₁ : x₁.Nodup := p₁.symm.nodup nd₂
  have p₀ : List.Perm x₀ x₁ := bucketSort_perm nd₁
    (fun x hx => hkey 0 x
      (p₇.subset (p₆.subset (p₅.subset (p₄.subset (p₃.subset
        (p₂.subset (p₁.subset hx))))))))
  change List.Perm x₀ xs
  exact p₀.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans
    (p₅.trans (p₆.trans p₇))))))

theorem radixSort8_pairwise {α : Type*}
    {q : ℕ} {digits : Fin 8 → α → ℕ} {xs : List α} :
    (radixSort8 q digits xs).Pairwise (LexOn digits digitOrder) := by
  let x₇ := bucketSort q (digits 7) xs
  let x₆ := bucketSort q (digits 6) x₇
  let x₅ := bucketSort q (digits 5) x₆
  let x₄ := bucketSort q (digits 4) x₅
  let x₃ := bucketSort q (digits 3) x₄
  let x₂ := bucketSort q (digits 2) x₃
  let x₁ := bucketSort q (digits 1) x₂
  let x₀ := bucketSort q (digits 0) x₁
  have hbase : xs.Pairwise (LexOn digits []) := by
    change xs.Pairwise (fun _ _ => True)
    induction xs with
    | nil => exact List.Pairwise.nil
    | cons a xs ih => exact List.Pairwise.cons (by simp) ih
  have h₇ : x₇.Pairwise (LexOn digits [7]) := by
    simpa [x₇, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 7) hbase)
  have h₆ : x₆.Pairwise (LexOn digits [6, 7]) := by
    simpa [x₆, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 6) h₇)
  have h₅ : x₅.Pairwise (LexOn digits [5, 6, 7]) := by
    simpa [x₅, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 5) h₆)
  have h₄ : x₄.Pairwise (LexOn digits [4, 5, 6, 7]) := by
    simpa [x₄, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 4) h₅)
  have h₃ : x₃.Pairwise (LexOn digits [3, 4, 5, 6, 7]) := by
    simpa [x₃, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 3) h₄)
  have h₂ : x₂.Pairwise (LexOn digits [2, 3, 4, 5, 6, 7]) := by
    simpa [x₂, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 2) h₃)
  have h₁ : x₁.Pairwise (LexOn digits [1, 2, 3, 4, 5, 6, 7]) := by
    simpa [x₁, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 1) h₂)
  have h₀ : x₀.Pairwise (LexOn digits digitOrder) := by
    simpa [x₀, digitOrder, LexOn] using
      (pairwise_bucketSort_lex (q := q) (key := digits 0) h₁)
  exact h₀

/-- An element lexicographically between two equal digit vectors has the
same digits as both endpoints. -/
theorem lexOn_between_eq {α : Type*} {digits : Fin 8 → α → ℕ}
    {ds : List (Fin 8)} {x y z : α}
    (hxy : ∀ d ∈ ds, digits d x = digits d y)
    (hxz : LexOn digits ds x z) (hzy : LexOn digits ds z y) :
    ∀ d ∈ ds, digits d x = digits d z := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      simp only [LexOn] at hxz hzy
      have hdxy := hxy d (by simp)
      have hdxz : digits d x = digits d z := by
        rcases hxz with hlt | ⟨heq, -⟩
        · rcases hzy with hlt' | ⟨heq', -⟩ <;> omega
        · exact heq
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hdxz
      · apply ih
        · intro a ha
          exact hxy a (by simp [ha])
        · rcases hxz with hlt | ⟨heq, htail⟩
          · omega
          · exact htail
        · rcases hzy with hlt | ⟨heq, htail⟩
          · omega
          · exact htail
        · exact he

/-- In a lexicographically sorted list, any repeated digit vector already
appears on an adjacent pair, exactly what `detectCollision` checks. -/
theorem exists_adjacent_equal_of_equal_indices {α : Type*}
    {digits : Fin 8 → α → ℕ} {xs : List α}
    (hpair : xs.Pairwise (LexOn digits digitOrder))
    {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length) (hij : i < j)
    (heq : ∀ d ∈ digitOrder, digits d xs[i] = digits d xs[j]) :
    ∃ k : Fin (xs.length - 1),
      ∀ d ∈ digitOrder,
        digits d xs[k.val] = digits d xs[k.val + 1] := by
  by_cases hadj : i + 1 = j
  · refine ⟨⟨i, by omega⟩, ?_⟩
    simpa [hadj] using heq
  · have hi1 : i + 1 < xs.length := by omega
    have hi1j : i + 1 < j := by omega
    have hxz : LexOn digits digitOrder xs[i] xs[i + 1] := by
      simpa [List.get_eq_getElem] using
        (List.pairwise_iff_get.mp hpair
          (i := ⟨i, hi⟩) (j := ⟨i + 1, hi1⟩)
          (by change i < i + 1; omega))
    have hzy : LexOn digits digitOrder xs[i + 1] xs[j] := by
      simpa [List.get_eq_getElem] using
        (List.pairwise_iff_get.mp hpair
          (i := ⟨i + 1, hi1⟩) (j := ⟨j, hj⟩)
          (by change i + 1 < j; exact hi1j))
    refine ⟨⟨i, by omega⟩, ?_⟩
    exact lexOn_between_eq heq hxz hzy

end Lax235315Proofs.Construction.RadixMath
