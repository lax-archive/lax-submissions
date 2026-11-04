import Lax185574Proofs.ResolveRam.Glue.Book
import Lax185574Proofs.ResolveRam.Glue.Dist

/-!
The state of the glue program of lem:resolve-lift and its changes.

The data of the tests are kept as the color table `ctW` (every color `Y`
that occurs, with `cTab G P Y` and `cTab G Q Y`), from which `dwOf`
reads the data `DW` of the tests (`dwOf_ok`).

The state at a position of the schedule is the record `SW` of words:
the color table, the answer of the rank shift of the current item, the
answer of the canonical form on its atom words, the lengths of the
levels, the words of the entries of the scatter type, the filtered far
tree of the current item, the answers of its compositions so far, the items of the levels
and the outputs. `swAt c` is the state written by the round that issues
the call at `c`. Round `0` keeps no words: it only issues the call of
the scatter type, and round `1` reads the input again and builds the
color table and level `0`. On the way down the levels are those up to `d` and the
part of level `d + 1` built so far. On the way up all levels are kept,
with the outputs of level `d + 1` followed by the outputs of level `d`
built so far.

The lemmas `sw_*` describe the state at the next position from the
state at `c` and the answer of the call at `c`, and the lemmas
`realQ_*` (StateUp) the query of the next call on words. These are the specifications of
the pieces of the glue program.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.DistanceLogic
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ResolveRam Lax185574Proofs.Words

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-! ### The color table -/

/-- Entry `j` (`0` or `1`) of the table at color `Y`, `0` if `Y` is
not in the table. -/
def tabLook : List ℕ → ℕ → ℕ → ℕ
  | Y' :: a :: b :: r, j, Y => if Y' = Y then (if j = 0 then a else b) else tabLook r j Y
  | _, _, _ => 0

/-- The color `Y` is in the table. -/
def inCT : List ℕ → ℕ → Bool
  | Y' :: _ :: _ :: r, Y => decide (Y' = Y) || inCT r Y
  | _, _ => false

/-- The color table. -/
noncomputable def ctW : List ℕ := (colsL G).flatMap fun Y => [Y, cTab G P Y, cTab G Q Y]

/-- The data of the tests from the table. -/
def dwOf (P Q sg : ℕ) (CT : List ℕ) : DW :=
  ⟨P, Q, sg == 1, inCT CT P, inCT CT Q, tabLook CT 0, tabLook CT 1⟩

theorem tabLook_flatMap (l : List ℕ) (f g : ℕ → ℕ) (j Y : ℕ) :
    tabLook (l.flatMap fun Y => [Y, f Y, g Y]) j Y =
      if Y ∈ l then (if j = 0 then f Y else g Y) else 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, tabLook, List.mem_cons]
    by_cases h : a = Y
    · subst h; simp
    · rw [if_neg h, ih]
      by_cases h' : Y ∈ l
      · simp [h', Ne.symm h]
      · simp [h', Ne.symm h]

theorem inCT_flatMap (l : List ℕ) (f g : ℕ → ℕ) (Y : ℕ) :
    inCT (l.flatMap fun Y => [Y, f Y, g Y]) Y = decide (Y ∈ l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, inCT, ih, List.mem_cons]
    by_cases h : a = Y
    · subst h; simp
    · simp [h, Ne.symm h]

theorem cTab_not_occ {X Y : ℕ} (hY : Y ∉ colsL G) : cTab G X Y = 0 := by
  unfold cTab
  rw [dif_neg]
  rintro ⟨s, x, y, -, hy, -⟩
  apply hY
  simp only [colsL, Finset.mem_sort, colsCore, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨y, hy⟩

theorem tabLook_ctW_P (Y : ℕ) : tabLook (ctW G P Q) 0 Y = cTab G P Y := by
  rw [ctW, tabLook_flatMap]
  by_cases hY : Y ∈ colsL G
  · simp [hY]
  · rw [if_neg hY, cTab_not_occ G hY]

theorem tabLook_ctW_Q (Y : ℕ) : tabLook (ctW G P Q) 1 Y = cTab G Q Y := by
  rw [ctW, tabLook_flatMap]
  by_cases hY : Y ∈ colsL G
  · simp [hY]
  · rw [if_neg hY, cTab_not_occ G hY]

theorem tabT_cTab (X Y r : ℕ) : cdSem G X Y r = tabT (fun Y => cTab G X Y) Y r := by
  rw [Bool.eq_iff_iff, cdSem_iff, tabT]
  simp

/-- **The data of the tests from the color table.** -/
theorem dwOf_ok : (dwOf P Q (if s then 1 else 0) (ctW G P Q)).OK (dataOf G P Q s k₀ q₀) where
  P := rfl
  Q := rfl
  sg := by cases s <;> rfl
  cP := by
    simp only [dwOf, ctW, inCT_flatMap]
    congr 1
    exact propext (mem_colsL G P Q s k₀ q₀ P)
  cQ := by
    simp only [dwOf, ctW, inCT_flatMap]
    congr 1
    exact propext (mem_colsL G P Q s k₀ q₀ Q)
  tP := by
    intro Y r
    show cdSem G P Y r = tabT (tabLook (ctW G P Q) 0) Y r
    rw [tabT_cTab]
    simp only [tabT, tabLook_ctW_P]
  tQ := by
    intro Y r
    show cdSem G Q Y r = tabT (tabLook (ctW G P Q) 1) Y r
    rw [tabT_cTab]
    simp only [tabT, tabLook_ctW_Q]

/-- The data of the tests of the instance. -/
noncomputable def dW : DW := dwOf P Q (if s then 1 else 0) (ctW G P Q)

theorem dW_ok : (dW G P Q s).OK (dataOf G P Q s k₀ q₀) := dwOf_ok G P Q s k₀ q₀

/-! ### The state -/

/-- The state of the glue program, as words. -/
structure SW where
  /-- The color table. -/
  CT : List ℕ
  /-- The words of the entries of the scatter type. -/
  SG : List (List ℕ)
  /-- The answer of the rank shift of the current item. -/
  SH : List ℕ
  /-- The answer of the canonical form on the atom words of the current item. -/
  AT : List ℕ
  /-- The lengths of the levels. -/
  LL : List ℕ
  /-- The words of the filtered far tree of the current item. -/
  FA : List (List ℕ)
  /-- The answers of the compositions of the current item so far. -/
  CO : List (List ℕ)
  /-- The item words of the levels. -/
  LV : List (List ℕ)
  /-- The output words. -/
  OU : List (List ℕ)

/-- The list of words of a state. -/
def SW.ws (w : SW) : List (List ℕ) := [w.CT, w.SH, w.AT, w.LL] ++ w.SG ++ w.FA ++ w.CO ++ w.LV ++ w.OU

/-- A default item. -/
def dItem : Item := ((0, 0), ⟨0, 0, 0, (∅ : Finset (DistFO 0))⟩)

/-- Item `i` of level `d`. -/
noncomputable def itm (d i : ℕ) : Item := (lvR G P Q s k₀ q₀ d).getD i dItem

theorem itm_eq {d i : ℕ} (h : i < (lvR G P Q s k₀ q₀ d).length) :
    itm G P Q s k₀ q₀ d i = (lvR G P Q s k₀ q₀ d)[i] := by
  simp [itm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The item words of level `d`. -/
noncomputable def lvW (d : ℕ) : List (List ℕ) := (lvR G P Q s k₀ q₀ d).map itemW

/-- The item words of the levels `0, …, d`. -/
noncomputable def lvsW (d : ℕ) : List (List ℕ) := (List.range (d + 1)).flatMap (lvW G P Q s k₀ q₀)

/-- The lengths of the levels `0, …, d`. -/
noncomputable def llW (d : ℕ) : List ℕ := (List.range (d + 1)).map fun e => (lvR G P Q s k₀ q₀ e).length

/-- The answers of the compositions of an item. -/
noncomputable def coW (τ : TypeTree) : List (List ℕ) :=
  (faP G (dataOf G P Q s k₀ q₀) τ).map fun ν => toWord (coOf G (shOf G τ) ν)

/-- The state written by the round that issues the call at a position. -/
noncomputable def swAt : Cur → SW
  | .stp => ⟨[], [], [], [], [], [], [], [], []⟩
  | .dn d i m =>
    let τ := (itm G P Q s k₀ q₀ d i).2
    ⟨ctW G P Q, (stp G k₀ q₀).words, if 1 ≤ m then toWord (shOf G τ) else [],
      [], llW G P Q s k₀ q₀ d ++ [(nxL G P Q s k₀ q₀ d i).length],
      if 2 ≤ m then (faP G (dataOf G P Q s k₀ q₀) τ).map toWord else [],
      (coW G P Q s k₀ q₀ τ).take (m - 2), lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d i, []⟩
  | .up d i m =>
    let τ := (itm G P Q s k₀ q₀ d i).2
    ⟨ctW G P Q, (stp G k₀ q₀).words, [], if m = 1 then canonW (atomQ G P Q s k₀ q₀ τ) else [],
      llW G P Q s k₀ q₀ q₀, [], [], lvsW G P Q s k₀ q₀ q₀,
      (if d < q₀ then outW G P Q s k₀ q₀ (d + 1) else []) ++ outP G P Q s k₀ q₀ d i⟩
  | .fin => ⟨[], [], [], [], [], [], [], [], []⟩

/-! ### Facts on the levels as words -/

theorem lvsW_succ (d : ℕ) :
    lvsW G P Q s k₀ q₀ (d + 1) = lvsW G P Q s k₀ q₀ d ++ lvW G P Q s k₀ q₀ (d + 1) := by
  simp [lvsW, List.range_succ (n := d + 1)]

theorem llW_succ (d : ℕ) :
    llW G P Q s k₀ q₀ (d + 1) = llW G P Q s k₀ q₀ d ++ [(lvR G P Q s k₀ q₀ (d + 1)).length] := by
  simp [llW, List.range_succ (n := d + 1)]

theorem lvW_nil {d : ℕ} (h : (lvR G P Q s k₀ q₀ d).length = 0) : lvW G P Q s k₀ q₀ d = [] := by
  rw [List.length_eq_zero_iff] at h; simp [lvW, h]

/-- Above an empty level the levels add no words. -/
theorem lvsW_le {d e : ℕ} (h : (lvR G P Q s k₀ q₀ (d + 1)).length = 0) (hde : d ≤ e) :
    lvsW G P Q s k₀ q₀ e = lvsW G P Q s k₀ q₀ d := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e he ih =>
    rw [lvsW_succ, ih, lvW_nil G P Q s k₀ q₀ (lvR_nil_of_le G P Q s k₀ q₀ h (by omega)),
      List.append_nil]

/-- Above an empty level the lengths are zeros. -/
theorem llW_le {d e : ℕ} (h : (lvR G P Q s k₀ q₀ (d + 1)).length = 0) (hde : d ≤ e) :
    llW G P Q s k₀ q₀ e = llW G P Q s k₀ q₀ d ++ List.replicate (e - d) 0 := by
  induction e, hde using Nat.le_induction with
  | base => simp
  | succ e he ih =>
    rw [llW_succ, ih, lvR_nil_of_le G P Q s k₀ q₀ h (by omega), List.append_assoc,
      show e + 1 - d = (e - d) + 1 by omega, List.replicate_succ']

theorem nxW_full (d : ℕ) :
    nxW G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length = lvW G P Q s k₀ q₀ (d + 1) := by
  rw [nxW, nxL_full]; rfl

theorem length_nxL_full (d : ℕ) :
    (nxL G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length).length = (lvR G P Q s k₀ q₀ (d + 1)).length := by
  rw [nxL_full]

/-- The offset of level `d` among the item words. -/
noncomputable def offL (d : ℕ) : ℕ := ((List.range d).map fun e => (lvR G P Q s k₀ q₀ e).length).sum

theorem length_lvsW (d : ℕ) : (lvsW G P Q s k₀ q₀ d).length = offL G P Q s k₀ q₀ (d + 1) := by
  induction d with
  | zero => simp [lvsW, offL, lvW]
  | succ d ih =>
    rw [lvsW_succ, List.length_append, ih, offL, offL, List.range_succ (n := d + 1)]
    simp [lvW]

theorem offL_succ (d : ℕ) :
    offL G P Q s k₀ q₀ (d + 1) = offL G P Q s k₀ q₀ d + (lvR G P Q s k₀ q₀ d).length := by
  simp [offL, List.range_succ]

theorem lvsW_eq (d : ℕ) :
    lvsW G P Q s k₀ q₀ d = (List.range d).flatMap (lvW G P Q s k₀ q₀) ++ lvW G P Q s k₀ q₀ d := by
  simp [lvsW, List.range_succ]

theorem length_pre (d : ℕ) :
    ((List.range d).flatMap (lvW G P Q s k₀ q₀)).length = offL G P Q s k₀ q₀ d := by
  induction d with
  | zero => simp [offL]
  | succ d ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, offL_succ]
    simp [lvW]

theorem lvsW_prefix {d e : ℕ} (hde : d ≤ e) : ∃ Z, lvsW G P Q s k₀ q₀ e = lvsW G P Q s k₀ q₀ d ++ Z := by
  induction e, hde using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ e _ ih =>
    obtain ⟨Z, hZ⟩ := ih
    exact ⟨Z ++ lvW G P Q s k₀ q₀ (e + 1), by rw [lvsW_succ, hZ, List.append_assoc]⟩

/-- **Item `i` of level `d` among the item words.** -/
theorem lvsW_get {d e i : ℕ} (hde : d ≤ e) (hi : i < (lvR G P Q s k₀ q₀ d).length) (X : List (List ℕ)) :
    (lvsW G P Q s k₀ q₀ e ++ X)[offL G P Q s k₀ q₀ d + i]? = some (itemW (lvR G P Q s k₀ q₀ d)[i]) := by
  obtain ⟨Z, hZ⟩ := lvsW_prefix G P Q s k₀ q₀ hde
  rw [hZ, lvsW_eq, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [length_pre]; omega), length_pre,
    show offL G P Q s k₀ q₀ d + i - offL G P Q s k₀ q₀ d = i by omega,
    List.getElem?_append_left (by simp [lvW]; omega)]
  simp [lvW, List.getElem?_map, List.getElem?_eq_getElem hi]

/-! ### The steps on the way down -/

section down

variable {G P Q s k₀ q₀}

theorem nDn_itm {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    nDn G P Q s k₀ q₀ d i = 2 + (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length := by
  rw [nDn_eq G P Q s k₀ q₀ hi, length_downCalls, itm_eq G P Q s k₀ q₀ hi]

theorem length_coW (τ : TypeTree) :
    (coW G P Q s k₀ q₀ τ).length = (faP G (dataOf G P Q s k₀ q₀) τ).length := by
  simp [coW]

/-- The call of the item at step `m` of the way down. -/
theorem callOf_dn' {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm : m < nDn G P Q s k₀ q₀ d i) :
    callOf G P Q s k₀ q₀ (.dn d i m) =
      if m = 0 then .shift (itm G P Q s k₀ q₀ d i).2
      else if m = 1 then .ftree (itm G P Q s k₀ q₀ d i).2
      else .compose (shOf G (itm G P Q s k₀ q₀ d i).2)
        (((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2)).getD (m - 2) (itm G P Q s k₀ q₀ d i).2) := by
  have hm' : m < (downCalls G P Q s k₀ q₀ (lvR G P Q s k₀ q₀ d)[i]).length := by
    rw [nDn_eq G P Q s k₀ q₀ hi] at hm; exact hm
  rw [itm_eq G P Q s k₀ q₀ hi, callOf_dn G P Q s k₀ q₀ hi hm']
  generalize (lvR G P Q s k₀ q₀ d)[i] = x at hm' ⊢
  rcases m with _ | _ | m
  · rfl
  · rfl
  · simp only [downCalls, List.cons_append, List.nil_append, List.getElem_cons_succ,
      List.getElem_map, show m + 1 + 1 ≠ 0 by omega, show m + 1 + 1 ≠ 1 by omega, if_false,
      show m + 1 + 1 - 2 = m by omega]
    simp only [downCalls, List.length_append, List.length_cons, List.length_nil,
      List.length_map] at hm'
    rw [List.getD_eq_getElem _ _ (by omega)]

/-- **After the rank shift.** -/
theorem sw_shift {d i : ℕ} :
    swAt G P Q s k₀ q₀ (.dn d i 1) =
      { swAt G P Q s k₀ q₀ (.dn d i 0) with SH := toWord (shOf G (itm G P Q s k₀ q₀ d i).2) } := by
  simp [swAt]

/-- **After the far tree.** -/
theorem sw_ftree {d i : ℕ} :
    swAt G P Q s k₀ q₀ (.dn d i 2) =
      { swAt G P Q s k₀ q₀ (.dn d i 1) with
        FA := ((faOf G (itm G P Q s k₀ q₀ d i).2).map toWord).filter
          (passSel (dW G P Q s) (swAt G P Q s k₀ q₀ (.dn d i 1)).SH) } := by
  simp only [swAt, le_refl, if_true, show (1 : ℕ) ≤ 2 by omega, show ¬ (2 : ℕ) ≤ 1 by omega,
    if_false, show (2 : ℕ) - 2 = 0 by rfl, show (1 : ℕ) - 2 = 0 by rfl]
  rw [← faP_words (dW_ok G P Q s k₀ q₀)]

/-- **After a composition.** -/
theorem sw_compose {d i m : ℕ} (hm : 2 ≤ m)
    (hr : m - 2 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length) :
    swAt G P Q s k₀ q₀ (.dn d i (m + 1)) =
      { swAt G P Q s k₀ q₀ (.dn d i m) with
        CO := (swAt G P Q s k₀ q₀ (.dn d i m)).CO ++
          [toWord (coOf G (shOf G (itm G P Q s k₀ q₀ d i).2)
            ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2)[m - 2]))] } := by
  simp only [swAt, show 1 ≤ m + 1 by omega, show 1 ≤ m by omega, show 2 ≤ m + 1 by omega, hm,
    if_true, show m + 1 - 2 = (m - 2) + 1 by omega]
  congr 1
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_coW]; exact hr)]
  simp [coW]

/-- The state after the last item of a level, before the next level. -/
theorem sw_fin_item {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) {k q ℓ : ℕ}
    {t : Node (q + 1) ℓ} (hx : (itm G P Q s k₀ q₀ d i).2 = ⟨k, q + 1, ℓ, t⟩) :
    nxW G P Q s k₀ q₀ d (i + 1) = nxW G P Q s k₀ q₀ d i ++
      (exW (dW G P Q s) k q ℓ (toWord t) (coW G P Q s k₀ q₀ ⟨k, q + 1, ℓ, t⟩)).map (i :: ·) := by
  rw [itm_eq G P Q s k₀ q₀ hi] at hx
  exact nxW_succ G P Q s k₀ q₀ (dW_ok G P Q s k₀ q₀) hi hx

/-- **After the last call of an item, next item.** -/
theorem sw_next_item {d i : ℕ} :
    swAt G P Q s k₀ q₀ (.dn d (i + 1) 0) =
      ⟨ctW G P Q, (stp G k₀ q₀).words, [], [],
        llW G P Q s k₀ q₀ d ++ [(nxW G P Q s k₀ q₀ d (i + 1)).length], [], [],
        lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d (i + 1), []⟩ := by
  simp [swAt, nxW]

/-- **After the last item of a level, next level.** -/
theorem sw_next_level {d : ℕ} :
    swAt G P Q s k₀ q₀ (.dn (d + 1) 0 0) =
      ⟨ctW G P Q, (stp G k₀ q₀).words, [], [],
        (llW G P Q s k₀ q₀ d ++ [(nxW G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length).length]) ++ [0], [], [],
        lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length, []⟩ := by
  simp only [swAt, nxL_zero, nxW, List.map_nil, List.append_nil, List.length_nil, llW_succ,
    lvsW_succ, nxL_full, List.length_map]
  simp [lvW, nxW, nxL_full]

/-- **After the last item of the way down, the last level.** -/
theorem sw_down_end {d : ℕ} (hd : d + 1 = q₀) :
    swAt G P Q s k₀ q₀ (.up (d + 1) 0 0) =
      ⟨ctW G P Q, (stp G k₀ q₀).words, [], [],
        llW G P Q s k₀ q₀ d ++ [(nxW G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length).length], [], [],
        lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length, []⟩ := by
  subst hd
  simp only [swAt, lt_irrefl, if_false, List.nil_append, outP, List.take_zero, show (0 : ℕ) ≠ 1 by omega]
  rw [llW_succ, lvsW_succ, nxW_full]
  simp [lvW]

/-- **After the last item, the next level empty.** -/
theorem sw_down_empty {d : ℕ} (hd : d < q₀)
    (h : (lvR G P Q s k₀ q₀ (d + 1)).length = 0) :
    swAt G P Q s k₀ q₀ (.up d 0 0) =
      ⟨ctW G P Q, (stp G k₀ q₀).words, [], [],
        llW G P Q s k₀ q₀ d ++ List.replicate (q₀ - d) 0, [], [],
        lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).length,
        outW G P Q s k₀ q₀ (d + 1)⟩ := by
  simp only [swAt, hd, if_true, outP, List.take_zero, List.append_nil, show (0 : ℕ) ≠ 1 by omega,
    if_false]
  rw [llW_le G P Q s k₀ q₀ h hd.le, lvsW_le G P Q s k₀ q₀ h hd.le, nxW_full,
    lvW_nil G P Q s k₀ q₀ h, List.append_nil]

end down

end Lax185574Proofs.ResolveRam.Glue
