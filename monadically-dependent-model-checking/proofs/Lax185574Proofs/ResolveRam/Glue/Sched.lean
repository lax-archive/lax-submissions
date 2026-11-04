import Lax185574Proofs.ResolveRam.CallList

/-!
The schedule of the glue program of lem:resolve-lift.

A position `Cur` of the schedule is the call of the scatter type, call
`m` of item `i` of level `d` on the way down (`dn d i m`) or on the way
up (`up d i m`), or the end. `rest c` is the list of the calls from
position `c` on, and `next c` the position that follows `c`. The round
that receives the answer of the call at `c` computes `next c` from the
lengths of the levels and of the filtered far trees. A level that is
empty is never visited: the levels below an empty level are empty, so
the way down ends at the last nonempty level and the way up starts
there.

`rest_step`: at a valid position `c`, `rest c` is the call `callOf c`
followed by `rest (next c)`. `rcalls_drop`: the calls from call `j` on
are `rest (cur j)` for the position `cur j` reached after `j` steps, so
`rcalls[j]` is `callOf (cur j)` and the end comes after the last call.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.ResolveRam

/-- A position of the schedule. -/
inductive Cur
  | stp
  | dn (d i m : ℕ)
  | up (d i m : ℕ)
  | fin
  deriving DecidableEq

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The calls of level `d` on the way down. -/
noncomputable def fD (d : ℕ) : List RCall := (lvR G P Q s k₀ q₀ d).flatMap (downCalls G P Q s k₀ q₀)

/-- The calls of level `d` on the way up. -/
noncomputable def fU (d : ℕ) : List RCall :=
  (lvR G P Q s k₀ q₀ d).zipIdx.flatMap (upCalls G P Q s k₀ q₀ d)

/-- The calls of the levels `d, …, q₀ - 1` on the way down. -/
noncomputable def dFrom (d : ℕ) : List RCall := (List.range' d (q₀ - d)).flatMap (fD G P Q s k₀ q₀)

/-- The calls of the levels `d - 1, …, 0` on the way up. -/
noncomputable def uBelow (d : ℕ) : List RCall := (List.range d).reverse.flatMap (fU G P Q s k₀ q₀)

/-- The calls from a position on. -/
noncomputable def rest : Cur → List RCall
  | .stp => .stp :: (dFrom G P Q s k₀ q₀ 0 ++ uBelow G P Q s k₀ q₀ (q₀ + 1))
  | .dn d i m => ((((lvR G P Q s k₀ q₀ d).drop i).flatMap (downCalls G P Q s k₀ q₀)).drop m ++
      dFrom G P Q s k₀ q₀ (d + 1)) ++ uBelow G P Q s k₀ q₀ (q₀ + 1)
  | .up d i m => (((lvR G P Q s k₀ q₀ d).zipIdx.drop i).flatMap (upCalls G P Q s k₀ q₀ d)).drop m ++
      uBelow G P Q s k₀ q₀ d
  | .fin => []

/-- The number of calls of item `i` of level `d` on the way down. -/
noncomputable def nDn (d i : ℕ) : ℕ :=
  match (lvR G P Q s k₀ q₀ d)[i]? with
  | some x => (downCalls G P Q s k₀ q₀ x).length
  | none => 0

/-- The number of calls of an item of level `d` on the way up. -/
def nUp (d : ℕ) : ℕ := if d < q₀ then 2 else 1

/-- The position after a position. -/
noncomputable def next : Cur → Cur
  | .stp => if q₀ = 0 then .up 0 0 0 else .dn 0 0 0
  | .dn d i m =>
    if m + 1 < nDn G P Q s k₀ q₀ d i then .dn d i (m + 1)
    else if i + 1 < (lvR G P Q s k₀ q₀ d).length then .dn d (i + 1) 0
    else if (lvR G P Q s k₀ q₀ (d + 1)).length = 0 then .up d 0 0
    else if d + 1 < q₀ then .dn (d + 1) 0 0 else .up (d + 1) 0 0
  | .up d i m =>
    if m + 1 < nUp q₀ d then .up d i (m + 1)
    else if i + 1 < (lvR G P Q s k₀ q₀ d).length then .up d (i + 1) 0
    else if d = 0 then .fin else .up (d - 1) 0 0
  | .fin => .fin

/-- The positions that carry a call. -/
def Valid : Cur → Prop
  | .stp => (lvR G P Q s k₀ q₀ 0).length ≠ 0
  | .dn d i m => d < q₀ ∧ i < (lvR G P Q s k₀ q₀ d).length ∧ m < nDn G P Q s k₀ q₀ d i
  | .up d i m => d ≤ q₀ ∧ i < (lvR G P Q s k₀ q₀ d).length ∧ m < nUp q₀ d
  | .fin => False

/-- The call at a position. -/
noncomputable def callOf : Cur → RCall
  | .stp => .stp
  | .dn d i m => match (lvR G P Q s k₀ q₀ d)[i]? with
    | some x => ((downCalls G P Q s k₀ q₀ x)[m]?).getD .stp
    | none => .stp
  | .up d i m => match (lvR G P Q s k₀ q₀ d)[i]? with
    | some x => ((upCalls G P Q s k₀ q₀ d (x, i))[m]?).getD .stp
    | none => .stp
  | .fin => .stp

/-! ### Facts on the levels -/

theorem lvR_succ (d : ℕ) :
    lvR G P Q s k₀ q₀ (d + 1) = nextLevel (exR G P Q s k₀ q₀) (lvR G P Q s k₀ q₀ d) :=
  levels_succ _ _ d

theorem lvR_succ_nil {d : ℕ} (h : (lvR G P Q s k₀ q₀ d).length = 0) :
    (lvR G P Q s k₀ q₀ (d + 1)).length = 0 := by
  rw [List.length_eq_zero_iff] at h ⊢
  rw [lvR_succ, h]
  rfl

theorem lvR_nil_of_le {d e : ℕ} (h : (lvR G P Q s k₀ q₀ d).length = 0) (hde : d ≤ e) :
    (lvR G P Q s k₀ q₀ e).length = 0 := by
  induction e, hde using Nat.le_induction with
  | base => exact h
  | succ e _ ih => exact lvR_succ_nil G P Q s k₀ q₀ ih

theorem lvR_zero_length : (lvR G P Q s k₀ q₀ 0).length = n := by
  simp [lvR, levels, famItems]

theorem fD_nil {d : ℕ} (h : (lvR G P Q s k₀ q₀ d).length = 0) : fD G P Q s k₀ q₀ d = [] := by
  rw [List.length_eq_zero_iff] at h
  simp [fD, h]

theorem fU_nil {d : ℕ} (h : (lvR G P Q s k₀ q₀ d).length = 0) : fU G P Q s k₀ q₀ d = [] := by
  rw [List.length_eq_zero_iff] at h
  simp [fU, h]

theorem dFrom_succ {d : ℕ} (h : d < q₀) :
    dFrom G P Q s k₀ q₀ d = fD G P Q s k₀ q₀ d ++ dFrom G P Q s k₀ q₀ (d + 1) := by
  unfold dFrom
  rw [show q₀ - d = (q₀ - (d + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

theorem dFrom_ge {d : ℕ} (h : q₀ ≤ d) : dFrom G P Q s k₀ q₀ d = [] := by
  simp [dFrom, show q₀ - d = 0 by omega]

theorem dFrom_nil {d : ℕ} (h : (lvR G P Q s k₀ q₀ d).length = 0) : dFrom G P Q s k₀ q₀ d = [] := by
  unfold dFrom
  rw [List.flatMap_eq_nil_iff]
  intro e he
  rw [List.mem_range'_1] at he
  exact fD_nil G P Q s k₀ q₀ (lvR_nil_of_le G P Q s k₀ q₀ h he.1)

theorem uBelow_succ (d : ℕ) :
    uBelow G P Q s k₀ q₀ (d + 1) = fU G P Q s k₀ q₀ d ++ uBelow G P Q s k₀ q₀ d := by
  simp [uBelow, List.range_succ]

theorem uBelow_zero : uBelow G P Q s k₀ q₀ 0 = [] := rfl

/-- Above an empty level the way up has no calls. -/
theorem uBelow_eq {d e : ℕ} (h : (lvR G P Q s k₀ q₀ (d + 1)).length = 0) (hde : d + 1 ≤ e) :
    uBelow G P Q s k₀ q₀ e = uBelow G P Q s k₀ q₀ (d + 1) := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e he ih =>
    rw [uBelow_succ, fU_nil G P Q s k₀ q₀ (lvR_nil_of_le G P Q s k₀ q₀ h he), List.nil_append, ih]

/-! ### The step -/

theorem length_downCalls (x : Item) :
    (downCalls G P Q s k₀ q₀ x).length = 2 + (faP G (dataOf G P Q s k₀ q₀) x.2).length := by
  simp [downCalls]; omega

theorem length_upCalls (d : ℕ) (y : Item × ℕ) :
    (upCalls G P Q s k₀ q₀ d y).length = nUp q₀ d := by
  unfold upCalls nUp; split_ifs <;> rfl

theorem nDn_eq {d i : ℕ} (h : i < (lvR G P Q s k₀ q₀ d).length) :
    nDn G P Q s k₀ q₀ d i = (downCalls G P Q s k₀ q₀ (lvR G P Q s k₀ q₀ d)[i]).length := by
  simp [nDn, List.getElem?_eq_getElem h]

theorem two_le_nDn {d i : ℕ} (h : i < (lvR G P Q s k₀ q₀ d).length) : 2 ≤ nDn G P Q s k₀ q₀ d i := by
  rw [nDn_eq G P Q s k₀ q₀ h, length_downCalls]; omega

theorem drop_flatMap_cons {α β : Type*} (f : α → List β) (x : α) (l : List α) {m : ℕ}
    (hm : m < (f x).length) :
    ((x :: l).flatMap f).drop m = (f x)[m] :: (((x :: l).flatMap f).drop (m + 1)) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  congr 1
  simp [List.flatMap_cons, List.getElem_append_left hm]

theorem drop_flatMap_last {α β : Type*} (f : α → List β) (x : α) (l : List α) {m : ℕ}
    (hm : m + 1 = (f x).length) :
    ((x :: l).flatMap f).drop (m + 1) = l.flatMap f := by
  rw [List.flatMap_cons, List.drop_append_of_le_length (by omega), hm, List.drop_length,
    List.nil_append]

theorem callOf_dn {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m < (downCalls G P Q s k₀ q₀ (lvR G P Q s k₀ q₀ d)[i]).length) :
    callOf G P Q s k₀ q₀ (.dn d i m) = (downCalls G P Q s k₀ q₀ (lvR G P Q s k₀ q₀ d)[i])[m] := by
  simp [callOf, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hm]

theorem callOf_up {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m < (upCalls G P Q s k₀ q₀ d ((lvR G P Q s k₀ q₀ d)[i], i)).length) :
    callOf G P Q s k₀ q₀ (.up d i m) = (upCalls G P Q s k₀ q₀ d ((lvR G P Q s k₀ q₀ d)[i], i))[m] := by
  simp [callOf, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hm]

theorem rest_dn_zero (d : ℕ) :
    rest G P Q s k₀ q₀ (.dn d 0 0) = (fD G P Q s k₀ q₀ d ++ dFrom G P Q s k₀ q₀ (d + 1)) ++
      uBelow G P Q s k₀ q₀ (q₀ + 1) := by
  simp [rest, fD]

theorem rest_up_zero (d : ℕ) :
    rest G P Q s k₀ q₀ (.up d 0 0) = uBelow G P Q s k₀ q₀ (d + 1) := by
  simp [rest, fU, uBelow_succ]

theorem drop_step {α β : Type*} (L : List α) (f : α → List β) {i m : ℕ} (hi : i < L.length)
    (hm : m < (f L[i]).length) :
    ((L.drop i).flatMap f).drop m = (f L[i])[m] :: ((L.drop i).flatMap f).drop (m + 1) := by
  rw [List.drop_eq_getElem_cons hi]; exact drop_flatMap_cons _ _ _ hm

theorem drop_last {α β : Type*} (L : List α) (f : α → List β) {i m : ℕ} (hi : i < L.length)
    (hm : m + 1 = (f L[i]).length) :
    ((L.drop i).flatMap f).drop (m + 1) = (L.drop (i + 1)).flatMap f := by
  rw [List.drop_eq_getElem_cons hi]; exact drop_flatMap_last _ _ _ hm

theorem step_dn {d i m : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m < nDn G P Q s k₀ q₀ d i) :
    rest G P Q s k₀ q₀ (.dn d i m) =
        callOf G P Q s k₀ q₀ (.dn d i m) :: rest G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)) ∧
      (Valid G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))) := by
  have hn := nDn_eq G P Q s k₀ q₀ hi
  have hm' : m < (downCalls G P Q s k₀ q₀ (lvR G P Q s k₀ q₀ d)[i]).length := by omega
  have hhead := drop_step _ (downCalls G P Q s k₀ q₀) hi hm'
  have hcall := callOf_dn G P Q s k₀ q₀ hi hm'
  simp only [next]
  by_cases h1 : m + 1 < nDn G P Q s k₀ q₀ d i
  · rw [if_pos h1]
    refine ⟨?_, hd, hi, h1⟩
    simp only [rest]
    rw [hcall, hhead]
    rfl
  rw [if_neg h1]
  have hlast := drop_last _ (downCalls G P Q s k₀ q₀) hi (m := m) (by omega)
  have hr : rest G P Q s k₀ q₀ (.dn d i m) = callOf G P Q s k₀ q₀ (.dn d i m) ::
      ((((lvR G P Q s k₀ q₀ d).drop (i + 1)).flatMap (downCalls G P Q s k₀ q₀) ++
        dFrom G P Q s k₀ q₀ (d + 1)) ++ uBelow G P Q s k₀ q₀ (q₀ + 1)) := by
    simp only [rest]
    rw [hcall, hhead, hlast]
    rfl
  rw [hr]
  by_cases h2 : i + 1 < (lvR G P Q s k₀ q₀ d).length
  · rw [if_pos h2]
    refine ⟨?_, hd, h2, by have := two_le_nDn G P Q s k₀ q₀ h2; omega⟩
    simp only [rest, List.drop_zero]
  rw [if_neg h2]
  have hnil : (lvR G P Q s k₀ q₀ d).drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
  rw [hnil, List.flatMap_nil, List.nil_append]
  by_cases h3 : (lvR G P Q s k₀ q₀ (d + 1)).length = 0
  · rw [if_pos h3, dFrom_nil G P Q s k₀ q₀ h3, List.nil_append, rest_up_zero,
      uBelow_eq G P Q s k₀ q₀ h3 (by omega)]
    exact ⟨rfl, by omega, by omega, by unfold nUp; split_ifs <;> omega⟩
  rw [if_neg h3]
  by_cases h4 : d + 1 < q₀
  · rw [if_pos h4, rest_dn_zero, ← dFrom_succ G P Q s k₀ q₀ h4]
    exact ⟨rfl, h4, by omega, by have := two_le_nDn G P Q s k₀ q₀ (d := d + 1) (i := 0) (by omega); omega⟩
  · rw [if_neg h4, rest_up_zero, dFrom_ge G P Q s k₀ q₀ (by omega), List.nil_append,
      show q₀ + 1 = d + 1 + 1 by omega]
    exact ⟨rfl, by omega, by omega, by unfold nUp; split_ifs <;> omega⟩

theorem step_up {d i m : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m < nUp q₀ d) :
    rest G P Q s k₀ q₀ (.up d i m) =
        callOf G P Q s k₀ q₀ (.up d i m) :: rest G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)) ∧
      (Valid G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.up d i m)) ∨
        next G P Q s k₀ q₀ (.up d i m) = .fin) := by
  have hzi : i < (lvR G P Q s k₀ q₀ d).zipIdx.length := by simpa using hi
  have hz : (lvR G P Q s k₀ q₀ d).zipIdx[i] = ((lvR G P Q s k₀ q₀ d)[i], i) := by
    simp [List.getElem_zipIdx]
  have hm' : m < (upCalls G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).zipIdx[i]).length := by
    rw [hz, length_upCalls]; exact hm
  have hhead := drop_step _ (upCalls G P Q s k₀ q₀ d) hzi hm'
  have hcall : callOf G P Q s k₀ q₀ (.up d i m) =
      (upCalls G P Q s k₀ q₀ d (lvR G P Q s k₀ q₀ d).zipIdx[i])[m] := by
    rw [callOf_up G P Q s k₀ q₀ hi (by rw [length_upCalls]; exact hm)]
    simp only [hz]
  simp only [next]
  by_cases h1 : m + 1 < nUp q₀ d
  · rw [if_pos h1]
    refine ⟨?_, Or.inl ⟨hd, hi, h1⟩⟩
    simp only [rest]
    rw [hcall, hhead]
    rfl
  rw [if_neg h1]
  have hlast := drop_last _ (upCalls G P Q s k₀ q₀ d) hzi (m := m)
    (by rw [hz, length_upCalls]; omega)
  have hr : rest G P Q s k₀ q₀ (.up d i m) = callOf G P Q s k₀ q₀ (.up d i m) ::
      (((lvR G P Q s k₀ q₀ d).zipIdx.drop (i + 1)).flatMap (upCalls G P Q s k₀ q₀ d) ++
        uBelow G P Q s k₀ q₀ d) := by
    simp only [rest]
    rw [hcall, hhead, hlast]
    rfl
  rw [hr]
  by_cases h2 : i + 1 < (lvR G P Q s k₀ q₀ d).length
  · rw [if_pos h2]
    refine ⟨rfl, Or.inl ⟨hd, h2, by unfold nUp; split_ifs <;> omega⟩⟩
  rw [if_neg h2]
  have hnil : (lvR G P Q s k₀ q₀ d).zipIdx.drop (i + 1) = [] :=
    List.drop_eq_nil_of_le (by simp; omega)
  rw [hnil, List.flatMap_nil, List.nil_append]
  by_cases h3 : d = 0
  · rw [if_pos h3, h3, uBelow_zero]
    exact ⟨rfl, Or.inr rfl⟩
  rw [if_neg h3]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [show e + 1 - 1 = e by omega, rest_up_zero]
  refine ⟨rfl, Or.inl ⟨by omega, ?_, by unfold nUp; split_ifs <;> omega⟩⟩
  by_contra h
  have := lvR_succ_nil G P Q s k₀ q₀ (d := e) (by omega)
  omega

/-- **The step of the schedule.** -/
theorem rest_step {c : Cur} (hc : Valid G P Q s k₀ q₀ c) :
    rest G P Q s k₀ q₀ c = callOf G P Q s k₀ q₀ c :: rest G P Q s k₀ q₀ (next G P Q s k₀ q₀ c) ∧
      (Valid G P Q s k₀ q₀ (next G P Q s k₀ q₀ c) ∨ next G P Q s k₀ q₀ c = .fin) := by
  match c, hc with
  | .stp, hc =>
    simp only [Valid] at hc
    simp only [next]
    by_cases hq : q₀ = 0
    · rw [if_pos hq, rest_up_zero]
      refine ⟨?_, Or.inl ⟨by omega, by omega, by unfold nUp; split_ifs <;> omega⟩⟩
      simp only [rest, callOf]
      rw [dFrom_ge G P Q s k₀ q₀ (show q₀ ≤ 0 by omega), List.nil_append, hq]
    · rw [if_neg hq, rest_dn_zero, ← dFrom_succ G P Q s k₀ q₀ (show 0 < q₀ by omega)]
      refine ⟨rfl, Or.inl ⟨by omega, by omega, ?_⟩⟩
      have := two_le_nDn G P Q s k₀ q₀ (d := 0) (i := 0) (by omega); omega
  | .dn d i m, ⟨hd, hi, hm⟩ =>
    obtain ⟨h1, h2⟩ := step_dn G P Q s k₀ q₀ hd hi hm
    exact ⟨h1, Or.inl h2⟩
  | .up d i m, ⟨hd, hi, hm⟩ => exact step_up G P Q s k₀ q₀ hd hi hm

/-- The position after `j` steps. -/
noncomputable def cur (j : ℕ) : Cur := (next G P Q s k₀ q₀)^[j] .stp

theorem cur_succ (j : ℕ) : cur G P Q s k₀ q₀ (j + 1) = next G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) := by
  simp only [cur, Function.iterate_succ_apply']

theorem rcalls_eq (hn : 1 ≤ n) : rcalls G P Q s k₀ q₀ = rest G P Q s k₀ q₀ .stp := by
  simp only [rcalls, show n ≠ 0 by omega, if_false, rest, downAll, upAll]
  congr 2
  rw [dFrom, Nat.sub_zero, ← List.range_eq_range']
  rfl

/-- **The schedule.** The calls from call `j` on are those from the
position `cur j`, which is valid before the last call and the end
after it. -/
theorem rcalls_drop (hn : 1 ≤ n) : ∀ j, j ≤ (rcalls G P Q s k₀ q₀).length →
    (rcalls G P Q s k₀ q₀).drop j = rest G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) ∧
      (Valid G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) ∨ cur G P Q s k₀ q₀ j = .fin) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨by rw [List.drop_zero, rcalls_eq G P Q s k₀ q₀ hn]; rfl, Or.inl ?_⟩
    show (lvR G P Q s k₀ q₀ 0).length ≠ 0
    rw [lvR_zero_length]; omega
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    rcases h2 with hv | hf
    · obtain ⟨h3, h4⟩ := rest_step G P Q s k₀ q₀ hv
      rw [cur_succ]
      refine ⟨?_, h4⟩
      rw [← List.drop_drop, h1, h3]
      rfl
    · exfalso
      rw [hf] at h1
      have := congrArg List.length h1
      simp [rest] at this
      omega

theorem rest_ne_nil {c : Cur} (hc : Valid G P Q s k₀ q₀ c) : rest G P Q s k₀ q₀ c ≠ [] := by
  rw [(rest_step G P Q s k₀ q₀ hc).1]; exact List.cons_ne_nil _ _

/-- **The call `j`.** -/
theorem rcalls_get (hn : 1 ≤ n) {j : ℕ} (hj : j < (rcalls G P Q s k₀ q₀).length) :
    Valid G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) ∧
      (rcalls G P Q s k₀ q₀)[j]? = some (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) := by
  obtain ⟨h1, h2⟩ := rcalls_drop G P Q s k₀ q₀ hn j hj.le
  have hv : Valid G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) := by
    rcases h2 with h | h
    · exact h
    · rw [h] at h1
      have := congrArg List.length h1
      simp [rest] at this
      omega
  refine ⟨hv, ?_⟩
  have h3 := (rest_step G P Q s k₀ q₀ hv).1
  rw [h3] at h1
  rw [← List.head?_drop, h1]
  rfl

/-- **The end.** After the last call the position is the end. -/
theorem cur_length (hn : 1 ≤ n) :
    cur G P Q s k₀ q₀ (rcalls G P Q s k₀ q₀).length = .fin := by
  obtain ⟨h1, h2⟩ := rcalls_drop G P Q s k₀ q₀ hn _ le_rfl
  rcases h2 with h | h
  · rw [List.drop_length] at h1
    exact absurd h1.symm (rest_ne_nil G P Q s k₀ q₀ h)
  · exact h

/-- The position of the next call is the end exactly at the last call. -/
theorem cur_succ_fin (hn : 1 ≤ n) {j : ℕ} (hj : j < (rcalls G P Q s k₀ q₀).length) :
    cur G P Q s k₀ q₀ (j + 1) = .fin ↔ j + 1 = (rcalls G P Q s k₀ q₀).length := by
  constructor
  · intro h
    by_contra hne
    have := (rcalls_get G P Q s k₀ q₀ hn (j := j + 1) (by omega)).1
    rw [h] at this
    exact this
  · intro h; rw [h]; exact cur_length G P Q s k₀ q₀ hn

end Lax185574Proofs.ResolveRam.Glue
