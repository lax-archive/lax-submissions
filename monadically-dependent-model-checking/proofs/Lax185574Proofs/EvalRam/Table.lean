import Lax185574Proofs.EvalRam.ReadFml
import Lax185574Proofs.Words.TreeBfs

/-!
The table of the evaluation, as functions of the arrays.

The program fills two tables indexed by the positions `p` of the code `F`
of the formula. `en[p]` is the end of the subformula whose code starts at
`p`, and `val[p · N + c]` is its value at the node `c` of the list of
nodes. The rows are filled from the last position to the first, so the
subformulas of a formula are evaluated before it. This module gives the
values that the program computes (`endVal`, `cellVal`) and shows that at
the start of a subformula they are its end and its value (`endVal_eq`,
`cellVal_eq`), given that the later rows are right.
-/

namespace Lax185574Proofs.EvalRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-- The end of the subformula at `p`, from the ends of the later
positions, capped at `L`. -/
def endVal (F EN : List ℕ) (L p : ℕ) : ℕ :=
  let op := xg F p
  min L (if op < 4 then p + 3 else if op < 6 then p + 4 else if op = 6 then xg EN (p + 1)
    else if op = 7 then xg EN (xg EN (p + 1)) else if op = 8 then xg EN (p + 3) else p + 1)

/-- The frame at `fr` of `X` is the atom code of length `al` at `p` of
`F` (for `al` equal to `3` or `4`). -/
def fm (X F : List ℕ) (fr p al : ℕ) : Bool :=
  xg X fr == al && xg X (fr + 1) == xg F p && xg X (fr + 2) == xg F (p + 1) &&
    xg X (fr + 3) == xg F (p + 2) && (al == 3 || xg X (fr + 4) == xg F (p + 3))

/-- Some of the first `n` frames of the list at `y` is the atom code at
`p`. -/
def atHit (X F : List ℕ) (y p al n : ℕ) : Bool :=
  (List.range n).any fun j => fm X F (frPos X y j) p al

/-- Some of the first `n` extension frames of the list at `e` has the
guard at `p + 1` and a child, listed from `ch` on, where row `p + 3` holds
`1`. -/
def exHit (X F VL : List ℕ) (N e p ch n : ℕ) : Bool :=
  (List.range n).any fun j =>
    xg X (frPos X e j + 1) == xg F (p + 1) && xg VL ((p + 3) * N + (ch + j)) == 1

/-- The value that the program stores for the position `p` and the node
`c`. -/
def cellVal (X F PA DA FA EN VL : List ℕ) (q N p c : ℕ) : ℕ :=
  let y := xg PA c
  let op := xg F p
  if op < 6 then bv (atHit X F y p (if op < 4 then 3 else 4) (xg X y))
  else if op = 6 then (if xg VL ((p + 1) * N + c) = 1 then 0 else 1)
  else if op = 7 then
    (if xg VL ((p + 1) * N + c) = 1 then (if xg VL (xg EN (p + 1) * N + c) = 1 then 1 else 0) else 0)
  else if op = 8 then
    (if q - xg DA c = 0 then 0
      else bv (exHit X F VL N (listEnd X y) p (xg FA c) (xg X (listEnd X y))))
  else 0

theorem cellVal_le (X F PA DA FA EN VL : List ℕ) (q N p c : ℕ) :
    cellVal X F PA DA FA EN VL q N p c ≤ 1 := by
  simp only [cellVal]
  split_ifs <;> first | exact bv_le _ | omega

/-- The rows after `p` are right: at the start of every subformula
after `p`, the end and the values are those of the subformula. -/
def RowsOK (X F PA DA EN VL : List ℕ) (q N L p0 : ℕ) : Prop :=
  ∀ p, p0 ≤ p → p < L → ∀ (ℓ : ℕ) (ψ : DistFO ℓ) (r : List ℕ), F.drop p = code ψ ++ r →
    p + (code ψ).length ≤ L →
      xg EN p = p + (code ψ).length ∧
        ∀ c < N, xg VL (p * N + c) = bv (evalW X ψ (xg PA c) (q - xg DA c))

theorem xg_drop {F : List ℕ} {p : ℕ} {w r : List ℕ} (h : F.drop p = w ++ r) {i : ℕ}
    (hi : i < w.length) : xg F (p + i) = w[i] := by
  have := congrArg (·[i]?) h
  simp only [List.getElem?_drop, List.getElem?_append_left hi, List.getElem?_eq_getElem hi] at this
  simp [xg, List.getD_eq_getElem?_getD, this]

theorem drop_tail {F : List ℕ} {p : ℕ} {u w r : List ℕ} (h : F.drop p = u ++ (w ++ r)) :
    F.drop (p + u.length) = w ++ r := drop_add_of_drop h

/-- **The ends.** -/
theorem endVal_eq {X F PA DA EN VL : List ℕ} {q N L p : ℕ}
    (hrows : RowsOK X F PA DA EN VL q N L (p + 1)) {ℓ : ℕ} (ψ : DistFO ℓ) {r : List ℕ}
    (hF : F.drop p = code ψ ++ r) (hL : p + (code ψ).length ≤ L) :
    endVal F EN L p = p + (code ψ).length := by
  have h0 := xg_drop (i := 0) hF (one_le_code_length ψ)
  cases ψ with
  | eq i j => simp [code] at h0 hL; simp [endVal, h0, code]; omega
  | edge i j => simp [code] at h0 hL; simp [endVal, h0, code]; omega
  | nonEdge i j => simp [code] at h0 hL; simp [endVal, h0, code]; omega
  | color Y i => simp [code] at h0 hL; simp [endVal, h0, code]; omega
  | distLe s i j => simp [code] at h0 hL; simp [endVal, h0, code]; omega
  | distColorLt s Y i => simp [code] at h0 hL; simp [endVal, h0, code]; omega
  | not φ =>
    have hF1 : F.drop (p + 1) = code φ ++ r := drop_tail (u := [6]) (by simpa [code] using hF)
    have hl : (code (DistFO.not φ)).length = (code φ).length + 1 := by simp [code]
    have := one_le_code_length φ
    obtain ⟨he, -⟩ := hrows (p + 1) le_rfl (by omega) _ φ r hF1 (by omega)
    simp [code] at h0
    simp only [endVal, h0, hl]
    simp [he]; omega
  | and φ χ =>
    have hF1 : F.drop (p + 1) = code φ ++ (code χ ++ r) :=
      drop_tail (u := [7]) (by simpa [code] using hF)
    have hF2 : F.drop (p + 1 + (code φ).length) = code χ ++ r := drop_tail hF1
    have hl : (code (DistFO.and φ χ)).length = (code φ).length + (code χ).length + 1 := by
      simp [code] <;> omega
    have := one_le_code_length φ
    have := one_le_code_length χ
    obtain ⟨he, -⟩ := hrows (p + 1) le_rfl (by omega) _ φ _ hF1 (by omega)
    obtain ⟨he2, -⟩ := hrows (p + 1 + (code φ).length) (by omega) (by omega) _ χ r hF2 (by omega)
    simp [code] at h0
    simp only [endVal, h0, hl]
    simp [he, he2]; omega
  | exLocal i s φ =>
    have hF3 : F.drop (p + 3) = code φ ++ r := drop_tail (u := [8, i.val, s]) (by simpa [code] using hF)
    have hl : (code (DistFO.exLocal i s φ)).length = (code φ).length + 3 := by simp [code]
    have := one_le_code_length φ
    obtain ⟨he, -⟩ := hrows (p + 3) (by omega) (by omega) _ φ r hF3 (by omega)
    simp [code] at h0
    simp only [endVal, h0, hl]
    simp [he]; omega

theorem any_range_iff (n : ℕ) (f : ℕ → Bool) : (List.range n).any f = true ↔ ∃ j < n, f j = true := by
  simp [List.any_eq_true]

/-- An atom code of length `3` or `4` is a frame of the list `ws` exactly
if the frame test succeeds. -/
theorem atHit_iff {X F : List ℕ} {y p : ℕ} {ws : List (List ℕ)} {r r' w : List ℕ}
    (hx : X.drop y = toWord ws ++ r) (hF : F.drop p = w ++ r') (hw : w.length = 3 ∨ w.length = 4) :
    atHit X F y p w.length (xg X y) = true ↔ w ∈ ws := by
  obtain ⟨h0, -, hfr, -⟩ := listAt hx
  rw [atHit, any_range_iff, h0]
  have key : ∀ j (hj : j < ws.length), fm X F (frPos X y j) p w.length = true ↔ ws[j] = w := by
    intro j hj
    obtain ⟨hl, -, hd⟩ := hfr j hj
    generalize frPos X y j = fr at hl hd
    generalize ws[j] = u at hl hd
    have hu : ∀ i (hi : i < u.length), xg X (fr + 1 + i) = u[i] := fun i hi => xg_drop hd hi
    have hw' : ∀ i (hi : i < w.length), xg F (p + i) = w[i] := fun i hi => xg_drop hF hi
    simp only [fm, hl, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨hlen, h1⟩, h2⟩, h3⟩, h4⟩
      apply List.ext_getElem hlen
      intro i hi1 hi2
      rw [← hu i hi1, ← hw' i hi2]
      have hi4 : i < 4 := by omega
      interval_cases i
      · simpa using h1
      · simpa using h2
      · simpa using h3
      · rcases h4 with h4 | h4
        · omega
        · simpa [Nat.add_comm] using h4
      all_goals omega
    · rintro rfl
      refine ⟨⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [show fr + 1 = fr + 1 + 0 by rfl, hu 0 (by omega), show p = p + 0 by rfl, hw' 0 (by omega)]
      · rw [show fr + 2 = fr + 1 + 1 by omega, hu 1 (by omega), hw' 1 (by omega)]
      · rw [show fr + 3 = fr + 1 + 2 by omega, hu 2 (by omega), hw' 2 (by omega)]
      · rcases hw with hw | hw
        · exact Or.inl hw
        · right
          rw [show fr + 4 = fr + 1 + 3 by omega, hu 3 (by omega), hw' 3 (by omega)]
  constructor
  · rintro ⟨j, hj, hm⟩
    rw [← (key j hj).1 hm]; exact List.getElem_mem hj
  · intro hm
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hm
    exact ⟨j, hj, (key j hj).2 hjw⟩

/-- The facts about a listed node `c` that the evaluation uses. -/
structure NodeOK (X PA DA FA : List ℕ) (q N c : ℕ) : Prop where
  dep_le : xg DA c ≤ q
  fc_le : xg FA c ≤ N
  node : NodeAt X (xg PA c) (q - xg DA c)
  child : xg DA c < q → ∀ j < xg X (listEnd X (xg PA c)), xg FA c + j < N ∧
    xg PA (xg FA c + j) = frPos X (listEnd X (xg PA c)) j + 2 ∧ xg DA (xg FA c + j) = xg DA c + 1

/-- **The values.** At the start of a subformula, given the later rows,
the program stores the value of the subformula at the node. -/
theorem cellVal_eq {X F PA DA FA EN VL : List ℕ} {q N L p c : ℕ}
    (hrows : RowsOK X F PA DA EN VL q N L (p + 1)) (hc : NodeOK X PA DA FA q N c) (hcN : c < N)
    {ℓ : ℕ} (ψ : DistFO ℓ) {r : List ℕ}
    (hF : F.drop p = code ψ ++ r) (hL : p + (code ψ).length ≤ L) :
    cellVal X F PA DA FA EN VL q N p c = bv (evalW X ψ (xg PA c) (q - xg DA c)) := by
  obtain ⟨ws, r0, hws⟩ := hc.node.atomList
  have hlw : listWords X (xg PA c) = ws := listWords_eq hws
  have hatom : ∀ (w : List ℕ), F.drop p = w ++ r → (w.length = 3 ∨ w.length = 4) →
      atHit X F (xg PA c) p w.length (xg X (xg PA c)) = decide (w ∈ listWords X (xg PA c)) := by
    intro w hw hl
    rw [hlw]
    by_cases hm : w ∈ ws
    · rw [decide_eq_true hm]; exact (atHit_iff hws hw hl).2 hm
    · rw [decide_eq_false hm]; exact Bool.eq_false_iff.mpr fun h => hm ((atHit_iff hws hw hl).1 h)
  have h0 := xg_drop (i := 0) hF (one_le_code_length ψ)
  cases ψ with
  | eq i j =>
    have := hatom _ hF (by simp [code])
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [← this]; simp [code]
  | edge i j =>
    have := hatom _ hF (by simp [code])
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [← this]; simp [code]
  | nonEdge i j =>
    have := hatom _ hF (by simp [code])
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [← this]; simp [code]
  | color Y i =>
    have := hatom _ hF (by simp [code])
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [← this]; simp [code]
  | distLe s i j =>
    have := hatom _ hF (by simp [code])
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [← this]; simp [code]
  | distColorLt s Y i =>
    have := hatom _ hF (by simp [code])
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [← this]; simp [code]
  | not φ =>
    have hF1 : F.drop (p + 1) = code φ ++ r := drop_tail (u := [6]) (by simpa [code] using hF)
    have hl : (code (DistFO.not φ)).length = (code φ).length + 1 := by simp [code]
    have := one_le_code_length φ
    obtain ⟨-, hv⟩ := hrows (p + 1) le_rfl (by omega) _ φ r hF1 (by omega)
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [hv c hcN]
    generalize evalW X φ (xg PA c) (q - xg DA c) = b
    cases b <;> simp
  | and φ χ =>
    have hF1 : F.drop (p + 1) = code φ ++ (code χ ++ r) :=
      drop_tail (u := [7]) (by simpa [code] using hF)
    have hF2 : F.drop (p + 1 + (code φ).length) = code χ ++ r := drop_tail hF1
    have hl : (code (DistFO.and φ χ)).length = (code φ).length + (code χ).length + 1 := by
      simp [code] <;> omega
    have := one_le_code_length φ
    have := one_le_code_length χ
    obtain ⟨he, hv⟩ := hrows (p + 1) le_rfl (by omega) _ φ _ hF1 (by omega)
    obtain ⟨-, hv2⟩ := hrows (p + 1 + (code φ).length) (by omega) (by omega) _ χ r hF2 (by omega)
    simp [code] at h0
    simp only [cellVal, h0, evalW]
    rw [hv c hcN, he, hv2 c hcN]
    generalize evalW X φ (xg PA c) (q - xg DA c) = b
    generalize evalW X χ (xg PA c) (q - xg DA c) = b'
    cases b <;> cases b' <;> simp
  | exLocal i s φ =>
    have hF3 : F.drop (p + 3) = code φ ++ r := drop_tail (u := [8, i.val, s]) (by simpa [code] using hF)
    have hl : (code (DistFO.exLocal i s φ)).length = (code φ).length + 3 := by simp [code]
    have := one_le_code_length φ
    obtain ⟨-, hv⟩ := hrows (p + 3) (by omega) (by omega) _ φ r hF3 (by omega)
    have hg : xg F (p + 1) = i.val := by
      have := xg_drop (i := 1) hF (by simp [code])
      simpa [code] using this
    simp [code] at h0
    simp only [cellVal, h0]
    simp only [show (8 : ℕ) < 6 ↔ False by decide, if_false, show (8 : ℕ) = 6 ↔ False by decide,
      show (8 : ℕ) = 7 ↔ False by decide, if_true]
    obtain ⟨h, hh⟩ : ∃ h, q - xg DA c = h := ⟨_, rfl⟩
    rw [hh]
    cases h with
    | zero => simp [evalW]
    | succ h =>
      simp only [Nat.add_one_ne_zero, if_false, evalW]
      congr 1
      have hlt : xg DA c < q := by omega
      rw [Bool.eq_iff_iff, exHit, any_range_iff, decide_eq_true_iff]
      refine exists_congr fun j => and_congr_right fun hj => ?_
      obtain ⟨hjN, hpj, hdj⟩ := hc.child hlt j hj
      rw [hv _ hjN, hpj, hdj, hg, show q - (xg DA c + 1) = h by omega]
      simp [bv_eq_one]

end Lax185574Proofs.EvalRam
