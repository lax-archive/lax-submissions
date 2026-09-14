/-
The value of the product weighted automaton of
`RequestProject/PartB/PairWeighted.lean`.

The automaton `pairW K M N` has the states `(p, q, i)` with `i ∈ {0,1}` and the
transitions

  `(p, q, 0) --a / K ^ |x|--> (p', q', 0)`,
  `(p, q, 0) --a / iota K x--> (p', q', 1)`,
  `(p, q, 1) --a / 1--> (p', q', 1)`,

one for each pair of transitions `p --a/x--> p'` of `M` and `q --a/y--> q'` of
`N` reading the same letter `a`.  Writing `sumFrom` for the sum of the weights
of the accepting runs from a state, an induction on the input string gives

  `sumFrom (p, q, 1) w = nRun M p w * nRun N q w`,
  `sumFrom (p, q, 0) w = iRun K M p w * nRun N q w`,

where `nRun` counts the accepting runs of a code from a state and `iRun` sums
the numbers `iota K` representing their outputs; the second identity says that a
run of the product splits at the position where the bit switches, and that
`iota` is additive on the left.  Summing over the initial states gives the value
of the automaton (`pairW_eval`).
-/
import Lax132576Proofs.Source.PartB.PairWeighted
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace PairWeighted

open LabAut CodeMerge Iota RunList

/-! ## Sums over lists -/

lemma sum_map_mul_left {α : Type} (c : ℚ) (l : List α) (g : α → ℚ) :
    (l.map (fun x => c * g x)).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, mul_add]

lemma sum_map_filter {α : Type} (l : List α) (p : α → Bool) (g : α → ℚ) :
    ((l.filter p).map g).sum = (l.map (fun x => if p x then g x else 0)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      by_cases h : p x = true <;> simp [h, ih]

lemma sum_map_sprod {α β : Type} (l₁ : List α) (l₂ : List β) (g : α × β → ℚ) :
    ((l₁ ×ˢ l₂).map g).sum = (l₁.map (fun a => (l₂.map (fun b => g (a, b))).sum)).sum := by
  show ((l₁.flatMap (fun a => l₂.map (Prod.mk a))).map g).sum = _
  rw [RunList.sum_map_flatMap]
  exact congrArg List.sum (List.map_congr_left (fun a _ => by rw [List.map_map]; rfl))

lemma sum_mul_sum {α β : Type} (l₁ : List α) (l₂ : List β) (X : α → ℚ) (Y : β → ℚ) :
    (l₁.map X).sum * (l₂.map Y).sum
      = (l₁.map (fun a => (l₂.map (fun b => X a * Y b)).sum)).sum := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, ih]
      rw [sum_map_mul_left]

lemma cast_sum_map {α : Type} (l : List α) (g : α → ℕ) :
    (((l.map g).sum : ℕ) : ℚ) = (l.map (fun x => ((g x : ℕ) : ℚ))).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih]

/-! ## Codes with no accepting run -/

/-- If a code has no accepting run over a string, then the sum over its
accepting runs of the numbers representing their outputs is `0`. -/
lemma iAll_eq_zero {K : ℕ} {M : RelCode} (hMa : LetterAtomic M) {w : List ℕ}
    (h : ∀ v, ¬ codeRel M w v) : iAll K M w = 0 := by
  rw [iAll]
  refine List.sum_eq_zero (fun x hx => ?_)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  have hnil : RunList.accRuns M.1 M.2.2 p w = [] := by
    by_contra hne
    obtain ⟨ρ, hρ⟩ := List.exists_mem_of_ne_nil _ hne
    exact h _ (codeRel_of_mem_accRuns hMa hp hρ)
  rw [iRun, hnil, List.map_nil, List.sum_nil]

/-! ## The sum of the weights of the accepting runs from a state -/

/-- The sum of the weights of the accepting runs of the product automaton from a
state. -/
def sumFrom (K : ℕ) (M N : RelCode) (q : ℕ) (w : List ℕ) : ℚ :=
  ((RunList.accRuns (qTrans K M N) (pairFin M N) q w).map weightOf).sum

lemma sumFrom_nil (K : ℕ) (M N : RelCode) (q : ℕ) :
    sumFrom K M N q [] = if q ∈ pairFin M N then 1 else 0 := by
  rw [sumFrom, RunList.accRuns_nil']
  by_cases h : q ∈ pairFin M N <;> simp [h]

/-- The recursion for the sum of the weights of the accepting runs, obtained
from the recursion for the accepting runs of a letter-atomic automaton. -/
lemma sumFrom_cons (K : ℕ) (M N : RelCode) (q a : ℕ) (w : List ℕ) :
    sumFrom K M N q (a :: w)
      = ((qTrans K M N).map (fun t => if t.1 = q ∧ t.2.1 = [a] then
          t.2.2.1 * sumFrom K M N t.2.2.2 w else 0)).sum := by
  rw [sumFrom, RunList.sum_map_accRuns_cons]
  refine congrArg List.sum (List.map_congr_left (fun t _ => ?_))
  by_cases hc : t.1 = q ∧ t.2.1 = [a]
  · rw [if_pos hc, if_pos hc, sumFrom]
    rw [← sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left (fun ts _ => by simp [weightOf_cons]))
  · rw [if_neg hc, if_neg hc]

/-- The sum over the transitions of the product automaton, rewritten as a double
sum over the transitions of the two codes. -/
lemma sum_qTrans (K : ℕ) (M N : RelCode) (G : RunList.T ℚ → ℚ) :
    ((qTrans K M N).map G).sum
      = (M.1.map (fun s => (N.1.map (fun t =>
          if s.2.1 = t.2.1 then
            G (sel K (s, t) 0) + G (sel K (s, t) 1) + G (sel K (s, t) 2) else 0)).sum)).sum := by
  rw [qTrans, List.map_map]
  show (((((M.1 ×ˢ N.1).filter (fun z => decide (z.1.2.1 = z.2.2.1))) ×ˢ [0, 1, 2]).map
    (fun zi => G (sel K zi.1 zi.2))).sum) = _
  rw [sum_map_sprod]
  rw [sum_map_filter]
  rw [sum_map_sprod]
  refine congrArg List.sum (List.map_congr_left (fun s _ => ?_))
  refine congrArg List.sum (List.map_congr_left (fun t _ => ?_))
  by_cases h : s.2.1 = t.2.1
  · simp [h]
    ring
  · simp [h]

/-! ## The value of the product automaton from a state -/

lemma sel_zero (K : ℕ) (s t : CodeMerge.Tr) :
    sel K (s, t) 0 =
      (st s.1 t.1 0, s.2.1, ((K ^ s.2.2.1.length : ℕ) : ℚ), st s.2.2.2 t.2.2.2 0) := by
  simp [sel, bits]

lemma sel_one (K : ℕ) (s t : CodeMerge.Tr) :
    sel K (s, t) 1 =
      (st s.1 t.1 0, s.2.1, ((iota K s.2.2.1 : ℕ) : ℚ), st s.2.2.2 t.2.2.2 1) := by
  simp [sel, bits]

lemma sel_two (K : ℕ) (s t : CodeMerge.Tr) :
    sel K (s, t) 2 = (st s.1 t.1 1, s.2.1, (1 : ℚ), st s.2.2.2 t.2.2.2 1) := by
  simp [sel, bits]

lemma st_eq_zero_iff (p q p' q' : ℕ) : st p q 0 = st p' q' 0 ↔ (p = p' ∧ q = q') :=
  ⟨fun h => ⟨(st_inj (by norm_num) (by norm_num) h).1,
      (st_inj (by norm_num) (by norm_num) h).2.1⟩,
    fun h => by rw [h.1, h.2]⟩

lemma st_eq_one_iff (p q p' q' : ℕ) : st p q 1 = st p' q' 1 ↔ (p = p' ∧ q = q') :=
  ⟨fun h => ⟨(st_inj (by norm_num) (by norm_num) h).1,
      (st_inj (by norm_num) (by norm_num) h).2.1⟩,
    fun h => by rw [h.1, h.2]⟩

lemma st_one_ne_zero' (p q p' q' : ℕ) : st p q 1 ≠ st p' q' 0 :=
  st_ne (by norm_num) (by norm_num) (by norm_num)

lemma st_zero_ne_one' (p q p' q' : ℕ) : st p q 0 ≠ st p' q' 1 :=
  st_ne (by norm_num) (by norm_num) (by norm_num)

lemma sumFrom_rec (K : ℕ) (M N : RelCode) :
    ∀ (w : List ℕ) (p q : ℕ),
      sumFrom K M N (st p q 0) w = (iRun K M p w : ℚ) * (nRun N q w : ℚ) ∧
        sumFrom K M N (st p q 1) w = (nRun M p w : ℚ) * (nRun N q w : ℚ) := by
  intro w
  induction w with
  | nil =>
      intro p q
      constructor
      · rw [sumFrom_nil, if_neg not_mem_pairFin_zero, iRun_nil]
        simp
      · rw [sumFrom_nil, nRun_nil, nRun_nil]
        by_cases hp : p ∈ M.2.2
        · by_cases hq : q ∈ N.2.2
          · rw [if_pos (mem_pairFin.2 ⟨hp, hq⟩)]; simp [hp, hq]
          · rw [if_neg (fun h => hq (mem_pairFin.1 h).2)]; simp [hq]
        · rw [if_neg (fun h => hp (mem_pairFin.1 h).1)]; simp [hp]
  | cons a w ih =>
      intro p q
      constructor
      · rw [sumFrom_cons, sum_qTrans, iRun_cons, nRun_cons, cast_sum_map, cast_sum_map,
          sum_mul_sum]
        refine congrArg List.sum (List.map_congr_left (fun s _ => ?_))
        refine congrArg List.sum (List.map_congr_left (fun t _ => ?_))
        rw [sel_zero, sel_one, sel_two]
        by_cases hst : s.2.1 = t.2.1
        · rw [if_pos hst]
          by_cases hsa : s.2.1 = [a]
          · have hta : t.2.1 = [a] := by rw [← hst, hsa]
            by_cases hs1 : s.1 = p
            · by_cases ht1 : t.1 = q
              · have hz : st s.1 t.1 0 = st p q 0 := (st_eq_zero_iff _ _ _ _).2 ⟨hs1, ht1⟩
                rw [if_pos ⟨hz, hsa⟩, if_pos ⟨hz, hsa⟩,
                  if_neg (fun h : st s.1 t.1 1 = st p q 0 ∧ _ => st_one_ne_zero' _ _ _ _ h.1),
                  if_pos ⟨hs1, hsa⟩, if_pos ⟨ht1, hta⟩,
                  (ih s.2.2.2 t.2.2.2).1, (ih s.2.2.2 t.2.2.2).2]
                push_cast
                ring
              · have hz : ¬ (st s.1 t.1 0 = st p q 0) :=
                  fun h => ht1 ((st_eq_zero_iff _ _ _ _).1 h).2
                rw [if_neg (fun h : st s.1 t.1 0 = st p q 0 ∧ _ => hz h.1),
                  if_neg (fun h : st s.1 t.1 0 = st p q 0 ∧ _ => hz h.1),
                  if_neg (fun h : st s.1 t.1 1 = st p q 0 ∧ _ => st_one_ne_zero' _ _ _ _ h.1),
                  if_neg (fun h : t.1 = q ∧ _ => ht1 h.1)]
                simp
            · have hz : ¬ (st s.1 t.1 0 = st p q 0) :=
                fun h => hs1 ((st_eq_zero_iff _ _ _ _).1 h).1
              rw [if_neg (fun h : st s.1 t.1 0 = st p q 0 ∧ _ => hz h.1),
                if_neg (fun h : st s.1 t.1 0 = st p q 0 ∧ _ => hz h.1),
                if_neg (fun h : st s.1 t.1 1 = st p q 0 ∧ _ => st_one_ne_zero' _ _ _ _ h.1),
                if_neg (fun h : s.1 = p ∧ _ => hs1 h.1)]
              simp
          · rw [if_neg (fun h : _ ∧ s.2.1 = [a] => hsa h.2),
              if_neg (fun h : _ ∧ s.2.1 = [a] => hsa h.2),
              if_neg (fun h : _ ∧ s.2.1 = [a] => hsa h.2),
              if_neg (fun h : s.1 = p ∧ s.2.1 = [a] => hsa h.2)]
            simp
        · rw [if_neg hst]
          by_cases hsa : s.2.1 = [a]
          · rw [if_neg (fun h : t.1 = q ∧ t.2.1 = [a] => hst (by rw [hsa, h.2]))]
            simp
          · rw [if_neg (fun h : s.1 = p ∧ s.2.1 = [a] => hsa h.2)]
            simp
      · rw [sumFrom_cons, sum_qTrans, nRun_cons, nRun_cons, cast_sum_map, cast_sum_map,
          sum_mul_sum]
        refine congrArg List.sum (List.map_congr_left (fun s _ => ?_))
        refine congrArg List.sum (List.map_congr_left (fun t _ => ?_))
        rw [sel_zero, sel_one, sel_two]
        by_cases hst : s.2.1 = t.2.1
        · rw [if_pos hst,
            if_neg (fun h : st s.1 t.1 0 = st p q 1 ∧ _ => st_zero_ne_one' _ _ _ _ h.1),
            if_neg (fun h : st s.1 t.1 0 = st p q 1 ∧ _ => st_zero_ne_one' _ _ _ _ h.1)]
          by_cases hsa : s.2.1 = [a]
          · have hta : t.2.1 = [a] := by rw [← hst, hsa]
            by_cases hs1 : s.1 = p
            · by_cases ht1 : t.1 = q
              · have hz : st s.1 t.1 1 = st p q 1 := (st_eq_one_iff _ _ _ _).2 ⟨hs1, ht1⟩
                rw [if_pos ⟨hz, hsa⟩, if_pos ⟨hs1, hsa⟩, if_pos ⟨ht1, hta⟩,
                  (ih s.2.2.2 t.2.2.2).2]
                push_cast
                ring
              · have hz : ¬ (st s.1 t.1 1 = st p q 1) :=
                  fun h => ht1 ((st_eq_one_iff _ _ _ _).1 h).2
                rw [if_neg (fun h : st s.1 t.1 1 = st p q 1 ∧ _ => hz h.1),
                  if_neg (fun h : t.1 = q ∧ _ => ht1 h.1)]
                simp
            · have hz : ¬ (st s.1 t.1 1 = st p q 1) :=
                fun h => hs1 ((st_eq_one_iff _ _ _ _).1 h).1
              rw [if_neg (fun h : st s.1 t.1 1 = st p q 1 ∧ _ => hz h.1),
                if_neg (fun h : s.1 = p ∧ _ => hs1 h.1)]
              simp
          · rw [if_neg (fun h : _ ∧ s.2.1 = [a] => hsa h.2),
              if_neg (fun h : s.1 = p ∧ s.2.1 = [a] => hsa h.2)]
            simp
        · rw [if_neg hst]
          by_cases hsa : s.2.1 = [a]
          · rw [if_neg (fun h : t.1 = q ∧ t.2.1 = [a] => hst (by rw [hsa, h.2]))]
            simp
          · rw [if_neg (fun h : s.1 = p ∧ s.2.1 = [a] => hsa h.2)]
            simp

/-- From a state with the bit `0` the product automaton computes the sum, over
the pairs of accepting runs, of the number representing the output of the first
one. -/
lemma sumFrom_zero (K : ℕ) (M N : RelCode) (p q : ℕ) (w : List ℕ) :
    sumFrom K M N (st p q 0) w = (iRun K M p w : ℚ) * (nRun N q w : ℚ) :=
  (sumFrom_rec K M N w p q).1

/-- From a state with the bit `1` the product automaton just counts the pairs of
accepting runs. -/
lemma sumFrom_one (K : ℕ) (M N : RelCode) (p q : ℕ) (w : List ℕ) :
    sumFrom K M N (st p q 1) w = (nRun M p w : ℚ) * (nRun N q w : ℚ) :=
  (sumFrom_rec K M N w p q).2

/-! ## The value of the product automaton -/

/-- **The value of the product automaton.**  On a nonempty string it is the
product of the sum over the accepting runs of `M` of the number representing
their output with the number of accepting runs of `N`. -/
theorem pairW_eval (K : ℕ) (M N : RelCode) (hMa : LetterAtomic M)
    (hMnd : M.1.Nodup) (hNnd : N.1.Nodup) (hMc : Canonical M) (hNc : Canonical N)
    (hMi : M.2.1.Nodup) (hNi : N.2.1.Nodup) {w : List ℕ} (hw : w ≠ []) :
    wcodeEval (pairW K M N) w = (iAll K M w : ℚ) * (nAll N w : ℚ) := by
  have hsum : (wcodeAut (pairW K M N)).wEval w
      = ((RunList.allRuns (qTrans K M N) (pairInit M N) (pairFin M N) w).map weightOf).sum :=
    RunList.wEval_eq_sum (delta_pairW K M N) (init_pairW M N) (final_pairW M N)
      (qTrans_atomic hMa) (qTrans_nodup hMnd hNnd hMc hNc) (pairInit_nodup hMi hNi) hw
  show (wcodeAut (pairW K M N)).wEval w = _
  rw [hsum, RunList.allRuns, RunList.sum_map_flatMap]
  have hstep : ∀ x ∈ pairInit M N,
      ((RunList.accRuns (qTrans K M N) (pairFin M N) x w).map weightOf).sum
        = sumFrom K M N x w := fun _ _ => rfl
  rw [List.map_congr_left hstep, pairInit, List.map_map]
  have hcongr : ∀ z ∈ M.2.1 ×ˢ N.2.1,
      ((fun x => sumFrom K M N x w) ∘ fun z : ℕ × ℕ => st z.1 z.2 0) z
        = (iRun K M z.1 w : ℚ) * (nRun N z.2 w : ℚ) :=
    fun z _ => sumFrom_zero K M N z.1 z.2 w
  rw [List.map_congr_left hcongr, sum_map_sprod, iAll, nAll, cast_sum_map, cast_sum_map,
    sum_mul_sum]

/-- The product automaton has no accepting run over the empty string: its
initial states carry the bit `0` and its final states the bit `1`. -/
theorem pairW_eval_nil (K : ℕ) (M N : RelCode) (hMa : LetterAtomic M) :
    wcodeEval (pairW K M N) [] = 0 := by
  have hempty : (wcodeAut (pairW K M N)).acceptingOn [] = ∅ := by
    ext ts
    simp only [Set.mem_empty_iff_false, iff_false, LabAut.acceptingOn, Set.mem_setOf_eq, not_and]
    rintro ⟨q, hq, p, hp, hpath⟩ hin
    match ts with
    | [] =>
        have hqp : q = p := Path.eq_of_nil hpath
        obtain ⟨z, -, hz⟩ := List.mem_map.1 (show q ∈ pairInit M N from hq)
        obtain ⟨z', -, hz'⟩ := List.mem_map.1 (show p ∈ pairFin M N from hp)
        rw [hqp] at hz
        exact st_ne (by norm_num) (by norm_num) (by norm_num) (hz.trans hz'.symm)
    | t :: ts' =>
        obtain ⟨-, ht, -⟩ := Path.cons_inv hpath
        obtain ⟨b, hb⟩ := qTrans_atomic hMa _ ((delta_pairW K M N t).1 ht)
        rw [LabAut.inputOf_cons, hb] at hin
        exact absurd hin (by simp)
  show (wcodeAut (pairW K M N)).wEval [] = 0
  rw [LabAut.wEval, hempty, finsum_mem_empty]

end PairWeighted
end Lax132576Proofs.Transducers
