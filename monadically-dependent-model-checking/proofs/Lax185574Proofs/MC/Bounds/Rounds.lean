import Lax185574Proofs.MC.Asm.Fit

/-!
The sizes of the rounds of the glue program.

Let the heads of the rounds have length and largest entry at most `H1`,
and length plus window length at most `H2`, and let the queries and
answers of the calls be small for `CB` with colors at most `maxEntry x`.
Then the input and the output of round `j` have total length at most
`3 H2 + 2 CB + 7`, plus `|x|` in round `0`, and their entries are at most
`|x| + maxEntry x + H1 + CB + 1`. The bound on the lengths does not
involve `x` beyond round `0`, which is what makes the time linear in the
number of steps.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Words Lax185574Proofs.RamSim Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs

theorem finAns_small {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    (finAns s q φ).length ≤ 2 ∧ ∀ e ∈ finAns s q φ, e ≤ 1 := by
  unfold finAns
  split_ifs
  · simp only [callYE, word_simps, List.length_cons, List.length_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    refine ⟨by omega, fun e he => ?_⟩
    rcases he with rfl | rfl
    · omega
    · split_ifs <;> omega
  · simp

theorem getD_mem_le {l : List ℕ} (i : ℕ) : l.getD i 0 ≤ maxEntry l := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[i]? with _ | e
  · simp
  · exact le_maxEntry (List.mem_of_getElem? h)

theorem getD_append_left {l u : List ℕ} {i : ℕ} (h : i < l.length) :
    (l ++ u).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

section

variable {n : ℕ} {x : List ℕ} {s : List (PartialGraph (Fin n))} {q : ℕ}
  {φ : Lax3.FirstOrder.FO 0} {steps : List Step} {hd : ℕ → List ℕ} {H1 H2 CB : ℕ}

/-- **Sizes of the rounds.** -/
theorem round_small
    (hhd : ∀ j < (pcalls n steps).length,
      hd j ≠ [] ∧ (hd j).head? ≠ some 0 ∧ (hd j).getD 1 0 + 3 = (hd j).length)
    (hH1 : ∀ j < (pcalls n steps).length, (hd j).length + maxEntry (hd j) ≤ H1)
    (hH2 : ∀ j < (pcalls n steps).length, (hd j).length + (hd j).getD 2 0 ≤ H2)
    (hcall : ∀ c ∈ pcalls n steps, Small (callQ s q φ c) CB (maxEntry x) ∧
      Small (callY s q φ c) CB (maxEntry x))
    {j : ℕ} (hj : j ≤ (pcalls n steps).length) :
    (pU x s q φ (pcalls n steps) hd (finAns s q φ) j).length +
        (glueOut s q φ (pcalls n steps) hd (finAns s q φ) j).length + 1 ≤
      (if j = 0 then x.length else 0) + 3 * H2 + 2 * CB + 7 ∧
    ∀ e ∈ pU x s q φ (pcalls n steps) hd (finAns s q φ) j ++
        glueOut s q φ (pcalls n steps) hd (finAns s q φ) j,
      e ≤ x.length + maxEntry x + H1 + CB + 1 := by
  obtain ⟨fa1, fa2⟩ := finAns_small s q φ
  set cs := pcalls n steps
  set ans := finAns s q φ
  -- the output of round `j`
  have hout : (glueOut s q φ cs hd ans j).length ≤ H2 + CB + 3 ∧
      ∀ e ∈ glueOut s q φ cs hd ans j, e ≤ H1 + CB + maxEntry x + 1 := by
    rcases hc : cs[j]? with _ | c
    · simp only [glueOut, hc, List.length_cons, List.mem_cons]
      refine ⟨by omega, fun e he => ?_⟩
      rcases he with rfl | he
      · omega
      · have := fa2 e he; omega
    · have hjl : j < cs.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hc; simp at hc
      have hcm : c ∈ cs := List.mem_of_getElem? hc
      obtain ⟨⟨q1, q2⟩, -⟩ := hcall c hcm
      have h1 := hH1 j hjl
      have h2 := hH2 j hjl
      simp only [glueOut, hc, List.length_append, List.mem_append]
      refine ⟨by omega, fun e he => ?_⟩
      rcases he with he | he
      · have := le_maxEntry he; omega
      · have := q2 e he; omega
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · -- round `0`
    have hU : pU x s q φ cs hd ans 0 = [0, x.length] ++ x ++ [] ++ [0] := by
      simp [pU, pA, pB, lpU, lpA0]
    have hU0 : ∀ e ∈ pU x s q φ cs hd ans 0, e ≤ x.length + maxEntry x := by
      rw [hU]; intro e he
      simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at he
      rcases he with ((rfl | rfl) | he) | rfl
      · omega
      · omega
      · have := le_maxEntry he; omega
      · omega
    have hl0 : (pU x s q φ cs hd ans 0).length = x.length + 3 := by rw [hU]; simp
    have ho := hout.1
    refine ⟨by rw [hl0]; simp only [if_true]; omega, fun e he => ?_⟩
    rcases List.mem_append.1 he with h | h
    · exact le_trans (hU0 e h) (by omega)
    · have := hout.2 e h; omega
  -- round `i + 1`, after call `i`
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hil : i < cs.length := by omega
  obtain ⟨c, hc⟩ : ∃ c, cs[i]? = some c := ⟨cs[i], List.getElem?_eq_getElem hil⟩
  have hcm : c ∈ cs := List.mem_of_getElem? hc
  obtain ⟨⟨q1, q2⟩, ⟨y1, y2⟩⟩ := hcall c hcm
  obtain ⟨hne, -, hlen⟩ := hhd i hil
  have h1 := hH1 i hil
  have h2 := hH2 i hil
  have hA : pA x s q φ cs hd ans (i + 1) = hd i ++ callQ s q φ c := by
    simp only [pA, glueOut, hc]
  have hB : pB s q φ cs (i + 1) = callY s q φ c := by simp only [pB, hc]
  have hU : pU x s q φ cs hd ans (i + 1) = lpU x (hd i ++ callQ s q φ c) (callY s q φ c) := by
    simp only [pU, hA, hB]
  have g0 : (hd i ++ callQ s q φ c).getD 0 0 = (hd i).getD 0 0 := getD_append_left (by omega)
  have g1 : (hd i ++ callQ s q φ c).getD 1 0 = (hd i).getD 1 0 := getD_append_left (by omega)
  have g2 : (hd i ++ callQ s q φ c).getD 2 0 = (hd i).getD 2 0 := getD_append_left (by omega)
  have m0 := getD_mem_le (l := hd i) 0
  have m1 := getD_mem_le (l := hd i) 1
  rw [hU]
  simp only [lpU, g0, g1, g2, List.length_append, List.length_cons, List.length_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Nat.add_one_ne_zero, if_false]
  have l1 := List.length_take_le ((hd i).getD 2 0) (x.drop ((hd i ++ callQ s q φ c).getD 3 0))
  have l2 := List.length_take_le ((hd i).getD 1 0) ((hd i ++ callQ s q φ c).drop 3)
  have ho := hout.1
  refine ⟨by omega, fun e he => ?_⟩
  rcases he with (((((rfl | rfl) | he) | he) | (rfl | he)) | he)
  · omega
  · omega
  · have := le_maxEntry (List.mem_of_mem_drop (List.mem_of_mem_take he)); omega
  · have he' := List.mem_of_mem_drop (List.mem_of_mem_take he)
    rcases List.mem_append.1 he' with he' | he'
    · have := le_maxEntry he'; omega
    · have := q2 e he'; omega
  · omega
  · have := y2 e he; omega
  · have := hout.2 e he; omega

end

/-- A sum over the positions of a list, bounded by an extra term per
position and a cost per entry. -/
theorem sum_range_le_map {α : Type*} (h : α → ℕ) :
    ∀ (F E : ℕ → ℕ) (l : List α), (∀ j (hj : j < l.length), F j ≤ E j + h l[j]) →
      ∑ j ∈ Finset.range l.length, F j ≤ ∑ j ∈ Finset.range l.length, E j + (l.map h).sum
  | _, _, [], _ => by simp
  | F, E, a :: l, hF => by
    rw [List.length_cons, Finset.sum_range_succ', Finset.sum_range_succ', List.map_cons,
      List.sum_cons]
    have h1 := sum_range_le_map h (fun j => F (j + 1)) (fun j => E (j + 1)) l (fun j hj => by
      have := hF (j + 1) (by simp; omega)
      rwa [List.getElem_cons_succ] at this)
    have h0 := hF 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    omega

/-- **Cost of the rounds.** If round `j` costs at most `N` (in round `0`
only) plus the cost of its call, then all rounds with a call cost at most
`N + (m + 1) B`. -/
theorem sum_rounds_le {n A B N : ℕ} (hA : A ≤ B) (steps : List Step)
    (F : ℕ → ℕ) (hF : ∀ j (hj : j < (pcalls n steps).length),
      F j ≤ (if j = 0 then N else 0) + callCost A B (pcalls n steps)[j]) :
    ∑ j ∈ Finset.range (pcalls n steps).length, F j ≤ N + (steps.length + 1) * B := by
  have h1 := sum_range_le_map (callCost A B) F _ (pcalls n steps) hF
  have h2 := sum_cost_pcalls (n := n) hA steps
  have h3 : ∑ j ∈ Finset.range (pcalls n steps).length, (if j = 0 then N else 0) ≤ N := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> omega
  omega

end Lax185574Proofs.MC
