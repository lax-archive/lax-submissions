import Lax185574Proofs.Words.TreeJobs

/-!
The jobs of a one-pass transformation describe the transformed tree.

The answers to the jobs of `rawJobs` are the canonical forms of the sets
of the transformed nodes, from the last node to the first, and the result
of the last item `rawFinal` is the header followed by `treeOut` of the
root (`rawJobs_out`). The jobs are well formed (`rawJobs_wf`).
-/

namespace Lax185574Proofs.Words

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

theorem flatMap_two_getElem? {α β : Type*} (f : α → List β) (hf : ∀ a, (f a).length = 2) :
    ∀ (L : List α) (i b : ℕ) (hi : i < L.length), b < 2 → (L.flatMap f)[2 * i + b]? = (f L[i])[b]?
  | [], i, b, hi, _ => by simp at hi
  | a :: L, 0, b, _, hb => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
    rw [List.getElem?_append_left (by rw [hf]; exact hb)]
  | a :: L, i + 1, b, hi, hb => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by rw [hf]; omega), hf]
    rw [show 2 * (i + 1) + b - 2 = 2 * i + b by omega]
    exact flatMap_two_getElem? f hf L i b (by simp at hi; omega) hb

theorem length_flatMap_two {α β : Type*} (f : α → List β) (hf : ∀ a, (f a).length = 2) :
    ∀ L : List α, (L.flatMap f).length = 2 * L.length
  | [] => rfl
  | a :: L => by simp only [List.flatMap_cons, List.length_append, hf, length_flatMap_two f hf L,
      List.length_cons]; ring

section Raw

variable (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (X : List ℕ) (q N : ℕ)
  (PA DA FA : List ℕ)

theorem length_nodeJobs (c : ℕ) : (nodeJobs sub gsub X q N PA DA FA c).length = 2 := rfl

theorem length_rawJobs : (rawJobs sub gsub X q N PA DA FA).length = 2 * N := by
  rw [rawJobs, length_flatMap_two _ (length_nodeJobs sub gsub X q N PA DA FA)]; simp

theorem rawJobs_getElem? {c : ℕ} (hc : c < N) (b : ℕ) (hb : b < 2) :
    (rawJobs sub gsub X q N PA DA FA)[2 * (N - 1 - c) + b]? =
      (nodeJobs sub gsub X q N PA DA FA c)[b]? := by
  rw [rawJobs, flatMap_two_getElem? _ (length_nodeJobs sub gsub X q N PA DA FA) _ _ _ (by simp; omega) hb]
  congr 2
  rw [List.getElem_reverse]; simp; omega

theorem allResults_getD {js : List Job} {j : ℕ} (hj : j < js.length) :
    (allResults js).getD j [] = jobAnswer ((allResults js).take j) (js.getD j (0, [])) := by
  rw [List.getD_eq_getElem?_getD, allResults_getElem? js j hj, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem take_getD {Rs : List (List ℕ)} {j r : ℕ} (hr : r < j) : (Rs.take j).getD r [] = Rs.getD r [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hr]

theorem jobs_getD {c : ℕ} (hc : c < N) (b : ℕ) (hb : b < 2) :
    (rawJobs sub gsub X q N PA DA FA).getD (2 * (N - 1 - c) + b) (0, []) =
      (nodeJobs sub gsub X q N PA DA FA c).getD b (0, []) := by
  rw [List.getD_eq_getElem?_getD, rawJobs_getElem? sub gsub X q N PA DA FA hc b hb,
    List.getD_eq_getElem?_getD]

theorem nodeJob0 {c : ℕ} (hc : c < N) :
    (rawJobs sub gsub X q N PA DA FA).getD (2 * (N - 1 - c)) (0, []) =
      (0, atomCands sub (DA.getD c 0) X (PA.getD c 0)) := by
  have := jobs_getD sub gsub X q N PA DA FA hc 0 (by norm_num)
  rw [Nat.add_zero] at this
  rw [this, nodeJobs, List.getD_cons_zero]

theorem nodeJob1 {c : ℕ} (hc : c < N) :
    (rawJobs sub gsub X q N PA DA FA).getD (2 * (N - 1 - c) + 1) (0, []) =
      (1, if DA.getD c 0 < q then
        exCands gsub (DA.getD c 0) X (listEnd X (PA.getD c 0))
          (fun i => refsOf q N DA (FA.getD c 0 + i)) (xg X (listEnd X (PA.getD c 0)))
      else []) := by
  rw [jobs_getD sub gsub X q N PA DA FA hc 1 (by norm_num), nodeJobs, List.getD_cons_succ,
    List.getD_cons_zero]

theorem jobQuery_zero (Rs : List (List ℕ)) (l : List (List ℕ)) : jobQuery Rs (0, l) = l := by
  have : expandItem Rs 0 = id := by funext u; simp [expandItem]
  simp [jobQuery, this]

theorem jobQuery_one (Rs : List (List ℕ)) (l : List (List ℕ)) :
    jobQuery Rs (1, l) = l.map (expandItem Rs 1) := rfl

/-- The expansion of the extension candidates, given the answers of the
children. -/
theorem exCands_expand (hscan : ScannedOK X q N N PA DA FA) {c : ℕ} (hc : c < N)
    (hdq : DA.getD c 0 < q) {h : ℕ} (hh : q - DA.getD c 0 = h + 1) (Rs : List (List ℕ))
    (hR : ∀ c', c < c' → c' < N →
      ((refsOf q N DA c').map fun r => Rs.getD r []).flatten =
        treeOut sub gsub (q - DA.getD c' 0) (DA.getD c' 0) X (PA.getD c' 0))
    (hRs : ∀ c', c < c' → c' < N → ∀ r ∈ refsOf q N DA c',
      (Rs.take (2 * (N - 1 - c) + 1)).getD r [] = Rs.getD r []) :
    (exCands gsub (DA.getD c 0) X (listEnd X (PA.getD c 0))
        (fun i => refsOf q N DA (FA.getD c 0 + i)) (xg X (listEnd X (PA.getD c 0)))).map
        (expandItem (Rs.take (2 * (N - 1 - c) + 1)) 1) =
      extCands sub gsub h (DA.getD c 0) X (PA.getD c 0) := by
  rw [exCands, extCands, List.map_filterMap]
  apply List.filterMap_congr
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨hlt, hfc, hrest⟩ := hscan c hc
  obtain ⟨hcn, hpos, hdep⟩ := hrest hdq i hi
  cases gsub (DA.getD c 0) (xg X (frPos X (listEnd X (PA.getD c 0)) i + 1)) with
  | none => rfl
  | some g =>
    simp only [Option.map_some, Option.some.injEq, expandItem, Nat.one_ne_zero, if_false,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.singleton_append,
      List.cons.injEq, true_and]
    have e1 : ((refsOf q N DA (FA.getD c 0 + i)).map fun r =>
        (Rs.take (2 * (N - 1 - c) + 1)).getD r []) =
        ((refsOf q N DA (FA.getD c 0 + i)).map fun r => Rs.getD r []) :=
      List.map_congr_left fun r hr => hRs _ (by omega) hcn r hr
    rw [e1, hR _ (by omega) hcn, hdep, hpos, show q - (DA.getD c 0 + 1) = h by omega]

theorem refsOf_lt_of {c c' : ℕ} (hcc : c < c') (hc' : c' < N) :
    ∀ r ∈ refsOf q N DA c', r < 2 * (N - 1 - c) + 1 := by
  intro r hr
  simp only [refsOf] at hr
  split_ifs at hr <;> simp at hr <;> omega

/-- The answers to the jobs of the nodes. -/
theorem refs_expand (hnodes : NodesOK X q N PA DA) (hscan : ScannedOK X q N N PA DA FA) :
    ∀ m c, N - 1 - c = m → c < N →
      ((refsOf q N DA c).map fun r => (allResults (rawJobs sub gsub X q N PA DA FA)).getD r []).flatten =
        treeOut sub gsub (q - DA.getD c 0) (DA.getD c 0) X (PA.getD c 0) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c hcm hc
  have hlen : (rawJobs sub gsub X q N PA DA FA).length = 2 * N := length_rawJobs sub gsub X q N PA DA FA
  have hdq : DA.getD c 0 ≤ q := (hnodes c hc).1
  have hA : (allResults (rawJobs sub gsub X q N PA DA FA)).getD (2 * (N - 1 - c)) [] =
      toWord (sortedDistinct (atomCands sub (DA.getD c 0) X (PA.getD c 0))) := by
    rw [allResults_getD (by omega), nodeJob0 sub gsub X q N PA DA FA hc, jobAnswer, jobQuery_zero]
  by_cases hdq' : DA.getD c 0 < q
  · obtain ⟨h, hh⟩ : ∃ h, q - DA.getD c 0 = h + 1 := ⟨q - DA.getD c 0 - 1, by omega⟩
    have hE : (allResults (rawJobs sub gsub X q N PA DA FA)).getD (2 * (N - 1 - c) + 1) [] =
        toWord (sortedDistinct (extCands sub gsub h (DA.getD c 0) X (PA.getD c 0))) := by
      rw [allResults_getD (by omega), nodeJob1 sub gsub X q N PA DA FA hc, if_pos hdq', jobAnswer,
        jobQuery_one]
      rw [exCands_expand sub gsub X q N PA DA FA hscan hc hdq' hh _
        (fun c' hcc hc' => ih (N - 1 - c') (by omega) c' rfl hc')
        (fun c' hcc hc' r hr => take_getD (refsOf_lt_of q N DA hcc hc' r hr))]
    have hrc : refsOf q N DA c = [2 * (N - 1 - c), 2 * (N - 1 - c) + 1] := by
      simp only [refsOf, if_pos hdq']
    rw [hrc]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hA, hE, hh, treeOut_succ]
  · have hdq2 : DA.getD c 0 = q := by omega
    have hrc : refsOf q N DA c = [2 * (N - 1 - c)] := by simp only [refsOf, if_neg hdq']
    rw [hrc]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hA, hdq2, Nat.sub_self, treeOut_zero]

/-- **The result of the jobs.** -/
theorem rawJobs_out (k olv : ℕ) (hnodes : NodesOK X q N PA DA) (hscan : ScannedOK X q N N PA DA FA)
    (hp0 : PA.getD 0 0 = 0) (hd0 : DA.getD 0 0 = 0) (hN : 1 ≤ N) :
    jobsOut (rawJobs sub gsub X q N PA DA FA) (rawFinal k q olv N) = [k, q, olv] ++ treeOut sub gsub q 0 X 0 := by
  have h := refs_expand sub gsub X q N PA DA FA hnodes hscan (N - 1 - 0) 0 rfl (by omega)
  rw [hp0, hd0, Nat.sub_zero] at h
  have hr : (rawFinal k q olv N).2 = refsOf q N DA 0 := by
    simp only [rawFinal, refsOf, hd0, Nat.sub_zero]
  unfold jobsOut finalOut
  rw [hr, show jobResults (rawJobs sub gsub X q N PA DA FA) [] = allResults (rawJobs sub gsub X q N PA DA FA)
    from rfl, h]
  rfl

theorem rawJobs_getElem_eq {j : ℕ} (hj : j < (rawJobs sub gsub X q N PA DA FA).length) :
    (rawJobs sub gsub X q N PA DA FA)[j] = (rawJobs sub gsub X q N PA DA FA).getD j (0, []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- **The jobs are well formed.** -/
theorem rawJobs_wf (k olv : ℕ) (hscan : ScannedOK X q N N PA DA FA) (hN : 1 ≤ N) :
    JobsWF (rawJobs sub gsub X q N PA DA FA) (rawFinal k q olv N) := by
  have hlen := length_rawJobs sub gsub X q N PA DA FA
  refine ⟨fun j hj hf u hu => ?_, fun r hr => ?_⟩
  · rw [rawJobs_getElem_eq sub gsub X q N PA DA FA hj] at hf hu
    rw [hlen] at hj
    obtain ⟨i, b, hb, rfl⟩ : ∃ i b, b < 2 ∧ j = 2 * i + b := ⟨j / 2, j % 2, Nat.mod_lt _ (by norm_num),
      (Nat.div_add_mod j 2).symm⟩
    have hi : i = N - 1 - (N - 1 - i) := by omega
    have hcN : N - 1 - i < N := by omega
    rw [hi] at hf hu
    interval_cases b
    · rw [Nat.add_zero, nodeJob0 sub gsub X q N PA DA FA hcN] at hf
      exact absurd rfl hf
    · rw [nodeJob1 sub gsub X q N PA DA FA hcN] at hu
      simp only at hu
      split_ifs at hu with hdq
      · rw [exCands, List.mem_filterMap] at hu
        obtain ⟨i', hi', hg⟩ := hu
        rw [List.mem_range] at hi'
        cases hgs : gsub (DA.getD (N - 1 - i) 0)
            (xg X (frPos X (listEnd X (PA.getD (N - 1 - i) 0)) i' + 1)) with
        | none => rw [hgs] at hg; simp at hg
        | some g =>
          rw [hgs] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          subst hg
          obtain ⟨hlt, hfc, hrest⟩ := hscan (N - 1 - i) hcN
          obtain ⟨hcn, -, -⟩ := hrest hdq i' hi'
          refine ⟨by simp, fun r hr => ?_⟩
          simp only [List.drop_succ_cons, List.drop_zero] at hr
          have := refsOf_lt_of q N DA (c := N - 1 - i) (by omega) hcn r hr
          rw [← hi] at this
          omega
      · simp at hu
  · rw [hlen]
    simp only [rawFinal] at hr
    split_ifs at hr <;> simp at hr <;> omega

theorem length_toWord_extCands_le (h d ℓ : ℕ) (p : ℕ) (t : Node (h + 1) ℓ) (r : List ℕ)
    (hx : X.drop p = toWord t ++ r) :
    (toWord (extCands sub gsub h d X p)).length + (toWord (Node.atoms t).words).length ≤
      (toWord t).length := by
  obtain ⟨h1, h2⟩ := nodeSplit hx
  have h0 := (listAt h2).1
  unfold extCands
  rw [h0]
  obtain ⟨hc, ht⟩ := total_filterMap_le _ (Node.exts t).words rfl
    (fun j => (gsub d (xg X (frPos X (listEnd X p) j + 1))).map fun g =>
      g :: treeOut sub gsub h (d + 1) X (frPos X (listEnd X p) j + 2))
    (fun j hj u hu => by
      obtain ⟨a, ha, haw⟩ := getElem_words hj
      obtain ⟨-, r', hr'⟩ := extFrame h2 hj haw
      simp only [Option.map_eq_some_iff] at hu
      obtain ⟨g, -, rfl⟩ := hu
      rw [← haw, toWord_ext]
      simpa using length_treeOut_le sub gsub h (d + 1) (ℓ + 1) X _ a.2 r' hr')
  rw [toWord_node_succ, List.length_append]
  simp only [length_toWord_words]
  omega

/-- Every query is at most as long as the root word. -/
theorem rawJobs_query_le (hnodes : NodesOK X q N PA DA) (hscan : ScannedOK X q N N PA DA FA)
    (hX : X ≠ []) {j : ℕ} (hj : j < 2 * N) :
    (toWord (jobQuery ((allResults (rawJobs sub gsub X q N PA DA FA)).take j)
      ((rawJobs sub gsub X q N PA DA FA).getD j (0, [])))).length ≤ X.length := by
  obtain ⟨i, b, hb, rfl⟩ : ∃ i b, b < 2 ∧ j = 2 * i + b := ⟨j / 2, j % 2, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod j 2).symm⟩
  have hi : i = N - 1 - (N - 1 - i) := by omega
  have hcN : N - 1 - i < N := by omega
  obtain ⟨hdq, ℓ, t, r, hxt⟩ := hnodes (N - 1 - i) hcN
  rw [hi]
  interval_cases b
  · rw [Nat.add_zero, nodeJob0 sub gsub X q N PA DA FA hcN, jobQuery_zero]
    obtain ⟨ws, r', hws⟩ := NodeAt.atomList ⟨ℓ, t, r, hxt⟩
    have h1 := toWord_atomCands_le hws sub (DA.getD (N - 1 - i) 0)
    have h2 : (toWord ws).length ≤ X.length := by
      have := congrArg List.length hws
      simp only [List.length_drop, List.length_append] at this; omega
    omega
  · rw [nodeJob1 sub gsub X q N PA DA FA hcN]
    by_cases hd : DA.getD (N - 1 - i) 0 < q
    · rw [if_pos hd, jobQuery_one]
      obtain ⟨h', hh'⟩ : ∃ h', q - DA.getD (N - 1 - i) 0 = h' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [exCands_expand sub gsub X q N PA DA FA hscan hcN hd hh' _
        (fun c' hcc hc' => refs_expand sub gsub X q N PA DA FA hnodes hscan _ c' rfl hc')
        (fun c' hcc hc' r hr => take_getD (refsOf_lt_of q N DA hcc hc' r hr))]
      have hn : NodeAt X (PA.getD (N - 1 - i) 0) (h' + 1) := hh' ▸ ⟨ℓ, t, r, hxt⟩
      obtain ⟨ℓ', t', r', hxt'⟩ := hn
      have := length_toWord_extCands_le sub gsub X h' (DA.getD (N - 1 - i) 0) ℓ' (PA.getD (N - 1 - i) 0) t' r' hxt'
      have ht' : (toWord t').length ≤ X.length := by
        have := congrArg List.length hxt'
        simp only [List.length_drop, List.length_append] at this; omega
      omega
    · rw [if_neg hd, jobQuery_one, List.map_nil]
      have : 0 < X.length := List.length_pos_iff.mpr hX
      simp [toWord_words, frames]; omega

end Raw

/-- The size of a list of jobs whose queries are short. -/
theorem jobSize_le (js : List Job) (fin : List ℕ × List ℕ) (Q : ℕ)
    (hq : ∀ j < js.length,
      (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length ≤ Q) :
    jobSize js fin ≤ (toWord (js, fin)).length + js.length + 2 * (js.length * Q) +
      (jobsOut js fin).length := by
  have h1 : total (allResults js) ≤ js.length * Q := by
    unfold total
    rw [List.length_flatten]
    have := List.sum_le_card_nsmul ((allResults js).map List.length) Q (by
      intro n hn
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hn
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      have hj' : j < js.length := by rwa [length_allResults] at hj
      have e := allResults_getD (js := js) hj'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at e
      rw [e, jobAnswer]
      exact le_trans (length_toWord_sortedDistinct_le _) (hq j hj'))
    simpa [length_allResults] using this
  have h2 : ((List.range js.length).map fun j =>
      (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length).sum ≤ js.length * Q := by
    have := List.sum_le_card_nsmul ((List.range js.length).map fun j =>
      (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length) Q (by
        intro n hn
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hn
        exact hq j (List.mem_range.mp hj))
    simpa using this
  unfold jobSize
  rw [length_allResults]
  omega

end Lax185574Proofs.Words
