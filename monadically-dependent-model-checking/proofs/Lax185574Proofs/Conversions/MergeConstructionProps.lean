import Lax185574Proofs.Conversions.MergeConstructionRun
import Lax185574Proofs.Conversions.BetterMergeFunction

/-!
The construction script of cl:from-merge-to-construction produces a
construction sequence of the graph, of radius-r width at most
max(1, w_r), and its word has small entries.
-/

namespace Lax185574Proofs.Conversions.MergeConstruction

open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.SequenceEncoding
open Lax185574.MergeSequences Lax185574.Partitions Lax185574.GraphBalls
open Lax185574.ConstructionWidth Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574Proofs.WithinDistBasics

open Classical

noncomputable section

variable {n : ℕ} {G : SimpleGraph (Fin n)} {ms : List (Setoid (Fin n) × SimpleGraph (Fin n))}

variable (G ms) in
/-- The state at the start of stage `j`: the coloring of `𝒫_j` and the
pairs of the blocks before `j`. -/
def stageStart (j : ℕ) : PartialGraph (Fin n) := mk G (col ms j) (resolvedAt ms j)

variable (G ms) in
/-- A partial graph of stage `j`: its coloring is constant on the parts
of `𝒫_j`, and its resolved pairs are those resolved at the start of
the stage together with some rectangles of the stage. -/
def Good (j : ℕ) (H : PartialGraph (Fin n)) : Prop :=
  ∃ (c : Fin n → ℕ) (R : SimpleGraph (Fin n)), H = mk G c R ∧
    (∀ x y, part ms j x y → c x = c y) ∧
    ∃ L : List (Fin n × Fin n), (∀ p ∈ L, Resolves ms j p) ∧
      R = resolvedAt ms j ⊔ doneGraph ms j L

variable (G ms) in
/-- Two consecutive partial graphs of the run belong to one stage. -/
def SameStage (H H' : PartialGraph (Fin n)) : Prop :=
  ∃ j < ms.length, Good G ms j H ∧ Good G ms j H'

theorem good_resolveState (j : ℕ) (L : List (Fin n × Fin n)) (hL : ∀ p ∈ L, Resolves ms j p) :
    Good G ms j (resolveState G ms j L) :=
  ⟨col ms j, _, rfl, fun x y h => (col_eq_iff ms j x y).2 h, L, hL, rfl⟩

theorem good_mergeState (hm : IsMergeSequence G ms) (j : ℕ) (D : List (Fin n)) :
    Good G ms j (mergeState G ms j D) := by
  refine ⟨mergeCol ms j D, _, rfl, fun x y h => ?_, resolvePairs ms j,
    fun p hp => (mem_resolvePairs ms j p).1 hp, (resolvedAt_sup_doneGraph ms j).symm⟩
  have h1 : rep (part ms j) x = rep (part ms j) y := rep_eq_of_rel _ h
  have h2 : col ms (j + 1) x = col ms (j + 1) y := (col_eq_iff ms _ x y).2 (part_succ_le hm j h)
  have h3 : col ms j x = col ms j y := (col_eq_iff ms _ x y).2 h
  simp only [mergeCol, h1, h2, h3]

theorem resolveState_nil (j : ℕ) : resolveState G ms j [] = stageStart G ms j := by
  simp [resolveState, stageStart, doneGraph_nil]

/-- **One stage.** The steps of stage `j` lead from the start of stage `j`
to the start of stage `j + 1`, and consecutive partial graphs belong to
stage `j`. -/
theorem stage_run (hm : IsMergeSequence G ms) {j : ℕ} (hj : j < ms.length) :
    (stageSteps G ms j).foldl apply (stageStart G ms j) = stageStart G ms (j + 1) ∧
      ((stageSteps G ms j).scanl apply (stageStart G ms j)).IsChain (SameStage G ms) := by
  -- the resolves
  have hR := chain_scanl_of_states apply (SameStage G ms) ((resolvePairs ms j).map (resolveStep G ms j))
    (fun k => resolveState G ms j ((resolvePairs ms j).take k)) (fun k hk => by
      simp only [List.length_map] at hk
      have hk' : k < (resolvePairs ms j).length := hk
      have htake : (resolvePairs ms j).take (k + 1) =
          (resolvePairs ms j).take k ++ [(resolvePairs ms j)[k]] := List.take_succ_eq_append_getElem hk'
      have hsub : ∀ k, ∀ p ∈ (resolvePairs ms j).take k, Resolves ms j p :=
        fun k p hp => (mem_resolvePairs ms j p).1 (List.mem_of_mem_take hp)
      refine ⟨?_, j, hj, good_resolveState j _ (hsub k), good_resolveState j _ (hsub (k + 1))⟩
      rw [List.getElem_map, htake]
      exact apply_resolveStep hm hj _ _)
  -- the merges
  have hM := chain_scanl_of_states apply (SameStage G ms) ((mergeSources ms j).map (mergeStep ms j))
    (fun k => mergeState G ms j ((mergeSources ms j).take k)) (fun k hk => by
      simp only [List.length_map] at hk
      have htake : (mergeSources ms j).take (k + 1) =
          (mergeSources ms j).take k ++ [(mergeSources ms j)[k]] := List.take_succ_eq_append_getElem hk
      refine ⟨?_, j, hj, good_mergeState hm j _, good_mergeState hm j _⟩
      rw [List.getElem_map, htake]
      have hnd : (mergeSources ms j).Nodup := (List.nodup_finRange n).filter _
      refine apply_mergeStep hm j _ ((mem_mergeSources j _).1 (List.getElem_mem hk)) ?_
      intro hmem
      obtain ⟨i, hi, hik⟩ := List.mem_iff_getElem.1 hmem
      rw [List.getElem_take] at hik
      have hi' : i < k := by simp at hi; omega
      have := (hnd.getElem_inj_iff (i := i) (j := k) (hi := by omega) (hj := hk)).1 hik
      omega)
  obtain ⟨hR1, hR2⟩ := hR
  obtain ⟨hM1, hM2⟩ := hM
  have e0 : resolveState G ms j ((resolvePairs ms j).take 0) = stageStart G ms j := by
    simp [resolveState_nil]
  have e1 : resolveState G ms j ((resolvePairs ms j).take ((resolvePairs ms j).map
      (resolveStep G ms j)).length) = mergeState G ms j ((mergeSources ms j).take 0) := by
    simp only [List.length_map, List.take_length, List.take_zero, mergeState_nil, resolveState]
    rw [resolvedAt_sup_doneGraph]
  have e2 : mergeState G ms j ((mergeSources ms j).take ((mergeSources ms j).map
      (mergeStep ms j)).length) = stageStart G ms (j + 1) := by
    simp only [List.length_map, List.take_length]
    exact mergeState_all hm j
  rw [e0] at hR1 hR2
  rw [e1] at hR1
  rw [e2] at hM1
  refine ⟨?_, ?_⟩
  · rw [stageSteps, List.foldl_append, hR1, hM1]
  · refine chain_scanl_append _ _ _ _ _ hR2 ?_
    rw [hR1]
    exact hM2

/-- **All stages.** -/
theorem stages_run (hm : IsMergeSequence G ms) :
    ∀ k ≤ ms.length,
      ((List.range k).flatMap (stageSteps G ms)).foldl apply (stageStart G ms 0) =
          stageStart G ms k ∧
        (((List.range k).flatMap (stageSteps G ms)).scanl apply (stageStart G ms 0)).IsChain
          (SameStage G ms) := by
  intro k hk
  induction k with
  | zero => exact ⟨rfl, List.isChain_singleton _⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨h1, h2⟩ := stage_run hm (j := k) (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨by rw [List.foldl_append, ih1, h1], chain_scanl_append _ _ _ _ _ ih2 ?_⟩
    rw [ih1]
    exact h2

theorem stageStart_zero (hm : IsMergeSequence G ms) :
    stageStart G ms 0 = unresolved (script G ms).colors := by
  refine partialGraph_ext ?_ ?_ ?_
  · simp [stageStart, mk, resolvedAt_zero, unresolved]
  · simp [stageStart, mk, resolvedAt_zero, unresolved]
  · funext x
    simp [stageStart, mk, unresolved, script, col, part_zero hm, rep_bot]

theorem run_eq (hm : IsMergeSequence G ms) :
    (script G ms).run = (script G ms).steps.scanl apply (stageStart G ms 0) := by
  rw [Script.run, stageStart_zero hm]

theorem foldl_run (hm : IsMergeSequence G ms) :
    (script G ms).steps.foldl apply (stageStart G ms 0) = stageStart G ms ms.length :=
  (stages_run hm ms.length le_rfl).1

theorem chain_run (hm : IsMergeSequence G ms) :
    (script G ms).run.IsChain (SameStage G ms) := by
  rw [run_eq hm]
  exact (stages_run hm ms.length le_rfl).2

theorem good_stageStart (j : ℕ) : Good G ms j (stageStart G ms j) := by
  rw [← resolveState_nil]
  exact good_resolveState j [] (by simp)

/-- Every partial graph of the run belongs to some stage. -/
theorem good_run (hm : IsMergeSequence G ms) (t : ℕ) (ht : t < (script G ms).run.length) :
    ∃ j < ms.length, Good G ms j (script G ms).run[t] := by
  have hc := List.isChain_iff_getElem.1 (chain_run hm)
  by_cases h1 : t + 1 < (script G ms).run.length
  · obtain ⟨j, hj, h, -⟩ := hc t h1
    exact ⟨j, hj, h⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · refine ⟨0, List.length_pos_of_ne_nil hm.1, ?_⟩
      have : (script G ms).run[0] = stageStart G ms 0 := by
        simp only [run_eq hm, List.getElem_scanl_zero]
      rw [this]
      exact good_stageStart 0
    · obtain ⟨j, hj, -, h⟩ := hc (t - 1) (by omega)
      refine ⟨j, hj, ?_⟩
      have e : t - 1 + 1 = t := by omega
      simp only [e] at h
      exact h

/-! ### The merges are proper -/

theorem merge_ne {s : Step} (hs : s ∈ (script G ms).steps) {P Q : ℕ} (h : s = .merge P Q) :
    P ≠ Q := by
  simp only [script, List.mem_flatMap, List.mem_range] at hs
  obtain ⟨j, -, hs⟩ := hs
  simp only [stageSteps, List.mem_append, List.mem_map] at hs
  rcases hs with ⟨p, -, rfl⟩ | ⟨v, hv, rfl⟩
  · unfold resolveStep at h
    split_ifs at h
  · simp only [mergeStep, Step.merge.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := ((mem_mergeSources j v).1 hv).2
    exact fun h' => this (Fin.ext h')

/-! ### Construction sequence -/

/-- **The run is a construction sequence of `G`.** -/
theorem isConstructionSequence (hm : IsMergeSequence G ms) :
    IsConstructionSequence G (script G ms).run := by
  have hne : (script G ms).run ≠ [] := List.scanl_ne_nil
  refine ⟨hne, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Script.run, List.head_scanl]
    refine ⟨rfl, rfl, fun x y h => ?_⟩
    exact Fin.ext h
  · intro t ht
    have e := List.getElem_succ_scanl (f := apply) (b := unresolved (script G ms).colors)
      (l := (script G ms).steps) (i := t) ht
    simp only [Script.run] at ht ⊢
    rw [e]
    have htl : t < (script G ms).steps.length := by simp at ht; omega
    generalize hs : (script G ms).steps[t] = s
    have hmem : s ∈ (script G ms).steps := hs ▸ List.getElem_mem htl
    cases s with
    | merge P Q => exact ⟨P, Q, Or.inl ⟨merge_ne hmem rfl, rfl⟩⟩
    | resolvePos P Q => exact ⟨P, Q, Or.inr (Or.inl rfl)⟩
    | resolveNeg P Q => exact ⟨P, Q, Or.inr (Or.inr rfl)⟩
  · intro u v
    have : (script G ms).run.getLast hne = stageStart G ms ms.length := by
      simp only [run_eq hm, List.getLast_scanl, foldl_run hm]
    rw [this]
    simp only [stageStart, mk, col]
    exact congrArg Fin.val (rep_eq_of_rel _ (by rw [part_last hm (by omega)]; trivial))
  · have : (script G ms).run.getLast hne = stageStart G ms ms.length := by
      simp only [run_eq hm, List.getLast_scanl, foldl_run hm]
    rw [this]
    simp [stageStart, mk, resolvedAt_length hm]
  · have : (script G ms).run.getLast hne = stageStart G ms ms.length := by
      simp only [run_eq hm, List.getLast_scanl, foldl_run hm]
    rw [this]
    simp [stageStart, mk, resolvedAt_length hm]

/-! ### Width -/

theorem resolved_le_rel (hm : IsMergeSequence G ms) {j : ℕ} {L : List (Fin n × Fin n)}
    (hL : ∀ p ∈ L, Resolves ms j p) :
    resolvedAt ms j ⊔ doneGraph ms j L ≤ rel ms (j + 1) :=
  sup_le ((resolvedAt_le_rel hm j).trans (rel_succ_le hm j)) (doneGraph_le_rel ms j L hL)

theorem partCount_le_mergeWidth {j : ℕ} (hj : j + 1 < ms.length) (r : ℕ) (v : Fin n) :
    partCount (part ms j) (graphBall (rel ms (j + 1)) r {v}) ≤ mergeWidth r ms := by
  have e1 : part ms j = ms[j].1 := by simp [part, show j < ms.length by omega]
  have e2 : rel ms (j + 1) = ms[j + 1].2 := by simp [rel, hj]
  rw [e1, e2]
  refine le_csSup ⟨n, ?_⟩ ⟨j, hj, v, rfl⟩
  rintro K ⟨t, ht, w, rfl⟩
  exact (Set.ncard_image_le (Set.toFinite _)).trans ((Set.ncard_le_card _).trans (by simp))

/-- The ball of a good partial graph lies in the ball of `R_{j+1}`. -/
theorem ball_subset (hm : IsMergeSequence G ms) {j : ℕ} {c : Fin n → ℕ} {L : List (Fin n × Fin n)}
    (hL : ∀ p ∈ L, Resolves ms j p) (r : ℕ) (v : Fin n) :
    (mk G c (resolvedAt ms j ⊔ doneGraph ms j L)).ball r v ⊆ graphBall (rel ms (j + 1)) r {v} := by
  intro u hu
  simp only [PartialGraph.ball, resolved_mk, Set.mem_ofPred_eq] at hu
  exact ⟨v, rfl, withinDist_le_graph (resolved_le_rel hm hL) hu⟩

/-- The number of colors meeting a set, for a coloring constant on the
parts of `𝒫_j`. -/
theorem ncard_color_le {j : ℕ} {c : Fin n → ℕ} (hc : ∀ x y, part ms j x y → c x = c y)
    (X : Set (Fin n)) : (c '' X).ncard ≤ partCount (part ms j) X :=
  Lax185574Proofs.FormulaRank.ncard_image_le_of_factor c (Quotient.mk (part ms j))
    (fun a _ b _ h => hc a b (Quotient.exact h)) (Set.toFinite _)

theorem width_good (hm : IsMergeSequence G ms) {j : ℕ} (hj : j < ms.length)
    {H : PartialGraph (Fin n)} (hH : Good G ms j H) (r : ℕ) (v : Fin n) :
    (H.color '' H.ball r v).ncard ≤ max 1 (mergeWidth r ms) := by
  obtain ⟨c, R, rfl, hc, L, hL, rfl⟩ := hH
  by_cases hj1 : j + 1 < ms.length
  · refine le_max_of_le_right ((ncard_color_le hc _).trans ?_)
    exact (Lax185574Proofs.Conversions.BetterMerge.partCount_mono _ (ball_subset hm hL r v)).trans
      (partCount_le_mergeWidth hj1 r v)
  · refine le_max_of_le_left ?_
    have htop : part ms j = ⊤ := part_last hm (by omega)
    have : (mk G c (resolvedAt ms j ⊔ doneGraph ms j L)).color ''
        (mk G c (resolvedAt ms j ⊔ doneGraph ms j L)).ball r v ⊆ {c v} := by
      rintro _ ⟨u, -, rfl⟩
      exact hc u v (by rw [htop]; trivial)
    exact (Set.ncard_le_ncard this (Set.finite_singleton _)).trans (by simp)

/-- **The width bound** `max(1, w_r)`. -/
theorem constructionWidth_le (hm : IsMergeSequence G ms) (r : ℕ) :
    constructionWidth r (script G ms).run ≤ max 1 (mergeWidth r ms) := by
  apply csSup_le'
  rintro K ⟨t, ht, v, rfl⟩
  obtain ⟨j, hj, h⟩ := good_run hm t ht
  exact width_good hm hj h r v

/-! ### Entries of the output word -/

theorem stepCode_entries {s : Step} (hs : s ∈ (script G ms).steps) :
    ∀ v ∈ stepCode s, v < n ∨ v ≤ 2 := by
  simp only [script, List.mem_flatMap, List.mem_range] at hs
  obtain ⟨j, -, hs⟩ := hs
  simp only [stageSteps, List.mem_append, List.mem_map] at hs
  rcases hs with ⟨p, -, rfl⟩ | ⟨v, -, rfl⟩
  · unfold resolveStep
    split_ifs <;> simp [stepCode]
  · simp [mergeStep, stepCode]

theorem length_steps_le (σ : Script n) : σ.steps.length + 2 ≤ wordLength σ := by
  have h : ∀ l : List Step, l.length ≤ ((l.map stepCode).flatten).length := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have : 1 ≤ (stepCode s).length := by
        cases s <;> simp [stepCode]
      omega
  have := h σ.steps
  have e : (toWord : Step → List ℕ) = stepCode := rfl
  simp only [wordLength, word_simps, e, List.length_append, List.length_cons]
  omega

/-- **Every entry of the output word is at most its length plus `n`.** -/
theorem entries_le (v : ℕ) (hv : v ∈ toWord (script G ms)) :
    v ≤ wordLength (script G ms) + n := by
  have hlen := length_steps_le (script G ms)
  change v ∈ toWord (List.ofFn (script G ms).colors) ++ toWord (script G ms).steps at hv
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · change v ∈ (List.ofFn (script G ms).colors).length ::
      ((List.ofFn (script G ms).colors).map toWord).flatten at hv
    simp only [List.mem_cons, List.length_ofFn, List.mem_flatten, List.mem_map,
      List.mem_ofFn] at hv
    rcases hv with rfl | ⟨l, ⟨c, ⟨x, rfl⟩, rfl⟩, hv⟩
    · omega
    · change v ∈ [((x : Fin n) : ℕ)] at hv
      simp only [List.mem_singleton] at hv
      omega
  · change v ∈ (script G ms).steps.length :: ((script G ms).steps.map toWord).flatten at hv
    simp only [List.mem_cons, List.mem_flatten, List.mem_map] at hv
    rcases hv with rfl | ⟨l, ⟨s, hs, rfl⟩, hv⟩
    · omega
    · rcases stepCode_entries hs v hv with h | h <;> omega

end

end Lax185574Proofs.Conversions.MergeConstruction
