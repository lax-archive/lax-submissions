import Lax185574Proofs.MainRam.Defs

/-!
The mathematics of the validation program: decoding the word of a
script, simulating a script on a color vector and a status matrix, and
the characterization of `ValidScript` by the checks the program makes.
Every step of a script is a step in the sense of construction
sequences: a merge of a color with itself changes nothing, which is
also a resolve between two colors no vertex has.
-/

namespace Lax185574Proofs.MainRam

open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.ConstructionSequences
open Lax185574.PartialGraphs

/-! ### Decoding -/

/-- The step with opcode `op` and colors `P`, `Q`. -/
def mkStep (op P Q : ℕ) : Step :=
  if op = 0 then .merge P Q else if op = 1 then .resolvePos P Q else .resolveNeg P Q

/-- The number of steps declared by the word `y` of a script on `n`
vertices. -/
def numSteps (n : ℕ) (y : List ℕ) : ℕ := y.getD (n + 1) 0

/-- The step `t` of the word `y`. -/
def stepAt (n : ℕ) (y : List ℕ) (t : ℕ) : Step :=
  mkStep (y.getD (n + 2 + 3 * t) 0) (y.getD (n + 3 + 3 * t) 0) (y.getD (n + 4 + 3 * t) 0)

/-- The script read off a word. -/
def decodeScript (n : ℕ) (y : List ℕ) : Script n where
  colors v := y.getD (v + 1) 0
  steps := (List.range (numSteps n y)).map (stepAt n y)

/-- The word has the shape of the word of a script on `n` vertices. -/
def ParseOK (n : ℕ) (y : List ℕ) : Prop :=
  y.getD 0 0 = n ∧ y.length = n + 2 + 3 * numSteps n y ∧
    ∀ t < numSteps n y, y.getD (n + 2 + 3 * t) 0 ≤ 2

theorem stepCode_mkStep {op P Q : ℕ} (h : op ≤ 2) : toWord (mkStep op P Q) = [op, P, Q] := by
  unfold mkStep
  split_ifs with h0 h1
  · subst h0; rfl
  · subst h1; rfl
  · have : op = 2 := by omega
    subst this; rfl

theorem toWord_script (n : ℕ) (σ : Script n) :
    toWord σ = n :: (List.ofFn σ.colors ++ (σ.steps.length :: (σ.steps.map toWord).flatten)) := by
  change toWord (List.ofFn σ.colors) ++ toWord σ.steps = _
  rw [Lax185574Proofs.Compose.toWord_list_nat, List.length_ofFn]
  rfl

theorem drop_three (l : List ℕ) (i : ℕ) (h : i + 3 ≤ l.length) :
    l.drop i = l.getD i 0 :: l.getD (i + 1) 0 :: l.getD (i + 2) 0 :: l.drop (i + 3) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega),
    List.getElem?_eq_getElem (show i + 1 < l.length by omega),
    List.getElem?_eq_getElem (show i + 2 < l.length by omega), Option.getD_some]

/-- The words of steps `t, t+1, …` of a well-shaped word. -/
theorem flatten_steps_eq {n : ℕ} {y : List ℕ} (h : ParseOK n y) :
    ∀ k ≤ numSteps n y,
      (((List.range' (numSteps n y - k) k).map (stepAt n y)).map toWord).flatten =
        y.drop (n + 2 + 3 * (numSteps n y - k)) := by
  obtain ⟨-, hlen, hop⟩ := h
  intro k
  induction k with
  | zero =>
      intro _
      simp only [List.range'_zero, List.map_nil, List.flatten_nil]
      symm; rw [List.drop_eq_nil_iff]; omega
  | succ k ih =>
      intro hk
      set m := numSteps n y
      have e : List.range' (m - (k + 1)) (k + 1) = (m - (k + 1)) :: List.range' (m - k) k := by
        rw [List.range'_succ]; congr 2; omega
      rw [e, List.map_cons, List.map_cons, List.flatten_cons, ih (by omega)]
      set t := m - (k + 1) with ht
      rw [stepAt, stepCode_mkStep (hop t (by omega))]
      have hd : y.drop (n + 2 + 3 * t) = y.getD (n + 2 + 3 * t) 0 :: y.getD (n + 3 + 3 * t) 0 ::
          y.getD (n + 4 + 3 * t) 0 :: y.drop (n + 2 + 3 * (m - k)) := by
        rw [drop_three y (n + 2 + 3 * t) (by omega), show n + 2 + 3 * t + 1 = n + 3 + 3 * t by omega,
          show n + 2 + 3 * t + 2 = n + 4 + 3 * t by omega,
          show n + 2 + 3 * t + 3 = n + 2 + 3 * (m - k) by omega]
      rw [hd]; rfl

/-- A well-shaped word is the word of its decoded script. -/
theorem toWord_decodeScript {n : ℕ} {y : List ℕ} (h : ParseOK n y) :
    toWord (decodeScript n y) = y := by
  have hf' : (((List.range (numSteps n y)).map (stepAt n y)).map toWord).flatten =
      y.drop (n + 2) := by
    have := flatten_steps_eq h (numSteps n y) le_rfl
    simpa [List.range_eq_range'] using this
  obtain ⟨h0, hlen, -⟩ := h
  rw [toWord_script]
  simp only [decodeScript]
  rw [hf', List.length_map, List.length_range]
  apply List.ext_getElem?
  intro i
  rcases i with _ | j
  · simp only [List.getElem?_cons_zero]
    rw [← h0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  · rw [List.getElem?_cons_succ]
    rcases Nat.lt_or_ge j n with hj | hj
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
      simp only [dif_pos hj, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (show j + 1 < y.length by omega)]; rfl
    · rw [List.getElem?_append_right (by simp; omega), List.length_ofFn]
      rcases Nat.eq_or_lt_of_le hj with rfl | hj'
      · simp only [Nat.sub_self, List.getElem?_cons_zero, numSteps, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (show n + 1 < y.length by omega)]; rfl
      · rw [show j - n = (j - n - 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop]
        congr 1; omega

/-- The word of a script is well shaped. -/
theorem parseOK_toWord {n : ℕ} (σ : Script n) : ParseOK n (toWord σ) ∧
    decodeScript n (toWord σ) = σ := by
  have hP : ParseOK n (toWord σ) := by
    rw [toWord_script]
    have hlen : (σ.steps.map toWord).flatten.length = 3 * σ.steps.length := by
      rw [List.length_flatten, List.map_map]
      have : ∀ st ∈ σ.steps, (List.length ∘ toWord) st = 3 := fun st _ =>
        Lax185574Proofs.Compose.stepCode_length st
      rw [List.map_congr_left this, List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]
    have hm : numSteps n (n :: (List.ofFn σ.colors ++ (σ.steps.length ::
        (σ.steps.map toWord).flatten))) = σ.steps.length := by
      simp only [numSteps, List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    refine ⟨rfl, ?_, ?_⟩
    · rw [hm]; simp [hlen]; omega
    · rw [hm]
      intro t ht
      simp only [List.getD_cons_succ, show n + 2 + 3 * t = (n + 1 + 3 * t) + 1 by omega]
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn, show n + 1 + 3 * t - n = (3 * t) + 1 by omega,
        List.getD_cons_succ]
      -- the opcode of step `t`
      have key : ∀ (l : List Step) (t : ℕ), t < l.length →
          ((l.map toWord).flatten).getD (3 * t) 0 ≤ 2 := by
        intro l
        induction l with
        | nil => intro t ht; simp at ht
        | cons s l ih =>
            intro t ht
            simp only [List.map_cons, List.flatten_cons]
            rcases t with _ | t
            · rw [List.getD_append _ _ _ _ (by rw [Lax185574Proofs.Compose.stepCode_length]; omega)]
              cases s <;> simp [word_simps, stepCode]
            · rw [List.getD_append_right _ _ _ _
                (by rw [Lax185574Proofs.Compose.stepCode_length]; omega)]
              rw [Lax185574Proofs.Compose.stepCode_length,
                show 3 * (t + 1) - 3 = 3 * t by omega]
              exact ih t (by simpa using ht)
      exact key σ.steps t ht
  refine ⟨hP, Lax185574Proofs.Compose.script_toWord_injective (toWord_decodeScript hP)⟩

/-- The words of scripts are exactly the well-shaped words. -/
theorem exists_script_iff {n : ℕ} {y : List ℕ} :
    (∃ σ : Script n, y = toWord σ) ↔ ParseOK n y :=
  ⟨fun ⟨σ, h⟩ => h ▸ (parseOK_toWord σ).1, fun h => ⟨_, (toWord_decodeScript h).symm⟩⟩

/-! ### Every step is a step -/

/-- A color that no vertex has. -/
theorem exists_unused {n : ℕ} (G : PartialGraph (Fin n)) : ∃ c, ∀ v, G.color v ≠ c := by
  refine ⟨(Finset.univ.image G.color).sup id + 1, fun v h => ?_⟩
  have : G.color v ≤ (Finset.univ.image G.color).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  omega

theorem resolvePos_unused {n : ℕ} (G : PartialGraph (Fin n)) {c : ℕ} (hc : ∀ v, G.color v ≠ c) :
    resolvePos G c c = G := by
  have hb : between G c c = ⊥ := by
    ext u v; simp [between, SimpleGraph.fromRel_adj, hc]
  cases G
  simp only [resolvePos, hb, bot_sdiff, sup_bot_eq]

theorem isStep_apply {n : ℕ} (G : PartialGraph (Fin n)) (s : Step) : IsStep G (apply G s) := by
  cases s with
  | merge P Q =>
      by_cases h : P = Q
      · subst h
        obtain ⟨c, hc⟩ := exists_unused G
        have hm : merge G P P = G := by
          cases G; simp only [merge]; congr; funext v; split_ifs with h <;> simp [h]
        refine ⟨c, c, Or.inr (Or.inl ?_)⟩
        show merge G P P = resolvePos G c c
        rw [hm, resolvePos_unused G hc]
      · exact ⟨P, Q, Or.inl ⟨h, rfl⟩⟩
  | resolvePos P Q => exact ⟨P, Q, Or.inr (Or.inl rfl)⟩
  | resolveNeg P Q => exact ⟨P, Q, Or.inr (Or.inr rfl)⟩

/-! ### Simulation on arrays -/

/-- The state of the simulation: the color of each vertex and the
status of each pair, `0` unresolved, `1` edge, `2` non-edge. -/
structure SimSt where
  col : ℕ → ℕ
  st : ℕ → ℕ → ℕ

/-- The pair `(u, v)` lies in `P^G Q^G` in either order. -/
def Btw (s : SimSt) (P Q u v : ℕ) : Prop :=
  u ≠ v ∧ ((s.col u = P ∧ s.col v = Q) ∨ (s.col u = Q ∧ s.col v = P))

open Classical in
/-- One step on arrays. -/
noncomputable def simStep (s : SimSt) (op P Q : ℕ) : SimSt :=
  if op = 0 then ⟨fun v => if s.col v = Q then P else s.col v, s.st⟩
  else ⟨s.col, fun u v => if s.st u v = 0 ∧ Btw s P Q u v then op else s.st u v⟩

/-- The arrays represent the partial graph. -/
def Rep {n : ℕ} (s : SimSt) (G : PartialGraph (Fin n)) : Prop :=
  (∀ v : Fin n, G.color v = s.col v) ∧ (∀ u v, s.st u v ≤ 2) ∧
    ∀ u v : Fin n, (G.edge.Adj u v ↔ s.st u v = 1) ∧ (G.nonEdge.Adj u v ↔ s.st u v = 2)

theorem btw_iff {n : ℕ} {s : SimSt} {G : PartialGraph (Fin n)} (hc : ∀ v : Fin n, G.color v = s.col v)
    (P Q : ℕ) (u v : Fin n) : (between G P Q).Adj u v ↔ Btw s P Q u v := by
  simp only [between, SimpleGraph.fromRel_adj, Btw, hc, ne_eq, Fin.val_inj]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr ⟨h2.2, h2.1⟩⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr ⟨h2.2, h2.1⟩⟩

theorem rep_step {n : ℕ} {s : SimSt} {G : PartialGraph (Fin n)} (h : Rep s G) {op P Q : ℕ}
    (hop : op ≤ 2) : Rep (simStep s op P Q) (apply G (mkStep op P Q)) := by
  obtain ⟨hc, hle, he⟩ := h
  have hb := btw_iff hc P Q
  have hle' : ∀ u v, (simStep s op P Q).st u v ≤ 2 := by
    intro u v
    unfold simStep
    split_ifs with h0 <;> dsimp only <;> (try split_ifs) <;> first | exact hle u v | omega
  unfold mkStep
  by_cases h0 : op = 0
  · subst h0
    unfold simStep
    simp only [if_true]
    refine ⟨fun v => ?_, hle, fun u v => ?_⟩
    · simp [apply, merge, hc]
    · simpa [apply, merge] using he u v
  rw [if_neg h0]
  unfold simStep at hle' ⊢
  rw [if_neg h0] at hle' ⊢
  by_cases h1 : op = 1
  · subst h1
    simp only [if_true]
    refine ⟨fun v => by simp [apply, resolvePos, hc], hle', fun u v => ?_⟩
    obtain ⟨E, N⟩ := he u v
    have := hle u v
    simp only [apply, resolvePos, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
    by_cases hh : s.st u v = 0 ∧ Btw s P Q u v
    · rw [if_pos hh]
      have hn : ¬ G.nonEdge.Adj u v := fun h => by have := N.1 h; omega
      exact ⟨⟨fun _ => rfl, fun _ => Or.inr ⟨(hb u v).2 hh.2, hn⟩⟩,
        ⟨fun h => absurd h hn, fun h => by omega⟩⟩
    · rw [if_neg hh]
      refine ⟨⟨?_, fun h => Or.inl (E.2 h)⟩, N⟩
      rintro (h | ⟨h, h'⟩)
      · exact E.1 h
      · have hB := (hb u v).1 h
        rcases Nat.lt_or_ge (s.st u v) 1 with h3 | h3
        · exact absurd ⟨by omega, hB⟩ hh
        · rcases Nat.lt_or_ge (s.st u v) 2 with h4 | h4
          · omega
          · exact absurd (N.2 (by omega)) h'
  · have h2 : op = 2 := by omega
    subst h2
    simp only [show ¬ (2 : ℕ) = 1 from by omega, if_false]
    refine ⟨fun v => by simp [apply, resolveNeg, hc], hle', fun u v => ?_⟩
    obtain ⟨E, N⟩ := he u v
    have := hle u v
    simp only [apply, resolveNeg, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
    by_cases hh : s.st u v = 0 ∧ Btw s P Q u v
    · rw [if_pos hh]
      have hn : ¬ G.edge.Adj u v := fun h => by have := E.1 h; omega
      exact ⟨⟨fun h => absurd h hn, fun h => by omega⟩,
        ⟨fun _ => rfl, fun _ => Or.inr ⟨(hb u v).2 hh.2, hn⟩⟩⟩
    · rw [if_neg hh]
      refine ⟨E, ?_, fun h => Or.inl (N.2 h)⟩
      rintro (h | ⟨h, h'⟩)
      · exact N.1 h
      · have hB := (hb u v).1 h
        rcases Nat.lt_or_ge (s.st u v) 1 with h3 | h3
        · exact absurd ⟨by omega, hB⟩ hh
        · rcases Nat.lt_or_ge (s.st u v) 2 with h4 | h4
          · exact absurd (E.2 (by omega)) h'
          · omega

/-! ### The checks -/

def opAt (n : ℕ) (y : List ℕ) (t : ℕ) : ℕ := y.getD (n + 2 + 3 * t) 0
def pAt (n : ℕ) (y : List ℕ) (t : ℕ) : ℕ := y.getD (n + 3 + 3 * t) 0
def qAt (n : ℕ) (y : List ℕ) (t : ℕ) : ℕ := y.getD (n + 4 + 3 * t) 0

/-- The arrays before the first step. -/
def simInit (y : List ℕ) : SimSt := ⟨fun v => y.getD (v + 1) 0, fun _ _ => 0⟩

/-- The arrays after `k` steps. -/
noncomputable def simFold (n : ℕ) (y : List ℕ) (k : ℕ) : SimSt :=
  (List.range k).foldl (fun s t => simStep s (opAt n y t) (pAt n y t) (qAt n y t)) (simInit y)

theorem simFold_succ (n : ℕ) (y : List ℕ) (k : ℕ) :
    simFold n y (k + 1) = simStep (simFold n y k) (opAt n y k) (pAt n y k) (qAt n y k) := by
  simp [simFold, List.range_succ, List.foldl_append]

theorem rep_simInit {n : ℕ} (y : List ℕ) :
    Rep (simInit y) (unresolved (decodeScript n y).colors) := by
  refine ⟨fun v => rfl, fun _ _ => by simp [simInit], fun u v => ?_⟩
  simp [unresolved, simInit]

theorem rep_simFold {n : ℕ} {y : List ℕ} (h : ParseOK n y) :
    ∀ k ≤ numSteps n y, Rep (simFold n y k)
      (((decodeScript n y).steps.take k).foldl apply (unresolved (decodeScript n y).colors)) := by
  intro k
  induction k with
  | zero => intro _; simpa [simFold] using rep_simInit y
  | succ k ih =>
      intro hk
      have hks : k < (decodeScript n y).steps.length := by simp [decodeScript]; omega
      rw [List.take_succ, List.getElem?_eq_getElem hks, Option.toList_some, List.foldl_append,
        List.foldl_cons, List.foldl_nil, simFold_succ]
      have hst : (decodeScript n y).steps[k] = mkStep (opAt n y k) (pAt n y k) (qAt n y k) := by
        simp [decodeScript, stepAt, opAt, pAt, qAt]
      rw [hst]
      exact rep_step (ih (by omega)) (h.2.2 k (by omega))

theorem simFold_diag (n : ℕ) (y : List ℕ) (k u : ℕ) : (simFold n y k).st u u = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [simFold_succ]
      unfold simStep
      split_ifs with h0
      · exact ih
      · dsimp only
        rw [if_neg (fun h => h.2.1 rfl)]; exact ih

/-- **The checks of the validation.** -/
theorem validScript_iff {n : ℕ} (G : SimpleGraph (Fin n)) (y : List ℕ) :
    ValidScript n G y ↔ ParseOK n y ∧
      (∀ u v : Fin n, u ≠ v → y.getD (u + 1) 0 ≠ y.getD (v + 1) 0) ∧
      (∀ v : Fin n, (simFold n y (numSteps n y)).col v = (simFold n y (numSteps n y)).col 0) ∧
      (∀ u v : Fin n, u ≠ v →
        ((simFold n y (numSteps n y)).st u v = 1 ∧ G.Adj u v) ∨
        ((simFold n y (numSteps n y)).st u v = 2 ∧ ¬ G.Adj u v)) := by
  constructor
  · rintro ⟨σ, rfl, hcs⟩
    obtain ⟨hP, hdec⟩ := parseOK_toWord σ
    refine ⟨hP, ?_⟩
    have hR := rep_simFold hP (numSteps n (toWord σ)) le_rfl
    have hlen : (decodeScript n (toWord σ)).steps.length = numSteps n (toWord σ) := by
      simp [decodeScript]
    rw [List.take_of_length_le (by omega), hdec] at hR
    obtain ⟨hne, hinit, -, hcol, hedge, hnon⟩ := hcs
    have hlast : σ.run.getLast hne = σ.steps.foldl apply (unresolved σ.colors) := by
      simp only [Script.run]; exact List.getLast_scanl _
    rw [hlast] at hcol hedge hnon
    obtain ⟨hc, -, he⟩ := hR
    refine ⟨?_, ?_, ?_⟩
    · intro u v huv heq
      have hh : (σ.run.head hne) = unresolved σ.colors := by simp [Script.run]
      have := hinit.2.2
      rw [hh] at this
      apply huv
      apply this
      have h1 : σ.colors u = (decodeScript n (toWord σ)).colors u := by rw [hdec]
      have h2 : σ.colors v = (decodeScript n (toWord σ)).colors v := by rw [hdec]
      simp only [unresolved, h1, h2, decodeScript]; exact heq
    · intro v
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact absurd v.isLt (by omega)
      · have := hcol v ⟨0, h0⟩
        rw [hc v, hc ⟨0, h0⟩] at this; exact this
    · intro u v huv
      have E := (he u v).1
      have N := (he u v).2
      by_cases hadj : G.Adj u v
      · left; refine ⟨E.1 ?_, hadj⟩; rw [hedge]; exact hadj
      · right; refine ⟨N.1 ?_, hadj⟩; rw [hnon]; exact ⟨huv, hadj⟩
  · rintro ⟨hP, hinj, hcol, hfin⟩
    refine ⟨decodeScript n y, (toWord_decodeScript hP).symm, ?_⟩
    set σ := decodeScript n y
    have hR := rep_simFold hP (numSteps n y) le_rfl
    rw [List.take_of_length_le (by simp [decodeScript])] at hR
    obtain ⟨hc, hle, he⟩ := hR
    have hne : σ.run ≠ [] := by simp [Script.run]
    have hlast : σ.run.getLast hne = σ.steps.foldl apply (unresolved σ.colors) := by
      simp only [Script.run]; exact List.getLast_scanl _
    refine ⟨hne, ⟨by simp [Script.run, unresolved], by simp [Script.run, unresolved], ?_⟩,
      ?_, ?_, ?_, ?_⟩
    · intro u v huv
      simp only [Script.run, List.head_scanl, unresolved] at huv
      by_contra hne'
      exact hinj u v hne' huv
    · intro t ht
      simp only [Script.run]
      rw [List.getElem_succ_scanl]
      exact isStep_apply _ _
    · intro u v
      rw [hlast, hc u, hc v, hcol u, hcol v]
    · ext u v
      rw [hlast, (he u v).1]
      by_cases huv : u = v
      · subst huv; simp; have := simFold_diag n y (numSteps n y) u; omega
      · rcases hfin u v huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, h2]
        · simp [h1, h2]
    · ext u v
      rw [hlast, (he u v).2, SimpleGraph.compl_adj]
      by_cases huv : u = v
      · subst huv; simp; have := simFold_diag n y (numSteps n y) u; omega
      · rcases hfin u v huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, h2, huv]
        · simp [h1, h2, huv]

end Lax185574Proofs.MainRam
