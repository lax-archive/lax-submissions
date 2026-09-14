/-
Part D: the nest of loops of a for-transducer in prenex form, as run by the simulating pebble
transducer.

The machine and the elementary facts about its steps are in
`RequestProject/PartD/PebbleForDef.lean` and `RequestProject/PartD/PebbleForRun.lean`.  This file
puts one iteration of a loop together (`PebFor.Setup.IterStmt`), then all the iterations of a loop
(`PebFor.Setup.LoopStmt`), then a whole sub-nest (`PebFor.Setup.ClaimStmt`).
-/
import Lax194892Proofs.Source.PartD.PebbleForRun
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebFor

open PolyEnum

variable {A B : Type}

namespace Setup

variable (S : Setup A B)

/-! ## The Boolean variables stay inside the first `m` of them -/

lemma bv_inv_step (pre : List ℕ) (bvr : ℕ → Bool) (hbvr : ∀ i, S.m ≤ i → bvr i = false)
    (t : List ℕ) : ∀ i, S.m ≤ i → (S.nestStep pre bvr t).1 i = false := by
  intro i hi
  unfold nestStep
  rw [ForProg.exec_bv_unchanged _ _ _ _ (fun hmem => absurd (S.hm i hmem) (by omega))]
  exact hbvr i hi

lemma bv_inv_runList (pre : List ℕ) :
    ∀ (ts : List (List ℕ)) (bvr : ℕ → Bool), (∀ i, S.m ≤ i → bvr i = false) →
      ∀ i, S.m ≤ i → (runList (S.nestStep pre) ts bvr).1 i = false := by
  intro ts
  induction ts with
  | nil => intro bvr hbvr i hi; exact hbvr i hi
  | cons t ts ih =>
      intro bvr hbvr i hi
      rw [runList_cons]
      exact ih _ (S.bv_inv_step pre bvr hbvr t) i hi

lemma bv_inv_nest (pre : List ℕ) (j : ℕ) (bvr : ℕ → Bool)
    (hbvr : ∀ i, S.m ≤ i → bvr i = false) : ∀ i, S.m ≤ i → (S.nestRun pre j bvr).1 i = false :=
  S.bv_inv_runList pre _ bvr hbvr

/-! ## Elementary facts about the positions of a loop -/

lemma nextPos_lt {d : Bool} {n p p' : ℕ} (h : nextPos d n p = some p') (hp : p < n) : p' < n := by
  cases d
  · simp only [nextPos, if_neg (by simp : ¬ (false = true))] at h
    by_cases hp0 : p = 0
    · rw [if_pos hp0] at h; exact absurd h (by simp)
    · rw [if_neg hp0] at h
      have : p' = p - 1 := (Option.some_inj.mp h).symm
      omega
  · simp only [nextPos] at h
    by_cases h1 : p + 1 < n
    · rw [if_pos h1] at h
      have : p' = p + 1 := (Option.some_inj.mp h).symm
      omega
    · rw [if_neg h1] at h; exact absurd h (by simp)

lemma remPos_length_lt {d : Bool} {n p p' : ℕ} (hp : p < n) (h : nextPos d n p = some p') :
    (remPos d n p').length = (remPos d n p).length - 1 := by
  rw [remPos_cons d hp, h]
  simp

/-! ## The nest of loops, level by level -/

/-- The innermost level of the nest: one execution of the body. -/
lemma nestRun_last (t : List ℕ) (bvr : ℕ → Bool) :
    S.nestRun t S.k bvr = ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) bvr := by
  have hdrop : S.L.drop S.k = [] := by rw [← S.hk]; simp
  unfold nestRun
  rw [hdrop, tuplesOf_nil, runList_cons, runList_nil]
  unfold nestStep
  simp

/-- Peeling off the outermost loop of a sub-nest. -/
lemma nestRun_cons {j : ℕ} (hj : j < S.k) (pre : List ℕ) (bvr : ℕ → Bool) :
    S.nestRun pre j bvr
      = runList (fun bv x => S.nestRun (pre ++ [x]) (j + 1) bv)
          (loopRange (dirOf S.L j) S.n) bvr := by
  have hjl : j < S.L.length := by rw [S.hk]; exact hj
  have hdrop : S.L.drop j = S.L[j] :: S.L.drop (j + 1) := List.drop_eq_getElem_cons hjl
  rcases hd : S.L[j] with ⟨d, x⟩
  rw [hd] at hdrop
  have hdir : dirOf S.L j = d := by
    unfold dirOf
    rw [List.getD_eq_getElem _ _ hjl, hd]
  unfold nestRun
  rw [hdrop, hdir, tuplesOf_cons, runList_flatMap]
  refine congrArg (fun f => runList f (loopRange d S.n) bvr) ?_
  funext bv p
  rw [runList_map]
  refine congrArg (fun f => runList f (tuplesOf (S.L.drop (j + 1)) S.n) bv) ?_
  funext bv' t
  unfold nestStep
  rw [show pre ++ p :: t = (pre ++ [p]) ++ t from by simp]

/-! ## One iteration of a loop -/

/-- Once the sub-nest below the loop `j` has been run for the position `p`, the loop moves on. -/
lemma iter_finish {j : ℕ} (hj : j < S.k) {pre : List ℕ} (hpre : pre.length = j) {p : ℕ}
    (hp : p < S.n) (q q' : PSt A B S.k S.m S.N) (s : Fin S.m → Bool) (out : List B)
    (hgood' : S.Good q'.ord q'.pend (pre ++ [p])) (hadv : S.AtAdv q' s j (pre ++ [p]))
    (hre : S.M.Reaches S.w (S.cfgAt q (pre ++ [p])) out (S.cfgAt q' (pre ++ [p]))) :
    ∃ q'' : PSt A B S.k S.m S.N,
      (match nextPos (dirOf S.L j) S.n p with
        | some p' =>
            S.Good q''.ord q''.pend (pre ++ [p']) ∧ S.AtEnter q'' s (j + 1) (pre ++ [p']) ∧
              S.M.Reaches S.w (S.cfgAt q (pre ++ [p])) out (S.cfgAt q'' (pre ++ [p']))
        | none =>
            S.Good q''.ord q''.pend pre ∧ S.AtNext q'' s j pre ∧
              S.M.Reaches S.w (S.cfgAt q (pre ++ [p])) out (S.cfgAt q'' pre)) := by
  obtain ⟨q'', hq''⟩ := S.adv_run hj hpre hp q' s hadv hgood'
  refine ⟨q'', ?_⟩
  cases hnp : nextPos (dirOf S.L j) S.n p with
  | none =>
      rw [hnp] at hq''
      obtain ⟨h1, h2, h3⟩ := hq''
      exact ⟨h1, h2, by simpa using Pebble.reaches_trans hre h3⟩
  | some p' =>
      rw [hnp] at hq''
      obtain ⟨h1, h2, h3⟩ := hq''
      exact ⟨h1, h2, by simpa using Pebble.reaches_trans hre h3⟩

lemma mem_snoc_lt {pre : List ℕ} {p : ℕ} (hprelt : ∀ x ∈ pre, x < S.n) (hp : p < S.n) :
    ∀ x ∈ pre ++ [p], x < S.n := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hprelt x h
  · rw [List.mem_singleton.mp h]; exact hp

/-- One iteration of the innermost loop of the nest. -/
lemma iter_innermost {j : ℕ} (hj : j < S.k) (hjk : j + 1 = S.k) : S.IterStmt j := by
  intro pre hpre hprelt p hp bvr hbvr q hgood hen
  have ht : (pre ++ [p]).length = S.k := by simp [hpre, hjk]
  have hlt : ∀ x ∈ pre ++ [p], x < S.n := S.mem_snoc_lt hprelt hp
  have hnr : S.nestRun (pre ++ [p]) (j + 1) bvr
      = ForProg.exec S.w S.body (setTuple S.L (pre ++ [p]) (fun _ => 0)) bvr := by
    rw [hjk]; exact S.nestRun_last _ _
  rw [hnr]
  rw [hjk] at hen
  obtain ⟨q', hg', hnx, hre⟩ := S.body_run ht hlt bvr hbvr q hgood hen
  have hadv : S.AtAdv q'
      (resBV S.m (ForProg.exec S.w S.body (setTuple S.L (pre ++ [p]) (fun _ => 0)) bvr).1) j
      (pre ++ [p]) := by
    unfold AtNext at hnx
    rw [if_neg (by omega : ¬ S.k = 0)] at hnx
    rwa [show S.k - 1 = j from by omega] at hnx
  exact S.iter_finish hj hpre hp q q' _ _ hg' hadv hre

/-- One iteration of a loop that is not the innermost one. -/
lemma iter_of_claim {j : ℕ} (hj1 : j + 1 < S.k) (hcl : S.ClaimStmt (j + 1)) : S.IterStmt j := by
  intro pre hpre hprelt p hp bvr hbvr q hgood hen
  have hlt : ∀ x ∈ pre ++ [p], x < S.n := S.mem_snoc_lt hprelt hp
  have hlen : (pre ++ [p]).length = j + 1 := by simp [hpre]
  obtain ⟨q', hg', hnx, hre⟩ := hcl (pre ++ [p]) hlen hlt bvr hbvr q hgood hen
  have hadv : S.AtAdv q' (resBV S.m (S.nestRun (pre ++ [p]) (j + 1) bvr).1) j (pre ++ [p]) := by
    unfold AtNext at hnx
    rw [if_neg (by omega : ¬ (j + 1 = 0))] at hnx
    simpa using hnx
  exact S.iter_finish (by omega) hpre hp q q' _ _ hg' hadv hre

/-! ## All the iterations of a loop -/

lemma loop_aux {j : ℕ} (hit : S.IterStmt j) :
    ∀ (N : ℕ) (pre : List ℕ), pre.length = j → (∀ x ∈ pre, x < S.n) →
    ∀ (p : ℕ), p < S.n → (remPos (dirOf S.L j) S.n p).length ≤ N →
    ∀ (bvr : ℕ → Bool), (∀ i, S.m ≤ i → bvr i = false) →
    ∀ (q : PSt A B S.k S.m S.N), S.Good q.ord q.pend (pre ++ [p]) →
      S.AtEnter q (resBV S.m bvr) (j + 1) (pre ++ [p]) →
      ∃ q' : PSt A B S.k S.m S.N,
        S.Good q'.ord q'.pend pre ∧
        S.AtNext q' (resBV S.m
            (runList (fun bv x => S.nestRun (pre ++ [x]) (j + 1) bv)
              (remPos (dirOf S.L j) S.n p) bvr).1) j pre ∧
        S.M.Reaches S.w (S.cfgAt q (pre ++ [p]))
          (runList (fun bv x => S.nestRun (pre ++ [x]) (j + 1) bv)
            (remPos (dirOf S.L j) S.n p) bvr).2 (S.cfgAt q' pre) := by
  intro N
  induction N with
  | zero =>
      intro pre _ _ p hp hN bvr _ q _ _
      rw [remPos_cons _ hp] at hN
      simp at hN
  | succ N ih =>
      intro pre hpre hprelt p hp hN bvr hbvr q hgood hen
      obtain ⟨q1, hq1⟩ := hit pre hpre hprelt p hp bvr hbvr q hgood hen
      rw [remPos_cons (dirOf S.L j) hp, runList_cons]
      cases hnp : nextPos (dirOf S.L j) S.n p with
      | none =>
          rw [hnp] at hq1
          obtain ⟨h1, h2, h3⟩ := hq1
          refine ⟨q1, h1, ?_, ?_⟩
          · simpa using h2
          · simpa using h3
      | some p' =>
          rw [hnp] at hq1
          obtain ⟨h1, h2, h3⟩ := hq1
          have hp' : p' < S.n := nextPos_lt hnp hp
          have hN' : (remPos (dirOf S.L j) S.n p').length ≤ N := by
            rw [remPos_cons (dirOf S.L j) hp, hnp] at hN
            simp only [Option.elim, List.length_cons] at hN
            omega
          have hbvr' : ∀ i, S.m ≤ i → (S.nestRun (pre ++ [p]) (j + 1) bvr).1 i = false :=
            S.bv_inv_nest _ _ bvr hbvr
          obtain ⟨q2, hg2, hn2, hr2⟩ := ih pre hpre hprelt p' hp' hN' _ hbvr' q1 h1 h2
          exact ⟨q2, hg2, hn2, Pebble.reaches_trans h3 hr2⟩

lemma loop_of_iter {j : ℕ} (hit : S.IterStmt j) : S.LoopStmt j := by
  intro pre hpre hprelt p hp bvr hbvr q hgood hen
  exact S.loop_aux hit _ pre hpre hprelt p hp (le_refl _) bvr hbvr q hgood hen

/-! ## Walking a backward loop to the last position -/

/-- The last step of the walk: at the right end of the input the pebble turns back. -/
lemma seek_last {j : ℕ} (hj : j < S.k) {pre : List ℕ} (hpre : pre.length = j) (hn : 0 < S.n)
    (q : PSt A B S.k S.m S.N) (hph : q.ph = Ph.seek (S.fin' j))
    (hgood : S.Good q.ord q.pend (pre ++ [S.n])) :
    ∃ q' : PSt A B S.k S.m S.N,
      S.Good q'.ord q'.pend (pre ++ [S.n - 1]) ∧ S.AtEnter q' q.bv (j + 1) (pre ++ [S.n - 1]) ∧
      S.M.Reaches S.w (S.cfgAt q (pre ++ [S.n])) [] (S.cfgAt q' (pre ++ [S.n - 1])) := by
  have hjv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = j := S.fin'_val (le_of_lt hj)
  have hxv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = pre.length := by rw [hjv, hpre]
  have hlet : letAt (viewOf S.w (0 :: (pre ++ [S.n]))) ((S.fin' j : Fin (S.k + 1)) : ℕ)
      = S.w[S.n]? := S.letAt_snoc hxv
  have ha : S.w[S.n]? = none := List.getElem?_eq_none (le_refl S.w.length)
  refine ⟨⟨q.bv, S.ordTrue (pre ++ [S.n]), some (S.fin' j, false),
      Ph.enter (fsucc S.k (S.fin' j))⟩, S.good_left hxv hn, ?_, ?_⟩
  · exact S.atEnter_of_ph _ (j + 1) (by simp only [fsucc_fin']) (pre ++ [S.n - 1])
  · refine Pebble.reaches_one (S.stepCfg_left ?_ hn)
    rw [S.step_seek q (S.fin' j) hph, hlet, ha, hgood]

/-- The pebble of a backward loop is pushed at the position `0` and then walked to the right end
of the input, from which it starts its iterations. -/
lemma seek_run {j : ℕ} (hj : j < S.k) {pre : List ℕ} (hpre : pre.length = j)
    (s : Fin S.m → Bool) :
    ∀ (r p : ℕ), p ≤ S.n → S.n - p ≤ r → 0 < p →
    ∀ (q : PSt A B S.k S.m S.N), q.bv = s → q.ph = Ph.seek (S.fin' j) →
      S.Good q.ord q.pend (pre ++ [p]) →
      ∃ q' : PSt A B S.k S.m S.N,
        S.Good q'.ord q'.pend (pre ++ [S.n - 1]) ∧ S.AtEnter q' s (j + 1) (pre ++ [S.n - 1]) ∧
        S.M.Reaches S.w (S.cfgAt q (pre ++ [p])) [] (S.cfgAt q' (pre ++ [S.n - 1])) := by
  have hjv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = j := S.fin'_val (le_of_lt hj)
  have hxv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = pre.length := by rw [hjv, hpre]
  intro r
  induction r with
  | zero =>
      intro p hple hr hp0 q hbv hph hgood
      have hpn : p = S.n := by omega
      subst hpn
      obtain ⟨q', h1, h2, h3⟩ := S.seek_last hj hpre hp0 q hph hgood
      exact ⟨q', h1, hbv ▸ h2, h3⟩
  | succ r ih =>
      intro p hple hr hp0 q hbv hph hgood
      by_cases hpn : p = S.n
      · subst hpn
        obtain ⟨q', h1, h2, h3⟩ := S.seek_last hj hpre hp0 q hph hgood
        exact ⟨q', h1, hbv ▸ h2, h3⟩
      · have hlt : p < S.w.length := by
          have h : p < S.n := by omega
          exact h
        have hlet : letAt (viewOf S.w (0 :: (pre ++ [p]))) ((S.fin' j : Fin (S.k + 1)) : ℕ)
            = S.w[p]? := S.letAt_snoc hxv
        obtain ⟨a, ha⟩ : ∃ a, S.w[p]? = some a := ⟨_, List.getElem?_eq_getElem hlt⟩
        set q1 : PSt A B S.k S.m S.N :=
          ⟨q.bv, S.ordTrue (pre ++ [p]), some (S.fin' j, true), Ph.seek (S.fin' j)⟩ with hq1
        have hact : S.M.step q (viewOf S.w (0 :: (pre ++ [p])))
            = (q1, PebbleAction.move true) := by
          rw [S.step_seek q (S.fin' j) hph, hlet, ha, hgood]
        have hr1 : S.M.stepCfg S.w (S.cfgAt q (pre ++ [p]))
            = some ([], S.cfgAt q1 (pre ++ [p + 1])) := S.stepCfg_right hact hlt
        obtain ⟨q2, hg2, he2, hre2⟩ := ih (p + 1) (by omega) (by omega) (by omega) q1
          (by rw [hq1]; exact hbv) rfl (S.good_right hxv)
        exact ⟨q2, hg2, he2, by
          simpa using Pebble.reaches_trans (Pebble.reaches_one hr1) hre2⟩
/-! ## A whole sub-nest -/

lemma tuplesOf_drop_zero {j : ℕ} (hj : j < S.k) : tuplesOf (S.L.drop j) 0 = [] := by
  have hjl : j < S.L.length := by rw [S.hk]; exact hj
  rcases hd : S.L[j] with ⟨d, x⟩
  have hdrop : S.L.drop j = (d, x) :: S.L.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hjl, hd]
  rw [hdrop, tuplesOf_cons]
  cases d <;> simp

lemma claim_of_loop {j : ℕ} (hj : j < S.k) (hlp : S.LoopStmt j) : S.ClaimStmt j := by
  intro pre hpre hprelt bvr hbvr q hgood hen
  have hprek : pre.length < S.k := by omega
  have hjv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = j := S.fin'_val (le_of_lt hj)
  have hxv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = pre.length := by rw [hjv, hpre]
  set q1 : PSt A B S.k S.m S.N :=
    ⟨resBV S.m bvr, S.ordTrue pre, none, Ph.init (S.fin' j)⟩ with hq1
  have hact : S.M.step q (viewOf S.w (0 :: pre)) = (q1, PebbleAction.push) := by
    rw [S.step_def q pre, hen, hgood]
    unfold enterAct
    rw [if_neg (by rw [hjv]; omega)]
  have hr1 : S.M.stepCfg S.w (S.cfgAt q pre) = some ([], S.cfgAt q1 (pre ++ [0])) :=
    S.stepCfg_push hact hprek
  have hg1 : S.Good q1.ord q1.pend (pre ++ [0]) := S.good_push pre
  have hlet : letAt (viewOf S.w (0 :: (pre ++ [0]))) ((S.fin' j : Fin (S.k + 1)) : ℕ)
      = S.w[0]? := S.letAt_snoc hxv
  by_cases hn : S.n = 0
  · -- the input is empty: the loop has no iteration at all
    have hw : S.w = [] := List.eq_nil_of_length_eq_zero hn
    have ha : S.w[0]? = none := by rw [hw]; rfl
    set q2 : PSt A B S.k S.m S.N :=
      ⟨q1.bv, popFix S.k (S.ordTrue (pre ++ [0])) (S.fin' j) (viewOf S.w (0 :: (pre ++ [0]))),
        none, if ((S.fin' j : Fin (S.k + 1)) : ℕ) = 0 then Ph.epiStart
          else Ph.adv (fpred S.k (S.fin' j))⟩ with hq2
    have hact2 : S.M.step q1 (viewOf S.w (0 :: (pre ++ [0]))) = (q2, PebbleAction.pop) := by
      rw [S.step_init q1 (S.fin' j) rfl, hlet, ha, hg1]
      rfl
    have hr2 : S.M.stepCfg S.w (S.cfgAt q1 (pre ++ [0])) = some ([], S.cfgAt q2 pre) :=
      S.stepCfg_pop hact2
    have hz : S.nestRun pre j bvr = (bvr, []) := by
      unfold nestRun
      rw [hn, S.tuplesOf_drop_zero hj]
      rfl
    rw [hz]
    refine ⟨q2, S.good_pop hxv hprek, S.atNext_of_pop (le_of_lt hj) q2 pre rfl, ?_⟩
    exact (show ([] : List B) = [] ++ [] from rfl) ▸
      Pebble.reaches_trans (Pebble.reaches_one hr1) (Pebble.reaches_one hr2)
  · have hnpos : 0 < S.n := Nat.pos_of_ne_zero hn
    obtain ⟨a, ha⟩ : ∃ a, S.w[0]? = some a :=
      ⟨_, List.getElem?_eq_getElem (show 0 < S.w.length from hnpos)⟩
    cases hd : dirOf S.L j with
    | true =>
        have hen1 : S.AtEnter q1 (resBV S.m bvr) (j + 1) (pre ++ [0]) := by
          show stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q1 (viewOf S.w (0 :: (pre ++ [0])))
            = enterAct S.k S.m S.N S.L S.body S.epilogue S.vf (S.fin' (j + 1)) (resBV S.m bvr)
                (fixOrd S.k q1.ord q1.pend (viewOf S.w (0 :: (pre ++ [0]))))
                (viewOf S.w (0 :: (pre ++ [0])))
          rw [hg1, ← S.step_def q1 (pre ++ [0]), S.step_init q1 (S.fin' j) rfl, hlet, ha, hg1,
            hjv, hd, if_pos rfl, fsucc_fin']
        have hRR : runList (fun bv x => S.nestRun (pre ++ [x]) (j + 1) bv)
            (remPos (dirOf S.L j) S.n 0) bvr = S.nestRun pre j bvr := by
          rw [S.nestRun_cons hj pre bvr, hd, remPos_eq_loopRange_true]
        obtain ⟨q', hg', hn', hre'⟩ :=
          hlp pre hpre hprelt 0 hnpos bvr hbvr q1 hg1 hen1
        rw [hRR] at hn' hre'
        refine ⟨q', hg', hn', ?_⟩
        exact (show (S.nestRun pre j bvr).2 = [] ++ (S.nestRun pre j bvr).2 from rfl) ▸
          Pebble.reaches_trans (Pebble.reaches_one hr1) hre'
    | false =>
        set q2 : PSt A B S.k S.m S.N :=
          ⟨q1.bv, S.ordTrue (pre ++ [0]), some (S.fin' j, true), Ph.seek (S.fin' j)⟩ with hq2
        have hact2 : S.M.step q1 (viewOf S.w (0 :: (pre ++ [0])))
            = (q2, PebbleAction.move true) := by
          rw [S.step_init q1 (S.fin' j) rfl, hlet, ha, hg1, hjv, hd]
          rfl
        have hr2 : S.M.stepCfg S.w (S.cfgAt q1 (pre ++ [0]))
            = some ([], S.cfgAt q2 (pre ++ [0 + 1])) :=
          S.stepCfg_right hact2 (show 0 < S.w.length from hnpos)
        obtain ⟨q3, hg3, hen3, hre3⟩ :=
          S.seek_run hj hpre (resBV S.m bvr) S.n 1 (by omega) (by omega) (by omega) q2
            (by rw [hq2, hq1]) rfl (by rw [hq2]; exact S.good_right hxv)
        have hRR : runList (fun bv x => S.nestRun (pre ++ [x]) (j + 1) bv)
            (remPos (dirOf S.L j) S.n (S.n - 1)) bvr = S.nestRun pre j bvr := by
          rw [S.nestRun_cons hj pre bvr, hd, remPos_eq_loopRange_false hnpos]
        obtain ⟨q', hg', hn', hre'⟩ :=
          hlp pre hpre hprelt (S.n - 1) (by omega) bvr hbvr q3 hg3 hen3
        rw [hRR] at hn' hre'
        refine ⟨q', hg', hn', ?_⟩
        have hchain : S.M.Reaches S.w (S.cfgAt q pre) ([] ++ ([] ++ ([] ++
            (S.nestRun pre j bvr).2))) (S.cfgAt q' pre) :=
          Pebble.reaches_trans (Pebble.reaches_one hr1)
            (Pebble.reaches_trans (Pebble.reaches_one hr2)
              (Pebble.reaches_trans hre3 hre'))
        simpa using hchain


end Setup

end PebFor

end Lax194892Proofs.Transducers
