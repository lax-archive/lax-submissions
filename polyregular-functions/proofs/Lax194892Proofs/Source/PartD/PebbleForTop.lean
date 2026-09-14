/-
Part D: a for-transducer is simulated by a pebble transducer.

This finishes the easy inclusion of Theorem `thm:pebble-are-for`.  The run of the nest of loops is
described in `RequestProject/PartD/PebbleForNest.lean`; what is left is the start of the run (the
pebble that stays at the position `0` is pushed), the epilogue, and the passage from a program in
prenex form to an arbitrary for-transducer through Lemma `lemma:prenex-normal-form`.
-/
import Lax194892Proofs.Source.PartD.PebbleForNest
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebFor

open PolyEnum

variable {A B : Type}

namespace Setup

variable (S : Setup A B)

/-! ## The loops of the nest, from the outermost one -/

lemma claim_all : ∀ (d j : ℕ), j + d + 1 = S.k → S.ClaimStmt j := by
  intro d
  induction d with
  | zero =>
      intro j hjk
      have hj : j < S.k := by omega
      exact S.claim_of_loop hj (loop_of_iter S (S.iter_innermost hj (by omega)))
  | succ d ih =>
      intro j hjk
      have hj : j < S.k := by omega
      have hj1 : j + 1 < S.k := by omega
      exact S.claim_of_loop hj (loop_of_iter S (S.iter_of_claim hj1 (ih (j + 1) (by omega))))

/-! ## The epilogue -/

/-- Emitting, one letter per step, the output of the epilogue that the machine still carries. -/
lemma epi_run (ps : List ℕ) : ∀ (l : List B) (hl : l.length ≤ S.N)
    (q : PSt A B S.k S.m S.N), q.ph = Ph.epi ⟨l, hl⟩ →
      S.M.Reaches S.w (S.cfgAt q ps) l PebbleCfg.halt := by
  intro l
  induction l with
  | nil =>
      intro hl q hph
      have hact : S.M.step q (viewOf S.w (0 :: ps))
          = (⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), none,
              Ph.epi ⟨[], hl⟩⟩, PebbleAction.terminate) := by
        rw [S.step_epi q ⟨[], hl⟩ hph]
      exact Pebble.reaches_one (S.stepCfg_terminate hact)
  | cons b rest ih =>
      intro hl q hph
      have hl' : rest.length ≤ S.N := by
        have := hl
        simp only [List.length_cons] at this
        omega
      have hact : S.M.step q (viewOf S.w (0 :: ps))
          = (⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), none,
              Ph.epi (BddList.tail ⟨b :: rest, hl⟩)⟩, PebbleAction.out b) := by
        rw [S.step_epi q ⟨b :: rest, hl⟩ hph]
      refine (show b :: rest = [b] ++ rest from rfl) ▸
        Pebble.reaches_trans (Pebble.reaches_one (S.stepCfg_out hact)) ?_
      exact ih hl' _ rfl

/-- Once the nest of loops is over, the machine runs the epilogue and emits its output. -/
lemma epi_finish (q : PSt A B S.k S.m S.N) (s : Fin S.m → Bool)
    (hgood : S.Good q.ord q.pend []) (hep : S.AtEpi q s []) :
    S.M.Reaches S.w (S.cfgAt q [])
      (ForProg.exec S.w S.epilogue (fun _ => 0) (extBV S.m s)).2 PebbleCfg.halt := by
  have hview : letAt (viewOf S.w (0 :: ([] : List ℕ))) S.k = S.w[0]? := by
    rw [letAt_viewOf, posOf_of_length_le (by simp)]
  have hex : ForProg.exec (letAt (viewOf S.w (0 :: ([] : List ℕ))) S.k).toList S.epilogue
      (fun _ => 0) (extBV S.m s)
      = ForProg.exec S.w S.epilogue (fun _ => 0) (extBV S.m s) := by
    rw [hview]
    refine (ForProg.exec_congr_view S.w _ S.epilogue S.hepi _ _ _ (fun i _ j _ => by simp)
      ?_).symm
    intro i _
    exact (PolyEnum.option_toList_getElem? (S.w[0]?)).symm
  have key : ∀ (E2 : List B), E2.length ≤ S.N →
      S.M.step q (viewOf S.w (0 :: ([] : List ℕ)))
        = (match E2 with
          | [] => (⟨s, S.ordTrue [], none, Ph.epiStart⟩, PebbleAction.terminate)
          | b :: rest => (⟨s, S.ordTrue [], none, Ph.epi (BddList.of rest)⟩,
              PebbleAction.out b)) →
        S.M.Reaches S.w (S.cfgAt q []) E2 PebbleCfg.halt := by
    intro E2 hlen hstep
    cases E2 with
    | nil => exact Pebble.reaches_one (S.stepCfg_terminate hstep)
    | cons b rest =>
        have hrl : rest.length ≤ S.N := by
          have := hlen
          simp only [List.length_cons] at this
          omega
        refine (show b :: rest = [b] ++ rest from rfl) ▸
          Pebble.reaches_trans (Pebble.reaches_one (S.stepCfg_out hstep)) ?_
        refine S.epi_run [] rest hrl _ ?_
        exact congrArg Ph.epi (Subtype.ext (BddList.of_val hrl))
  refine key _ (le_trans (length_exec_le S.hepi _ _ _) S.hN) ?_
  rw [S.step_def q [], hep, hgood]
  unfold epiAct
  rw [hex]
  rfl

/-! ## The whole run -/

lemma fin'_zero : S.fin' 0 = 0 := by
  refine Fin.ext ?_
  simp [fin']

lemma nestRun_top (bvr : ℕ → Bool) :
    S.nestRun [] 0 bvr
      = runList (fun bv t => ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) bv)
          (tuplesOf S.L S.w.length) bvr := by
  have hstep : S.nestStep [] =
      fun bv t => ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) bv := by
    funext bv t
    unfold nestStep
    simp
  unfold nestRun
  rw [hstep]
  simp
  rfl

/-- **The simulating machine computes the program.** -/
lemma computes_eval :
    S.M.Computes S.w
      (ForProg.eval (ForProg.seq (ForProg.nestLoops S.L S.body) S.epilogue) S.w) := by
  classical
  set bv0 : ℕ → Bool := fun _ => false with hbv0
  have hbv0inv : ∀ i, S.m ≤ i → bv0 i = false := fun _ _ => rfl
  set q1 : PSt A B S.k S.m S.N := ⟨fun _ => false, fun _ _ => true, none, Ph.enter 0⟩ with hq1
  have hstep0 : S.M.step S.M.init (viewOf S.w []) = (q1, PebbleAction.push) := rfl
  have hr0 : S.M.stepCfg S.w (PebbleCfg.conf S.M.init []) = some ([], S.cfgAt q1 []) := by
    simp only [Pebble.stepCfg, hstep0]
    rw [if_pos (by simp)]
    simp [cfgAt]
  have hg1 : S.Good q1.ord q1.pend [] := by
    show (fun _ _ => true) = S.ordTrue []
    funext i j
    simp [ordTrue, posOf]
  have hen1 : S.AtEnter q1 (resBV S.m bv0) 0 [] :=
    S.atEnter_of_ph q1 0 (by rw [hq1, S.fin'_zero]) []
  have hnest : ∃ q2 : PSt A B S.k S.m S.N, S.Good q2.ord q2.pend [] ∧
      S.AtEpi q2 (resBV S.m (S.nestRun [] 0 bv0).1) [] ∧
      S.M.Reaches S.w (S.cfgAt q1 []) (S.nestRun [] 0 bv0).2 (S.cfgAt q2 []) := by
    by_cases hk0 : S.k = 0
    · have ht : ([] : List ℕ).length = S.k := by simp [hk0]
      have hen1' : S.AtEnter q1 (resBV S.m bv0) S.k [] := by rw [hk0]; exact hen1
      obtain ⟨q2, hg2, hnx, hre⟩ := S.body_run ht (by simp) bv0 hbv0inv q1 hg1 hen1'
      have hnr : S.nestRun [] 0 bv0
          = ForProg.exec S.w S.body (setTuple S.L [] (fun _ => 0)) bv0 := by
        have h := S.nestRun_last [] bv0
        rwa [hk0] at h
      refine ⟨q2, hg2, ?_, by rw [hnr]; exact hre⟩
      rw [hnr]
      unfold AtNext at hnx
      rwa [if_pos hk0] at hnx
    · have hcl : S.ClaimStmt 0 := S.claim_all (S.k - 1) 0 (by omega)
      obtain ⟨q2, hg2, hnx, hre⟩ := hcl [] rfl (by simp) bv0 hbv0inv q1 hg1 hen1
      refine ⟨q2, hg2, ?_, hre⟩
      unfold AtNext at hnx
      rwa [if_pos rfl] at hnx
  obtain ⟨q2, hg2, hep2, hre2⟩ := hnest
  set BV := (S.nestRun [] 0 bv0).1 with hBV
  have hBVinv : ∀ i, S.m ≤ i → BV i = false := S.bv_inv_nest [] 0 bv0 hbv0inv
  have hre3 := S.epi_finish q2 (resBV S.m BV) hg2 hep2
  rw [extBV_resBV S.m BV hBVinv] at hre3
  have hfin : S.M.Reaches S.w (PebbleCfg.conf S.M.init [])
      ([] ++ ((S.nestRun [] 0 bv0).2 ++ (ForProg.exec S.w S.epilogue (fun _ => 0) BV).2))
      PebbleCfg.halt :=
    Pebble.reaches_trans (Pebble.reaches_one hr0) (Pebble.reaches_trans hre2 hre3)
  have hval : ForProg.eval (ForProg.seq (ForProg.nestLoops S.L S.body) S.epilogue) S.w
      = (S.nestRun [] 0 bv0).2 ++ (ForProg.exec S.w S.epilogue (fun _ => 0) BV).2 := by
    rw [hBV, S.nestRun_top bv0]
    unfold ForProg.eval
    rw [exec_seq, exec_nestLoops]
  show S.M.Reaches S.w (PebbleCfg.conf S.M.init []) _ PebbleCfg.halt
  rw [hval]
  simpa using hfin

end Setup

/-! ## For-transducers are pebble transducers -/

/-- **A for-transducer in prenex form is simulated by a pebble transducer.** -/
theorem isPebbleTransducer_of_prenex [Finite B] {P : ForProg A B} (hP : P.PrenexForm) :
    IsPebbleTransducer P.eval := by
  classical
  obtain ⟨L, body, epilogue, hbody, hepi, hone, rfl⟩ := hP
  set k := L.length with hk
  set m := maxList body.boolVars + 1 with hm
  set N := outBound epilogue with hN
  have hmlt : ∀ i ∈ body.boolVars, i < m := by
    intro i hi
    have := le_maxList body.boolVars i hi
    omega
  set vf : ℕ → Fin (k + 1) := fun i => ⟨virt L i, Nat.lt_succ_of_le (virt_le L i)⟩ with hvf
  refine ⟨k + 1, PSt A B k m N, inferInstance, peb k m N L body epilogue vf, fun w => ?_⟩
  exact (Setup.mk k m N w L hk.symm body epilogue vf hbody hepi hone hmlt
    (fun _ => rfl) (le_refl _)).computes_eval

/-- **Every function computed by a for-transducer is computed by a pebble transducer.** -/
theorem isPebbleTransducer_of_isForTransducer [Finite B] {f : List A → List B}
    (hf : IsForTransducer f) : IsPebbleTransducer f := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨P', hpre, hval⟩ := forTransducer_prenex_aux P
  obtain ⟨k, Q, hQ, M, hM⟩ := isPebbleTransducer_of_prenex hpre
  exact ⟨k, Q, hQ, M, fun w => by rw [← hP w, ← hval w]; exact hM w⟩

end PebFor

end Lax194892Proofs.Transducers
