/-
**The run of the two-pebble transducer of `RequestProject/PartD/ChildGraphAut.lean`.**

This file analyses the machine `Transducers.CG.cgAut` phase by phase and proves the two facts that
Claim `claim:from-child-configuration-graph-to-children` needs:

* `Transducers.CG.cgAut_halts`: the machine halts on **every** input, so that it computes a total
  function;
* `Transducers.CG.cgAut_computes_cgOut`: on a string that represents a child configuration graph it
  outputs the concatenation of the string representations of the children.
-/
import Lax194892Proofs.Source.PartD.ChildGraphAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CG

variable {A Q : Type} {k : ℕ} {u : List (CGLetter A Q k)}

/-! ## Composing runs -/

private lemma reaches_trans {c c' c'' : PebbleCfg (PSt Q)} {v v' : List (ConfLetter A Q k)}
    (h : cgAut.Reaches u c v c') (h' : cgAut.Reaches u c' v' c'') :
    cgAut.Reaches u c (v ++ v') c'' := by
  induction h with
  | refl _ => simpa using h'
  | step hs _ ih => exact (List.append_assoc _ _ _ ▸ Pebble.Reaches.step hs (ih h'))

private lemma reaches_one {c c' : PebbleCfg (PSt Q)} {v : List (ConfLetter A Q k)}
    (h : cgAut.stepCfg u c = some (v, c')) : cgAut.Reaches u c v c' := by
  simpa using Pebble.Reaches.step h (Pebble.Reaches.refl c')

/-! ## The individual steps -/

lemma step_start : cgAut.stepCfg u (PebbleCfg.conf PSt.start []) =
    some ([], PebbleCfg.conf (PSt.chk true) [0]) := by
  simp [Pebble.stepCfg, cgAut, cgStep]

lemma step_dead {st : List ℕ} :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.dead : PSt Q) st) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep]

lemma step_chk_move {ok : Bool} {p : ℕ} {c : CGLetter A Q k} (hc : u[p]? = some c) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.chk ok) [p]) =
      some ([], PebbleCfg.conf (PSt.chk (ok && pairOK (leftLet u p) (some c))) [p + 1]) := by
  have hp : p < u.length := (List.getElem?_eq_some_iff.1 hc).1
  simp only [Pebble.stepCfg, cgAut, cgStep, letsAt_one]
  rw [hc]
  simp [hp]

lemma step_chk_end_ok {ok : Bool} {p : ℕ} (hn : u[p]? = none)
    (h : (ok && pairOK (leftLet u p) none && ((leftLet u p).isSome)) = true) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.chk ok) [p]) =
      some ([], PebbleCfg.conf PSt.find [p - 1]) := by
  have hp : p ≠ 0 := by
    intro h0
    rw [h0] at h
    simp [leftLet] at h
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp
  simp [Pebble.stepCfg, cgAut, cgStep, hn, h, hp0]

lemma step_chk_end_bad {ok : Bool} {p : ℕ} (hn : u[p]? = none)
    (h : (ok && pairOK (leftLet u p) none && ((leftLet u p).isSome)) = false) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.chk ok) [p]) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hn, h]

lemma step_find_src {p : ℕ} {c : CGLetter A Q k} {q : Q} (hc : u[p]? = some c)
    (hq : pickSrc c.src = some q) :
    cgAut.stepCfg u (PebbleCfg.conf PSt.find [p]) =
      some ([], PebbleCfg.conf (PSt.prt q) [p, 0]) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hc, hq]

lemma step_find_move {p : ℕ} {c : CGLetter A Q k} (hc : u[p]? = some c)
    (hq : pickSrc c.src = (none : Option Q)) (hp : p ≠ 0) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.find : PSt Q) [p]) =
      some ([], PebbleCfg.conf PSt.find [p - 1]) := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp
  have hl : (leftLet u p).isSome = true := by
    have hlt : p < u.length := (List.getElem?_eq_some_iff.1 hc).1
    simp only [leftLet, if_neg hp]
    rw [Option.isSome_iff_exists]
    exact ⟨u[p - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  simp [Pebble.stepCfg, cgAut, cgStep, hc, hq, hl, hp0]

lemma step_find_stop_zero {c : CGLetter A Q k} (hc : u[0]? = some c)
    (hq : pickSrc c.src = (none : Option Q)) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.find : PSt Q) [0]) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hc, hq, leftLet]

lemma step_find_end {p : ℕ} (hn : u[p]? = none) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.find : PSt Q) [p]) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hn]

lemma step_prt_out {q : Q} {p j : ℕ} {c : CGLetter A Q k} (hc : u[j]? = some c) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.prt q) [p, j]) =
      some ([(q, c.lett, fun i => c.peb i || (decide (i = c.nid) && decide (p = j)))],
        PebbleCfg.conf (PSt.mv q) [p, j]) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hc]

lemma step_prt_pop {q : Q} {p j : ℕ} (hn : u[j]? = none) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.prt q) [p, j]) =
      some ([], PebbleCfg.conf (PSt.adv q) [p]) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hn]

lemma step_mv {q : Q} {p j : ℕ} (hj : j < u.length) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.mv q) [p, j]) =
      some ([], PebbleCfg.conf (PSt.prt q) [p, j + 1]) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hj]

lemma step_adv_end {q : Q} {p : ℕ} (hn : u[p]? = none) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.adv q) [p]) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hn]

lemma step_adv_stop {q : Q} {p : ℕ} {c : CGLetter A Q k} (hc : u[p]? = some c)
    (hq : c.nxt q = none) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.adv q) [p]) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hc, hq]

lemma step_adv_stay {q q' : Q} {p : ℕ} {c : CGLetter A Q k} (hc : u[p]? = some c)
    (hq : c.nxt q = some (q', none)) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.adv q) [p]) =
      some ([], PebbleCfg.conf (PSt.prt q') [p, 0]) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hc, hq]

lemma step_adv_right {q q' : Q} {p : ℕ} {c : CGLetter A Q k} (hc : u[p]? = some c)
    (hq : c.nxt q = some (q', some true)) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.adv q) [p]) =
      some ([], PebbleCfg.conf (PSt.ent q') [p + 1]) := by
  have hp : p < u.length := (List.getElem?_eq_some_iff.1 hc).1
  simp only [Pebble.stepCfg, cgAut, cgStep, letsAt_one]
  rw [hc]
  simp [hq, hp]

lemma step_adv_left {q q' : Q} {p : ℕ} {c : CGLetter A Q k} (hc : u[p]? = some c)
    (hq : c.nxt q = some (q', some false)) (hp : p ≠ 0) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.adv q) [p]) =
      some ([], PebbleCfg.conf (PSt.ent q') [p - 1]) := by
  have hlt : p < u.length := (List.getElem?_eq_some_iff.1 hc).1
  have hl : (leftLet u p).isSome = true := by
    simp only [leftLet, if_neg hp]
    rw [Option.isSome_iff_exists]
    exact ⟨u[p - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp
  simp [Pebble.stepCfg, cgAut, cgStep, hc, hq, hl, hp0]

lemma step_adv_left_zero {q q' : Q} {c : CGLetter A Q k} (hc : u[0]? = some c)
    (hq : c.nxt q = some (q', some false)) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.adv q) [0]) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hc, hq, leftLet]

lemma step_ent_end {q : Q} {p : ℕ} (hn : u[p]? = none) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.ent q) [p]) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hn]

lemma step_ent_push {q : Q} {p : ℕ} {c : CGLetter A Q k} (hc : u[p]? = some c) :
    cgAut.stepCfg u (PebbleCfg.conf (PSt.ent q) [p]) =
      some ([], PebbleCfg.conf (PSt.prt q) [p, 0]) := by
  simp [Pebble.stepCfg, cgAut, cgStep, hc]

/-! ## Computing the successor -/

lemma succOf_of_nxt_none {v : Vtx Q} {c : CGLetter A Q k} (hc : u[v.2]? = some c)
    (h : c.nxt v.1 = none) : succOf u v = none := by
  simp [succOf, hc, h]

lemma succOf_of_nxt {v : Vtx Q} {c : CGLetter A Q k} {q' : Q} {d : Dir} (hc : u[v.2]? = some c)
    (h : c.nxt v.1 = some (q', d)) : succOf u v = (dest v.2 d).map fun p' => (q', p') := by
  simp [succOf, hc, h]

lemma walkOut_of_out_of_range {v : Vtx Q} (h : u[v.2]? = none) (n : ℕ) :
    walkOut u (some v) n = [] := by
  cases n with
  | zero => simp
  | succ n =>
      rw [walkOut_succ]
      simp [emitOf, h, nxtOpt, succOf_of_out_of_range h]

/-! ## The sweep that checks local consistency -/

/-- The accumulated result of the local consistency test over the first `j` gaps. -/
noncomputable def chkAcc (u : List (CGLetter A Q k)) : ℕ → Bool
  | 0 => true
  | j + 1 => chkAcc u j && pairOK (leftLet u j) u[j]?

lemma chkAcc_iff (n : ℕ) : chkAcc u n = true ↔ ∀ i < n, pairOK (leftLet u i) u[i]? = true := by
  induction n with
  | zero => simp [chkAcc]
  | succ n ih =>
      simp only [chkAcc, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_or_ge i n with h | h
        · exact h1 i h
        · have : i = n := by omega
          rw [this]; exact h2
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

lemma chk_run : ∀ d j, j + d = u.length →
    cgAut.Reaches u (PebbleCfg.conf (PSt.chk (chkAcc u j)) [j]) []
      (PebbleCfg.conf (PSt.chk (chkAcc u u.length)) ([u.length] : List ℕ)) := by
  intro d
  induction d with
  | zero => intro j hj; rw [show j = u.length from by omega]; exact Pebble.Reaches.refl _
  | succ d ih =>
      intro j hj
      have hjlt : j < u.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, u[j]? = some c :=
        ⟨u[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
      have hstep := step_chk_move (u := u) (ok := chkAcc u j) hc
      have heq : chkAcc u (j + 1) = (chkAcc u j && pairOK (leftLet u j) (some c)) := by
        simp [chkAcc, hc]
      have := reaches_one hstep
      rw [← heq] at this
      simpa using reaches_trans this (ih (j + 1) (by omega))

/-! ## The sweep that prints one child -/

lemma prt_run (v : Vtx Q) : ∀ d j, j + d = u.length →
    cgAut.Reaches u (PebbleCfg.conf (PSt.prt v.1) [v.2, j]) ((confAt u v).drop j)
      (PebbleCfg.conf (PSt.adv v.1) [v.2]) := by
  intro d
  induction d with
  | zero =>
      intro j hj
      have hj' : j = u.length := by omega
      have hn : u[j]? = none := by rw [hj']; exact List.getElem?_eq_none (by omega)
      have hdrop : (confAt u v).drop j = [] := by
        rw [List.drop_eq_nil_iff]
        simp [hj']
      rw [hdrop]
      exact reaches_one (step_prt_pop hn)
  | succ d ih =>
      intro j hj
      have hjlt : j < u.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, u[j]? = some c := ⟨u[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
      have hu : u[j] = c := by rw [← Option.some_inj, ← hc]; simp
      have hget : (confAt u v)[j]'(by simpa using hjlt) =
          (v.1, c.lett, fun i => c.peb i || (decide (i = c.nid) && decide (v.2 = j))) := by
        simp only [confAt, List.getElem_mapIdx, hu]
      have hdrop : (confAt u v).drop j =
          (v.1, c.lett, fun i => c.peb i || (decide (i = c.nid) && decide (v.2 = j))) ::
            (confAt u v).drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hjlt), hget]
      rw [hdrop]
      have h1 := reaches_one (step_prt_out (u := u) (q := v.1) (p := v.2) hc)
      have h2 := reaches_one (step_mv (u := u) (q := v.1) (p := v.2) (j := j) hjlt)
      have h3 := ih (j + 1) (by omega)
      have := reaches_trans h1 (reaches_trans h2 h3)
      simpa using this

/-! ## The walk along the edges -/

lemma walk_run : ∀ n (v : Vtx Q), (u[v.2]?).isSome → (nxtOpt u)^[n] (some v) = none →
    cgAut.Reaches u (PebbleCfg.conf (PSt.prt v.1) [v.2, 0]) (walkOut u (some v) n)
      PebbleCfg.halt := by
  intro n
  induction n with
  | zero => intro v hv hn; simp at hn
  | succ n ih =>
      intro v hv hn
      rw [Function.iterate_succ_apply] at hn
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hv
      have hent : ∀ w : Vtx Q, (nxtOpt u)^[n] (some w) = none →
          cgAut.Reaches u (PebbleCfg.conf (PSt.ent w.1) [w.2]) (walkOut u (some w) n)
            PebbleCfg.halt := by
        intro w hw
        cases hcw : u[w.2]? with
        | none =>
            rw [walkOut_of_out_of_range hcw]
            exact reaches_one (step_ent_end (q := w.1) hcw)
        | some c' =>
            have hstep := reaches_one (step_ent_push (u := u) (q := w.1) (p := w.2) hcw)
            simpa using reaches_trans hstep (ih w (by rw [hcw]; simp) hw)
      rw [walkOut_succ]
      have hemit : emitOf u (some v) = confAt u v := by simp [emitOf, hv]
      rw [hemit]
      refine reaches_trans (by simpa using prt_run (u := u) v u.length 0 (by omega)) ?_
      cases hnx : c.nxt v.1 with
      | none =>
          have hs : nxtOpt u (some v) = none := by
            simp [nxtOpt, succOf_of_nxt_none hc hnx]
          rw [hs, walkOut_none]
          exact reaches_one (step_adv_stop hc hnx)
      | some x =>
          obtain ⟨q', d⟩ := x
          have hsucc := succOf_of_nxt hc hnx
          cases d with
          | none =>
              have hs : nxtOpt u (some v) = some (q', v.2) := by
                simp [nxtOpt, hsucc, dest]
              rw [hs]
              have hstep := reaches_one (step_adv_stay hc hnx)
              simpa using reaches_trans hstep (ih (q', v.2) hv (by rw [← hs]; exact hn))
          | some b =>
              cases b with
              | true =>
                  have hs : nxtOpt u (some v) = some (q', v.2 + 1) := by
                    simp [nxtOpt, hsucc, dest]
                  rw [hs]
                  have hstep := reaches_one (step_adv_right hc hnx)
                  simpa using reaches_trans hstep (hent (q', v.2 + 1) (by rw [← hs]; exact hn))
              | false =>
                  by_cases h0 : v.2 = 0
                  · have hs : nxtOpt u (some v) = none := by
                      simp [nxtOpt, hsucc, dest, h0]
                    rw [hs, walkOut_none]
                    have hc0 : u[(0 : ℕ)]? = some c := by rw [← h0]; exact hc
                    have hstep := reaches_one (step_adv_left_zero (u := u) (q := v.1) hc0 hnx)
                    rw [h0]
                    exact hstep
                  · have hs : nxtOpt u (some v) = some (q', v.2 - 1) := by
                      simp [nxtOpt, hsucc, dest, h0]
                    rw [hs]
                    have hstep := reaches_one (step_adv_left hc hnx h0)
                    simpa using reaches_trans hstep (hent (q', v.2 - 1) (by rw [← hs]; exact hn))

/-! ## Finding the first child -/

lemma find_src_run {v₀ : Vtx Q} (hsrc : ∀ v, IsSrc u v ↔ v = v₀) :
    ∀ d j, v₀.2 + d = j → j < u.length →
      cgAut.Reaches u (PebbleCfg.conf PSt.find [j]) []
        (PebbleCfg.conf (PSt.prt v₀.1) [v₀.2, 0]) := by
  obtain ⟨c₀, hc₀, hs₀⟩ := (hsrc v₀).2 rfl
  intro d
  induction d with
  | zero =>
      intro j hj _
      have hj' : j = v₀.2 := by omega
      subst hj'
      have hpick : pickSrc c₀.src = some v₀.1 := by
        refine pickSrc_of_unique hs₀ ?_
        intro q' hq'
        have : ((q', v₀.2) : Vtx Q) = v₀ := (hsrc (q', v₀.2)).1 ⟨c₀, hc₀, hq'⟩
        exact congrArg Prod.fst this
      exact reaches_one (step_find_src hc₀ hpick)
  | succ d ih =>
      intro j hj hjlt
      obtain ⟨c, hc⟩ : ∃ c, u[j]? = some c := ⟨u[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
      have hpick : pickSrc c.src = (none : Option Q) := by
        cases hp : pickSrc c.src with
        | none => rfl
        | some q =>
            exfalso
            have : ((q, j) : Vtx Q) = v₀ := (hsrc (q, j)).1 ⟨c, hc, pickSrc_eq_some hp⟩
            have : j = v₀.2 := congrArg Prod.snd this
            omega
      have hstep := reaches_one (step_find_move hc hpick (by omega))
      simpa using reaches_trans hstep (ih (j - 1) (by omega) (by omega))

section Halting

variable [Finite Q]

lemma find_halt (hchk : Chk u) : ∀ j, j < u.length →
    ∃ o, cgAut.Reaches u (PebbleCfg.conf (PSt.find : PSt Q) [j]) o PebbleCfg.halt := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hjlt
      obtain ⟨c, hc⟩ : ∃ c, u[j]? = some c := ⟨u[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
      cases hp : pickSrc c.src with
      | some q =>
          have hisrc : IsSrc u ((q, j) : Vtx Q) := ⟨c, hc, pickSrc_eq_some hp⟩
          obtain ⟨n, hn⟩ := exists_walk_stop hchk hisrc
          have hw := walk_run n ((q, j) : Vtx Q) (by rw [hc]; simp) hn
          exact ⟨_, reaches_trans (reaches_one (step_find_src hc hp)) hw⟩
      | none =>
          by_cases h0 : j = 0
          · subst h0
            exact ⟨_, reaches_one (step_find_stop_zero hc hp)⟩
          · obtain ⟨o, ho⟩ := ih (j - 1) (by omega) (by omega)
            exact ⟨_, reaches_trans (reaches_one (step_find_move hc hp h0)) ho⟩

/-- **The machine halts on every input.** -/
theorem cgAut_halts (u : List (CGLetter A Q k)) : ∃ o, cgAut.Computes u o := by
  have hstart : cgAut.Reaches u (PebbleCfg.conf (PSt.start : PSt Q) []) []
      (PebbleCfg.conf (PSt.chk (chkAcc u 0)) [0]) := by
    simpa [chkAcc] using reaches_one (step_start (u := u))
  have hchkrun := reaches_trans hstart (chk_run (u := u) u.length 0 (by omega))
  have hn : u[u.length]? = none := List.getElem?_eq_none (by omega)
  by_cases hb : (chkAcc u u.length && pairOK (leftLet u u.length) none &&
      ((leftLet u u.length).isSome)) = true
  · have hb2 : (chkAcc u u.length = true ∧ pairOK (leftLet u u.length) none = true) ∧
        (leftLet u u.length).isSome = true := by simpa using hb
    have hb2 := hb2.1
    have hchk : Chk u := by
      intro i hi
      rcases Nat.lt_or_ge i u.length with h | h
      · exact (chkAcc_iff (u := u) u.length).1 hb2.1 i h
      · have hiu : i = u.length := by omega
        subst hiu
        rw [hn]
        exact hb2.2
    have hlen : u.length ≠ 0 := by
      intro h0
      rw [h0] at hb
      simp [leftLet] at hb
    obtain ⟨o, ho⟩ := find_halt hchk (u.length - 1) (by omega)
    exact ⟨_, reaches_trans hchkrun
      (reaches_trans (reaches_one (step_chk_end_ok hn hb)) ho)⟩
  · rw [Bool.not_eq_true] at hb
    exact ⟨_, reaches_trans hchkrun (reaches_one (step_chk_end_bad hn hb))⟩

omit [Finite Q] in
/-- **On a string that represents a child configuration graph, the machine outputs exactly the
string representations of the children.** -/
theorem cgAut_computes_cgOut {m : ℕ} {p : ℕ → Vtx Q} (h : CGPath u m p) :
    cgAut.Computes u (cgOut u m p) := by
  have hchk := h.chk
  have hp0 := h.inRange 0 (Nat.zero_le _)
  obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.1 hp0
  have hlt0 : (p 0).2 < u.length := (List.getElem?_eq_some_iff.1 hc₀).1
  have hlen : u.length ≠ 0 := by omega
  have hn : u[u.length]? = none := List.getElem?_eq_none (by omega)
  have hacc : chkAcc u u.length = true :=
    (chkAcc_iff (u := u) u.length).2 fun i hi => hchk i (by omega)
  have hpair : pairOK (leftLet u u.length) none = true := by
    have := hchk u.length le_rfl
    rwa [hn] at this
  have hleft : ((leftLet u u.length).isSome) = true := by
    simp only [leftLet, if_neg hlen]
    rw [Option.isSome_iff_exists]
    exact ⟨u[u.length - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hb : (chkAcc u u.length && pairOK (leftLet u u.length) none &&
      ((leftLet u u.length).isSome)) = true := by rw [hacc, hpair, hleft]; rfl
  have hstart : cgAut.Reaches u (PebbleCfg.conf (PSt.start : PSt Q) []) []
      (PebbleCfg.conf (PSt.chk (chkAcc u 0)) [0]) := by
    simpa [chkAcc] using reaches_one (step_start (u := u))
  have hchkrun := reaches_trans hstart (chk_run (u := u) u.length 0 (by omega))
  have hfind := find_src_run (u := u) h.srcEq (u.length - 1 - (p 0).2) (u.length - 1)
    (by omega) (by omega)
  have hstop : (nxtOpt u)^[m + 1] (some (p 0)) = none := h.orbit_none (m + 1) (by omega)
  have hwalk := walk_run (m + 1) (p 0) hp0 hstop
  rw [h.walkOut_eq hstop] at hwalk
  have : cgAut.Reaches u (PebbleCfg.conf (PSt.start : PSt Q) []) (cgOut u m p)
      PebbleCfg.halt := by
    have := reaches_trans hchkrun (reaches_trans (reaches_one (step_chk_end_ok hn hb))
      (reaches_trans hfind hwalk))
    simpa using this
  simpa [Pebble.Computes, cgAut] using this

end Halting

end CG

end Lax194892Proofs.Transducers
