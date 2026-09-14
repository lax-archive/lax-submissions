/-
**The simulation phase of the checking automaton** of `RequestProject/PartD/PebReachAut.lean`, and
the correctness statement `PebReach.reachAut_answers_iff` that the four preliminary phases
(`RequestProject/PartD/PebReachRun.lean`) and the simulation phase add up to.

The simulation phase is where the automaton runs `M` step by step.  Two things have to be checked:

* the target test `PebReach.tOk` is correct, that is, the automaton can tell from the letters under
  its pebbles whether its stack is exactly the target stack (`PebReach.tOk_iff`).  This uses that
  the encoding stores, in the letter of each gap, the *set* of pebble indices of the target
  configuration that sit in that gap;
* one step of the automaton mirrors one step of `M` (`PebReach.next_sim_step`); the exceptional
  cases -- `M` halts, `M` dies, or a pop would take the stack below the floor `ℓ` -- are exactly the
  cases in which the automaton's run can no longer answer.
-/
import Lax194892Proofs.Source.PartD.PebReachRun
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers
namespace PebReach
open PebEnc

variable {A B Q : Type} {k : ℕ}
variable (M : Pebble A B Q k) (ℓ : ℕ) (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A)

lemma entryRight_enc (st : List ℕ) (hstb : ∀ p ∈ st, p ≤ w.length) (j : ℕ) (hj : j < st.length) :
    entryRight (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) j
      = some (q₁, q₂, w[st[j]]?, ann k sts st[j], ann k stt st[j]) := by
  rw [entryRight_viewOf, List.getElem?_eq_getElem hj]
  exact pairEnc_getElem? q₁ q₂ sts stt w (hstb _ (List.getElem_mem hj))

lemma tOk_enc (st : List ℕ) (hstb : ∀ p ∈ st, p ≤ w.length) (hstk : st.length ≤ k) :
    tOk (hmark k stt) (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) = true ↔
      ((∀ j, j < st.length → stt[j]? = st[j]?) ∧
        ∀ i, i < k → st.length ≤ i → stt.length ≤ i) := by
  rw [tOk, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  simp only [viewOf_length, List.mem_range, List.mem_finRange, forall_const]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, fun i hik hle => ?_⟩
    · have h := h1 j hj
      rw [entryRight_enc q₁ q₂ sts stt w st hstb j hj] at h
      simp only [bidx_ann stt st[j] j (lt_of_lt_of_le hj hstk), decide_eq_true_eq] at h
      exact h.trans (List.getElem?_eq_getElem hj).symm
    · have h := h2 ⟨i, hik⟩
      simp only [hmark] at h
      rw [if_neg (by omega)] at h
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, fun i => ?_⟩
    · rw [entryRight_enc q₁ q₂ sts stt w st hstb j hj]
      simp only [bidx_ann stt st[j] j (lt_of_lt_of_le hj hstk), decide_eq_true_eq]
      exact (h1 j hj).trans (List.getElem?_eq_getElem hj)
    · simp only [hmark]
      split_ifs with h
      · rfl
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        exact fun hc => absurd (h2 i i.isLt (by omega)) (by omega)

lemma tOk_iff (st : List ℕ) (hstb : ∀ p ∈ st, p ≤ w.length) (hstk : st.length ≤ k)
    (hsttk : stt.length ≤ k) :
    tOk (hmark k stt) (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) = true ↔ st = stt := by
  rw [tOk_enc q₁ q₂ sts stt w st hstb hstk]
  constructor
  · rintro ⟨h1, h2⟩
    have hle1 : st.length ≤ stt.length := by
      by_contra hc
      push_neg at hc
      have h := h1 stt.length hc
      rw [List.getElem?_eq_getElem hc] at h
      simp at h
    have hle2 : stt.length ≤ st.length := by
      by_contra hc
      push_neg at hc
      exact absurd (h2 st.length (by omega) le_rfl) (by omega)
    refine List.ext_getElem (by omega) ?_
    intro n hn hn'
    have h := h1 n hn
    rw [List.getElem?_eq_getElem hn', List.getElem?_eq_getElem hn] at h
    exact (Option.some_injective _ h).symm
  · rintro rfl
    exact ⟨fun j _ => rfl, fun i _ h => h⟩


open scoped Classical in
lemma next_sim_halt (S T : Fin k → Bool) (q : Q) (st : List ℕ)
    (h : (tOk T (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) && decide (q = q₂)) = true) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (simSt S T q, st))
      = Sum.inr (some true) := by
  simp [PebbleAut.next, reachAut, rstep, simSt, h]

open scoped Classical in
lemma next_sim_step (S T : Fin k → Bool) (q : Q) (st : List ℕ)
    (hstb : ∀ p ∈ st, p ≤ w.length) (hl : ℓ ≤ st.length)
    (hne : ¬ (tOk T (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) && decide (q = q₂)) = true) :
    (∃ (q' : Q) (st' : List ℕ) (o : List B),
        M.stepCfg w (PebbleCfg.conf q st) = some (o, PebbleCfg.conf q' st') ∧ ℓ ≤ st'.length ∧
        (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (simSt S T q, st))
          = Sum.inl (simSt S T q', st'))
      ∨ ((∀ o : Bool, ¬ (reachAut M ℓ q₁ q₂).Answers (pairEnc q₁ q₂ sts stt w)
            ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (simSt S T q, st))) o) ∧
          ∀ (q' : Q) (st' : List ℕ) (o : List B),
            M.stepCfg w (PebbleCfg.conf q st) = some (o, PebbleCfg.conf q' st') →
              st'.length < ℓ) := by
  have hunv : unview (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) = viewOf w st :=
    unview_viewOf q₁ q₂ sts stt w st hstb
  have hdead : ∀ (s : RSt Q k) (st'' : List ℕ),
      (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (simSt S T q, st))
          = Sum.inl (s, st'') → s.phase = Phase.dead →
      ∀ o : Bool, ¬ (reachAut M ℓ q₁ q₂).Answers (pairEnc q₁ q₂ sts stt w)
        ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (simSt S T q, st))) o := by
    intro s st'' he hs o
    rw [he]
    exact not_answers_dead M ℓ q₁ q₂ _ s hs st'' o
  have hnone : (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (simSt S T q, st))
        = Sum.inr none →
      ∀ o : Bool, ¬ (reachAut M ℓ q₁ q₂).Answers (pairEnc q₁ q₂ sts stt w)
        ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (simSt S T q, st))) o := by
    intro he o
    rw [he]
    exact PebbleAut.not_answers_of_dead (m := 0) rfl o
  cases hact : (M.step q (viewOf w st)).2 with
  | out b =>
      refine Or.inl ⟨(M.step q (viewOf w st)).1, st, [b], ?_, hl, ?_⟩
      · simp [Pebble.stepCfg, hact]
      · simp [PebbleAut.next, reachAut, rstep, simSt, hne, hunv, hact]
  | terminate =>
      refine Or.inr ⟨hdead (deadSt S T q) st
        (by simp [PebbleAut.next, reachAut, rstep, simSt, deadSt, hne, hunv, hact]) rfl, ?_⟩
      intro q' st' o hs
      simp [Pebble.stepCfg, hact] at hs
  | push =>
      by_cases hlt : st.length < k
      · refine Or.inl ⟨(M.step q (viewOf w st)).1, st ++ [0], [], ?_, by simp; omega, ?_⟩
        · simp [Pebble.stepCfg, hact, hlt]
        · simp [PebbleAut.next, reachAut, rstep, simSt, hne, hunv, hact, hlt,
            show st.length < k + 1 by omega]
      · refine Or.inr ⟨hdead (deadSt S T q) st
          (by simp [PebbleAut.next, reachAut, rstep, simSt, deadSt, hne, hunv, hact, hlt]) rfl, ?_⟩
        intro q' st' o hs
        simp [Pebble.stepCfg, hact, hlt] at hs
  | pop =>
      by_cases hd : st = [] ∨ st.length - 1 < ℓ
      · refine Or.inr ⟨hdead (deadSt S T q) st
          (by simp [PebbleAut.next, reachAut, rstep, simSt, deadSt, hne, hunv, hact, hd]) rfl, ?_⟩
        intro q' st' o hs
        by_cases hnil : st = []
        · simp [Pebble.stepCfg, hact, if_pos hnil] at hs
        · simp only [Pebble.stepCfg, hact, if_neg hnil, Option.some.injEq, Prod.mk.injEq,
            PebbleCfg.conf.injEq] at hs
          obtain ⟨-, -, rfl⟩ := hs
          have hpos : 0 < st.length := List.length_pos_iff.2 hnil
          rcases hd with h | h
          · exact absurd h hnil
          · rw [List.length_dropLast]; omega
      · push_neg at hd
        obtain ⟨hnil, hd2⟩ := hd
        refine Or.inl ⟨(M.step q (viewOf w st)).1, st.dropLast, [], ?_, ?_, ?_⟩
        · simp [Pebble.stepCfg, hact, hnil]
        · rw [List.length_dropLast]; omega
        · simp [PebbleAut.next, reachAut, rstep, simSt, hne, hunv, hact, hnil,
            show ¬ (st.length - 1 < ℓ) by omega]
  | move d =>
      cases hlast : st.getLast? with
      | none =>
          have hrl : rightLet (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st) = none := by
            rw [rightLet_viewOf_gen, hlast]; rfl
          cases d with
          | true =>
              refine Or.inr ⟨hdead (deadSt S T q) st
                (by simp [PebbleAut.next, reachAut, rstep, simSt, deadSt, hne, hunv, hact, hrl])
                  rfl, ?_⟩
              intro q' st' o hs
              simp [Pebble.stepCfg, hact, hlast] at hs
          | false =>
              refine Or.inr ⟨hnone
                (by simp [PebbleAut.next, reachAut, rstep, simSt, hne, hunv, hact, hlast]), ?_⟩
              intro q' st' o hs
              simp [Pebble.stepCfg, hact, hlast] at hs
      | some p =>
          have hp : p ≤ w.length := hstb p (List.mem_of_getLast? hlast)
          have hrl : rightLet (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st)
              = some (q₁, q₂, w[p]?, ann k sts p, ann k stt p) := by
            rw [rightLet_viewOf_gen, hlast]
            exact pairEnc_getElem? q₁ q₂ sts stt w hp
          cases d with
          | true =>
              by_cases hpl : p < w.length
              · have hw : w[p]? = some w[p] := List.getElem?_eq_getElem hpl
                refine Or.inl ⟨(M.step q (viewOf w st)).1, st.dropLast ++ [p + 1], [], ?_, ?_, ?_⟩
                · simp [Pebble.stepCfg, hact, hlast, hpl]
                · have : 0 < st.length := List.length_pos_iff.2
                    (by intro h; rw [h] at hlast; simp at hlast)
                  simp [List.length_dropLast]; omega
                · simp [PebbleAut.next, reachAut, rstep, simSt, hne, hunv, hact, hrl, hw, hlast]
                  omega
              · have hw : w[p]? = none := by
                  rw [List.getElem?_eq_none]; omega
                refine Or.inr ⟨hdead (deadSt S T q) st
                  (by simp [PebbleAut.next, reachAut, rstep, simSt, deadSt, hne, hunv, hact, hrl,
                    hw]) rfl, ?_⟩
                intro q' st' o hs
                simp [Pebble.stepCfg, hact, hlast, hpl] at hs
          | false =>
              by_cases hp0 : 0 < p
              · refine Or.inl ⟨(M.step q (viewOf w st)).1, st.dropLast ++ [p - 1], [], ?_, ?_, ?_⟩
                · simp [Pebble.stepCfg, hact, hlast, hp0]
                · have : 0 < st.length := List.length_pos_iff.2
                    (by intro h; rw [h] at hlast; simp at hlast)
                  simp [List.length_dropLast]; omega
                · simp [PebbleAut.next, reachAut, rstep, simSt, hne, hunv, hact, hlast, hp0]
              · refine Or.inr ⟨hnone
                  (by simp [PebbleAut.next, reachAut, rstep, simSt, hne, hunv, hact, hlast, hp0]),
                    ?_⟩
                intro q' st' o hs
                simp [Pebble.stepCfg, hact, hlast, hp0] at hs


/-! ### From a run of the transducer to an answer of the automaton, and back -/

lemma restrReaches_not_halt {ℓ' : ℕ} {c : PebbleCfg Q} :
    ¬ M.RestrReaches w ℓ' PebbleCfg.halt c := by
  intro h; cases h

lemma restrReaches_le {ℓ' : ℕ} {q : Q} {st : List ℕ} {c : PebbleCfg Q}
    (h : M.RestrReaches w ℓ' (PebbleCfg.conf q st) c) : ℓ' ≤ st.length := by
  cases h with
  | refl _ _ hle => exact hle
  | step hle _ _ => exact hle

open scoped Classical in
/-- A run of `M` that stays above the floor is answered by the automaton. -/
lemma answers_of_restr (S : Fin k → Bool) (hsttb : ∀ p ∈ stt, p ≤ w.length)
    (hsttk : stt.length ≤ k) {c c' : PebbleCfg Q} (h : M.RestrReaches w ℓ c c') :
    ∀ {q : Q} {st : List ℕ}, c = PebbleCfg.conf q st → c' = PebbleCfg.conf q₂ stt →
      (∀ p ∈ st, p ≤ w.length) → st.length ≤ k →
      (reachAut M ℓ q₁ q₂).Answers (pairEnc q₁ q₂ sts stt w)
        (Sum.inl (simSt S (hmark k stt) q, st)) true := by
  induction h with
  | refl q0 st0 hle =>
      intro q st h1 h2 hstb hstk
      simp only [PebbleCfg.conf.injEq] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1
      rw [h2.1, h2.2]
      refine ⟨1, ?_⟩
      rw [Function.iterate_one]
      exact next_sim_halt M ℓ q₁ q₂ sts stt w S (hmark k stt) q₂ stt
        (by rw [Bool.and_eq_true]
            exact ⟨(tOk_iff q₁ q₂ sts stt w stt hsttb hsttk hsttk).2 rfl, by simp⟩)
  | @step q0 st0 c' c'' o hle hs hr ih =>
      intro q st h1 h2 hstb hstk
      simp only [PebbleCfg.conf.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      by_cases hc : (tOk (hmark k stt) (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st0)
          && decide (q0 = q₂)) = true
      · exact ⟨1, by rw [Function.iterate_one]
                     exact next_sim_halt M ℓ q₁ q₂ sts stt w S (hmark k stt) q0 st0 hc⟩
      · cases hc' : c' with
        | halt => rw [hc'] at hr; exact absurd hr (restrReaches_not_halt M w)
        | conf q' st' =>
            rw [hc'] at hs hr
            have hl' : ℓ ≤ st'.length := restrReaches_le M w hr
            rcases next_sim_step M ℓ q₁ q₂ sts stt w S (hmark k stt) q0 st0 hstb hle hc with
              ⟨q'', st'', o'', hs'', -, he⟩ | ⟨-, hbad⟩
            · rw [hs] at hs''
              simp only [Option.some.injEq, Prod.mk.injEq, PebbleCfg.conf.injEq] at hs''
              obtain ⟨-, rfl, rfl⟩ := hs''
              obtain ⟨hstb', hstk'⟩ := stepCfg_inv M w hstb hstk hs
              refine PebbleAut.answers_of_next ?_
              rw [he]
              exact ih (by rw [hc']) h2 hstb' hstk'
            · exact absurd (hbad q' st' o hs) (by omega)

open scoped Classical in
/-- An answer of the automaton comes from a run of `M` that stays above the floor. -/
lemma restr_of_answers (S : Fin k → Bool) (hsttb : ∀ p ∈ stt, p ≤ w.length)
    (hsttk : stt.length ≤ k) :
    ∀ (n : ℕ) (q : Q) (st : List ℕ), (∀ p ∈ st, p ≤ w.length) → st.length ≤ k → ℓ ≤ st.length →
      ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[n]
          (Sum.inl (simSt S (hmark k stt) q, st)) = Sum.inr (some true) →
      M.RestrReaches w ℓ (PebbleCfg.conf q st) (PebbleCfg.conf q₂ stt) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q st hstb hstk hl hn
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [Function.iterate_succ_apply] at hn
      by_cases hc : (tOk (hmark k stt) (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) st)
          && decide (q = q₂)) = true
      · rw [Bool.and_eq_true, decide_eq_true_eq,
          tOk_iff q₁ q₂ sts stt w st hstb hstk hsttk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Pebble.RestrReaches.refl _ _ hl
      · rcases next_sim_step M ℓ q₁ q₂ sts stt w S (hmark k stt) q st hstb hl hc with
          ⟨q', st', o, hs, hl', he⟩ | ⟨hno, -⟩
        · rw [he] at hn
          obtain ⟨hstb', hstk'⟩ := stepCfg_inv M w hstb hstk hs
          exact Pebble.RestrReaches.step hl hs (ih n (by omega) q' st' hstb' hstk' hl' hn)
        · exact absurd ⟨n, hn⟩ (hno true)

/-- **The automaton is correct.**  On the string representation of the pair of configurations
`(q₁, sts)` and `(q₂, stt)`, the automaton answers `true` exactly when the first reaches the second
by a run that never pops below the floor `ℓ`. -/
theorem reachAut_answers_iff (hstsb : ∀ p ∈ sts, p ≤ w.length) (hsttb : ∀ p ∈ stt, p ≤ w.length)
    (hstsk : sts.length ≤ k) (hsttk : stt.length ≤ k) (hl : ℓ ≤ sts.length) :
    (reachAut M ℓ q₁ q₂).Answers (pairEnc q₁ q₂ sts stt w) (Sum.inl (startSt q₁, [])) true
      ↔ M.RestrReaches w ℓ (PebbleCfg.conf q₁ sts) (PebbleCfg.conf q₂ stt) := by
  obtain ⟨m, hm⟩ := pre_run M ℓ q₁ q₂ sts stt w hstsb hsttb hstsk
  rw [PebbleAut.answers_iterate_eq hm]
  constructor
  · rintro ⟨n, hn⟩
    exact restr_of_answers M ℓ q₁ q₂ sts stt w (hmark k sts) hsttb hsttk n q₁ sts hstsb hstsk hl hn
  · intro h
    exact answers_of_restr M ℓ q₁ q₂ sts stt w (hmark k sts) hsttb hsttk h rfl rfl hstsb hstsk

end PebReach
end Lax194892Proofs.Transducers
