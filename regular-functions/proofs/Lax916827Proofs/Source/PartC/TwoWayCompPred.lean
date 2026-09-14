/-
Walking backwards along the run of a two-way transducer.

This is the step of the proof of Theorem `thm:composition-of-two-way-transducers` of *Transducers*
(M. Bojańczyk) that makes it possible for the composed transducer to move the head of the second
transducer to the left: from the annotation of the two letters adjacent to a cut one can read off
which configurations of the first transducer lie on the run at the two neighbouring cuts, and a
configuration on the run has a unique predecessor on the run (`TwoWay.pred_unique`). -/
import Lax916827Proofs.Source.PartC.TwoWayCompAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open scoped Classical

variable {A B Q S : Type}

/-- The predecessor of the current configuration of `M` on the run, if it lies
to the right of the head: the state of `M` and the direction in which the head
has to move. -/
noncomputable def predRight (D : DFA (Marked A Q) S) (M : TwoWay A B Q)
    (r : Option (AnnLet A S)) (q : Q) : Option (Q × Bool) :=
  match r with
  | none => none
  | some e =>
      if h : ∃ q₁ : Q, onRunRight D e q₁ = true ∧
          ∃ o, M.step (some e.letter) q₁ e.next = Sum.inr (q, o, false) then
        some (h.choose, true)
      else none

/-- The predecessor of the current configuration of `M` on the run: the state of
`M` and the direction in which the head has to move. -/
noncomputable def predOf (D : DFA (Marked A Q) S) (M : TwoWay A B Q)
    (l r : Option (AnnLet A S)) (q : Q) : Option (Q × Bool) :=
  match l with
  | none => predRight D M r q
  | some d =>
      if h : ∃ q₁ : Q, onRunLeft D d q₁ = true ∧
          ∃ o, M.step d.prev q₁ (some d.letter) = Sum.inr (q, o, true) then
        some (h.choose, false)
      else predRight D M r q

variable (D : DFA (Marked A Q) S) (M : TwoWay A B Q)

/-- The annotation letter at a position, with its three input letters spelled
out. -/
lemma annot_getElem_eq (w : List A) {i : ℕ} (hi : i < w.length) :
    ∃ e : AnnLet A S, (annot D w)[i]? = some e ∧ e.prev = (w.take i).getLast? ∧
      e.letter = w[i] ∧ e.next = w[i + 1]? := by
  refine ⟨_, annot_getElem D w hi, ?_, rfl, rfl⟩
  rw [take_getLast?' w (le_of_lt hi)]
  rfl

/-! ### Soundness -/

lemma predRight_sound (hD : D.accepts = {z | (visitAut M).Accepts z}) (w : List A) {i : ℕ}
    {q q₁ : Q} {dir : Bool}
    (h : predRight D M ((annot D w)[i]?) q = some (q₁, dir)) :
    dir = true ∧ i < w.length ∧
      ∃ o : List B, Visits M w (Cfg.conf (w.take (i + 1)) q₁ (w.drop (i + 1))) ∧
        M.stepCfg (Cfg.conf (w.take (i + 1)) q₁ (w.drop (i + 1)))
          = some (o, Cfg.conf (w.take i) q (w.drop i)) := by
  by_cases hi : i < w.length
  · obtain ⟨e, he, hprev, hlet, hnext⟩ := annot_getElem_eq D w hi
    rw [he, predRight] at h
    by_cases hc : ∃ q' : Q, onRunRight D e q' = true ∧
        ∃ o, M.step (some e.letter) q' e.next = Sum.inr (q, o, false)
    · rw [dif_pos hc] at h
      have hpair := Option.some_injective _ h
      have hq : hc.choose = q₁ := congrArg Prod.fst hpair
      have hdir : dir = true := (congrArg Prod.snd hpair).symm
      obtain ⟨hvis, o, ho⟩ := hc.choose_spec
      rw [hq] at hvis ho
      refine ⟨hdir, hi, o, ?_, ?_⟩
      · exact (onRunRight_iff D M hD w hi e he q₁).mp hvis
      · have hlast : (w.take (i + 1)).getLast? = some (w[i]'hi) := by
          rw [take_getLast?' w (by omega), if_neg (by omega)]
          simp only [Nat.add_sub_cancel]
          exact List.getElem?_eq_getElem hi
        have hhead : (w.drop (i + 1)).head? = e.next := by
          rw [List.head?_drop, hnext]
        have hstep : M.step (w.take (i + 1)).getLast? q₁ (w.drop (i + 1)).head?
            = Sum.inr (q, o, false) := by
          rw [hlast, hhead, ← hlet]
          exact ho
        have e1 : (w.take (i + 1)).dropLast = w.take i := by
          rw [List.dropLast_eq_take, List.length_take,
            min_eq_left (by omega : i + 1 ≤ w.length), List.take_take]
          congr 1
          omega
        have e2 : (w[i]'hi) :: w.drop (i + 1) = w.drop i := (List.drop_eq_getElem_cons hi).symm
        rw [stepCfg_left_some M hlast hstep, e1, e2]
    · rw [dif_neg hc] at h
      exact absurd h (by simp)
  · rw [List.getElem?_eq_none (by rw [annot_length]; omega), predRight] at h
    exact absurd h (by simp)

lemma predOf_sound (hD : D.accepts = {z | (visitAut M).Accepts z}) (w : List A) {i : ℕ}
    {q q₁ : Q} {dir : Bool}
    (h : predOf D M (prevLet (annot D w) i) ((annot D w)[i]?) q = some (q₁, dir)) :
    ∃ (k : ℕ) (o : List B),
      ((dir = false ∧ 0 < i ∧ k = i - 1) ∨ (dir = true ∧ i < w.length ∧ k = i + 1)) ∧
      Visits M w (Cfg.conf (w.take k) q₁ (w.drop k)) ∧
      M.stepCfg (Cfg.conf (w.take k) q₁ (w.drop k))
        = some (o, Cfg.conf (w.take i) q (w.drop i)) := by
  have hright : predRight D M ((annot D w)[i]?) q = some (q₁, dir) →
      ∃ (k : ℕ) (o : List B),
        ((dir = false ∧ 0 < i ∧ k = i - 1) ∨ (dir = true ∧ i < w.length ∧ k = i + 1)) ∧
        Visits M w (Cfg.conf (w.take k) q₁ (w.drop k)) ∧
        M.stepCfg (Cfg.conf (w.take k) q₁ (w.drop k))
          = some (o, Cfg.conf (w.take i) q (w.drop i)) := by
    intro hr
    obtain ⟨hdir, hi, o, hvis, hstep⟩ := predRight_sound D M hD w hr
    exact ⟨i + 1, o, Or.inr ⟨hdir, hi, rfl⟩, hvis, hstep⟩
  rcases hl : prevLet (annot D w) i with _ | d
  · rw [hl, predOf] at h
    exact hright h
  · rw [hl, predOf] at h
    by_cases hc : ∃ q' : Q, onRunLeft D d q' = true ∧
        ∃ o, M.step d.prev q' (some d.letter) = Sum.inr (q, o, true)
    · rw [dif_pos hc] at h
      have hpair := Option.some_injective _ h
      have hq : hc.choose = q₁ := congrArg Prod.fst hpair
      have hdir : dir = false := (congrArg Prod.snd hpair).symm
      obtain ⟨hvis, o, ho⟩ := hc.choose_spec
      rw [hq] at hvis ho
      have hipos : i ≠ 0 := by
        rintro rfl
        rw [prevLet_zero] at hl
        exact absurd hl (by simp)
      rw [prevLet_pos hipos] at hl
      have hi1 : i - 1 < w.length := by
        by_contra hcon
        rw [List.getElem?_eq_none (by rw [annot_length]; omega)] at hl
        exact absurd hl (by simp)
      obtain ⟨e, he, hprev, hlet, hnext⟩ := annot_getElem_eq D w hi1
      rw [he] at hl
      have hde : d = e := Option.some_injective _ hl.symm
      subst hde
      refine ⟨i - 1, o, Or.inl ⟨hdir, by omega, rfl⟩, ?_, ?_⟩
      · exact (onRunLeft_iff D M hD w hi1 d he q₁).mp hvis
      · have hdrop : w.drop (i - 1) = (w[i - 1]'hi1) :: w.drop i := by
          rw [List.drop_eq_getElem_cons hi1, show i - 1 + 1 = i from by omega]
        have hstep : M.step (w.take (i - 1)).getLast? q₁
            (((w[i - 1]'hi1) :: w.drop i).head?) = Sum.inr (q, o, true) := by
          rw [← hprev]
          simp only [List.head?_cons]
          rw [← hlet]
          exact ho
        rw [hdrop, stepCfg_right_cons M hstep,
          ← List.take_succ_eq_append_getElem hi1, show i - 1 + 1 = i from by omega]
    · rw [dif_neg hc] at h
      exact hright h

/-! ### Completeness -/

lemma predOf_isSome (hD : D.accepts = {z | (visitAut M).Accepts z}) (w : List A) {i : ℕ}
    (hi : i ≤ w.length) {q q₀ : Q} {u₀ v₀ : List A} {o : List B}
    (hvis : Visits M w (Cfg.conf u₀ q₀ v₀))
    (hstep : M.stepCfg (Cfg.conf u₀ q₀ v₀) = some (o, Cfg.conf (w.take i) q (w.drop i))) :
    ∃ x, predOf D M (prevLet (annot D w) i) ((annot D w)[i]?) q = some x := by
  have huv : u₀ ++ v₀ = w := visits_append M w hvis
  have hu₀ : w.take u₀.length = u₀ := by rw [← huv]; simp
  have hv₀ : w.drop u₀.length = v₀ := by rw [← huv]; simp
  have hu₀len : u₀.length ≤ w.length := by rw [← huv]; simp
  rcases hM : M.step u₀.getLast? q₀ v₀.head? with oo | ⟨q', oo, dir⟩
  · rw [stepCfg_halt_eq M hM] at hstep
    exact absurd hstep (by simp)
  · cases dir with
    | true =>
        cases hv : v₀ with
        | nil =>
            rw [hv] at hM
            rw [hv, stepCfg_right_nil M hM] at hstep
            exact absurd hstep (by simp)
        | cons a v₀' =>
            rw [hv] at hM
            rw [hv, stepCfg_right_cons M hM] at hstep
            have hpair := Option.some_injective _ hstep
            have hcfg : Cfg.conf (u₀ ++ [a]) q' v₀' = Cfg.conf (w.take i) q (w.drop i) :=
              congrArg Prod.snd hpair
            obtain ⟨h1, h2, -⟩ := Cfg.conf.injEq .. ▸ hcfg
            have hlen : u₀.length + 1 = i := by
              have := congrArg List.length h1
              simp only [List.length_append, List.length_cons, List.length_nil,
                List.length_take] at this
              omega
            have hipos : i ≠ 0 := by omega
            have hi1 : i - 1 < w.length := by omega
            have hu₀eq : u₀ = w.take (i - 1) := by
              rw [← hu₀, show u₀.length = i - 1 from by omega]
            have hv₀eq : v₀ = w.drop (i - 1) := by
              rw [← hv₀, show u₀.length = i - 1 from by omega]
            obtain ⟨e, he, hprev, hlet, hnext⟩ := annot_getElem_eq D w hi1
            have hcond : ∃ q₁ : Q, onRunLeft D e q₁ = true ∧
                ∃ o', M.step e.prev q₁ (some e.letter) = Sum.inr (q, o', true) := by
              refine ⟨q₀, ?_, oo, ?_⟩
              · refine (onRunLeft_iff D M hD w hi1 e he q₀).mpr ?_
                rw [← hu₀eq, ← hv₀eq]
                exact hvis
              · rw [hprev, ← hu₀eq, hlet]
                have hh : (some (w[i - 1]'hi1) : Option A) = v₀.head? := by
                  rw [hv₀eq, List.head?_drop, List.getElem?_eq_getElem hi1]
                rw [hh, ← h2, hv]
                exact hM
            refine ⟨(hcond.choose, false), ?_⟩
            rw [prevLet_pos hipos, he, predOf, dif_pos hcond]
    | false =>
        rcases hlast : u₀.getLast? with _ | a
        · rw [stepCfg_left_none M hlast hM] at hstep
          exact absurd hstep (by simp)
        · rw [stepCfg_left_some M hlast hM] at hstep
          have hpair := Option.some_injective _ hstep
          have hcfg : Cfg.conf u₀.dropLast q' (a :: v₀) = Cfg.conf (w.take i) q (w.drop i) :=
            congrArg Prod.snd hpair
          obtain ⟨h1, h2, -⟩ := Cfg.conf.injEq .. ▸ hcfg
          have hne : u₀ ≠ [] := by
            rintro rfl
            exact absurd hlast (by simp)
          have hlen : u₀.length = i + 1 := by
            have := congrArg List.length h1
            simp only [List.length_dropLast, List.length_take] at this
            have hpos : 0 < u₀.length := List.length_pos_iff.mpr hne
            omega
          have hilt : i < w.length := by omega
          have hu₀eq : u₀ = w.take (i + 1) := by rw [← hu₀, hlen]
          have hv₀eq : v₀ = w.drop (i + 1) := by rw [← hv₀, hlen]
          obtain ⟨e, he, hprev, hlet, hnext⟩ := annot_getElem_eq D w hilt
          by_cases hcl : (prevLet (annot D w) i).isSome ∧
              ∃ d : AnnLet A S, prevLet (annot D w) i = some d ∧
                ∃ q₁ : Q, onRunLeft D d q₁ = true ∧
                  ∃ o', M.step d.prev q₁ (some d.letter) = Sum.inr (q, o', true)
          · obtain ⟨-, d, hd, hcond⟩ := hcl
            exact ⟨(hcond.choose, false), by rw [hd, predOf, dif_pos hcond]⟩
          · have hcond : ∃ q₁ : Q, onRunRight D e q₁ = true ∧
                ∃ o', M.step (some e.letter) q₁ e.next = Sum.inr (q, o', false) := by
              refine ⟨q₀, ?_, oo, ?_⟩
              · refine (onRunRight_iff D M hD w hilt e he q₀).mpr ?_
                rw [← hu₀eq, ← hv₀eq]
                exact hvis
              · have hl' : (some e.letter : Option A) = u₀.getLast? := by
                  rw [hlet, hu₀eq, take_getLast?' w (by omega), if_neg (by omega)]
                  simp only [Nat.add_sub_cancel]
                  exact (List.getElem?_eq_getElem hilt).symm
                have hr' : e.next = v₀.head? := by
                  rw [hnext, hv₀eq, List.head?_drop]
                rw [hl', hr', ← h2]
                exact hM
            rcases hl : prevLet (annot D w) i with _ | d
            · exact ⟨(hcond.choose, true), by rw [predOf, he, predRight, dif_pos hcond]⟩
            · have hnc : ¬ ∃ q₁ : Q, onRunLeft D d q₁ = true ∧
                  ∃ o', M.step d.prev q₁ (some d.letter) = Sum.inr (q, o', true) := by
                intro hcc
                exact hcl ⟨by rw [hl]; rfl, d, hl, hcc⟩
              exact ⟨(hcond.choose, true),
                by rw [predOf, dif_neg hnc, he, predRight, dif_pos hcond]⟩

end TwoWay

end Lax916827Proofs.Transducers
