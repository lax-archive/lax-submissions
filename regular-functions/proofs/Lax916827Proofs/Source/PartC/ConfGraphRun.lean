/-
The string encoding of the reachable configuration graph agrees with the run semantics.

The two-way transducer `TwoWay.pathTrans M` of `ConfGraph.lean` walks along the encoded
configuration graph `TwoWay.enc M w`.  This file proves that its run mirrors the run of `M` on `w`
step by step, and therefore that

* `TwoWay.computes_enc`: if `M` outputs `v` on `w`, then `pathTrans M` outputs `v` on `enc M w`;
* `TwoWay.computes_enc_iff`: whenever the run of `M` on `w` halts, the two views are
  interchangeable.

This is the sense in which the encoding of Section *Continuity* of *Transducers* (M. Bojańczyk) and
the run semantics of `TwoWayRun.lean` describe the same object.
-/
import Lax916827Proofs.Source.PartC.ConfGraph
import Lax916827Proofs.Source.PartC.RegCodeBound
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-! ## Auxiliary facts about the run -/

/-- On the empty input, the only configuration on the run is the initial one. -/
lemma visits_nil_conf {M : TwoWay A B Q} {u v : List A} {q : Q}
    (h : Visits M [] (Cfg.conf u q v)) : u = [] ∧ v = [] ∧ q = M.init := by
  obtain ⟨t, ht⟩ := h
  have huv : u ++ v = [] := cfgAt_append M [] t ht
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv
  refine ⟨rfl, rfl, ?_⟩
  cases t with
  | zero =>
      simp only [cfgAt_zero, Option.some.injEq, Cfg.conf.injEq] at ht
      exact ht.2.1.symm
  | succ s =>
      obtain ⟨c', hc', hstep⟩ := exists_pred M [] ht
      cases c' with
      | halt => simp [stepCfg] at hstep
      | conf u' q' v' =>
          have huv' : u' ++ v' = [] := cfgAt_append M [] s hc'
          obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv'
          rcases hM : M.step (([] : List A).getLast?) q' (([] : List A).head?) with o | ⟨p, o, dir⟩
          · rw [stepCfg_halt_eq M hM] at hstep
            simp at hstep
          · cases dir with
            | true => rw [stepCfg_right_nil M hM] at hstep; simp at hstep
            | false =>
                rw [stepCfg_left_none M (by simp) hM] at hstep
                simp at hstep

/-- A configuration reached from a configuration on the run is again on the run. -/
lemma visits_step (M : TwoWay A B Q) {w : List A} {c c' : Cfg A Q} {o : List B}
    (hvis : Visits M w c) (hs : M.stepCfg c = some (o, c')) : Visits M w c' := by
  obtain ⟨t, ht⟩ := hvis
  exact ⟨t + 1, cfgAt_succ_of_step M w ht hs⟩

/-! ## Reading the encoded graph at a cut -/

variable (M : TwoWay A B Q) {w : List A}

lemma enc_take_getLast? (hw : w ≠ []) {i : ℕ} (h0 : i ≠ 0) (hi : i ≤ w.length) :
    ((enc M w).take i).getLast? = some (Sum.inl (encSlice M w (i - 1))) := by
  have hlen : (enc M w).length = w.length := enc_length hw
  have hli : ((enc M w).take i).length = i := by
    rw [List.length_take, hlen]; omega
  rw [List.getLast?_eq_getElem?, hli, List.getElem?_take, if_pos (by omega),
    enc_getElem? hw (by omega : i - 1 < w.length)]

lemma enc_drop_head? (hw : w ≠ []) {i : ℕ} (hi : i < w.length) :
    ((enc M w).drop i).head? = some (Sum.inl (encSlice M w i)) := by
  rw [List.head?_drop, enc_getElem? hw hi]

lemma enc_drop_head?_end (hw : w ≠ []) {i : ℕ} (hi : w.length ≤ i) :
    ((enc M w).drop i).head? = none := by
  have hlen : (enc M w).length = w.length := enc_length hw
  rw [List.head?_drop, List.getElem?_eq_none (by omega)]

lemma readR_enc (hw : w ≠ []) {i : ℕ} (hi : i < w.length) (q : Q) :
    readR ((enc M w).drop i).head? q = cutV M w i q true := by
  rw [enc_drop_head? M hw hi]
  rfl

lemma readR_enc_end (hw : w ≠ []) {i : ℕ} (hi : w.length ≤ i) (q : Q) :
    readR ((enc M w).drop i).head? q = VOut.nil := by
  rw [enc_drop_head?_end M hw hi]
  rfl

lemma readL_enc (hw : w ≠ []) {i : ℕ} (h0 : i ≠ 0) (hi : i ≤ w.length) (q : Q) :
    readL ((enc M w).take i).getLast? q = cutV M w i q false := by
  rw [enc_take_getLast? M hw h0 hi]
  show cutV M w (i - 1 + 1) q false = _
  rw [show i - 1 + 1 = i by omega]

/-! ## The step of `pathTrans M` on an encoded graph -/

/-- One step of the run of `M` is mirrored by one step of the run of `pathTrans M` on the encoded
configuration graph. -/
lemma stepCfg_pathTrans {u v : List A} {q : Q} {o : List B} {c : Cfg A Q}
    (hvis : Visits M w (Cfg.conf u q v)) (hs : M.stepCfg (Cfg.conf u q v) = some (o, c)) :
    (pathTrans M).stepCfg (encCfg M w (Cfg.conf u q v)) = some (o, encCfg M w c) := by
  classical
  have huv : u ++ v = w := visits_append M w hvis
  have hu : w.take u.length = u := by rw [← huv]; simp
  have hv : w.drop u.length = v := by rw [← huv]; simp
  have hile : u.length ≤ w.length := by rw [← huv]; simp
  have hgl : prevAt w u.length = u.getLast? := by
    rcases Nat.eq_zero_or_pos u.length with h0 | hpos
    · have : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [prevAt, if_pos h0, this]; rfl
    · rw [prevAt, if_neg (by omega), ← hu, List.getLast?_eq_getElem?, List.length_take,
        show min u.length w.length = u.length by omega, List.getElem?_take, if_pos (by omega)]
  have hhd : w[u.length]? = v.head? := by rw [← hv, List.head?_drop]
  have hvis' : Visits M w (Cfg.conf (w.take u.length) q (w.drop u.length)) := by
    rw [hu, hv]; exact hvis
  have hcut : ∀ d : Bool, cutV M w u.length q d = edgeOf M u.getLast? q v.head? d := by
    intro d
    rw [cutV, if_pos hvis', hgl, hhd]
  by_cases hw : w = []
  · -- the empty input: the special letter of the alphabet `C`
    subst hw
    obtain ⟨rfl, rfl, rfl⟩ := visits_nil_conf hvis
    rcases hM : M.step (([] : List A).getLast?) M.init (([] : List A).head?) with o' | ⟨p, o', dir⟩
    · rw [stepCfg_halt_eq M hM] at hs
      obtain ⟨rfl, rfl⟩ : o' = o ∧ Cfg.halt = c := by
        simpa [Prod.ext_iff] using Option.some.inj hs
      have hMn : M.step none M.init none = Sum.inl o' := by simpa using hM
      have hem : emptyOut M = some (labOf M none M.init none) := by
        simp only [emptyOut, hMn]
      have hread : readR ((enc M ([] : List A)).drop 0).head? M.init
          = VOut.halt (labOf M none M.init none) := by
        rw [enc_nil]
        show readR (some (Sum.inr (emptyOut M))) M.init = _
        rw [hem]
        rfl
      have hstep := pathTrans_step_readR_halt (l := ((enc M ([] : List A)).take 0).getLast?) hread
      rw [labOf_val, transOut_halt hMn] at hstep
      simpa using stepCfg_halt_eq (pathTrans M) (u := (enc M ([] : List A)).take 0)
        (v := (enc M ([] : List A)).drop 0) hstep
    · cases dir with
      | true => rw [stepCfg_right_nil M hM] at hs; simp at hs
      | false => rw [stepCfg_left_none M (by simp) hM] at hs; simp at hs
  · -- the general case
    have hlenE : (enc M w).length = w.length := enc_length hw
    have hwpos : 0 < w.length := List.length_pos_iff.mpr hw
    rcases hM : M.step u.getLast? q v.head? with o' | ⟨p, o', dir⟩
    · -- a halting transition
      rw [stepCfg_halt_eq M hM] at hs
      obtain ⟨rfl, rfl⟩ : o' = o ∧ Cfg.halt = c := by
        simpa [Prod.ext_iff] using Option.some.inj hs
      have hedge : ∀ d : Bool, cutV M w u.length q d = VOut.halt (labOf M u.getLast? q v.head?) :=
        fun d => by rw [hcut d, edgeOf_halt hM]
      have hstep : (pathTrans M).step (((enc M w).take u.length).getLast?) q
          (((enc M w).drop u.length).head?) = Sum.inl o' := by
        by_cases hlt : u.length < w.length
        · have hr : readR ((enc M w).drop u.length).head? q
              = VOut.halt (labOf M u.getLast? q v.head?) := by
            rw [readR_enc M hw hlt, hedge true]
          have := pathTrans_step_readR_halt (l := ((enc M w).take u.length).getLast?) hr
          rwa [labOf_val, transOut_halt hM] at this
        · have hr : readR ((enc M w).drop u.length).head? q = VOut.nil :=
            readR_enc_end M hw (by omega) q
          have hl : readL ((enc M w).take u.length).getLast? q
              = VOut.halt (labOf M u.getLast? q v.head?) := by
            rw [readL_enc M hw (by omega) hile, hedge false]
          have := pathTrans_step_readL_halt hr hl
          rwa [labOf_val, transOut_halt hM] at this
      simp only [encCfg_conf, encCfg_halt]
      exact stepCfg_halt_eq (pathTrans M) hstep
    · cases dir with
      | true =>
          -- a transition that moves the head right
          rcases hvv : v with _ | ⟨a, v'⟩
          · rw [hvv] at hs hM
            rw [stepCfg_right_nil M hM] at hs
            simp at hs
          · rw [hvv] at hs hM
            rw [stepCfg_right_cons M hM] at hs
            obtain ⟨rfl, rfl⟩ : o' = o ∧ Cfg.conf (u ++ [a]) p v' = c := by
              simpa [Prod.ext_iff] using Option.some.inj hs
            have hlt : u.length < w.length := by
              have : u.length + (a :: v').length = w.length := by
                rw [← huv, hvv]; simp
              simp at this ⊢
              omega
            have hr : readR ((enc M w).drop u.length).head? q
                = VOut.move p (labOf M u.getLast? q (a :: v').head?) := by
              rw [readR_enc M hw hlt, hcut true, hvv, edgeOf_move hM]
            have hstep := pathTrans_step_readR_move
              (l := ((enc M w).take u.length).getLast?) hr
            rw [labOf_val, transOut_move hM] at hstep
            -- the encoded configuration reached by that step
            have hdrop : (enc M w).drop u.length
                = (enc M w)[u.length]'(by omega) :: (enc M w).drop (u.length + 1) :=
              List.drop_eq_getElem_cons (by omega)
            have htake : (enc M w).take (u.length + 1)
                = (enc M w).take u.length ++ [(enc M w)[u.length]'(by omega)] :=
              List.take_succ_eq_append_getElem (by omega)
            have hlen1 : (u ++ [a]).length = u.length + 1 := by simp
            simp only [encCfg_conf, hlen1]
            rw [htake, hdrop]
            rw [hdrop] at hstep
            exact stepCfg_right_cons (pathTrans M) hstep
      | false =>
          -- a transition that moves the head left
          rcases hu' : u.getLast? with _ | a
          · rw [hu'] at hM
            rw [stepCfg_left_none M hu' (by rw [hu']; exact hM)] at hs
            simp at hs
          · have hM' : M.step u.getLast? q v.head? = Sum.inr (p, o', false) := hM
            rw [stepCfg_left_some M hu' hM'] at hs
            obtain ⟨rfl, rfl⟩ : o' = o ∧ Cfg.conf u.dropLast p (a :: v) = c := by
              simpa [Prod.ext_iff] using Option.some.inj hs
            have hpos : 0 < u.length := by
              rcases u with _ | ⟨b, u'⟩
              · simp at hu'
              · simp
            have hr : readR ((enc M w).drop u.length).head? q = VOut.nil := by
              by_cases hlt : u.length < w.length
              · rw [readR_enc M hw hlt, hcut true, edgeOf_move_ne hM' (by simp)]
              · exact readR_enc_end M hw (by omega) q
            have hl : readL ((enc M w).take u.length).getLast? q
                = VOut.move p (labOf M u.getLast? q v.head?) := by
              rw [readL_enc M hw (by omega) hile, hcut false, edgeOf_move hM']
            have hstep := pathTrans_step_readL_move hr hl
            rw [labOf_val, transOut_move hM'] at hstep
            have hEl : ((enc M w).take u.length).getLast?
                = some (Sum.inl (encSlice M w (u.length - 1))) :=
              enc_take_getLast? M hw (by omega) hile
            have hdropL : (enc M w).drop (u.length - 1)
                = Sum.inl (encSlice M w (u.length - 1)) :: (enc M w).drop u.length := by
              have hc : (enc M w).drop (u.length - 1)
                  = (enc M w)[u.length - 1]'(by omega) :: (enc M w).drop (u.length - 1 + 1) :=
                List.drop_eq_getElem_cons (by omega)
              rw [show u.length - 1 + 1 = u.length by omega] at hc
              have hEi : (enc M w)[u.length - 1]'(by omega)
                  = Sum.inl (encSlice M w (u.length - 1)) := by
                have := enc_getElem? (M := M) hw (by omega : u.length - 1 < w.length)
                rw [List.getElem?_eq_getElem (by omega)] at this
                exact Option.some.inj this
              rw [hc, hEi]
            have hdropLast : ((enc M w).take u.length).dropLast
                = (enc M w).take (u.length - 1) := by
              rw [List.dropLast_eq_take, List.length_take,
                show min u.length (enc M w).length = u.length by omega, List.take_take,
                show min (u.length - 1) u.length = u.length - 1 by omega]
            simp only [encCfg_conf, List.length_dropLast, ← hdropLast, hdropL]
            exact stepCfg_left_some (pathTrans M) hEl hstep

/-! ## The runs of `M` and of `pathTrans M` agree -/

/-- The run of `pathTrans M` on the encoded configuration graph mirrors the run of `M`. -/
lemma reaches_pathTrans {c t : Cfg A Q} {out : List B} (h : M.Reaches c out t) :
    t = Cfg.halt → Visits M w c → (pathTrans M).Reaches (encCfg M w c) out Cfg.halt := by
  induction h with
  | refl c =>
      rintro rfl _
      simpa using Reaches.refl (M := pathTrans M) Cfg.halt
  | @step c c' c'' o o' hstep _ ih =>
      rintro rfl hvis
      obtain ⟨u, q, v, rfl⟩ := exists_conf_of_stepCfg M hstep
      have hnext : (pathTrans M).stepCfg (encCfg M w (Cfg.conf u q v)) = some (o, encCfg M w c') :=
        stepCfg_pathTrans M hvis hstep
      exact Reaches.step hnext (ih rfl (visits_step M hvis hstep))

/-- **The encoding agrees with the run semantics.**  If the two-way transducer `M` outputs `v` on
the input `w`, then the transducer `pathTrans M`, which walks along the encoded reachable
configuration graph, outputs `v` on `enc M w`. -/
theorem computes_enc {v : List B} (h : M.Computes w v) :
    (pathTrans M).Computes (enc M w) v := by
  have hvis : Visits M w (Cfg.conf [] M.init w) := ⟨0, rfl⟩
  have hre := reaches_pathTrans M h rfl hvis
  simpa [Computes, encCfg] using hre

/-- **The encoding agrees with the run semantics**, in both directions: whenever the run of `M` on
`w` halts, the outputs of `M` on `w` and of `pathTrans M` on the encoded configuration graph are the
same. -/
theorem computes_enc_iff {v : List B} (hhalt : ∃ v₀, M.Computes w v₀) :
    (pathTrans M).Computes (enc M w) v ↔ M.Computes w v := by
  obtain ⟨v₀, h₀⟩ := hhalt
  constructor
  · intro h
    have hvv := computes_unique h (computes_enc M h₀)
    rw [hvv]
    exact h₀
  · exact computes_enc M

end TwoWay

end Lax916827Proofs.Transducers
