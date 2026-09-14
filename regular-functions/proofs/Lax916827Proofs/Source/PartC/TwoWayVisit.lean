/-
The configurations that lie on the run of a two-way transducer form a regular
property of the input, in the following sense: mark one letter of the input with
a state of the transducer and a side (left or right of that letter, which
selects a cut of the input); the marked inputs for which the run visits the
selected cut in the selected state form a regular language.

This is the step of the proof of Theorem `thm:composition-of-two-way-transducers` of *Transducers*
(M. Bojańczyk) that replaces the analysis of the reachable configuration graph of Lemma
`lem:compute-configuration-graph`: instead of describing the reachable configuration graph by hand,
we obtain the information needed to walk backwards along the run from a deterministic automaton,
using Shepherdson's Theorem (`TwoDFA.accepts_isRegular`) for the two-way automaton that simulates
the transducer and accepts as soon as the run reaches the marked cut in the marked state. -/
import Lax916827Proofs.Source.PartC.TwoWayRun
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- The marked alphabet: an input letter, possibly carrying a marker.  The
marker `Sum.inl q` selects the cut to the left of the letter and the state `q`,
the marker `Sum.inr q` selects the cut to its right. -/
abbrev Marked (A Q : Type) := A × Option (Q ⊕ Q)

/-- A string of the input alphabet, read as a marked string without markers. -/
def plainList {A : Type} (Q : Type) (w : List A) : List (Marked A Q) :=
  w.map (fun a => (a, none))

@[simp] lemma plainList_length {A Q : Type} (w : List A) : (plainList Q w).length = w.length := by
  simp [plainList]

@[simp] lemma plainList_map_fst {A Q : Type} (w : List A) :
    (plainList Q w).map Prod.fst = w := by
  simp [plainList, Function.comp_def]

namespace TwoWay

variable {A B Q : Type}

open scoped Classical

/-- The two-way automaton that simulates `M` and accepts as soon as the run
reaches the marked cut in the marked state.  If the run halts, or falls off the
input, before that, the automaton rejects. -/
noncomputable def visitAut (M : TwoWay A B Q) : TwoDFA (Marked A Q) Q where
  init := M.init
  step := fun l q r =>
    if (∃ x : A, r = some (x, some (Sum.inl q))) ∨ (∃ x : A, l = some (x, some (Sum.inr q))) then
      Sum.inl true
    else
      match M.step (l.map Prod.fst) q (r.map Prod.fst) with
      | Sum.inl _ => Sum.inl false
      | Sum.inr (q', _, d) => Sum.inr (q', d)

/-- The cut `i` of the marked string `z` carries the marker for the state `q`. -/
def hit (z : List (Marked A Q)) (i : ℕ) (q : Q) : Prop :=
  (∃ x : A, z[i]? = some (x, some (Sum.inl q))) ∨
    (∃ x : A, (if i = 0 then none else z[i - 1]?) = some (x, some (Sum.inr q)))

/-- The configuration of `visitAut M` corresponding to a configuration of `M`. -/
def visCfg : Cfg A Q → TwoCfg Q
  | Cfg.conf u q _ => Sum.inl (u.length, q)
  | Cfg.halt => Sum.inr false

/-- The configuration of `visitAut M` corresponding to a step of the run. -/
def visCfgOpt : Option (Cfg A Q) → TwoCfg Q
  | some c => visCfg c
  | none => Sum.inr false

variable (M : TwoWay A B Q)

lemma visitAut_step_hit {l r : Option (Marked A Q)} {q : Q}
    (h : (∃ x : A, r = some (x, some (Sum.inl q))) ∨ (∃ x : A, l = some (x, some (Sum.inr q)))) :
    (visitAut M).step l q r = Sum.inl true := by
  simp only [visitAut, if_pos h]

lemma visitAut_step_miss {l r : Option (Marked A Q)} {q : Q}
    (h : ¬ ((∃ x : A, r = some (x, some (Sum.inl q))) ∨
      (∃ x : A, l = some (x, some (Sum.inr q))))) :
    (visitAut M).step l q r =
      (match M.step (l.map Prod.fst) q (r.map Prod.fst) with
        | Sum.inl _ => Sum.inl false
        | Sum.inr (q', _, d) => Sum.inr (q', d)) := by
  simp only [visitAut, if_neg h]

/-- At a marked cut the automaton accepts. -/
lemma next_visCfg_hit {z : List (Marked A Q)} {i : ℕ} {q : Q} (h : hit z i q) :
    (visitAut M).next z (Sum.inl (i, q)) = Sum.inr true := by
  have h' : (∃ x : A, z[i]? = some (x, some (Sum.inl q))) ∨
      (∃ x : A, (if i = 0 then none else z[i - 1]?) = some (x, some (Sum.inr q))) := h
  simp only [TwoDFA.next, visitAut_step_hit M h']

/-- Away from the marked cut, the automaton follows the run of `M`. -/
lemma next_visCfg {z : List (Marked A Q)} {w u v : List A} {q : Q}
    (hz : z.map Prod.fst = w) (huv : u ++ v = w) (hnot : ¬ hit z u.length q) :
    (visitAut M).next z (Sum.inl (u.length, q))
      = visCfgOpt ((M.stepCfg (Cfg.conf u q v)).map Prod.snd) := by
  have hlenz : z.length = w.length := by rw [← hz]; simp
  have hmap : ∀ i : ℕ, z[i]?.map Prod.fst = w[i]? := by
    intro i; rw [← hz, List.getElem?_map]
  have hleft : (if u.length = 0 then none else z[u.length - 1]?).map Prod.fst = u.getLast? := by
    by_cases hu : u = []
    · simp [hu]
    · have hpos : 0 < u.length := List.length_pos_iff.mpr hu
      rw [if_neg (by omega), hmap, ← huv, List.getElem?_append_left (by omega),
        List.getLast?_eq_getElem?]
  have hright : z[u.length]?.map Prod.fst = v.head? := by
    rw [hmap, ← huv, List.getElem?_append_right (le_refl _), Nat.sub_self,
      ← List.head?_eq_getElem?]
  have hlen : w.length = u.length + v.length := by rw [← huv]; simp
  have hnot' : ¬ ((∃ x : A, z[u.length]? = some (x, some (Sum.inl q))) ∨
      (∃ x : A, (if u.length = 0 then none else z[u.length - 1]?)
        = some (x, some (Sum.inr q)))) := hnot
  rw [TwoDFA.next, visitAut_step_miss M hnot', hleft, hright]
  rcases hM : M.step u.getLast? q v.head? with o | ⟨q', o, dir⟩
  · rw [stepCfg_halt_eq M hM]
    rfl
  · cases dir with
    | true =>
        cases v with
        | nil =>
            rw [stepCfg_right_nil M hM]
            have : ¬ (u.length < z.length) := by rw [hlenz]; simp at hlen; omega
            simp only [visCfgOpt, Option.map_none, if_neg this]
        | cons b v' =>
            rw [stepCfg_right_cons M hM]
            have hlt : u.length < z.length := by rw [hlenz]; simp at hlen; omega
            simp only [visCfgOpt, visCfg, Option.map_some, if_pos hlt]
            simp
    | false =>
        rcases hu : u.getLast? with _ | b
        · rw [stepCfg_left_none M hu hM]
          have h0 : u.length = 0 := by
            rcases u with _ | ⟨c, u'⟩
            · simp
            · simp at hu
          simp only [visCfgOpt, Option.map_none, if_neg (by omega : ¬ (0 < u.length))]
        · rw [stepCfg_left_some M hu hM]
          have hpos : 0 < u.length := by
            rcases u with _ | ⟨c, u'⟩
            · simp at hu
            · simp
          simp only [visCfgOpt, visCfg, Option.map_some, if_pos hpos]
          simp

/-- As long as the run of `M` has not reached a marked cut, the run of the
automaton follows it. -/
lemma iterate_visCfg {z : List (Marked A Q)} {w : List A} (hz : z.map Prod.fst = w) (t : ℕ)
    (hmiss : ∀ s < t, ∀ u q v, cfgAt M w s = some (Cfg.conf u q v) → ¬ hit z u.length q) :
    ((visitAut M).next z)^[t] (Sum.inl (0, (visitAut M).init)) = visCfgOpt (cfgAt M w t) := by
  induction t with
  | zero => simp [visCfgOpt, visCfg, visitAut]
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (fun s hs => hmiss s (by omega))]
      rcases hc : cfgAt M w t with _ | c
      · rw [cfgAt_none_succ M w hc]
        rfl
      · cases c with
        | halt =>
            rw [cfgAt_halt_succ M w hc]
            rfl
        | conf u q v =>
            have hnot := hmiss t (by omega) u q v hc
            rw [show visCfgOpt (some (Cfg.conf u q v)) = Sum.inl (u.length, q) from rfl,
              next_visCfg M hz (cfgAt_append M w t hc) hnot, cfgAt_succ, hc]
            rfl

/-- The automaton accepts exactly when the run of `M` visits a marked cut in the
marked state. -/
theorem visitAut_accepts_iff {z : List (Marked A Q)} {w : List A} (hz : z.map Prod.fst = w) :
    (visitAut M).Accepts z ↔ ∃ u q v, Visits M w (Cfg.conf u q v) ∧ hit z u.length q := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    by_contra hcon
    push_neg at hcon
    have hmiss : ∀ s < n, ∀ u q v, cfgAt M w s = some (Cfg.conf u q v) → ¬ hit z u.length q := by
      intro s _ u q v hs hhit
      exact hcon u q v ⟨s, hs⟩ hhit
    rw [iterate_visCfg M hz n hmiss] at hn
    rcases hcc : cfgAt M w n with _ | c
    · rw [hcc] at hn; exact absurd hn (by simp [visCfgOpt])
    · cases c with
      | halt => rw [hcc] at hn; exact absurd hn (by simp [visCfgOpt, visCfg])
      | conf u q v => rw [hcc] at hn; exact absurd hn (by simp [visCfgOpt, visCfg])
  · rintro ⟨u, q, v, ⟨n, hn⟩, hhit⟩
    have hex : ∃ t, ∃ u q v, cfgAt M w t = some (Cfg.conf u q v) ∧ hit z u.length q :=
      ⟨n, u, q, v, hn, hhit⟩
    obtain ⟨u', q', v', hc', hhit'⟩ := Nat.find_spec hex
    have hmiss : ∀ s < Nat.find hex, ∀ u q v,
        cfgAt M w s = some (Cfg.conf u q v) → ¬ hit z u.length q := by
      intro s hs u₁ q₁ v₁ h₁ hh₁
      exact Nat.find_min hex hs ⟨u₁, q₁, v₁, h₁, hh₁⟩
    refine ⟨Nat.find hex + 1, ?_⟩
    rw [Function.iterate_succ_apply', iterate_visCfg M hz _ hmiss, hc']
    exact next_visCfg_hit M hhit'

/-! ### The two marked words -/

/-- The marker carried by the letter at a position. -/
lemma getElem?_marked (x : List A) (mk : Option (Q ⊕ Q)) (a : A) (y : List A) (i : ℕ) :
    ((plainList Q x ++ (a, mk) :: plainList Q y)[i]?).bind (fun c => c.2) =
      if i = x.length then mk else none := by
  rcases lt_trichotomy i x.length with h | h | h
  · rw [List.getElem?_append_left (by simpa using h), if_neg (by omega)]
    rcases hx : (plainList Q x)[i]? with _ | c
    · rfl
    · have : c ∈ plainList Q x := List.mem_of_getElem? hx
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp this
      rfl
  · subst h
    rw [List.getElem?_append_right (by simp), if_pos rfl]
    simp
  · rw [List.getElem?_append_right (by simp; omega), if_neg (by omega)]
    have hi : i - (plainList Q x).length = (i - x.length - 1) + 1 := by simp; omega
    rw [hi, List.getElem?_cons_succ]
    rcases hy : (plainList Q y)[i - x.length - 1]? with _ | c
    · rfl
    · have : c ∈ plainList Q y := List.mem_of_getElem? hy
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp this
      rfl

lemma exists_fst_iff {z : List (Marked A Q)} {i : ℕ} {mk : Q ⊕ Q} :
    (∃ x : A, z[i]? = some (x, some mk)) ↔ z[i]?.bind (fun c => c.2) = some mk := by
  rcases hz : z[i]? with _ | ⟨b, o⟩
  · simp
  · constructor
    · rintro ⟨x, hx⟩
      rw [hx]
      rfl
    · intro h
      simp only [Option.bind_some] at h
      exact ⟨b, by rw [h]⟩

lemma hit_left (x : List A) (a : A) (y : List A) (q₀ : Q) (i : ℕ) (q : Q) :
    hit (plainList Q x ++ (a, some (Sum.inl q₀)) :: plainList Q y) i q ↔
      (i = x.length ∧ q = q₀) := by
  constructor
  · rintro (h | h)
    · rw [exists_fst_iff, getElem?_marked] at h
      by_cases hi : i = x.length
      · rw [if_pos hi] at h
        exact ⟨hi, by simpa using (Option.some_injective _ h).symm⟩
      · rw [if_neg hi] at h; simp at h
    · obtain ⟨b, hb⟩ := h
      by_cases hi : i = 0
      · rw [if_pos hi] at hb; simp at hb
      · rw [if_neg hi] at hb
        have : ((plainList Q x ++ (a, some (Sum.inl q₀)) :: plainList Q y)[i - 1]?).bind
            (fun c => c.2) = some (Sum.inr q) := by rw [hb]; rfl
        rw [getElem?_marked] at this
        by_cases hi' : i - 1 = x.length
        · rw [if_pos hi'] at this; simp at this
        · rw [if_neg hi'] at this; simp at this
  · rintro ⟨rfl, rfl⟩
    left
    rw [exists_fst_iff, getElem?_marked, if_pos rfl]

lemma hit_right (x : List A) (a : A) (y : List A) (q₀ : Q) (i : ℕ) (q : Q) :
    hit (plainList Q x ++ (a, some (Sum.inr q₀)) :: plainList Q y) i q ↔
      (i = x.length + 1 ∧ q = q₀) := by
  constructor
  · rintro (h | h)
    · rw [exists_fst_iff, getElem?_marked] at h
      by_cases hi : i = x.length
      · rw [if_pos hi] at h; simp at h
      · rw [if_neg hi] at h; simp at h
    · obtain ⟨b, hb⟩ := h
      by_cases hi : i = 0
      · rw [if_pos hi] at hb; simp at hb
      · rw [if_neg hi] at hb
        have hbb : ((plainList Q x ++ (a, some (Sum.inr q₀)) :: plainList Q y)[i - 1]?).bind
            (fun c => c.2) = some (Sum.inr q) := by rw [hb]; rfl
        rw [getElem?_marked] at hbb
        by_cases hi' : i - 1 = x.length
        · rw [if_pos hi'] at hbb
          refine ⟨by omega, ?_⟩
          simpa using (Option.some_injective _ hbb).symm
        · rw [if_neg hi'] at hbb; simp at hbb
  · rintro ⟨rfl, rfl⟩
    right
    refine ⟨a, ?_⟩
    have hne : ¬ (x.length + 1 = 0) := by omega
    rw [if_neg hne]
    have h1 : x.length + 1 - 1 = x.length := by omega
    rw [h1, List.getElem?_append_right (by simp)]
    simp

/-- The run visits the cut before the marked letter in the marked state. -/
theorem visits_iff_accepts_left (x : List A) (a : A) (y : List A) (q : Q) :
    Visits M (x ++ a :: y) (Cfg.conf x q (a :: y)) ↔
      (visitAut M).Accepts (plainList Q x ++ (a, some (Sum.inl q)) :: plainList Q y) := by
  have hz : (plainList Q x ++ (a, some (Sum.inl q)) :: plainList Q y).map Prod.fst
      = x ++ a :: y := by
    simp [plainList, Function.comp_def]
  rw [visitAut_accepts_iff M hz]
  constructor
  · intro h
    exact ⟨x, q, a :: y, h, (hit_left x a y q x.length q).mpr ⟨rfl, rfl⟩⟩
  · rintro ⟨u, q', v, hv, hh⟩
    obtain ⟨hlen, rfl⟩ := (hit_left x a y q u.length q').mp hh
    have huv : u ++ v = x ++ a :: y := visits_append M _ hv
    obtain ⟨rfl, rfl⟩ := List.append_inj huv hlen
    exact hv

/-- The run visits the cut after the marked letter in the marked state. -/
theorem visits_iff_accepts_right (x : List A) (a : A) (y : List A) (q : Q) :
    Visits M (x ++ a :: y) (Cfg.conf (x ++ [a]) q y) ↔
      (visitAut M).Accepts (plainList Q x ++ (a, some (Sum.inr q)) :: plainList Q y) := by
  have hz : (plainList Q x ++ (a, some (Sum.inr q)) :: plainList Q y).map Prod.fst
      = x ++ a :: y := by
    simp [plainList, Function.comp_def]
  rw [visitAut_accepts_iff M hz]
  constructor
  · intro h
    refine ⟨x ++ [a], q, y, h, (hit_right x a y q _ q).mpr ⟨by simp, rfl⟩⟩
  · rintro ⟨u, q', v, hv, hh⟩
    obtain ⟨hlen, rfl⟩ := (hit_right x a y q u.length q').mp hh
    have huv : u ++ v = x ++ a :: y := visits_append M _ hv
    have hlen' : u.length = (x ++ [a]).length := by simp [hlen]
    have huv' : u ++ v = (x ++ [a]) ++ y := by simpa using huv
    obtain ⟨rfl, rfl⟩ := List.append_inj huv' hlen'
    exact hv

/-- The marked inputs whose run visits the marked cut in the marked state form a
regular language. -/
theorem visitLang_isRegular [Finite A] [Finite Q] :
    Language.IsRegular {z : List (Marked A Q) | (visitAut M).Accepts z} :=
  TwoDFA.accepts_isRegular _

end TwoWay

end Lax916827Proofs.Transducers
