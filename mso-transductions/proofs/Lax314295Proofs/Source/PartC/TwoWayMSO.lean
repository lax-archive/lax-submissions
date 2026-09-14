/- From two-way transducers to mso transductions: the easy half of Theorem
`thm:logic-regular-functions` of *Transducers* (M. Bojańczyk).

As in the book, the mso transduction simply formalises the semantics of the
two-way transducer: the elements of the output universe are the pairs

  (configuration of the run, index of a letter in the string produced there),

that is, `|Q| · (K+1)` copies of the input positions (plus as many extra
elements for the configurations whose head is at the right end of the input),
where `K` bounds the length of the string produced by one transition.  An
element is selected when the run really visits that configuration and really
produces that letter; the letter formulas give the letter produced; and the
order is the order of time.

All the formulas are obtained from `RequestProject/PartC/RunMark.lean`, where
the corresponding properties of the marked input string are shown to be regular,
through Theorem `thm:mso-logic-languages` in the form of
`RequestProject/PartC/MarkLogic.lean` (one free variable) and
`RequestProject/PartC/MarkLogic2.lean` (two free variables).  The combinatorics
of the output list is in `RequestProject/PartC/RunElts.lean`.
-/
import Lax314295Proofs.Source.PartC.RunElts
import Lax916827Proofs.Source.PartC.RunMark
import Lax314295Proofs.Source.PartC.MarkLogic
import Lax916827Proofs.Source.PartC.MarkLogic2
import Lax916827Proofs.Source.PartC.MSODef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace TwoWayMSO

open TwoWay MarkStr RunMark RunElts

variable {A B Q : Type}

/-! ## Targets of the three kinds -/

lemma tgPos_zero (q : Q) (w : List A) (x y : ℕ) : tgPos (⟨q, 0⟩ : Tgt Q) w x y = x := by
  simp [tgPos]

lemma tgPos_one (q : Q) (w : List A) (x y : ℕ) : tgPos (⟨q, 1⟩ : Tgt Q) w x y = y := by
  simp [tgPos]

lemma tgPos_two (q : Q) (w : List A) (x y : ℕ) : tgPos (⟨q, 2⟩ : Tgt Q) w x y = w.length := by
  simp [tgPos]

lemma tgOK_zero (q : Q) (w : List A) (x y : ℕ) :
    TgOK (⟨q, 0⟩ : Tgt Q) w x y ↔ x < w.length := by simp [TgOK]

lemma tgOK_one (q : Q) (w : List A) (x y : ℕ) :
    TgOK (⟨q, 1⟩ : Tgt Q) w x y ↔ y < w.length := by simp [TgOK]

lemma tgOK_two (q : Q) (w : List A) (x y : ℕ) : TgOK (⟨q, 2⟩ : Tgt Q) w x y := by
  simp [TgOK]

/-! ## The elements -/

variable {m K : ℕ}

/-- The state of an element. -/
def eltSt (eIdx : Q × Fin (K + 1) ≃ Fin m) : (Fin m × ℕ) ⊕ Fin m → Q
  | Sum.inl (c, _) => (eIdx.symm c).1
  | Sum.inr d => (eIdx.symm d).1

/-- The index, inside the string produced by one transition, of an element. -/
def eltIx (eIdx : Q × Fin (K + 1) ≃ Fin m) : (Fin m × ℕ) ⊕ Fin m → ℕ
  | Sum.inl (c, _) => ((eIdx.symm c).2 : ℕ)
  | Sum.inr d => ((eIdx.symm d).2 : ℕ)

/-- The head position of an element.  A copy of a position that does not exist
is sent to `|w| + 1`, which is not the position of any configuration. -/
def eltPos (w : List A) : (Fin m × ℕ) ⊕ Fin m → ℕ
  | Sum.inl (_, p) => if p < w.length then p else w.length + 1
  | Sum.inr _ => w.length

/-- The state and the head position of the run at a given time. -/
noncomputable def stPos (M : TwoWay A B Q) (w : List A) (t : ℕ) : Q × ℕ :=
  match cfgAt M w t with
  | some (Cfg.conf x q _) => (q, x.length)
  | _ => (M.init, 0)

lemma stPos_eq (M : TwoWay A B Q) (w : List A) {q : Q} {p t : ℕ} (h : RunAt M w q p t) :
    stPos M w t = (q, p) := by
  have hc := h.take_drop
  have hp : p ≤ w.length := h.le_length
  rw [stPos, hc]
  simp only [List.length_take]
  congr 1
  omega

/-- The index of a letter, as an element of `Fin (K+1)`. -/
def fk (K i : ℕ) : Fin (K + 1) := if h : i < K + 1 then ⟨i, h⟩ else ⟨0, Nat.succ_pos K⟩

lemma fk_val {K i : ℕ} (h : i < K + 1) : (fk K i : ℕ) = i := by
  rw [fk, dif_pos h]

/-- The element attached to a step of the run and to an index. -/
noncomputable def mkElt (M : TwoWay A B Q) (w : List A) (eIdx : Q × Fin (K + 1) ≃ Fin m)
    (ti : ℕ × ℕ) : (Fin m × ℕ) ⊕ Fin m :=
  if (stPos M w ti.1).2 < w.length then
    Sum.inl (eIdx ((stPos M w ti.1).1, fk K ti.2), (stPos M w ti.1).2)
  else Sum.inr (eIdx ((stPos M w ti.1).1, fk K ti.2))

/-! ## Auxiliary formulas -/

/-- A formula that is always true. -/
def trueF (A : Type) : MSO A := MSO.le 0 0

/-- A formula that is always false. -/
def falseF (A : Type) : MSO A := MSO.not (MSO.le 0 0)

/-- The formula `x₀ = x₁`. -/
def eqF01 (A : Type) : MSO A := MSO.and (MSO.le 0 1) (MSO.le 1 0)

lemma sat_trueF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    MSO.Sat w fo so (trueF A) := le_refl _

lemma sat_falseF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    ¬ MSO.Sat w fo so (falseF A) := by
  intro h
  exact h (le_refl _)

lemma sat_eqF01 (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    MSO.Sat w fo so (eqF01 A) ↔ fo 0 = fo 1 := by
  show (fo 0 ≤ fo 1 ∧ fo 1 ≤ fo 0) ↔ _
  omega

/-! ## The transduction -/

open scoped Classical in
/-- The mso transduction attached to a two-way transducer, given the families of
formulas that describe its run. -/
noncomputable def runT (eIdx : Q × Fin (K + 1) ≃ Fin m)
    (upF ucF : Q × Fin (K + 1) → MSO A) (lpF lcF : Q × Fin (K + 1) → B → MSO A)
    (bppF bpcF bcpF bccF : Q × Fin (K + 1) → Q × Fin (K + 1) → MSO A) :
    MSOTransduction A B where
  copies := m
  extra := m
  univP := fun c => upF (eIdx.symm c)
  univC := fun d => ucF (eIdx.symm d)
  labP := fun c b => lpF (eIdx.symm c) b
  labC := fun d b => lcF (eIdx.symm d) b
  ordPP := fun c c' => MSO.or (bppF (eIdx.symm c) (eIdx.symm c'))
    (if (eIdx.symm c).1 = (eIdx.symm c').1 ∧ (eIdx.symm c).2 ≤ (eIdx.symm c').2
      then eqF01 A else falseF A)
  ordPC := fun c d => bpcF (eIdx.symm c) (eIdx.symm d)
  ordCP := fun d c => bcpF (eIdx.symm d) (eIdx.symm c)
  ordCC := fun d d' => MSO.or (bccF (eIdx.symm d) (eIdx.symm d'))
    (if (eIdx.symm d).1 = (eIdx.symm d').1 ∧ (eIdx.symm d).2 ≤ (eIdx.symm d').2
      then trueF A else falseF A)

section Spec

variable [Finite A] [Finite Q]
  (M : TwoWay A B Q) (w : List A) {Tm : ℕ} (hTm : cfgAt M w Tm = some Cfg.halt)
  (eIdx : Q × Fin (K + 1) ≃ Fin m)
  (upF ucF : Q × Fin (K + 1) → MSO A) (lpF lcF : Q × Fin (K + 1) → B → MSO A)
  (bppF bpcF bcpF bccF : Q × Fin (K + 1) → Q × Fin (K + 1) → MSO A)

/-- The specification of the formula families used by `runT`. -/
structure Forms : Prop where
  /-- The universe formulas for the copies of the positions. -/
  up : ∀ (qi : Q × Fin (K + 1)) (v : List A) (x : ℕ),
    MSO.Sat v (fun _ => x) (fun _ => ∅) (upF qi) ↔
      markAt2 v x x ∈ visitLang M ⟨qi.1, 0⟩ (qi.2 : ℕ)
  /-- The universe formulas for the extra elements. -/
  uc : ∀ (qi : Q × Fin (K + 1)) (v : List A) (x : ℕ),
    MSO.Sat v (fun _ => x) (fun _ => ∅) (ucF qi) ↔
      markAt2 v x x ∈ visitLang M ⟨qi.1, 2⟩ (qi.2 : ℕ)
  /-- The letter formulas for the copies of the positions. -/
  lp : ∀ (qi : Q × Fin (K + 1)) (b : B) (v : List A) (x : ℕ),
    MSO.Sat v (fun _ => x) (fun _ => ∅) (lpF qi b) ↔
      markAt2 v x x ∈ labLang M ⟨qi.1, 0⟩ (qi.2 : ℕ) b
  /-- The letter formulas for the extra elements. -/
  lc : ∀ (qi : Q × Fin (K + 1)) (b : B) (v : List A) (x : ℕ),
    MSO.Sat v (fun _ => x) (fun _ => ∅) (lcF qi b) ↔
      markAt2 v x x ∈ labLang M ⟨qi.1, 2⟩ (qi.2 : ℕ) b
  /-- The order formulas between two copies of positions. -/
  bpp : ∀ (qi qj : Q × Fin (K + 1)) (v : List A) (x y : ℕ),
    MSO.Sat v (fun i => if i = 0 then x else y) (fun _ => ∅) (bppF qi qj) ↔
      markAt2 v x y ∈ beforeLang M ⟨qi.1, 0⟩ ⟨qj.1, 1⟩
  /-- The order formulas from a copy of a position to an extra element. -/
  bpc : ∀ (qi qj : Q × Fin (K + 1)) (v : List A) (x : ℕ),
    MSO.Sat v (fun _ => x) (fun _ => ∅) (bpcF qi qj) ↔
      markAt2 v x x ∈ beforeLang M ⟨qi.1, 0⟩ ⟨qj.1, 2⟩
  /-- The order formulas from an extra element to a copy of a position. -/
  bcp : ∀ (qi qj : Q × Fin (K + 1)) (v : List A) (x : ℕ),
    MSO.Sat v (fun _ => x) (fun _ => ∅) (bcpF qi qj) ↔
      markAt2 v x x ∈ beforeLang M ⟨qi.1, 2⟩ ⟨qj.1, 0⟩
  /-- The order formulas between two extra elements. -/
  bcc : ∀ (qi qj : Q × Fin (K + 1)) (v : List A) (x : ℕ),
    MSO.Sat v (fun _ => x) (fun _ => ∅) (bccF qi qj) ↔
      markAt2 v x x ∈ beforeLang M ⟨qi.1, 2⟩ ⟨qj.1, 2⟩

variable {M w eIdx upF ucF lpF lcF bppF bpcF bcpF bccF}

include hTm

omit [Finite A] [Finite Q] in
/-- Two configurations of a halting run happen at the same time exactly when
they are the same configuration. -/
lemma time_eq_iff {q q' : Q} {p p' t t' : ℕ} (h : RunAt M w q p t) (h' : RunAt M w q' p' t') :
    t = t' ↔ (q = q' ∧ p = p') := by
  constructor
  · rintro rfl
    exact h.unique h'
  · rintro ⟨rfl, rfl⟩
    exact h.time_unique hTm h'

omit [Finite A] [Finite Q] in
/-- Selection: an element is selected exactly when the run produces the
corresponding letter. -/
lemma selected_iff (hF : Forms M upF ucF lpF lcF bppF bpcF bcpF bccF)
    (e : (Fin m × ℕ) ⊕ Fin m) :
    (runT eIdx upF ucF lpF lcF bppF bpcF bcpF bccF).selected w e ↔
      ∃ t, RunAt M w (eltSt eIdx e) (eltPos w e) t ∧
        eltIx eIdx e < (outAt M w t).length := by
  match e with
  | Sum.inl (c, p) =>
      show (p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (upF (eIdx.symm c))) ↔ _
      rw [hF.up (eIdx.symm c) w p, mem_visitLang M _ _ w hTm p p, tgPos_zero]
      show _ ↔ ∃ t, RunAt M w (eIdx.symm c).1 (if p < w.length then p else w.length + 1) t ∧
        ((eIdx.symm c).2 : ℕ) < (outAt M w t).length
      by_cases hp : p < w.length
      · rw [if_pos hp]
        constructor
        · rintro ⟨-, t, hrun, -, hi⟩
          exact ⟨t, hrun, hi⟩
        · rintro ⟨t, hrun, hi⟩
          exact ⟨hp, t, hrun, (tgOK_zero _ w p p).2 hp, hi⟩
      · rw [if_neg hp]
        constructor
        · rintro ⟨h, -⟩
          exact absurd h hp
        · rintro ⟨t, hrun, -⟩
          have := hrun.le_length
          omega
  | Sum.inr d =>
      show MSO.Sat w (fun _ => 0) (fun _ => ∅) (ucF (eIdx.symm d)) ↔ _
      rw [hF.uc (eIdx.symm d) w 0, mem_visitLang M _ _ w hTm 0 0, tgPos_two]
      show _ ↔ ∃ t, RunAt M w (eIdx.symm d).1 w.length t ∧
        ((eIdx.symm d).2 : ℕ) < (outAt M w t).length
      constructor
      · rintro ⟨t, hrun, -, hi⟩
        exact ⟨t, hrun, hi⟩
      · rintro ⟨t, hrun, hi⟩
        exact ⟨t, hrun, tgOK_two _ w 0 0, hi⟩

omit hTm [Finite A] [Finite Q] in
/-- A selected copy of a position really is a position. -/
lemma lt_of_selected {c : Fin m} {p : ℕ}
    (h : (runT eIdx upF ucF lpF lcF bppF bpcF bcpF bccF).selected w (Sum.inl (c, p))) :
    p < w.length := h.1

omit hTm [Finite A] in
lemma eltPos_inl_of_lt {c : Fin m} {p : ℕ} (hp : p < w.length) :
    eltPos (m := m) w (Sum.inl (c, p)) = p := by
  show (if p < w.length then p else w.length + 1) = p
  rw [if_pos hp]

omit [Finite A] [Finite Q] in
/-- **The specification of `runT`.** -/
theorem spec_runT (hKb : ∀ (l : Option A) (q : Q) (r : Option A), (outWord M l q r).length ≤ K)
    (hF : Forms M upF ucF lpF lcF bppF bpcF bcpF bccF) :
    RunElts.Spec M w (eltSt eIdx) (eltPos w) (eltIx eIdx) (mkElt M w eIdx)
      ((runT eIdx upF ucF lpF lcF bppF bpcF bcpF bccF).selected w)
      ((runT eIdx upF ucF lpF lcF bppF bpcF bcpF bccF).ordRel w)
      ((runT eIdx upF ucF lpF lcF bppF bpcF bcpF bccF).labRel w) := by
  classical
  set T := runT eIdx upF ucF lpF lcF bppF bpcF bcpF bccF with hT
  have hsel := selected_iff (w := w) (eIdx := eIdx) hTm hF
  refine ⟨hsel, ?_, ?_, ?_, ?_⟩
  · -- injectivity on the selected elements
    intro e e' he he' hst hpos hix
    match e, e' with
    | Sum.inl (c, p), Sum.inl (c', p') =>
        have hp : p < w.length := lt_of_selected he
        have hp' : p' < w.length := lt_of_selected he'
        rw [eltPos_inl_of_lt (m := m) (c := c) hp, eltPos_inl_of_lt (m := m) (c := c') hp'] at hpos
        subst hpos
        have : eIdx.symm c = eIdx.symm c' := by
          refine Prod.ext hst ?_
          exact Fin.ext hix
        have hcc : c = c' := by
          have := congrArg eIdx this
          simpa using this
        rw [hcc]
    | Sum.inl (c, p), Sum.inr d' =>
        have hp : p < w.length := lt_of_selected he
        rw [eltPos_inl_of_lt (m := m) (c := c) hp] at hpos
        replace hpos : p = w.length := hpos
        omega
    | Sum.inr d, Sum.inl (c', p') =>
        have hp' : p' < w.length := lt_of_selected he'
        rw [eltPos_inl_of_lt (m := m) (c := c') hp'] at hpos
        replace hpos : w.length = p' := hpos
        omega
    | Sum.inr d, Sum.inr d' =>
        have : eIdx.symm d = eIdx.symm d' := Prod.ext hst (Fin.ext hix)
        have hdd : d = d' := by
          have := congrArg eIdx this
          simpa using this
        rw [hdd]
  · -- the element attached to a step of the run
    intro t i q p hrun hi
    have hiK : i < K + 1 := by
      have hlen : (outAt M w t).length ≤ K := by
        rw [outAt_eq_outWord M w hTm hrun]
        exact hKb _ _ _
      omega
    have hsp : stPos M w t = (q, p) := stPos_eq M w hrun
    have hple : p ≤ w.length := hrun.le_length
    by_cases hp : p < w.length
    · have hmk : mkElt M w eIdx (t, i) = Sum.inl (eIdx (q, fk K i), p) := by
        rw [mkElt, hsp]
        simp only []
        rw [if_pos hp]
      rw [hmk]
      refine ⟨?_, ?_, ?_⟩
      · show (eIdx.symm (eIdx (q, fk K i))).1 = q
        simp
      · show (if p < w.length then p else w.length + 1) = p
        rw [if_pos hp]
      · show ((eIdx.symm (eIdx (q, fk K i))).2 : ℕ) = i
        simp [fk_val hiK]
    · have hpw : p = w.length := by omega
      have hmk : mkElt M w eIdx (t, i) = Sum.inr (eIdx (q, fk K i)) := by
        rw [mkElt, hsp]
        simp only []
        rw [if_neg hp]
      rw [hmk]
      refine ⟨?_, ?_, ?_⟩
      · show (eIdx.symm (eIdx (q, fk K i))).1 = q
        simp
      · show w.length = p
        omega
      · show ((eIdx.symm (eIdx (q, fk K i))).2 : ℕ) = i
        simp [fk_val hiK]
  · -- the order
    intro e e' he he' t t' hrun hrun'
    match e, e' with
    | Sum.inl (c, p), Sum.inl (c', p') =>
        have hp : p < w.length := lt_of_selected he
        have hp' : p' < w.length := lt_of_selected he'
        rw [eltPos_inl_of_lt (m := m) (c := c) hp] at hrun
        rw [eltPos_inl_of_lt (m := m) (c := c') hp'] at hrun'
        show (MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅)
            (MSO.or (bppF (eIdx.symm c) (eIdx.symm c'))
              (if (eIdx.symm c).1 = (eIdx.symm c').1 ∧ (eIdx.symm c).2 ≤ (eIdx.symm c').2
                then eqF01 A else falseF A))) ↔ _
        show (MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅)
            (bppF (eIdx.symm c) (eIdx.symm c')) ∨ _) ↔ _
        rw [hF.bpp (eIdx.symm c) (eIdx.symm c') w p p',
          mem_beforeLang M _ _ w hTm p p', tgPos_zero, tgPos_one]
        have hbefore :
            (TgOK (⟨(eIdx.symm c).1, 0⟩ : Tgt Q) w p p' ∧ ∃ t₁, RunAt M w (eIdx.symm c).1 p t₁ ∧
              ∀ t₂, TgOK (⟨(eIdx.symm c').1, 1⟩ : Tgt Q) w p p' →
                RunAt M w (eIdx.symm c').1 p' t₂ → t₁ < t₂) ↔ t < t' := by
          constructor
          · rintro ⟨-, t₁, hr₁, hlt⟩
            have : t₁ = t := hr₁.time_unique hTm hrun
            subst this
            exact hlt t' ((tgOK_one _ w p p').2 hp') hrun'
          · intro hlt
            refine ⟨(tgOK_zero _ w p p').2 hp, t, hrun, ?_⟩
            intro t₂ _ hr₂
            have : t₂ = t' := hr₂.time_unique hTm hrun'
            omega
        rw [hbefore]
        have htie : (MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅)
            (if (eIdx.symm c).1 = (eIdx.symm c').1 ∧ (eIdx.symm c).2 ≤ (eIdx.symm c').2
              then eqF01 A else falseF A)) ↔
            (t = t' ∧ eltIx eIdx (Sum.inl (c, p)) ≤ eltIx eIdx (Sum.inl (c', p'))) := by
          rw [time_eq_iff hTm hrun hrun']
          by_cases hc : (eIdx.symm c).1 = (eIdx.symm c').1 ∧ (eIdx.symm c).2 ≤ (eIdx.symm c').2
          · rw [if_pos hc, sat_eqF01]
            simp only [if_neg (by omega : ¬ (1 : ℕ) = 0)]
            constructor
            · intro hpp
              exact ⟨⟨hc.1, hpp⟩, hc.2⟩
            · rintro ⟨⟨-, hpp⟩, -⟩
              exact hpp
          · rw [if_neg hc]
            constructor
            · intro hcon
              exact absurd hcon (sat_falseF w _ _)
            · rintro ⟨⟨hq, hpp⟩, hix⟩
              exact absurd ⟨hq, Fin.le_def.2 hix⟩ hc
        rw [htie]
    | Sum.inl (c, p), Sum.inr d' =>
        have hp : p < w.length := lt_of_selected he
        rw [eltPos_inl_of_lt (m := m) (c := c) hp] at hrun
        show (MSO.Sat w (fun _ => p) (fun _ => ∅) (bpcF (eIdx.symm c) (eIdx.symm d'))) ↔ _
        rw [hF.bpc (eIdx.symm c) (eIdx.symm d') w p,
          mem_beforeLang M _ _ w hTm p p, tgPos_zero, tgPos_two]
        have hne : ¬ t = t' := by
          rw [time_eq_iff hTm hrun hrun']
          rintro ⟨-, hpp⟩
          replace hpp : p = w.length := hpp
          omega
        constructor
        · rintro ⟨-, t₁, hr₁, hlt⟩
          have : t₁ = t := hr₁.time_unique hTm hrun
          subst this
          exact Or.inl (hlt t' (tgOK_two _ w p p) hrun')
        · rintro (hlt | ⟨heq, -⟩)
          · refine ⟨(tgOK_zero _ w p p).2 hp, t, hrun, ?_⟩
            intro t₂ _ hr₂
            have : t₂ = t' := hr₂.time_unique hTm hrun'
            omega
          · exact absurd heq hne
    | Sum.inr d, Sum.inl (c', p') =>
        have hp' : p' < w.length := lt_of_selected he'
        rw [eltPos_inl_of_lt (m := m) (c := c') hp'] at hrun'
        show (MSO.Sat w (fun _ => p') (fun _ => ∅) (bcpF (eIdx.symm d) (eIdx.symm c'))) ↔ _
        rw [hF.bcp (eIdx.symm d) (eIdx.symm c') w p',
          mem_beforeLang M _ _ w hTm p' p', tgPos_two, tgPos_zero]
        have hne : ¬ t = t' := by
          rw [time_eq_iff hTm hrun hrun']
          rintro ⟨-, hpp⟩
          replace hpp : w.length = p' := hpp
          omega
        constructor
        · rintro ⟨-, t₁, hr₁, hlt⟩
          have : t₁ = t := hr₁.time_unique hTm hrun
          subst this
          exact Or.inl (hlt t' ((tgOK_zero _ w p' p').2 hp') hrun')
        · rintro (hlt | ⟨heq, -⟩)
          · refine ⟨tgOK_two _ w p' p', t, hrun, ?_⟩
            intro t₂ _ hr₂
            have : t₂ = t' := hr₂.time_unique hTm hrun'
            omega
          · exact absurd heq hne
    | Sum.inr d, Sum.inr d' =>
        show (MSO.Sat w (fun _ => 0) (fun _ => ∅)
            (MSO.or (bccF (eIdx.symm d) (eIdx.symm d'))
              (if (eIdx.symm d).1 = (eIdx.symm d').1 ∧ (eIdx.symm d).2 ≤ (eIdx.symm d').2
                then trueF A else falseF A))) ↔ _
        show (MSO.Sat w (fun _ => 0) (fun _ => ∅) (bccF (eIdx.symm d) (eIdx.symm d')) ∨ _) ↔ _
        rw [hF.bcc (eIdx.symm d) (eIdx.symm d') w 0,
          mem_beforeLang M _ _ w hTm 0 0, tgPos_two, tgPos_two]
        have hbefore :
            (TgOK (⟨(eIdx.symm d).1, 2⟩ : Tgt Q) w 0 0 ∧
              ∃ t₁, RunAt M w (eIdx.symm d).1 w.length t₁ ∧
                ∀ t₂, TgOK (⟨(eIdx.symm d').1, 2⟩ : Tgt Q) w 0 0 →
                  RunAt M w (eIdx.symm d').1 w.length t₂ → t₁ < t₂) ↔ t < t' := by
          constructor
          · rintro ⟨-, t₁, hr₁, hlt⟩
            have : t₁ = t := hr₁.time_unique hTm hrun
            subst this
            exact hlt t' (tgOK_two _ w 0 0) hrun'
          · intro hlt
            refine ⟨tgOK_two _ w 0 0, t, hrun, ?_⟩
            intro t₂ _ hr₂
            have : t₂ = t' := hr₂.time_unique hTm hrun'
            omega
        rw [hbefore]
        have htie : (MSO.Sat w (fun _ => 0) (fun _ => ∅)
            (if (eIdx.symm d).1 = (eIdx.symm d').1 ∧ (eIdx.symm d).2 ≤ (eIdx.symm d').2
              then trueF A else falseF A)) ↔
            (t = t' ∧ eltIx eIdx (Sum.inr d) ≤ eltIx eIdx (Sum.inr d')) := by
          rw [time_eq_iff hTm hrun hrun']
          by_cases hc : (eIdx.symm d).1 = (eIdx.symm d').1 ∧ (eIdx.symm d).2 ≤ (eIdx.symm d').2
          · rw [if_pos hc]
            constructor
            · intro _
              exact ⟨⟨hc.1, rfl⟩, hc.2⟩
            · intro _
              exact sat_trueF w _ _
          · rw [if_neg hc]
            constructor
            · intro hcon
              exact absurd hcon (sat_falseF w _ _)
            · rintro ⟨⟨hq, -⟩, hix⟩
              exact absurd ⟨hq, Fin.le_def.2 hix⟩ hc
        rw [htie]
  · -- the labels
    intro e b he t hrun
    match e with
    | Sum.inl (c, p) =>
        have hp : p < w.length := lt_of_selected he
        rw [eltPos_inl_of_lt (m := m) (c := c) hp] at hrun
        show (MSO.Sat w (fun _ => p) (fun _ => ∅) (lpF (eIdx.symm c) b)) ↔ _
        rw [hF.lp (eIdx.symm c) b w p, mem_labLang M _ _ b w hTm p p, tgPos_zero]
        constructor
        · rintro ⟨t₁, hr₁, -, hb⟩
          have : t₁ = t := hr₁.time_unique hTm hrun
          subst this
          exact hb
        · intro hb
          exact ⟨t, hrun, (tgOK_zero _ w p p).2 hp, hb⟩
    | Sum.inr d =>
        show (MSO.Sat w (fun _ => 0) (fun _ => ∅) (lcF (eIdx.symm d) b)) ↔ _
        rw [hF.lc (eIdx.symm d) b w 0, mem_labLang M _ _ b w hTm 0 0, tgPos_two]
        constructor
        · rintro ⟨t₁, hr₁, -, hb⟩
          have : t₁ = t := hr₁.time_unique hTm hrun
          subst this
          exact hb
        · intro hb
          exact ⟨t, hrun, tgOK_two _ w 0 0, hb⟩

end Spec

/-! ## The construction -/

variable [Finite A] [Finite Q]

/-- **The easy half of Theorem `thm:logic-regular-functions`.**  Every function computed by a
two-way transducer is defined by an mso transduction. -/
theorem isMSOTransduction_of_isTwoWay {f : List A → List B} (hf : IsTwoWay f) :
    IsMSOTransduction f := by
  classical
  obtain ⟨Q, hQ, M, hM⟩ := hf
  haveI := hQ
  haveI : Nonempty Q := ⟨M.init⟩
  -- a bound on the length of the string produced by one transition
  obtain ⟨z₀, hz₀⟩ := Finite.exists_max
    (fun z : Option A × Q × Option A => (outWord M z.1 z.2.1 z.2.2).length)
  set K := (outWord M z₀.1 z₀.2.1 z₀.2.2).length with hKdef
  have hKb : ∀ (l : Option A) (q : Q) (r : Option A), (outWord M l q r).length ≤ K :=
    fun l q r => hz₀ (l, q, r)
  -- the index set of the copies
  set m := Nat.card (Q × Fin (K + 1)) with hmdef
  set eIdx : Q × Fin (K + 1) ≃ Fin m := Finite.equivFin _ with heIdx
  -- the formulas
  choose upF hupF using fun qi : Q × Fin (K + 1) =>
    MarkLogic.exists_form_of_regular (visitLang M ⟨qi.1, 0⟩ (qi.2 : ℕ))
      (isRegular_visitLang M ⟨qi.1, 0⟩ _)
  choose ucF hucF using fun qi : Q × Fin (K + 1) =>
    MarkLogic.exists_form_of_regular (visitLang M ⟨qi.1, 2⟩ (qi.2 : ℕ))
      (isRegular_visitLang M ⟨qi.1, 2⟩ _)
  choose lpF hlpF using fun (qi : Q × Fin (K + 1)) (b : B) =>
    MarkLogic.exists_form_of_regular (labLang M ⟨qi.1, 0⟩ (qi.2 : ℕ) b)
      (isRegular_labLang M ⟨qi.1, 0⟩ _ b)
  choose lcF hlcF using fun (qi : Q × Fin (K + 1)) (b : B) =>
    MarkLogic.exists_form_of_regular (labLang M ⟨qi.1, 2⟩ (qi.2 : ℕ) b)
      (isRegular_labLang M ⟨qi.1, 2⟩ _ b)
  choose bppF hbppF using fun qi qj : Q × Fin (K + 1) =>
    MarkLogic2.exists_form2_of_regular (beforeLang M ⟨qi.1, 0⟩ ⟨qj.1, 1⟩)
      (isRegular_beforeLang M _ _)
  choose bpcF hbpcF using fun qi qj : Q × Fin (K + 1) =>
    MarkLogic.exists_form_of_regular (beforeLang M ⟨qi.1, 0⟩ ⟨qj.1, 2⟩)
      (isRegular_beforeLang M _ _)
  choose bcpF hbcpF using fun qi qj : Q × Fin (K + 1) =>
    MarkLogic.exists_form_of_regular (beforeLang M ⟨qi.1, 2⟩ ⟨qj.1, 0⟩)
      (isRegular_beforeLang M _ _)
  choose bccF hbccF using fun qi qj : Q × Fin (K + 1) =>
    MarkLogic.exists_form_of_regular (beforeLang M ⟨qi.1, 2⟩ ⟨qj.1, 2⟩)
      (isRegular_beforeLang M _ _)
  have hF : Forms M upF ucF lpF lcF bppF bpcF bcpF bccF :=
    ⟨fun qi v x => hupF qi v x, fun qi v x => hucF qi v x,
     fun qi b v x => hlpF qi b v x, fun qi b v x => hlcF qi b v x,
     fun qi qj v x y => hbppF qi qj v x y, fun qi qj v x => hbpcF qi qj v x,
     fun qi qj v x => hbcpF qi qj v x, fun qi qj v x => hbccF qi qj v x⟩
  refine ⟨runT eIdx upF ucF lpF lcF bppF bpcF bcpF bccF, ?_, ?_⟩
  · intro w
    obtain ⟨Tm, hTm, -⟩ := exists_halt_time M w (hM w)
    exact RunElts.proper_props (spec_runT hTm hKb hF)
  · intro w
    obtain ⟨Tm, hTm, hout⟩ := exists_halt_time M w (hM w)
    obtain ⟨es, h1, h2, h3, h4, h5⟩ := RunElts.exists_elts hTm (spec_runT hTm hKb hF)
    rw [hout] at h4 h5
    exact ⟨es, h1, h2, h3, h4, h5⟩

end TwoWayMSO

export TwoWayMSO (isMSOTransduction_of_isTwoWay)

end Lax314295Proofs.Transducers
