/-
The regular languages of doubly marked strings that describe the run of a
two-way transducer.

Part of the proof of Theorem `thm:logic-regular-functions` of *Transducers* (M. Bojańczyk).  A
*target* is a state of the transducer together with the kind of position at which it is to be
observed: the first mark of the doubly marked input, its second mark, or the right end of the input.
For a target one can ask whether the run reaches it, which letter it produces there, and, for two
targets, which of the two is reached first.  All these questions are answered by the probing
automaton of `RequestProject/PartC/RunProbe.lean`, so the corresponding languages of doubly marked
strings are regular, and Theorem `thm:mso-logic-languages` turns them into mso formulas
(`RequestProject/PartC/MarkLogic.lean` and `RequestProject/PartC/MarkLogic2.lean`). -/
import Lax916827Proofs.Source.PartC.RunProbe
import Lax916827Proofs.Source.PartC.MarkStr
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers
namespace RunMark

open TwoWay MarkStr RunProbe

variable {A B Q : Type}

open scoped Classical

/-! ## The output of a single transition -/

/-- The string produced by one transition of the transducer. -/
def outWord (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) : List B :=
  match M.step l q r with
  | Sum.inl o => o
  | Sum.inr (_, o, _) => o

lemma stepCfg_out (M : TwoWay A B Q) {x y : List A} {q : Q} {o : List B} {c : Cfg A Q}
    (h : M.stepCfg (Cfg.conf x q y) = some (o, c)) :
    o = outWord M x.getLast? q y.head? := by
  rw [outWord]
  rcases hs : M.step x.getLast? q y.head? with o' | ⟨q', o', dir⟩
  · rw [stepCfg_halt_eq M hs] at h
    simpa using (congrArg Prod.fst (Option.some.inj h)).symm
  · rcases dir with _ | _
    · rcases hu : x.getLast? with _ | a
      · rw [stepCfg_left_none M hu hs] at h; simp at h
      · rw [stepCfg_left_some M hu hs] at h
        simpa using (congrArg Prod.fst (Option.some.inj h)).symm
    · rcases hv : y with _ | ⟨a, y'⟩
      · subst hv
        rw [stepCfg_right_nil M hs] at h; simp at h
      · subst hv
        rw [stepCfg_right_cons M hs] at h
        simpa using (congrArg Prod.fst (Option.some.inj h)).symm

/-- The output produced at a time of the run, in terms of the state and the
position. -/
lemma outAt_eq_outWord (M : TwoWay A B Q) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) {q : Q} {p t : ℕ} (h : RunAt M w q p t) :
    outAt M w t = outWord M (leftLet w p) q w[p]? := by
  have hp : p ≤ w.length := h.le_length
  have hcfg := h.take_drop
  -- the run is still alive at time `t`
  have htT : t < T := by
    rcases Nat.lt_or_ge t T with h' | h'
    · exact h'
    · exfalso
      rcases Nat.eq_or_lt_of_le h' with rfl | hlt
      · rw [hT] at hcfg; simp at hcfg
      · have : cfgAt M w t = none :=
          cfgAt_none_mono M w (by omega) (cfgAt_halt_succ M w hT)
        rw [this] at hcfg; simp at hcfg
  have halive : (cfgAt M w (t + 1)).isSome :=
    cfgAt_isSome_of_le M w (show t + 1 ≤ T by omega) (by rw [hT]; simp)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 halive
  obtain ⟨c', hc', hs⟩ := exists_pred M w hc
  rw [hcfg] at hc'
  obtain rfl : c' = Cfg.conf (w.take p) q (w.drop p) := (Option.some.inj hc').symm
  have := stepCfg_out M hs
  rw [this, getLast?_take w hp, List.head?_drop]

/-! ## Targets -/

/-- A target configuration of the run, as seen by the probing automaton: a state
together with the kind of position at which it is observed -- the first mark
(`0`), the second mark (`1`), or the right end of the input (`2`). -/
structure Tgt (Q : Type) where
  /-- The state of the target configuration. -/
  st : Q
  /-- The kind of position of the target configuration. -/
  kind : Fin 3

/-- Whether the letter to the right of the head carries the mark of the given
kind (for the kind `2`: whether the head is at the right end). -/
def markOf (k : Fin 3) (r : Option (Mark2 A)) : Bool :=
  match r with
  | none => decide (k = 2)
  | some z => if k = 0 then z.2.1 else if k = 1 then z.2.2 else false

open scoped Classical in
/-- The trigger of a target: the state matches and the position is of the right
kind. -/
noncomputable def hitsB (tg : Tgt Q) : Option (Mark2 A) → Q → Option (Mark2 A) → Bool :=
  fun _ q r => decide (q = tg.st) && markOf tg.kind r

/-- The position of a target in a doubly marked string. -/
def tgPos (tg : Tgt Q) (w : List A) (x y : ℕ) : ℕ :=
  if tg.kind = 0 then x else if tg.kind = 1 then y else w.length

/-- The position of a target exists. -/
def TgOK (tg : Tgt Q) (w : List A) (x y : ℕ) : Prop :=
  if tg.kind = 0 then x < w.length else if tg.kind = 1 then y < w.length else True

lemma hitsB_iff (tg : Tgt Q) (w : List A) (x y p : ℕ) (q : Q) (hp : p ≤ w.length) :
    hitsB tg (leftLet (markAt2 w x y) p) q (markAt2 w x y)[p]? = true ↔
      (q = tg.st ∧ p = tgPos tg w x y ∧ TgOK tg w x y) := by
  have hget : (markAt2 w x y)[p]? = (w[p]?).map (fun a => (a, decide (p = x), decide (p = y))) :=
    markAt2_getElem? w x y p
  rw [hitsB, Bool.and_eq_true, decide_eq_true_eq, hget]
  refine and_congr_right' ?_
  obtain ⟨s, k⟩ := tg
  simp only [tgPos, TgOK]
  rcases Nat.lt_or_ge p w.length with hlt | hge
  · obtain ⟨a, ha⟩ : ∃ a, w[p]? = some a := ⟨w[p], List.getElem?_eq_getElem hlt⟩
    rw [ha]
    fin_cases k <;> simp [markOf] <;> omega
  · have hpw : p = w.length := by omega
    subst hpw
    rw [List.getElem?_eq_none (le_refl _)]
    fin_cases k <;> simp [markOf] <;> omega

lemma trigAt_hitsB (M : TwoWay A B Q) (tg : Tgt Q) (w : List A) (x y t : ℕ) :
    TrigAt M Prod.fst (hitsB tg) (markAt2 w x y) t ↔
      (RunAt M w tg.st (tgPos tg w x y) t ∧ TgOK tg w x y) := by
  have hmap : (markAt2 w x y).map Prod.fst = w := map_fst_markAt2 w x y
  constructor
  · rintro ⟨q, p, hrun, hhit⟩
    rw [hmap] at hrun
    rw [hitsB_iff tg w x y p q hrun.le_length] at hhit
    obtain ⟨rfl, rfl, hok⟩ := hhit
    exact ⟨hrun, hok⟩
  · rintro ⟨hrun, hok⟩
    refine ⟨tg.st, tgPos tg w x y, by rwa [hmap], ?_⟩
    rw [hitsB_iff tg w x y _ _ hrun.le_length]
    exact ⟨rfl, rfl, hok⟩

lemma ansAt_iff (M : TwoWay A B Q) (ans : Option (Mark2 A) → Q → Option (Mark2 A) → Bool)
    (w : List A) (x y t : ℕ) {q : Q} {p : ℕ} (hrun : RunAt M w q p t) :
    AnsAt M Prod.fst ans (markAt2 w x y) t ↔
      ans (leftLet (markAt2 w x y) p) q (markAt2 w x y)[p]? = true := by
  have hmap : (markAt2 w x y).map Prod.fst = w := map_fst_markAt2 w x y
  constructor
  · rintro ⟨q', p', hrun', hans⟩
    rw [hmap] at hrun'
    obtain ⟨rfl, rfl⟩ := hrun'.unique hrun
    exact hans
  · intro hans
    exact ⟨q, p, by rwa [hmap], hans⟩

/-! ## The languages -/

variable [Finite A] [Finite Q]

/-- The language of doubly marked strings in which the run reaches the target
and the answer holds there. -/
def probeLangT (M : TwoWay A B Q) (tg : Tgt Q)
    (ans : Option (Mark2 A) → Q → Option (Mark2 A) → Bool) : Language (Mark2 A) :=
  {u | (probeAut M Prod.fst (hitsB tg) ans).Accepts u}

lemma isRegular_probeLangT (M : TwoWay A B Q) (tg : Tgt Q)
    (ans : Option (Mark2 A) → Q → Option (Mark2 A) → Bool) :
    (probeLangT M tg ans).IsRegular :=
  RunProbe.isRegular_probeLang M Prod.fst (hitsB tg) ans

omit [Finite A] [Finite Q] in
/-- The characterisation of the language of a single target: since the run
halts, it reaches a given configuration at most once, so the first trigger is
the only one. -/
lemma mem_probeLangT (M : TwoWay A B Q) (tg : Tgt Q)
    (ans : Option (Mark2 A) → Q → Option (Mark2 A) → Bool) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (x y : ℕ) :
    markAt2 w x y ∈ probeLangT M tg ans ↔
      ∃ t, RunAt M w tg.st (tgPos tg w x y) t ∧ TgOK tg w x y ∧
        ans (leftLet (markAt2 w x y) (tgPos tg w x y)) tg.st
          (markAt2 w x y)[tgPos tg w x y]? = true := by
  change (probeAut M Prod.fst (hitsB tg) ans).Accepts (markAt2 w x y) ↔ _
  rw [RunProbe.accepts_probeAut_iff]
  constructor
  · rintro ⟨t, htrig, -, hans⟩
    rw [trigAt_hitsB] at htrig
    obtain ⟨hrun, hok⟩ := htrig
    rw [ansAt_iff M ans w x y t hrun] at hans
    exact ⟨t, hrun, hok, hans⟩
  · rintro ⟨t, hrun, hok, hans⟩
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [trigAt_hitsB]; exact ⟨hrun, hok⟩
    · intro s hs hts
      rw [trigAt_hitsB] at hts
      exact absurd (hrun.time_unique hT hts.1) (by omega)
    · rw [ansAt_iff M ans w x y t hrun]
      exact hans

/-! ### Visiting a target, and the letter produced there -/

open scoped Classical in
/-- The answer "the string produced by the transition has more than `i`
letters". -/
noncomputable def ansLen (M : TwoWay A B Q) (i : ℕ) :
    Option (Mark2 A) → Q → Option (Mark2 A) → Bool :=
  fun l q r => decide (i < (outWord M (l.map Prod.fst) q (r.map Prod.fst)).length)

open scoped Classical in
/-- The answer "the `i`-th letter produced by the transition is `b`". -/
noncomputable def ansLab (M : TwoWay A B Q) (i : ℕ) (b : B) :
    Option (Mark2 A) → Q → Option (Mark2 A) → Bool :=
  fun l q r => decide ((outWord M (l.map Prod.fst) q (r.map Prod.fst))[i]? = some b)

omit [Finite A] [Finite Q] in
lemma outWord_at_target (M : TwoWay A B Q) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (x y : ℕ) {q : Q} {p t : ℕ}
    (hrun : RunAt M w q p t) :
    outWord M ((leftLet (markAt2 w x y) p).map Prod.fst) q
      (((markAt2 w x y)[p]?).map Prod.fst) = outAt M w t := by
  have hmap : (markAt2 w x y).map Prod.fst = w := map_fst_markAt2 w x y
  rw [map_leftLet, hmap, ← List.getElem?_map, hmap]
  exact (outAt_eq_outWord M w hT hrun).symm

open scoped Classical in
/-- The language of a target with the answer "more than `i` letters are
produced". -/
noncomputable def visitLang (M : TwoWay A B Q) (tg : Tgt Q) (i : ℕ) : Language (Mark2 A) :=
  probeLangT M tg (ansLen M i)

open scoped Classical in
/-- The language of a target with the answer "the `i`-th letter produced is
`b`". -/
noncomputable def labLang (M : TwoWay A B Q) (tg : Tgt Q) (i : ℕ) (b : B) : Language (Mark2 A) :=
  probeLangT M tg (ansLab M i b)

lemma isRegular_visitLang (M : TwoWay A B Q) (tg : Tgt Q) (i : ℕ) :
    (visitLang M tg i).IsRegular := isRegular_probeLangT _ _ _

lemma isRegular_labLang (M : TwoWay A B Q) (tg : Tgt Q) (i : ℕ) (b : B) :
    (labLang M tg i b).IsRegular := isRegular_probeLangT _ _ _

omit [Finite A] [Finite Q] in
lemma mem_visitLang (M : TwoWay A B Q) (tg : Tgt Q) (i : ℕ) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (x y : ℕ) :
    markAt2 w x y ∈ visitLang M tg i ↔
      ∃ t, RunAt M w tg.st (tgPos tg w x y) t ∧ TgOK tg w x y ∧
        i < (outAt M w t).length := by
  rw [visitLang, mem_probeLangT M tg _ w hT x y]
  refine exists_congr (fun t => and_congr_right (fun hrun => and_congr_right (fun _ => ?_)))
  rw [ansLen, decide_eq_true_eq, outWord_at_target M w hT x y hrun]

omit [Finite A] [Finite Q] in
lemma mem_labLang (M : TwoWay A B Q) (tg : Tgt Q) (i : ℕ) (b : B) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (x y : ℕ) :
    markAt2 w x y ∈ labLang M tg i b ↔
      ∃ t, RunAt M w tg.st (tgPos tg w x y) t ∧ TgOK tg w x y ∧
        (outAt M w t)[i]? = some b := by
  rw [labLang, mem_probeLangT M tg _ w hT x y]
  refine exists_congr (fun t => and_congr_right (fun hrun => and_congr_right (fun _ => ?_)))
  rw [ansLab, decide_eq_true_eq, outWord_at_target M w hT x y hrun]

/-! ### Comparing the times of two targets -/

/-- The language of doubly marked strings in which the run reaches the first
target strictly before the second one. -/
def beforeLang (M : TwoWay A B Q) (tg₁ tg₂ : Tgt Q) : Language (Mark2 A) :=
  {u | (probeAut M Prod.fst (fun l q r => hitsB tg₁ l q r || hitsB tg₂ l q r)
      (fun l q r => hitsB tg₁ l q r && !hitsB tg₂ l q r)).Accepts u}

lemma isRegular_beforeLang (M : TwoWay A B Q) (tg₁ tg₂ : Tgt Q) :
    (beforeLang M tg₁ tg₂).IsRegular :=
  RunProbe.isRegular_probeLang _ _ _ _

omit [Finite A] [Finite Q] in
lemma mem_beforeLang (M : TwoWay A B Q) (tg₁ tg₂ : Tgt Q) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (x y : ℕ) :
    markAt2 w x y ∈ beforeLang M tg₁ tg₂ ↔
      (TgOK tg₁ w x y ∧ ∃ t₁, RunAt M w tg₁.st (tgPos tg₁ w x y) t₁ ∧
        ∀ t₂, TgOK tg₂ w x y → RunAt M w tg₂.st (tgPos tg₂ w x y) t₂ → t₁ < t₂) := by
  classical
  set h₁ : ℕ → Prop := fun t => RunAt M w tg₁.st (tgPos tg₁ w x y) t ∧ TgOK tg₁ w x y with hh₁
  set h₂ : ℕ → Prop := fun t => RunAt M w tg₂.st (tgPos tg₂ w x y) t ∧ TgOK tg₂ w x y with hh₂
  have hmap : (markAt2 w x y).map Prod.fst = w := map_fst_markAt2 w x y
  -- the trigger and the answer, in terms of `h₁` and `h₂`
  have htrig : ∀ t, TrigAt M Prod.fst
      (fun l q r => hitsB tg₁ l q r || hitsB tg₂ l q r) (markAt2 w x y) t ↔ (h₁ t ∨ h₂ t) := by
    intro t
    constructor
    · rintro ⟨q, p, hrun, hor⟩
      rw [hmap] at hrun
      rw [Bool.or_eq_true, hitsB_iff tg₁ w x y p q hrun.le_length,
        hitsB_iff tg₂ w x y p q hrun.le_length] at hor
      rcases hor with ⟨rfl, rfl, hok⟩ | ⟨rfl, rfl, hok⟩
      · exact Or.inl ⟨hrun, hok⟩
      · exact Or.inr ⟨hrun, hok⟩
    · rintro (⟨hrun, hok⟩ | ⟨hrun, hok⟩)
      · refine ⟨tg₁.st, tgPos tg₁ w x y, by rwa [hmap], ?_⟩
        rw [Bool.or_eq_true]
        exact Or.inl ((hitsB_iff tg₁ w x y _ _ hrun.le_length).2 ⟨rfl, rfl, hok⟩)
      · refine ⟨tg₂.st, tgPos tg₂ w x y, by rwa [hmap], ?_⟩
        rw [Bool.or_eq_true]
        exact Or.inr ((hitsB_iff tg₂ w x y _ _ hrun.le_length).2 ⟨rfl, rfl, hok⟩)
  have hans : ∀ t, AnsAt M Prod.fst
      (fun l q r => hitsB tg₁ l q r && !hitsB tg₂ l q r) (markAt2 w x y) t ↔ (h₁ t ∧ ¬ h₂ t) := by
    intro t
    constructor
    · rintro ⟨q, p, hrun, hand⟩
      rw [hmap] at hrun
      rw [Bool.and_eq_true, Bool.not_eq_true', hitsB_iff tg₁ w x y p q hrun.le_length] at hand
      obtain ⟨⟨rfl, rfl, hok⟩, hne⟩ := hand
      refine ⟨⟨hrun, hok⟩, ?_⟩
      rintro ⟨hrun₂, hok₂⟩
      obtain ⟨hst, hpos⟩ := hrun.unique hrun₂
      rw [(hitsB_iff tg₂ w x y _ _ hrun.le_length).2 ⟨hst, hpos, hok₂⟩] at hne
      simp at hne
    · rintro ⟨⟨hrun, hok⟩, hn₂⟩
      refine ⟨tg₁.st, tgPos tg₁ w x y, by rwa [hmap], ?_⟩
      rw [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨(hitsB_iff tg₁ w x y _ _ hrun.le_length).2 ⟨rfl, rfl, hok⟩, ?_⟩
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      rw [hitsB_iff tg₂ w x y _ _ hrun.le_length] at hcon
      obtain ⟨hst, hpos, hok₂⟩ := hcon
      exact hn₂ ⟨by rw [← hst, ← hpos]; exact hrun, hok₂⟩
  -- uniqueness of the times
  have huniq₁ : ∀ s t, h₁ s → h₁ t → s = t := fun s t hs ht => hs.1.time_unique hT ht.1
  have huniq₂ : ∀ s t, h₂ s → h₂ t → s = t := fun s t hs ht => hs.1.time_unique hT ht.1
  change (probeAut M Prod.fst _ _).Accepts (markAt2 w x y) ↔ _
  rw [RunProbe.accepts_probeAut_iff]
  constructor
  · rintro ⟨t, -, hmin, hansv⟩
    rw [hans] at hansv
    obtain ⟨⟨hrun, hok⟩, hn₂⟩ := hansv
    refine ⟨hok, t, hrun, ?_⟩
    intro t₂ hok₂ hrun₂
    rcases Nat.lt_trichotomy t t₂ with h | rfl | h
    · exact h
    · exact absurd ⟨hrun₂, hok₂⟩ hn₂
    · exact absurd ((htrig t₂).2 (Or.inr ⟨hrun₂, hok₂⟩)) (hmin t₂ h)
  · rintro ⟨hok, t₁, hrun, hlater⟩
    refine ⟨t₁, (htrig t₁).2 (Or.inl ⟨hrun, hok⟩), ?_, (hans t₁).2 ⟨⟨hrun, hok⟩, ?_⟩⟩
    · intro s hs hts
      rcases (htrig s).1 hts with h | h
      · exact absurd (huniq₁ s t₁ h ⟨hrun, hok⟩) (by omega)
      · exact absurd (hlater s h.2 h.1) (by omega)
    · rintro ⟨hrun₂, hok₂⟩
      exact absurd (hlater t₁ hok₂ hrun₂) (by omega)

end RunMark
end Lax916827Proofs.Transducers
