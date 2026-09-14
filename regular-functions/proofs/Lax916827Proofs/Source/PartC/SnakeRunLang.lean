/-
Regular languages that describe the run of a two-way transducer on its *whole*
input: the inputs on which the run halts, the inputs on which it reaches the
right end of the input in a given state, and the inputs on which it has width at
most `k`.

These are the questions that the checking automaton of the book's first stage in
the proof of the snake lemma (`RequestProject/PartC/SnakeStage1.lean`) asks about
the *window transducer* of a piece: a guessed piece is correct when the run of
its window transducer on the guessed window halts at the right end of the window
in the guessed state and has width at most `k - 1`, which is exactly what makes
`TwoWay.widthOut` of the window transducer compute the output of the piece.

All three languages are recognised by a deterministic two-way automaton that
simulates the run, so they are regular by Shepherdson's theorem, which is
available here through the probing automaton of
`RequestProject/PartC/RunProbe.lean`.  For the width the two-way automaton alone
does not suffice -- a visit counter would have to be attached to a column, which
a two-way automaton cannot remember -- so the column is *marked*, the visits to
a marked column are counted by the probing automaton (they happen in pairwise
distinct states, because the run of a halting deterministic transducer does not
repeat a configuration), and the mark is removed by the universal quantifier of
`RequestProject/PartC/SnakeForall.lean`.
-/
import Lax916827Proofs.Source.PartC.RunMark
import Lax916827Proofs.Source.PartC.SnakeWidth
import Lax916827Proofs.Source.PartC.SnakeForall
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SnakeRun

open TwoWay RunProbe

variable {A A' B Q : Type}

/-! ## Probing for the existence of a trigger -/

/-- The probing automaton whose answer is always `true` accepts exactly when the
trigger fires at some time of the run. -/
lemma accepts_probe_true (M : TwoWay A B Q) (π : A' → A)
    (Trig : Option A' → Q → Option A' → Bool) (u : List A') :
    (probeAut M π Trig (fun _ _ _ => true)).Accepts u ↔ ∃ t, TrigAt M π Trig u t := by
  classical
  rw [accepts_probeAut_iff]
  constructor
  · rintro ⟨t, ht, -, -⟩
    exact ⟨t, ht⟩
  · intro h
    refine ⟨Nat.find h, Nat.find_spec h, fun s hs => Nat.find_min h hs, ?_⟩
    obtain ⟨q, p, hrun, -⟩ := Nat.find_spec h
    exact ⟨q, p, hrun, rfl⟩

/-- The language of the inputs at which some trigger fires is regular. -/
lemma isRegular_trigLang [Finite A'] [Finite Q] (M : TwoWay A B Q) (π : A' → A)
    (Trig : Option A' → Q → Option A' → Bool) :
    Language.IsRegular {u : List A' | ∃ t, TrigAt M π Trig u t} := by
  refine RegAut.isRegular_of_eq (isRegular_probeLang M π Trig (fun _ _ _ => true)) ?_
  intro u
  exact (accepts_probe_true M π Trig u).symm

/-! ## The letters adjacent to the head -/

/-- The two letters adjacent to the head, in terms of the position. -/
lemma takeDrop_letters (w : List A) {p : ℕ} (hp : p ≤ w.length) :
    (w.take p).getLast? = leftLet w p ∧ (w.drop p).head? = w[p]? :=
  ⟨getLast?_take w hp, head?_drop w p⟩

/-! ## The inputs on which the run halts -/

/-- The trigger "the transition halts". -/
def haltTrig (M : TwoWay A B Q) : Option A → Q → Option A → Bool :=
  fun l q r => (M.step l q r).isLeft

/-- The language of the inputs on which the run of `M` halts. -/
def haltLang (M : TwoWay A B Q) : Language A := {w | ∃ T, cfgAt M w T = some Cfg.halt}

lemma trig_haltLang (M : TwoWay A B Q) (w : List A) :
    (∃ t, TrigAt M (id : A → A) (haltTrig M) w t) ↔ w ∈ haltLang M := by
  classical
  constructor
  · rintro ⟨t, q, p, hrun, hleft⟩
    rw [List.map_id] at hrun
    have hp : p ≤ w.length := hrun.le_length
    obtain ⟨o, ho⟩ : ∃ o, M.step (leftLet w p) q w[p]? = Sum.inl o := by
      rcases hs : M.step (leftLet w p) q w[p]? with o | x
      · exact ⟨o, rfl⟩
      · rw [haltTrig, hs] at hleft; simp at hleft
    have hstep : M.stepCfg (Cfg.conf (w.take p) q (w.drop p)) = some (o, Cfg.halt) := by
      refine stepCfg_halt_eq M ?_
      rw [getLast?_take w hp, head?_drop w p]
      exact ho
    exact ⟨t + 1, cfgAt_succ_of_step M w hrun.take_drop hstep⟩
  · rintro ⟨T, hT⟩
    have hex : ∃ T, cfgAt M w T = some Cfg.halt := ⟨T, hT⟩
    have hSspec : cfgAt M w (Nat.find hex) = some Cfg.halt := Nat.find_spec hex
    have hS0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, cfgAt_zero] at hSspec
      simp at hSspec
    obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := ⟨Nat.find hex - 1, by omega⟩
    rw [hs] at hSspec
    obtain ⟨c', hc', hstep⟩ := exists_pred M w hSspec
    rcases c' with ⟨x, q, y⟩ | -
    · have hxy : x ++ y = w := cfgAt_append M w s hc'
      have hlen : x.length ≤ w.length := by rw [← hxy]; simp
      have hleft : M.stepCfg (Cfg.conf x q y) = some (outAt M w s, Cfg.halt) := hstep
      obtain ⟨o, ho⟩ : ∃ o, M.step x.getLast? q y.head? = Sum.inl o := by
        rcases hs : M.step x.getLast? q y.head? with o | ⟨q', o, dir⟩
        · exact ⟨o, rfl⟩
        · exfalso
          rcases dir with _ | _
          · rcases hu : x.getLast? with _ | a
            · rw [stepCfg_left_none M hu hs] at hleft; simp at hleft
            · rw [stepCfg_left_some M hu hs] at hleft; simp at hleft
          · rcases hv : y with _ | ⟨a, y'⟩
            · subst hv; rw [stepCfg_right_nil M hs] at hleft; simp at hleft
            · subst hv; rw [stepCfg_right_cons M hs] at hleft; simp at hleft
      refine ⟨s, q, x.length, ?_, ?_⟩
      · rw [List.map_id]
        exact ⟨x, y, hc', rfl⟩
      · rw [haltTrig, ← getLast?_take w hlen, ← head?_drop w x.length]
        have h1 : w.take x.length = x := by rw [← hxy, List.take_left]
        have h2 : w.drop x.length = y := by rw [← hxy, List.drop_left]
        rw [h1, h2, ho]
        simp
    · rw [stepCfg] at hstep
      simp at hstep

/-- **The inputs on which the run halts form a regular language.** -/
theorem isRegular_haltLang [Finite A] [Finite Q] (M : TwoWay A B Q) :
    (haltLang M).IsRegular := by
  refine RegAut.isRegular_of_eq (isRegular_trigLang M (id : A → A) (haltTrig M)) ?_
  intro u
  exact (trig_haltLang M u).symm

/-! ## The inputs on which the run reaches the right end in a given state -/

/-- The trigger "the head is at the right end of the input, in the state `f`". -/
def endTrig [DecidableEq Q] (f : Q) : Option A → Q → Option A → Bool :=
  fun _ q r => decide (q = f) && r.isNone

/-- The language of the inputs on which the run of `M` reaches the right end of
the input in the state `f`. -/
def endLang (M : TwoWay A B Q) (f : Q) : Language A :=
  {w | ∃ T, cfgAt M w T = some (Cfg.conf w f [])}

lemma trig_endLang [DecidableEq Q] (M : TwoWay A B Q) (f : Q) (w : List A) :
    (∃ t, TrigAt M (id : A → A) (endTrig f) w t) ↔ w ∈ endLang M f := by
  classical
  constructor
  · rintro ⟨t, q, p, hrun, htrig⟩
    rw [List.map_id] at hrun
    rw [endTrig, Bool.and_eq_true, decide_eq_true_eq] at htrig
    obtain ⟨rfl, hnone⟩ := htrig
    have hp : p ≤ w.length := hrun.le_length
    have hpl : p = w.length := by
      by_contra hcon
      have hlt : p < w.length := by omega
      rw [List.getElem?_eq_getElem hlt] at hnone
      simp at hnone
    refine ⟨t, ?_⟩
    have := hrun.take_drop
    rw [hpl] at this
    simpa using this
  · rintro ⟨T, hT⟩
    refine ⟨T, f, w.length, ?_, ?_⟩
    · rw [List.map_id]
      exact ⟨w, [], by simpa using hT, rfl⟩
    · rw [endTrig, List.getElem?_eq_none (le_refl _)]
      simp

/-- **The inputs on which the run reaches the right end in a given state form a
regular language.** -/
theorem isRegular_endLang [Finite A] [Finite Q] (M : TwoWay A B Q) (f : Q) :
    (endLang M f).IsRegular := by
  classical
  refine RegAut.isRegular_of_eq (isRegular_trigLang M (id : A → A) (endTrig f)) ?_
  intro u
  exact (trig_endLang M f u).symm

/-! ## Finite conjunctions and disjunctions of regular languages -/

/-- A conjunction indexed by a finite type. -/
lemma isRegular_forall_fintype {Γ ι : Type} [Finite ι] (L : ι → Language Γ)
    (h : ∀ i, (L i).IsRegular) : Language.IsRegular {u : List Γ | ∀ i, u ∈ L i} := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine RegAut.isRegular_of_eq
    (RegAut.isRegular_forall_list L (Finset.univ.toList) (fun x _ => h x)) ?_
  exact fun u => ⟨fun hu x _ => hu x, fun hu x => hu x (Finset.mem_toList.2 (Finset.mem_univ x))⟩

/-- A disjunction of complements, indexed by a finite type. -/
lemma isRegular_exists_not {Γ ι : Type} [Finite ι] (L : ι → Language Γ)
    (h : ∀ i, (L i).IsRegular) : Language.IsRegular {u : List Γ | ∃ i, u ∉ L i} := by
  classical
  refine RegAut.isRegular_of_eq (RegAut.isRegular_not (isRegular_forall_fintype L h)) ?_
  intro u
  constructor
  · rintro ⟨i, hi⟩ hall
    exact hi (hall i)
  · intro hu
    by_contra hcon
    exact hu (fun i => not_not.1 (fun hni => hcon ⟨i, hni⟩))

/-- A language guarded by a proposition that does not depend on the string. -/
lemma isRegular_imp_const {Γ : Type} (P : Prop) {L : Language Γ} (h : L.IsRegular) :
    Language.IsRegular {u : List Γ | P → u ∈ L} := by
  classical
  by_cases hP : P
  · exact RegAut.isRegular_of_eq h (fun u => ⟨fun hu => hu hP, fun hu _ => hu⟩)
  · exact RegAut.isRegular_of_eq RegAut.isRegular_univ
      (fun u => ⟨fun _ => Set.mem_univ u, fun _ hc => absurd hc hP⟩)

/-! ## The width of a halting run -/

/-- The run visits the column `x` in the state `q`. -/
def VisitSt (M : TwoWay A B Q) (w : List A) (x : ℕ) (q : Q) : Prop := ∃ t, RunAt M w q x t

variable {M : TwoWay A B Q} {w : List A}

lemma posAt_of_runAt {q : Q} {x t : ℕ} (h : RunAt M w q x t) : posAt M w t = some x := by
  have hx : x ≤ w.length := h.le_length
  rw [posAt, h.take_drop]
  simp only [Option.bind_some, List.length_take]
  congr 1
  omega

lemma runAt_of_posAt {x t : ℕ} (h : posAt M w t = some x) :
    RunAt M w ((stateAt M w t).getD M.init) x t := by
  rcases hc : cfgAt M w t with _ | (⟨u, q, v⟩ | -)
  · rw [posAt, hc] at h; simp at h
  · rw [posAt, hc] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    have hst : stateAt M w t = some q := by rw [stateAt, hc]; rfl
    rw [hst]
    exact ⟨u, v, hc, h⟩
  · rw [posAt, hc] at h; simp at h

/-- **The width of a halting run, in terms of the states in which a column is
visited**: a column is visited at most `k` times if and only if there is no
injective family of `k + 1` states all of which occur at that column.  The two
formulations agree because a halting run never repeats a configuration. -/
lemma widthLe_iff_no_inj [Finite Q] {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) (k : ℕ) :
    WidthLe M w k ↔
      ∀ (x : ℕ) (g : Fin (k + 1) → Q), Function.Injective g → ∃ i, ¬ VisitSt M w x (g i) := by
  classical
  constructor
  · intro hwidth x g hg
    by_contra hcon
    push_neg at hcon
    choose t ht using hcon
    have htinj : Function.Injective t := by
      intro i j hij
      have h1 := ht i
      have h2 := ht j
      rw [hij] at h1
      exact hg (h1.unique h2).1
    have hcards : (Finset.image t Finset.univ).card = k + 1 := by
      rw [Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ s ∈ Finset.image t Finset.univ, posAt M w s = some x := by
      intro s hsmem
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hsmem
      exact posAt_of_runAt (ht i)
    have := hwidth x _ hmem
    omega
  · intro h x s hs
    by_contra hcard
    have hle : k + 1 ≤ s.card := by omega
    obtain ⟨s', hsub, hcard'⟩ := Finset.exists_subset_card_eq hle
    set e := s'.orderIsoOfFin hcard' with he
    set g : Fin (k + 1) → Q := fun i => (stateAt M w ((e i : ℕ))).getD M.init with hgdef
    have hrun : ∀ i, RunAt M w (g i) x ((e i : ℕ)) := by
      intro i
      exact runAt_of_posAt (hs _ (hsub (e i).2))
    have hginj : Function.Injective g := by
      intro i j hij
      have h1 := hrun i
      have h2 := hrun j
      rw [hij] at h1
      have : ((e i : ℕ)) = ((e j : ℕ)) := h1.time_unique hT h2
      have hee : e i = e j := Subtype.ext this
      exact e.injective hee
    obtain ⟨i, hi⟩ := h x g hginj
    exact hi ⟨_, hrun i⟩

/-- A visit to the column at the very right end of the input is a run that
reaches the right end. -/
lemma visitSt_length_iff (M : TwoWay A B Q) (w : List A) (q : Q) :
    VisitSt M w w.length q ↔ w ∈ endLang M q := by
  constructor
  · rintro ⟨t, hrun⟩
    refine ⟨t, ?_⟩
    have := hrun.take_drop
    simpa using this
  · rintro ⟨t, ht⟩
    exact ⟨t, w, [], by simpa using ht, rfl⟩

/-- A column beyond the right end of the input is never visited. -/
lemma not_visitSt_of_gt (M : TwoWay A B Q) (w : List A) {x : ℕ} (hx : w.length < x) (q : Q) :
    ¬ VisitSt M w x q := by
  rintro ⟨t, hrun⟩
  have := hrun.le_length
  omega

/-! ## The regular language of the inputs of bounded width -/

section WidthLang

open MarkStr RunMark

variable [Finite A] [Finite Q]

/-- The doubly marked strings in which the run visits the first mark in the
state `q`. -/
noncomputable def visitStLang (M : TwoWay A B Q) (q : Q) : Language (Mark2 A) :=
  probeLangT M ⟨q, 0⟩ (fun _ _ _ => true)

lemma isRegular_visitStLang (M : TwoWay A B Q) (q : Q) : (visitStLang M q).IsRegular :=
  isRegular_probeLangT _ _ _

omit [Finite A] [Finite Q] in
lemma mem_visitStLang (M : TwoWay A B Q) (q : Q) {w : List A} {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (x y : ℕ) :
    markAt2 w x y ∈ visitStLang M q ↔ (VisitSt M w x q ∧ x < w.length) := by
  rw [visitStLang, mem_probeLangT M ⟨q, 0⟩ _ w hT x y]
  have hpos : tgPos (⟨q, 0⟩ : Tgt Q) w x y = x := by simp [tgPos]
  have hok : TgOK (⟨q, 0⟩ : Tgt Q) w x y ↔ x < w.length := by simp [TgOK]
  constructor
  · rintro ⟨t, hrun, hok', -⟩
    rw [hpos] at hrun
    exact ⟨⟨t, hrun⟩, hok.1 hok'⟩
  · rintro ⟨⟨t, hrun⟩, hlt⟩
    exact ⟨t, by rw [hpos]; exact hrun, hok.2 hlt, rfl⟩

/-- The doubly marked strings in which the column of the first mark is visited
in at most `k` distinct states. -/
noncomputable def widthMarkLang (M : TwoWay A B Q) (k : ℕ) : Language (Mark2 A) :=
  {v | ∀ g : Fin (k + 1) → Q, Function.Injective g → ∃ i, v ∉ visitStLang M (g i)}

lemma isRegular_widthMarkLang (M : TwoWay A B Q) (k : ℕ) : (widthMarkLang M k).IsRegular := by
  classical
  refine isRegular_forall_fintype
    (fun g : Fin (k + 1) → Q =>
      ({v | Function.Injective g → ∃ i, v ∉ visitStLang M (g i)} : Language (Mark2 A)))
    (fun g => ?_)
  exact isRegular_imp_const _
    (isRegular_exists_not (fun i => visitStLang M (g i)) (fun i => isRegular_visitStLang M (g i)))

/-- The inputs whose right end is visited in at most `k` distinct states. -/
def widthEndLang (M : TwoWay A B Q) (k : ℕ) : Language A :=
  {w | ∀ g : Fin (k + 1) → Q, Function.Injective g → ∃ i, w ∉ endLang M (g i)}

lemma isRegular_widthEndLang (M : TwoWay A B Q) (k : ℕ) : (widthEndLang M k).IsRegular := by
  classical
  refine isRegular_forall_fintype
    (fun g : Fin (k + 1) → Q =>
      ({w | Function.Injective g → ∃ i, w ∉ endLang M (g i)} : Language A))
    (fun g => ?_)
  exact isRegular_imp_const _
    (isRegular_exists_not (fun i => endLang M (g i)) (fun i => isRegular_endLang M (g i)))

/-- **The inputs on which the run halts and has width at most `k` form a regular
language.** -/
theorem isRegular_haltWidthLang (M : TwoWay A B Q) (k : ℕ) :
    Language.IsRegular {w : List A | w ∈ haltLang M ∧ WidthLe M w k} := by
  classical
  have hreg := RegAut.isRegular_and (isRegular_haltLang M)
    (RegAut.isRegular_and (SnakeMSO.isRegular_forall1 (isRegular_widthMarkLang M k))
      (isRegular_widthEndLang M k))
  refine RegAut.isRegular_of_eq hreg ?_
  intro w
  constructor
  · rintro ⟨⟨T, hT⟩, hwidth⟩
    refine ⟨⟨T, hT⟩, ?_, ?_⟩
    · intro x hx g hg
      obtain ⟨i, hi⟩ := (widthLe_iff_no_inj hT k).1 hwidth x g hg
      exact ⟨i, fun hmem => hi ((mem_visitStLang M (g i) hT x x).1 hmem).1⟩
    · intro g hg
      obtain ⟨i, hi⟩ := (widthLe_iff_no_inj hT k).1 hwidth w.length g hg
      exact ⟨i, fun hmem => hi ((visitSt_length_iff M w (g i)).2 hmem)⟩
  · rintro ⟨⟨T, hT⟩, hmark, hend⟩
    refine ⟨⟨T, hT⟩, (widthLe_iff_no_inj hT k).2 ?_⟩
    intro x g hg
    rcases lt_trichotomy x w.length with hlt | heq | hgt
    · obtain ⟨i, hi⟩ := hmark x hlt g hg
      exact ⟨i, fun hvis => hi ((mem_visitStLang M (g i) hT x x).2 ⟨hvis, hlt⟩)⟩
    · subst heq
      obtain ⟨i, hi⟩ := hend g hg
      exact ⟨i, fun hvis => hi ((visitSt_length_iff M w (g i)).1 hvis)⟩
    · exact ⟨0, not_visitSt_of_gt M w hgt (g 0)⟩

end WidthLang

end SnakeRun

end Lax916827Proofs.Transducers
