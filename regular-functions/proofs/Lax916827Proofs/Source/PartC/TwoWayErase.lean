/-
Pre-composition of two-way transducers with an *erasing* homomorphism, i.e. one
that maps every letter either to a single letter or to the empty word (part of
the proof of Corollary `cor:2dfa-closure-under-composition` of *Transducers*, M. Bojańczyk).  Such a
homomorphism is the same thing as `List.filterMap e` for a partial map
`e : A → Option B` on the letters.

The difficulty is that several positions of the input correspond to the same
position of its image, namely the positions inside a block of erased letters.
The simulating transducer keeps its head at the *canonical* such position: the
one immediately to the left of the next non-erased letter (or at the very end of
the input).  The letter of the image to the right of the head is then visible,
but the letter to the left is not, so it has to be found by a scan to the left
(mode `scanL`), after which the head has to come back (modes `phase1`, which
crosses the erased letters and the first non-erased one, and `phase2`, which
skips the erased letters that follow).
-/
import Lax916827Proofs.Source.PartC.TwoWayBlock
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Erased and settled words -/

section Words

variable {A B : Type} (e : A → Option B)

/-- All letters of the word are erased. -/
def ErasedList (l : List A) : Prop := ∀ c ∈ l, e c = none

/-- The word does not end with an erased letter. -/
def SettledL (u : List A) : Prop := ∀ c ∈ u.getLast?, e c ≠ none

/-- The word does not begin with an erased letter. -/
def SettledR (v : List A) : Prop := ∀ c ∈ v.head?, e c ≠ none

variable {e}

@[simp] lemma erasedList_nil : ErasedList e ([] : List A) := by simp [ErasedList]

@[simp] lemma settledL_nil : SettledL e ([] : List A) := by simp [SettledL]

@[simp] lemma settledR_nil : SettledR e ([] : List A) := by simp [SettledR]

lemma erasedList_cons {c : A} {l : List A} (h : ErasedList e (c :: l)) :
    e c = none ∧ ErasedList e l :=
  ⟨h c (by simp), fun x hx => h x (by simp [hx])⟩

lemma erasedList_append {l₁ l₂ : List A} (h : ErasedList e (l₁ ++ l₂)) :
    ErasedList e l₁ ∧ ErasedList e l₂ :=
  ⟨fun x hx => h x (by simp [hx]), fun x hx => h x (by simp [hx])⟩

lemma filterMap_erasedList {l : List A} (h : ErasedList e l) : l.filterMap e = [] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      obtain ⟨hc, hl⟩ := erasedList_cons h
      simp [hc, ih hl]

lemma getLast?_filterMap_settled {u : List A} (hu : SettledL e u) :
    (u.filterMap e).getLast? = u.getLast?.bind e := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u' z _ =>
      have hz : e z ≠ none := hu z (by simp)
      rcases hez : e z with _ | b
      · exact absurd hez hz
      · simp [hez]

lemma head?_filterMap_settled {v : List A} (hv : SettledR e v) :
    (v.filterMap e).head? = v.head?.bind e := by
  cases v with
  | nil => simp
  | cons c v' =>
      have hc : e c ≠ none := hv c (by simp)
      rcases hec : e c with _ | b
      · exact absurd hec hc
      · simp [hec]

/-- Every word splits into a settled prefix and a block of erased letters. -/
lemma exists_split_left (u : List A) :
    ∃ u₁ mid, u = u₁ ++ mid ∧ ErasedList e mid ∧ SettledL e u₁ := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨[], [], by simp, by simp, by simp⟩
  | append_singleton u' z ih =>
      rcases hez : e z with _ | b
      · obtain ⟨u₁, mid, rfl, hmid, hset⟩ := ih
        refine ⟨u₁, mid ++ [z], by simp, ?_, hset⟩
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hmid x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hez
      · exact ⟨u' ++ [z], [], by simp, by simp, by simp [SettledL, hez]⟩

/-- Every word splits into a block of erased letters and a settled suffix. -/
lemma exists_split_right (v : List A) :
    ∃ mid v', v = mid ++ v' ∧ ErasedList e mid ∧ SettledR e v' := by
  induction v with
  | nil => exact ⟨[], [], by simp, by simp, by simp⟩
  | cons c v ih =>
      rcases hec : e c with _ | b
      · obtain ⟨mid, v', rfl, hmid, hset⟩ := ih
        refine ⟨c :: mid, v', by simp, ?_, hset⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hec
        · exact hmid x hx
      · exact ⟨[], c :: v, by simp, by simp, by simp [SettledR, hec]⟩

end Words

/-! ## The simulating transducer -/

section Erase

variable {A B C P : Type}

/-- The mode of the simulating transducer: scanning to the left for the letter
of the image to the left of the head (`scanL`), coming back to the right and
still having to cross one non-erased letter (`phase1`), or skipping the erased
letters to the right of the head (`phase2`, which is also the mode in which the
head sits at a canonical position). -/
inductive EMode
  | scanL
  | phase1
  | phase2
  deriving DecidableEq, Fintype

variable (N : TwoWay B C P) (e : A → Option B)

/-- The transition that performs a step of `N`.  The head sits just to the right
of the letter `lb` that produces the letter of the image to the left of the head
of `N`, and `r` is the letter that produces the letter of the image to the right
of the head of `N`.  The mode `mR` is used when the head moves to the right. -/
def eraseAct (mR : EMode) (lb r : Option A) (p : P) :
    List C ⊕ ((P × Option A × EMode) × List C × Bool) :=
  match N.step (lb.bind e) p (r.bind e) with
  | Sum.inl o => Sum.inl o
  | Sum.inr (p', o, true) => Sum.inr ((p', r, mR), o, true)
  | Sum.inr (p', o, false) => Sum.inr ((p', r, EMode.phase2), o, false)

/-- The transition at a position whose right neighbourhood is settled: either
the letter to the left is erased, and the head moves left to look for a
non-erased one, or a step of `N` is performed. -/
def eraseSettled (mR : EMode) (la r : Option A) (p : P) :
    List C ⊕ ((P × Option A × EMode) × List C × Bool) :=
  match la with
  | none => eraseAct N e mR none r p
  | some c =>
      match e c with
      | none => Sum.inr ((p, r, EMode.scanL), [], false)
      | some _ => eraseAct N e mR (some c) r p

/-- The transducer simulating `N` on the image of the input. -/
def eraseAut : TwoWay A C (P × Option A × EMode) where
  init := (N.init, none, EMode.phase2)
  step := fun la s rb =>
    match s with
    | (p, r, EMode.scanL) => eraseSettled N e EMode.phase1 la r p
    | (p, r, EMode.phase1) =>
        match rb with
        | none => Sum.inl []
        | some c =>
            match e c with
            | none => Sum.inr ((p, r, EMode.phase1), [], true)
            | some _ => Sum.inr ((p, r, EMode.phase2), [], true)
    | (p, r, EMode.phase2) =>
        match rb with
        | none => eraseSettled N e EMode.phase2 la none p
        | some c =>
            match e c with
            | none => Sum.inr ((p, r, EMode.phase2), [], true)
            | some _ => eraseSettled N e EMode.phase2 la (some c) p

variable {N e}

lemma eraseAut_scanL (la r : Option A) (p : P) (rb : Option A) :
    (eraseAut N e).step la (p, r, EMode.scanL) rb = eraseSettled N e EMode.phase1 la r p := rfl

lemma eraseAut_phase1_erased {c : A} (h : e c = none) (la r : Option A) (p : P) :
    (eraseAut N e).step la (p, r, EMode.phase1) (some c) =
      Sum.inr ((p, r, EMode.phase1), [], true) := by
  simp [eraseAut, h]

lemma eraseAut_phase1_keep {c : A} {b : B} (h : e c = some b) (la r : Option A) (p : P) :
    (eraseAut N e).step la (p, r, EMode.phase1) (some c) =
      Sum.inr ((p, r, EMode.phase2), [], true) := by
  simp [eraseAut, h]

lemma eraseAut_phase2_erased {c : A} (h : e c = none) (la r : Option A) (p : P) :
    (eraseAut N e).step la (p, r, EMode.phase2) (some c) =
      Sum.inr ((p, r, EMode.phase2), [], true) := by
  simp [eraseAut, h]

/-- At a settled position, the mode `phase2` performs a step of `N`. -/
lemma eraseAut_phase2_settled {v : List A} (hv : SettledR e v) (la : Option A) (p : P)
    (r : Option A) :
    (eraseAut N e).step la (p, r, EMode.phase2) v.head? =
      eraseSettled N e EMode.phase2 la v.head? p := by
  cases v with
  | nil => rfl
  | cons c v' =>
      have hc : e c ≠ none := hv c (by simp)
      rcases hec : e c with _ | b
      · exact absurd hec hc
      · simp [eraseAut, hec]

/-- If the letter to the left is not erased, a settled transition performs a
step of `N`. -/
lemma eraseSettled_of_settledL {u : List A} (hu : SettledL e u) (mR : EMode) (r : Option A)
    (p : P) :
    eraseSettled N e mR u.getLast? r p = eraseAct N e mR u.getLast? r p := by
  rcases hlast : u.getLast? with _ | z
  · rfl
  · have hz : e z ≠ none := hu z (by simp [hlast])
    rcases hez : e z with _ | b
    · exact absurd hez hz
    · simp [eraseSettled, hez]

/-! ## Runs of the simulating transducer -/

/-- Scanning to the left across a block of erased letters. -/
lemma scanL_run {mid : List A} (hmid : ErasedList e mid) (u₁ : List A) (p : P) (r : Option A) :
    ∀ rest : List A, (eraseAut N e).Reaches (Cfg.conf (u₁ ++ mid) (p, r, EMode.scanL) rest) []
      (Cfg.conf u₁ (p, r, EMode.scanL) (mid ++ rest)) := by
  induction mid using List.reverseRecOn with
  | nil => intro rest; simpa using TwoWay.Reaches.refl _
  | append_singleton mid' z ih =>
      intro rest
      obtain ⟨hmid', -⟩ := erasedList_append hmid
      have hz : e z = none := hmid z (by simp)
      have hlast : (u₁ ++ (mid' ++ [z])).getLast? = some z := by simp
      have hstep : (eraseAut N e).stepCfg (Cfg.conf (u₁ ++ (mid' ++ [z])) (p, r, EMode.scanL) rest)
          = some ([], Cfg.conf (u₁ ++ mid') (p, r, EMode.scanL) (z :: rest)) := by
        have h := TwoWay.stepCfg_left_some (M := eraseAut N e) (u := u₁ ++ (mid' ++ [z]))
          (v := rest) (q := (p, r, EMode.scanL)) (q' := (p, r, EMode.scanL)) (o := []) hlast ?_
        · simpa using h
        · rw [hlast, eraseAut_scanL, eraseSettled, hz]
      have h2 := ih hmid' (z :: rest)
      have := (TwoWay.reaches_one hstep).trans h2
      simpa using this

/-- Coming back to the right: crossing the remaining erased letters and the
first non-erased one. -/
lemma phase1_run {mid : List A} (hmid : ErasedList e mid) {a : A} {b : B} (ha : e a = some b)
    (p : P) (r : Option A) :
    ∀ (u v' : List A), (eraseAut N e).Reaches
      (Cfg.conf u (p, r, EMode.phase1) (mid ++ a :: v')) []
      (Cfg.conf (u ++ mid ++ [a]) (p, r, EMode.phase2) v') := by
  induction mid with
  | nil =>
      intro u v'
      have hstep : (eraseAut N e).stepCfg (Cfg.conf u (p, r, EMode.phase1) (a :: v')) =
          some ([], Cfg.conf (u ++ [a]) (p, r, EMode.phase2) v') := by
        refine TwoWay.stepCfg_right_cons _ ?_
        simpa using eraseAut_phase1_keep (N := N) ha u.getLast? r p
      simpa using TwoWay.reaches_one hstep
  | cons z mid ih =>
      intro u v'
      obtain ⟨hz, hmid'⟩ := erasedList_cons hmid
      have hstep : (eraseAut N e).stepCfg
          (Cfg.conf u (p, r, EMode.phase1) (z :: (mid ++ a :: v'))) =
          some ([], Cfg.conf (u ++ [z]) (p, r, EMode.phase1) (mid ++ a :: v')) := by
        refine TwoWay.stepCfg_right_cons _ ?_
        simpa using eraseAut_phase1_erased (N := N) hz u.getLast? r p
      have h2 := ih hmid' (u ++ [z]) v'
      have := (TwoWay.reaches_one hstep).trans h2
      simpa using this

/-- Skipping a block of erased letters to the right. -/
lemma phase2_run {mid : List A} (hmid : ErasedList e mid) (p : P) (r : Option A) :
    ∀ (u v : List A), (eraseAut N e).Reaches
      (Cfg.conf u (p, r, EMode.phase2) (mid ++ v)) [] (Cfg.conf (u ++ mid) (p, r, EMode.phase2) v)
      := by
  induction mid with
  | nil => intro u v; simpa using TwoWay.Reaches.refl _
  | cons z mid ih =>
      intro u v
      obtain ⟨hz, hmid'⟩ := erasedList_cons hmid
      have hstep : (eraseAut N e).stepCfg
          (Cfg.conf u (p, r, EMode.phase2) (z :: (mid ++ v))) =
          some ([], Cfg.conf (u ++ [z]) (p, r, EMode.phase2) (mid ++ v)) := by
        refine TwoWay.stepCfg_right_cons _ ?_
        simpa using eraseAut_phase2_erased (N := N) hz u.getLast? r p
      have h2 := ih hmid' (u ++ [z]) v
      have := (TwoWay.reaches_one hstep).trans h2
      simpa using this

/-- From a canonical position, the transducer reaches the position from which a
step of `N` is performed. -/
lemma reach_act {u₁ mid v : List A} (hmid : ErasedList e mid) (hu : SettledL e u₁)
    (hv : SettledR e v) (p : P) (r : Option A) :
    ∃ (m : EMode) (r' : Option A),
      (eraseAut N e).Reaches (Cfg.conf (u₁ ++ mid) (p, r, EMode.phase2) v) []
        (Cfg.conf u₁ (p, r', m) (mid ++ v)) ∧
      (eraseAut N e).step u₁.getLast? (p, r', m) (mid ++ v).head? =
        eraseAct N e (if mid = [] then EMode.phase2 else EMode.phase1) u₁.getLast? v.head? p := by
  rcases List.eq_nil_or_concat mid with rfl | ⟨mid', z, hcon⟩
  · refine ⟨EMode.phase2, r, ?_, ?_⟩
    · simp only [List.append_nil, List.nil_append]
      exact TwoWay.Reaches.refl _
    simp only [List.nil_append]
    rw [eraseAut_phase2_settled hv, eraseSettled_of_settledL hu]
    simp
  · have hmid2 : mid = mid' ++ [z] := by simpa using hcon
    subst hmid2
    obtain ⟨hmid', -⟩ := erasedList_append hmid
    have hz : e z = none := hmid z (by simp)
    have hlast : (u₁ ++ (mid' ++ [z])).getLast? = some z := by simp
    have hstep : (eraseAut N e).stepCfg
        (Cfg.conf (u₁ ++ (mid' ++ [z])) (p, r, EMode.phase2) v) =
        some ([], Cfg.conf (u₁ ++ mid') (p, v.head?, EMode.scanL) (z :: v)) := by
      have h := TwoWay.stepCfg_left_some (M := eraseAut N e) (u := u₁ ++ (mid' ++ [z]))
        (v := v) (q := (p, r, EMode.phase2)) (q' := (p, v.head?, EMode.scanL)) (o := []) hlast ?_
      · simpa using h
      · rw [hlast, eraseAut_phase2_settled hv, eraseSettled, hz]
    refine ⟨EMode.scanL, v.head?, ?_, ?_⟩
    · have h2 := scanL_run (N := N) hmid' u₁ p v.head? (z :: v)
      have := (TwoWay.reaches_one hstep).trans h2
      simpa using this
    · rw [eraseAut_scanL, eraseSettled_of_settledL hu]
      simp

/-! ## The simulation -/

/-- The relation between the configurations of `eraseAut` and those of `N`. -/
def eraseRel (e : A → Option B) :
    Cfg A (P × Option A × EMode) → Cfg B P → Prop := fun X c =>
  (X = Cfg.halt ∧ c = Cfg.halt) ∨
    ∃ (u v : List A) (p : P) (r : Option A), SettledR e v ∧
      X = Cfg.conf u (p, r, EMode.phase2) v ∧
      c = Cfg.conf (u.filterMap e) p (v.filterMap e)

/-- The one-step condition of the simulation principle. -/
lemma eraseAut_step (X : Cfg A (P × Option A × EMode)) (c : Cfg B P) (o : List C)
    (c' : Cfg B P) (hR : eraseRel (P := P) e X c) (hs : N.stepCfg c = some (o, c')) :
    ∃ Y, (eraseAut N e).Reaches X o Y ∧ eraseRel (P := P) e Y c' := by
  rcases hR with ⟨-, rfl⟩ | ⟨u, v, p, r, hv, rfl, rfl⟩
  · simp [TwoWay.stepCfg] at hs
  obtain ⟨u₁, mid, rfl, hmid, hu⟩ := exists_split_left (e := e) u
  have hfu : (u₁ ++ mid).filterMap e = u₁.filterMap e := by
    rw [List.filterMap_append, filterMap_erasedList hmid, List.append_nil]
  have hlast : ((u₁ ++ mid).filterMap e).getLast? = u₁.getLast?.bind e := by
    rw [hfu, getLast?_filterMap_settled hu]
  have hhead : (v.filterMap e).head? = v.head?.bind e := head?_filterMap_settled hv
  obtain ⟨m, r', hreach, hstepeq⟩ := reach_act (N := N) hmid hu hv p r
  set mR : EMode := if mid = [] then EMode.phase2 else EMode.phase1 with hmR
  rcases hNstep : N.step ((u₁ ++ mid).filterMap e).getLast? p (v.filterMap e).head? with
    o₁ | ⟨p', o₁, dir⟩
  · -- `N` halts
    rw [TwoWay.stepCfg_halt_eq N hNstep] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨Cfg.halt, ?_, Or.inl ⟨rfl, rfl⟩⟩
    have hact : (eraseAut N e).stepCfg (Cfg.conf u₁ (p, r', m) (mid ++ v)) =
        some (o₁, Cfg.halt) := by
      refine TwoWay.stepCfg_halt_eq _ ?_
      rw [hstepeq, eraseAct]
      rw [hlast, hhead] at hNstep
      rw [hNstep]
    have := hreach.trans (TwoWay.reaches_one hact)
    simpa using this
  · cases dir with
    | true =>
        -- `N` moves to the right
        rcases hvc : v with _ | ⟨a, v'⟩
        · subst hvc
          simp only [List.filterMap_nil] at hs
          rw [TwoWay.stepCfg_right_nil N hNstep] at hs
          simp at hs
        · subst hvc
          have ha : e a ≠ none := hv a (by simp)
          rcases hea : e a with _ | b
          · exact absurd hea ha
          have hfv : (a :: v').filterMap e = b :: v'.filterMap e := by simp [hea]
          rw [hfv] at hs hNstep
          rw [TwoWay.stepCfg_right_cons N hNstep] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          -- the simulating transducer crosses `mid` and `a`
          have hact : (eraseAut N e).step u₁.getLast? (p, r', m)
              (mid ++ a :: v').head? = Sum.inr ((p', some a, mR), o₁, true) := by
            rw [hstepeq, eraseAct]
            rw [hlast] at hNstep
            simp only [List.head?_cons, Option.bind_some, hea] at hNstep ⊢
            rw [hNstep]
          obtain ⟨mid', v'', hv'eq, hmid'', hset''⟩ := exists_split_right (e := e) v'
          have hcross : (eraseAut N e).Reaches (Cfg.conf u₁ (p, r', m)
              (mid ++ a :: v')) o₁ (Cfg.conf (u₁ ++ mid ++ [a]) (p', some a, EMode.phase2) v') := by
            rcases hmidc : mid with _ | ⟨z, mid₀⟩
            · subst hmidc
              have hmR2 : mR = EMode.phase2 := by simp [hmR]
              have h1 : (eraseAut N e).stepCfg (Cfg.conf u₁ (p, r', m)
                  ([] ++ a :: v')) = some (o₁, Cfg.conf (u₁ ++ [a]) (p', some a, EMode.phase2) v')
                  := by
                refine TwoWay.stepCfg_right_cons _ ?_
                simpa [hmR2] using hact
              simpa using TwoWay.reaches_one h1
            · subst hmidc
              have hmR2 : mR = EMode.phase1 := by simp [hmR]
              obtain ⟨hz, hmid₀⟩ := erasedList_cons hmid
              have h1 : (eraseAut N e).stepCfg (Cfg.conf u₁ (p, r', m)
                  ((z :: mid₀) ++ a :: v')) =
                  some (o₁, Cfg.conf (u₁ ++ [z]) (p', some a, EMode.phase1) (mid₀ ++ a :: v')) := by
                refine TwoWay.stepCfg_right_cons _ ?_
                simpa [hmR2] using hact
              have h2 := phase1_run (N := N) hmid₀ hea p' (some a) (u₁ ++ [z]) v'
              have := (TwoWay.reaches_one h1).trans h2
              simpa using this
          have hskip := phase2_run (N := N) hmid'' p' (some a) (u₁ ++ mid ++ [a]) v''
          rw [← hv'eq] at hskip
          refine ⟨Cfg.conf (u₁ ++ mid ++ [a] ++ mid') (p', some a, EMode.phase2) v'', ?_, ?_⟩
          · have := hreach.trans (hcross.trans hskip)
            simpa using this
          · refine Or.inr ⟨u₁ ++ mid ++ [a] ++ mid', v'', p', some a, hset'', rfl, ?_⟩
            have h1 : (u₁ ++ mid ++ [a] ++ mid').filterMap e = u₁.filterMap e ++ [b] := by
              rw [List.filterMap_append, List.filterMap_append, List.filterMap_append,
                filterMap_erasedList hmid, filterMap_erasedList hmid'']
              simp [hea]
            have h2 : v''.filterMap e = v'.filterMap e := by
              rw [hv'eq, List.filterMap_append, filterMap_erasedList hmid'', List.nil_append]
            rw [h1, h2, hfu]
    | false =>
        -- `N` moves to the left
        rcases hg : ((u₁ ++ mid).filterMap e).getLast? with _ | y
        · rw [TwoWay.stepCfg_left_none N hg hNstep] at hs; simp at hs
        · rw [TwoWay.stepCfg_left_some N hg hNstep] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          rw [hlast] at hg
          rcases hz : u₁.getLast? with _ | z
          · rw [hz] at hg; simp at hg
          rw [hz] at hg
          simp only [Option.bind_some] at hg
          have hdrop : u₁.dropLast ++ [z] = u₁ := List.dropLast_append_getLast? _ hz
          have hact : (eraseAut N e).step u₁.getLast? (p, r', m) (mid ++ v).head? =
              Sum.inr ((p', v.head?, EMode.phase2), o₁, false) := by
            rw [hstepeq, eraseAct]
            rw [hlast, hhead] at hNstep
            rw [hNstep]
          have h1 : (eraseAut N e).stepCfg (Cfg.conf u₁ (p, r', m) (mid ++ v)) =
              some (o₁, Cfg.conf u₁.dropLast (p', v.head?, EMode.phase2) (z :: (mid ++ v))) := by
            exact TwoWay.stepCfg_left_some _ hz hact
          refine ⟨Cfg.conf u₁.dropLast (p', v.head?, EMode.phase2) (z :: (mid ++ v)), ?_, ?_⟩
          · have := hreach.trans (TwoWay.reaches_one h1)
            simpa using this
          · refine Or.inr ⟨u₁.dropLast, z :: (mid ++ v), p', v.head?, ?_, rfl, ?_⟩
            · intro x hx
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
              subst hx
              rw [hg]; simp
            · have hfu2 : u₁.filterMap e = u₁.dropLast.filterMap e ++ [y] := by
                conv_lhs => rw [← hdrop]
                rw [List.filterMap_append]
                simp [hg]
              have h2 : (z :: (mid ++ v)).filterMap e = y :: v.filterMap e := by
                rw [List.filterMap_cons_some hg, List.filterMap_append,
                  filterMap_erasedList hmid, List.nil_append]
              rw [h2, hfu, hfu2]
              simp

/-- The transducer `eraseAut` computes the composition with `List.filterMap e`. -/
theorem eraseAut_computes {g : List B → List C} (hN : ∀ v, N.Computes v (g v)) (w : List A) :
    (eraseAut N e).Computes w (g (w.filterMap e)) := by
  obtain ⟨mid, w', hw, hmid, hset⟩ := exists_split_right (e := e) w
  refine TwoWay.computes_of_sim' (eraseRel (P := P) e) (eraseAut_step (N := N) (e := e))
    (X₀ := Cfg.conf mid (N.init, none, EMode.phase2) w') ?_ ?_ ?_ (hN _)
  · have := phase2_run (N := N) (e := e) hmid N.init none [] w'
    rw [← hw] at this
    simpa [eraseAut] using this
  · refine Or.inr ⟨mid, w', N.init, none, hset, rfl, ?_⟩
    rw [filterMap_erasedList hmid, hw, List.filterMap_append, filterMap_erasedList hmid,
      List.nil_append]
  · rintro Y (⟨rfl, -⟩ | ⟨u, v, p, r, -, -, h⟩)
    · rfl
    · exact absurd h (by simp)

/-- Two-way transducers are closed under pre-composition with an erasing
homomorphism. -/
theorem isTwoWay_comp_filterMap [Finite A] {g : List B → List C} (hg : IsTwoWay g)
    (e : A → Option B) : IsTwoWay (fun w => g (w.filterMap e)) := by
  obtain ⟨P, hP, N, hN⟩ := hg
  haveI := hP
  exact ⟨P × Option A × EMode, inferInstance, eraseAut N e, fun w => eraseAut_computes hN w⟩

/-- An erasing homomorphism is a `List.filterMap`. -/
lemma homOf_eq_filterMap {ρ : A → List B} (hρ : ∀ a, (ρ a).length ≤ 1) (w : List A) :
    homOf ρ w = w.filterMap (fun a => (ρ a).head?) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [homOf_cons, ih]
      rcases hr : ρ a with _ | ⟨b, t⟩
      · simp [hr]
      · have ht : t = [] := by
          have h1 := hρ a
          rw [hr] at h1
          simp only [List.length_cons] at h1
          exact List.length_eq_zero_iff.mp (by omega)
        subst ht
        simp [hr]

/-- Two-way transducers are closed under pre-composition with a homomorphism
that maps every letter to at most one letter. -/
theorem isTwoWay_comp_eraseHom [Finite A] {g : List B → List C} (hg : IsTwoWay g)
    {ρ : A → List B} (hρ : ∀ a, (ρ a).length ≤ 1) : IsTwoWay (fun w => g (homOf ρ w)) := by
  have h := isTwoWay_comp_filterMap (g := g) hg (fun a => (ρ a).head?)
  simpa [homOf_eq_filterMap hρ] using h

end Erase

end Lax916827Proofs.Transducers
