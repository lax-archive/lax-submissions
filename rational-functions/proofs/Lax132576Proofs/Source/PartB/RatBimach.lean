/-
From rational functions to bimachines (the remaining implication of
Theorem `thm:bimachines`).

Let `f` be a rational function.  By `exists_unambiguous_aut_of_rationalFun` it is
computed by an unambiguous ε-free nfa with output `N`.  The associated bimachine
is built as follows.

* The prefix automaton is the subset construction: after reading the prefix `u`
  its state is the set `reach u` of states of `N` that are reachable from an
  initial state by a run over `u`, together with a flag saying whether `u` is
  empty.
* The suffix automaton is the co-reachability subset construction, run from
  right to left: at the gap before the suffix `z` its state is the set
  `coreach z` of states from which a run over `z` reaches an accepting state,
  together with the first letter of `z` and the set `coreach` of the rest of `z`
  (or `none` if `z` is empty).
* Since `N` is unambiguous, for every gap of the input the intersection
  `reach u ∩ coreach z` contains exactly one state: the state of the unique
  accepting run at that gap.  The output at a gap whose suffix starts with the
  letter `a` is therefore the output of the transition of the run that reads
  this `a`, which is determined by the two states that this transition connects.
-/
import Lax132576Proofs.Source.PartB.Bimachine
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace RatBimach

open LabAut NFAO Unambig

variable {A B Q : Type} (N : NFAO A B Q)

lemma inputOf_append {L : Type} (ts ts' : List (Q × List A × L × Q)) :
    inputOf (ts ++ ts') = inputOf ts ++ inputOf ts' := by
  simp [inputOf]

/-! ### Reachability and co-reachability -/

/-- The states reachable in one letter from a set of states. -/
def stepSet (R : Set Q) (a : A) : Set Q := {q' | ∃ q ∈ R, ∃ y, (q, [a], y, q') ∈ N.δ}

/-- The states from which one letter leads into a set of states. -/
def coStep (T : Set Q) (a : A) : Set Q := {q | ∃ y q', (q, [a], y, q') ∈ N.δ ∧ q' ∈ T}

/-- The states reachable from an initial state by a run over `u`. -/
def reach (u : List A) : Set Q := strTrans (stepSet N) u N.init

/-- The states from which a run over `z` reaches an accepting state. -/
def coreach (z : List A) : Set Q := strTrans (coStep N) z.reverse N.final

@[simp] lemma reach_nil : reach N [] = N.init := rfl

lemma reach_snoc (u : List A) (a : A) : reach N (u ++ [a]) = stepSet N (reach N u) a := by
  simp [reach, strTrans, List.foldl_append]

@[simp] lemma coreach_nil : coreach N [] = N.final := rfl

lemma coreach_cons (a : A) (z : List A) : coreach N (a :: z) = coStep N (coreach N z) a := by
  simp [coreach, strTrans]

/-- A path can be split at its first transition. -/
lemma path_cons_iff {L : Type} {M : LabAut A L Q} {q p : Q} {ts : List (Q × List A × L × Q)}
    {t : Q × List A × L × Q} :
    M.Path q (t :: ts) p ↔ t.1 = q ∧ t ∈ M.δ ∧ M.Path t.2.2.2 ts p := by
  constructor
  · intro h
    cases h with
    | cons ht hrest => exact ⟨rfl, ht, hrest⟩
  · rintro ⟨rfl, ht, hrest⟩
    have hteq : t = (t.1, t.2.1, t.2.2.1, t.2.2.2) := rfl
    rw [hteq]
    exact Path.cons ht hrest

/-- The first transition of a path of the one-letter automaton over `a :: z`
reads `a`. -/
lemma letter_head {t : Tr A B Q} {ts : List (Tr A B Q)} {a : A} {z : List A}
    (ht : t ∈ (letterAut N).δ) (hin : inputOf (t :: ts) = a :: z) :
    t.2.1 = [a] ∧ inputOf ts = z := by
  have hcard : (t.2.1).length = 1 := ht.2
  have hsum : t.2.1 ++ inputOf ts = a :: z := by simpa using hin
  match hcase : t.2.1 with
  | [] => rw [hcase] at hcard; simp at hcard
  | [b] =>
      rw [hcase] at hsum
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsum
      exact ⟨by simp [hsum.1], hsum.2⟩
  | b :: c :: r => rw [hcase] at hcard; simp at hcard

lemma mem_reach {q : Q} {u : List A} :
    q ∈ reach N u ↔
      ∃ q₀ ∈ N.init, ∃ ts, (letterAut N).Path q₀ ts q ∧ inputOf ts = u := by
  induction u using List.reverseRecOn generalizing q with
  | nil =>
      simp only [reach_nil]
      constructor
      · intro hq; exact ⟨q, hq, [], Path.nil q, rfl⟩
      · rintro ⟨q₀, hq₀, ts, hpath, hin⟩
        obtain ⟨rfl, rfl⟩ := letterPath_nil N hpath hin
        exact hq₀
  | append_singleton u a ih =>
      rw [reach_snoc]
      constructor
      · rintro ⟨r, hr, y, hy⟩
        obtain ⟨q₀, hq₀, ts, hpath, hin⟩ := ih.mp hr
        refine ⟨q₀, hq₀, ts ++ [(r, [a], y, q)], ?_, ?_⟩
        · exact path_snoc_iff.mpr ⟨hpath, ⟨hy, by simp⟩, rfl⟩
        · rw [inputOf_append, hin]; simp
      · rintro ⟨q₀, hq₀, ts, hpath, hin⟩
        obtain ⟨ts', t, rfl, hin', hta⟩ := letterPath_snoc N hpath hin
        obtain ⟨hpre, htδ, hte⟩ := path_snoc_iff.mp hpath
        refine ⟨t.1, ih.mpr ⟨q₀, hq₀, ts', hpre, hin'⟩, t.2.2.1, ?_⟩
        have heq : (t.1, [a], t.2.2.1, q) = t := by rw [← hta, ← hte]
        rw [heq]
        exact htδ.1

lemma mem_coreach {q : Q} {z : List A} :
    q ∈ coreach N z ↔
      ∃ p ∈ N.final, ∃ ts, (letterAut N).Path q ts p ∧ inputOf ts = z := by
  induction z generalizing q with
  | nil =>
      simp only [coreach_nil]
      constructor
      · intro hq; exact ⟨q, hq, [], Path.nil q, rfl⟩
      · rintro ⟨p, hp, ts, hpath, hin⟩
        obtain ⟨rfl, rfl⟩ := letterPath_nil N hpath hin
        exact hp
  | cons a z ih =>
      rw [coreach_cons]
      constructor
      · rintro ⟨y, q', hq', hmem⟩
        obtain ⟨p, hp, ts, hpath, hin⟩ := ih.mp hmem
        refine ⟨p, hp, (q, [a], y, q') :: ts, ?_, by simp [hin]⟩
        exact path_cons_iff.mpr ⟨rfl, ⟨hq', by simp⟩, hpath⟩
      · rintro ⟨p, hp, ts, hpath, hin⟩
        cases ts with
        | nil => simp at hin
        | cons t ts =>
            obtain ⟨ht1, htδ, hrest⟩ := path_cons_iff.mp hpath
            obtain ⟨hta, hin'⟩ := letter_head N htδ hin
            refine ⟨t.2.2.1, t.2.2.2, ?_, ih.mpr ⟨p, hp, ts, hrest, hin'⟩⟩
            have heq : (q, [a], t.2.2.1, t.2.2.2) = t := by rw [← hta, ← ht1]
            rw [heq]
            exact htδ.1

/-! ### The bimachine -/

variable [Nonempty Q]

open scoped Classical in
/-- The unique element of a set of states (junk if the set is not a
singleton). -/
noncomputable def theElt (X : Set Q) : Q :=
  if h : X.Nonempty then h.choose else Classical.arbitrary Q

lemma theElt_singleton {X : Set Q} {q : Q} (h : X = {q}) : theElt X = q := by
  classical
  have hne : X.Nonempty := by rw [h]; exact ⟨q, rfl⟩
  have h2 : hne.choose ∈ X := hne.choose_spec
  have h3 : theElt X = hne.choose := by rw [theElt, dif_pos hne]
  rw [h3, Set.eq_singleton_iff_unique_mem] at *
  exact h.2 _ h2

open scoped Classical in
/-- The output of a transition from `q` to `q'` reading `a` (junk if there is no
such transition). -/
noncomputable def chosenOut (q : Q) (a : A) (q' : Q) : List B :=
  if h : ∃ x, (q, [a], x, q') ∈ N.δ then h.choose else []

omit [Nonempty Q] in
lemma chosenOut_mem {q : Q} {a : A} {q' : Q} (h : ∃ x, (q, [a], x, q') ∈ N.δ) :
    (q, [a], chosenOut N q a q', q') ∈ N.δ := by
  classical
  rw [chosenOut, dif_pos h]
  exact h.choose_spec

/-- The bimachine associated with an unambiguous nfa with output computing
`f`. -/
noncomputable def bm (f : List A → List B) :
    Bimachine A B (Set Q × Bool) (Set Q × Option (A × Set Q)) where
  prefixInit := (N.init, false)
  prefixStep := fun x a => (stepSet N x.1 a, true)
  suffixInit := (N.final, none)
  suffixStep := fun y a => (coStep N y.1 a, some (a, y.1))
  out := fun x y =>
    match y.2 with
    | some (a, T') => chosenOut N (theElt (x.1 ∩ y.1)) a (theElt (stepSet N x.1 a ∩ T'))
    | none => if x.2 then [] else f []

variable (f : List A → List B)

lemma suffixState (z : List A) :
    strTrans (bm N f).suffixStep z.reverse (bm N f).suffixInit =
      (coreach N z, match z with | [] => none | a :: z' => some (a, coreach N z')) := by
  induction z with
  | nil => rfl
  | cons a z ih =>
      have hstep : strTrans (bm N f).suffixStep (a :: z).reverse (bm N f).suffixInit =
          (bm N f).suffixStep (strTrans (bm N f).suffixStep z.reverse (bm N f).suffixInit) a := by
        simp [strTrans, List.reverse_cons]
      rw [hstep, ih]
      simp [bm, coreach_cons]

/-! ### Correctness -/

variable {N f}

omit [Nonempty Q] in
/-- The state of the unique accepting run at a gap is the unique element of the
intersection of the reachable and the co-reachable set. -/
lemma gap_state_unique (hunamb : N.Unambiguous) {u z : List A} (huz : u ++ z ≠ [])
    {q₀ q p : Q} {ts₁ ts₂ : List (Tr A B Q)} (hq₀ : q₀ ∈ N.init) (hp : p ∈ N.final)
    (h₁ : (letterAut N).Path q₀ ts₁ q) (hin₁ : inputOf ts₁ = u)
    (h₂ : (letterAut N).Path q ts₂ p) (hin₂ : inputOf ts₂ = z) :
    reach N u ∩ coreach N z = {q} := by
  have hacc : N.Accepting (ts₁ ++ ts₂) :=
    ⟨q₀, hq₀, p, hp, (path_of_letterPath h₁).append (path_of_letterPath h₂)⟩
  have hinacc : inputOf (ts₁ ++ ts₂) = u ++ z := by rw [inputOf_append, hin₁, hin₂]
  ext r
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hr₁, hr₂⟩
    obtain ⟨q₀', hq₀', ts₁', hpath₁', hin₁'⟩ := (mem_reach N).mp hr₁
    obtain ⟨p', hp', ts₂', hpath₂', hin₂'⟩ := (mem_coreach N).mp hr₂
    have hacc' : N.Accepting (ts₁' ++ ts₂') :=
      ⟨q₀', hq₀', p', hp', (path_of_letterPath hpath₁').append (path_of_letterPath hpath₂')⟩
    have hinacc' : inputOf (ts₁' ++ ts₂') = u ++ z := by rw [inputOf_append, hin₁', hin₂']
    have heq : ts₁' ++ ts₂' = ts₁ ++ ts₂ :=
      (hunamb (u ++ z)).unique ⟨hacc', hinacc'⟩ ⟨hacc, hinacc⟩
    have hlen : ts₁'.length = ts₁.length := by
      have e1 := letterPath_length N hpath₁'
      have e2 := letterPath_length N h₁
      rw [hin₁'] at e1
      rw [hin₁] at e2
      omega
    obtain ⟨e1, e2⟩ := List.append_inj heq hlen
    rw [e1] at hpath₁'
    rw [e2] at hpath₂'
    cases ts₂ with
    | cons t ts =>
        have k1 := path_cons_iff.mp hpath₂'
        have k2 := path_cons_iff.mp h₂
        rw [← k1.1, k2.1]
    | nil =>
        cases ts₁ with
        | cons t ts =>
            have k1 := path_cons_iff.mp hpath₁'
            have k2 := path_cons_iff.mp h₁
            have hq₀eq : q₀' = q₀ := by rw [← k1.1, k2.1]
            subst hq₀eq
            exact path_end_unique hpath₁' h₁
        | nil =>
            exact absurd (by rw [← hin₁, ← hin₂]; simp) huz
  · rintro rfl
    exact ⟨(mem_reach N).mpr ⟨q₀, hq₀, ts₁, h₁, hin₁⟩,
      (mem_coreach N).mpr ⟨p, hp, ts₂, h₂, hin₂⟩⟩

/-- The output of the bimachine over a suffix is the output of the
corresponding part of the unique accepting run. -/
lemma evalFrom_eq (hunamb : N.Unambiguous) :
    ∀ (z u : List A), u ++ z ≠ [] → ∀ (q₀ q p : Q) (ts₁ ts₂ : List (Tr A B Q)),
      q₀ ∈ N.init → p ∈ N.final → (letterAut N).Path q₀ ts₁ q → inputOf ts₁ = u →
      (letterAut N).Path q ts₂ p → inputOf ts₂ = z →
      (bm N f).evalFrom (reach N u, !u.isEmpty) z = outputOf ts₂ := by
  intro z
  induction z with
  | nil =>
      intro u huz q₀ q p ts₁ ts₂ hq₀ hp h₁ hin₁ h₂ hin₂
      obtain ⟨rfl, rfl⟩ := letterPath_nil N h₂ hin₂
      have hu : u ≠ [] := by simpa using huz
      have hflag : (!u.isEmpty) = true := by
        cases u with
        | nil => exact absurd rfl hu
        | cons a u => simp
      rw [Bimachine.evalFrom_nil]
      simp [bm, hflag]
  | cons a z ih =>
      intro u huz q₀ q p ts₁ ts₂ hq₀ hp h₁ hin₁ h₂ hin₂
      cases ts₂ with
      | nil => simp at hin₂
      | cons t ts =>
          obtain ⟨ht1, htδ, hrest⟩ := path_cons_iff.mp h₂
          obtain ⟨hta, hinrest⟩ := letter_head N htδ hin₂
          -- the induction hypothesis for the longer prefix
          have hpath₁' : (letterAut N).Path q₀ (ts₁ ++ [t]) t.2.2.2 :=
            path_snoc_iff.mpr ⟨by rw [ht1]; exact h₁, htδ, rfl⟩
          have hin₁' : inputOf (ts₁ ++ [t]) = u ++ [a] := by
            rw [inputOf_append, hin₁]
            simp [hta]
          have hih := ih (u ++ [a]) (by simp) q₀ t.2.2.2 p (ts₁ ++ [t]) ts
            hq₀ hp hpath₁' hin₁' hrest hinrest
          have hpre : reach N (u ++ [a]) = stepSet N (reach N u) a := reach_snoc N u a
          have hflag : (!(u ++ [a]).isEmpty) = true := by simp
          rw [hpre, hflag] at hih
          rw [Bimachine.evalFrom_cons]
          have hsuf : strTrans (bm N f).suffixStep (a :: z).reverse (bm N f).suffixInit =
              (coreach N (a :: z), some (a, coreach N z)) := suffixState N f (a :: z)
          rw [hsuf]
          have hstep : (bm N f).prefixStep (reach N u, !u.isEmpty) a =
              (stepSet N (reach N u) a, true) := rfl
          rw [hstep, hih]
          -- the output of the piece at this gap is the output of the transition `t`
          have hq : reach N u ∩ coreach N (a :: z) = {q} :=
            gap_state_unique hunamb (by simp) hq₀ hp h₁ hin₁ h₂ hin₂
          have hq' : stepSet N (reach N u) a ∩ coreach N z = {t.2.2.2} := by
            rw [← reach_snoc]
            exact gap_state_unique hunamb (by simp) hq₀ hp hpath₁' hin₁' hrest hinrest
          have hout : (bm N f).out (reach N u, !u.isEmpty)
              (coreach N (a :: z), some (a, coreach N z)) = chosenOut N q a t.2.2.2 := by
            simp only [bm]
            rw [theElt_singleton hq, theElt_singleton hq']
          rw [hout]
          -- the chosen transition is the transition of the run
          have hex : ∃ x, (q, [a], x, t.2.2.2) ∈ N.δ := by
            refine ⟨t.2.2.1, ?_⟩
            have heq : (q, [a], t.2.2.1, t.2.2.2) = t := by rw [← hta, ← ht1]
            rw [heq]
            exact htδ.1
          have hmem := chosenOut_mem N hex
          have hacc1 : N.Accepting (ts₁ ++ (q, [a], chosenOut N q a t.2.2.2, t.2.2.2) :: ts) :=
            ⟨q₀, hq₀, p, hp, (path_of_letterPath h₁).append
              (Path.cons hmem (path_of_letterPath hrest))⟩
          have hacc2 : N.Accepting (ts₁ ++ t :: ts) :=
            ⟨q₀, hq₀, p, hp, (path_of_letterPath h₁).append (path_of_letterPath h₂)⟩
          have hin1 : inputOf (ts₁ ++ (q, [a], chosenOut N q a t.2.2.2, t.2.2.2) :: ts) =
              u ++ a :: z := by
            rw [inputOf_append, hin₁]
            simp [hinrest]
          have hin2 : inputOf (ts₁ ++ t :: ts) = u ++ a :: z := by
            rw [inputOf_append, hin₁, hin₂]
          have heq := (hunamb (u ++ a :: z)).unique ⟨hacc1, hin1⟩ ⟨hacc2, hin2⟩
          have hteq : (q, [a], chosenOut N q a t.2.2.2, t.2.2.2) :: ts = t :: ts :=
            (List.append_inj heq rfl).2
          have hxeq : chosenOut N q a t.2.2.2 = t.2.2.1 := by
            have := congrArg (fun s => s.2.2.1) (List.cons.inj hteq).1
            simpa using this
          rw [hxeq]
          simp

/-- The bimachine computes `f`. -/
theorem bm_eval (hunamb : N.Unambiguous)
    (hef : ∀ ts, N.Accepting ts →
      (inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧ (inputOf ts = [] → ts.length = 1))
    (hrel : ∀ w v, N.rel w v ↔ v = f w) : (bm N f).eval = f := by
  funext w
  rw [Bimachine.eval_eq_evalFrom]
  by_cases hw : w = []
  · subst hw
    rw [Bimachine.evalFrom_nil]
    simp [bm]
  · obtain ⟨ts, ⟨hacc, hin⟩, -⟩ := hunamb w
    obtain ⟨q₀, hq₀, p, hp, hpath⟩ := hacc
    have hlen := (hef ts ⟨q₀, hq₀, p, hp, hpath⟩).1 (by rw [hin]; exact hw)
    have hletter : (letterAut N).Path q₀ ts p := letterPath_of_path hpath hlen
    have hval : outputOf ts = f w := by
      have hr : N.rel w (outputOf ts) := ⟨ts, ⟨q₀, hq₀, p, hp, hpath⟩, hin, rfl⟩
      exact (hrel w _).mp hr
    have hmain := evalFrom_eq (f := f) hunamb w [] (by simpa using hw) q₀ q₀ p [] ts
      hq₀ hp (Path.nil q₀) rfl hletter hin
    simpa [bm, hval] using hmain

end RatBimach

/-- A rational function is computed by a bimachine. -/
theorem isBimachine_of_rationalFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : IsBimachine f := by
  obtain ⟨Q, hQ, N, hunamb, hef, hrel⟩ := exists_unambiguous_aut_of_rationalFun hf
  have hne : Nonempty Q := by
    obtain ⟨ts, ⟨⟨q₀, hq₀, p, hp, hpath⟩, -⟩, -⟩ := hunamb []
    exact ⟨q₀⟩
  exact ⟨Set Q × Bool, Set Q × Option (A × Set Q), inferInstance, inferInstance,
    RatBimach.bm N f, RatBimach.bm_eval hunamb hef hrel⟩

end Lax132576Proofs.Transducers
