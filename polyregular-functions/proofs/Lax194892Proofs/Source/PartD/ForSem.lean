/-
Part D: for-transducers -- the semantic toolkit.

Elementary facts about the semantics of the for-transducers of *Transducers* (M. Bojańczyk), used
in the proofs of Lemma `lemma:prenex-normal-form` and of Lemma `lem:for-closed-under-composition`.

The central one is `Transducers.exec_nestLoops`: a nest of loops runs its body once for every
tuple of positions, in the lexicographic order of the tuples, and threads the Boolean valuation
through them.  This turns the nests of loops -- which is what the prenex form of Definition
`def:prenex-normal-form-for-transducers` is made of -- into folds over an explicit list, where they
can be manipulated by list lemmas.
-/
import Lax194892Proofs.Source.PartD.ForDef

namespace Lax194892Proofs.Transducers

open scoped Classical

/-! ## A generic fold -/

/-- Folding a step function over a list, threading a state and concatenating the outputs.  This is
`Transducers.forLoopRun` for an arbitrary index type. -/
def runList {α S B : Type} (step : S → α → S × List B) : List α → S → S × List B
  | [], s => (s, [])
  | a :: as, s =>
      let r := step s a
      let r' := runList step as r.1
      (r'.1, r.2 ++ r'.2)

variable {α β S B : Type}

@[simp] lemma runList_nil (step : S → α → S × List B) (s : S) : runList step [] s = (s, []) := rfl

lemma runList_cons (step : S → α → S × List B) (a : α) (as : List α) (s : S) :
    runList step (a :: as) s =
      ((runList step as (step s a).1).1, (step s a).2 ++ (runList step as (step s a).1).2) := rfl

lemma forLoopRun_eq_runList {B : Type} (body : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B)
    (ps : List ℕ) (bv : ℕ → Bool) : forLoopRun body ps bv = runList body ps bv := by
  induction ps generalizing bv with
  | nil => rfl
  | cons p ps ih => simp [forLoopRun, runList_cons, ih]

lemma runList_append (step : S → α → S × List B) (as bs : List α) (s : S) :
    runList step (as ++ bs) s =
      ((runList step bs (runList step as s).1).1,
        (runList step as s).2 ++ (runList step bs (runList step as s).1).2) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih => simp [runList_cons, ih, List.append_assoc]

lemma runList_map (step : S → β → S × List B) (f : α → β) (as : List α) (s : S) :
    runList step (as.map f) s = runList (fun s a => step s (f a)) as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [runList_cons, ih]

lemma runList_flatMap (step : S → β → S × List B) (f : α → List β) (as : List α) (s : S) :
    runList step (as.flatMap f) s = runList (fun s a => runList step (f a) s) as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, runList_append, runList_cons, ih]

/-- If every step of the list leaves the state alone and produces nothing, so does the fold. -/
lemma runList_noop (step : S → α → S × List B) (as : List α) (s : S)
    (h : ∀ a ∈ as, step s a = (s, [])) : runList step as s = (s, []) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      have ha : step s a = (s, []) := h a (by simp)
      simp [runList_cons, ha, ih (fun b hb => h b (by simp [hb]))]

/-- Steps that do nothing can be dropped from the list. -/
lemma runList_filter (step : S → α → S × List B) (p : α → Bool) (as : List α) (s : S)
    (h : ∀ a ∈ as, p a = false → ∀ t, step t a = (t, [])) :
    runList step as s = runList step (as.filter p) s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      have h' : ∀ b ∈ as, p b = false → ∀ t, step t b = (t, []) :=
        fun b hb => h b (by simp [hb])
      by_cases hp : p a = true
      · rw [List.filter_cons_of_pos hp, runList_cons, runList_cons, ih (step s a).1 h']
      · have hpa : p a = false := by simpa using hp
        have hs : step s a = (s, []) := h a (by simp) hpa s
        rw [List.filter_cons_of_neg (by simp [hpa]), runList_cons, hs, ih s h']
        simp

/-- A fixed coordinate of the state that no step changes is not changed by the fold. -/
lemma runList_fix {γ : Type} (step : S → α → S × List B) (as : List α) (s : S)
    (val : S → γ) (h : ∀ t a, val (step t a).1 = val t) : val (runList step as s).1 = val s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [runList_cons, ih, h]

/-- Two folds that are related step by step stay related. -/
lemma runList_sim {S₁ S₂ : Type} (step₁ : S₁ → α → S₁ × List B) (step₂ : S₂ → α → S₂ × List B)
    (R : S₁ → S₂ → Prop) (as : List α) (s₁ : S₁) (s₂ : S₂) (hs : R s₁ s₂)
    (h : ∀ t₁ t₂ a, a ∈ as → R t₁ t₂ →
      (step₁ t₁ a).2 = (step₂ t₂ a).2 ∧ R (step₁ t₁ a).1 (step₂ t₂ a).1) :
    (runList step₁ as s₁).2 = (runList step₂ as s₂).2 ∧
      R (runList step₁ as s₁).1 (runList step₂ as s₂).1 := by
  induction as generalizing s₁ s₂ with
  | nil => exact ⟨rfl, hs⟩
  | cons a as ih =>
      obtain ⟨h1, h2⟩ := h s₁ s₂ a (by simp) hs
      obtain ⟨h3, h4⟩ := ih _ _ h2 (fun t₁ t₂ b hb => h t₁ t₂ b (by simp [hb]))
      exact ⟨by simp [runList_cons, h1, h3], by simpa [runList_cons] using h4⟩

/-! ## Nests of loops as folds over tuples -/

/-- The list of positions visited by a loop of direction `d` over a word of length `n`. -/
def loopRange (d : Bool) (n : ℕ) : List ℕ := if d then List.range n else (List.range n).reverse

@[simp] lemma loopRange_true (n : ℕ) : loopRange true n = List.range n := rfl
@[simp] lemma loopRange_false (n : ℕ) : loopRange false n = (List.range n).reverse := rfl

lemma mem_loopRange {d : Bool} {n p : ℕ} : p ∈ loopRange d n ↔ p < n := by
  cases d <;> simp [loopRange]

lemma loopRange_length (d : Bool) (n : ℕ) : (loopRange d n).length = n := by
  cases d <;> simp [loopRange]

/-- The tuples of positions visited by a nest of loops, in the order in which the nest visits
them. -/
def tuplesOf : List (Bool × ℕ) → ℕ → List (List ℕ)
  | [], _ => [[]]
  | (d, _) :: L, n => (loopRange d n).flatMap (fun p => (tuplesOf L n).map (fun t => p :: t))

@[simp] lemma tuplesOf_nil (n : ℕ) : tuplesOf [] n = [[]] := rfl

lemma tuplesOf_cons (d : Bool) (x n : ℕ) (L : List (Bool × ℕ)) :
    tuplesOf ((d, x) :: L) n =
      (loopRange d n).flatMap (fun p => (tuplesOf L n).map (fun t => p :: t)) := rfl

/-- Setting the loop variables of a nest to the values of a tuple. -/
def setTuple : List (Bool × ℕ) → List ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | (_, x) :: L, p :: t, pos => setTuple L t (Function.update pos x p)
  | _, _, pos => pos

@[simp] lemma setTuple_nil (t : List ℕ) (pos : ℕ → ℕ) : setTuple [] t pos = pos := by
  cases t <;> rfl

@[simp] lemma setTuple_cons (d : Bool) (x : ℕ) (L : List (Bool × ℕ)) (p : ℕ) (t : List ℕ)
    (pos : ℕ → ℕ) :
    setTuple ((d, x) :: L) (p :: t) pos = setTuple L t (Function.update pos x p) := rfl

/-- A tuple only changes the loop variables of the nest. -/
lemma setTuple_of_not_mem (L : List (Bool × ℕ)) (t : List ℕ) (pos : ℕ → ℕ) {i : ℕ}
    (hi : i ∉ L.map Prod.snd) : setTuple L t pos i = pos i := by
  induction L generalizing t pos with
  | nil => simp
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      cases t with
      | nil => rfl
      | cons p t =>
          simp only [setTuple_cons]
          rw [ih t _ (by simpa using (by simpa using hi : i ≠ x ∧ i ∉ L.map Prod.snd).2)]
          rw [Function.update_of_ne (by simpa using (by simpa using hi : i ≠ x ∧ i ∉ L.map Prod.snd).1)]

variable {A B : Type}

/-- **A nest of loops is a fold over the tuples of positions.** -/
lemma exec_nestLoops (w : List A) (L : List (Bool × ℕ)) (body : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) :
    ForProg.exec w (ForProg.nestLoops L body) pos bv
      = runList (fun bv t => ForProg.exec w body (setTuple L t pos) bv) (tuplesOf L w.length) bv := by
  induction L generalizing pos bv with
  | nil => simp [ForProg.nestLoops, runList_cons]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      have hd : (if d then List.range w.length else (List.range w.length).reverse)
          = loopRange d w.length := by cases d <;> rfl
      simp only [ForProg.nestLoops, ForProg.exec, hd, forLoopRun_eq_runList, tuplesOf_cons,
        runList_flatMap]
      refine congrArg (fun f => runList f (loopRange d w.length) bv) ?_
      funext bv' p
      rw [ih, runList_map]
      simp

lemma nestLoops_append (L₁ L₂ : List (Bool × ℕ)) (body : ForProg A B) :
    ForProg.nestLoops (L₁ ++ L₂) body = ForProg.nestLoops L₁ (ForProg.nestLoops L₂ body) := by
  induction L₁ with
  | nil => rfl
  | cons a L ih => obtain ⟨d, x⟩ := a; simp [ForProg.nestLoops, ih]

/-! ## The variables and the letters that a program mentions -/

namespace ForTest

variable {A : Type}

/-- The position variables occurring in a test. -/
def posVars : ForTest A → List ℕ
  | boolVar _ => []
  | eqPos i j => [i, j]
  | lePos i j => [i, j]
  | label i _ => [i]
  | not t => posVars t
  | and t s => posVars t ++ posVars s
  | or t s => posVars t ++ posVars s

/-- The Boolean variables occurring in a test. -/
def boolVars : ForTest A → List ℕ
  | boolVar i => [i]
  | eqPos _ _ => []
  | lePos _ _ => []
  | label _ _ => []
  | not t => boolVars t
  | and t s => boolVars t ++ boolVars s
  | or t s => boolVars t ++ boolVars s

/-- The letters of the input alphabet occurring in a test. -/
def letters : ForTest A → List A
  | boolVar _ => []
  | eqPos _ _ => []
  | lePos _ _ => []
  | label _ a => [a]
  | not t => letters t
  | and t s => letters t ++ letters s
  | or t s => letters t ++ letters s

/-- A test only depends on the variables it mentions. -/
lemma holds_congr (w : List A) (t : ForTest A) (pos pos' : ℕ → ℕ) (bv bv' : ℕ → Bool)
    (hp : ∀ i ∈ t.posVars, pos i = pos' i) (hb : ∀ i ∈ t.boolVars, bv i = bv' i) :
    Holds w pos bv t ↔ Holds w pos' bv' t := by
  induction t with
  | boolVar i => simp [Holds, hb i (by simp [boolVars])]
  | eqPos i j =>
      simp [Holds, hp i (by simp [posVars]), hp j (by simp [posVars])]
  | lePos i j =>
      simp [Holds, hp i (by simp [posVars]), hp j (by simp [posVars])]
  | label i a => simp [Holds, hp i (by simp [posVars])]
  | not t ih => simp [Holds, ih hp hb]
  | and t s iht ihs =>
      simp only [Holds]
      rw [iht (fun i hi => hp i (by simp [posVars, hi])) (fun i hi => hb i (by simp [boolVars, hi])),
        ihs (fun i hi => hp i (by simp [posVars, hi])) (fun i hi => hb i (by simp [boolVars, hi]))]
  | or t s iht ihs =>
      simp only [Holds]
      rw [iht (fun i hi => hp i (by simp [posVars, hi])) (fun i hi => hb i (by simp [boolVars, hi])),
        ihs (fun i hi => hp i (by simp [posVars, hi])) (fun i hi => hb i (by simp [boolVars, hi]))]

end ForTest

namespace ForProg

variable {A B : Type}

/-- The position variables occurring in a program, free or bound. -/
def posVars : ForProg A B → List ℕ
  | skip => []
  | output _ => []
  | assign _ _ => []
  | seq P Q => posVars P ++ posVars Q
  | ite t P Q => t.posVars ++ posVars P ++ posVars Q
  | loop _ x P => x :: posVars P

/-- The Boolean variables occurring in a program. -/
def boolVars : ForProg A B → List ℕ
  | skip => []
  | output _ => []
  | assign i _ => [i]
  | seq P Q => boolVars P ++ boolVars Q
  | ite t P Q => t.boolVars ++ boolVars P ++ boolVars Q
  | loop _ _ P => boolVars P

/-- The letters of the input alphabet occurring in a program. -/
def letters : ForProg A B → List A
  | skip => []
  | output _ => []
  | assign _ _ => []
  | seq P Q => letters P ++ letters Q
  | ite t P Q => t.letters ++ letters P ++ letters Q
  | loop _ _ P => letters P

/-- A program only depends on the position variables it mentions. -/
lemma exec_congr_pos (w : List A) (P : ForProg A B) (pos pos' : ℕ → ℕ) (bv : ℕ → Bool)
    (h : ∀ i ∈ P.posVars, pos i = pos' i) : exec w P pos bv = exec w P pos' bv := by
  induction P generalizing pos pos' bv with
  | skip => rfl
  | output b => rfl
  | assign i v => rfl
  | seq P Q ihP ihQ =>
      simp only [exec]
      rw [ihP pos pos' bv (fun i hi => h i (by simp [posVars, hi])),
        ihQ pos pos' _ (fun i hi => h i (by simp [posVars, hi]))]
  | ite t P Q ihP ihQ =>
      have ht : ForTest.Holds w pos bv t ↔ ForTest.Holds w pos' bv t :=
        ForTest.holds_congr w t pos pos' bv bv (fun i hi => h i (by simp [posVars, hi]))
          (fun _ _ => rfl)
      simp only [exec]
      rw [ihP pos pos' bv (fun i hi => h i (by simp [posVars, hi])),
        ihQ pos pos' bv (fun i hi => h i (by simp [posVars, hi]))]
      exact if_congr ht rfl rfl
  | loop d x P ih =>
      simp only [exec]
      refine congrArg (fun f => forLoopRun f _ bv) ?_
      funext bv' p
      refine ih _ _ _ (fun i hi => ?_)
      by_cases hix : i = x
      · subst hix; rw [Function.update_self, Function.update_self]
      · simp [Function.update_of_ne hix, h i (by simp [posVars, hi])]

/-- A program does not change the Boolean variables it does not mention. -/
lemma exec_bv_unchanged (w : List A) (P : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool) {i : ℕ}
    (h : i ∉ P.boolVars) : (exec w P pos bv).1 i = bv i := by
  induction P generalizing pos bv with
  | skip => rfl
  | output b => rfl
  | assign j v =>
      have : i ≠ j := by simpa [boolVars] using h
      simp [exec, Function.update_of_ne this]
  | seq P Q ihP ihQ =>
      simp only [exec, boolVars, List.mem_append, not_or] at *
      rw [ihQ _ _ h.2, ihP _ _ h.1]
  | ite t P Q ihP ihQ =>
      simp only [boolVars, List.mem_append, not_or] at h
      simp only [exec]
      split
      · exact ihP _ _ h.1.2
      · exact ihQ _ _ h.2
  | loop d x P ih =>
      simp only [exec, forLoopRun_eq_runList]
      exact runList_fix _ _ _ (fun bv' : ℕ → Bool => bv' i) (fun t p => ih _ _ h)

/-! ## Renaming the position variables -/

/-- Renaming the position variables of a test. -/
def _root_.Lax194892Proofs.Transducers.ForTest.renamePos {A : Type} (f : ℕ → ℕ) : ForTest A → ForTest A
  | ForTest.boolVar i => ForTest.boolVar i
  | ForTest.eqPos i j => ForTest.eqPos (f i) (f j)
  | ForTest.lePos i j => ForTest.lePos (f i) (f j)
  | ForTest.label i a => ForTest.label (f i) a
  | ForTest.not t => ForTest.not (ForTest.renamePos f t)
  | ForTest.and t s => ForTest.and (ForTest.renamePos f t) (ForTest.renamePos f s)
  | ForTest.or t s => ForTest.or (ForTest.renamePos f t) (ForTest.renamePos f s)

lemma _root_.Lax194892Proofs.Transducers.ForTest.holds_renamePos {A : Type} (w : List A) (f : ℕ → ℕ)
    (t : ForTest A) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForTest.Holds w pos bv (ForTest.renamePos f t) ↔ ForTest.Holds w (fun i => pos (f i)) bv t := by
  induction t with
  | boolVar i => rfl
  | eqPos i j => rfl
  | lePos i j => rfl
  | label i a => rfl
  | not t ih => simp [ForTest.renamePos, ForTest.Holds, ih]
  | and t s iht ihs => simp [ForTest.renamePos, ForTest.Holds, iht, ihs]
  | or t s iht ihs => simp [ForTest.renamePos, ForTest.Holds, iht, ihs]

/-- Renaming the position variables of a program. -/
def renamePos (f : ℕ → ℕ) : ForProg A B → ForProg A B
  | skip => skip
  | output b => output b
  | assign i v => assign i v
  | seq P Q => seq (renamePos f P) (renamePos f Q)
  | ite t P Q => ite (ForTest.renamePos f t) (renamePos f P) (renamePos f Q)
  | loop d x P => loop d (f x) (renamePos f P)

lemma exec_renamePos (w : List A) (f : ℕ → ℕ) (P : ForProg A B) (hP : P.LoopFree)
    (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    exec w (renamePos f P) pos bv = exec w P (fun i => pos (f i)) bv := by
  induction P generalizing bv with
  | skip => rfl
  | output b => rfl
  | assign i v => rfl
  | seq P Q ihP ihQ =>
      obtain ⟨h1, h2⟩ := hP
      simp only [renamePos, exec, ihP h1, ihQ h2]
  | ite t P Q ihP ihQ =>
      obtain ⟨h1, h2⟩ := hP
      simp only [renamePos, exec, ihP h1, ihQ h2]
      exact if_congr (ForTest.holds_renamePos w f t pos bv) rfl rfl
  | loop d x P ih => exact absurd hP (by simp [LoopFree])

lemma loopFree_renamePos (f : ℕ → ℕ) (P : ForProg A B) (hP : P.LoopFree) :
    (renamePos f P).LoopFree := by
  induction P with
  | skip => trivial
  | output b => trivial
  | assign i v => trivial
  | seq P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | ite t P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | loop d x P ih => exact absurd hP (by simp [LoopFree])

lemma boolVars_renamePos (f : ℕ → ℕ) (P : ForProg A B) : (renamePos f P).boolVars = P.boolVars := by
  induction P with
  | skip => rfl
  | output b => rfl
  | assign i v => rfl
  | seq P Q ihP ihQ => simp [renamePos, boolVars, ihP, ihQ]
  | ite t P Q ihP ihQ =>
      have : (ForTest.renamePos f t).boolVars = t.boolVars := by
        induction t with
        | boolVar i => rfl
        | eqPos i j => rfl
        | lePos i j => rfl
        | label i a => rfl
        | not t ih => simpa [ForTest.renamePos, ForTest.boolVars] using ih
        | and t s iht ihs => simp [ForTest.renamePos, ForTest.boolVars, iht, ihs]
        | or t s iht ihs => simp [ForTest.renamePos, ForTest.boolVars, iht, ihs]
      simp [renamePos, boolVars, ihP, ihQ, this]
  | loop d x P ih => simp [renamePos, boolVars, ih]

lemma posVars_renamePos (f : ℕ → ℕ) (P : ForProg A B) :
    (renamePos f P).posVars = P.posVars.map f := by
  have htest : ∀ t : ForTest A, (ForTest.renamePos f t).posVars = t.posVars.map f := by
    intro t
    induction t with
    | boolVar i => rfl
    | eqPos i j => rfl
    | lePos i j => rfl
    | label i a => rfl
    | not t ih => simpa [ForTest.renamePos, ForTest.posVars] using ih
    | and t s iht ihs => simp [ForTest.renamePos, ForTest.posVars, iht, ihs]
    | or t s iht ihs => simp [ForTest.renamePos, ForTest.posVars, iht, ihs]
  induction P with
  | skip => rfl
  | output b => rfl
  | assign i v => rfl
  | seq P Q ihP ihQ => simp [renamePos, posVars, ihP, ihQ]
  | ite t P Q ihP ihQ => simp [renamePos, posVars, ihP, ihQ, htest t]
  | loop d x P ih => simp [renamePos, posVars, ih]

end ForProg

/-! ## Unfolding the sequential composition and the conditional -/

lemma exec_seq (w : List A) (P Q : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForProg.exec w (ForProg.seq P Q) pos bv
      = ((ForProg.exec w Q pos (ForProg.exec w P pos bv).1).1,
        (ForProg.exec w P pos bv).2 ++ (ForProg.exec w Q pos (ForProg.exec w P pos bv).1).2) := by
  simp only [ForProg.exec]

lemma exec_ite_pos (w : List A) (t : ForTest A) (P Q : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool)
    (h : ForTest.Holds w pos bv t) :
    ForProg.exec w (ForProg.ite t P Q) pos bv = ForProg.exec w P pos bv := by
  simp only [ForProg.exec, if_pos h]

lemma exec_ite_neg (w : List A) (t : ForTest A) (P Q : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool)
    (h : ¬ ForTest.Holds w pos bv t) :
    ForProg.exec w (ForProg.ite t P Q) pos bv = ForProg.exec w Q pos bv := by
  simp only [ForProg.exec, if_neg h]


end Lax194892Proofs.Transducers
