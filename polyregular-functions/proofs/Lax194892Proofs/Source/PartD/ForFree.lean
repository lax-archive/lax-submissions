/-
Part D: for-transducers -- the free position variables of a program, and closing a program.

The translation of the outer for-transducer used in the proof of Lemma
`lem:for-closed-under-composition` represents a position variable of the translated program by a
tuple of positions of the input of the inner one.  This makes sense for a position variable that
is bound by a loop of the translated program, and only for such a variable: a *free* position
variable of the translated program denotes the first position of the intermediate string, which is
not, in general, one of the positions at which the inner transducer produces a letter.

This file introduces the free position variables of a program (`Transducers.ForProg.freePos`) and
the transformation `Transducers.closeProg`, which turns a program into an equivalent one with no
free position variable: every free variable is bound by an extra loop that is executed only at the
first position of the input, and the empty input, on which such a loop does nothing, is dealt with
separately by a constant program.
-/
import Lax194892Proofs.Source.PartD.ForAtom

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B C : Type}

namespace ForProg

/-! ## The free position variables of a program -/

/-- The position variables that occur free in a program, that is, those that are not bound by an
enclosing loop. -/
def freePos : ForProg A B → List ℕ
  | skip => []
  | output _ => []
  | assign _ _ => []
  | seq P Q => freePos P ++ freePos Q
  | ite t P Q => t.posVars ++ freePos P ++ freePos Q
  | loop _ x P => (freePos P).filter (fun z => !decide (z = x))

@[simp] lemma freePos_skip : (ForProg.skip : ForProg A B).freePos = [] := rfl

@[simp] lemma freePos_output (b : B) : (ForProg.output b : ForProg A B).freePos = [] := rfl

@[simp] lemma freePos_assign (i : ℕ) (v : Bool) :
    (ForProg.assign i v : ForProg A B).freePos = [] := rfl

@[simp] lemma freePos_seq (P Q : ForProg A B) :
    (ForProg.seq P Q).freePos = P.freePos ++ Q.freePos := rfl

@[simp] lemma freePos_ite (t : ForTest A) (P Q : ForProg A B) :
    (ForProg.ite t P Q).freePos = t.posVars ++ P.freePos ++ Q.freePos := rfl

@[simp] lemma freePos_loop (d : Bool) (x : ℕ) (P : ForProg A B) :
    (ForProg.loop d x P).freePos = P.freePos.filter (fun z => !decide (z = x)) := rfl

lemma mem_freePos_loop {d : Bool} {x y : ℕ} {P : ForProg A B} (hy : y ∈ P.freePos) (hxy : y ≠ x) :
    y ∈ (ForProg.loop d x P).freePos := by
  simp [List.mem_filter, hy, hxy]

/-- A free position variable of a program occurs in it. -/
lemma freePos_subset_posVars : ∀ (P : ForProg A B) (y : ℕ), y ∈ P.freePos → y ∈ P.posVars := by
  intro P
  induction P with
  | skip => intro y hy; simp at hy
  | output b => intro y hy; simp at hy
  | assign i v => intro y hy; simp at hy
  | seq P Q ihP ihQ =>
      intro y hy
      simp only [freePos_seq, List.mem_append] at hy
      rcases hy with h | h
      · simp [posVars, ihP y h]
      · simp [posVars, ihQ y h]
  | ite t P Q ihP ihQ =>
      intro y hy
      simp only [freePos_ite, List.mem_append] at hy
      rcases hy with (h | h) | h
      · simp [posVars, h]
      · simp [posVars, ihP y h]
      · simp [posVars, ihQ y h]
  | loop d x P ih =>
      intro y hy
      simp only [freePos_loop, List.mem_filter] at hy
      simp [posVars, ih y hy.1]

end ForProg

/-! ## Unfolding a single loop -/

/-- A loop is a fold of its body over the positions of the input. -/
lemma exec_loop_eq (w : List A) (d : Bool) (x : ℕ) (body : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) :
    ForProg.exec w (ForProg.loop d x body) pos bv
      = runList (fun s p => ForProg.exec w body (Function.update pos x p) s)
          (loopRange d w.length) bv :=
  exec_nest_cons w d x [] body pos bv

/-! ## Binding a free position variable -/

/-- Running a program once, with the position variable `y` bound to the first position of the
input: the Boolean variable `X` is raised before the loop and lowered after the first iteration,
so that the later iterations do nothing. -/
def firstOnly (X y : ℕ) (P : ForProg A B) : ForProg A B :=
  ForProg.seq (ForProg.assign X true)
    (ForProg.loop true y
      (ForProg.ite (ForTest.boolVar X) (ForProg.seq P (ForProg.assign X false)) ForProg.skip))

lemma allAtomic_firstOnly (X y : ℕ) (P : ForProg A B) (hP : P.AllAtomic) :
    (firstOnly X y P).AllAtomic :=
  ⟨trivial, trivial, ⟨hP, trivial⟩, trivial⟩

lemma freePos_firstOnly (X y : ℕ) (P : ForProg A B) :
    (firstOnly X y P).freePos = P.freePos.filter (fun z => !decide (z = y)) := by
  simp [firstOnly, ForTest.posVars]

lemma boolVars_firstOnly (X y : ℕ) (P : ForProg A B) (i : ℕ)
    (hi : i ∈ (firstOnly X y P).boolVars) : i = X ∨ i ∈ P.boolVars := by
  simp only [firstOnly, ForProg.boolVars, ForTest.boolVars, List.mem_append,
    List.mem_singleton, List.not_mem_nil, or_false] at hi
  tauto

/-- **The program bound at the first position.**  On a nonempty input, `firstOnly X y P` runs `P`
once, with `y` bound to the first position; it leaves the Boolean variables of `P` as `P` does. -/
lemma exec_firstOnly (w : List A) (X y : ℕ) (P : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool)
    (hw : 0 < w.length) :
    (ForProg.exec w (firstOnly X y P) pos bv).2
        = (ForProg.exec w P (Function.update pos y 0) (Function.update bv X true)).2 ∧
      ∀ i, i ≠ X →
        (ForProg.exec w (firstOnly X y P) pos bv).1 i
          = (ForProg.exec w P (Function.update pos y 0) (Function.update bv X true)).1 i := by
  classical
  set body : ForProg A B :=
    ForProg.ite (ForTest.boolVar X) (ForProg.seq P (ForProg.assign X false)) ForProg.skip
    with hbody
  set s0 : ℕ → Bool := Function.update bv X true with hs0
  have hs0X : s0 X = true := by simp [hs0]
  set step : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B :=
    fun s q => ForProg.exec w body (Function.update pos y q) s with hstep
  have hfirst : ForProg.exec w (firstOnly X y P) pos bv = runList step (List.range w.length) s0 := by
    show ForProg.exec w (ForProg.seq (ForProg.assign X true) (ForProg.loop true y body)) pos bv = _
    rw [exec_seq]
    have h1 : ForProg.exec w (ForProg.assign X true) pos bv = (s0, ([] : List B)) := rfl
    rw [h1, exec_loop_eq]
    simp [hstep]
  have hstep0 : step s0 0
      = (Function.update (ForProg.exec w P (Function.update pos y 0) s0).1 X false,
          (ForProg.exec w P (Function.update pos y 0) s0).2) := by
    show ForProg.exec w body (Function.update pos y 0) s0 = _
    rw [hbody, exec_ite_pos _ _ _ _ _ _ (show ForTest.Holds w (Function.update pos y 0) s0
      (ForTest.boolVar X) from hs0X), exec_seq]
    simp [ForProg.exec]
  obtain ⟨m, hm⟩ : ∃ m, w.length = m + 1 := ⟨w.length - 1, by omega⟩
  have hdead : ∀ q ∈ (List.range m).map Nat.succ, step (step s0 0).1 q = ((step s0 0).1, []) := by
    intro q _
    have hX' : (step s0 0).1 X = false := by rw [hstep0]; simp
    show ForProg.exec w body (Function.update pos y q) _ = _
    rw [hbody, exec_ite_neg _ _ _ _ _ _ (by
      show ¬ ((step s0 0).1 X = true)
      rw [hX']; simp)]
    rfl
  have hrun : runList step (List.range w.length) s0 = step s0 0 := by
    rw [hm, List.range_succ_eq_map]
    exact runList_head_dead step 0 _ s0 hdead
  rw [hfirst, hrun, hstep0]
  exact ⟨rfl, fun i hi => Function.update_of_ne hi _ _⟩

/-- Binding a list of position variables, each by its own loop, with the fresh Boolean flags
`F`, `F + 1`, ... -/
def bindVars (F : ℕ) : List ℕ → ForProg A B → ForProg A B
  | [], P => P
  | y :: ys, P => firstOnly F y (bindVars (F + 1) ys P)

lemma allAtomic_bindVars : ∀ (ys : List ℕ) (F : ℕ) (P : ForProg A B), P.AllAtomic →
    (bindVars F ys P).AllAtomic := by
  intro ys
  induction ys with
  | nil => intro F P hP; exact hP
  | cons y ys ih => intro F P hP; exact allAtomic_firstOnly _ _ _ (ih (F + 1) P hP)

lemma boolVars_bindVars : ∀ (ys : List ℕ) (F : ℕ) (P : ForProg A B) (i : ℕ),
    i ∈ (bindVars F ys P).boolVars → i ∈ P.boolVars ∨ F ≤ i := by
  intro ys
  induction ys with
  | nil => intro F P i h; exact Or.inl h
  | cons y ys ih =>
      intro F P i h
      rcases boolVars_firstOnly F y _ i h with h | h
      · exact Or.inr (by omega)
      · rcases ih (F + 1) P i h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by omega)

lemma freePos_bindVars : ∀ (ys : List ℕ) (F : ℕ) (P : ForProg A B) (z : ℕ),
    z ∈ (bindVars F ys P).freePos → z ∈ P.freePos ∧ z ∉ ys := by
  intro ys
  induction ys with
  | nil => intro F P z h; exact ⟨h, by simp⟩
  | cons y ys ih =>
      intro F P z h
      rw [bindVars, freePos_firstOnly, List.mem_filter] at h
      obtain ⟨hz, hzy⟩ := h
      obtain ⟨h1, h2⟩ := ih (F + 1) P z hz
      refine ⟨h1, ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨by simpa using hzy, h2⟩

/-- **Binding the free position variables.**  On a nonempty input, the program obtained by binding
a list of position variables computes the same output as the original one. -/
lemma exec_bindVars (w : List A) (hw : 0 < w.length) :
    ∀ (ys : List ℕ) (F : ℕ) (P : ForProg A B), (∀ i ∈ P.boolVars, i < F) →
      ∀ (pos : ℕ → ℕ), (∀ z, pos z = 0) → ∀ (bv : ℕ → Bool),
        (ForProg.exec w (bindVars F ys P) pos bv).2 = (ForProg.exec w P pos bv).2 := by
  intro ys
  induction ys with
  | nil => intro F P _ pos _ bv; rfl
  | cons y ys ih =>
      intro F P hP pos hpos bv
      have hupd : Function.update pos y 0 = pos := by
        funext z
        by_cases h : z = y
        · subst h; simp [hpos]
        · simp [Function.update_of_ne h]
      have hFP : F ∉ P.boolVars := fun hc => absurd (hP F hc) (lt_irrefl _)
      rw [bindVars, (exec_firstOnly w F y (bindVars (F + 1) ys P) pos bv hw).1, hupd,
        ih (F + 1) P (fun i hi => by have := hP i hi; omega) pos hpos (Function.update bv F true)]
      exact (exec_congr_bv w P pos (fun i => i ∈ P.boolVars) (fun i hi => hi)
        (Function.update bv F true) bv
        (fun i hi => Function.update_of_ne (by rintro rfl; exact hFP hi) _ _)).1

/-! ## Closing a program -/

lemma allAtomic_constProg : ∀ l : List C, (constProg l : ForProg A C).AllAtomic := by
  intro l
  induction l with
  | nil => trivial
  | cons c l ih => exact ⟨trivial, ih⟩

lemma freePos_constProg : ∀ l : List C, (constProg l : ForProg A C).freePos = [] := by
  intro l
  induction l with
  | nil => rfl
  | cons c l ih => simp [constProg, ih]

/-- The flag loop: it raises `E` if and only if the input is nonempty. -/
lemma exec_flagLoop (w : List A) (E : ℕ) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForProg.exec w (ForProg.loop true 0 (ForProg.assign E true) : ForProg A B) pos bv
      = (if w.length = 0 then bv else Function.update bv E true, []) := by
  classical
  rw [exec_loop_eq]
  simp only [loopRange_true]
  cases hn : w.length with
  | zero => simp
  | succ m =>
      rw [List.range_succ_eq_map,
        runList_head_dead _ 0 _ bv (fun q _ => by
          show ForProg.exec w (ForProg.assign E true) _ _ = _
          simp [ForProg.exec, Function.update_idem])]
      show (Function.update bv E true, ([] : List B)) = _
      simp

/-- **Closing a program.**  Every free position variable of `Q` is bound by a loop that runs only
at the first position of the input; the empty input, where those loops do nothing, is dealt with
by the constant program that outputs `Q.eval []`.  The Boolean variable `E` records whether the
input is nonempty, and `F`, `F + 1`, ... are the flags used to bind the variables. -/
noncomputable def closeProg (E F : ℕ) (Q : ForProg B C) : ForProg B C :=
  ForProg.seq (ForProg.loop true 0 (ForProg.assign E true))
    (ForProg.ite (ForTest.boolVar E) (bindVars F Q.posVars Q) (constProg (Q.eval [])))

lemma allAtomic_closeProg (E F : ℕ) (Q : ForProg B C) (hQ : Q.AllAtomic) :
    (closeProg E F Q).AllAtomic :=
  ⟨trivial, trivial, allAtomic_bindVars _ _ _ hQ, allAtomic_constProg _⟩

/-- The closed program has no free position variable. -/
lemma freePos_closeProg (E F : ℕ) (Q : ForProg B C) : (closeProg E F Q).freePos = [] := by
  classical
  have hb : (bindVars F Q.posVars Q).freePos = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr (fun z hz => ?_)
    obtain ⟨h1, h2⟩ := freePos_bindVars Q.posVars F Q z hz
    exact h2 (ForProg.freePos_subset_posVars Q z h1)
  simp [closeProg, hb, freePos_constProg, ForTest.posVars]

/-- **The closed program is equivalent to the original one.** -/
lemma eval_closeProg (E F : ℕ) (Q : ForProg B C) (hE : E ∉ Q.boolVars)
    (hF : ∀ i ∈ Q.boolVars, i < F) (v : List B) : (closeProg E F Q).eval v = Q.eval v := by
  classical
  show (ForProg.exec v (ForProg.seq _ _) (fun _ => 0) (fun _ => false)).2 = _
  rw [exec_seq, exec_flagLoop]
  by_cases hv : v.length = 0
  · simp only [if_pos hv, List.nil_append]
    have hEfalse : ¬ ForTest.Holds v (fun _ => 0) (fun _ : ℕ => false) (ForTest.boolVar E) := by
      simp [ForTest.Holds]
    rw [exec_ite_neg _ _ _ _ _ _ hEfalse, exec_constProg]
    have : v = [] := List.eq_nil_of_length_eq_zero hv
    rw [this]
  · simp only [if_neg hv, List.nil_append]
    have hEtrue : ForTest.Holds v (fun _ => 0)
        (Function.update (fun _ : ℕ => false) E true) (ForTest.boolVar E) := by
      show Function.update (fun _ : ℕ => false) E true E = true
      simp
    rw [exec_ite_pos _ _ _ _ _ _ hEtrue,
      exec_bindVars v (by omega) Q.posVars F Q hF (fun _ => 0) (fun _ => rfl)
        (Function.update (fun _ : ℕ => false) E true)]
    refine (exec_congr_bv v Q (fun _ => 0) (fun i => i ∈ Q.boolVars) (fun i hi => hi)
      (Function.update (fun _ : ℕ => false) E true) (fun _ => false)
      (fun i hi => Function.update_of_ne (by rintro rfl; exact hE hi) _ _)).1

end Lax194892Proofs.Transducers
