/-
Part D: for-transducers -- the trace of a nest of loops, and marking its output.

Two ingredients of the proof of Lemma `lem:for-closed-under-composition`.

The first one is the *trace* of a nest of loops: its output is the concatenation, over the tuples
of positions, of what the body produces at that tuple, in the Boolean state reached just before it
-- and that state is itself the state produced by the tuples that are lexicographically smaller,
which is what makes it computable by another nest of loops.  The tuples at which the body produces
a letter are the *events*, and they are in one-to-one, order-preserving correspondence with the
positions of the output string.

The second one is `Transducers.markOut`, the transformation that replaces every `output` of a
program by an assignment to a Boolean variable.  It is what lets a for-transducer observe the
output of another one: with the flag `fl` and a predicate `q` on letters, the flag ends up holding
the value of `q` on the last letter that was output.
-/
import Lax194892Proofs.Source.PartD.ForLex

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B C : Type}

/-! ## The trace of a fold over a sorted list -/

/-- The output of a fold over a repetition-free sorted list is the concatenation, over its
elements, of what the step produces at the state reached by the smaller elements. -/
lemma runList_out_of_sorted {α S D : Type} (step : S → α → S × List D) (r : α → α → Prop)
    (hirr : ∀ a, ¬ r a a) (hasymm : ∀ a b, r a b → ¬ r b a) :
    ∀ (as : List α), as.Pairwise r → ∀ s : S,
      (runList step as s).2
        = as.flatMap (fun a =>
            (step (runList step (as.filter (fun t => decide (r t a))) s).1 a).2) := by
  intro as
  induction as with
  | nil => intro _ s; rfl
  | cons a as ih =>
      intro hs s
      have hhead : (a :: as).filter (fun t => decide (r t a)) = [] := by
        rw [List.filter_cons_of_neg (by simp [hirr a])]
        refine List.filter_eq_nil_iff.mpr (fun t ht => ?_)
        simp only [decide_eq_true_eq]
        exact hasymm a t (List.rel_of_pairwise_cons hs ht)
      have htail : ∀ b ∈ as, (a :: as).filter (fun t => decide (r t b))
          = a :: as.filter (fun t => decide (r t b)) := by
        intro b hb
        exact List.filter_cons_of_pos (by simp [List.rel_of_pairwise_cons hs hb])
      rw [runList_cons, List.flatMap_cons, hhead]
      show ((step s a).2 ++ _) = ((step _ a).2 ++ _)
      congr 1
      rw [ih hs.of_cons (step s a).1]
      refine List.flatMap_congr (fun b hb => ?_)
      rw [htail b hb, runList_cons]

/-! ## The trace of a nest of loops -/

/-- The Boolean state of a nest of loops just before the tuple `z`: the state produced by the
tuples that come before `z`. -/
noncomputable def stateBefore (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (z : List ℕ) : ℕ → Bool :=
  (runList (fun s t => ForProg.exec w p (setTuple L t pos) s)
    ((tuplesOf L w.length).filter (fun t => decide (LexLt (L.map Prod.fst) t z))) bv).1

/-- What a nest of loops outputs at the tuple `z`. -/
noncomputable def outAt (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (z : List ℕ) : List B :=
  (ForProg.exec w p (setTuple L z pos) (stateBefore w L p pos bv z)).2

/-- **The trace of a nest of loops.** -/
lemma nest_out_trace (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) :
    (ForProg.exec w (ForProg.nestLoops L p) pos bv).2
      = (tuplesOf L w.length).flatMap (outAt w L p pos bv) := by
  rw [exec_nestLoops]
  exact runList_out_of_sorted _ (LexLt (L.map Prod.fst)) (lexLt_irrefl _) (lexLt_asymm _)
    _ (sorted_tuplesOf L w.length) bv

/-- The tuples at which the nest of loops produces a letter. -/
noncomputable def events (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) : List (List ℕ) :=
  (tuplesOf L w.length).filter (fun z => decide (outAt w L p pos bv z ≠ []))

lemma mem_events {w : List A} {L : List (Bool × ℕ)} {p : ForProg A B} {pos : ℕ → ℕ}
    {bv : ℕ → Bool} {z : List ℕ} :
    z ∈ events w L p pos bv ↔ z ∈ tuplesOf L w.length ∧ outAt w L p pos bv z ≠ [] := by
  simp [events]

/-- Only the tuples where a letter is produced contribute to the output. -/
lemma flatMap_eq_filter {α D : Type} (f : α → List D) :
    ∀ l : List α, l.flatMap f = (l.filter (fun a => decide (f a ≠ []))).flatMap f := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : f a = []
      · rw [List.filter_cons_of_neg (by simp [h]), List.flatMap_cons, h, List.nil_append, ih]
      · rw [List.filter_cons_of_pos (by simp [h]), List.flatMap_cons, List.flatMap_cons, ih]

lemma nest_out_events (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) :
    (ForProg.exec w (ForProg.nestLoops L p) pos bv).2
      = (events w L p pos bv).flatMap (outAt w L p pos bv) := by
  rw [nest_out_trace]
  exact flatMap_eq_filter _ _

lemma events_sorted (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) : (events w L p pos bv).Pairwise (LexLt (L.map Prod.fst)) :=
  (sorted_tuplesOf L w.length).filter _

lemma events_subset {w : List A} {L : List (Bool × ℕ)} {p : ForProg A B} {pos : ℕ → ℕ}
    {bv : ℕ → Bool} {z : List ℕ} (hz : z ∈ events w L p pos bv) : z ∈ tuplesOf L w.length :=
  (mem_events.mp hz).1

/-! ## Reading the output string off the events -/

/-- A concatenation of one-letter blocks. -/
lemma length_flatMap_singleton {α D : Type} (f : α → List D) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = 1) → (l.flatMap f).length = l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      intro h
      rw [List.flatMap_cons, List.length_append, ih (fun b hb => h b (by simp [hb])),
        h a (by simp), List.length_cons]
      omega

lemma getElem?_flatMap_singleton {α D : Type} (f : α → List D) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = 1) → ∀ (q : ℕ) (hq : q < l.length),
      (l.flatMap f)[q]? = (f l[q]).head? := by
  intro l
  induction l with
  | nil => intro _ q hq; simp at hq
  | cons a l ih =>
      intro h q hq
      have ha : (f a).length = 1 := h a (by simp)
      obtain ⟨c, hc⟩ : ∃ c, f a = [c] := by
        cases hfa : f a with
        | nil => rw [hfa] at ha; simp at ha
        | cons c t =>
            cases t with
            | nil => exact ⟨c, rfl⟩
            | cons c' t' => rw [hfa] at ha; simp at ha
      cases q with
      | zero => simp [List.flatMap_cons, hc]
      | succ q =>
          simp only [List.length_cons] at hq
          rw [List.flatMap_cons, hc, List.cons_append]
          simp only [List.getElem?_cons_succ, List.getElem_cons_succ]
          exact ih (fun b hb => h b (by simp [hb])) q (by omega)

/-! ## Marking the output of a program -/

/-- Replacing every `output c` of a program by the assignment of `q c` to the Boolean variable
`fl`.  The resulting program produces no output; the flag records the value of `q` on the last
letter that the original program would have produced. -/
def markOut (fl : ℕ) (q : B → Bool) : ForProg A B → ForProg A C
  | ForProg.skip => ForProg.skip
  | ForProg.output c => ForProg.assign fl (q c)
  | ForProg.assign i v => ForProg.assign i v
  | ForProg.seq P Q => ForProg.seq (markOut fl q P) (markOut fl q Q)
  | ForProg.ite t P Q => ForProg.ite t (markOut fl q P) (markOut fl q Q)
  | ForProg.loop d x P => ForProg.loop d x (markOut fl q P)

/-- The value that the flag of `Transducers.markOut` ends up holding. -/
def lastFlag (init : Bool) (q : B → Bool) (out : List B) : Bool :=
  out.foldl (fun _ c => q c) init

@[simp] lemma lastFlag_nil (init : Bool) (q : B → Bool) : lastFlag init q [] = init := rfl

@[simp] lemma lastFlag_append (init : Bool) (q : B → Bool) (l₁ l₂ : List B) :
    lastFlag init q (l₁ ++ l₂) = lastFlag (lastFlag init q l₁) q l₂ := by
  simp [lastFlag, List.foldl_append]

@[simp] lemma lastFlag_single (init : Bool) (q : B → Bool) (c : B) :
    lastFlag init q [c] = q c := rfl

lemma posVars_markOut (fl : ℕ) (q : B → Bool) :
    ∀ p : ForProg A B, (markOut (C := C) fl q p).posVars = p.posVars := by
  intro p
  induction p with
  | skip => rfl
  | output c => rfl
  | assign i v => rfl
  | seq P Q ihP ihQ => simp [markOut, ForProg.posVars, ihP, ihQ]
  | ite t P Q ihP ihQ => simp [markOut, ForProg.posVars, ihP, ihQ]
  | loop d x P ih => simp [markOut, ForProg.posVars, ih]

lemma boolVars_markOut (fl : ℕ) (q : B → Bool) :
    ∀ (p : ForProg A B) (i : ℕ), i ∈ (markOut (C := C) fl q p).boolVars →
      i ∈ p.boolVars ∨ i = fl := by
  intro p
  induction p with
  | skip => simp [markOut, ForProg.boolVars]
  | output c => simp [markOut, ForProg.boolVars]
  | assign j v => simp [markOut, ForProg.boolVars]
  | seq P Q ihP ihQ =>
      intro i hi
      simp only [markOut, ForProg.boolVars, List.mem_append] at hi ⊢
      rcases hi with h | h
      · rcases ihP i h with h' | h' <;> tauto
      · rcases ihQ i h with h' | h' <;> tauto
  | ite t P Q ihP ihQ =>
      intro i hi
      simp only [markOut, ForProg.boolVars, List.mem_append] at hi ⊢
      rcases hi with (h | h) | h
      · tauto
      · rcases ihP i h with h' | h' <;> tauto
      · rcases ihQ i h with h' | h' <;> tauto
  | loop d x P ih =>
      intro i hi
      simp only [markOut, ForProg.boolVars] at hi ⊢
      exact ih i hi

lemma loopFree_markOut (fl : ℕ) (q : B → Bool) :
    ∀ p : ForProg A B, p.LoopFree → (markOut (C := C) fl q p).LoopFree := by
  intro p
  induction p with
  | skip => exact fun _ => trivial
  | output c => exact fun _ => trivial
  | assign i v => exact fun _ => trivial
  | seq P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | ite t P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | loop d x P ih => exact fun h => h.elim

/-- **The marked program computes the flag.**  It produces no output, it has the same effect as
the original program on every other Boolean variable, and it leaves in `fl` the value of `q` on
the last letter that the original program produces. -/
lemma markOut_spec (w : List A) (fl : ℕ) (q : B → Bool) :
    ∀ (p : ForProg A B), fl ∉ p.boolVars → ∀ (pos : ℕ → ℕ) (bv bv' : ℕ → Bool),
      (∀ i, i ≠ fl → bv i = bv' i) →
      (ForProg.exec w (markOut (C := C) fl q p) pos bv').2 = [] ∧
        (∀ i, i ≠ fl → (ForProg.exec w (markOut (C := C) fl q p) pos bv').1 i
          = (ForProg.exec w p pos bv).1 i) ∧
        (ForProg.exec w (markOut (C := C) fl q p) pos bv').1 fl
          = lastFlag (bv' fl) q (ForProg.exec w p pos bv).2 := by
  intro p
  induction p with
  | skip => intro _ pos bv bv' h; exact ⟨rfl, fun i hi => (h i hi).symm, rfl⟩
  | output c =>
      intro _ pos bv bv' h
      refine ⟨rfl, fun i hi => ?_, ?_⟩
      · show Function.update bv' fl (q c) i = bv i
        rw [Function.update_of_ne hi]
        exact (h i hi).symm
      · show Function.update bv' fl (q c) fl = lastFlag (bv' fl) q [c]
        simp
  | assign j v =>
      intro hfl pos bv bv' h
      have hjfl : j ≠ fl := by
        intro hc
        exact hfl (by simp [ForProg.boolVars, hc])
      refine ⟨rfl, fun i hi => ?_, ?_⟩
      · show Function.update bv' j v i = Function.update bv j v i
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
          exact (h i hi).symm
      · show Function.update bv' j v fl = _
        rw [Function.update_of_ne (Ne.symm hjfl)]
        rfl
  | seq P Q ihP ihQ =>
      intro hfl pos bv bv' h
      simp only [ForProg.boolVars, List.mem_append, not_or] at hfl
      obtain ⟨h1, h2, h3⟩ := ihP hfl.1 pos bv bv' h
      obtain ⟨h4, h5, h6⟩ := ihQ hfl.2 pos _ _ (fun i hi => (h2 i hi).symm)
      refine ⟨by show _ ++ _ = []; rw [h1, h4]; rfl, fun i hi => ?_, ?_⟩
      · show (ForProg.exec w (markOut fl q Q) pos _).1 i = _
        exact h5 i hi
      · show (ForProg.exec w (markOut fl q Q) pos _).1 fl = _
        rw [h6, h3]
        show _ = lastFlag (bv' fl) q ((ForProg.exec w P pos bv).2 ++ _)
        rw [lastFlag_append]
  | ite t P Q ihP ihQ =>
      intro hfl pos bv bv' h
      simp only [ForProg.boolVars, List.mem_append, not_or] at hfl
      have ht : ForTest.Holds w pos bv t ↔ ForTest.Holds w pos bv' t :=
        ForTest.holds_congr w t pos pos bv bv' (fun _ _ => rfl) (fun i hi => h i (fun hc => by
          exact hfl.1.1 (hc ▸ hi)))
      simp only [markOut]
      by_cases hT : ForTest.Holds w pos bv t
      · rw [exec_ite_pos _ _ _ _ _ _ hT, exec_ite_pos _ _ _ _ _ _ (ht.mp hT)]
        exact ihP hfl.1.2 pos bv bv' h
      · rw [exec_ite_neg _ _ _ _ _ _ hT, exec_ite_neg _ _ _ _ _ _ (fun hc => hT (ht.mpr hc))]
        exact ihQ hfl.2 pos bv bv' h
  | loop d x P ih =>
      intro hfl pos bv bv' h
      simp only [ForProg.boolVars] at hfl
      simp only [markOut, ForProg.exec, forLoopRun_eq_runList]
      -- the two folds are run in step
      have key : ∀ (l : List ℕ) (s s' : ℕ → Bool), (∀ i, i ≠ fl → s i = s' i) →
          (runList (fun t p' => ForProg.exec w (markOut (C := C) fl q P)
              (Function.update pos x p') t) l s').2 = [] ∧
            (∀ i, i ≠ fl → (runList (fun t p' => ForProg.exec w (markOut (C := C) fl q P)
              (Function.update pos x p') t) l s').1 i
              = (runList (fun t p' => ForProg.exec w P (Function.update pos x p') t) l s).1 i) ∧
            (runList (fun t p' => ForProg.exec w (markOut (C := C) fl q P)
              (Function.update pos x p') t) l s').1 fl
              = lastFlag (s' fl) q
                (runList (fun t p' => ForProg.exec w P (Function.update pos x p') t) l s).2 := by
        intro l
        induction l with
        | nil => intro s s' hss; exact ⟨rfl, fun i hi => (hss i hi).symm, rfl⟩
        | cons a l ihl =>
            intro s s' hss
            obtain ⟨h1, h2, h3⟩ := ih hfl (Function.update pos x a) s s' hss
            obtain ⟨h4, h5, h6⟩ := ihl _ _ (fun i hi => (h2 i hi).symm)
            refine ⟨?_, ?_, ?_⟩
            · simp only [runList_cons, h1, h4, List.append_nil]
            · intro i hi
              simp only [runList_cons]
              exact h5 i hi
            · simp only [runList_cons]
              rw [lastFlag_append, ← h3]
              exact h6
      exact key _ bv bv' h

end Lax194892Proofs.Transducers
