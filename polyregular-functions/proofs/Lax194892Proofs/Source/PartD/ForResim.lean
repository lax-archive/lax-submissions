/-
Part D: for-transducers -- re-simulating a nest of loops at a given tuple.

In the proof of Lemma `lem:for-closed-under-composition`, the outer for-transducer must be able to
ask questions about the output of the inner one: at the tuple of positions held in a block of
position variables, does the inner nest of loops produce a letter, and does that letter satisfy a
given property?  Since the body of the inner nest reads Boolean variables whose values depend on
all the earlier iterations, this cannot be answered by a test; it is answered by a program,
`Transducers.resim`, which re-runs the inner nest over the tuples that come before the given one --
discarding the output -- and then evaluates the body at the given tuple, recording the answer in a
Boolean flag.
-/
import Lax194892Proofs.Source.PartD.ForPrenexTop
import Lax194892Proofs.Source.PartD.ForTrace

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B C : Type}

/-! ## A fold that only computes -/

/-- A fold whose steps produce no output and follow another fold up to a relation. -/
lemma runList_sim_silent {α S₁ S₂ D₁ D₂ : Type} (step₁ : S₁ → α → S₁ × List D₁)
    (step₂ : S₂ → α → S₂ × List D₂) (R : S₁ → S₂ → Prop) :
    ∀ (as : List α) (s₁ : S₁) (s₂ : S₂), R s₁ s₂ →
      (∀ t₁ t₂ a, a ∈ as → R t₁ t₂ → R (step₁ t₁ a).1 (step₂ t₂ a).1) →
      (∀ t₁ a, a ∈ as → (step₁ t₁ a).2 = []) →
      (runList step₁ as s₁).2 = [] ∧ R (runList step₁ as s₁).1 (runList step₂ as s₂).1 := by
  intro as
  induction as with
  | nil => intro s₁ s₂ hs _ _; exact ⟨rfl, hs⟩
  | cons a as ih =>
      intro s₁ s₂ hs hstep hout
      obtain ⟨h1, h2⟩ := ih (step₁ s₁ a).1 (step₂ s₂ a).1 (hstep s₁ s₂ a (by simp) hs)
        (fun t₁ t₂ b hb => hstep t₁ t₂ b (by simp [hb])) (fun t₁ b hb => hout t₁ b (by simp [hb]))
      refine ⟨?_, ?_⟩
      · simp only [runList_cons, hout s₁ a (by simp), h1, List.append_nil]
      · simpa only [runList_cons] using h2

/-! ## Setting a list of Boolean variables to false -/

/-- The program setting a list of Boolean variables to `false`. -/
def clearBools : List ℕ → ForProg A C
  | [] => ForProg.skip
  | i :: l => ForProg.seq (ForProg.assign i false) (clearBools l)

lemma exec_clearBools (w : List A) : ∀ (l : List ℕ) (pos : ℕ → ℕ) (bv : ℕ → Bool),
    (ForProg.exec w (clearBools l : ForProg A C) pos bv).2 = [] ∧
      ∀ i, (ForProg.exec w (clearBools l : ForProg A C) pos bv).1 i
        = if i ∈ l then false else bv i := by
  intro l
  induction l with
  | nil => intro pos bv; exact ⟨rfl, fun i => by show bv i = _; simp⟩
  | cons j l ih =>
      intro pos bv
      obtain ⟨h1, h2⟩ := ih pos (Function.update bv j false)
      refine ⟨?_, fun i => ?_⟩
      · show (ForProg.exec w (clearBools l : ForProg A C) pos (Function.update bv j false)).2 = []
        exact h1
      show (ForProg.exec w (clearBools l : ForProg A C) pos (Function.update bv j false)).1 i = _
      rw [h2 i]
      by_cases hij : i = j
      · subst hij; simp
      · by_cases hil : i ∈ l <;> simp [hij, hil]

/-! ## Renaming a tuple of position variables -/

/-- The renaming that sends the `j`-th variable of `X` to the `j`-th variable of `Y`. -/
def renTuple : List ℕ → List ℕ → ℕ → ℕ
  | x :: xs, y :: ys => fun i => if i = x then y else renTuple xs ys i
  | _, _ => id

lemma renTuple_of_not_mem : ∀ (X Y : List ℕ) (i : ℕ), i ∉ X → renTuple X Y i = i := by
  intro X
  induction X with
  | nil => intro Y i _; cases Y <;> rfl
  | cons x X ih =>
      intro Y i hi
      cases Y with
      | nil => rfl
      | cons y Y =>
          simp only [List.mem_cons, not_or] at hi
          show (if i = x then y else renTuple X Y i) = i
          rw [if_neg hi.1]
          exact ih Y i hi.2

/-- The renaming, followed by the ambient valuation, gives the tuple held in `Y`. -/
lemma renTuple_setTuple : ∀ (L : List (Bool × ℕ)) (Y : List ℕ), (L.map Prod.snd).Nodup →
    Y.length = L.length → ∀ (pos : ℕ → ℕ) (i : ℕ), i ∈ L.map Prod.snd →
      pos (renTuple (L.map Prod.snd) Y i) = setTuple L (Y.map pos) (fun _ => 0) i := by
  intro L
  induction L with
  | nil => intro Y _ _ pos i hi; simp at hi
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      intro Y hnd hlen pos i hi
      cases Y with
      | nil => simp at hlen
      | cons y Y =>
        simp only [List.map_cons, List.nodup_cons] at hnd
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [List.map_cons, List.mem_cons] at hi
        by_cases hix : i = x
        · subst hix
          show pos (if i = i then y else _) = _
          rw [if_pos rfl]
          simp only [List.map_cons, setTuple_cons]
          rw [setTuple_of_not_mem L (Y.map pos) _ hnd.1, Function.update_self]
        · have hiL : i ∈ L.map Prod.snd := by rcases hi with h | h; · exact absurd h hix
                                              · exact h
          show pos (if i = x then y else renTuple (L.map Prod.snd) Y i) = _
          rw [if_neg hix]
          simp only [List.map_cons, setTuple_cons]
          rw [setTuple_mem_eq L (Y.map pos) (by simpa using hlen) _ (fun _ => 0) hiL]
          exact ih Y hnd.2 hlen pos i hiL

/-- A tuple gives the loop variables the values of its entries. -/
lemma map_setTuple : ∀ (L : List (Bool × ℕ)) (t : List ℕ), (L.map Prod.snd).Nodup →
    t.length = L.length → ∀ pos : ℕ → ℕ, (L.map Prod.snd).map (setTuple L t pos) = t := by
  intro L
  induction L with
  | nil => intro t _ hlen _; simp at hlen; simp [hlen]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      intro t hnd hlen pos
      cases t with
      | nil => simp at hlen
      | cons c t =>
        simp only [List.map_cons, List.nodup_cons] at hnd
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [List.map_cons, setTuple_cons]
        refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
        · rw [setTuple_of_not_mem L t _ hnd.1, Function.update_self]
        · exact ih t hnd.2 hlen _

/-! ## The re-simulation program -/

/-- **Re-simulating the inner nest at the tuple held in `Y`.**  The nest of loops `L` with body
`p` is re-run over the tuples that come before the one held in the position variables `Y`, with the
output discarded and recorded in the scratch flag `fl'`; then the body is evaluated at the tuple
held in `Y`, and the flag `fl` records the value of `q` on the letter it produces (and stays
`false` if it produces none). -/
def resim (L : List (Bool × ℕ)) (p : ForProg A B) (Y : List ℕ) (fl fl' : ℕ) (q : B → Bool) :
    ForProg A C :=
  ForProg.seq (clearBools (fl :: fl' :: p.boolVars))
    (ForProg.seq
      (ForProg.nestLoops L
        (ForProg.ite (lexLtTest (L.map Prod.fst) (L.map Prod.snd) Y)
          (markOut fl' (fun _ => true) p) ForProg.skip))
      (ForProg.renamePos (renTuple (L.map Prod.snd) Y) (markOut fl q p)))

section

variable (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (Y : List ℕ) (fl fl' : ℕ)
  (q : B → Bool)

/-- The re-simulating nest reaches the Boolean state of the inner nest just before the tuple held
in `Y`. -/
lemma resim_nest_spec (hnd : (L.map Prod.snd).Nodup) (hfl'p : fl' ∉ p.boolVars) (hYX : ∀ y ∈ Y, y ∉ L.map Prod.snd) (pos : ℕ → ℕ) (bv : ℕ → Bool)
    (hpos0 : ∀ i, i ∉ L.map Prod.snd → i ∈ p.posVars → pos i = 0)
    (hbv : ∀ i ∈ p.boolVars, bv i = false) :
    (ForProg.exec w (ForProg.nestLoops L
        (ForProg.ite (lexLtTest (L.map Prod.fst) (L.map Prod.snd) Y)
          (markOut (C := C) fl' (fun _ => true) p) ForProg.skip)) pos bv).2 = [] ∧
      (∀ i ∈ p.boolVars, (ForProg.exec w (ForProg.nestLoops L
          (ForProg.ite (lexLtTest (L.map Prod.fst) (L.map Prod.snd) Y)
            (markOut (C := C) fl' (fun _ => true) p) ForProg.skip)) pos bv).1 i
        = stateBefore w L p (fun _ => 0) (fun _ => false) (Y.map pos) i) ∧
      (∀ i, i ≠ fl' → i ∉ p.boolVars → (ForProg.exec w (ForProg.nestLoops L
          (ForProg.ite (lexLtTest (L.map Prod.fst) (L.map Prod.snd) Y)
            (markOut (C := C) fl' (fun _ => true) p) ForProg.skip)) pos bv).1 i = bv i) := by
  classical
  have hposeq : ∀ t ∈ tuplesOf L w.length, (L.map Prod.snd).map (setTuple L t pos) = t :=
    fun t ht => map_setTuple L t hnd (length_of_mem_tuplesOf L w.length ht) pos
  have hYeq : ∀ t : List ℕ, Y.map (setTuple L t pos) = Y.map pos := by
    intro t
    refine List.map_congr_left (fun y hy => ?_)
    exact setTuple_of_not_mem L t pos (hYX y hy)
  have htest : ∀ (t : List ℕ), t ∈ tuplesOf L w.length → ∀ s : ℕ → Bool,
      (ForTest.Holds w (setTuple L t pos) s
        (lexLtTest (L.map Prod.fst) (L.map Prod.snd) Y : ForTest A)
        ↔ LexLt (L.map Prod.fst) t (Y.map pos)) := by
    intro t ht s
    rw [holds_lexLtTest, hposeq t ht, hYeq t]
  -- only the tuples before the one held in `Y` do anything
  rw [exec_nestLoops]
  rw [runList_filter _ (fun t => decide (LexLt (L.map Prod.fst) t (Y.map pos))) _ _ ?_]
  · -- on the remaining tuples the body is run
    rw [runList_congr_mem _ (fun s t => ForProg.exec w (markOut (C := C) fl' (fun _ => true) p)
      (setTuple L t pos) s) _ _ ?_]
    · -- compare with the reference run
      have hsim := runList_sim_silent
        (fun (s : ℕ → Bool) (t : List ℕ) => ForProg.exec w
          (markOut (C := C) fl' (fun _ => true) p) (setTuple L t pos) s)
        (fun (s : ℕ → Bool) (t : List ℕ) => ForProg.exec w p (setTuple L t (fun _ => 0)) s)
        (fun s s' => (∀ i ∈ p.boolVars, s i = s' i) ∧ ∀ i, i ≠ fl' → i ∉ p.boolVars → s i = bv i)
        ((tuplesOf L w.length).filter
          (fun t => decide (LexLt (L.map Prod.fst) t (Y.map pos)))) bv (fun _ => false)
        ⟨fun i hi => hbv i hi, fun i _ _ => rfl⟩ ?_ ?_
      · refine ⟨hsim.1, fun i hi => (hsim.2.1 i hi), fun i hi hi' => hsim.2.2 i hi hi'⟩
      · -- the step preserves the relation
        rintro s₁ s₂ t ht ⟨hR, hR'⟩
        have hmem : t ∈ tuplesOf L w.length := List.mem_of_mem_filter ht
        have hpp : ForProg.exec w p (setTuple L t pos) s₁
            = ForProg.exec w p (setTuple L t (fun _ => 0)) s₁ := by
          refine ForProg.exec_congr_pos w p _ _ _ (fun i hi => ?_)
          by_cases hiX : i ∈ L.map Prod.snd
          · exact setTuple_mem_eq L t (length_of_mem_tuplesOf L w.length hmem) _ _ hiX
          · rw [setTuple_of_not_mem L t _ hiX, setTuple_of_not_mem L t _ hiX, hpos0 i hiX hi]
        have hbvcongr := exec_congr_bv w p (setTuple L t (fun _ => 0))
          (fun i => i ∈ p.boolVars) (fun i hi => hi) s₁ s₂ hR
        have hmark := markOut_spec (C := C) w fl' (fun _ => true) p hfl'p (setTuple L t pos)
          s₁ s₁ (fun _ _ => rfl)
        refine ⟨fun i hi => ?_, fun i hi hi' => ?_⟩
        · rw [hmark.2.1 i (fun hc => hfl'p (hc ▸ hi)), hpp]
          exact hbvcongr.2 i hi
        · by_cases hifl : i = fl'
          · exact absurd hifl hi
          · rw [hmark.2.1 i hifl, hpp]
            rw [ForProg.exec_bv_unchanged w p _ s₁ hi']
            exact hR' i hi hi'
      · -- the step produces no output
        intro s t _
        exact (markOut_spec (C := C) w fl' (fun _ => true) p hfl'p (setTuple L t pos) s s
          (fun _ _ => rfl)).1
    · intro s t ht
      have hmem : t ∈ tuplesOf L w.length := List.mem_of_mem_filter ht
      have hlt : LexLt (L.map Prod.fst) t (Y.map pos) := by
        have := List.of_mem_filter ht
        simpa using this
      exact exec_ite_pos _ _ _ _ _ _ ((htest t hmem s).mpr hlt)
  · intro t ht hfalse s
    have hnlt : ¬ LexLt (L.map Prod.fst) t (Y.map pos) := by simpa using hfalse
    exact exec_ite_neg _ _ _ _ _ _ (fun hc => hnlt ((htest t ht s).mp hc))

/-- **The re-simulation answers the question.**  The flag `fl` ends up saying whether the inner
nest produces, at the tuple held in `Y`, a letter satisfying `q`. -/
lemma resim_spec (hp : p.LoopFree) (hnd : (L.map Prod.snd).Nodup) (hlen : Y.length = L.length)
    (hflp : fl ∉ p.boolVars) (hfl'p : fl' ∉ p.boolVars) (hff : fl ≠ fl')
    (hYX : ∀ y ∈ Y, y ∉ L.map Prod.snd) (pos : ℕ → ℕ) (bv : ℕ → Bool)
    (hpos0 : ∀ i, i ∉ L.map Prod.snd → i ∈ p.posVars → pos i = 0) :
    (ForProg.exec w (resim (C := C) L p Y fl fl' q) pos bv).2 = [] ∧
      (∀ i, i ≠ fl → i ≠ fl' → i ∉ p.boolVars →
        (ForProg.exec w (resim (C := C) L p Y fl fl' q) pos bv).1 i = bv i) ∧
      (ForProg.exec w (resim (C := C) L p Y fl fl' q) pos bv).1 fl
        = lastFlag false q (outAt w L p (fun _ => 0) (fun _ => false) (Y.map pos)) := by
  classical
  rw [resim, exec_seq, exec_seq]
  obtain ⟨hc1, hc2⟩ := exec_clearBools (C := C) w (fl :: fl' :: p.boolVars) pos bv
  set s₀ : ℕ → Bool := (ForProg.exec w (clearBools (fl :: fl' :: p.boolVars) : ForProg A C)
    pos bv).1 with hs₀
  have hs₀fl : s₀ fl = false := by rw [hc2 fl]; simp
  have hs₀fl' : s₀ fl' = false := by rw [hc2 fl']; simp
  have hs₀p : ∀ i ∈ p.boolVars, s₀ i = false := by
    intro i hi; rw [hc2 i]; simp [hi]
  have hs₀other : ∀ i, i ≠ fl → i ≠ fl' → i ∉ p.boolVars → s₀ i = bv i := by
    intro i h1 h2 h3; rw [hc2 i]; simp [h1, h2, h3]
  obtain ⟨hn1, hn2, hn3⟩ := resim_nest_spec (C := C) w L p Y fl' hnd hfl'p hYX pos s₀
    hpos0 hs₀p
  set s₁ : ℕ → Bool := (ForProg.exec w (ForProg.nestLoops L
      (ForProg.ite (lexLtTest (L.map Prod.fst) (L.map Prod.snd) Y)
        (markOut (C := C) fl' (fun _ => true) p) ForProg.skip)) pos s₀).1 with hs₁
  -- the last step: evaluating the body at the tuple held in `Y`
  have hren : ForProg.exec w (ForProg.renamePos (renTuple (L.map Prod.snd) Y)
        (markOut (C := C) fl q p)) pos s₁
      = ForProg.exec w (markOut (C := C) fl q p)
        (fun i => pos (renTuple (L.map Prod.snd) Y i)) s₁ :=
    ForProg.exec_renamePos w _ _ (loopFree_markOut fl q p hp) pos s₁
  have hposren : ForProg.exec w p (fun i => pos (renTuple (L.map Prod.snd) Y i)) s₁
      = ForProg.exec w p (setTuple L (Y.map pos) (fun _ => 0)) s₁ := by
    refine ForProg.exec_congr_pos w p _ _ _ (fun i hi => ?_)
    by_cases hiX : i ∈ L.map Prod.snd
    · exact renTuple_setTuple L Y hnd hlen pos i hiX
    · rw [renTuple_of_not_mem (L.map Prod.snd) Y i hiX, setTuple_of_not_mem L _ _ hiX,
        hpos0 i hiX hi]
  have houts : (ForProg.exec w p (fun i => pos (renTuple (L.map Prod.snd) Y i)) s₁).2
      = outAt w L p (fun _ => 0) (fun _ => false) (Y.map pos) := by
    rw [hposren]
    exact (exec_congr_bv w p (setTuple L (Y.map pos) (fun _ => 0)) (fun i => i ∈ p.boolVars)
      (fun i hi => hi) s₁ (stateBefore w L p (fun _ => 0) (fun _ => false) (Y.map pos))
      (fun i hi => hn2 i hi)).1
  have hs₁fl : s₁ fl = false := by rw [hn3 fl hff hflp, hs₀fl]
  have hmark := markOut_spec (C := C) w fl q p hflp
    (fun i => pos (renTuple (L.map Prod.snd) Y i)) s₁ s₁ (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_⟩
  · rw [hc1, hn1, hren, hmark.1]
    rfl
  · intro i h1 h2 h3
    rw [hren, hmark.2.1 i h1, ForProg.exec_bv_unchanged w p _ s₁ h3,
      hn3 i h2 h3, hs₀other i h1 h2 h3]
  · rw [hren, hmark.2.2, hs₁fl, houts]

end

end Lax194892Proofs.Transducers
