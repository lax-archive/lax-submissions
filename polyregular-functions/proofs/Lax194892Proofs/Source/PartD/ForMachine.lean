/-
Part D: for-transducers -- a small machine language that compiles into for-programs.

Writing a for-program by hand and computing its semantics is painful, because the Boolean
variables of a for-program are an unstructured family of bits and its conditionals test one
atomic property at a time.  This file introduces a machine language `Transducers.MProg` whose
programs manipulate a *state* taken from an arbitrary finite type `Q`, and which is compiled into
a for-program by `Transducers.MProg.compile`: the state is stored in Boolean variables, and an
action of the machine becomes a conditional that first determines the state, the letters under
the (at most two) position variables that the action looks at, and their relative order.

The main result of the file is `Transducers.isForTransducer_of_mprog`: a function computed by a
machine program is computed by a for-transducer.  It is through this lemma that the prime
polyregular functions -- rational functions, map reverse, map duplicate and marked squaring --
are shown to be computed by for-transducers, in `RequestProject/PartD/ForPrimes.lean`.
-/
import Lax194892Proofs.Source.PartD.ForAtom

namespace Lax194892Proofs.Transducers

open scoped Classical

/-! ## Encoding a finite state space by Boolean variables -/

/-- An encoding of the states of a machine by the values of the Boolean variables
`0, …, n-1` of a for-program, in which the initial state is encoded by all bits false. -/
structure BoolEnc (Q : Type) (q₀ : Q) where
  /-- The number of Boolean variables used. -/
  n : ℕ
  /-- The bits of a state. -/
  bits : Q → ℕ → Bool
  /-- The first `n` bits determine the state. -/
  inj : ∀ q q' : Q, (∀ i, i < n → bits q i = bits q' i) → q = q'
  /-- The initial state is encoded by all bits false. -/
  init_false : ∀ i, bits q₀ i = false

/-- Every finite state space with a distinguished initial state has an encoding. -/
lemma nonempty_boolEnc {Q : Type} [Finite Q] (q₀ : Q) : Nonempty (BoolEnc Q q₀) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Q
  refine ⟨{ n := n
            bits := fun q i => decide (q ≠ q₀ ∧ (e q : ℕ) = i)
            inj := ?_
            init_false := ?_ }⟩
  · intro q q' h
    by_cases hq : q = q₀
    · by_cases hq' : q' = q₀
      · rw [hq, hq']
      · exfalso
        have h2 := h (e q' : ℕ) (e q').isLt
        simp [hq, hq'] at h2
    · by_cases hq' : q' = q₀
      · exfalso
        have h2 := h (e q : ℕ) (e q).isLt
        simp [hq, hq'] at h2
      · have h2 := h (e q : ℕ) (e q).isLt
        simp [hq, hq'] at h2
        have hfin : e q' = e q := Fin.ext (by omega)
        exact (e.injective hfin).symm
  · intro i; simp

namespace BoolEnc

variable {A B Q : Type} {q₀ : Q} (E : BoolEnc Q q₀)

/-- The Boolean valuation obtained by writing the state `q` into the first `E.n` variables. -/
def repOf (q : Q) (bv : ℕ → Bool) : ℕ → Bool := fun i => if i < E.n then E.bits q i else bv i

lemma repOf_init : E.repOf q₀ (fun _ => false) = fun _ => false := by
  funext i
  by_cases hi : i < E.n <;> simp [repOf, hi, E.init_false]

/-- The test that the first `k` Boolean variables hold the bits of the state `q`. -/
def stTestAux (q : Q) : ℕ → ForTest A
  | 0 => ForTest.eqPos 0 0
  | k + 1 =>
      ForTest.and (stTestAux q k)
        (if E.bits q k then ForTest.boolVar k else ForTest.not (ForTest.boolVar k))

lemma holds_stTestAux (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) (q : Q) :
    ∀ k, (ForTest.Holds w pos bv (E.stTestAux q k) ↔ ∀ i, i < k → bv i = E.bits q i) := by
  intro k
  induction k with
  | zero => simp [stTestAux, ForTest.Holds]
  | succ k ih =>
      have h2 : ForTest.Holds w pos bv
          (if E.bits q k then ForTest.boolVar (A := A) k
            else ForTest.not (ForTest.boolVar k)) ↔ bv k = E.bits q k := by
        cases hb : E.bits q k <;> simp [ForTest.Holds]
      have hsplit : ForTest.Holds w pos bv (E.stTestAux (A := A) q (k + 1))
          ↔ (ForTest.Holds w pos bv (E.stTestAux (A := A) q k) ∧
              ForTest.Holds w pos bv (if E.bits q k then ForTest.boolVar (A := A) k
                else ForTest.not (ForTest.boolVar k))) := Iff.rfl
      rw [hsplit, ih, h2]
      constructor
      · rintro ⟨h1, hk⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact h1 i hi'
        · exact hk
      · intro h
        exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

/-- The test that the state is `q`. -/
def stTest (q : Q) : ForTest A := E.stTestAux q E.n

lemma holds_stTest (w : List A) (pos : ℕ → ℕ) (q q' : Q) (bv : ℕ → Bool) :
    ForTest.Holds w pos (E.repOf q' bv) (E.stTest q) ↔ q = q' := by
  rw [stTest, holds_stTestAux]
  constructor
  · intro h
    refine E.inj q q' (fun i hi => ?_)
    have hi' := h i hi
    simp only [repOf, if_pos hi] at hi'
    exact hi'.symm
  · rintro rfl i hi
    simp [repOf, hi]

/-- The program that writes the bits of the state `q` into the first `k` Boolean variables. -/
def setStateAux (q : Q) : ℕ → ForProg A B
  | 0 => ForProg.skip
  | k + 1 => ForProg.seq (setStateAux q k) (ForProg.assign k (E.bits q k))

lemma exec_setStateAux (w : List A) (pos : ℕ → ℕ) (q : Q) :
    ∀ (k : ℕ) (bv : ℕ → Bool),
      ForProg.exec w (E.setStateAux (B := B) q k) pos bv
        = ((fun i => if i < k then E.bits q i else bv i), []) := by
  intro k
  induction k with
  | zero => intro bv; simp [setStateAux, ForProg.exec]
  | succ k ih =>
      intro bv
      show ForProg.exec w (ForProg.seq (E.setStateAux q k) (ForProg.assign k (E.bits q k))) pos bv = _
      rw [exec_seq, ih]
      simp only [ForProg.exec]
      refine Prod.ext ?_ (by simp)
      funext i
      show Function.update (fun j => if j < k then E.bits q j else bv j) k (E.bits q k) i
        = (if i < k + 1 then E.bits q i else bv i)
      by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik]
        by_cases h : i < k
        · simp [h, show i < k + 1 by omega]
        · simp [h, show ¬ i < k + 1 by omega]

/-- The program that sets the state to `q`. -/
def setState (q : Q) : ForProg A B := E.setStateAux q E.n

lemma exec_setState (w : List A) (pos : ℕ → ℕ) (q q' : Q) (bv : ℕ → Bool) :
    ForProg.exec w (E.setState (B := B) q) pos (E.repOf q' bv) = (E.repOf q bv, []) := by
  rw [setState, exec_setStateAux]
  refine Prod.ext ?_ rfl
  funext i
  by_cases hi : i < E.n <;> simp [repOf, hi]

end BoolEnc

/-! ## The machine language -/

/-- Programs of the machine language: an action that transforms the state, an action that may
also look at the letters under two position variables and at their relative order, sequential
composition, and a loop that binds a position variable. -/
inductive MProg (A B Q : Type) : Type
  /-- An action depending on the state only. -/
  | act : (Q → Q × List B) → MProg A B Q
  /-- An action depending on the state, on the letters at the position variables `x` and `y` and
  on the two order tests `x ≤ y` and `y ≤ x`. -/
  | act2 : ℕ → ℕ → (Q → Option A → Option A → Bool → Bool → Q × List B) → MProg A B Q
  /-- Sequential composition. -/
  | seq : MProg A B Q → MProg A B Q → MProg A B Q
  /-- A loop over the positions of the input, forwards (`true`) or backwards (`false`). -/
  | loop : Bool → ℕ → MProg A B Q → MProg A B Q

namespace MProg

variable {A B Q : Type}

/-- The semantics of a machine program: the new state and the produced output. -/
def sem (w : List A) : MProg A B Q → (ℕ → ℕ) → Q → Q × List B
  | act f, _, q => f q
  | act2 x y f, pos, q =>
      f q w[pos x]? w[pos y]? (decide (pos x ≤ pos y)) (decide (pos y ≤ pos x))
  | seq P R, pos, q =>
      let r := sem w P pos q
      let r' := sem w R pos r.1
      (r'.1, r.2 ++ r'.2)
  | loop d x P, pos, q =>
      runList (fun q' p => sem w P (Function.update pos x p) q') (loopRange d w.length) q

@[simp] lemma sem_act (w : List A) (f : Q → Q × List B) (pos : ℕ → ℕ) (q : Q) :
    sem w (act f) pos q = f q := rfl

@[simp] lemma sem_act2 (w : List A) (x y : ℕ)
    (f : Q → Option A → Option A → Bool → Bool → Q × List B) (pos : ℕ → ℕ) (q : Q) :
    sem w (act2 x y f) pos q
      = f q w[pos x]? w[pos y]? (decide (pos x ≤ pos y)) (decide (pos y ≤ pos x)) := rfl

@[simp] lemma sem_seq (w : List A) (P R : MProg A B Q) (pos : ℕ → ℕ) (q : Q) :
    sem w (P.seq R) pos q =
      ((sem w R pos (sem w P pos q).1).1,
        (sem w P pos q).2 ++ (sem w R pos (sem w P pos q).1).2) := rfl

@[simp] lemma sem_loop (w : List A) (d : Bool) (x : ℕ) (P : MProg A B Q) (pos : ℕ → ℕ) (q : Q) :
    sem w (loop d x P) pos q =
      runList (fun q' p => sem w P (Function.update pos x p) q') (loopRange d w.length) q := rfl

end MProg

/-! ## Compiling a machine program into a for-program -/

section Compile

variable {A B Q : Type}

/-- A conditional cascade: the branch of the first index whose test holds. -/
def casesBy {ι : Type} (test : ι → ForTest A) (body : ι → ForProg A B) : List ι → ForProg A B
  | [] => ForProg.skip
  | i :: rest => ForProg.ite (test i) (body i) (casesBy test body rest)

lemma exec_casesBy {ι : Type} (test : ι → ForTest A) (body : ι → ForProg A B) (w : List A)
    (pos : ℕ → ℕ) (bv : ℕ → Bool) (i₀ : ι) :
    ∀ (l : List ι), i₀ ∈ l → (∀ i ∈ l, (ForTest.Holds w pos bv (test i) ↔ i = i₀)) →
      ForProg.exec w (casesBy test body l) pos bv = ForProg.exec w (body i₀) pos bv := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons i rest ih =>
      intro hmem huniq
      simp only [casesBy]
      by_cases hi : ForTest.Holds w pos bv (test i)
      · have : i = i₀ := (huniq i (by simp)).mp hi
        subst this
        rw [exec_ite_pos _ _ _ _ _ _ hi]
      · rw [exec_ite_neg _ _ _ _ _ _ hi]
        refine ih ?_ (fun j hj => huniq j (by simp [hj]))
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd ((huniq i₀ (by simp)).mpr rfl) hi
        · exact h

/-- The test that the letter at the position variable `x` is `oa`; `as` is meant to list all
letters of the alphabet. -/
def labTest (as : List A) (x : ℕ) : Option A → ForTest A
  | some a => ForTest.label x a
  | none => as.foldr (fun a t => ForTest.and (ForTest.not (ForTest.label x a)) t)
      (ForTest.eqPos 0 0)

lemma holds_labTest_none (as : List A) (x : ℕ) (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForTest.Holds w pos bv (labTest as x none) ↔ ∀ a ∈ as, w[pos x]? ≠ some a := by
  simp only [labTest]
  induction as with
  | nil => simp [ForTest.Holds]
  | cons a as ih =>
      simp only [List.foldr_cons, ForTest.Holds, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩ b hb
        rcases hb with rfl | hb
        · exact h1
        · exact h2 b hb
      · intro h
        exact ⟨h a (Or.inl rfl), fun b hb => h b (Or.inr hb)⟩

lemma holds_labTest (as : List A) (has : ∀ a : A, a ∈ as) (x : ℕ) (w : List A) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (oa : Option A) :
    ForTest.Holds w pos bv (labTest as x oa) ↔ w[pos x]? = oa := by
  cases oa with
  | some a => simp [labTest, ForTest.Holds]
  | none =>
      rw [holds_labTest_none]
      constructor
      · intro h
        cases hw : w[pos x]? with
        | none => rfl
        | some a => exact absurd hw (h a (has a))
      · intro h a _
        rw [h]; simp

/-- The test that the two order comparisons of `x` and `y` have the prescribed values. -/
def cmpTest (x y : ℕ) (c₁ c₂ : Bool) : ForTest A :=
  ForTest.and (if c₁ then ForTest.lePos x y else ForTest.not (ForTest.lePos x y))
    (if c₂ then ForTest.lePos y x else ForTest.not (ForTest.lePos y x))

lemma holds_cmpTest (x y : ℕ) (c₁ c₂ : Bool) (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForTest.Holds w pos bv (cmpTest x y c₁ c₂) ↔
      (decide (pos x ≤ pos y) = c₁ ∧ decide (pos y ≤ pos x) = c₂) := by
  cases c₁ <;> cases c₂ <;>
    simp [cmpTest, ForTest.Holds, decide_eq_false_iff_not]

variable {q₀ : Q} (E : BoolEnc Q q₀) (as : List A) (qs : List Q)

/-- The for-program computed by a machine program. -/
noncomputable def MProg.compile : MProg A B Q → ForProg A B
  | .act f =>
      casesBy (E.stTest) (fun q => ForProg.seq (constProg (f q).2) (E.setState (f q).1)) qs
  | .act2 x y f =>
      casesBy
        (fun z : Q × Option A × Option A × Bool × Bool =>
          ForTest.and (E.stTest z.1)
            (ForTest.and (labTest as x z.2.1)
              (ForTest.and (labTest as y z.2.2.1) (cmpTest x y z.2.2.2.1 z.2.2.2.2))))
        (fun z =>
          ForProg.seq (constProg (f z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).2)
            (E.setState (f z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).1))
        (qs.flatMap (fun q => (none :: as.map some).flatMap (fun oa =>
          (none :: as.map some).flatMap (fun ob =>
            [true, false].flatMap (fun c₁ => [true, false].map (fun c₂ => (q, oa, ob, c₁, c₂)))))))
  | .seq P R => ForProg.seq (P.compile) (R.compile)
  | .loop d x P => ForProg.loop d x (P.compile)

variable {E as qs}

/-- **The compiled program simulates the machine program.** -/
theorem exec_compile (has : ∀ a : A, a ∈ as) (hqs : ∀ q : Q, q ∈ qs) (w : List A) :
    ∀ (M : MProg A B Q) (pos : ℕ → ℕ) (bv : ℕ → Bool) (q : Q),
      ForProg.exec w (M.compile E as qs) pos (E.repOf q bv)
        = (E.repOf (M.sem w pos q).1 bv, (M.sem w pos q).2) := by
  intro M
  induction M with
  | act f =>
      intro pos bv q
      rw [MProg.compile,
        exec_casesBy _ _ _ _ _ q qs (hqs q) (fun q' _ => E.holds_stTest w pos q' q bv)]
      rw [exec_seq, exec_constProg, E.exec_setState]
      simp
  | act2 x y f =>
      intro pos bv q
      set z₀ : Q × Option A × Option A × Bool × Bool :=
        (q, w[pos x]?, w[pos y]?, decide (pos x ≤ pos y), decide (pos y ≤ pos x)) with hz₀
      rw [MProg.compile]
      rw [exec_casesBy _ _ _ _ _ z₀ _ ?_ ?_]
      · rw [exec_seq, exec_constProg, E.exec_setState]
        simp [MProg.sem, hz₀]
      · simp only [List.mem_flatMap, List.mem_map, List.mem_cons]
        refine ⟨q, hqs q, w[pos x]?, ?_, w[pos y]?, ?_, decide (pos x ≤ pos y), by cases hc : decide (pos x ≤ pos y) <;> simp, ?_⟩
        · cases h : w[pos x]? with
          | none => simp
          | some a => exact Or.inr ⟨a, has a, rfl⟩
        · cases h : w[pos y]? with
          | none => simp
          | some a => exact Or.inr ⟨a, has a, rfl⟩
        · exact ⟨decide (pos y ≤ pos x), by cases hc : decide (pos y ≤ pos x) <;> simp, rfl⟩
      · intro z _
        simp only [ForTest.Holds, E.holds_stTest w pos z.1 q bv, holds_labTest as has,
          holds_cmpTest]
        constructor
        · rintro ⟨h1, h2, h3, h4, h5⟩
          rw [hz₀]
          have : z = (z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2) := rfl
          rw [this, h1, h2, h3, h4, h5]
        · rintro rfl
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | seq P R ihP ihR =>
      intro pos bv q
      rw [MProg.compile, exec_seq, ihP, ihR]
      simp
  | loop d x P ih =>
      intro pos bv q
      rw [MProg.compile]
      show forLoopRun _ _ _ = _
      rw [show (if d then List.range w.length else (List.range w.length).reverse)
            = loopRange d w.length from (by cases d <;> rfl), forLoopRun_eq_runList,
        MProg.sem_loop]
      generalize loopRange d w.length = ps
      induction ps generalizing q with
      | nil => simp
      | cons p ps ihps =>
          rw [runList_cons, runList_cons, ih]
          simp only []
          rw [ihps]

end Compile

/-! ## From machine programs to for-transducers -/

/-- **A function computed by a machine program is computed by a for-transducer.** -/
theorem isForTransducer_of_mprog {A B Q : Type} [Finite A] [Finite Q] (M : MProg A B Q) (q₀ : Q)
    (f : List A → List B) (h : ∀ w, (M.sem w (fun _ => 0) q₀).2 = f w) : IsForTransducer f := by
  classical
  obtain ⟨E⟩ := nonempty_boolEnc q₀
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype Q := Fintype.ofFinite Q
  refine ⟨M.compile E (Finset.univ : Finset A).toList (Finset.univ : Finset Q).toList, ?_⟩
  intro w
  have h0 : (fun _ => false : ℕ → Bool) = E.repOf q₀ (fun _ => false) := E.repOf_init.symm
  rw [ForProg.eval, h0,
    exec_compile (fun a => by simp) (fun q => by simp) w M (fun _ => 0) (fun _ => false) q₀]
  exact h w

end Lax194892Proofs.Transducers
