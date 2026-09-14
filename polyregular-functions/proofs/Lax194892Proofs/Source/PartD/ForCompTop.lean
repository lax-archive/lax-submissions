/-
Part D: for-transducers -- the composition of two for-transducers.

This file assembles the proof of Lemma `lem:for-closed-under-composition` from the correctness
`Transducers.tr_spec` of the translation of the outer for-transducer.

Given for-transducers `P` computing `f` and `Q` computing `g`, the composed program branches on
the length of the input:

* on the inputs of length at least two, `P` is computed by a single nest of loops
  (`Transducers.for_nest_form`), and the translation `Transducers.tr` of the closed, atomised form
  of `Q` runs `Q` over the positions at which that nest produces a letter;
* on the inputs of length at most one, the nest of loops is of no use -- a nest produces nothing
  on the empty input -- so the composition is computed directly: the loop-free simulation
  `Transducers.shortSim` of `P` is run in continuation-passing style
  (`Transducers.cpsFree`), each of its finitely many possible outputs `v` being replaced by the
  constant string `Q.eval v`.

The Boolean flags `X` and `Y`, computed by `Transducers.lenProg`, say whether the input has at
least one and at least two letters.
-/
import Lax194892Proofs.Source.PartD.ForComp

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B C : Type}

/-! ## Measuring the length of the input -/

/-- A loop raising the flag `X` at the first position of the input and the flag `Y` at the second
one: after it, `X` says that the input is nonempty and `Y` that it has at least two letters. -/
def lenProg (X Y : ℕ) : ForProg A C :=
  ForProg.loop true 0
    (ForProg.ite (ForTest.boolVar X) (ForProg.assign Y true) (ForProg.assign X true))

section

variable (w : List A) (X Y : ℕ)

/-- The step of `Transducers.lenProg`. -/
private noncomputable def lenStep (pos : ℕ → ℕ) : (ℕ → Bool) → ℕ → (ℕ → Bool) × List C :=
  fun s q => ForProg.exec w
    (ForProg.ite (ForTest.boolVar X) (ForProg.assign Y true) (ForProg.assign X true) : ForProg A C)
    (Function.update pos 0 q) s

private lemma lenStep_true (pos : ℕ → ℕ) (s : ℕ → Bool) (q : ℕ) (hs : s X = true) :
    lenStep (C := C) w X Y pos s q = (Function.update s Y true, []) := by
  show ForProg.exec w (ForProg.ite _ _ _ : ForProg A C) _ s = _
  rw [exec_ite_pos _ _ _ _ _ _ (show ForTest.Holds w (Function.update pos 0 q) s
    (ForTest.boolVar X) from hs)]
  rfl

private lemma lenStep_false (pos : ℕ → ℕ) (s : ℕ → Bool) (q : ℕ) (hs : s X = false) :
    lenStep (C := C) w X Y pos s q = (Function.update s X true, []) := by
  show ForProg.exec w (ForProg.ite _ _ _ : ForProg A C) _ s = _
  rw [exec_ite_neg _ _ _ _ _ _ (by
    show ¬ (s X = true)
    rw [hs]; simp)]
  rfl

private lemma lenRun_true (hXY : X ≠ Y) (pos : ℕ → ℕ) :
    ∀ (l : List ℕ) (s : ℕ → Bool), s X = true →
      runList (lenStep (C := C) w X Y pos) l s
        = (if l = [] then s else Function.update s Y true, []) := by
  intro l
  cases l with
  | nil => intro s _; simp
  | cons a l =>
      intro s hs
      have hs1 : (Function.update s Y true) X = true := by
        rw [Function.update_of_ne hXY]; exact hs
      rw [runList_head_dead _ a l s (fun q _ => by
        rw [lenStep_true w X Y pos s a hs, lenStep_true w X Y pos _ q hs1,
          Function.update_idem])]
      rw [lenStep_true w X Y pos s a hs]
      simp

private lemma lenRun_false (hXY : X ≠ Y) (pos : ℕ → ℕ) (l : List ℕ) (s : ℕ → Bool)
    (hsX : s X = false) :
    (runList (lenStep (C := C) w X Y pos) l s).2 = [] ∧
      (runList (lenStep (C := C) w X Y pos) l s).1 X = decide (l ≠ []) ∧
      (runList (lenStep (C := C) w X Y pos) l s).1 Y
        = (if 2 ≤ l.length then true else s Y) ∧
      ∀ i, i ≠ X → i ≠ Y → (runList (lenStep (C := C) w X Y pos) l s).1 i = s i := by
  cases l with
  | nil => simp [hsX]
  | cons a l =>
      have hs1 : (Function.update s X true) X = true := by simp
      have hupdYX : ∀ t : ℕ → Bool, Function.update t Y true X = t X :=
        fun t => Function.update_of_ne hXY _ _
      have hupdXY : ∀ t : ℕ → Bool, Function.update t X true Y = t Y :=
        fun t => Function.update_of_ne (Ne.symm hXY) _ _
      rw [runList_cons, lenStep_false w X Y pos s a hsX,
        lenRun_true w X Y hXY pos l _ hs1]
      refine ⟨by simp, ?_, ?_, ?_⟩
      · by_cases hl : l = [] <;> simp [hl, hupdYX]
      · by_cases hl : l = []
        · subst hl; simp [hupdXY]
        · have hpos : 1 ≤ l.length := by
            cases l with
            | nil => simp at hl
            | cons b l => simp
          simp [hl, hpos]
      · intro i hiX hiY
        by_cases hl : l = [] <;>
          simp [hl, Function.update_of_ne hiX, Function.update_of_ne hiY]

/-- **The length flags.**  After `Transducers.lenProg`, the flag `X` says that the input is
nonempty and the flag `Y` that it has at least two letters. -/
lemma lenProg_spec (hXY : X ≠ Y) (pos : ℕ → ℕ) (bv : ℕ → Bool) (hX : bv X = false)
    (hY : bv Y = false) :
    (ForProg.exec w (lenProg X Y : ForProg A C) pos bv).2 = [] ∧
      ((ForProg.exec w (lenProg X Y : ForProg A C) pos bv).1 X = true ↔ 0 < w.length) ∧
      ((ForProg.exec w (lenProg X Y : ForProg A C) pos bv).1 Y = true ↔ 2 ≤ w.length) ∧
      ∀ i, i ≠ X → i ≠ Y →
        (ForProg.exec w (lenProg X Y : ForProg A C) pos bv).1 i = bv i := by
  classical
  have hrun : ForProg.exec w (lenProg X Y : ForProg A C) pos bv
      = runList (lenStep (C := C) w X Y pos) (List.range w.length) bv := by
    rw [lenProg, exec_loop_eq]
    rfl
  obtain ⟨h1, h2, h3, h4⟩ := lenRun_false w X Y hXY pos (List.range w.length) bv hX
  rw [hrun]
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [h2]
    have hnil : (List.range w.length = []) ↔ w.length = 0 := by
      constructor
      · intro h; simpa using congrArg List.length h
      · intro h; rw [h]; rfl
    simp only [ne_eq, hnil, decide_eq_true_eq]
    omega
  · rw [h3, hY]
    by_cases h : 2 ≤ w.length <;> simp [h]

end

/-! ## Post-composing a loop-free program with an arbitrary function -/

/-- The continuation-passing translation of a loop-free program: `cpsFree R k` runs `R` without
producing its output, and then runs the program `k v`, where `v` is the string that `R` would have
produced. -/
def cpsFree : ForProg A B → (List B → ForProg A C) → ForProg A C
  | ForProg.skip, k => k []
  | ForProg.output b, k => k [b]
  | ForProg.assign i v, k => ForProg.seq (ForProg.assign i v) (k [])
  | ForProg.seq R S, k => cpsFree R (fun u => cpsFree S (fun v => k (u ++ v)))
  | ForProg.ite t R S, k => ForProg.ite t (cpsFree R k) (cpsFree S k)
  | ForProg.loop _ _ _, _ => ForProg.skip

/-- **The continuation-passing translation is correct.** -/
lemma exec_cpsFree (w : List A) : ∀ (R : ForProg A B), R.LoopFree →
    ∀ (k : List B → ForProg A C) (pos : ℕ → ℕ) (bv : ℕ → Bool),
      ForProg.exec w (cpsFree R k) pos bv
        = ForProg.exec w (k (ForProg.exec w R pos bv).2) pos (ForProg.exec w R pos bv).1 := by
  intro R
  induction R with
  | skip => intro _ k pos bv; rfl
  | output b => intro _ k pos bv; rfl
  | assign i v =>
      intro _ k pos bv
      show ForProg.exec w (ForProg.seq (ForProg.assign i v) (k [])) pos bv = _
      rw [exec_seq]
      show ((ForProg.exec w (k []) pos (Function.update bv i v)).1,
          ([] : List C) ++ (ForProg.exec w (k []) pos (Function.update bv i v)).2)
        = ForProg.exec w (k []) pos (Function.update bv i v)
      simp
  | seq R S ihR ihS =>
      intro hLF k pos bv
      show ForProg.exec w (cpsFree R (fun u => cpsFree S (fun v => k (u ++ v)))) pos bv = _
      rw [ihR hLF.1, ihS hLF.2]
      rfl
  | ite t R S ihR ihS =>
      intro hLF k pos bv
      show ForProg.exec w (ForProg.ite t (cpsFree R k) (cpsFree S k)) pos bv = _
      by_cases h : ForTest.Holds w pos bv t
      · rw [exec_ite_pos _ _ _ _ _ _ h, ihR hLF.1, exec_ite_pos _ _ _ _ _ _ h]
      · rw [exec_ite_neg _ _ _ _ _ _ h, ihS hLF.2, exec_ite_neg _ _ _ _ _ _ h]
  | loop d x R _ => intro hLF; exact absurd hLF (by exact fun h => h)

/-! ## The composition -/

/-- **The composed program** of Lemma `lem:for-closed-under-composition`.  The inner
for-transducer `P` is given by the nest of loops `L` with loop-free body `p`, and the outer one by
the program `Q`; `base`, `flQ`, `flS` are the fresh variables of the translation, `X` and `Y` the
two length flags, and `N` the fresh variable used to close the atomised form of `Q`.

The program is named so that the proof of Exercise `exer:forward-for-transducer` can inspect the
direction of its loops; the numbered result is `Transducers.forTransducer_comp_aux` below. -/
noncomputable def compProgAt (P : ForProg A B) (Q : ForProg B C) (L : List (Bool × ℕ))
    (p : ForProg A B) (base flQ flS X Y N : ℕ) : ForProg A C :=
  ForProg.seq (lenProg X Y)
    (ForProg.ite (ForTest.boolVar Y)
      (tr L p base flQ flS (fun _ => 0) 1 (closeProg N (N + 1) (ForProg.atomize Q)))
      (cpsFree (shortSim X P) (fun v => constProg (Q.eval v))))

/-- **The composed program is correct.** -/
theorem eval_compProgAt (P : ForProg A B) (Q : ForProg B C) (L : List (Bool × ℕ))
    (p : ForProg A B) (M N base flQ flS X Y : ℕ)
    (hbase : base = M + 3) (hflQ : flQ = M + 1) (hflS : flS = M + 2)
    (hX : X = base) (hY : Y = base + 2)
    (hMmem : ∀ x ∈ p.posVars ++ p.boolVars ++ L.map Prod.snd ++ P.posVars ++ P.boolVars, x ≤ M)
    (hNmem : ∀ i ∈ (ForProg.atomize Q).boolVars, i < N)
    (hpLF : p.LoopFree) (hpout : p.OutputsAtMostOne) (hpnd : (L.map Prod.snd).Nodup)
    (hnest : ∀ w : List A, 2 ≤ w.length →
      (ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2 = P.eval w)
    (w : List A) :
    (compProgAt P Q L p base flQ flS X Y N).eval w = Q.eval (P.eval w) := by
  classical
  have hok : CompOk L p base flQ flS :=
    { loopFree := hpLF
      out1 := hpout
      nodup := hpnd
      xlt := fun x hx => by have := hMmem x (by simp [hx]); omega
      poslt := fun i hi => by have := hMmem i (by simp [hi]); omega
      boollt := fun i hi => by have := hMmem i (by simp [hi]); omega
      flQS := by omega
      flSbase := by omega }
  -- the closed, atomised form of the outer program
  set Q₀ : ForProg B C := ForProg.atomize Q with hQ₀
  set Q₂ : ForProg B C := closeProg N (N + 1) Q₀ with hQ₂
  have hQ₂atom : Q₂.AllAtomic :=
    allAtomic_closeProg _ _ _ (ForProg.allAtomic_atomize Q)
  have hQ₂free : Q₂.freePos = [] := freePos_closeProg _ _ _
  have hQ₂eval : ∀ v, Q₂.eval v = Q.eval v := by
    intro v
    rw [hQ₂, eval_closeProg N (N + 1) Q₀ (fun hc => absurd (hNmem N hc) (lt_irrefl _))
      (fun i hi => by have := hNmem i hi; omega)]
    show (ForProg.exec v (ForProg.atomize Q) (fun _ => 0) (fun _ => false)).2 = Q.eval v
    rw [ForProg.exec_atomize]
    rfl
  have hXY : X ≠ Y := by omega
  have hqbvX : ∀ i, qbv base i ≠ X := fun i => by rw [qbv]; omega
  have hqbvY : ∀ i, qbv base i ≠ Y := fun i => by rw [qbv]; omega
  have hXP : X ∉ P.boolVars := fun hc => by have := hMmem X (by simp [hc]); omega
  have hYP : Y ∉ P.boolVars := fun hc => by have := hMmem Y (by simp [hc]); omega
  rw [compProgAt, ForProg.eval]
  set s : ℕ → Bool := (ForProg.exec w (lenProg X Y : ForProg A C) (fun _ => 0)
    (fun _ => false)).1 with hs
  obtain ⟨hlen1, hlen2, hlen3, hlen4⟩ :=
    lenProg_spec (C := C) w X Y hXY (fun _ => 0) (fun _ => false) rfl rfl
  show (ForProg.exec w (ForProg.seq _ _) (fun _ => 0) (fun _ => false)).2 = Q.eval (P.eval w)
  rw [exec_seq, hlen1, List.nil_append]
  by_cases hbig : 2 ≤ w.length
  · -- the input has at least two letters: the translation of the outer program
    have hYtrue : ForTest.Holds w (fun _ => 0) s (ForTest.boolVar Y) := hlen3.mpr hbig
    rw [exec_ite_pos _ _ _ _ _ _ hYtrue]
    have hbv : ∀ i, s (qbv base i) = (fun _ : ℕ => false) i := fun i => by
      rw [hs, hlen4 (qbv base i) (hqbvX i) (hqbvY i)]
    obtain ⟨hout, -, -⟩ := tr_spec w L p base flQ flS hok Q₂ (fun _ => 0) 1 hQ₂atom
      (fun _ => 0) (fun _ => false) (fun _ => 0) s
      (fun y hy => absurd hy (by rw [hQ₂free]; simp))
      (fun i _ => rfl)
      (fun y hy => absurd hy (by rw [hQ₂free]; simp))
      hbv
    rw [hout]
    have hinner : innerOut w L p = P.eval w := by
      rw [innerOut_def, hnest w hbig]
    show (ForProg.exec (innerOut w L p) Q₂ (fun _ => 0) (fun _ => false)).2 = Q.eval (P.eval w)
    rw [show (ForProg.exec (innerOut w L p) Q₂ (fun _ => 0) (fun _ => false)).2
        = Q₂.eval (innerOut w L p) from rfl, hQ₂eval, hinner]
  · -- the input has at most one letter: the direct simulation
    have hshort : w.length ≤ 1 := by omega
    have hYfalse : ¬ ForTest.Holds w (fun _ => 0) s (ForTest.boolVar Y) := by
      intro hc
      exact hbig (hlen3.mp hc)
    rw [exec_ite_neg _ _ _ _ _ _ hYfalse,
      exec_cpsFree w (shortSim X P) (loopFree_shortSim X P) _ (fun _ => 0) s]
    have hsim : ForProg.exec w (shortSim X P) (fun _ => 0) s = ForProg.exec w P (fun _ => 0) s :=
      shortSim_spec X w hshort _ (fun _ => rfl) P hXP s hlen2
    have hstate : (ForProg.exec w P (fun _ => 0) s).2 = P.eval w := by
      rw [ForProg.eval]
      exact (exec_congr_bv w P (fun _ => 0) (fun i => i ∈ P.boolVars) (fun i hi => hi)
        s (fun _ => false) (fun i hi => by
          rw [hs, hlen4 i (fun hc => hXP (hc ▸ hi)) (fun hc => hYP (hc ▸ hi))])).1
    rw [hsim, hstate, exec_constProg]

/-- **Lemma `lem:for-closed-under-composition`.**  The string-to-string functions computed by
for-transducers are closed under composition.  This is the statement proved in
`RequestProject/PartD/Statements.lean`. -/
theorem forTransducer_comp_aux {f : List A → List B} {g : List B → List C}
    (hf : IsForTransducer f) (hg : IsForTransducer g) : IsForTransducer (g ∘ f) := by
  classical
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  obtain ⟨L, p, hpLF, hpout, hpnd, hnest⟩ := for_nest_form P
  set M : ℕ := maxList (p.posVars ++ p.boolVars ++ L.map Prod.snd ++ P.posVars ++ P.boolVars)
    with hM
  set N : ℕ := maxList (ForProg.atomize Q).boolVars + 1 with hN
  refine ⟨compProgAt P Q L p (M + 3) (M + 1) (M + 2) (M + 3) (M + 5) N, fun w => ?_⟩
  rw [eval_compProgAt P Q L p M N (M + 3) (M + 1) (M + 2) (M + 3) (M + 5) rfl rfl rfl rfl rfl
    (fun x hx => le_maxList _ x hx)
    (fun i hi => by have := le_maxList (ForProg.atomize Q).boolVars i hi; omega)
    hpLF hpout hpnd (fun v hv => by rw [hnest v hv]) w, hP w]
  exact hQ (f w)

end Lax194892Proofs.Transducers
