/-
Part D: the ingredients of the scan of the enumeration.

The second phase of the proof that a for-transducer in prenex form computes a polyregular function
(the right-to-left inclusion of Theorem `thm:for-transducers-are-polyregular`) is a machine that
scans the enumeration of the tuples of positions -- one annotated copy of the input per tuple --
and runs the body of the nest of loops on each copy.  This file collects what that machine needs:

* `Transducers.ForProg.exec_congr_view`: a loop-free program only sees the letters under its
  position variables and the order of those variables, so two inputs that look the same under the
  variables give the same execution.  This is what lets the machine replace the input string and
  the tuple by a *canonical* string of bounded length, which fits in its finite memory.
* `Transducers.virt`: the loop variable of a nest that a position variable of the body refers to,
  and the fact that the valuation of a tuple is read off the extended tuple through it.
* `Transducers.PolyEnum.Blk`: the finite information about one annotated copy that the machine
  keeps -- the letter under each variable and the order of the variables -- together with the
  canonical string `cword` and the canonical valuation `cpos` built from it.
-/
import Lax194892Proofs.Source.PartD.PolyEnumPoly
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B : Type}

/-! ## A loop-free program only sees the view of its position variables -/

namespace ForTest

/-- Two valuations that order the position variables of a test in the same way, and put the same
letters under them, give the test the same truth value. -/
lemma holds_congr_view (w w' : List A) (t : ForTest A) (pos pos' : ℕ → ℕ) (bv : ℕ → Bool)
    (hle : ∀ i ∈ t.posVars, ∀ j ∈ t.posVars, (pos i ≤ pos j ↔ pos' i ≤ pos' j))
    (hlab : ∀ i ∈ t.posVars, w[pos i]? = w'[pos' i]?) :
    Holds w pos bv t ↔ Holds w' pos' bv t := by
  induction t with
  | boolVar i => rfl
  | eqPos i j =>
      have h1 := hle i (by simp [posVars]) j (by simp [posVars])
      have h2 := hle j (by simp [posVars]) i (by simp [posVars])
      simp only [Holds]
      omega
  | lePos i j => simpa only [Holds] using hle i (by simp [posVars]) j (by simp [posVars])
  | label i a => simp only [Holds, hlab i (by simp [posVars])]
  | not t ih =>
      simp only [Holds]
      rw [ih (fun i hi j hj => hle i (by simpa [posVars] using hi) j (by simpa [posVars] using hj))
        (fun i hi => hlab i (by simpa [posVars] using hi))]
  | and t s iht ihs =>
      simp only [Holds]
      rw [iht (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
          (fun i hi => hlab i (by simp [posVars, hi])),
        ihs (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
          (fun i hi => hlab i (by simp [posVars, hi]))]
  | or t s iht ihs =>
      simp only [Holds]
      rw [iht (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
          (fun i hi => hlab i (by simp [posVars, hi])),
        ihs (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
          (fun i hi => hlab i (by simp [posVars, hi]))]

end ForTest

namespace ForProg

/-- **A loop-free program only sees the view of its position variables.**  Two inputs, with two
valuations that order the position variables of the program in the same way and put the same
letters under them, give the same execution. -/
lemma exec_congr_view (w w' : List A) (P : ForProg A B) (hP : P.LoopFree)
    (pos pos' : ℕ → ℕ) (bv : ℕ → Bool)
    (hle : ∀ i ∈ P.posVars, ∀ j ∈ P.posVars, (pos i ≤ pos j ↔ pos' i ≤ pos' j))
    (hlab : ∀ i ∈ P.posVars, w[pos i]? = w'[pos' i]?) :
    exec w P pos bv = exec w' P pos' bv := by
  induction P generalizing bv with
  | skip => rfl
  | output b => rfl
  | assign i v => rfl
  | seq P Q ihP ihQ =>
      obtain ⟨h1, h2⟩ := hP
      have hP' := ihP h1 bv (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
        (fun i hi => hlab i (by simp [posVars, hi]))
      have hQ' := ihQ h2 (exec w' P pos' bv).1
        (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
        (fun i hi => hlab i (by simp [posVars, hi]))
      simp only [exec, hP', hQ']
  | ite t P Q ihP ihQ =>
      obtain ⟨h1, h2⟩ := hP
      have ht : ForTest.Holds w pos bv t ↔ ForTest.Holds w' pos' bv t :=
        ForTest.holds_congr_view w w' t pos pos' bv
          (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
          (fun i hi => hlab i (by simp [posVars, hi]))
      have hP' := ihP h1 bv (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
        (fun i hi => hlab i (by simp [posVars, hi]))
      have hQ' := ihQ h2 bv
        (fun i hi j hj => hle i (by simp [posVars, hi]) j (by simp [posVars, hj]))
        (fun i hi => hlab i (by simp [posVars, hi]))
      simp only [exec, hP', hQ']
      exact if_congr ht rfl rfl
  | loop d x P _ => exact absurd hP (by simp [LoopFree])

end ForProg

/-! ## The loop variable that a position variable refers to -/

/-- The loop of a nest that binds the position variable `i`: the index of the innermost loop whose
variable is `i`, and `L.length` if no loop of the nest binds `i` (in which case the variable keeps
its initial value). -/
def virt : List (Bool × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, x) :: L, i => if virt L i = L.length ∧ x = i then 0 else virt L i + 1

lemma virt_le (L : List (Bool × ℕ)) (i : ℕ) : virt L i ≤ L.length := by
  induction L with
  | nil => simp [virt]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      by_cases h : virt L i = L.length ∧ x = i
      · simp [virt, h]
      · simp only [virt, if_neg h, List.length_cons]
        omega

/-- The valuation of the position variables produced by a tuple is read off the extended tuple
through `Transducers.virt`. -/
lemma setTuple_virt (L : List (Bool × ℕ)) :
    ∀ (t : List ℕ), t.length = L.length → ∀ (base : ℕ → ℕ) (i : ℕ),
      setTuple L t base i
        = if virt L i < L.length then t.getD (virt L i) 0 else base i := by
  induction L with
  | nil => intro t ht base i; simp [virt]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      intro t ht base i
      cases t with
      | nil => simp at ht
      | cons p t =>
          have ht' : t.length = L.length := by simpa using ht
          rw [setTuple_cons, ih t ht' _ i]
          by_cases h : virt L i = L.length ∧ x = i
          · have hx : x = i := h.2
            subst hx
            have h1 : virt L x = L.length := h.1
            have hv : virt ((d, x) :: L) x = 0 := by simp [virt, h1]
            rw [if_neg (by omega), hv, if_pos (by simp)]
            simp
          · simp only [virt, if_neg h, List.length_cons]
            by_cases hlt : virt L i < L.length
            · rw [if_pos (by omega), if_pos (by omega)]
              simp
            · have hEq : virt L i = L.length := le_antisymm (virt_le L i) (by omega)
              have hne : x ≠ i := fun hx => h ⟨hEq, hx⟩
              rw [if_neg (by omega), if_neg (by omega)]
              exact Function.update_of_ne (Ne.symm hne) _ _

/-- The entries of a tuple visited by a nest of loops are positions of the input string. -/
lemma mem_tuplesOf_lt : ∀ (L : List (Bool × ℕ)) (n : ℕ) {t : List ℕ},
    t ∈ tuplesOf L n → ∀ p ∈ t, p < n := by
  intro L
  induction L with
  | nil => intro n t ht; simp only [tuplesOf_nil, List.mem_singleton] at ht; simp [ht]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      intro n t ht
      rw [tuplesOf_cons] at ht
      simp only [List.mem_flatMap, List.mem_map] at ht
      obtain ⟨p, hp, t', ht', rfl⟩ := ht
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact mem_loopRange.mp hp
      · exact ih n ht' q hq'

/-- The value of the position variable `i` under a tuple, read off the tuple extended by the
initial value `0`. -/
lemma setTuple_getD (L : List (Bool × ℕ)) (t : List ℕ) (ht : t.length = L.length) (i : ℕ) :
    setTuple L t (fun _ => 0) i = (t ++ [0]).getD (virt L i) 0 := by
  rw [setTuple_virt L t ht]
  by_cases h : virt L i < L.length
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
  · have hEq : virt L i = L.length := le_antisymm (virt_le L i) (by omega)
    rw [if_neg h, hEq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [ht]

namespace PolyEnum

/-! ## The information kept about one annotated copy -/

/-- What the scanning machine remembers about the annotated copy it is reading: the letter under
each of the `k` loop variables and under the constant variable `0` (the index `k`), and the order
of those variables. -/
structure Blk (A : Type) (k : ℕ) where
  /-- The letter at the position of each variable. -/
  lets : Fin (k + 1) → A
  /-- Whether the position of the first variable is at most the position of the second. -/
  le : Fin (k + 1) → Fin (k + 1) → Bool

instance {A : Type} {k : ℕ} [Finite A] : Finite (Blk A k) := by
  have h : Function.Injective (fun v : Blk A k => (v.lets, v.le)) := by
    intro v v' h
    cases v; cases v'
    simp_all
  exact Finite.of_injective _ h

variable {k : ℕ}

/-- The canonical position of a variable: the number of variables that lie strictly before it. -/
def cpos (v : Blk A k) (j : Fin (k + 1)) : Fin (k + 1) :=
  ⟨{i | v.le i j ∧ ¬ v.le j i}.toFinset.card, by
    have hsub : ({i | v.le i j ∧ ¬ v.le j i}.toFinset : Finset (Fin (k + 1))) ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr (fun h => ?_)
      have : j ∈ ({i | v.le i j ∧ ¬ v.le j i}.toFinset : Finset (Fin (k + 1))) := by
        rw [h]; exact Finset.mem_univ j
      simp at this
    have := Finset.card_lt_card hsub
    simpa using this⟩

/-- The canonical string of the copy: one letter per canonical position. -/
noncomputable def cword (v : Blk A k) : List A :=
  List.ofFn (fun q : Fin (k + 1) =>
    match (List.finRange (k + 1)).find? (fun j => decide (cpos v j = q)) with
    | some j => v.lets j
    | none => v.lets (Fin.last k))

/-- The letter under a variable is the letter of the canonical string at its canonical position,
provided variables with the same canonical position carry the same letter. -/
lemma cword_getElem (v : Blk A k) (hcons : ∀ i j, cpos v i = cpos v j → v.lets i = v.lets j)
    (j : Fin (k + 1)) : (cword v)[(cpos v j : ℕ)]? = some (v.lets j) := by
  have hlt : (cpos v j : ℕ) < k + 1 := (cpos v j).2
  rw [cword, List.getElem?_ofFn]
  rw [dif_pos hlt]
  have hfind : ∃ i, (List.finRange (k + 1)).find? (fun i => decide (cpos v i = cpos v j))
      = some i := by
    rcases hf : (List.finRange (k + 1)).find? (fun i => decide (cpos v i = cpos v j)) with _ | i
    · rw [List.find?_eq_none] at hf
      exact absurd (hf j (List.mem_finRange j)) (by simp)
    · exact ⟨i, rfl⟩
  obtain ⟨i, hi⟩ := hfind
  have hip : cpos v i = cpos v j := by
    have := List.find?_some hi
    simpa using this
  simp only [Fin.eta, hi]
  exact congrArg some (hcons i j hip)

/-! ## The canonical positions of a copy of a real input -/

section Concrete

variable (v : Blk A k) (T : Fin (k + 1) → ℕ)

/-- The canonical positions order the variables in the same way as the real positions. -/
lemma cpos_lt_of_lt (hle : ∀ i j, v.le i j = decide (T i ≤ T j)) {i j : Fin (k + 1)}
    (h : T i < T j) : (cpos v i : ℕ) < (cpos v j : ℕ) := by
  have hsub : ({l | v.le l i ∧ ¬ v.le i l}.toFinset : Finset (Fin (k + 1)))
      ⊂ {l | v.le l j ∧ ¬ v.le j l}.toFinset := by
    constructor
    · intro l hl
      simp only [Set.mem_toFinset, Set.mem_setOf_eq, hle, decide_eq_true_eq] at hl ⊢
      omega
    · intro hcon
      have hi : i ∈ ({l | v.le l j ∧ ¬ v.le j l}.toFinset : Finset (Fin (k + 1))) := by
        simp only [Set.mem_toFinset, Set.mem_setOf_eq, hle, decide_eq_true_eq]
        omega
      have := hcon hi
      simp only [Set.mem_toFinset, Set.mem_setOf_eq, hle, decide_eq_true_eq] at this
      omega
  simpa [cpos] using Finset.card_lt_card hsub

lemma cpos_eq_of_eq (hle : ∀ i j, v.le i j = decide (T i ≤ T j)) {i j : Fin (k + 1)}
    (h : T i = T j) : cpos v i = cpos v j := by
  refine Fin.ext ?_
  simp only [cpos]
  congr 1
  refine Finset.ext (fun l => ?_)
  simp only [Set.mem_toFinset, Set.mem_setOf_eq, hle, h]

lemma cpos_le_iff (hle : ∀ i j, v.le i j = decide (T i ≤ T j)) (i j : Fin (k + 1)) :
    ((cpos v i : ℕ) ≤ (cpos v j : ℕ)) ↔ T i ≤ T j := by
  constructor
  · intro h
    by_contra hcon
    have hlt : T j < T i := by omega
    have := cpos_lt_of_lt v T hle hlt
    omega
  · intro h
    rcases Nat.lt_or_ge (T i) (T j) with hlt | hge
    · exact le_of_lt (cpos_lt_of_lt v T hle hlt)
    · have : T i = T j := by omega
      exact le_of_eq (congrArg Fin.val (cpos_eq_of_eq v T hle this))

lemma cpos_consistent (hle : ∀ i j, v.le i j = decide (T i ≤ T j))
    (hlets : ∀ i j, T i = T j → v.lets i = v.lets j) (i j : Fin (k + 1))
    (h : cpos v i = cpos v j) : v.lets i = v.lets j := by
  refine hlets i j ?_
  have h1 := (cpos_le_iff v T hle i j).mp (le_of_eq (congrArg Fin.val h))
  have h2 := (cpos_le_iff v T hle j i).mp (le_of_eq (congrArg Fin.val h.symm))
  omega

end Concrete

end PolyEnum

end Lax194892Proofs.Transducers
