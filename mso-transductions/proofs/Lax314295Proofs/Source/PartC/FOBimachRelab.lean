/-
From aperiodic bimachines to first-order relabellings: one implication of
Theorem `thm:fo-rational-functions` of *Transducers* (M. Bojańczyk).

"Consider the prefix automaton, which is aperiodic.  Thanks to
Theorem `thm:logic-aperiodic` we can describe runs of this automaton in first-order logic. [...]
Similarly, we can describe in first-order logic the transitions of the suffix
automaton.  By combining these formulas, we can describe in first-order logic
the pairs (transition of the prefix automaton, transition of the suffix
automaton) that are used on each input position, and using these pairs we can
compute the corresponding parts of the output string."

The formula attached to a position `x` says: the prefix strictly before `x`
takes the prefix automaton to the state `q` (a sentence given by
Theorem `thm:logic-aperiodic`, relativised to the positions `< x`), the letter at `x` is `a`,
the suffix strictly after `x` takes the suffix automaton to the state `s` (a
sentence for the *reverse* of a language recognised by an aperiodic automaton,
which is first-order definable by `Transducers.FODefinable.reverse`, relativised
to the positions `> x`), and `x` is, or is not, the last position.

A bimachine outputs one block per gap of the input string, one more than the
number of positions; the block of the gap `i` is produced at the position `i`,
and the block of the last gap is appended to the block produced at the last
position.  On the empty input the relabelling outputs the single block of the
bimachine.
-/
import Lax314295Proofs.Source.PartC.FORev
import Lax314295Proofs.Source.PartC.FORename
import Lax132576Proofs.Source.PartB.Bimachine
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace FOBimachRelab

open MSO

variable {A B P S : Type}

/-! ## The last position -/

/-- The formula saying that `x₀` is the last position of the string. -/
def lastF : MSO A := not (exFO 1 (ltVar 0 1))

lemma isFO_lastF : (lastF : MSO A).IsFO := isFO_ltVar 0 1

lemma sat_lastF (w : List A) (p : ℕ) (hp : p < w.length) (so : ℕ → Set ℕ) :
    Sat w (fun _ => p) so (lastF : MSO A) ↔ p + 1 = w.length := by
  show (¬ ∃ y < w.length, Sat w (Function.update (fun _ => p) 1 y) so (ltVar 0 1)) ↔ _
  have hupd : ∀ y : ℕ,
      Sat w (Function.update (fun _ => p) 1 y) so (ltVar (A := A) 0 1) ↔ p < y := by
    intro y
    rw [sat_ltVar, Function.update_of_ne (by omega), Function.update_self]
  constructor
  · intro h
    by_contra hne
    exact h ⟨p + 1, by omega, (hupd (p + 1)).mpr (by omega)⟩
  · rintro h ⟨y, hy, hsat⟩
    have := (hupd y).mp hsat
    omega

/-! ## The formulas of the relabelling -/

/-- The index set of the relabelling: a state of the prefix automaton, a
letter, a state of the suffix automaton, and a Boolean telling whether the
position is the last one. -/
abbrev Idx (A P S : Type) : Type := P × A × S × Bool

/-- The formula attached to an index. -/
def formOf (χ : P → MSO A) (ξ : S → MSO A) (x : Idx A P S) : MSO A :=
  MSO.and (MSO.and (relLt 0 (shiftUp 1 (χ x.1))) (MSO.lab x.2.1 0))
    (MSO.and (relGt 0 (shiftUp 1 (ξ x.2.2.1)))
      (if x.2.2.2 then lastF else MSO.not lastF))

lemma isFO_formOf {χ : P → MSO A} {ξ : S → MSO A} (hχ : ∀ q, (χ q).IsFO)
    (hξ : ∀ s, (ξ s).IsFO) (x : Idx A P S) : (formOf χ ξ x).IsFO := by
  refine ⟨⟨isFO_relLt 0 (isFO_shiftUp 1 (hχ _)), trivial⟩,
    isFO_relGt 0 (isFO_shiftUp 1 (hξ _)), ?_⟩
  cases x.2.2.2 with
  | false => exact isFO_lastF
  | true => exact isFO_lastF

lemma sat_formOf {χ : P → MSO A} {ξ : S → MSO A} {Pp : List A → P → Prop}
    {Ps : List A → S → Prop}
    (hχfo : ∀ q, (χ q).IsFO) (hχfree : ∀ q, (χ q).freeFO = ∅)
    (hχsat : ∀ (q : P) (u : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), Sat u fo so (χ q) ↔ Pp u q)
    (hξfo : ∀ s, (ξ s).IsFO) (hξfree : ∀ s, (ξ s).freeFO = ∅)
    (hξsat : ∀ (s : S) (u : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), Sat u fo so (ξ s) ↔ Ps u s)
    (w : List A) (p : ℕ) (hp : p < w.length) (x : Idx A P S) :
    Sat w (fun _ => p) (fun _ => ∅) (formOf χ ξ x) ↔
      (Pp (w.take p) x.1 ∧ w[p]? = some x.2.1 ∧ Ps (w.drop (p + 1)) x.2.2.1 ∧
        ((p + 1 = w.length) ↔ x.2.2.2 = true)) := by
  have h1 : Sat w (fun _ => p) (fun _ => ∅) (relLt 0 (shiftUp 1 (χ x.1))) ↔
      Pp (w.take p) x.1 := by
    rw [sat_relLt w 0 _ (isFO_shiftUp 1 (hχfo x.1))
      (zero_notMem_foVars_shiftUp 0 (χ x.1)) _ _
      (by intro i hi
          rw [freeFO_shiftUp_eq_empty 1 (hχfree x.1)] at hi
          exact absurd hi (Set.notMem_empty i))]
    rw [sat_shiftUp_sentence (hχfo x.1) (hχfree x.1) 1 _ _ (fun _ => 0) _ (fun _ => ∅)]
    exact hχsat x.1 _ _ _
  have h2 : Sat w (fun _ => p) (fun _ => ∅) (relGt 0 (shiftUp 1 (ξ x.2.2.1))) ↔
      Ps (w.drop (p + 1)) x.2.2.1 := by
    rw [sat_relGt w 0 _ (isFO_shiftUp 1 (hξfo x.2.2.1))
      (zero_notMem_foVars_shiftUp 0 (ξ x.2.2.1)) _ _
      (by intro i hi
          rw [freeFO_shiftUp_eq_empty 1 (hξfree x.2.2.1)] at hi
          exact absurd hi (Set.notMem_empty i))]
    rw [sat_shiftUp_sentence (hξfo x.2.2.1) (hξfree x.2.2.1) 1 _ _ (fun _ => 0) _ (fun _ => ∅)]
    exact hξsat x.2.2.1 _ _ _
  have h3 : Sat w (fun _ => p) (fun _ => ∅)
      (if x.2.2.2 then (lastF : MSO A) else MSO.not lastF) ↔
      ((p + 1 = w.length) ↔ x.2.2.2 = true) := by
    cases hb : x.2.2.2 with
    | false =>
        rw [if_neg (by simp)]
        show (¬ Sat w (fun _ => p) (fun _ => ∅) (lastF : MSO A)) ↔ _
        rw [sat_lastF w p hp]
        simp
    | true =>
        rw [if_pos (by simp)]
        rw [sat_lastF w p hp]
        simp
  have hlab : Sat w (fun _ => p) (fun _ => ∅) (MSO.lab x.2.1 0) ↔ w[p]? = some x.2.1 := Iff.rfl
  show ((Sat w (fun _ => p) (fun _ => ∅) (relLt 0 (shiftUp 1 (χ x.1))) ∧
      Sat w (fun _ => p) (fun _ => ∅) (MSO.lab x.2.1 0)) ∧
    (Sat w (fun _ => p) (fun _ => ∅) (relGt 0 (shiftUp 1 (ξ x.2.2.1))) ∧
      Sat w (fun _ => p) (fun _ => ∅)
        (if x.2.2.2 then (lastF : MSO A) else MSO.not lastF))) ↔ _
  rw [h1, h2, h3, hlab]
  constructor
  · rintro ⟨⟨a1, a2⟩, a3, a4⟩
    exact ⟨a1, a2, a3, a4⟩
  · rintro ⟨a1, a2, a3, a4⟩
    exact ⟨⟨a1, a2⟩, a3, a4⟩

/-! ## The output blocks -/

/-- The block of output produced by the bimachine at the gap `i`. -/
def gap (M : Bimachine A B P S) (w : List A) (i : ℕ) : List B :=
  M.out (strTrans M.prefixStep (w.take i) M.prefixInit)
    (strTrans M.suffixStep (w.drop i).reverse M.suffixInit)

lemma eval_eq_flatten (M : Bimachine A B P S) (w : List A) :
    M.eval w = ((List.range (w.length + 1)).map (gap M w)).flatten := rfl

/-- The output of the relabelling at an index. -/
def outOf (M : Bimachine A B P S) (x : Idx A P S) : List B :=
  if x.2.2.2 then
    M.out x.1 (M.suffixStep x.2.2.1 x.2.1) ++ M.out (M.prefixStep x.1 x.2.1) M.suffixInit
  else M.out x.1 (M.suffixStep x.2.2.1 x.2.1)

/-- The canonical index at a position of a string. -/
def idxAt (M : Bimachine A B P S) (w : List A) (p : ℕ) (hp : p < w.length) : Idx A P S :=
  (strTrans M.prefixStep (w.take p) M.prefixInit, w[p],
    strTrans M.suffixStep (w.drop (p + 1)).reverse M.suffixInit, decide (p + 1 = w.length))

/-- Reading one more letter at the end of the input of `strTrans`. -/
lemma strTrans_concat {Q : Type} (δ : Q → A → Q) (u : List A) (a : A) (q : Q) :
    strTrans δ (u ++ [a]) q = δ (strTrans δ u q) a := by
  simp only [strTrans, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma out_idxAt (M : Bimachine A B P S) (w : List A) (p : ℕ) (hp : p < w.length) :
    outOf M (idxAt M w p hp) =
      if p + 1 = w.length then gap M w p ++ gap M w (p + 1) else gap M w p := by
  have hsuf : M.suffixStep (strTrans M.suffixStep (w.drop (p + 1)).reverse M.suffixInit) w[p]
      = strTrans M.suffixStep (w.drop p).reverse M.suffixInit := by
    have hrev : (w.drop p).reverse = (w.drop (p + 1)).reverse ++ [w[p]] := by
      rw [List.drop_eq_getElem_cons hp, List.reverse_cons]
    rw [hrev, strTrans_concat]
  have hpre : M.prefixStep (strTrans M.prefixStep (w.take p) M.prefixInit) w[p]
      = strTrans M.prefixStep (w.take (p + 1)) M.prefixInit := by
    have htake : w.take (p + 1) = w.take p ++ [w[p]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hp]; rfl
    rw [htake, strTrans_concat]
  by_cases hlast : p + 1 = w.length
  · rw [if_pos hlast]
    show (if decide (p + 1 = w.length) = true then _ else _) = _
    rw [if_pos (by simp [hlast])]
    show M.out (strTrans M.prefixStep (w.take p) M.prefixInit)
        (M.suffixStep (strTrans M.suffixStep (w.drop (p + 1)).reverse M.suffixInit) w[p]) ++
        M.out (M.prefixStep (strTrans M.prefixStep (w.take p) M.prefixInit) w[p]) M.suffixInit
      = _
    rw [hsuf, hpre]
    show gap M w p ++ _ = gap M w p ++ gap M w (p + 1)
    congr 1
    show M.out (strTrans M.prefixStep (w.take (p + 1)) M.prefixInit) M.suffixInit
      = gap M w (p + 1)
    rw [gap, hlast]
    simp [strTrans]
  · rw [if_neg hlast]
    show (if decide (p + 1 = w.length) = true then _ else _) = _
    rw [if_neg (by simp [hlast])]
    show M.out (strTrans M.prefixStep (w.take p) M.prefixInit)
        (M.suffixStep (strTrans M.suffixStep (w.drop (p + 1)).reverse M.suffixInit) w[p]) = _
    rw [hsuf]
    rfl

lemma flatten_gaps (M : Bimachine A B P S) (w : List A) (m : ℕ) (hm : w.length = m + 1) :
    ((List.range w.length).map
        (fun p => if p + 1 = w.length then gap M w p ++ gap M w (p + 1) else gap M w p)).flatten
      = ((List.range (w.length + 1)).map (gap M w)).flatten := by
  rw [hm]
  have hleft : ((List.range (m + 1)).map
      (fun p => if p + 1 = m + 1 then gap M w p ++ gap M w (p + 1) else gap M w p)).flatten
      = ((List.range m).map (gap M w)).flatten ++ (gap M w m ++ gap M w (m + 1)) := by
    rw [List.range_succ]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil]
    congr 1
    refine congrArg List.flatten (List.map_congr_left ?_)
    intro p hp
    have : p < m := List.mem_range.mp hp
    rw [if_neg (by omega)]
  rw [hleft, List.range_succ, List.range_succ]
  simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [List.append_assoc]

end FOBimachRelab

/-- **One implication of Theorem `thm:fo-rational-functions`.**  A function computed by an aperiodic
bimachine is a first-order relabelling. -/
theorem isFORelabelling_of_isAperiodicBimachine {A B : Type} [Finite A] {f : List A → List B}
    (h : IsAperiodicBimachine f) : IsFORelabelling f := by
  classical
  obtain ⟨P, S, hP, hS, M, hM, hpre, hsuf⟩ := h
  haveI := hP; haveI := hS
  -- the sentences describing the states of the two automata
  choose χ hχfo hχfree hχsat using fun q : P =>
    FODefinable.exists_sentence (foDefinable_state_lang M.prefixStep hpre M.prefixInit q)
  choose ξ hξfo hξfree hξsat using fun s : S =>
    FODefinable.exists_sentence (foDefinable_rev_state_lang M.suffixStep hsuf M.suffixInit s)
  have hsat : ∀ (w : List A) (p : ℕ), p < w.length → ∀ x : FOBimachRelab.Idx A P S,
      (MSO.Sat w (fun _ => p) (fun _ => ∅) (FOBimachRelab.formOf χ ξ x) ↔
        (strTrans M.prefixStep (w.take p) M.prefixInit = x.1 ∧ w[p]? = some x.2.1 ∧
          strTrans M.suffixStep (w.drop (p + 1)).reverse M.suffixInit = x.2.2.1 ∧
          ((p + 1 = w.length) ↔ x.2.2.2 = true))) := by
    intro w p hp x
    exact FOBimachRelab.sat_formOf hχfo hχfree (fun q u fo so => hχsat q u fo so)
      hξfo hξfree (fun s u fo so => hξsat s u fo so) w p hp x
  have hidx : ∀ (w : List A) (p : ℕ) (hp : p < w.length),
      MSO.Sat w (fun _ => p) (fun _ => ∅)
        (FOBimachRelab.formOf χ ξ (FOBimachRelab.idxAt M w p hp)) := by
    intro w p hp
    refine (hsat w p hp _).mpr ⟨rfl, ?_, rfl, by simp [FOBimachRelab.idxAt]⟩
    show w[p]? = some w[p]
    exact List.getElem?_eq_getElem hp
  have huniq : ∀ (w : List A) (p : ℕ), p < w.length →
      ∃! i : FOBimachRelab.Idx A P S,
        MSO.Sat w (fun _ => p) (fun _ => ∅) (FOBimachRelab.formOf χ ξ i) := by
    intro w p hp
    refine ⟨FOBimachRelab.idxAt M w p hp, hidx w p hp, ?_⟩
    rintro ⟨q, a, s, b⟩ hy
    obtain ⟨e1, e2, e3, e4⟩ := (hsat w p hp _).mp hy
    have e1' : strTrans M.prefixStep (w.take p) M.prefixInit = q := e1
    have e2' : w[p]? = some a := e2
    have e3' : strTrans M.suffixStep (w.drop (p + 1)).reverse M.suffixInit = s := e3
    have e4' : (p + 1 = w.length ↔ b = true) := e4
    have ha : a = w[p] := by
      rw [List.getElem?_eq_getElem hp] at e2'
      exact (Option.some.inj e2').symm
    have hb : b = decide (p + 1 = w.length) := by
      cases b with
      | false => simp only [Bool.false_eq_true, iff_false] at e4'; simp [e4']
      | true => simp only [iff_true] at e4'; simp [e4']
    show (q, a, s, b) = (_, _, _, _)
    rw [← e1', ha, ← e3', hb]
  refine ⟨{ Idx := FOBimachRelab.Idx A P S
            finIdx := inferInstance
            form := FOBimachRelab.formOf χ ξ
            out := FOBimachRelab.outOf M
            emptyOut := M.out M.prefixInit M.suffixInit
            unique := huniq },
    fun x => FOBimachRelab.isFO_formOf hχfo hξfo x, ?_⟩
  intro w
  subst hM
  show (w = [] ∧ _) ∨ (w ≠ [] ∧ _)
  rcases eq_or_ne w [] with rfl | hw
  · exact Or.inl ⟨rfl, by rw [M.eval_eq_evalFrom, M.evalFrom_nil]⟩
  · obtain ⟨m, hm⟩ : ∃ m, w.length = m + 1 := by
      cases hl : w.length with
      | zero => exact absurd (List.eq_nil_of_length_eq_zero hl) hw
      | succ m => exact ⟨m, rfl⟩
    have ha : ∃ a : A, a ∈ w := by
      cases w with
      | nil => exact absurd rfl hw
      | cons a u => exact ⟨a, by simp⟩
    obtain ⟨a₀, -⟩ := ha
    refine Or.inr ⟨hw, fun p => if hp : p < w.length then FOBimachRelab.idxAt M w p hp
      else (M.prefixInit, a₀, M.suffixInit, false), ?_, ?_⟩
    · intro p hp
      show MSO.Sat w (fun _ => p) (fun _ => ∅) (FOBimachRelab.formOf χ ξ
        (if hp : p < w.length then FOBimachRelab.idxAt M w p hp
          else (M.prefixInit, a₀, M.suffixInit, false)))
      rw [dif_pos hp]
      exact hidx w p hp
    · show M.eval w = ((List.range w.length).map
        (fun p => FOBimachRelab.outOf M
          (if hp : p < w.length then FOBimachRelab.idxAt M w p hp
            else (M.prefixInit, a₀, M.suffixInit, false)))).flatten
      rw [FOBimachRelab.eval_eq_flatten M w, ← FOBimachRelab.flatten_gaps M w m hm]
      refine congrArg List.flatten (List.map_congr_left ?_).symm
      intro p hp'
      have hp : p < w.length := List.mem_range.mp hp'
      rw [dif_pos hp, FOBimachRelab.out_idxAt M w p hp]

end Lax314295Proofs.Transducers
