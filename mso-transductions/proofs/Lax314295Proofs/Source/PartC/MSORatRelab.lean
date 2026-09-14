/- Theorem `thm:logic-rational-functions` of *Transducers* (M. Bojańczyk): a string-to-string
function is rational if and only if it is definable by an mso relabelling.

Both inclusions go through bimachines (Theorem `thm:bimachines`), which is a convenient
deterministic presentation of the unambiguous one-way transducer used in the
book.

* rational ⊆ mso relabellings.  A bimachine outputs, in every gap of the input
  string, a string that depends on the state of the prefix automaton and on the
  state of the suffix automaton in that gap.  The relabelling has one formula
  per pair of such states (together with the information needed to attach the
  output of the last gap to the last position); the formula for a pair `(p, s)`
  says that the prefix automaton reaches `p` and the suffix automaton reaches
  `s` in the position `x₀`, which is a regular property of the string marked at
  `x₀`, and hence definable in mso by `MarkLogic.exists_form_of_regular`.  This
  is Claim `claim:transition-formula` of the book, which the book states in terms of the transitions
  of an unambiguous transducer.

* mso relabellings ⊆ rational.  Each formula of the relabelling gives a regular language of marked
  strings (Lemma `lem:mso-free-variables`, in the form `MarkStr.markedSat2`), and
  `MarkBimach.markFun` turns a finite family of such languages into a bimachine; the output in a
  position is the output string of the unique formula that holds there.  This is the second half of
  the proof in the book, where the same is done with the regular language of Claim
  `claim:mso-annotation-regular`.
-/
import Lax314295Proofs.Source.PartC.MarkLogic
import Lax314295Proofs.Source.PartC.MarkBimach
import Lax132576Proofs.Source.PartB.RationalStatements
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace RatRelab

open MarkStr MarkBimach

/-! ## From a bimachine to an mso relabelling -/

section OfBimachine

variable {A B P S : Type} (M : Bimachine A B P S)

/-- The state of the prefix automaton in the gap before the position `x`. -/
def preOf (w : List A) (x : ℕ) : P := strTrans M.prefixStep (w.take x) M.prefixInit

/-- The state of the suffix automaton in the gap before the position `x`. -/
def sufOf (w : List A) (x : ℕ) : S := strTrans M.suffixStep (w.drop x).reverse M.suffixInit

/-- The index of the formula that is true in the position `x`: the pair of
states of the bimachine in the gap before `x`, together with the state of the
prefix automaton at the end of the string if `x` is the last position (the
output of the last gap is attached to the last position). -/
def idxOf (w : List A) (x : ℕ) : (P × S) × Option P :=
  ((preOf M w x, sufOf M w x),
    if x + 1 = w.length then some (strTrans M.prefixStep w M.prefixInit) else none)

/-- The output string attached to an index. -/
def outOf (i : (P × S) × Option P) : List B :=
  M.out i.1.1 i.1.2 ++ (i.2.elim [] (fun p => M.out p M.suffixInit))

/-- The states of the automaton reading a marked string: the state of the
prefix automaton, and — after the mark has been read — the state of the prefix
automaton at the mark, the state transformation of the suffix automaton on the
part of the string from the mark on, and a bit saying whether the mark is not
the last position. -/
abbrev St (P S : Type) : Type := P × Option (P × (S → S) × Bool)

/-- The transition function of that automaton. -/
def stepM : St P S → Mark2 A → St P S := fun st z =>
  if z.2.1 then
    (M.prefixStep st.1 z.1, some (st.1, (fun s => M.suffixStep s z.1), false))
  else
    match st.2 with
    | none => (M.prefixStep st.1 z.1, none)
    | some (px, T, _) =>
        (M.prefixStep st.1 z.1, some (px, (fun s => T (M.suffixStep s z.1)), true))

/-- Its initial state. -/
def startM : St P S := (M.prefixInit, none)

lemma foldl_unmark2_none (u : List A) (p : P) :
    strTrans (stepM M) (unmark2 u) ((p, none) : St P S) =
      (strTrans M.prefixStep u p, none) := by
  induction u generalizing p with
  | nil => rfl
  | cons a u ih =>
      have : strTrans (stepM M) (unmark2 (a :: u)) ((p, none) : St P S) =
          strTrans (stepM M) (unmark2 u) ((M.prefixStep p a, none) : St P S) := rfl
      rw [this, ih]
      rfl

lemma foldl_unmark2_some (u : List A) (p px : P) (T : S → S) (b : Bool) :
    strTrans (stepM M) (unmark2 u) ((p, some (px, T, b)) : St P S) =
      (strTrans M.prefixStep u p,
        some (px, (fun s => T (strTrans M.suffixStep u.reverse s)), b || decide (u ≠ []))) := by
  induction u generalizing p T b with
  | nil => simp [strTrans]
  | cons a u ih =>
      have hstep : strTrans (stepM M) (unmark2 (a :: u)) ((p, some (px, T, b)) : St P S) =
          strTrans (stepM M) (unmark2 u)
            ((M.prefixStep p a, some (px, (fun s => T (M.suffixStep s a)), true)) : St P S) := rfl
      rw [hstep, ih]
      have hfun : (fun s => T (M.suffixStep (strTrans M.suffixStep u.reverse s) a))
          = (fun s => T (strTrans M.suffixStep (a :: u).reverse s)) := by
        funext s
        refine congrArg T ?_
        rw [List.reverse_cons]
        simp [strTrans, List.foldl_append]
      have hbool : (true || decide (u ≠ [])) = (b || decide ((a :: u) ≠ [])) := by simp
      exact Prod.ext rfl (congrArg some (Prod.ext rfl (Prod.ext hfun hbool)))

lemma foldl_markAt2_diag (w : List A) (x : ℕ) (hx : x < w.length) :
    strTrans (stepM M) (markAt2 w x x) (startM M) =
      (strTrans M.prefixStep w M.prefixInit,
        some (preOf M w x, (fun s => strTrans M.suffixStep (w.drop x).reverse s),
          decide (x + 1 < w.length))) := by
  have hw : w.take x ++ w[x] :: w.drop (x + 1) = w := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  rw [markAt2_diag w x hx]
  rw [show strTrans (stepM M) (unmark2 (w.take x) ++ (w[x], true, true) ::
      unmark2 (w.drop (x + 1))) (startM M) =
      strTrans (stepM M) ((w[x], true, true) :: unmark2 (w.drop (x + 1)))
        (strTrans (stepM M) (unmark2 (w.take x)) (startM M)) by
    simp [strTrans, List.foldl_append]]
  rw [show startM M = ((M.prefixInit, none) : St P S) from rfl, foldl_unmark2_none]
  have hstep : strTrans (stepM M) ((w[x], true, true) :: unmark2 (w.drop (x + 1)))
      ((strTrans M.prefixStep (w.take x) M.prefixInit, none) : St P S) =
      strTrans (stepM M) (unmark2 (w.drop (x + 1)))
        ((M.prefixStep (strTrans M.prefixStep (w.take x) M.prefixInit) w[x],
          some (strTrans M.prefixStep (w.take x) M.prefixInit,
            (fun s => M.suffixStep s w[x]), false)) : St P S) := rfl
  rw [hstep, foldl_unmark2_some]
  refine Prod.ext ?_ (congrArg some (Prod.ext rfl (Prod.ext ?_ ?_)))
  · show strTrans M.prefixStep (w.drop (x + 1))
      (M.prefixStep (strTrans M.prefixStep (w.take x) M.prefixInit) w[x]) = _
    conv_rhs => rw [← hw]
    simp only [strTrans, List.foldl_append, List.foldl_cons]
  · funext s
    show M.suffixStep (strTrans M.suffixStep (w.drop (x + 1)).reverse s) w[x] = _
    rw [show w.drop x = w[x] :: w.drop (x + 1) from (List.drop_eq_getElem_cons hx)]
    rw [List.reverse_cons]
    simp [strTrans, List.foldl_append]
  · show (false || decide (w.drop (x + 1) ≠ [])) = decide (x + 1 < w.length)
    simp only [Bool.false_or]
    refine decide_eq_decide.2 ?_
    constructor
    · intro hne
      by_contra hcon
      exact hne (List.drop_eq_nil_of_le (by omega))
    · intro hlt hcon
      have : (w.drop (x + 1)).length = 0 := by rw [hcon]; rfl
      rw [List.length_drop] at this
      omega

open scoped Classical in
/-- The set of states of the marked automaton that witness the index `i`. -/
def accSet (i : (P × S) × Option P) : Set (St P S) :=
  {st | ∃ px T b, st.2 = some (px, T, b) ∧ px = i.1.1 ∧ T M.suffixInit = i.1.2 ∧
    (if b then i.2 = none else i.2 = some st.1)}

open scoped Classical in
lemma mem_accSet_iff (w : List A) (x : ℕ) (hx : x < w.length) (i : (P × S) × Option P) :
    strTrans (stepM M) (markAt2 w x x) (startM M) ∈ accSet M i ↔ idxOf M w x = i := by
  rw [foldl_markAt2_diag M w x hx, accSet]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨px, T, b, heq, hpx, hT, hlast⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    refine Prod.ext (Prod.ext hpx hT) ?_
    rw [idxOf]
    by_cases hb : x + 1 < w.length
    · rw [if_pos (by simpa using hb)] at hlast
      rw [hlast, if_neg (by omega)]
    · rw [if_neg (by simpa using hb)] at hlast
      rw [hlast, if_pos (by omega)]
  · rintro rfl
    refine ⟨preOf M w x, (fun s => strTrans M.suffixStep (w.drop x).reverse s),
      decide (x + 1 < w.length), rfl, rfl, rfl, ?_⟩
    rw [idxOf]
    by_cases hb : x + 1 < w.length
    · rw [if_pos (by simpa using hb), if_neg (by omega)]
    · rw [if_neg (by simpa using hb), if_pos (by omega)]

variable [Finite A] [Finite P] [Finite S]

open scoped Classical in
omit [Finite A] in
lemma isRegular_idx (i : (P × S) × Option P) :
    Language.IsRegular {u : List (Mark2 A) | strTrans (stepM M) u (startM M) ∈ accSet M i} :=
  RegAut.isRegular_foldl (stepM M) (startM M) (accSet M i)

open scoped Classical in
/-- **Claim `claim:transition-formula`** (the internal step of Theorem
`thm:logic-rational-functions`), for a bimachine: for every index there is an mso formula with one
free variable that selects the positions with that index. -/
lemma exists_form (i : (P × S) × Option P) :
    ∃ φ : MSO A, ∀ (w : List A) (x : ℕ), x < w.length →
      (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ idxOf M w x = i) := by
  obtain ⟨φ, hφ⟩ := MarkLogic.exists_form_of_regular _ (isRegular_idx M i)
  refine ⟨φ, fun w x hx => ?_⟩
  rw [hφ w x]
  exact mem_accSet_iff M w x hx i

end OfBimachine

/-! ## The output of a bimachine, position by position -/

lemma flatten_extra {B : Type} (n : ℕ) (hn : 0 < n) (g : ℕ → List B) :
    ((List.range n).map (fun x => g x ++ (if x + 1 = n then g n else []))).flatten
      = ((List.range (n + 1)).map g).flatten := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ (n := m + 1), List.range_succ (n := m), List.map_append, List.map_append]
  have hcongr : (List.range m).map (fun x => g x ++ (if x + 1 = m + 1 then g (m + 1) else []))
      = (List.range m).map g := by
    refine List.map_congr_left (fun x hx => ?_)
    rw [List.mem_range] at hx
    rw [if_neg (by omega), List.append_nil]
  rw [hcongr]
  simp

section Eval

variable {A B P S : Type} (M : Bimachine A B P S)

lemma eval_eq_flatten (w : List A) (hw : w ≠ []) :
    M.eval w = ((List.range w.length).map (fun x => outOf M (idxOf M w x))).flatten := by
  have hn : 0 < w.length := List.length_pos_iff.2 hw
  have h1 : preOf M w w.length = strTrans M.prefixStep w M.prefixInit := by
    rw [preOf, List.take_of_length_le (le_refl _)]
  have h2 : sufOf M w w.length = M.suffixInit := by
    rw [sufOf, List.drop_of_length_le (le_refl _)]
    rfl
  have hg : ∀ x, outOf M (idxOf M w x) =
      M.out (preOf M w x) (sufOf M w x) ++
        (if x + 1 = w.length then M.out (preOf M w w.length) (sufOf M w w.length) else []) := by
    intro x
    have hunfold : outOf M (idxOf M w x) = M.out (preOf M w x) (sufOf M w x) ++
        ((if x + 1 = w.length then some (strTrans M.prefixStep w M.prefixInit) else none).elim []
          (fun p => M.out p M.suffixInit)) := rfl
    rw [hunfold, h1, h2]
    by_cases hx : x + 1 = w.length
    · rw [if_pos hx, if_pos hx]
      rfl
    · rw [if_neg hx, if_neg hx]
      rfl
  have hmap : (List.range w.length).map (fun x => outOf M (idxOf M w x)) =
      (List.range w.length).map (fun x =>
        M.out (preOf M w x) (sufOf M w x) ++
          (if x + 1 = w.length then M.out (preOf M w w.length) (sufOf M w w.length) else [])) :=
    List.map_congr_left (fun x _ => hg x)
  rw [hmap, flatten_extra w.length hn (fun i => M.out (preOf M w i) (sufOf M w i))]
  rfl

end Eval

/-! ## Theorem `thm:logic-rational-functions` -/

section Main

variable {A B : Type} [Finite A] [Finite B]

open scoped Classical in
/-- A rational function is definable by an mso relabelling. -/
theorem msoRelabelling_of_isRationalFun {f : List A → List B} (hf : IsRationalFun f) :
    IsMSORelabelling f := by
  obtain ⟨P, S, hP, hS, M, hM⟩ := (rational_iff_unambiguous_iff_bimachine f).out 0 2 |>.1 hf
  haveI := hP
  haveI := hS
  subst hM
  choose form hform using (fun i => exists_form M i)
  refine ⟨{ Idx := (P × S) × Option P
            finIdx := inferInstance
            form := form
            out := outOf M
            emptyOut := M.out M.prefixInit M.suffixInit
            unique := ?_ }, ?_⟩
  · intro w p hp
    refine ⟨idxOf M w p, (hform _ w p hp).2 rfl, fun i hi => ?_⟩
    exact ((hform i w p hp).1 hi).symm
  · intro w
    by_cases hw : w = []
    · subst hw
      exact Or.inl ⟨rfl, by simp [Bimachine.eval_eq_evalFrom]⟩
    · refine Or.inr ⟨hw, idxOf M w, fun p hp => (hform _ w p hp).2 rfl, ?_⟩
      exact eval_eq_flatten M w hw

open scoped Classical in
/-- A function definable by an mso relabelling is rational. -/
theorem isRationalFun_of_msoRelabelling {f : List A → List B} (hf : IsMSORelabelling f) :
    IsRationalFun f := by
  obtain ⟨R, hR⟩ := hf
  haveI := R.finIdx
  have hreg : ∀ i : R.Idx, (markedSat2 (R.form i)).IsRegular := fun i => isRegular_markedSat2 _
  choose σ hσ D hD using hreg
  haveI : ∀ i, Finite (σ i) := fun i => @Finite.of_fintype _ (hσ i)
  -- the truth value of the formula `i` in the position `x`
  set bitOf : A → ((i : R.Idx) → σ i × (σ i → σ i)) → R.Idx → Prop :=
    fun a g i => (g i).2 ((D i).step (g i).1 (a, true, true)) ∈ (D i).accept with hbit
  set h : A → ((i : R.Idx) → σ i × (σ i → σ i)) → List B :=
    fun a g => if hex : ∃ i, bitOf a g i then R.out hex.choose else [] with hh
  have hbit_iff : ∀ (w : List A) (x : ℕ) (hx : x < w.length), ∀ i : R.Idx,
      bitOf w[x] (fun i => (markPreSt D w x i, sufTr D w x i)) i ↔
        MSO.Sat w (fun _ => x) (fun _ => ∅) (R.form i) := by
    intro w x hx i
    rw [hbit]
    simp only [sufTr, markPreSt]
    rw [← eval_markAt2_diag (D i) w x hx, hD i]
    rw [markAt2_mem_markedSat2 (R.form i) w x x hx hx]
    have : (fun j => if j = 0 then x else x) = (fun _ : ℕ => x) := by
      funext j; simp
    rw [this]
  have hfeq : f = markFun D h R.emptyOut := by
    funext w
    by_cases hw : w = []
    · subst hw
      rcases hR [] with ⟨-, hv⟩ | ⟨hne, -⟩
      · rw [hv, markFun, if_pos rfl]
      · exact absurd rfl hne
    · rcases hR w with ⟨hnil, -⟩ | ⟨-, g, hg, hv⟩
      · exact absurd hnil hw
      · rw [hv, markFun, if_neg hw]
        refine congrArg List.flatten (List.map_congr_left (fun x hx => ?_)).symm
        rw [List.mem_range] at hx
        rw [posOut, List.getElem?_eq_getElem hx]
        show h w[x] (fun i => (markPreSt D w x i, sufTr D w x i)) = R.out (g x)
        have hgx : bitOf w[x] (fun i => (markPreSt D w x i, sufTr D w x i)) (g x) :=
          (hbit_iff w x hx (g x)).2 (hg x hx)
        have hex : ∃ i, bitOf w[x] (fun i => (markPreSt D w x i, sufTr D w x i)) i := ⟨g x, hgx⟩
        rw [hh]
        simp only [dif_pos hex]
        obtain ⟨i₀, -, huniq⟩ := R.unique w x hx
        have h1 := (hbit_iff w x hx hex.choose).1 hex.choose_spec
        rw [huniq _ h1, huniq _ (hg x hx)]
  rw [hfeq]
  exact isRationalFun_markFun D h R.emptyOut

end Main

end RatRelab

/-- **Theorem `thm:logic-rational-functions`.**  A string-to-string function is rational if and only
if it is definable by an mso relabelling. -/
theorem rational_iff_msoRelabelling_aux {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ IsMSORelabelling f :=
  ⟨RatRelab.msoRelabelling_of_isRationalFun, RatRelab.isRationalFun_of_msoRelabelling⟩

end Lax314295Proofs.Transducers
