/-
The string encoding of the reachable configuration graph, read off the annotation of the input.

The annotation of `TwoWayAnnot.lean` decorates each input position with the letters around it and
with enough information about the automaton `D` recognising the visited configurations to decide,
for every state `q` of the transducer, whether the run visits the cut to the left (or to the right)
of that position in the state `q`.  That is exactly the data that the slice of the reachable
configuration graph at that position consists of, so the encoding `TwoWay.enc M w` of a non-empty
input is a letter-to-letter image of the annotation (`TwoWay.enc_eq_map_annot`).

This file also proves that the correct annotations form a regular language
(`TwoWay.validLang_isRegular`): validity is the local consistency condition `TwoWay.LocalOK` between
consecutive annotation letters, which a deterministic automaton checks while scanning the string.
Together, these two facts are the book's "main observation" that the strings representing reachable
configuration graphs form a regular language; it is drawn in `ConfGraphReg.lean`.
-/
import Lax916827Proofs.Source.PartC.ConfGraph
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open scoped Classical

variable {A B Q S : Type}

/-! ## The slice determined by an annotation letter -/

/-- The slice of the reachable configuration graph that is described by an annotation letter. -/
noncomputable def sliceOfAnn (D : DFA (Marked A Q) S) (M : TwoWay A B Q) (c : AnnLet A S) :
    Slice Q (Lab M) := fun x =>
  if x.1 then
    (if onRunRight D c x.2 then edgeOf M (some c.letter) x.2 c.next false else VOut.nil)
  else
    (if onRunLeft D c x.2 then edgeOf M c.prev x.2 (some c.letter) true else VOut.nil)

variable (D : DFA (Marked A Q) S) (M : TwoWay A B Q)

/-- On a non-empty input, the string representation of the reachable configuration graph is a
letter-to-letter image of the annotation of the input. -/
theorem enc_eq_map_annot (hD : D.accepts = {z | (visitAut M).Accepts z}) {w : List A}
    (hw : w ≠ []) :
    enc M w = (annot D w).map (fun c => Sum.inl (sliceOfAnn D M c)) := by
  apply List.ext_getElem?
  intro j
  rcases Nat.lt_or_ge j w.length with hj | hj
  · rw [enc_getElem? hw hj, List.getElem?_map, annot_getElem D w hj]
    simp only [Option.map_some, Option.some.injEq]
    congr 1
    funext x
    obtain ⟨d, q⟩ := x
    set c : AnnLet A S := ((prevAt w j, w[j]'hj, w[j + 1]?), leftSt D (w.take j),
      rhoOf D (w.drop (j + 1))) with hc
    have hcann : (annot D w)[j]? = some c := annot_getElem D w hj
    have hletter : c.letter = w[j]'hj := rfl
    have hprev : c.prev = prevAt w j := rfl
    have hnext : c.next = w[j + 1]? := rfl
    cases d with
    | false =>
        show cutV M w j q true = _
        have hvis : onRunLeft D c q = true ↔ Visits M w (Cfg.conf (w.take j) q (w.drop j)) :=
          onRunLeft_iff D M hD w hj c hcann q
        by_cases hv : Visits M w (Cfg.conf (w.take j) q (w.drop j))
        · rw [cutV, if_pos hv]
          show _ = (if onRunLeft D c q then edgeOf M c.prev q (some c.letter) true else VOut.nil)
          rw [if_pos (hvis.mpr hv), hprev, hletter]
          congr 1
          exact List.getElem?_eq_getElem hj
        · rw [cutV, if_neg hv]
          show _ = (if onRunLeft D c q then edgeOf M c.prev q (some c.letter) true else VOut.nil)
          rw [if_neg (fun h => hv (hvis.mp h))]
    | true =>
        show cutV M w (j + 1) q false = _
        have hvis : onRunRight D c q = true ↔
            Visits M w (Cfg.conf (w.take (j + 1)) q (w.drop (j + 1))) :=
          onRunRight_iff D M hD w hj c hcann q
        have hprevat : prevAt w (j + 1) = some (w[j]'hj) := by
          rw [prevAt, if_neg (by omega)]
          simp
        by_cases hv : Visits M w (Cfg.conf (w.take (j + 1)) q (w.drop (j + 1)))
        · rw [cutV, if_pos hv, hprevat]
          show _ = (if onRunRight D c q then edgeOf M (some c.letter) q c.next false else VOut.nil)
          rw [if_pos (hvis.mpr hv), hletter, hnext]
        · rw [cutV, if_neg hv]
          show _ = (if onRunRight D c q then edgeOf M (some c.letter) q c.next false else VOut.nil)
          rw [if_neg (fun h => hv (hvis.mp h))]
  · rw [List.getElem?_eq_none (by rw [enc_length hw]; omega), List.getElem?_eq_none (by simp; omega)]

/-! ## The correct annotations form a regular language -/

/-- Local consistency of a string of annotation letters, checked from left to right, with `p` the
letter preceding the string. -/
def ValidFrom (D : DFA (Marked A Q) S) : Option (AnnLet A S) → List (AnnLet A S) → Prop
  | p, [] => LocalOK D p none
  | p, c :: rest => LocalOK D p (some c) ∧ ValidFrom D (some c) rest

lemma validFrom_iff (p : Option (AnnLet A S)) (z : List (AnnLet A S)) :
    ValidFrom D p z ↔ ∀ i ≤ z.length, LocalOK D (if i = 0 then p else z[i - 1]?) z[i]? := by
  induction z generalizing p with
  | nil =>
      constructor
      · intro h i hi
        have : i = 0 := by simpa using hi
        subst this
        simpa using h
      · intro h
        have := h 0 (by omega)
        simpa using this
  | cons c rest ih =>
      have hidx : ∀ k : ℕ,
          ((c :: rest)[k]? : Option (AnnLet A S)) = if k = 0 then some c else rest[k - 1]? := by
        intro k
        cases k with
        | zero => simp
        | succ k => simp
      constructor
      · rintro ⟨h0, hrest⟩ i hi
        cases i with
        | zero => simpa using h0
        | succ k =>
            have hk : k ≤ rest.length := by simpa using hi
            have h := (ih (some c)).mp hrest k hk
            rw [if_neg (by omega), show k + 1 - 1 = k from rfl, hidx k, List.getElem?_cons_succ]
            exact h
      · intro h
        refine ⟨by simpa using h 0 (by omega), (ih (some c)).mpr (fun k hk => ?_)⟩
        have h2 := h (k + 1) (by simpa using hk)
        rw [if_neg (by omega), show k + 1 - 1 = k from rfl, hidx k,
          List.getElem?_cons_succ] at h2
        exact h2

lemma valid_iff_validFrom (z : List (AnnLet A S)) : Valid D z ↔ ValidFrom D none z := by
  rw [validFrom_iff]
  rfl

/-- The state of the scanning automaton: the previous letter, or `none` if the check has already
failed. -/
private noncomputable def vstep (D : DFA (Marked A Q) S) :
    Option (Option (AnnLet A S)) → AnnLet A S → Option (Option (AnnLet A S))
  | some p, c => if LocalOK D p (some c) then some (some c) else none
  | none, _ => none

private def vacc (D : DFA (Marked A Q) S) : Set (Option (Option (AnnLet A S))) :=
  {s | ∃ p, s = some p ∧ LocalOK D p none}

private lemma vfoldl_none (z : List (AnnLet A S)) : z.foldl (vstep D) none = none := by
  induction z with
  | nil => rfl
  | cons c rest ih => simpa [vstep] using ih

private lemma vfoldl_iff (p : Option (AnnLet A S)) (z : List (AnnLet A S)) :
    z.foldl (vstep D) (some p) ∈ vacc D ↔ ValidFrom D p z := by
  induction z generalizing p with
  | nil =>
      simp only [List.foldl_nil]
      constructor
      · rintro ⟨p', hp', h⟩
        rw [Option.some.injEq] at hp'
        subst hp'
        exact h
      · intro h; exact ⟨p, rfl, h⟩
  | cons c rest ih =>
      by_cases hok : LocalOK D p (some c)
      · rw [List.foldl_cons, show vstep D (some p) c = some (some c) by simp [vstep, hok]]
        rw [ih (some c)]
        exact ⟨fun h => ⟨hok, h⟩, fun h => h.2⟩
      · rw [List.foldl_cons, show vstep D (some p) c = none by simp [vstep, hok]]
        rw [vfoldl_none]
        constructor
        · rintro ⟨p', hp', -⟩; exact absurd hp' (by simp)
        · rintro ⟨h, -⟩; exact absurd h hok

/-- **The correct annotations form a regular language.**  Validity is a local condition on
consecutive annotation letters, so a deterministic automaton can check it while scanning the
string. -/
theorem validLang_isRegular [Finite A] [Finite S] :
    Language.IsRegular {z : List (AnnLet A S) | Valid D z} := by
  have h := RegAut.isRegular_foldl (Γ := AnnLet A S) (vstep D) (some none) (vacc D)
  refine RegAut.isRegular_of_eq h (fun z => ?_)
  change Valid D z ↔ z.foldl (vstep D) (some none) ∈ vacc D
  rw [valid_iff_validFrom, ← vfoldl_iff D none z]

end TwoWay

end Lax916827Proofs.Transducers
