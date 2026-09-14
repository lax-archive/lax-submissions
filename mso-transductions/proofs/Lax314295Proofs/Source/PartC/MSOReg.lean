/- Every mso transduction is a regular function: the hard half of Theorem
`thm:logic-regular-functions` of *Transducers* (M. Bojańczyk).

The proof follows the book.  Let `f` be defined by an mso transduction.

* By Lemma `lem:logic-reduction-to-type-n` (`MSOTransduction.exists_norm`, in
  `RequestProject/PartC/MSONorm.lean`) the transduction is *normalised*: on a
  non-empty input its output is presented by a list of pairs (tag, position)
  enumerated in the order given by the order formula.
* The walking transducer of `RequestProject/PartC/WalkAut.lean` walks that list.
  The questions it asks are the mso formulas of
  `RequestProject/PartC/MSOWalkForms.lean`: the unary ones ("is this element the
  last one?", "does its successor sit in the same position, or to the right?",
  "which letter does it carry?", "is it the first element?") and the two binary
  ones ("is the element at the right-hand marked position the successor of the
  element at the left-hand one?", and its mirror image).
* Lemma `lem:logic-precomputation` (`mso_formulas_via_rational`) precomputes the answers: it
  provides a letter-to-letter *rational* function `pre : A* → C*` such that the
  unary questions become sets of letters of `pre w` and the binary ones become
  regular languages of infixes of `pre w`.  The infix languages are read by a
  finite family of deterministic automata, whose product (together with the last
  letter read) is the automaton carried by the walking transducer;
  `RequestProject/PartC/MSOWalkData.lean` assembles this and proves that the
  walking transducer computes `f w` on the input `pre w`.
* Finally `f` is the composition of the rational function `pre` with the function computed by the
  walking transducer, and the latter is regular by Theorem `thm:2dfa-decomposition-into-primes`.
  Instead of the two-way transducer itself -- which need not halt on the strings of `C*` that are
  not of the form `pre w` -- we use its *width-bounded output* `TwoWay.widthOut`, which is a total
  function, is regular by the snake lemma, and agrees with the run wherever the run halts.

The converse implication (every regular function is an mso transduction) is
`Transducers.isMSOTransduction_of_isTwoWay`, in
`RequestProject/PartC/TwoWayMSO.lean`.
-/
import Lax314295Proofs.Source.PartC.MSOWalkData
import Lax314295Proofs.Source.PartC.MSOPrecomp
import Lax916827Proofs.Source.PartC.SnakeReg
import Lax314295Proofs.Source.PartC.TwoWayMSO
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace MSOReg

open MSO NormT WalkAut MSOWalk

variable {A B : Type} [Finite A] [Finite B]

/-! ## The formulas that are precomputed -/

/-- The index of the unary questions of the walking transducer. -/
abbrev UIdx (N : NormT A B) : Type :=
  (N.Tag × B) ⊕ N.Tag ⊕ N.Tag ⊕ N.Tag ⊕ (N.Tag × N.Tag)

/-- The unary questions: the letter formulas, "is this the last element", "is
this the first element", "is the successor to the right" and "is the successor
in the same position with the given tag". -/
noncomputable def uForm (N : NormT A B) : UIdx N → MSO A
  | Sum.inl (t, b) => N.Lb t b
  | Sum.inr (Sum.inl t) => N.isMaxF (tagList N) t
  | Sum.inr (Sum.inr (Sum.inl t)) => N.isMinF (tagList N) t
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => N.succRF (tagList N) t
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, t')))) => N.succHF (tagList N) t t'

/-- The binary questions: "is the element with tag `t'` at the right-hand marked
position the successor of the element with tag `t` at the left-hand one", and
the same question with the two positions exchanged. -/
noncomputable def bForm (N : NormT A B) : QIdx N → MSO A
  | Sum.inl (t, t') => N.isSuccF (tagList N) t t'
  | Sum.inr (t, t') => N.isSuccSwapF (tagList N) t t'

/-! ## From an mso transduction to a regular function -/

open TwoWay in
/-- **Theorem `thm:logic-regular-functions`, left-to-right implication.**  Every string-to-string
mso transduction defines a regular function. -/
theorem isRegularFun_of_isMSOTransduction {f : List A → List B}
    (hf : IsMSOTransduction f) : IsRegularFun f := by
  classical
  obtain ⟨T, hP, hout⟩ := hf
  rcases isEmpty_or_nonempty B with hB | hB
  · -- there is no letter at all, so every output is empty
    have hnil : ∀ w : List A, f w = [] := by
      intro w
      exact List.eq_nil_iff_forall_not_mem.2 (fun b _ => hB.false b)
    refine (isRegularFun_homOf (fun _ : A => ([] : List B))).congr (fun w => ?_)
    rw [hnil w, homOf]
    simp
  -- the normalised transduction
  obtain ⟨N, hNProp, hNPres⟩ := MSOTransduction.exists_norm T hP
  haveI := N.finTag
  -- the enumeration of the elements of the output, for every non-empty input
  have hex : ∀ w : List A, ∃ es : List N.Elt, 0 < w.length → N.Presents w es (f w) := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨es, hes⟩ := hNPres w (f w) hw (hout w)
      exact ⟨es, fun _ => hes⟩
    · exact ⟨[], fun h => absurd h hw⟩
  choose esf hesf using hex
  -- the precomputation of Lemma `lem:logic-precomputation`
  obtain ⟨C, hC, pre, hrat, hlenpre, h1, h2⟩ :=
    mso_formulas_via_rational_aux (Set.range (uForm N)) (Set.range (bForm N))
      (Set.finite_range _) (Set.finite_range _)
  haveI : Finite C := hC
  -- the sets of letters answering the unary questions
  have hu : ∀ k : UIdx N, ∃ F : Set C, ∀ (w : List A) (x : ℕ), x < w.length →
      (MSO.Sat w (fun _ => x) (fun _ => ∅) (uForm N k) ↔ ∃ c ∈ F, (pre w)[x]? = some c) :=
    fun k => h1 _ ⟨k, rfl⟩
  choose UF hUF using hu
  -- the automata answering the binary questions
  have hb : ∀ k : QIdx N, ∃ L : Language C, L.IsRegular ∧ ∀ (w : List A) (x y : ℕ),
      x ≤ y → y < w.length →
      (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) (bForm N k) ↔
        ((pre w).drop x).take (y - x + 1) ∈ L) :=
    fun k => h2 _ ⟨k, rfl⟩
  choose Lang hLangReg hLangSpec using hb
  choose sig hsigFin Mach hMach using hLangReg
  haveI : ∀ k, Finite (sig k) := fun k => @Finite.of_fintype _ (hsigFin k)
  -- the segment read by the automata
  have hseg : ∀ (z : List C) (x y : ℕ), x ≤ y →
      (z.take (y + 1)).drop x = (z.drop x).take (y - x + 1) := by
    intro z x y hxy
    rw [show y - x + 1 = y + 1 - x by omega]
    simp [List.drop_take]
  -- the specifications in the form required by `computes_walkData`
  have hFlb : ∀ (t : N.Tag) (b : B) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ UF (Sum.inl (t, b)) ↔ MSO.Sat w (fun _ => x) (fun _ => ∅) (N.Lb t b)) :=
    fun t b => letter_mem_iff (hUF (Sum.inl (t, b)))
  have hFMax : ∀ (t : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ UF (Sum.inr (Sum.inl t)) ↔
          MSO.Sat w (fun _ => x) (fun _ => ∅) (N.isMaxF (tagList N) t)) :=
    fun t => letter_mem_iff (hUF (Sum.inr (Sum.inl t)))
  have hFMin : ∀ (t : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ UF (Sum.inr (Sum.inr (Sum.inl t))) ↔
          MSO.Sat w (fun _ => x) (fun _ => ∅) (N.isMinF (tagList N) t)) :=
    fun t => letter_mem_iff (hUF (Sum.inr (Sum.inr (Sum.inl t))))
  have hFR : ∀ (t : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ UF (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))) ↔
          MSO.Sat w (fun _ => x) (fun _ => ∅) (N.succRF (tagList N) t)) :=
    fun t => letter_mem_iff (hUF (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))))
  have hFH : ∀ (t t' : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ UF (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, t'))))) ↔
          MSO.Sat w (fun _ => x) (fun _ => ∅) (N.succHF (tagList N) t t')) :=
    fun t t' => letter_mem_iff (hUF (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, t'))))))
  have hMS : ∀ (t t' : N.Tag) (w : List A) (x y : ℕ), x ≤ y → y < w.length →
      (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅)
          (N.isSuccF (tagList N) t t') ↔
        ((pre w).take (y + 1)).drop x ∈ (Mach (Sum.inl (t, t'))).accepts) := by
    intro t t' w x y hxy hy
    rw [hMach (Sum.inl (t, t')), hseg _ x y hxy]
    exact hLangSpec (Sum.inl (t, t')) w x y hxy hy
  have hML : ∀ (t t' : N.Tag) (w : List A) (x y : ℕ), x ≤ y → y < w.length →
      (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅)
          (N.isSuccSwapF (tagList N) t t') ↔
        ((pre w).take (y + 1)).drop x ∈ (Mach (Sum.inr (t, t'))).accepts) := by
    intro t t' w x y hxy hy
    rw [hMach (Sum.inr (t, t')), hseg _ x y hxy]
    exact hLangSpec (Sum.inr (t, t')) w x y hxy hy
  -- the walking transducer
  have hcomp := computes_walkData N Mach pre f esf
    (fun t b => UF (Sum.inl (t, b))) (fun t => UF (Sum.inr (Sum.inl t)))
    (fun t => UF (Sum.inr (Sum.inr (Sum.inl t))))
    (fun t => UF (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))))
    (fun t t' => UF (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, t'))))))
    hlenpre hNProp hesf hFlb hFMax hFMin hFR hFH hMS hML
  set D := walkData N Mach (f [])
    (fun t b => UF (Sum.inl (t, b))) (fun t => UF (Sum.inr (Sum.inl t)))
    (fun t => UF (Sum.inr (Sum.inr (Sum.inl t))))
    (fun t => UF (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))))
    (fun t t' => UF (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, t')))))) with hD
  -- its width-bounded output is a regular function agreeing with `f` after `pre`
  haveI : Finite (PSt C (QIdx N) sig) := inferInstance
  haveI : Finite (St N.Tag (PSt C (QIdx N) sig)) := inferInstance
  have hreg : IsRegularFun (widthOut (aut D) (Nat.card (St N.Tag (PSt C (QIdx N) sig)))) :=
    boundedWidth_isRegular _ _
  have hval : ∀ w, widthOut (aut D) (Nat.card (St N.Tag (PSt C (QIdx N) sig))) (pre w) = f w := by
    intro w
    obtain ⟨Tm, hTm, -⟩ := exists_halt_time (aut D) (pre w) (hcomp w)
    rw [widthOut, if_pos (widthLe_card (aut D) (pre w) hTm),
      runOut_eq (aut D) (pre w) (hcomp w)]
  exact IsRegularFun.comp' (IsRegularFun.of_rational hrat) hreg (fun w => (hval w).symm)

end MSOReg

export MSOReg (isRegularFun_of_isMSOTransduction)

end Lax314295Proofs.Transducers
