/-
The machine independent characterisation of subsequential functions
(Theorem `thm:subsequential-functions`).

The transducer constructed here reads the input and outputs the non-branching
part `alpha D w` of the prefix `w` read so far, with a delay of `M` letters,
where `M` is the deletion bound of `SubseqBound.lean`: the last `M` letters of
`alpha D w` are kept in a buffer, because they may still be deleted, and the
buffer is flushed whenever it gets longer than `2 * M`.  Its state consists of
the Myhill-Nerode state of `w` (which determines the increment of the
non-branching part, `incr_congr`) together with the buffer.  At the end of the
input, the buffer is emitted together with the branching part `endOut D w`,
which is also determined by the state.

Since a sequential transducer produces no output before reading a letter, while
the non-branching part `alpha D []` of the empty input is already nonempty in
general, the state carries in addition a boolean flag recording whether the
initial output `out0` (the permanent part of `alpha D []`) has been emitted; it
is emitted with the first letter, or by the end-of-input function if the input
is empty.
-/
import Lax132576Proofs.Source.PartB.SubseqBound
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Subseq

variable {A B : Type} (D : Data A B)

/-! ## The buffer -/

/-- Flushing the buffer: if it is longer than `2 * M`, all but its last `M`
letters are emitted. -/
noncomputable def trim (M : ℕ) (p : List B) : List B × List B :=
  if p.length ≤ 2 * M then ([], p) else (p.take (p.length - M), p.drop (p.length - M))

lemma trim_append (M : ℕ) (p : List B) : (trim M p).1 ++ (trim M p).2 = p := by
  unfold trim
  split <;> simp

lemma trim_snd_length_le (M : ℕ) (p : List B) : (trim M p).2.length ≤ 2 * M := by
  unfold trim
  split
  · simpa
  · simp only [List.length_drop]
    omega

/-! ## The initial output -/

/-- The part of the non-branching part of the empty input that is permanent, and
is emitted with the first letter. -/
noncomputable def out0 (M : ℕ) : List B := (alpha D []).take ((alpha D []).length - M)

/-- The initial contents of the buffer: the part of `alpha D []` that may still
be deleted. -/
noncomputable def buf0 (M : ℕ) : List B := (alpha D []).drop ((alpha D []).length - M)

lemma out0_append_buf0 (M : ℕ) : out0 D M ++ buf0 D M = alpha D [] :=
  List.take_append_drop _ _

lemma buf0_length_le (M : ℕ) : (buf0 D M).length ≤ 2 * M := by
  simp only [buf0, List.length_drop]
  omega

/-! ## The transducer -/

/-- A representative of a state. -/
noncomputable def rep (s : Set.range (state D)) : List A := s.2.choose

lemma state_rep (s : Set.range (state D)) : state D (rep D s) = s.val := s.2.choose_spec

/-- The state reached from `s` by reading the letter `a`. -/
noncomputable def stepSt (s : Set.range (state D)) (a : A) : Set.range (state D) :=
  ⟨state D (rep D s ++ [a]), ⟨rep D s ++ [a], rfl⟩⟩

lemma stepSt_eq {s : Set.range (state D)} {w : List A} (hw : state D w = s.val) (a : A) :
    (stepSt D s a).val = state D (w ++ [a]) := by
  have h : state D (rep D s) = state D w := by rw [state_rep, hw]
  exact state_append_congr D h [a]

/-- The subsequential transducer computing `D.f`. -/
noncomputable def transducer (M : ℕ) :
    Subsequential A B (Bool × Set.range (state D) × {p : List B // p.length ≤ 2 * M}) where
  init := (false, ⟨state D [], ⟨[], rfl⟩⟩, ⟨buf0 D M, buf0_length_le D M⟩)
  step := fun q a =>
    let dt := incr D (rep D q.2.1) a
    let p := q.2.2.val.take (q.2.2.val.length - dt.1) ++ dt.2
    ((true, stepSt D q.2.1 a, ⟨(trim M p).2, trim_snd_length_le M p⟩),
      (if q.1 then [] else out0 D M) ++ (trim M p).1)
  endOfInput := fun q =>
    (endOut D (rep D q.2.1)).map (fun u => (if q.1 then [] else out0 D M) ++ (q.2.2.val ++ u))

/-- The state of the transducer after reading `w`. -/
noncomputable def stQ (M : ℕ) (w : List A) :
    Bool × Set.range (state D) × {p : List B // p.length ≤ 2 * M} :=
  strTrans (transducer D M).toSequential.transFun w (transducer D M).toSequential.init

/-- The output produced after reading `w`, including the initial output if it
has not been emitted yet. -/
noncomputable def outOf (M : ℕ) (w : List A) : List B :=
  (if (stQ D M w).1 then [] else out0 D M) ++ (transducer D M).toSequential.eval w

/-- The contents of the buffer after reading `w`. -/
noncomputable def bufOf (M : ℕ) (w : List A) : List B := (stQ D M w).2.2.val

/-- The buffer contents before trimming, after reading one more letter. -/
noncomputable def pstep (M : ℕ) (w : List A) (a : A) : List B :=
  (bufOf D M w).take ((bufOf D M w).length - (incr D (rep D (stQ D M w).2.1) a).1)
    ++ (incr D (rep D (stQ D M w).2.1) a).2

lemma stQ_append (M : ℕ) (w : List A) (a : A) :
    stQ D M (w ++ [a]) = (transducer D M).toSequential.transFun (stQ D M w) a := by
  simp [stQ, strTrans]

lemma flag_append (M : ℕ) (w : List A) (a : A) : (stQ D M (w ++ [a])).1 = true := by
  rw [stQ_append]
  rfl

lemma flag_eq (M : ℕ) (w : List A) : (stQ D M w).1 = true ∨ w = [] := by
  rcases List.eq_nil_or_concat w with rfl | ⟨w', b, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl (by simpa [List.concat_eq_append] using flag_append D M w' b)

lemma stQ_state_append (M : ℕ) (w : List A) (a : A) :
    (stQ D M (w ++ [a])).2.1 = stepSt D (stQ D M w).2.1 a := by
  rw [stQ_append]
  rfl

lemma bufOf_nil (M : ℕ) : bufOf D M [] = buf0 D M := rfl

lemma eval_nil (M : ℕ) : (transducer D M).toSequential.eval ([] : List A) = [] := rfl

lemma flag_nil (M : ℕ) : (stQ D M ([] : List A)).1 = false := rfl

lemma outOf_nil (M : ℕ) : outOf D M [] = out0 D M := by
  rw [outOf, eval_nil, flag_nil]
  simp

lemma bufOf_append (M : ℕ) (w : List A) (a : A) :
    bufOf D M (w ++ [a]) = (trim M (pstep D M w a)).2 := by
  rw [bufOf, stQ_append]
  rfl

lemma eval_append_single (M : ℕ) (w : List A) (a : A) :
    (transducer D M).toSequential.eval (w ++ [a]) =
      (transducer D M).toSequential.eval w ++
        ((if (stQ D M w).1 then [] else out0 D M) ++ (trim M (pstep D M w a)).1) := by
  rw [Sequential.eval_append]
  congr 1
  simp only [Sequential.run, List.append_nil]
  rfl

lemma outOf_append (M : ℕ) (w : List A) (a : A) :
    outOf D M (w ++ [a]) = outOf D M w ++ (trim M (pstep D M w a)).1 := by
  have hL : outOf D M (w ++ [a]) = (transducer D M).toSequential.eval (w ++ [a]) := by
    rw [outOf, flag_append]
    simp
  rw [hL, eval_append_single, outOf]
  rcases flag_eq D M w with hf | rfl
  · rw [hf]
    simp
  · rw [eval_nil]
    simp

/-- The second component of the state of the transducer after reading `w` is the
Myhill-Nerode state of `w`. -/
lemma transducer_state (M : ℕ) (w : List A) : (stQ D M w).2.1.val = state D w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [stQ_state_append, stepSt_eq D ih.symm a]

/-- The main invariant: after reading `w`, the transducer has produced the
non-branching part of `w` minus the contents of its buffer, and everything it
has produced is permanent. -/
lemma transducer_run (M : ℕ)
    (hM : ∀ w v : List A, w ++ v ∈ Pre D.f → -(M : ℤ) ≤ dl D w v)
    {w : List A} (hw : w ∈ Pre D.f) :
    outOf D M w ++ bufOf D M w = alpha D w ∧
      ∀ v : List A, w ++ v ∈ Pre D.f → outOf D M w <+: alpha D (w ++ v) := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_⟩
    · rw [outOf_nil, bufOf_nil]
      exact out0_append_buf0 D M
    · intro v hv
      rw [outOf_nil, out0]
      exact alpha_stable D hM [] v hv
  | append_singleton w a ih =>
    have hw' : w ∈ Pre D.f := mem_pre_of_append hw
    obtain ⟨hinv, hsafe⟩ := ih hw'
    have hrep : state D (rep D (stQ D M w).2.1) = state D w := by
      rw [state_rep, transducer_state]
    have hincr : incr D (rep D (stQ D M w).2.1) a = incr D w a :=
      (incr_congr D hrep.symm hw).symm
    have hp : pstep D M w a =
        (bufOf D M w).take ((bufOf D M w).length - (incr D w a).1) ++ (incr D w a).2 := by
      rw [pstep, hincr]
    have hsafe_a : outOf D M w <+: alpha D (w ++ [a]) := hsafe [a] hw
    have hpre_alpha : outOf D M w <+: alpha D w := ⟨bufOf D M w, hinv⟩
    have hL : outOf D M w <+: lcp2 (alpha D w) (alpha D (w ++ [a])) :=
      prefix_lcp2 hpre_alpha hsafe_a
    have hlenL := hL.length_le
    have hLle : (lcp2 (alpha D w) (alpha D (w ++ [a]))).length ≤ (alpha D w).length :=
      lcp2_length_le_left _ _
    have hlenAlpha : (outOf D M w).length + (bufOf D M w).length = (alpha D w).length := by
      rw [← hinv]
      simp
    have hdeq : (incr D w a).1
        = (alpha D w).length - (lcp2 (alpha D w) (alpha D (w ++ [a]))).length := rfl
    have hdle : (incr D w a).1 ≤ (bufOf D M w).length := by omega
    have hta : (alpha D w).take ((alpha D w).length - (incr D w a).1)
        = outOf D M w ++ (bufOf D M w).take ((bufOf D M w).length - (incr D w a).1) := by
      conv_lhs => rw [← hinv]
      rw [List.take_append]
      congr 1
      · rw [List.take_of_length_le]
        simp only [List.length_append]
        omega
      · congr 1
        simp only [List.length_append]
        omega
    have hstep : outOf D M w ++ pstep D M w a = alpha D (w ++ [a]) := by
      rw [hp, alpha_step D w a, hta, List.append_assoc]
    refine ⟨?_, ?_⟩
    · rw [outOf_append, bufOf_append, List.append_assoc, trim_append, hstep]
    · intro v hv
      rw [outOf_append]
      by_cases hc : (pstep D M w a).length ≤ 2 * M
      · have htrim : trim M (pstep D M w a) = ([], pstep D M w a) := by
          unfold trim
          rw [if_pos hc]
        simp only [htrim]
        have hv' : w ++ ([a] ++ v) ∈ Pre D.f := by
          rw [← List.append_assoc]
          exact hv
        have hsv := hsafe ([a] ++ v) hv'
        rw [← List.append_assoc] at hsv
        simpa using hsv
      · have htrim : trim M (pstep D M w a) =
            ((pstep D M w a).take ((pstep D M w a).length - M),
              (pstep D M w a).drop ((pstep D M w a).length - M)) := by
          unfold trim
          rw [if_neg hc]
        simp only [htrim]
        have h2 : (alpha D (w ++ [a])).take ((alpha D (w ++ [a])).length - M)
            = outOf D M w ++ (pstep D M w a).take ((pstep D M w a).length - M) := by
          conv_lhs => rw [← hstep]
          rw [List.take_append]
          congr 1
          · rw [List.take_of_length_le]
            simp only [List.length_append]
            omega
          · congr 1
            simp only [List.length_append]
            omega
        rw [← h2]
        exact alpha_stable D hM (w ++ [a]) v hv

lemma eval_append_ini (M : ℕ) (w : List A) :
    (transducer D M).toSequential.eval w ++ (if (stQ D M w).1 then [] else out0 D M)
      = outOf D M w := by
  rcases flag_eq D M w with hf | rfl
  · rw [outOf, hf]
    simp
  · rw [outOf, eval_nil]
    simp

lemma transducer_eval (M : ℕ)
    (hM : ∀ w v : List A, w ++ v ∈ Pre D.f → -(M : ℤ) ≤ dl D w v) :
    (transducer D M).eval = D.f := by
  funext w
  have hend : endOut D (rep D (stQ D M w).2.1) = endOut D w :=
    endOut_congr D (by rw [state_rep, transducer_state])
  have hev : (transducer D M).eval w =
      (endOut D w).map (fun u => outOf D M w ++ (bufOf D M w ++ u)) := by
    rw [Subsequential.eval]
    show ((transducer D M).endOfInput (stQ D M w)).map
      (fun u => (transducer D M).toSequential.eval w ++ u) = _
    show ((endOut D (rep D (stQ D M w).2.1)).map
        (fun u => (if (stQ D M w).1 then [] else out0 D M) ++ ((bufOf D M w) ++ u))).map
      (fun u => (transducer D M).toSequential.eval w ++ u) = _
    rw [hend, Option.map_map]
    congr 1
    funext u
    simp only [Function.comp_apply, ← List.append_assoc, eval_append_ini]
  cases hx : D.f w with
  | none =>
    have : endOut D w = none := by simp [endOut, hx]
    rw [hev, this]
    simp
  | some x =>
    have hdom : w ∈ Dom D.f := by
      show (D.f w).isSome
      rw [hx]; simp
    have hpre : w ∈ Pre D.f := mem_pre_of_mem_dom hdom
    obtain ⟨hinv, _⟩ := transducer_run D M hM hpre
    have hendw : endOut D w = some (x.drop (alpha D w).length) := by simp [endOut, hx]
    rw [hev, hendw]
    simp only [Option.map_some, ← List.append_assoc, hinv]
    rw [alpha_append_endOut D hx]

/-- Every continuous partial function with bounded variation is
subsequential. -/
lemma isSubsequential_of_continuous_boundedVariation [Finite A] [Finite B]
    {f : List A → Option (List B)} (hcont : PartialContinuous f) (hbv : BoundedVariation f) :
    IsSubsequential f := by
  obtain ⟨D, rfl⟩ := exists_data hcont hbv
  obtain ⟨M, _, hM⟩ := exists_deletion_bound D
  haveI : Finite (Set.range (state D)) := (state_range_finite D).to_subtype
  haveI : Finite {p : List B // p.length ≤ 2 * M} := (List.finite_length_le B (2 * M)).to_subtype
  exact ⟨_, inferInstance, transducer D M, transducer_eval D M hM⟩

end Subseq

/-- **Theorem `thm:subsequential-functions`.**  A partial function is subsequential if and only if
it is continuous and has bounded variation. -/
theorem isSubsequential_iff_aux {A B : Type} [Finite A] [Finite B]
    (f : List A → Option (List B)) :
    IsSubsequential f ↔
      (PartialContinuous f ∧
        ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
          f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K) := by
  constructor
  · intro hf
    exact ⟨hf.partialContinuous, hf.boundedVariation⟩
  · rintro ⟨hcont, hbv⟩
    exact Subseq.isSubsequential_of_continuous_boundedVariation hcont hbv

end Lax132576Proofs.Transducers
